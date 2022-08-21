:-[ruleMod, faultDet, reformation, util].


/**********************************************************************************************************************
    main(PSPath, KGPath): generate repair plans for the KG.
    Input:  ProofFile is the directory of file 'proofs.txt'.
            PST, PSF  are the directories of the true set and false set of the preferred structure.
            TriplesF is the directory for triple file, where all constants in the triples are replaced with reps.
            RulesF is the directory for rule file, where all constants in the triples are replaced with reps.
            HPath is the directory of heuristics and repair records.
    Output: repairNew is the file of the list of new repair plans.
    Important: the output need to be %print ed after string 'RepairPlans:' so that the python script can get it.
***********************************************************************************************************************/
main(ProofFile, PST, PSF, TriplesF, RulesF, HPath, RepairNew):-
    % get the inputs: the banned and applied repairs; heuristics and the proofs of sufficiencies and insufficiencies
    init([ProofFile, TriplesF, RulesF, PST, PSF],  [[SuffsIn, InsuffsIn, IncompsPairs], Abox, Rules, TrueSetE, FalseSetE], HPath),
    assert(spec(ts(TrueSetE))),
    assert(spec(fs(FalseSetE))),

    writeLog([nl, write_term('--------- Start repairGeneration '),nl, finishLog]),

    % Collect all unwanted proofs and ignore their goals
    findall(UnwantProof,
            (member((_, UnwantedProofs), IncompsPairs), member(UnwantProof, UnwantedProofs)),
            IncompsIn),

    appEach(InsuffsIn, [repairPlan, Abox, Rules, SuffsIn], RepPlans1),
    appEach(IncompsIn, [repairPlan, Abox, Rules, SuffsIn], RepPlans2),
    append(RepPlans1, RepPlans2, RepPlans), % RepPlans = [ [rp1, rp2], []...]
    % RepPlans = [RepPlan1|RepPlans2],
    %print (' fault\'s new repair plans found. '),

    % write all combined repiars into the file.
    open(RepairNew, write, StreamReps),
    forall(member(X, RepPlans), writeAll(StreamReps, X)),
    close(StreamReps),


    nl,print('success').

/**********************************************************************************************************************
    repCombine(RepPlans, Rules, RepSolsOut):-
            update Group by revising Rep.
    Input:  RepPlans: the list of the collection of repair plans for each fault.
            Rules: the Rules.
    Output: RepSolsOut: a list of solutions of repair plans. Each solution is the maximum group of independent repair plans.
************************************************************************************************************************/
repCombine([], _, []):- !.
repCombine(RepPlans, Rules, RepSolsOut):-
    findall(RepS,
                    (repCombine(RepPlans, Rules, [[]], RawSols), % RawSols is a collection of groups:[[[Rep1,Rep2...]]]
                     member(RawSol, RawSols),
                     findall(Rep,
                                 (member([_,(RepS,_),_],RawSol),
                                  member(Rep, RepS)),
                             RepS)),
            RepSolsTem),
    % get the group which is not contained by others. TODO: revise updGroup
    findall(Group,
                    (member(Group, RepSolsTem),
                     Group = [_|_],
                     forall((member(r, RepSolsTem), Group2 \= Group),
                              deleteAll(Group, Group2, [_|_]))),
            RepSols),
    sort(RepSols, RepSolsOut),
    writeLog([nl, write_term('All collections of repair plans are: '), nl, write_termAll(RepSolsOut),nl, finishLog]).


repCombine([], _, Solutions, Solutions).
repCombine([Reps1| Rest], Rules, Groups, Solutions):-
    % Reps1 is a list of repair plans for one fault.
    member(Rep1, Reps1),
    appEach(Groups, [updGroup, Rep1, Rules], GroupsTem),
    appAll(append, GroupsTem, [[]], GroupsNew, 1),
    repCombine(Rest, Rules, GroupsNew, Solutions).

/**********************************************************************************************************************
    updGroup(Group, Rep, Rules, GroupsOut):-
            update Group by revising Rep.
    Input:  Group: a group of repair plans, among which all members are independent from each other.
            Rep: the repair plans for fixing one fault, together with its information.
            Rules: the Rules.
    Output: GroupsPair: a pair of groups.
************************************************************************************************************************/
updGroup([], Rep, _, [[Rep]]):- !.
updGroup(Group, Rep, Rules, GroupsOut):-
    Rep = [FType1, (_, TargCls1), Cl1],
    findall(RepS,
                    (member(RepS, Group),
                    RepS = [FTypeS, (_, TargClsS), ClS],
                    repConflict(FType1, FTypeS, Rules, TargCls1, TargClsS, Cl1, ClS)),
                    %writeLog([nl,write_term('--Conflicts of repairs:'),nl, write_term(FType1),write_term(' vs '), write_term(FTypeS),nl, write_term(Rep),nl,write_term(RepS),nl, finishLog])),
            Confs),
    (Confs = [_|_]->
        deleteAll(Group, Confs, Fusion), !,
        Group2= [Rep| Fusion],
        sort([Group, Group2], GroupsOut);
    Confs = []->
        GroupsOut= [[Rep| Group]]).


/**********************************************************************************************************************
    repConflict(FType1, FType2, Rules, TargetCls1, TargetCls2, ClP1/ClE1, ClP2/ClE2):-
            check if repair plan 1 and 2 conflict with each other.
    Input:  RepPlans: the list of the collection of repair plans for each fault.
            Rules: the rules in the input KG
            TargetCls1: the targeted clauses which will be changed by applying repair plan 1
            TargetCls2:    the targeted clauses which will be changed by applying repair plan 2
            ClP1/ClE1:    the clauses of an incompatibility's proof/ the unprovable sub-goals of an insufficiency, which will be repaired by repair plan 1
            ClP2/ClE2:    the clauses of an incompatibility's proof/ the unprovable sub-goals of an insufficiency, which will be repaired by repair plan 2
    Output: None. terminate with success if repair plan 1 conflicts with repair plan 2.
***********************************************************************************************************************/

repConflict(incomp, incomp, _, TargetCls1, TargetCls2, ClP1, ClP2):- !,
    intersection(TargetCls1, ClP2, [_|_]), !; intersection(TargetCls2, ClP1, [_|_]).

% insuff vs insuff
repConflict(insuff, insuff, Rules, TargetCls1, TargetCls2, ClE1, ClE2):-
    findall(P1, (member(Cl1, ClE1),
                 (member(+[P1|_], Cl1); member(-[P1|_], Cl1))),
            PCl1),
    findall(P2, (member(Cl2, ClE2),
                 (member(+[P2|_], Cl2); member(-[P2|_], Cl2))),
            PCl2),

    (setof(Int,
            ((member([+[P|_]|_], TargetCls1), !; [+[P|_]|_] = TargetCls1),
            extBranch([TargetCls1| Rules], [P], PBranch),    % get all predicates which is after P on their branches.
            intersection(PBranch, PCl2, Int),
            Int = [_|_]),
        Conflicts), !;
    setof(Int,
            ((member([+[P|_]|_], TargetCls2), !; [+[P|_]|_] = TargetCls2),
            extBranch([TargetCls2| Rules], [P], PBranch),
            intersection(PBranch, PCl1, Int),
            Int = [_|_]),
        Conflicts)),
    writeLog([nl,write_term('--Conflicts of insuff vs insuff:'),write_term(Conflicts),nl, finishLog]).

repConflict(insuff, incomp, Rules, TargetCls1, TargetCls2, ClP1, ClP2):-
    repConflict(incomp, insuff, Rules, TargetCls2, TargetCls1, ClP2, ClP1).

% incomp vs insuff
repConflict(incomp, insuff, Rules, TargetCls1, TargetCls2, ClP1, ClP2):-
    intersection(TargetCls2, ClP1, [_|_]), !;
    intersection(TargetCls1, ClP2, [_|_]), !;
    findall(P2, (member(Cl2, ClP2),
                 (member(+[P2|_], Cl2); member(-[P2|_], Cl2))),
            PCl2),
    setof(Int,
            (member([+[P|_]|_], TargetCls1),
            extBranch(Rules, [P], PBranch),
            intersection(PBranch, PCl2, Int),
            Int = [_|_]),    % there is an axiom which constitutes the proof of repairing the insufficiency whose predicate is under the scope of P's influence
        Conflicts),
    writeLog([nl,write_term('--Conflicts of incomp vs insuff:'),write_term(Conflicts),nl, finishLog]).





%% No goal.   appEach(InsuffsIn, [repairPlan, Abox, Rules, SuffsIn], RepPlans1),
repairPlan(Goal, _, _, _):-
    occur(Goal, [(_, []), [], ([],_)]), !.

% TODO: MERGE insufficiencies goals with same predicate and then add the rule which proves all of them
repairPlan((Goal, Evidences), Abox, Rules, Suffs, RepPlansOut):-
    spec(rsb(RsBanned)),
    spec(rsa(RsList)),
    findall(RepairInfo,
                (buildP((Goal, Evidences), Abox, Rules, Suffs, RepairInfo),
                RepairInfo = [insuff, (RepPlans, _), _],
                RepPlans \= [],
                % check if the repair plan conflicts previous ones or it has been suggested
                intersection(RepPlans, RsBanned, []),
                intersection(RepPlans, RsList, [])),
            RepPlansTem),
    sort(RepPlansTem, RepPlansOut),

    length(RepPlansOut, N),
    writeLog([nl,write_term(N), write_term('repair plans  for buildP:'),write_term([Goal, Evidences]),
            nl,nl,nl,write_termAll(RepPlansOut),nl, finishLog]).

repairPlan(ProofInp, Abox, Rules, Suffs, RepPlansOut):-
    ProofInp = [_|_],
    spec(rsb(RsBanned)),
    spec(rsa(RsList)),

    findall(RepairInfo,
                (blockP(ProofInp, Abox, Rules, Suffs, RepairInfo),
                RepairInfo = [incomp, (RepPlans, _), _],
                RepPlans \= [],
                % check if the repair plan conflicts previous ones or it has been suggested
                intersection(RepPlans, RsBanned, []),
                intersection(RepPlans, RsList, [])),
            RepPlansTem),
    sort(RepPlansTem, RepPlansOut),

    length(RepPlansOut, N),
    writeLog([nl,write_term(N),write_term(' repair plans for blockP:'),write_term(ProofInp), nl,nl,nl,write_termAll(RepPlansOut),nl, finishLog]).


/**********************************************************************************************************************
    blockProof(Proof, Abox, Rules, SuffGoals, [RepPlan, TargetCls]): block one unwanted proof.
                The reason of not blocking all unwanted proofs is that the theory is changed and the other unwanted proofs could be changed.
    Input:  Proof: unwanted proof of an incompatibility.
            Abox, Rules: the KG.
                RsIn: a list of repairs that have been applied to get the KG, each of which is in the format of (Rs, Cl, I)
                RsBanned: the repairs that have been banned to apply, e.g., the ones failed in applying or violates some constrains.
    Output: [RepPlan]: a list of the repair plans which block Proof.
            TargetCls:    the clauses on which the RepPlan will apply.
            ClP: a collection of the clauses which constitute the proof.
************************************************************************************************************************/
%% Block the unwanted proof by adding a unprovable precondition.
blockP(Proof, Abox, Rules, SuffGoals, [incomp, ([RepPlan], ClT), ClS]):-
    spec(heuris(Heuristics)),
    spec(ts(TrueSetE)),
    spec(fs(FalseSetE)),

    % not all three heuristics are employed.
    deleteAll([noRuleChange, noPrecAdd, noAss2Rule, noAxiomDele], Heuristics, [_|_]),
    writeLog([nl, write_term('-------- Start blockProof1: -------- '),
            nl, write_termAll(Proof), finishLog]),

    % get the clauses in the unwanted proof.
    findall([Cl, Subs],
                    (member((_, Cl, Subs, _, _), Proof),
                    is_list(Cl)),
            CandRules),
    transposeF(CandRules, [ClS, _]),
    member([Axiom, IncomSubs], CandRules),    % target at one clause,
    writeLog([nl, write_term('Original Axiom is: '), write_term(Axiom),nl, finishLog]),

    spec(protList(ProtectedList)),
    notin(Axiom, ProtectedList),

    (occur(-_, Axiom), intersection([noRuleChange, noPrecAdd], Heuristics, []),    % if it is a rule
        % Add a irresolvable precondition to the rule to make it unprovable.
        % Appliable when the new rule still works for the sufficiency of which the old rule is essential)
        getAdjCond(Axiom, IncomSubs, SuffGoals, Abox, Rules, TrueSetE, FalseSetE, RepCands),
        % get single repair plan, RepPlan is an atom not a list.
        member(RepPlan, RepCands);
    Axiom=[+[Pred|_]], intersection([noRuleChange, noAss2Rule], Heuristics, []), notin(asst(Pred), ProtectedList),
        % Turn the assertion to a rule to make it unprovable.
        % Appliable when it is not essential for any sufficiency)
        % RepPlan = [(ass2rule(Axiom, NewRule), Axiom),...]
        asser2rule(Axiom,  SuffGoals, Abox, Rules, TrueSetE, FalseSetE, RepCands),
        member(RepPlan, RepCands);
    notin(noAxiomDele, Heuristics),  notEss2suff(SuffGoals, Axiom),
        (occur(-_, Axiom); Axiom=[+[Pred|_]], notin(asst(Pred), ProtectedList)),
        % if the axiom is not essential to an sufficiency, it can be deleted.
        RepPlan = delete(Axiom)),
    ClT = [Axiom].



%% Block the unwanted proof by reformation
blockP(Proof, Abox, Rules, SuffGoals, [incomp, ([RepPlan], [TargCl]), ClS]):-
    spec(heuris(Heuristics)),
    notin(noReform, Heuristics),
    spec(ts(TrueSetE)),
    spec(fs(FalseSetE)),
    spec(protList(ProtectedList0)),

    append(TrueSetE, FalseSetE, PrefStruc),
    append(ProtectedList0, PrefStruc, ProtectedList),


    findall(Cl, (member((_, Cl, _, _, _), Proof), is_list(Cl)), ClS),
    writeLog([nl, write_term('-------- Start blockProof2: reformation -------- '),
            nl, write_term('-------- Proof is:'),nl,write_term(Proof), nl,nl,
            nl, write_term('-------- SuffGoals is:'),nl,write_term(SuffGoals), nl,nl, finishLog]),

    %%print (' Proof is ' ), nl,%print (Proof),nl,
    member(TrgResStep, Proof),
    %%print (' TrgResStep is ' ), nl,%print (TrgResStep),nl,
    TrgResStep = ([-PropGoal|_], InpCl1, _, _, _),
    split(Proof, TrgResStep, ResStepPre, _),    % split the proof at TrgResStep.

    InpCl1 = [+[P| ArgsCl1]| _],        % automatically skip RS based on unae, as their InputClause =unae.
    traceBackPos(PropGoal, ResStepPre, -[P| ArgsG], InpCl2, _),    % Get the original negative literal and its clause where -GTarg comes from.

    % not both clauses are under protected.
    (notin(-_, InpCl1)-> deleteAll([asst(P), InpCl2], ProtectedList, [_|_]);
     member(-_, InpCl1)-> deleteAll([InpCl1, InpCl2], ProtectedList, [_|_])),

    %%print (' InpCl1 and InpCl2 are ' ), nl,%print (InpCl1),nl,%print (InpCl2),nl,
    %(InpCl1 = [+[bird,vble(y)], -[penguin,vble(y)]] -> pause;true),
    % get all candidates of unifiable pairs to block.
    findall([CC, VCG, VCIn, VV],
                (    nth0(X, ArgsCl1, C1),
                    nth0(X, ArgsG, C2),
                    (% if C1 and C2 are two constants
                     C1 = [], C1 = C2, CC = C1, VCG = [], VCIn = [];
                     % if C1 is a variable and C2 is a constant
                     C1 = vble(_),
                     C2 = [_], VCIn = (C1, C2), CC = [], VCG = [];
                     % if C2 is a variable and C1 is a constant
                     C1 = [_],
                     C2 = vble(_),    % If the variable occurs in the head of InpCl2, omit it.
                     % InpCl2 = [+[_| ArgsHead2]|_],
                     % because the repair plan of weakening it COULD be generated when targeting  RS0 where InpCl2 is the input clause. But if RS0 is between variables then no repair plan will be generated by it
                     % notin(vble(Y), ArgsHead2),
                     VCG = (C2, C1), CC = [], VCIn = [];
                     % if C1 and C2 are two vables
                     C1 = vble(_),
                     C2 = vble(_),
                     VV = [C1,C2], CC=[], VCG=[], VCIn= [])),
            UPairs),
    sort(UPairs, SortedPairs),    % the pairs are not empty
    SortedPairs = [_|_],

    transposeF(SortedPairs, [CCP, VCPG, VCPIn, VV]),
    %%print (' [CCP, VCPG, VCPIn] is ' ), nl,%print ([CCP, VCPG, VCPIn]),nl,
    (    (notin(InpCl1, ProtectedList),
            TargLit = +[P| ArgsCl1],
            TargCl = InpCl1,
            (findall(C, member((_, C), VCPG), CS),    % if the variable is from the goal literal and the constant is from InpCl1
             append(CS, CCP, ConsIn),    % get all the constants contained by InpCl1 which contribute to the unification.
             weakenVble(TargLit, TargCl, SuffGoals, ConsIn, VCPIn, Abox, Rules,  RepPlan)));
        (notin(InpCl2, ProtectedList), InpCl2 \= [],    % InpCl2 is neither an input clause under protected, nor from the preferred structure.
             TargLit = -[P| ArgsG],
            TargCl = InpCl2,
             (findall(C, member((_, C), VCPIn), CS),    % if the variable is from the goal literal and the constant is from InpCl1
             append(CS, CCP, ConsG),
              weakenVble(TargLit, TargCl, SuffGoals, ConsG, VCPG, Abox, Rules, RepPlan);
             % if 1. there are at least one more occurrence of the predicate in an assertion, which avoid mirror repaired theories.
             findall([+[P|ArgsTem]],
                  (member([+[P|ArgsTem]], Abox),
                   notin([+[P|ArgsTem]], [InpCl1, InpCl2])),
                      [_|_]),
             % and if 2.P is not under protected,
             notin([arity(P)], ProtectedList),%print (ProtectedList),nl,
             % then the goal literal could be the unique one.
             RepPlan = arityInc(P, TargLit, TargCl, +[P| ArgsCl1], InpCl1)));
        (member(InpCl1, ProtectedList), notin(InpCl2, ProtectedList),
            TargLit = -[P| ArgsG],
            TargCl = InpCl2,
            findall(C, member((_, C), VCPIn), CS),    % if the variable is from the goal literal and the constant is from InpCl1
             append(CS, CCP, ConsG),
            (weakenVble(TargLit, TargCl, SuffGoals, ConsG, VCPG, Abox, Rules,  RepPlan);
             notin([arity(P)], ProtectedList),%print (ProtectedList),nl,
             RepPlan = arityInc(P, TargLit, TargCl, +[P| ArgsCl1], InpCl1)))),
    %nl,nl,%print (' RepPlan is '), nl, %print (RepPlan),nl,nl,
    writeLog([nl, write_term('--Blocking Repair Plan11 InpClause:'),
                nl, write_term(TargCl),nl, nl,
                write_term(RepPlan),nl, finishLog]).

/**********************************************************************************************************************
   buildProof(Evidences, Abox, Rules, Suffs, Output):
        Generate a repair to unblock a proof of Goal and try best to avoid introducing insufficiecy.
   Input:    Abox, Rules: the KG.
               Evidences: [Goal, Evis], where
               Goal(-Assertion): the negative literal that cannot be resolved away by the KG.
               Evidences: the partial proofs of Goal.
               Suffs: all provable goals with their proofs.
   Output:     RepairPlans = a list of repair plans for unblocking an evidence of the goal.
               TargCls: a list of clauses to which the repair plan will apply.
               ClE: a collection of the remaining unprovabe sub-goals in all the evidences of that Goal.
************************************************************************************************************************/
buildP([], _, _, _, _):-fail,!.
buildP(([], []), _, _, _, _):-fail,!.


buildP((Goal, Evidences), Abox, Rules,  SuffGoals, [insuff, (RepPlans, TargCls), ClS]):-
    spec(heuris(Heuristics)),
    %print ('--------Start unblocking 1 based on evidences  ------'),
    Goal \= [],

    % Get one partial proof Evd and its clauses information lists ClsList.
    member(Evi, Evidences),

    findall((Num, GoalsRem, ProofCur),
               ((member((Subgoals, _, _, _, _), Evi); member((_, _, _, Subgoals, _), Evi)),
                findall([SubG, Proof],
                            (member(SubG, Subgoals),
                            slRL([SubG], Abox, Rules,  Proof,_,_),
                            Proof = [_|_]),        % found a non-empty proof
                        ResovlableG),
                transposeF(ResovlableG, [ResGs, SubGProofs]),    % get all resolvable sub-goals
                subtract(Subgoals, ResGs, GoalsRem),
                length(GoalsRem, Num),
                appAll(append, SubGProofs,[Evi], ProofCur,1)),    % ProofCur is a set of RS ignoring their order that results the remaining irresolvalble sub-goals only.
           Rems),
    sort(Rems, SortedRems),
    SortedRems = [(MiniRemG, _,_)|_],        % get the number of the least unresolvable subgoals
    member((MiniRemG, Unresolvables, ProofCur), SortedRems),    % get one minimal group of the unresovable sub-goals.
    writeLog([nl,write_term('-- Unresolvables and ProofCur is :'),nl,write_term(Unresolvables),nl,write_term(ProofCur),nl,  finishLog]),

    (notin(noPrecDele, Heuristics),    % unblocking by deleting unprovable preconditions
        writeLog([nl,write_term('--Deleting unprovable preconditions:'),nl,write_term(Unresolvables),nl,  finishLog]),
        delPreCond(Unresolvables, Evi, RepPlans1, TargCls),
        RepPlans = [RepPlans1];
    notin(noReform, Heuristics),    % by reformation.
        writeLog([nl,write_term('--Reformation: Unresolvables:'),nl,write_term(Unresolvables),nl,  finishLog]),
        findall(Cl, member((_,Cl,_,_,_), Evi), ClUsed),
        reformUnblock(Unresolvables, Evi, ClUsed, SuffGoals, Abox, Rules,  RepInfo),
        transposeF(RepInfo, [RepPlans, TargClsList]),
        setof(Cl, (member(List, TargClsList),
                    member(Cl, List)),
              TargCls);
    intersection([noAxiomAdd, noAssAdd], Heuristics, []),    % by adding the goal as an axiom or a rule which derives the goal.
        setof([expand([+Prop]),    [+Prop]],
                    (member(-PropG, Unresolvables),
                    replace(vble(_), [dummy_vble_1], PropG, Prop)),
                RepPairs),
        transposeF(RepPairs, [RepPlans, TargCls])),

    % get all of the clauses which constitute the target proof to unblock
    findall(Cl, (member((_,Cl,_,_,_), ProofCur), is_list(Cl)), ClE1),
    append(TargCls, ClE1, ClS1),
    delete(ClS1, [], ClS),

    %print ('--Unblocking 1: RepPlanS:'),nl,%print (RepPlans),nl, %print (TargCls),
    nl.



%% Repair the insufficiency by adding a rule whose head is the goal.
buildP((Goal, _), Abox, Rules, _, [insuff, (RepPlans, RuleNew), ClS]):-
    %% Repair the insufficiency by abduction.
    spec(heuris(Heuris)),
    notin(noAxiomAdd, Heuris),
    notin(noRuleChange, Heuris),
    spec(ts(TrueSetE)),
    spec(fs(FalseSetE)),
    Goal = [-PropG|_],
    %print ('--------Start unblocking 2 by adding a rule with goal: '), %print (PropG),nl,
    % get all relevant theorems to the goal
    findall((L, Theorem),
                (PropG = [_ |Args],
                 member(C, Args),
                 allTheoremsC(Abox, C, Theorems),
                 member(Theorem, Theorems),
                 Theorem = [+[_|Arg2]],
                 deleteAll(Args, Arg2, DistArg),
                 length(DistArg, L)),    % L is the number of arguments in Goal but not in the theorem.
                RelTheorems),
    mergeTailSort(RelTheorems, [(_, Cands)|_]), % get all candidates which is the most relevant theorems to Goal.
    deleteAll(Cands, FalseSetE, Cands2),    % the precondition does not correspond to the false set.

    % Heuristic7: When there is other theorems of C, do not consider the inequalities of C.
    (member([+[P|_]], Cands2), P \= (\=)-> delete(Cands2, [+[\=|_]],Cands3);
     Cands3 = Cands2),

    % get all restrict constrains which are under protected.
    findall(Constrain,(member(Constrain, Rules),
                     notin(+_, Constrain),
                     spec(protList(ProtectedList)),
                     member(Constrain, ProtectedList)),
            ResCons),
    % find all violations of the candidate rule CandRule w.r.t. protected constains in the thoery.
    findall([+Prop],
                (member([+Prop], Cands3),
                 member(Constrain, ResCons),    % check based on a protected constrain axiom.
                 % there is a proof of the violation of the constrain.
                 slRL(Constrain, [[+Prop], [+PropG]], [], [_|_], [], []),
                 writeLog([nl,write_term('**** Constrains check failed: '),nl,
                     write_term([+PropG, -Prop]),
                    write_term(' vs '),write_term(Constrain),nl])),    % proof exists
            VioCand),
    deleteAll(Cands3, VioCand, RuleCands),

    % formalise  a rule with only one prediction.
    member([+Prop], RuleCands),
    nl,%print ([+PropG, -Prop]),
    generalise([+PropG, -Prop], RuleTem),
    nl,%print ('RuleTem is '), %print (RuleTem),nl,
    % check incompatibilities.
    findall(Proof,
             (member([+[Pre| Args]], FalseSetE),
              % skip equalities/inequalities which have been tackled.
              notin(Pre, [\=, =]),
              NVioSent = [-[Pre| Args]],
              % get all of a proof of Goal
              slRL(NVioSent, Abox, [RuleTem| Rules], Proof, [], []),
              Proof \= []),                                       % Detect incompatibility based on refutation.
         Incompat),                                      % Find all incompatibilities. FaultsProofs is the proofs that the objective theory proves one or more violative sentences.
    (Incompat = []->
        RuleNews = [[expand(RuleTem)]];
    Incompat = [_|_]->
        % check if there is an incompatibility caused by RuleR6
        findall(Subs,
                (member(IncompProof, Incompat),
                 member((_,RuleTem,Subs,_,_), IncompProof)),
                IncomSubsRaw),

        sort(IncomSubsRaw, IncomSubs),
        findall(Proof,
                    (slRL(Goal, Abox, [RuleTem| Rules], Proof, [], []),
                    Proof \=[]),
                Proofs),

        getAdjCond(RuleTem, IncomSubs, [(Goal, Proofs)], Abox, [RuleTem| Rules], TrueSetE, FalseSetE, CandAll),
        (findall([expand(RuleNew)],
                (member(add_pre(Precondition, _), CandAll),
                 sort([Precondition| RuleTem], RuleNew)),
                 RuleNews);
         CandAll = []-> RuleNews = [[expand(RuleTem)]])),

    member(RepPlans, RuleNews),
    RepPlans = [expand(RuleNew)],
    % get all of the clauses which constitute the target proof to unblock

    % only consider the rule that can prove the goal
    setof(Cl, (slRL(Goal, Abox, [RuleNew|Rules], ProofUnblocked, [], []),
                member((_,Cl,_,_,_), ProofUnblocked),
                is_list(Cl)),     % do not record keyword 'unae'
            ClS),
   %print ('--Unblocking 2: RepPlanS/CLE'),nl,%print (RepPlans),nl,%print (ClS),
   nl.

%% Repair the insufficiency by analogising an existing rule and give them different preconditions.
buildP((Goal, Evidences), Abox, Rules, Suffs, [insuff, (RepPlans, RuleR7), ClS]):-
    spec(heuris(Heuristics)),
    notin(noRuleChange, Heuristics),
    notin(noAnalogy, Heuristics),
    spec(protList(ProtectedList)),
    spec(ts(TrueSetE)),
    spec(fs(FalseSetE)),
    %print ('--------Start unblocking 3: by Analogical Abduction for ------'),
    findall(Rule,
            (member((_, Proofs), Suffs),
             member(Proof, Proofs),
             member((_,Rule,_,_, _), Proof),    % Sub is the substitutions that have applied to the rule in Proof.
             is_list(Rule),                        % do not take the keyword 'unae' into account.
             notin(Rule, ProtectedList),
             length(Rule, L),
             L>1),
            RulesUseful),
     (RulesUseful = []->
         writeLog([nl, write_term('******** No rules are useful, Analogy fails.'),nl, finishLog]);
         RulesUseful = [_|_]),

     findall(GoalRem,
               (member(Evi, Evidences),
                (member((Subgoals, _, _, _, _), Evi); member((_, _, _, Subgoals, _), Evi)),
                findall(SubG,
                            (member(SubG, Subgoals),
                            slRL([SubG], Abox, Rules, Proof,_,_),
                            Proof = [_|_]),        % found a non-empty proof
                        ResovlableGs),    % get all resolvable sub-goals
                subtract(Subgoals, ResovlableGs, GoalRem),
                length(GoalRem, 1)),
           SingleGs),
    sort([Goal| SingleGs], SingleGoalList),        % get the list of the single unresolvable subgoal.
    writeLog([nl,write_term('-- The single unresolvable subgoal. is :'),nl,write_term(SingleGoalList),nl,  finishLog]),

    setof(Relevancy,
            (member(RuleC, RulesUseful),        % get a rule candidate
             member(TargetG, SingleGoalList),    % get a target goal candidate
             relevancy(RuleC, TargetG, Abox, Relevancy)),
         Relevancies),
    % get the most relevant rule w.r.t. the goal.
    last(Relevancies, (S1, S2, RuleSR, TGoal, PreCondRel, PPs)),
       findall(-P, (member(-P, RuleSR), notin(-P, PreCondRel)), PSIrrela),
    writeLog([nl, write_term('The scored relevant rule is '), nl, write_term(RuleSR), nl,
            write_term(S1), write_term(','), write_term(S2), nl, finishLog]),

    % remove irrelevant preconditions
    deleteAll(RuleSR, PSIrrela, RuleR),
    RuleR \= [],
    TGoal = [-[PG| ArgG]],
    member(+[_|ArgsHR1], RuleR),
    delete(RuleR, +[_|ArgsHR1], Body1),

    % instantiate RuleR based on the target goal.
    unification([PG| ArgG], [PG| ArgsHR1], [],[],_, Substitution, []),        % If successful resolution
    subst(Substitution, Body1, Body2),
    % get the partner precondition which can be resolved by a theorem,
    % and the mis-matched arguemnts between the preconditions in Body2 and their partner preconditions.
    findall([PartPre, MisPairs],
            (member(-Precond, Body2),
             mmMatches(-Precond, PPs, PartPre, MisPairs)),
            Body3Info),

    % divid the list of the minimal argument mismatches MMPs
    transposeF(Body3Info, [Body4, MMPsList]),
    RuleR4 = [+[PG| ArgG]| Body4],
    % reorganise all mismatches as one list of constants.
    findall(C, (member(MMPs, MMPsList),
                member((C1,C2),MMPs),
                member(C, [C1,C2])), MMPsAll),

    % get the introduction preconditions for MMPs.
    getIntro(MMPsAll, Abox, Rules, IntroPs),
    writeLog([nl, write_term('The introduction preconditions are '), nl,
                write_termAll(IntroPs), nl, finishLog]),
    append(RuleR4, IntroPs, RuleR5),

    % generalisation
    generalise(RuleR5, RuleR6, _, _),    % e.g., Subs65 is [[a]/vble(z)]
    writeLog([nl, write_term('The generalised rule RuleR6 is'), nl,
                write_term(RuleR6), nl, finishLog]),

    % check incompatibilities.
      findall(Proof,
               (member([+[Pre| Args]], FalseSetE),
                % skip equalities/inequalities which have been tackled.
                notin(Pre, [\=, =]),
                NVioSent = [-[Pre| Args]],
                % get all of a proof of Goal
                slRL(NVioSent,Abox, [RuleR6| Rules], Proof, [], []),
                Proof \= []),                                       % Detect incompatibility based on refutation.
           Incompat),                                      % Find all incompatibilities. FaultsProofs is the proofs that the objective theory proves one or more violative sentences.

    % check if there is an incompatibility caused by RuleR6
    findall(Subs,
            (member(IncompProof, Incompat),
             member((_,RuleR6,Subs,_,_), IncompProof)),
            R6IncomSubsRaw),

    sort(R6IncomSubsRaw, R6IncomSubs),
    findall(Proof,
                (slRL(Goal, Abox, [RuleR6| Rules], Proof, [], []),
                Proof \=[]),
            Proofs),

    getAdjCond(RuleR6, R6IncomSubs, [(Goal, Proofs)], Abox, [RuleR6| Rules], TrueSetE, FalseSetE, CandAll),
    (member(add_pre(Precondition, _), CandAll)-> sort([Precondition| RuleR6], RuleR7);
     CandAll = []-> RuleR7 = RuleR6),

   writeLog([nl, write_term('--------The incompatibilities of R6 include'),
                nl, write_termAll(R6IncomSubs), nl,
               nl, write_term('--------The resulted rules of analogise RuleSR include'),
               nl, write_termAll(RuleR7), finishLog]),

    %convertForm([RuleSR, RuleR7], [SRAxiom, RuleNew]),    % rever the internal format of rules back to axioms
    RepPlans = [analogy(RuleSR, RuleR7)],

    % get all of the clauses which constitute the target proof to unblock
    findall(Cl, (slRL(Goal, Abox, [RuleR7|Rules], ProofUnblocked, [], []),
                member((_,Cl,_,_,_), ProofUnblocked),
                is_list(Cl)),
            ClS).
