/*    ABCT Repair System Procedure %%
      Xue Li Nov 2021

This file contains the functions/predicates of dealing with proofs.
Update Date: 13.08.2022
*/
:- [util].
:- use_module(library(lists)).


/**********************************************************************************************************************
    main(TriplesF, RulesF, PosF, NegF, outputF)
            detect sufficiencies and faults of insufficiencies, incompatibilities of
            the objective theory based on preferred structure (PS).
    Input:  TriplesF is the directory for triple file, where all constants in the triples are replaced with reps.
            RulesF is the directory for rule file, where all constants in the triples are replaced with reps.
            EquF is the directory for equivalence classes file
            PosF is the directory for positive examples in PS.
            NegF is the  directory for negative examples in PS.
    Output: FaultF: is the  directory for output file written FaultState = (Suffs, InSuffs, InComps), where
                        Suffs: the provable goals from pf(T).
                        InSuffs: the unprovable goals from pf(T).
                        InComps: the provable goals from pf(F).
************************************************************************************************************************/
main(TriplesF, RulesF, PosF, NegF, FaultF):-
    % initialisation
    retractall(spec(_)),
    init([TriplesF, RulesF, PosF, NegF],  [Abox, Rules, TrueSetE, FalseSetE]),

    % Find all proofs or failed proofs of each preferred proposition.
    findall( [Suff, InSuff],
            ( % Each preferred sentence is negated, and then added into Theory.
              member([+[Pre| Args]], TrueSetE),
              % skip equalities/inequalities which have been tackled.
              notin(Pre, [\=, =]),
              Goal = [-[Pre| Args]],

              % Get all proofs and failed proofs of the goal.
              findall( [Proof, Evidence],
                     ( slRL(Goal, Abox, Rules, Proof, Evidence, [])),
                     Proofs1),
              % Proofs1= [[P1, []],[P2, []],[[],E1]...]; Proofs2 = [[P1,P2,[]],[[],[],E]]
              transposeF(Proofs1, [Proofs, Evis]),
              % only collect none empty proofs/evidences
              (Proofs = []-> Suff = [], InSuff =(Goal, Evis);
               Proofs = [_|_]->Suff =(Goal, Proofs), InSuff=[])),
           AllP),
     % Split into a list of sufficiencies (Suffs), and a list of insufficiencies (InSuffs).
     transposeF(AllP, [Suffs, InSuffs]),

     writeLog([nl, write_term('---------SufGoals is------'), nl,write_term(Suffs),
     nl, write_term('---------InsufGoals is------'), nl,write_term(InSuffs), finishLog]),

    % detect the incompatibilities represented as a list of (Goal, Proofs), where -Goal is from F(PS).
      findall((Goal, UnwProofs),
           (member([+[Pre| Args]], FalseSetE),
            % skip equalities/inequalities which have been tackled.
            notin(Pre, [\=, =]),
            Goal = [-[Pre| Args]],
            % Get all proofs of the goal.
            findall(UnwProof,
                    (slRL(Goal, Abox, Rules, UnwProof, [], []), UnwProof \= []),
                    UnwProofs),
            UnwProofs \= []), % Detected incompatibility based on refutation.
           InComps),             % Find all incompatibilities.

    writeLog([nl, write_term('---------InComps are------'),nl, write_termAll(InComps), finishLog]),
    % detect the inconsistencies due to the violation of constrains
    % TODO: from theory to rule set
    findall((Constrain, UnwProofs),
              (member(Constrain, Rules),        % get a constrain axiom from the theory.
               notin(+_, Constrain),
               % Get all proofs of the goal.
               findall(UnwProof,
                       (slRL(Constrain, Abox, Rules, UnwProof, [], []), UnwProof \= []),
                       UnwProofs),
            UnwProofs \= []),
          Violations),
    writeLog([nl, write_term('---------Violations are------'),nl, write_termAll(Violations), finishLog]),
    append(InComps, Violations, Unwanted),
    open(FaultF, write, StreamOut),
    write(StreamOut, Suffs), write(StreamOut, "."), nl(StreamOut),
    write(StreamOut, InSuffs), write(StreamOut, "."), nl(StreamOut),
    write(StreamOut, Unwanted), write(StreamOut, "."),
    close(StreamOut),

    length(InSuffs, InSuffsNum),
    length(Unwanted, InCompsNum),

    % IMPORTNAT: below is the fixed form for python script to get the fault number. Do not change.
    nl, print(InSuffsNum), nl, print(InCompsNum).


/**********************************************************************************************
unification(E1, E2, SigmaIn, UnisIn, UnisOut, SigmaOut, Result): Unify the equation E.
    Notice: The left side of the unification EL is the goal literal.
Input:     E1 and E2 have to be two propositions: [P|Args]. Args vs Args will fail.
        SigmaIn: the applied substitutions.
        UnisIn = [], for keeping record of UnisOut.
Output:    Unis: all unifications between terms or predicate symbols, e.g.,  [european=european, vble(x)=[lily]]
        SigmaOut: all of the applied substitutions.
        Result: [] if all equations success, or the remaining equations.
***********************************************************************************************/
unification(E1, E2, SigmaIn, UnisIn, UnisOut, SigmaOut, Result):-
    pairwise([E1], [E2], Equations),
    unification(Equations, SigmaIn, UnisIn, UnisOut, SigmaOut, Result).

unification([],Sigma, Unis, Unis, Sigma, []) :- !.   % Fail if failure wanted, but base case is successful

unification([[F1|Args1]=[F2|Args2]|Old], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    F1==F2, !, length(Args1,L), length(Args2,L),       % If functors and arities agree
    pairwise(Args1, Args2, New),                      % Pair up corresponding subterms
    append(New, Old, Rest),                           % Add them to the Old problems
    unification(Rest, SigmaIn, [([F1|Args1]=[F2|Args2])|UnisIn], UnisOut, SigmaOut, UniResult).        % Repair either from recursive part

%
unification([vble(X)=vble(X)|Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-   % If two vars and same then
    !, unification(Rest, SigmaIn, [(vble(X)=vble(X))|UnisIn], UnisOut, SigmaOut, UniResult).                   % ignore them and carry on with the rest

% Case VV/=: variables are different
unification([vble(X)=vble(Y)|Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    X\==Y, !,                                                    % If two vars are different then
    Subst1 = vble(Y)/vble(X),                                 % some subst needed
    compose1(Subst1,SigmaIn,SigmaMid),                        % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),                             % substitute one for the other in the problems
    unification(NewRest, SigmaMid, [(vble(X)=vble(Y))|UnisIn], UnisOut, SigmaOut, UniResult).              % Recurse with new problem

%% Switch expressions if in wrong order
unification([A = B| Rest], SigmaIn, UnisIn, UnisOut, SigmaOut, UniResult) :-
    member(A = B, [(vble(X) = C), (C=vble(X))]),!,
    is_list(C), length(C, 1),                              % Constant is a constant
    Subst1 = C/vble(X),
    compose1(Subst1,SigmaIn,SigmaMid),                         % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),
    unification(NewRest, SigmaMid, [(A = B)|UnisIn], UnisOut, SigmaOut, UniResult).


unification(Ununifiable,Sigma, Unis, Unis, Sigma, Ununifiable).        % the remaining failed unifications.

/**********************************************************************************************************************
slRL(Goal, Abox, Rules, Proof, Evidence, Theorem): SL resolution based on reputation.
Input:  Goal: Goal is the main goal, which could be a list of subgoals.
        Abox is the input triples, where all constants have been replaced by their equivalence representatives.
        Rules is the input rules, where all constants have been replaced by their equivalence representatives.
        * CAUTION: each input clause is a Horn clause with its HEAD IN FRONT.
Output: Theorem:         when there is positive literal in the input Goal, it could be a theorem derived in the end.
        Proof/Evidence:    either a Proof of Goal or an evidence of a failed proof, and the other is [].
        Proof/Evidence = [(Goal0, InputClause1, Subs1, Goal1, RemCondNum1), (Goal1, InputClause2, Subs2, Goal2, RemCondNum2), ...]
                where Goal0 is the current goal clause,
                      InputClause1 is a clause that resolves the fist subgoal of Goal0;
                        Subs1 is a list of substitutions that applies to the arguments of InputClause1 in the proof/evidence;
                        Goal1 is the resulting goal clause of this derivation step which will be the goal to resolve in the nest step,
                        NumRemain is the number of the preconditions which originally come from InputClause1 and remain in the newest goal clause GoalX. For a proof, these numbers are 0.
        Unresovlales: the unresolvable Subgoals.
CAUTION: In a failed proof, it is the first subgoal cannot be resolved, and it is unknown whether the rest subgoals are resolvable or not.
************************************************************************************************************************/
% Nothing if the input theory is empty.
slRL(_, [], _, [], [], []):-!.

% Rewrite the input goal and the theory.
slRL(Goal, Abox, Rules, _, _, _):-
    (\+is_list(Goal), nl,print('ERROR: slRL\'s Goal is not a list'),nl;
    \+is_list(Abox), nl,print('ERROR: slRL\'s Abox is not a list'),nl;
    \+is_list(Rules), nl,print('ERROR: slRL\'s Rules is not a list'),nl), fail, !.

% Rewrite the input goal and the theory.
slRL(Goal, Abox, Rules, Proof, Evidence, Theorem):-!,
    % Set an depth limit of the resoluton according to the length of the thoery.
    length(Abox, L),
    RCostLimit is L*L,    % the depth limit of a proof.
      % if there is a head in the goal clause, then move the head to the end, which is for the derivation of an assertion theorem.
    ( member(+Head, Goal) -> delete(Goal, +Head, RestGoal), append(RestGoal, [+Head], GoalNew),!;
                            notin(+_, Goal) -> GoalNew = Goal),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),

slRLMain(GoalNew, [], Abox, Rules, ProofTem, EvidenceTem, Theorem, RCostLimit),
    cleanSubMid(ProofTem, Proof),
    cleanSubMid(EvidenceTem, Evidence).
/* writeLog([nl,write_term('--------SL Resolution with Goal: '),
        write_term(Goal), write_term('--------'),nl,
        write_term('Proof is:'),write_term(Proof),nl,
        write_term('Evidence is:'),write_term(Evidence),nl,
        write_term('Theorem is:'),write_term(Theorem),nl, finishLog]).
*/

%% slRLMain1: No goals remain to resolve, a theorem is found, output the whole proof ([], Ancestors).
% When a proof is found, do not search further, and the evidence of partial proof is empty.
slRLMain([+Literal], Evi, _, _, ProofOut, [], Theorem, _):-
    (Evi = [] -> ProofOut = [([+Literal],[],[],[+Literal],[0,0])];
     Evi = [_|_] -> ProofOut = Evi),
    Theorem = [+Literal], !.

%% slRLMain2: No goals to resolve, output the whole proof ([], Ancestors) with [] for Evidence and Theorem.
% When a proof is found, do not search further
slRLMain([], Proof, _,_, Proof, [], [],_):- !.                                    % The proof is output. Reset the proofStatus to the default value 0.


%% slRLMain33: Use an input triple to resolve Goal.
slRLMain(Goals, Deriv, Abox, Rules, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-[P| Arg]| GoalsRest],
    notin(P, [=, \=]),
    (notin(vble(_), Arg)->
                member([+[P| Arg]], Abox),
                InputClause = [+[P| Arg]],
                GoalsNew = GoalsRest,
                SG =[];
     occur(vble(_), Arg)->
                 member([+[P| Arg2]], Abox),
                 InputClause = [+[P| Arg2]],
                 unification([P| Arg], [P| Arg2], [],[],_, SG, []),
                 subst(SG, GoalsRest, GoalsNew)),
    CurDerStep = ((Goals, SG), (InputClause, []), GoalsNew, [0, 0]),
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, Abox, Rules, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.


%% slRLMain33: Use an input rule to resolve Goal.
slRLMain(Goals, Deriv, Abox, Rules, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-Goal| GoalsRest],
    Goal = [Pred| _],            % get the predicate of the left most sub-goal to resolve.
    notin(Pred, [=, \=]),    % Pred is not = neither \=.
    %**Caution: any CUT here will cause the issue of unable to find all proofs even under findall/3. Therefore, a Flag proofStatus is applied.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),   % Set the proofStatus as 1, so the first sub-goal will be resolved if it can be.
    length(Deriv, RDepth),
    RDepth < RCostLimit,    % The current proof depth has not bigger than the limit.
    % Require that the head of a clause should be its first literal.
    InputClause = [+[Pred| _]| [_|_]],    % get a rule whose tail is also a list.
    member(InputClause, Rules),             % Successfully get one input clause whose head has the same predicate with the predicate of the goal. % It could be a clause added by abduction
    % rewrite shared the variable in Goals if that variable occurs both in the goal and the input clause.
    rewriteVble(Goals, InputClause, RewClause, SubsVG),
    RewClause = [+[Pred| ArgCl]| Body],
    % between two variables, SubsRes replace the goal's variable with the input clause's variable
    unification(Goal, [Pred| ArgCl], [],[],_, SubsRes, []),        % If successful resolution
    append(Body, GoalsRest, GoalsTem2),    % Get the resulting clause C with newly introduced literals Body in front.
    subst(SubsRes, GoalsTem2, GoalsNew),
    noloopBack(GoalsNew, Deriv),        % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),      % Reset the flag to the default value 0.
    %* Do not remove duplicated sub-goals which will effect trace-back process.
    length(Body, RemCondNum),            % the number of the remaining preconditions in the NewGoal.
    subDiv(SubsRes, Goals, SG),    % divide the substitutions to the ones applied to goal SG and the ones to the input clause SC.
    subDiv(SubsRes, InputClause, SI),
    compose1(SubsVG, SI, SubsCl),
    CurDerStep = ((Goals, SG), (InputClause, SubsCl), GoalsNew, [RemCondNum, 0]),
    updateDeriv(Deriv, CurDerStep, firstNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    slRLMain(GoalsNew, DerivNew, Abox, Rules, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

%% slRLMain4: When there the firs sub-goal is irresolvable,return the evidence of the partial proof with [] as the proof and theorem.
%% Notice that only the first subgoal in Goals is gaurenteed to be unresolvable. The following subgoals could be resolvable.
slRLMain(Goals, Deriv, _, _, [], Evidence, [], _):-
    spec(proofStatus(1)),      % All axioms from the input theory have been tried for resolving the goal.
    Goals \= [],                    % And they all failed in resolving the remaining Goal.
    Goals \= [+_],                    % And it is not a derived assertion
    (Deriv = []-> Evidence = [(Goals, [], [], Goals, [0, 0])];    % record the unprovable goal when no RS have been done.
    Deriv \= []-> Evidence = Deriv),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))).   % The failed proof is output. Reset the proofStatus to the default value 0.


%% slRLMain5: resolve Goal whose predicate is \= or = based on UNA.
slRLMain(Goals, Deriv, _, _, Proof, Evidence, Theorem, RCostLimit):-
    forall(member(-[P|_], Goals), occur(P, [=, \=])),    % all of the goal predicates are equality/inequality predicates.
    % update the number of remaining goals fromt the non-equality/non-inequality to equality/inequality.
    findall((RS, RSNew),
                (member(RS, Deriv),
                RS = (CG, Inp, GN, Sub, [Num1, Num2]),
                Num1 \= 0,
                N2New is Num1 + Num2,        % the remaining goal number is the sum of both type
                RSNew = (CG, Inp, GN, Sub, [0, N2New])),
            TypeUp),
    replace(TypeUp, Deriv, DerivNew),
    % As all constants in triples and rules have been replaced with their representatives, No further EC to consider. Thus, it is [] given as EC below.
    resolveEqu(Goals, DerivNew, [], Proof, Evidence, Theorem, RCostLimit).



/**********************************************************************************************************************
    updateDeriv(DerivIn, ResStep, PredType, DerivOut):
            Update the record of the derivation steps.
    Input:  DerivIn: a list of the previous resolution steps, each of which is (Goal, InputClause, Subs, NextGoal, RemCondNum).
                InputClause: the input clause which resolves the first subgoal in Goal.
                Subs: the substitutions which have been applied to the InputClause.
                NextGoal: the resulting goal after resolvig with InputClause.
                RemCondNum: the remaining number of the preconditions of the InputClause in the last, newest Goal clause.
            ResStep: the last derivation step.
            PredType: the type of the predicate of the resolved subgoal: secondNum for = or \=, and firstNum for others.
    Output: DerivOut: the record of all derivation steps.
************************************************************************************************************************/
updateDeriv(Deriv, reorder, DerivNew):-
    findall(E,
            (member(E, Deriv),
             E = (_,  _, _, _, [0,0])),
            ES),
    deleteAll(Deriv, ES, DerivRemain),
    last(DerivRemain, Target),
    Target = (G1, Cl, S2, G2, [NumR1, NumR2]),
    NumR1New is NumR1 - 1,
    NumR2New is NumR2 + 1,
    TargetNew = (G1, Cl, S2, G2, [NumR1New, NumR2New]),
    replace(Target, TargetNew, Deriv, DerivNew).

updateDeriv(DerivIn, ResStep, PredType, DerivOut):-
    ResStep = ((G, SubG), (InputClause, SubCl), GoalsNew, Num),
    CurrentStep = (G, InputClause, SubCl, GoalsNew, Num),
    reverse(DerivIn, Deriv1),      % the update will start from the last InputClause.
    pairSub(G, SubG, GSPairs),    % get the list of pairs between a sub-goal and its new substitutions.
    updateOldCls(Deriv1, GSPairs, PredType, Deriv2),
    reverse([CurrentStep| Deriv2], DerivOut).    % make the derivation back in order.

updateOldCls([],_,_,[]):-!.
% Need to decrease the number of the remaining conditions of the inputclause which introduced the current resovled subgoal.
% H is the target RS which introduces the resolved subgoal.
updateOldCls([H|Rest], [(_, Subs)|RestPairs], PredType, [HNew| RestNew]):-
    H = (Goal, InputClause, SubOld, NextGoal, [RemNum1, RemNum2]),
    % update the number of the remaining preconditions of this rule in the current goal clause
    (PredType = firstNum, RemNum1 > 0 ->
        RemNum1New is RemNum1 - 1,
         NumUpd = [RemNum1New, RemNum2], !;
    PredType = secondNum, RemNum2 > 0 ->
        RemNum2New is RemNum2 - 1,
        NumUpd = [RemNum1, RemNum2New], !),
    compose1(Subs, SubOld, SubNew), !,   % the current substitutions are applied to this clause, so update Subs.
    HNew = (Goal, InputClause, SubNew, NextGoal, NumUpd),
    % update the substitutions.
    updatePreDer(Rest, RestPairs, RestNew).
% if the last branch fails, try this one.
updateOldCls([H|Rest], RestPairs, PredType, [H| RestNew]):-
    updateOldCls(Rest, RestPairs, PredType, RestNew).

% Supplement the substitution which applied to the latest resovaled subgoal to previous sub-goals that have not been fully resolved away.
% Do not need to decrease the number of the remaining conditions of the inputclause which introduced the current resovled subgoal.
updatePreDer([],_,[]):-!.
updatePreDer(All, [], All):- !.
updatePreDer([H|Rest], PairsIn, [HNew| RestNew]):-
    H = (Goal, InputClause, SubOld, NextGoal, [RemNum1, RemNum2]),
    RemCondNum is RemNum1 + RemNum2,
    % update the substitutions
    (RemCondNum > 0 ->
            PairsIn =[(_, Subs)|RestPairsNew],
            compose1(Subs, SubOld, SubNew),
            HNew = (Goal, InputClause, SubNew, NextGoal,  [RemNum1, RemNum2]), !;
     RemCondNum = 0 ->
            HNew = H, RestPairsNew = PairsIn),
    updatePreDer(Rest, RestPairsNew, RestNew).

/**********************************************************************************************************************
    resolveEqu(Goals, Derivation, EC, Proof, Theorem, RCostLimit):
            resolve the goals of equalities, after which resolve inequalities.
            When there is a variable, the instantiation choice of an equality is usually fewer than an inequality, so do it first.
    Input:  Goals: the list of subgoals to resolve.
            Derivation: a list of the previous derivation steps. For more infomation, please see updateDeriv.
            EC: the equivalence classes.
            RCostLimit: the limit of the length of the derivations.
    Output: Proof: the record of all derivation steps.
            Theorem: the derived theorem.
************************************************************************************************************************/
resolveEqu([], Proof, _, Proof, [], [], _):-!.
%    findall(E, (member((_,[+[= | Args]],_,_, ))).
resolveEqu([+P], Proof, _, Proof, [], [+P], _):-!.

resolveEqu(_, Evidence, _, [], Evidence, [], RCostLimit):-
    length(Evidence, RDepth),
    RDepth >= RCostLimit, !.        % The current proof depth has not bigger than the limit.

resolveEqu([-[=, X, Y]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),
    equalSub([=, X, Y], EC, Subs),
       % apply the substitution to the rest goal clause.
       subst(Subs, GRest, GoalsNew),
    noloopBack(GoalsNew, Deriv),      % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
     retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),
     CurDerStep = (([-[=, X, Y]| GRest], Subs), (unae, []), GoalsNew, [0, 0]),
     updateDeriv(Deriv, CurDerStep, secondNum, DerivNew),
     resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit).

% resolve inequalities if there is no equalities left in the goal clause.
resolveEqu([-[\=|Args]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    % check if there is no equalities left in the goal clause.
    notin(-[=|_], GRest),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(1))),       % Set the proofStatus as 1, so the first sub-goal will be resolved if it can be.
    equalSub([\=|Args], EC, Subs),    % the inequality is true by appying substitution Subs.
    subst(Subs, GRest, GoalsNew),    % appying that substitution to the rest sub-goals.
    noloopBack(GoalsNew, Deriv),      % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
     retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))),         % Reset the proofStatus flag to the default value 0.
     CurDerStep = (([-[\=|Args]| GRest],Subs), (unae, []), GoalsNew, [0, 0]),
     updateDeriv(Deriv, CurDerStep, secondNum, DerivNew),    % 1 stands for the resolution of non equality predicates.
    resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit). % Resolve the rest goals.

% move inequalities to the end of the negative literals in the goal clause.
resolveEqu([-[\=|Args]| GRest], Deriv, EC, Proof, Evidence, Theorem, RCostLimit):-
    occur(-[=|_], GRest),    % not all of the goal predicates are inequality predicate.
    % move the equality or inequality to the end of the negative subgoals.
    % keep the positive literal in the end if there is one.
    (last(GRest, -[_]) ->
                append(GRest, [-[\=|Args]], GoalsNew);
     last(GRest, +[_]) ->
                 reverse(GRest, [+P|GTail]),
                 reverse([+P| [-[\=|Args]| GTail]], GoalsNew)),
    updateDeriv(Deriv, reorder, DerivNew),    % update the derivation record.
    resolveEqu(GoalsNew, DerivNew, EC, Proof, Evidence, Theorem, RCostLimit).

%% When there the firs sub-goal is irresolvable,
%% return the evidence of the partial proof with [] as the proof and theorem.
%% Notice that only the first subgoal in Goals is guaranteed to be irresolvable. The following subgoals could be resolvable.
resolveEqu(Goals, Deriv, _, [], Evidence, [], _):-
    spec(proofStatus(1)),      % All axioms from the input theory have been tried for resolving the goal.
    Goals \= [],                    % And they all failed in resolving the remaining Goal.
    Goals \= [+_],                    % And it is not a derived assertion
    (Deriv = []-> Evidence = [(Goals, [], [], Goals, [0, 0])];    % record the unprovable goal when no RS have been done.
    Deriv \= []-> Evidence = Deriv),
    retractall(spec(proofStatus(_))), assert(spec(proofStatus(0))).      % The failed proof is output. Reset the proofStatus to the default value 0.


/***************************************************************************************************************
    noloopBack(GoalsCur, Derivations):-
           Check if the current goals is no more complex than a previous goal in its own Proof.
           If yes, return true, otherwise, return false.
    Input:  GoalsCur: the current goal clause.
            Derivations is a list of derivation steps.
            Derivations = [(Goal, InputClause, SubNew, NextGoal, RemCondNum), ....]
****************************************************************************************************************/
noloopBack([], _):- !.    % empty goal clause could not cause a loop.
noloopBack(_, []):- !.
noloopBack(_, Deriv):-         % a loop is found when there is already an empty goal clause.
    member((_, _, _, [], _), Deriv), fail, !.
% The current goal is more complicated than a previous goal if all of the previous subgoals can be resolved with a proposition in the current goal.
noloopBack(GoalsCur, Deriv):-
    % Check for any previous goal PreGoal,
    (forall(member((_, _, _, PreGoal, _), Deriv),
            %there is a subgoal PreSubG which cannot be resolved with any subgoal in the current goal GoalPar.
            setof(PreSubG,
                    (member(-PreSubG, PreGoal),
                     % not resolvable with any current subgoal
                     forall(member(-CurSubG, GoalsCur),
                                unification(PreSubG, CurSubG, [], [], _, _, [_|_]))),
                      _))-> true, !;
     writeLog([nl, write_term('******** Warning: Loop resolution ********'), nl,
            write_term('Current goal is: '), nl, write_term(GoalsCur), nl,
            write_term('The derivation steps are: '), nl,write_term(Deriv), finishLog]),fail).


/***************************************************************************************************************
    traceBackPos(TgtProp, Deriv, NegLit, InputClause, Subs):
            Find the original input clause which introduces the targeted proposition.
    Input:  Deriv is the derivation of a list of the resolution steps. For details, please see DerivIn in updateDeriv.
            Derivation = [(Goal, InputClause, Subs, NextGoal, RemCondNum), ...]
    Output: NegLit is the negative literal which introduces TgtProp.
               ClauseOri: the original input clause of NegProp.
    * InputClause is a Horn clause which has its positive literal as the head.
****************************************************************************************************************/
% Find the input clause which introduces the targeted proposition.
traceBackPos([P|ArgT], Deriv, NegLit, InputClause, Subs):-
    last(Deriv, CurResStep),
    CurResStep = (_, InputClause, Subs,_,_),
    setof(-[P|Arg],
            ( member(-[P|Arg], InputClause),
              unification([P|ArgT], [P|Arg],[],[],_,_,[])),
            [NegLit|_]), !.    % get the original negative literal.

% if it is the first step, then the targeted negative proposition is from preferred structure.
traceBackPos([P|ArgT], [(Goal, _,_,_,_)], NegLit, InputClause, Subs):-
    member(-[P| Argori], Goal),
    unification([P|ArgT], [P| Argori],[],[],_,Subs,[]), !,
    (Goal = [_|[_|_]] ->    % the original goal clause have at least two proposition, then it is a constran axiom from the input theory.
        NegLit = -[P|ArgT], InputClause = Goal;
     Goal = [-_] -> InputClause = [], NegLit= -[P|ArgT]).    % Otherwise, it comes from the preferred structure.

% otherwise, try the ancestors.
traceBackPos(TargProp, Deriv, NegLit, InputClause, Subs):-
    dropTail(Deriv, Ances),    % try the ancestors.
    traceBackPos(TargProp, Ances, NegLit, InputClause, Subs).


/***************************************************************************************************************
    traceBackC(C, Deriv, NegLit, InputClause, Subs):
            Find the original input clause which introduces the targeted constant.
    Input:  C: the target constant, e.g., [c].
            Deriv is the derivation of a list of the resolution steps. For details, please see DerivIn in updateDeriv.
            Derivation = [(Goal, InputClause, Subs, NextGoal, RemCondNum), ...]
    Output: Clause is the source of that constant, which can be a goal clause or a input clause.
    * InputClause is a Horn clause which has its positive literal as the head.
****************************************************************************************************************/
% Find the input clause which introduces the targeted proposition.
traceBackC(C, [([+[P|Args]], [],[],[+[P|Args]],[0,0])], [+[P|Args]]):-
    member(C, Args), !.
traceBackC(C, Deriv, Clause):-
    Deriv = [(Goals,InputCl,_,_,_)| _],
    % Try if c comes from the goal clause over the head of the input clause.
    findall(Prop, (member(-Prop, Goals), occur(C, Prop)), Props),
    (Props \= [], Clause = Goals, !;
     Props = []->
         (% try if c comes from the body of the input clause.
         findall(Prop2, (member(-Prop2, InputCl), occur(C, Prop2)), Props2),
         Props2 \= [], Clause = InputCl, !;
        last(Deriv, GoalLast),
        findall(PropL, (member(-PropL, GoalLast), occur(C, PropL)), Propsl),
        (Propsl \= [], Flag = true;
         Props = []-> Flag = false),
        traceBackCTail(C, Deriv, Flag, Clause))).    % get the original negative literal.

traceBackCTail(_, [], []):- fail, !.

traceBackCTail(C, Deriv, Flag, Output):-
    last(Deriv, (Goals,InputClause,_,_,_)),
    findall(Prop, (member(-Prop, Goals),occur(C, Prop)), Props),
    (Props = [], ( Flag == true ->  InputClause = Output, !; % find the last goal which does not contain the target, so the input clause in this step introduces the target.
                  Flag == false ->
                      dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, false, Output));        % the target constant has gone from the goal clause previously.
    Props \= [],( Flag == true    ->
                    dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, true, Output);            % the target constant has occured.
                  Flag == false ->
                    dropTail(Deriv, Ances), !,    % try the ancestors.
                    traceBackCTail(C, Ances, true, Output))).

/**********************************************************************************************************************
    subDiv(SubsList, Clause, SG):
            Among SubsList, get the substitutions that applied to the goal clause (SG).
    Input: SubsList: a list of substitutions
           Clause: the clause
    Output: SG: the substitutions that applied to the clause (SG).
************************************************************************************************************************/
subDiv([],_,[]):-!.
subDiv(SubsList, Clause, SG):-
    findall(vble(X),
            (member(-[_|Args], Clause),    % omit the head as all variables in the head also occur in the boody in Datalog.
             member(vble(X),Args)),
            GVbles),
    findall((A/B),
            (member((A/B), SubsList),
            member(B, GVbles)),
            SGRaw),
    sort(SGRaw, SG).

/**********************************************************************************************************************
    pairSub(Goal, SubsList, SGPairs):
            get the pairs between a sub-goal and its substitutions that applied to that sub-goal
    Input: SubsList: a list of substitutions
           Goal: the goal clause
    Output: SGPairs=[(-[a,vble(x),vble(y)], [[c]/vble(x), [d]/vble(y)]),...]
************************************************************************************************************************/
pairSub([],_,[]):-!.
pairSub([SubG1| RestG], SubG, [(SubG1, SG1)| PRest]):-
    subDiv(SubG, [SubG1], SG1),
    pairSub(RestG, SubG, PRest).

/**********************************************************************************************************************
    cleanSubMid(Proof, ProofClean): delete the mid substitutions from each RS.
    Input: Proof: a list of resolution steps.
    Output: ProofClean: a list of resolution steps where mid substitutions are deleted.
************************************************************************************************************************/
cleanSubMid([], []):-!.
cleanSubMid([RS| Rest], [RSC| RestC]):-
    RS = (G, InpClause, Sub, GN, Num),
    (Sub = []-> RSC = RS;
     Sub = [_|_]->
    findall(vble(X),
            (member(-[_|Args], InpClause),    % omit the head as all variables in the head also occur in the boody in Datalog.
             member(vble(X), Args)),
            Vbles),
    findall((A/B),
            (member((A/B), Sub),
             member(B, Vbles)),
            NewSubRaw),
    sort(NewSubRaw, NewSub),
    RSC    = (G, InpClause, NewSub, GN, Num)),
    cleanSubMid(Rest, RestC).
