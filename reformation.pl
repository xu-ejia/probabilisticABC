/*
  This file contains the functions/predicates of generating reformation repair plans.
  Update Date: 13.08.2022
*/

/*********************************************************************************************************************************
    weakenVble, mergePlan,
            reformation relevant.
**********************************************************************************************************************************/

% reformation repair plans generated based on a pair of unified arguments
weakenVble(TargLit, TargCl, Suffs, CCP, VCP, ABox, TBox, RepPlan):-
    spec(heuris(Heuristics)),
    spec(protList(ProtectedList)),
    notEss2suff(Suffs, TargCl), !,    % TODO: or being sufficient by having the variable being bound with one constant
    (notin(noRename, Heuristics),
     member(C, CCP),
     (occur(C, ProtectedList)-> notUnique(C, ABox, TBox);  true),  %  F occurs more than onces.
     RepPlan = rename(C, TargLit, TargCl);

    notin(noVabWeaken, Heuristics),
    member((V1, OrigCons), VCP),
    % Heuristic1: check that there must be more than one argument in the target rule. Otherwise, the rule would contain no variables after weaken one to a constant.
    setof(vble(V),
                ((member(+[_|Args], TargCl); member(-[_|Args], TargCl)),
                member(vble(V), Args)),
            [_|[_|_]]),
    % generate the constant
    % dummyTerm(OrigCons, ABox, NewCons),
    RepPlan = weaken(V1, [OrigCons], TargCl)).

% the input clause is essential, then get all the essential substitutions of its
weakenVble(_, TargCl, Suffs, _, VCP, _, RepPlan):-
    spec(heuris(Heuristics)),
    notin(noVabWeaken, Heuristics),
    essSubs(Suffs, TargCl, SubstList),
    member((_, V1), VCP),
    % if the variable is bound to one constant in the proofs of the sufficiency where the input clause is essential.
    setof(C,    (member(Subst, SubstList),
                subst(Subst, V1, C)),
        [CSuff]),
    % then the variable can be weaken to that constant so it won't introduce insufficiency.
    RepPlan = weaken(V1, CSuff, TargCl).

/**********************************************************************************************************************
   mergePlan(Mismatches, [PG| ArgsG], TargetLit, TargCl, ABox, TBox, RepPlan, TargCls)
        Generate a repair plan of merge predicate
   Input:    Mismatches: the mismatched predicate and/or arguments between the goal argument and the target argument
            TargetLit: the target literal whose predicate and/or argument will be merged as the goal's
            TargCl: the clause where TargetLit comes
            TABox, TBox: the object KG
   Output:     RepPlan: a repair plan of merge predicate
               TargCls: all the clauses that contains the predicate to be merged.
************************************************************************************************************************/
mergePlan(Mismatches, [PG| ArgsG], TargetLit, TargCl, ABox, TBox, RepPlan, TargCls):-
    Mismatches = (predicate, ArgDiff),
    spec(protList(ProtectedList)),
    flatten(ProtectedList, ProtectedListF),
    % Get the predicate in the targeted literal
    prop(TargetLit, [PT| ArgsT]),
    length(ArgsT, ArityT),
    length(ArgsG, ArityG),
    (intersection([PT, +[PT|_], -[PT|_]], ProtectedListF, [])->
        (ArityT > ArityG->
            % make PG's arity ArityT, and replace all PG with PR
            RepPlan = merge(PT, PG, ArgsG, dec);
        ArgDiff = []->
            % replace all PG with PR
            RepPlan = merge(PT, PG, ArgsG, equ);
        ArityT < ArityG->
            % increase PG's arity by adding ArgDiff and then replace all PG with PR
            RepPlan = merge(PT, PG, ArgDiff, inc)),
        findall(Cl, ((member(Cl, ABox); member(Cl, TBox)), (member(+[PT|_], Cl); member(-[PT|_], Cl))), TargCls);
    % When PG is under protected, only refom the literal not all accurance of PG,
    % if that Literal is not the only occurance of PG.
    intersection([PT, +[PT|_], -[PT|_]], ProtectedListF, Int), Int =[_|_]->
    notUnique(PT, ABox, TBox),  % reform that literal won't make PG gone.
     (ArityT > ArityG->
            % make PG's arity Arity, and rename the PG with PR
            RepPlan = rename(PT, PG, ArgsG, TargetLit, TargCl, dec);
      ArgDiff = []->
            % replace all PG with PR
            RepPlan = rename(PT, PG, ArgsG, TargetLit, TargCl, equ);
      ArityT < ArityG->
            % increase PG's arity by adding ArgDiff and then rename the PG with PT
            RepPlan = rename(PT, PG, ArgDiff, TargetLit, TargCl, inc)),
    TargCls = [TargCl]).

% Only rename the instance of the mismatched predicate in the target clause.
renamePred(Mismatches, [PG| _], TargetLit, TargCl, RepPlan, [TargCl]):-
    Mismatches = (predicate, []),
    appLiteral(TargetLit, [replacePos, 1, 0, PG], LitNew),
    appLiteral(TargetLit, [nth0, 1, 0], PT),
    replace(TargetLit, LitNew, TargCl, ClNew),
    RepPlan = rename(PT, PG, TargCl, ClNew).

% generate reformation repair plan when the predicate is matched but arguments.
renameArgs(Mismatches, Nth, Evi, SuffGoals, MisNum, ABox, TBox, RepPlan, TargCls):-
    Mismatches = [_|_],
    spec(protList(ProtectedList)),
    writeLog([nl,write_term('--renameArgs: Mismatches:'),nl,write_term(Mismatches),nl,
      write_term(ProtectedList),nl,finishLog]),

     setof([(COrig, CTarget, C1Cl), C1Cl],
                (member((C1, C2),Mismatches),
                nth0(Nth, [C1, C2], COrig),    % Get the target constant.
                delete([C1, C2], COrig, [CTarget]),    % rename Corig by CTarget.
                COrig = [CC],
                notin(CC, ProtectedList),
                traceBackC(COrig, Evi, C1Cl),
                % occur(+_, C1Cl),
                (member(C1Cl, ABox); member(C1Cl, TBox)),    % it is an axiom from the theory not the preferred structure.
                notin(C1Cl, ProtectedList),
                asserProCheck(C1Cl, ProtectedList),
                notEss2suff(SuffGoals, C1Cl)),
                RS),
    length(RS, MisNum),     % have found the clause of all mismached pairs
    transposeF(RS, [MisPairs, TargCls]),
    RepPlan = rename(MisPairs),
    writeLog([nl,write_term('--renameArgs: RepPlanS:'),nl,write_term(RepPlan),nl,
        nl,write_term('--renameArgs: TargCls:'),nl,write_term(TargCls),nl, finishLog]).

% generate reformation repair plan of extend a constant to a variable when the predicate is matched but arguments.
extCons2Vble(Mismatches, Nth, Evi, _, MisNum, ABox, TBox, RepPlan, TargCls):-
    Mismatches = [_|_],
    spec(protList(ProtectedList)),
    setof([(COrig, NewVble, C1Cl), C1Cl],
                (member((C1, C2),Mismatches),
                nth0(Nth, [C1, C2], COrig),    % Get the target constant.
                notin(COrig, ProtectedList),
                traceBackC(COrig, Evi, C1Cl),
                member(-_, C1Cl),        % it is a rule
                (member(C1Cl, ABox); member(C1Cl, TBox)),    % it is an axiom from the theory not the preferred structure.
                notin(C1Cl, ProtectedList),
                    % get the list of variables in the input clause.
                findall(X,
                        ( (member(+[_| Arg], C1Cl);
                           member(-[_| Arg], C1Cl)),
                          member(vble(X), Arg)),
                        AvoidList),
                getNewVble([COrig], AvoidList, [(COrig, NewVble)], _)),
                RS),
     length(RS, MisNum),     % have found the clause of all mismached pairs
    transposeF(RS, [MisPairs, TargCls]),
    RepPlan = extC2V(MisPairs),
    writeLog([nl,write_term('--extC2V: RepPlanS:'),nl,write_term(RepPlan),nl,
        nl,write_term('--extC2V: TargCls:'),nl,write_term(TargCls),nl, finishLog]).


/*********************************************************************************************************************************
    reformUnblock(UnresSubGoals, EC, Evi, SuffGoals, ABox, TBox, Output):
            unblock a proof by reformation
    Input:  UnresSubGoals: a list of unresolvable subgoals.
            EC: the equivalence classes.
            Evi: the evidence of the proof to unblock
            ClUsed: the input clauses that constitute Evi
            ABox, TBox: the KG.
            SubsSuff: a list of wanted substitution lists, e.g., [[[a]/vble(x),[a]/vble(y)], [[b]/vble(x),[c]/vble(y)]]
    Output: The list of repair information: [[RepPlans, ClS], [RepPlans2, ClS2], ....]
               where [RepPlans, ClS] = [ass2rule(Axiom, NewRule),...]
               All repair plans in the list need to be applied to unblock a proof.
            ClS: the list of clauses to change by applying RepPlans.
**********************************************************************************************************************************/
reformUnblock([], _, _, _, _, _, []).
reformUnblock([H|T], Evi, ClUsed, SuffGoals, ABox, TBox, [HOut| RestOut]):-
        refUnblock(H, Evi, ClUsed, SuffGoals, ABox, TBox, HOut),
        reformUnblock(T, Evi, ClUsed, SuffGoals, ABox, TBox, RestOut).

refUnblock(-[PG| ArgsG],  Evi, ClUsed, SuffGoals, ABox, TBox, [RepPlan, TargCls]):-
    % Get the original negative literal and its clause where -GTarg comes from.
    traceBackPos([PG| ArgsG], Evi, InpLi, InpCl2, _),    % InpCl2 = [] if it comes from the preferred structure.
    spec(protList(ProtectedList)),
    writeLog([nl,write_term('Reformation: targeted evidence'),nl,write_term([PG| ArgsG]), finishLog]),

    setof( (Axiom, [+[PT|ArgsT]], Mismatches, MisNum, MisPairPos, Proof),
            ((member(Axiom, ABox); member(Axiom, TBox)),
             \+member(Axiom, ClUsed),    % the clause that has been used in the proof should not be a candidate to change for resolving the remaining sub-goal, otherwise, the evidence will be broken.
             %occur(-_, Rule), % it is possible to merge an assertion's predicate with the goal's predicate
             slRL(Axiom, ABox, TBox, Proof, [], [+[PT|ArgsT]]),
             % heuristics:  the rule whose head predicate is same with the goal predicate;
             % or only choose the rule whose arguments overlaps goal's arguments.
             (PT = PG->    argsMis(ArgsG, ArgsT, Mismatches, MisPairPos),
                         length(Mismatches, MisNum);
             PT \= PG-> diff(ArgsG, ArgsT, ArgDiff),     % TODO:consider variables in ArgsG
                        Mismatches = (predicate, ArgDiff),
                        length(ArgDiff, MisNum),
                        MisPairPos = [])),
            Cand),
    writeLog([nl,write_term('--------Reformation Candidates------'),nl, write_term(Cand), finishLog]),
    member((Axiom, [+[PT|ArgsT]], Mismatches, MisNum, MisPairPos, ProofRest), Cand),
    writeLog([nl,write_term('---------------Axiom is 1  '),write_term(Axiom), finishLog]),
    writeLog([nl,write_term('---------------Mismatches is 1  '),write_term(Mismatches), finishLog]),

    spec(heuris(Heuristics)),
    (% if the irresolvable sub-goal is not from the preferred structure, reform the sub-goal
        % Or if the Axiom is not under protected, reform it
        (notin(noRename, Heuristics), notin(Axiom, ProtectedList),
            Axiom = [+Head|_],
            (mergePlan(Mismatches, [PG| ArgsG], +Head, Axiom, ABox, TBox, RepPlan, TargCls);
            renamePred(Mismatches, [PG| ArgsG], +Head, Axiom, RepPlan, TargCls);
            renameArgs(Mismatches, 1, ProofRest, SuffGoals, MisNum, ABox, TBox, RepPlan, TargCls)));
        (InpCl2 \= [], notin(InpCl2, ProtectedList),
                (% generate repair plan of merge(PP, PT, ArgDiff, inc) or rename(PP, PT, ArityT, TargetLit, TargCl, dec/inc).
                notin(noRename, Heuristics),
                (mergePlan(Mismatches, [PT|ArgsT], InpLi, InpCl2, ABox, TBox, RepPlan, TargCls);
                renamePred(Mismatches, [PT|ArgsT], InpLi, InpCl2, RepPlan, TargCls);
                renameArgs(Mismatches, 0, Evi, SuffGoals, MisNum, ABox, TBox, RepPlan, TargCls));
                extCons2Vble(Mismatches, 0, Evi, _, MisNum, ABox, TBox, RepPlan, TargCls)))).
