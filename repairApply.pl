:-[util].
/*
  This file contains the functions/predicates of applying repair plans to the input theory.
  Update Date: 13.08.2022
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%     APPLY   REPAIR   PLANS    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**********************************************************************************************************************
    appRepair(RsPlans, ABox, TBox, MainPath): apply the repair plans to the KG.
    Input:  RepPlansStr: a string of repair plans to be applied.
            ABox: the ABox to which RsPlans will be applied.
            TBox: the TBox to which RsPlans will be applied.
            MainPath: the main directory that contains the original KG, PS and Heuristics
    Output: Write output data into files respectively.
***********************************************************************************************************************/
main(RepPlansStr, TripleDir, RuleDir, HPath, RepTripleDir, RepRuleDir, HPathNew):-
    % get the inputs: the banned and applied repairs; heuristics and the proofs of sufficiencies and insufficiencies
    init([TripleDir, RuleDir],  [ABox, TBox], HPath),
    spec(rsb(RsBanIn)),
    spec(rsa(RsList)),
    (term_string([_, (RepPlans,_), _], RepPlansStr), !; term_string(RepPlans, RepPlansStr)),
    appRepair(RepPlans, ABox, TBox, RsBanIn, ABoxOut, TBoxOut, RsBanOut, [], RsAppCur)->
    /*get_time(S), term_string(S, SS),
      string_concat(SS, '.txt', SSF),
      open(SSF, write, StreamSS),
      write(StreamSS, RepPlans),nl(StreamSS),
      writeAll(StreamSS, ABoxOut),
      close(StreamSS), */
    (ABox = ABoxOut, TBox = TBoxOut ->
      print('No changes after applying repair palns: '), !, print(RepPlans),nl,print('fail'),
      open(HPathNew, write, StreamOutH),
      append(RepPlans, RsBanIn, RsBanOut),
      writeAll(StreamOutH, [RsBanOut, [], 0]),
      close(StreamOutH);
      print(ABox),
      print(ABoxOut),
      print('Finish applying repair palns: '), print(RepPlans), nl,print('success'),
      open(RepTripleDir, write, StreamOutABox),
      writeAll(StreamOutABox, ABoxOut), close(StreamOutABox),

      open(RepRuleDir, write, StreamOutRule),
      writeAll(StreamOutRule, TBoxOut), close(StreamOutRule),

      open(HPathNew, write, StreamOutH),
      append(RsList, RsAppCur, RepApplied),
      length(RepApplied, RepAppLen),
      writeAll(StreamOutH, [RsBanOut, RepApplied, RepAppLen]),
      close(StreamOutH)).


appRepair([], ABox, TBox, RsBan, ABox, TBox, RsBan, RsApplied, RsApplied):-!,
    writeLog([nl, write_term('-------- Finish applying repair plans.'), nl, finishLog]).

appRepair([Rs1|Rest], ABox, TBox, RsBanIn, ABoxOut, TBoxOut, RsBanOut, RsAppIn, RsAppOut):-
    appRepair(Rs1, ABox, TBox, RsBanIn, ABoxTem, TBoxTem, RsBanTem),
    verifyRules(TBoxTem, Rs1, RsBanTem, RsBanTem2, Result),
    (Result = 'success' ->
        appRepair(Rest, ABoxTem, TBoxTem, RsBanTem2, ABoxOut, TBoxOut, RsBanOut, [Rs1|RsAppIn], RsAppOut), !;
    Result = 'fail' -> % update banned repairPlan
        appRepair(Rest, ABox, TBox, [Rs1| RsBanIn], ABoxOut, TBoxOut, RsBanOut, RsAppIn, RsAppOut)).



%% Belief revision: delete unwanted clauses from the original Theory.
appRepair(delete(Clause), ABox, TBox, RsBan, ABoxN, TBoxN, [ expand(Clause)|RsBan]):-
    delete(ABox, Clause, ABoxN),
    delete(TBox, Clause, TBoxN), !.

appRepair(dele_pre(RulePairs), ABox, TBox, RsBan, ABox, TBoxN, [add_pre(RulePairs)|RsBan]):-
    replaceS(RulePairs, TBox, TBoxN),!.

%% add a new triples
appRepair(expand(Clause), ABox, TBox, RsBan, ABoxN, TBoxN, [delete(Clause)| RsBan]):- !,
    Clause = [+_] -> sort([Clause| ABox], ABoxN), TBoxN = TBox;
    member(-_, Clause), sort([Clause| TBox], TBoxN), ABoxN = ABox.

appRepair(analogy(_, NewRule), ABox, TBox, RsBan, ABox, TBoxN, [delete(NewRule)|RsBan]):- !,
    sort([NewRule| TBox], TBoxN).

%% turn an old assertion to a new rule
appRepair(ass2rule(Triple, NewRule), ABox, TBox, RsBan, ABoxN, TBoxN, RsBan):-
    delete(ABox, Triple, ABoxN),
    sort([NewRule|TBox], TBoxN), !.

%% add a new precondition to a rule
appRepair(add_pre(NewPrec, Rule), ABox, TBox, RsBan, ABox, TBoxN, [dele_pre(NewPrec, Rule)| RsBan]):-
    sort([NewPrec| Rule], RuleNew),    % sort the clause where the head will be placed as the first literal.
    replaceS(Rule, RuleNew, TBox, TBoxN),!.


%% Apply repair which increase the arity of P by 1, and give distinguished constants to propositions Pro1 and Pro2: arityInc([P|Args]).
%% The new arguments should BLOCK the targeted unwanted unification in Proof.
%% The input theory does not include propositions in preferred structure(PS).
%% Therefore, arityInc which blocks the unification of a proposition from PS and a input proposition will fail.
appRepair(arityInc(P, TargetL, TargetCl, _, PairCl), ABox, TBox, RsBan, ABoxN, TBoxN, RsBanNew):-
    % collect the existing dummy terms in the input theory.
    findall(Num, (  (member(+[P| Args], ABox);
                    member(+[P| Args], TBox);
                    member(-[P| Args], TBox)),
                member([C], Args),
                string_concat('dummy_Normal', Num, C)),
            OldSer),
       sort(OldSer,  Sorted),

    % get dummy terms
    dummyTermArityInc(Sorted, DefCons, UniqCons),

    % Add unique constant/default constant to the targeted propositions and update them in the theory.
    % Heuristic6: When there are multiple occurrences of predicate, allocate them with same new argument while applying arity increment.
    findall((TLit, TLNew),
                (member(TLit, TargetCl),
                (TLit = +[P|_]; TLit = -[P|_]),
                appLiteral(TLit, [append, 0, [[UniqCons]]], TLNew)),
            TPairLis),

    replaceS(TPairLis, TargetCl, ClNew),
    % Get the desired arity of P, to avoid repeated arity increment in the following process.
    appLiteral(TargetL, [length, 0, PosNewArg]),
    RsBan2 = [delete(ClNew), deleArg(P, PosNewArg)],
    append(RsBan2, RsBan, RsBanNew),            % Heuristic: do not delete the unique instantce

    findall((Lit, LNew),
                (member(Lit, PairCl),
                (Lit = +[P|_]; Lit = -[P|_]),
                appLiteral(Lit, [append, 0, [[DefCons]]], LNew)),
            PairLis),
    replaceS(PairLis, PairCl, PairClNew),

    replaceS([(TargetCl, ClNew), (PairCl, PairClNew)], ABox, ABoxN1),
    replaceS([(TargetCl, ClNew), (PairCl, PairClNew)], TBox, TBoxN1),

    % Add the default constant/independent variables to all occurrences of P,
    % and get the list of targeting propagated predicates, which occur in a rule together with P.
    propArityInc([(P,1,PosNewArg)], ABoxN1, ABoxN, [[DefCons]]),
    propArityInc([(P,1,PosNewArg)], TBoxN1, TBoxN, [[DefCons]]).


%% Apply weaken a variable vble(X) to a constant.
appRepair(weaken(vble(X), TargConLists, TargCl), ABox, TBox, RsBan, ABox, TBoxN, [extC2V(TargCons)| RsBan]):-
    sort(TargConLists, [OrigCons|_]),
    append(ABox, TBox, TheoryIn),
    dummyTerm(OrigCons, TheoryIn, TargCons),
    appEach(TargCl, [appLiteral, [replace, 2, vble(X), TargCons]], ClNew),
    replaceS(TargCl, ClNew, TBox, TBoxN), !.

appRepair(extC2V(X), ABox, TBox, RsBanIn, ABox, TBoxN, RsBanOut):-
    appRepair(rename(X), TBox, RsBanIn, TBoxN, RsBanOut).


%% Apply rename an item F which is either a predicate or a constant.
%% Rename includes blocks the unification of a proposition from PS and a input proposition.
%% Rename the Item in either side of the unification except the one from the preferred structure.
appRepair(rename(F, TargetL, TargetCl), ABox, TBox, RsBanIn, ABoxN, TBoxN, RsBanOut):-
    length(TargetCl, 1)->
        appRepair2(rename(F, TargetL, TargetCl), ABox, RsBanIn, ABoxN, RsBanOut),
        TBoxN = TBox, !;
        appRepair2(rename(F, TargetL, TargetCl), TBox, RsBanIn, TBoxN, RsBanOut),
        ABox = ABoxN.


appRepair(rename(_, _, InpClOld, ClNew), ABox, TBox, RsBan, ABoxN, TBoxN, RsBan):-
    replaceS(InpClOld, ClNew, ABox, ABoxN),
    replaceS(InpClOld, ClNew, TBox, TBoxN).

appRepair(rename(POld, PNew, Arity, LitOld, InpClOld, Opt), ABox, TBox, RsBan, ABoxN, TBoxN, RsBan):-
    appLiteral(LitOld, [mergeProp, 0, POld, PNew, Arity, Opt], LitNew),
    replaceS(LitOld, LitNew, InpClOld, InpClNew),
    replaceS(InpClOld, InpClNew, ABox, ABoxN),
    replaceS(InpClOld, InpClNew, TBox, TBoxN).


% rename the constant Cold with CNew in clause ClOld.
appRepair(rename(RenameList), ABox, TBox, RsBan, ABoxN, TBoxN, RsBan):-
    appAll(appRename, RenameList, [ABox], ABoxN, 1),
    appAll(appRename, RenameList, [TBox], TBoxN, 1).

% merge by make all F1's arity to be Arity, and then replacing all F1 with F2.
appRepair(merge(POld, PNew, ArgDiff, Op), ABox, TBox, RsBan, ABoxN, TBoxN, RsBan):-
    % replace all F1 with F2 at each proposition
    appEach(ABox, [appEach, [appLiteral, [mergeProp, 0, POld, PNew, ArgDiff, Op]]], ABoxTem),
    appEach(ABoxTem, [sort], ABoxTem2),    % remove duplicate literals at each axiom.
    sort(ABoxTem2, ABoxN),
    appEach(TBox, [appEach, [appLiteral, [mergeProp, 0, POld, PNew, ArgDiff, Op]]], TBoxTem),
    appEach(TBoxTem, [sort], TBoxTem2),    % remove duplicate literals at each axiom.
    sort(TBoxTem2, TBoxN).


appRename((COld, CNew, ClOld), TheoryIn, TheoryOut):-
    appEach(ClOld, [appLiteral, [replace, 2, COld, CNew]], ClNew),
    replaceS(ClOld, ClNew, TheoryIn, TheoryOut).


appRepair2(rename(F, TargetL, TargetCl), TheoryIn, RsBanIn, TheoryOut, RsBanOut):-
    dummyTerm(F, TheoryIn, FNew),
    spec(protList(ProtectedList)),
    appLiteral(TargetL, [nth0, 1, Ith, F]),    % Get the position of the original argument vble(X).
    appLiteral(TargetL, [replacePos, 1, Ith, FNew], LitNew),
    replaceS(TargetL, LitNew, TargetCl, ClNew),
    orderAxiom(ClNew, ClNewSorted),
    replaceS(TargetCl, ClNewSorted, TheoryIn, TheoryOut),
    (OccF == 0, occur(F, ProtectedList)->

     OccF < 2, occur(F,ProtectedList)->
                 RsBanOut = [rename(F)| RsBanIn], writeLog([nl, write_term('******** Warning2 do not apply:'),
                 write_term(rename(F)),nl, write_term(' more.'), nl, finishLog]),!;     % do not rename F further
     RsBanOut = RsBanIn, writeLog([nl, write_term('******** Finish renaming.'),nl, finishLog]),!).


/**********************************************************************************************************************
    verifyRules(TBox, RepPlan, RsBanIn, Result):
            verify whether the repair plan fails constraints of rules. If yes, add RepPlan to RsBanIn.
    Input:  TBox: the resulting rules after applying the repair plan.
            RepPlan: the applied repair plan.
            RsBanIn: the banned list of repair plans.
    Output: RsBanOut: the revised banned list of repair plans.
            Result: fail/success in the verification
***********************************************************************************************************************/
% no orphan variable allowed
verifyRules([], _, RsBan, RsBan, 'success'):-!.
verifyRules(TBox, RepPlan, RsBanIn, [RepPlan|RsBanIn], 'fail'):-
    %  orphan Vb
    appEach(TBox, [orphanVb], Ophans),  % X = [[],[],(AxiomOphan, Ophans),[]...]
    sort(Ophans, OpOrdered), % remove duplicates.
    % check that there should not be any axiom with orphan variable.
    flatten(OpOrdered, [_|_]).


% Heuristic4: no mirror rule is allowed
verifyRules(TBox, RepPlan, RsBanIn, [RepPlan|RsBanIn], 'fail'):-
    setof([+Y,-X], (member([+X,-Y], TBox), member([+Y,-X], TBox)), _).

% Finish the verification.
verifyRules(_, _, RsBan, RsBan, 'success').
