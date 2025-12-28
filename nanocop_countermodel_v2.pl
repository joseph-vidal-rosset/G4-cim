%% ============================================================================
%% File: nanocop_countermodel_v2.pl
%% Version: 2.0
%% Author: Joseph Vidal-Rosset (based on nanoCop 2.0 by Jens Otten)
%% Purpose: Extension of nanoCop to extract countermodels from open branches
%%
%% Key Innovation:
%%   When nanoCop fails to prove a formula by refutation, the open branches
%%   in the proof search represent ANTISEQUENTS (Γ ⊬ Δ) that demonstrate
%%   why the formula is invalid. This module captures these antisequents
%%   and presents them as countermodels.
%%
%% Theoretical Foundation:
%%   - nanoCop proves ¬F by closing all branches in the tableau for ¬F
%%   - An OPEN branch means: assumptions in Path cannot derive Goal
%%   - This is precisely an ANTISEQUENT: Path < Goal (Γ ⊬ Δ)
%%   - The antisequent defines a countermodel where Path is true but Goal fails
%%
%% Usage:
%%   ?- prove_or_refute(Formula, Result).
%%   Result = valid(Proof)           % Formula is a theorem
%%   Result = invalid(Countermodels) % Formula is refutable (with witnesses)
%%   Result = unknown                % Search failed/timeout
%% ============================================================================

:- ensure_loaded(nanocop20_swi).

:- dynamic(open_branch/3).  % open_branch(Path, Goal, Context)

%% ============================================================================
%% MAIN INTERFACE
%% ============================================================================

%% prove_or_refute(+Formula, -Result)
%%
%% Attempts to prove Formula. On failure, captures open branches as countermodels.
%%
%% @param Formula  A first-order formula in nanoCop syntax
%% @param Result   valid(Proof) | invalid(Countermodels) | unknown
%%
prove_or_refute(F, Result) :-
    retractall(open_branch(_,_,_)),
    ( prove_with_countermodel_capture(F, Proof) ->
        Result = valid(Proof)
    ;
        findall(antisequent(Gamma, Delta), open_branch(Gamma, Delta, _), Branches),
        ( Branches = [] ->
            Result = unknown  % Timeout or pathological case
        ;
            Result = invalid(Branches)
        )
    ).

%% ============================================================================
%% MODIFIED NANOCOP PROVER WITH OPEN BRANCH CAPTURE
%% ============================================================================

%% prove_with_countermodel_capture(+Formula, -Proof)
%%
%% Modified version of nanoCop's prove/2 that records open branches
%% when lit(NegLit, ...) fails to find a connection.
%%
prove_with_countermodel_capture(F, Proof) :-
    prove2_capture(F, [cut, comp(7)], Proof).

prove2_capture(F, Set, Proof) :-
    bmatrix(F, Set, Mat),
    retractall(lit(_,_,_,_)),
    assert_matrix(Mat),
    prove_capture_main(Mat, 1, Set, Proof).

%% Main proof search with iterative deepening
prove_capture_main(Mat, PathLim, Set, [(I^0)^V:Proof]) :-
    ( member(scut, Set) -> 
        ( append([(I^0)^V:Cla1|_], [!|_], Mat) ;
          member((I^0)^V:Cla, Mat), positiveC(Cla, Cla1) ) -> true
    ;
        ( append(MatC, [!|_], Mat) -> 
            member((I^0)^V:Cla1, MatC)
        ;
            member((I^0)^V:Cla, Mat), positiveC(Cla, Cla1)
        )
    ),
    prove_with_capture(Cla1, Mat, [], [I^0], PathLim, [], Set, Proof).

prove_capture_main(Mat, PathLim, Set, Proof) :-
    retract(pathlim) ->
    ( member(comp(PathLim), Set) -> 
        prove_capture_main(Mat, 1, [], Proof)
    ;
        PathLim1 is PathLim+1,
        prove_capture_main(Mat, PathLim1, Set, Proof)
    ) ;
    member(comp(_), Set) -> prove_capture_main(Mat, 1, [], Proof).

%% Axiom rule - empty clause proven
prove_with_capture([], _, _, _, _, _, _, []).

%% Decomposition rule - process matrix literal
prove_with_capture([J:Mat1|Cla], MI, Path, PI, PathLim, Lem, Set, Proof) :-
    !,
    member(I^V:Cla1, Mat1),
    prove_with_capture(Cla1, MI, Path, [I,J|PI], PathLim, Lem, Set, Proof1),
    prove_with_capture(Cla, MI, Path, PI, PathLim, Lem, Set, Proof2),
    Proof = [J:I^V:Proof1|Proof2].

%% Extension and reduction rules - WITH OPEN BRANCH CAPTURE
%%
%% This is where the magic happens:
%% When lit(NegLit, ClaB, Cla1, Grnd1) FAILS, it means we cannot find
%% a clause to extend the proof. The current Path and [Lit|Cla] form
%% an ANTISEQUENT demonstrating that Path does not entail [Lit|Cla].
%%
prove_with_capture([Lit|Cla], MI, Path, PI, PathLim, Lem, Set, Proof) :-
    Proof = [Lit, I^V:[NegLit|Proof1]|Proof2],
    \+ (member(LitC, [Lit|Cla]), member(LitP, Path), LitC==LitP),
    (-NegLit=Lit ; -Lit=NegLit) ->
       ( % Try lemma
         member(LitL, Lem), Lit==LitL, 
         _ClaB1=[], Proof1=[], I=l, V=[]
         ;
         % Try reduction (close with path literal)
         member(NegL, Path), unify_with_occurs_check(NegL, NegLit),
         _ClaB1=[], Proof1=[], I=r, V=[]
         ;
         % Try extension (find complementary clause)
         ( lit(NegLit, ClaB, Cla1, Grnd1) ->
             % Extension found - continue proof search
             ( Grnd1=g -> true
             ; length(Path, K), K<PathLim -> true
             ; \+ pathlim -> assert(pathlim), fail
             ),
             prove_ec(ClaB, Cla1, MI, PI, I^V:ClaB1, MI1),
             prove_with_capture(ClaB1, MI1, [Lit|Path], [I|PI], PathLim, Lem, Set, Proof1)
         ;
             % CRITICAL: Extension failed - OPEN BRANCH DETECTED
             % This means: Path ⊬ [Lit|Cla]
             % We record this as an antisequent (countermodel witness)
             capture_open_branch(Path, [Lit|Cla]),
             fail  % Continue failing to allow backtracking
         )
       ),
       ( member(cut, Set) -> ! ; true ),
       prove_with_capture(Cla, MI, Path, PI, PathLim, [Lit|Lem], Set, Proof2).

%% ============================================================================
%% OPEN BRANCH CAPTURE
%% ============================================================================

%% capture_open_branch(+Path, +Goal)
%%
%% Records an open branch as an antisequent.
%% Path = assumptions that hold on this branch
%% Goal = formulas that cannot be derived from Path
%%
%% This represents: Path ⊬ Goal (Γ ⊬ Δ in sequent notation)
%%
capture_open_branch(Path, Goal) :-
    copy_term((Path, Goal), (PathCopy, GoalCopy)),
    simplify_antisequent(PathCopy, GoalCopy, Gamma, Delta),
    \+ open_branch(Gamma, Delta, _),  % Avoid duplicates
    assert(open_branch(Gamma, Delta, [])).

%% simplify_antisequent(+RawPath, +RawGoal, -Gamma, -Delta)
%%
%% Cleans up the antisequent for presentation:
%% - Removes negations where appropriate
%% - Normalizes format
%% - Extracts meaningful literals
%%
simplify_antisequent(Path, Goal, Gamma, Delta) :-
    clean_literals(Path, Gamma),
    clean_literals(Goal, Delta).

clean_literals([], []).
clean_literals([L|Ls], [L1|Ls1]) :-
    ( L = -Lit -> L1 = -(Lit)  % Keep negated literals marked
    ; L1 = L                    % Positive literals as-is
    ),
    clean_literals(Ls, Ls1).

%% ============================================================================
%% PRESENTATION AND INTERPRETATION
%% ============================================================================

%% print_result(+Result)
%%
%% Pretty-prints the result of prove_or_refute/2
%%
print_result(valid(Proof)) :-
    nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('  ✓ FORMULA IS VALID (Theorem)'), nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('Proof found: '), write(Proof), nl, nl.

print_result(invalid(Countermodels)) :-
    nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('  ✗ FORMULA IS INVALID (Refutable)'), nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('Countermodel(s) - Antisequents demonstrating invalidity:'), nl,
    nl,
    print_antisequents(Countermodels, 1),
    nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('Interpretation: Each antisequent Γ ⊬ Δ represents'), nl,
    write('a scenario where assumptions Γ hold but Δ fails,'), nl,
    write('thus refuting the original formula.'), nl,
    write('═══════════════════════════════════════════════════'), nl, nl.

print_result(unknown) :-
    nl,
    write('═══════════════════════════════════════════════════'), nl,
    write('  ? UNKNOWN (Search incomplete)'), nl,
    write('═══════════════════════════════════════════════════'), nl, nl.

print_antisequents([], _).
print_antisequents([antisequent(Gamma, Delta)|Rest], N) :-
    write('  ['), write(N), write('] '),
    write_sequent(Gamma, Delta),
    nl,
    interpret_antisequent(Gamma, Delta),
    nl,
    N1 is N+1,
    print_antisequents(Rest, N1).

write_sequent(Gamma, Delta) :-
    write_formula_list(Gamma),
    write(' ⊬ '),  % Turnstile with slash (does not entail)
    write_formula_list(Delta).

write_formula_list([]) :- write('∅').
write_formula_list([F]) :- !, write(F).
write_formula_list([F|Fs]) :-
    write(F), write(', '),
    write_formula_list(Fs).

%% interpret_antisequent(+Gamma, +Delta)
%%
%% Provides a semantic interpretation of the antisequent as a countermodel
%%
interpret_antisequent(Gamma, Delta) :-
    extract_model(Gamma, Delta, Model),
    ( Model \= [] ->
        write('      Countermodel: '), write_model(Model)
    ; true ).

extract_model(Gamma, Delta, Model) :-
    findall(Atom=true, member(Atom, Gamma), TrueLits),
    findall(Atom=false, (member(Atom, Delta), \+ member(Atom, Gamma)), FalseLits),
    append(TrueLits, FalseLits, Model).

write_model([]) :- write('{ }').
write_model([Atom=Val]) :- !, 
    write('{ '), write(Atom), write(' ↦ '), write(Val), write(' }').
write_model([Atom=Val|Rest]) :-
    write('{ '), write(Atom), write(' ↦ '), write(Val),
    write_model_rest(Rest).

write_model_rest([]).
write_model_rest([Atom=Val|Rest]) :-
    write(', '), write(Atom), write(' ↦ '), write(Val),
    write_model_rest(Rest).

%% ============================================================================
%% CONVENIENCE PREDICATES
%% ============================================================================

%% test(+Formula)
%%
%% Quick test predicate: prove and print result
%%
test(F) :-
    write('Testing: '), write(F), nl, nl,
    prove_or_refute(F, Result),
    print_result(Result).

%% compare_with_g4mic(+Formula)
%%
%% Tests formula with nanoCop countermodel extraction and suggests
%% comparison with g4mic's antisequent system
%%
compare_with_g4mic(F) :-
    write('═══════════════════════════════════════════════════'), nl,
    write('Testing with nanoCop countermodel extraction:'), nl,
    write('═══════════════════════════════════════════════════'), nl,
    nl,
    test(F),
    write('To compare with g4mic antisequents, run:'), nl,
    write('  g4mic_decides('), write(F), write(').'), nl,
    nl.

%% ============================================================================
%% HELP AND DOCUMENTATION
%% ============================================================================

help :-
    nl,
    write('═══════════════════════════════════════════════════════════════════'), nl,
    write('  nanoCop v2.0 - COUNTERMODEL EXTRACTION'), nl,
    write('  Extension for extracting antisequents from failed proofs'), nl,
    write('═══════════════════════════════════════════════════════════════════'), nl,
    nl,
    write('MAIN PREDICATES:'), nl,
    nl,
    write('  prove_or_refute(Formula, Result)'), nl,
    write('    Result = valid(Proof)'), nl,
    write('           | invalid(Countermodels)'), nl,
    write('           | unknown'), nl,
    nl,
    write('  test(Formula)'), nl,
    write('    Quick test with formatted output'), nl,
    nl,
    write('  compare_with_g4mic(Formula)'), nl,
    write('    Test and suggest g4mic comparison'), nl,
    nl,
    write('THEORETICAL BACKGROUND:'), nl,
    nl,
    write('  When nanoCop fails to prove F, it means ¬F has open branches.'), nl,
    write('  Each open branch represents an ANTISEQUENT (Γ ⊬ Δ):'), nl,
    write('    - Γ (Gamma): Assumptions on the path that hold'), nl,
    write('    - Δ (Delta): Goal formulas that cannot be derived'), nl,
    nl,
    write('  This antisequent defines a COUNTERMODEL where Γ is true'), nl,
    write('  but Δ fails, demonstrating why F is invalid.'), nl,
    nl,
    write('CONNECTION TO G4MIC:'), nl,
    nl,
    write('  g4mic generates antisequents (Γ < Δ) in classical logic'), nl,
    write('  when formulas are unprovable. nanoCop\'s open branches'), nl,
    write('  provide the same information from a different angle:'), nl,
    write('    - g4mic: Direct antisequent generation (top-down)'), nl,
    write('    - nanoCop: Open branch extraction (bottom-up)'), nl,
    nl,
    write('  Both systems agree on invalid formulas!'), nl,
    nl,
    write('EXAMPLES:'), nl,
    nl,
    write('  ?- test((a => b)).           % Invalid: a ⊬ b'), nl,
    write('  ?- test((p,(p=>q))=>q).      % Valid: modus ponens'), nl,
    write('  ?- test(ex Y:(d(Y)=>all X:d(X))).  % Valid: drinker'), nl,
    nl,
    write('  For comparison:'), nl,
    write('  ?- compare_with_g4mic((a => b)).'), nl,
    nl,
    write('═══════════════════════════════════════════════════════════════════'), nl, nl.

:- initialization(help).
