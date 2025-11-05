% =========================================================================
% UNIFIED OPTIMIZED DRIVER: PATTERN DETECTION + 2-PASS STRATEGY
% Version with native G4 sequent syntax [Premises] > [Conclusion]
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- [i_operators].
:- [ii_substitutions].
:- [iii_g4_prover].
:- [iv_sequent_calculus_printer].
:- [v_common_nd_printing].
:- [vi_nd_flag_style].
:- [vii_nd_tree_style].
:- [viii_latex_utilities].
:- [ix_logic_level_detection].
:- [x_validation_warnings].
:- [xi_tests_pelletier].
:- [xii_theorems_tests].
:- [xiii_sequents_tests_prop].
:- [xiv_sequents_tests_fol].

% =========================================================================
% STARTUP BANNER
% =========================================================================

:- initialization(show_banner).

show_banner :-
    nl,
    write('╔═══════════════════════════════════════════════════════════════╗'), nl,
    write('║                   G4 F.O.L. PROVER  -  1.0                    ║'), nl,
    write('║            Minimal,  Intuitionistic and Classical Logic       ║'), nl,
    write('╚═══════════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('  help. to get help'), nl,
    write('  quickref. =  quick reference '), nl,
    write('  examples. to see examples'), nl,
    write('  run_all_test_files. to see the results of all tests'), nl,
    nl.

% =========================================================================
% ITERATION LIMITS CONFIGURATION
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 15).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 3).
logic_iteration_limit(fol, 15).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(I, M, N) :- M =< N, I = M.
for(I, M, N) :- M < N, M1 is M+1, for(I, M1, N).

% =========================================================================
% DÉTECTION THÉORÈME vs SÉQUENT (simplifié)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premise_list/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================

% normalize_formula/2: Apply efficiency-improving transformations
normalize_formula(Formula, Normalized) :-
    normalize_double_negations(Formula, F1),
    normalize_biconditional_order(F1, Normalized).

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :- 
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 2.
formula_complexity(A => B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.
contains_classical_pattern(![_-_]:A) :-
    contains_classical_pattern(A), !.
contains_classical_pattern(?[_-_]:A) :-
    contains_classical_pattern(A), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :- 
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================

% NOUVEAU : Détection automatique pour séquents avec prémisses
prove(G > D) :-
    G \= [],  % Prémisses non vides = SEQUENT
    !,
     % ✅ VALIDATION : Vérifier les prémisses et la conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent (with premises)'), nl,
    nl,
    
    % Stocker les prémisses pour l'affichage
    retractall(premise_list(_)),
    assertz(premise_list(G)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),
    
    % Préparer les formules
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    % Détecter pattern classique dans la conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    → Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal → Intuitionistic → Classical ==='), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('  ✓ Constructive proof found in MINIMAL LOGIC '), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('  ✓ Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write(' ✓ Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ;
                write('  → No explosion → INTUITIONISTIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('  ✗ Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            write('  ✓ Proof found in CLASSICAL LOGIC '), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).

% Biconditionals - REGROUPÉS PAR TYPE
prove(Left <=> Right) :- !,
         % ✅ VALIDATION : Vérifier les deux directions
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Left => Right)),
    time((decide_silent(Left => Right, Proof1, Logic1))),
    
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Right => Left)),
    time((decide_silent(Right => Left, Proof2, Logic2))),
    
    nl,
    write('=== BICONDITIONAL: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
    write('    '), portray_clause(Proof1), nl,nl,
    output_logic_label(Logic2), nl, nl,
    write('    '), portray_clause(Proof2), nl,nl,
    write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % FITCH STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Fitch Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof1),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof2),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('b) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof1), nl, nl,
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    write('This biconditional is valid:'), nl,
    write('- Direction 1 ('), write(Left => Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right => Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.


% Equivalence de séquents: [A] <> [B] prouve [A] > [B] ET [B] > [A]
prove([Left] <> [Right]) :- !,
          % ✅ VALIDATION : Vérifier les deux formules
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    % Direction 1: Left > Right
    assertz(current_proof_sequent([Left] > [Right])),
    time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))),   
    % Direction 2: Right > Left
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))),
    nl,
    write('=== SEQUENT EQUIVALENCE: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
    write('    '), portray_clause(Proof1), nl, nl,
    output_logic_label(Logic2), nl, nl,
    write('    '), portray_clause(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % FITCH STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Fitch Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premise_list(_)),
    assertz(premise_list([Left])),
    g4_to_fitch_sequent(Proof1, [Left] > [Right]),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premise_list(_)),
    assertz(premise_list([Right])),
    g4_to_fitch_sequent(Proof2, [Right] > [Left]),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('b) Tree Style:'), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premise_list(_)),
    assertz(premise_list([Left])),
    render_nd_tree_proof(Proof1), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premise_list(_)),
    assertz(premise_list([Right])),
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    write('This sequent equivalence is valid:'), nl,
    write('- Direction 1 ('), write(Left), write(' ⊢ '), write(Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right), write(' ⊢ '), write(Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.

% Theorems (original logic)
prove(Formula) :-
         % ✅ VALIDATION : Vérifier la formule
    validate_and_warn(Formula, _ValidatedFormula),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR: '), write(Formula), nl,
    write('------------------------------------------'), nl,  
    write('MODE: Theorem (no premises)'), nl,
    nl,
    
    retractall(premise_list(_)),
    retractall(current_proof_sequent(_)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        write('=== DOUBLE NEGATION DETECTED ==='), nl,
        write('    → Trying constructive first'), nl,
        write('=== TRYING CONSTRUCTIVE LOGIC ==='), nl,
        ( time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('  ✓ Constructive proof found'), nl,
            ( time(provable_at_level([] > [F2], minimal, _)) ->
                write(' ✓ Constructive proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write(' ✓ Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                )
            )
        ;
            write('  ✗ Constructive failed'), nl,
            write('=== FALLBACK: CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('  ✓ Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ; is_classical_pattern(F2) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    → Skipping constructive logic'), nl,
        write('=== TRYING CLASSICAL LOGIC ==='), nl,
        time(provable_at_level([] > [F2], classical, Proof)),
        write('  ✓ Classical proof found'), nl,
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal → Intuitionistic → Classical ==='), nl,
        ( time(provable_at_level([] > [F2], minimal, Proof)) ->
            write('  ✓ Minimal proof found → MINIMAL'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('  ✓ Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  → Uses explosion (⊥E) → INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            ;
                write('  → No explosion → INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            )
        ;
            write('  ✗ Constructive failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('  ✓ Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, Formula, theorem).

% =========================================================================
% HELPERS
% =========================================================================

% Préparer une liste de formules
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Affichage compact d'un séquent
write_sequent_compact([], [D]) :- !, write('⊢ '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' ⊢ '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' ⊢ '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% VALIDATION DES FORMULES ET SÉQUENTS
% =========================================================================

% Valider un séquent (prémisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Valider toutes les prémisses
    forall(member(Premise, G), validate_and_warn(Premise, _)),
    % Valider toutes les conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    output_logic_label(LogicType),
    write('Prolog terms:'), nl, nl,
    write('    '),
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           portray_clause(ProofCopy),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),
    write('Q.E.D.'), nl, nl,
    write('- Sequent Calculus -'), nl,nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('- Natural Deduction -'), nl, 
    write('a) Fitch Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    ( Mode = sequent ->
        g4_to_fitch_sequent(Proof, OriginalFormula)
    ;
        g4_to_fitch_theorem(Proof)
    ),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('b) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof),nl,nl,
    write('Q.E.D.'), nl, nl,
    !.

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], constructive, Proof) ->
        Logic = constructive
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL (simplifié)
% =========================================================================

provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(I, 0, MaxIter),
    Sequent = (G > D),
    prove(G > D, [], I, 1, _, intuitionistic, P),
    !.

provable_at_level(Sequent, LogicLevel, P) :-
    logic_iteration_limit(LogicLevel, MaxIter),
    for(I, 0, MaxIter),
    Sequent = (G > D),
    prove(G > D, [], I, 1, _, LogicLevel, P),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================
% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (G > D),
    prepare_sequent_formulas(G, D, PrepG, PrepD),
    ( member(SingleGoal, PrepD), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepG > PrepD, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepG > PrepD, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepG > PrepD, constructive, Proof) ->
        ( proof_uses_lbot(Proof) -> Logic = intuitionistic ; Logic = intuitionistic )
    ;
        provable_at_level(PrepG > PrepD, classical, Proof),
        Logic = classical
    ).

output_logic_label(constructive) :-
    nl,
    write('G4 Proofs:'), nl, nl.
output_logic_label(minimal) :- 
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :- 
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :- 
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).

% =========================================================================
% MINIMAL INTERFACE decide/1
% =========================================================================

decide(Left <=> Right) :- !,
         % ✅ VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide_silent(Left => Right, _, _),
        decide_silent(Right => Left, _, _)
    )),
    !.

decide(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    ( is_classical_pattern(F2) ->
        time(provable_at_level([] > [F2], classical, _))
    ;
        time(progressive_proof_silent(F2, _, _))
    ),
    !.

% decide/1 for sequents
decide(G > D) :-
    G \= [], !,
       % ✅ VALIDATION
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        time(provable_at_level(PrepG > PrepD, classical, _))
    ;
        ( time(provable_at_level(PrepG > PrepD, minimal, _)) ->
            true
        ; time(provable_at_level(PrepG > PrepD, constructive, _)) ->
            true
        ;
            time(provable_at_level(PrepG > PrepD, classical, _))
        )
    ),
    !.

% Equivalence pour decide
decide([Left] <> [Right]) :- !,
         % ✅ VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide([Left] > [Right]),
        decide([Right] > [Left])
    )),
    !.
 
% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('╔═══════════════════════════════════════════════════════════════╗'), nl,
    write('║                      G4 PROVER GUIDE                          ║'), nl,
    write('╚═══════════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('███ MAIN COMMANDS ███'), nl,
    nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  decide(Formula).           - says either true or false'), nl,
    write('  help.                      - gets help'), nl,
    write('  examples.                  - shows examples'), nl,
    nl,
    write('███ SYNTAX EXAMPLES ███'), nl,
    nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    nl,
    write('  SEQUENTS (NEW - G4 native syntax):'), nl,
    write('    prove([p] > [p]).                 - Sequent: p ⊢ p'), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: p, q ⊢ p ∧ q'), nl,
    write('    prove([p => q, p] > [q]).         - Modus ponens sequent'), nl,
    nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~~p).                 - Double negation (classical)'), nl,
    nl,
    write('███ COMMON MISTAKES ███'), nl,
    nl,
    write('  ❌ [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('  ✅ [p] > [p]           - CORRECT (sequent syntax)'), nl,
    nl,
    write('  ❌ p > q               - WRONG (use => for implication)'), nl,
    write('  ✅ p => q              - CORRECT (implication)'), nl,
    nl,
    write('  ❌ x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('  ✅ x = y in FOL        - CORRECT (equality)'), nl,
    nl,
    write('███ LOGICAL OPERATORS ███'), nl,
    write('  ~A  A & B  A | B  A => B  A <=> B  #  ![x]:A  ?[x]:A'), nl,
    nl.

examples :-
    nl,
    write('╔════════════════════════════════════════════════════════════════╗'), nl,
    write('║                     EXAMPLES                                  ║'), nl,
    write('╚════════════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    nl,
    write('  % Sequent: single premise'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    nl,
    write('  % Sequent: multiple premises'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    nl,
    write('  % LEM (classical)'), nl,
    write('  ?- prove(p | ~p).'), nl,
    nl.

quickref :-
    nl,
    write('╔═══════════════════════════════════════════════════════════════╗'), nl,
    write('║      QUICK REFERENCE                                          ║'), nl,
    write('╚═══════════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('  THEOREMS: prove(Formula)'), nl,
    write('  SEQUENTS: prove([Premises] > [Conclusion])'), nl,
    write('  BICOND:   prove(A <=> B)'), nl,
    nl,
    write('  prove(Formula).  decide(Formula).  help.'), nl,
    nl.

% ============================================
% DRIVER - Test Suite Runner with Timer
% ============================================

%! run_all_test_files
%  Exécute l'intégralité de la suite de tests avec mesure du temps
%  Inclut : tests unitaires, séquents FOL/Prop, Pelletier
run_all_test_files :- 
    get_time(StartTime),
    writeln(''),
    writeln('╔════════════════════════════════════════════╗'),
    writeln('║   START OF THE COMPLETE SERIES OF TESTS    ║'),
    writeln('╚════════════════════════════════════════════╝'),
    format('Démarrage : ~w~n~n', [StartTime]),
    
    safe_run(run_all_tests, 'FOL Theorems'),
    safe_run(run_fol_seq, 'FOL Valid Sequents'),
    safe_run(run_prop_seq, 'Propositional sequents'),
    safe_run(run_pelletier, 'Pelletier Problems'),
    
    get_time(EndTime),
    ElapsedTime is EndTime - StartTime,
    
    writeln(''),
    writeln('╔════════════════════════════════════════════╗'),
    writeln('║    END OF THE COMPLETE SERIES OF TESTS     ║'),
    writeln('╚════════════════════════════════════════════╝'),
    format_execution_time(ElapsedTime),
    writeln('').

%! safe_run(+Goal, +Name)
%  Exécute un prédicat de test avec gestion d'erreurs et chronomètre
safe_run(Goal, Name) :-
    format('~n--- ~w ---~n', [Name]),
    get_time(Start),
    catch(
        (call(Goal) -> 
            (get_time(End), 
             Duration is End - Start,
             format('✓ ~w : SUCCÈS (~2f secondes)~n', [Name, Duration])) 
        ; 
            (get_time(End), 
             Duration is End - Start,
             format('✗ ~w : ÉCHEC (~2f secondes)~n', [Name, Duration]))
        ),
        Error,
        (get_time(End), 
         Duration is End - Start,
         format('✗ ~w : ERREUR - ~w (~2f secondes)~n', [Name, Error, Duration]))
    ).

%! format_execution_time(+Seconds)
%  Affiche le temps d'exécution dans un format lisible
format_execution_time(Seconds) :-
    Seconds < 60,
    !,
    format('Temps total d\'exécution : ~2f secondes~n', [Seconds]).
format_execution_time(Seconds) :-
    Seconds < 3600,
    !,
    Minutes is floor(Seconds / 60),
    RemainingSeconds is Seconds - (Minutes * 60),
    format('Temps total d\'exécution : ~d min ~2f sec~n', [Minutes, RemainingSeconds]).
format_execution_time(Seconds) :-
    Hours is floor(Seconds / 3600),
    RemainingMinutes is floor((Seconds - (Hours * 3600)) / 60),
    RemainingSeconds is Seconds - (Hours * 3600) - (RemainingMinutes * 60),
    format('Temps total d\'exécution : ~d h ~d min ~2f sec~n', [Hours, RemainingMinutes, RemainingSeconds]).
% =========================================================================
% END OF DRIVER
% =========================================================================
