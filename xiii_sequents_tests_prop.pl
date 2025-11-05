%=================================================================
% SEQUENT TESTS - PROPOSITIONAL LOGIC ONLY
% Tests for sequents with premises (avoiding classical disjunction theorems)
% =================================================================

% =================================================================
% 1. BASIC SEQUENT TESTS - MINIMAL LOGIC
% =================================================================

% Identity with premises
test_seq_identity_premise :-
    write('Test Seq 1.1: {P} ⊢ P'), nl,
    prove([p] > [p]), nl.

test_seq_weakening :-
    write('Test Seq 1.2: {P, Q} ⊢ P'), nl,
    prove([p, q] > [p]), nl.

test_seq_implication_intro :-
    write('Test Seq 1.3: {P} ⊢ Q → P'), nl,
    prove([p] > [q => p]), nl.

% =================================================================
% 2. CONJUNCTION SEQUENTS
% =================================================================

test_seq_conjunction_intro :-
    write('Test Seq 2.1: {P, Q} ⊢ P ∧ Q'), nl,
    prove([p, q] > [p & q]), nl.

test_seq_conjunction_elim_left :-
    write('Test Seq 2.2: {P ∧ Q} ⊢ P'), nl,
    prove([p & q] > [p]), nl.

test_seq_conjunction_elim_right :-
    write('Test Seq 2.3: {P ∧ Q} ⊢ Q'), nl,
    prove([p & q] > [q]), nl.

test_seq_conjunction_comm :-
    write('Test Seq 2.4: {P ∧ Q} ⊢ Q ∧ P'), nl,
    prove([p & q] > [q & p]), nl.

test_seq_conjunction_assoc :-
    write('Test Seq 2.5: {(P ∧ Q) ∧ R} ⊢ P ∧ (Q ∧ R)'), nl,
    prove([(p & q) & r] > [p & (q & r)]), nl.

test_seq_conjunction_nested :-
    write('Test Seq 2.6: {P, Q, R} ⊢ (P ∧ Q) ∧ R'), nl,
    prove([p, q, r] > [(p & q) & r]), nl.

% =================================================================
% 3. IMPLICATION SEQUENTS
% =================================================================

test_seq_modus_ponens :-
    write('Test Seq 3.1: {P → Q, P} ⊢ Q'), nl,
    prove([p => q, p] > [q]), nl.

test_seq_hypothetical_syllogism :-
    write('Test Seq 3.2: {P → Q, Q → R} ⊢ P → R'), nl,
    prove([p => q, q => r] > [p => r]), nl.

test_seq_implication_chain :-
    write('Test Seq 3.3: {P → Q, Q → R, P} ⊢ R'), nl,
    prove([p => q, q => r, p] > [r]), nl.

test_seq_curry :-
    write('Test Seq 3.4: {(P ∧ Q) → R} ⊢ P → (Q → R)'), nl,
    prove([(p & q) => r] > [p => (q => r)]), nl.

test_seq_uncurry :-
    write('Test Seq 3.5: {P → (Q → R)} ⊢ (P ∧ Q) → R'), nl,
    prove([p => (q => r)] > [(p & q) => r]), nl.

% =================================================================
% 4. DISJUNCTION SEQUENTS (NON-CLASSICAL)
% =================================================================

test_seq_disj_intro_left :-
    write('Test Seq 4.1: {P} ⊢ P ∨ Q'), nl,
    prove([p] > [(p | q)]), nl.

test_seq_disj_intro_right :-
    write('Test Seq 4.2: {Q} ⊢ P ∨ Q'), nl,
    prove([q] > [(p | q)]), nl.

test_seq_disj_elim :-
    write('Test Seq 4.3: {P ∨ Q, P → R, Q → R} ⊢ R'), nl,
    prove([(p | q), p => r, q => r] > [r]), nl.

test_seq_disj_syllogism :-
    write('Test Seq 4.4: {P ∨ Q, ¬P} ⊢ Q'), nl,
    prove([(p | q), ~ p] > [q]), nl.

test_seq_disj_comm :-
    write('Test Seq 4.5: {P ∨ Q} ⊢ Q ∨ P'), nl,
    prove([(p | q)] > [(q | p)]), nl.

% =================================================================
% 5. NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_negation_intro :-
    write('Test Seq 5.1: {P → ⊥} ⊢ ¬P'), nl,
    prove([p => #] > [~ p]), nl.

test_seq_negation_elim :-
    write('Test Seq 5.2: {P, ¬P} ⊢ ⊥'), nl,
    prove([p, ~ p] > [#]), nl.

test_seq_explosion :-
    write('Test Seq 5.3: {⊥} ⊢ P'), nl,
    prove([#] > [p]), nl.

test_seq_modus_tollens :-
    write('Test Seq 5.4: {P → Q, ¬Q} ⊢ ¬P'), nl,
    prove([p => q, ~ q] > [~ p]), nl.

test_seq_contraposition_weak :-
    write('Test Seq 5.5: {P → Q} ⊢ ¬Q → ¬P'), nl,
    prove([p => q] > [~ q => ~ p]), nl.

test_seq_double_negation_intro :-
    write('Test Seq 5.6: {P} ⊢ ¬¬P'), nl,
    prove([p] > [~ ~ p]), nl.

% =================================================================
% 6. BICONDITIONAL SEQUENTS
% =================================================================

test_seq_biconditional_intro :-
    write('Test Seq 6.1: {P → Q, Q → P} ⊢ P ↔ Q'), nl,
    prove([p => q, q => p] > [p <=> q]), nl.

test_seq_biconditional_elim_left :-
    write('Test Seq 6.2: {P ↔ Q} ⊢ P → Q'), nl,
    prove([p <=> q] > [p => q]), nl.

test_seq_biconditional_elim_right :-
    write('Test Seq 6.3: {P ↔ Q} ⊢ Q → P'), nl,
    prove([p <=> q] > [q => p]), nl.

test_seq_biconditional_modus_ponens :-
    write('Test Seq 6.4: {P ↔ Q, P} ⊢ Q'), nl,
    prove([p <=> q, p] > [q]), nl.

% =================================================================
% 7. COMPLEX SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_complex_1 :-
    write('Test Seq 7.1: {(P → Q) ∧ (Q → R), P} ⊢ R'), nl,
    prove([(p => q) , (q => r), p] > [r]), nl.

test_seq_complex_2 :-
    write('Test Seq 7.2: {P ∧ (Q ∨ R)} ⊢ (P ∧ Q) ∨ (P ∧ R)'), nl,
    prove([p , (q | r)] > [((p & q) | (p & r))]), nl.

test_seq_complex_3 :-
    write('Test Seq 7.3: {(P ∨ Q) ∧ (P ∨ R)} ⊢ P ∨ (Q ∧ R)'), nl,
    prove([(p | q) , (p | r)] > [(p | (q & r))]), nl.

test_seq_complex_4 :-
    write('Test Seq 7.4: {P → (Q → R)} ⊢ Q → (P → R)'), nl,
    prove([p => (q => r)] > [q => (p => r)]), nl.



% =================================================================
% 8. DOUBLE NEGATION SEQUENTS - INTUITIONISTIC
% =================================================================

test_seq_dn_peirce :-
    write('Test Seq 8.1: {} ⊢ ¬¬(((P → Q) → P) → P)'), nl,
    prove([~ (((p => q) => p) => p)] > [#]), nl.

test_seq_dn_lem :-
    write('Test Seq 8.2: {} ⊢ ¬¬(P ∨ ¬P)'), nl,
    prove([~ (p | ~ p)] > [#]), nl.

test_seq_dn_dummett :-
    write('Test Seq 8.3: {} ⊢ ¬¬((P → Q) ∨ (Q → P))'), nl,
    prove([~ ((p => q) | (q => p))] > [#]), nl.

% =================================================================
% TEST RUNNERS
% =================================================================

run_prop_seq :-
    write('========================================'), nl,
    write('SEQUENT TESTS - PROPOSITIONAL LOGIC'), nl,
    write('========================================'), nl, nl,
    
    write('=== 1. BASIC SEQUENTS ==='), nl,
    test_seq_identity_premise,
    test_seq_weakening,
    test_seq_implication_intro,
    
    write('=== 2. CONJUNCTION SEQUENTS ==='), nl,
    test_seq_conjunction_intro,
    test_seq_conjunction_elim_left,
    test_seq_conjunction_elim_right,
    test_seq_conjunction_comm,
    test_seq_conjunction_assoc,
    test_seq_conjunction_nested,
    
    write('=== 3. IMPLICATION SEQUENTS ==='), nl,
    test_seq_modus_ponens,
    test_seq_hypothetical_syllogism,
    test_seq_implication_chain,
    test_seq_curry,
    test_seq_uncurry,
    
    write('=== 4. DISJUNCTION SEQUENTS ==='), nl,
    test_seq_disj_intro_left,
    test_seq_disj_intro_right,
    test_seq_disj_elim,
    test_seq_disj_syllogism,
    test_seq_disj_comm,
    
    write('=== 5. NEGATION SEQUENTS ==='), nl,
    test_seq_negation_intro,
    test_seq_negation_elim,
    test_seq_explosion,
    test_seq_modus_tollens,
    test_seq_contraposition_weak,
    test_seq_double_negation_intro,
    
    write('=== 6. BICONDITIONAL SEQUENTS ==='), nl,
    test_seq_biconditional_intro,
    test_seq_biconditional_elim_left,
    test_seq_biconditional_elim_right,
    test_seq_biconditional_modus_ponens,
    
    write('=== 7. COMPLEX SEQUENTS ==='), nl,
    test_seq_complex_1,
    test_seq_complex_2,
    test_seq_complex_3,
    test_seq_complex_4,
    
    write('=== 8. DOUBLE NEGATION SEQUENTS ==='), nl,
    test_seq_dn_peirce,
    test_seq_dn_lem,
    test_seq_dn_dummett,
    
    write('========================================'), nl,
    write('SEQUENT TESTS END'), nl,
    write('========================================'), nl,
    !.

% Quick tests
quick_sequent_tests :-
    write('=== QUICK SEQUENT TESTS ==='), nl,
    test_seq_identity_premise,
    test_seq_modus_ponens,
    test_seq_disj_syllogism,
    test_seq_ltoto_2,
    write('=== QUICK TESTS END ==='), nl.
