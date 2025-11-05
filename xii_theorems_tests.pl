% =================================================================
% 1. BASIC TESTS - MINIMAL PROPOSITIONAL LOGIC
% =================================================================
% Identity and implication introduction tests
test_identity_simple :-
    write('P → P'), nl,
    prove(p => p).
test_identity_complex :-
    write('P → (Q → P)'), nl,
    prove(p => (q => p)).
test_permutation :-
    write('P → (Q → (P ∧ Q))'), nl,
    prove(p => (q => (p & q))).
% Conjunction tests
test_conjunction_intro :-
    write('(P ∧ Q) → (Q ∧ P)'), nl,
    prove((p & q) => (q & p)).
test_conjunction_assoc :-
    write('((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))'), nl,
    prove(((p & q) & r) => (p & (q & r))).
% Disjunction tests
test_disjunction_intro :-
    write('P → (P ∨ Q)'), nl,
    prove(p => (p | q)).
test_disjunction_comm :-
    write('(P ∨ Q) → (Q ∨ P)'), nl,
    prove((p | q) => (q | p)).
test_disjunction_elim :-
    write('((P → R) ∧ (Q → R)) → ((P ∨ Q) → R)'), nl,
    prove(((p => r) & (q => r)) => ((p | q) => r)).
% Biconditional tests
test_distrib_disj_over_conj :-
        write('((P | Q) & (P | R)) <=> (P | (Q & R))'),nl,
        prove(((p | q) & (p | r)) <=> (p | (q & r))).
test_biconditional_intro :-
    write('(P → Q) → ((Q → P) → (P ↔ Q))'), nl,
    prove((p => q) => ((q => p) => (p <=> q))).
test_biconditional_elim :-
    write('(P ↔ Q) → (P → Q)'), nl,
    prove((p <=> q) => (p => q)).
% Modus Tollens tests (CORRECTED)
test_modus_tollens :-
    write('((P → Q) ∧ ¬Q) → ¬P'), nl,
    prove(((p => q) & ~ q) => ~ p).
test_modus_tollens_complex :-
    write('((P → (Q → R)) ∧ ¬R) → (P → ¬Q)'), nl,
    prove(((p => (q => r)) & ~ r) => (p => ~ q)).
test_absurdity_chain_m :-
    write('P -> (¬P → ⊥) '), nl,
    prove(p => (~ p => #)).
% Negation introduction/elimination tests
test_negation_intro :-
    write('(P → ⊥) → ¬P'), nl,
    prove((p => #) => ~ p).
test_negation_elim :-
    write('(P ∧ ¬P) → ⊥'), nl,
    prove((p & ~ p) => #).
% =================================================================
% 2. INTUITIONISTIC TESTS - NEGATION
% =================================================================
% Contradiction tests
test_contradiction_anything :-
    write(' ⊥ → P'), nl,
    prove(# => p).
test_absurdity_chain_i :-
    write('~  ~  P <=> (~  P => P)'), nl,
    prove((~ p => #) <=> ((p => #) => p)).
test_dn_Peirce :-
    write('~  ~  (((P => Q) => P) => P)'), nl,
    prove(~  ~  (((p => q) => p) => p)).
test_dn_Dummett :-
    write('~  ~  ((P => Q) v (Q => P))'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_Dummett :-
    write('~  ~  ((P => Q) v (Q => P))'), nl,
    prove(~  ~  ((p => q) | (q => p))).
test_dn_classical_contraposition :-
    write('~  ~  ((~  Q => ~  P) <=>  (P => Q))'), nl,
    prove(~  ~  ((~  q => ~  p) <=> (p => q))).
% =================================================================
% 3. CLASSICAL TESTS - BEYOND INTUITIONISTIC LOGIC
% =================================================================
% Indirect proof tests
test_indirect_proof :-
    write('¬¬P → P (Double negation elimination)'), nl,
    prove( ~  ~  p => p).
test_excluded_middle :-
    write('Test 3.2: P ∨ ¬P (Excluded middle) [classical]'), nl,
    prove(p | ~  p).
test_material_implication :-
    write('Test 3.3: (P → Q) ↔ (¬P ∨ Q)'), nl,
    prove((( ~  p | q) <=> (p => q))).
% Classical contraposition tests
test_contraposition_strong :-
    write('Test 3.4: (¬Q → ¬P) → (P → Q)'), nl,
    prove(( ~  q => ~  p) => (p => q)).
test_absurdity_chain_c :-
    write('Test 2.5: (¬P → ⊥) → P [may fail in intuitionistic logic]'), nl,
    prove((~ p => #) => p), nl.
% =================================================================
% 4. QUANTIFIER TESTS - CORRECTED SYNTAX
% =================================================================
% Basic universal tests
test_universal_intro :-
    write('Test 4.1: ∀x(P(x) → P(x))'), nl,
    prove(![x]:(p(x) => p(x))).
test_universal_elim :-
    write('Test 4.2: (∀x P(x)) → P(a)'), nl,
    prove((![x]:p(x)) => p(a)).
test_universal_distribution :-
    write('Test 4.3: (∀x(P(x) → Q(x))) → ((∀x P(x)) → (∀x Q(x)))'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
% Basic existential tests
test_existential_intro :-
    write('Test 4.4: P(a) → ∃x P(x)'), nl,
    prove(p(a) => (?[x]:p(x))).
test_existential_elim :-
    write('Test 4.5: (∃x P(x)) → (∀x(P(x) → Q)) → Q'), nl,
    prove((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)).
test_mixed_quantifiers :-
    write('Test 4.6: Valid mixed quantifiers'), nl,
    prove((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))).
test_quantifier_negation :-
    write('Test 4.7: ¬(∀x P(x)) ↔ (∃x ¬P(x))'), nl,
    catch(prove((~ (![x]:p(x))) <=> (?[x]: ~  p(x))), 
          _, write('May fail - complex equivalence')), nl.
test_Spinoza :-
        write(' Nothing is contingent '), nl,
        prove((![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))) & ![x]:(?[z]:d(z,x))) => ![x]: ~ c(x)).
test_Lepage :-
        write( 'Lepage, Éléments de logique contemporaine, p. 202, ex. 14*-g'), nl,
        prove((![x]:(f(x) <=> g(x)) & ![x]:(h(x) <=> i(x)) & ?[x]:(i(x) & ![y]:(f(y) => j(y)))) => ?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))).
% =================================================================
% 5. PREMISE TESTS - PRACTICAL REASONING
% =================================================================
% Modus ponens with premises
test_modus_ponens :-
    write('Test 5.1: ((P => Q) & P) => Q'), nl,
    prove(((p => q) & p) => q).
test_hypothetical_syllogism :-
    write('Test 5.2: ((P → Q) &(Q → R)) => (P → R)'), nl,
    prove(((p => q) & (q => r)) => (p => r)).
test_disjunctive_syllogism :-
    write('Test 5.3: ((P ∨ Q)& ¬P) => Q'), nl,
    prove(((p | q) & ~  p ) => q).

% Complex tests with quantifiers - SIMPLIFIED
test_universal_instantiation :-
    write('Test 5.4: {∀x(H(x) → M(x)), H(a)} ⊢ M(a)'), nl,
    prove((![x]:(h(x) => m(x)) & h(a)) => m(a)).
test_existential_generalization :-
    write('Test 5.5: {M(a)} ⊢ ∃x M(x)'), nl,
    prove(m(a) => ?[x]:m(x)).
% =================================================================
% 6. STRESS TESTS - COMPLEX FORMULAS
% =================================================================
test_complex_formula_1 :-
    write('Test 6.1: Complex formula with quantifiers'), nl,
    prove((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).
test_complex_formula_2 :-
    write('Test 6.2: Mixed conditionals and conjunctions'), nl,
    prove(((p => q) & (r => s)) => ((p & r) => (q & s))).
test_Pelletier_17 :-
        write( ' Pelletier 17' ),
        prove( ( ( p & ( q => r ) ) => s ) <=> ( ( ~ p | q | s ) & ( ~ p | ~ r | s ) ) ).
% =================================================================
% TEST RUNNERS
% =================================================================
run_all_tests :-
    write('========================================'), nl,
    write('FOL PROVER TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    % Minimal propositional tests
    write('=== MINIMAL PROPOSITIONAL LOGIC ==='), nl,
    test_identity_simple, nl,
    test_identity_complex, nl,
    test_permutation, nl,
    test_conjunction_intro, nl,
    test_conjunction_assoc, nl,
    test_disjunction_intro, nl,
    test_disjunction_comm, nl,
    test_disjunction_elim, nl,
    test_distrib_disj_over_conj, nl,
    test_biconditional_intro, nl,
    test_biconditional_elim, nl,
    test_modus_tollens, nl,
    test_modus_tollens_complex, nl,
    test_absurdity_chain_m,nl,
    test_negation_intro, nl,
    test_negation_elim, nl,
    
    % Intuitionistic tests
    write('=== INTUITIONISTIC LOGIC ==='), nl,
    test_contradiction_anything, nl,
    test_absurdity_chain_i, nl,
    test_dn_Peirce, nl,
    test_dn_Dummett,nl,
    test_dn_classical_contraposition,nl,
    
 
    % Classical tests
    write('=== CLASSICAL LOGIC ==='), nl,
    test_indirect_proof, nl,
    test_excluded_middle, nl,
    test_material_implication, nl,
    test_contraposition_strong, nl,
    
    % Quantifier tests
    write('=== QUANTIFIERS ==='), nl,
    test_universal_intro, nl,
    test_universal_elim, nl,
    test_universal_distribution, nl,
    test_existential_intro, nl,
    test_existential_elim, nl,
    test_mixed_quantifiers, nl,
    test_quantifier_negation, nl,
    test_Spinoza,nl,
    test_Lepage,nl,
   
    write('=== Usual logical truths ==='), nl,
    test_modus_ponens, nl,
    test_hypothetical_syllogism, nl,
    test_disjunctive_syllogism, nl,
    test_universal_instantiation, nl,
    test_existential_generalization, nl,
    
    % Stress tests
    write('=== STRESS TESTS ==='), nl,
   % test_complex_formula_1, nl,
    test_complex_formula_2, nl,
    test_Pelletier_17,nl,
    
    write('========================================'), nl,
    write('TEST SUITE END'), nl,
    write('========================================'), nl,
    !.

% Quick tests for immediate verification
quick_tests :-
    write('=== QUICK TESTS ==='), nl,
    test_identity_simple, nl,
    test_modus_tollens, nl.
 %   test_modus_ponens_premises, nl,
  /*
    test_universal_intro, nl,
    write('=== QUICK TESTS END ==='), nl.
*/
% Individual MT test for debugging
test_mt_only :-
    write('=== ISOLATED MT TEST ==='), nl,
    test_modus_tollens, nl.

% Logic level demonstration tests
demo_logic_levels :-
    write('=== LOGIC LEVEL DEMONSTRATION ==='), nl,
    write('--- Minimal Logic Example ---'), nl,
    prove(p => p), nl,
    write('--- Intuitionistic Logic Example ---'), nl, 
    prove((p & ~  p) => #), nl,!.
    /*
    write('--- Classical Logic Example ---'), nl,
    prove( ~  ~  a => a), nl,
    write('=== DEMO END ==='), nl.
   */
% =========================================================================
% TESTS FOL - FORMULES SIMPLES
% =========================================================================

test_fol_identity :-
    write('Test FOL 1: ![x]:p(x) => ![x]:p(x)'), nl,
    prove(![x]:p(x) => ![x]:p(x)), nl.

test_fol_instantiation :-
    write('Test FOL 2: ![x]:p(x) => ?[x]:p(x)'), nl,
    prove(![x]:p(x) => ?[x]:p(x)), nl.

test_fol_barber :-
    write('Test FOL 3: (?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))'), nl,
    prove((?[y]:(![x]:(f(x,y)))) => (![x]:(?[y]:(f(x,y))))), nl.

% Ajouter aux tests existants
run_fol_tests :-
    % ... tests propositionnels existants ...
    
    write('=== FOL TESTS ==='), nl,
    test_fol_identity, nl,
    test_fol_instantiation, nl,
    test_fol_barber, nl,
    
    write('========================================'), nl,
    write('TEST SUITE END'), nl,
    write('========================================'), nl.
