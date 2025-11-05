% =================================================================
% SEQUENT TESTS - FIRST ORDER LOGIC (FOL)
% Tests for sequents with quantifiers and predicates
% =================================================================

% =================================================================
% BASIC QUANTIFIER SEQUENTS
% =================================================================

test_seq_forall_elim :-
    write('∀E: ∀x P(x) ⊢ P(a)'), nl,
    prove([![x]:p(x)] > [p(a)]).

test_seq_exists_intro :-
    write('∃I: P(a) ⊢ ∃x P(x)'), nl,
    prove([p(a)] > [?[x]:p(x)]).

test_seq_exists_elim :-
    write('∃E: ∃x P(x), ∀x(P(x) → Q) ⊢ Q'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q)] > [q]).

% =================================================================
% QUANTIFIER DISTRIBUTION
% =================================================================

test_seq_forall_distribution :-
    write('∀x(P(x) → Q(x)), ∀x P(x) ⊢ ∀x Q(x)'), nl,
    prove([![x]:(p(x) => q(x)), ![x]:p(x)] > [![x]:q(x)]).

test_seq_exists_distribution :-
    write('∃x(P(x) ∧ Q(x)) ⊢ ∃x P(x) ∧ ∃x Q(x)'), nl,
    prove([?[x]:(p(x) & q(x))] > [?[x]:p(x) & ?[x]:q(x)]).

test_seq_mixed_quantifiers :-
    write('∃y ∀x P(x,y) ⊢ ∀x ∃y P(x,y)'), nl,
    prove([?[y]:(![x]:p(x,y))] > [![x]:(?[y]:p(x,y))]).

% =================================================================
% QUANTIFIER NEGATION (DE MORGAN FOR QUANTIFIERS)
% =================================================================

test_seq_neg_forall :-
    write('¬∀x P(x) ⊢ ∃x ¬P(x) [classical]'), nl,
    prove([~ (![x]:p(x))] <> [?[x]: ~ p(x)]).

test_seq_neg_exists :-
    write('¬∃x P(x) ⊢ ∀x ¬P(x)'), nl,
    prove([~ (?[x]:p(x))] <> [![x]: ~ p(x)]).

% =================================================================
% MODUS PONENS WITH QUANTIFIERS
% =================================================================

test_seq_forall_mp :-
    write('∀x(P(x) → Q(x)), P(a) ⊢ Q(a)'), nl,
    prove([![x]:(p(x) => q(x)), p(a)] > [q(a)]).

test_seq_exists_mp :-
    write('∃x P(x), ∀x(P(x) → Q(x)) ⊢ ∃x Q(x)'), nl,
    prove([?[x]:p(x), ![x]:(p(x) => q(x))] > [?[x]:q(x)]).

% =================================================================
% CLASSICAL LOGIC WITH QUANTIFIERS
% =================================================================

test_seq_barber_paradox :-
    write('∀x(B(x,x) ↔ ¬B(x,x)) ⊢ ⊥ [Barber paradox]'), nl,
    prove([![x]:(b(x,x) <=> ~ b(x,x))] > [#]).

test_seq_drinker :-
    write('⊢ ∃x(D(x) → ∀y D(y)) [Drinker paradox - classical]'), nl,
    prove([~ #] > [?[x]:(d(x) => ![y]:d(y))]).

% =================================================================
% SYLLOGISMS WITH QUANTIFIERS
% =================================================================

test_seq_barbara :-
    write('Barbara: ∀x(M(x) → P(x)), ∀x(S(x) → M(x)) ⊢ ∀x(S(x) → P(x))'), nl,
    prove([![x]:(m(x) => p(x)), ![x]:(s(x) => m(x))] > [![x]:(s(x) => p(x))]).

test_seq_darii :-
    write('Darii: ∀x(M(x) → P(x)), ∃x(S(x) ∧ M(x)) ⊢ ∃x(S(x) ∧ P(x))'), nl,
    prove([![x]:(m(x) => p(x)), ?[x]:(s(x) & m(x))] > [?[x]:(s(x) & p(x))]).

test_seq_socrates :-
    write('Socrates: ∀x(H(x) → M(x)), H(socrates) ⊢ M(socrates)'), nl,
    prove([![x]:(h(x) => m(x)), h(socrates)] > [m(socrates)]).

% =================================================================
% EQUALITY REASONING
% =================================================================

test_seq_eq_reflexive :-
    write('Reflexivity: ⊢ a = a'), nl,
    prove([~ #] > [a = a]).

test_seq_eq_symmetric :-
    write('Symmetry: a = b ⊢ b = a'), nl,
    prove([a = b] > [b = a]).

test_seq_eq_transitive :-
    write('Transitivity: a = b, b = c ⊢ a = c'), nl,
    prove([a = b, b = c] > [a = c]).

test_seq_eq_substitution :-
    write('Substitution: a = b, P(a) ⊢ P(b)'), nl,
    prove([a = b, p(a)] > [p(b)]).

test_seq_eq_congruence :-
    write('Congruence: a = b ⊢ f(a) = f(b)'), nl,
    prove([a = b] > [f(a) = f(b)]).

% =================================================================
% COMPLEX FOL SEQUENTS
% =================================================================

test_seq_spinoza :-
    write('Spinoza: Nothing is contingent'), nl,
    prove([
        ![x]:(~ c(x) <=> (?[y]:n(y,x) | ?[z]:d(z,x))),
        ![x]:(?[z]:d(z,x))
    ] > [![x]: ~ c(x)]).

test_seq_lepage :-
    write('Lepage exercise 14*-g'), nl,
    prove([
        ![x]:(f(x) <=> g(x)),
        ![x]:(h(x) <=> i(x)),
        ?[x]:(i(x) & ![y]:(f(y) => j(y)))
    ] > [?[x]:(h(x) & ![y]:(j(y) | ~ g(y)))]).

% =================================================================
% BICONDITIONAL SEQUENTS
% =================================================================

test_seq_bicond_left :-
    write('A ↔ B, A ⊢ B'), nl,
    prove([a <=> b, a] > [b]).

test_seq_bicond_right :-
    write('A → B, B → A ⊢ A ↔ B'), nl,
    prove([a => b, b => a] > [a <=> b]).

test_seq_bicond_quantifier :-
    write('∀x(P(x) ↔ Q(x)), P(a) ⊢ Q(a)'), nl,
    prove([![x]:(p(x) <=> q(x)), p(a)] > [q(a)]).

% =================================================================
% TEST RUNNERS
% =================================================================

run_fol_seq :-
        retractall(fitch_line(_, _, _, _)),      % ← Nettoyage global
    retractall(abbreviated_line(_)),
    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    
    write('=== BASIC QUANTIFIERS ==='), nl,
    test_seq_exists_intro, nl,
    test_seq_exists_elim, nl,
    
    write('=== QUANTIFIER DISTRIBUTION ==='), nl,
    test_seq_forall_distribution, nl,
    test_seq_exists_distribution, nl,
    test_seq_mixed_quantifiers, nl,
    
    write('=== QUANTIFIER NEGATION ==='), nl,
    test_seq_neg_exists, nl,
    test_seq_neg_forall, nl,
    
    write('=== MODUS PONENS WITH QUANTIFIERS ==='), nl,
    test_seq_forall_mp, nl,
    test_seq_exists_mp, nl,
    
    write('=== CLASSICAL FOL ==='), nl,
    test_seq_barber_paradox, nl,
    test_seq_drinker, nl,
    
    write('=== SYLLOGISMS ==='), nl,
    test_seq_barbara, nl,
    test_seq_darii, nl,
    test_seq_socrates, nl,
    
    write('=== EQUALITY ==='), nl,
    test_seq_eq_reflexive, nl,
    test_seq_eq_symmetric, nl,
    test_seq_eq_transitive, nl,
    test_seq_eq_substitution, nl,
    test_seq_eq_congruence, nl,
    
    write('=== COMPLEX FOL ==='), nl,
    test_seq_spinoza, nl,
    test_seq_lepage, nl,
    
    write('=== BICONDITIONALS ==='), nl,
    test_seq_bicond_left, nl,
    test_seq_bicond_right, nl,
    test_seq_bicond_quantifier, nl,
    
    write('========================================'), nl,
    write('FOL SEQUENT TEST SUITE END'), nl,
    write('========================================'), nl.

run_quick_fol_sequent_tests :-
    write('=== QUICK FOL SEQUENT TESTS ==='), nl,
    test_seq_forall_elim, nl,
    test_seq_exists_intro, nl,
    test_seq_socrates, nl,
    test_seq_eq_transitive, nl,
    write('=== QUICK TESTS END ==='), nl.
