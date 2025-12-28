%% ============================================================================
%% File: EXAMPLES_countermodel.pl
%% Purpose: Comprehensive examples for nanoCop countermodel extraction
%% Author: Joseph Vidal-Rosset
%% ============================================================================

:- ensure_loaded(nanocop_countermodel_v2).

%% ============================================================================
%% SECTION 1: PROPOSITIONAL LOGIC EXAMPLES
%% ============================================================================

%% Example 1.1: Simple invalid implication
example_invalid_implication :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 1.1: Invalid Implication'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Does p imply q in general?'), nl,
    write('Formula: p => q'), nl,
    nl,
    test((p => q)),
    write('Explanation: Without any relationship between p and q,'), nl,
    write('we can have p true and q false, refuting the implication.'), nl,
    nl.

%% Example 1.2: Valid modus ponens
example_modus_ponens :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 1.2: Modus Ponens (Valid)'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Formula: (p, (p => q)) => q'), nl,
    nl,
    test((p, (p => q)) => q),
    write('This is the fundamental inference rule modus ponens.'), nl,
    write('Given p and p→q, we can always derive q.'), nl,
    nl.

%% Example 1.3: Invalid converse
example_invalid_converse :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 1.3: Invalid Converse'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Does q imply p if we know p => q?'), nl,
    write('Formula: (p => q) => (q => p)'), nl,
    nl,
    test((p => q) => (q => p)),
    write('Explanation: This is the fallacy of affirming the consequent.'), nl,
    write('Just because p implies q does NOT mean q implies p.'), nl,
    nl.

%% Example 1.4: Law of excluded middle (valid in classical logic)
example_excluded_middle :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 1.4: Law of Excluded Middle'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Formula: p | (~p)'), nl,
    nl,
    test((p ; ~p)),
    write('This fundamental principle of classical logic states:'), nl,
    write('Every proposition is either true or false (no middle ground).'), nl,
    nl.

%% Example 1.5: Pierce's Law (valid only in classical logic)
example_pierce :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 1.5: Pierce\'s Law'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Formula: ((p => q) => p) => p'), nl,
    nl,
    test(((p => q) => p) => p),
    write('Pierce\'s law is a classical tautology but NOT valid in'), nl,
    write('intuitionistic logic. nanoCop (classical) proves it.'), nl,
    nl.

%% ============================================================================
%% SECTION 2: FIRST-ORDER LOGIC - QUANTIFIERS
%% ============================================================================

%% Example 2.1: Invalid universal instantiation (empty domain)
example_empty_domain :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 2.1: Empty Domain Problem'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Does ∀x.P(x) imply P(a)?'), nl,
    write('Formula: (all X:p(X)) => p(a)'), nl,
    nl,
    test((all X:p(X)) => p(a)),
    write('Explanation: In an EMPTY domain, ∀x.P(x) is vacuously true'), nl,
    write('(there are no x to check), but P(a) requires \'a\' to exist.'), nl,
    write('Hence the formula can fail!'), nl,
    nl.

%% Example 2.2: Drinker's Paradox (valid)
example_drinker :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 2.2: Drinker\'s Paradox'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Statement: In any pub, there exists someone such that'), nl,
    write('if they are drinking, then everyone is drinking.'), nl,
    nl,
    write('Formula: ∃y.(D(y) → ∀x.D(x))'), nl,
    nl,
    test(ex Y:(d(Y) => all X:d(X))),
    write('This famous paradox is valid in classical logic!'), nl,
    write('Proof sketch: Either everyone drinks or someone doesn\'t.'), nl,
    write('  - If everyone drinks: pick anyone as the witness'), nl,
    write('  - If someone doesn\'t: pick them as the witness'), nl,
    write('    (their non-drinking makes the implication vacuously true)'), nl,
    nl.

%% Example 2.3: Invalid quantifier swap
example_quantifier_swap :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 2.3: Invalid Quantifier Swap'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Does ∀x∃y.L(x,y) imply ∃y∀x.L(x,y)?'), nl,
    write('Formula: (all X:ex Y:loves(X,Y)) => (ex Y:all X:loves(X,Y))'), nl,
    nl,
    test((all X:ex Y:loves(X,Y)) => (ex Y:all X:loves(X,Y))),
    write('Explanation: "Everyone loves someone" does NOT imply'), nl,
    write('"There is someone loved by everyone."'), nl,
    write('Different people can love different people!'), nl,
    nl.

%% Example 2.4: Valid Barbara syllogism
example_barbara :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 2.4: Barbara Syllogism'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Premises: All men are mortal. Socrates is a man.'), nl,
    write('Conclusion: Therefore, Socrates is mortal.'), nl,
    nl,
    write('Formula: (all X:(man(X) => mortal(X)), man(socrates))'), nl,
    write('         => mortal(socrates)'), nl,
    nl,
    test((all X:(man(X) => mortal(X)), man(socrates)) => mortal(socrates)),
    write('This is the classic Aristotelian syllogism.'), nl,
    nl.

%% ============================================================================
%% SECTION 3: COMPARISON WITH G4MIC
%% ============================================================================

%% Example 3.1: Side-by-side comparison on invalid formula
example_compare_invalid :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 3.1: Comparing nanoCop and g4mic on Invalid Formula'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    compare_with_g4mic((a => b)).

%% Example 3.2: Side-by-side comparison on valid formula
example_compare_valid :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 3.2: Comparing nanoCop and g4mic on Valid Formula'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    compare_with_g4mic((p, (p => q)) => q).

%% Example 3.3: Complex formula comparison
example_compare_complex :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 3.3: Complex Formula - Pelletier Problem 9'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Formula: ∀x∃y.(∀z∃w.((P(x)∧Q(y))→(P(z)∧Q(w)))) →'), nl,
    write('         ((P(x)∧Q(y))→(∀z.P(z)∧∀w.Q(w)))'), nl,
    nl,
    compare_with_g4mic(
        (all X:ex Y:(all Z:ex W:((p(X),q(Y))=>(p(Z),q(W))))) =>
        ((p(X),q(Y))=>(all Z:p(Z),all W:q(W)))
    ),
    write('NOTE: This is Pelletier problem 9, which is INVALID.'), nl,
    write('Both nanoCop and g4mic should detect this.'), nl,
    nl.

%% ============================================================================
%% SECTION 4: PEDAGOGICAL SCENARIOS
%% ============================================================================

%% Example 4.1: Teaching conditional reasoning
example_teaching_conditional :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('TEACHING EXAMPLE: Understanding Conditionals'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Common student mistake: Confusing p→q with q→p'), nl,
    nl,
    write('Let\'s test: If it rains, the ground is wet.'), nl,
    write('             Does this mean: If the ground is wet, it rained?'), nl,
    nl,
    write('Formula: (rain => wet) => (wet => rain)'), nl,
    nl,
    test((rain => wet) => (wet => rain)),
    write('The countermodel shows: The ground can be wet (from a hose)'), nl,
    write('without it having rained!'), nl,
    nl.

%% Example 4.2: Teaching quantifiers
example_teaching_quantifiers :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('TEACHING EXAMPLE: Quantifier Scope'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Everyone has a mother. Is there a universal mother?'), nl,
    nl,
    write('Formula: (∀x.∃y.mother(y,x)) → (∃y.∀x.mother(y,x))'), nl,
    nl,
    test((all X:ex Y:mother(Y,X)) => (ex Y:all X:mother(Y,X))),
    write('The countermodel shows: Different people have different mothers!'), nl,
    write('The existential quantifier must be IN SCOPE of the universal.'), nl,
    nl.

%% ============================================================================
%% SECTION 5: ADVANCED EXAMPLES
%% ============================================================================

%% Example 5.1: Equality reasoning
example_equality :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 5.1: Equality - Leibniz\'s Law'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Leibniz\'s Law: If a=b, then whatever is true of a is true of b'), nl,
    write('Formula: (a=b, p(a)) => p(b)'), nl,
    nl,
    test((a=b, p(a)) => p(b)),
    write('This should be VALID (requires equality axioms).'), nl,
    write('nanoCop handles this via leancop_equal/2.'), nl,
    nl.

%% Example 5.2: Function substitution
example_function_substitution :-
    write('═══════════════════════════════════════════════════════════'), nl,
    write('EXAMPLE 5.2: Function Substitution'), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    nl,
    write('Question: Does a=b imply f(a)=f(b)?'), nl,
    write('Formula: (a=b) => (f(a)=f(b))'), nl,
    nl,
    test((a=b) => (f(a)=f(b))),
    write('This tests congruence of function application.'), nl,
    write('Should be valid with proper equality handling.'), nl,
    nl.

%% ============================================================================
%% BATCH RUNNERS
%% ============================================================================

%% Run all propositional examples
run_propositional_examples :-
    nl,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║         PROPOSITIONAL LOGIC EXAMPLES                        ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl,
    nl,
    example_invalid_implication,
    example_modus_ponens,
    example_invalid_converse,
    example_excluded_middle,
    example_pierce,
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  Propositional examples completed!'), nl,
    write('═══════════════════════════════════════════════════════════'), nl, nl.

%% Run all first-order examples
run_fol_examples :-
    nl,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║         FIRST-ORDER LOGIC EXAMPLES                          ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl,
    nl,
    example_empty_domain,
    example_drinker,
    example_quantifier_swap,
    example_barbara,
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  First-order examples completed!'), nl,
    write('═══════════════════════════════════════════════════════════'), nl, nl.

%% Run comparison examples
run_comparison_examples :-
    nl,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║         G4MIC COMPARISON EXAMPLES                           ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl,
    nl,
    example_compare_invalid,
    example_compare_valid,
    example_compare_complex,
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  Comparison examples completed!'), nl,
    write('═══════════════════════════════════════════════════════════'), nl, nl.

%% Run teaching examples
run_teaching_examples :-
    nl,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║         PEDAGOGICAL EXAMPLES                                ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl,
    nl,
    example_teaching_conditional,
    example_teaching_quantifiers,
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  Teaching examples completed!'), nl,
    write('═══════════════════════════════════════════════════════════'), nl, nl.

%% Run ALL examples
run_all_examples :-
    run_propositional_examples,
    run_fol_examples,
    run_comparison_examples,
    run_teaching_examples,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║                ALL EXAMPLES COMPLETED!                      ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl, nl.

%% ============================================================================
%% QUICK START MENU
%% ============================================================================

menu :-
    nl,
    write('╔═════════════════════════════════════════════════════════════╗'), nl,
    write('║     NANOCOP COUNTERMODEL EXTRACTION - EXAMPLES              ║'), nl,
    write('╚═════════════════════════════════════════════════════════════╝'), nl,
    nl,
    write('INDIVIDUAL EXAMPLES:'), nl,
    nl,
    write('  Propositional Logic:'), nl,
    write('    example_invalid_implication.'), nl,
    write('    example_modus_ponens.'), nl,
    write('    example_invalid_converse.'), nl,
    write('    example_excluded_middle.'), nl,
    write('    example_pierce.'), nl,
    nl,
    write('  First-Order Logic:'), nl,
    write('    example_empty_domain.'), nl,
    write('    example_drinker.'), nl,
    write('    example_quantifier_swap.'), nl,
    write('    example_barbara.'), nl,
    nl,
    write('  Comparisons with g4mic:'), nl,
    write('    example_compare_invalid.'), nl,
    write('    example_compare_valid.'), nl,
    write('    example_compare_complex.'), nl,
    nl,
    write('  Teaching Scenarios:'), nl,
    write('    example_teaching_conditional.'), nl,
    write('    example_teaching_quantifiers.'), nl,
    nl,
    write('BATCH RUNNERS:'), nl,
    nl,
    write('  run_propositional_examples.'), nl,
    write('  run_fol_examples.'), nl,
    write('  run_comparison_examples.'), nl,
    write('  run_teaching_examples.'), nl,
    write('  run_all_examples.'), nl,
    nl,
    write('═════════════════════════════════════════════════════════════'), nl, nl.

:- initialization(menu).
