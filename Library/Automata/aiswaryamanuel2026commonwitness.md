---
bibkey: aiswaryamanuel2026commonwitness
authors: C. Aiswarya, Amaldev Manuel, Saina Sunny
year: 2026
title: "Deciding Conjugacy of a Rational Relation"
doi: null
url: https://arxiv.org/abs/2307.06777v4
claim: "Definition 5 and Lemma 6 state the common-witness finite-family principle for word-pair relations."
strata_touched:
  - D5/S1/Words/Powers/CommonWitnessCompactness
license: citation-only
triage: anchor
---

## Verified locator

C. Aiswarya, Amaldev Manuel and Saina Sunny, *Deciding Conjugacy of a Rational Relation*, arXiv:2307.06777v4, 7 July 2026.

Source: https://arxiv.org/abs/2307.06777v4. Definition 5 is in section 3; Lemma 6 is in section 4.2.

Definition 5 and Lemma 6, printed p. 25, state that an infinite set of pairs with a common witness on every finite subset has a common witness. The source works over a finite alphabet and uses the two witness orientations from Definition 5.

## Statement and correspondence

The formal result `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite` uses literal `List alpha` pairs and `Set (List alpha × List alpha)`. Its public `CommonWitness G` is the disjunction of one global inner witness, satisfying `a ++ z = z ++ b` for every pair in `G`, or one global outer witness, satisfying `z ++ a = b ++ z` for every pair in `G`. The finite-subset direction retains the same disjunction independently for each finite subset; no orientation is added as a premise.

The word argument uses cancellation and cyclic centralizers, with classical case splitting on the family. The existing `ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut` supplies the single-equation short-cut normal form for a nonempty first component. Its witnesses are prefix-comparable, enabling transport through the cyclic centralizer. If a row has two distinct shared witnesses, that transport makes it hold for every anchor witness; otherwise a finite three-row obstruction stabilizes the unique candidate. A relation with no nonempty first component is neutral by singleton length cancellation. The outer orientation is reduced by the involution `(a,b) ↦ (b,a)`. For the global orientation, either every finite subset has an inner witness, or a fixed finite inner obstruction forces the outer orientation on its union with every finite subset. The empty relation, empty words, empty and infinite alphabets, and finite and infinite relations remain in scope.

The cited paper states the finite-alphabet version and is used as a literature locator and source boundary. The arbitrary-universe, arbitrary-alphabet List statement, the global-orientation disjunction, and the edge cases are kernel-checked here. No compact topological model, finite alphabet instance, pairwise-only replacement, infinite-word endpoint, or group-element statement is used.

## License

Citation and mathematical paraphrase only. No source prose, figures, or external proof code are copied, and public availability of the preprint is not treated as a permissive code license.
