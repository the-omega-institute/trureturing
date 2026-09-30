# Maximal R-Cliques in Finite Connected Racks

## Abstract

Finite conjugation racks answer Problem 5.22 negatively and Problem 5.24 positively.

**Definition 1.1 (Right racks).**

$$\forall Q \in Type,\; \forall mul \in Q \to \left(Q \to Q\right),\; (\operatorname{IsRack}\left(mul\right)) \Leftrightarrow ((\forall y \in Q,\; \operatorname{Bijective}\left((\lambda x, \operatorname{mul}\left(x, y\right))\right)) \land (\forall x \in Q,\; \forall y \in Q,\; \forall z \in Q,\; \operatorname{mul}\left(\operatorname{mul}\left(x, y\right), z\right) = \operatorname{mul}\left(\operatorname{mul}\left(x, z\right), \operatorname{mul}\left(y, z\right)\right)))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsRack` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

On printed page 13 the paper states: "A magma (Q, ∗) is a right quasigroup if for every x ∈ Q the right translation Rₓ is a permutation of Q." It then states: "A right quasigroup (Q, ∗) is a rack if it satisfies right self-distributivity (x ∗ y) ∗ z = (x ∗ z) ∗ (y ∗ z)." Here mul(x,y) means x ∗ y. Bijective applies to x ↦ mul(x,y), for every y; the order of the operands is the paper's right-hand convention.

**Definition 1.2 (Commuting right translations).**

$$\forall Q \in Type,\; \forall mul \in Q \to \left(Q \to Q\right),\; \forall a \in Q,\; \forall b \in Q,\; (\operatorname{RCommute}\left(mul, a, b\right)) \Leftrightarrow (\forall x \in Q,\; \operatorname{mul}\left(\operatorname{mul}\left(x, a\right), b\right) = \operatorname{mul}\left(\operatorname{mul}\left(x, b\right), a\right))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.RCommute` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed pages 17–18 state: "Let ∼ be the binary relation on a right quasigroup Q defined by a ∼ b if and only if [Ra, Rb] = 1." "If a ∼ b, we say that a and b R-commute." For bijective right translations their commutator is the identity exactly when the two compositions agree. The definition expresses that equality at every x, without replacing it by commutation of group elements.

**Definition 1.3 (R-cliques).**

$$\forall Q \in Type,\; \forall mul \in Q \to \left(Q \to Q\right),\; \forall C \in \operatorname{Finset}\left(Q\right),\; (\operatorname{IsRClique}\left(mul, C\right)) \Leftrightarrow (\forall a \in Q,\; (a \in C) \Rightarrow (\forall b \in Q,\; (b \in C) \Rightarrow (\operatorname{RCommute}\left(mul, a, b\right))))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsRClique` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed page 18 states: "A subset C of a right quasigroup Q is an R-clique if a ∼ b for every a, b ∈ C." C is a Finset Q, representing a subset of a finite carrier. The quantifiers include equal members as well as distinct members.

**Definition 1.4 (Inclusion maximality).**

$$\forall Q \in Type,\; \forall mul \in Q \to \left(Q \to Q\right),\; \forall C \in \operatorname{Finset}\left(Q\right),\; (\operatorname{IsMaximalRClique}\left(mul, C\right)) \Leftrightarrow ((\operatorname{IsRClique}\left(mul, C\right)) \land (\forall D \in \operatorname{Finset}\left(Q\right),\; (\operatorname{IsRClique}\left(mul, D\right)) \Rightarrow ((C \subseteq D) \Rightarrow (D = C))))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsMaximalRClique` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed page 19, Proposition 5.15, states: "Let Q be a rack and let C be a maximal R-clique of Q. Then C is a subrack of Q." Its proof uses "Since C is maximal, b ∈ C." Thus maximal means that every R-clique D containing C equals C; it does not mean maximum cardinality.

**Definition 1.5 (Connected racks).**

$$\forall Q \in Type,\; \forall mul \in Q \to \left(Q \to Q\right),\; (\operatorname{Connected}\left(mul\right)) \Leftrightarrow (\forall x \in Q,\; \forall y \in Q,\; \exists l \in \operatorname{List}\left(Q\right),\; \operatorname{foldl}\left(mul, x, l\right) = y)$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.Connected` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed page 17 states: "Recall that a rack Q is connected if the permutation group Mltr(Q) acts transitively on Q." Connected is encoded by a positive finite word l of right translations carrying each x to each y. foldl(mul,x,l) denotes l.foldl mul x: starting at x, apply the right translations listed in l in order. On a finite rack each right translation is a finite-order permutation, so its inverse is a positive power. Consequently positive-word reachability is precisely transitivity of the generated right multiplication group in the finite-rack hypotheses below.

**Definition 1.6 (Problem 5.22).**

$$(claim22) \Leftrightarrow (\forall Q \in Type,\; (\operatorname{Fintype}\left(Q\right)) \Rightarrow ((\operatorname{DecidableEq}\left(Q\right)) \Rightarrow (\forall mul \in Q \to \left(Q \to Q\right),\; (\operatorname{IsRack}\left(mul\right)) \Rightarrow ((\operatorname{Connected}\left(mul\right)) \Rightarrow (\forall C \in \operatorname{Finset}\left(Q\right),\; \forall D \in \operatorname{Finset}\left(Q\right),\; (\operatorname{IsMaximalRClique}\left(mul, C\right)) \Rightarrow ((\operatorname{IsMaximalRClique}\left(mul, D\right)) \Rightarrow (\operatorname{FinsetCard}\left(C\right) = \operatorname{FinsetCard}\left(D\right))))))))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.claim22` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed page 21: "Problem 5.22. Do all maximal R-cliques in a finite connected rack have the same size?" claim22 is the universal affirmative answer, with two inclusion-maximal finsets C and D and their Finset.card values.

**Definition 1.7 (Problem 5.24).**

$$(claim24) \Leftrightarrow (\forall Q \in Type,\; (\operatorname{Fintype}\left(Q\right)) \Rightarrow ((\operatorname{DecidableEq}\left(Q\right)) \Rightarrow (\forall mul \in Q \to \left(Q \to Q\right),\; (\operatorname{IsRack}\left(mul\right)) \Rightarrow ((\operatorname{Connected}\left(mul\right)) \Rightarrow (\forall C \in \operatorname{Finset}\left(Q\right),\; (\operatorname{IsMaximalRClique}\left(mul, C\right)) \Rightarrow (\operatorname{FinsetCard}\left(C\right) \mid \operatorname{FintypeCard}\left(Q\right)))))))$$

*Formalization.* `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.claim24` (`✓ std3`).

*Citation.* Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský (2026). *Algebraic invariants of multi-virtual links*. DOI: [10.1016/j.jalgebra.2026.03.018](https://doi.org/10.1016/j.jalgebra.2026.03.018). URL: <https://arxiv.org/abs/2504.09368v1>.

*Commentary.*

Printed page 21: "Problem 5.24. Does there exist a finite connected rack Q and a maximal R-clique C of Q such that |C| does not divide |Q|?" claim24 is the negation of this existence assertion: every maximal R-clique in every finite connected rack has cardinality dividing the carrier cardinality. Refuting claim24 answers the printed existence question Yes. FinsetCard(C) means C.card and FintypeCard(Q) means Fintype.card Q. Both claims quantify over Q : Type with Fintype Q and DecidableEq Q and over every binary operation mul; these structures impose no additional finite-rack restriction.

**Theorem 1.8 (Unequal maximal R-cliques).**

$$\neg claim22$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the conjugation rack of the 105 fixed-point-free involutions in S₈, x ∗ y = y⁻¹xy. On points 0 through 7, the seven translations tₐ(x) = x XOR a for a = 1 through 7 form a maximal R-clique. The nine permutations pₐᵦ for a,b = 1,2,3, acting by x XOR a on the lower block and by 4 + ((x−4) XOR b) on the upper block, form another maximal R-clique. Their cardinalities 7 and 9 differ. Fin 105 indexes the literal permutation vectors and conjugation table; positive right-translation words certify connectedness.

**Theorem 1.9 (A size that does not divide the carrier size).**

$$\neg claim24$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the conjugation rack of the 70 three-cycles in S₇. The subset {(1 2 3),(1 3 2),(4 5 6),(4 6 5)} is a maximal R-clique of size 4, and 4 does not divide 70. Fin 70 indexes the literal permutation vectors and conjugation table. Positive right-translation words certify connectedness. This refutes universal divisibility and supplies the existence requested in Problem 5.24.

## References

- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.Connected`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsMaximalRClique`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsRClique`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.IsRack`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.RCommute`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.claim22`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.claim24`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result22`
- Truth anchor: `D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.result24`
