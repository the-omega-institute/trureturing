# A Boolean Bruhat interval with no magic word

## Abstract

A crystallographic type B₂ Boolean Bruhat interval has no magic word.

**Definition 1.1 (Braid exponent from a Cartan product).**

$$\begin{aligned}\operatorname{cartanExponent}\left(0\right) = 2\\\operatorname{cartanExponent}\left(1\right) = 3\\\operatorname{cartanExponent}\left(2\right) = 4\\\operatorname{cartanExponent}\left(3\right) = 6\\\forall a \in \mathbb{Z},\; \left(\neg (a \in \left\{0, 1, 2, 3\right\})\right) \Rightarrow \operatorname{cartanExponent}\left(a\right) = 0\end{aligned}$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.cartanExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

The input is an integer and the output is a natural number. Output zero encodes infinite braid exponent. Cartan products off the diagonal are nonnegative.

**Definition 1.2 (Cartan origin of a Coxeter matrix).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \operatorname{CartanOrigin}\left(M\right) \Leftrightarrow (\operatorname{Finite}\left(S\right) \land \left(\exists A \in \operatorname{Matrix}\left(S, S, \mathbb{Z}\right),\; \left(\forall i \in S,\; A\left(i, i\right) = 2\right) \land \left(\forall i \in S,\; \forall j \in S,\; i \ne j \Rightarrow \left(A\left(i, j\right) \le 0 \land \left(\left(A\left(i, j\right) = 0 \Leftrightarrow A\left(j, i\right) = 0\right) \land M\left(i, j\right) = \operatorname{cartanExponent}\left(A\left(i, j\right) \cdot A\left(j, i\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.CartanOrigin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

The index type S is finite. The integral matrix A has diagonal entries two, nonpositive off-diagonal entries and symmetric zero support. Off the diagonal its entry products determine the braid exponents of M.

**Definition 1.3 (Letters selected by a positional mask).**

$$\forall S \in Type,\; (\begin{aligned}\forall mask \in \operatorname{List}\left(Bool\right),\; \operatorname{retained}\left([], mask\right) = []\\\forall i \in S,\; \forall Q \in \operatorname{List}\left(S\right),\; \operatorname{retained}\left(List.cons\left(i, Q\right), []\right) = []\\\forall i \in S,\; \forall Q \in \operatorname{List}\left(S\right),\; \forall mask \in \operatorname{List}\left(Bool\right),\; \operatorname{retained}\left(List.cons\left(i, Q\right), List.cons\left(true, mask\right)\right) = List.cons\left(i, \operatorname{retained}\left(Q, mask\right)\right)\\\forall i \in S,\; \forall Q \in \operatorname{List}\left(S\right),\; \forall mask \in \operatorname{List}\left(Bool\right),\; \operatorname{retained}\left(List.cons\left(i, Q\right), List.cons\left(false, mask\right)\right) = \operatorname{retained}\left(Q, mask\right)\end{aligned})$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.retained` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

The result is a list on S. Square brackets with no entries denote the empty list. Each step pairs a letter with a Boolean, retaining the letter exactly when the Boolean is true. Recursion stops when either list is exhausted.

**Definition 1.4 (Product of selected letters).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall Q \in \operatorname{List}\left(S\right),\; \forall mask \in \operatorname{List}\left(Bool\right),\; \operatorname{positionalProduct}\left(cs, Q, mask\right) = CoxeterSystem.wordProd\left(cs, \operatorname{retained}\left(Q, mask\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.positionalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

The Coxeter system multiplies the simple reflections at the retained positions in their original order. The empty list has product the group identity. The length condition for a mask is imposed by MaskFor.

**Definition 1.5 (Masks of the required length and product).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall Q \in \operatorname{List}\left(S\right),\; \forall u \in W,\; \forall mask \in \operatorname{List}\left(Bool\right),\; \operatorname{MaskFor}\left(cs, Q, u, mask\right) \Leftrightarrow (List.length\left(mask\right) = List.length\left(Q\right) \land \operatorname{positionalProduct}\left(cs, Q, mask\right) = u)$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.MaskFor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

There is one Boolean entry per letter of Q, and the retained product is u. Distinct masks can have the same product, including when some retained words are nonreduced.

**Definition 1.6 (Bruhat comparison by subwords).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall u \in W,\; \forall w \in W,\; \operatorname{BruhatLE}\left(cs, u, w\right) \Leftrightarrow (\exists Q \in \operatorname{List}\left(S\right),\; CoxeterSystem.IsReduced\left(cs, Q\right) \land \left(CoxeterSystem.wordProd\left(cs, Q\right) = w \land \left(\exists mask \in \operatorname{List}\left(Bool\right),\; \operatorname{MaskFor}\left(cs, Q, u, mask\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.BruhatLE` (`✓ std3`).

*Citation.* Anders Björner and Francesco Brenti (2005). *The Bruhat Order*. DOI: [10.1007/3-540-27596-7_2](https://doi.org/10.1007/3-540-27596-7_2). URL: <https://doi.org/10.1007/3-540-27596-7_2>.

*Commentary.*

Björner and Brenti’s subword criterion uses a reduced expression of the upper element and a reduced subword for the lower element. The deletion condition can shorten any retained word to a reduced subword with the same product, so the existence tests coincide.

**Definition 1.7 (The full Bruhat interval).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall v \in W,\; \forall w \in W,\; \operatorname{BruhatInterval}\left(cs, v, w\right) = \{u: W \mid \operatorname{BruhatLE}\left(cs, v, u\right) \land \operatorname{BruhatLE}\left(cs, u, w\right)\}$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.BruhatInterval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anders Björner and Francesco Brenti (2005). *The Bruhat Order*. DOI: [10.1007/3-540-27596-7_2](https://doi.org/10.1007/3-540-27596-7_2). URL: <https://doi.org/10.1007/3-540-27596-7_2>.

*Commentary.*

The braces denote the subtype of W containing every element satisfying both Bruhat comparisons.

**Definition 1.8 (Boolean order on the interval).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall v \in W,\; \forall w \in W,\; \operatorname{IsHypercube}\left(cs, v, w\right) \Leftrightarrow (\exists n \in \mathbb{N},\; \exists f \in \operatorname{Equiv}\left(\operatorname{BruhatInterval}\left(cs, v, w\right), \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \forall x \in \operatorname{BruhatInterval}\left(cs, v, w\right),\; \forall y \in \operatorname{BruhatInterval}\left(cs, v, w\right),\; \operatorname{BruhatLE}\left(cs, Subtype.val\left(x\right), Subtype.val\left(y\right)\right) \Leftrightarrow f\left(x\right) \subseteq f\left(y\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.IsHypercube` (`✓ std3`).

*Citation.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

The equivalence f is a bijection from the full interval to the finite subsets of Fin n. Subtype.val takes an interval element to its underlying group element. The bijection preserves and reflects order for every pair.

**Definition 1.9 (A magic word for the interval).**

$$\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall v \in W,\; \forall w \in W,\; \forall Q \in \operatorname{List}\left(S\right),\; \operatorname{MagicFor}\left(cs, v, w, Q\right) \Leftrightarrow (CoxeterSystem.IsReduced\left(cs, Q\right) \land \left(CoxeterSystem.wordProd\left(cs, Q\right) = w \land \left(\exists mask \in \operatorname{List}\left(Bool\right),\; \operatorname{MaskFor}\left(cs, Q, v, mask\right) \land \left(\forall other \in \operatorname{List}\left(Bool\right),\; \operatorname{MaskFor}\left(cs, Q, v, other\right) \Rightarrow other = mask\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.MagicFor` (`✓ std3`).

*Citation.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

Q is reduced and has product w. Exactly one length-matched Boolean mask has product v. The count includes masks with nonreduced retained words.

**Definition 1.10 (Elek’s Conjecture 3.3).**

$$claim \Leftrightarrow (\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall v \in W,\; \forall w \in W,\; \operatorname{CartanOrigin}\left(M\right) \Rightarrow \left(\operatorname{BruhatLE}\left(cs, v, w\right) \Rightarrow \left(\operatorname{IsHypercube}\left(cs, v, w\right) \Leftrightarrow (\exists Q \in \operatorname{List}\left(S\right),\; \operatorname{MagicFor}\left(cs, v, w, Q\right))\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.claim` (`✓ std3`).

*Citation.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

“A Bruhat interval [v,w] is a hypercube if and only if there exists a magic word Q for [v,w].”

The Cartan-origin hypothesis represents the Kac–Moody Weyl-group setting. The group itself may be infinite. The comparison hypothesis restricts the claim to pairs v ≤ w.

In sts the masks 000 and 101 both give the identity, and 101 retains the nonreduced word ss. Deletion preserves the existence of a product and can change the number of masks.

**Theorem 1.11 (The type B₂ counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/elek-2026-magic-word-converse` (refuted) by `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elek-2026-magic-word-converse","declaration_gid":"D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Acknowledgement.* Anders Björner and Francesco Brenti (2005). *The Bruhat Order*. DOI: [10.1007/3-540-27596-7_2](https://doi.org/10.1007/3-540-27596-7_2). URL: <https://doi.org/10.1007/3-540-27596-7_2>.

*Acknowledgement.* Vincent Umutabazi (2022). *Zircons and smooth Bruhat intervals in symmetric groups*. DOI: [10.48550/arXiv.2206.06538](https://doi.org/10.48550/arXiv.2206.06538). URL: <https://arxiv.org/abs/2206.06538v1>.

*Commentary.*

Use the canonical presentation with simple reflections s,t and braid exponent four, induced by the type B₂ Cartan matrix. The homomorphism to the dihedral group of order eight sends s and t to two adjacent reflections. Testing words through length three under this map and using a shortest word in the presentation gives length(sts) = 3 and forces sts as its only reduced expression.

The subword products below sts are e, s, t, st, ts and sts. Exactly s, st, ts and sts are above s. The Bruhat comparisons on these four elements agree in both directions with subset inclusion under the map to the empty set, {0}, {1} and {0,1}, respectively.

The masks 100 and 001 retain different positions of the only reduced word sts and both give s. The Boolean-to-magic implication therefore fails. Umutabazi uses the same interval for a left-descent criterion. Elek’s Lemma 2.17 gives the related last-letter obstruction to uniqueness even among reduced subwords.

## References

- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.BruhatInterval`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.BruhatLE`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.CartanOrigin`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.IsHypercube`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.MagicFor`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.MaskFor`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.cartanExponent`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.positionalProduct`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.retained`
