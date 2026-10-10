# OccupationHilbertContractions

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Definition 1.1 (CanonicalSequence).**

$$\operatorname{CanonicalSequence}. \operatorname{mk} : (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})\to (\forall (i : \mathbb{N}), 0 \leq \operatorname{coeff} i)\to (\operatorname{Summable} \operatorname{fun} (i : \mathbb{N})\mapsto( \operatorname{coeff} i)^{2})\to \sum ' (i : \mathbb{N}),( \operatorname{coeff} i)^{2}= 1 \to \operatorname{CanonicalSequence}$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.CanonicalSequence` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.2 (weighted_schur).**

$$\forall \{\iota : \operatorname{Type}\}[\operatorname{Fintype} \iota](K : \iota \to \iota \to \mathbb{R}), (\forall (i j : \iota), 0 \leq K i j)\to (\forall (i j : \iota), K i j = K j i)\to \forall (f : \iota \to \mathbb{R}), (\forall (i : \iota), 0 < f i)\to \forall (z : \iota \to \mathbb{C}), (\sum i : \iota, \sum j : \iota, ((K i j): \mathbb{C})* \operatorname{star} (z i)* z j). \operatorname{re} \leq \sum i : \iota,( \left\lVert z i  \right\rVert)^{2}* ((\sum j : \iota, K i j * f j)/ f i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.weighted_schur` (`✓ std3`). ∎

*Citation.* Issai Schur (1911). *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen Veränderlichen*. DOI: [10.1515/crll.1911.140.1](https://doi.org/10.1515/crll.1911.140.1). URL: <https://doi.org/10.1515/crll.1911.140.1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.3 (pairKernel_weighted_row).**

$$\forall \{\iota : \operatorname{Type}\}[\operatorname{Fintype} \iota][\operatorname{DecidableEq} \iota](a : \mathbb{R})(p : \iota \to \mathbb{R}), 0 \leq a \to (\forall (i : \iota), 0 \leq p i)\to \forall (D : \operatorname{Finset} \iota), (\sum E : \operatorname{Finset} \iota, \operatorname{pairKernel} p D E * \operatorname{comparisonVector} a p E)/ \operatorname{comparisonVector} a p D \leq (\sum i \in D, p i)+ ((D. \operatorname{card} : \mathbb{R})+ a * (\sum i \in D, p i))* (\sum j \in D ^{c}, p j / (1 + a * p j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_weighted_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The product comparison vector bounds every pair-incidence row. A zero coefficient receives weight one, so the vector remains positive.

**Theorem 1.4 (pairKernel_row_bound).**

$$\forall \{\iota : \operatorname{Type}\}[\operatorname{Fintype} \iota][\operatorname{DecidableEq} \iota](p : \iota \to \mathbb{R})(m : \mathbb{N}), 1 \leq m \to \forall (\alpha : \mathbb{R}), 0 \leq \alpha \to (\forall (i : \iota), 0 \leq p i)\to (\forall (i : \iota), p i \leq \alpha)\to (\sum i : \iota, p i)\leq 1 \to 2 * (m : \mathbb{R})* \alpha \leq 1 \to \forall (D : \operatorname{Finset} \iota), D. \operatorname{card} \leq m \to (\sum E : \operatorname{Finset} \iota, \operatorname{pairKernel} p D E * \operatorname{comparisonVector} ((m : \mathbb{R})- 1)p E)/ \operatorname{comparisonVector} ((m : \mathbb{R})- 1)p D \leq (m : \mathbb{R})- (m : \mathbb{R})* ((m : \mathbb{R})- 1)* (\sum i : \iota,( p i)^{2})+ 5 / 2 *( (m : \mathbb{R}))^{3}*( \alpha)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_row_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.5 (pairKernel_row).**

$$\forall \{\iota : \operatorname{Type}\}[\operatorname{Fintype} \iota][\operatorname{DecidableEq} \iota](p : \iota \to \mathbb{R})(f : \operatorname{Finset} \iota \to \mathbb{R})(D : \operatorname{Finset} \iota), \sum E : \operatorname{Finset} \iota, \operatorname{pairKernel} p D E * f E = \sum i \in D, \operatorname{Real}. \operatorname{sqrt} (p i)* \sum j \in (D. \operatorname{erase} i)^{c}, \operatorname{Real}. \operatorname{sqrt} (p j)* f (\operatorname{insert} j (D. \operatorname{erase} i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.6 (pairKernel).**

$$\forall (\iota : \operatorname{Type})[\operatorname{Fintype} \iota][\operatorname{DecidableEq} \iota](p : \iota \to \mathbb{R})(D : \operatorname{Finset} \iota)(E : \operatorname{Finset} \iota), (\operatorname{pairKernel} (p)(D)(E): \mathbb{R})= (\operatorname{dotProduct} (\operatorname{fun} (R : \operatorname{Finset} \iota)\mapsto \operatorname{pairIncidence} p R D)(\operatorname{fun} (R : \operatorname{Finset} \iota)\mapsto \operatorname{pairIncidence} p R E))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.7 (pairIncidence).**

$$\forall (\iota : \operatorname{Type})[\operatorname{Fintype} \iota][\operatorname{DecidableEq} \iota](p : \iota \to \mathbb{R})(R : \operatorname{Finset} \iota)(D : \operatorname{Finset} \iota), (\operatorname{pairIncidence} (p)(R)(D): \mathbb{R})= (\sum i : \iota, \operatorname{if} i \in D \land R = D. \operatorname{erase} i \operatorname{then} \operatorname{Real}. \operatorname{sqrt} (p i)\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairIncidence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.8 (denominator_sum_bound).**

$$\forall \{\iota : \operatorname{Type}\}[\operatorname{Fintype} \iota](p : \iota \to \mathbb{R})(a \alpha : \mathbb{R}), 0 \leq a \to 0 \leq \alpha \to (\forall (i : \iota), 0 \leq p i)\to (\forall (i : \iota), p i \leq \alpha)\to (\sum i : \iota, p i)\leq 1 \to \sum i : \iota, p i / (1 + a * p i)\leq 1 - a * (\sum i : \iota,( p i)^{2})+( a)^{2}*( \alpha)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.denominator_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The rational cubic remainder is bounded using the coefficient cap and total mass. This estimate retains the negative fourth-moment correction for unrenormalized finite cutoffs.

**Definition 1.9 (comparisonWeight).**

$$\forall (a : \mathbb{R})(p : \mathbb{R}), (\operatorname{comparisonWeight} (a)(p): \mathbb{R})= (\operatorname{if} p = 0 \operatorname{then} 1 \operatorname{else} \operatorname{Real}. \operatorname{sqrt} p / (1 + a * p))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.10 (comparisonVector_pos).**

$$\forall \{\iota : \operatorname{Type}\}(a : \mathbb{R})(p : \iota \to \mathbb{R}), 0 \leq a \to (\forall (i : \iota), 0 \leq p i)\to \forall (D : \operatorname{Finset} \iota), 0 < \operatorname{comparisonVector} a p D$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonVector_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.11 (comparisonVector).**

$$\forall (\iota : \operatorname{Type})(a : \mathbb{R})(p : \iota \to \mathbb{R})(D : \operatorname{Finset} \iota), (\operatorname{comparisonVector} (a)(p)(D): \mathbb{R})= (\prod i \in D, \operatorname{comparisonWeight} a (p i))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.12 (adapted_hilbert_basis).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{CompleteSpace} E]\{\iota : \operatorname{Type}\}\{v : \iota \to E\}, \operatorname{Orthonormal} \mathbb{C} v \to \exists (w : \operatorname{Set} E)(b : \operatorname{HilbertBasis} (w : \operatorname{Type})\mathbb{C} E), \operatorname{Set}. \operatorname{range} v \subseteq w \land (b : (w : \operatorname{Type})\to E)= \operatorname{Subtype}. \operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.adapted_hilbert_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.13 (annihilationCoordinate).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(i : \mathbb{N})(R : \operatorname{Finset} \mathbb{N}), (\operatorname{annihilationCoordinate} (\psi)(i)(R): \mathbb{C})= (\operatorname{if} \neg (i \in R)\land (\operatorname{insert} i R). \operatorname{card} = N \operatorname{then}( (- 1))^{\{k \in R | k < i\}.\operatorname{card}}* (\psi : (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)\langle \operatorname{insert} i R,...\rangle\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.annihilationCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.14 (canonicalRayleigh).**

$$\forall (N : \mathbb{N})(c : \operatorname{CanonicalSequence})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{canonicalRayleigh} (c)(\psi): \mathbb{R})= (2 * \sum ' (R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}),( \left\lVert \sum ' (i : \mathbb{N}), ((c. \operatorname{coeff} i): \mathbb{C})* \operatorname{pairCoordinate} \psi (2 * i)(2 * i + 1)(R : \operatorname{Finset} \mathbb{N}) \right\rVert)^{2})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.canonicalRayleigh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.15 (coordinateClaim).**

$$(\operatorname{coordinateClaim} : \operatorname{Prop})= (\forall (m : \mathbb{N}), 1 \leq m \to \forall (c : \operatorname{CanonicalSequence})(\alpha : \mathbb{R}), (\forall (i : \mathbb{N}),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to 2 * (m : \mathbb{R})* \alpha \leq 1 \to \forall (\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \left\lVert \psi  \right\rVert= 1 \to \operatorname{canonicalRayleigh} c \psi \leq 2 * (m : \mathbb{R})* (1 - ((m : \mathbb{R})- 1)* (\sum ' (i : \mathbb{N}),( c. \operatorname{coeff} i)^{4})+ 5 / 8 *( (2 * (m : \mathbb{R})* \alpha))^{2}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.16 (coordinateRename).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(e : \operatorname{Function}. \operatorname{Embedding} A B)(h : \operatorname{Orthonormal} \mathbb{C} (\operatorname{fun} a : A \mapsto (\operatorname{lp}. \operatorname{single} 2 (e a)(1 : \mathbb{C}): \operatorname{lp} (\operatorname{fun} _ : B \mapsto \mathbb{C})2))), (\operatorname{coordinateRename} (e): (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)\to_{li} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))= (h. \operatorname{orthogonalFamily}. \operatorname{linearIsometry})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.17 (coordinateRename_image).**

$$\forall \{A : \operatorname{Type}\}\{B : \operatorname{Type}\}(e : \operatorname{Function}. \operatorname{Embedding} A B)(\psi : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2))(a : A), (((\operatorname{coordinateRename} e : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))\psi): (i : B)\to (\operatorname{fun} (_ : B)\mapsto \mathbb{C})i)((e : A \to B)a)= (\psi : (i : A)\to (\operatorname{fun} (_ : A)\mapsto \mathbb{C})i)a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.18 (coordinateRename_outside).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(e : \operatorname{Function}. \operatorname{Embedding} A B)(\psi : \operatorname{lp} (\operatorname{fun} _ : A \mapsto \mathbb{C})2)(b : B), \neg (b \in \operatorname{Set}. \operatorname{range} e)\to \operatorname{coordinateRename} e \psi b = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.19 (countable_norm_sq).**

$$\forall \{A : \operatorname{Type}\}(\psi : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)),( \left\lVert \psi  \right\rVert)^{2}= \sum ' (a : A),( \left\lVert (\psi : (i : A)\to (\operatorname{fun} (_ : A)\mapsto \mathbb{C})i)a  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.20 (countable_norm_sq_summable).**

$$\forall \{A : \operatorname{Type}\}(\psi : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)), \operatorname{Summable} \operatorname{fun} (a : A)\mapsto( \left\lVert (\psi : (i : A)\to (\operatorname{fun} (_ : A)\mapsto \mathbb{C})i)a  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_norm_sq_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.21 (countable_pair_sign).**

$$\forall \{N : \mathbb{N}\}(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(i : \mathbb{N})(R : \operatorname{Finset} \mathbb{N}), \neg (2 * i \in R)\to \neg (2 * i + 1 \in R)\to \forall (\operatorname{hN} : (\operatorname{insert} (2 * i)(\operatorname{insert} (2 * i + 1)R)). \operatorname{card} = N), \operatorname{pairCoordinate} \psi (2 * i)(2 * i + 1)R = (\psi : (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)\langle \operatorname{insert} (2 * i)(\operatorname{insert} (2 * i + 1)R), \operatorname{hN}\rangle$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_pair_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.22 (lift).**

$$\forall (d : \mathbb{N})(N : \mathbb{N})(\psi : \operatorname{EuclideanSpace} \mathbb{C} \{s : \operatorname{Fin} d \to \operatorname{Bool} / / \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N\}), (\operatorname{lift} (\psi): \operatorname{EuclideanSpace} \mathbb{C} (\operatorname{Fin} d \to \operatorname{Bool}))= (\operatorname{WithLp}. \operatorname{toLp} 2 \operatorname{fun} (s : \operatorname{Fin} d \to \operatorname{Bool})\mapsto \operatorname{if} h : \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{FockSpace}. \operatorname{ForbiddenNeighbourDeterminant}. \operatorname{occupationCount} s = N \operatorname{then} \psi. \operatorname{ofLp} \langle s, h\rangle\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.23 (orthonormal_countable).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E]\{\iota : \operatorname{Type}\}[\operatorname{TopologicalSpace}. \operatorname{SeparableSpace} E]\{v : \iota \to E\}, \operatorname{Orthonormal} \mathbb{C} v \to \operatorname{Countable} \iota$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.orthonormal_countable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.24 (pairContract).**

$$\forall (N : \mathbb{N})(i : \mathbb{N})(j : \mathbb{N}), (\operatorname{pairContract} (N)(i)(j): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))= (\operatorname{partialPullCLM} (\operatorname{pairValid} N i j)(\operatorname{pairInsert} N i j)... (\operatorname{pairPhase} i j)...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairContract` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.25 (occupiedOrderedPairEquiv).**

$$\forall (N i j : \mathbb{N})(\operatorname{hij} : i \neq j), (\operatorname{occupiedOrderedPairEquiv} N i j \operatorname{hij} : \{R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}/ / \operatorname{pairValid} N i j R\}\equiv \{S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}/ / i \in S. \operatorname{val} \land j \in S. \operatorname{val}\})= \{\operatorname{toFun} := \operatorname{fun} (R : \{R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}/ / \operatorname{pairValid} N i j R\})\mapsto \langle \operatorname{pairInsert} N i j R,...\rangle, \operatorname{invFun} := \operatorname{fun} (S : \{S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}/ / i \in S. \operatorname{val} \land j \in S. \operatorname{val}\})\mapsto \langle \langle (S. \operatorname{val}. \operatorname{val}. \operatorname{erase} i). \operatorname{erase} j,...\rangle,...\rangle, \operatorname{left}_{\operatorname{inv}} :=..., \operatorname{right}_{\operatorname{inv}} :=...\}$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.occupiedOrderedPairEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

Ordered pair insertion and removal give inverse maps on the occupied configurations. Proof fields are omitted by proof irrelevance.

**Theorem 1.26 (ordered_pair_energy).**

$$\forall (N i j : \mathbb{N})(\psi : \operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2),( \left\lVert \operatorname{pairContract} N i j \psi  \right\rVert)^{2}= (\sum ' (S : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\}), \operatorname{if} i \neq j \land i \in S. \operatorname{val} \land j \in S. \operatorname{val} \operatorname{then}( \left\lVert \psi S  \right\rVert)^{2}\operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.ordered_pair_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

An ordered contraction counts exactly the configurations containing both distinct modes.

**Theorem 1.27 (pairContract_apply).**

$$\forall (N i j : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}), (((\operatorname{pairContract} N i j : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\psi): (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})i)R = \operatorname{pairCoordinate} \psi i j (R : \operatorname{Finset} \mathbb{N})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairContract_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.28 (pairCoordinate).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(i : \mathbb{N})(j : \mathbb{N})(R : \operatorname{Finset} \mathbb{N}), (\operatorname{pairCoordinate} (\psi)(i)(j)(R): \mathbb{C})= (\operatorname{if} i \neq j \land \neg (i \in R)\land \neg (j \in R)\land (\operatorname{insert} i (\operatorname{insert} j R)). \operatorname{card} = N \operatorname{then}( (- 1))^{\{k \in R | k < j\}. \operatorname{card} + \{k \in \operatorname{insert} j R | k < i\}. \operatorname{card}}* (\psi : (i : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\to (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})i)\langle \operatorname{insert} i (\operatorname{insert} j R),...\rangle\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.29 (pairInsert).**

$$\forall (N : \mathbb{N})(i : \mathbb{N})(j : \mathbb{N})(R : \{R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}/ / \operatorname{pairValid} N i j R\}), (\operatorname{pairInsert} (N)(i)(j)(R): \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})= (\langle \operatorname{insert} i (\operatorname{insert} j ((R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}): \operatorname{Finset} \mathbb{N})),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairInsert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.30 (pairPhase).**

$$\forall (N : \mathbb{N})(i : \mathbb{N})(j : \mathbb{N})(R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}), (\operatorname{pairPhase} (i)(j)(R): \mathbb{C})= (((- 1))^{\{k \in (R : \operatorname{Finset} \mathbb{N})| k < j\}. \operatorname{card} + \{k \in \operatorname{insert} j (R : \operatorname{Finset} \mathbb{N})| k < i\}. \operatorname{card}})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.31 (pairValid).**

$$\forall (N : \mathbb{N})(i : \mathbb{N})(j : \mathbb{N})(R : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\}), (\operatorname{pairValid} (N)(i)(j)(R): \operatorname{Prop})= (i \neq j \land \neg (i \in (R : \operatorname{Finset} \mathbb{N}))\land \neg (j \in (R : \operatorname{Finset} \mathbb{N}))\land (\operatorname{insert} i (\operatorname{insert} j (R : \operatorname{Finset} \mathbb{N}))). \operatorname{card} = N)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.32 (partialPull).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(P : B \to \operatorname{Prop})(f : \{b : B / / P b\}\to A)(\operatorname{hf} : \operatorname{Function}. \operatorname{Injective} f)(\operatorname{phase} : B \to \mathbb{C})(\operatorname{hphase} : \forall (b : B), \left\lVert \operatorname{phase} b  \right\rVert\leq 1)(\psi : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)), (\operatorname{partialPull} (P)(f)(\operatorname{hf})(\operatorname{phase})(\operatorname{hphase})(\psi): (\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))= (\langle \operatorname{partialPullRaw} P f \operatorname{phase} \psi,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPull` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.33 (partialPullCLM).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(P : B \to \operatorname{Prop})(f : \{b : B / / P b\}\to A)(\operatorname{hf} : \operatorname{Function}. \operatorname{Injective} f)(\operatorname{phase} : B \to \mathbb{C})(\operatorname{hphase} : \forall (b : B), \left\lVert \operatorname{phase} b  \right\rVert\leq 1), (\operatorname{partialPullCLM} (P)(f)(\operatorname{hf})(\operatorname{phase})(\operatorname{hphase}): (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))= ((\operatorname{partialPullLinear} P f \operatorname{hf} \operatorname{phase} \operatorname{hphase}). \operatorname{mkContinuous} 1...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullCLM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.34 (partialPullLinear).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(P : B \to \operatorname{Prop})(f : \{b : B / / P b\}\to A)(\operatorname{hf} : \operatorname{Function}. \operatorname{Injective} f)(\operatorname{phase} : B \to \mathbb{C})(\operatorname{hphase} : \forall (b : B), \left\lVert \operatorname{phase} b  \right\rVert\leq 1), (\operatorname{partialPullLinear} (P)(f)(\operatorname{hf})(\operatorname{phase})(\operatorname{hphase}): (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)\to_{l} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : B)\mapsto \mathbb{C})2))= (\{\operatorname{toFun} := \operatorname{partialPull} P f \operatorname{hf} \operatorname{phase} \operatorname{hphase}, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullLinear` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.35 (partialPullRaw).**

$$\forall (A : \operatorname{Type})(B : \operatorname{Type})(P : B \to \operatorname{Prop})(f : \{b : B / / P b\}\to A)(\operatorname{phase} : B \to \mathbb{C})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2))(b : B), (\operatorname{partialPullRaw} (P)(f)(\operatorname{phase})(\psi)(b): \mathbb{C})= (\operatorname{if} h : P b \operatorname{then} \operatorname{phase} b * (\psi : (i : A)\to (\operatorname{fun} (_ : A)\mapsto \mathbb{C})i)(f \langle b, h\rangle)\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullRaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.36 (sum_pair_energies).**

$$\forall (m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2))(t : \operatorname{Finset} \mathbb{N}), \sum i \in t,( \left\lVert (\operatorname{pairContract} (2 * m)(2 * i)(2 * i + 1): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))\psi  \right\rVert)^{2}\leq (m : \mathbb{R})*( \left\lVert \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.sum_pair_energies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.37 (tensorBasisVector).**

$$\forall (E : \operatorname{Type})(F : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F](\iota : \operatorname{Type})(\kappa : \operatorname{Type})(b : \operatorname{HilbertBasis} \iota \mathbb{C} E)(c : \operatorname{HilbertBasis} \kappa \mathbb{C} F)(p : \iota \times \kappa), (\operatorname{tensorBasisVector} (b)(c)(p): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F))= ((\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} (b p. 1)(c p. 2): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorBasisVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.38 (tensorHilbertBasis).**

$$\forall (E : \operatorname{Type})(F : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F](\iota : \operatorname{Type})(\kappa : \operatorname{Type})(b : \operatorname{HilbertBasis} \iota \mathbb{C} E)(c : \operatorname{HilbertBasis} \kappa \mathbb{C} F)(h : \operatorname{Orthonormal} \mathbb{C} (\operatorname{tensorBasisVector} b c))(g : (\operatorname{Submodule}. \operatorname{span} \mathbb{C} (\operatorname{Set}. \operatorname{range} (\operatorname{tensorBasisVector} b c)))\perp = \operatorname{bot}), (\operatorname{tensorHilbertBasis} (b)(c): \operatorname{HilbertBasis} (\iota \times \kappa)\mathbb{C} (\operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F)))= (\operatorname{HilbertBasis}. \operatorname{mkOfOrthogonalEqBot} h g)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorHilbertBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.39 (tensorHilbertBasis_apply).**

$$\forall \{E : \operatorname{Type}\}\{F : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E][\operatorname{NormedAddCommGroup} F][\operatorname{InnerProductSpace} \mathbb{C} F]\{\iota : \operatorname{Type}\}\{\kappa : \operatorname{Type}\}(b : \operatorname{HilbertBasis} \iota \mathbb{C} E)(c : \operatorname{HilbertBasis} \kappa \mathbb{C} F)(p : \iota \times \kappa), (\operatorname{tensorHilbertBasis} b c : \iota \times \kappa \to \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E F))p = \operatorname{tensorBasisVector} b c p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorHilbertBasis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.CanonicalSequence`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.adapted_hilbert_basis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.annihilationCoordinate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.canonicalRayleigh`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonVector`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonVector_pos`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.comparisonWeight`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateClaim`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename_image`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.coordinateRename_outside`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_norm_sq`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_norm_sq_summable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.countable_pair_sign`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.denominator_sum_bound`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.lift`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.occupiedOrderedPairEquiv`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.ordered_pair_energy`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.orthonormal_countable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairContract`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairContract_apply`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairCoordinate`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairIncidence`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairInsert`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_row`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_row_bound`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairKernel_weighted_row`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairPhase`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.pairValid`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPull`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullCLM`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullLinear`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.partialPullRaw`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.sum_pair_energies`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorBasisVector`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorHilbertBasis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.tensorHilbertBasis_apply`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions.weighted_schur`
- Dependency: [D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem](../../Observer/HilbertGeometry/HilbertPathFundamentalTheorem.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound](../../Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound.md)
