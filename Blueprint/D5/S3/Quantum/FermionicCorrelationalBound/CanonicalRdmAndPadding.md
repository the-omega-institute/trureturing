# CanonicalRdmAndPadding

## Abstract

Completed fermionic operators and their correlational estimate.

All types range over arbitrary universes. Underscores in declaration names appear as typographical subscripts and retain the full Lean spelling. Juxtaposition and the displayed binders use Lean function-application syntax; sums and products use Lean's typed binder syntax. Bracketed typeclass requirements are anonymous instances. Real and complex casts retain their target-type annotation. Submodules and lp spaces in type position carry the ordinary CoeSort coercion. Nat subtraction is truncated, Nat division is Euclidean division, and field division is written with a slash. Named constants retain their actual Lean spelling. The three-dot marker suppresses only proof fields and proof arguments, which are proof-irrelevant; it never suppresses mathematical data. The additional h and g binders in construction equations stand for proofs of the displayed propositions; proof irrelevance makes the equation independent of their choice. Completed tensors are UniformSpace.Completion of the Mathlib Hilbert tensor product.

**Theorem 1.1 (up_down_ne).**

$$\forall (L s : \mathbb{N})(i j : \operatorname{Fin} L), \operatorname{upMode} (s := s)i \neq \operatorname{downMode} (s := s)j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.up_down_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.2 (upMode_injective).**

$$\forall (L s : \mathbb{N}), \operatorname{Function}. \operatorname{Injective} (\operatorname{upMode} (L := L)(s := s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.upMode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.3 (upMode).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L), (\operatorname{upMode} (i): \operatorname{Fin} (2 * L + s))= (\langle 2 * (i : \mathbb{N}),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.upMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.4 (transition_remove).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{pairTransition} i x y \iff \operatorname{pairFull} i y \land x = \operatorname{removePair} i y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.transition_remove` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.5 (transition_add).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{pairTransition} i x y \iff \operatorname{pairEmpty} i x \land y = \operatorname{addPair} i x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.transition_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.6 (standardB).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(\operatorname{coeff} : \operatorname{Fin} L \to \mathbb{R}), (\operatorname{standardB} (\operatorname{coeff}): \operatorname{Matrix} (\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{Fin} (2 * L + s)\to \operatorname{Bool})\mathbb{C})= (\sum i : \operatorname{Fin} L, ((\operatorname{coeff} i): \mathbb{C})\cdot (\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{downMode} i)* \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{upMode} i)))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.standardB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.7 (removePair).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{aAnon} : \operatorname{Fin} (2 * L + s)), (\operatorname{removePair} (i)(y)(\operatorname{aAnon}): \operatorname{Bool})= (\operatorname{Function}. \operatorname{update} (\operatorname{Function}. \operatorname{update} y (\operatorname{upMode} i)\operatorname{false})(\operatorname{downMode} i)\operatorname{false} \operatorname{aAnon})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.removePair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.8 (paired_entries).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{downMode} i)* \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{upMode} i))x y = \prod k : \operatorname{Fin} (2 * L + s), \operatorname{pairWord} i k (x k)(y k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paired_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.9 (pair_entry_transition).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{downMode} i)* \operatorname{D5}. \operatorname{S3}. \operatorname{Quantum}. \operatorname{SpinChains}. \operatorname{SupersymmetricFermion}. \operatorname{JordanWigner}. \operatorname{fullC} (\operatorname{upMode} i))x y = \operatorname{if} \operatorname{pairTransition} i x y \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pair_entry_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.10 (pairWord).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(k : \operatorname{Fin} (2 * L + s)), (\operatorname{pairWord} (i)(k): \operatorname{Matrix} \operatorname{Bool} \operatorname{Bool} \mathbb{C})= (\operatorname{if} k = \operatorname{upMode} i \lor k = \operatorname{downMode} i \operatorname{then} \operatorname{Matrix}. \operatorname{single} \operatorname{false} \operatorname{true} 1 \operatorname{else} 1)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.11 (pairTransition).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(y : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{pairTransition} (i)(x)(y): \operatorname{Prop})= (x (\operatorname{upMode} i)= \operatorname{false} \land y (\operatorname{upMode} i)= \operatorname{true} \land x (\operatorname{downMode} i)= \operatorname{false} \land y (\operatorname{downMode} i)= \operatorname{true} \land \forall (k : \operatorname{Fin} (2 * L + s)), k \neq \operatorname{upMode} i \to k \neq \operatorname{downMode} i \to x k = y k)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairTransition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.12 (pairFull).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{pairFull} (i)(x): \operatorname{Prop})= (x (\operatorname{upMode} i)= \operatorname{true} \land x (\operatorname{downMode} i)= \operatorname{true})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairFull` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.13 (pairEmpty).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{pairEmpty} (i)(x): \operatorname{Prop})= (x (\operatorname{upMode} i)= \operatorname{false} \land x (\operatorname{downMode} i)= \operatorname{false})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.14 (downMode_injective).**

$$\forall (L s : \mathbb{N}), \operatorname{Function}. \operatorname{Injective} (\operatorname{downMode} (L := L)(s := s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.downMode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.15 (downMode).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L), (\operatorname{downMode} (i): \operatorname{Fin} (2 * L + s))= (\langle 2 * (i : \mathbb{N})+ 1,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.downMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.16 (doublePairs_remove).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{doublePairs} (\operatorname{removePair} i x)= (\operatorname{doublePairs} x). \operatorname{erase} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs_remove` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.17 (doublePairs_add).**

$$\forall \{L s : \mathbb{N}\}(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), \operatorname{doublePairs} (\operatorname{addPair} i x)= \operatorname{insert} i (\operatorname{doublePairs} x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.18 (doublePairs).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool}), (\operatorname{doublePairs} (x): \operatorname{Finset} (\operatorname{Fin} L))= (\{i : \operatorname{Fin} L | x (\operatorname{upMode} i)= \operatorname{true} \land x (\operatorname{downMode} i)= \operatorname{true}\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.19 (addPair).**

$$\forall (L : \mathbb{N})(s : \mathbb{N})(i : \operatorname{Fin} L)(x : \operatorname{Fin} (2 * L + s)\to \operatorname{Bool})(\operatorname{aAnon} : \operatorname{Fin} (2 * L + s)), (\operatorname{addPair} (i)(x)(\operatorname{aAnon}): \operatorname{Bool})= (\operatorname{Function}. \operatorname{update} (\operatorname{Function}. \operatorname{update} x (\operatorname{upMode} i)\operatorname{true})(\operatorname{downMode} i)\operatorname{true} \operatorname{aAnon})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.addPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.20 (adaptedLabel).**

$$\forall (E : \operatorname{Type})(\iota : \operatorname{Type})(v : \iota \times \operatorname{Fin} 2 \to E)(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(w : \operatorname{Set} E)(g : \operatorname{Function}. \operatorname{Embedding} (w : \operatorname{Type})\mathbb{N})(y : (w : \operatorname{Type})), (\operatorname{adaptedLabel} (v)(e)(w)(g)(y): \mathbb{N})= (\operatorname{if} h : (y : E)\in \operatorname{Set}. \operatorname{range} v \operatorname{then} \operatorname{canonicalModeLabel} e (\operatorname{Classical}. \operatorname{choose} h)\operatorname{else} 4 * (g : (w : \operatorname{Type})\to \mathbb{N})y + 2)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.21 (adaptedLabel_injective).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E]\{\iota : \operatorname{Type}\}\{v : \iota \times \operatorname{Fin} 2 \to E\}(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(w : \operatorname{Set} E)(g : \operatorname{Function}. \operatorname{Embedding} (w : \operatorname{Type})\mathbb{N}), \operatorname{Function}. \operatorname{Injective} (\operatorname{adaptedLabel} v e w g)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.22 (adaptedLabel_on_pair).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E]\{\iota : \operatorname{Type}\}\{v : \iota \times \operatorname{Fin} 2 \to E\}, \operatorname{Function}. \operatorname{Injective} v \to \forall (e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(w : \operatorname{Set} E)(g : \operatorname{Function}. \operatorname{Embedding} (w : \operatorname{Type})\mathbb{N})(\operatorname{hw} : \operatorname{Set}. \operatorname{range} v \subseteq w)(p : \iota \times \operatorname{Fin} 2), \operatorname{adaptedLabel} v e w g \langle v p, \operatorname{hw} (\operatorname{Exists}. \operatorname{intro} p \operatorname{rfl})\rangle= \operatorname{canonicalModeLabel} e p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel_on_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.23 (canonicalCoefficients).**

$$\forall (c : \operatorname{CanonicalSequence}), (\operatorname{canonicalCoefficients} (c): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N})\mapsto \mathbb{C})2))= (\langle \operatorname{fun} (i : \mathbb{N})\mapsto ((c. \operatorname{coeff} i): \mathbb{C}),...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.24 (canonicalModeLabel).**

$$\forall (\iota : \operatorname{Type})(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N})(p : \iota \times \operatorname{Fin} 2), (\operatorname{canonicalModeLabel} (e)(p): \mathbb{N})= (4 * (e : \iota \to \mathbb{N})p. 1 + (p. 2 : \mathbb{N}))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalModeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.25 (canonicalTensor).**

$$\forall (c : \operatorname{CanonicalSequence})(h : \operatorname{Orthonormal} \mathbb{C} \operatorname{orderedPairWedge}), (\operatorname{canonicalTensor} (c): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))= (h. \operatorname{orthogonalFamily}. \operatorname{linearIsometry} (\operatorname{canonicalCoefficients} c))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalTensor` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.26 (completedRayleigh).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(\varphi : (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)), (\operatorname{completedRayleigh} (N)(\psi)(\varphi): \mathbb{R})= ((\operatorname{inner} \mathbb{C} \varphi ((\operatorname{countableGammaCLM} N \psi : (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))\varphi)). \operatorname{re})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completedRayleigh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.27 (completedRayleigh_contraction).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(\varphi : (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)), \operatorname{completedRayleigh} N \psi \varphi =( \left\lVert \operatorname{tensorSynthesis} N \psi (\operatorname{star} \varphi) \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completedRayleigh_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.28 (completed_identity_2_4).**

$$\forall (c : \operatorname{CanonicalSequence})(m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \operatorname{completedRayleigh} (2 * m)\psi (\operatorname{canonicalTensor} c)= 2 *( \left\lVert \operatorname{countableB} c. \operatorname{coeff} m \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completed_identity_2_4` (`✓ std3`). ∎

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.29 (contractionFamily).**

$$\forall (m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), (\operatorname{contractionFamily} (m)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N})\mapsto \mathbb{R})2))= (\langle \operatorname{fun} (i : \mathbb{N})\mapsto \left\lVert (\operatorname{pairContract} (2 * m)(2 * i)(2 * i + 1): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))\psi  \right\rVert,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.contractionFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.30 (countableB).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})(m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), (\operatorname{countableB} (\operatorname{coeff})(m)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))= (\sum ' (i : \mathbb{N}), ((\operatorname{coeff} i): \mathbb{C})\cdot (\operatorname{pairContract} (2 * m)(2 * i)(2 * i + 1): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))\psi)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.31 (countableBL).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})(m : \mathbb{N})(L : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), (\operatorname{countableBL} (\operatorname{coeff})(m)(L)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))= (\sum i \in \operatorname{Finset}. \operatorname{range} L, ((\operatorname{coeff} i): \mathbb{C})\cdot (\operatorname{pairContract} (2 * m)(2 * i)(2 * i + 1): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))\psi)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableBL` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.32 (countableBL_tendsto).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R}), (\operatorname{Summable} \operatorname{fun} (i : \mathbb{N})\mapsto( \operatorname{coeff} i)^{2})\to \forall (m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \operatorname{Filter}. \operatorname{Tendsto} (\operatorname{fun} (L : \mathbb{N})\mapsto \operatorname{countableBL} \operatorname{coeff} m L \psi)\operatorname{Filter}. \operatorname{atTop} (\operatorname{nhds} (\operatorname{countableB} \operatorname{coeff} m \psi))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableBL_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.33 (countableGammaCLM).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{countableGammaCLM} (N)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))= ((\operatorname{ContinuousLinearMap}. \operatorname{adjoint} : ((\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))(\operatorname{tensorConjugateCLM} N \psi)\circ_{\operatorname{SL}} \operatorname{tensorConjugateCLM} N \psi)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableGammaCLM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.34 (countable_identity_2_4).**

$$\forall (c : \operatorname{CanonicalSequence})(m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \operatorname{canonicalRayleigh} c \psi = 2 *( \left\lVert \operatorname{countableB} c. \operatorname{coeff} m \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countable_identity_2_4` (`✓ std3`). ∎

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.35 (countable_ordered_pair_trace).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), \sum ' (\operatorname{ij} : \mathbb{N} \times \mathbb{N}),( \left\lVert (\operatorname{pairContract} N \operatorname{ij}. 1 \operatorname{ij}. 2 : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\psi  \right\rVert)^{2}= ((N * (N - 1)): \mathbb{R})*( \left\lVert \psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countable_ordered_pair_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.36 (finite_mass_le_one).**

$$\forall (c : \operatorname{CanonicalSequence})(L : \mathbb{N}), \sum i \in \operatorname{Finset}. \operatorname{range} L,( c. \operatorname{coeff} i)^{2}\leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.finite_mass_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.37 (inner_star_star_countable).**

$$\forall \{A : \operatorname{Type}\}(x y : (\operatorname{lp} (\operatorname{fun} (_ : A)\mapsto \mathbb{C})2)), \operatorname{inner} \mathbb{C} (\operatorname{star} x)(\operatorname{star} y)= \operatorname{inner} \mathbb{C} y x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.inner_star_star_countable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.38 (norm_limit_chr3).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E](c : \operatorname{CanonicalSequence})(m : \mathbb{N})(\alpha : \mathbb{R}), (\forall (i : \mathbb{N}),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to \forall (v : \mathbb{N} \to E)(\operatorname{vLimit} : E), \operatorname{Filter}. \operatorname{Tendsto} v \operatorname{Filter}. \operatorname{atTop} (\operatorname{nhds} \operatorname{vLimit})\to (\forall (L : \mathbb{N}),( \left\lVert v L  \right\rVert)^{2}\leq (m : \mathbb{R})- (m : \mathbb{R})* ((m : \mathbb{R})- 1)* (\sum i \in \operatorname{Finset}. \operatorname{range} L,( c. \operatorname{coeff} i)^{4})+ 5 / 2 *( (m : \mathbb{R}))^{3}*( \alpha)^{2})\to 2 *( \left\lVert \operatorname{vLimit}  \right\rVert)^{2}\leq 2 * (m : \mathbb{R})* (1 - ((m : \mathbb{R})- 1)* (\sum ' (i : \mathbb{N}),( c. \operatorname{coeff} i)^{4})+ 5 / 8 *( (2 * (m : \mathbb{R})* \alpha))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.norm_limit_chr3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.39 (orderedContractionFamily).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{orderedContractionFamily} (N)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{R})2))= (\langle \operatorname{fun} (\operatorname{ij} : \mathbb{N} \times \mathbb{N})\mapsto \left\lVert (\operatorname{pairContract} N \operatorname{ij}. 1 \operatorname{ij}. 2 : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\psi  \right\rVert,...\rangle)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedContractionFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.40 (orderedPairWedge).**

$$\forall (i : \mathbb{N}), (\operatorname{orderedPairWedge} (i): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))= (((\operatorname{Real}. \operatorname{sqrt} 2 : \mathbb{C}))^{- 1}\cdot (\operatorname{lp}. \operatorname{single} 2 (2 * i, 2 * i + 1)1 - \operatorname{lp}. \operatorname{single} 2 (2 * i + 1, 2 * i)1))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedPairWedge` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.41 (orderedPairWedge_orthonormal).**

$$\operatorname{Orthonormal} \mathbb{C} \operatorname{orderedPairWedge}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedPairWedge_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.42 (ordered_pair_energies_summable).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), \operatorname{Summable} \operatorname{fun} (\operatorname{ij} : \mathbb{N} \times \mathbb{N})\mapsto( \left\lVert (\operatorname{pairContract} N \operatorname{ij}. 1 \operatorname{ij}. 2 : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\psi  \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.ordered_pair_energies_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.43 (padCanonicalSequence).**

$$\forall (c : \operatorname{CanonicalSequence}), (\operatorname{padCanonicalSequence} (c): \operatorname{CanonicalSequence})= (\{\operatorname{coeff} := \operatorname{paddedCoeff} c. \operatorname{coeff}, \operatorname{nonneg} :=..., \operatorname{summable}_{\operatorname{sq}} :=..., \operatorname{mass} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.44 (padCanonicalSequence_cap).**

$$\forall (c : \operatorname{CanonicalSequence})(\alpha : \mathbb{R}), (\forall (i : \mathbb{N}),( c. \operatorname{coeff} i)^{2}\leq \alpha)\to \forall (i : \mathbb{N}),( (\operatorname{padCanonicalSequence} c). \operatorname{coeff} i)^{2}\leq \alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.45 (padCanonicalSequence_fourth).**

$$\forall (c : \operatorname{CanonicalSequence}), \sum ' (i : \mathbb{N}),( (\operatorname{padCanonicalSequence} c). \operatorname{coeff} i)^{4}= (\sum ' (i : \mathbb{N}),( c. \operatorname{coeff} i)^{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.46 (paddedCoeff).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})(i : \mathbb{N}), (\operatorname{paddedCoeff} (\operatorname{coeff})(i): \mathbb{R})= (\operatorname{if} \operatorname{Nat}. \operatorname{mod} i 2 = 0 \operatorname{then} \operatorname{coeff} ((\operatorname{Nat}. \operatorname{div} i 2))\operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paddedCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.47 (paddedCoeff_even).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R})(i : \mathbb{N}), \operatorname{paddedCoeff} \operatorname{coeff} (2 * i)= \operatorname{coeff} i$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paddedCoeff_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Theorem 1.48 (pairSeries_summable).**

$$\forall (\operatorname{coeff} : \mathbb{N} \to \mathbb{R}), (\operatorname{Summable} \operatorname{fun} (i : \mathbb{N})\mapsto( \operatorname{coeff} i)^{2})\to \forall (m : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)), \operatorname{Summable} \operatorname{fun} (i : \mathbb{N})\mapsto ((\operatorname{coeff} i): \mathbb{C})\cdot (\operatorname{pairContract} (2 * m)(2 * i)(2 * i + 1): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = 2 * m - 2\})\mapsto \mathbb{C})2))\psi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairSeries_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.49 (sourcePairWedge).**

$$\forall (E : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E](\iota : \operatorname{Type})(v : \iota \times \operatorname{Fin} 2 \to E)(i : \iota), (\operatorname{sourcePairWedge} (v)(i): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E))= (((\operatorname{Real}. \operatorname{sqrt} 2 : \mathbb{C}))^{- 1}\cdot (((\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} (v (i, 0))(v (i, 1))): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E))- ((\operatorname{TensorProduct}. \operatorname{tmul} \mathbb{C} (v (i, 1))(v (i, 0))): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E))))$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.sourcePairWedge` (`✓ std3`).

*Citation.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

Section 1, p. 2, defines “u∧v := 1/√2 (u⊗v−v⊗u)”. The displayed expression is exactly that normalized wedge in the actual completed Hilbert tensor product.

**Definition 1.50 (tensorConjugateCLM).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{tensorConjugateCLM} (N)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))= (\operatorname{star} (\operatorname{WithConv}. \operatorname{toConv} (\operatorname{tensorSynthesisCLM} N \psi))). \operatorname{ofConv}$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorConjugateCLM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.51 (tensorCoordinateEmbedding).**

$$\forall (E : \operatorname{Type})[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E](\iota : \operatorname{Type})(b : \operatorname{HilbertBasis} \iota \mathbb{C} E)(e : \operatorname{Function}. \operatorname{Embedding} \iota \mathbb{N}), (\operatorname{tensorCoordinateEmbedding} (b)(e): \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E)\to_{li} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))= ((\operatorname{coordinateRename} (e. \operatorname{prodMap} e)). \operatorname{comp} (\operatorname{tensorHilbertBasis} b b). \operatorname{repr}. \operatorname{toLinearIsometry})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorCoordinateEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Theorem 1.52 (tensorCoordinateEmbedding_sourcePairWedge).**

$$\forall \{E : \operatorname{Type}\}[\operatorname{NormedAddCommGroup} E][\operatorname{InnerProductSpace} \mathbb{C} E]\{\iota : \operatorname{Type}\}\{w : \operatorname{Type}\}(v : \iota \times \operatorname{Fin} 2 \to E)(b : \operatorname{HilbertBasis} w \mathbb{C} E)(e : \operatorname{Function}. \operatorname{Embedding} w \mathbb{N})(r : \iota \times \operatorname{Fin} 2 \to w), (\forall (p : \iota \times \operatorname{Fin} 2), (b : w \to E)(r p)= v p)\to \forall (a : \iota \to \mathbb{N}), (\forall (i : \iota), (e : w \to \mathbb{N})(r (i, 0))= 2 * a i)\to (\forall (i : \iota), (e : w \to \mathbb{N})(r (i, 1))= 2 * a i + 1)\to \forall (i : \iota), (\operatorname{tensorCoordinateEmbedding} b e : \operatorname{UniformSpace}. \operatorname{Completion} (\operatorname{TensorProduct} \mathbb{C} E E)\to (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2))(\operatorname{sourcePairWedge} v i)= \operatorname{orderedPairWedge} (a i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorCoordinateEmbedding_sourcePairWedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed statement is proved on the completed Hilbert or occupation carrier shown, with the written hypotheses.

**Definition 1.53 (tensorSynthesis).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2))(\varphi : (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)), (\operatorname{tensorSynthesis} (N)(\psi)(\varphi): (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))= (\sum ' (\operatorname{ij} : \mathbb{N} \times \mathbb{N}), (\varphi : (i : \mathbb{N} \times \mathbb{N})\to (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})i)\operatorname{ij} \cdot (\operatorname{pairContract} N \operatorname{ij}. 1 \operatorname{ij}. 2 : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)\to (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))\psi)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.54 (tensorSynthesisCLM).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{tensorSynthesisCLM} (N)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to_{L} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))= ((\operatorname{tensorSynthesisLinear} N \psi). \operatorname{mkContinuous} \left\lVert \operatorname{orderedContractionFamily} N \psi  \right\rVert...)$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesisCLM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

**Definition 1.55 (tensorSynthesisLinear).**

$$\forall (N : \mathbb{N})(\psi : (\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N\})\mapsto \mathbb{C})2)), (\operatorname{tensorSynthesisLinear} (N)(\psi): (\operatorname{lp} (\operatorname{fun} (_ : \mathbb{N} \times \mathbb{N})\mapsto \mathbb{C})2)\to_{l} [\mathbb{C}](\operatorname{lp} (\operatorname{fun} (_ : \{s : \operatorname{Finset} \mathbb{N} / / s. \operatorname{card} = N - 2\})\mapsto \mathbb{C})2))= (\{\operatorname{toFun} := \operatorname{tensorSynthesis} N \psi, \operatorname{map}_{\operatorname{add'}} :=..., \operatorname{map}_{\operatorname{smul'}} :=...\})$$

*Formalization.* `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesisLinear` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Martin Ravn Christiansen (2025). *A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators*. URL: <https://arxiv.org/abs/2505.21167v1>.

*Commentary.*

The displayed defining equation retains the data fields; proof fields are omitted by proof irrelevance.

## References

- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel_injective`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.adaptedLabel_on_pair`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.addPair`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalCoefficients`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalModeLabel`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.canonicalTensor`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completedRayleigh`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completedRayleigh_contraction`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.completed_identity_2_4`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.contractionFamily`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableB`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableBL`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableBL_tendsto`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countableGammaCLM`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countable_identity_2_4`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.countable_ordered_pair_trace`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs_add`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.doublePairs_remove`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.downMode`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.downMode_injective`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.finite_mass_le_one`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.inner_star_star_countable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.norm_limit_chr3`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedContractionFamily`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedPairWedge`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.orderedPairWedge_orthonormal`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.ordered_pair_energies_summable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence_cap`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.padCanonicalSequence_fourth`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paddedCoeff`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paddedCoeff_even`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairEmpty`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairFull`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairSeries_summable`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairTransition`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pairWord`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.pair_entry_transition`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.paired_entries`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.removePair`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.sourcePairWedge`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.standardB`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorConjugateCLM`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorCoordinateEmbedding`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorCoordinateEmbedding_sourcePairWedge`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesis`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesisCLM`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.tensorSynthesisLinear`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.transition_add`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.transition_remove`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.upMode`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.upMode_injective`
- Truth anchor: `D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding.up_down_ne`
- Dependency: [D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions](OccupationHilbertContractions.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner](../SpinChains/SupersymmetricFermion/JordanWigner.md)
