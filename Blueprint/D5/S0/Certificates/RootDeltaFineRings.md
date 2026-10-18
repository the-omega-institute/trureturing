# A negative answer to displayed Problem 4.4 of sqrt(Delta)-Fine Rings

## Abstract

Every root-Delta-fine associative unital ring is fine, including the trivial ring.

**Definition 1.1 (The explicit left-unit test).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow (\forall d \in R,\; (DeltaMember\left(d\right)) \Leftrightarrow (\forall v \in Units\left(R\right),\; IsUnit\left(1 - val\left(v\right) \cdot d\right)))$$

*Formalization.* `D5/S0/Certificates/RootDeltaFineRings.DeltaMember` (`✓ std3`).

*Citation.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

In arXiv:2608.30734v2, Introduction S1.p6, Delta consists exactly of d for which 1-v*d is a unit for every two-sided unit v. Units(R) denotes Lean's R-units and val(v) its value in R. The multiplication order is essential.

**Definition 1.2 (A strictly positive power in Delta).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow (\forall a \in R,\; (RootDeltaMember\left(a\right)) \Leftrightarrow (\exists n \in Nat\left(\right),\; (0 < n) \land (DeltaMember\left(a^{n}\right))))$$

*Formalization.* `D5/S0/Certificates/RootDeltaFineRings.RootDeltaMember` (`✓ std3`).

*Citation.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Introduction S1.p7 requires an exponent at least one. The witness n is a natural number and 0<n is an explicit conjunct.

**Definition 1.3 (Root-Delta-fine rings).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((RootDeltaFine\left(R\right)) \Leftrightarrow (\forall x \in R,\; (\neg x = 0) \Rightarrow (\exists v \in Units\left(R\right),\; \exists a \in R,\; (x = val\left(v\right) + a) \land (RootDeltaMember\left(a\right)))))$$

*Formalization.* `D5/S0/Certificates/RootDeltaFineRings.RootDeltaFine` (`✓ std3`).

*Citation.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Definition 2.1 quantifies over every nonzero r. Its decomposition has a two-sided unit and a root-Delta summand. No commutation is imposed; only the source's separately named strong variant imposes that condition.

**Definition 1.4 (Fine rings).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((Fine\left(R\right)) \Leftrightarrow (\forall x \in R,\; (\neg x = 0) \Rightarrow (\exists v \in Units\left(R\right),\; \exists a \in R,\; (x = val\left(v\right) + a) \land (IsNilpotent\left(a\right)))))$$

*Formalization.* `D5/S0/Certificates/RootDeltaFineRings.Fine` (`✓ std3`).

*Citation.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Introduction S1.p4 requires the same decomposition for every nonzero element, with a nilpotent summand. IsNilpotent is Mathlib's standard power-zero predicate.

**Theorem 1.5 (Zero belongs to Delta).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow (DeltaMember\left(0\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.zero_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Every test at zero is the unit one. This also proves the reverse containment needed to read delta_eq_zero as Delta={0}.

**Theorem 1.6 (A Delta member cannot be a unit in a nontrivial ring).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((Nontrivial\left(R\right)) \Rightarrow (\forall d \in R,\; (DeltaMember\left(d\right)) \Rightarrow (\neg IsUnit\left(d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.delta_not_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

For a unit d, its inverse makes 1-d inverse*d equal to zero. Nontriviality is needed only by this auxiliary statement, not by the main theorems.

**Theorem 1.7 (Root-Delta-fineness forces Delta to be zero).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((RootDeltaFine\left(R\right)) \Rightarrow (\forall d \in R,\; (DeltaMember\left(d\right)) \Rightarrow (d = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.delta_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Apply the decomposition to a hypothetical nonzero Delta member d=u+a. The test b=1-u inverse*d is a unit. The proof checks (-u)*b=a using associativity, distributivity and u*u inverse=1 in this order. Thus a and the power witnessing its root-Delta membership are units, a contradiction. Nontriviality is constructed locally from d not equal to zero; the theorem itself assumes only Ring(R) and RootDeltaFine(R).

**Theorem 1.8 (Every root-Delta-fine ring is fine).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((RootDeltaFine\left(R\right)) \Rightarrow (Fine\left(R\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.rootDeltaFine_implies_fine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

The positive power of each summand belongs to Delta and is therefore zero. The same unit and summand give a fine decomposition. This answers the entire displayed Problem 4.4 negatively for arbitrary associative unital rings, with no commutativity, finiteness or nontriviality hypothesis.

**Theorem 1.9 (Every fine ring is root-Delta-fine).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((Fine\left(R\right)) \Rightarrow (RootDeltaFine\left(R\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.fine_implies_rootDeltaFine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

A nilpotency exponent n gives the strictly positive exponent n+1. Its power is zero, which belongs to Delta. This handles Mathlib's exponent-zero convention without excluding the trivial ring.

**Theorem 1.10 (The two ring classes coincide).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow ((RootDeltaFine\left(R\right)) \Leftrightarrow (Fine\left(R\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.rootDeltaFine_iff_fine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

The checked forward and converse implications give an equivalence in every carrier universe. In these displays Type denotes Type u for arbitrary u, and Ring(R) renders Lean's typeclass binder [Ring R].

**Theorem 1.11 (Displayed Problem 4.4: No).**

$$\forall R \in Type\left(\right),\; (Ring\left(R\right)) \Rightarrow (\neg \left((RootDeltaFine\left(R\right)) \land (\neg Fine\left(R\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RootDeltaFineRings.no_rootDeltaFine_not_fine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan (2026). *sqrt(Delta)-Fine Rings*. DOI: [10.48550/arXiv.2608.30734](https://doi.org/10.48550/arXiv.2608.30734). URL: <https://arxiv.org/html/2608.30734v2>.

*Commentary.*

Danchev, Hasanzadeh, Moussavi and Javan ask: Is there a sqrt(Delta)-fine ring which is not fine? The answer is No. The pre-question paragraph conjectures existence, while the concluding discussion conjectures the implication; the introductory radical-description prose is also inconsistent. This result follows the explicit unit-test definitions and the displayed question, without relying on those other assertions. Global prior publication and priority remain ASSUMED-UNVERIFIED; no first-discovery claim is made.

## References

- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.DeltaMember`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.Fine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.RootDeltaFine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.RootDeltaMember`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.delta_eq_zero`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.delta_not_unit`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.fine_implies_rootDeltaFine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.no_rootDeltaFine_not_fine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.rootDeltaFine_iff_fine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.rootDeltaFine_implies_fine`
- Truth anchor: `D5/S0/Certificates/RootDeltaFineRings.zero_delta`
