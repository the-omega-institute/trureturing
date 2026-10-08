# McNulty Path Robustness

## Abstract

The operator certificate gives the upper bound for P₂ₙ.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Definition 1.1 (claim).**

$$\begin{aligned}\operatorname{claim} \iff (\forall n : \mathbb{N} , 1 \leq n \to (\forall d : \mathbb{N} , \forall A : \operatorname{Fin} (2 \cdot n) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) , \operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{pathGraph} (2 \cdot n)) A \to \operatorname{IsGreatest} \{eta : \mathbb{R} | eta \in \operatorname{Set} . \operatorname{Icc} 0 1 \land \operatorname{JM} A eta\} (\operatorname{visibility} n)) \land (\forall d : \mathbb{N} , \forall A : \operatorname{Fin} (2 \cdot n + 1) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) , \operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{pathGraph} (2 \cdot n + 1)) A \to \operatorname{IsGreatest} \{eta : \mathbb{R} | eta \in \operatorname{Set} . \operatorname{Icc} 0 1 \land \operatorname{JM} A eta\} (\operatorname{visibility} n)) \land (\forall d : \mathbb{N} , \forall A : \operatorname{Fin} (2 \cdot n + 2) \to (\operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} d) \mathbb{C}) , \operatorname{Realization} (\operatorname{SimpleGraph} . \operatorname{cycleGraph} (2 \cdot n + 2)) A \to \operatorname{IsGreatest} \{eta : \mathbb{R} | eta \in \operatorname{Set} . \operatorname{Icc} 0 1 \land \operatorname{JM} A eta\} (\operatorname{visibility} n)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.claim` (`✓ std3`).

*Citation.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

McNulty, Conjecture 1, p. 9, verbatim: "For all n ≥ 1, paths satisfy" η(P₂ₙ) = η(P₂ₙ₊₁) = η(C₂ₙ₊₂) = (2/(2n+2)) csc(π/(2n+2)). The claim quantifies over every d and every realization on ℂ^d; Realization includes 1 ≤ d. The graph conventions are Mathlib pathGraph and cycleGraph. IsGreatest states both attainability and the upper bound in the feasible visibility subset of [0,1].

**Theorem 1.2 (result).**

$$\begin{aligned}\operatorname{claim}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.result` (`✓ std3`). ∎

*Resolves.* `Problems/mcnulty-2025-path-robustness` (proved) by `D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mcnulty-2025-path-robustness","declaration_gid":"D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniel McNulty (2025). *A Graph-Theoretic Approach to Quantum Measurement Incompatibility*. URL: <https://arxiv.org/abs/2511.15954>.

*Commentary.*

The operator certificate gives the upper bound for P₂ₙ. Restricting a parent to its initial induced path gives the same upper bound for P₂ₙ₊₁ and C₂ₙ₊₂. For the lower bound, each family is represented or extended by 2n+2 Majoranas and compressed from the Fourier-vacuum parent. The even-cycle construction uses the central involution and relabels the final outcome in each central sector.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/McNultyPathRobustness.result`
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations](CentralCycleRealizations.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents](CliffordBondParents.md)
