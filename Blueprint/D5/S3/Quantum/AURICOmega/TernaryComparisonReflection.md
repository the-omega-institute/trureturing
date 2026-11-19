# Reflection sequences of ternary comparison structures

## Abstract

Two-point reflection sequences are group powers, so equally spaced readings agree.

**Definition 1.1 (The reflection sequence through two points).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall a \in M, b \in M,\; \operatorname{reflectionSeq}\left(C, a, b, 0\right) = a \land \left(\operatorname{reflectionSeq}\left(C, a, b, 1\right) = b \land \left(\forall n \in \mathbb{N},\; \operatorname{reflectionSeq}\left(C, a, b, n + 2\right) = \operatorname{tri}\left(C, \operatorname{reflectionSeq}\left(C, a, b, n + 1\right), \operatorname{reflectionSeq}\left(C, a, b, n\right), \operatorname{reflectionSeq}\left(C, a, b, n + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.reflectionSeq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For points a and b of a ternary comparison structure C, the reflection sequence x starts with x 0 = a and x 1 = b, and each further point x (n + 2) = tri (x (n + 1)) (x n) (x (n + 1)) is the reflection of the point before last through the last point. In a group with the transfer x * y^-1 * z this is the step x (n + 2) = x (n + 1) * (x n)^-1 * x (n + 1).

**Theorem 1.2 (Reflection sequences are powers).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall a \in M, b \in M,\; \forall n \in \mathbb{N},\; \operatorname{reflectionSeq}\left(C, a, b, n\right) = \operatorname{pow}\left(\operatorname{groupAt}\left(C, a\right), b, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.reflectionSeq_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremiah Certaine (1943). *The ternary operation (abc) = ab^{-1}c of a group*. DOI: [10.1090/S0002-9904-1943-08042-1](https://doi.org/10.1090/S0002-9904-1943-08042-1).

*Commentary.*

In the group at a, where a is the identity and tri x y z = x * y^-1 * z, the n-th point of the reflection sequence is b^n. The proof is an induction on pairs of consecutive points: x 0 = a = b^0 and x 1 = b = b^1, and if x n = b^n and x (n + 1) = b^(n + 1), then x (n + 2) = b^(n + 1) * (b^n)^-1 * b^(n + 1) = b^(n + 2). Thus the sequence consists of the powers of b in the group at a.

**Theorem 1.3 (Equally spaced readings agree).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall a \in M, b \in M,\; \forall m \in \mathbb{N}, n \in \mathbb{N},\; \operatorname{kappa}\left(C, \operatorname{reflectionSeq}\left(C, a, b, m\right), \operatorname{reflectionSeq}\left(C, a, b, m + n\right)\right) = \operatorname{kappa}\left(C, a, \operatorname{reflectionSeq}\left(C, a, b, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.kappa_reflectionSeq_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural numbers m and n, the reading between the m-th and the (m + n)-th point of the reflection sequence equals the reading between the starting point a and the n-th point. By the previous theorem the two points are b^m and b^m * b^n in the group at a. Left multiplication by b^m in that group is the transfer y -> tri (b^m) a y, under which the reading is invariant, and tri (b^m) a a = b^m, so the reading of b^m and b^m * b^n equals the reading of a and b^n.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.kappa_reflectionSeq_add`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.reflectionSeq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.reflectionSeq_eq_pow`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonGroup](TernaryComparisonGroup.md)
