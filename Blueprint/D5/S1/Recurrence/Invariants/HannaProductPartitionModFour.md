# Hanna's product-partition congruence

## Abstract

Hanna's OEIS A356508 product equation and its coefficient residues modulo four.

The source is P. D. Hanna's OEIS A356508 entry. It states verbatim: G.f. A(x) satisfies: 2 = Product_{n>=1} (1 + x^n*A(x)) * (1 + x^(n-1)/A(x)). Its comment conjectures verbatim: a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd number of partitions (A052002), otherwise a(n) == 0 (mod 4) when n > 0.

PowerSeries is the formal power-series type, X is its indeterminate, coeff and constantCoeff read coefficients, and invOfUnit is the formal inverse determined by the nonzero constant coefficient. Products are coefficientwise finite windows; Nat.Partition and Fintype.card give the ordinary partition number.

**Definition 1.1 (The coefficientwise product equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(A\right) \ne 0) \land (\forall m \in Nat,\; \operatorname{PowerSeries}.\operatorname{coeff}\left(m, \operatorname{Finset}.\operatorname{prod}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, m + 1\right), (n: Nat \mapsto \left(1 + (\operatorname{PowerSeries}.\operatorname{X}\left(\right))^{n} \cdot A\right) \cdot \left(1 + (\operatorname{PowerSeries}.\operatorname{X}\left(\right))^{n - 1} \cdot \operatorname{PowerSeries}.\operatorname{invOfUnit}\left(A, 1\right)\right))\right)\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(m, 2\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A356508, product-partition generating-function congruence*. URL: <https://oeis.org/A356508>.

*Commentary.*

The displayed predicate is the source generating-function equation over rational formal power series, with each coefficient represented by the finite window through index m+1.

**Definition 1.2 (Hanna's coefficient-residue conjecture).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow ((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Rightarrow (\forall n \in Nat,\; (0 < n) \Rightarrow (\exists z \in Int,\; (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = \operatorname{Int}.\operatorname{cast}\left(z\right)) \land (((\exists k \in Nat,\; (0 < k) \land ((n = 2 \cdot k) \land (\operatorname{Odd}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{Partition}\left(k\right)\right)\right)))) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 2\right))) \land ((\neg (\exists k \in Nat,\; (0 < k) \land ((n = 2 \cdot k) \land (\operatorname{Odd}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{Partition}\left(k\right)\right)\right))))) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 0\right))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2022). *OEIS A356508, product-partition generating-function congruence*. URL: <https://oeis.org/A356508>.

*Commentary.*

The displayed proposition includes existence of a rational solution and the source's integer-coefficient and modulo-four assertions for every positive coefficient.

**Theorem 1.3 (The A356508 conjecture).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Rightarrow (\forall n \in Nat,\; (0 < n) \Rightarrow (\exists z \in Int,\; (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = \operatorname{Int}.\operatorname{cast}\left(z\right)) \land (((\exists k \in Nat,\; (0 < k) \land ((n = 2 \cdot k) \land (\operatorname{Odd}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{Partition}\left(k\right)\right)\right)))) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 2\right))) \land ((\neg (\exists k \in Nat,\; (0 < k) \land ((n = 2 \cdot k) \land (\operatorname{Odd}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{Partition}\left(k\right)\right)\right))))) \Rightarrow (\operatorname{Int}.\operatorname{ModEq}\left(4, z, 0\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a356508-hanna-product-partition-mod-four` (proved) by `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a356508-hanna-product-partition-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2022). *OEIS A356508, product-partition generating-function congruence*. URL: <https://oeis.org/A356508>.

*Commentary.*

Integral coefficient contraction gives the unique solution. Mapping the fixed-point equation to ZMod 4, the candidate 2 times the partition series in X squared minus one squares to one; the paired product therefore reduces to the reciprocal partition identity. Its coefficient formula is 2 times the ordinary partition number at n/2 for even n and zero for odd n, which gives the two residue cases.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.result`
- Dependency: [D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity](../Bilateral/HannaPentagonalPartitionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour](../Parity/BilateralQuarticPowerThetaModFour.md)
