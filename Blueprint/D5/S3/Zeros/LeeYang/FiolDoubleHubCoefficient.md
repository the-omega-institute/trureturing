# Double-hub coefficient

## Abstract

The physical double-hub family: coefficient.

For each placement, the finite sum over endpoint choices reduces to products of U,V,W,H and 1+X. The two central edges, the two central-pendant classes, and the two pendant-pendant classes contribute their actual physical weights.

Their weighted aggregate is Q_d=H_2(A V^2+B U W+C(1+X)UV+D(1+X)^2 U^2)+H_3(EUV+G(1+X)U^2)+9H_4U^2, with A=2d^4, B=3d^2(d^2-1)/2, C=4d(d-1)(2d-1), D=2(d-1)(2d-3), E=8d(2d-1), and G=16(d-1). Thus the actual coefficient is 200 times 12^(2m) times R_m for every m>=1 and cutoff>=3.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (actual coefficient identity).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient.actual_coefficient_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient.actual_coefficient_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects the independently defined source coefficient and closed R polynomial using all placements and actual normalization. Exact source statement: theorem actual_coefficient_identity (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :     sourceCoefficient m cutoff = Polynomial.C (200*(12:ℝ)^(2*m))*R m.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient.actual_coefficient_identity`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence](FiolDoubleHubIncidence.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
