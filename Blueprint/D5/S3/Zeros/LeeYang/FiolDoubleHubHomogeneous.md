# Double-hub homogeneous

## Abstract

The physical double-hub family: homogeneous.

The coefficient of the original independent two-coupling source equals 200 times 12^(2m) times the sum of [X^j]R_m times a^(4m+6-j)b^j, for 0<=j<=4m+6. This identity holds for every pair of complex couplings.

For a nonzero first coupling, the source ratio identity and the coefficient identity give the formula directly. Both sides are continuous in the first coupling, and equality on its dense nonzero locus extends to zero. The ratio formula itself retains its nonzero hypothesis.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (actual closed ratio).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_closed_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_closed_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_closed_ratio (m cutoff : ℕ) (hm : 1≤m) (hc : 3≤cutoff)     (a b : ℂ) (ha : a≠0) :     homogeneousCoefficient m cutoff a b = (200*(12:ℂ)^(2*m))*a^(4*m+6)*       ((R m).map Complex.ofRealHom).eval (b/a).

**Theorem 1.2 (actual homogeneous identity).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_homogeneous_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_homogeneous_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves all-complex homogeneous equality from independent finite sums, a degree bound and continuous extension through a=0. Exact source statement: theorem actual_homogeneous_identity (m cutoff : ℕ) (hm : 1≤m) (hc : 3≤cutoff)     (a b : ℂ) : homogeneousCoefficient m cutoff a b=expectedHomogeneousCoefficient m a b.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_closed_ratio`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_homogeneous_identity`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient](FiolDoubleHubCoefficient.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
