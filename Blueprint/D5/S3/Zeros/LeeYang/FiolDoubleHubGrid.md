# Double-hub grid

## Abstract

The physical double-hub family: grid.

The value of Q at 1 is strictly positive, so the factor (1-X)^h contributes exactly h copies of the root 1. The recurrence between U,V and W and the parity of h are valid for both polynomial families.

The grid sign estimate applies uniformly for d>=5. On the negative half of the cosine grid, the sine lower bound supplies a distance from zero; explicit inequalities then give the sign of the quadratic f_d. The central derivative at d=4r+2 is -8d^4-16d^2(2d-1), which is strictly negative.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (R neg one pos).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.R_neg_one_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.R_neg_one_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem R_neg_one_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (R m).eval (-1).

**Theorem 1.2 (Q one pos).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.Q_one_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.Q_one_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem Q_one_pos (d : ℕ) (hd : 2 ≤ d) : 0 < (Q d).eval 1.

**Theorem 1.3 (candidate one multiplicity).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.candidate_one_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.candidate_one_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem candidate_one_multiplicity (m : ℕ) (hm : 1 ≤ m) :     Polynomial.rootMultiplicity (1:ℂ) ((R m).map Complex.ofRealHom) = h (m+1).

**Theorem 1.4 (actual grid sign).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.actual_grid_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.actual_grid_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the all-large-d grid signs from the new analytic estimates. Exact source statement: theorem actual_grid_sign (d k : ℕ) (hd : 5 ≤ d)     (hk : 1 ≤ k) (hkd : k ≤ d+1) :     let x : ℝ := d     let t : ℝ := 2*Real.cos (gridAngle d k)     let f := fun t : ℝ => (4*x^2+6*x-1)*t^2 -       ((3*x^4-19*x^2+8*x+8)/2)*t-(32*x-14)     if 2*k ≤ d+1 then f t < 0 else 0 < f t.

**Definition 1.5 (t).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.t`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.t` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines t for the physical double-hub family.

**Definition 1.6 (ell).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.ell`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.ell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines ell for the physical double-hub family.

**Definition 1.7 (u).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.u`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines u for the physical double-hub family.

**Definition 1.8 (v).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.v`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines v for the physical double-hub family.

**Definition 1.9 (A).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.A`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines A for the physical double-hub family.

**Definition 1.10 (B).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.B`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines B for the physical double-hub family.

**Definition 1.11 (C).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.C`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines C for the physical double-hub family.

**Definition 1.12 (E).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.E`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines E for the physical double-hub family.

**Definition 1.13 (f).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.f`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines f for the physical double-hub family.

**Definition 1.14 (F).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.F`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines F for the physical double-hub family.

**Theorem 1.15 (central derivative).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.central_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.central_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem central_derivative (r : ℕ) :     F (4*(r:ℝ)+2) (Real.pi/2) = 0 ∧     HasDerivAt (F (4*(r:ℝ)+2))       (-4*A (4*(r:ℝ)+2)-2*(4*(r:ℝ)+2)*E (4*(r:ℝ)+2)) (Real.pi/2).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.A`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.B`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.C`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.E`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.F`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.Q_one_pos`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.R_neg_one_pos`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.actual_grid_sign`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.candidate_one_multiplicity`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.central_derivative`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.ell`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.f`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.t`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.u`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubGrid.v`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint](FiolDoubleHubEndpoint.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
