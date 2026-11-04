# Double-hub phase

## Abstract

The physical double-hub family: phase.

Writing t=2cos(theta) and ell=2cos(theta/2), the phase is A t v^2+ell((B+C+E)t-E)uv+f_d(t)u^2. Here u,v are sine ratios for odd d and cosines for even d, and f_d(t)=(4d^2+6d-1)t^2-(3d^4-19d^2+8d+8)t/2-(32d-14).

For odd d the grids are a_j=2pi j/d and b_j=2pi j/(d+1), giving phase values A t and f_d(t). For even d they are a_j=(2j-1)pi/d and b_j=(2j-1)pi/(d+1), giving A t(2-t) and (2-t)f_d(t). All surviving H_3 and H_4 contributions are retained.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (ep).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines ep for the physical double-hub family.

**Theorem 1.2 (ep pow).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem ep_pow (x : ℝ) (n : ℕ) : ep x^n = ep (x*n).

**Definition 1.3 (realVal).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.realVal`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.realVal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines realVal for the physical double-hub family.

**Definition 1.4 (fValue).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.fValue`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.fValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines fValue for the physical double-hub family.

**Theorem 1.5 (Q phase reduced).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.Q_phase_reduced`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.Q_phase_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses the derived recurrence to obtain the exact real two-term phase reduction. Exact source statement: theorem Q_phase_reduced (d : ℕ) (hd : 2 ≤ d) (theta : ℝ)     (hs : Real.sin (theta/2) ≠ 0) :     let x : ℝ := d     let u := realVal d 0 theta     let v := realVal d 1 theta     let ell := 2*Real.cos (theta/2)     let t := 2*Real.cos theta     phaseValue d theta =       ((2*x^4*t*v^2 + ell*(((3/2:ℝ)*x^2*(x^2-1)+         4*x*(x-1)*(2*x-1)+8*x*(2*x-1))*t-8*x*(2*x-1))*u*v+         fValue x t*u^2 : ℝ):ℂ).

**Theorem 1.6 (odd a values).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_values`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_a_values (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)     (hj : 1 ≤ j) (hjd : 2*j < d) :     let a := 2*Real.pi*(j:ℝ)/(d:ℝ)     realVal d 0 a = 0 ∧ realVal d 1 a = (-1:ℝ)^j.

**Theorem 1.7 (odd b values).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_values`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_b_values (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :     let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)     realVal d 1 b = 0 ∧ realVal d 0 b = (-1:ℝ)^(j+1).

**Theorem 1.8 (odd a phase).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_a_phase (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)     (hj : 1 ≤ j) (hjd : 2*j < d) :     let a := 2*Real.pi*(j:ℝ)/(d:ℝ)     phaseValue d a = ((2*(d:ℝ)^4*(2*Real.cos a):ℝ):ℂ).

**Theorem 1.9 (odd b phase).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_b_phase (d j : ℕ) (hd : 2 ≤ d) (ho : Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :     let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)     phaseValue d b = ((fValue (d:ℝ) (2*Real.cos b):ℝ):ℂ).

**Theorem 1.10 (even a phase).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_a_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_a_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem even_a_phase (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d) :     let a := (2*(j:ℝ)-1)*Real.pi/(d:ℝ)     phaseValue d a = ((2*(d:ℝ)^4*(2*Real.cos a)*(2-2*Real.cos a):ℝ):ℂ).

**Theorem 1.11 (even b phase).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_b_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_b_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem even_b_phase (d j : ℕ) (hd : 2 ≤ d) (ho : ¬ Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d+2) :     let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)     phaseValue d b = (((2-2*Real.cos b)*fValue (d:ℝ) (2*Real.cos b):ℝ):ℂ).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.Q_phase_reduced`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.ep_pow`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_a_phase`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.even_b_phase`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.fValue`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_phase`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_a_values`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_phase`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.odd_b_values`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhase.realVal`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal](FiolDoubleHubReciprocal.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
