# Double-hub rootgeometry

## Abstract

The physical double-hub family: rootgeometry.

The intermediate value theorem produces one phase zero in each interval with opposite endpoint signs. Exponentiation is injective on the open upper semicircle. Real coefficients supply conjugate lower roots; the two families are disjoint. A degree bound of 2N then exhausts the polynomial and proves simplicity.

The exact b-grid values at d=2 are -21 and 216; at d=3 they are -82 and 234; at d=4 they are 42-69sqrt(5),42+69sqrt(5),2952. These boundary evaluations join the uniform d>=5 sign estimate.

For residue 3 modulo 4, an intermediate value solution of v+ell*u=0 lies in the central gap and has positive phase, because the resulting g_d(t)u^2 is strictly positive. For residue 2 the negative derivative at pi/2 gives a nearby positive point on the left and negative point on the right, including d=2.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (exp upper injective).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.exp_upper_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.exp_upper_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem exp_upper_injective :     Set.InjOn (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (Set.Icc 0 Real.pi).

**Theorem 1.2 (roots from alternating samples).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_from_alternating_samples`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_from_alternating_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs an ordered root in each disjoint interval from strict sign alternation. Exact source statement: theorem roots_from_alternating_samples (d n : ℕ) (hd : 2 ≤ d)     (s : Fin (n+1) → ℝ) (hmono : StrictMono s)     (hbound : ∀ j, 0 ≤ s j ∧ s j ≤ Real.pi)     (hsign : ∀ j : Fin n,       (phaseValue d (s j.castSucc)).re*(phaseValue d (s j.succ)).re < 0) :     ∃ theta : Fin n → ℝ,       (∀ j, s j.castSucc < theta j ∧ theta j < s j.succ) ∧       StrictMono theta ∧       (∀ j, 0 < theta j ∧ theta j < Real.pi ∧         ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta j:ℂ)*Complex.I))).

**Theorem 1.3 (roots exhausted by upper family).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_exhausted_by_upper_family`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_exhausted_by_upper_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs disjoint upper/conjugate root multisets and exhausts the exact degree. Exact source statement: theorem roots_exhausted_by_upper_family (p : Polynomial ℝ) (n : ℕ)     (hp : p ≠ 0) (hdeg : p.natDegree ≤ 2*n) (r : Fin n → ℂ)     (hrinj : Function.Injective r) (hrupper : ∀ j, 0 < (r j).im)     (hrroot : ∀ j, (p.map Complex.ofRealHom).IsRoot (r j)) :     (p.map Complex.ofRealHom).roots =       Finset.univ.val.map r + Finset.univ.val.map (fun j => star (r j)) ∧     (p.map Complex.ofRealHom).roots.Nodup.

**Theorem 1.4 (phaseValue half pi negative).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.phaseValue_half_pi_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.phaseValue_half_pi_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem phaseValue_half_pi_negative (d : ℕ) (hd : 2 ≤ d) (hi : d%4 ≠ 2) :     (phaseValue d (Real.pi/2)).re < 0.

**Theorem 1.5 (small b grid values).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.small_b_grid_values`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.small_b_grid_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Discharges the exact d=2,3,4 numerical premises of the uniform sign proof. Exact source statement: theorem small_b_grid_values :     phaseValue 2 (Real.pi/3) = -21 ∧ phaseValue 2 Real.pi = 216 ∧     phaseValue 3 (Real.pi/2) = -82 ∧ phaseValue 3 Real.pi = 234 ∧     phaseValue 4 (Real.pi/5) = ((42-69*Real.sqrt 5:ℝ):ℂ) ∧     phaseValue 4 (3*Real.pi/5) = ((42+69*Real.sqrt 5:ℝ):ℂ) ∧     phaseValue 4 Real.pi = 2952.

**Theorem 1.6 (odd b sign large).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.odd_b_sign_large`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.odd_b_sign_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem odd_b_sign_large (d j : ℕ) (hd : 5 ≤ d) (ho : Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :     let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)     if 4*j ≤ d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re.

**Theorem 1.7 (even b sign large).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.even_b_sign_large`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.even_b_sign_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem even_b_sign_large (d j : ℕ) (hd : 5 ≤ d) (ho : ¬ Odd d)     (hj : 1 ≤ j) (hjd : 2*j ≤ d+2) :     let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)     if 2*(2*j-1) ≤ d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re.

**Theorem 1.8 (actual central derivative).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_central_derivative (r : ℕ) :     HasDerivAt (fun theta : ℝ => (phaseValue (4*r+2) theta).re)       (-8*(4*(r:ℝ)+2)^4-16*(4*(r:ℝ)+2)^2*(2*(4*(r:ℝ)+2)-1)) (Real.pi/2).

**Theorem 1.9 (actual central two sides).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_two_sides`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_two_sides` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repairs the residue2 central grid with actual phase derivative evidence. Exact source statement: theorem actual_central_two_sides (r : ℕ) (a b : ℝ)     (ha : a < Real.pi/2) (hb : Real.pi/2 < b) :     ∃ l q : ℝ, a < l ∧ l < Real.pi/2 ∧ Real.pi/2 < q ∧ q < b ∧       0 < (phaseValue (4*r+2) l).re ∧ (phaseValue (4*r+2) q).re < 0.

**Theorem 1.10 (central gap residue three).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.central_gap_residue_three`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.central_gap_residue_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses IVT and simultaneous-nonzero/positivity facts to construct the missing central positive sample. Exact source statement: theorem central_gap_residue_three (r : ℕ) :     ∃ c : ℝ, Real.pi/2 < c ∧ c < 2*Real.pi*((r:ℝ)+1)/(4*(r:ℝ)+3) ∧       0 < (phaseValue (4*r+3) c).re.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_derivative`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.actual_central_two_sides`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.central_gap_residue_three`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.even_b_sign_large`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.exp_upper_injective`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.odd_b_sign_large`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.phaseValue_half_pi_negative`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_exhausted_by_upper_family`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.roots_from_alternating_samples`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.small_b_grid_values`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubPhase](FiolDoubleHubPhase.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
