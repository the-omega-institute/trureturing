/- GID: D5/S3/QuantumBounds/ReferenceFrameTax
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the flat tax and a sine witness for zero-boundary nearest-neighbour averaging. -/

/-
Library-search audit trail (mathlib v4.31.0, offline, 2026-08-12):

* Searches for path-graph adjacency spectra, tridiagonal eigenvalues, and nearest-neighbour
  operator norms found the combinatorial `SimpleGraph.pathGraph`, but no packaged spectral theorem
  for its adjacency matrix.
* `Real.sin_add` and `Real.sin_sub` supply the coordinate recurrence. Exact special-angle facts
  `Real.sq_sin_pi_div_three`, `Real.sin_pi_div_four`, and `Real.cos_pi_div_five` supply the
  finite consistency checks.
* Mathlib has Chebyshev polynomial infrastructure, but the searched evaluation API does not
  directly provide the finite path operator-norm bound needed for optimality.

Repository search audit trail (working tree, 2026-08-12):

* Searches under `D5/` for entanglement fidelity, reference frames, excitation exchange,
  Dirichlet nearest-neighbour averaging, and the target theorem name found no prior formalization.
* The two stale-queue comparison modules named by the caller do exist:
  `D5/S3/Quantum/DoubleArtanhBounds.lean` and
  `D5/S3/QuantumBounds/LagrangeGramIdentity.lean`.
-/

import Mathlib

/-!
# Reduced reference-frame tax identities

This module proves only the finite real linear-algebra identities obtained after replacing the
physical problem by zero-boundary nearest-neighbour averaging. It does **not** claim or formalize
the reduction from excitation-exchange unitaries, channels, or entanglement fidelity to this
quadratic form.

The exact flat-vector identity is proved for `2 ≤ N`; at `N = 1` its advertised extension is
false, and the actual tax is proved to be `1`. The sine vector is proved coordinatewise to be an
eigenvector, and its resulting quadratic value is summed. The operator-norm upper bound required
to call this value optimal is not proved here, so no theorem in this module claims the optimal
identity or the asserted two-dimensional degeneracy.
-/

namespace D5.S3.QuantumBounds.ReferenceFrameTax

open scoped BigOperators

/-- The squared norm after zero-boundary nearest-neighbour averaging.

This is the module's single definition: naming the repeated pair of dependent boundary tests
keeps every theorem statement readable while leaving the finite quadratic form fully explicit. -/
noncomputable def nearestNeighborQuadratic {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ m : Fin N,
    (((if _h : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2) ^ 2

/-- For every ladder of length at least two, the uniform unit vector has exact tax `3 / (2N)`. -/
theorem flat_reference_frame_tax (N : ℕ) (hN : 2 ≤ N) :
    1 - nearestNeighborQuadratic (N := N) (fun _ => 1 / Real.sqrt (N : ℝ)) =
      3 / (2 * (N : ℝ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hN
  have hNk : N = k + 2 := by omega
  clear hk hN
  subst N
  unfold nearestNeighborQuadratic
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, lt_self_iff_false, ↓reduceDIte, zero_add,
    lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, Nat.cast_add, Nat.cast_ofNat, one_div,
    Fin.val_succ, Fin.val_castSucc, add_lt_add_iff_right, Order.add_one_le_iff, Fin.is_lt,
    add_self_div_two, inv_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Fin.succ_last, Nat.succ_eq_add_one, Fin.val_last, add_zero]
  have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [Real.sq_sqrt hkpos.le]
  field_simp [Real.sqrt_ne_zero'.2 hkpos]
  rw [Real.sq_sqrt hkpos.le]
  ring

example (N : ℕ) (hN : 2 ≤ N) :
    1 - nearestNeighborQuadratic (N := N) (fun _ => 1 / Real.sqrt (N : ℝ)) =
      3 / (2 * (N : ℝ)) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact flat_reference_frame_tax N hN

/-- At `N = 1`, both neighbours are boundary zeros, so the actual flat tax is `1`, not `3/2`. -/
theorem flat_reference_frame_tax_one :
    1 - nearestNeighborQuadratic (N := 1) (fun _ => 1 / Real.sqrt (1 : ℝ)) = 1 := by
  simp [nearestNeighborQuadratic]

example :
    1 - nearestNeighborQuadratic (N := 1) (fun _ => 1 / Real.sqrt (1 : ℝ)) = 1 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact flat_reference_frame_tax_one

/-- The unnormalized box sine vector is an eigenvector of zero-boundary nearest-neighbour
averaging with eigenvalue `cos (π / (N+1))`. This is an attainment witness, not an optimality
statement. -/
theorem sine_reference_eigenvector (N : ℕ) (m : Fin N) :
    let theta := Real.pi / (N + 1 : ℝ)
    let c : Fin N → ℝ := fun i => Real.sin ((i.val + 1) * theta)
    ((if _h : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2 =
      Real.cos theta * c m := by
  dsimp only
  let theta := Real.pi / (N + 1 : ℝ)
  have htrig (x : ℝ) :
      (Real.sin (x - theta) + Real.sin (x + theta)) / 2 =
        Real.cos theta * Real.sin x := by
    rw [Real.sin_sub, Real.sin_add]
    ring
  have hleft :
      (if _h : 0 < m.val then
          Real.sin (((((m.val - 1 : ℕ) : ℝ) + 1) * theta)) else 0) =
        Real.sin (m.val * theta) := by
    by_cases hl : 0 < m.val
    · simp only [hl, ↓reduceDIte]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ m.val)]
      norm_num
    · have hm0 : m.val = 0 := by omega
      simp [hm0]
  have hright :
      (if _h : m.val + 1 < N then
          Real.sin (((((m.val + 1 : ℕ) : ℝ) + 1) * theta)) else 0) =
        Real.sin ((m.val + 2) * theta) := by
    by_cases hr : m.val + 1 < N
    · simp only [hr, ↓reduceDIte]
      congr 1
      push_cast
      ring
    · have hm : m.val + 1 = N := by omega
      simp only [hr, ↓reduceDIte]
      symm
      have harg : (((m.val : ℝ) + 2) * theta) = Real.pi := by
        dsimp [theta]
        have hmR : (m.val : ℝ) + 1 = N := by exact_mod_cast hm
        rw [show (m.val : ℝ) + 2 = (N : ℝ) + 1 by linarith]
        field_simp
      rw [harg]
      exact Real.sin_pi
  change
    ((if _h : 0 < m.val then
        Real.sin (((((m.val - 1 : ℕ) : ℝ) + 1) * theta)) else 0) +
      (if _h : m.val + 1 < N then
        Real.sin (((((m.val + 1 : ℕ) : ℝ) + 1) * theta)) else 0)) / 2 =
      Real.cos theta * Real.sin (((m.val : ℝ) + 1) * theta)
  rw [hleft, hright]
  convert htrig (((m.val + 1 : ℕ) : ℝ) * theta) using 1 <;> push_cast <;> ring

example (N : ℕ) (m : Fin N) :
    let theta := Real.pi / (N + 1 : ℝ)
    let c : Fin N → ℝ := fun i => Real.sin ((i.val + 1) * theta)
    ((if _h : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2 =
      Real.cos theta * c m := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact sine_reference_eigenvector N m

/-- Summing the coordinate witness gives its exact quadratic value. This theorem remains a
witness equality and does not assert that the value is maximal among unit vectors. -/
theorem sine_reference_quadratic_witness (N : ℕ) :
    let theta := Real.pi / (N + 1 : ℝ)
    nearestNeighborQuadratic (N := N) (fun m => Real.sin ((m.val + 1) * theta)) =
      Real.cos theta ^ 2 * ∑ m : Fin N, Real.sin ((m.val + 1) * theta) ^ 2 := by
  dsimp
  unfold nearestNeighborQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  change
    (((if _h : 0 < m.val then
        (fun i : Fin N => Real.sin ((i.val + 1) * (Real.pi / (N + 1 : ℝ))))
          ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < N then
        (fun i : Fin N => Real.sin ((i.val + 1) * (Real.pi / (N + 1 : ℝ))))
          ⟨m.val + 1, _h⟩ else 0)) / 2) ^ 2 = _
  rw [sine_reference_eigenvector N m]
  ring

example (N : ℕ) :
    let theta := Real.pi / (N + 1 : ℝ)
    nearestNeighborQuadratic (N := N) (fun m => Real.sin ((m.val + 1) * theta)) =
      Real.cos theta ^ 2 * ∑ m : Fin N, Real.sin ((m.val + 1) * theta) ^ 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact sine_reference_quadratic_witness N

/-- For `1 ≤ N`, a normalized sine vector attains quadratic value
`cos² (π / (N+1))`. This proves the witness/lower-bound half only; it does not say that no unit
vector has a larger value. -/
theorem exists_unit_sine_reference_witness (N : ℕ) (hN : 1 ≤ N) :
    let theta := Real.pi / (N + 1 : ℝ)
    ∃ c : Fin N → ℝ,
      (∑ i : Fin N, c i ^ 2) = 1 ∧
      nearestNeighborQuadratic c = Real.cos theta ^ 2 := by
  dsimp
  let theta := Real.pi / (N + 1 : ℝ)
  let s := ∑ i : Fin N, Real.sin ((i.val + 1) * theta) ^ 2
  have hden : (1 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hN
  have htheta_pos : 0 < theta := div_pos Real.pi_pos (by linarith)
  have htheta_lt : theta < Real.pi := div_lt_self Real.pi_pos hden
  have hsin : 0 < Real.sin theta := Real.sin_pos_of_pos_of_lt_pi htheta_pos htheta_lt
  have hs : 0 < s := by
    let i0 : Fin N := ⟨0, by omega⟩
    apply Finset.sum_pos' (fun i _ => sq_nonneg _)
    refine ⟨i0, Finset.mem_univ _, ?_⟩
    simpa [i0] using sq_pos_of_pos hsin
  let c : Fin N → ℝ := fun i => (1 / Real.sqrt s) * Real.sin ((i.val + 1) * theta)
  refine ⟨c, ?_, ?_⟩
  · change (∑ i : Fin N, ((1 / Real.sqrt s) * Real.sin ((i.val + 1) * theta)) ^ 2) = 1
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    change (1 / Real.sqrt s) ^ 2 * s = 1
    field_simp [Real.sqrt_ne_zero'.2 hs]
    rw [Real.sq_sqrt hs.le]
  · have hscale (a : ℝ) (v : Fin N → ℝ) :
        nearestNeighborQuadratic (fun i => a * v i) =
          a ^ 2 * nearestNeighborQuadratic v := by
      unfold nearestNeighborQuadratic
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
        simp [hl, hr] <;> ring
    change nearestNeighborQuadratic
      (fun i => (1 / Real.sqrt s) * Real.sin ((i.val + 1) * theta)) = _
    rw [hscale]
    have hraw := sine_reference_quadratic_witness N
    dsimp at hraw
    change nearestNeighborQuadratic (fun i => Real.sin ((i.val + 1) * theta)) =
      Real.cos theta ^ 2 * s at hraw
    rw [hraw]
    have hscalar : (1 / Real.sqrt s) ^ 2 * s = 1 := by
      field_simp [Real.sqrt_ne_zero'.2 hs]
      rw [Real.sq_sqrt hs.le]
    calc
      (1 / Real.sqrt s) ^ 2 * (Real.cos theta ^ 2 * s) =
          Real.cos theta ^ 2 * ((1 / Real.sqrt s) ^ 2 * s) := by ring
      _ = Real.cos theta ^ 2 := by rw [hscalar, mul_one]

example (N : ℕ) (hN : 1 ≤ N) :
    let theta := Real.pi / (N + 1 : ℝ)
    ∃ c : Fin N → ℝ,
      (∑ i : Fin N, c i ^ 2) = 1 ∧
      nearestNeighborQuadratic c = Real.cos theta ^ 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact exists_unit_sine_reference_witness N hN

/-- At `N = 2`, the compiled flat tax coincides with the sine-witness tax `sin²(π/3)`. -/
theorem flat_sine_tax_coincide_two :
    1 - nearestNeighborQuadratic (N := 2) (fun _ => 1 / Real.sqrt (2 : ℝ)) =
      Real.sin (Real.pi / (2 + 1 : ℝ)) ^ 2 := by
  have hflat := flat_reference_frame_tax 2 (by norm_num)
  norm_num at hflat
  simp only [one_div]
  rw [hflat]
  rw [show (2 + 1 : ℝ) = 3 by norm_num]
  exact Real.sq_sin_pi_div_three.symm

example :
    1 - nearestNeighborQuadratic (N := 2) (fun _ => 1 / Real.sqrt (2 : ℝ)) =
      Real.sin (Real.pi / (2 + 1 : ℝ)) ^ 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact flat_sine_tax_coincide_two

/-- At `N = 3`, the compiled flat tax coincides with the sine-witness tax `sin²(π/4)`. -/
theorem flat_sine_tax_coincide_three :
    1 - nearestNeighborQuadratic (N := 3) (fun _ => 1 / Real.sqrt (3 : ℝ)) =
      Real.sin (Real.pi / (3 + 1 : ℝ)) ^ 2 := by
  have hflat := flat_reference_frame_tax 3 (by norm_num)
  norm_num at hflat
  simp only [one_div]
  rw [hflat]
  rw [show (3 + 1 : ℝ) = 4 by norm_num, Real.sin_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

example :
    1 - nearestNeighborQuadratic (N := 3) (fun _ => 1 / Real.sqrt (3 : ℝ)) =
      Real.sin (Real.pi / (3 + 1 : ℝ)) ^ 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact flat_sine_tax_coincide_three

/-- At `N = 4`, the sine-witness tax is strictly smaller than the compiled flat tax `3/8`. -/
theorem sine_tax_lt_flat_tax_four :
    Real.sin (Real.pi / (4 + 1 : ℝ)) ^ 2 <
      1 - nearestNeighborQuadratic (N := 4) (fun _ => 1 / Real.sqrt (4 : ℝ)) := by
  have hflat := flat_reference_frame_tax 4 (by norm_num)
  norm_num at hflat
  norm_num [one_div]
  rw [hflat]
  have hsqrt : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hpyth := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at hpyth
  have hsqrtSq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

example :
    Real.sin (Real.pi / (4 + 1 : ℝ)) ^ 2 <
      1 - nearestNeighborQuadratic (N := 4) (fun _ => 1 / Real.sqrt (4 : ℝ)) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact sine_tax_lt_flat_tax_four

#print axioms flat_reference_frame_tax
#print axioms flat_reference_frame_tax_one
#print axioms sine_reference_eigenvector
#print axioms sine_reference_quadratic_witness
#print axioms exists_unit_sine_reference_witness
#print axioms flat_sine_tax_coincide_two
#print axioms flat_sine_tax_coincide_three
#print axioms sine_tax_lt_flat_tax_four

end D5.S3.QuantumBounds.ReferenceFrameTax
