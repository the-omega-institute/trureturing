/- GID: D5/S3/QuantumBounds/ReferenceFrameTaxOptimal
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the sharp upper bound for zero-boundary nearest-neighbour averaging. -/

import D5.S3.QuantumBounds.ReferenceFrameTax

/-!
# Optimal reduced reference-frame tax

This module proves optimality only for the finite real zero-boundary nearest-neighbour quadratic
form. It does **not** claim or formalize the physical reduction from excitation-exchange
unitaries, channels, or entanglement fidelity to that quadratic form.
-/

namespace D5.S3.QuantumBounds.ReferenceFrameTax

open scoped BigOperators

/-- The sine-witness value is a universal scale-free upper bound. -/
theorem nearestNeighborQuadratic_le_cos_sq (N : ℕ) (c : Fin N → ℝ) :
    nearestNeighborQuadratic c ≤
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 * ∑ i : Fin N, c i ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [nearestNeighborQuadratic]
  by_cases hNone : N = 1
  · subst N
    unfold nearestNeighborQuadratic
    simp only [Nat.cast_one, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton]
    calc
      _ = 0 := by norm_num
      _ ≤ Real.cos (Real.pi / ((1 : ℝ) + 1)) ^ 2 * c 0 ^ 2 :=
        mul_nonneg
          (sq_nonneg (Real.cos (Real.pi / ((1 : ℝ) + 1))))
          (sq_nonneg (c 0))
  have hNtwo : 2 ≤ N := by omega
  let theta := Real.pi / (N + 1 : ℝ)
  let w : Fin N → ℝ := fun i => Real.sin ((i.val + 1) * theta)
  have hw_pos (i : Fin N) : 0 < w i := by
    have hnum : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
    have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hnat : i.val + 1 < N + 1 := by omega
    have hcast : (i.val : ℝ) + 1 < (N : ℝ) + 1 := by exact_mod_cast hnat
    have hratio : ((i.val : ℝ) + 1) / ((N : ℝ) + 1) < 1 :=
      (div_lt_one hden).2 hcast
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hnum (div_pos Real.pi_pos hden)
    · calc
        ((i.val : ℝ) + 1) * theta =
            Real.pi * (((i.val : ℝ) + 1) / ((N : ℝ) + 1)) := by
              simp only [theta, div_eq_mul_inv]
              ac_rfl
        _ < Real.pi * 1 := mul_lt_mul_of_pos_left hratio Real.pi_pos
        _ = Real.pi := mul_one _
  have hrec (m : Fin N) :
      ((if _h : 0 < m.val then
          w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
        (if _h : m.val + 1 < N then w ⟨m.val + 1, _h⟩ else 0)) / 2 =
        Real.cos theta * w m := by
    simpa only [theta, w] using sine_reference_eigenvector N m
  have weighted_two (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      ((a + b) / 2) ^ 2 ≤ ((u + v) / 4) * (a ^ 2 / u + b ^ 2 / v) := by
    let f : ℕ → ℝ := fun i => if i = 0 then a else b
    let g : ℕ → ℝ := fun i => if i = 0 then u else v
    have hg : ∀ i ∈ Finset.range 2, 0 < g i := by
      intro i hi
      have hi' : i < 2 := Finset.mem_range.mp hi
      interval_cases i <;> simp [g, hu, hv]
    have hcs := Finset.sq_sum_div_le_sum_sq_div
      (Finset.range 2) f hg
    norm_num [Finset.sum_range_succ, f, g] at hcs
    have huv : 0 < u + v := add_pos hu hv
    have hmul : (a + b) ^ 2 ≤ (a ^ 2 / u + b ^ 2 / v) * (u + v) :=
      (div_le_iff₀ huv).mp hcs
    nlinarith
  have hpoint (m : Fin (N)) :
      (((if _h : 0 < m.val then
          c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
        (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2) ^ 2 ≤
        (Real.cos theta * w m / 2) *
          ((if _h : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
                w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
            (if _h : m.val + 1 < N then
              c ⟨m.val + 1, _h⟩ ^ 2 / w ⟨m.val + 1, _h⟩ else 0)) := by
    by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N
    · simp only [hl, hr, ↓reduceDIte]
      have hwl := hw_pos
        ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩
      have hwr := hw_pos ⟨m.val + 1, hr⟩
      have hmrec := hrec m
      simp only [hl, hr, ↓reduceDIte] at hmrec
      calc
        _ ≤ ((w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ +
                w ⟨m.val + 1, hr⟩) / 4) *
              (c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
                  w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ +
                c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩) :=
            weighted_two _ _ _ _ hwl hwr
        _ = _ := by
          congr 1
          linarith
    · simp only [hl, hr, ↓reduceDIte]
      have hwl := hw_pos
        ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩
      have hmrec := hrec m
      simp only [hl, hr, ↓reduceDIte, add_zero] at hmrec
      rw [show Real.cos theta * w m / 2 =
        w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ / 4 by linarith]
      field_simp [hwl.ne']
      ring_nf
      exact le_refl _
    · simp only [hl, hr, ↓reduceDIte]
      have hwr := hw_pos ⟨m.val + 1, hr⟩
      have hmrec := hrec m
      simp only [hl, hr, ↓reduceDIte, zero_add] at hmrec
      rw [show Real.cos theta * w m / 2 = w ⟨m.val + 1, hr⟩ / 4 by linarith]
      field_simp [hwr.ne']
      ring_nf
      exact le_refl _
    · omega
  have hshift_left :
      (∑ m : Fin N, w m *
        (if hl : 0 < m.val then
          c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
            w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0)) =
        ∑ k : Fin N, c k ^ 2 / w k *
          (if hk : k.val + 1 < N then w ⟨k.val + 1, hk⟩ else 0) := by
    let L : Fin N → ℝ := fun m => w m *
      (if hl : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
          w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0)
    let R : Fin N → ℝ := fun k => c k ^ 2 / w k *
      (if hk : k.val + 1 < N then w ⟨k.val + 1, hk⟩ else 0)
    change (∑ m, L m) = ∑ k, R k
    refine Finset.sum_bij_ne_zero
      (fun m _hm _hLm =>
        (⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ : Fin N)) ?_ ?_ ?_ ?_
    · simp
    · intro m₁ _hm₁ hLm₁ m₂ _hm₂ hLm₂ heq
      have hm₁pos : 0 < m₁.val := by
        by_contra h
        exact hLm₁ (by simp [L, h])
      have hm₂pos : 0 < m₂.val := by
        by_contra h
        exact hLm₂ (by simp [L, h])
      apply Fin.ext
      have hval := congrArg Fin.val heq
      dsimp at hval
      omega
    · intro k _hk hRk
      have hnext : k.val + 1 < N := by
        by_contra h
        exact hRk (by simp [R, h])
      let m : Fin N := ⟨k.val + 1, hnext⟩
      have hmpos : 0 < m.val := by simp [m]
      have heq : L m = R k := by
        simp [L, R, m, hmpos, hnext]
        ring
      refine ⟨m, Finset.mem_univ _, ?_, ?_⟩
      · intro hzero
        exact hRk (heq.symm.trans hzero)
      · apply Fin.ext
        simp [m]
    · intro m _hm hLm
      have hmpos : 0 < m.val := by
        by_contra h
        exact hLm (by simp [L, h])
      have hnext : m.val - 1 + 1 < N := by omega
      have hback :
          (⟨m.val - 1 + 1, hnext⟩ : Fin N) = m := by
        ext
        change m.val - 1 + 1 = m.val
        omega
      simp only [L, R, hmpos, hnext, ↓reduceDIte]
      rw [hback]
      exact mul_comm _ _
  have hshift_right :
      (∑ m : Fin N, w m *
        (if hr : m.val + 1 < N then
          c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0)) =
        ∑ k : Fin N, c k ^ 2 / w k *
          (if hk : 0 < k.val then
            w ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0) := by
    let L : Fin N → ℝ := fun m => w m *
      (if hr : m.val + 1 < N then
        c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0)
    let R : Fin N → ℝ := fun k => c k ^ 2 / w k *
      (if hk : 0 < k.val then
        w ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0)
    change (∑ m, L m) = ∑ k, R k
    refine Finset.sum_bij_ne_zero
      (fun m _hm _hLm => (⟨m.val + 1, by
        by_contra h
        exact _hLm (by simp [L, h])⟩ : Fin N)) ?_ ?_ ?_ ?_
    · simp
    · intro m₁ _hm₁ hLm₁ m₂ _hm₂ hLm₂ heq
      apply Fin.ext
      have hval := congrArg Fin.val heq
      dsimp at hval
      omega
    · intro k _hk hRk
      have hkpos : 0 < k.val := by
        by_contra h
        exact hRk (by simp [R, h])
      let m : Fin N := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩
      have hnext : m.val + 1 < N := by
        dsimp [m]
        omega
      have hback :
          (⟨m.val + 1, hnext⟩ : Fin N) = k := by
        ext
        dsimp [m]
        omega
      have heq : L m = R k := by
        simp only [L, R, hnext, hkpos, ↓reduceDIte]
        rw [hback]
        exact mul_comm _ _
      refine ⟨m, Finset.mem_univ _, ?_, ?_⟩
      · intro hzero
        exact hRk (heq.symm.trans hzero)
      · apply Fin.ext
        simp [m]
        omega
    · intro m _hm hLm
      have hnext : m.val + 1 < N := by
        by_contra h
        exact hLm (by simp [L, h])
      simp [L, R, hnext]
      ring
  have hweighted_sum :
      (∑ m : Fin N, w m *
        ((if hl : 0 < m.val then
            c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
              w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
          (if hr : m.val + 1 < N then
            c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0))) =
        2 * Real.cos theta * ∑ k : Fin N, c k ^ 2 := by
    calc
      _ =
          (∑ m : Fin N, w m *
            (if hl : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
                w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0)) +
          (∑ m : Fin N, w m *
            (if hr : m.val + 1 < N then
              c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m _hm
            ring
      _ =
          (∑ k : Fin N, c k ^ 2 / w k *
            (if hk : k.val + 1 < N then w ⟨k.val + 1, hk⟩ else 0)) +
          (∑ k : Fin N, c k ^ 2 / w k *
            (if hk : 0 < k.val then
              w ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0)) := by
            rw [hshift_left, hshift_right]
      _ = ∑ k : Fin N,
          (c k ^ 2 / w k *
              (if hk : k.val + 1 < N then w ⟨k.val + 1, hk⟩ else 0) +
            c k ^ 2 / w k *
              (if hk : 0 < k.val then
                w ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ k : Fin N, 2 * Real.cos theta * c k ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _hk
            have hkrec := hrec k
            have hwne := (hw_pos k).ne'
            calc
              _ = c k ^ 2 / w k *
                  ((if hk : 0 < k.val then
                      w ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩ else 0) +
                    (if hk : k.val + 1 < N then w ⟨k.val + 1, hk⟩ else 0)) := by
                      ring
              _ = c k ^ 2 / w k * (2 * (Real.cos theta * w k)) := by
                      congr 1
                      linarith
              _ = 2 * Real.cos theta * c k ^ 2 := by
                      field_simp [hwne]
      _ = _ := by rw [Finset.mul_sum]
  unfold nearestNeighborQuadratic
  calc
    _ ≤ ∑ m : Fin N,
        (Real.cos theta * w m / 2) *
          ((if hl : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
                w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
            (if hr : m.val + 1 < N then
              c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0)) :=
          Finset.sum_le_sum fun m _hm => hpoint m
    _ = (Real.cos theta / 2) *
        ∑ m : Fin N, w m *
          ((if hl : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ ^ 2 /
                w ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
            (if hr : m.val + 1 < N then
              c ⟨m.val + 1, hr⟩ ^ 2 / w ⟨m.val + 1, hr⟩ else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _hm
          ring
    _ = (Real.cos theta / 2) *
        (2 * Real.cos theta * ∑ k : Fin N, c k ^ 2) := by rw [hweighted_sum]
    _ = Real.cos theta ^ 2 * ∑ k : Fin N, c k ^ 2 := by ring
    _ = Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 * ∑ k : Fin N, c k ^ 2 := by
      rfl

#print axioms nearestNeighborQuadratic_le_cos_sq

end D5.S3.QuantumBounds.ReferenceFrameTax

namespace D5.S3.QuantumBounds.ReferenceFrameTax

theorem reference_frame_tax_isGreatest (N : ℕ) (hN : 1 ≤ N) :
    IsGreatest {q : ℝ | ∃ c : Fin N → ℝ, (∑ i, c i ^ 2) = 1 ∧
      nearestNeighborQuadratic c = q}
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) := by
  fail_if_success ((try simp); done)
  refine ⟨?_, ?_⟩
  · rcases exists_unit_sine_reference_witness N hN with ⟨c, hc, hq⟩
    exact ⟨c, hc, hq⟩
  · intro q hq
    rcases hq with ⟨c, hc, hq⟩
    calc
      q = nearestNeighborQuadratic c := hq.symm
      _ ≤ Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 * ∑ i, c i ^ 2 :=
        nearestNeighborQuadratic_le_cos_sq N c
      _ = Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 := by rw [hc, mul_one]

theorem reference_frame_tax_optimal_identity (N : ℕ) (_hN : 1 ≤ N) :
    1 - Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 =
      Real.sin (Real.pi / (N + 1 : ℝ)) ^ 2 := by
  fail_if_success ((try simp); done)
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (N + 1 : ℝ))]

#print axioms reference_frame_tax_isGreatest
#print axioms reference_frame_tax_optimal_identity

end D5.S3.QuantumBounds.ReferenceFrameTax
