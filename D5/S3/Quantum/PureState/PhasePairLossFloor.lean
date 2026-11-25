/- GID: D5/S3/Quantum/PureState/PhasePairLossFloor
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhasePairLossFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp lower loss coefficients for two-coordinate ensembles on complex disks. -/

import D5.S3.Quantum.PureState.PhaseProductFidelity

/-! The lower comparison for the simplex and cube deficits changes at radius one. -/

namespace D5.S3.Quantum.PureState.PhasePairLossFloor

open PhaseProductFidelity

private theorem loss_split (u : Fin 2 → ℂ) (C : ℝ) :
    let x := ((u 0).re + (u 1).re) / 2
    (1 - cube u) - C * (1 - simplex u) =
      (1 - x) * ((3 + x) / 4 - C * (4 * (2 + x) / 9)) +
        ((u 0).re - (u 1).re)^2 / 16 + C * ((u 0).im + (u 1).im)^2 / 9 := by
  simp [cube, simplex, Fin.prod_univ_two, Fin.sum_univ_two, Complex.normSq_apply]
  ring

private theorem unrestricted (u : Fin 2 → ℂ) :
    (3 / 4 : ℝ) * (1 - simplex u) ≤ 1 - cube u := by
  have h := loss_split u (3 / 4)
  dsimp only at h
  nlinarith only [h, sq_nonneg (1 - ((u 0).re + (u 1).re) / 2),
    sq_nonneg ((u 0).re - (u 1).re), sq_nonneg ((u 0).im + (u 1).im)]

private theorem disk_bound (u : Fin 2 → ℂ) {y C : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1)
    (hu : ∀ k, ‖u k‖ ≤ y) (hC : C ≤ 9 * (3 + y) / (16 * (2 + y))) :
    C * (1 - simplex u) ≤ 1 - cube u := by
  let x := ((u 0).re + (u 1).re) / 2
  let c := 9 * (3 + y) / (16 * (2 + y))
  have hx : x ≤ y := by
    have hre (k : Fin 2) := ((le_abs_self _).trans (Complex.abs_re_le_norm (u k))).trans (hu k)
    dsimp [x]
    linarith only [hre 0, hre 1]
  have hx₁ : x ≤ 1 := hx.trans hy₁
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hfactor : (3 + x) / 4 - c * (4 * (2 + x) / 9) = (y - x) / (4 * (2 + y)) := by
    dsimp [c]
    field_simp
    <;> ring
  have hsharp : c * (1 - simplex u) ≤ 1 - cube u := by
    have h := loss_split u c
    change _ = (1 - x) * ((3 + x) / 4 - c * (4 * (2 + x) / 9)) + _ + _ at h
    rw [hfactor] at h
    have hgap : 0 ≤ (1 - x) * ((y - x) / (4 * (2 + y))) :=
      mul_nonneg (sub_nonneg.mpr hx₁) (div_nonneg (sub_nonneg.mpr hx) (by positivity))
    have hre : 0 ≤ ((u 0).re - (u 1).re)^2 / 16 := by positivity
    have him : 0 ≤ c * ((u 0).im + (u 1).im)^2 / 9 := by positivity
    linarith only [h, hgap, hre, him]
  have hnorm : ‖1 + u 0 + u 1‖ ≤ 3 := calc
    _ ≤ ‖1 + u 0‖ + ‖u 1‖ := norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + ‖u 0‖ + ‖u 1‖ := add_le_add_left (norm_add_le _ _) _
    _ ≤ 3 := by rw [norm_one]; linarith only [hu 0, hu 1, hy₁]
  have hloss : 0 ≤ 1 - simplex u := by
    apply sub_nonneg.mpr
    rw [simplex, Fin.sum_univ_two, ← add_assoc, Complex.normSq_eq_norm_sq]
    have hthree : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
    rw [hthree]
    exact (div_le_one (by positivity)).mpr (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
  exact (mul_le_mul_of_nonneg_right hC hloss).trans hsharp

private theorem singleton_gap (t C : ℝ) :
    mixedDeficit cube (fun _ : Fin 1 => 1) (fun _ (_ : Fin 2) => (t : ℂ)) -
      C * mixedDeficit simplex (fun _ : Fin 1 => 1) (fun _ (_ : Fin 2) => (t : ℂ)) =
        (1 - t^2) * ((3 + t^2) / 4 - C * (4 * (2 + t^2) / 9)) := by
  simpa [mixedDeficit, Fin.sum_univ_one, ← Complex.ofReal_mul, pow_two] using
    loss_split (fun _ => ((t * t : ℝ) : ℂ)) C

/-- The exact lower loss coefficients on a closed disk, with no normalization of the weights. -/
theorem mixed_lower_coefficient_iff (R C : ℝ) (hR : 0 ≤ R) :
    (∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → Fin 2 → ℂ),
      (∀ i j, 0 ≤ p i * p j) → (∀ i, p i ≠ 0 → ∀ k, ‖v i k‖ ≤ R) →
      C * mixedDeficit simplex p v ≤ mixedDeficit cube p v) ↔
    (if R ≤ 1 then C ≤ 9 * (3 + R^2) / (16 * (2 + R^2)) else C = 3 / 4) := by
  constructor
  · intro h
    let f (t : ℝ) := (3 + t^2) / 4 - C * (4 * (2 + t^2) / 9)
    have hf : Continuous f := by unfold f; fun_prop
    have hs (t : ℝ) (ht : 0 ≤ t) (htR : t ≤ R) : 0 ≤ (1 - t^2) * f t := by
      have hrow := h 1 (fun _ => 1) (fun _ _ => (t : ℂ)) (by intros; norm_num)
        (fun _ _ _ => by rwa [Complex.norm_of_nonneg ht])
      rw [← singleton_gap]
      exact sub_nonneg.mpr hrow
    by_cases hlt : R < 1
    · rw [ite_eq_left hlt.le]
      have hpos : 0 < 1 - R^2 := by nlinarith only [sq_lt_sq' (by linarith) hlt]
      have hval := (mul_nonneg_iff_of_pos_left hpos).mp (hs R hR le_rfl)
      exact (le_div_iff₀ (by positivity)).mpr (by dsimp [f] at hval; linarith only [hval])
    · have h₁R : 1 ≤ R := le_of_not_gt hlt
      have hleft : 0 ≤ f 1 := by
        apply ge_of_tendsto
          (hf.continuousAt.continuousWithinAt (s := Set.Iio 1))
        have hn : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), 0 ≤ t :=
          (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin, hn] with t ht ht₀
        change t < 1 at ht
        have hpos : 0 < 1 - t^2 := by nlinarith only [sq_lt_sq' (by linarith) ht]
        exact (mul_nonneg_iff_of_pos_left hpos).mp (hs t ht₀ (ht.le.trans h₁R))
      by_cases hle : R ≤ 1
      · have hEq : R = 1 := le_antisymm hle h₁R
        rw [hEq, ite_eq_left le_rfl]
        norm_num [f] at hleft ⊢
        linarith only [hleft]
      · rw [ite_eq_right hle]
        have hright : f 1 ≤ 0 := by
          apply le_of_tendsto
            (hf.continuousAt.continuousWithinAt (s := Set.Ioi 1))
          have hnear : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Ioi 1), t ≤ R :=
            (eventually_le_nhds (lt_of_not_ge hle)).filter_mono nhdsWithin_le_nhds
          filter_upwards [self_mem_nhdsWithin, hnear] with t ht htR
          change 1 < t at ht
          have hneg : 1 - t^2 < 0 := by nlinarith only [sq_lt_sq' (by linarith) ht]
          exact nonpos_of_mul_nonneg_right
            (by simpa only [mul_comm (f t)] using hs t (by linarith) htR) hneg
        norm_num [f] at hleft hright
        linarith only [hleft, hright]
  · intro hC m p v hp hv
    unfold mixedDeficit
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hi : p i = 0
    · simp [hi]
    by_cases hj : p j = 0
    · simp [hj]
    let u (k : Fin 2) := star (v i k) * v j k
    have hpair : C * (1 - simplex u) ≤ 1 - cube u := by
      by_cases hle : R ≤ 1
      · rw [ite_eq_left hle] at hC
        have hu (k : Fin 2) : ‖u k‖ ≤ R^2 := by
          simpa [u, norm_mul, pow_two] using
            mul_le_mul (hv i hi k) (hv j hj k) (norm_nonneg _) hR
        have hy₁ : R^2 ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ hR hle 2
        exact disk_bound u (sq_nonneg R) hy₁ hu hC
      · rw [ite_eq_right hle] at hC
        rw [hC]
        exact unrestricted u
    simpa only [u, mul_left_comm (p i * p j) C] using
      mul_le_mul_of_nonneg_left hpair (hp i j)

end D5.S3.Quantum.PureState.PhasePairLossFloor
