/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Critical-scale coefficient and boundary limits for the growing cyclic moment fit. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit

/-! Critical-scale limits and boundary signs for the coupled moment fit. -/

open Filter Finset Matrix
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits

noncomputable section

set_option autoImplicit false

def budget (n : ℕ) : ℝ := (n : ℝ) * (n + 1) / 5

def target (n : ℕ) (h : ℝ) : Fin 3 → ℝ :=
  ![1 - budget n * h^2, budget n / (n : ℝ)^2, 3 * (n : ℝ)^3 * budget n * h^2 / 4]

/-- The coefficient fit associated with the critical-scale budget. -/
def coefficientFit (S : Finset ℝ) (n : ℕ) (h : ℝ) : Fin 3 → ℝ :=
  (coupledMomentMatrix S n h)⁻¹ *ᵥ target n h

/-- A signed weight at a front offset from the growing radius. -/
def boundaryValue (S : Finset ℝ) (n : ℕ) (h offset : ℝ) : ℝ :=
  let x := ((n : ℝ) + offset) / n
  let u := (n : ℝ) * h
  let f := frontFeatures u x 0
  let z := frontFeatures u x 1
  coefficientRow n f z (1 - f) ⬝ᵥ coefficientFit S n h

/-- A signed weight at a fixed offset from the antipode. -/
def rearValue (S : Finset ℝ) (n : ℕ) (h r : ℝ) : ℝ :=
  let w := rearWeight h r
  coefficientRow n (1 - w) (rearMoment h r / (n : ℝ)^2) w ⬝ᵥ coefficientFit S n h

private theorem target_tendsto {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K)) :
    Tendsto (fun n => target n (h n)) atTop (𝓝 ![(1 : ℝ), 1/5, 3*K/20]) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  let b := fun n : ℕ => (1 + (n : ℝ)⁻¹) / 5
  have hb : Tendsto b atTop (𝓝 (1/5 : ℝ)) := by
    simpa [b] using (tendsto_const_nhds.add hi (a := (1 : ℝ))).div_const 5
  have hb1 : Tendsto (fun n : ℕ => budget n / (n : ℝ)^2) atTop (𝓝 (1/5 : ℝ)) := by
    apply hb.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    dsimp [budget, b]
    field_simp
    <;> ring
  have hmass : Tendsto (fun n : ℕ => budget n * (h n)^2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => b n * ((n : ℝ)^5 * (h n)^2) * ((n : ℝ)⁻¹)^3)
        atTop (𝓝 0) := by
      simpa using (hb.mul hK).mul (hi.pow 3)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    dsimp [b,budget]
    field_simp
    <;> ring
  have hrear : Tendsto (fun n : ℕ => 3 * (n : ℝ)^3 * budget n * (h n)^2 / 4)
      atTop (𝓝 (3*K/20)) := by
    have ht := ((hb.mul hK).const_mul (3/4 : ℝ))
    have he : (3/4 : ℝ) * (1/5 * K) = 3*K/20 := by ring
    rw [he] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    dsimp [b,budget]
    field_simp
    <;> ring
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simpa [target] using tendsto_const_nhds.sub hmass (a := (1 : ℝ))
  · exact hb1
  · exact hrear

private theorem critical_mesh_limits {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K)) :
    (Tendsto h atTop (𝓝 0)) ∧
      (Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0)) ∧
      (Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have ht : Tendsto (fun n : ℕ => ((n : ℝ)^5 * (h n)^2)^2 * ((n : ℝ)⁻¹)^3)
      atTop (𝓝 0) := by simpa using (hK.pow 2).mul (hi.pow 3)
  have hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    field_simp [hn0]
  obtain ⟨hh,hu⟩ := mesh_limits hscale
  exact ⟨hh,hu,hscale⟩

def limitCoefficients (S : Finset ℝ) (K : ℝ) : Fin 3 → ℝ :=
  ![3/4, -3/4, (3*K/20 + 3*(∑ r ∈ S, r^2)/4) / (S.card : ℝ)]

private theorem limit_matrix_mul (S : Finset ℝ) (hS : S.Nonempty) (K : ℝ) :
    (!![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)]) *ᵥ limitCoefficients S K
      = ![(1 : ℝ), 1/5, 3*K/20] := by
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, limitCoefficients]
  all_goals field_simp [hs] <;> ring

theorem coefficient_tendsto {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    Tendsto (fun n => readout ((S,n),h n)) atTop (𝓝 (limitCoefficients S K)) := by
  dsimp only [coefficientFit]
  obtain ⟨hh,hu,hscale⟩ := critical_mesh_limits hK
  let M := !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0; 0, ∑ r ∈ S, r^2, (S.card : ℝ)]
  have hM : Tendsto (fun n => coupledMomentMatrix S n (h n)) atTop (𝓝 M) :=
    coupledMatrix_tendsto hscale S
  have hdet : M.det ≠ 0 := by
    have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    rw [show M.det = 16 * (S.card : ℝ) / 45 from coupledLimit_det S]
    positivity
  have hInv : Tendsto (fun n => (coupledMomentMatrix S n (h n))⁻¹) atTop (𝓝 M⁻¹) := by
    apply (continuousAt_matrix_inv M ?_).tendsto.comp hM
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hb := target_tendsto hK
  have hout : Tendsto (fun n => (coupledMomentMatrix S n (h n))⁻¹ *ᵥ target n (h n)) atTop
      (𝓝 (M⁻¹ *ᵥ ![(1 : ℝ), 1/5, 3*K/20])) := by
    apply tendsto_pi_nhds.2
    intro i
    simp only [mulVec, dotProduct]
    apply tendsto_finsetSum
    intro j _
    exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hInv i) j).mul (tendsto_pi_nhds.1 hb j)
  have he : M *ᵥ limitCoefficients S K = ![(1 : ℝ), 1/5, 3*K/20] :=
    limit_matrix_mul S hS K
  rw [← he, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec] at hout
  exact hout


/-- The first two coefficient errors are controlled by the scaled residual with
the third coefficient held fixed. -/
private theorem two_row_scaled_error {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : Tendsto (fun n => (M n).submatrix Fin.castSucc Fin.castSucc) atTop (𝓝 P))
    (hd : P.det ≠ 0) {a b c : ℕ → Fin 3 → ℝ}
    (heq : ∀ᶠ n in atTop, M n *ᵥ a n = b n)
    (hc : ∀ᶠ n in atTop, a n 2 = c n 2)
    (hr : Tendsto (fun (n : ℕ) => fun i : Fin 2 => (n : ℝ) *
      (b n i.castSucc - (M n *ᵥ c n) i.castSucc)) atTop (𝓝 0)) :
    Tendsto (fun (n : ℕ) => fun i : Fin 2 => (n : ℝ) *
      (a n i.castSucc - c n i.castSucc)) atTop (𝓝 0) := by
  let Q := fun n => (M n).submatrix (Fin.castSucc : Fin 2 → Fin 3) Fin.castSucc
  let r := fun (n : ℕ) => fun i : Fin 2 => (n : ℝ) *
    (b n i.castSucc - (M n *ᵥ c n) i.castSucc)
  let e := fun (n : ℕ) => fun i : Fin 2 => (n : ℝ) * (a n i.castSucc - c n i.castSucc)
  have hdet := (continuous_id.matrix_det.continuousAt (x := P)).tendsto.comp hP
  have hinv : Tendsto (fun n => (Q n)⁻¹) atTop (𝓝 P⁻¹) := by
    apply (continuousAt_matrix_inv P ?_).tendsto.comp hP
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd
  have hm : Tendsto (fun n => (Q n)⁻¹ *ᵥ r n) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.2
    intro i
    simp only [Pi.zero_apply, mulVec, dotProduct]
    have ht := tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinv i) j).mul (tendsto_pi_nhds.1 hr j))
    simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using ht
  apply hm.congr'
  filter_upwards [heq, hc, hdet.eventually_ne hd] with n hn hn3 hne
  have hres : Q n *ᵥ e n = r n := by
    funext i
    have h := congrFun hn i.castSucc
    simp only [Q, r, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.submatrix_apply, Fin.castSucc_zero,
      Fin.castSucc_one] at h ⊢
    rw [← hn3]
    linear_combination (n : ℝ) * h
  change (Q n).det ≠ 0 at hne
  change (Q n)⁻¹ *ᵥ r n = e n
  rw [← hres, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne), one_mulVec]


private theorem scaled_mesh_sq {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ) * h n)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2 * ((n : ℝ)⁻¹)^2)
      atTop (𝓝 0) := by simpa using hK.mul (hi.pow 2)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  field_simp [hn0]
  <;> ring

private theorem scaled_frontGram_error {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (i j : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (frontGram n ((n : ℝ)*h n) i j - frontGram n 0 i j)) atTop (𝓝 0) := by
  have hu := scaled_mesh_sq hK
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto (fun n : ℕ => 2 * ((n : ℝ) * ((n : ℝ)*h n)^2))
      atTop (𝓝 0) by simpa using hu.const_mul (2 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ (n : ℝ) * (2 * ((n : ℝ)*h n)^2) :=
      mul_le_mul_of_nonneg_left (frontGram_sub_le n hnpos _ i j) (Nat.cast_nonneg n)
    _ = _ := by ring


private def rearScaledTop (n h r : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  let w := rearWeight h r
  let f := 1 - w
  let x := rearMoment h r
  !![f^2, f*x/n^2, f*w/n^2; x*f/n^2, x^2/n^4, x*w/n^4]

private theorem rear_scaled_top_tendsto {h : ℕ → ℝ}
    (hh : Tendsto h atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n : ℕ => rearScaledTop n (h n) r) atTop (𝓝 0) := by
  let w := fun n => rearWeight (h n) r
  let f := fun n => 1 - w n
  let x := fun n => rearMoment (h n) r
  obtain ⟨hw, hx⟩ := rearFeatures_tendsto hh r
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub hw (a := (1 : ℝ))
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · change Tendsto (fun n => f n^2) atTop (𝓝 0)
    simpa using hf.pow 2
  · change Tendsto (fun n : ℕ => f n*x n/(n : ℝ)^2) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero] using (hf.mul hx).mul (hi.pow 2)
  · change Tendsto (fun n : ℕ => f n*w n/(n : ℝ)^2) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero] using (hf.mul hw).mul (hi.pow 2)
  · change Tendsto (fun n : ℕ => x n*f n/(n : ℝ)^2) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero] using (hx.mul hf).mul (hi.pow 2)
  · change Tendsto (fun n : ℕ => x n^2/(n : ℝ)^4) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero, zero_pow (by decide : 4 ≠ 0)] using (hx.pow 2).mul (hi.pow 4)
  · change Tendsto (fun n : ℕ => x n*w n/(n : ℝ)^4) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero, zero_pow (by decide : 4 ≠ 0)] using (hx.mul hw).mul (hi.pow 4)

private def frontUpper (n : ℕ) (u : ℝ) (i : Fin 2) : ℝ :=
  (∑ j ∈ latticeInterval n, frontFeatures u ((j : ℝ)/n) i *
    ((1 - Real.cos (((j : ℝ)/n)*u))/2)) / (n : ℝ)^3

private theorem scaled_front_upper {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (i : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ) * frontUpper n (u n) i) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  refine squeeze_zero' ?_ ?_ (show Tendsto (fun n : ℕ => (3/4 : ℝ)*(u n)^2*(n : ℝ)⁻¹)
      atTop (𝓝 0) by simpa only [mul_zero] using ((hu.pow 2).const_mul (3/4 : ℝ)).mul hi)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    unfold frontUpper
    apply mul_nonneg hnr.le
    apply div_nonneg _ (by positivity)
    apply sum_nonneg
    intro j hj
    obtain ⟨hw,hf⟩ := front_site_bounds n (show 0 < n from hn) (u n) hj i
    exact mul_nonneg hf.1 hw.1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hb : frontUpper n (u n) i ≤ 3*(u n)^2/(4*(n : ℝ)^2) :=
      (front_mixed_block n (show 0 < n from hn) (u n) i).1
    calc
      _ ≤ (n : ℝ)*(3*(u n)^2/(4*(n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hb hnr.le
      _ = _ := by field_simp [hnr.ne']

private def referenceTop (n : ℕ) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun i j => Fin.lastCases 0 (fun j => frontGram n 0 i j) j

private def frontScaledTop (n : ℕ) (u : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun i j => Fin.lastCases ((n : ℝ) * frontUpper n u i)
    (fun j => (n : ℝ) * (frontGram n u i j - frontGram n 0 i j)) j

private theorem scaled_top_matrix {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) •
      ((coupledMomentMatrix S n (h n)).submatrix Fin.castSucc id - referenceTop n))
      atTop (𝓝 0) := by
  obtain ⟨hh, hu, _⟩ := critical_mesh_limits hK
  have hf : Tendsto (fun n : ℕ => frontScaledTop n ((n : ℝ)*h n)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change Tendsto (fun n : ℕ => (n : ℝ) * frontUpper n ((n : ℝ)*h n) i) atTop (𝓝 0)
      exact scaled_front_upper hu i
    · simpa only [frontScaledTop, Fin.lastCases_castSucc, Matrix.zero_apply] using scaled_frontGram_error hK i k
  have hr : Tendsto (fun n : ℕ => ∑ r ∈ S, rearScaledTop n (h n) r) atTop (𝓝 0) := by
    simpa only [sum_const_zero] using
      tendsto_finsetSum S (fun r _ => rear_scaled_top_tendsto hh r)
  apply (show Tendsto (fun n => frontScaledTop n ((n : ℝ)*h n) +
      ∑ r ∈ S, rearScaledTop n (h n) r) atTop (𝓝 0) by simpa using hf.add hr).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.submatrix_apply, id_eq, smul_eq_mul, coupledMomentMatrix]
  rw [mul_sub, mul_add, Finset.mul_sum, add_sub_right_comm]
  congr 1
  · fin_cases i <;> fin_cases j
    · change (n : ℝ) * (frontGram n ((n : ℝ)*h n) 0 0 - frontGram n 0 0 0) =
        (n : ℝ) * frontGram n ((n : ℝ)*h n) 0 0 - (n : ℝ) * frontGram n 0 0 0
      ring
    · change (n : ℝ) * (frontGram n ((n : ℝ)*h n) 0 1 - frontGram n 0 0 1) =
        (n : ℝ) * frontGram n ((n : ℝ)*h n) 0 1 - (n : ℝ) * frontGram n 0 0 1
      ring
    · change (n : ℝ) * frontUpper n ((n : ℝ)*h n) 0 =
        (n : ℝ) * frontUpper n ((n : ℝ)*h n) 0 - (n : ℝ) * 0
      ring
    · change (n : ℝ) * (frontGram n ((n : ℝ)*h n) 1 0 - frontGram n 0 1 0) =
        (n : ℝ) * frontGram n ((n : ℝ)*h n) 1 0 - (n : ℝ) * frontGram n 0 1 0
      ring
    · change (n : ℝ) * (frontGram n ((n : ℝ)*h n) 1 1 - frontGram n 0 1 1) =
        (n : ℝ) * frontGram n ((n : ℝ)*h n) 1 1 - (n : ℝ) * frontGram n 0 1 1
      ring
    · change (n : ℝ) * frontUpper n ((n : ℝ)*h n) 1 =
        (n : ℝ) * frontUpper n ((n : ℝ)*h n) 1 - (n : ℝ) * 0
      ring
  · apply sum_congr rfl
    intro r _
    let w := rearWeight (h n) r
    let f := 1 - w
    let x := rearMoment (h n) r
    fin_cases i <;> fin_cases j
    · change f^2 = (n : ℝ) * (f^2/n)
      field_simp [hn0]
    · change f*x/(n : ℝ)^2 = (n : ℝ) * (f*x/n^3)
      field_simp [hn0]
    · change f*w/(n : ℝ)^2 = (n : ℝ) * (f*w/n^3)
      field_simp [hn0]
    · change x*f/(n : ℝ)^2 = (n : ℝ) * (x*f/n^3)
      field_simp [hn0]
    · change x^2/(n : ℝ)^4 = (n : ℝ) * (x^2/n^5)
      field_simp [hn0]
    · change x*w/(n : ℝ)^4 = (n : ℝ) * (x*w/n^5)
      field_simp [hn0]


def radiusSq (n : ℕ) : ℝ := (n : ℝ) * (n + 1) - 1/2
def latticeCoeffs (n : ℕ) : Fin 2 → ℝ :=
  ![(n : ℝ)*radiusSq n / normalizer n (radiusSq n),
    -(n : ℝ)^3 / normalizer n (radiusSq n)]

private theorem normalized_Z :
    Tendsto (fun n : ℕ => normalizer n (radiusSq n)/(n : ℝ)^3) atTop (𝓝 (4/3)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hp := tendsto_const_nhds.add hi (a := (2 : ℝ))
  have hq := (((tendsto_const_nhds.add hi (a := (1 : ℝ))).const_mul (2/3 : ℝ)).sub
    ((hi.pow 2).const_mul (1/2 : ℝ)))
  have ht : Tendsto (fun n : ℕ => (2+(n : ℝ)⁻¹) *
      (2/3*(1+(n : ℝ)⁻¹) - (1/2)*(n : ℝ)⁻¹^2)) atTop (𝓝 (4/3 : ℝ)) := by
    convert hp.mul hq using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  rw [normalizer_formula]
  unfold radiusSq
  field_simp [hn0]
  <;> ring

private theorem lattice_coeff_tendsto :
    Tendsto latticeCoeffs atTop (𝓝 ![(3/4 : ℝ), -3/4]) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have htop : Tendsto (fun n : ℕ => radiusSq n/(n : ℝ)^2) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1+(n : ℝ)⁻¹-(1/2)*(n : ℝ)⁻¹^2)
        atTop (𝓝 1) := by simpa using
      (tendsto_const_nhds.add hi (a := (1 : ℝ))).sub ((hi.pow 2).const_mul (1/2 : ℝ))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    unfold radiusSq
    field_simp [hn0]
    <;> ring
  have hden := normalized_Z
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · have ht := htop.div hden (by norm_num : (4/3 : ℝ) ≠ 0)
    have hlim : (1 : ℝ)/(4/3) = 3/4 := by norm_num
    rw [hlim] at ht
    change Tendsto (fun n : ℕ => (n : ℝ)*radiusSq n / normalizer n (radiusSq n)) atTop (𝓝 (3/4))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    have hz : (0 : ℝ) < normalizer n (radiusSq n) := by
      apply normalizer_pos n (show 0 < n from hn)
      unfold radiusSq
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    change (radiusSq n / (n : ℝ)^2) / (normalizer n (radiusSq n)/(n : ℝ)^3) = (n : ℝ)*radiusSq n / normalizer n (radiusSq n)
    field_simp [hn0,hz.ne']
    <;> ring
  · have ht := (tendsto_const_nhds (x := (-1 : ℝ))).div hden
      (by norm_num : (4/3 : ℝ) ≠ 0)
    have hlim : (-1 : ℝ)/(4/3) = -3/4 := by norm_num
    rw [hlim] at ht
    change Tendsto (fun n : ℕ => -(n : ℝ)^3 / normalizer n (radiusSq n)) atTop (𝓝 (-3/4))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    have hz : (0 : ℝ) < normalizer n (radiusSq n) := by
      apply normalizer_pos n (show 0 < n from hn)
      unfold radiusSq
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    change (-1 : ℝ) / (normalizer n (radiusSq n)/(n : ℝ)^3) = -(n : ℝ)^3 / normalizer n (radiusSq n)
    field_simp [hn0,hz.ne']
    <;> ring


private theorem lattice_reference_exact (n : ℕ) (hn : 0 < n) (i : Fin 2) :
    (frontGram n 0 *ᵥ latticeCoeffs n) i =
      (![1, budget n/(n : ℝ)^2] : Fin 2 → ℝ) i := by
  have hb := frontGram_reference_residual_le n hn 0 i
  change |(frontGram n 0 *ᵥ latticeCoeffs n) i -
    (![1, budget n/(n : ℝ)^2] : Fin 2 → ℝ) i| ≤
    2 * (0 : ℝ)^2 * (|latticeCoeffs n 0| + |latticeCoeffs n 1|) at hb
  have hz : |(frontGram n 0 *ᵥ latticeCoeffs n) i -
    (![1, budget n/(n : ℝ)^2] : Fin 2 → ℝ) i| = 0 := by
    apply le_antisymm _ (abs_nonneg _)
    simpa using hb
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

private theorem scaled_mass_error {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => (n : ℝ)*budget n*(h n)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hb : Tendsto (fun n : ℕ => (1+(n : ℝ)⁻¹)/5) atTop (𝓝 (1/5 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hi (a := (1 : ℝ))).div_const 5
  have ht : Tendsto (fun n : ℕ => ((1+(n : ℝ)⁻¹)/5) * ((n : ℝ)*((n : ℝ)*h n)^2))
      atTop (𝓝 0) := by simpa only [mul_zero] using hb.mul (scaled_mesh_sq hK)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  dsimp [budget]
  field_simp [hn0]
  <;> ring

theorem refined_coefficients {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    Tendsto (fun n : ℕ => fun i : Fin 2 => (n : ℝ) *
      (readout ((S,n),h n) i.castSucc - latticeCoeffs n i)) atTop (𝓝 0) := by
  let a := fun n => coefficientFit S n (h n)
  change Tendsto (fun n : ℕ => fun i : Fin 2 => (n : ℝ) *
      (a n i.castSucc - latticeCoeffs n i)) atTop (𝓝 0)
  obtain ⟨_,_,hscale⟩ := critical_mesh_limits hK
  let M := fun n => coupledMomentMatrix S n (h n)
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 2/3; 2/3, 2/5]
  let L : Matrix (Fin 3) (Fin 3) ℝ := !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0;
      0, ∑ r ∈ S, r^2, (S.card : ℝ)]
  have hM : Tendsto M atTop (𝓝 L) := coupledMatrix_tendsto hscale S
  have heq : ∀ᶠ n in atTop, M n *ᵥ a n = target n (h n) := by
    filter_upwards [coupledMatrix_eventually_det_ne_zero hscale hS] with n hn
    change (M n).det ≠ 0 at hn
    change M n *ᵥ ((M n)⁻¹ *ᵥ target n (h n)) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn), one_mulVec]
  have hP : Tendsto (fun n => (M n).submatrix Fin.castSucc Fin.castSucc) atTop (𝓝 P) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    have ht := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hM i.castSucc) j.castSucc
    fin_cases i <;> fin_cases j <;> exact ht
  have hdP : P.det ≠ 0 := by
    dsimp [P]
    rw [Matrix.det_fin_two]
    norm_num
  let c := fun n => ![latticeCoeffs n 0, latticeCoeffs n 1, a n 2]
  have hc : ∀ᶠ n in atTop, a n 2 = c n 2 := Eventually.of_forall fun _ => rfl
  have hcLim : Tendsto c atTop
      (𝓝 ![(3/4 : ℝ), -3/4, limitCoefficients S K 2]) := by
    have ha := coefficient_tendsto hK S hS
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact tendsto_pi_nhds.1 lattice_coeff_tendsto 0
    · exact tendsto_pi_nhds.1 lattice_coeff_tendsto 1
    · exact tendsto_pi_nhds.1 ha 2
  have hR := scaled_top_matrix hK S
  have hmul : Tendsto (fun n : ℕ => ((n : ℝ) •
        ((M n).submatrix Fin.castSucc id - referenceTop n)) *ᵥ c n) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.2
    intro i
    simp only [Matrix.zero_apply, Pi.zero_apply, mulVec, dotProduct]
    have ht := tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hR i) j).mul (tendsto_pi_nhds.1 hcLim j))
    simpa only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero] using ht
  have htarget : Tendsto (fun n : ℕ => ![-((n : ℝ)*budget n*(h n)^2), (0 : ℝ)]) atTop (𝓝 (0 : Fin 2 → ℝ)) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · change Tendsto (fun n : ℕ => -((n : ℝ)*budget n*(h n)^2)) atTop (𝓝 0)
      simpa only [neg_zero] using (scaled_mass_error hK).neg
    · exact tendsto_const_nhds
  have hr : Tendsto (fun n : ℕ => fun i : Fin 2 => (n : ℝ) *
      (target n (h n) i.castSucc - (M n *ᵥ c n) i.castSucc)) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ => ![-((n : ℝ)*budget n*(h n)^2), (0 : ℝ)] -
        (((n : ℝ) • ((M n).submatrix Fin.castSucc id - referenceTop n)) *ᵥ c n))
        atTop (𝓝 0) by simpa only [sub_zero] using htarget.sub hmul).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have href (i : Fin 2) : (referenceTop n *ᵥ c n) i =
        (![1, budget n/(n : ℝ)^2] : Fin 2 → ℝ) i := by
      have hh := lattice_reference_exact n (show 0 < n from hn) i
      simp only [mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] at hh ⊢
      change frontGram n 0 i 0 * latticeCoeffs n 0 + frontGram n 0 i 1 * latticeCoeffs n 1 +
        0 * a n 2 = _
      simpa only [zero_mul, add_zero] using hh
    funext i
    have hread := congrFun (show (M n).submatrix Fin.castSucc id *ᵥ c n =
        fun i : Fin 2 => (M n *ᵥ c n) i.castSucc from by
      ext i
      rfl) i
    rw [Pi.sub_apply, smul_mulVec, sub_mulVec, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      hread, href]
    fin_cases i <;> simp [target, budget] <;> ring
  have hh := two_row_scaled_error hP hdP heq hc hr
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    funext i
    fin_cases i <;> rfl


private theorem edge_ratio_tendsto (k : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ)+k)/(n : ℝ)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have ht : Tendsto (fun n : ℕ => 1+k*(n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hi.const_mul k) (a := (1 : ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  field_simp [hn0]

private theorem reference_boundary_tendsto (k : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (latticeCoeffs n 0 + latticeCoeffs n 1 * (((n : ℝ)+k)/(n : ℝ))^2))
      atTop (𝓝 ((3/4)*(1-2*k))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have ha : Tendsto (fun n : ℕ => (n : ℝ)^3 / normalizer n (radiusSq n))
      atTop (𝓝 (3/4)) := by
    have ht := (tendsto_pi_nhds.1 lattice_coeff_tendsto (1 : Fin 2)).neg
    change Tendsto (fun n : ℕ => - (-(n : ℝ)^3 / normalizer n (radiusSq n)))
      atTop (𝓝 (-(-3/4))) at ht
    simpa only [neg_div, neg_neg] using ht
  have hb : Tendsto (fun n : ℕ => (1-2*k) - (k^2+1/2)*(n : ℝ)⁻¹)
      atTop (𝓝 (1-2*k)) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (k^2+1/2)) (a := 1-2*k)
  apply (ha.mul hb).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  have hz : (0 : ℝ) < normalizer n (radiusSq n) := by
    apply normalizer_pos n (show 0 < n from hn)
    unfold radiusSq
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  change (n : ℝ)^3 / normalizer n (radiusSq n) * ((1-2*k)-(k^2+1/2)*(n : ℝ)⁻¹) = _
  simp only [latticeCoeffs, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold radiusSq
  field_simp [hn0,hz.ne']
  <;> ring

private theorem edge_feature_error {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (k : ℝ) (i : Fin 2) :
    let x := fun n : ℕ => ((n : ℝ)+k)/(n : ℝ)
    let u := fun n : ℕ => (n : ℝ)*h n
    Tendsto (fun n : ℕ => (n : ℝ) * (frontFeatures (u n) (x n) i -
      latticeFeatures (x n) i)) atTop (𝓝 0) := by
  intro x u
  have hx : Tendsto x atTop (𝓝 1) := edge_ratio_tendsto k
  have hu := scaled_mesh_sq hK
  have hxBound : ∀ᶠ n in atTop, |x n| < 2 := by
    have ht := hx.abs
    simpa using ht.eventually (gt_mem_nhds (by norm_num : |(1 : ℝ)| < 2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto (fun n : ℕ => 6*((n : ℝ)*u n^2)) atTop (𝓝 0) by
      simpa only [mul_zero] using hu.const_mul (6 : ℝ))
  filter_upwards [hxBound] with n hn
  have hx2 : x n^2 ≤ 4 := by
    have he := (sq_le_sq₀ (abs_nonneg (x n)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hn.le
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using he
  have hx4 : x n^4 ≤ 16 := by
    nlinarith only [sq_nonneg (x n), sq_nonneg (x n^2), mul_nonneg (sq_nonneg (x n))
      (sub_nonneg.mpr hx2), hx2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ (n : ℝ) * (6*u n^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      fin_cases i
      · change |(1 + Real.cos (x n*u n))/2 - 1| ≤ _
        rw [abs_of_nonpos (by linarith [Real.cos_le_one (x n*u n)])]
        have hh := Real.one_sub_sq_div_two_le_cos (x := x n*u n)
        nlinarith only [hh, sq_nonneg (u n), mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg (u n))]
      · by_cases hz : u n = 0
        · simp [frontFeatures, latticeFeatures, hz]
        · simp only [frontFeatures, latticeFeatures, Matrix.cons_val_one, Matrix.cons_val_zero,
            if_neg hz]
          refine (scaled_sin_sq_error (x n) (u n) hz).trans ?_
          nlinarith only [mul_nonneg (sub_nonneg.mpr hx4) (sq_nonneg (u n)), sq_nonneg (u n)]
    _ = _ := by ring


theorem scaled_boundary_value {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) (offset : ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      boundaryValue state.1.1.1 state.1.1.2 state.1.2 state.2
    Tendsto (fun n : ℕ => (n : ℝ)^2 * readout (((S,n),h n),offset)) atTop
      (𝓝 ((3/4)*(1-2*offset))) := by
  let a := fun n => coefficientFit S n (h n)
  let x := fun n : ℕ => ((n : ℝ)+offset)/(n : ℝ)
  let u := fun n : ℕ => (n : ℝ)*h n
  let F := fun n => frontFeatures (u n) (x n) 0
  let X := fun n => frontFeatures (u n) (x n) 1
  change Tendsto (fun n : ℕ => (n : ℝ)^2 * (coefficientRow n (F n) (X n) (1-F n) ⬝ᵥ a n))
    atTop (𝓝 ((3/4)*(1-2*offset)))
  have ha := coefficient_tendsto hK S hS
  have hA : Tendsto (fun n => a n 0) atTop (𝓝 (3/4)) :=
    tendsto_pi_nhds.1 ha 0
  have hC : Tendsto (fun n => a n 1) atTop (𝓝 (-3/4)) :=
    tendsto_pi_nhds.1 ha 1
  have hB : Tendsto (fun n => a n 2) atTop (𝓝 (limitCoefficients S K 2)) :=
    tendsto_pi_nhds.1 ha 2
  have he := refined_coefficients hK S hS
  have hAerr : Tendsto (fun n : ℕ => (n : ℝ)*(a n 0-latticeCoeffs n 0)) atTop (𝓝 0) :=
    tendsto_pi_nhds.1 he 0
  have hCerr : Tendsto (fun n : ℕ => (n : ℝ)*(a n 1-latticeCoeffs n 1)) atTop (𝓝 0) :=
    tendsto_pi_nhds.1 he 1
  have hx : Tendsto x atTop (𝓝 1) := edge_ratio_tendsto offset
  obtain ⟨_, hu, _⟩ := critical_mesh_limits hK
  have hf : Tendsto F atTop (𝓝 1) := by
    have ht := hx.mul hu
    rw [mul_zero] at ht
    have hcos := Real.continuous_cos.continuousAt.tendsto.comp ht
    change Tendsto (fun n => Real.cos (x n*u n)) atTop (𝓝 (Real.cos 0)) at hcos
    rw [Real.cos_zero] at hcos
    simpa [F, frontFeatures] using (tendsto_const_nhds.add hcos (a := (1 : ℝ))).div_const 2
  have hferr : Tendsto (fun n : ℕ => (n : ℝ)*(F n-1)) atTop (𝓝 0) :=
    edge_feature_error hK offset 0
  have hxerr : Tendsto (fun n : ℕ => (n : ℝ)*(X n-x n^2)) atTop (𝓝 0) :=
    edge_feature_error hK offset 1
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hReference := reference_boundary_tendsto offset
  have ht := ((((hReference.add hAerr).add (hCerr.mul (hx.pow 2))).add
    (hA.mul hferr)).add (hC.mul hxerr)).add ((hB.mul (tendsto_const_nhds.sub hf (a := (1 : ℝ)))).mul hi)
  have hout : Tendsto (fun n : ℕ => (n : ℝ)*(latticeCoeffs n 0 +
      latticeCoeffs n 1*x n^2) + (n : ℝ)*(a n 0 - latticeCoeffs n 0)
      + ((n : ℝ)*(a n 1 - latticeCoeffs n 1))*x n^2 +
      a n 0*((n : ℝ)*(F n-1)) + a n 1*((n : ℝ)*(X n-x n^2))
      + a n 2*(1-F n)*(n : ℝ)⁻¹)
      atTop (𝓝 ((3/4)*(1-2*offset))) := by
    simpa only [one_pow, zero_mul, mul_zero, add_zero] using ht
  apply hout.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  simp only [coefficientRow, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change (n : ℝ)*(latticeCoeffs n 0 + latticeCoeffs n 1*x n^2) + (n : ℝ)*(a n 0 - latticeCoeffs n 0) +
    ((n : ℝ)*(a n 1-latticeCoeffs n 1))*x n^2 + a n 0*((n : ℝ)*(F n-1)) +
    a n 1*((n : ℝ)*(X n-x n^2)) + a n 2*(1-F n)*(n : ℝ)⁻¹ =
    (n : ℝ)^2 * (F n / n * a n 0 + X n / n * a n 1 + ((1-F n)/(n : ℝ)^3)*a n 2)
  field_simp [hn0]
  <;> ring


theorem scaled_rear_value {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      rearValue state.1.1.1 state.1.1.2 state.1.2 state.2
    Tendsto (fun n : ℕ => (n : ℝ)^3 * readout (((S,n),h n),r)) atTop
      (𝓝 (limitCoefficients S K 2 - 3*r^2/4)) := by
  let a := fun n => coefficientFit S n (h n)
  let W := fun n => rearWeight (h n) r
  let X := fun n : ℕ => rearMoment (h n) r / (n : ℝ)^2
  change Tendsto (fun n : ℕ => (n : ℝ)^3 * (coefficientRow n (1-W n) (X n) (W n) ⬝ᵥ a n))
    atTop (𝓝 (limitCoefficients S K 2 - 3*r^2/4))
  obtain ⟨hh,hu,_⟩ := critical_mesh_limits hK
  have ha := coefficient_tendsto hK S hS
  have hA : Tendsto (fun n => a n 0) atTop (𝓝 (3/4)) :=
    tendsto_pi_nhds.1 ha 0
  have hC : Tendsto (fun n => a n 1) atTop (𝓝 (-3/4)) :=
    tendsto_pi_nhds.1 ha 1
  have hB : Tendsto (fun n => a n 2) atTop (𝓝 (limitCoefficients S K 2)) :=
    tendsto_pi_nhds.1 ha 2
  obtain ⟨hw,hx⟩ := rearFeatures_tendsto hh r
  have hf : Tendsto (fun n : ℕ => (n : ℝ)^2*(1-W n)) atTop (𝓝 0) :=
    rearDeficit_scaled_tendsto hu r
  have ht := ((hf.mul hA).add (hx.mul hC)).add (hw.mul hB)
  have hlim : (0:ℝ)*(3/4) + r^2*(-3/4) + 1*limitCoefficients S K 2 =
      limitCoefficients S K 2 - 3*r^2/4 := by ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  simp only [coefficientRow, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change (n : ℝ)^2*(1-W n)*a n 0 + rearMoment (h n) r*a n 1 + W n*a n 2 =
    (n : ℝ)^3*((1-W n)/n*a n 0 + X n/n*a n 1 + (W n/(n : ℝ)^3)*a n 2)
  dsimp only [X]
  field_simp [hn0]
  <;> ring


end

end D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
