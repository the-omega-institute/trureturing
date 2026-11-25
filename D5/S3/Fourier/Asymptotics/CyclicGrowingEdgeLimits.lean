/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Critical-scale coefficient and boundary limits for the growing cyclic moment fit. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit

/-! Critical-scale limits and boundary signs for the coupled moment fit. -/

open Filter Finset Matrix Asymptotics
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

theorem critical_bound_mesh_limits {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ))) :
    Tendsto h atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have ht : (fun n : ℕ => ((n : ℝ)^5 * (h n)^2)^2 * ((n : ℝ)⁻¹)^3)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹)^3) := by
    simpa only [← pow_two, one_pow, one_mul] using
      (hB.mul hB).mul (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹)^3) atTop)
  have hscale : Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) := by
    apply (ht.trans_tendsto (by simpa using hi.pow 3)).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    field_simp [hn0]
  obtain ⟨hh,hu⟩ := mesh_limits hscale
  exact ⟨hh,hu,hscale⟩

private theorem critical_mesh_limits {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5 * (h n)^2) atTop (𝓝 K)) :
    Tendsto h atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ)^3 * ((n : ℝ) * h n)^4) atTop (𝓝 0) :=
  critical_bound_mesh_limits (hK.isBigO_one ℝ)

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


private theorem mulVec_bounded {ι κ : Type*} [Fintype κ]
    {M : ℕ → Matrix ι κ ℝ} {v : ℕ → κ → ℝ}
    (hm : ∀ i j, (fun n => M n i j) =O[atTop] (fun _ => (1 : ℝ)))
    (hv : ∀ j, (fun n => v n j) =O[atTop] (fun _ => (1 : ℝ))) (i : ι) :
    (fun n => (M n *ᵥ v n) i) =O[atTop] (fun _ => (1 : ℝ)) := by
  simp only [mulVec, dotProduct]
  have h (j : κ) : (fun n => M n i j * v n j) =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [one_mul] using (hm i j).mul (hv j)
  apply (IsBigO.sum (s := Finset.univ) (fun j _ => h j)).congr_left
  intro n
  rw [Finset.sum_apply]

/-- The first two coefficient errors are controlled by the scaled residual with
the third coefficient held fixed. -/
private theorem two_row_scaled_error {M : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : Tendsto (fun n => (M n).submatrix Fin.castSucc Fin.castSucc) atTop (𝓝 P))
    (hd : P.det ≠ 0) {a b c : ℕ → Fin 3 → ℝ}
    (heq : ∀ᶠ n in atTop, M n *ᵥ a n = b n)
    (hc : ∀ᶠ n in atTop, a n 2 = c n 2)
    (hr : ∀ i : Fin 2, (fun (n : ℕ) => (n : ℝ)^3 *
      (b n i.castSucc - (M n *ᵥ c n) i.castSucc)) =O[atTop] (fun _ => (1 : ℝ))) :
    (fun (n : ℕ) => fun i : Fin 2 => (n : ℝ)^3 *
      (a n i.castSucc - c n i.castSucc)) =O[atTop] (fun _ => (1 : ℝ)) := by
  let Q := fun n => (M n).submatrix (Fin.castSucc : Fin 2 → Fin 3) Fin.castSucc
  let r := fun (n : ℕ) => fun i : Fin 2 => (n : ℝ)^3 *
    (b n i.castSucc - (M n *ᵥ c n) i.castSucc)
  let e := fun (n : ℕ) => fun i : Fin 2 => (n : ℝ)^3 * (a n i.castSucc - c n i.castSucc)
  have hdet := (continuous_id.matrix_det.continuousAt (x := P)).tendsto.comp hP
  have hinv : Tendsto (fun n => (Q n)⁻¹) atTop (𝓝 P⁻¹) := by
    apply (continuousAt_matrix_inv P ?_).tendsto.comp hP
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd
  have hm : (fun n => (Q n)⁻¹ *ᵥ r n) =O[atTop] (fun _ => (1 : ℝ)) := by
    apply isBigO_pi.mpr
    intro i
    apply mulVec_bounded (M := fun n => (Q n)⁻¹) (v := r) _ hr i
    intro j k
    exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinv j) k).isBigO_one ℝ
  apply hm.congr' ?_ EventuallyEq.rfl
  filter_upwards [heq, hc, hdet.eventually_ne hd] with n hn hn3 hne
  have hres : Q n *ᵥ e n = r n := by
    funext i
    have h := congrFun hn i.castSucc
    simp only [Q, r, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.submatrix_apply, Fin.castSucc_zero,
      Fin.castSucc_one] at h ⊢
    rw [← hn3]
    linear_combination (n : ℝ)^3 * h
  change (Q n).det ≠ 0 at hne
  change (Q n)⁻¹ *ᵥ r n = e n
  rw [← hres, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne), one_mulVec]


private theorem scaled_mesh_sq {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (p : ℕ) (hp : p < 3) :
    Tendsto (fun n : ℕ => (n : ℝ)^p * ((n : ℝ) * h n)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)^(3-p)) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : 3-p ≠ 0)] using hi.pow (3-p)
  have ht : (fun n : ℕ => (n : ℝ)^5 * (h n)^2 * ((n : ℝ)⁻¹)^(3-p))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹)^(3-p)) := by
    simpa only [one_mul] using hB.mul (isBigO_refl
      (fun n : ℕ => ((n : ℝ)⁻¹)^(3-p)) atTop)
  apply (ht.trans_tendsto hpow).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  interval_cases p <;> norm_num at * <;> field_simp [hn0] <;> ring

private theorem scaled_frontGram_bound {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (i j : Fin 2) :
    (fun n : ℕ => (n : ℝ)^3 *
      (frontGram n ((n : ℝ)*h n) i j - frontGram n 0 i j))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C,hC⟩ := hB.isBigOWith
  apply IsBigO.of_bound (2*C)
  filter_upwards [eventually_ge_atTop (1 : ℕ),hC.bound] with n hn hb
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)^3),
    norm_one, mul_one]
  have hs : 0 < n := hn
  calc
    _ ≤ (n : ℝ)^3*(2*((n : ℝ)*h n)^2) :=
      mul_le_mul_of_nonneg_left (frontGram_sub_le n hs _ i j) (by positivity)
    _ = 2*((n : ℝ)^5*(h n)^2) := by ring
    _ ≤ 2*C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one, mul_one] at hb
      linarith

private def rearScaledTop (n h r : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  let w := rearWeight h r
  let f := 1 - w
  let x := rearMoment h r
  !![n^2*f^2, f*x, f*w; x*f, x^2/n^2, x*w/n^2]

private theorem rear_scaled_top_tendsto {h : ℕ → ℝ}
    (hh : Tendsto h atTop (𝓝 0))
    (hu : Tendsto (fun n : ℕ => (n : ℝ)*h n) atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n : ℕ => rearScaledTop n (h n) r) atTop (𝓝 0) := by
  let w := fun n => rearWeight (h n) r
  let f := fun n => 1 - w n
  let x := fun n => rearMoment (h n) r
  obtain ⟨hw, hx⟩ := rearFeatures_tendsto hh r
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub hw (a := (1 : ℝ))
  have hnf : Tendsto (fun n : ℕ => (n : ℝ)^2 * f n) atTop (𝓝 0) :=
    rearDeficit_scaled_tendsto hu r
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · change Tendsto (fun n : ℕ => (n : ℝ)^2*f n^2) atTop (𝓝 0)
    apply (show Tendsto (fun n : ℕ => ((n : ℝ)^2*f n)*f n) atTop (𝓝 0)
      by simpa only [zero_mul] using hnf.mul hf).congr; intro n; ring
  · change Tendsto (fun n => f n*x n) atTop (𝓝 0)
    simpa only [zero_mul] using hf.mul hx
  · change Tendsto (fun n => f n*w n) atTop (𝓝 0)
    simpa only [zero_mul] using hf.mul hw
  · change Tendsto (fun n => x n*f n) atTop (𝓝 0)
    simpa only [mul_zero] using hx.mul hf
  · change Tendsto (fun n : ℕ => x n^2/(n : ℝ)^2) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      using (hx.pow 2).mul (hi.pow 2)
  · change Tendsto (fun n : ℕ => x n*w n/(n : ℝ)^2) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)]
      using (hx.mul hw).mul (hi.pow 2)

private def frontUpper (n : ℕ) (u : ℝ) (i : Fin 2) : ℝ :=
  (∑ j ∈ latticeInterval n, frontFeatures u ((j : ℝ)/n) i *
    ((1 - Real.cos (((j : ℝ)/n)*u))/2)) / (n : ℝ)^3

private theorem scaled_front_upper {u : ℕ → ℝ} (hu : Tendsto (fun n : ℕ => (n : ℝ)*(u n)^2) atTop (𝓝 0)) (i : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ)^3 * frontUpper n (u n) i) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (show Tendsto (fun n : ℕ => (3/4 : ℝ)*((n : ℝ)*(u n)^2))
      atTop (𝓝 0) by simpa only [mul_zero] using hu.const_mul (3/4 : ℝ))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    unfold frontUpper
    apply mul_nonneg (by positivity)
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
      _ ≤ (n : ℝ)^3*(3*(u n)^2/(4*(n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp [hnr.ne']

private def referenceTop (n : ℕ) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun i j => Fin.lastCases 0 (fun j => frontGram n 0 i j) j

private def frontScaledTop (n : ℕ) (u : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun i j => Fin.lastCases ((n : ℝ)^3 * frontUpper n u i)
    (fun j => (n : ℝ)^3 * (frontGram n u i j - frontGram n 0 i j)) j

private theorem scaled_top_matrix {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (i : Fin 2) (j : Fin 3) :
    (fun n : ℕ => ((n : ℝ)^3 •
      ((coupledMomentMatrix S n (h n)).submatrix Fin.castSucc id - referenceTop n)) i j)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨hh, hu, _⟩ := critical_bound_mesh_limits hB
  have hsmall : Tendsto (fun n : ℕ => (n : ℝ)*((n : ℝ)*h n)^2) atTop (𝓝 0) := by
    simpa only [pow_one] using scaled_mesh_sq hB 1 (by decide)
  have hf : (fun n : ℕ => frontScaledTop n ((n : ℝ)*h n) i j)
      =O[atTop] (fun _ => (1 : ℝ)) := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change (fun n : ℕ => (n : ℝ)^3*frontUpper n ((n : ℝ)*h n) i)
        =O[atTop] (fun _ => (1 : ℝ))
      exact (scaled_front_upper hsmall i).isBigO_one ℝ
    · simpa only [frontScaledTop, Fin.lastCases_castSucc] using scaled_frontGram_bound hB i k
  have hr : Tendsto (fun n : ℕ => ∑ r ∈ S, rearScaledTop n (h n) r) atTop (𝓝 0) := by
    simpa only [sum_const_zero] using
      tendsto_finsetSum S (fun r _ => rear_scaled_top_tendsto hh hu r)
  have hr' : (fun n : ℕ => (∑ r ∈ S, rearScaledTop n (h n) r) i j)
      =O[atTop] (fun _ => (1 : ℝ)) :=
    (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hr i) j).isBigO_one ℝ
  have he : ∀ᶠ n : ℕ in atTop, frontScaledTop n ((n : ℝ)*h n) +
      (∑ r ∈ S, rearScaledTop n (h n) r) =
      (n : ℝ)^3 • ((coupledMomentMatrix S n (h n)).submatrix Fin.castSucc id - referenceTop n) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    ext i j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.submatrix_apply, id_eq, smul_eq_mul, coupledMomentMatrix]
    rw [mul_sub, mul_add, Finset.mul_sum, add_sub_right_comm]
    congr 1
    · fin_cases i <;> fin_cases j
      · change (n : ℝ)^3 * (frontGram n ((n : ℝ)*h n) 0 0 - frontGram n 0 0 0) =
          (n : ℝ)^3 * frontGram n ((n : ℝ)*h n) 0 0 - (n : ℝ)^3 * frontGram n 0 0 0
        ring
      · change (n : ℝ)^3 * (frontGram n ((n : ℝ)*h n) 0 1 - frontGram n 0 0 1) =
          (n : ℝ)^3 * frontGram n ((n : ℝ)*h n) 0 1 - (n : ℝ)^3 * frontGram n 0 0 1
        ring
      · change (n : ℝ)^3 * frontUpper n ((n : ℝ)*h n) 0 =
          (n : ℝ)^3 * frontUpper n ((n : ℝ)*h n) 0 - (n : ℝ)^3 * 0
        ring
      · change (n : ℝ)^3 * (frontGram n ((n : ℝ)*h n) 1 0 - frontGram n 0 1 0) =
          (n : ℝ)^3 * frontGram n ((n : ℝ)*h n) 1 0 - (n : ℝ)^3 * frontGram n 0 1 0
        ring
      · change (n : ℝ)^3 * (frontGram n ((n : ℝ)*h n) 1 1 - frontGram n 0 1 1) =
          (n : ℝ)^3 * frontGram n ((n : ℝ)*h n) 1 1 - (n : ℝ)^3 * frontGram n 0 1 1
        ring
      · change (n : ℝ)^3 * frontUpper n ((n : ℝ)*h n) 1 =
          (n : ℝ)^3 * frontUpper n ((n : ℝ)*h n) 1 - (n : ℝ)^3 * 0
        ring
    · apply sum_congr rfl
      intro r _
      let w := rearWeight (h n) r
      let f := 1 - w
      let x := rearMoment (h n) r
      fin_cases i <;> fin_cases j
      · change (n : ℝ)^2*f^2 = (n : ℝ)^3 * (f^2/n)
        field_simp [hn0]
      · change f*x = (n : ℝ)^3 * (f*x/n^3)
        field_simp [hn0]
      · change f*w = (n : ℝ)^3 * (f*w/n^3)
        field_simp [hn0]
      · change x*f = (n : ℝ)^3 * (x*f/n^3)
        field_simp [hn0]
      · change x^2/(n : ℝ)^2 = (n : ℝ)^3 * (x^2/n^5)
        field_simp [hn0]
      · change x*w/(n : ℝ)^2 = (n : ℝ)^3 * (x*w/n^5)
        field_simp [hn0]


  apply (hf.add hr').congr' ?_ EventuallyEq.rfl
  filter_upwards [he] with n hn
  exact congrFun (congrFun hn i) j

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

private theorem budget_ratio_tendsto :
    Tendsto (fun n : ℕ => budget n/(n : ℝ)^2) atTop (𝓝 (1/5)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hb : Tendsto (fun n : ℕ => (1+(n : ℝ)⁻¹)/5) atTop (𝓝 (1/5 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hi (a := (1 : ℝ))).div_const 5
  apply hb.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  dsimp [budget]
  field_simp [hn0]
  <;> ring

private theorem scaled_mass_bound {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ))) :
    (fun n : ℕ => (n : ℝ)^3*budget n*(h n)^2) =O[atTop] (fun _ => (1 : ℝ)) := by
  have ht : (fun n : ℕ => (budget n/(n : ℝ)^2) * ((n : ℝ)^5 * (h n)^2))
      =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [one_mul] using (budget_ratio_tendsto.isBigO_one ℝ).mul hB
  apply ht.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  field_simp [hn0]
  <;> ring

private theorem target_bounded {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (i : Fin 3) :
    (fun n => target n (h n) i) =O[atTop] (fun _ => (1 : ℝ)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hmass : (fun n : ℕ => budget n*(h n)^2) =O[atTop] (fun _ => (1 : ℝ)) := by
    have hh : (fun n : ℕ => ((n : ℝ)^3*budget n*(h n)^2)*((n : ℝ)⁻¹)^3)
        =O[atTop] (fun _ => (1 : ℝ)) := by
      simpa only [one_mul] using (scaled_mass_bound hB).mul ((hi.pow 3).isBigO_one ℝ)
    apply hh.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    field_simp [hn0]
  fin_cases i
  · change (fun n => 1-budget n*(h n)^2) =O[atTop] (fun _ => (1 : ℝ))
    exact (isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop).sub hmass
  · exact budget_ratio_tendsto.isBigO_one ℝ
  · change (fun n : ℕ => 3*(n : ℝ)^3*budget n*(h n)^2/4)
      =O[atTop] (fun _ => (1 : ℝ))
    apply ((scaled_mass_bound hB).const_mul_left (3/4 : ℝ)).congr_left
    intro n
    ring

private theorem coefficientFit_bounded {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) (i : Fin 3) :
    (fun n => coefficientFit S n (h n) i) =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨_,_,hscale⟩ := critical_bound_mesh_limits hB
  let L : Matrix (Fin 3) (Fin 3) ℝ := !![(2 : ℝ), 2/3, 0; 2/3, 2/5, 0;
    0, ∑ r ∈ S, r^2, (S.card : ℝ)]
  have hM : Tendsto (fun n => coupledMomentMatrix S n (h n)) atTop (𝓝 L) :=
    coupledMatrix_tendsto hscale S
  have hd : L.det ≠ 0 := by
    have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    rw [show L.det = 16 * (S.card : ℝ)/45 from coupledLimit_det S]
    positivity
  have hinv : Tendsto (fun n => (coupledMomentMatrix S n (h n))⁻¹) atTop (𝓝 L⁻¹) := by
    apply (continuousAt_matrix_inv L ?_).tendsto.comp hM
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd
  apply mulVec_bounded (v := fun n => target n (h n)) _ (target_bounded hB) i
  intro j k
  exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinv j) k).isBigO_one ℝ

theorem refined_coefficients {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    (fun n : ℕ => fun i : Fin 2 => (n : ℝ)^3 *
      (readout ((S,n),h n) i.castSucc - latticeCoeffs n i)) =O[atTop] (fun _ => (1 : ℝ)) := by
  let a := fun n => coefficientFit S n (h n)
  change (fun n : ℕ => fun i : Fin 2 => (n : ℝ)^3 *
      (a n i.castSucc - latticeCoeffs n i)) =O[atTop] (fun _ => (1 : ℝ))
  obtain ⟨_,_,hscale⟩ := critical_bound_mesh_limits hB
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
  have hcBound (i : Fin 3) : (fun n => c n i) =O[atTop] (fun _ => (1 : ℝ)) := by
    fin_cases i
    · exact (tendsto_pi_nhds.1 lattice_coeff_tendsto 0).isBigO_one ℝ
    · exact (tendsto_pi_nhds.1 lattice_coeff_tendsto 1).isBigO_one ℝ
    · exact coefficientFit_bounded hB S hS 2
  have hmul (i : Fin 2) : (fun n : ℕ => (((n : ℝ)^3 •
        ((M n).submatrix Fin.castSucc id - referenceTop n)) *ᵥ c n) i)
        =O[atTop] (fun _ => (1 : ℝ)) :=
    mulVec_bounded (scaled_top_matrix hB S) hcBound i
  have htarget (i : Fin 2) : (fun n : ℕ => ![-((n : ℝ)^3*budget n*(h n)^2), (0 : ℝ)] i)
      =O[atTop] (fun _ => (1 : ℝ)) := by
    fin_cases i
    · exact (scaled_mass_bound hB).neg_left
    · exact isBigO_zero _ _
  have hr (i : Fin 2) : (fun n : ℕ => (n : ℝ)^3 *
      (target n (h n) i.castSucc - (M n *ᵥ c n) i.castSucc))
      =O[atTop] (fun _ => (1 : ℝ)) := by
    apply ((htarget i).sub (hmul i)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have href (i : Fin 2) : (referenceTop n *ᵥ c n) i =
        (![1, budget n/(n : ℝ)^2] : Fin 2 → ℝ) i := by
      have hh := lattice_reference_exact n (show 0 < n from hn) i
      simp only [mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] at hh ⊢
      change frontGram n 0 i 0 * latticeCoeffs n 0 + frontGram n 0 i 1 * latticeCoeffs n 1 +
        0 * a n 2 = _
      simpa only [zero_mul, add_zero] using hh
    have hread := congrFun (show (M n).submatrix Fin.castSucc id *ᵥ c n =
        fun i : Fin 2 => (M n *ᵥ c n) i.castSucc from by
      ext i
      rfl) i
    rw [smul_mulVec, sub_mulVec, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      hread, href]
    fin_cases i <;> simp [target, budget] <;> ring
  have hh := two_row_scaled_error hP hdP heq hc hr
  apply hh.congr' ?_ EventuallyEq.rfl
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

private theorem edge_feature_error {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (k : ℝ) (i : Fin 2) :
    let x := fun n : ℕ => ((n : ℝ)+k)/(n : ℝ)
    let u := fun n : ℕ => (n : ℝ)*h n
    Tendsto (fun n : ℕ => (n : ℝ)^2 * (frontFeatures (u n) (x n) i -
      latticeFeatures (x n) i)) atTop (𝓝 0) := by
  intro x u
  have hx : Tendsto x atTop (𝓝 1) := edge_ratio_tendsto k
  have hu := scaled_mesh_sq hB 2 (by decide)
  have hxBound : ∀ᶠ n in atTop, |x n| < 2 := by
    have ht := hx.abs
    simpa using ht.eventually (gt_mem_nhds (by norm_num : |(1 : ℝ)| < 2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto (fun n : ℕ => 6*((n : ℝ)^2*u n^2)) atTop (𝓝 0) by
      simpa only [mul_zero] using hu.const_mul (6 : ℝ))
  filter_upwards [hxBound] with n hn
  have hx2 : x n^2 ≤ 4 := by
    have he := (sq_le_sq₀ (abs_nonneg (x n)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hn.le
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using he
  have hx4 : x n^4 ≤ 16 := by
    nlinarith only [sq_nonneg (x n), sq_nonneg (x n^2), mul_nonneg (sq_nonneg (x n))
      (sub_nonneg.mpr hx2), hx2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (n : ℝ))]
  calc
    _ ≤ (n : ℝ)^2 * (6*u n^2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (n : ℝ))
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


private theorem bounded_mul_zero {f g : ℕ → ℝ}
    (hf : f =O[atTop] (fun _ => (1 : ℝ))) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  have ht : (fun n => f n*g n) =O[atTop] g := by
    simpa only [one_mul] using hf.mul (isBigO_refl g atTop)
  exact ht.trans_tendsto hg

private theorem scaled_coefficient_error {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) (i : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (coefficientFit S n (h n) i.castSucc-latticeCoeffs n i)) atTop (𝓝 0) := by
  have he := isBigO_pi.mp (refined_coefficients hB S hS) i
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  apply (bounded_mul_zero he hi).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  field_simp [hn0]

private theorem boundary_reference_error {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) (offset : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^3*boundaryValue S n (h n) offset -
      (n : ℝ)^2*(latticeCoeffs n 0 + latticeCoeffs n 1*(((n : ℝ)+offset)/n)^2))
      atTop (𝓝 0) := by
  let a := fun n => coefficientFit S n (h n)
  let x := fun n : ℕ => ((n : ℝ)+offset)/(n : ℝ)
  let u := fun n : ℕ => (n : ℝ)*h n
  let F := fun n => frontFeatures (u n) (x n) 0
  let X := fun n => frontFeatures (u n) (x n) 1
  have hA : (fun n => a n 0) =O[atTop] (fun _ => (1 : ℝ)) := coefficientFit_bounded hB S hS 0
  have hC : (fun n => a n 1) =O[atTop] (fun _ => (1 : ℝ)) := coefficientFit_bounded hB S hS 1
  have hB' : (fun n => a n 2) =O[atTop] (fun _ => (1 : ℝ)) := coefficientFit_bounded hB S hS 2
  have hAerr : Tendsto (fun n : ℕ => (n : ℝ)^2*(a n 0-latticeCoeffs n 0)) atTop (𝓝 0) :=
    scaled_coefficient_error hB S hS 0
  have hCerr : Tendsto (fun n : ℕ => (n : ℝ)^2*(a n 1-latticeCoeffs n 1)) atTop (𝓝 0) :=
    scaled_coefficient_error hB S hS 1
  have hx : Tendsto x atTop (𝓝 1) := edge_ratio_tendsto offset
  obtain ⟨_, hu, _⟩ := critical_bound_mesh_limits hB
  have hf : Tendsto F atTop (𝓝 1) := by
    have ht := hx.mul hu
    rw [mul_zero] at ht
    have hcos := Real.continuous_cos.continuousAt.tendsto.comp ht
    change Tendsto (fun n => Real.cos (x n*u n)) atTop (𝓝 (Real.cos 0)) at hcos
    rw [Real.cos_zero] at hcos
    simpa [F, frontFeatures] using (tendsto_const_nhds.add hcos (a := (1 : ℝ))).div_const 2
  have hferr : Tendsto (fun n : ℕ => (n : ℝ)^2*(F n-1)) atTop (𝓝 0) :=
    edge_feature_error hB offset 0
  have hxerr : Tendsto (fun n : ℕ => (n : ℝ)^2*(X n-x n^2)) atTop (𝓝 0) :=
    edge_feature_error hB offset 1
  have hfw : Tendsto (fun n => 1-F n) atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub hf (a := (1 : ℝ))
  have hout := (((hAerr.add (hCerr.mul (hx.pow 2))).add
    (bounded_mul_zero hA hferr)).add (bounded_mul_zero hC hxerr)).add
    (bounded_mul_zero hB' hfw)
  apply (show Tendsto (fun n : ℕ => (n : ℝ)^2*(a n 0-latticeCoeffs n 0)
      + ((n : ℝ)^2*(a n 1-latticeCoeffs n 1))*x n^2 +
      a n 0*((n : ℝ)^2*(F n-1)) + a n 1*((n : ℝ)^2*(X n-x n^2)) +
      a n 2*(1-F n)) atTop (𝓝 0) by
      simpa only [one_pow, zero_mul, add_zero] using hout).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
  change _ = (n : ℝ)^3*(coefficientRow n (F n) (X n) (1-F n) ⬝ᵥ a n) -
    (n : ℝ)^2*(latticeCoeffs n 0+latticeCoeffs n 1*x n^2)
  simp only [coefficientRow, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change _ = (n : ℝ)^3*(F n/n*a n 0 + X n/n*a n 1 + (1-F n)/(n : ℝ)^3*a n 2) -
    (n : ℝ)^2*(latticeCoeffs n 0+latticeCoeffs n 1*x n^2)
  field_simp [hn0]
  <;> ring

theorem scaled_boundary_value {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) (offset : ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      boundaryValue state.1.1.1 state.1.1.2 state.1.2 state.2
    Tendsto (fun n : ℕ => (n : ℝ)^2 * readout (((S,n),h n),offset)) atTop
      (𝓝 ((3/4)*(1-2*offset))) := by
  dsimp only
  let x := fun n : ℕ => ((n : ℝ)+offset)/(n : ℝ)
  let ref := fun n : ℕ => latticeCoeffs n 0+latticeCoeffs n 1*x n^2
  have herror := boundary_reference_error hB S hS offset
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hsmall : Tendsto (fun n : ℕ => (n : ℝ)^2*boundaryValue S n (h n) offset -
      (n : ℝ)*ref n) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ =>
        ((n : ℝ)^3*boundaryValue S n (h n) offset-(n : ℝ)^2*ref n)*(n : ℝ)⁻¹)
        atTop (𝓝 0) by simpa only [mul_zero] using herror.mul hi).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    field_simp [hn0]
  have href := reference_boundary_tendsto offset
  apply (show Tendsto (fun n : ℕ => (n : ℝ)^2*boundaryValue S n (h n) offset -
      (n : ℝ)*ref n+(n : ℝ)*ref n) atTop (𝓝 ((3/4)*(1-2*offset))) by
      simpa only [zero_add] using hsmall.add href).congr
  intro n
  ring

theorem boundary_midpoint_value {h : ℕ → ℝ}
    (hB : (fun n : ℕ => (n : ℝ)^5 * (h n)^2) =O[atTop] (fun _ => (1 : ℝ)))
    (S : Finset ℝ) (hS : S.Nonempty) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      boundaryValue state.1.1 state.1.2 state.2 (1/2)
    Tendsto (fun n : ℕ => (n : ℝ)^3 * readout ((S,n),h n)) atTop (𝓝 (-9/16)) := by
  dsimp only
  let ref := fun n : ℕ => latticeCoeffs n 0+
    latticeCoeffs n 1*(((n : ℝ)+(1/2 : ℝ))/n)^2
  have herror := boundary_reference_error hB S hS (1/2)
  have href : Tendsto (fun n : ℕ => (n : ℝ)^2*ref n) atTop (𝓝 (-9/16)) := by
    have ht := (tendsto_pi_nhds.1 lattice_coeff_tendsto (1 : Fin 2)).const_mul (3/4 : ℝ)
    have hl : (3/4 : ℝ)*(-3/4) = -9/16 := by norm_num
    change Tendsto (fun n => (3/4 : ℝ)*latticeCoeffs n 1) atTop (𝓝 ((3/4 : ℝ)*(-3/4))) at ht
    rw [hl] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show 0 < n from hn).ne'
    have hz : (0 : ℝ) < normalizer n (radiusSq n) := by
      apply normalizer_pos n (show 0 < n from hn)
      unfold radiusSq
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    simp only [latticeCoeffs, Matrix.cons_val_zero, Matrix.cons_val_one, ref]
    unfold radiusSq
    field_simp [hn0,hz.ne']
    <;> ring
  apply (show Tendsto (fun n : ℕ => (n : ℝ)^3*boundaryValue S n (h n) (1/2) -
      (n : ℝ)^2*ref n+(n : ℝ)^2*ref n) atTop (𝓝 (-9/16)) by
      simpa only [zero_add] using herror.add href).congr
  intro n
  ring

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
