/- GID: D5/S3/Fourier/Concentration/FiniteSineMissingWindow
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteSineMissingWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite concentration gives a strict sine-score margin on a closed window. -/

import D5.S3.Fourier.WeightedPhaseRelationLattice
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn

/-! Simultaneous one-sided concentration and uniform control of finite sine scores. -/

namespace D5.S3.Fourier.Concentration.FiniteSineMissingWindow

open Finset MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

private def signValue (b : Bool) : ℝ := if b then 1 else -1

private def fairCoin : Measure Bool := uniformOn Set.univ

private instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

private def signsMeasure (J : Type*) [Fintype J] : Measure (J → Bool) :=
  Measure.pi (fun _ => fairCoin)

private instance {J : Type*} [Fintype J] : IsProbabilityMeasure (signsMeasure J) := by
  unfold signsMeasure
  infer_instance

private theorem fairCoin_singleton (b : Bool) : fairCoin.real {b} = 1 / 2 := by
  rw [measureReal_def, fairCoin, uniformOn_univ, Measure.count_singleton]
  norm_num [ENNReal.toReal_div]

private theorem coin_integral (c : ℝ) : ∫ b, signValue b * c ∂fairCoin = 0 := by
  rw [integral_fintype Integrable.of_finite]
  simp [fairCoin_singleton, smul_eq_mul, signValue]

private theorem signed_sum_tail {J : Type*} [Fintype J] (s : Finset J)
    (w : J → ℝ≥0) (c : J → ℝ) (hc : ∀ j ∈ s, |c j| ≤ w j)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (signsMeasure J).real {b | δ ≤ ∑ j ∈ s, signValue (b j) * c j} ≤
      Real.exp (-δ ^ 2 / (2 * ∑ j ∈ s, (w j : ℝ) ^ 2)) := by
  let X (j : J) (b : J → Bool) := signValue (b j) * c j
  have hind : iIndepFun X (signsMeasure J) :=
    iIndepFun_pi (μ := fun _ : J => fairCoin)
      (fun j : J => (measurable_of_finite (fun b : Bool => signValue b * c j)).aemeasurable)
  have hsub (j : J) (hj : j ∈ s) : HasSubgaussianMGF (X j) (w j ^ 2) (signsMeasure J) := by
    have hbound : ∀ᵐ b ∂signsMeasure J, X j b ∈ Icc (-(w j : ℝ)) (w j : ℝ) := by
      apply ae_of_all
      intro b
      apply abs_le.mp
      rw [show X j b = signValue (b j) * c j from rfl, abs_mul]
      cases h : b j <;> simpa [h, signValue] using hc j hj
    have hmean : ∫ b, X j b ∂signsMeasure J = 0 := by
      change ∫ b, (fun x : Bool => signValue x * c j) (b j)
        ∂Measure.pi (fun _ : J => fairCoin) = 0
      rw [integral_comp_eval (μ := fun _ : J => fairCoin) (i := j)
        (f := fun b : Bool => signValue b * c j) (measurable_of_finite _).aestronglyMeasurable]
      exact coin_integral (c j)
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (measurable_of_finite (X j)).aemeasurable hbound hmean
    have hradius : ‖(w j : ℝ) - (-(w j : ℝ))‖₊ / 2 = w j := by
      apply NNReal.eq
      simp only [NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
      rw [abs_of_nonneg (by linarith only [NNReal.coe_nonneg (w j)])]
      ring
    rwa [hradius] at h
  simpa only [X, NNReal.coe_sum, NNReal.coe_pow] using
    HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hδ

def signedScore {J : Type*} (s : Finset J) (c : J → ℝ) (b : J → Bool) : ℝ :=
  ∑ j ∈ s, (if b j then 1 else -1) * c j

/-- A single assignment of signs makes every one of a finite family of bounded linear
scores strictly smaller than the threshold. At zero variance all scores vanish. -/
theorem exists_signs_on_grid {J K : Type*} [Finite J] [Fintype K]
    (s : Finset J) (w : J → ℝ≥0) (c : K → J → ℝ)
    (hc : ∀ k j, j ∈ s → |c k j| ≤ w j) {δ : ℝ} (hδ : 0 < δ)
    (hbudget : (∑ j ∈ s, (w j : ℝ) ^ 2) = 0 ∨
      (Fintype.card K : ℝ) * Real.exp (-δ ^ 2 / (2 * ∑ j ∈ s, (w j : ℝ) ^ 2)) < 1) :
    ∃ b : J → Bool, ∀ k, signedScore s (c k) b < δ := by
  classical
  let := Fintype.ofFinite J
  rcases hbudget with hzero | hbudget
  · have hw := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j : ℝ))).mp hzero
    refine ⟨fun _ => true, fun k => ?_⟩
    have hc0 (j : J) (hj : j ∈ s) : c k j = 0 := by
      have hz := sq_eq_zero_iff.mp (hw j hj)
      exact abs_eq_zero.mp (le_antisymm ((hc k j hj).trans_eq hz) (abs_nonneg _))
    have hsum : signedScore s (c k) (fun _ => true) = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hc0 j hj]
    rwa [hsum]
  · let bad (k : K) : Set (J → Bool) := {b | δ ≤ ∑ j ∈ s, signValue (b j) * c k j}
    have hmeasure : (signsMeasure J).real (⋃ k, bad k) < 1 := calc
      _ ≤ ∑ k, (signsMeasure J).real (bad k) := measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _k : K, Real.exp (-δ ^ 2 / (2 * ∑ j ∈ s, (w j : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun k _ => signed_sum_tail s w (c k) (hc k) hδ.le
      _ < 1 := by simpa using hbudget
    by_contra! h
    have hall : (⋃ k, bad k) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro b
      obtain ⟨k, hk⟩ := h b
      exact mem_iUnion.mpr ⟨k, hk⟩
    simp [hall] at hmeasure

theorem floor_grid_cover {R h : ℝ} (hh : 0 < h) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) R) :
    ∃ k : Fin (⌊R / h⌋₊ + 1), |t - (k : ℕ) * h| ≤ h := by
  let k := ⌊t / h⌋₊
  have hk : k ≤ ⌊R / h⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hh.le)
  have hleft : (k : ℝ) * h ≤ t :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht.1 hh.le))
  have hright : t < ((k : ℝ) + 1) * h :=
    (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (t / h))
  refine ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
  linarith only [hright]

theorem sine_score_change {J : Type*} (s : Finset J)
    (f a : J → ℝ) (w : J → ℝ≥0) (t v : ℝ) :
    (∑ j ∈ s, (w j : ℝ) * Real.sin (a j + f j * t)) -
      (∑ j ∈ s, (w j : ℝ) * Real.sin (a j + f j * v)) ≤
        (∑ j ∈ s, (w j : ℝ) * |f j|) * |t - v| := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (w j).coe_nonneg
  rw [← abs_mul, mul_sub]
  exact (le_abs_self _).trans (by
    simpa only [add_sub_add_left_eq_sub] using
      Real.abs_sin_sub_sin_le (a j + f j * t) (a j + f j * v))

def sineScore {J : Type*} [Fintype J] (f φ : J → ℝ) (w : J → ℝ≥0) (t : ℝ) : ℝ :=
  ∑ j, (w j : ℝ) * Real.sin (φ j + f j * t)

/-- With arbitrary prescribed head phases, one choice of zero or π on the tail
keeps the full weighted sine sum strictly below head mass plus the grid threshold
and the tail slope allowance throughout the closed window. -/
theorem exists_phases_on_closed_window {J : Type*} [Fintype J] [DecidableEq J]
    (head : Finset J) (f θ : J → ℝ) (w : J → ℝ≥0) {R h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ)
    (hbudget : (∑ j ∈ headᶜ, (w j : ℝ) ^ 2) = 0 ∨
      ((⌊R / h⌋₊ : ℝ) + 1) *
        Real.exp (-δ ^ 2 / (2 * ∑ j ∈ headᶜ, (w j : ℝ) ^ 2)) < 1) :
    ∃ φ : J → ℝ, (∀ j ∈ head, φ j = θ j) ∧ (∀ j ∈ headᶜ, φ j = 0 ∨ φ j = Real.pi) ∧
      ∀ t ∈ Icc (0 : ℝ) R,
        sineScore f φ w t <
          (∑ j ∈ head, (w j : ℝ)) + δ + h * ∑ j ∈ headᶜ, (w j : ℝ) * |f j| := by
  let K := Fin (⌊R / h⌋₊ + 1)
  let grid (k : K) : ℝ := (k : ℕ) * h
  have hc (k : K) (j : J) (_ : j ∈ headᶜ) :
      |(w j : ℝ) * Real.sin (f j * grid k)| ≤ w j := by
    rw [abs_mul, abs_of_nonneg (w j).coe_nonneg]
    exact mul_le_of_le_one_right (w j).coe_nonneg (Real.abs_sin_le_one _)
  obtain ⟨b, hb⟩ := exists_signs_on_grid headᶜ w _ hc hδ
    (by simpa [K, Nat.cast_add] using hbudget)
  let φ (j : J) := if j ∈ head then θ j else if b j then 0 else Real.pi
  have hφhead (j : J) (hj : j ∈ head) : φ j = θ j := ite_eq_left hj
  have hφtail (j : J) (hj : j ∈ headᶜ) : φ j = if b j then 0 else Real.pi :=
    ite_eq_right (mem_compl.mp hj)
  have hgrid (k : K) : (∑ j ∈ headᶜ, (w j : ℝ) * Real.sin (φ j + f j * grid k)) < δ := by
    convert hb k using 1
    unfold signedScore
    apply Finset.sum_congr rfl
    intro j hj
    rw [hφtail j hj]
    cases b j <;> simp [add_comm Real.pi, Real.sin_add_pi]
  refine ⟨φ, hφhead, ?_, ?_⟩
  · intro j hj
    rw [hφtail j hj]
    cases b j <;> simp
  · intro t ht
    obtain ⟨k, hk⟩ := floor_grid_cover hh ht
    have hhead : (∑ j ∈ head, (w j : ℝ) * Real.sin (φ j + f j * t)) ≤
        ∑ j ∈ head, (w j : ℝ) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_of_le_one_right (w j).coe_nonneg (Real.sin_le_one _)
    have hslope : 0 ≤ ∑ j ∈ headᶜ, (w j : ℝ) * |f j| :=
      Finset.sum_nonneg fun j _ => mul_nonneg (w j).coe_nonneg (abs_nonneg _)
    have hstep := (sine_score_change headᶜ f φ w t (grid k)).trans
      (mul_le_mul_of_nonneg_left hk hslope)
    unfold sineScore
    rw [← Finset.sum_add_sum_compl head (fun j => (w j : ℝ) * Real.sin (φ j + f j * t))]
    linarith only [hhead, hgrid k, hstep, mul_comm h (∑ j ∈ headᶜ, (w j : ℝ) * |f j|)]

private theorem phase_score_le_of_chord {J : Type*} [Fintype J]
    (f φ ψ : J → ℝ) (w : J → ℝ≥0) {η : ℝ}
    (hclose : ∀ j, ‖(Circle.exp (ψ j) : ℂ) - (Circle.exp (φ j) : ℂ)‖ ≤ η) (t : ℝ) :
    sineScore f ψ w t ≤ sineScore f φ w t + (∑ j, (w j : ℝ)) * η := by
  unfold sineScore
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (w j).coe_nonneg
  have him (x : ℝ) : (Circle.exp x : ℂ).im = Real.sin x :=
    Complex.exp_ofReal_mul_I_im x
  have hterm : Real.sin (ψ j + f j * t) - Real.sin (φ j + f j * t) ≤ η := by
    rw [← him, ← him, ← Complex.sub_im, Circle.exp_add, Circle.exp_add]
    simp only [Circle.coe_mul]
    calc
      _ ≤ ‖(↑(Circle.exp (ψ j)) * ↑(Circle.exp (f j * t)) -
          ↑(Circle.exp (φ j)) * ↑(Circle.exp (f j * t)) : ℂ)‖ := Complex.im_le_norm _
      _ = ‖(Circle.exp (ψ j) : ℂ) - (Circle.exp (φ j) : ℂ)‖ := by
        rw [← sub_mul, norm_mul, Circle.norm_coe, mul_one]
      _ ≤ η := hclose j
  linarith only [hterm]

/-- Under rational independence, the whole-window bound occurs in the original orbit
above every starting height. One chord-distance tolerance works for all offsets. -/
theorem exists_arbitrarily_late_missing_window {J : Type*} [Fintype J] [DecidableEq J]
    (head : Finset J) (f : J → ℝ) (w : J → ℝ≥0) (hli : LinearIndependent ℚ f)
    {R h δ B : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hbudget : (∑ j ∈ headᶜ, (w j : ℝ) ^ 2) = 0 ∨
      ((⌊R / h⌋₊ : ℝ) + 1) *
        Real.exp (-δ ^ 2 / (2 * ∑ j ∈ headᶜ, (w j : ℝ) ^ 2)) < 1)
    (hmargin : (∑ j ∈ head, (w j : ℝ)) + δ +
      h * ∑ j ∈ headᶜ, (w j : ℝ) * |f j| < B) (A : ℝ) :
    ∃ a > A, ∀ u ∈ Icc a (a + R), sineScore f 0 w u < B := by
  classical
  obtain ⟨φ, _, _, hscore⟩ := exists_phases_on_closed_window head f 0 w hh hδ hbudget
  let W := ∑ j, (w j : ℝ)
  let M := (∑ j ∈ head, (w j : ℝ)) + δ + h * ∑ j ∈ headᶜ, (w j : ℝ) * |f j|
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => (w j).coe_nonneg
  let η := (B - M) / (W + 1)
  have hη : 0 < η := div_pos (sub_pos.mpr hmargin) (by linarith)
  have herr : W * η ≤ B - M := by
    have hηmul : η * (W + 1) = B - M :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith only [hηmul, hη]
  let p (j : J) := Circle.exp (φ j)
  let U : Set (J → Circle) := {q | ∀ j, ‖(q j : ℂ) - (p j : ℂ)‖ < η}
  have hU : IsOpen U := by
    have hset : U = ⋂ j : J, {q : J → Circle | ‖(q j : ℂ) - (p j : ℂ)‖ < η} := by
      ext q
      simp only [U, mem_setOf_eq, mem_iInter]
    rw [hset]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_lt _ continuous_const
    exact ((continuous_subtype_val.comp (continuous_apply j)).sub continuous_const).norm
  have hp : p ∈ U := fun j => by simpa using hη
  let orbit (a : ℝ) (j : J) := Circle.exp (f j * a)
  have hpcl : p ∈ closure (orbit '' Ioi A) := by
    have hclosure := WeightedPhaseRelationLattice.closure_real_phase_orbit f
    rw [(hclosure.2 A).2, hclosure.1]
    intro k hk
    have hrats : ∑ j, ((k j : ℤ) : ℚ) • f j = 0 := by
      simpa only [Rat.smul_def, Rat.cast_intCast] using hk
    have hzero (j : J) : k j = 0 := by
      exact_mod_cast (Fintype.linearIndependent_iff.mp hli _ hrats j)
    simp [hzero]
  obtain ⟨_, hclose, ⟨a, ha, rfl⟩⟩ := mem_closure_iff.mp hpcl U hU hp
  refine ⟨a, ha, fun u hu => ?_⟩
  let t := u - a
  have ht : t ∈ Icc (0 : ℝ) R :=
    ⟨sub_nonneg.mpr hu.1, sub_le_iff_le_add.mpr (by simpa [add_comm] using hu.2)⟩
  have hshift : sineScore f (fun j => f j * a) w t = sineScore f 0 w u := by
    unfold sineScore
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.zero_apply, zero_add, ← mul_add, add_sub_cancel]
  have htransport := phase_score_le_of_chord f φ (fun j => f j * a) w
    (fun j => (hclose j).le) t
  rw [hshift] at htransport
  change sineScore f 0 w u ≤ sineScore f φ w t + W * η at htransport
  exact htransport.trans_lt (by linarith only [hscore t ht, herr])

#print axioms exists_signs_on_grid
#print axioms exists_phases_on_closed_window
#print axioms exists_arbitrarily_late_missing_window

end

end D5.S3.Fourier.Concentration.FiniteSineMissingWindow
