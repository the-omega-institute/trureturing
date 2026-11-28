/- GID: D5/S3/Fourier/Asymptotics/PlanarWindowSampling
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/PlanarWindowSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform sampling error for translated and rescaled smooth planar windows. -/

import D5.S3.Fourier.Asymptotics.PlanarFourierTail
import D5.S3.Fourier.CoordinatePoisson
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! Sampling a smooth planar periodization from bounds on the retained Fourier modes. -/

open MeasureTheory WithLp Finset
open scoped BigOperators ContDiff FourierTransform RealInnerProductSpace SchwartzMap Topology

namespace D5.S3.Fourier.Asymptotics.PlanarWindowSampling

open PlanarFourierTail

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem fourier_dilation (f : Plane → ℂ) (ε : ℝ) (hε : 0 < ε) (w : Plane) :
    𝓕 (fun x : Plane => f (ε⁻¹ • x)) w = (ε ^ 2 : ℝ) • 𝓕 f (ε • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let g : Plane → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * ⟪x, ε • w⟫) * Complex.I)) • f x
  have hg : (fun x : Plane =>
      Complex.exp ((↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I)) • f (ε⁻¹ • x)) =
      fun x => g (ε⁻¹ • x) := by
    funext x
    dsimp [g]
    rw [real_inner_smul_left, real_inner_smul_right]
    congr 3
    field_simp
  rw [hg, Measure.integral_comp_inv_smul_of_nonneg volume g hε.le]
  simp [g]

private theorem scaled_schwartz_fourier_bound (f : 𝓢(Plane, ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ∀ w : Plane,
      ‖𝓕 (fun x : Plane => f (ε⁻¹ • x)) w‖ ≤ K * ε ^ 2 / (1 + ε * ‖w‖) ^ 8 := by
  let F : 𝓢(Plane, ℂ) := 𝓕 f
  let K : ℝ := 2 ^ (8 : ℕ) *
    (Finset.Iic (8, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨K, hK, fun ε hε w => ?_⟩
  have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8, 0)) (k := 8) (n := 0) le_rfl le_rfl F (ε • w)
  have hscale : (1 + ε * ‖w‖) ^ 8 * ‖𝓕 (f : Plane → ℂ) (ε • w)‖ ≤ K := by
    simpa [F, K, SchwartzMap.fourier_coe, norm_smul, Real.norm_eq_abs, abs_of_pos hε] using hd
  rw [fourier_dilation _ ε hε w, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hscale (sq_nonneg ε)

private theorem frequency_radius_le (m : ℤ × ℤ) :
    (max m.1.natAbs m.2.natAbs : ℝ) ≤
      ‖(WithLp.toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)] : Plane)‖ := by
  let z : Plane := WithLp.toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]
  refine max_le ?_ ?_
  · simpa [z, Real.norm_eq_abs, ← Int.cast_abs, Nat.cast_natAbs] using
      PiLp.norm_apply_le (p := 2) z (0 : Fin 2)
  · simpa [z, Real.norm_eq_abs, ← Int.cast_abs, Nat.cast_natAbs] using
      PiLp.norm_apply_le (p := 2) z (1 : Fin 2)

private theorem fourier_translate (f : Plane → ℂ) (x w : Plane) :
    𝓕 (fun y => f (y + x)) w = Real.fourierChar ⟪x, w⟫ • 𝓕 f w := by
  exact congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ Plane) f x) w

private theorem translated_lattice_decay (f : Plane → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ), 0 < ε → ∀ (c : Plane) (m : ℤ × ℤ),
      ‖𝓕 (fun x : Plane => f (ε⁻¹ • (x - c)))
        (WithLp.toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)])‖ ≤
          K * ε ^ 2 / (1 + ε * (max m.1.natAbs m.2.natAbs : ℕ)) ^ 8 := by
  obtain ⟨K, hK, h⟩ := scaled_schwartz_fourier_bound (hf.toSchwartzMap hs)
  refine ⟨K, hK, fun ε he c m => ?_⟩
  let w : Plane := WithLp.toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]
  let g : Plane → ℂ := fun x => f (ε⁻¹ • x)
  have htrans : ‖𝓕 (fun x : Plane => g (x - c)) w‖ = ‖𝓕 g w‖ := by
    simp only [sub_eq_add_neg, fourier_translate, Circle.smul_def, smul_eq_mul, norm_mul,
      Circle.norm_coe, one_mul]
  change ‖𝓕 (fun x : Plane => g (x - c)) w‖ ≤ _
  rw [htrans]
  refine (h ε he w).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ (by positivity) (by rw [Nat.cast_max]; gcongr; exact frequency_radius_le m) _)


private theorem coordinate_fourier_integral (f : Plane → ℂ) (m : ℤ × ℤ) :
    (∫ x : Fin 2 → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
      (∑ i : Fin 2, (![(m.1 : ℝ), (m.2 : ℝ)] : Fin 2 → ℝ) i * x i : ℝ)) *
        f (toLp 2 x)) = 𝓕 f (toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]) := by
  rw [Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_eq_mul]
  congr 2
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [RCLike.star_def, conj_trivial, Pi.star_apply, dotProduct]
  push_cast
  ring


private theorem locally_finite_lattice_translates {ι : Type*} [Finite ι]
    (f : C(ι → ℝ, ℂ)) (hf : HasCompactSupport f) (K : TopologicalSpace.Compacts (ι → ℝ)) :
    Summable (fun a : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  obtain ⟨S, hS⟩ := hf.isCompact.isBounded.subset_closedBall 0
  let B : Finset (ι → ℤ) := Fintype.piFinset (fun _ => Finset.Icc ⌈-(R + S)⌉ ⌊R + S⌋)
  apply summable_of_ne_finset_zero (s := B)
  intro a ha
  suffices hzero : (f.comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K = 0 by
    rw [hzero, norm_zero]
  apply ContinuousMap.ext
  intro x
  change f (x.val + fun i => (a i : ℝ)) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  apply ha
  apply Fintype.mem_piFinset.mpr
  intro i
  have hxR : ‖x.val‖ ≤ R := by simpa using hR x.property
  have hxS : ‖x.val + fun j => (a j : ℝ)‖ ≤ S := by simpa using hS hx
  have hxi := (norm_le_pi_norm x.val i).trans hxR
  have hai := (norm_le_pi_norm (x.val + fun j => (a j : ℝ)) i).trans hxS
  change ‖x.val i + (a i : ℝ)‖ ≤ S at hai
  rw [Real.norm_eq_abs, abs_le] at hxi hai
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

private theorem lattice_periodization (f : Plane → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (p : Plane)
    (hs : Summable (fun m : ℤ × ℤ =>
      𝓕 f (toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]))) :
    (∑' a : Fin 2 → ℤ, f (toLp 2 (fun i => (a i : ℝ)) + p)) =
      ∑' m : ℤ × ℤ, 𝓕 f (toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]) *
        (Real.fourierChar ⟪p, toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]⟫ : ℂ) := by
  let F : Plane → ℂ := fun y => f (y + p)
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toHomeomorph
  let G : C(Fin 2 → ℝ, ℂ) :=
    ⟨F ∘ E, (hc.comp (continuous_id.add continuous_const)).comp E.continuous⟩
  have hG : HasCompactSupport G := (hf.comp_homeomorph (Homeomorph.addRight p)).comp_homeomorph E
  let equiv := finTwoArrowEquiv ℤ
  let A : (ℤ × ℤ) → ℂ := fun m => 𝓕 f (toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)])
  let χ : (ℤ × ℤ) → ℂ := fun m =>
    Real.fourierChar ⟪p, toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]⟫
  have hsum : Summable (fun m => A m * χ m) := by
    refine hs.norm.of_norm_bounded (fun m => ?_)
    simp [A, χ, Circle.norm_coe]
  have hint (k : Fin 2 → ℤ) :
      (∫ x : Fin 2 → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i : Fin 2, (k i : ℝ) * x i : ℝ)) * G x) = A (equiv k) * χ (equiv k) := by
    let m := equiv k
    have hm (i : Fin 2) :
        (k i : ℝ) = (![(m.1 : ℝ), (m.2 : ℝ)] : Fin 2 → ℝ) i := by
      fin_cases i <;> rfl
    simp_rw [hm]
    change (∫ x : Fin 2 → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
      (∑ i : Fin 2, (![(m.1 : ℝ), (m.2 : ℝ)] : Fin 2 → ℝ) i * x i : ℝ)) *
        F (toLp 2 x)) = A m * χ m
    rw [coordinate_fourier_integral, fourier_translate]
    simp [A, χ, Circle.smul_def, mul_comm]
  have hfourier : Summable (fun k : Fin 2 → ℤ =>
      ∫ x : Fin 2 → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i : Fin 2, (k i : ℝ) * x i : ℝ)) * G x) :=
    (equiv.summable_iff.mpr hsum).congr fun k => (hint k).symm
  calc
    _ = ∑' k : Fin 2 → ℤ, ∫ x : Fin 2 → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i : Fin 2, (k i : ℝ) * x i : ℝ)) * G x :=
      D5.S3.Fourier.CoordinatePoisson.tsum_eq_tsum_integral
        (G.continuous.integrable_of_hasCompactSupport hG)
        (locally_finite_lattice_translates G hG) hfourier
    _ = ∑' m : ℤ × ℤ, A m * χ m :=
      (tsum_congr hint).trans (equiv.tsum_eq fun m => A m * χ m)

private theorem mode_count_le (s : Finset (ℤ × ℤ)) (J : ℕ)
    (h : ∀ m ∈ s, modeRadius m ≤ J) : (s.card : ℝ) ≤ (2 * (J : ℝ) + 1) ^ 2 := by
  let B : Finset ℤ := Finset.Icc (-(J : ℤ)) J
  have hcoord (z : ℤ) (hz : z.natAbs ≤ J) : z ∈ B := by
    change z ∈ Finset.Icc _ _
    rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs, Int.ofNat_le]
    exact hz
  have hsub : s ⊆ B ×ˢ B := by
    intro m hm
    have hmax := h m hm
    change max m.1.natAbs m.2.natAbs ≤ J at hmax
    exact Finset.mem_product.mpr
      ⟨hcoord _ ((le_max_left _ _).trans hmax), hcoord _ ((le_max_right _ _).trans hmax)⟩
  have hcard : B.card = 2 * J + 1 := by
    change (Finset.Icc (-(J : ℤ)) (J : ℤ)).card = _
    rw [Int.card_Icc]
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product, hcard, ← pow_two] at hc
  exact_mod_cast hc

private theorem scaled_fourier_mass (s : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℂ) (ε K : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1) (hK : 0 ≤ K)
    (hd : ∀ m ∈ s, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6) :
    ∑ m ∈ s, ‖a m‖ ≤ 27 * K := by
  classical
  let J := ⌈ε⁻¹⌉₊
  have hceil : ε⁻¹ ≤ (J : ℝ) := Nat.le_ceil _
  have hJ : 0 < J := by
    exact_mod_cast (inv_pos.mpr he).trans_le hceil
  have hlow : 1 ≤ ε * (J : ℝ) := by
    have q := mul_le_mul_of_nonneg_left hceil he.le
    rwa [mul_inv_cancel₀ he.ne'] at q
  have hupper : ε * (J : ℝ) ≤ 2 := by
    have q := Nat.ceil_lt_add_one (inv_nonneg.mpr he.le)
    have h := mul_le_mul_of_nonneg_left q.le he.le
    rw [mul_add, mul_inv_cancel₀ he.ne', mul_one] at h
    linarith
  have hinner :
      ∑ m ∈ s.filter (fun m => modeRadius m ≤ J), ‖a m‖ ≤ 25 * K := by
    have hcard := mode_count_le (s.filter (fun m => modeRadius m ≤ J)) J
      (fun m hm => (mem_filter.mp hm).2)
    calc
      _ ≤ ∑ _m ∈ s.filter (fun m => modeRadius m ≤ J), K * ε ^ 2 := by
        refine sum_le_sum fun m hm => (hd m (mem_filter.mp hm).1).trans ?_
        apply div_le_self (by positivity)
        exact one_le_pow₀ (le_add_of_nonneg_right (by positivity))
      _ ≤ (2 * (J : ℝ) + 1) ^ 2 * (K * ε ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K * (2 * (ε * (J : ℝ)) + ε) ^ 2 := by ring
      _ ≤ 25 * K := by
        have hsmall : 2 * (ε * (J : ℝ)) + ε ≤ 5 := by linarith
        have hs : (2 * (ε * (J : ℝ)) + ε) ^ 2 ≤ (5 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hsmall _
        linarith [mul_le_mul_of_nonneg_left hs hK]
  have htail := lattice_fourier_tail (s.filter (fun m => J < modeRadius m)) a J ε K
    hJ he hK (fun m hm => (mem_filter.mp hm).2) (fun m hm => hd m (mem_filter.mp hm).1)
  have hout : ∑ m ∈ s.filter (fun m => J < modeRadius m), ‖a m‖ ≤ 2 * K := by
    refine htail.trans ?_
    apply div_le_self (by positivity)
    rw [← mul_pow]
    exact one_le_pow₀ hlow
  have hsplit := sum_filter_add_sum_filter_not (s := s) (p := fun m => modeRadius m ≤ J)
    (f := fun m => ‖a m‖)
  simp only [not_le] at hsplit
  linarith [hinner, hout]

private theorem scaled_fourier_masses (s : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℂ) (ε K : ℝ)
    (he : 0 < ε) (he1 : ε ≤ 1) (hK : 0 ≤ K)
    (hd : ∀ m ∈ s, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8) :
    (∑ m ∈ s, ‖a m‖ ≤ 27 * K) ∧
    (∑ m ∈ s, (modeRadius m : ℝ) ^ 2 * ‖a m‖ ≤ 27 * K / ε ^ 2) := by
  have hscale (m : ℤ × ℤ) : 1 ≤ 1 + ε * modeRadius m :=
    le_add_of_nonneg_right (by positivity)
  constructor
  · refine scaled_fourier_mass s a ε K he he1 hK fun m hm => (hd m hm).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (hscale m) (by decide : 6 ≤ 8))
  · let b (m : ℤ × ℤ) : ℂ := ((ε * (modeRadius m : ℝ)) ^ 2 : ℝ) • a m
    have hb (m : ℤ × ℤ) (hm : m ∈ s) :
        ‖b m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 6 := by
      change ‖((ε * (modeRadius m : ℝ)) ^ 2 : ℝ) • a m‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (1 + ε * modeRadius m) ^ 2 *
            (K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8) := by
          apply mul_le_mul _ (hd m hm) (norm_nonneg _) (sq_nonneg _)
          gcongr
          linarith
        _ = _ := by field_simp
    have h := scaled_fourier_mass s b ε K he he1 hK hb
    apply (le_div_iff₀ (sq_pos_of_pos he)).2
    calc
      _ = ∑ m ∈ s, ‖b m‖ := by
        rw [mul_comm, mul_sum]
        apply sum_congr rfl
        intro m hm
        change _ = ‖((ε * (modeRadius m : ℝ)) ^ 2 : ℝ) • a m‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        ring
      _ ≤ _ := h

private theorem mode_action_bound (s : Finset (ℤ × ℤ)) (a A : ℤ × ℤ → ℂ)
    (J : ℕ) (ε K c d : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hJ : 0 < J)
    (hdecay : ∀ m ∈ s, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8)
    (hsmall : ∀ m ∈ s, modeRadius m ≤ J → ‖A m‖ ≤ c + d * (modeRadius m : ℝ) ^ 2)
    (hlarge : ∀ m ∈ s, J < modeRadius m → ‖A m‖ ≤ 1) :
    ‖∑ m ∈ s, a m * A m‖ ≤
      27 * K * c + (27 * K / ε ^ 2) * d + 2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
  classical
  let low := s.filter (fun m => modeRadius m ≤ J)
  let high := s.filter (fun m => J < modeRadius m)
  have hsplit : (∑ m ∈ low, a m * A m) + ∑ m ∈ high, a m * A m =
      ∑ m ∈ s, a m * A m := by
    simpa only [low, high, not_le] using
      (sum_filter_add_sum_filter_not (s := s) (p := fun m => modeRadius m ≤ J)
        (f := fun m => a m * A m))
  obtain ⟨hmass, hmom⟩ := scaled_fourier_masses low a ε K he he1 hK
    (fun m hm => hdecay m (mem_filter.mp hm).1)
  have hlow :
      ‖∑ m ∈ low, a m * A m‖ ≤ 27 * K * c + (27 * K / ε ^ 2) * d := by
    calc
      _ ≤ ∑ m ∈ low, ‖a m‖ * (c + d * (modeRadius m : ℝ) ^ 2) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
        rw [norm_mul]
        obtain ⟨hs, hj⟩ := mem_filter.mp hm
        exact mul_le_mul_of_nonneg_left (hsmall m hs hj) (norm_nonneg _)
      _ = (∑ m ∈ low, ‖a m‖) * c +
          (∑ m ∈ low, (modeRadius m : ℝ) ^ 2 * ‖a m‖) * d := by
        simp only [sum_mul, ← sum_add_distrib]
        exact sum_congr rfl fun m _ => by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hmass hc)
        (mul_le_mul_of_nonneg_right hmom hd)
  have hhigh : ‖∑ m ∈ high, a m * A m‖ ≤
      2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun m hm => ?_).trans
      (lattice_fourier_tail high a J ε K hJ he hK
        (fun m hm => (mem_filter.mp hm).2) (fun m hm => ?_)))
    · rw [norm_mul]
      obtain ⟨hs, hj⟩ := mem_filter.mp hm
      simpa using mul_le_mul_of_nonneg_left (hlarge m hs hj) (norm_nonneg (a m))
    · refine (hdecay m (mem_filter.mp hm).1).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) (by decide : 6 ≤ 8))
  rw [← hsplit]
  exact (norm_add_le _ _).trans (add_le_add hlow hhigh)

private theorem scaled_fourier_action (a A : ℤ × ℤ → ℂ)
    (J : ℕ) (ε K c d : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hJ : 0 < J)
    (hdecay : ∀ m, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8)
    (hsmall : ∀ m, modeRadius m ≤ J → ‖A m‖ ≤ c + d * (modeRadius m : ℝ) ^ 2)
    (hlarge : ∀ m, J < modeRadius m → ‖A m‖ ≤ 1) :
    Summable (fun m : ℤ × ℤ => a m * A m) ∧
    ‖∑' m : ℤ × ℤ, a m * A m‖ ≤
      27 * K * c + (27 * K / ε ^ 2) * d + 2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
  have hA (m : ℤ × ℤ) : ‖A m‖ ≤ max (c + d * (J : ℝ) ^ 2) 1 := by
    rcases le_or_gt (modeRadius m) J with hm | hm
    · refine (hsmall m hm).trans ((?_ : _ ≤ c + d * (J : ℝ) ^ 2).trans (le_max_left _ _))
      gcongr
    · exact (hlarge m hm).trans (le_max_right _ _)
  have hnorm : Summable (fun m : ℤ × ℤ => ‖a m‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) (fun s =>
      (scaled_fourier_masses s a ε K he he1 hK (fun m _ => hdecay m)).1)
  have hsNorm : Summable (fun m => ‖a m * A m‖) := by
    refine (hnorm.mul_right (max (c + d * (J : ℝ) ^ 2) 1)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun m => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hA m) (norm_nonneg _)
  refine ⟨hsNorm.of_norm, ?_⟩
  have hlim := hsNorm.of_norm.hasSum.norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun s => mode_action_bound s a A J ε K c d he he1 hK hc hd hJ
    (fun m _ => hdecay m) (fun m _ => hsmall m) (fun m _ => hlarge m)


private theorem scaled_sampling_error {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (χ : (ℤ × ℤ) → ι → ℂ) (a : ℤ × ℤ → ℂ)
    (J : ℕ) (ε K c d : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hJ : 0 < J)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : ∑ i ∈ s, w i = 1)
    (hχ : ∀ m i, ‖χ m i‖ ≤ 1) (hχ0 : ∀ i, χ (0, 0) i = 1)
    (hdecay : ∀ m, ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8)
    (hmode : ∀ m ≠ (0, 0), modeRadius m ≤ J →
      ‖∑ i ∈ s, (w i : ℂ) * χ m i‖ ≤ c + d * (modeRadius m : ℝ) ^ 2) :
    ‖(∑ i ∈ s, (w i : ℂ) * ∑' m : ℤ × ℤ, a m * χ m i) - a (0, 0)‖ ≤
      27 * K * c + (27 * K / ε ^ 2) * d + 2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
  classical
  let E (m : ℤ × ℤ) := ∑ i ∈ s, (w i : ℂ) * χ m i
  let A (m : ℤ × ℤ) := E m - if m = (0, 0) then 1 else 0
  have hE (m : ℤ × ℤ) : ‖E m‖ ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ s, ‖(w i : ℂ) * χ m i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, w i := by
        apply sum_le_sum fun i hi => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
        simpa using mul_le_mul_of_nonneg_left (hχ m i) (hw i hi)
      _ = 1 := hW
  have hE0 : E (0, 0) = 1 := by
    simp only [E, hχ0, mul_one]
    exact_mod_cast hW
  have hA0 : A (0, 0) = 0 := by simp [A, hE0]
  have hsmall (m : ℤ × ℤ) (hm : modeRadius m ≤ J) :
      ‖A m‖ ≤ c + d * (modeRadius m : ℝ) ^ 2 := by
    by_cases h : m = (0, 0)
    · rw [h, hA0, norm_zero]
      positivity
    · simpa [A, E, h] using hmode m h hm
  have hlarge (m : ℤ × ℤ) (hm : J < modeRadius m) : ‖A m‖ ≤ 1 := by
    by_cases h : m = (0, 0)
    · simp [h, hA0]
    · simpa [A, h] using hE m
  have hnorm : Summable (fun m : ℤ × ℤ => ‖a m‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) (fun s =>
      (scaled_fourier_masses s a ε K he he1 hK (fun m _ => hdecay m)).1)
  have hχseries (i : ι) : Summable (fun m : ℤ × ℤ => a m * χ m i) := by
    refine hnorm.of_norm_bounded (fun m => ?_)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hχ m i) (norm_nonneg (a m))
  have hEs : Summable (fun m : ℤ × ℤ => a m * E m) := by
    refine hnorm.of_norm_bounded (fun m => ?_)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hE m) (norm_nonneg (a m))
  let z (m : ℤ × ℤ) := if m = (0, 0) then a (0, 0) else 0
  have hzs : HasSum z (a (0, 0)) := by
    exact hasSum_ite_eq _ _
  have hinterchange :
      (∑ i ∈ s, (w i : ℂ) * ∑' m : ℤ × ℤ, a m * χ m i) = ∑' m, a m * E m := by
    simp_rw [← (hχseries _).tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun i _ => (hχseries i).mul_left _)]
    congr 1
    funext m
    dsimp only [E]
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [hinterchange, ← hzs.tsum_eq, ← hEs.tsum_sub hzs.summable]
  convert (scaled_fourier_action a A J ε K c d he he1 hK hc hd hJ hdecay hsmall hlarge).2 using 2
  congr 1
  funext m
  by_cases hm : m = (0, 0) <;> simp [A, z, hm, mul_sub]

/-- The torus character at an integer frequency, evaluated on a representative point. -/
def character (m : ℤ × ℤ) (p : Plane) : ℂ :=
  Real.fourierChar ⟪p, toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)]⟫

/-- A smooth compactly supported window has uniform sampling error over its centers and scales. -/
theorem compact_window_sampling {ι : Type*} (f : Plane → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) :
    ∃ K ≥ (0 : ℝ), ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (center : Plane) (s : Finset ι) (w : ι → ℝ) (p : ι → Plane)
        (J : ℕ) (c d : ℝ), 0 ≤ c → 0 ≤ d → 0 < J →
        (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
        (∀ m ≠ (0, 0), modeRadius m ≤ J →
          ‖∑ i ∈ s, (w i : ℂ) * character m (p i)‖ ≤ c + d * (modeRadius m : ℝ) ^ 2) →
        ‖(∑ i ∈ s, (w i : ℂ) *
          ∑' a : Fin 2 → ℤ, f (ε⁻¹ • (toLp 2 (fun j => (a j : ℝ)) + p i - center))) -
          (ε ^ 2 : ℝ) • (∫ x, f x)‖ ≤
            27 * K * c + (27 * K / ε ^ 2) * d + 2 * K / (ε ^ 4 * (J : ℝ) ^ 4) := by
  obtain ⟨K, hK, hdecay⟩ := translated_lattice_decay f hf hs
  refine ⟨K, hK, fun ε he he1 center s w p J c d hc hd hJ hw hW hmode => ?_⟩
  let g : Plane → ℂ := fun x => f (ε⁻¹ • (x - center))
  have hg : HasCompactSupport g := (hf.comp_smul (inv_ne_zero he.ne')).comp_homeomorph
    (Homeomorph.addRight (-center))
  have hgc : Continuous g := by dsimp [g]; fun_prop
  let a : ℤ × ℤ → ℂ := fun m => 𝓕 g (toLp 2 ![(m.1 : ℝ), (m.2 : ℝ)])
  have hA (m : ℤ × ℤ) : ‖a m‖ ≤ K * ε ^ 2 / (1 + ε * modeRadius m) ^ 8 :=
    hdecay ε he center m
  have hsum : Summable a :=
    (summable_of_sum_le (fun m => norm_nonneg (a m)) (fun t =>
      (scaled_fourier_masses t a ε K he he1 hK (fun m _ => hA m)).1)).of_norm
  have hz : (toLp 2 ![(0 : ℝ), (0 : ℝ)] : Plane) = 0 := by
    ext j
    fin_cases j <;> rfl
  have hzero : a (0, 0) = (ε ^ 2 : ℝ) • (∫ x, f x) := by
    change 𝓕 g (toLp 2 ![((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]) = _
    rw [Int.cast_zero, hz, Real.fourier_eq']
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul]
    change (∫ x, f (ε⁻¹ • (x - center))) = _
    calc
      _ = ∫ x, f (ε⁻¹ • x) := by
        simpa only [sub_eq_add_neg] using
          (integral_add_right_eq_self (fun x : Plane => f (ε⁻¹ • x)) (-center))
      _ = _ := by
        rw [Measure.integral_comp_inv_smul_of_nonneg volume f he.le]
        simp
  have hχ0 (i : ι) : character (0, 0) (p i) = 1 := by
    change (Real.fourierChar ⟪p i, toLp 2 ![((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)]⟫ : ℂ) = 1
    simp [hz]
  have hsample := scaled_sampling_error s w (fun m i => character m (p i))
    a J ε K c d he he1 hK hc hd hJ hw hW (fun _ _ => (Circle.norm_coe _).le) hχ0 hA hmode
  rw [hzero] at hsample
  change ‖(∑ i ∈ s, (w i : ℂ) * ∑' a : Fin 2 → ℤ,
    g (toLp 2 (fun j => (a j : ℝ)) + p i)) - _‖ ≤ _
  simp_rw [lattice_periodization g hg hgc _ hsum]
  exact hsample

#print axioms compact_window_sampling

end

end D5.S3.Fourier.Asymptotics.PlanarWindowSampling
