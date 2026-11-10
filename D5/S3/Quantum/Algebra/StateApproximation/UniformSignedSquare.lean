/- GID: D5/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/UniformSignedSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique, mathlib/module/Mathlib.Analysis.InnerProductSpace.StarOrder, mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic]
   utility: none
   digest: Uniform signed original-algebra square approximation for whole-state-space extreme real states. -/

import D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.VonNeumannAlgebra.Density
import D5.S3.Quantum.Algebra.StateApproximation.TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
open Filter Topology InnerProductSpace
open scoped ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace D5.S3.Quantum.Algebra.StateApproximation.UniformSignedSquare
universe u v
variable {A : Type u} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

/- Original algebra square, with its actual selfadjoint subtype. -/
def square (e : selfAdjoint A) : selfAdjoint A := ⟨(e : A)^2, e.property.pow 2⟩
/- The real sign, used only with a nonzero state reading. -/
def sigma (r : ℝ) : ℝ := if 0 < r then 1 else -1
/- The signed square is formed inside the original algebra. -/
def signedSquare (r : ℝ) (e : selfAdjoint A) : selfAdjoint A := sigma r • square e

theorem sigma_sq (r : ℝ) : sigma r * sigma r = 1 := by
  unfold sigma
  split <;> norm_num

theorem sigma_abs (r : ℝ) : |sigma r| = 1 := by
  unfold sigma
  split <;> norm_num

theorem signedSquare_cone (r : ℝ) (e : selfAdjoint A) :
    0 ≤ sigma r • (signedSquare r e : A) := by
  change 0 ≤ sigma r • (sigma r • ((e : A)^2))
  rw [smul_smul, sigma_sq, one_smul]
  exact e.property.sq_nonneg

theorem signedSquare_norm (r : ℝ) (e : selfAdjoint A) {L : ℝ}
    (hL : 0 ≤ L) (he : ‖e‖ ≤ L) : ‖(signedSquare r e : A)‖ ≤ L^2 := by
  change ‖sigma r • ((e : A)^2)‖ ≤ L^2
  rw [norm_smul, Real.norm_eq_abs, sigma_abs, one_mul]
  change ‖(e : A)‖ ≤ L at he
  exact (norm_pow_le (e : A) 2).trans (by nlinarith [norm_nonneg (e : A)])

section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- Symmetrization supplies an original selfadjoint preimage without faithfulness. -/
theorem selfAdjoint_lift (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {b : H →L[ℂ] H} (hb : b ∈ π.range) (hbs : IsSelfAdjoint b) :
    ∃ a : selfAdjoint A, π (a : A) = b := by
  obtain ⟨a, rfl⟩ := hb
  let a' : selfAdjoint A := ⟨(2⁻¹ : ℝ) • (a + star a),
    (IsSelfAdjoint.all (2⁻¹ : ℝ)).smul (.add_star_self a)⟩
  refine ⟨a', ?_⟩
  change IsSelfAdjoint (π a) at hbs
  change π.toAlgHom ((2⁻¹ : ℝ) • (a + star a)) = π a
  rw [π.toAlgHom.map_smul_of_tower]
  change (2⁻¹ : ℝ) • π (a + star a) = π a
  rw [map_add π, map_star π, hbs.star_eq, ← two_smul ℝ (π a), smul_smul]
  norm_num

/- CFC truncation gives a bound in the original algebra before any accuracy is chosen. -/
theorem bounded_strong_lift (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hirr : Physicslib4.GNS.IsIrreducible π) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ L : ℝ, 0 < L ∧ ∀ (x y : H) (δ : ℝ), 0 < δ →
      ∃ e : selfAdjoint A, ‖e‖ ≤ L ∧
        ‖π (e : A) x - T x‖ < δ ∧ ‖π (e : A) y - T y‖ < δ := by
  let R : ℝ := 1 + ‖T‖
  have hR : 0 < R := by dsimp [R]; positivity
  let B : H →L[ℂ] H := R⁻¹ • T
  have hB : IsSelfAdjoint B := (IsSelfAdjoint.all (R⁻¹ : ℝ)).smul hT
  have hBnorm : ‖B‖ ≤ 1 := by
    dsimp [B]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    apply (inv_mul_le_iff₀ hR).2
    dsimp [R]
    linarith
  let U : H →L[ℂ] H := cfc TauCeti.kaplanskyFunInv B
  have hU : IsSelfAdjoint U := IsSelfAdjoint.cfc
  have hFU : cfc TauCeti.kaplanskyFun U = B :=
    hB.cfc_kaplanskyFun_cfc_kaplanskyFunInv hBnorm
  let q := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  let f : selfAdjoint A → H →Lₚₜ[ℂ] H := fun a => q (π (a : A))
  have himage : Set.range f = q '' ((π.range : Set (H →L[ℂ] H)) ∩
      selfAdjoint (H →L[ℂ] H)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨π (a : A), ⟨⟨(a : A), rfl⟩, a.property.map π⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hbs⟩, rfl⟩
      obtain ⟨a, ha⟩ := selfAdjoint_lift π hb hbs
      exact ⟨a, congrArg q ha⟩
  have hclosure : q U ∈ closure (Set.range f) := by
    rw [himage, StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    refine ⟨U, ⟨?_, hU⟩, rfl⟩
    have hu : U ∈ Physicslib4.GNS.gnsVonNeumann π := by
      rw [Physicslib4.GNS.gnsVonNeumann_eq_univ_of_isIrreducible hirr]
      exact Set.mem_univ U
    exact hu
  let l : Filter (selfAdjoint A) := Filter.comap f (𝓝 (q U))
  haveI : l.NeBot := by
    apply Filter.comap_neBot
    intro t ht
    obtain ⟨z, hz⟩ := mem_closure_iff_nhds'.mp hclosure t ht
    obtain ⟨a, ha⟩ := z.property
    exact ⟨a, ha ▸ hz⟩
  have hraw : ∀ x : H, Tendsto (fun a : selfAdjoint A => π (a : A) x) l (𝓝 (U x)) := by
    have hf : Tendsto f l (𝓝 (q U)) := tendsto_comap
    exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hf
  let e : selfAdjoint A → selfAdjoint A := fun a =>
    ⟨R • cfc TauCeti.kaplanskyFun (a : A),
      (IsSelfAdjoint.all R).smul IsSelfAdjoint.cfc⟩
  have henorm : ∀ a, ‖e a‖ ≤ R := by
    intro a
    change ‖R • cfc TauCeti.kaplanskyFun (a : A)‖ ≤ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact (mul_le_mul_of_nonneg_left (TauCeti.norm_cfc_kaplanskyFun_le (a : A)) hR.le).trans_eq (mul_one R)
  have hemap : ∀ a, π (e a : A) = R • cfc TauCeti.kaplanskyFun (π (a : A)) := by
    intro a
    change π.toAlgHom (R • cfc TauCeti.kaplanskyFun (a : A)) = _
    rw [π.toAlgHom.map_smul_of_tower]
    congr 1
    exact π.map_cfc TauCeti.kaplanskyFun (a : A)
      TauCeti.continuous_kaplanskyFun.continuousOn (by fun_prop)
      a.property (a.property.map π)
  have heconv : ∀ x : H, Tendsto (fun a => π (e a : A) x) l (𝓝 (T x)) := by
    intro x
    have hc := (TauCeti.tendsto_cfc_kaplanskyFun_apply
      (Eventually.of_forall (fun a : selfAdjoint A => a.property.map π)) hU hraw x).const_smul R
    have hRT : R • B = T := by
      dsimp [B]
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    simpa only [hemap, ContinuousLinearMap.smul_apply, hFU, ← ContinuousLinearMap.smul_apply, hRT] using hc
  refine ⟨R, hR, ?_⟩
  intro x y δ hδ
  have hx := (tendsto_iff_norm_sub_tendsto_zero.mp (heconv x)).eventually_lt_const hδ
  have hy := (tendsto_iff_norm_sub_tendsto_zero.mp (heconv y)).eventually_lt_const hδ
  obtain ⟨a, hax, hay⟩ := (hx.and hy).exists
  exact ⟨e a, henorm a, hax, hay⟩

/- The original square reading is exactly the represented vector norm squared. -/
theorem square_reading (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (hm : ∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ))
    (d : selfAdjoint A) : Real.sqrt (β (square d)) = ‖π (d : A) Ω‖ := by
  have hp : (π (d : A)).adjoint = π (d : A) :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (d.property.map π)
  have hn : ‖π (d : A) Ω‖^2 = (inner ℂ Ω (π ((d : A)^2) Ω)).re := by
    simpa only [map_pow, pow_two, map_mul, ContinuousLinearMap.mul_def, hp,
      RCLike.re_eq_complex_re] using
      (π (d : A)).apply_norm_sq_eq_inner_adjoint_right Ω
  have hb : β (square d) = ‖π (d : A) Ω‖^2 := by
    rw [hn]
    exact (congrArg Complex.re (hm (square d))).symm
  rw [hb, Real.sqrt_sq (norm_nonneg _)]

/- A positive rank-one endpoint has a selfadjoint square root with the required signed action. -/
theorem signed_endpoint (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H)
    (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (hm : ∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ))
    (k : selfAdjoint A) (hr : β k ≠ 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
      T (T Ω) = sigma (β k) • π (k : A) Ω := by
  let r : ℝ := β k
  let v : H := π (k : A) Ω
  have hi : inner ℂ v Ω = (r : ℂ) := by
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (k.property.map π)) Ω Ω).trans (hm k)
  have hratio : |r|⁻¹ * r = sigma r := by
    by_cases hp : 0 < r
    · rw [abs_of_pos hp, inv_mul_cancel₀ hp.ne', sigma, if_pos hp]
    · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
      rw [abs_of_neg hn, inv_neg, neg_mul, inv_mul_cancel₀ hr, sigma, if_neg hp]
  let S : H →L[ℂ] H := |r|⁻¹ • rankOne ℂ v v
  have hS : 0 ≤ S := by
    exact smul_nonneg (inv_nonneg.mpr (abs_nonneg r))
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self v))
  have hSO : S Ω = sigma r • v := by
    have hrv : (r : ℂ) • v = r • v := IsScalarTower.algebraMap_smul ℂ r v
    simp only [S, ContinuousLinearMap.smul_apply, rankOne_apply, hi, hrv, smul_smul, hratio]
  refine ⟨CFC.sqrt S, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S), ?_⟩
  change (CFC.sqrt S * CFC.sqrt S) Ω = sigma r • v
  rw [CFC.sqrt_mul_sqrt_self S hS, hSO]
end Representation

/- Uniform signed original-square approximation for an arbitrary whole-space extreme real state. -/
theorem uniform_signed_original_square (β : selfAdjoint A →ₗ[ℝ] ℝ)
    (hβ : D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.IsRealState β) (hpure : β ∈ (D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.realStateSpace A).extremePoints ℝ)
    (k : selfAdjoint A) (hr : β k ≠ 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ η : ℝ, 0 < η → ∃ e : selfAdjoint A,
      ‖e‖ ≤ L ∧
      IsSelfAdjoint (signedSquare (β k) e : A) ∧
      0 ≤ sigma (β k) • (signedSquare (β k) e : A) ∧
      ‖(signedSquare (β k) e : A)‖ ≤ L^2 ∧
      Real.sqrt (β (square (signedSquare (β k) e - k))) < η := by
  obtain ⟨φ, hφ, hφβ, huniq, H, hN, hI, hC, π, Ω, hn, hcyc, hrep, hm, hirr⟩ :=
    D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS.actual_pure_gns β hβ hpure
  letI := hN
  letI := hI
  letI := hC
  obtain ⟨T, hT, hTO⟩ := signed_endpoint π Ω β hm k hr
  obtain ⟨L, hL, happ⟩ := bounded_strong_lift π hirr T hT
  refine ⟨L, hL.le, ?_⟩
  intro η hη
  let δ : ℝ := η / (L + 1)
  have hδ : 0 < δ := div_pos hη (by linarith)
  obtain ⟨e, he, hx, hy⟩ := happ Ω (T Ω) δ hδ
  let E := π (e : A)
  have hE : ‖E‖ ≤ L := (NonUnitalStarAlgHom.norm_apply_le π (e : A)).trans he
  have herr : ‖E (E Ω) - T (T Ω)‖ < η := by
    have hid : E (E Ω) - T (T Ω) =
        E (E Ω - T Ω) + (E (T Ω) - T (T Ω)) := by simp only [map_sub]; abel
    rw [hid]
    calc
      _ ≤ ‖E (E Ω - T Ω)‖ + ‖E (T Ω) - T (T Ω)‖ := norm_add_le _ _
      _ ≤ L * ‖E Ω - T Ω‖ + ‖E (T Ω) - T (T Ω)‖ :=
        add_le_add (ContinuousLinearMap.le_of_opNorm_le E hE _) le_rfl
      _ < L * δ + δ := add_lt_add (mul_lt_mul_of_pos_left hx hL) hy
      _ = η := by dsimp [δ]; field_simp
  refine ⟨e, he, (signedSquare (β k) e).property,
    signedSquare_cone _ _, signedSquare_norm _ _ hL.le he, ?_⟩
  rw [square_reading β π Ω hm]
  have hid : π ((signedSquare (β k) e - k : selfAdjoint A) : A) Ω =
      sigma (β k) • (E (E Ω) - T (T Ω)) := by
    have hsign : sigma (β k) • T (T Ω) = π (k : A) Ω := by
      rw [hTO, smul_smul, sigma_sq, one_smul]
    change π.toAlgHom (sigma (β k) • ((e : A)^2) - (k : A)) Ω = _
    rw [map_sub, π.toAlgHom.map_smul_of_tower, map_pow, pow_two]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, smul_sub, hsign, E]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, sigma_abs, one_mul]
  exact herr

end D5.S3.Quantum.Algebra.StateApproximation.UniformSignedSquare
