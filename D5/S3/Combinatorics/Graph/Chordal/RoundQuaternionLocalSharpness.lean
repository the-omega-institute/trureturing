/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict quantitative sharpness and an angular neighborhood for round quaternion reconstruction on four vertices. -/

import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation

/-! A quantitative strict fit near the cyclic quarter turn, and its weighted-variance angular region. -/

noncomputable section

open Real Quaternion
open scoped Quaternion InnerProductSpace

namespace RoundQuaternionLocalSharpness

open RoundQuaternionK4Bounds
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (unitI inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

private def phaseFactor (q : ℂ) : ℂ :=
  Complex.exp ((↑(-Complex.arg (q * (zeta - 1)) / 2) : ℂ) * Complex.I)

private theorem phaseFactor_norm (q : ℂ) : ‖phaseFactor q‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phaseFactor_align (q : ℂ) :
    (phaseFactor q ^ 2 * q) * (zeta - 1) = (↑(√3 * ‖q‖) : ℂ) := by
  let z := q * (zeta - 1)
  let l := phaseFactor q
  change (l ^ 2 * q) * (zeta - 1) = _
  have hs : l ^ 2 = Complex.exp (-(↑(Complex.arg z) * Complex.I)) := by
    rw [pow_two]
    change Complex.exp ((↑(-Complex.arg z / 2) : ℂ) * Complex.I) *
      Complex.exp ((↑(-Complex.arg z / 2) : ℂ) * Complex.I) = _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hz : ‖zeta - 1‖ = √3 := by
    have h3 : (√3 : ℝ)^2 = 3 := Real.sq_sqrt (by norm_num)
    rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Complex.sq_norm,
      Complex.normSq_apply]
    norm_num [zeta, Complex.sub_re, Complex.sub_im]
    nlinarith
  rw [mul_assoc, show q * (zeta - 1) = z by rfl, hs]
  let θ : ℂ := ↑(Complex.arg z) * Complex.I
  calc
    Complex.exp (-θ) * z = Complex.exp (-θ) * (↑‖z‖ * Complex.exp θ) :=
      congrArg (fun v => Complex.exp (-θ) * v) (Complex.norm_mul_exp_arg_mul_I z).symm
    _ = (↑‖z‖ : ℂ) := by
      rw [mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = (↑(√3 * ‖q‖) : ℂ) := by
      congr 1
      rw [show ‖z‖ = ‖q‖ * ‖zeta - 1‖ by exact norm_mul _ _, hz, mul_comm]

private def axisConjugator (l : ℂ) (hl : ‖l‖ = 1) : U :=
  asUnit (quatPair l 0) (by simp [local_geometry.local_normSq_pair, hl])

private theorem phase_coords (l z w : ℂ) (hl : ‖l‖ = 1) (a : U)
    (ha : (a : ℍ[ℝ]) = quatPair z w) :
    (conjugate (axisConjugator l hl) a : ℍ[ℝ]) = quatPair z (l ^ 2 * w) := by
  have h : l.re ^ 2 + l.im ^ 2 = 1 := by
    have hs := Complex.sq_norm l
    rw [hl, Complex.normSq_apply] at hs
    nlinarith
  change quatPair l 0 * (a : ℍ[ℝ]) * star (quatPair l 0) = _
  rw [ha]
  ext <;> simp only [quatPair, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im, pow_two] <;>
    first
    | (ring; done)
    | (linear_combination z.re * h; done)
    | (linear_combination z.im * h; done)

/-- The explicit rim potential uses the Fourier modes after phase normalization and then
transports the result back to the original quaternion coordinates. -/
def quarterLocalPotential (p q : ℂ) : Fin 4 → U :=
  let l := phaseFactor q
  let C := axisConjugator l (phaseFactor_norm q)
  conjugate C⁻¹ ∘ phasedPotential (l ^ 2 * p) (l ^ 2 * q)

private theorem zero_parameters {p q : ℂ} {η : Fin 3 → ℝ} :
    ‖q‖ / 200 + (3/100) * (‖p‖ ^ 2 + etaMax η) = 0 ↔
      p = 0 ∧ q = 0 ∧ η = 0 := by
  constructor
  · intro h
    have hE := local_geometry.local_eta_nonneg η
    have hp : ‖p‖ ^ 2 = 0 := by nlinarith [norm_nonneg q, sq_nonneg ‖p‖]
    have hq : ‖q‖ = 0 := by nlinarith [norm_nonneg q, sq_nonneg ‖p‖]
    have hη : etaMax η = 0 := by nlinarith [norm_nonneg q, sq_nonneg ‖p‖]
    refine ⟨norm_eq_zero.mp (by nlinarith [norm_nonneg p]), norm_eq_zero.mp hq, funext fun j => ?_⟩
    exact abs_eq_zero.mp (le_antisymm ((local_geometry.local_abs_eta η j).trans_eq hη) (abs_nonneg _))
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [etaMax]

private theorem quarter_defect_exact :
    hubMaxDefect (fun _ => unitI) = π / 2 := by
  have hSpoke : roundDist 1 unitI = π / 2 := by
    rw [roundDist, inner_eq_components]
    norm_num [unitI, Real.arccos_zero]
  have hRim : roundDist (unitI * unitI * unitI) 1 = π / 2 := by
    rw [local_geometry.dist_trace, inv_one, mul_one]
    norm_num [unitI, Real.arccos_zero, Submonoid.coe_mul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  simp [hubMaxDefect, hSpoke, hRim]

/-- The exact triangle defect controls the error of the explicit local potential, with a
quantitative improvement for every nonzero Fourier or scalar perturbation. -/
theorem quarterLocal_strictFit (A : Fin 3 → U) (p q : ℂ) (η γ : Fin 3 → ℝ)
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j))
    (hγ : ∀ j, γ j = √(1 - (η j)^2 - ‖transverse p q j‖^2))
    (hγpos : ∀ j, 0 < γ j)
    (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (he : etaMax η ≤ localR) :
    let g := hubGaugedGains A
    let e := hubMaxDefect A
    let φ := quarterLocalPotential p q
    DefectLE g e ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ roundDist (g i j * g j k) (g i k) = e) ∧
    (∀ i j, i ≠ j → cos (cStar * e) + ‖q‖ / 200 + (3/100) * (‖p‖^2 + etaMax η) ≤
      ⟪(g i j : ℍ[ℝ]), (↑((φ i)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ) ∧
    Fits g φ (cStar * e) ∧
    (¬ (p = 0 ∧ q = 0 ∧ η = 0) → ∃ R < cStar * e, Fits g φ R) ∧
    (p = 0 ∧ q = 0 ∧ η = 0 → ∀ ψ R, R < cStar * e → ¬ Fits g ψ R) := by
  let l := phaseFactor q
  let C := axisConjugator l (phaseFactor_norm q)
  let p' := l^2*p
  let q' := l^2*q
  let A' := conjugate C ∘ A
  let φ' := phasedPotential p' q'
  have hl : ‖l‖ = 1 := phaseFactor_norm q
  have hnp : ‖p'‖ = ‖p‖ := by simp [p', norm_mul, norm_pow, hl]
  have hnq : ‖q'‖ = ‖q‖ := by simp [q', norm_mul, norm_pow, hl]
  have hw j : transverse p' q' j = l^2 * transverse p q j := by
    unfold transverse p' q'
    ring
  have hA' j : (A' j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p' q' j) := by
    rw [hw]
    exact phase_coords l _ _ hl (A j) (hA j)
  have hγ' j : γ j = √(1 - (η j)^2 - ‖transverse p' q' j‖^2) := by
    rw [hw, norm_mul, norm_pow, hl, one_pow, one_mul, ← hγ]
  have hphase : q' * (zeta-1) = (↑(√3*‖q'‖) : ℂ) := by
    rw [hnq]
    exact phaseFactor_align q
  have hs i j (hij : i ≠ j) := local_minScore
    (hnp ▸ hp) (hnq ▸ hq) he hγ' hA' hphase i j hij
  have hdef := local_defect_estimates A p q η γ hA hγpos hp hq he
  have hfit := hdef.fit_radius_range
  let δ := ‖q‖/200 + (3/100)*(‖p‖^2 + etaMax η)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity [local_geometry.local_eta_nonneg η]
  have hscore i j (hij : i ≠ j) :
      cos (cStar * hubMaxDefect A) + δ ≤
        ⟪(hubGaugedGains A i j : ℍ[ℝ]),
          (↑((quarterLocalPotential p q i)⁻¹ * quarterLocalPotential p q j) : ℍ[ℝ])⟫_ℝ := by
    have hb := hs i j hij
    rw [hnp, hnq] at hb
    change _ ≤ ⟪(hubGaugedGains A' i j : ℍ[ℝ]), ((φ' i)⁻¹ * φ' j : U)⟫_ℝ at hb
    rw [local_geometry.conjugate_hub] at hb
    rw [show φ' i = conjugate C (quarterLocalPotential p q i) by
      simpa [quarterLocalPotential, Function.comp_apply, inv_inv] using
        (local_geometry.conj_cancel C⁻¹ (φ' i)).symm,
      show φ' j = conjugate C (quarterLocalPotential p q j) by
        simpa [quarterLocalPotential, Function.comp_apply, inv_inv] using
          (local_geometry.conj_cancel C⁻¹ (φ' j)).symm,
      ← local_geometry.conj_inv, ← local_geometry.conj_mul, local_geometry.conj_inner] at hb
    have hb' := hb
    rw [pure_score_estimates.constant_values.1, pure_score_estimates.constant_values.2.2] at hb'
    simpa only [δ, add_assoc] using hdef.score_comparison _
      (by simpa [localAlpha, div_eq_mul_inv, mul_comm, localR] using hb')
  rcases local_geometry.hub_faces A with ⟨hfaces, hattain⟩
  refine ⟨hfaces, hattain, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa only [δ, add_assoc] using hscore i j hij
  · intro i j hij
    exact (local_geometry.score_ge_iff hfit).mpr (le_trans (le_add_of_nonneg_right hδ) (hscore i j hij))
  · intro hn
    exact local_geometry.strict_fit_of_scores hfit (lt_of_le_of_ne hδ (Ne.symm (mt zero_parameters.mp hn))) hscore
  · rintro ⟨rfl, rfl, rfl⟩ ψ R hR hf
    have hA0 : A = fun _ => unitI := by
      funext j
      apply Subtype.ext
      rw [hA, hγ]
      simp [transverse, quatPair, unitI]
    rw [hA0, quarter_defect_exact] at hR
    have hθ : cStar * (π / 2) = quarterError := by
      unfold cStar
      field_simp [Real.pi_ne_zero]
    rw [hθ] at hR
    subst A
    obtain ⟨i, j, hij, hmin⟩ := quarter_turn_sharp.2.2.1 ψ
    exact (not_lt_of_ge (hmin.trans (hf i j hij))) hR

private def chartTheta (a b c : ℝ) : Fin 3 → ℝ := ![a, b, c]

private def chartDir (u v w : ℝ) : Fin 3 → ℍ[ℝ] :=
  ![⟨0, 1, 0, 0⟩, ⟨0, cos u, sin u, 0⟩, ⟨0, cos v, sin v * cos w, sin v * sin w⟩]

private theorem chartDir_re (u v w : ℝ) (j : Fin 3) : (chartDir u v w j).re = 0 := by
  fin_cases j <;> rfl

private theorem chartDir_norm (u v w : ℝ) (j : Fin 3) : ‖chartDir u v w j‖ = 1 := by
  have h : normSq (chartDir u v w j) = 1 := by
    fin_cases j
    · norm_num [chartDir, normSq_def']
    · simp [chartDir, normSq_def'] <;> nlinarith [sin_sq_add_cos_sq u]
    · simp [chartDir, normSq_def'] <;>
        linear_combination (sin v)^2 * sin_sq_add_cos_sq w + sin_sq_add_cos_sq v
  rw [normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg (chartDir u v w j)]

private def chartRim (a b c u v w : ℝ) (j : Fin 3) : U :=
  let θ := chartTheta a b c j
  asUnit (⟨cos θ, 0, 0, 0⟩ + sin θ • chartDir u v w j) (by
    have hn := chartDir_norm u v w j
    have hd : normSq (chartDir u v w j) = 1 := by
      rw [normSq_eq_norm_mul_self, hn, mul_one]
    simp only [normSq_def', chartDir_re] at hd
    simp only [normSq_def', Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul, chartDir_re, mul_zero, zero_add, add_zero]
    linear_combination (sin θ)^2 * hd + sin_sq_add_cos_sq θ)

/-- The three rim gains in the ordered spherical chart, with all angles in radians. -/
def chartGains (a b c u v w : ℝ) : Fin 4 → Fin 4 → U :=
  hubGaugedGains (chartRim a b c u v w)

private theorem chart_sin_cos {θ : ℝ} (hθ : |θ - π / 2| ≤ 17 * π / 900) :
    499 / 500 ≤ sin θ ∧ sin θ ≤ 1 ∧ |cos θ| ≤ localR := by
  have hangle : |θ - π / 2| ≤ (3 / 50 : ℝ) := by linarith [Real.pi_lt_d6]
  have hsq : (θ - π / 2)^2 ≤ (3 / 50 : ℝ)^2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (θ - π / 2)) hangle 2
  refine ⟨?_, sin_le_one _, ?_⟩
  · rw [← cos_sub_pi_div_two]
    linarith [one_sub_sq_div_two_le_cos (x := θ - π / 2)]
  · rw [← abs_neg (cos θ), ← sin_sub_pi_div_two]
    exact (abs_sin_le_abs (x := θ - π / 2)).trans hangle

private theorem chart_chord (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ‖chartDir u v w 0 - chartDir u v w 1‖ ≤ u ∧
    ‖chartDir u v w 0 - chartDir u v w 2‖ ≤ v ∧
    ‖chartDir u v w 1 - chartDir u v w 2‖ ≤ u + v := by
  let d := chartDir u v w
  have h₁ : ‖d 0 - d 1‖ ≤ u := by
    apply (sq_le_sq₀ (norm_nonneg _) hu).mp
    rw [pow_two ‖d 0 - d 1‖, ← normSq_eq_norm_mul_self]
    simp [d, chartDir, normSq_def']
    nlinarith [sin_sq_add_cos_sq u, one_sub_sq_div_two_le_cos (x := u)]
  have h₂ : ‖d 0 - d 2‖ ≤ v := by
    apply (sq_le_sq₀ (norm_nonneg _) hv).mp
    rw [pow_two ‖d 0 - d 2‖, ← normSq_eq_norm_mul_self]
    have he : normSq (d 0 - d 2) = 2 - 2 * cos v := by
      simp [d, chartDir, normSq_def']
      linear_combination (sin v)^2 * sin_sq_add_cos_sq w + sin_sq_add_cos_sq v
    rw [he]
    linarith [one_sub_sq_div_two_le_cos (x := v)]
  refine ⟨h₁, h₂, ?_⟩
  calc
    ‖d 1 - d 2‖ = ‖(d 1 - d 0) + (d 0 - d 2)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖d 1 - d 0‖ + ‖d 0 - d 2‖ := norm_add_le _ _
    _ ≤ u + v := by
      rw [norm_sub_rev (d 1) (d 0)]
      exact add_le_add h₁ h₂

private def chartRotate (C : U) : ℍ[ℝ] →ₗᵢ[ℝ] ℍ[ℝ] where
  toLinearMap := (LinearMap.mulRight ℝ (↑(C⁻¹) : ℍ[ℝ])).comp
    (LinearMap.mulLeft ℝ (↑C : ℍ[ℝ]))
  norm_map' := fun x => by
    simp [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, norm_mul]

/-- The normalized imaginary sum gives an explicit quaternion aligning its axis with I. -/
private theorem chartRotate_axis (x : ℍ[ℝ]) (hx : x.re = 0)
    (hn : ‖x‖ = 1) (hi : 0 < x.imI) :
    ∃ C : U, chartRotate C x = (unitI : ℍ[ℝ]) := by
  let I : ℍ[ℝ] := unitI
  let y := I + x
  have hne : y ≠ 0 := by
    intro h
    have hh := congrArg (fun z : ℍ[ℝ] => z.imI) h
    change 1 + x.imI = 0 at hh
    linarith
  have hnp : 0 < ‖y‖ := norm_pos_iff.mpr hne
  have hx2 : x * x = (-1 : ℍ[ℝ]) := by
    simpa [pow_two, normSq_eq_norm_mul_self, hn] using (sq_eq_neg_normSq.mpr hx)
  have hi2 : I * I = (-1 : ℍ[ℝ]) := by
    ext <;> norm_num [I, unitI, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  have hmul : y * x = I * y := by
    dsimp [y]
    rw [add_mul, mul_add, hx2, hi2, add_comm]
  let z : ℍ[ℝ] := ‖y‖⁻¹ • y
  have hz : ‖z‖ = 1 := by
    simp [z, norm_smul, hnp.ne']
  let C := asUnit z (by rw [normSq_eq_norm_mul_self, hz, mul_one])
  have hzmul : z * x = I * z := by
    simp only [z, smul_mul_assoc, mul_smul_comm, hmul]
  refine ⟨C, ?_⟩
  change z * x * ↑(C⁻¹) = I
  rw [hzmul, mul_assoc]
  change I * ↑(C * C⁻¹) = I
  simp

private theorem chartRotate_real (C : U) (x : ℍ[ℝ]) : (chartRotate C x).re = x.re := by
  change ((C : ℍ[ℝ]) * x * ↑(C⁻¹)).re = x.re
  rw [local_geometry.re_cyclic, local_geometry.re_cyclic]
  change ((↑(C⁻¹ * C) : ℍ[ℝ]) * x).re = x.re
  simp

private theorem chartRotate_scalar (C : U) (r : ℝ) :
    chartRotate C (⟨r, 0, 0, 0⟩ : ℍ[ℝ]) = ⟨r, 0, 0, 0⟩ := by
  rw [show (⟨r, 0, 0, 0⟩ : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) by ext <;> simp,
    map_smul]
  have h : chartRotate C (1 : ℍ[ℝ]) = 1 := by
    change (C : ℍ[ℝ]) * 1 * ↑(C⁻¹) = 1
    rw [mul_one]
    change (↑(C * C⁻¹) : ℍ[ℝ]) = 1
    simp
  rw [h]

private def chartTransverse (x : ℍ[ℝ]) : ℂ := ⟨x.imJ, x.imK⟩

private theorem chartTransverse_sub (x y : ℍ[ℝ]) :
    chartTransverse (x - y) = chartTransverse x - chartTransverse y :=
  Complex.ext (by simp [chartTransverse]) (by simp [chartTransverse])

private theorem chartTransverse_norm (x : ℍ[ℝ]) : ‖chartTransverse x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, pow_two ‖x‖, ← normSq_eq_norm_mul_self]
  simp [chartTransverse, Complex.normSq_apply, normSq_def']
  nlinarith [sq_nonneg x.re, sq_nonneg x.imI]

private theorem chart_variance (s : Fin 3 → ℝ) (x : Fin 3 → ℂ)
    (hs : ∀ j, 499 / 500 ≤ s j ∧ s j ≤ 1)
    (hz : s 0 • x 0 + s 1 • x 1 + s 2 • x 2 = 0) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h01 : ‖x 0 - x 1‖ ≤ u) (h02 : ‖x 0 - x 2‖ ≤ v)
    (h12 : ‖x 1 - x 2‖ ≤ u + v) :
    ‖s 0 • x 0‖^2 + ‖s 1 • x 1‖^2 + ‖s 2 • x 2‖^2 ≤
      (u^2 + v^2 + (u + v)^2) / (2 + 499 / 500) := by
  let S := s 0 + s 1 + s 2
  let V := s 0 * ‖x 0‖^2 + s 1 * ‖x 1‖^2 + s 2 * ‖x 2‖^2
  let K : ℝ := 2 + 499 / 500
  have hpos (j) : 0 < s j := by linarith [(hs j).1]
  have hS : 0 < S := by dsimp [S]; positivity [hpos 0, hpos 1, hpos 2]
  have hK : 0 < K := by norm_num [K]
  have hvard :
      S * V = s 0 * s 1 * ‖x 0 - x 1‖^2 + s 0 * s 2 * ‖x 0 - x 2‖^2 +
        s 1 * s 2 * ‖x 1 - x 2‖^2 := by
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.zero_re, Complex.zero_im] at hr hi
    simp only [S, V, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    linear_combination
      (s 0 * (x 0).re + s 1 * (x 1).re + s 2 * (x 2).re) * hr +
      (s 0 * (x 0).im + s 1 * (x 1).im + s 2 * (x 2).im) * hi
  have hc {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ 1)
      (hb' : b ≤ 1) (hc : 499 / 500 ≤ c) : a * b * K ≤ a + b + c := by
    have hab₁ := mul_le_of_le_one_right ha hb'
    have hab₂ := mul_le_of_le_one_left hb ha'
    have hab₃ := hab₁.trans ha'
    dsimp [K]
    linarith
  have hp (i j : Fin 3) (m : ℝ) (hm : 0 ≤ m) (hd : ‖x i - x j‖ ≤ m)
      (hsum : s i * s j * K ≤ S) :
      s i * s j * ‖x i - x j‖^2 * K ≤ S * m^2 := by
    have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    calc
      _ = s i * s j * K * ‖x i - x j‖^2 := by ring
      _ ≤ s i * s j * K * m^2 := mul_le_mul_of_nonneg_left hd2 (by positivity [hpos i, hpos j])
      _ ≤ S * m^2 := mul_le_mul_of_nonneg_right hsum (by positivity)
  have h0 := hp 0 1 u hu h01 (hc (hpos 0).le (hpos 1).le (hs 0).2 (hs 1).2 (hs 2).1)
  have h1 := hp 0 2 v hv h02 (by
    dsimp [S]
    linarith [hc (hpos 0).le (hpos 2).le (hs 0).2 (hs 2).2 (hs 1).1])
  have h2 := hp 1 2 (u+v) (add_nonneg hu hv) h12 (by
    dsimp [S]
    linarith [hc (hpos 1).le (hpos 2).le (hs 1).2 (hs 2).2 (hs 0).1])
  have hV : V ≤ (u^2 + v^2 + (u+v)^2) / K := by
    rw [le_div_iff₀ hK, ← mul_le_mul_iff_left₀ hS]
    linear_combination h0 + h1 + h2 + K * hvard
  have hsq (j : Fin 3) : ‖s j • x j‖^2 ≤ s j * ‖x j‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos j), mul_pow]
    exact mul_le_mul_of_nonneg_right (by
      simpa [pow_two] using mul_le_of_le_one_right (hpos j).le (hs j).2) (sq_nonneg _)
  exact (add_le_add (add_le_add (hsq 0) (hsq 1)) (hsq 2)).trans hV

private theorem chartFourier (x : Fin 3 → ℂ) (h : x 0 + x 1 + x 2 = 0) :
    ∃ p q : ℂ, (∀ j, transverse p q j = x j) ∧
      3 * (‖p‖^2 + ‖q‖^2) = ‖x 0‖^2 + ‖x 1‖^2 + ‖x 2‖^2 := by
  let t := √3
  let a := (x 0).re
  let b := (x 0).im
  let c := (x 1).re
  let d := (x 1).im
  let p : ℂ := ⟨a/2 + (b+2*d)*t/6, b/2 - (a+2*c)*t/6⟩
  let q : ℂ := ⟨a/2 - (b+2*d)*t/6, b/2 + (a+2*c)*t/6⟩
  have hx : x 2 = -(x 0 + x 1) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm (x 2)] using h
  have ht : t^2 = 3 := sq_sqrt (by norm_num)
  refine ⟨p, q, ?_, ?_⟩
  · intro j
    fin_cases j <;> apply Complex.ext <;>
      simp [p, q, transverse, rimPhase, zeta, t, hx,
        Complex.mul_re, Complex.mul_im, a, b, c, d] <;>
      ring_nf <;> norm_num [Real.sq_sqrt] <;> ring
  · simp only [p, q, Complex.sq_norm, Complex.normSq_apply, hx, Complex.neg_re,
      Complex.neg_im, Complex.add_re, Complex.add_im]
    change _ = a * a + b * b + (c * c + d * d) + (-(a+c) * -(a+c) + -(b+d) * -(b+d))
    ring_nf
    rw [ht]
    ring

private theorem chartRim_center (w : ℝ) :
    chartRim (π / 2) (π / 2) (π / 2) 0 0 w = fun _ => unitI := by
  funext j
  apply Subtype.ext
  fin_cases j <;> ext <;> simp [chartRim, chartTheta, chartDir, asUnit, unitI]

private theorem chart_center (w : ℝ) :
    chartGains (π / 2) (π / 2) (π / 2) 0 0 w = quarterGains := by
  rw [chartGains, chartRim_center]
  rfl

private theorem chartAlignment (a b c u v w : ℝ)
    (ha : |a - π/2| ≤ 17*π/900) (hb : |b - π/2| ≤ 17*π/900)
    (hc : |c - π/2| ≤ 17*π/900)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v < π/2)
    (hsize : u^2 + v^2 + (u+v)^2 ≤ (4497/500) * localR^2) :
    ∃ C : U, ∃ p q : ℂ, ∃ η : Fin 3 → ℝ,
      (∀ j, (↑(conjugate C (chartRim a b c u v w j)) : ℍ[ℝ]) =
        quatPair ⟨-η j, √(1 - (η j)^2 - ‖transverse p q j‖^2)⟩ (transverse p q j)) ∧
      (∀ j, 0 < √(1 - (η j)^2 - ‖transverse p q j‖^2)) ∧
      ‖p‖ ≤ localR ∧ ‖q‖ ≤ localR ∧ etaMax η ≤ localR ∧
      (p = 0 ∧ q = 0 ∧ η = 0 →
        a = π/2 ∧ b = π/2 ∧ c = π/2 ∧ u = 0 ∧ v = 0) := by
  let θ := chartTheta a b c
  let d := chartDir u v w
  let s : Fin 3 → ℝ := fun j => sin (θ j)
  let η : Fin 3 → ℝ := fun j => -cos (θ j)
  let m := s 0 • d 0 + s 1 • d 1 + s 2 • d 2
  have hθ (j : Fin 3) : |θ j - π / 2| ≤ 17 * π / 900 := by
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  have hs (j : Fin 3) : 499/500 ≤ s j ∧ s j ≤ 1 := by
    obtain ⟨hl, hu, _⟩ := chart_sin_cos (hθ j)
    exact ⟨hl, hu⟩
  have hspos (j) : 0 < s j := by linarith [(hs j).1]
  have hη (j : Fin 3) : |η j| ≤ localR := by
    simpa [η] using (chart_sin_cos (hθ j)).2.2
  obtain ⟨h01, h02, h12⟩ := chart_chord u v w hu hv
  have hsmall : u + v < 1 := by
    by_contra! h
    have hh := mul_nonneg (show 0 ≤ u + v - 1 by linarith)
      (show 0 ≤ u + v + 1 by linarith)
    norm_num [localR] at hsize
    nlinarith only [hsize, hh, sq_nonneg u, sq_nonneg v]
  have hd (i j : Fin 3) : ‖d i - d j‖ ≤ 1 := by
    have h₁ := h01.trans (show u ≤ 1 by linarith)
    have h₂ := h02.trans (show v ≤ 1 by linarith)
    have h₃ := h12.trans hsmall.le
    fin_cases i <;> fin_cases j
    · simp
    · exact h₁
    · exact h₂
    · rw [norm_sub_rev]
      exact h₁
    · simp
    · exact h₃
    · rw [norm_sub_rev]
      exact h₂
    · rw [norm_sub_rev]
      exact h₃
    · simp
  have hdot (i j : Fin 3) : 0 < ⟪d i, d j⟫_ℝ := by
    have hq := pow_le_pow_left₀ (norm_nonneg (d i - d j)) (hd i j) 2
    have hn (k) : ‖d k‖ = 1 := chartDir_norm u v w k
    rw [norm_sub_sq_real, hn i, hn j] at hq
    linarith
  have hm (j : Fin 3) : 0 < ⟪m, d j⟫_ℝ := by
    simp only [m, inner_add_left, real_inner_smul_left]
    positivity [hspos 0, hspos 1, hspos 2, hdot 0 j, hdot 1 j, hdot 2 j]
  have hm0 : m ≠ 0 := by
    intro he
    simpa [he] using hm 0
  have hmr : m.re = 0 := by simp [m, d, chartDir_re]
  have hmi : 0 < m.imI := by
    simpa [d, chartDir,
      D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_eq_components] using hm 0
  let axis := ‖m‖⁻¹ • m
  have hmn : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hAxisNorm : ‖axis‖ = 1 := by
    simp [axis, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmn, hmn.ne']
  obtain ⟨C, hC⟩ := chartRotate_axis axis (by simp [axis, hmr]) hAxisNorm
    (by simp [axis]; positivity [hmi])
  let rot := chartRotate C
  let f : Fin 3 → ℍ[ℝ] := fun j => rot (d j)
  let x : Fin 3 → ℂ := fun j => chartTransverse (f j)
  have hM : rot m = ‖m‖ • (unitI : ℍ[ℝ]) := by
    change chartRotate C m = _
    rw [← hC, map_smul]
    simp [axis, smul_smul, hmn.ne']
  have hmcoord : s 0 • f 0 + s 1 • f 1 + s 2 • f 2 = ‖m‖ • (unitI : ℍ[ℝ]) := by
    simpa [rot, m, f, map_smul, map_add] using hM
  have hsum : s 0 • x 0 + s 1 • x 1 + s 2 • x 2 = 0 := by
    apply Complex.ext
    · simpa [x, chartTransverse, unitI] using congrArg (fun z : ℍ[ℝ] => z.imJ) hmcoord
    · simpa [x, chartTransverse, unitI] using congrArg (fun z : ℍ[ℝ] => z.imK) hmcoord
  have hfpos (j : Fin 3) : 0 < (f j).imI := by
    have hdot := hm j
    rw [← (chartRotate C).inner_map_map, show chartRotate C m = ‖m‖ • (unitI : ℍ[ℝ])
      from hM, real_inner_smul_left] at hdot
    change 0 < ‖m‖ * ⟪(unitI : ℍ[ℝ]), f j⟫_ℝ at hdot
    have hh := pos_of_mul_pos_right hdot hmn.le
    simpa [unitI, D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_eq_components] using hh
  have hpair (i j : Fin 3) : ‖x i - x j‖ ≤ ‖d i - d j‖ := by
    rw [show x i - x j = chartTransverse (rot (d i - d j)) by
      simp [x, f, rot, map_sub, chartTransverse_sub]]
    exact (chartTransverse_norm _).trans ((chartRotate C).norm_map _).le
  obtain ⟨p, q, hpq, hvard⟩ := chartFourier (fun j => s j • x j) hsum
  have hvbd := chart_variance s x hs hsum u v hu hv
    ((hpair 0 1).trans h01) ((hpair 0 2).trans h02) ((hpair 1 2).trans h12)
  rw [← hvard] at hvbd
  have hpqbd : ‖p‖^2 + ‖q‖^2 ≤ localR^2 := by
    norm_num [localR] at hsize hvbd ⊢
    linarith
  have hA (j : Fin 3) : (↑(conjugate C (chartRim a b c u v w j)) : ℍ[ℝ]) =
      ⟨cos (θ j), 0, 0, 0⟩ + s j • f j := by
    change chartRotate C (⟨cos (θ j), 0, 0, 0⟩ + s j • d j) = _
    rw [map_add, chartRotate_scalar, map_smul]
  have hftr (j : Fin 3) : chartTransverse (↑(conjugate C (chartRim a b c u v w j)) : ℍ[ℝ]) =
      transverse p q j := by
    rw [hA, hpq]
    exact Complex.ext (by simp [x, chartTransverse]) (by simp [x, chartTransverse])
  have hfre (j) : (f j).re = 0 := by
    dsimp [f, rot]
    rw [chartRotate_real, chartDir_re]
  have hroot (j : Fin 3) : √(1 - (η j)^2 - ‖transverse p q j‖^2) = s j * (f j).imI := by
    have hn : normSq (↑(conjugate C (chartRim a b c u v w j)) : ℍ[ℝ]) = 1 := by
      rw [normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, mul_one]
    have hd : 1 - (η j)^2 - ‖transverse p q j‖^2 = (s j * (f j).imI)^2 := by
      rw [← hftr, hA, Complex.sq_norm]
      rw [hA, normSq_def'] at hn
      simp only [Complex.normSq_apply, chartTransverse, Quaternion.re_add, Quaternion.re_smul,
        Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add, Quaternion.imI_smul,
        Quaternion.imJ_smul, Quaternion.imK_smul, hfre, smul_eq_mul, mul_zero, add_zero,
        zero_add, η, neg_sq] at hn ⊢
      nlinarith
    rw [hd, sqrt_sq (mul_pos (hspos j) (hfpos j)).le]
  refine ⟨C, p, q, η, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hA, hroot, hpq]
    ext <;> simp [quatPair, x, chartTransverse, η, hfre]
  · intro j
    rw [hroot]
    exact mul_pos (hspos j) (hfpos j)
  · exact (sq_le_sq₀ (norm_nonneg _) (by norm_num [localR])).mp (by linarith [sq_nonneg ‖q‖])
  · exact (sq_le_sq₀ (norm_nonneg _) (by norm_num [localR])).mp (by linarith [sq_nonneg ‖p‖])
  · exact max_le (hη 0) (max_le (hη 1) (hη 2))
  · rintro ⟨hp, hq, he⟩
    have hAngle (j : Fin 3) : θ j = π/2 := by
      have hzero : η j = 0 := congrFun he j
      change -cos (θ j) = 0 at hzero
      apply strictAntiOn_cos.injOn
      · have hh := abs_le.mp (hθ j)
        exact ⟨by linarith [hh.1, pi_pos], by linarith [hh.2, pi_pos]⟩
      · exact ⟨by positivity, by linarith [pi_pos]⟩
      · simpa using hzero
    have hzero (j : Fin 3) : x j = 0 := by
      have hh : s j • x j = 0 := by simpa [hp, hq, transverse] using (hpq j).symm
      exact (smul_eq_zero.mp hh).resolve_left (hspos j).ne'
    have hfI (j : Fin 3) : f j = (unitI : ℍ[ℝ]) := by
      have hre := hfre j
      have hrj : (f j).imJ = 0 := congrArg Complex.re (hzero j)
      have hri : (f j).imK = 0 := congrArg Complex.im (hzero j)
      have hn : normSq (f j) = 1 := by
        rw [normSq_eq_norm_mul_self, show ‖f j‖ = 1 by
          exact ((chartRotate C).norm_map _).trans (chartDir_norm u v w j), mul_one]
      rw [normSq_def', hre, hrj, hri] at hn
      have hi : (f j).imI = 1 := by nlinarith [hfpos j]
      ext <;> simp [unitI, hre, hrj, hri, hi]
    have hsame (j : Fin 3) : d j = d 0 := by
      exact (chartRotate C).injective ((hfI j).trans (hfI 0).symm)
    have hsinU : sin u = 0 := congrArg (fun z : ℍ[ℝ] => z.imJ) (hsame 1)
    have hsinV : sin v = 0 := by
      have hj : sin v * cos w = 0 := congrArg (fun z : ℍ[ℝ] => z.imJ) (hsame 2)
      have hk : sin v * sin w = 0 := congrArg (fun z : ℍ[ℝ] => z.imK) (hsame 2)
      by_contra hne
      rcases mul_eq_zero.mp hj with h | h
      · exact hne h
      · rcases mul_eq_zero.mp hk with h' | h'
        · exact hne h'
        · have hs := sin_sq_add_cos_sq w
          rw [h, h'] at hs
          norm_num at hs
    exact ⟨hAngle 0, hAngle 1, hAngle 2,
      (sin_eq_zero_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).mp hsinU,
      (sin_eq_zero_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).mp hsinV⟩

/-- The exact maximum triangle defect of the chart gain assignment. -/
def chartMaxDefect (a b c u v w : ℝ) : ℝ :=
  hubMaxDefect (chartRim a b c u v w)

/-- Weighted variance puts each chart point in the strict-fit region. -/
theorem quarterLocal_angularRegion (a b c u v w : ℝ)
    (ha : |a - π/2| ≤ 17*π/900) (hb : |b - π/2| ≤ 17*π/900)
    (hc : |c - π/2| ≤ 17*π/900) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v < π/2)
    (hsize : u^2 + v^2 + (u+v)^2 ≤ (4497/500) * localR^2) :
    let g := chartGains a b c u v w
    let e := chartMaxDefect a b c u v w
    let center := a = π/2 ∧ b = π/2 ∧ c = π/2 ∧ u = 0 ∧ v = 0
    DefectLE g e ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ roundDist (g i j * g j k) (g i k) = e) ∧
    (∃ φ, Fits g φ (cStar * e) ∧ (¬ center → ∃ R < cStar * e, Fits g φ R)) ∧
    (center → ∀ ψ R, R < cStar * e → ¬ Fits g ψ R) := by
  let A := chartRim a b c u v w
  obtain ⟨C, p, q, η, hA, hγpos, hp, hq, he, hz⟩ :=
    chartAlignment a b c u v w ha hb hc hu hv huv hsize
  obtain ⟨_, _, _, hf, hs, _⟩ := quarterLocal_strictFit (conjugate C ∘ A) p q η
    (fun j => √(1-(η j)^2-‖transverse p q j‖^2)) hA (fun _ => rfl) hγpos hp hq he
  rw [local_geometry.conjugate_hubMaxDefect] at hf hs
  let φ := conjugate C⁻¹ ∘ quarterLocalPotential p q
  have transport (R : ℝ) (h : Fits (hubGaugedGains (conjugate C ∘ A))
      (quarterLocalPotential p q) R) : Fits (hubGaugedGains A) φ R := by
    apply (local_geometry.conjugate_fits C (hubGaugedGains A) φ R).mp
    have hg : (fun i j => conjugate C (hubGaugedGains A i j)) =
        hubGaugedGains (conjugate C ∘ A) := by
      funext i j
      exact (local_geometry.conjugate_hub C A i j).symm
    have hφ : conjugate C ∘ φ = quarterLocalPotential p q := by
      funext i
      simpa [φ, Function.comp_apply] using local_geometry.conj_cancel C⁻¹ (quarterLocalPotential p q i)
    rw [hg, hφ]
    exact h
  have faces := local_geometry.hub_faces A
  refine ⟨faces.1, faces.2, ⟨φ, transport _ hf, ?_⟩, ?_⟩
  · intro hn
    obtain ⟨R, hR, hF⟩ := hs (mt hz hn)
    exact ⟨R, hR, transport R hF⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩ ψ R hl hF
    rw [chart_center] at hF
    have hA₀ : chartRim (π/2) (π/2) (π/2) 0 0 w = fun _ => unitI := by
      funext j
      apply Subtype.ext
      fin_cases j <;> ext <;> simp [chartRim, chartTheta, chartDir, asUnit, unitI]
    rw [chartMaxDefect, hA₀, quarter_defect_exact, show cStar * (π / 2) = quarterError by
      unfold cStar
      field_simp [Real.pi_ne_zero]] at hl
    obtain ⟨i, j, hi, hj⟩ := quarter_turn_sharp.2.2.1 ψ
    exact hl.not_ge (hj.trans (hF i j hi))

end RoundQuaternionLocalSharpness
