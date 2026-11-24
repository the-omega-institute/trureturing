/- GID: D5/S3/Geometry/AdS3MarkedFillingCharacter
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech orbifold character as a regularized genus-one sum over marked AdS₃ fillings. -/

import D5.S3.Geometry.AdS3LoxodromicLength
import D5.S3.Geometry.AdS3RademacherFilling
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldRademacherCharacter

/-!
# The genus-one character from marked AdS₃ fillings

Each term starts with the inverse deck multiplier of a loxodromic solid
torus. Nonpolar terms subtract the exponential of the cusp value of the
transformed modulus. The marked meridian circles index the finite cutoffs.
-/

set_option autoImplicit false

open scoped BigOperators Matrix MatrixGroups UpperHalfPlane

namespace D5.S3.Geometry.AdS3MarkedFillingCharacter

open AdS3LoxodromicQuotient (UpperHalfSpace)
open AdS3LoxodromicQuotient.Loxodromic
open AdS3RademacherFilling
open HyperbolicUpperHalfSpace (hyperbolicDist)
open D5.S3.Arith.ModularForms.RademacherVacuum (rademacherCutoff)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries (character)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldRademacherCharacter
  (tendstoLocallyUniformly_rademacherCutoff_sub_twelve_character)

noncomputable section

local notation "κ" => (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

/-- The inverse deck multiplier of the actual modular filling. -/
def rawBoltzmann (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (modularFilling (γ • τ)).multiplier (-1)

theorem rawBoltzmann_eq_exp (γ : SL(2, ℤ)) (τ : ℍ) :
    rawBoltzmann γ τ = Complex.exp (-κ * ((γ • τ : ℍ) : ℂ)) := by
  calc
    rawBoltzmann γ τ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((γ • τ : ℍ) : ℂ)) ^ (-1 : ℤ) :=
      ofTau_multiplier ((γ • τ : ℍ) : ℂ) (γ • τ).im_pos (-1)
    _ = _ := by
      rw [zpow_neg, zpow_one, ← Complex.exp_neg]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul]

/-- The core length measured by the minimum displacement of the deck generator. -/
def coreTranslationLength (γ : SL(2, ℤ)) (τ : ℍ) : ℝ :=
  sInf (Set.range fun x : UpperHalfSpace =>
    hyperbolicDist x ((modularFilling (γ • τ)).act 1 x))

theorem coreTranslationLength_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    coreTranslationLength γ τ = 2 * Real.pi * τ.im / ‖modularFactor γ τ‖ ^ 2 :=
  modular_core_translation_length γ τ

/-- The raw modulus is the exponential of the geometric core length. -/
theorem norm_rawBoltzmann (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖rawBoltzmann γ τ‖ = Real.exp (coreTranslationLength γ τ) := by
  have him : (γ • τ).im = τ.im / ‖modularFactor γ τ‖ ^ 2 := by
    simpa only [ModularGroup.denom_apply, modularFactor, Complex.normSq_eq_norm_sq] using
      ModularGroup.im_smul_eq_div_normSq γ τ
  rw [rawBoltzmann_eq_exp, Complex.norm_exp, coreTranslationLength_eq,
    mul_div_assoc, ← him]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The polar normalization agrees with the reciprocal of the level-one nome. -/
theorem rawBoltzmann_one (τ : ℍ) :
    rawBoltzmann 1 τ = (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
  rw [rawBoltzmann_eq_exp, one_smul, Function.Periodic.qParam, ← Complex.exp_neg]
  simp [neg_mul]

private theorem vacuumExp_add_int (z : ℂ) (k : ℤ) :
    Complex.exp (-κ * (z + (k : ℂ))) = Complex.exp (-κ * z) := by
  have hk : Complex.exp (-κ * (k : ℂ)) = 1 := by
    simpa only [Int.cast_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul,
      mul_comm (2 * (Real.pi : ℂ) * Complex.I) (k : ℂ)] using
      Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [mul_add, Complex.exp_add, hk, mul_one]

private theorem rawBoltzmann_translate (γ : SL(2, ℤ)) (τ : ℍ) (k : ℤ) :
    rawBoltzmann (ModularGroup.T ^ k * γ) τ = rawBoltzmann γ τ := by
  rw [rawBoltzmann_eq_exp, rawBoltzmann_eq_exp, mul_smul, ModularGroup.coe_T_zpow_smul_eq]
  exact vacuumExp_add_int _ k

private theorem rawBoltzmann_neg (γ : SL(2, ℤ)) (τ : ℍ) :
    rawBoltzmann (-γ) τ = rawBoltzmann γ τ := by
  simp only [rawBoltzmann, ModularGroup.SL_neg_smul]

/-- The subtraction is zero in the polar class and the cusp phase elsewhere. -/
def cuspSubtraction (γ : SL(2, ℤ)) : ℂ :=
  if γ 1 0 = 0 then 0 else Complex.exp (-κ * ((γ 0 0 : ℂ) / (γ 1 0 : ℂ)))

/-- Each nonpolar subtraction has unit modulus. -/
theorem norm_cuspSubtraction (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    ‖cuspSubtraction γ‖ = 1 := by
  rw [cuspSubtraction, ite_eq_right hc]
  have h : -κ * ((γ 0 0 : ℂ) / (γ 1 0 : ℂ)) =
      (((-(2 * Real.pi) * ((γ 0 0 : ℝ) / (γ 1 0 : ℝ))) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem cuspSubtraction_translate (γ : SL(2, ℤ)) (k : ℤ) :
    cuspSubtraction (ModularGroup.T ^ k * γ) = cuspSubtraction γ := by
  have hrow := congrFun (ModularGroup.T_pow_mul_apply_one k γ) 0
  simp only [cuspSubtraction, hrow]
  split_ifs with hc
  · rfl
  · have htop : (ModularGroup.T ^ k * γ) 0 0 = γ 0 0 + k * γ 1 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        ModularGroup.coe_T_zpow]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [htop, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_right₀ _ hc']
    exact vacuumExp_add_int _ k

private theorem cuspSubtraction_neg (γ : SL(2, ℤ)) :
    cuspSubtraction (-γ) = cuspSubtraction γ := by
  simp [cuspSubtraction, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

/-- The polar or cusp-subtracted vacuum contribution computed in a completion. -/
def completedVacuumSummand (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  rawBoltzmann γ τ - cuspSubtraction γ

/-- Changing the completion of the same normalized marked filling preserves
both the inverse deck multiplier and the cusp subtraction. -/
theorem fillingWeights_eq_of_fillingIndex_eq {γ δ : SL(2, ℤ)}
    (h : fillingIndex δ = fillingIndex γ) (τ : ℍ) :
    rawBoltzmann δ τ = rawBoltzmann γ τ ∧ cuspSubtraction δ = cuspSubtraction γ := by
  rcases (fillingIndex_eq_iff γ δ).mp h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨rawBoltzmann_translate γ τ k, cuspSubtraction_translate γ k⟩
  · exact ⟨(rawBoltzmann_translate (-γ) τ k).trans (rawBoltzmann_neg γ τ),
      (cuspSubtraction_translate (-γ) k).trans (cuspSubtraction_neg γ)⟩

/-- The filled core length is independent of completion and global sign. -/
theorem coreTranslationLength_eq_of_fillingIndex_eq {γ δ : SL(2, ℤ)}
    (h : fillingIndex δ = fillingIndex γ) (τ : ℍ) :
    coreTranslationLength δ τ = coreTranslationLength γ τ := by
  apply Real.exp_injective
  rw [← norm_rawBoltzmann, ← norm_rawBoltzmann, (fillingWeights_eq_of_fillingIndex_eq h τ).1]

/-- The embedded circle marking distinguishes the normalized fillings. -/
theorem markedMeridianCircle_injective (τ : ℍ) :
    Function.Injective (markedMeridianCircle τ) := by
  intro p q hpq
  apply markedMeridian_injective τ
  funext t
  rw [← markedMeridian_eq τ p p.completion p.completion_c p.completion_d t,
    ← markedMeridian_eq τ q q.completion q.completion_c q.completion_d t]
  exact congrFun hpq (Circle.exp (2 * Real.pi * t))

/-- A filling represented by its normalized embedded meridian on the marked boundary. -/
abbrev MarkedFilling (τ : ℍ) := Set.range (markedMeridianCircle τ)

/-- The geometric marking gives a bijection with the normalized primitive rows. -/
def markedFillingEquiv (τ : ℍ) : FillingIndex ≃ MarkedFilling τ :=
  Equiv.ofInjective _ (markedMeridianCircle_injective τ)

/-- The polar filling together with the strict rectangular cutoff of other fillings. -/
def markedFillingCutoff (τ : ℍ) (N : ℕ) : Finset (MarkedFilling τ) :=
  (insert polarIndex (fillingCutoff N)).map (markedFillingEquiv τ).toEmbedding

/-- The geometric cutoff membership determines a unique normalized representative. -/
theorem mem_markedFillingCutoff_iff (τ : ℍ) (N : ℕ) (m : MarkedFilling τ) :
    m ∈ markedFillingCutoff τ N ↔
      ∃! p : FillingIndex, markedMeridianCircle τ p = m.val ∧
        (p = polarIndex ∨ 0 < p.c ∧ p.c < (N : ℤ) ∧ |p.d| < (N : ℤ) ^ 2) := by
  constructor
  · intro hm
    obtain ⟨p, hp, hpm⟩ := Finset.mem_map.mp hm
    refine ⟨p, ⟨congrArg Subtype.val hpm, ?_⟩, ?_⟩
    · simpa only [Finset.mem_insert, mem_fillingCutoff] using hp
    · intro q hq
      exact markedMeridianCircle_injective τ (hq.1.trans (congrArg Subtype.val hpm).symm)
  · rintro ⟨p, ⟨hpm, hp⟩, _⟩
    apply Finset.mem_map.mpr
    exact ⟨p, by simpa only [Finset.mem_insert, mem_fillingCutoff] using hp, Subtype.ext hpm⟩

/-- The cusp-subtracted vacuum family with the geometric markings as indices. -/
def markedFillingVacuumSummand (τ : ℍ) (m : MarkedFilling τ) : ℂ :=
  completedVacuumSummand ((markedFillingEquiv τ).symm m).completion τ

/-- The geometric summand may be evaluated in any modular representative. -/
theorem markedFillingVacuumSummand_of_matrix (γ : SL(2, ℤ)) (τ : ℍ) :
    markedFillingVacuumSummand τ (markedFillingEquiv τ (fillingIndex γ)) =
      completedVacuumSummand γ τ := by
  have h := fillingWeights_eq_of_fillingIndex_eq (fillingIndex_completion (fillingIndex γ)) τ
  simp only [markedFillingVacuumSummand, Equiv.symm_apply_apply, completedVacuumSummand,
    h.1, h.2]

/-- At each cutoff the geometric sum gives the literal rectangular Rademacher sum. -/
theorem sum_markedFillingCutoff_eq_rademacherCutoff (N : ℕ) (τ : ℍ) :
    (∑ m ∈ markedFillingCutoff τ N, markedFillingVacuumSummand τ m) = rademacherCutoff N τ := by
  have hp : polarIndex ∉ fillingCutoff N := by simp [polarIndex]
  rw [markedFillingCutoff, Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, markedFillingVacuumSummand, Equiv.symm_apply_apply]
  rw [Finset.sum_insert hp, rademacherCutoff_eq_fillingCutoff]
  congr 1
  · simp [completedVacuumSummand, rawBoltzmann_eq_exp, cuspSubtraction, polarIndex]
  · apply Finset.sum_congr rfl
    intro p hp
    have hc : p.c ≠ 0 := (mem_fillingCutoff.mp hp).1.ne'
    simp [completedVacuumSummand, rawBoltzmann_eq_exp, cuspSubtraction, hc]

/-- The strict cutoff sums of the actual marked solid-torus contributions,
after the constant 12 is subtracted, converge locally uniformly to the native
Leech orbifold graded-dimension character. -/
theorem tendstoLocallyUniformly_markedFillingCutoff_sub_twelve_character :
    TendstoLocallyUniformly
      (fun N τ => (∑ m ∈ markedFillingCutoff τ N, markedFillingVacuumSummand τ m) - 12)
      character Filter.atTop := by
  simpa only [sum_markedFillingCutoff_eq_rademacherCutoff] using
    tendstoLocallyUniformly_rademacherCutoff_sub_twelve_character

end

end D5.S3.Geometry.AdS3MarkedFillingCharacter
