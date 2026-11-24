import D5.S3.Geometry.AdS3LoxodromicQuotient
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.LocalAtTarget

/-! The geometric boundary marking of a Euclidean AdS₃ solid-torus filling under
the modular action on its upper-half-plane parameter. -/

noncomputable section

set_option autoImplicit false

open Function Set Topology
open scoped MatrixGroups UpperHalfPlane

namespace D5.S3.Geometry.AdS3LoxodromicQuotient.Loxodromic

/-- The boundary lift is open and quotient. The exponential first maps onto the
punctured plane. Height-zero points form the full preimage of the boundary
under the compactified orbit projection. -/
theorem boundaryLift_isOpenQuotientMap (g : Loxodromic) : IsOpenQuotientMap g.boundaryLift := by
  let boundary : Set g.CompactifiedQuotient := {q | g.IsBoundary q}
  let q : CompactifiedCover → g.CompactifiedQuotient := Quotient.mk g.compactOrbitSetoid
  let e : {z : ℂ // z ≠ 0} ≃ₜ q ⁻¹' boundary := {
    toFun z := ⟨⟨(z, 0), le_rfl, fun h => z.property (congrArg Prod.fst h)⟩, rfl⟩
    invFun p := ⟨p.val.val.1, fun h =>
      p.val.property.2 (Prod.ext h ((g.isBoundary_mk p.val).mp p.property))⟩
    left_inv _ := rfl
    right_inv p :=
      Subtype.ext (Subtype.ext (Prod.ext rfl ((g.isBoundary_mk p.val).mp p.property).symm))
    continuous_toFun :=
      (((continuous_subtype_val.prodMk continuous_const).subtype_mk _).subtype_mk _)
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  }
  let expLift (z : ℂ) : {u : ℂ // u ≠ 0} :=
    ⟨Periodic.qParam 1 z, Periodic.qParam_ne_zero (h := 1) z⟩
  have hexp : IsOpenMap expLift := by
    have hNZ : IsOpen ({z : ℂ | z ≠ 0} : Set ℂ) := isClosed_singleton.isOpen_compl
    apply hNZ.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    have hscale : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    simpa only [expLift, comp_def, Periodic.qParam, Complex.ofReal_one, div_one,
      Homeomorph.coe_mulLeft₀] using
      Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ hscale).isOpenMap
  have hcomp : g.boundaryLift = (boundary.restrictPreimage q) ∘ e ∘ expLift := rfl
  refine ⟨g.surjective_boundaryLift, g.continuous_boundaryLift, ?_⟩
  rw [hcomp]
  exact (g.compactQuotientProjection_isOpenQuotientMap.restrictPreimage boundary).isOpenMap.comp
    (e.isOpenMap.comp hexp)

/-- The filling whose boundary parameter is the given upper-half-plane point. -/
abbrev modularFilling (τ : ℍ) : Loxodromic := ofTau (τ : ℂ) τ.im_pos

/-- The complex factor by which the modular boundary map multiplies the cover. -/
def modularFactor (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)

variable (γ : SL(2, ℤ)) (τ : ℍ)

theorem modularFactor_ne_zero : modularFactor γ τ ≠ 0 := by
  simpa [modularFactor, UpperHalfPlane.denom] using
    UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ

/-- The image of the period 1 in the target's ordered basis (1, τ). -/
theorem one_mul_modularFactor :
    (1 : ℂ) * modularFactor γ τ = (γ 1 1 : ℂ) + (γ 1 0 : ℂ) * (τ : ℂ) := by
  rw [one_mul, modularFactor, add_comm]

/-- The image of the period γ • τ in the target's ordered basis (1, τ). -/
theorem smul_mul_modularFactor :
    ((γ • τ : ℍ) : ℂ) * modularFactor γ τ =
      (γ 0 1 : ℂ) + (γ 0 0 : ℂ) * (τ : ℂ) := by
  have h : ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) / modularFactor γ τ := by
    simpa [modularFactor] using UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  rw [h, div_mul_cancel₀ _ (modularFactor_ne_zero γ τ), add_comm]

private theorem modularPeriod (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * ((γ • τ : ℍ) : ℂ)) * modularFactor γ τ =
      ((γ 1 1 * m + γ 0 1 * n : ℤ) : ℂ) +
        ((γ 1 0 * m + γ 0 0 * n : ℤ) : ℂ) * (τ : ℂ) := by
  rw [add_mul, mul_assoc, smul_mul_modularFactor]
  have h := one_mul_modularFactor γ τ
  rw [one_mul] at h
  rw [h]
  push_cast
  ring

/-- Cover multiplication preserves and reflects the fibers of the two geometric
boundary lifts. On integral period coordinates its matrix has determinant one. -/
theorem modularBoundaryLift_eq_iff (z w : ℂ) :
    (modularFilling (γ • τ)).boundaryLift z = (modularFilling (γ • τ)).boundaryLift w ↔
    (modularFilling τ).boundaryLift (z * modularFactor γ τ) =
      (modularFilling τ).boundaryLift (w * modularFactor γ τ) := by
  rw [boundaryLift_eq_iff (γ • τ : ℍ) (γ • τ : ℍ).im_pos z w,
    boundaryLift_eq_iff τ τ.im_pos, ← sub_mul]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨_, _, by rw [h, modularPeriod]⟩
  · rintro ⟨m, n, h⟩
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    let p := γ 0 0 * m - γ 0 1 * n
    let q := γ 1 1 * n - γ 1 0 * m
    have hp : γ 1 1 * p + γ 0 1 * q = m := by
      dsimp [p, q]
      linear_combination m * hdet
    have hq : γ 1 0 * p + γ 0 0 * q = n := by
      dsimp [p, q]
      linear_combination n * hdet
    refine ⟨p, q, mul_right_cancel₀ (modularFactor_ne_zero γ τ) ?_⟩
    rw [h, modularPeriod, hp, hq]

private def modularBoundaryMap :
    C((modularFilling (γ • τ)).Boundary, (modularFilling τ).Boundary) := by
  let g := modularFilling (γ • τ)
  let q : C(ℂ, g.Boundary) := ⟨g.boundaryLift, g.continuous_boundaryLift⟩
  exact g.boundaryLift_isOpenQuotientMap.isQuotientMap.lift (f := q)
    ⟨fun z => (modularFilling τ).boundaryLift (z * modularFactor γ τ),
      (modularFilling τ).continuous_boundaryLift.comp (continuous_id.mul continuous_const)⟩
    (fun {_ _} h => (modularBoundaryLift_eq_iff γ τ _ _).mp h)

private theorem modularBoundaryMap_boundaryLift (z : ℂ) :
    modularBoundaryMap γ τ ((modularFilling (γ • τ)).boundaryLift z) =
      (modularFilling τ).boundaryLift (z * modularFactor γ τ) := by
  let g := modularFilling (γ • τ)
  let q : C(ℂ, g.Boundary) := ⟨g.boundaryLift, g.continuous_boundaryLift⟩
  let f : C(ℂ, (modularFilling τ).Boundary) :=
    ⟨fun z => (modularFilling τ).boundaryLift (z * modularFactor γ τ),
      (modularFilling τ).continuous_boundaryLift.comp (continuous_id.mul continuous_const)⟩
  have hf : FactorsThrough f q :=
    fun {_ _} h => (modularBoundaryLift_eq_iff γ τ _ _).mp h
  change ((g.boundaryLift_isOpenQuotientMap.isQuotientMap.lift (f := q) f hf).comp q) z = f z
  rw [IsQuotientMap.lift_comp]

/-- The modular homeomorphism between the literal height-zero boundaries, induced
by multiplying the complex cover coordinate by cτ + d. -/
def modularBoundaryHomeomorph :
    (modularFilling (γ • τ)).Boundary ≃ₜ (modularFilling τ).Boundary := by
  have hq := (modularFilling (γ • τ)).boundaryLift_isOpenQuotientMap
  have hscaled := (modularFilling τ).boundaryLift_isOpenQuotientMap.comp
    (Homeomorph.mulRight₀ _ (modularFactor_ne_zero γ τ)).isOpenQuotientMap
  have hcomp : modularBoundaryMap γ τ ∘ (modularFilling (γ • τ)).boundaryLift =
      (modularFilling τ).boundaryLift ∘ Homeomorph.mulRight₀ _ (modularFactor_ne_zero γ τ) :=
    funext (modularBoundaryMap_boundaryLift γ τ)
  have hinj : Injective (modularBoundaryMap γ τ) := by
    intro x y h
    obtain ⟨z, rfl⟩ := hq.surjective x
    obtain ⟨w, rfl⟩ := hq.surjective y
    rw [modularBoundaryMap_boundaryLift, modularBoundaryMap_boundaryLift] at h
    exact (modularBoundaryLift_eq_iff γ τ z w).mpr h
  have hsurj : Surjective (modularBoundaryMap γ τ) :=
    Surjective.of_comp (hcomp ▸ hscaled.surjective)
  have hopen : IsOpenMap (modularBoundaryMap γ τ) :=
    hq.isOpenMap_iff.mpr (hcomp ▸ hscaled.isOpenMap)
  exact (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    (modularBoundaryMap γ τ).continuous hopen

/-- The geometric homeomorphism evaluates exactly as the prescribed cover map. -/
theorem modularBoundaryHomeomorph_boundaryLift (z : ℂ) :
    modularBoundaryHomeomorph γ τ ((modularFilling (γ • τ)).boundaryLift z) =
      (modularFilling τ).boundaryLift (z * modularFactor γ τ) :=
  modularBoundaryMap_boundaryLift γ τ z

/-- The restriction of the lift to the real axis traces the boundary of the
geometric meridian disk at longitudinal coordinate zero. -/
theorem boundaryLift_ofReal (g : Loxodromic) (x : ℝ) :
    g.boundaryLift (x : ℂ) = g.meridianCircle 0 (Circle.exp (2 * Real.pi * x)) := by
  apply Subtype.ext
  change Quotient.mk g.compactOrbitSetoid _ = Quotient.mk g.compactOrbitSetoid _
  congr 1
  apply Subtype.ext
  rw [g.compactCoverHomeomorph_symm_val]
  apply Prod.ext
  · change Periodic.qParam 1 (x : ℂ) =
      (Real.exp (0 * Real.log g.rho) : ℂ) * phase (g.theta * 0) *
        (Circle.exp (2 * Real.pi * x) : ℂ)
    simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, mul_zero, phase, Complex.ofReal_zero,
      Complex.exp_zero, one_mul]
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Circle.coe_exp,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    ring
  · change (0 : ℝ) = Real.exp (0 * Real.log g.rho) *
      Real.sqrt (1 - ‖(Circle.exp (2 * Real.pi * x) : ℂ)‖ ^ 2)
    rw [Circle.norm_coe]
    simp

/-- The marked meridian of the filling at γ • τ is the cycle in the target
boundary parameterized by the primitive period cτ + d. -/
theorem modularBoundaryHomeomorph_meridianCircle (x : ℝ) :
    modularBoundaryHomeomorph γ τ
        ((modularFilling (γ • τ)).meridianCircle 0 (Circle.exp (2 * Real.pi * x))) =
      (modularFilling τ).boundaryLift ((x : ℂ) * modularFactor γ τ) := by
  rw [← boundaryLift_ofReal, modularBoundaryHomeomorph_boundaryLift]

/-- The transported meridian is an embedded circle in the target boundary. -/
theorem modularBoundaryHomeomorph_meridianCircle_isEmbedding :
    IsEmbedding (fun u : Circle =>
      modularBoundaryHomeomorph γ τ ((modularFilling (γ • τ)).meridianCircle 0 u)) := by
  let g := modularFilling (γ • τ)
  have h : g.meridianCircle 0 =
      g.boundaryCircleHomeomorph.symm ∘ (fun u : Circle => (u, (0 : AddCircle (1 : ℝ)))) := by
    funext u
    apply g.boundaryCircleHomeomorph.injective
    rw [g.boundaryCircleHomeomorph_meridianCircle, comp_apply, Homeomorph.apply_symm_apply]
    simp
  have he : IsEmbedding (g.meridianCircle 0) := by
    rw [h]
    exact g.boundaryCircleHomeomorph.symm.isEmbedding.comp (isEmbedding_prodMkLeft 0)
  exact (modularBoundaryHomeomorph γ τ).isEmbedding.comp he

/-- The primitive integer pairs are exactly the bottom rows of modular matrices. -/
theorem exists_modular_bottomRow_iff (c d : ℤ) :
    (∃ γ : SL(2, ℤ), γ 1 0 = c ∧ γ 1 1 = d) ↔ Int.gcd c d = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact ⟨fun ⟨γ, hc, hd⟩ => hc ▸ hd ▸ γ.isCoprime_row 1, fun h => h.exists_SL2_row 1⟩

/-- Two completions of a fixed primitive row differ by adding an integer
multiple of the bottom row to the top row. -/
theorem modular_same_bottomRow_iff (γ δ : SL(2, ℤ)) :
    δ 1 = γ 1 ↔ ∃ k : ℤ, δ = ModularGroup.T ^ k * γ := by
  constructor
  · intro h
    have hc := congrFun h 0
    have hd := congrFun h 1
    have hγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have hδ : δ 0 0 * γ 1 1 - δ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two, hc, hd] using δ.det_coe
    have hdiff : (δ 0 0 - γ 0 0) * γ 1 1 - (δ 0 1 - γ 0 1) * γ 1 0 = 0 := by
      linear_combination hδ - hγ
    let k := γ 0 0 * (δ 0 1 - γ 0 1) - γ 0 1 * (δ 0 0 - γ 0 0)
    have ha : δ 0 0 = γ 0 0 + k * γ 1 0 := by
      dsimp [k]
      linear_combination γ 0 0 * hdiff - (δ 0 0 - γ 0 0) * hγ
    have hb : δ 0 1 = γ 0 1 + k * γ 1 1 := by
      dsimp [k]
      linear_combination γ 0 1 * hdiff - (δ 0 1 - γ 0 1) * hγ
    refine ⟨k, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        ModularGroup.coe_T_zpow, ha, hb, hc, hd]
  · rintro ⟨k, rfl⟩
    exact ModularGroup.T_pow_mul_apply_one k γ

/-- The parameterized target meridian depends only on the bottom row. -/
theorem modularBoundaryHomeomorph_meridianCircle_congr
    (δ : SL(2, ℤ)) (h : δ 1 = γ 1) (x : ℝ) :
    modularBoundaryHomeomorph δ τ
        ((modularFilling (δ • τ)).meridianCircle 0 (Circle.exp (2 * Real.pi * x))) =
      modularBoundaryHomeomorph γ τ
        ((modularFilling (γ • τ)).meridianCircle 0 (Circle.exp (2 * Real.pi * x))) := by
  rw [modularBoundaryHomeomorph_meridianCircle, modularBoundaryHomeomorph_meridianCircle]
  simp only [modularFactor, congrFun h 0, congrFun h 1]

end D5.S3.Geometry.AdS3LoxodromicQuotient.Loxodromic
