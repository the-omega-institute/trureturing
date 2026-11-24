import D5.S3.Geometry.AdS3LoxodromicQuotient.Compactification

/-! The complex lift of the loxodromic boundary torus and its two periods. -/

noncomputable section
set_option autoImplicit false

open Function Metric Set Topology

namespace D5.S3.Geometry.AdS3LoxodromicQuotient

namespace Loxodromic

variable (g : Loxodromic)

private def expBoundaryPoint (z : ℂ) : CompactifiedCover :=
  ⟨(Function.Periodic.qParam 1 z, 0), le_rfl, fun h =>
    Function.Periodic.qParam_ne_zero (h := 1) z (congrArg (fun p : ℂ × ℝ => p.1) h)⟩

/-- The literal boundary lift sends `z` to the orbit of `(exp (2πiz), 0)`. -/
def boundaryLift (z : ℂ) : g.Boundary :=
  ⟨Quotient.mk g.compactOrbitSetoid (expBoundaryPoint z), (g.isBoundary_mk _).2 rfl⟩

theorem continuous_boundaryLift : Continuous g.boundaryLift := by
  have hx : Continuous expBoundaryPoint :=
    ((Function.Periodic.continuous_qParam (h := 1)).prodMk continuous_const).subtype_mk _
  exact (g.compactQuotientProjection_isOpenQuotientMap.continuous.comp hx).subtype_mk _

theorem surjective_boundaryLift : Surjective g.boundaryLift := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.val
  have hp : g.IsBoundary (Quotient.mk g.compactOrbitSetoid x) := by
    rw [hx]
    exact q.property
  have hr : x.val.2 = 0 := (g.isBoundary_mk x).mp hp
  have hz : x.val.1 ≠ 0 := fun he => x.property.2 (Prod.ext he hr)
  refine ⟨Function.Periodic.invQParam 1 x.val.1, Subtype.ext ?_⟩
  change Quotient.mk g.compactOrbitSetoid
    (expBoundaryPoint (Function.Periodic.invQParam 1 x.val.1)) = q.val
  refine (congrArg (Quotient.mk g.compactOrbitSetoid)
    (Subtype.ext (Prod.ext ?_ hr.symm))).trans hx
  exact Function.Periodic.qParam_right_inv one_ne_zero hz

private theorem qParam_one_eq_exp (z : ℂ) :
    Function.Periodic.qParam 1 z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := by
  simp [Function.Periodic.qParam]

private theorem ofTau_compactAct_expBoundaryPoint (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) (z : ℂ) :
    (ofTau τ hτ).compactAct n (expBoundaryPoint z) = expBoundaryPoint (z + (n : ℂ) * τ) := by
  apply Subtype.ext
  rw [compactAct_val]
  refine Prod.ext ?_ (mul_zero _)
  change (ofTau τ hτ).multiplier n * Function.Periodic.qParam 1 z =
    Function.Periodic.qParam 1 (z + (n : ℂ) * τ)
  rw [ofTau_multiplier, qParam_one_eq_exp, qParam_one_eq_exp, ← Complex.exp_int_mul,
    ← Complex.exp_add]
  congr 1
  ring

/-- The boundary seen in the complex lift has precisely the lattice periods `1` and `τ`. -/
theorem boundaryLift_eq_iff (τ : ℂ) (hτ : 0 < τ.im) (z w : ℂ) :
    (ofTau τ hτ).boundaryLift z = (ofTau τ hτ).boundaryLift w ↔
      ∃ m n : ℤ, z - w = (m : ℂ) + (n : ℂ) * τ := by
  have horbit :
      (ofTau τ hτ).boundaryLift z = (ofTau τ hτ).boundaryLift w ↔
        ∃ n : ℤ, expBoundaryPoint (w + (n : ℂ) * τ) = expBoundaryPoint z := by
    constructor
    · intro h
      have hrel : (ofTau τ hτ).compactOrbitSetoid (expBoundaryPoint z) (expBoundaryPoint w) :=
        Quotient.exact (congrArg Subtype.val h)
      obtain ⟨n, hn⟩ := ((ofTau τ hτ).compactOrbitSetoid_iff _ _).mp hrel
      exact ⟨n, (ofTau_compactAct_expBoundaryPoint τ hτ n w).symm.trans hn⟩
    · rintro ⟨n, hn⟩
      apply Subtype.ext
      apply Quotient.sound
      exact ((ofTau τ hτ).compactOrbitSetoid_iff _ _).mpr
        ⟨n, (ofTau_compactAct_expBoundaryPoint τ hτ n w).trans hn⟩
  rw [horbit]
  constructor
  · rintro ⟨n, hn⟩
    have he : Function.Periodic.qParam 1 z = Function.Periodic.qParam 1 (w + (n : ℂ) * τ) :=
      congrArg (fun p : CompactifiedCover => p.val.1) hn.symm
    rw [qParam_one_eq_exp, qParam_one_eq_exp] at he
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    have hscaled : (2 * (Real.pi : ℂ) * Complex.I) * z =
        (2 * (Real.pi : ℂ) * Complex.I) * (w + (m : ℂ) + (n : ℂ) * τ) := by
      rw [hm]
      ring
    have hz := mul_left_cancel₀ Complex.two_pi_I_ne_zero hscaled
    exact ⟨m, n, by rw [hz]; ring⟩
  · rintro ⟨m, n, h⟩
    have hz : z = w + (m : ℂ) + (n : ℂ) * τ := by
      calc
        z = w + (z - w) := by ring
        _ = _ := by rw [h]; ring
    refine ⟨n, Subtype.ext (Prod.ext ?_ rfl)⟩
    change Function.Periodic.qParam 1 (w + (n : ℂ) * τ) = Function.Periodic.qParam 1 z
    rw [qParam_one_eq_exp, qParam_one_eq_exp]
    symm
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨m, by rw [hz]; ring⟩

end Loxodromic

end D5.S3.Geometry.AdS3LoxodromicQuotient
