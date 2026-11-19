/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeSpectrum
   mirror-E: none(waiver:algebraic-original-orbifold-relative-spectrum)
   anchors: []
   utility: none
   digest: The native ghost-number-one BRST spectrum at every integral hyperbolic momentum. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet

/-! The native relative BRST quotient at zero momentum and above the shell cutoff,
combined with the nonzero on-shell quartet to give the complete dimension formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRelativeSpectrum

open OriginalOrbifoldCriticalMatter OriginalOrbifoldRelativeMassShell
open OriginalOrbifoldRelativeNull OriginalOrbifoldRelativeQuartet
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private def coordinateNumber : Module.End ℂ (ShellIndex → ℂ) where
  toFun x k := (ghostNumber k : ℂ) * x k
  map_add' x y := by
    funext k
    exact mul_add _ _ _
  map_smul' c x := by
    funext k
    change (ghostNumber k : ℂ) * (c * x k) = c * ((ghostNumber k : ℂ) * x k)
    exact mul_left_comm _ _ _

private theorem shellNumber_conjugate (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0)
    (x : relativeMassShell a) :
    shellCoordinates a ha (shellNumber a x) = coordinateNumber (shellCoordinates a ha x) := by
  let B := shellBasis a ha
  let e := shellCoordinates a ha
  have h : e.toLinearMap.comp (shellNumber a) = coordinateNumber.comp e.toLinearMap := by
    apply B.ext
    intro k
    have hB : shellNumber a (B k) = (ghostNumber k : ℂ) • B k := by
      apply Subtype.ext
      change VirasoroBRST.number (V := Matter) (B k : State) =
        (ghostNumber k : ℂ) • (B k : State)
      rw [shellBasis_coe]
      exact ghostNumber_shellVector a k
    change e (shellNumber a (B k)) = coordinateNumber (e (B k))
    rw [hB, e.map_smul]
    funext j
    change (ghostNumber k : ℂ) * B.equivFun (B k) j =
      (ghostNumber j : ℂ) * B.equivFun (B k) j
    rw [B.equivFun_self]
    by_cases hkj : k = j <;> simp [hkj]
  exact LinearMap.congr_fun h x

private abbrev zeroCoordinates := shellCoordinates (0 : UCharge)
  (LatticePositiveEnergy.chargeEnergy_zero hyperbolicData)

private theorem differential_zero : differential (0 : UCharge) = 0 := by
  apply LinearMap.ext
  intro x
  apply zeroCoordinates.injective
  change zeroCoordinates (differential 0 x) = zeroCoordinates (0 : relativeMassShell 0)
  rw [zeroCoordinates.map_zero,
    differential_conjugate 0 (LatticePositiveEnergy.chargeEnergy_zero hyperbolicData) x]
  funext k
  rcases k with u | (i | u) <;> simp only [coordinateDifferential, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.zero_apply, Int.cast_zero, zero_mul, neg_zero, sub_zero]

private theorem cycles_zero : ghostOneCycles (0 : UCharge) = ghostSector 0 1 := by
  rw [ghostOneCycles, differential_zero, LinearMap.ker_zero, inf_top_eq]

private theorem boundaries_zero : ghostOneBoundaries (0 : UCharge) = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  ext x : 1
  apply Subtype.ext
  change differential (0 : UCharge) (x : relativeMassShell 0) = 0
  rw [differential_zero, LinearMap.zero_apply]

private theorem mem_ghostOneCycles_zero_iff (x : relativeMassShell (0 : UCharge)) :
    x ∈ ghostOneCycles (0 : UCharge) ↔
      zeroCoordinates x (.inl ()) = 0 ∧ zeroCoordinates x (.inr (.inr ())) = 0 := by
  rw [cycles_zero, Module.End.mem_eigenspace_iff, Int.cast_one, one_smul]
  have h (k : ShellIndex) : zeroCoordinates (shellNumber 0 x) k =
      (ghostNumber k : ℂ) * zeroCoordinates x k :=
    congrFun (shellNumber_conjugate 0 _ x) k
  constructor
  · intro hx
    rw [hx] at h
    refine ⟨?_, ?_⟩
    · simpa [ghostNumber] using h (.inl ())
    · have ht := h (.inr (.inr ()))
      norm_num [ghostNumber] at ht
      linear_combination -ht
  · rintro ⟨hb, ht⟩
    apply zeroCoordinates.injective
    funext k
    rw [h]
    rcases k with ⟨⟩ | (i | ⟨⟩) <;> simp [ghostNumber, hb, ht]

private def extendMiddle (y : Fin 2 → ℂ) : ShellIndex → ℂ
  | .inl _ => 0
  | .inr (.inl i) => y i
  | .inr (.inr _) => 0

private def zeroCycleCoordinates : ghostOneCycles (0 : UCharge) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x i := zeroCoordinates x (.inr (.inl i))
  invFun y := ⟨zeroCoordinates.symm (extendMiddle y),
    (mem_ghostOneCycles_zero_iff _).mpr (by simp [extendMiddle])⟩
  left_inv x := by
    obtain ⟨hb, ht⟩ := (mem_ghostOneCycles_zero_iff _).mp x.property
    apply Subtype.ext
    apply zeroCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    rcases k with ⟨⟩ | (i | ⟨⟩) <;> simp [extendMiddle, hb, ht]
  right_inv y := by
    funext i
    change zeroCoordinates (zeroCoordinates.symm (extendMiddle y)) (.inr (.inl i)) = y i
    rw [LinearEquiv.apply_symm_apply]
    rfl
  map_add' x y := by
    funext i
    change zeroCoordinates ((x : relativeMassShell 0) + y) (.inr (.inl i)) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    funext i
    change zeroCoordinates (c • (x : relativeMassShell 0)) (.inr (.inl i)) = _
    rw [map_smul]
    rfl

/-- At zero momentum the actual quotient is the pair of middle coordinates of the null shell. -/
def ghostOneCohomologyEquiv_zero : GhostOneCohomology (0 : UCharge) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  ((ghostOneBoundaries 0).quotEquivOfEqBot boundaries_zero).trans zeroCycleCoordinates

theorem ghostOneCohomologyEquiv_zero_apply_mk (x : ghostOneCycles (0 : UCharge)) (i : Fin 2) :
    ghostOneCohomologyEquiv_zero (Submodule.Quotient.mk x) i =
      shellCoordinates 0 (LatticePositiveEnergy.chargeEnergy_zero hyperbolicData) x
        (.inr (.inl i)) := by
  change zeroCycleCoordinates
    ((ghostOneBoundaries 0).quotEquivOfEqBot boundaries_zero (Submodule.Quotient.mk x)) i = _
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  rfl

/-- Above the mass-shell cutoff the actual ghost-one quotient is trivial. -/
theorem ghostOneCohomology_subsingleton_of_one_lt (a : UCharge)
    (ha : 1 < chargeEnergy hyperbolicData a) : Subsingleton (GhostOneCohomology a) := by
  let _ : Subsingleton (relativeMassShell a) :=
    Submodule.subsingleton_iff_eq_bot.mpr (relativeMassShell_eq_bot_of_one_lt a ha)
  let _ : Subsingleton (ghostOneCycles a) := inferInstance
  infer_instance

/-- The dimension at each integral momentum, with the exceptional zero sector retained. -/
theorem ghostOneCohomology_finrank (a : UCharge) :
    Module.finrank ℂ (GhostOneCohomology a) =
      if a = 0 then 2
      else if a 0 * a 1 ≤ 1 then Module.finrank ℂ (orbifoldGrade (1 - a 0 * a 1).toNat)
      else 0 := by
  classical
  by_cases hz : a = 0
  · subst a
    rw [ite_eq_left rfl, ghostOneCohomologyEquiv_zero.finrank_eq, Module.finrank_fin_fun]
  · rw [ite_eq_right hz]
    by_cases he : a 0 * a 1 ≤ 1
    · have hcut : massShellCutoff hyperbolicData a = (1 - a 0 * a 1).toNat := by
        rw [massShellCutoff, hyperbolic_chargeEnergy a]
      rw [ite_eq_left he,
        (ghostOneCohomologyEquiv a hz ((hyperbolic_chargeEnergy a).trans_le he)).finrank_eq, hcut]
    · rw [ite_eq_right he]
      let _ := ghostOneCohomology_subsingleton_of_one_lt a
        ((hyperbolic_chargeEnergy a).symm ▸ lt_of_not_ge he)
      exact Module.finrank_zero_of_subsingleton

#print axioms ghostOneCohomologyEquiv_zero
#print axioms ghostOneCohomologyEquiv_zero_apply_mk
#print axioms ghostOneCohomology_subsingleton_of_one_lt
#print axioms ghostOneCohomology_finrank

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeSpectrum
