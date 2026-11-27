/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedGroundRecognition
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedGroundRecognition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recognition of the cubic momentum charge action from its zero-momentum scalar. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeAction
import Mathlib.LinearAlgebra.DFinsupp

/-!
Bakalov–Kac, arXiv:math/0402315v3, (4.42) and (4.46) give the charge
multiplier and the moving scalar. Equation (4.56) and Lemma 4.7 give the
weight-space interpretation of the independent target submodules used here.
The result concerns the charge action on the ground space in (4.55).
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedGroundRecognition

open LatticeGeneratingFieldLocality ThirdTwistedChargeAction

noncomputable section

variable {D : LatticeData} {g : Charge D ≃+ Charge D}
variable {C : Multiplier D g} {E : LiftPhase D g C} {hExact : MovingExact D g}
variable (s : MomentumSection D g)
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (T : Charge D → Module.End ℂ M) (w : M)

/-- Extend the section translates of the zero-momentum vector by finite linear combination. -/
def recognitionMap : Ground D g →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ fun p => T (s.lift p) w

theorem recognitionMap_single (p : Momentum D g) (z : ℂ) :
    recognitionMap s T w (Finsupp.single p z) = z • T (s.lift p) w :=
  Finsupp.linearCombination_single ℂ z p

private theorem shift_lift_zero (p : Momentum D g) : shift D g (s.lift p) 0 = p := by
  apply Subtype.ext
  change (0 : Charge D) + N D g (s.lift p) = p.1
  rw [zero_add, s.right_inv]

variable {s T w}

/-- The target multiplication and stabilizer laws give exactly the existing source coefficient. -/
theorem recognitionMap_intertwines
    (hMul : ∀ a b, (T a).comp (T b) = (C.c a b : ℂ) • T (a + b))
    (hχ : ∀ m : Moving D g, T m.1 w = (chi D g C E hExact m : ℂ) • w)
    (a : Charge D) :
    (T a).comp (recognitionMap s T w) =
      (recognitionMap s T w).comp (U D g C E hExact s a) := by
  apply Finsupp.lhom_ext
  intro p z
  let r := s.lift (shift D g a p)
  let m := sectionDifference D g s a p
  have hDecompose : r + m.1 = a + s.lift p := by
    change r + (a + s.lift p - r) = a + s.lift p
    abel
  have hApply (b c : Charge D) :
      T b (T c w) = (C.c b c : ℂ) • T (b + c) w :=
    DFunLike.congr_fun (hMul b c) w
  have hStabilizer := hApply r m.1
  rw [hχ m, map_smul, hDecompose] at hStabilizer
  have hRewrite :
      T (a + s.lift p) w =
        (↑((C.c r m.1)⁻¹ * chi D g C E hExact m) : ℂ) • T r w := by
    calc
      _ = (↑((C.c r m.1)⁻¹) : ℂ) • ((C.c r m.1 : ℂ) • T (a + s.lift p) w) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = _ := by rw [← hStabilizer, smul_smul, Units.val_mul]
  simp only [LinearMap.comp_apply, recognitionMap_single, U_single, map_smul]
  rw [hApply, hRewrite]
  simp only [coefficient, Units.val_mul, smul_smul, mul_assoc]
  congr 1
  ring

/-- The inverse stabilizer scalar at the section's lift of zero normalizes the zero basis vector. -/
theorem recognitionMap_normalized_zero
    (hχ : ∀ m : Moving D g, T m.1 w = (chi D g C E hExact m : ℂ) • w) :
    recognitionMap s T w (Finsupp.single 0
      (↑((chi D g C E hExact ⟨s.lift 0, s.right_inv 0⟩)⁻¹) : ℂ)) = w := by
  let m : Moving D g := ⟨s.lift 0, s.right_inv 0⟩
  rw [recognitionMap_single]
  change (↑((chi D g C E hExact m)⁻¹) : ℂ) • T m.1 w = w
  rw [hχ m, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- Every momentum is a section charge shift of zero, so one vector determines an intertwiner. -/
theorem intertwiner_eq_of_zero
    {F G : Ground D g →ₗ[ℂ] M}
    (hF : ∀ a, (T a).comp F = F.comp (U D g C E hExact s a))
    (hG : ∀ a, (T a).comp G = G.comp (U D g C E hExact s a))
    (hZero : F (Finsupp.single 0 1) = G (Finsupp.single 0 1)) : F = G := by
  apply Finsupp.lhom_ext
  intro p z
  have h := (DFunLike.congr_fun (hF (s.lift p)) (Finsupp.single 0 1)).symm.trans
    ((congrArg (T (s.lift p)) hZero).trans
      (DFunLike.congr_fun (hG (s.lift p)) (Finsupp.single 0 1)))
  simp only [LinearMap.comp_apply, U_single, shift_lift_zero, map_smul] at h
  have hBasis := (smul_right_injective M (Units.ne_zero (coefficient D g C E hExact s
    (s.lift p) 0))) h
  have hz : z • Finsupp.single p (1 : ℂ) = Finsupp.single p z := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [← hz, map_smul, map_smul, hBasis]

/-- Independent momentum subspaces separate the nonzero section translates. -/
theorem recognitionMap_injective
    (hUnit : T 0 = LinearMap.id)
    (hMul : ∀ a b, (T a).comp (T b) = (C.c a b : ℂ) • T (a + b))
    (hw : w ≠ 0) {W : Momentum D g → Submodule ℂ M} (hIndep : iSupIndep W)
    (hWeight : ∀ p, T (s.lift p) w ∈ W p) :
    Function.Injective (recognitionMap s T w) := by
  apply hIndep.linearIndependent W hWeight
  intro p hp
  have h := DFunLike.congr_fun (hMul (-s.lift p) (s.lift p)) w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hp, map_zero, neg_add_cancel,
    hUnit, LinearMap.id_apply] at h
  exact (smul_ne_zero (Units.ne_zero _) hw) h.symm

/-- The range is a nonzero charge-invariant subspace. -/
theorem recognitionMap_surjective
    (hMul : ∀ a b, (T a).comp (T b) = (C.c a b : ℂ) • T (a + b))
    (hχ : ∀ m : Moving D g, T m.1 w = (chi D g C E hExact m : ℂ) • w)
    (hw : w ≠ 0)
    (hIrred : ∀ S : Submodule ℂ M, (∀ a x, x ∈ S → T a x ∈ S) → S = ⊥ ∨ S = ⊤) :
    Function.Surjective (recognitionMap s T w) := by
  let F := recognitionMap s T w
  apply LinearMap.range_eq_top.mp
  rcases hIrred (LinearMap.range F) (fun a x ⟨y, hy⟩ =>
    ⟨U D g C E hExact s a y, by
      rw [← hy]
      exact (DFunLike.congr_fun (recognitionMap_intertwines hMul hχ a) y).symm⟩)
    with hBot | hTop
  · have hMem : w ∈ LinearMap.range F := ⟨_, recognitionMap_normalized_zero (s := s) hχ⟩
    rw [hBot, Submodule.mem_bot] at hMem
    exact (hw hMem).elim
  · exact hTop

/-- Recognition of an irreducible target with independent momentum spaces. -/
theorem recognition_of_irreducible
    (hUnit : T 0 = LinearMap.id)
    (hMul : ∀ a b, (T a).comp (T b) = (C.c a b : ℂ) • T (a + b))
    (hχ : ∀ m : Moving D g, T m.1 w = (chi D g C E hExact m : ℂ) • w)
    (hw : w ≠ 0) {W : Momentum D g → Submodule ℂ M} (hIndep : iSupIndep W)
    (hWeight : ∀ p, T (s.lift p) w ∈ W p)
    (hIrred : ∀ S : Submodule ℂ M, (∀ a x, x ∈ S → T a x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ e : Ground D g ≃ₗ[ℂ] M, e.toLinearMap = recognitionMap s T w ∧
      ∀ a, (T a).comp e.toLinearMap = e.toLinearMap.comp (U D g C E hExact s a) :=
  ⟨LinearEquiv.ofBijective (recognitionMap s T w)
    ⟨recognitionMap_injective hUnit hMul hw hIndep hWeight,
      recognitionMap_surjective hMul hχ hw hIrred⟩,
    rfl, recognitionMap_intertwines hMul hχ⟩

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedGroundRecognition
