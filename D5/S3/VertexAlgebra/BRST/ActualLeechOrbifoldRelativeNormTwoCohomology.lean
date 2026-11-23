/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual norm-two relative BRST quotient in every ghost degree. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Relative BRST cochains, cycles, boundaries and the quotient at the
norm-two momentum of the actual Leech orbifold string. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo

open ActualLeechOrbifoldBRST (ComplexState Q)
open private Q_on_C N_on_C N_psi psi_mem_C relative_coordinates rho_psi
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo

private def ghostDegree (q : ℤ) : Submodule ℂ ComplexState :=
  Module.End.eigenspace (R := ℂ) (M := ComplexState) N (q : ℂ)

/-- The relative cochain space in integral ghost degree q. -/
def Cq (q : ℤ) : Submodule ℂ ComplexState := C ⊓ ghostDegree q

/-- The actual charge restricted from one relative ghost degree to the next. -/
def d (q : ℤ) : Cq q →ₗ[ℂ] Cq (q + 1) :=
  Q.domRestrict (Cq q) |>.codRestrict (Cq (q + 1)) fun x => by
    change Q x.val ∈ Cq (q + 1)
    rw [Q_on_C x.property.1]
    exact (Cq (q + 1)).zero_mem

/-- The preceding actual differential with its codomain identified with degree q. -/
def incoming (q : ℤ) : Cq (q - 1) →ₗ[ℂ] Cq q :=
  (LinearEquiv.ofEq _ _ (congrArg Cq (sub_add_cancel q 1))).toLinearMap.comp (d (q - 1))

private theorem d_apply_zero (q : ℤ) (x : Cq q) : d q x = 0 :=
  Subtype.ext (Q_on_C x.property.1)

private theorem incoming_apply_zero (q : ℤ) (x : Cq (q - 1)) : incoming q x = 0 := by
  unfold incoming
  rw [LinearMap.comp_apply, d_apply_zero, map_zero]

/-- Cycles are the kernel of the actual restricted differential. -/
def Cycles (q : ℤ) : Submodule ℂ (Cq q) := LinearMap.ker (d q)

private instance cochainAddCommGroup (q : ℤ) : AddCommGroup (Cq q) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := ℂ) (M := ComplexState) (Cq q)

instance (q : ℤ) : AddCommGroup (Cycles q) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := ℂ) (M := Cq q) (Cycles q)

instance (q : ℤ) : Module ℂ (Cycles q) :=
  Submodule.module (Cycles q)

private def incomingCycles (q : ℤ) : Cq (q - 1) →ₗ[ℂ] Cycles q :=
  (incoming q).codRestrict (Cycles q) fun x => by
    change d q (incoming q x) = 0
    apply Subtype.ext
    change Q (Q x.val) = 0
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun ActualLeechOrbifoldBRST.Q_squared x.val

/-- Boundaries inside the cycle space, using the actual preceding differential. -/
def Boundaries (q : ℤ) : Submodule ℂ (Cycles q) := LinearMap.range (incomingCycles q)

/-- Relative BRST cohomology at the fixed norm-two momentum in degree q. -/
abbrev Cohomology (q : ℤ) := Cycles q ⧸ Boundaries q

private theorem boundaries_eq_bot (q : ℤ) : Boundaries q = ⊥ := by
  apply bot_unique
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_bot]
  exact Subtype.ext (incoming_apply_zero _ y)

/-- The distinguished relative degree-one cycle on the actual state space. -/
def psiCycle : Cycles 1 :=
  ⟨⟨ψ, psi_mem_C, Module.End.mem_eigenspace_iff.mpr (by simpa using N_psi)⟩,
    d_apply_zero _ _⟩

/-- The class of the vacuum momentum state with its single ghost excitation. -/
def psiClass : Cohomology 1 := Submodule.Quotient.mk psiCycle

private def cycleCoordinates : Cycles 1 ≃ₗ[ℂ] ℂ where
  toLinearMap := ρ.comp ((Cq 1).subtype.comp (Cycles 1).subtype)
  invFun z := z • psiCycle
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (relative_coordinates x.val.property.1).symm
  right_inv z := by
    change ρ (z • ψ) = z
    rw [map_smul, rho_psi, smul_eq_mul, mul_one]

/-- In ghost degree one the coefficient of the relative generator identifies cohomology with ℂ. -/
def cohomologyOne : Cohomology 1 ≃ₗ[ℂ] ℂ :=
  (Boundaries 1).quotEquivOfEqBot (boundaries_eq_bot 1) ≪≫ₗ cycleCoordinates

/-- The displayed equivalence assigns coefficient one to the actual class [ψ]. -/
theorem cohomologyOne_psiClass : cohomologyOne psiClass = 1 := by
  change cycleCoordinates ((Boundaries 1).quotEquivOfEqBot (boundaries_eq_bot 1)
    (Submodule.Quotient.mk psiCycle)) = 1
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  exact rho_psi

/-- The displayed relative class is nonzero in the actual quotient. -/
theorem psiClass_ne_zero : psiClass ≠ 0 := by
  intro h
  have hzero : cohomologyOne (0 : Cohomology 1) = 0 := cohomologyOne.map_zero
  have heq := congrArg (fun z : Cohomology 1 => cohomologyOne z) h
  exact one_ne_zero (cohomologyOne_psiClass.symm.trans (heq.trans hzero))

/-- Every other integral ghost degree has zero relative cohomology. -/
theorem cohomology_vanishes (q : ℤ) (hq : q ≠ 1) : Subsingleton (Cohomology q) := by
  have hzero (x : Cq q) : x = 0 := by
    apply Subtype.ext
    have h := Module.End.mem_eigenspace_iff.mp x.property.2
    rw [N_on_C x.property.1] at h
    have hcoef : ρ x.val = (q : ℂ) * ρ x.val := by
      simpa only [map_smul, smul_eq_mul] using congrArg (fun y : ComplexState => ρ y) h
    have hmul : ((q : ℂ) - 1) * ρ x.val = 0 := by
      rw [sub_mul, one_mul, ← hcoef, sub_self]
    have hz := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hq))
    change x.val = (0 : ComplexState)
    exact (relative_coordinates x.property.1).trans (by rw [hz, zero_smul])
  have : Subsingleton (Cycles q) :=
    ⟨fun x y => Subtype.ext ((hzero x.val).trans (hzero y.val).symm)⟩
  exact ((Boundaries q).quotEquivOfEqBot (boundaries_eq_bot q)).injective.subsingleton

#print axioms cohomologyOne
#print axioms cohomologyOne_psiClass
#print axioms psiClass_ne_zero
#print axioms cohomology_vanishes


end D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativeNormTwo
