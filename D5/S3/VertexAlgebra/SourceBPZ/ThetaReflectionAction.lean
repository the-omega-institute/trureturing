/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: The order-two lattice reflection action and its fixed-grade coevaluation invariants. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
The already constructed lattice involution is packaged as the genuine cyclic
order-two action.  This records the representation-theoretic content that is
otherwise hidden in the `theta` involution: `-I` is the nontrivial element,
the source pairing is an isometry, and every theta-fixed finite grade carries
the trivial restricted action.  The last fact makes the finite coevaluation
kernel invariant under the reflection without choosing orbit representatives.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open SourcePairingLaws OriginalSourcePairing OriginalSourceCoevaluation

abbrev ReflectionGroup := ZMod 2

/-- The underlying linear equivalence attached to each additive group element. -/
def thetaRep (D : LatticeData) (g : ReflectionGroup) : Carrier D ≃ₗ[ℂ] Carrier D :=
  if g = 0 then LinearEquiv.refl ℂ (Carrier D) else theta D

private def thetaPerm (D : LatticeData) (g : ReflectionGroup) : Equiv.Perm (Carrier D) :=
  if g = 0 then Equiv.refl _ else (theta D).toEquiv

private theorem theta_apply_involutive (D : LatticeData) (v : Carrier D) :
    theta D (theta D v) = v := by
  change thetaLinear D (thetaLinear D v) = v
  exact theta_involutive D v

/-- The cyclic order-two representation, with the additive `ZMod 2` law made
visible through the standard `Additive` type tag on permutations. -/
def thetaRepHom (D : LatticeData) :
    ReflectionGroup →+ Additive (Equiv.Perm (Carrier D)) :=
  { toFun := fun g => Additive.ofMul (thetaPerm D g)
    map_zero' := by
      change (Equiv.refl (Carrier D)) = 1
      rfl
    map_add' := by
      intro g h
      fin_cases g <;> fin_cases h <;>
        apply Additive.ext
      all_goals
        apply Equiv.ext
        intro v
        norm_num [thetaPerm, theta_apply_involutive] }

@[simp] theorem thetaRep_zero (D : LatticeData) :
    thetaRep D 0 = LinearEquiv.refl ℂ (Carrier D) := by
  simp [thetaRep]

@[simp] theorem thetaRep_one (D : LatticeData) :
    thetaRep D 1 = theta D := by
  simp [thetaRep]

/-- The generator is the negative identity (`-I`) in the order-two quotient. -/
@[simp] theorem thetaRep_neg_one (D : LatticeData) :
    thetaRep D (-1) = theta D := by
  have h : (-1 : ReflectionGroup) = 1 := by decide
  rw [h]
  exact thetaRep_one D

@[simp] theorem thetaRep_apply_zero (D : LatticeData) (v : Carrier D) :
    thetaRep D 0 v = v := by
  simp

@[simp] theorem thetaRep_apply_one (D : LatticeData) (v : Carrier D) :
    thetaRep D 1 v = theta D v := by
  simp

theorem thetaRep_pairing (D : LatticeData) (g : ReflectionGroup)
    (u v : Carrier D) :
    sourcePairing D (thetaRep D g u) (thetaRep D g v) = sourcePairing D u v := by
  fin_cases g
  · simp
  · simpa [thetaRep] using sourcePairing_theta D u v

theorem thetaRep_involutive (D : LatticeData) (v : Carrier D) :
    thetaRep D 1 (thetaRep D 1 v) = v := by
  simpa [thetaRep] using theta_apply_involutive D v

theorem thetaRep_fixed (D : LatticeData) (g : ReflectionGroup)
    (v : ↥(fixedSpace D)) :
    thetaRep D g v.val = v.val := by
  fin_cases g
  · rfl
  · simpa [thetaRep] using (mem_fixedSpace D v.val).mp v.property

theorem coevaluation_fixed_under_theta (D : LatticeData)
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    thetaRep D 1 (coevaluation D h f).val = (coevaluation D h f).val := by
  simpa [thetaRep] using (mem_fixedSpace D (coevaluation D h f).val).mp
    (coevaluation D h f).property.2

theorem coevaluation_fixed_under_reflection (D : LatticeData)
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)) :
    thetaRep D (-1) (coevaluation D h f).val = (coevaluation D h f).val := by
  simpa using coevaluation_fixed_under_theta D h f

end D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction

#print axioms thetaRep
#print axioms thetaRep_pairing
#print axioms coevaluation_fixed_under_reflection
