/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: The order-two lattice reflection action, energy-grade equivariance, and fixed-grade coevaluation invariants. -/

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
open LatticeAllStateField
open MvPolynomial
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
        have hsum : (1 + 1 : ReflectionGroup) = 0 := by decide
        simp [thetaPerm, hsum, theta_apply_involutive] }

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

private theorem theta_carrierBasis (D : LatticeData) (a : Label D) :
    theta D (carrierBasis D a) =
      ((-1 : ℂ) ^ (occurrences D a.2).length) •
        carrierBasis D (-a.1, a.2) := by
  change thetaLinear D (carrierBasis D a) = _
  rw [carrierBasis_apply, theta_single, sigma_monomial, carrierBasis_apply,
    ← Finsupp.smul_single]

theorem thetaRep_preserves_energy_grade (D : LatticeData) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D n) :
    thetaRep D 1 v ∈ grade D n := by
  rw [grade_eq_span] at hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨a, ha, rfl⟩
    rw [thetaRep_apply_one, theta_carrierBasis]
    apply (grade D n).smul_mem _
    rw [grade_eq_span]
    have hneg : energy D (-a.1, a.2) = n := by
      simpa [energy, chargeEnergy, bilinear] using ha
    exact Submodule.subset_span ⟨(-a.1, a.2), hneg, rfl⟩
  · exact Submodule.zero_mem _
  · rintro x y _ _ hx hy
    simpa only [map_add] using (grade D n).add_mem hx hy
  · rintro c x _ hx
    simpa only [map_smul] using (grade D n).smul_mem c hx

theorem thetaRep_charge_energy_neg (D : LatticeData) (a : Charge D) :
    chargeEnergy D (-a) = chargeEnergy D a := by
  simp [chargeEnergy, bilinear]

private theorem gradeProjection_eq_self_of_mem_grade (D : LatticeData) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D n) :
    gradeProjection D n v = v := by
  apply (carrierCoeffEquiv D).injective
  ext a
  rw [gradeProjection_coeff]
  by_cases ha : energy D a = n
  · simp [ha]
  · rw [if_neg ha]
    exact ((mem_grade_iff D n v).mp hv a ha).symm

private theorem gradeProjection_zero_of_mem_grade_ne (D : LatticeData)
    (n m : ℤ) (hmn : m ≠ n) (v : Carrier D) (hv : v ∈ grade D m) :
    gradeProjection D n v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  simp only [map_zero, Finsupp.zero_apply]
  rw [gradeProjection_coeff]
  by_cases ha : energy D a = n
  · have ham : energy D a ≠ m := by
      intro h
      exact hmn (h.symm.trans ha)
    rw [if_pos ha]
    exact (mem_grade_iff D m v).mp hv a ham
  · simp [ha]

private theorem gradeProjection_zero_of_not_mem (D : LatticeData) (n : ℤ)
    (v : Carrier D) (hv : n ∉ stateEnergies D v) :
    gradeProjection D n v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  rw [gradeProjection_coeff]
  by_cases ha : energy D a = n
  · have ha' : a ∉ (carrierCoeffEquiv D v).support := by
      intro has
      apply hv
      exact Finset.mem_image.mpr ⟨a, has, ha⟩
    simp [ha, Finsupp.notMem_support_iff.mp ha']
  · simp [ha]

theorem thetaRep_gradeProjection_commute (D : LatticeData) (n : ℤ)
    (v : Carrier D) :
    thetaRep D 1 (gradeProjection D n v) =
      gradeProjection D n (thetaRep D 1 v) := by
  classical
  simp only [thetaRep_apply_one]
  have htheta_sum : theta D v =
      ∑ m ∈ stateEnergies D v, theta D (gradeProjection D m v) := by
    symm
    simpa only [map_sum] using congrArg (theta D) (sum_gradeProjections D v)
  symm
  rw [htheta_sum]
  simp only [map_sum]
  by_cases hn : n ∈ stateEnergies D v
  · rw [Finset.sum_eq_single n]
    · exact gradeProjection_eq_self_of_mem_grade D n _
        (thetaRep_preserves_energy_grade D n _ (gradeProjection_mem D n v))
    · intro m hm hmn
      exact gradeProjection_zero_of_mem_grade_ne D n m hmn _
        (thetaRep_preserves_energy_grade D m _ (gradeProjection_mem D m v))
    · intro hnot
      exact (hnot hn).elim
  · have hzero :
        (∑ m ∈ stateEnergies D v,
          gradeProjection D n (theta D (gradeProjection D m v))) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      exact gradeProjection_zero_of_mem_grade_ne D n m
        (by intro h; exact hn (h ▸ hm)) _
        (thetaRep_preserves_energy_grade D m _ (gradeProjection_mem D m v))
    rw [hzero, gradeProjection_zero_of_not_mem D n v hn]
    simp

theorem thetaRep_grade_plus_minus_decomposition (D : LatticeData) (n : ℤ)
    (v : grade D n) :
    v.val = plusPart D v.val + minusPart D v.val ∧
      plusPart D v.val ∈ grade D n ∧
      minusPart D v.val ∈ grade D n ∧
      plusPart D v.val ∈ fixedSpace D ∧
      minusPart D v.val ∈ minusSpace D := by
  have htheta : theta D v.val ∈ grade D n :=
    thetaRep_preserves_energy_grade D n v.val v.property
  have hplus_grade : plusPart D v.val ∈ grade D n := by
    exact (grade D n).smul_mem _ ((grade D n).add_mem v.property htheta)
  have hminus_grade : minusPart D v.val ∈ grade D n := by
    exact (grade D n).smul_mem _ ((grade D n).sub_mem v.property htheta)
  have hplus_fixed : plusPart D v.val ∈ fixedSpace D := by
    rw [mem_fixedSpace]
    have hi : theta D (theta D v.val) = v.val := theta_involutive D v.val
    simp only [plusPart, map_smul, map_add]
    rw [hi]
    rw [add_comm]
  have hminus_minus : minusPart D v.val ∈ minusSpace D := by
    change minusPart D v.val ∈ eigenspace D (-1)
    rw [mem_eigenspace]
    have hi : theta D (theta D v.val) = v.val := theta_involutive D v.val
    simp only [minusPart, map_smul, map_sub]
    rw [hi]
    module
  refine ⟨?_, hplus_grade, hminus_grade, hplus_fixed, hminus_minus⟩
  simp only [plusPart, minusPart, smul_add, smul_sub]
  module

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

#print axioms thetaRep
#print axioms thetaRep_preserves_energy_grade
#print axioms thetaRep_gradeProjection_commute
#print axioms thetaRep_pairing
#print axioms coevaluation_fixed_under_reflection

end D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
