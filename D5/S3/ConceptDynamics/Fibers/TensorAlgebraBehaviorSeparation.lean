/- GID: D5/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/TensorAlgebraBehaviorSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tensor splitting need not split behavior; degenerate controls are audited. -/

/- Library-search audit trail (2026-08-25):
   * Current-tree `PrimePowerTensorTower.prime_power_tensor_factor_decomposition`
     is the exact algebraic input and is applied at the two-prime window `M = 6`.
   * Current-tree `joint_residue_image_ssubset_product_iff` supplies the constrained
     readout image, while `residue_realization_independent_iff_coprime` supplies the
     coprime control. The former says nothing about matrix-algebra tensor products.
   * Current-tree `CoordinateResidueBilayerNotProduct` treats unequal dependent fibers,
     not a cross-factor admission constraint, so it is not used as a substitute.
   * Pinned Mathlib hits `Set.range_eq_univ` and `Set.univ_prod_univ`; no packaged
     statement combining an algebra tensor equivalence with behavior was found. -/

import D5.S3.Factorization.PrimePowers.CompatibleResidueJointImage
import D5.S3.ObserverMemory.PrimePowerTensorTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.TensorAlgebraBehaviorSeparation

open D5.S3.Factorization.PrimePowers.CompatibleResidueJointImage
open D5.S3.ObserverMemory.PrimePowerTensorTower

/-- The locally admissible states in the left factor. -/
def leftAdmission {A B : Type*} (admission : Set (A × B)) : Set A :=
  Prod.fst '' admission

/-- The locally admissible states in the right factor. -/
def rightAdmission {A B : Type*} (admission : Set (A × B)) : Set B :=
  Prod.snd '' admission

/-- The minimal behavior-product test used here: the jointly admitted pairs are exactly
the product of their two marginal admission sets. This deliberately omits a general
behavioral quotient, categorical product, and temporal trace semantics. -/
def AdmissionBehaviorProduct {A B : Type*} (admission : Set (A × B)) : Prop :=
  admission = leftAdmission admission ×ˢ rightAdmission admission

/-- A state carrier has the required independent-product shape. -/
def StateSpaceIsIndependentProduct (S A B : Type*) : Prop :=
  Nonempty (S ≃ A × B)

/-- An update on a product state acts separately on its two factors. -/
def UpdateActsFactorwise {A B : Type*} (update : A × B → A × B) : Prop :=
  ∃ updateLeft : A → A, ∃ updateRight : B → B,
    ∀ state, update state = (updateLeft state.1, updateRight state.2)

/-- A product-valued readout acts separately on its two state factors. -/
def ReadoutActsFactorwise {A B : Type*} (readout : A × B → A × B) : Prop :=
  ∃ readoutLeft : A → A, ∃ readoutRight : B → B,
    ∀ state, readout state = (readoutLeft state.1, readoutRight state.2)

/-- There is no cross-factor admission condition when every product state is admitted. -/
def NoCrossFactorConstraint {A B : Type*} (admission : Set (A × B)) : Prop :=
  admission = Set.univ

private theorem leftAdmission_jointResidueImage_eq_univ (m n : Nat) :
    leftAdmission (jointResidueImage m n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  rcases ZMod.intCast_surjective a with ⟨x, hx⟩
  refine ⟨(a, localResidueReadout n x), ?_, rfl⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · exact hx
  · rfl

private theorem rightAdmission_jointResidueImage_eq_univ (m n : Nat) :
    rightAdmission (jointResidueImage m n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  rcases ZMod.intCast_surjective b with ⟨x, hx⟩
  refine ⟨(localResidueReadout m x, b), ?_, rfl⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · rfl
  · exact hx

/-- Compatible residue admission is a behavior product exactly for coprime moduli. -/
theorem joint_residue_admission_product_iff_coprime (m n : Nat) :
    AdmissionBehaviorProduct (jointResidueImage m n) ↔ Nat.Coprime m n := by
  constructor
  · intro hproduct
    have himage : jointResidueImage m n = Set.univ := by
      calc
        jointResidueImage m n =
            leftAdmission (jointResidueImage m n) ×ˢ
              rightAdmission (jointResidueImage m n) := hproduct
        _ = (Set.univ : Set (ZMod m)) ×ˢ (Set.univ : Set (ZMod n)) := by
          rw [leftAdmission_jointResidueImage_eq_univ]
          rw [rightAdmission_jointResidueImage_eq_univ]
        _ = Set.univ := Set.univ_prod_univ
    apply (residue_realization_independent_iff_coprime m n).mp
    rw [ResidueRealizationIndependent, ← Set.range_eq_univ]
    exact himage
  · intro hcoprime
    have hsurjective : ResidueRealizationIndependent m n :=
      (residue_realization_independent_iff_coprime m n).mpr hcoprime
    have himage : jointResidueImage m n = Set.univ := by
      rw [jointResidueImage, Set.range_eq_univ]
      exact hsurjective
    calc
      jointResidueImage m n = Set.univ := himage
      _ = (Set.univ : Set (ZMod m)) ×ˢ (Set.univ : Set (ZMod n)) :=
        Set.univ_prod_univ.symm
      _ = leftAdmission (jointResidueImage m n) ×ˢ
          rightAdmission (jointResidueImage m n) := by
        rw [leftAdmission_jointResidueImage_eq_univ]
        rw [rightAdmission_jointResidueImage_eq_univ]

#print axioms joint_residue_admission_product_iff_coprime

private theorem primeFactors_six_eq : (6 : Nat).primeFactors = {2, 3} := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    have hpos : 0 < p := hp.pos
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> norm_num at *
  · rintro (rfl | rfl) <;> norm_num

private theorem primeFactors_four_eq : (4 : Nat).primeFactors = {2} := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    have hpos : 0 < p := hp.pos
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p <;> norm_num at *
  · rintro rfl
    norm_num

/- Boundary with FPOD 107.1: that module proves a readout-layer fact, namely that a joint
residue image is a compatible subobject. It contains no claim about algebra tensor products.
This module adds the independent algebra-layer witness and proves that it cannot decide the
behavior-product predicate without the four extra premises. -/

/-- The nontrivial algebra decomposition at `M = 6` coexists with a behavior whose state,
update, and readout are products, but whose repeated-modulus admission set is constrained.
Thus the fourth premise alone can fail, and the behavior admission is not a product. -/
theorem tensor_algebra_decomposition_does_not_force_behavior_product :
    (6 : Nat).primeFactors.card = 2 ∧
      Function.Bijective (primePowerTensorFactorization 6) ∧
      StateSpaceIsIndependentProduct (ZMod 2 × ZMod 2) (ZMod 2) (ZMod 2) ∧
      UpdateActsFactorwise (id : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2) ∧
      ReadoutActsFactorwise (id : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2) ∧
      ¬NoCrossFactorConstraint (jointResidueImage 2 2) ∧
      ¬AdmissionBehaviorProduct (jointResidueImage 2 2) := by
  refine ⟨?_, prime_power_tensor_factor_decomposition 6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [primeFactors_six_eq]
    norm_num
  · exact ⟨Equiv.refl _⟩
  · refine ⟨id, id, ?_⟩
    rintro ⟨left, right⟩
    rfl
  · refine ⟨id, id, ?_⟩
    rintro ⟨left, right⟩
    rfl
  · intro hfree
    have hstrict := (joint_residue_image_ssubset_product_iff 2 2).mpr (by norm_num)
    exact (Set.ssubset_univ_iff.mp hstrict) hfree
  · rw [joint_residue_admission_product_iff_coprime]
    norm_num

#print axioms tensor_algebra_decomposition_does_not_force_behavior_product

/-- With coprime local factors, the same nontrivial algebra tensor decomposition has a
control behavior satisfying all four premises, and its admission behavior is a product. -/
theorem all_four_premises_give_behavior_product_control :
    (6 : Nat).primeFactors.card = 2 ∧
      Function.Bijective (primePowerTensorFactorization 6) ∧
      StateSpaceIsIndependentProduct (ZMod 2 × ZMod 3) (ZMod 2) (ZMod 3) ∧
      UpdateActsFactorwise (id : ZMod 2 × ZMod 3 → ZMod 2 × ZMod 3) ∧
      ReadoutActsFactorwise (id : ZMod 2 × ZMod 3 → ZMod 2 × ZMod 3) ∧
      NoCrossFactorConstraint (jointResidueImage 2 3) ∧
      AdmissionBehaviorProduct (jointResidueImage 2 3) := by
  refine ⟨?_, prime_power_tensor_factor_decomposition 6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [primeFactors_six_eq]
    norm_num
  · exact ⟨Equiv.refl _⟩
  · refine ⟨id, id, ?_⟩
    rintro ⟨left, right⟩
    rfl
  · refine ⟨id, id, ?_⟩
    rintro ⟨left, right⟩
    rfl
  · change jointResidueImage 2 3 = Set.univ
    rw [jointResidueImage, Set.range_eq_univ]
    exact (residue_realization_independent_iff_coprime 2 3).mpr (by norm_num)
  · exact (joint_residue_admission_product_iff_coprime 2 3).mpr (by norm_num)

#print axioms all_four_premises_give_behavior_product_control

/- Assumption audit: all three public theorems introduced here have no proposition
hypotheses and no typeclass parameters. The natural numbers `m` and `n` in the exact
criterion are unrestricted data, so there is no necessary hypothesis requiring a named
counterexample theorem. The imported algebra theorem's `NeZero M` instance is discharged
at the concrete values 6, 4, and 1 below. Primality is used inside that imported theorem
to construct its prime-power factors; the behavioral criterion and its counterexample use
arbitrary moduli and do not need primality. -/

/- Degenerate audit: an empty factor makes the product carrier empty, but the named state
product and full-admission behavior product remain valid. -/
example : StateSpaceIsIndependentProduct (Empty × Bool) Empty Bool :=
  ⟨Equiv.refl _⟩

example : UpdateActsFactorwise (id : Empty × Bool → Empty × Bool) := by
  exact ⟨id, id, fun state => Empty.elim state.1⟩

example : ReadoutActsFactorwise (id : Empty × Bool → Empty × Bool) := by
  exact ⟨id, id, fun state => Empty.elim state.1⟩

example : NoCrossFactorConstraint (Set.univ : Set (Empty × Bool)) := rfl

example : AdmissionBehaviorProduct (Set.univ : Set (Empty × Bool)) := by
  rw [AdmissionBehaviorProduct]
  ext state
  exact Empty.elim state.1

/- Degenerate audit: singleton factors satisfy both the unrestricted and behavior-product
conditions, so the positive control is not relying on two nontrivial carriers. -/
example : StateSpaceIsIndependentProduct (Unit × Unit) Unit Unit :=
  ⟨Equiv.refl _⟩

example : UpdateActsFactorwise (id : Unit × Unit → Unit × Unit) := by
  exact ⟨id, id, fun _ => rfl⟩

example : ReadoutActsFactorwise (id : Unit × Unit → Unit × Unit) := by
  exact ⟨id, id, fun _ => rfl⟩

example : NoCrossFactorConstraint (Set.univ : Set (Unit × Unit)) := rfl

example : AdmissionBehaviorProduct (Set.univ : Set (Unit × Unit)) := by
  simp [AdmissionBehaviorProduct, leftAdmission, rightAdmission]

/- Degenerate audit: constant and zero maps are factorwise; identity maps are exercised in
both public contrast theorems. Thus factorwise action alone cannot remove admission data. -/
example : UpdateActsFactorwise (fun _ : Bool × Bool => (false, true)) := by
  exact ⟨fun _ => false, fun _ => true, fun _ => rfl⟩

example : ReadoutActsFactorwise (fun _ : ZMod 2 × ZMod 3 => (0, 0)) := by
  exact ⟨fun _ => 0, fun _ => 0, fun _ => rfl⟩

/- Degenerate audit: the zero-modulus pair has a strict diagonal behavior, whereas a
modulus-one factor removes the constraint even when the other modulus is zero. -/
example : ¬AdmissionBehaviorProduct (jointResidueImage 0 0) := by
  rw [joint_residue_admission_product_iff_coprime]
  norm_num

example : AdmissionBehaviorProduct (jointResidueImage 0 1) := by
  rw [joint_residue_admission_product_iff_coprime]
  norm_num

/- Degenerate audit: `M = 4` has one prime-power tensor factor, so its algebra splitting is
the single-factor case and says nothing additional about behavior. -/
example :
    (4 : Nat).primeFactors.card = 1 ∧
      Function.Bijective (primePowerTensorFactorization 4) := by
  refine ⟨?_, prime_power_tensor_factor_decomposition 4⟩
  rw [primeFactors_four_eq]
  norm_num

/- Degenerate audit: `ZMod 1` indexes the one-by-one matrix algebra and has no prime-power
factors; the empty tensor decomposition still exists and does not create behavior data. -/
example : Subsingleton (ZMod 1) := inferInstance

example :
    (1 : Nat).primeFactors.card = 0 ∧
      Function.Bijective (primePowerTensorFactorization 1) := by
  exact ⟨by simp, prime_power_tensor_factor_decomposition 1⟩

end D5.S3.ConceptDynamics.Fibers.TensorAlgebraBehaviorSeparation
