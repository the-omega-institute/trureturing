/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed physical current jet finite differences for the original charged fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
import D5.S3.VertexAlgebra.LatticeAllStateLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/- proof_shape: physicalCurrent_charge_ward: bind-only;
   physicalCurrent_current_locality: content; physicalCurrent_charge_locality: content;
   physicalJet_charge_locality: content; physicalJet_pair_locality: content
   admission_basis: escape-witness
   escape_witness: The actual signed Heisenberg diagonal and the Ward parity carry
   are annihilated by proved finite differences. The factorial-normalized jet
   recurrence consumes the iterated linear-weight Leibniz calculation for every
   signed mode and every finite order. The Ward binding has live jet-locality
   consumers and is not counted as new mathematics.
   Literature status: classical formal lattice field calculus; zero novelty. -/

namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open FieldNormalProductLocality
open scoped VertexOperator TensorProduct

noncomputable section

def firstWeight {State : Type*} [AddCommGroup State] [Module ℂ State] (constant : ℂ)
    (distribution : ℤ → ℤ → State) : ℤ → ℤ → State :=
  fun left right => ((left : ℂ) + constant) • distribution left right

def firstShift {State : Type*} (distribution : ℤ → ℤ → State) : ℤ → ℤ → State :=
  fun left right => distribution (left + 1) right

private theorem delta_firstWeight {State : Type*} [AddCommGroup State] [Module ℂ State]
    (constant : ℂ) (distribution : ℤ → ℤ → State) :
    delta (firstWeight constant distribution) =
      firstWeight constant (delta distribution) + firstShift distribution := by
  funext left right
  simp only [firstWeight, delta, firstShift, Pi.add_apply, Int.cast_add, Int.cast_one]
  module

private theorem delta_firstShift {State : Type*} [AddCommGroup State]
    (distribution : ℤ → ℤ → State) :
    delta (firstShift distribution) = firstShift (delta distribution) := by
  funext left right
  simp only [firstShift, delta]

private theorem firstWeight_iterate {State : Type*} [AddCommGroup State] [Module ℂ State]
    (constant : ℂ) (distribution : ℤ → ℤ → State) (degree : ℕ) :
    delta^[degree + 1] (firstWeight constant distribution) =
      firstWeight constant (delta^[degree + 1] distribution) +
        ((degree + 1 : ℕ) : ℂ) • firstShift (delta^[degree] distribution) := by
  induction degree with
  | zero => simpa using delta_firstWeight constant distribution
  | succ degree inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof]
    have additive (first second : ℤ → ℤ → State) :
        delta (first + second) = delta first + delta second := by
      funext left right
      simp only [delta, Pi.add_apply]
      abel
    have scalar (scalar : ℂ) (value : ℤ → ℤ → State) :
        delta (scalar • value) = scalar • delta value := by
      funext left right
      simp [delta, smul_sub]
    rw [additive, scalar, delta_firstWeight, delta_firstShift]
    rw [← Function.iterate_succ_apply' (f := delta) (degree + 1),
      ← Function.iterate_succ_apply' (f := delta) degree]
    funext left right
    simp only [Pi.add_apply, Pi.smul_apply]
    push_cast
    module

theorem firstWeight_locality {State : Type*} [AddCommGroup State] [Module ℂ State]
    (constant : ℂ) (distribution : ℤ → ℤ → State) (order : ℕ)
    (killed : delta^[order] distribution = 0) :
    delta^[order + 1] (firstWeight constant distribution) = 0 := by
  rw [firstWeight_iterate, Function.iterate_succ_apply', killed]
  funext left right
  simp [delta, firstWeight, firstShift]

private theorem tensorCurrent_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Fin D.rank) (left right : ℤ) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) first left *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) second right -
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) second right *
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) first left =
      if left + right + 1 = 0 then
        (LatticeHalfFock.frequency left * (D.G first second : ℂ)) • LinearMap.id else 0 := by
  apply TensorProduct.ext'
  intro polynomial ground
  simp only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
    LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.sub_tmul, LatticeHalfFock.current_heisenberg_apply]
  split_ifs <;> simp [TensorProduct.smul_tmul']

theorem physicalCurrent_current_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Fin D.rank) :
    delta^[2] (commutator (physicalJet D hu (first, 0))
      (physicalJet D hu (second, 0))) = 0 := by
  funext left right
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, delta,
    FieldNormalProductLocality.commutator, physicalJet_mode, jetCurrent, jetScalar, Finset.range_zero,
    Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
  simp_rw [tensorCurrent_commutator]
  rw [show left + 1 + 1 + right + 1 = left + right + 3 by omega,
    show left + 1 + (right + 1) + 1 = left + right + 3 by omega,
    show left + (right + 1 + 1) + 1 = left + right + 3 by omega]
  by_cases diagonal : left + right + 3 = 0
  · simp only [diagonal, if_true, Pi.zero_apply, LatticeHalfFock.frequency]
    push_cast
    module
  · simp [diagonal]

theorem physicalCurrent_charge_ward (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (charge : Charge D) (parity left right : ℤ) :
    commutator (physicalJet D hu (colour, 0))
        (physicalSlice D hu (chargedField D hu charge) parity) left right =
      (bilinear D (unitCharge D colour) charge : ℂ) •
        (physicalSlice D hu (chargedField D hu charge) (1 - parity))[[right + left + parity]] := by
  simp only [FieldNormalProductLocality.commutator, physicalJet_mode, physicalSlice_mode, jetCurrent,
    jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
    Nat.cast_one, div_one, one_smul, chargedField, HVertexOperator.coeff_of_coeff]
  rw [charged_tensor_current_ward]
  rw [show -2 * right - parity - 2 - (2 * left + 1) =
    -2 * (right + left + parity) - (1 - parity) - 2 by omega]

theorem physicalCurrent_charge_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (charge : Charge D) (parity : ℤ) :
    delta^[1] (commutator (physicalJet D hu (colour, 0))
      (physicalSlice D hu (chargedField D hu charge) parity)) = 0 := by
  funext left right
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, delta,
    physicalCurrent_charge_ward, Pi.zero_apply]
  rw [show right + (left + 1) + parity = right + 1 + left + parity by omega]
  exact sub_self _

private theorem jetScalar_succ (order : ℕ) (mode : ℤ) :
    jetScalar (order + 1) mode =
      (-((order + 1 : ℕ) : ℂ)⁻¹) * ((mode : ℂ) + 3 / 2 + order) *
        jetScalar order mode := by
  simp only [jetScalar, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have factorialNonzero : (order.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero order
  have successorNonzero : (order : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero order
  field_simp
  ring

private theorem jet_commutator_succ (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (order : ℕ) (field : VertexOperator ℂ (ActualTensor D hu)) :
    commutator (physicalJet D hu (colour, order + 1)) field =
      (-((order + 1 : ℕ) : ℂ)⁻¹) •
        firstWeight (3 / 2 + order) (commutator (physicalJet D hu (colour, order)) field) := by
  funext left right
  simp only [FieldNormalProductLocality.commutator, physicalJet_mode, jetCurrent, jetScalar_succ, firstWeight,
    Pi.smul_apply, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub, smul_smul]
  module

private theorem delta_smul {State : Type*} [AddCommGroup State] [Module ℂ State]
    (scalar : ℂ) (distribution : ℤ → ℤ → State) (order : ℕ) :
    delta^[order] (scalar • distribution) = scalar • delta^[order] distribution := by
  induction order with
  | zero => rfl
  | succ order inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof, Function.iterate_succ_apply']
    funext left right
    simp [delta, smul_sub]

private theorem physicalJet_left_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (colour : Fin D.rank) (field : VertexOperator ℂ (ActualTensor D hu)) (bound order : ℕ)
    (base : delta^[bound] (commutator (physicalJet D hu (colour, 0)) field) = 0) :
    delta^[bound + order] (commutator (physicalJet D hu (colour, order)) field) = 0 := by
  induction order with
  | zero => simpa using base
  | succ order inductionProof =>
    rw [jet_commutator_succ, delta_smul]
    rw [show bound + (order + 1) = (bound + order) + 1 by omega,
      firstWeight_locality _ _ _ inductionProof, smul_zero]

theorem physicalJet_charge_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (charge : Charge D) (parity : ℤ) :
    delta^[index.2 + 1] (commutator (physicalJet D hu index)
      (physicalSlice D hu (chargedField D hu charge) parity)) = 0 := by
  simpa only [Nat.add_comm] using physicalJet_left_locality D hu index.1
    (physicalSlice D hu (chargedField D hu charge) parity) 1 index.2
      (physicalCurrent_charge_locality D hu index.1 charge parity)

theorem physicalJet_pair_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Index D) :
    delta^[first.2 + second.2 + 2]
      (commutator (physicalJet D hu first) (physicalJet D hu second)) = 0 := by
  have firstAgainstBase := physicalJet_left_locality D hu first.1
    (physicalJet D hu (second.1, 0)) 2 first.2
      (physicalCurrent_current_locality D hu first.1 second.1)
  have baseAgainstFirst := FiniteFieldLocality.symmetry _ _ _ firstAgainstBase
  have secondAgainstFirst := physicalJet_left_locality D hu second.1
    (physicalJet D hu first) (2 + first.2) second.2 baseAgainstFirst
  have firstAgainstSecond := FiniteFieldLocality.symmetry _ _ _ secondAgainstFirst
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using firstAgainstSecond

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalGeneratorLocality
