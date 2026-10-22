/- GID: D5/S3/VertexAlgebra/TwistedGround/OperatorAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OperatorAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral charge lifts give the full actual twisted-ground endomorphism algebra. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

noncomputable section

def integralLift (D : LatticeData) (charge : ModTwoCharge D) : Charge D :=
  fun index => Int.ofNat (charge index).val

def chargeLift (D : LatticeData) (charge : ModTwoCharge D) : Extension D ⧸ K D :=
  QuotientGroup.mk (⟨0, integralLift D charge⟩ : Extension D)

def quotientCharge (D : LatticeData) (element : Extension D ⧸ K D) : ModTwoCharge D :=
  (quotientEquiv D element).charge

def chargeOperator (D : LatticeData) {rank : ℕ}
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (charge : ModTwoCharge D) : Module.End ℂ (Ground rank) :=
  rho (chargeLift D charge)

def dualOperator (D : LatticeData) {rank : ℕ}
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (charge : ModTwoCharge D) : Module.End ℂ (Ground rank) :=
  rho (chargeLift D charge)⁻¹

def traceCoefficient (D : LatticeData) {rank : ℕ}
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (charge : ModTwoCharge D) : Module.End ℂ (Ground rank) →ₗ[ℂ] ℂ :=
  (Module.finrank ℂ (Ground rank) : ℂ)⁻¹ •
    (LinearMap.trace ℂ (Ground rank)).comp
      (LinearMap.mulLeft ℂ (dualOperator D rho charge))

private theorem reduced_lift (D : LatticeData) (charge : ModTwoCharge D) :
    quotientEquiv D (chargeLift D charge) = ⟨0, charge⟩ := by
  change reduction D (⟨0, integralLift D charge⟩ : Extension D) = _
  ext index
  · rfl
  · simp [reduction, reduceCharge, integralLift]

private theorem quotient_charge_mul (D : LatticeData) (first second : Extension D ⧸ K D) :
    quotientCharge D (first * second) = quotientCharge D first + quotientCharge D second := by
  simp only [quotientCharge, map_mul]
  rfl

private theorem quotient_charge_inv (D : LatticeData) (element : Extension D ⧸ K D) :
    quotientCharge D element⁻¹ = -quotientCharge D element := by
  simp only [quotientCharge, map_inv]
  rfl

private theorem quotient_charge_lift (D : LatticeData) (charge : ModTwoCharge D) :
    quotientCharge D (chargeLift D charge) = charge := by
  simp [quotientCharge, reduced_lift]

private theorem anticommuting_charge (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : ModTwoCharge D) (nonzero : charge ≠ 0) :
    ∃ partner : ModTwoCharge D, modTwoPairing D charge partner = 1 := by
  have exists_partner : ∃ partner, modTwoPairing D charge partner ≠ 0 := by
    by_contra absent
    push Not at absent
    exact nonzero ((mod_two_pairing_nondegenerate D hu).1 charge absent)
  obtain ⟨partner, pairing⟩ := exists_partner
  refine ⟨partner, ?_⟩
  generalize equation : modTwoPairing D charge partner = value at *
  fin_cases value <;> norm_num at *

private theorem original_anticommutation (D : LatticeData)
    (element : Extension D ⧸ K D) (partner : ModTwoCharge D)
    (pairing : modTwoPairing D (quotientCharge D element) partner = 1) :
    element * chargeLift D partner =
      QuotientGroup.mk (⟨1, 0⟩ : Extension D) * (chargeLift D partner * element) := by
  apply (quotientEquiv D).injective
  simp only [map_mul, reduced_lift]
  change quotientEquiv D element * (⟨0, partner⟩ : ReducedExtension D) =
    (⟨1, 0⟩ : ReducedExtension D) * ((⟨0, partner⟩ : ReducedExtension D) * _)
  change modTwoPairing D (quotientEquiv D element).charge partner = 1 at pairing
  rw [reduced_commutation, pairing]

theorem nonzero_charge_trace (D : LatticeData) (hu : IsUnit D.G.det)
    {rank : ℕ} (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank)))
    (element : Extension D ⧸ K D) (nonzero : quotientCharge D element ≠ 0) :
    LinearMap.trace ℂ (Ground rank) (rho element) = 0 := by
  obtain ⟨partner, pairing⟩ := anticommuting_charge D hu _ nonzero
  have anti : rho element * rho (chargeLift D partner) =
      -(rho (chargeLift D partner) * rho element) := by
    rw [← map_mul, original_anticommutation D element partner pairing,
      map_mul, map_mul, central, neg_one_mul]
  have conjugate : rho (chargeLift D partner)⁻¹ *
      (rho element * rho (chargeLift D partner)) = -rho element := by
    rw [anti, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have traces := congrArg (LinearMap.trace ℂ (Ground rank)) conjugate
  rw [LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel,
    map_one, mul_one, map_neg] at traces
  have twice : (2 : ℂ) * LinearMap.trace ℂ (Ground rank) (rho element) = 0 := by
    linear_combination traces
  exact (mul_eq_zero.mp twice).resolve_left (by norm_num)

private theorem trace_dual (D : LatticeData) (hu : IsUnit D.G.det)
    {rank : ℕ} (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (first second : ModTwoCharge D) :
    LinearMap.trace ℂ (Ground rank) (dualOperator D rho first * chargeOperator D rho second) =
      if first = second then (Module.finrank ℂ (Ground rank) : ℂ) else 0 := by
  classical
  unfold dualOperator chargeOperator
  rw [← map_mul]
  by_cases same : first = second
  · subst second
    simp [LinearMap.trace_one]
  · rw [if_neg same]
    apply nonzero_charge_trace D hu rho central
    rw [quotient_charge_mul, quotient_charge_inv, quotient_charge_lift,
      quotient_charge_lift]
    intro vanished
    exact same (neg_add_eq_zero.mp vanished)

private theorem ground_dimension_nonzero (rank : ℕ) :
    (Module.finrank ℂ (Ground rank) : ℂ) ≠ 0 := by
  simp [Ground, Half, Module.finrank_fintype_fun_eq_card, F₂]

private theorem coefficient_operator (D : LatticeData) (hu : IsUnit D.G.det)
    {rank : ℕ} (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (first second : ModTwoCharge D) :
    traceCoefficient D rho first (chargeOperator D rho second) =
      if first = second then 1 else 0 := by
  classical
  change (Module.finrank ℂ (Ground rank) : ℂ)⁻¹ *
    LinearMap.trace ℂ (Ground rank) (dualOperator D rho first * chargeOperator D rho second) = _
  rw [trace_dual D hu rho central]
  split_ifs
  · exact inv_mul_cancel₀ (ground_dimension_nonzero rank)
  · exact mul_zero _

private theorem operator_independent (D : LatticeData) (hu : IsUnit D.G.det)
    {rank : ℕ} (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) :
    LinearIndependent ℂ (chargeOperator D rho) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients vanishes charge
  have projected := congrArg (traceCoefficient D rho charge) vanishes
  simpa [map_sum, map_smul, coefficient_operator D hu rho central] using projected

private theorem operator_count (D : LatticeData) (rank : ℕ) (rank_eq : D.rank = rank + rank) :
    Fintype.card (ModTwoCharge D) = Module.finrank ℂ (Module.End ℂ (Ground rank)) := by
  simp [ModTwoCharge, Ground, Half, F₂, Module.finrank_linearMap,
    Module.finrank_fintype_fun_eq_card, rank_eq, pow_add]

def operatorBasis (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) :
    Module.Basis (ModTwoCharge D) ℂ (Module.End ℂ (Ground rank)) :=
  basisOfLinearIndependentOfCardEqFinrank (operator_independent D hu rho central)
    (operator_count D rank rank_eq)

private theorem operator_basis_apply (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (charge : ModTwoCharge D) :
    operatorBasis D hu rank rank_eq rho central charge = chargeOperator D rho charge := by
  simp [operatorBasis]

private theorem coefficient_repr (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (operator : Module.End ℂ (Ground rank))
    (charge : ModTwoCharge D) :
    (operatorBasis D hu rank rank_eq rho central).repr operator charge =
      traceCoefficient D rho charge operator := by
  classical
  have expanded := congrArg (traceCoefficient D rho charge)
    ((operatorBasis D hu rank rank_eq rho central).sum_repr operator)
  simpa [map_sum, map_smul, operator_basis_apply,
    coefficient_operator D hu rho central] using expanded

private theorem operator_reconstruction (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (operator : Module.End ℂ (Ground rank)) :
    ∑ charge : ModTwoCharge D, traceCoefficient D rho charge operator •
      chargeOperator D rho charge = operator := by
  simpa only [operator_basis_apply, coefficient_repr] using
    (operatorBasis D hu rank rank_eq rho central).sum_repr operator

private theorem commutes_with_all (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) (operator : Module.End ℂ (Ground rank))
    (commutes : ∀ charge, operator * chargeOperator D rho charge =
      chargeOperator D rho charge * operator) (other : Module.End ℂ (Ground rank)) :
    operator * other = other * operator := by
  conv_lhs => rhs; rw [← operator_reconstruction D hu rank rank_eq rho central other]
  conv_rhs => lhs; rw [← operator_reconstruction D hu rank rank_eq rho central other]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, commutes]

private theorem scalar_of_all_commute (rank : ℕ) (operator : Module.End ℂ (Ground rank))
    (commutes : ∀ other, operator * other = other * operator) :
    ∃ scalar : ℂ, operator = scalar • (1 : Module.End ℂ (Ground rank)) := by
  have centered : operator ∈ Set.center (Module.End ℂ (Ground rank)) :=
    Semigroup.mem_center_iff.mpr (fun other => (commutes other).symm)
  obtain ⟨scalar, _, equality⟩ := Module.End.mem_center_iff.mp centered
  refine ⟨scalar, equality.trans ?_⟩
  apply LinearMap.ext
  intro state
  rfl

structure GroundAlgebra (D : LatticeData) (rank : ℕ)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank)) where
  basis : Module.Basis (ModTwoCharge D) ℂ (Module.End ℂ (Ground rank))
  basis_apply : ∀ charge, basis charge = chargeOperator D rho charge
  dimension_nonzero : (Module.finrank ℂ (Ground rank) : ℂ) ≠ 0
  full_span : Submodule.span ℂ (Set.range (chargeOperator D rho)) = ⊤
  trace_dual : ∀ first second, LinearMap.trace ℂ (Ground rank)
    (dualOperator D rho first * chargeOperator D rho second) =
      if first = second then (Module.finrank ℂ (Ground rank) : ℂ) else 0
  coefficient_repr : ∀ operator charge, basis.repr operator charge =
    traceCoefficient D rho charge operator
  reconstruction : ∀ operator, ∑ charge : ModTwoCharge D,
    traceCoefficient D rho charge operator • chargeOperator D rho charge = operator
  scalar_commutant : ∀ operator, (∀ charge, operator * chargeOperator D rho charge =
    chargeOperator D rho charge * operator) ↔
      ∃ scalar : ℂ, operator = scalar • (1 : Module.End ℂ (Ground rank))

theorem actual_operator_algebra (D : LatticeData) (hu : IsUnit D.G.det)
    (rank : ℕ) (rank_eq : D.rank = rank + rank)
    (rho : Representation ℂ (Extension D ⧸ K D) (Ground rank))
    (central : rho (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
      -(1 : Module.End ℂ (Ground rank))) : Nonempty (GroundAlgebra D rank rho) := by
  refine ⟨{
    basis := operatorBasis D hu rank rank_eq rho central
    basis_apply := operator_basis_apply D hu rank rank_eq rho central
    dimension_nonzero := ground_dimension_nonzero rank
    full_span := (operator_independent D hu rho central).span_eq_top_of_card_eq_finrank
      (operator_count D rank rank_eq)
    trace_dual := trace_dual D hu rho central
    coefficient_repr := coefficient_repr D hu rank rank_eq rho central
    reconstruction := operator_reconstruction D hu rank rank_eq rho central
    scalar_commutant := ?_ }⟩
  intro operator
  constructor
  · intro commutes
    exact scalar_of_all_commute rank operator
      (commutes_with_all D hu rank rank_eq rho central operator commutes)
  · rintro ⟨scalar, rfl⟩ charge
    simp

def chosenRank (D : LatticeData) (hu : IsUnit D.G.det) : ℕ :=
  Classical.choose (actual_twisted_ground_representation D hu)

def chosenRepresentation (D : LatticeData) (hu : IsUnit D.G.det) :
    Representation ℂ (Extension D ⧸ K D) (Ground (chosenRank D hu)) :=
  Classical.choose (Classical.choose_spec (actual_twisted_ground_representation D hu))

private theorem native_algebra_exists (D : LatticeData) (hu : IsUnit D.G.det) :
    Nonempty (GroundAlgebra D (chosenRank D hu) (chosenRepresentation D hu)) := by
  change Nonempty (GroundAlgebra D
    (Classical.choose (actual_twisted_ground_representation D hu))
    (Classical.choose (Classical.choose_spec (actual_twisted_ground_representation D hu))))
  have properties := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  exact actual_operator_algebra D hu _ properties.1 _ properties.2.2.1

def nativeOperatorAlgebra (D : LatticeData) (hu : IsUnit D.G.det) :
    GroundAlgebra D (chosenRank D hu) (chosenRepresentation D hu) :=
  Classical.choice (native_algebra_exists D hu)

#print axioms actual_operator_algebra
#print axioms nativeOperatorAlgebra

end

end D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
