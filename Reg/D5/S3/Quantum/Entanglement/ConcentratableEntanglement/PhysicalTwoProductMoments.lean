import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments

/-! Source-bound readout of the actual finite physical family as the real order varies. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- The joint sort of the dependent readout necessarily contains both universe levels.
set_option linter.checkUnivs false

namespace Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
open _root_.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
open _root_.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

noncomputable section
universe u v

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := {I : Type u} → [Fintype I] → {D : I → Type v} →
    [∀ i, Fintype (D i)] → [∀ i, DecidableEq (D i)] →
    ℂ → ℂ → ((i : I) → D i → ℂ) → ((i : I) → D i → ℂ) → Finset I → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ K => @physicalCutMoment.{u,v} K) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ {_} [_] {_} [_] [_] _ _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {K : ℝ}, 0 < K →
    let observed := @Realization.readout signature.{u,v} R () () K
    ∀ {I : Type u} [Fintype I] {D : I → Type v} [∀ i, Fintype (D i)]
      [∀ i, DecidableEq (D i)] (a b : ℂ) (x z : ∀ i, D i → ℂ),
    (∀ i, overlap (x i) (x i) = 1) →
    (∀ i, overlap (z i) (z i) = 1) →
    totalMass a b x z ≠ 0 →
    let f := @observed I inferInstance D inferInstance inferInstance a b x z
    let s := fun i => Complex.normSq (overlap (x i) (z i))
    (∀ i, s i ≤ 1) ∧
    2*(‖a‖*‖b‖)*(1-√(∏ i,s i)) ≤ totalMass a b x z ∧
    ∀ U : Finset I,
      let d := (‖a‖*‖b‖/totalMass a b x z)^2 *
        (1-∏ i ∈ U,s i)*(1-∏ i ∈ (Finset.univ \ U),s i)
      let t := √(1-4*d)
      f U = ((1+t)/2)^K+((1-t)/2)^K

abbrev ProbeSite := ULift.{u} (Fin 2)
abbrev ProbeLevel := ULift.{v} (Fin 2)
private local instance probeSiteClassical : DecidableEq ProbeSite.{u} := Classical.decEq _

def site0 : ProbeSite := ⟨0⟩
def site1 : ProbeSite := ⟨1⟩

private def e0 : ProbeLevel := ⟨0⟩
private def e1 : ProbeLevel := ⟨1⟩

private def basis (a x : ProbeLevel.{v}) : ℂ := if x = a then 1 else 0

def firstBasis (_ : ProbeSite.{u}) : ProbeLevel.{v} → ℂ := basis e0
def secondBasis (_ : ProbeSite.{u}) : ProbeLevel.{v} → ℂ := basis e1

private theorem e0_ne_e1 : (e0 : ProbeLevel.{v}) ≠ e1 := by
  intro h
  have q := congrArg ULift.down h
  norm_num [e0,e1] at q

theorem firstBasis_unit (i : ProbeSite.{u}) :
    overlap (firstBasis.{u,v} i) (firstBasis.{u,v} i) = 1 := by
  simp [firstBasis, overlap, basis, apply_ite]

theorem secondBasis_unit (i : ProbeSite.{u}) :
    overlap (secondBasis.{u,v} i) (secondBasis.{u,v} i) = 1 := by
  simp [secondBasis, overlap, basis, apply_ite]

private theorem opposite_basis_overlap (i : ProbeSite.{u}) :
    overlap (firstBasis.{u,v} i) (secondBasis.{u,v} i) = 0 := by
  simp [firstBasis, secondBasis, overlap, basis, apply_ite, Ne.symm e0_ne_e1]

private theorem one_hot_product (a : ProbeLevel.{v}) (x : ProbeSite.{u} → ProbeLevel.{v}) :
    (∏ i, basis a (x i)) = if x = fun _ => a then 1 else 0 := by
  by_cases h : x = fun _ => a
  · subst x
    simp [basis]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ a := by
      by_contra! hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [basis,hi]

theorem bell_mass :
    totalMass 1 1 (firstBasis.{u,v}) (secondBasis.{u,v}) = 2 := by
  unfold totalMass
  change (∑ x : ProbeSite.{u} → ProbeLevel.{v},
    Complex.normSq (1*(∏ i, basis e0 (x i)) + 1*(∏ i, basis e1 (x i)))) = 2
  simp only [one_mul]
  simp_rw [one_hot_product]
  have h : (fun _ : ProbeSite.{u} => (e0 : ProbeLevel.{v})) ≠ fun _ => e1 :=
    fun h => e0_ne_e1 (congrFun h site0)
  have point (x : ProbeSite.{u} → ProbeLevel.{v}) :
      Complex.normSq ((if x = (fun _ => e0) then 1 else 0) +
        (if x = (fun _ => e1) then 1 else 0)) =
        (if x = (fun _ => e0) then (1 : ℝ) else 0) + (if x = (fun _ => e1) then 1 else 0) := by
    by_cases h₀ : x = (fun _ => e0) <;> by_cases h₁ : x = (fun _ => e1)
    · exact (h (h₀.symm.trans h₁)).elim
    · simp [h₀,h]
    · simp [h₁,Ne.symm h]
    · simp [h₀,h₁]
  simp [point, Finset.sum_add_distrib]
  norm_num

theorem bell_mass_ne :
    totalMass 1 1 (firstBasis.{u,v}) (secondBasis.{u,v}) ≠ 0 :=
  bell_mass.trans_ne (by norm_num)

set_option maxHeartbeats 1600000 in
theorem bell_empty {K : ℝ} (hK : 0 < K) :
    physicalCutMoment K 1 1 (firstBasis.{u,v}) (secondBasis.{u,v}) ∅ = 1 := by
  have ht := (physical_two_product_moments hK 1 1 firstBasis.{u,v} secondBasis.{u,v}
    firstBasis_unit secondBasis_unit bell_mass_ne).2.2 (∅ : Finset ProbeSite.{u})
  simpa [Real.zero_rpow hK.ne'] using ht

set_option maxHeartbeats 1600000 in
theorem bell_left {K : ℝ} (hK : 0 < K) :
    physicalCutMoment K 1 1 (firstBasis.{u,v}) (secondBasis.{u,v}) {site0} =
      ((1/2 : ℝ)^K + (1/2 : ℝ)^K) := by
  have ht := (physical_two_product_moments hK 1 1 firstBasis.{u,v} secondBasis.{u,v}
    firstBasis_unit secondBasis_unit bell_mass_ne).2.2 ({site0} : Finset ProbeSite.{u})
  dsimp only at ht
  have h01 : (site1 : ProbeSite.{u}) ≠ site0 := by
    intro hh
    have q := congrArg ULift.down hh
    norm_num [site0,site1] at q
  have hc : (∏ i ∈ (Finset.univ \ {site0} : Finset ProbeSite.{u}),
      Complex.normSq (overlap (firstBasis.{u,v} i) (secondBasis.{u,v} i))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ site1,by simp [h01]⟩)
      (by rw [opposite_basis_overlap, Complex.normSq_zero])
  rw [hc] at ht
  norm_num [bell_mass, opposite_basis_overlap] at ht
  exact ht

set_option maxHeartbeats 1000000 in
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have ht := (h (K := 2) (by norm_num) 1 1 firstBasis.{u,v} secondBasis.{u,v}
    firstBasis_unit secondBasis_unit bell_mass_ne).2.2 (∅ : Finset ProbeSite.{u})
  change (-1 : ℝ) = _ at ht
  norm_num at ht

set_option maxHeartbeats 1000000 in
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨(),2,3,?_⟩
  intro h
  let eval (F : signature.{u,v}.Output () role) := @F ProbeSite.{u} inferInstance
    (fun _ => ProbeLevel.{v}) inferInstance inferInstance 1 1 firstBasis secondBasis {site0}
  have eq := congrArg eval h
  change physicalCutMoment 2 1 1 firstBasis.{u,v} secondBasis.{u,v} {site0} =
    physicalCutMoment 3 1 1 firstBasis.{u,v} secondBasis.{u,v} {site0} at eq
  rw [bell_left (by norm_num), bell_left (by norm_num)] at eq
  norm_num [← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast] at eq

def source_registration : Registration arena.{u,v} (type_of% @physical_two_product_moments.{u,v}) where
  actual := actual.{u,v}
  bridge := Iff.rfl
  variation := ⟨@physical_two_product_moments.{u,v},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_two_product_moments.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments.physical_two_product_moments.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ K => @physicalCutMoment.{u,v} K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
