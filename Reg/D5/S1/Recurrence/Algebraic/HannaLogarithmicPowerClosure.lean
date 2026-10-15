import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

noncomputable section
namespace Reg.D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
open _root_.D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
universe u

local instance : CharZero (ULift.{u} ℚ) where
  cast_injective m n h := by
    have hQ : (m : ℚ) = (n : ℚ) := congrArg ULift.down h
    exact_mod_cast hQ

structure FieldData where
  carrier : Type u
  field : Field carrier
  charZero : CharZero carrier
attribute [instance] FieldData.field FieldData.charZero

abbrev signature : Signature where
  Params := FieldData.{u}
  State p := (ℕ → p.carrier) × ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.carrier
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s =>
    coeff s.2.2 (logarithmicTransform (fun n => s.1 n ^ s.2.1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p : FieldData, ∀ L : ℕ → p.carrier,
    IntegralSeries (logarithmicTransform L) → ∀ m : ℕ, 0 < m →
      ∀ r : ℕ, ∃ z : ℤ, R.readout () p (L, m, r) = (z : p.carrier)

private theorem zero_integral {K : Type*} [Field K] [CharZero K] :
    IntegralSeries (logarithmicTransform (fun _ => (0 : K))) := by
  have he : egf (fun _ => (0 : K)) = 0 := by ext n; simp [egf]
  intro n
  refine ⟨0, ?_⟩
  rw [logarithmicTransform, he, ← coe_substAlgHom HasSubst.log, map_zero]
  simp

private theorem rejected_bad : ¬ arena.Law (rejected.{u}) := by
  intro h
  let p : FieldData.{u} := ⟨ULift.{u} ℚ, inferInstance, inferInstance⟩
  let : Field p.carrier := p.field
  let : CharZero p.carrier := p.charZero
  obtain ⟨z, hz⟩ := h p (fun _ => 0) zero_integral 1 (by omega) 0
  change (1 / 2 : ULift.{u} ℚ) = (z : ULift.{u} ℚ) at hz
  have hzQ := congrArg ULift.down hz
  have hzQ' : (1 / 2 : ℚ) = (z : ℚ) := by simpa using hzQ
  have hd := congrArg Rat.den hzQ'
  norm_num at hd

private theorem constant_transform {K : Type*} [Field K] [CharZero K] (L : ℕ → K) :
    coeff 0 (logarithmicTransform L) = L 0 := by
  rw [logarithmicTransform, coeff_subst' HasSubst.log, finsum_eq_single _ 0]
  · simp [egf]
  · intro n hn
    have hz : coeff 0 (log K ^ n) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr constantCoeff_log) n) 0
        (Nat.pos_of_ne_zero hn)
    simp [hz]

def family : Registration (arena.{u}) (type_of% result.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h p L hL m hm r
      exact h p.carrier L hL m hm r
    · intro h K hf hc L hL m hm r
      exact h ⟨K, hf, hc⟩ L hL m hm r
  variation := ⟨by intro p L hL m hm r; exact result p.carrier L hL m hm r,
    rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let p : FieldData.{u} := ⟨ULift.{u} ℚ, inferInstance, inferInstance⟩
    refine ⟨p, ((fun _ => 0), 1, 0), ((fun _ => 1), 1, 0), ?_⟩
    change coeff 0 (logarithmicTransform (fun _ => (0 : ULift.{u} ℚ) ^ 1)) ≠
      coeff 0 (logarithmicTransform (fun _ => (1 : ULift.{u} ℚ) ^ 1))
    rw [constant_transform, constant_transform]
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} result.{u} (Realization signature.{u}) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.result "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
