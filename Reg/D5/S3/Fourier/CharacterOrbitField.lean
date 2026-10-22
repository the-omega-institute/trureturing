import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterOrbitField
import Reg.Support.SingleDependentReadout
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Field.ULift

/-! The actual character-field degree as a dependent readout of its character index. -/

namespace Reg.D5.S3.Fourier.CharacterOrbitField
open _root_.D5.S3.Fourier.CharacterOrbitField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Function
noncomputable section
universe u

structure Parameter where
  n : ℕ
  d : ℕ
  F : Type u
  field : Field F
  finite : Finite F
  charTwo : CharP F 2
  zeta : F

attribute [instance] Parameter.field Parameter.finite Parameter.charTwo

abbrev signature : Signature where
  Params := Parameter.{u}
  State p := Fin p.d → ZMod p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun (_ : Unit) (p : Parameter.{u}) (t : Fin p.d → ZMod p.n) =>
  letI : Algebra (ZMod 2) p.F := ZMod.algebra p.F 2
  Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2)
    (Set.range (fun i : Fin p.d => p.zeta ^ (t i).val)))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (p : Parameter.{u}) (_ : Fin p.d → ZMod p.n) => (0 : ℕ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (F : Type u) [f : Field F] [ff : Finite F] [ch : CharP F 2]
    (ζ : F) (_hζ : IsPrimitiveRoot ζ n) (t : Fin d → ZMod n),
    letI : NeZero n := ⟨by omega⟩
    let p : Equiv.Perm (Fin d → ZMod n) := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    R.readout () ⟨n, d, F, f, ff, ch, ζ⟩ t = minimalPeriod (p : _ → _) t

theorem finite_root : ∃ ζ : ULift.{u} (GaloisField 2 2), IsPrimitiveRoot ζ 3 := by
  let K := GaloisField 2 2
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have h : IsPrimitiveRoot (z : K) 3 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_units, hz, Nat.card_units, GaloisField.card 2 2 (by decide : 2 ≠ 0)]
    norm_num
  exact ⟨ULift.up (z : K), h.map_of_injective ULift.ringEquiv.symm.injective⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  obtain ⟨ζ,hζ⟩ := finite_root.{u}
  intro h
  have hh := h 3 0 (by omega) (by decide) (ULift.{u} (GaloisField 2 2)) ζ hζ 0
  change 0 = minimalPeriod _ (0 : Fin 0 → ZMod 3) at hh
  rw [minimalPeriod_eq_one_of_subsingleton] at hh
  omega

def registration : Registration arena.{u} (type_of% (@character_orbit_degree.{u})) := by
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@character_orbit_degree.{u}, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro e
        exact nomatch e
    dependence := ?_ }
  intro i
  obtain ⟨ζ,hζ⟩ := finite_root.{u}
  let F := ULift.{u} (GaloisField 2 2)
  let p : Parameter.{u} := ⟨3, 1, F, inferInstance, inferInstance, inferInstance, ζ⟩
  let per : Equiv.Perm (Fin 1 → ZMod 3) := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 3)).mulLeft)
  have hzero : minimalPeriod (per : _ → _) 0 = 1 := by
    apply minimalPeriod_eq_one_iff_isFixedPt.mpr
    ext j
    simp [per, Equiv.piCongrRight, Units.mulLeft]
  have hnonzero : minimalPeriod (per : _ → _) (fun _ => 1) ≠ 1 := by
    rw [ne_eq, minimalPeriod_eq_one_iff_isFixedPt]
    intro h
    have hh := congrFun h 0
    norm_num [per, Equiv.piCongrRight, Units.mulLeft, ZMod.coe_unitOfCoprime] at hh
    exact (by decide : (2 : ZMod 3) ≠ 1) hh
  refine ⟨p, 0, (fun _ => 1), ?_⟩
  have hd0 := character_orbit_degree 3 1 (by omega) (by decide) F ζ hζ 0
  have hd1 := character_orbit_degree 3 1 (by omega) (by decide) F ζ hζ (fun _ => 1)
  change actual.readout () p 0 = minimalPeriod (per : _ → _) 0 at hd0
  change actual.readout () p (fun _ => 1) = minimalPeriod (per : _ → _) (fun _ => 1) at hd1
  intro he
  exact hnonzero ((hd1.symm.trans (he.symm.trans hd0)).trans hzero)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@character_orbit_degree.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Fourier.CharacterOrbitField.character_orbit_degree.information_unit
  realizationName := `Reg.D5.S3.Fourier.CharacterOrbitField.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) (p : Parameter.{u}) (t : Fin p.d → ZMod p.n) =>
    letI : Algebra (ZMod 2) p.F := ZMod.algebra p.F 2
    Module.finrank (ZMod 2) (IntermediateField.adjoin (ZMod 2)
      (Set.range (fun i : Fin p.d => p.zeta ^ (t i).val)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.CharacterOrbitField
    definition := none
    coordinates := #[0, 1, 4, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Involution

structure Parameter extends Reg.D5.S3.Fourier.CharacterOrbitField.Parameter.{u} where
  t : Fin d → ZMod n

noncomputable abbrev field (a : Parameter.{u}) :
    letI : Algebra (ZMod 2) a.F := ZMod.algebra a.F 2
    IntermediateField (ZMod 2) a.F := by
  letI : Algebra (ZMod 2) a.F := ZMod.algebra a.F 2
  exact IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin a.d => a.zeta ^ (a.t i).val))

abbrev signature : Signature where
  Params := Parameter.{u}
  State a := field a ≃+* field a
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Fin a.d → a.F
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun (_ : Unit) (a : Parameter.{u}) (sigma : field a ≃+* field a) (i : Fin a.d) => by
    letI : Algebra (ZMod 2) a.F := ZMod.algebra a.F 2
    exact (sigma ⟨a.zeta ^ (a.t i).val,
      IntermediateField.subset_adjoin (ZMod 2) _ ⟨i,rfl⟩⟩ : a.F))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun (_ : Unit) (a : Parameter.{u}) (_ : field a ≃+* field a) (_ : Fin a.d) => (0 : a.F))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (F : Type u) [f : Field F] [ff : Finite F] [ch : CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n) (t : Fin d → ZMod n),
    letI : NeZero n := ⟨by omega⟩
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let K := IntermediateField.adjoin (ZMod 2) (Set.range (fun i : Fin d => ζ ^ (t i).val))
    ∀ j : ℕ, (p : G → G)^[j] t = -t → t ≠ 0 →
    ∃ sigma : K ≃+* K, Function.Involutive sigma ∧ sigma ≠ RingEquiv.refl K ∧
      Even (minimalPeriod (p : G → G) t) ∧
      ∀ i : Fin d, R.readout () ⟨⟨n,d,F,f,ff,ch,ζ⟩,t⟩ sigma i = (ζ ^ (t i).val)⁻¹

private theorem index_one :
    let p : Equiv.Perm (Fin 1 → ZMod 3) := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 3)).mulLeft)
    (p : _ → _)^[1] (fun _ => 1) = -(fun _ => 1) := by
  dsimp only
  funext i
  norm_num [Function.iterate_one, Equiv.piCongrRight, Units.mulLeft, ZMod.coe_unitOfCoprime]
  decide

private theorem index_ne_zero : (fun _ : Fin 1 => (1 : ZMod 3)) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  exact one_ne_zero hh

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  obtain ⟨ζ,hζ⟩ := Reg.D5.S3.Fourier.CharacterOrbitField.finite_root.{u}
  intro h
  obtain ⟨sigma,_,_,_,he⟩ := h 3 1 (by omega) (by decide)
    (ULift.{u} (GaloisField 2 2)) ζ hζ (fun _ => 1) 1 index_one index_ne_zero
  have hh := he 0
  change 0 = (ζ ^ (1 : ZMod 3).val)⁻¹ at hh
  have hnz := inv_ne_zero (pow_ne_zero (1 : ZMod 3).val (hζ.ne_zero (by decide)))
  exact hnz hh.symm

def registration : Registration arena.{u} (type_of% (@self_paired_character_involution.{u})) := by
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@self_paired_character_involution.{u}, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro e
        exact nomatch e
    dependence := ?_ }
  intro role
  obtain ⟨ζ,hζ⟩ := Reg.D5.S3.Fourier.CharacterOrbitField.finite_root.{u}
  let F := ULift.{u} (GaloisField 2 2)
  let a : Parameter.{u} := ⟨⟨3,1,F,inferInstance,inferInstance,inferInstance,ζ⟩,fun _ => 1⟩
  obtain ⟨sigma,_,_,_,he⟩ := self_paired_character_involution 3 1 (by omega) (by decide)
    F ζ hζ (fun _ => 1) 1 index_one index_ne_zero
  refine ⟨a,RingEquiv.refl (field a),sigma,?_⟩
  intro h
  have hh := congrFun h 0
  change ζ ^ (1 : ZMod 3).val =
    (sigma ⟨ζ ^ (1 : ZMod 3).val, _⟩ : F) at hh
  rw [he 0] at hh
  have hsq : ζ ^ 2 = 1 := by
    have h' : ζ = ζ⁻¹ := by
      simpa only [show (1 : ZMod 3).val = 1 from rfl, pow_one] using hh
    rw [pow_two]
    exact (congrArg (fun z => z * ζ) h').trans
      (inv_mul_cancel₀ (hζ.ne_zero (by decide)))
  have hd := (hζ.pow_eq_one_iff_dvd 2).mp hsq
  norm_num at hd

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@self_paired_character_involution.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Fourier.CharacterOrbitField.self_paired_character_involution.information_unit
  realizationName := `Reg.D5.S3.Fourier.CharacterOrbitField.Involution.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (a : Parameter.{u}) (sigma : field a ≃+* field a) (i : Fin a.d) => by
      letI : Algebra (ZMod 2) a.F := ZMod.algebra a.F 2
      exact (sigma ⟨a.zeta ^ (a.t i).val,
        IntermediateField.subset_adjoin (ZMod 2) _ ⟨i,rfl⟩⟩ : a.F))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Involution

end
end Reg.D5.S3.Fourier.CharacterOrbitField
