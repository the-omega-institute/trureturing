import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.HarderNarasimhan
import Reg.Support.UniverseSingleReadout

/-! The observed lattice element is the actual.{u} destabilizing witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices.HarderNarasimhan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Extremal

abbrev Params := Σ Λ : Type u, Λ

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{u} (fun p => p.1) (fun p => p.1)

def actual : Realization signature :=
  realize signature.{u} (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ p _ => p.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) (a b : Λ),
    (∃! e, D.Destabilizer a b (V.readout () ⟨Λ, a⟩ e)) ↔ a < b

/-- A nontrivial ranked chain used by both witness sensitivity checks. -/
def integerRankData : SlopeData (ULift.{u} ℤ) where
  rank := ULift.down
  rank_strictMono := fun _ _ h => h
  rank_modular := by
    intro x y
    change max x.down y.down + min x.down y.down = x.down + y.down
    omega
  degree := fun _ => 0
  degree_supermodular := by intro x y; simp

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨e, he, _⟩ :=
    (h integerRankData.{u} ⟨0⟩ ⟨1⟩).mpr (by change (0 : ℤ) < 1; omega)
  exact (lt_irrefl (ULift.up 0)) he.1

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  exact ⟨⟨ULift.{u} ℤ, ⟨0⟩⟩, ⟨0⟩, ⟨1⟩, by
    change (ULift.up 0 : ULift.{u} ℤ) ≠ ULift.up 1
    simp⟩

def family : Registration arena.{u} (type_of% @exists_unique_destabilizer) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@exists_unique_destabilizer, rejected.{u}, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual.{u} rejected.{u} rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unique_destabilizer) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhan.exists_unique_destabilizer "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Extremal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhan
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Extremal

namespace Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Filtration

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) List List

def actual : Realization signature :=
  realize signature.{u} (fun _ _ l => l) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) (a b : Λ),
    (∃! l, D.Filtration a b (V.readout () Λ l)) ↔ a ≤ b

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨l, hl, _⟩ :=
    (h Extremal.integerRankData.{u} ⟨0⟩ ⟨1⟩).mpr (by change (0 : ℤ) ≤ 1; omega)
  change Extremal.integerRankData.{u}.Filtration ⟨0⟩ ⟨1⟩ [] at hl
  cases hl

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  exact ⟨ULift.{u} ℤ, [], [⟨0⟩], by
    change ([] : List (ULift.{u} ℤ)) ≠ [⟨0⟩]; simp⟩

def family : Registration arena.{u} (type_of% @exists_unique_filtration) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@exists_unique_filtration, rejected.{u}, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual.{u} rejected.{u} rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unique_filtration) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhan.exists_unique_filtration "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Filtration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ l => l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Extremes

abbrev Params := Σ Λ : Type u, Σ _ : Λ, Σ _ : Λ, Λ

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{u}
    (fun p => List p.1) (fun p => p.1)

def actual : Realization signature :=
  realize signature.{u} (fun _ p l => lastLower p.2.1 (p.2.2.2 :: l))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ p _ => p.2.2.1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law V := ∀ {Λ : Type u} [Lattice Λ] (D : SlopeData Λ) (a b e : Λ) (l : List Λ),
    D.Filtration a b (e :: l) →
    let q := V.readout () ⟨Λ, a, b, e⟩ l
    a ≤ q ∧ q < b ∧
      IsGreatest {s | ∃ x, a < x ∧ x ≤ b ∧ D.slope a x = s} (D.slope a e) ∧
      IsLeast {s | ∃ x, a ≤ x ∧ x < b ∧ D.slope x b = s} (D.slope q b) ∧
      D.muMax a b = D.slope a e ∧ D.muMin a b = D.slope q b ∧
      D.Destabilizer a b e ∧ D.slope q b ≤ D.slope a e ∧
      (D.Semistable a b ↔ l = []) ∧
      (D.muMin a b = D.muMax a b ↔ D.Semistable a b) ∧
      (l ≠ [] → D.slope q b < D.slope a e)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  have hf : Extremal.integerRankData.{u}.Filtration ⟨0⟩ ⟨1⟩ [⟨1⟩] := by
    refine .cons ⟨by change (0 : ℤ) < 1; omega, ?_⟩ le_rfl (.nil (ULift.up 1)) trivial
    intro x hx hxb
    simp [SlopeData.slope, Extremal.integerRankData]
  intro h
  have hh := h Extremal.integerRankData.{u} ⟨0⟩ ⟨1⟩ ⟨1⟩ [] hf
  exact (lt_irrefl (ULift.up 1)) hh.2.1

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨ULift.{u} ℤ, ⟨0⟩, ⟨2⟩, ⟨1⟩⟩, [], [⟨2⟩], ?_⟩
  change (ULift.up 0 : ULift.{u} ℤ) ≠ ULift.up 1
  simp

def family : Registration arena.{u} (type_of% @filtration_extremes) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨@filtration_extremes, rejected.{u}, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual.{u} rejected.{u} rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filtration_extremes) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.HarderNarasimhan.filtration_extremes "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Filtration.Extremes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p l => lastLower p.2.1 (p.2.2.2 :: l)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.HarderNarasimhan
    definition := none
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extremes

end Reg.D5.S3.Combinatorics.Lattices.HarderNarasimhan.Filtration
