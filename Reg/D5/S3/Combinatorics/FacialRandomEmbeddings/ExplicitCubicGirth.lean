import D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

open D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth.Construction

namespace Reg.D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Input := (g : ℕ) × Vertices g

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ (a : Input) => side a.1 a.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let parity := R.readout () ()
    ∀ (g : ℕ) (hg : 2 ≤ g),
        Finite (Vertices g) ∧
        (explicitGraph g).Connected ∧
        (explicitGraph g).IsBipartite ∧
        (g : ℕ∞) < (explicitGraph g).egirth ∧
        Nat.card (Vertices g) ≤ (5^g+1)^4 ∧
        (∀ x, Nat.card ((explicitGraph g).neighborSet x) = 3) ∧
        (∀ e ∈ (explicitGraph g).edgeSet, ¬(explicitGraph g).IsBridge e) ∧
        (∀ i x, nextVertex g hg i (nextVertex g hg i x) = x) ∧
        (∀ x, Function.Injective (fun i => nextVertex g hg i x)) ∧
        (∀ i x, parity ⟨g, nextVertex g hg i x⟩ = !parity ⟨g, x⟩) ∧
        (∀ x y, (explicitGraph g).Adj x y ↔ ∃ i, nextVertex g hg i x = y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x⟩ := (result 2 le_rfl).2.1.nonempty
  have hb := (h 2 le_rfl).2.2.2.2.2.2.2.2.2.1 0 x
  change false = !false at hb
  contradiction

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hi : i = () := Subsingleton.elim _ _
  subst i
  obtain ⟨x⟩ := (result 2 le_rfl).2.1.nonempty
  refine ⟨(), ⟨2, nextVertex 2 le_rfl 0 x⟩, ⟨2, x⟩, ?_⟩
  intro he
  change side 2 (nextVertex 2 le_rfl 0 x) = side 2 x at he
  have hb := (result 2 le_rfl).2.2.2.2.2.2.2.2.2.1 0 x
  change side 2 (nextVertex 2 le_rfl 0 x) = !side 2 x at hb
  have hz := he.symm.trans hb
  cases hs : side 2 x <;> simp [hs] at hz

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ (a : Input) => side a.1 a.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth
