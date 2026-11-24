import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] a T initial terminal W cl

namespace CrossRelabel

abbrev signature : Signature where
  Params := Σ _ : Equiv.Perm (Fin 3), Boundary
  State _ := Row
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readout : Realization signature :=
  realize signature (fun b w r => match b with
    | false => cross (w.1 ∘ w.2) (w.1 ∘ r)
    | true => cross w.2 r) (fun e => nomatch e)

def rejected (i : Bool) : Realization signature :=
  realize signature (fun j w r =>
    if j = i then readout.readout j w r + 1 else readout.readout j w r) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (p : Boundary) (r : Row),
    R.readout false ⟨e, p⟩ r = R.readout true ⟨e, p⟩ r

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  have hh := h (Equiv.refl _) (fun _ => 0) (fun _ => 0)
  cases i <;> exact (by decide +kernel : ¬ _) hh

def family : Registration arena (type_of% @cross_relabel) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨cross_relabel, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext w r
      simp [rejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Equiv.refl _, fun _ => 0⟩, fun _ => 0, fun _ => 1, ?_⟩
    cases i <;> decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cross_relabel) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip.CrossRelabel.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun b w r => match b with
    | false => cross (w.1 ∘ w.2) (w.1 ∘ r)
    | true => cross w.2 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "arg"], stateBinder := 2,
        functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg"], stateBinder := 2,
        functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CrossRelabel

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    (R.readout () () (n + 9) : ℤ) = 84 * R.readout () () (n + 8) -
      2466 * R.readout () () (n + 7) + 31428 * R.readout () () (n + 6) -
      206469 * R.readout () () (n + 5) + 750384 * R.readout () () (n + 4) -
      1513404 * R.readout () () (n + 3) + 1574640 * R.readout () () (n + 2) -
      656100 * R.readout () () (n + 1)
private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
private theorem count_one_pos : 0 < a 1 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![0, 0, 1, 0, 1, 0, 1] x.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [count_zero]
    exact Nat.ne_of_lt count_one_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229585Strip.Recurrence.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Recurrence

namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 72) (fun _ => Fin 72) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => T x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 72,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = (fun x y => R.readout () x y) (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 72, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 10, W i.succ = Matrix.vecMul (W i.castSucc) (fun x y => R.readout () x y)) ∧
    W 10 = ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) • W ⟨2 + j.val, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.2.1 ![0, 1, 0, 1, 0, 1] ⟨1, by decide⟩ (by decide +kernel) 0
  have ha := finite_certificate.2.2.1 ![0, 1, 0, 1, 0, 1] ⟨1, by decide⟩ (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change T 0 0 ≠ T 0 2
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229585Strip.Certificate.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => T x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Certificate
namespace PolynomialRelation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 72) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ _ i => forward T initial (2 + 8) i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ i => forward T initial (2 + 8) i + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () =
    ∑ j : Fin 8, (![-656100, 1574640, -1513404, 750384, -206469, 31428, -2466, 84] j : ℤ) •
      forward T initial (2 + j.val)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := congrFun h (0 : Fin 72)
  have ht := congrFun polynomial_relation (0 : Fin 72)
  change forward T initial (2 + 8) 0 + 1 = _ at hf
  linarith

def family : Registration arena (type_of% @polynomial_relation) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨polynomial_relation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change forward T initial 10 0 ≠ forward T initial 10 2
    have hs : forward T initial 10 = W 10 := by
      let rows := List.ofFn W
      have hchain : rows.IsChain (fun u v => Matrix.vecMul u T = v) :=
        List.isChain_ofFn.mpr fun k hk => (finite_certificate.2.2.2.2.2.1.2 ⟨k, by omega⟩).symm
      have hlast : 10 < rows.length := by simp only [rows, List.length_ofFn]; decide
      have he := hchain.iterate_eq_of_apply_eq 10 hlast
      simp only [rows, List.getElem_ofFn] at he
      change forward T (W 0) 10 = W 10 at he
      rw [finite_certificate.2.2.2.2.2.1.1] at he
      exact he
    rw [hs]
    unfold W
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@polynomial_relation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip.PolynomialRelation.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => forward T initial (2 + 8) i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialRelation

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
