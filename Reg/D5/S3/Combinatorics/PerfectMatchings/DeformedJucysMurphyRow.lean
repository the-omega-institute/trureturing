import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
import Reg.Support.DependentFamily

/-! Audit of the literal native paired expansion and its complete-partition row. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

open _root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
open _root_.D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Σ k : ℕ, RatFunc ℂ × P k
  State p := P p.1 → RatFunc ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RatFunc ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p f => S p.2.1 p.1 f p.2.2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : RatFunc ℂ) (k : ℕ) (f : P k → RatFunc ℂ) (p : P k),
    R.readout () ⟨k, b, p⟩ f = ∑ q : Fin k, ∑ h : Fin q.val,
      (f (act (equalChargeVertex p q h) (edgeVertex q) p) +
        b * f (act (oppositeChargeVertex p q h) (edgeVertex q) p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 2 (fun _ => 1) (e 2)
  norm_num [rejected, realize, Fin.sum_univ_two] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1, e 2⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  change S 1 2 (fun _ => 0) (e 2) = S 1 2 (fun _ => 1) (e 2) at h
  rw [native_pair_expansion, native_pair_expansion] at h
  norm_num [Fin.sum_univ_two] at h

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro b k f p; exact native_pair_expansion b f p,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_contract : Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.native_pair_expansion)
    (type_of% (realize signature (fun _ p f => S p.2.1 p.1 f p.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.native_pair_expansion
    "Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.arena.__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => S p.2.1 p.1 f p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyComponents
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#check registration_contract
#print axioms registration
#print axioms registration_contract

/-- The row theorem has its own exact law; the state is the native input function. -/
abbrev rowArena : Arena where
  signature := signature
  Law R := ∀ (b : RatFunc ℂ) (k : ℕ) (lam : Nat.Partition k) (p : P k),
    R.readout () ⟨k, b, p⟩ (indicator lam) = rowCoefficient b (ct p) lam

def shifted : Realization signature := realize signature
  (fun _ p f => S p.2.1 p.1 f p.2.2 + 1) (fun e => nomatch e)

private theorem shifted_not_row : ¬ rowArena.Law shifted := by
  intro h
  have hh := h 0 1 (ct (e 1)) (e 1)
  change S 0 1 (indicator (ct (e 1))) (e 1) + 1 = _ at hh
  rw [native_row] at hh
  have hz : (1 : RatFunc ℂ) = 0 := by linear_combination hh
  exact one_ne_zero hz

def row_registration : Registration rowArena (rowArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro b k lam p; exact native_row b lam p,
    shifted, shifted_not_row⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨shifted, ?_, rfl, shifted_not_row⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def row_registration_contract : Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.native_row)
    (type_of% (realize signature (fun _ p f => S p.2.1 p.1 f p.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.native_row
    "Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.rowArena.__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow.row_registration
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena⟩
  objectArena := .source ⟨rowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena ⟨row_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => S p.2.1 p.1 f p.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#check row_registration_contract
#print axioms row_registration
#print axioms row_registration_contract

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
