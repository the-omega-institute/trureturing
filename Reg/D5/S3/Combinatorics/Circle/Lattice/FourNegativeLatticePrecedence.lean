import D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope necessary-order registration with literal physical positions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence

abbrev signature : Signature where
  Params := Σ n : ℕ, List (Fin (2 * (4 * n + 2) + 4))
  State p := Fin (2 * (4 * p.1 + 2) + 4)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => p.2.idxOf i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ => p.2.length) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀
    (n : ℕ) (hn : 1 ≤ n)
    (sigma : List (Fin (2 * (4 * n + 2) + 4))) (j : ℕ)
    (hj : j ≤ 2 * (4 * n + 2) + 4)
    (hold : OriginalOrder (2 * (4 * n + 2) + 4)
      (1 + 2 ^ (4 * n + 2) + 2 ^ (4 * n + 2 + 2) + 2 ^ (2 * (4 * n + 2) + 2)) sigma)
    (hnew : OriginalOrder (2 * (4 * n + 2) + 4 + 1)
      (2 * (1 + 2 ^ (4 * n + 2) + 2 ^ (4 * n + 2 + 2) + 2 ^ (2 * (4 * n + 2) + 2)))
      (earWord (2 * (4 * n + 2) + 4) sigma j)),
    let t := 4 * n + 2
    let k := 2 * t + 4
    let A := 1 + 2 ^ t + 2 ^ (t + 2) + 2 ^ (2 * t + 2)
    let alpha : Fin k := ⟨1, by omega⟩
    let gamma : Fin k := ⟨t + 3, by omega⟩
    let delta : Fin k := ⟨k - 1, by omega⟩
    R.readout () ⟨n, sigma⟩ delta < sigma.idxOf alpha ∧ sigma.idxOf delta < sigma.idxOf gamma ∧
    j ≤ sigma.idxOf alpha ∧ j ≤ sigma.idxOf gamma ∧
    (∀ i : Fin k, actualSource k A i < 0 → sigma.idxOf i < sigma.idxOf delta → i.val = t + 1) ∧
    Set.Subsingleton {i : Fin k | actualSource k A i < 0 ∧
      sigma.idxOf i < sigma.idxOf delta} ∧
    (∀ i : Fin k, actualSource k A i < 0 ↔
      i.val = 1 ∨ i.val = t + 1 ∨ i.val = t + 3 ∨ i.val = k - 1)

private def sample : List (Fin 16) := [14,4,15,8,13,11,10,1,6,5,7,0,12,3,2,9]

private theorem old_sample : OriginalOrder 16 16705 sample := by
  refine ⟨by decide, by decide, ?_⟩
  intro r
  have hh := inStrip_prefix (f := actualSource 16 16705) (B := 32767) (h := 0)
    (l := sample) (by norm_num [sample, InStrip, actualSource, centered, modulus]) r
  simpa [modulus] using hh

private theorem new_sample : OriginalOrder 17 (2*16705) (earWord 16 sample 0) := by
  refine ⟨by decide, by decide, ?_⟩
  intro r
  have hh := inStrip_prefix (f := actualSource 17 (2*16705)) (B := 65535) (h := 0)
    (l := earWord 16 sample 0)
    (by norm_num [sample, earWord, InStrip, actualSource, centered, modulus]) r
  simpa [modulus] using hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) sample 0 (by decide) old_sample new_sample
  norm_num [rejected,realize,sample] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, List.finRange 16⟩, 0, 1, ?_⟩
  change (List.finRange 16).idxOf (0 : Fin 16) ≠ (List.finRange 16).idxOf (1 : Fin 16)
  decide

def source_registration : Registration arena (type_of% (@actualSource_four_gap_lattice_precedence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_four_gap_lattice_precedence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence.actualSource_four_gap_lattice_precedence)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence.actualSource_four_gap_lattice_precedence.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #[
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "fn", "arg", "fn",
      "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end Reg.D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
