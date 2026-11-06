import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev PhysicalState := Σ r : ℕ, Fin (3 * (18 * r + 12))

abbrev signature : Signature where
  Params := Unit
  State _ := PhysicalState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s =>
    actualSource (3 * (18 * s.1 + 12))
      ((2 ^ (18 * s.1 + 12) - 1) * (2 * 2 ^ (18 * s.1 + 12) - 3)) s.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ),
    let d : ℕ := 18 * r + 12
    let B : ℕ := 2 ^ d
    let g : ℕ := B - 1
    let t : ℕ := g * (2 * B - 3)
    let Q : ℕ := (B ^ 2 + B + 1) / 19
    let A : Finset (Fin (3 * d)) :=
      Finset.univ.filter (fun i => Nat.testBit Q i.val = true)
    let C : Finset (Fin (3 * d)) :=
      Finset.univ.filter (fun i => Nat.testBit (2 * Q) i.val = true)
    (∑ i ∈ A, R.readout () () ⟨r, i⟩) = (0 : ℤ) ∧
    (∑ i ∈ C, R.readout () () ⟨r, i⟩) = (0 : ℤ) ∧
    (511 : ℤ) * (∑ i ∈ A ∩ C, R.readout () () ⟨r, i⟩) =
      -((B : ℤ) - 1) * (80 * (B : ℤ) ^ 2 - 1111 * (B : ℤ) + 1724) ∧
    (∑ i ∈ A ∩ C, R.readout () () ⟨r, i⟩) < (0 : ℤ)

private theorem actual_law : arena.Law actual := by
  intro r
  simpa only [actual, realize] using
    (D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection r)

private theorem source_equivalence :
    (type_of% (@D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection))
      ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 0
  norm_num [rejected, realize] at h

set_option maxHeartbeats 1000000 in
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), ⟨0, ⟨0, by decide⟩⟩, ⟨0, ⟨1, by decide⟩⟩, ?_⟩
  change actualSource 36 ((2 ^ 12 - 1) * (2 * 2 ^ 12 - 3)) ⟨0, by decide⟩ ≠
    actualSource 36 ((2 ^ 12 - 1) * (2 * 2 ^ 12 - 3)) ⟨1, by decide⟩
  norm_num [actual, realize, actualSource, centered, modulus]

set_option maxHeartbeats 1000000 in
-- The full telescope and dependent physical-state sensitivity require extra elaboration budget.
def family : Registration arena
    (type_of% (@D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.exceptional19_zero_pair_intersection)
    (Realization signature) Nat Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean
    "exceptional19_zero_pair_intersection.__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    actualSource (3 * (18 * s.1 + 12))
      ((2 ^ (18 * s.1 + 12) - 1) * (2 * 2 ^ (18 * s.1 + 12) - 3)) s.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "body"],
      stateBinder := 8,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Nonboolean
