import D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension

open _root_.D5.S3.Combinatorics.Graph.PrefixHamming
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open Finset LeanInformationAudit

private abbrev Parameters := Σ n : ℕ, Equiv.Perm (Fin n)

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Equiv.Perm (Fin p.1)) (fun _ => ℕ)

private def constantOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem prefix_observation_varies :
    prefixDistance (1 : Equiv.Perm (Fin 3)) 1 ≠
      prefixDistance (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) := by
  decide

namespace Dimension

private def actual : Realization signature :=
  realize signature (fun _ p q =>
    2 * (univ.filter fun k : Rank p.1 => prefixSet p.2 k.val.val ≠ prefixSet q k.val.val).card)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (_ : 3 ≤ n),
    (∃ f : Equiv.Perm (Fin n) → Fin d → Bool,
      ∀ p q, hammingDist (f p) (f q) = R.readout () ⟨n, p⟩ q) ↔
      (if n = 4 then 12 else 2 ^ n - 2) ≤ d

private theorem constant_one_invalid : ¬ arena.Law constantOne := by
  intro law
  obtain ⟨f, hf⟩ := (law 3 6 (by decide)).mpr (by decide)
  have same := hf 1 1
  simpa [constantOne, realize] using same

def evidence : Registration arena (type_of% (@minimum_hamming_dimension)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_hamming_dimension, constantOne, constant_one_invalid⟩
  sensitivity := sensitivity arena.Law actual constantOne constant_one_invalid
  dependence := by
    intro role
    cases role
    exact ⟨⟨3, 1⟩, 1, Equiv.swap 0 1, prefix_observation_varies⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@minimum_hamming_dimension) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.PrefixHamming.minimum_hamming_dimension.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension.Dimension.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p q =>
    2 * (univ.filter fun k : Rank p.1 => prefixSet p.2 k.val.val ≠ prefixSet q k.val.val).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dimension

end Reg.D5.S3.Combinatorics.Graph.PrefixHamming.ExactDimension
