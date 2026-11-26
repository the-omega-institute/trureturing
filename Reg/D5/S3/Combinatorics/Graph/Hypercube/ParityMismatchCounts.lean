import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
import Reg.Support.DependentFamily

/-! An intervention on the threshold changes the integer parity-cut test. -/

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts

open Finset LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
open _root_.D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => k * 2 ^ n) (fun e => nomatch e)

def zeroThreshold : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) [NeZero k] (a : Fin (n + 2) → ℕ),
    (∃ W : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, W p q = k) ∧ (∀ q, ∑ p, W p q = k) ∧
      ∀ i, (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) = 2 * a i) ↔
    (∀ i, a i ≤ k * 2 ^ n) ∧
    ∀ e : Profile (n + 2), parity e = 0 →
      R.readout () n k ≤ ∑ i, if e i = 0 then a i else k * 2 ^ n - a i

private theorem zero_threshold_fails : ¬ arena.Law zeroThreshold := by
  intro law
  have falseCut := (exact_integer_parity_mismatch_counts 0 1 (fun _ => 0)).mp
    ((law 0 1 (fun _ => 0)).mpr
      ⟨fun _ => Nat.zero_le _, fun _ _ => Nat.zero_le _⟩)
  have h := falseCut.2 0 (by simp [parity])
  norm_num at h

def family : Registration arena (type_of% exact_integer_parity_mismatch_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_integer_parity_mismatch_counts, zeroThreshold, zero_threshold_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroThreshold, ?_, rfl, zero_threshold_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    cases role
    exact ⟨0, 1, 2, by decide⟩


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_integer_parity_mismatch_counts (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts.cutThreshold
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => k * 2 ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
