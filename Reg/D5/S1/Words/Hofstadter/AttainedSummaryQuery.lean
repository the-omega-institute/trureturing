import D5.S1.Words.Hofstadter.AttainedSummaryQuery
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S1.Words.Hofstadter.OriginalHFoundation (Letter tau)
open _root_.D5.S1.Words.RankOneMorphismIterationBound (image)
open _root_.D5.S1.Words.Hofstadter.AttainedSummaryQuery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Hofstadter.AttainedSummaryQuery

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Top
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => acquire) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ),
    let z := R.readout () () N
    z.summary = generated z.layer ∧
    N ≤ z.summary.lengths.three ∧
    (∀ t, t < z.layer → (generated t).lengths.three < N) ∧
    (∀ t, N ≤ (generated t).lengths.three →
      (∀ k, k < t → (generated k).lengths.three < N) → t = z.layer) ∧
    N < 2 ^ analysisBits N ∧
    (∀ b, b < analysisBits N → 2 ^ b ≤ N) ∧
    z.layer ≤ 3 * analysisBits N ∧
    (∀ t a, (generated t).lengths.at a = (image tau t a).length ∧
      (generated t).counts.at a = (image tau t a).count .one ∧
      (generated t).counts.at a ≤ (generated t).lengths.at a ∧
      (generated t).lengths.at a ≤ 2 ^ t) ∧
    (∀ m, m ≤ N →
      (∀ k, k ≤ z.layer →
        let q := trajectory z .three m k;
        q.layer = z.layer - k ∧
        Invariant (((image tau z.layer .three).take m).count .one) m q ∧ Legal q) ∧
      (let q := trajectory z .three m z.layer;
        q.layer = 0 ∧ (q.residual = 0 ∨ q.residual = 1)) ∧
      query z m = ((image tau z.layer .three).take m).count .one ∧
      query z m ≤ m ∧ m - query z m ≤ m)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨0, ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩⟩)
    (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1).2.1
  change 1 ≤ 0 at hh
  omega

def family : Registration arena (type_of% attained_summary_query) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attained_summary_query, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change acquire 1 ≠ acquire 2
    intro he
    have h1 := attained_summary_query 1
    have h2 := attained_summary_query 2
    have ht : (acquire 1).layer = 0 := by
      by_contra hn
      have hh := h1.2.2.1 0 (by omega)
      change 1 < 1 at hh
      omega
    have hz := h2.1
    rw [← he, ht] at hz
    have hh := h2.2.1
    rw [← he, hz] at hh
    change 2 ≤ 1 at hh
    omega

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    attained_summary_query (type_of% actual) (ℕ → Top) Unit := {
  unitName := `D5.S1.Words.Hofstadter.AttainedSummaryQuery.attained_summary_query.__information_unit,
  realizationName := `Reg.D5.S1.Words.Hofstadter.AttainedSummaryQuery.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Hofstadter.AttainedSummaryQuery, definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.Hofstadter.AttainedSummaryQuery
