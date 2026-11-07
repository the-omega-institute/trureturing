import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! A full physical-telescope dependent-family registration attempt.
The seed is observed, including every physical clause of the source target. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open private bits_seed from D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ l => (bits l).toNat) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 6) (fun e => nomatch e)

private def physicalSeed {p : ℕ} (gaps : Fin p → ℕ) (e : ℕ) : Prop :=
  let k := period gaps
  let N := modulus k
  let H := N / 2
  ∃ wp wm : List (Fin k), ∃ cs : List (CornerRecord k),
    wp.Perm (List.finRange k) ∧ wm.Perm (List.finRange k) ∧
    (earWord k wp 0).Perm (List.finRange (k + 1)) ∧
    (earWord k wm 0).Perm (List.finRange (k + 1)) ∧
    (earWord k wp 0).head? = some (Fin.last k) ∧
    (earWord k wm 0).head? = some (Fin.last k) ∧
    actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) ∧
    oldPrefix k e wp (k + 1) = 0 ∧ newPrefix k e wp (k + 1) = 0 ∧
    oldPrefix k e wm (k + 1) = 0 ∧ newPrefix k e wm (k + 1) = 0 ∧
    (∀ q : ℕ, 0 ≤ oldPrefix k e wp q ∧ 0 ≤ newPrefix k e wp q) ∧
    (∀ q : ℕ, oldPrefix k e wm q ≤ H ∧ newPrefix k e wm q ≤ N) ∧
    cs.length ≤ p - 1 ∧
    (cs.map CornerRecord.prefixLength).Nodup ∧
    (cs.flatMap (fun c => [c.positive,c.terminal])).Nodup ∧
    (∀ c ∈ cs,
      0 < actualSource k e c.positive ∧
      0 < actualSource (k + 1) (2 * e) c.positive.castSucc ∧
      actualSource k e c.terminal < 0 ∧
      actualSource (k + 1) (2 * e) c.terminal.castSucc < 0 ∧
      IsStrictSplit gaps c.positive c.terminal ∧
      ∃ u v u' v' : List (Fin k),
        wp = u ++ [c.positive,c.terminal] ++ v ∧
        wm = u' ++ [c.terminal,c.positive] ++ v' ∧
        c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2) ∧
    swapAlong (cs.map (fun c => (c.positive,c.terminal))) wp = wm ∧
    (∀ q : ℕ, H < oldPrefix k e wp q ∨ N < newPrefix k e wp q →
      q ∈ cs.map CornerRecord.prefixLength) ∧
    (∀ q : ℕ, oldPrefix k e wm q < 0 ∨ newPrefix k e wm q < 0 →
      q ∈ cs.map CornerRecord.prefixLength) ∧
    ((Finset.univ : Finset (Fin (k + 2))).filter (fun q =>
      H < oldPrefix k e wp q.val ∨ N < newPrefix k e wp q.val)).card ≤ cs.length ∧
    ((Finset.univ : Finset (Fin (k + 2))).filter (fun q =>
      oldPrefix k e wm q.val < 0 ∨ newPrefix k e wm q.val < 0)).card ≤ cs.length

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ), 1 ≤ p → ∀ (gaps : Fin p → ℕ),
    (∀ j, 2 ≤ gaps j) → physicalSeed gaps (R.readout () () (gapList gaps))

private theorem actual_bridge : (type_of% (@uniform_sparse_necklace_rounding)) ↔ arena.Law actual := by
  constructor
  · intro h p hp gaps hg
    change physicalSeed gaps ((bits (gapList gaps)).toNat)
    rw [bits_seed,Int.toNat_natCast]
    exact h p hp gaps hg
  · intro h p hp gaps hg
    have hh := h p hp gaps hg
    change physicalSeed gaps ((bits (gapList gaps)).toNat) at hh
    rw [bits_seed,Int.toNat_natCast] at hh
    exact hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) (fun _ => 2) (by intro j; decide)
  change physicalSeed (fun _ : Fin 1 => 2) 6 at hh
  rcases hh with ⟨wp,wm,cs,hh⟩
  have hf := hh.2.2.2.2.2.2.1
  norm_num [period,actualSource,centered,modulus] at hf

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),[],[2],?_⟩
  norm_num [actual,realize,bits]

/-- Every source binder and every physical clause is retained. Structural
source-occurrence enrollment remains a separate native binding obligation. -/
def source_registration : Registration arena (type_of% (@uniform_sparse_necklace_rounding)) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp uniform_sparse_necklace_rounding,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := actual_dependence

/-- Typed Contract attempt; absent sourceSelection is disclosed rather than
reported as a validated current binding. -/
noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@uniform_sparse_necklace_rounding)
    (type_of% (realize signature (fun _ _ l => (bits l).toNat) (fun e => nomatch e))) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint.uniform_sparse_necklace_rounding.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => (bits l).toNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint
