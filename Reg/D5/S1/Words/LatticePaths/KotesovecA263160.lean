import D5.S1.Words.LatticePaths.KotesovecA263160
import Reg.Support.DependentFamily

/-! Typed insertion-family evidence. The Contract source-selection binding remains
unfinished: https://github.com/the-omega-institute/trureturing/issues/29924. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
namespace Reg.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity
open _root_.D5.S1.Words.LatticePaths.KotesovecA263160

abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p t => internal_words p.1 p.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d m k : ℕ,
    (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      ∑ t ∈ Finset.range (k + 1), k.choose t * R.readout () (d,m) t

private theorem rejected_failure : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0 0
  norm_num [rejected, realize] at h0

noncomputable def family : Registration arena (type_of% (@_root_.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    have h0 := _root_.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity 0 0 0
    have h1 := _root_.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity 0 0 1
    norm_num at h0 h1
    refine ⟨(0,0),0,1,?_⟩
    change internal_words 0 0 0 ≠ internal_words 0 0 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
    norm_num at h1
    omega
end Reg.D5.S1.Words.LatticePaths.KotesovecA263160.insertion_identity
