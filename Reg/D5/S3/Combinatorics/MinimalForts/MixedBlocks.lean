import Reg.Support.DependentFamily
import D5.S3.Combinatorics.MinimalForts.MixedBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.MinimalForts.MixedBlocks

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MinimalForts.UniversalRoot
open _root_.D5.S3.Combinatorics.MinimalForts.MixedBlocks

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ × ℕ × ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun i _ s => if i then
    (minimalForts (graph s.1 s.2.1 s.2.2.1 s.2.2.2)).card
    else Fintype.card (Vertex s.1 s.2.1 s.2.2.1 s.2.2.2)) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x y z r : ℕ,
    R.readout false () (x,y,z,r) = 6 * (x+y+z) + r + 3 ∧
    (graph x y z r).Connected ∧
    R.readout true () (x,y,z,r) =
      (r+2)*6^x*9^y*12^z + 15*x + 6*y + 11*z + (r+2).choose 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := (h 0 0 0 0).1
  norm_num [rejected, realize] at ha

private abbrev altered (i : Bool) : Realization signature :=
  realize signature (fun j p s => if j = i then 0 else actual.readout j p s)
    (fun e => nomatch e)

private theorem altered_law (i : Bool) : ¬ arena.Law (altered i) := by
  intro h
  cases i with
  | false =>
    have ha := (h 0 0 0 0).1
    norm_num [altered, realize] at ha
  | true =>
    have ha := (h 0 0 0 0).2.2
    norm_num [altered, realize, show Nat.choose 2 2 = 1 by decide] at ha

/-- The source model retains actual graph order, connectedness and all-fort cardinalities. -/
def family : Registration arena (type_of% (@mixed_graph_count)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_graph_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨altered i, ?_, rfl, altered_law i⟩
      intro j hj
      simp only [altered, realize, if_neg hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0,0,0,0), (0,0,0,1), ?_⟩
    cases i with
    | false =>
      change Fintype.card (Vertex 0 0 0 0) ≠ Fintype.card (Vertex 0 0 0 1)
      rw [(mixed_graph_count 0 0 0 0).1, (mixed_graph_count 0 0 0 1).1]
      decide
    | true =>
      change (minimalForts (graph 0 0 0 0)).card ≠ (minimalForts (graph 0 0 0 1)).card
      rw [(mixed_graph_count 0 0 0 0).2.2, (mixed_graph_count 0 0 0 1).2.2]
      norm_num [show Nat.choose 2 2 = 1 by decide, show Nat.choose 3 2 = 3 by decide]

end Reg.D5.S3.Combinatorics.MinimalForts.MixedBlocks
