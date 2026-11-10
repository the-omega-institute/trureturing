/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubGraph
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubGraph
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub graph identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubSource
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
namespace FiolDoubleHub

theorem nonloop (m : ℕ) (e : Edge m) : src e ≠ tgt e := by
  rcases e with ⟨b,o⟩
  cases o <;> simp [src,tgt]

private theorem edge_inj (m : ℕ) :
    Function.Injective (fun e : Edge m => s(src e, tgt e)) := by
  intro e e' he
  rcases Sym2.eq_iff.mp he with he | he
  · exact Option.some.inj he.1
  · rcases e with ⟨b,o⟩
    rcases e' with ⟨b',o'⟩
    cases o <;> cases o' <;> simp_all [src,tgt]

private theorem actual_adj (m : ℕ) (e : Edge m) :
    (graph m).Adj (src e) (tgt e) := by
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  exact ⟨⟨⟨e,Set.mem_univ e⟩, rfl⟩, nonloop m e⟩

private theorem actual_connected (m : ℕ) : (graph m).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.refl _
  | some e =>
    rcases e with ⟨b,o⟩
    cases o with
    | none => exact (actual_adj m (b,none)).symm.reachable
    | some i =>
      exact (actual_adj m (b,none)).symm.reachable.trans
        (actual_adj m (b,some i)).symm.reachable

private theorem edge_count (m : ℕ) : Nat.card (graph m).edgeSet = 2*m+2 := by
  classical
  let f : Edge m → (graph m).edgeSet := fun e =>
    ⟨s(src e,tgt e), by
      change s(src e,tgt e) ∈ (SimpleGraph.fromEdgeSet _).edgeSet
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨⟨⟨e,Set.mem_univ e⟩,rfl⟩, by
        simpa only [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using nonloop m e⟩⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact edge_inj m (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro a
    have ha := a.2
    change a.1 ∈ (SimpleGraph.fromEdgeSet _).edgeSet at ha
    rw [SimpleGraph.edgeSet_fromEdgeSet] at ha
    obtain ⟨e,he⟩ := ha.1
    exact ⟨e.1,Subtype.ext he⟩
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  rw [← hc, Nat.card_eq_fintype_card]
  simp [Edge]
  omega

theorem actual_tree (m : ℕ) : (graph m).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨actual_connected m, ?_⟩
  rw [edge_count, Nat.card_eq_fintype_card]
  simp [Vertex,Edge]
  omega

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
