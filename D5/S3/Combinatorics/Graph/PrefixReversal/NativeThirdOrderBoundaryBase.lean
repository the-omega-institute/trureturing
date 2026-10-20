/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeThirdOrderBoundaryBase
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeThirdOrderBoundaryBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restore the Actual Native Third-Order Base State. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
import D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeThirdOrderBoundaryBase

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase
open private R L cut cuts from
  D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase

universe v
variable {V : Type v} [DecidableEq V] {G : SimpleGraph V}

/-- The actual third-order base has precisely the two native marked
groups of this same cycle. Its primary boundary is O3 and its opposite
boundary is E3, with the distinguished and crossing identities kept. -/
theorem native_third_order_boundary_base {m : ℕ} {base : V}
    (F₀ F₁ : SupplyFrame m 3) (raw : V → Configuration m)
    (p : Bool × Fin 4 × Bool → V) (hp : Function.Injective p)
    (hports : ∀ (t : Bool) (i : Fin 4),
      raw (R p t i) = rightPort (if t then F₁ else F₀) i.val ∧
      raw (L p t i) = leftPort (if t then F₁ else F₀) i.val)
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (d : G.Walk (L p false 0) (L p false 2))
    (cross : G.Walk (R p false 0) (L p true 0))
    (g : G.Walk (R p true 0) (L p true 1))
    (a : G.Walk (R p false 1) (R p false 2))
    (b : G.Walk (L p true 3) (R p false 3))
    (q : G.Walk (R p true 2) (L p false 3))
    (e : G.Walk (R p true 1) (R p true 3))
    (f : G.Walk (L p true 2) (L p false 1))
    (hjoint : ActualCyclePartition c (cuts p false ∪ cuts p true)
      [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a⟩,
        ⟨_, _, b⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩]) :
    ∃ primary₁ : G.Walk (R p false 0) (R p false 3),
      ∃ primary₂ : G.Walk (L p false 1) (L p false 3),
      ∃ opposite₀ : G.Walk (L p true 0) (L p true 2),
      ∃ opposite₂ : G.Walk (R p true 2) (L p true 3),
      let primary : List (Piece G) :=
        [⟨_, _, d⟩, ⟨_, _, a⟩, ⟨_, _, primary₁⟩, ⟨_, _, primary₂⟩]
      let opposite : List (Piece G) :=
        [⟨_, _, opposite₀⟩, ⟨_, _, g⟩, ⟨_, _, e⟩, ⟨_, _, opposite₂⟩]
      ActualTwoOrderPartitions c (cuts p false) (cuts p true)
        [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a⟩,
          ⟨_, _, b⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩] primary opposite ∧
      NativeBoundaryPairs F₀ true raw primary ∧ NativeBoundaryPairs F₁ false raw opposite ∧
      (cuts p false).image (Sym2.map raw) = markedCuts F₀ ∧
      (cuts p true).image (Sym2.map raw) = markedCuts F₁ ∧
      ∃ hzero : G.Adj (R p false 0) (L p false 0),
        ∃ tail : G.Walk (L p false 2) (L p true 2),
          opposite₀ = (cross.reverse.concat hzero).append (d.append tail) := by
  classical
  obtain ⟨primary₁, primary₂, opposite₀, opposite₂, hstate, hprefix⟩ :=
    actual_third_order_boundary_base p hp c hc d cross g a b q e f hjoint
  have hcuts (t : Bool) : (cuts p t).image (Sym2.map raw) =
      markedCuts (if t then F₁ else F₀) := by
    simp only [cuts, Finset.image_image, markedCuts]
    apply congrArg (fun z : Fin 4 → Sym2 (Configuration m) => Finset.univ.image z)
    funext i
    change s(raw (R p t i), raw (L p t i)) =
      s(rightPort (if t then F₁ else F₀) i.val, leftPort (if t then F₁ else F₀) i.val)
    rw [(hports t i).1, (hports t i).2]
  refine ⟨primary₁, primary₂, opposite₀, opposite₂, hstate, ?_, ?_,
    hcuts false, hcuts true, hprefix⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨(0, 1), (2, 1), by simpa [specialPort] using (hports false 0).2,
        by simpa [specialPort] using (hports false 2).2, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(1, 0), (2, 0), by simpa [specialPort] using (hports false 1).1,
        by simpa [specialPort] using (hports false 2).1, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(0, 0), (3, 0), by simpa [specialPort] using (hports false 0).1,
        by simpa [specialPort] using (hports false 3).1, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(1, 1), (3, 1), by simpa [specialPort] using (hports false 1).2,
        by simpa [specialPort] using (hports false 3).2, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨(0, 1), (2, 1), by simpa [specialPort] using (hports true 0).2,
        by simpa [specialPort] using (hports true 2).2, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(0, 0), (1, 1), by simpa [specialPort] using (hports true 0).1,
        by simpa [specialPort] using (hports true 1).2, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(1, 0), (3, 0), by simpa [specialPort] using (hports true 1).1,
        by simpa [specialPort] using (hports true 3).1, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩
    · exact ⟨(2, 0), (3, 1), by simpa [specialPort] using (hports true 2).1,
        by simpa [specialPort] using (hports true 3).2, by norm_num [oddBoundary, evenBoundary, pair, ladder, code]⟩

#print axioms native_third_order_boundary_base

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeThirdOrderBoundaryBase
