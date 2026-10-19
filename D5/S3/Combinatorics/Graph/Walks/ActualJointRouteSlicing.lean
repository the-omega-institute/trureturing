/- GID: D5/S3/Combinatorics/Graph/Walks/ActualJointRouteSlicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualJointRouteSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual retained joint edges and ordered route cuts produce the literal P and Q fragments used by graph surgery. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
import D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
open D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
open D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder
open private join join_support from
  D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The actual previous joint state supplies the first rooted path and
retained edges; the actual single-order state supplies all B paths. The
final strict cut order is derived from these data and their E/O route. -/
theorem actual_joint_and_route_three_fragments {base : V}
    (joint : List (Piece G))
    (hjn : (joint.flatMap fun z => z.walk.support).Nodup)
    (jp : Piece G) (hjp : jp ∈ joint) (hjpath : jp.walk.IsPath)
    (p : Piece G) (ps : List (Piece G)) (hlink : Linked p ps)
    (Λ : G.Walk p.start (finish p ps))
    (hΛsupport : Λ.support = (p :: ps).flatMap fun z => z.walk.support)
    (hbn : ((p :: ps).flatMap fun z => z.walk.support).Nodup)
    (hbpath : ∀ z ∈ p :: ps, z.walk.IsPath)
    (hroot : jp.start = p.start)
    (w : G.Walk base base) (K H : Finset (Sym2 V))
    (hjointInventory : ∀ e, e ∈ joint.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hboundaryInventory : ∀ e, e ∈ (p :: ps).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K)
    {s : ℕ} (hspos : 0 < s) (hs : s < (p :: ps).length)
    {w₀ w₁ r₀ ℓ₀ r₁ ℓ₁ : V}
    (hjfinish : jp.finish = w₁)
    (hbfinish : ((p :: ps)[s]'hs).finish = w₀)
    (hja : s(w₁, r₀) ∈ joint.flatMap (fun z => z.walk.edges))
    (hjb : s(r₀, ℓ₀) ∈ joint.flatMap (fun z => z.walk.edges)) (hℓ₀ : ℓ₀ ≠ w₁)
    (hba : s(w₀, r₁) ∈ joint.flatMap (fun z => z.walk.edges))
    (hbb : s(r₁, ℓ₁) ∈ joint.flatMap (fun z => z.walk.edges)) (hℓ₁ : ℓ₁ ≠ w₀) :
    ∃ q₀ : G.Walk p.start ℓ₀, ∃ q₁ : G.Walk r₀ ℓ₁,
      ∃ q₂ : G.Walk r₁ (finish p ps),
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
        Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  have hrestore : ∀ e ∈ joint.flatMap (fun z => z.walk.edges),
      e ∈ (p :: ps).flatMap (fun z => z.walk.edges) := by
    intro e he
    have hj := (hjointInventory e).mp he
    exact (hboundaryInventory e).mpr
      ⟨hj.1, fun hk => hj.2 (Finset.mem_union.mpr (Or.inl hk))⟩
  have hja' : s(jp.finish, r₀) ∈ jp.walk.edges :=
    actual_partition_incident_edge_owner joint hjn jp hjp jp.walk.end_mem_support
      (hjfinish.symm ▸ hja)
  have hr₀ : r₀ ∈ jp.walk.support := jp.walk.snd_mem_support_of_mem_edges hja'
  have hjb' : s(r₀, ℓ₀) ∈ jp.walk.edges :=
    actual_partition_incident_edge_owner joint hjn jp hjp hr₀ hjb
  let q : G.Walk p.start w₁ := jp.walk.copy hroot hjfinish
  have hqpath : q.IsPath := by
    simpa only [q, SimpleGraph.Walk.isPath_copy] using hjpath
  have hkeep : ∀ e ∈ q.edges, e ∈ (p :: ps).flatMap (fun z => z.walk.edges) := by
    intro e he
    apply hrestore e
    apply List.mem_flatMap.mpr
    exact ⟨jp, hjp, by simpa only [q, SimpleGraph.Walk.edges_copy] using he⟩
  obtain ⟨i, hi, hil, hir⟩ := actual_restored_joint_cut_position
    (p :: ps) hbn p List.mem_cons_self (hbpath p List.mem_cons_self) q hqpath hkeep
    (by simpa only [q, SimpleGraph.Walk.edges_copy, hjfinish] using hja')
    (by simpa only [q, SimpleGraph.Walk.edges_copy] using hjb') hℓ₀
  let lastPiece := (p :: ps)[s]'hs
  have hlast : lastPiece ∈ p :: ps := List.getElem_mem hs
  have hba' : s(lastPiece.finish, r₁) ∈ lastPiece.walk.edges :=
    actual_partition_incident_edge_owner (p :: ps) hbn lastPiece hlast
      lastPiece.walk.end_mem_support (hbfinish.symm ▸ hrestore _ hba)
  have hr₁ : r₁ ∈ lastPiece.walk.support :=
    lastPiece.walk.snd_mem_support_of_mem_edges hba'
  have hbb' : s(r₁, ℓ₁) ∈ lastPiece.walk.edges :=
    actual_partition_incident_edge_owner (p :: ps) hbn lastPiece hlast hr₁ (hrestore _ hbb)
  obtain ⟨j, hj, hjl, hjr⟩ := actual_retained_suffix_cut_position
    lastPiece.walk (hbpath lastPiece hlast) hba' hbb'
      (by simpa only [lastPiece, hbfinish] using hℓ₁)
  have hpath : (join p ps hlink).IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [join_support]
    exact hbn)
  have hΛ : Λ = join p ps hlink := by
    apply SimpleGraph.Walk.ext_support
    rw [join_support]
    exact hΛsupport
  rw [hΛ]
  exact actual_joined_route_two_cut_slicing p ps hlink hpath hspos hs
    (by simpa only [List.getElem_cons_zero] using hi) hj
    (by simpa only [List.getElem_cons_zero] using hil)
    (by simpa only [List.getElem_cons_zero] using hir) hjl hjr

#print axioms actual_joint_and_route_three_fragments

end D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing
