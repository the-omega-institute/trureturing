/- GID: D5/S3/Combinatorics/Graph/Walks/ActualBaseJointRouteSlicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualBaseJointRouteSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Slice the Exceptional Base Q Route from Actual Joint Pieces. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualBaseJointRouteSlicing

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
open D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
open D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder
open private join join_support join_edges from
  D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The base middle boundary consists of three particular J paths.
Exact source inventories earn its literal refinement. The retained cuts
lie in its first and third J paths, so the two-cut split belongs to the
same supplied Λ and has no assumed comparison of positions. -/
theorem actual_base_joint_route_three_fragments {base : V}
    (w : G.Walk base base) (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (p₁ p₂ p₃ : Piece G) (rest : List (Piece G))
    (hjn : ((p₁ :: p₂ :: p₃ :: rest).flatMap fun z => z.walk.support).Nodup)
    (hjointInventory : ∀ e, e ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hcuts : ∀ e ∈ K ∪ H, e ∈ w.edges)
    (hseam₁ : s(p₁.finish, p₂.start) ∈ H)
    (hseam₂ : s(p₂.finish, p₃.start) ∈ H)
    (p₀ p₄ : Piece G) (old : G.Walk p₁.start p₃.finish)
    (hboundaryLink : Linked p₀ [⟨p₁.start, p₃.finish, old⟩, p₄])
    (hbn : ((p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
      fun z : Piece G => z.walk.support).Nodup)
    (hboundaryInventory : ∀ e,
      e ∈ (p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
        (fun z : Piece G => z.walk.edges) ↔ e ∈ w.edges ∧ e ∉ K)
    (Λ : G.Walk p₀.start p₄.finish)
    (hΛsupport : Λ.support = p₀.walk.support ++ old.support ++ p₄.walk.support)
    {r₀ ℓ₀ r₁ ℓ₁ : V}
    (hja : s(p₁.finish, r₀) ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges))
    (hjb : s(r₀, ℓ₀) ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges))
    (hneq₀ : ℓ₀ ≠ p₁.finish)
    (hba : s(p₃.finish, r₁) ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges))
    (hbb : s(r₁, ℓ₁) ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges))
    (hneq₁ : ℓ₁ ≠ p₃.finish) :
    ∃ q₀ : G.Walk p₀.start ℓ₀, ∃ q₁ : G.Walk r₀ ℓ₁,
      ∃ q₂ : G.Walk r₁ p₄.finish,
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  have h₁₂ : G.Adj p₁.finish p₂.start :=
    w.adj_of_mem_edges (hcuts _ (Finset.mem_union.mpr (Or.inr hseam₁)))
  have h₂₃ : G.Adj p₂.finish p₃.start :=
    w.adj_of_mem_edges (hcuts _ (Finset.mem_union.mpr (Or.inr hseam₂)))
  have hlinkTrip : Linked p₁ [p₂, p₃] := ⟨h₁₂, h₂₃, trivial⟩
  let trip : G.Walk p₁.start p₃.finish := join p₁ [p₂, p₃] hlinkTrip
  have htripSupport : trip.support =
      (p₁ :: p₂ :: p₃ :: []).flatMap (fun z => z.walk.support) :=
    join_support p₁ [p₂, p₃] hlinkTrip
  have htripEdges : trip.edges = chainEdges p₁ [p₂, p₃] :=
    join_edges p₁ [p₂, p₃] hlinkTrip
  have hntrip : trip.support.Nodup := by
    rw [htripSupport]
    exact (List.nodup_append'.mp (show
      (((p₁ :: p₂ :: p₃ :: []).flatMap fun z => z.walk.support) ++
        rest.flatMap fun z => z.walk.support).Nodup by
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc] using hjn)).1
  have htripPath : trip.IsPath := SimpleGraph.Walk.IsPath.mk' hntrip
  have hnotK (e : Sym2 V) (he : e ∈ H) : e ∉ K :=
    fun hk => Finset.disjoint_left.mp hdisjoint hk he
  have hjointKeep (p : Piece G) (hp : p ∈ p₁ :: p₂ :: p₃ :: rest)
      (e : Sym2 V) (he : e ∈ p.walk.edges) : e ∈ w.edges ∧ e ∉ K := by
    have h := (hjointInventory e).mp (List.mem_flatMap.mpr ⟨p, hp, he⟩)
    exact ⟨h.1, fun hk => h.2 (Finset.mem_union.mpr (Or.inl hk))⟩
  have htripKeep : ∀ e ∈ trip.edges,
      e ∈ (p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
        (fun z : Piece G => z.walk.edges) := by
    intro e he
    rw [htripEdges] at he
    simp only [chainEdges, List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at he
    apply (hboundaryInventory e).mpr
    rcases he with he | rfl | he | rfl | he
    · exact hjointKeep p₁ (by simp) e he
    · exact ⟨hcuts _ (Finset.mem_union.mpr (Or.inr hseam₁)), hnotK _ hseam₁⟩
    · exact hjointKeep p₂ (by simp) e he
    · exact ⟨hcuts _ (Finset.mem_union.mpr (Or.inr hseam₂)), hnotK _ hseam₂⟩
    · exact hjointKeep p₃ (by simp) e he
  let oldPiece : Piece G := ⟨p₁.start, p₃.finish, old⟩
  have holdPath : old.IsPath := SimpleGraph.Walk.IsPath.mk'
    ((List.nodup_flatMap.mp hbn).1 oldPiece (by simp [oldPiece]))
  obtain ⟨tail, hold, htail⟩ := actual_restored_partition_joint_prefix
    (p₀ :: oldPiece :: p₄ :: []) hbn oldPiece (by simp) holdPath trip htripPath htripKeep
  have htailNil : tail = .nil := (SimpleGraph.Walk.isPath_iff_nil.mp htail).eq_nil
  have holdTrip : old = trip := by
    simpa only [oldPiece, htailNil, SimpleGraph.Walk.append_nil] using hold
  obtain ⟨h₀₁, h₃₄, _⟩ := hboundaryLink
  have hlinkFull : Linked p₀ [p₁, p₂, p₃, p₄] := ⟨h₀₁, h₁₂, h₂₃, h₃₄, trivial⟩
  let full : G.Walk p₀.start p₄.finish := join p₀ [p₁, p₂, p₃, p₄] hlinkFull
  have hfullSupport : full.support =
      (p₀ :: p₁ :: p₂ :: p₃ :: p₄ :: []).flatMap (fun z => z.walk.support) :=
    join_support p₀ [p₁, p₂, p₃, p₄] hlinkFull
  have hΛjoin : Λ = full := by
    apply SimpleGraph.Walk.ext_support
    rw [hΛsupport, holdTrip, htripSupport, hfullSupport]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  have hfullPath : full.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [hfullSupport]
    have hbn' := hbn
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hbn'
    rw [holdTrip, htripSupport] at hbn'
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      using hbn'
  have hp₁ : p₁.walk.IsPath := SimpleGraph.Walk.IsPath.mk'
    ((List.nodup_flatMap.mp hjn).1 p₁ (by simp))
  have hp₃ : p₃.walk.IsPath := SimpleGraph.Walk.IsPath.mk'
    ((List.nodup_flatMap.mp hjn).1 p₃ (by simp))
  have hja' : s(p₁.finish, r₀) ∈ p₁.walk.edges :=
    actual_partition_incident_edge_owner _ hjn p₁ (by simp) p₁.walk.end_mem_support hja
  have hjb' : s(r₀, ℓ₀) ∈ p₁.walk.edges :=
    actual_partition_incident_edge_owner _ hjn p₁ (by simp)
      (p₁.walk.snd_mem_support_of_mem_edges hja') hjb
  have hba' : s(p₃.finish, r₁) ∈ p₃.walk.edges :=
    actual_partition_incident_edge_owner _ hjn p₃ (by simp) p₃.walk.end_mem_support hba
  have hbb' : s(r₁, ℓ₁) ∈ p₃.walk.edges :=
    actual_partition_incident_edge_owner _ hjn p₃ (by simp)
      (p₃.walk.snd_mem_support_of_mem_edges hba') hbb
  obtain ⟨i, hi, hil, hir⟩ := actual_retained_suffix_cut_position p₁.walk hp₁ hja' hjb' hneq₀
  obtain ⟨j, hj, hjl, hjr⟩ := actual_retained_suffix_cut_position p₃.walk hp₃ hba' hbb' hneq₁
  rw [hΛjoin]
  exact actual_joined_route_two_cut_slicing p₀ [p₁, p₂, p₃, p₄] hlinkFull hfullPath
    (by decide : 1 < 3) (by decide : 3 < 5)
    (by simpa using hi) (by simpa using hj)
    (by simpa using hil) (by simpa using hir) (by simpa using hjl) (by simpa using hjr)

#print axioms actual_base_joint_route_three_fragments

end D5.S3.Combinatorics.Graph.Walks.ActualBaseJointRouteSlicing
