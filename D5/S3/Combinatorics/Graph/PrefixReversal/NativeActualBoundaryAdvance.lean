/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualBoundaryAdvance
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualBoundaryAdvance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Advance Actual Native Boundaries with Retained Route Identities. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate
import D5.S3.Combinatorics.Graph.PrefixReversal.RecursiveBoundaryAdvance
import D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate
import D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
import D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
import D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualBoundaryAdvance

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursiveBoundaryAdvance
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs
open D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate
open D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
open D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
open D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs
open private mapped_complement_inventory from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate

private def shiftPort {k : ℕ} (p : Port k) : Port (k + 1) := (p.1.succ, p.2)

private theorem shifted_special_port {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (p : Port k) :
    specialPort (nextFrame F A u hbase) (shiftPort p) = specialPort F p := by
  have hs := native_marked_index_shift hm F A u hbase p.1.val
  simp only [specialPort, shiftPort, Fin.val_succ]
  split_ifs with h
  · simpa only [h, if_pos] using hs.1
  · simpa only [h, if_neg, if_false] using hs.2

/-- The old retained order may be either actual E or actual O. Its affected
whole path is factored around d by previous joint-path recovery. The current
joint filtered inventory is supplied by the already earned next joint update;
its two actual cut groups earn the restored/kept edge separation. This
constructs actual whole paths with the next same template; the exchange of
the two marked orders is the literal nextFrame indexing from the J step. -/
theorem native_actual_even_odd_boundary_advance {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (odd : Bool)
    {base priorBase r x ℓ z y ℓ₀ r₀ ℓ₁ r₁ : ParentVertex F A u hbase}
    (c : (ParentGraph F A u hbase).Walk base base) (hc : c.IsHamiltonianCycle)
    (prior : (ParentGraph F A u hbase).Walk priorBase priorBase) (hprior : prior.IsCycle)
    (d : (ParentGraph F A u hbase).Walk ℓ z)
    (cross : (ParentGraph F A u hbase).Walk r x)
    (old : (ParentGraph F A u hbase).Walk x y)
    (oldrest jointtail : List (Piece (ParentGraph F A u hbase)))
    (oldK oldH : Finset (Sym2 (ParentVertex F A u hbase)))
    (holdDisjoint : Disjoint oldK oldH)
    (hpriorJointSupport : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointtail).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.support).Perm prior.support.tail)
    (hpriorSingleSupport : ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.support).Perm prior.support.tail)
    (hpriorJointEdges : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointtail).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.edges).Perm
      (prior.edges.filter fun e => decide (e ∉ oldK ∪ oldH)))
    (hpriorSingleEdges : ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.edges).Perm
      (prior.edges.filter fun e => decide (e ∉ oldK)))
    (hpriorCuts : ∀ e ∈ oldK ∪ oldH, e ∈ prior.edges)
    (hpriorSeam : s(r, ℓ) ∈ oldH)
    (K H : Finset (Sym2 (ParentVertex F A u hbase)))
    (hdisjoint : Disjoint K H)
    (hpriorRestored : oldH.image (Sym2.map Subtype.val) =
      (H.erase s(ℓ₁, r₁)).image (Sym2.map Subtype.val))
    (restored deleted : List (Sym2 (ParentVertex F A u hbase)))
    (hrestored : restored = (H.erase s(ℓ₁, r₁)).toList)
    (hdeletedList : deleted = K.toList)
    (hrestoreCut : s(ℓ₁, r₁) ∈ H)
    (hdeleted : (deleted.map (Sym2.map Subtype.val)).toFinset =
      markedCuts (nextFrame F A u hbase))
    (new₀ : (ParentGraph F A u hbase).Walk z ℓ₀)
    (new₁ : (ParentGraph F A u hbase).Walk r₀ ℓ₁)
    (new₂ : (ParentGraph F A u hbase).Walk r₁ ℓ)
    (hcurrentSupport : c.support.tail.Perm
      (new₀.support ++ new₁.support ++ new₂.support ++
        (⟨r, x, cross⟩ :: jointtail).flatMap fun p => p.walk.support))
    (hcurrentJoint : (new₀.edges ++ new₁.edges ++ new₂.edges ++
        ((⟨r, x, cross⟩ :: jointtail).flatMap fun p => p.walk.edges)).Perm
      (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hcurrentCuts : ∀ e ∈ K ∪ H, e ∈ c.edges)
    (hx : x.val = leftPort F 0) (hy : y.val = leftPort F (k - 1))
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F A u hbase) 0)
    (hr₀ : r₀.val = rightPort (nextFrame F A u hbase) 0)
    (hrestBoundary : ∀ p ∈ oldrest, ∃ a b : Port k,
      p.start.val = specialPort F a ∧ p.finish.val = specialPort F b ∧
        (if odd then oddBoundary k else evenBoundary k) (code a) (code b)) :
    ∃ boundary₀ : (ParentGraph F A u hbase).Walk ℓ₀ y,
      ∃ boundary₁ : (ParentGraph F A u hbase).Walk r₀ x,
      let pieces : List (Piece (ParentGraph F A u hbase)) :=
        [⟨ℓ₀, y, boundary₀⟩, ⟨r₀, x, boundary₁⟩] ++ oldrest
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun p => p.walk.support).count v = 1) ∧
      (pieces.flatMap fun p => p.walk.support).Perm c.support.tail ∧
      (pieces.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ deleted.toFinset)) ∧
      (∀ e, e ∈ (pieces.flatMap fun p => p.walk.edges) ↔
        e ∈ c.edgeSet ∧ e ∉ deleted.toFinset) ∧
      (∀ e ∈ deleted.toFinset, e ∈ c.edgeSet) ∧ pieces.length = deleted.toFinset.card ∧
      (∀ e : Sym2 (Configuration m),
        e ∈ (pieces.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val) ↔
          e ∈ c.edges.map (Sym2.map Subtype.val) ∧
            e ∉ markedCuts (nextFrame F A u hbase)) ∧
      (∀ e ∈ markedCuts (nextFrame F A u hbase),
        e ∈ c.edges.map (Sym2.map Subtype.val)) ∧
      pieces.length = (markedCuts (nextFrame F A u hbase)).card ∧
      (∀ p ∈ pieces, ∃ a b : Port (k + 1),
        p.start.val = specialPort (nextFrame F A u hbase) a ∧
        p.finish.val = specialPort (nextFrame F A u hbase) b ∧
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) (code a) (code b)) ∧
      endpointPairs pieces =
        (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) ∪ {s(ℓ₀, y), s(r₀, x)} ∧
      s(ℓ₁, r₁) ∉ deleted.toFinset := by
  classical
  obtain ⟨hpriorRestore, _, _, _, holdNodup, holdSupport', holdEdges', tail, hold, _⟩ :=
    actual_prior_opposite_boundary_inputs prior hprior d cross jointtail old oldrest
      oldK oldH holdDisjoint hpriorJointSupport hpriorSingleSupport
      hpriorJointEdges hpriorSingleEdges hpriorCuts hpriorSeam
  let front := cross.reverse.concat hpriorRestore
  have holdSupport : (old.support ++ oldrest.flatMap fun p => p.walk.support).Perm
      (d.support ++ (⟨r, x, cross⟩ :: jointtail).flatMap fun p => p.walk.support) := by
    simpa only [List.flatMap_cons, List.append_assoc] using holdSupport'
  have heinjPrior : Function.Injective (Sym2.map
      (Subtype.val : ParentVertex F A u hbase → Configuration m)) :=
    Sym2.map.injective Subtype.val_injective
  have holdH : oldH = H.erase s(ℓ₁, r₁) := Finset.image_injective heinjPrior hpriorRestored
  have holdEdges : (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (⟨r, x, cross⟩ :: jointtail).flatMap
        (fun p => p.walk.edges) ++ restored) := by
    rw [holdH, ← hrestored] at holdEdges'
    simpa only [List.flatMap_cons, List.append_assoc] using holdEdges'
  obtain ⟨hcurrentEdges, hrestoreNotDeleted, _⟩ :=
    actual_joint_half_cut_inventory c hc.isCycle
      (new₀.edges ++ new₁.edges ++ new₂.edges ++
        ((⟨r, x, cross⟩ :: jointtail).flatMap fun p => p.walk.edges)) K H hdisjoint
      hcurrentJoint hcurrentCuts s(ℓ₁, r₁) hrestoreCut
  rw [← hrestored, ← hdeletedList] at hcurrentEdges
  have hrestore : (ParentGraph F A u hbase).Adj ℓ₁ r₁ :=
    c.adj_of_mem_edges (hcurrentCuts _ (Finset.mem_union.mpr (Or.inr hrestoreCut)))
  have hrestoreNotDeleted' : s(ℓ₁, r₁) ∉ deleted.toFinset := by
    simpa only [hdeletedList, List.mem_toFinset, Finset.mem_toList] using hrestoreNotDeleted
  obtain ⟨boundary₀, boundary₁, hpaths, hcount, hsupport, hedges, hinv, hcuts,
      hcard, hpairs, _, _⟩ :=
    actual_single_order_boundary_update c hc d front tail old hold oldrest (⟨r, x, cross⟩ :: jointtail)
      holdNodup holdSupport restored deleted holdEdges new₀ new₁ new₂ hrestore
      hcurrentSupport hcurrentEdges
  let pieces : List (Piece (ParentGraph F A u hbase)) :=
    [⟨ℓ₀, y, boundary₀⟩, ⟨r₀, x, boundary₁⟩] ++ oldrest
  let edgeVal : Sym2 (ParentVertex F A u hbase) → Sym2 (Configuration m) :=
    Sym2.map Subtype.val
  have heinj : Function.Injective edgeVal := Sym2.map.injective Subtype.val_injective
  have hcutimage : deleted.toFinset.image edgeVal = markedCuts (nextFrame F A u hbase) := by
    rw [← hdeleted]
    ext e
    simp only [edgeVal, Finset.mem_image, List.mem_toFinset, List.mem_map]
  have hrawinv (e : Sym2 (Configuration m)) :
      e ∈ (pieces.flatMap fun p => p.walk.edges).map edgeVal ↔
        e ∈ c.edges.map edgeVal ∧ e ∉ markedCuts (nextFrame F A u hbase) := by
    rw [← hcutimage]
    exact mapped_complement_inventory edgeVal heinj _ c.edges deleted.toFinset
      (by intro f; simpa only [SimpleGraph.Walk.mem_edgeSet] using hinv f) e
  have hrawcuts (e : Sym2 (Configuration m)) (he : e ∈ markedCuts (nextFrame F A u hbase)) :
      e ∈ c.edges.map edgeVal := by
    rw [← hcutimage] at he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact List.mem_map.mpr ⟨f,
      by simpa only [SimpleGraph.Walk.mem_edgeSet] using hcuts f hf, hfe⟩
  have hrawcard : pieces.length = (markedCuts (nextFrame F A u hbase)).card := by
    rw [← hcutimage, Finset.card_image_of_injective _ heinj]
    exact hcard
  have hxnext : x.val = leftPort (nextFrame F A u hbase) 1 :=
    hx.trans (native_marked_index_shift hm F A u hbase 0).2.symm
  have hynext : y.val = leftPort (nextFrame F A u hbase) k := by
    have hs := (native_marked_index_shift hm F A u hbase (k - 1)).2
    rw [show k - 1 + 1 = k by omega] at hs
    exact hy.trans hs.symm
  have hadvance (a b : RawPort) :
      advance k (if odd then oddBoundary k else evenBoundary k) a b →
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) a b := by
    cases odd
    · exact (advance_even_boundary k hk a b).mp
    · exact (advance_odd_boundary k hk a b).mp
  have hboundary (p : Piece (ParentGraph F A u hbase)) (hp : p ∈ pieces) :
      ∃ a b : Port (k + 1),
        p.start.val = specialPort (nextFrame F A u hbase) a ∧
        p.finish.val = specialPort (nextFrame F A u hbase) b ∧
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) (code a) (code b) := by
    simp only [pieces, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | hp
    · refine ⟨(0, 1), (⟨k, by omega⟩, 1), ?_, ?_, hadvance _ _ ?_⟩
      · simpa only [specialPort, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, if_false] using hℓ₀
      · simpa only [specialPort, Fin.val_mk, Fin.val_one, Nat.one_ne_zero, if_false] using hynext
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
    · refine ⟨(0, 0), (1, 1), ?_, ?_, hadvance _ _ ?_⟩
      · simpa only [specialPort, Fin.val_zero, if_true] using hr₀
      · simpa only [specialPort, Fin.val_one, Nat.one_ne_zero, if_false] using hxnext
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨a, b, hs, hf, hb⟩ := hrestBoundary p hp
      have hnot : ¬ pair (code a) (code b) (k - 1, 1) (0, 1) := by
        intro hpair
        have hpx : x ∈ p.walk.support := by
          rcases hpair with ⟨_, hb⟩ | ⟨ha, _⟩
          · have hbi : b.1.val = 0 := congrArg Prod.fst hb
            have hbs : b.2.val = 1 := congrArg Prod.snd hb
            have hf' : p.finish = x := Subtype.ext (hf.trans (by
              simpa only [specialPort, hbi, hbs, Nat.one_ne_zero, if_false] using hx.symm))
            exact hf' ▸ p.walk.end_mem_support
          · have hai : a.1.val = 0 := congrArg Prod.fst ha
            have has : a.2.val = 1 := congrArg Prod.snd ha
            have hs' : p.start = x := Subtype.ext (hs.trans (by
              simpa only [specialPort, hai, has, Nat.one_ne_zero, if_false] using hx.symm))
            exact hs' ▸ p.walk.start_mem_support
        exact List.disjoint_left.mp (List.nodup_append'.mp holdNodup).2.2
          old.start_mem_support (List.mem_flatMap.mpr ⟨p, hp, hpx⟩)
      refine ⟨shiftPort a, shiftPort b,
        hs.trans (shifted_special_port hm F A u hbase a).symm,
        hf.trans (shifted_special_port hm F A u hbase b).symm, hadvance _ _ ?_⟩
      apply Or.inl
      simpa only [shiftPort, code, previousIndex, Fin.val_succ, Nat.add_sub_cancel] using
        (show 0 < a.1.val + 1 ∧ 0 < b.1.val + 1 ∧
          (if odd then oddBoundary k else evenBoundary k) (code a) (code b) ∧
          ¬ pair (code a) (code b) (k - 1, 1) (0, 1) from
          ⟨by omega, by omega, hb, hnot⟩)
  refine ⟨boundary₀, boundary₁, hpaths, ?_, hsupport, hedges, hinv, hcuts, hcard,
    hrawinv, hrawcuts, hrawcard, hboundary, hpairs, hrestoreNotDeleted'⟩
  intro v
  convert hcount v using 1
  unfold List.count
  apply List.countP_congr
  intro x hx
  simp only [beq_iff_eq]

/-- The primary old order restores the first Q zero cut of the same
actual current joint partition. This is the other half of the simultaneous
boundary step; its new endpoints are l1/r1 and its restoration occurs on
the z side of the distinguished old path. Its same E/O template is earned
from the actual mirrored update and literal index shift. -/
theorem native_actual_first_cut_even_odd_boundary_advance {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (odd : Bool)
    {base priorBase ℓ z y ℓ₀ r₀ ℓ₁ r₁ : ParentVertex F A u hbase}
    (c : (ParentGraph F A u hbase).Walk base base) (hc : c.IsHamiltonianCycle)
    (prior : (ParentGraph F A u hbase).Walk priorBase priorBase) (hprior : prior.IsCycle)
    (d : (ParentGraph F A u hbase).Walk ℓ z)
    (old : (ParentGraph F A u hbase).Walk ℓ y)
    (oldrest jointrest : List (Piece (ParentGraph F A u hbase)))
    (oldK oldH : Finset (Sym2 (ParentVertex F A u hbase)))
    (holdDisjoint : Disjoint oldK oldH)
    (hpriorJointSupport : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.support).Perm prior.support.tail)
    (hpriorSingleSupport : ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.support).Perm prior.support.tail)
    (hpriorJointEdges : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.edges).Perm
      (prior.edges.filter fun e => decide (e ∉ oldK ∪ oldH)))
    (hpriorSingleEdges : ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece (ParentGraph F A u hbase) => p.walk.edges).Perm
      (prior.edges.filter fun e => decide (e ∉ oldK)))
    (hpriorCuts : ∀ e ∈ oldK ∪ oldH, e ∈ prior.edges)
    (K H : Finset (Sym2 (ParentVertex F A u hbase)))
    (hdisjoint : Disjoint K H)
    (hpriorRestored : oldH.image (Sym2.map Subtype.val) =
      (H.erase s(ℓ₀, r₀)).image (Sym2.map Subtype.val))
    (restored deleted : List (Sym2 (ParentVertex F A u hbase)))
    (hrestored : restored = (H.erase s(ℓ₀, r₀)).toList)
    (hdeletedList : deleted = K.toList)
    (hrestoreCut : s(ℓ₀, r₀) ∈ H)
    (hdeleted : (deleted.map (Sym2.map Subtype.val)).toFinset =
      markedCuts (nextFrame F A u hbase))
    (new₀ : (ParentGraph F A u hbase).Walk z ℓ₀)
    (new₁ : (ParentGraph F A u hbase).Walk r₀ ℓ₁)
    (new₂ : (ParentGraph F A u hbase).Walk r₁ ℓ)
    (hcurrentSupport : c.support.tail.Perm
      (new₀.support ++ new₁.support ++ new₂.support ++
        jointrest.flatMap fun p => p.walk.support))
    (hcurrentJoint : (new₀.edges ++ new₁.edges ++ new₂.edges ++
        (jointrest.flatMap fun p => p.walk.edges)).Perm
      (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hcurrentCuts : ∀ e ∈ K ∪ H, e ∈ c.edges)
    (hx : ℓ.val = leftPort F 0) (hy : y.val = leftPort F (k - 1))
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F A u hbase) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F A u hbase) 0)
    (hrestBoundary : ∀ p ∈ oldrest, ∃ a b : Port k,
      p.start.val = specialPort F a ∧ p.finish.val = specialPort F b ∧
        (if odd then oddBoundary k else evenBoundary k) (code a) (code b)) :
    ∃ boundary₀ : (ParentGraph F A u hbase).Walk ℓ₁ y,
      ∃ boundary₁ : (ParentGraph F A u hbase).Walk r₁ ℓ,
      let pieces : List (Piece (ParentGraph F A u hbase)) :=
        [⟨ℓ₁, y, boundary₀⟩, ⟨r₁, ℓ, boundary₁⟩] ++ oldrest
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun p => p.walk.support).count v = 1) ∧
      (pieces.flatMap fun p => p.walk.support).Perm c.support.tail ∧
      (pieces.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ deleted.toFinset)) ∧
      (∀ e, e ∈ (pieces.flatMap fun p => p.walk.edges) ↔
        e ∈ c.edgeSet ∧ e ∉ deleted.toFinset) ∧
      (∀ e ∈ deleted.toFinset, e ∈ c.edgeSet) ∧ pieces.length = deleted.toFinset.card ∧
      (∀ e : Sym2 (Configuration m),
        e ∈ (pieces.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val) ↔
          e ∈ c.edges.map (Sym2.map Subtype.val) ∧
            e ∉ markedCuts (nextFrame F A u hbase)) ∧
      (∀ e ∈ markedCuts (nextFrame F A u hbase),
        e ∈ c.edges.map (Sym2.map Subtype.val)) ∧
      pieces.length = (markedCuts (nextFrame F A u hbase)).card ∧
      (∀ p ∈ pieces, ∃ a b : Port (k + 1),
        p.start.val = specialPort (nextFrame F A u hbase) a ∧
        p.finish.val = specialPort (nextFrame F A u hbase) b ∧
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) (code a) (code b)) ∧
      endpointPairs pieces =
        (endpointPairs (⟨ℓ, y, old⟩ :: oldrest)).erase s(ℓ, y) ∪ {s(ℓ₁, y), s(r₁, ℓ)} ∧
      s(ℓ₀, r₀) ∉ deleted.toFinset := by
  classical
  obtain ⟨_, _, _, holdNodup, holdSupport, holdEdges', tail, hold', _⟩ :=
    actual_prior_primary_boundary_inputs prior hprior d jointrest old oldrest
      oldK oldH holdDisjoint hpriorJointSupport hpriorSingleSupport
      hpriorJointEdges hpriorSingleEdges hpriorCuts
  let front : (ParentGraph F A u hbase).Walk ℓ ℓ := .nil
  have hold : old = front.append (d.append tail) := by
    simpa only [front, SimpleGraph.Walk.nil_append] using hold'
  have heinjPrior : Function.Injective (Sym2.map
      (Subtype.val : ParentVertex F A u hbase → Configuration m)) :=
    Sym2.map.injective Subtype.val_injective
  have holdH : oldH = H.erase s(ℓ₀, r₀) := Finset.image_injective heinjPrior hpriorRestored
  have holdEdges : (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (jointrest).flatMap
        (fun p => p.walk.edges) ++ restored) := by
    rw [holdH, ← hrestored] at holdEdges'
    simpa only [List.flatMap_cons, List.append_assoc] using holdEdges'
  obtain ⟨hcurrentEdges, hrestoreNotDeleted, _⟩ :=
    actual_joint_half_cut_inventory c hc.isCycle
      (new₀.edges ++ new₁.edges ++ new₂.edges ++
        (jointrest.flatMap fun p => p.walk.edges)) K H hdisjoint
      hcurrentJoint hcurrentCuts s(ℓ₀, r₀) hrestoreCut
  rw [← hrestored, ← hdeletedList] at hcurrentEdges
  have hrestore : (ParentGraph F A u hbase).Adj ℓ₀ r₀ :=
    c.adj_of_mem_edges (hcurrentCuts _ (Finset.mem_union.mpr (Or.inr hrestoreCut)))
  have hrestoreNotDeleted' : s(ℓ₀, r₀) ∉ deleted.toFinset := by
    simpa only [hdeletedList, List.mem_toFinset, Finset.mem_toList] using hrestoreNotDeleted
  obtain ⟨boundary₀, boundary₁, hpaths, hcount, hsupport, hedges, hinv, hcuts,
      hcard, hpairs, _, _⟩ :=
    actual_single_order_first_cut_boundary_update c hc d front tail old hold oldrest jointrest
      holdNodup holdSupport restored deleted holdEdges new₀ new₁ new₂ hrestore
      hcurrentSupport hcurrentEdges
  let pieces : List (Piece (ParentGraph F A u hbase)) :=
    [⟨ℓ₁, y, boundary₀⟩, ⟨r₁, ℓ, boundary₁⟩] ++ oldrest
  let edgeVal : Sym2 (ParentVertex F A u hbase) → Sym2 (Configuration m) :=
    Sym2.map Subtype.val
  have heinj : Function.Injective edgeVal := Sym2.map.injective Subtype.val_injective
  have hcutimage : deleted.toFinset.image edgeVal = markedCuts (nextFrame F A u hbase) := by
    rw [← hdeleted]
    ext e
    simp only [edgeVal, Finset.mem_image, List.mem_toFinset, List.mem_map]
  have hrawinv (e : Sym2 (Configuration m)) :
      e ∈ (pieces.flatMap fun p => p.walk.edges).map edgeVal ↔
        e ∈ c.edges.map edgeVal ∧ e ∉ markedCuts (nextFrame F A u hbase) := by
    rw [← hcutimage]
    exact mapped_complement_inventory edgeVal heinj _ c.edges deleted.toFinset
      (by intro f; simpa only [SimpleGraph.Walk.mem_edgeSet] using hinv f) e
  have hrawcuts (e : Sym2 (Configuration m)) (he : e ∈ markedCuts (nextFrame F A u hbase)) :
      e ∈ c.edges.map edgeVal := by
    rw [← hcutimage] at he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact List.mem_map.mpr ⟨f,
      by simpa only [SimpleGraph.Walk.mem_edgeSet] using hcuts f hf, hfe⟩
  have hrawcard : pieces.length = (markedCuts (nextFrame F A u hbase)).card := by
    rw [← hcutimage, Finset.card_image_of_injective _ heinj]
    exact hcard
  have hxnext : ℓ.val = leftPort (nextFrame F A u hbase) 1 :=
    hx.trans (native_marked_index_shift hm F A u hbase 0).2.symm
  have hynext : y.val = leftPort (nextFrame F A u hbase) k := by
    have hs := (native_marked_index_shift hm F A u hbase (k - 1)).2
    rw [show k - 1 + 1 = k by omega] at hs
    exact hy.trans hs.symm
  have hadvance (a b : RawPort) :
      advance k (if odd then oddBoundary k else evenBoundary k) a b →
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) a b := by
    cases odd
    · exact (advance_even_boundary k hk a b).mp
    · exact (advance_odd_boundary k hk a b).mp
  have hboundary (p : Piece (ParentGraph F A u hbase)) (hp : p ∈ pieces) :
      ∃ a b : Port (k + 1),
        p.start.val = specialPort (nextFrame F A u hbase) a ∧
        p.finish.val = specialPort (nextFrame F A u hbase) b ∧
        (if odd then oddBoundary (k + 1) else evenBoundary (k + 1)) (code a) (code b) := by
    simp only [pieces, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | hp
    · refine ⟨(0, 1), (⟨k, by omega⟩, 1), ?_, ?_, hadvance _ _ ?_⟩
      · simpa only [specialPort, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, if_false] using hℓ₁
      · simpa only [specialPort, Fin.val_mk, Fin.val_one, Nat.one_ne_zero, if_false] using hynext
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
    · refine ⟨(0, 0), (1, 1), ?_, ?_, hadvance _ _ ?_⟩
      · simpa only [specialPort, Fin.val_zero, if_true] using hr₁
      · simpa only [specialPort, Fin.val_one, Nat.one_ne_zero, if_false] using hxnext
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨a, b, hs, hf, hb⟩ := hrestBoundary p hp
      have hnot : ¬ pair (code a) (code b) (k - 1, 1) (0, 1) := by
        intro hpair
        have hpx : ℓ ∈ p.walk.support := by
          rcases hpair with ⟨_, hb⟩ | ⟨ha, _⟩
          · have hbi : b.1.val = 0 := congrArg Prod.fst hb
            have hbs : b.2.val = 1 := congrArg Prod.snd hb
            have hf' : p.finish = ℓ := Subtype.ext (hf.trans (by
              simpa only [specialPort, hbi, hbs, Nat.one_ne_zero, if_false] using hx.symm))
            exact hf' ▸ p.walk.end_mem_support
          · have hai : a.1.val = 0 := congrArg Prod.fst ha
            have has : a.2.val = 1 := congrArg Prod.snd ha
            have hs' : p.start = ℓ := Subtype.ext (hs.trans (by
              simpa only [specialPort, hai, has, Nat.one_ne_zero, if_false] using hx.symm))
            exact hs' ▸ p.walk.start_mem_support
        exact List.disjoint_left.mp (List.nodup_append'.mp holdNodup).2.2
          old.start_mem_support (List.mem_flatMap.mpr ⟨p, hp, hpx⟩)
      refine ⟨shiftPort a, shiftPort b,
        hs.trans (shifted_special_port hm F A u hbase a).symm,
        hf.trans (shifted_special_port hm F A u hbase b).symm, hadvance _ _ ?_⟩
      apply Or.inl
      simpa only [shiftPort, code, previousIndex, Fin.val_succ, Nat.add_sub_cancel] using
        (show 0 < a.1.val + 1 ∧ 0 < b.1.val + 1 ∧
          (if odd then oddBoundary k else evenBoundary k) (code a) (code b) ∧
          ¬ pair (code a) (code b) (k - 1, 1) (0, 1) from
          ⟨by omega, by omega, hb, hnot⟩)
  refine ⟨boundary₀, boundary₁, hpaths, ?_, hsupport, hedges, hinv, hcuts, hcard,
    hrawinv, hrawcuts, hrawcard, hboundary, hpairs, hrestoreNotDeleted'⟩
  intro v
  convert hcount v using 1
  unfold List.count
  apply List.countP_congr
  intro x hx
  simp only [beq_iff_eq]

#print axioms native_actual_even_odd_boundary_advance
#print axioms native_actual_first_cut_even_odd_boundary_advance

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualBoundaryAdvance
