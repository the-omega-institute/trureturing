/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Split the actual Q child retained by the same native J2 parent witness. -/
/- Candidate, not yet kernel checked. In particular, no new Q cycle or
   independently chosen special path replaces the data saved in W. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBaseSlicing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2QSourcePromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBaseSlicing
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open private outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private j2SpecialMap j2_frame_special_domain j2_special_map_bijective
  j2_mapped_half_cuts from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open private same_seed_marked_cut_images from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
open private native_internal_seam_adj from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly

/-- The exact special child saved in W splits at the two new zero cuts.
The old middle E2 piece is recovered from joint pieces 5, 4 and reversed
1 of W.Q, using the actual restored opposite seams. Consequently all
three new paths partition this particular Q opening and its remaining
edges, with primary order nextFrame(reverseSelected F). -/
theorem native_j2_same_q_three_fragments {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let hBO := outer_base_bound F A u hbase hA
    let N₀ := nextFrame (reverseSelected F) A u hbase
    let N₁ := nextFrame F A u hbase
    ∃ r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // SpecialDomain O hBO x},
      r₀.val = rightPort N₀ 0 ∧ ℓ₀.val = leftPort N₀ 0 ∧
      r₁.val = rightPort N₁ 0 ∧ ℓ₁.val = leftPort N₁ 0 ∧
      ∃ q₀ : (domainGraph (SpecialDomain O hBO)).Walk
          (specialVertex (by omega : 3 ≤ m) O hBO (0, 0)) ℓ₀,
        ∃ q₁ : (domainGraph (SpecialDomain O hBO)).Walk r₀ ℓ₁,
        ∃ q₂ : (domainGraph (SpecialDomain O hBO)).Walk r₁
          (specialVertex (by omega : 3 ≤ m) O hBO (Fin.last 2, 1)),
          q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
          q₀.support ++ q₁.support ++ q₂.support = W.special.path.support ∧
          q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
            W.special.path.edges ∧
          q₀.edges ++ q₁.edges ++ q₂.edges = W.special.path.edges.filter
            (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let B := outerFrame (reverseSelected F) A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let hBB := outer_base_bound (reverseSelected F) A u hbase hA
  let lift := j2SpecialMap O hBO
  let J (i : Fin 6) := mapPiece lift (W.Q.seed.joint i)
  let K := W.Q.seed.K.image (Sym2.map lift)
  let H := W.Q.seed.H.image (Sym2.map lift)
  let w := W.Q.seed.walk.map lift
  let p₁ := J 5
  let p₂ := J 4
  let p₃ : Piece (domainGraph (SpecialDomain O hBO)) :=
    ⟨(J 1).finish, (J 1).start, (J 1).walk.reverse⟩
  let rest := [J 0, J 2, J 3]
  have hbij : Function.Bijective lift := j2_special_map_bijective O hBO
  obtain ⟨hcycle, _, hjs, hje, hjc⟩ := actual_cycle_partition_map lift hbij.injective
    W.Q.seed.walk W.Q.seed.hamiltonian.isCycle (List.ofFn W.Q.seed.joint)
    (W.Q.seed.K ∪ W.Q.seed.H) W.Q.seed.partitions.joint_partition.support
    W.Q.seed.partitions.joint_partition.edges W.Q.seed.partitions.joint_partition.cut_mem
  rw [Finset.image_union] at hje hjc
  have hmapped : (List.ofFn W.Q.seed.joint).map (mapPiece lift) = List.ofFn J := by
    rw [List.map_ofFn]
    rfl
  rw [hmapped] at hjs hje
  have hps : ((p₁ :: p₂ :: p₃ :: rest).flatMap fun z => z.walk.support).Perm
      ((List.ofFn J).flatMap fun z => z.walk.support) := by
    apply List.perm_iff_count.mpr
    intro x
    change ([J 5, J 4, p₃, J 0, J 2, J 3].flatMap fun z => z.walk.support).count x =
      ([J 0, J 1, J 2, J 3, J 4, J 5].flatMap fun z => z.walk.support).count x
    simp only [p₃, List.flatMap_cons, List.flatMap_nil,
      SimpleGraph.Walk.support_reverse, List.count_append,
      List.count_reverse, List.count_nil]
    omega
  have hpe : ((p₁ :: p₂ :: p₃ :: rest).flatMap fun z => z.walk.edges).Perm
      ((List.ofFn J).flatMap fun z => z.walk.edges) := by
    apply List.perm_iff_count.mpr
    intro e
    change ([J 5, J 4, p₃, J 0, J 2, J 3].flatMap fun z => z.walk.edges).count e =
      ([J 0, J 1, J 2, J 3, J 4, J 5].flatMap fun z => z.walk.edges).count e
    simp only [p₃, List.flatMap_cons, List.flatMap_nil,
      SimpleGraph.Walk.edges_reverse, List.count_append,
      List.count_reverse, List.count_nil]
    omega
  have hjn := (hps.trans hjs).nodup_iff.mpr hcycle.support_nodup
  have hji (e) : e ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H := by
    rw [hpe.mem_iff, hje.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq, w, K, H]
  have hd : Disjoint K H := by
    apply Finset.disjoint_left.mpr
    intro e heK heH
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp heK
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp heH
    have hab := (Sym2.map.injective hbij.injective) (hae.trans hbe.symm)
    exact Finset.disjoint_left.mp W.Q.seed.partitions.disjoint ha (hab.symm ▸ hb)
  have hK : K.image (Sym2.map Subtype.val) = markedCuts O := by
    simpa only [K, lift, Finset.image_image, Function.comp_def, Sym2.map_map, j2SpecialMap,
      RelHom.coeFn_mk] using
      (same_seed_marked_cut_images hm O W.Q).1
  have hH : H.image (Sym2.map Subtype.val) = markedCuts B := by
    have hH₀ : H.image (Sym2.map Subtype.val) = markedCuts (reverseSelected O) := by
      simpa only [H, lift, Finset.image_image, Function.comp_def, Sym2.map_map,
        j2SpecialMap, RelHom.coeFn_mk] using (same_seed_marked_cut_images hm O W.Q).2
    simpa only [B, O, outerFrame, reverseSelected] using hH₀
  have hKS : K = specialCuts (by omega : 3 ≤ m) O hBO := by
    dsimp only [K]
    rw [W.Q.primaryCuts]
    exact j2_mapped_half_cuts hm O hBO
  have hportR (i : Fin 3) : relabel O * port m (i, false, false) = rightPort O i.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using (native_j2_frame_ports hm O i).1
  have hportL (i : Fin 3) : relabel O * port m (i, false, true) = leftPort O i.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using (native_j2_frame_ports hm O i).2
  have hbarR (i : Fin 3) : relabel O * port m (i, true, false) = rightPort B i.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte, B, O, outerFrame, reverseSelected] using
      (native_j2_frame_barred_ports hm O i).1
  have hbarL (i : Fin 3) : relabel O * port m (i, true, true) = leftPort B i.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte, B, O, outerFrame, reverseSelected] using
      (native_j2_frame_barred_ports hm O i).2
  have hp₁s : p₁.start.val = leftPort O 1 :=
    ((W.Q.seed.jointPorts 5).1).trans (hportL 1)
  have hp₁f : p₁.finish.val = leftPort B 0 :=
    ((W.Q.seed.jointPorts 5).2).trans (hbarL 0)
  have hp₂s : p₂.start.val = rightPort B 0 :=
    ((W.Q.seed.jointPorts 4).1).trans (hbarR 0)
  have hp₂f : p₂.finish.val = rightPort B 1 :=
    ((W.Q.seed.jointPorts 4).2).trans (hbarR 1)
  have hp₃s : p₃.start.val = leftPort B 1 :=
    ((W.Q.seed.jointPorts 1).2).trans (hbarL 1)
  have hp₃f : p₃.finish.val = leftPort O 0 :=
    ((W.Q.seed.jointPorts 1).1).trans (hportL 0)
  have hs : (W.special.ordered 1).start = p₁.start := by
    apply Subtype.ext
    rw [(W.special.orderedPorts 1).1]
    exact hp₁s.symm
  have hf : (W.special.ordered 1).finish = p₃.finish := by
    apply Subtype.ext
    rw [(W.special.orderedPorts 1).2]
    exact hp₃f.symm
  let old := (W.special.ordered 1).walk.copy hs hf
  let p₀ : Piece (domainGraph (SpecialDomain O hBO)) :=
    ⟨specialVertex (by omega : 3 ≤ m) O hBO (0, 0), (W.special.ordered 0).finish,
      (W.special.ordered 0).walk.copy (W.special.orderedPorts 0).1 rfl⟩
  let p₄ : Piece (domainGraph (SpecialDomain O hBO)) :=
    ⟨(W.special.ordered 2).start, specialVertex (by omega : 3 ≤ m) O hBO (Fin.last 2, 1),
      (W.special.ordered 2).walk.copy rfl (by
        simpa [evenPortRoute, evenEnumerate, evenRoute, code] using
          (W.special.orderedPorts 2).2)⟩
  have hordered : List.ofFn W.special.ordered =
      [W.special.ordered 0, W.special.ordered 1, W.special.ordered 2] := by rfl
  have hlink : Linked p₀ [⟨p₁.start, p₃.finish, old⟩, p₄] := by
    refine ⟨?_, ?_, trivial⟩
    · change (domainGraph (SpecialDomain O hBO)).Adj (W.special.ordered 0).finish p₁.start
      rw [← hs, (W.special.orderedPorts 0).2, (W.special.orderedPorts 1).1]
      apply native_internal_seam_adj
      norm_num [evenPortRoute, evenEnumerate, evenRoute, code, internalSeam]
    · change (domainGraph (SpecialDomain O hBO)).Adj p₃.finish (W.special.ordered 2).start
      rw [← hf, (W.special.orderedPorts 1).2, (W.special.orderedPorts 2).1]
      apply native_internal_seam_adj
      norm_num [evenPortRoute, evenEnumerate, evenRoute, code, internalSeam]
  have hΛs : W.special.path.support =
      p₀.walk.support ++ old.support ++ p₄.walk.support := by
    have h := W.special.support
    rw [hordered] at h
    simpa only [p₀, p₄, old, SimpleGraph.Walk.support_copy,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using h
  have hbn : ((p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
      fun z : Piece (domainGraph (SpecialDomain O hBO)) => z.walk.support).Nodup := by
    have h := W.special.hamiltonian.isPath.support_nodup
    rw [hΛs] at h
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc] using h
  have hbi (e) : e ∈ (p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
      (fun z : Piece (domainGraph (SpecialDomain O hBO)) => z.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ K := by
    have h := W.special.uncutInventory e
    rw [hordered] at h
    simpa only [p₀, p₄, old, SimpleGraph.Walk.edges_copy, hKS, w,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
      SimpleGraph.Walk.mem_edgeSet] using h
  have hprotect := native_protected_labels O (by omega : 2 ≤ 2)
  have hAkeep (x y : {v : Configuration m // SpecialDomain O hBO v})
      (hxy : y.val = x.val * a m)
      (hne : s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP O (by omega), protectedQ O (by omega))) : s(x, y) ∈ w.edges := by
    let x₀ : {v : Configuration m // FrameDomain O v} :=
      ⟨x.val, (j2_frame_special_domain O hBO x.val).mpr x.property⟩
    let y₀ : {v : Configuration m // FrameDomain O v} :=
      ⟨y.val, (j2_frame_special_domain O hBO y.val).mpr y.property⟩
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x₀, y₀), W.Q.seed.keepsProtectedA x₀ y₀ hxy hne,
      congrArg₂ (fun a b => s(a, b)) (Subtype.ext rfl) (Subtype.ext rfl)⟩
  have hBkeep (x y : {v : Configuration m // SpecialDomain O hBO v})
      (hxy : y.val = x.val * b m) (ht : x.val (Fin.last m) ∉ F.selected.toFinset) :
      s(x, y) ∈ w.edges := by
    let x₀ : {v : Configuration m // FrameDomain O v} :=
      ⟨x.val, (j2_frame_special_domain O hBO x.val).mpr x.property⟩
    let y₀ : {v : Configuration m // FrameDomain O v} :=
      ⟨y.val, (j2_frame_special_domain O hBO y.val).mpr y.property⟩
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x₀, y₀), W.Q.seed.keepsRemainingB x₀ y₀ hxy ht,
      congrArg₂ (fun a b => s(a, b)) (Subtype.ext rfl) (Subtype.ext rfl)⟩
  have hN₁ := native_new_marked_cut_domains (by omega : 3 ≤ m) F A u hbase hA 0
  have hN₀ := native_new_marked_cut_domains (by omega : 3 ≤ m)
    (reverseSelected F) A u hbase hA 0
  have horders (x) : SpecialDomain B hBB x ↔ SpecialDomain O hBO x :=
    native_marked_orders_same_domain B O hBB hBO
      (by simp only [B, O, outerFrame, reverseSelected, List.toFinset_reverse]) rfl rfl x
  let r₀ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨rightPort (nextFrame (reverseSelected F) A u hbase) 0, (horders _).mp hN₀.1⟩
  let ℓ₀ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨leftPort (nextFrame (reverseSelected F) A u hbase) 0, (horders _).mp hN₀.2⟩
  let r₁ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨rightPort (nextFrame F A u hbase) 0, hN₁.1⟩
  let ℓ₁ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨leftPort (nextFrame F A u hbase) 0, hN₁.2⟩
  obtain ⟨q₀, q₁, q₂, hq₀, hq₁, hq₂, hqs, hqe, hqf⟩ :=
    native_actual_q_base_three_fragments (by omega : 3 ≤ m) F (reverseSelected F)
      A u hbase hbase (by simp only [reverseSelected, List.toFinset_reverse])
      (protectedP O (by omega)) (protectedQ O (by omega))
      (List.mem_toFinset.mpr hprotect.2.1) (List.mem_toFinset.mpr hprotect.2.2.1)
      (SpecialDomain O hBO) w hAkeep hBkeep p₁ p₂ p₃ rest hjn
      hp₁f hp₂s hp₂f hp₃s hp₃f K H hd hK hH hji hjc
      p₀ p₄ old hlink hbn hbi W.special.path hΛs
      (r₀ := r₀) (ℓ₀ := ℓ₀) (r₁ := r₁) (ℓ₁ := ℓ₁) rfl rfl rfl rfl
  exact ⟨r₀, ℓ₀, r₁, ℓ₁, rfl, rfl, rfl, rfl,
    q₀, q₁, q₂, hq₀, hq₁, hq₂, hqs, hqe, hqf⟩

#print axioms native_j2_same_q_three_fragments

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2QSourcePromotion
