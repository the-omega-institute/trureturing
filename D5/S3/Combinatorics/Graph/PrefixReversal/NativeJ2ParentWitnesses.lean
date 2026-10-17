/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve the same raw old P and outer Q suppliers in their actual parent cycle. -/
/- Same-witness companion to the unconditional native J2 parent cycle.
   Preserve the actual raw supplier and all three partitions before
   opening any child or choosing the final parent. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2JointPaths
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SelectedC
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private joint_half_union half_disjoint seed_protected_pair from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed
open private j2SpecialMap j2_frame_special_domain j2_special_map_bijective j2_mapped_half_cuts
  j2HalfStartPort j2HalfFinishPort j2_half_endpoints from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open private native_child_frame_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open private parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private special_child_path from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
open private anchor_coordinates bc_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open private frame_terminal_fresh from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains

/-- The raw native cycle is retained as data, and all three mapped
partitions in `seed` belong to its image, including their actual cuts. -/
structure RawSeedFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) where
  rawBase : {x : Configuration m // F2Domain m x}
  rawWalk : (domainGraph (F2Domain m)).Walk rawBase rawBase
  rawHamiltonian : rawWalk.IsHamiltonianCycle
  rawInventory : ∀ e, e ∈ rawWalk.edges.map (Sym2.map Subtype.val) ↔
    (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e
  seed : SeedFor F
  mappedBase : seed.base = frameDomainIso hm F rawBase
  mappedWalk : HEq seed.walk (rawWalk.map (frameDomainIso hm F).toHom)
  primaryCuts : seed.K = (actualHalfCuts (F2Domain m) false).image
    (Sym2.map (frameDomainIso hm F).toHom)
  oppositeCuts : seed.H = (actualHalfCuts (F2Domain m) true).image
    (Sym2.map (frameDomainIso hm F).toHom)

/-- Choose once, then retain the raw walk alongside its joint and both
half partitions and the three earned retained-edge invariants. -/
theorem native_j2_raw_seed {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    Nonempty (RawSeedFor hm F) := by
  classical
  obtain ⟨rawBase, rawWalk, base, w, hraw, hinv, hbase, hmap,
    hham, hframe, _, hA, hB, _, _⟩ := native_j2_frame_cycle_with_inventory hm F
  subst base
  cases hmap
  let iso : domainGraph (F2Domain m) ≃g domainGraph (FrameDomain F) := frameDomainIso hm F
  let K := (actualHalfCuts (F2Domain m) false).image (Sym2.map iso.toHom)
  let H := (actualHalfCuts (F2Domain m) true).image (Sym2.map iso.toHom)
  obtain ⟨joint, hjports, _, _, hjs, hje, hjc⟩ :=
    native_actual_j2_frame_joint_paths hm F rawWalk hraw hinv
  obtain ⟨primary, hpports, _, _, hps, hpe, hpc⟩ :=
    native_actual_j2_frame_half_paths hm F false rawWalk hraw hinv
  obtain ⟨opposite, hoports, _, _, hos, hoe, hoc⟩ :=
    native_actual_j2_frame_half_paths hm F true rawWalk hraw hinv
  have heinj := Sym2.map.injective iso.toEquiv.injective
  have hd : Disjoint K H := by
    apply Finset.disjoint_left.mpr
    intro e heK heH
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heK
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heH
    have hxy := heinj (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp (half_disjoint hm (F2Domain m)) hx (hxy.symm ▸ hy)
  have hu : (actualJointCuts (F2Domain m)).image (Sym2.map iso.toHom) = K ∪ H := by
    rw [joint_half_union, Finset.image_union]
  have hjpartition : ActualCyclePartition
      (rawWalk.map iso.toHom) (K ∪ H) (List.ofFn joint) := by
    dsimp only [iso] at hu
    rw [hu] at hje hjc
    exact ⟨hjs, hje, hjc⟩
  have hprotected : ∀ (x y : {v : Configuration m // FrameDomain F v}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP F (by omega), protectedQ F (by omega)) →
        s(x, y) ∈ (rawWalk.map iso.toHom).edges := by
    intro x y hxy hpair
    exact hA x y hxy (by simpa only [seed_protected_pair hm F] using hpair)
  let S : SeedFor F :=
    ⟨_, _, hham, K, H, joint, primary, opposite, hjports, hpports, hoports,
      ⟨hham.isCycle, hd, hjpartition, ⟨hps, hpe, hpc⟩, ⟨hos, hoe, hoc⟩⟩,
      hprotected, hB, native_j2_frame_c_selected hm F _ hframe⟩
  exact ⟨⟨rawBase, rawWalk, hraw, hinv, S, rfl, HEq.rfl, rfl, rfl⟩⟩

/-- The special path keeps its ordered false-half pieces, exact support
and exact seam chain, all referring to this particular raw supplier. -/
structure SpecialPathFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) (S : RawSeedFor hm F) where
  ordered : Fin 3 → Piece (domainGraph (SpecialDomain F hB))
  path : (domainGraph (SpecialDomain F hB)).Walk
    (specialVertex (by omega : 3 ≤ m) F hB (0, 0))
    (specialVertex (by omega : 3 ≤ m) F hB (Fin.last 2, 1))
  hamiltonian : path.IsHamiltonian
  orderedPorts : ∀ i,
    (ordered i).start = specialVertex (by omega : 3 ≤ m) F hB
      (evenPortRoute 0 ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
    (ordered i).finish = specialVertex (by omega : 3 ≤ m) F hB
      (evenPortRoute 0 ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
  support : path.support = (List.ofFn ordered).flatMap (fun z => z.walk.support)
  edges : path.edges = chainEdges (ordered 0)
    (List.ofFn fun i : Fin 2 => ordered i.succ)
  uncutInventory : ∀ e,
    e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
      e ∈ (S.seed.walk.map (j2SpecialMap F hB)).edgeSet ∧
        e ∉ specialCuts (by omega : 3 ≤ m) F hB

theorem native_j2_special_from_raw_seed {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) (S : RawSeedFor hm F) :
    Nonempty (SpecialPathFor hm F hB S) := by
  classical
  let lift := j2SpecialMap F hB
  let pieces := (List.ofFn S.seed.primary).map (mapPiece lift)
  have hbij : Function.Bijective lift := j2_special_map_bijective F hB
  obtain ⟨_, _, hs, he, hc⟩ := actual_cycle_partition_map lift hbij.injective
    S.seed.walk S.seed.hamiltonian.isCycle (List.ofFn S.seed.primary) S.seed.K
    S.seed.partitions.primary_partition.support
    S.seed.partitions.primary_partition.edges
    S.seed.partitions.primary_partition.cut_mem
  have hcuts : S.seed.K.image (Sym2.map lift) = specialCuts (by omega : 3 ≤ m) F hB := by
    rw [S.primaryCuts]
    exact j2_mapped_half_cuts hm F hB
  rw [hcuts] at he hc
  have hp : ∀ z ∈ pieces, ∃ p q : Port 2,
      z.start.val = specialPort F p ∧ z.finish.val = specialPort F q ∧
        evenBoundary 2 (code p) (code q) := by
    intro z hz
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpiece
    obtain ⟨hstart, hfinish, hboundary⟩ := j2_half_endpoints hm F i
    exact ⟨j2HalfStartPort i, j2HalfFinishPort i,
      (S.seed.primaryPorts i).1.trans hstart,
      (S.seed.primaryPorts i).2.trans hfinish, hboundary⟩
  obtain ⟨ordered, q, hq, hend, hsupp, hedges, hinv⟩ :=
    native_special_child_even_path (by omega : 3 ≤ m) 0 F hB
      (S.seed.walk.map lift) (SimpleGraph.Walk.IsHamiltonianCycle.map hbij S.seed.hamiltonian)
      pieces hs he hc hp
  exact ⟨⟨ordered, q, hq, hend, hsupp, hedges, hinv⟩⟩

private theorem seed_special_keeps_remaining_b {m : ℕ} (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) (S : SeedFor F) :
    ∀ (x y : {v : Configuration m // SpecialDomain F hB v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
        s(x, y) ∈ (S.walk.map (j2SpecialMap F hB)).edges := by
  intro x y hy ht
  let x₀ : {v : Configuration m // FrameDomain F v} :=
    ⟨x.val, (j2_frame_special_domain F hB x.val).mpr x.property⟩
  let y₀ : {v : Configuration m // FrameDomain F v} :=
    ⟨y.val, (j2_frame_special_domain F hB y.val).mpr y.property⟩
  have hx : j2SpecialMap F hB x₀ = x := Subtype.ext rfl
  have hy' : j2SpecialMap F hB y₀ = y := Subtype.ext rfl
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr ⟨s(x₀, y₀), S.keepsRemainingB x₀ y₀ hy ht, by
    rw [Sym2.map_mk, hx, hy']⟩

/-- The ordinary child cycle is the image of this same seed walk, so
its complete joint and both half partitions remain available after its
supplier cut is opened by the parent assembler. -/
structure OrdinaryCycleFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) (j : Fin F.base.length) (hj : 0 < j.val)
    (S : RawSeedFor hm (nativeChildFrame F j)) where
  cycle : SpecifiedOrdinaryCycle (by omega : 3 ≤ m) F hB j hj
  mappedBase : cycle.base = childMarkedDomainMap F hB j
    (j2SpecialMap (nativeChildFrame F j) (native_child_frame_base_bound F hB j) S.seed.base)
  mappedWalk : cycle.walk.copy mappedBase mappedBase =
    (S.seed.walk.map (j2SpecialMap (nativeChildFrame F j)
      (native_child_frame_base_bound F hB j))).map (childMarkedDomainMap F hB j)

theorem native_j2_ordinary_from_raw_seed {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    (S : RawSeedFor hm (nativeChildFrame F j)) :
    Nonempty (OrdinaryCycleFor hm F hB j hj S) := by
  let G := nativeChildFrame F j
  let hBG := native_child_frame_base_bound F hB j
  let w := S.seed.walk.map (j2SpecialMap G hBG)
  have hw : w.IsHamiltonianCycle := SimpleGraph.Walk.IsHamiltonianCycle.map
    (j2_special_map_bijective G hBG) S.seed.hamiltonian
  have hkeepB := seed_special_keeps_remaining_b G hBG S.seed
  obtain ⟨C, hbase, hwalk, _⟩ :=
    native_child_frame_specified_ordinary (by omega : 3 ≤ m) F hB j hj w hw hkeepB
  exact ⟨⟨C, hbase, hwalk⟩⟩

/-- Full same-witness parent data: the special supplier, every
base-rotated ordinary supplier, their chosen actual openings,
and the resulting parent with literal support and seam-chain inventory. -/
structure ParentWitnessFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) where
  specialSeed : RawSeedFor hm F
  special : SpecialPathFor hm F hB specialSeed
  ordinarySeeds : ∀ (j : Fin F.base.length) (hj : 0 < j.val),
    RawSeedFor hm (nativeChildFrame F j)
  ordinary : ∀ (j : Fin F.base.length) (hj : 0 < j.val),
    OrdinaryCycleFor hm F hB j hj (ordinarySeeds j hj)
  paths : ∀ j : Fin F.base.length, ActualChildPath F j
  specialPath : (paths ⟨0, by omega⟩).piece =
    (special_child_path (by omega : 3 ≤ m) F hB special.path special.hamiltonian).piece
  ordinaryInventory : ∀ (j : Fin F.base.length) (hj : 0 < j.val), ∀ e,
    e ∈ (paths j).piece.walk.edges ↔ e ∈ (ordinary j hj).cycle.walk.edges ∧
      e ≠ s(ordinaryRight (by omega : 3 ≤ m) F hB j hj,
        ordinaryLeft (by omega : 3 ≤ m) F hB j hj)
  pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F))
  base : {x : Configuration m // ParentDomain F x}
  cycle : (domainGraph (ParentDomain F)).Walk base base
  childPieces : ∀ j, pieces j = parentPiece F j (paths j)
  baseCoordinate : base.val = rightPort F 0
  hamiltonian : cycle.IsHamiltonianCycle
  support : cycle.support.tail =
    ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse
  edges : cycle.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
    (chainEdges (pieces ⟨0, by omega⟩)
      (List.ofFn fun i : Fin (F.base.length - 1) =>
        pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse

/-- Construct every supplier from native F2 once and keep its actual
false-half assembly and every opening attached to this very parent. -/
theorem native_j2_parent_with_raw_witnesses {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) :
    Nonempty (ParentWitnessFor hm F hB) := by
  classical
  let Q := Classical.choice (native_j2_raw_seed hm F)
  let special := Classical.choice (native_j2_special_from_raw_seed hm F hB Q)
  let seeds (j : Fin F.base.length) (hj : 0 < j.val) :=
    Classical.choice (native_j2_raw_seed hm (nativeChildFrame F j))
  let ordinary (j : Fin F.base.length) (hj : 0 < j.val) :=
    Classical.choice (native_j2_ordinary_from_raw_seed hm F hB j hj (seeds j hj))
  let children (j : Fin F.base.length) (hj : 0 < j.val) := (ordinary j hj).cycle
  obtain ⟨paths, hspecial, hordinary, pieces, base, c, hpieces, hbase, hc, hs, he⟩ :=
    recursive_cycle_from_specified_children_with_inventory (by omega : 3 ≤ m)
      F hB special.path special.hamiltonian children
  exact ⟨⟨Q, special, seeds, ordinary, paths, hspecial, hordinary,
    pieces, base, c, hpieces, hbase, hc, hs, he⟩⟩

private theorem old_base_bound {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) : 3 ≤ F.base.length := by
  simp only [hbase, List.length_append, List.length_singleton]
  omega

private theorem outer_base_bound {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    3 ≤ (outerFrame F A u hbase).base.length := by
  simp only [outerFrame, List.length_append, List.length_singleton]
  omega

private def pChildIndex {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) :
    Fin (outerFrame F A u hbase).base.length :=
  ⟨A.length, by simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩

/-- Lift the actual old P frame to its final child domain without
changing terminal or base inside the saved old witness. -/
def pMarkedChildMap {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    domainGraph (SpecialDomain F (old_base_bound F A u hbase hA)) →g
      domainGraph (ChildDomain (childGap (outerFrame F A u hbase) (pChildIndex F A u hbase))) :=
  ⟨fun x => ⟨x.val, (native_p_marked_domain_eq_child F A u hbase hA x.val).mp x.property⟩,
    fun h => h⟩

theorem p_marked_child_map_bijective {m k : ℕ} (F : SupplyFrame m k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    Function.Bijective (pMarkedChildMap F A u hbase hA) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val, (native_p_marked_domain_eq_child F A u hbase hA y.val).mpr y.property⟩,
      Subtype.ext rfl⟩

/-- In contrast to a newly chosen base-rotated final-child seed, this
specified child cycle is precisely the image of the retained old P seed. -/
structure OldPCycleFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) (P : RawSeedFor hm F) where
  cycle : SpecifiedOrdinaryCycle (by omega : 3 ≤ m) (outerFrame F A u hbase)
    (outer_base_bound F A u hbase hA) (pChildIndex F A u hbase)
    (by change 0 < A.length; omega)
  mappedBase : cycle.base = pMarkedChildMap F A u hbase hA
    (j2SpecialMap F (old_base_bound F A u hbase hA) P.seed.base)
  mappedWalk : cycle.walk.copy mappedBase mappedBase =
    (P.seed.walk.map (j2SpecialMap F (old_base_bound F A u hbase hA))).map
      (pMarkedChildMap F A u hbase hA)

theorem native_j2_old_p_specified_ordinary {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) (P : RawSeedFor hm F) :
    Nonempty (OldPCycleFor hm F A u hbase hA P) := by
  classical
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let j := pChildIndex F A u hbase
  have hj : 0 < j.val := by change 0 < A.length; omega
  let lift := pMarkedChildMap F A u hbase hA
  let w := P.seed.walk.map (j2SpecialMap F (old_base_bound F A u hbase hA))
  have hw : w.IsHamiltonianCycle := SimpleGraph.Walk.IsHamiltonianCycle.map
    (j2_special_map_bijective F _) P.seed.hamiltonian
  let r := ordinaryRight (by omega : 3 ≤ m) O hBO j hj
  let l := ordinaryLeft (by omega : 3 ≤ m) O hBO j hj
  let r' : {v : Configuration m // SpecialDomain F (old_base_bound F A u hbase hA) v} :=
    ⟨r.val, (native_p_marked_domain_eq_child F A u hbase hA r.val).mpr r.property⟩
  let l' : {v : Configuration m // SpecialDomain F (old_base_bound F A u hbase hA) v} :=
    ⟨l.val, (native_p_marked_domain_eq_child F A u hbase hA l.val).mpr l.property⟩
  have hterminal : r'.val (Fin.last m) ∉ F.selected.toFinset := by
    rw [show r'.val = rightPort O (2 + j.val) by rfl]
    rw [rightPort, bc_terminal (by omega : 2 ≤ m), (anchor_coordinates O).2]
    change O.terminal ∉ O.selected.toFinset
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh O (List.mem_append.mpr (Or.inl h))
  have hcut : s(r, l) ∈ (w.map lift).edgeSet := by
    change s(r, l) ∈ (w.map lift).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(r', l'),
      seed_special_keeps_remaining_b F _ P.seed r' l' rfl hterminal, rfl⟩
  let C : SpecifiedOrdinaryCycle (by omega : 3 ≤ m) O hBO j hj :=
    ⟨lift (j2SpecialMap F (old_base_bound F A u hbase hA) P.seed.base),
      w.map lift, SimpleGraph.Walk.IsHamiltonianCycle.map
      (p_marked_child_map_bijective F A u hbase hA) hw, hcut⟩
  exact ⟨⟨C, rfl, rfl⟩⟩

/-- The outer parent remembers the original P frame and its same
cycle, rather than replacing it with a newly chosen final-child seed.
The Q special path, every other child, and all final inventories are
also retained. -/
structure OuterParentWitnessFor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) where
  P : RawSeedFor hm F
  Q : RawSeedFor hm (outerFrame F A u hbase)
  special : SpecialPathFor hm (outerFrame F A u hbase)
    (outer_base_bound F A u hbase hA) Q
  oldP : OldPCycleFor hm F A u hbase hA P
  otherSeeds : ∀ (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val),
    RawSeedFor hm (nativeChildFrame (outerFrame F A u hbase) j)
  otherCycles : ∀ (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val),
    OrdinaryCycleFor hm (outerFrame F A u hbase) (outer_base_bound F A u hbase hA)
      j hj (otherSeeds j hj)
  children : ∀ (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val),
    SpecifiedOrdinaryCycle (by omega : 3 ≤ m) (outerFrame F A u hbase)
      (outer_base_bound F A u hbase hA) j hj
  oldPAttached : children (pChildIndex F A u hbase) (by change 0 < A.length; omega) =
    oldP.cycle
  otherAttached : ∀ j hj, j ≠ pChildIndex F A u hbase →
    children j hj = (otherCycles j hj).cycle
  paths : ∀ j : Fin (outerFrame F A u hbase).base.length,
    ActualChildPath (outerFrame F A u hbase) j
  specialPath : (paths ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩).piece =
    (special_child_path (by omega : 3 ≤ m) (outerFrame F A u hbase)
      (outer_base_bound F A u hbase hA) special.path special.hamiltonian).piece
  ordinaryInventory : ∀ j hj, ∀ e,
    e ∈ (paths j).piece.walk.edges ↔ e ∈ (children j hj).walk.edges ∧
      e ≠ s(ordinaryRight (by omega : 3 ≤ m) (outerFrame F A u hbase)
        (outer_base_bound F A u hbase hA) j hj,
        ordinaryLeft (by omega : 3 ≤ m) (outerFrame F A u hbase)
          (outer_base_bound F A u hbase hA) j hj)
  pieces : Fin (outerFrame F A u hbase).base.length →
    Piece (domainGraph (ParentDomain (outerFrame F A u hbase)))
  base : {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}
  cycle : (domainGraph (ParentDomain (outerFrame F A u hbase))).Walk base base
  childPieces : ∀ j, pieces j = parentPiece (outerFrame F A u hbase) j (paths j)
  baseCoordinate : base.val = rightPort (outerFrame F A u hbase) 0
  hamiltonian : cycle.IsHamiltonianCycle
  support : cycle.support.tail =
    ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse
  edges : cycle.edges = s(base, (pieces (pChildIndex F A u hbase)).finish) ::
    (chainEdges (pieces ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩)
      (List.ofFn fun i : Fin ((outerFrame F A u hbase).base.length - 1) =>
        pieces ⟨i.val + 1, by
          have hi := i.isLt
          simp only [outerFrame, List.length_append, List.length_singleton] at hi ⊢
          omega⟩)).reverse

/-- Native F2 earns both real old P and outer Q suppliers. The final
opening uses exactly the retained old P cycle and literal endpoint table;
the same assembled parent retains its complete support and edge chain. -/
theorem native_j2_outer_parent_with_raw_p_q {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    Nonempty (OuterParentWitnessFor hm F A u hbase hA) := by
  classical
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let jP := pChildIndex F A u hbase
  have hjP : 0 < jP.val := by change 0 < A.length; omega
  let P := Classical.choice (native_j2_raw_seed hm F)
  let Q := Classical.choice (native_j2_raw_seed hm O)
  let special := Classical.choice (native_j2_special_from_raw_seed hm O hBO Q)
  let oldP := Classical.choice (native_j2_old_p_specified_ordinary hm F A u hbase hA P)
  let seeds (j : Fin O.base.length) (hj : 0 < j.val) :=
    Classical.choice (native_j2_raw_seed hm (nativeChildFrame O j))
  let ordinary (j : Fin O.base.length) (hj : 0 < j.val) :=
    Classical.choice (native_j2_ordinary_from_raw_seed hm O hBO j hj (seeds j hj))
  let children (j : Fin O.base.length) (hj : 0 < j.val) :
      SpecifiedOrdinaryCycle (by omega : 3 ≤ m) O hBO j hj :=
    if he : j = jP then he.symm ▸ oldP.cycle else (ordinary j hj).cycle
  have hp : children jP hjP = oldP.cycle := by simp only [children, dif_pos rfl]
  have ho : ∀ j hj, j ≠ jP → children j hj = (ordinary j hj).cycle := by
    intro j hj hne
    simp only [children, dif_neg hne]
  obtain ⟨paths, hspecial, hordinary, pieces, base, c, hpieces, hbase', hc, hs, he⟩ :=
    recursive_cycle_from_specified_children_with_inventory (by omega : 3 ≤ m)
      O hBO special.path special.hamiltonian children
  have hlast : (⟨O.base.length - 1, by
      simp only [O, outerFrame, List.length_append, List.length_singleton]
      omega⟩ : Fin O.base.length) = jP := by
    apply Fin.ext
    simp only [O, outerFrame, List.length_append, List.length_singleton, jP, pChildIndex]
    omega
  rw [hlast] at he
  exact ⟨⟨P, Q, special, oldP, seeds, ordinary, children, hp, ho,
    paths, hspecial, hordinary, pieces, base, c, hpieces, hbase', hc, hs, he⟩⟩

#print axioms native_j2_raw_seed
#print axioms native_j2_special_from_raw_seed
#print axioms native_j2_ordinary_from_raw_seed
#print axioms native_j2_parent_with_raw_witnesses
#print axioms native_j2_old_p_specified_ordinary
#print axioms native_j2_outer_parent_with_raw_p_q

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
