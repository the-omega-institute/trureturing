/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual two-label witnesses construct an unconditional parent Hamilton cycle. -/
/- Unconditional two-selected-label parent construction.
   The special path uses the literal false-half pieces of one native F2
   cycle. Each other child uses its own native frame cycle and earned
   remaining-b cut. Independent child coverage earns the parent cycle. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialBoundaryInstances
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

private theorem j2_frame_special_domain {m : ℕ} (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) (x : Configuration m) :
    FrameDomain F x ↔ SpecialDomain F hB x := by
  change Layer F.selected.toFinset (F.terminal :: F.base : Cycle (Fin (m + 1))) x ↔
    Layer F.selected.toFinset (F.terminal :: F.base.rotate 0 : Cycle (Fin (m + 1))) x
  rw [List.rotate_zero]

private def j2SpecialMap {m : ℕ} (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) :
    domainGraph (FrameDomain F) →g domainGraph (SpecialDomain F hB) :=
  ⟨fun x => ⟨x.val, (j2_frame_special_domain F hB x.val).mp x.property⟩, fun h => h⟩

private theorem j2_special_map_bijective {m : ℕ} (F : SupplyFrame m 2)
    (hB : 3 ≤ F.base.length) : Function.Bijective (j2SpecialMap F hB) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.val, (j2_frame_special_domain F hB y.val).mpr y.property⟩, Subtype.ext rfl⟩

private noncomputable def j2RawCut {m : ℕ} (hm : 5 ≤ m) (i : Fin 3) :
    Sym2 {x : Configuration m // F2Domain m x} :=
  s(⟨port m (i, false, false), native_j2_port_domain hm _⟩,
    ⟨port m (i, false, true), native_j2_port_domain hm _⟩)

private theorem j2_raw_half_cuts {m : ℕ} (hm : 5 ≤ m) :
    actualHalfCuts (F2Domain m) false = Finset.univ.image (j2RawCut hm) := by
  classical
  ext e
  change (e ∈ Finset.univ.filter (fun z : Sym2 {x : Configuration m // F2Domain m x} =>
    HalfCut m false (Sym2.map Subtype.val z))) ↔ _
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, i, hi⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    simpa only [j2RawCut, Sym2.map_mk, markedEdge] using hi.symm
  · rintro ⟨i, _, rfl⟩
    exact ⟨Finset.mem_univ _, i, rfl⟩

private theorem j2_mapped_half_cuts {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) :
    ((actualHalfCuts (F2Domain m) false).image
      (Sym2.map (frameDomainIso hm F).toHom)).image
        (Sym2.map (j2SpecialMap F hB)) = specialCuts (by omega : 3 ≤ m) F hB := by
  classical
  let rawToFrame : {x : Configuration m // F2Domain m x} →
      {x : Configuration m // FrameDomain F x} := (frameDomainIso hm F).toHom
  let frameToSpecial : {x : Configuration m // FrameDomain F x} →
      {x : Configuration m // SpecialDomain F hB x} := j2SpecialMap F hB
  change ((actualHalfCuts (F2Domain m) false).image (Sym2.map rawToFrame)).image
    (Sym2.map frameToSpecial) = specialCuts (by omega : 3 ≤ m) F hB
  rw [j2_raw_half_cuts hm, Finset.image_image, Finset.image_image]
  unfold specialCuts
  congr 1
  funext i
  apply Sym2.map.injective Subtype.val_injective
  change s(relabel F * port m (i, false, false),
    relabel F * port m (i, false, true)) =
      s(specialPort F (i, 0), specialPort F (i, 1))
  simp only [port, Bool.false_eq_true, ↓reduceIte, specialPort,
    Fin.val_zero, Fin.val_one, zero_ne_one, one_ne_zero]
  rw [(native_j2_frame_ports hm F i).1, (native_j2_frame_ports hm F i).2]

private def j2HalfStartPort (i : Fin 3) : Port 2 :=
  match i.val with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | _ => (1, 0)

private def j2HalfFinishPort (i : Fin 3) : Port 2 :=
  match i.val with
  | 0 => (2, 0)
  | 1 => (1, 1)
  | _ => (2, 1)

private theorem j2_half_endpoints {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (i : Fin 3) :
    relabel F * port m (halfStart false i) = specialPort F (j2HalfStartPort i) ∧
    relabel F * port m (halfFinish false i) = specialPort F (j2HalfFinishPort i) ∧
    evenBoundary 2 (code (j2HalfStartPort i)) (code (j2HalfFinishPort i)) := by
  fin_cases i
  · refine ⟨?_, ?_, ?_⟩
    · change relabel F * NativeJ2Words.rightPort m 0 = rightPort F 0
      exact (native_j2_frame_ports hm F 0).1
    · change relabel F * NativeJ2Words.rightPort m 2 = rightPort F 2
      exact (native_j2_frame_ports hm F 2).1
    · norm_num [j2HalfStartPort, j2HalfFinishPort, evenBoundary, pair, code]
  · refine ⟨?_, ?_, ?_⟩
    · change relabel F * NativeJ2Words.leftPort m 0 = leftPort F 0
      exact (native_j2_frame_ports hm F 0).2
    · change relabel F * NativeJ2Words.leftPort m 1 = leftPort F 1
      exact (native_j2_frame_ports hm F 1).2
    · norm_num [j2HalfStartPort, j2HalfFinishPort, evenBoundary, pair, code]
  · refine ⟨?_, ?_, ?_⟩
    · change relabel F * NativeJ2Words.rightPort m 1 = rightPort F 1
      exact (native_j2_frame_ports hm F 1).1
    · change relabel F * NativeJ2Words.leftPort m 2 = leftPort F 2
      exact (native_j2_frame_ports hm F 2).2
    · norm_num [j2HalfStartPort, j2HalfFinishPort, evenBoundary, pair, code]

/-- The Hamilton path is constructed from the native F2 cycle itself.
The domain map is the identity on configurations; every sliced edge and
every endpoint is transferred from the same actual cycle. -/
theorem native_j2_special_hamilton_path {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) :
    ∃ q : (domainGraph (SpecialDomain F hB)).Walk
      (specialVertex (by omega : 3 ≤ m) F hB (0, 0))
      (specialVertex (by omega : 3 ≤ m) F hB (Fin.last 2, 1)),
      q.IsHamiltonian := by
  classical
  obtain ⟨rawBase, rawWalk, _, _, hraw, hinv, _⟩ :=
    native_j2_frame_cycle_with_inventory hm F
  let iso : domainGraph (F2Domain m) ≃g domainGraph (FrameDomain F) := frameDomainIso hm F
  let w := rawWalk.map iso.toHom
  let cuts := (actualHalfCuts (F2Domain m) false).image (Sym2.map iso.toHom)
  obtain ⟨pieces, hend, hw, _, hs, he, hc⟩ :=
    native_actual_j2_frame_half_paths hm F false rawWalk hraw hinv
  let lift : domainGraph (FrameDomain F) →g domainGraph (SpecialDomain F hB) :=
    j2SpecialMap F hB
  let w' := w.map lift
  let ps := (List.ofFn pieces).map (mapPiece lift)
  have hbij : Function.Bijective lift := j2_special_map_bijective F hB
  obtain ⟨_, _, hs', he', hc'⟩ :=
    actual_cycle_partition_map lift hbij.injective w hw.isCycle
      (List.ofFn pieces) cuts hs he hc
  have hcuts : cuts.image (Sym2.map lift) = specialCuts (by omega : 3 ≤ m) F hB :=
    j2_mapped_half_cuts hm F hB
  rw [hcuts] at he' hc'
  have hp : ∀ z ∈ ps, ∃ p q : Port 2,
      z.start.val = specialPort F p ∧ z.finish.val = specialPort F q ∧
        evenBoundary 2 (code p) (code q) := by
    intro z hz
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpiece
    obtain ⟨hstart, hfinish, hboundary⟩ := j2_half_endpoints hm F i
    exact ⟨j2HalfStartPort i, j2HalfFinishPort i,
      (hend i).1.trans hstart, (hend i).2.trans hfinish, hboundary⟩
  obtain ⟨_, q, hq, _⟩ := native_special_child_even_path (by omega : 3 ≤ m) 0 F hB
    w' (SimpleGraph.Walk.IsHamiltonianCycle.map hbij hw) ps hs' he' hc' hp
  exact ⟨q, hq⟩

private theorem j2_special_cycle_with_kept_b {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) :
    ∃ base : {x : Configuration m // SpecialDomain F hB x},
      ∃ w : (domainGraph (SpecialDomain F hB)).Walk base base,
        w.IsHamiltonianCycle ∧
        (∀ x y : {v : Configuration m // SpecialDomain F hB v},
          y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
            s(x, y) ∈ w.edges) := by
  classical
  obtain ⟨_, _, base, w, _, _, _, _, hw, _, _, _, hkeepB, _⟩ :=
    native_j2_frame_cycle_with_inventory hm F
  let lift : domainGraph (FrameDomain F) →g domainGraph (SpecialDomain F hB) :=
    j2SpecialMap F hB
  refine ⟨lift base, w.map lift,
    SimpleGraph.Walk.IsHamiltonianCycle.map (j2_special_map_bijective F hB) hw, ?_⟩
  intro x y hy ht
  let x₀ : {v : Configuration m // FrameDomain F v} :=
    ⟨x.val, (j2_frame_special_domain F hB x.val).mpr x.property⟩
  let y₀ : {v : Configuration m // FrameDomain F v} :=
    ⟨y.val, (j2_frame_special_domain F hB y.val).mpr y.property⟩
  have hx : lift x₀ = x := Subtype.ext rfl
  have hy' : lift y₀ = y := Subtype.ext rfl
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr ⟨s(x₀, y₀), hkeepB x₀ y₀ hy ht, by
    rw [Sym2.map_mk, hx, hy']⟩

/-- Unconditional parent Hamiltonicity for every two-selected-label
frame with a genuine base of length at least three. The special path,
the ordinary cycles and their removed b edges are constructed, not
assumed as induction certificates. -/
theorem native_j2_parent_hamiltonian_cycle {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (hB : 3 ≤ F.base.length) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
        base.val = rightPort F 0 ∧ c.IsHamiltonianCycle := by
  classical
  have hm3 : 3 ≤ m := by omega
  obtain ⟨q, hq⟩ := native_j2_special_hamilton_path hm F hB
  have hchildren (j : Fin F.base.length) (hj : 0 < j.val) :
      Nonempty (SpecifiedOrdinaryCycle hm3 F hB j hj) := by
    let G := nativeChildFrame F j
    have hBG : 3 ≤ G.base.length := by
      simpa only [G, nativeChildFrame, List.length_rotate] using hB
    obtain ⟨base, w, hw, hkeepB⟩ := j2_special_cycle_with_kept_b hm G hBG
    obtain ⟨C, _⟩ := native_child_frame_specified_ordinary hm3 F hB j hj w hw hkeepB
    exact ⟨C⟩
  let children (j : Fin F.base.length) (hj : 0 < j.val) :
      SpecifiedOrdinaryCycle hm3 F hB j hj := Classical.choice (hchildren j hj)
  obtain ⟨_, _, _, _, base, c, _, hbase, hc, _, _⟩ :=
    recursive_cycle_from_specified_children_with_inventory hm3 F hB q hq children
  exact ⟨base, c, hbase, hc⟩

#print axioms native_j2_special_hamilton_path
#print axioms native_j2_parent_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
