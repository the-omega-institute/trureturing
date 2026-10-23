/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2Seed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2Seed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One actual native seed cycle earns six joint paths, both literal restored halves, and all three retained-edge invariants. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2JointPaths
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SelectedC
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
import D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
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
open private raw_zero_coordinates relabel_anchor frame_selected_coordinates from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private markedCut_injective from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

private theorem joint_half_union {m : ℕ} (D : Configuration m → Prop) :
    actualJointCuts D = actualHalfCuts D false ∪ actualHalfCuts D true := by
  classical
  ext e
  simp only [actualJointCuts, actualHalfCuts, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨⟨i, side⟩, hi⟩
    cases side
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨(i, false), hi⟩
    · exact ⟨(i, true), hi⟩

private theorem half_disjoint {m : ℕ} (hm : 5 ≤ m)
    (D : Configuration m → Prop) :
    Disjoint (actualHalfCuts D false) (actualHalfCuts D true) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hf ht
  have hf' : HalfCut m false (Sym2.map Subtype.val e) := by
    simpa only [actualHalfCuts, Finset.mem_filter, Finset.mem_univ, true_and] using hf
  have ht' : HalfCut m true (Sym2.map Subtype.val e) := by
    simpa only [actualHalfCuts, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  obtain ⟨i, hi⟩ := hf'
  obtain ⟨j, hj⟩ := ht'
  have he := markedCut_injective hm (hi.symm.trans hj)
  exact Bool.noConfusion (congrArg Prod.snd he)

private theorem seed_protected_pair {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    s(relabel F (Fin.last m), relabel F 0) =
      s(protectedP F (by omega), protectedQ F (by omega)) := by
  have hp : relabel F (Fin.last m) = anchor F 0 := by
    have h := congrArg (fun z : Configuration m => z 0) (relabel_anchor F)
    change relabel F (NativeJ2Words.rightPort m 0 0) = anchor F 0 at h
    rw [(raw_zero_coordinates hm).1] at h
    exact h
  have hq : relabel F 0 = anchor F ⟨1, by omega⟩ := by
    have h := congrArg (fun z : Configuration m => z ⟨1, by omega⟩) (relabel_anchor F)
    change relabel F (NativeJ2Words.rightPort m 0 ⟨1, by omega⟩) =
      anchor F ⟨1, by omega⟩ at h
    rw [(raw_zero_coordinates hm).2] at h
    exact h
  simp only [protectedP, protectedQ, Nat.reduceSub, frame_selected_coordinates hm F,
    List.getElem_cons_zero, List.getElem_cons_succ, hp, hq]

/-- One actual cycle, all three literal partitions and all retained-edge
invariants needed before constructing the exceptional third-order state. -/
structure SeedFor {m : ℕ} (F : SupplyFrame m 2) where
  base : {x : Configuration m // FrameDomain F x}
  walk : (domainGraph (FrameDomain F)).Walk base base
  hamiltonian : walk.IsHamiltonianCycle
  K : Finset (Sym2 {x : Configuration m // FrameDomain F x})
  H : Finset (Sym2 {x : Configuration m // FrameDomain F x})
  joint : Fin 6 → Piece (domainGraph (FrameDomain F))
  primary : Fin 3 → Piece (domainGraph (FrameDomain F))
  opposite : Fin 3 → Piece (domainGraph (FrameDomain F))
  jointPorts : ∀ i,
    (joint i).start.val = relabel F * port m (componentStartPort i) ∧
      (joint i).finish.val = relabel F * port m (componentFinishPort i)
  primaryPorts : ∀ i,
    (primary i).start.val = relabel F * port m (halfStart false i) ∧
      (primary i).finish.val = relabel F * port m (halfFinish false i)
  oppositePorts : ∀ i,
    (opposite i).start.val = relabel F * port m (halfStart true i) ∧
      (opposite i).finish.val = relabel F * port m (halfFinish true i)
  partitions : ActualTwoOrderPartitions walk K H
    (List.ofFn joint) (List.ofFn primary) (List.ofFn opposite)
  keepsProtectedA : ∀ (x y : {v : Configuration m // FrameDomain F v}),
    y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠
      s(protectedP F (by omega), protectedQ F (by omega)) → s(x, y) ∈ walk.edges
  keepsRemainingB : ∀ (x y : {v : Configuration m // FrameDomain F v}),
    y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
      s(x, y) ∈ walk.edges
  selectedC : ∀ (x y : {v : Configuration m // FrameDomain F v}),
    y.val = x.val * c m → s(x, y) ∈ walk.edges →
      x.val (Fin.last m) ∈ F.selected.toFinset

/-- Choose the raw native witness only once. Its same mapped cycle
simultaneously earns all three actual partitions, their literal endpoints,
and the protected-a, remaining-b and selected-c induction invariants. -/
theorem native_actual_j2_seed {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    Nonempty (SeedFor F) := by
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
  refine ⟨⟨_, _, hham, K, H, joint, primary, opposite, hjports, hpports, hoports,
    ⟨hham.isCycle, hd, ?_, ⟨hps, hpe, hpc⟩, ⟨hos, hoe, hoc⟩⟩,
    ?_, hB, native_j2_frame_c_selected hm F _ hframe⟩⟩
  · dsimp only [iso] at hu
    rw [hu] at hje hjc
    exact ⟨hjs, hje, hjc⟩
  · intro x y hxy hpair
    exact hA x y hxy (by simpa only [seed_protected_pair hm F] using hpair)

#print axioms native_actual_j2_seed

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2Seed
