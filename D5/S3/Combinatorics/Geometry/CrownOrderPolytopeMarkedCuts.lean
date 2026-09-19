/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts]
   utility: none
   digest: Marked actual cycle cuts give rooted positive gap compositions. -/

/- Library search (2026-09-19): pinned Mathlib supplies `Equiv.finsetCongr`,
   `Finset.insertNone`/`eraseNone`, and `finSuccEquiv`, but no equivalence from
   marked cycle cuts to rooted positive compositions.  The construction below
   composes those primitives with the actual cut reconstruction. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCycleCuts
import Mathlib.Data.Finset.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

/-- An actual connected cycle partition together with one of its actual boundary cuts. -/
@[ext]
structure MarkedConnectedCyclePartition (N blocks : ℕ) [NeZero N] where
  partition : ConnectedCyclePartition N
  root : Fin N
  root_mem : root ∈ cycleBoundaryCuts partition
  boundary_card : (cycleBoundaryCuts partition).card = blocks

/-- A finite cyclic cut set together with one of its cuts as root. -/
@[ext]
structure RootedCycleCutSet (N blocks : ℕ) where
  cuts : Finset (Fin N)
  root : Fin N
  root_mem : root ∈ cuts
  cuts_card : cuts.card = blocks

private def rootRotation (N : ℕ) [NeZero N] (root : Fin N) :
    Fin N ≃ Option (Fin (N - 1)) :=
  (Equiv.addRight (-root)).trans <|
    (finCongr (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))).symm).trans
      (finSuccEquiv (N - 1))

private theorem rootRotation_root (N : ℕ) [NeZero N] (root : Fin N) :
    rootRotation N root root = none := by
  simp [rootRotation]

private def internalCuts {N : ℕ} [NeZero N] (root : Fin N)
    (cuts : Finset (Fin N)) : Finset (Fin (N - 1)) :=
  Finset.eraseNone ((rootRotation N root).finsetCongr cuts)

private def rootedInternalCuts {N blocks : ℕ} [NeZero N]
    (R : RootedCycleCutSet N blocks) : Finset (Fin (N - 1)) :=
  internalCuts R.root R.cuts

private theorem rootedInternalCuts_card {N blocks : ℕ} [NeZero N]
    (R : RootedCycleCutSet N blocks) :
    (rootedInternalCuts R).card = blocks - 1 := by
  unfold rootedInternalCuts internalCuts
  rw [Finset.card_eraseNone_of_mem]
  · rw [Equiv.finsetCongr_apply, Finset.card_map, R.cuts_card]
  · rw [← rootRotation_root N R.root]
    simp [R.root_mem]

private def rootedCutsOfInternal {N : ℕ} [NeZero N] (root : Fin N)
    (s : Finset (Fin (N - 1))) : Finset (Fin N) :=
  (rootRotation N root).symm.finsetCongr s.insertNone

private theorem root_mem_rootedCutsOfInternal {N : ℕ} [NeZero N]
    (root : Fin N) (s : Finset (Fin (N - 1))) :
    root ∈ rootedCutsOfInternal root s := by
  simp [rootedCutsOfInternal, rootRotation_root]

private theorem card_rootedCutsOfInternal {N : ℕ} [NeZero N]
    (root : Fin N) (s : Finset (Fin (N - 1))) :
    (rootedCutsOfInternal root s).card = s.card + 1 := by
  simp [rootedCutsOfInternal]

private theorem rootedCutsOfInternal_internalCuts {N : ℕ} [NeZero N]
    (root : Fin N) (cuts : Finset (Fin N)) (hroot : root ∈ cuts) :
    rootedCutsOfInternal root (internalCuts root cuts) = cuts := by
  unfold rootedCutsOfInternal internalCuts
  rw [← Equiv.finsetCongr_symm]
  apply (rootRotation N root).finsetCongr.injective
  rw [(rootRotation N root).finsetCongr.apply_symm_apply]
  rw [Finset.insertNone_eraseNone]
  apply Finset.insert_eq_of_mem
  rw [← rootRotation_root N root]
  simp [hroot]

private theorem internalCuts_rootedCutsOfInternal {N : ℕ} [NeZero N]
    (root : Fin N) (s : Finset (Fin (N - 1))) :
    internalCuts root (rootedCutsOfInternal root s) = s := by
  unfold internalCuts rootedCutsOfInternal
  rw [← Equiv.finsetCongr_symm]
  rw [(rootRotation N root).finsetCongr.apply_symm_apply]
  exact Finset.eraseNone_insertNone s

/-- Rooting one cut turns a cyclic cut set with `blocks` cuts into a root vertex
    and the `blocks - 1` internal boundaries of the resulting linear interval. -/
def rootedCycleCutSetEquiv (N blocks : ℕ) [NeZero N] (hblocks : 0 < blocks) :
    RootedCycleCutSet N blocks ≃ Fin N × PositionSet (N - 1) (blocks - 1) where
  toFun R := (R.root, ⟨rootedInternalCuts R, rootedInternalCuts_card R⟩)
  invFun data :=
    { cuts := rootedCutsOfInternal data.1 data.2.1
      root := data.1
      root_mem := root_mem_rootedCutsOfInternal data.1 data.2.1
      cuts_card := by
        rw [card_rootedCutsOfInternal, data.2.2]
        omega }
  left_inv R := by
    apply RootedCycleCutSet.ext
    · exact rootedCutsOfInternal_internalCuts R.root R.cuts R.root_mem
    · rfl
  right_inv data := by
    rcases data with ⟨root, s, hs⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact internalCuts_rootedCutsOfInternal root s

private noncomputable def markedPartitionCutEquiv (N blocks : ℕ) [NeZero N]
    (hN : 3 ≤ N) (hblocks : 2 ≤ blocks) :
    MarkedConnectedCyclePartition N blocks ≃ RootedCycleCutSet N blocks where
  toFun P :=
    { cuts := cycleBoundaryCuts P.partition
      root := P.root
      root_mem := P.root_mem
      cuts_card := P.boundary_card }
  invFun R := by
    let cuts : {cuts : Finset (Fin N) // 2 ≤ cuts.card} := ⟨R.cuts, by
      rw [R.cuts_card]
      exact hblocks⟩
    let P := (connectedCyclePartitionCutsEquiv N hN).symm cuts
    exact
      { partition := P.1
        root := R.root
        root_mem := by
          have hcuts : cycleBoundaryCuts P.1 = R.cuts := by
            exact congrArg Subtype.val
              ((connectedCyclePartitionCutsEquiv N hN).apply_symm_apply cuts)
          rw [hcuts]
          exact R.root_mem
        boundary_card := by
          have hcuts : cycleBoundaryCuts P.1 = R.cuts := by
            exact congrArg Subtype.val
              ((connectedCyclePartitionCutsEquiv N hN).apply_symm_apply cuts)
          rw [hcuts, R.cuts_card] }
  left_inv P := by
    apply MarkedConnectedCyclePartition.ext
    · change ((connectedCyclePartitionCutsEquiv N hN).symm
          ⟨cycleBoundaryCuts P.partition, by
            rw [P.boundary_card]
            exact hblocks⟩).1 = P.partition
      exact congrArg Subtype.val ((connectedCyclePartitionCutsEquiv N hN).symm_apply_apply
        ⟨P.partition, by
          rw [P.boundary_card]
          exact hblocks⟩)
    · rfl
  right_inv R := by
    apply RootedCycleCutSet.ext
    · change cycleBoundaryCuts (((connectedCyclePartitionCutsEquiv N hN).symm
          ⟨R.cuts, by
            rw [R.cuts_card]
            exact hblocks⟩).1) = R.cuts
      exact congrArg Subtype.val ((connectedCyclePartitionCutsEquiv N hN).apply_symm_apply
        ⟨R.cuts, by
          rw [R.cuts_card]
          exact hblocks⟩)
    · rfl

/-- The exact marked-cut coordinate system: an actual connected cycle partition
    with `blocks ≥ 2` blocks and a marked actual boundary is equivalent to a root
    vertex and a positive composition of the cycle length into those blocks. -/
noncomputable def markedCyclePartitionCompositionEquiv (N blocks : ℕ) [NeZero N]
    (hN : 3 ≤ N) (hblocks : 2 ≤ blocks) :
    MarkedConnectedCyclePartition N blocks ≃ Fin N × IndexedComposition N blocks :=
  (markedPartitionCutEquiv N blocks hN hblocks).trans <|
    (rootedCycleCutSetEquiv N blocks (by omega)).trans <|
      Equiv.prodCongr (Equiv.refl _) <|
        ((fixedLengthCompositionEquiv N blocks (by omega) (by omega)).symm.trans
          (IndexedComposition.compositionEquiv N blocks).symm)

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
