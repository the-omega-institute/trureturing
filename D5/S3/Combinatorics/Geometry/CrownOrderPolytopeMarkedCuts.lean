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
   composes those primitives with the actual cut reconstruction.  For the
   compatible-profile sum it also supplies `Finset.even_sum_iff_even_card_odd`,
   `Finset.card_eq_sum_card_fiberwise`, and `Nat.card_sigma`; neither Mathlib nor
   D5 contains the actual quotient-block count or compatible-profile decomposition. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCyclePartitions
import Mathlib.Algebra.BigOperators.Ring.Nat
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

private def internalCuts {N : ℕ} [NeZero N] (root : Fin N)
    (cuts : Finset (Fin N)) : Finset (Fin (N - 1)) :=
  Finset.eraseNone ((rootRotation N root).finsetCongr cuts)

private def rootedInternalCuts {N blocks : ℕ} [NeZero N]
    (R : RootedCycleCutSet N blocks) : Finset (Fin (N - 1)) :=
  internalCuts R.root R.cuts

private def rootedCutsOfInternal {N : ℕ} [NeZero N] (root : Fin N)
    (s : Finset (Fin (N - 1))) : Finset (Fin N) :=
  (rootRotation N root).symm.finsetCongr s.insertNone

private theorem rootedCutsOfInternal_internalCuts {N : ℕ} [NeZero N]
    (root : Fin N) (cuts : Finset (Fin N)) (hroot : root ∈ cuts) :
    rootedCutsOfInternal root (internalCuts root cuts) = cuts := by
  unfold rootedCutsOfInternal internalCuts
  rw [← Equiv.finsetCongr_symm]
  apply (rootRotation N root).finsetCongr.injective
  rw [(rootRotation N root).finsetCongr.apply_symm_apply]
  rw [Finset.insertNone_eraseNone]
  apply Finset.insert_eq_of_mem
  have hrotation : rootRotation N root root = none := by simp [rootRotation]
  rw [← hrotation]
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
  toFun R := (R.root, ⟨rootedInternalCuts R, by
    unfold rootedInternalCuts internalCuts
    rw [Finset.card_eraseNone_of_mem]
    · rw [Equiv.finsetCongr_apply, Finset.card_map, R.cuts_card]
    · have hrotation : rootRotation N R.root R.root = none := by simp [rootRotation]
      rw [← hrotation]
      simp [R.root_mem]⟩)
  invFun data :=
    { cuts := rootedCutsOfInternal data.1 data.2.1
      root := data.1
      root_mem := by
        unfold rootedCutsOfInternal
        rw [Equiv.finsetCongr_apply]
        apply Finset.mem_map.mpr
        refine ⟨none, by simp, ?_⟩
        simp [rootRotation]
      cuts_card := by
        simp only [rootedCutsOfInternal, Equiv.finsetCongr_apply, Finset.card_map,
          Finset.card_insertNone]
        rw [data.2.2]
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

private def linearComposition {N blocks : ℕ} (c : IndexedComposition N blocks) :
    Composition N :=
  (IndexedComposition.compositionEquiv N blocks c).1

private def rootSuccessorRotation (N : ℕ) [NeZero N] (root : Fin N) : Fin N ≃ Fin N :=
  (finRotate N).trans (Equiv.addRight root)

private def compositionBlockIndex {N blocks : ℕ} [NeZero N]
    (root : Fin N) (c : IndexedComposition N blocks) (v : Fin N) : Fin blocks :=
  Fin.cast c.blocks_length ((linearComposition c).index ((rootSuccessorRotation N root).symm v))

private def compositionCycleIndex {N : ℕ} [NeZero N]
    (root : Fin N) (d : Composition N) (v : Fin N) : Fin d.length :=
  d.index ((rootSuccessorRotation N root).symm v)

private def compositionBlockGraphHom {N : ℕ} [NeZero N]
    (root : Fin N) (d : Composition N) (i : Fin d.length) :
    SimpleGraph.pathGraph (d.blocksFun i) →g
      cyclePartitionGraph (Setoid.ker (compositionCycleIndex root d)) where
  toFun k := rootSuccessorRotation N root (d.embedding i k)
  map_rel' := by
    intro a b hab
    have hab' : (SimpleGraph.pathGraph N).Adj (d.embedding i a) (d.embedding i b) := by
      rw [SimpleGraph.pathGraph_adj] at hab ⊢
      change d.sizeUpTo i + a.val + 1 = d.sizeUpTo i + b.val ∨
        d.sizeUpTo i + b.val + 1 = d.sizeUpTo i + a.val
      omega
    refine ⟨?_, ?_⟩
    · simp only [Setoid.ker_def, compositionCycleIndex, Equiv.symm_apply_apply]
      rw [d.index_embedding, d.index_embedding]
    · simpa [rootSuccessorRotation, SimpleGraph.cycleGraph_adj', finRotate_apply] using
        (SimpleGraph.pathGraph_le_cycleGraph hab')

private noncomputable def compositionCyclePartition {N blocks : ℕ} [NeZero N]
    (root : Fin N) (c : IndexedComposition N blocks) : ConnectedCyclePartition N where
  toSetoid := Setoid.ker (compositionCycleIndex root (linearComposition c))
  connected := by
    intro u v huv
    let d := linearComposition c
    let x := (rootSuccessorRotation N root).symm u
    let y := (rootSuccessorRotation N root).symm v
    have hindex : d.index x = d.index y := by
      simpa [d, x, y, compositionCycleIndex] using huv
    let i := d.index x
    let kx := d.invEmbedding x
    let ky : Fin (d.blocksFun i) :=
      Fin.cast (congrArg d.blocksFun hindex.symm) (d.invEmbedding y)
    obtain ⟨w⟩ := SimpleGraph.pathGraph_preconnected (d.blocksFun i) kx ky
    let f := compositionBlockGraphHom root d i
    have w' := w.map f
    change Nonempty ((cyclePartitionGraph
      (Setoid.ker (compositionCycleIndex root (linearComposition c)))).Walk u v)
    refine ⟨?_⟩
    have hx : f kx = u := by
      change rootSuccessorRotation N root (d.embedding (d.index x) (d.invEmbedding x)) = u
      rw [d.embedding_comp_inv]
      exact (rootSuccessorRotation N root).apply_symm_apply u
    have hy : f ky = v := by
      change rootSuccessorRotation N root (d.embedding i ky) = v
      have hembed : d.embedding i ky = y := by
        apply Fin.ext
        simp only [Composition.coe_embedding]
        have hembedY := congrArg Fin.val (d.embedding_comp_inv y)
        simp only [Composition.coe_embedding] at hembedY
        have hindexVal := congrArg Fin.val hindex
        simp only [ky, Fin.val_cast]
        dsimp [i]
        rw [hindexVal]
        exact hembedY
      rw [hembed]
      exact (rootSuccessorRotation N root).apply_symm_apply v
    exact hx ▸ hy ▸ w'

private theorem mem_compositionInternalCuts_iff_index_ne {N : ℕ} (hN : 0 < N)
    (d : Composition N) (x : Fin (N - 1)) :
    x ∈ compositionAsSetEquiv N d.toCompositionAsSet ↔
      d.index (⟨x.val, by omega⟩ : Fin N) ≠
        d.index (⟨x.val + 1, by omega⟩ : Fin N) := by
  unfold compositionAsSetEquiv
  change x ∈ ({i : Fin (N - 1) |
    (⟨1 + i.val, by omega⟩ : Fin (N + 1)) ∈ d.toCompositionAsSet.boundaries} : Set _).toFinset ↔ _
  rw [Set.mem_toFinset]
  change (⟨1 + x.val, by omega⟩ : Fin (N + 1)) ∈ d.toCompositionAsSet.boundaries ↔ _
  rw [Composition.toCompositionAsSet_boundaries]
  let X : Fin N := ⟨x.val, by omega⟩
  let Y : Fin N := ⟨x.val + 1, by omega⟩
  constructor
  · intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
    have haVal : d.sizeUpTo a.val = x.val + 1 := by
      have := congrArg Fin.val ha
      simpa [Composition.boundary, Nat.add_comm] using this
    have haPos : 0 < a.val := by
      by_contra h
      have : a.val = 0 := by omega
      rw [this, d.sizeUpTo_zero] at haVal
      omega
    have haLt : a.val < d.length := by
      have haLe : a.val ≤ d.length := by omega
      by_contra h
      have : a.val = d.length := by omega
      rw [this, d.sizeUpTo_length] at haVal
      omega
    let i₀ : Fin d.length := ⟨a.val - 1, by omega⟩
    let i₁ : Fin d.length := ⟨a.val, haLt⟩
    have hi₀succ : i₀.val + 1 = a.val := by dsimp [i₀]; omega
    have hstrict₀ := d.sizeUpTo_strict_mono i₀.isLt
    have hstrict₁ := d.sizeUpTo_strict_mono i₁.isLt
    have hX : d.index X = i₀ := by
      symm
      rw [← d.mem_range_embedding_iff']
      rw [d.mem_range_embedding_iff]
      dsimp [X]
      constructor
      · rw [hi₀succ, haVal] at hstrict₀
        omega
      · rw [hi₀succ, haVal]
        omega
    have hY : d.index Y = i₁ := by
      symm
      rw [← d.mem_range_embedding_iff']
      rw [d.mem_range_embedding_iff]
      dsimp [Y, i₁]
      constructor
      · rw [haVal]
      · rw [haVal] at hstrict₁
        omega
    rw [hX, hY]
    intro h
    have := congrArg Fin.val h
    dsimp [i₀, i₁] at this
    omega
  · intro hne
    let i₀ := d.index X
    let i₁ := d.index Y
    have hiNe : i₀ ≠ i₁ := by simpa [i₀, i₁, X, Y] using hne
    have hXlow := d.sizeUpTo_index_le X
    have hXhigh := d.lt_sizeUpTo_index_succ X
    have hYlow := d.sizeUpTo_index_le Y
    have hYhigh := d.lt_sizeUpTo_index_succ Y
    change d.sizeUpTo i₀.val ≤ x.val at hXlow
    change x.val < d.sizeUpTo (i₀.val + 1) at hXhigh
    change d.sizeUpTo i₁.val ≤ x.val + 1 at hYlow
    change x.val + 1 < d.sizeUpTo (i₁.val + 1) at hYhigh
    have hiLt : i₀ < i₁ := by
      have hiLe : i₀ ≤ i₁ := by
        by_contra h
        have hsucc : i₁.val + 1 ≤ i₀.val := by omega
        have hmono := d.monotone_sizeUpTo hsucc
        change d.sizeUpTo (i₁.val + 1) ≤ d.sizeUpTo i₀.val at hmono
        omega
      have hiNeVal : i₀.val ≠ i₁.val := fun h => hiNe (Fin.ext h)
      have hiLeVal : i₀.val ≤ i₁.val := hiLe
      exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne hiLeVal hiNeVal)
    have hmono := d.monotone_sizeUpTo (show i₀.val + 1 ≤ i₁.val by omega)
    have hboundary : d.sizeUpTo i₁.val = x.val + 1 := by omega
    apply Finset.mem_map.mpr
    refine ⟨⟨i₁.val, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simpa [Composition.boundary, i₁, Nat.add_comm] using hboundary

private theorem internalCuts_compositionCyclePartition {N blocks : ℕ} [NeZero N]
    (hN : 3 ≤ N) (root : Fin N) (c : IndexedComposition N blocks) :
    internalCuts root (cycleBoundaryCuts (compositionCyclePartition root c)) =
      compositionAsSetEquiv N (linearComposition c).toCompositionAsSet := by
  ext x
  rw [mem_compositionInternalCuts_iff_index_ne (by omega)]
  unfold internalCuts
  rw [Finset.mem_eraseNone, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
  have hpreimage : (rootRotation N root).symm (some x) =
      rootSuccessorRotation N root (⟨x.val, by omega⟩ : Fin N) := by
    apply (rootRotation N root).injective
    rw [(rootRotation N root).apply_symm_apply]
    symm
    unfold rootRotation
    simp only [Equiv.trans_apply, Equiv.coe_addRight, finCongr_apply]
    rw [finSuccEquiv_eq_some]
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_succ]
    have hcancel :
        rootSuccessorRotation N root (⟨x.val, by omega⟩ : Fin N) + (-root) =
          (⟨x.val, by omega⟩ : Fin N) + 1 := by
      simp [rootSuccessorRotation, finRotate_apply, add_assoc]
    have hcancelVal := congrArg Fin.val hcancel
    have hxlt : x.val + 1 < N := by omega
    have hrhs : (((⟨x.val, by omega⟩ : Fin N) + 1).val) = x.val + 1 := by
      simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega), Nat.mod_eq_of_lt hxlt]
    exact hcancelVal.trans hrhs
  rw [hpreimage]
  simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  change (compositionCycleIndex root (linearComposition c)
      (rootSuccessorRotation N root (⟨x.val, by omega⟩ : Fin N)) ≠
    compositionCycleIndex root (linearComposition c)
      (rootSuccessorRotation N root (⟨x.val, by omega⟩ : Fin N) + 1)) ↔ _
  unfold compositionCycleIndex
  simp only [Equiv.symm_apply_apply]
  have hsuccessor :
      rootSuccessorRotation N root (⟨x.val, by omega⟩ : Fin N) + 1 =
        rootSuccessorRotation N root (⟨x.val + 1, by omega⟩ : Fin N) := by
    let X : Fin N := ⟨x.val, by omega⟩
    let Y : Fin N := ⟨x.val + 1, by omega⟩
    have hY : Y = X + 1 := by
      apply Fin.ext
      change x.val + 1 = (x.val + (1 % N)) % N
      rw [Nat.mod_eq_of_lt (show 1 < N by omega), Nat.mod_eq_of_lt (by omega)]
    change rootSuccessorRotation N root X + 1 = rootSuccessorRotation N root Y
    rw [hY]
    simp only [rootSuccessorRotation, Equiv.trans_apply, Equiv.coe_addRight, finRotate_apply]
    abel
  rw [hsuccessor]
  simp only [Equiv.symm_apply_apply]

private def compositionBlockRepresentative {N blocks : ℕ} [NeZero N]
    (root : Fin N) (c : IndexedComposition N blocks) (j : Fin blocks) : Fin N :=
  let d := linearComposition c
  let j' : Fin d.length := Fin.cast c.blocks_length.symm j
  rootSuccessorRotation N root (d.embedding j' ⟨0, by
    have := d.one_le_blocksFun j'
    omega⟩)

private noncomputable def compositionBlockQuotientEquiv {N blocks : ℕ} [NeZero N]
    (root : Fin N) (c : IndexedComposition N blocks) :
    Fin blocks ≃ Quotient (compositionCyclePartition root c).toSetoid := by
  have hrepresentative (j : Fin blocks) :
      compositionBlockIndex root c (compositionBlockRepresentative root c j) = j := by
    simp only [compositionBlockIndex, compositionBlockRepresentative, Equiv.symm_apply_apply]
    rw [(linearComposition c).index_embedding]
    exact Fin.ext rfl
  let f : Fin blocks → Quotient (compositionCyclePartition root c).toSetoid := fun j =>
    Quotient.mk'' (compositionBlockRepresentative root c j)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hrel := @Quotient.exact _ (compositionCyclePartition root c).toSetoid _ _ hab
    have hrel' := congrArg (Fin.cast c.blocks_length) hrel
    change compositionBlockIndex root c (compositionBlockRepresentative root c a) =
      compositionBlockIndex root c (compositionBlockRepresentative root c b) at hrel'
    simpa only [hrepresentative] using hrel'
  · intro q
    refine Quotient.inductionOn q ?_
    intro v
    let j := compositionBlockIndex root c v
    refine ⟨j, ?_⟩
    apply Quotient.sound
    change (linearComposition c).index ((rootSuccessorRotation N root).symm
        (compositionBlockRepresentative root c j)) =
      (linearComposition c).index ((rootSuccessorRotation N root).symm v)
    apply (Fin.cast_inj (eq := c.blocks_length)).mp
    change compositionBlockIndex root c (compositionBlockRepresentative root c j) =
      compositionBlockIndex root c v
    rw [hrepresentative]

private noncomputable def compositionPartFiberEquiv {N blocks : ℕ} [NeZero N]
    (root : Fin N) (c : IndexedComposition N blocks) (j : Fin blocks) :
    Fin (c.block j) ≃ {v : Fin N //
      (Quotient.mk'' v : Quotient (compositionCyclePartition root c).toSetoid) =
        Quotient.mk'' (compositionBlockRepresentative root c j)} := by
  let d := linearComposition c
  let j' : Fin d.length := Fin.cast c.blocks_length.symm j
  have hblock : d.blocksFun j' = c.block j := rfl
  let f : Fin (c.block j) → {v : Fin N //
      (Quotient.mk'' v : Quotient (compositionCyclePartition root c).toSetoid) =
        Quotient.mk'' (compositionBlockRepresentative root c j)} := fun k =>
    ⟨rootSuccessorRotation N root (d.embedding j' (Fin.cast hblock.symm k)), by
      apply Quotient.sound
      change d.index ((rootSuccessorRotation N root).symm
          (rootSuccessorRotation N root (d.embedding j' (Fin.cast hblock.symm k)))) =
        d.index ((rootSuccessorRotation N root).symm
          (compositionBlockRepresentative root c j))
      simp only [Equiv.symm_apply_apply]
      rw [d.index_embedding]
      simp only [compositionBlockRepresentative, Equiv.symm_apply_apply]
      rw [d.index_embedding]⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hrot := (rootSuccessorRotation N root).injective (congrArg Subtype.val hab)
    have hk := (d.embedding j').injective hrot
    exact Fin.ext (congrArg Fin.val hk)
  · rintro ⟨v, hv⟩
    have hrel := @Quotient.exact _ (compositionCyclePartition root c).toSetoid _ _ hv
    change d.index ((rootSuccessorRotation N root).symm v) =
      d.index ((rootSuccessorRotation N root).symm
        (compositionBlockRepresentative root c j)) at hrel
    have hindex : d.index ((rootSuccessorRotation N root).symm v) = j' := by
      rw [hrel]
      simp only [compositionBlockRepresentative, Equiv.symm_apply_apply]
      rw [d.index_embedding]
    have hrange : (rootSuccessorRotation N root).symm v ∈ Set.range (d.embedding j') := by
      rw [d.mem_range_embedding_iff']
      exact hindex.symm
    obtain ⟨k, hk⟩ := hrange
    refine ⟨Fin.cast hblock k, ?_⟩
    apply Subtype.ext
    dsimp [f]
    calc
      rootSuccessorRotation N root (d.embedding j' k) =
          rootSuccessorRotation N root ((rootSuccessorRotation N root).symm v) :=
        congrArg (rootSuccessorRotation N root) hk
      _ = v := (rootSuccessorRotation N root).apply_symm_apply v

private theorem compositionCyclePartition_eq_marked {N blocks : ℕ} [NeZero N]
    (hN : 3 ≤ N) (hblocks : 2 ≤ blocks) (P : MarkedConnectedCyclePartition N blocks) :
    let data := markedCyclePartitionCompositionEquiv N blocks hN hblocks P
    compositionCyclePartition data.1 data.2 = P.partition := by
  let data := markedCyclePartitionCompositionEquiv N blocks hN hblocks P
  let root := data.1
  let c := data.2
  let R := markedPartitionCutEquiv N blocks hN hblocks P
  let s := (rootedCycleCutSetEquiv N blocks (by omega) R).2
  have hs := congrArg Subtype.val
    ((fixedLengthCompositionEquiv N blocks (by omega) (by omega)).apply_symm_apply s)
  have hc : linearComposition c =
      ((fixedLengthCompositionEquiv N blocks (by omega) (by omega)).symm s).1 := rfl
  change compositionAsSetEquiv N
    (((fixedLengthCompositionEquiv N blocks (by omega) (by omega)).symm s).1.toCompositionAsSet) =
      s.1 at hs
  have hinternal :
      compositionAsSetEquiv N (linearComposition c).toCompositionAsSet =
        internalCuts root (cycleBoundaryCuts P.partition) := by
    rw [hc]
    exact hs
  have hroot : root = P.root := rfl
  have hrootComposition : root ∈ cycleBoundaryCuts (compositionCyclePartition root c) := by
    simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
    change (linearComposition c).index ((rootSuccessorRotation N root).symm root) ≠
      (linearComposition c).index ((rootSuccessorRotation N root).symm (root + 1))
    have hrootCoordinate :
        (rootSuccessorRotation N root).symm root = (⟨N - 1, by omega⟩ : Fin N) := by
      apply (rootSuccessorRotation N root).injective
      rw [(rootSuccessorRotation N root).apply_symm_apply]
      change root = finRotate N (⟨N - 1, by omega⟩ : Fin N) + root
      have hrotate : finRotate N (⟨N - 1, by omega⟩ : Fin N) = 0 := by
        rw [finRotate_apply]
        apply Fin.ext
        simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega),
          Nat.sub_add_cancel (by omega : 1 ≤ N)]
      simp [hrotate]
    have hsuccessorCoordinate :
        (rootSuccessorRotation N root).symm (root + 1) = 0 := by
      apply (rootSuccessorRotation N root).injective
      rw [(rootSuccessorRotation N root).apply_symm_apply]
      simp [rootSuccessorRotation, finRotate_apply, add_comm]
    rw [hrootCoordinate, hsuccessorCoordinate]
    let d := linearComposition c
    have hdlen : d.length = blocks := c.blocks_length
    let last : Fin N := ⟨N - 1, by omega⟩
    have hzeroVal : (d.index 0).val = 0 := by
      have hlow := d.sizeUpTo_index_le (0 : Fin N)
      change d.sizeUpTo (d.index (0 : Fin N)).val ≤ 0 at hlow
      have hsize : d.sizeUpTo (d.index 0).val = 0 := by omega
      by_contra h
      have hpos : 0 < (d.index 0).val := Nat.pos_of_ne_zero h
      let k : Fin d.length := ⟨(d.index 0).val - 1, by omega⟩
      have hstrict := d.sizeUpTo_strict_mono k.isLt
      have hsucc : k.val + 1 = (d.index 0).val := by dsimp [k]; omega
      rw [hsucc, hsize] at hstrict
      omega
    intro heq
    have hlastVal : (d.index last).val = 0 := by
      rw [heq]
      exact hzeroVal
    have hhigh := d.lt_sizeUpTo_index_succ last
    change N - 1 < d.sizeUpTo ((d.index last).val + 1) at hhigh
    rw [hlastVal] at hhigh
    let one : Fin d.length := ⟨1, by omega⟩
    have hstrict := d.sizeUpTo_strict_mono one.isLt
    have hmono := d.monotone_sizeUpTo (show 2 ≤ d.length by omega)
    rw [d.sizeUpTo_length] at hmono
    dsimp [last, one] at hhigh hstrict
    omega
  have hcuts : cycleBoundaryCuts (compositionCyclePartition root c) =
      cycleBoundaryCuts P.partition := by
    calc
      cycleBoundaryCuts (compositionCyclePartition root c) =
          rootedCutsOfInternal root
            (internalCuts root (cycleBoundaryCuts (compositionCyclePartition root c))) :=
        (rootedCutsOfInternal_internalCuts root _ hrootComposition).symm
      _ = rootedCutsOfInternal root
          (compositionAsSetEquiv N (linearComposition c).toCompositionAsSet) := by
        rw [internalCuts_compositionCyclePartition hN]
      _ = rootedCutsOfInternal root (internalCuts root (cycleBoundaryCuts P.partition)) := by
        rw [hinternal]
      _ = cycleBoundaryCuts P.partition := by
        apply rootedCutsOfInternal_internalCuts
        rw [hroot]
        exact P.root_mem
  have hcompositionCuts : 2 ≤
      (cycleBoundaryCuts (compositionCyclePartition root c)).card := by
    rw [hcuts, P.boundary_card]
    exact hblocks
  have hpartition : compositionCyclePartition root c = P.partition := by
    have hsubtype :
        (⟨compositionCyclePartition root c, hcompositionCuts⟩ :
            {Q : ConnectedCyclePartition N // 2 ≤ (cycleBoundaryCuts Q).card}) =
          ⟨P.partition, by rw [P.boundary_card]; exact hblocks⟩ := by
      apply (connectedCyclePartitionCutsEquiv N hN).injective
      apply Subtype.ext
      exact hcuts
    exact congrArg Subtype.val hsubtype
  exact hpartition

private noncomputable def markedCompositionPartFiberEquiv {N blocks : ℕ} [NeZero N]
    (hN : 3 ≤ N) (hblocks : 2 ≤ blocks) (P : MarkedConnectedCyclePartition N blocks)
    (j : Fin blocks) :
    let data := markedCyclePartitionCompositionEquiv N blocks hN hblocks P
    Fin (data.2.block j) ≃ {v : Fin N //
      (Quotient.mk'' v : Quotient P.partition.toSetoid) =
        Quotient.mk'' (compositionBlockRepresentative data.1 data.2 j)} := by
  let data := markedCyclePartitionCompositionEquiv N blocks hN hblocks P
  change Fin (data.2.block j) ≃ {v : Fin N //
    (Quotient.mk'' v : Quotient P.partition.toSetoid) =
      Quotient.mk'' (compositionBlockRepresentative data.1 data.2 j)}
  rw [← compositionCyclePartition_eq_marked hN hblocks P]
  exact compositionPartFiberEquiv data.1 data.2 j

private noncomputable def actualOddCycleBlocks {N : ℕ} (P : ConnectedCyclePartition N) :
    Finset (Quotient P.toSetoid) := by
  classical
  exact (Finset.univ.image fun v : Fin N =>
    (Quotient.mk'' v : Quotient P.toSetoid)).filter fun C =>
      Odd (Set.ncard {v : Fin N | (Quotient.mk'' v : Quotient P.toSetoid) = C})

private noncomputable def markedPrescribedOddCompositionEquiv
    (N blocks oddCount : ℕ) [NeZero N] (hN : 3 ≤ N) (hblocks : 2 ≤ blocks) :
    {P : MarkedConnectedCyclePartition N blocks //
        (actualOddCycleBlocks P.partition).card = oddCount} ≃
      Fin N × PrescribedOddComposition N blocks oddCount := by
  classical
  let base := markedCyclePartitionCompositionEquiv N blocks hN hblocks
  let restricted :
      {P : MarkedConnectedCyclePartition N blocks //
          (actualOddCycleBlocks P.partition).card = oddCount} ≃
        {data : Fin N × IndexedComposition N blocks //
          (oddSupport data.2).card = oddCount} := by
    apply base.subtypeEquiv
    intro P
    let data := base P
    let root := data.1
    let c := data.2
    have hpartition : compositionCyclePartition root c = P.partition :=
      compositionCyclePartition_eq_marked hN hblocks P
    let e := compositionBlockQuotientEquiv root c
    have heval (j : Fin blocks) :
        e j = Quotient.mk'' (compositionBlockRepresentative root c j) := rfl
    have hfiber (j : Fin blocks) :
        Set.ncard {v : Fin N |
          (Quotient.mk'' v : Quotient (compositionCyclePartition root c).toSetoid) = e j} =
            c.block j := by
      rw [heval]
      rw [hpartition]
      have hcard := Set.ncard_congr'
        ((Equiv.Set.univ (Fin (c.block j))).trans
          (markedCompositionPartFiberEquiv hN hblocks P j))
      calc
        Set.ncard {v : Fin N |
            (Quotient.mk'' v : Quotient P.partition.toSetoid) =
              Quotient.mk'' (compositionBlockRepresentative root c j)} =
            Set.ncard (Set.univ : Set (Fin (c.block j))) := hcard.symm
        _ = c.block j := by simp only [Set.ncard_univ, Nat.card_fin]
    have hodd (j : Fin blocks) :
        j ∈ oddSupport c ↔
          Odd (Set.ncard {v : Fin N |
            (Quotient.mk'' v : Quotient (compositionCyclePartition root c).toSetoid) = e j}) := by
      simp only [oddSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfiber]
    have hfinset : e.finsetCongr (oddSupport c) =
        actualOddCycleBlocks (compositionCyclePartition root c) := by
      ext C
      simp only [Equiv.finsetCongr_apply, actualOddCycleBlocks, Finset.mem_filter]
      constructor
      · intro hC
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hC
        refine ⟨Finset.mem_image.mpr ⟨compositionBlockRepresentative root c j,
          Finset.mem_univ _, rfl⟩, (hodd j).mp hj⟩
      · rintro ⟨_, hC⟩
        refine Finset.mem_map.mpr ⟨e.symm C, ?_, e.apply_symm_apply C⟩
        apply (hodd (e.symm C)).mpr
        simpa only [e.apply_symm_apply] using hC
    have hcard : (actualOddCycleBlocks P.partition).card = (oddSupport c).card := by
      rw [← hpartition]
      calc
        (actualOddCycleBlocks (compositionCyclePartition root c)).card =
            (e.finsetCongr (oddSupport c)).card := congrArg Finset.card hfinset.symm
        _ = (oddSupport c).card := by
          simp only [Equiv.finsetCongr_apply, Finset.card_map]
    change (actualOddCycleBlocks P.partition).card = oddCount ↔
      (oddSupport data.2).card = oddCount
    rw [hcard]
  exact restricted.trans
    { toFun := fun data => (data.1.1, ⟨data.1.2, data.2⟩)
      invFun := fun data => ⟨(data.1, data.2.1), data.2.2⟩
      left_inv := by intro data; rfl
      right_inv := by intro data; rfl }

private abbrev PrescribedOddConnectedCyclePartition
    (N blocks oddCount : ℕ) [NeZero N] :=
  {P : ConnectedCyclePartition N //
    (cycleBoundaryCuts P).card = blocks ∧ (actualOddCycleBlocks P).card = oddCount}

private theorem card_prescribedOddConnectedCyclePartition_identity
    (n i m : ℕ) [NeZero (2 * n)] (hn : 2 ≤ n) (hi : 2 ≤ i) :
    i * Nat.card (PrescribedOddConnectedCyclePartition (2 * n) i (2 * m)) =
      2 * n * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) := by
  classical
  let A := PrescribedOddConnectedCyclePartition (2 * n) i (2 * m)
  let toCuts : A → Finset (Fin (2 * n)) := fun P => cycleBoundaryCuts P.1
  have toCuts_injective : Function.Injective toCuts := by
    intro P Q hcuts
    have hP : 2 ≤ (cycleBoundaryCuts P.1).card := by rw [P.2.1]; exact hi
    have hQ : 2 ≤ (cycleBoundaryCuts Q.1).card := by rw [Q.2.1]; exact hi
    have hsubtype :
        (⟨P.1, hP⟩ : {R : ConnectedCyclePartition (2 * n) //
          2 ≤ (cycleBoundaryCuts R).card}) = ⟨Q.1, hQ⟩ := by
      apply (connectedCyclePartitionCutsEquiv (2 * n) (by omega)).injective
      apply Subtype.ext
      exact hcuts
    apply Subtype.ext
    exact congrArg (fun X : {R : ConnectedCyclePartition (2 * n) //
      2 ≤ (cycleBoundaryCuts R).card} => X.1) hsubtype
  letI : Fintype A := Fintype.ofInjective toCuts toCuts_injective
  let M := {P : MarkedConnectedCyclePartition (2 * n) i //
    (actualOddCycleBlocks P.partition).card = 2 * m}
  let markedCompositionEquiv :=
    markedPrescribedOddCompositionEquiv (2 * n) i (2 * m) (by omega) hi
  letI : Fintype M := Fintype.ofEquiv
    (Fin (2 * n) × PrescribedOddComposition (2 * n) i (2 * m))
      markedCompositionEquiv.symm
  let markedSigma : M ≃ Σ P : A, {root : Fin (2 * n) //
      root ∈ cycleBoundaryCuts P.1} :=
    { toFun := fun P =>
        ⟨⟨P.1.partition, P.1.boundary_card, P.2⟩, ⟨P.1.root, P.1.root_mem⟩⟩
      invFun := fun data =>
        ⟨{ partition := data.1.1
           root := data.2.1
           root_mem := data.2.2
           boundary_card := data.1.2.1 }, data.1.2.2⟩
      left_inv := by intro P; cases P; rfl
      right_inv := by intro data; cases data; rfl }
  have hmarkedUnmarked : Fintype.card M = i * Fintype.card A := by
    rw [Fintype.card_congr markedSigma, Fintype.card_sigma]
    calc
      ∑ P : A, Fintype.card {root : Fin (2 * n) //
          root ∈ cycleBoundaryCuts P.1} = ∑ _P : A, i := by
        apply Finset.sum_congr rfl
        intro P _
        rw [Fintype.card_coe, P.2.1]
      _ = Fintype.card A * i := by simp
      _ = i * Fintype.card A := Nat.mul_comm _ _
  have hmarkedComposition :
      Fintype.card M =
        2 * n * (Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1)) := by
    rw [Fintype.card_congr markedCompositionEquiv, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_congr (parityEvenizationEquiv n i m), Fintype.card_prod,
      Fintype.card_finset_len, Fintype.card_fin,
      Fintype.card_congr (IndexedComposition.compositionEquiv (n + m) i),
      Fintype.card_congr (fixedLengthCompositionEquiv (n + m) i (by omega) (by omega)),
      Fintype.card_finset_len, Fintype.card_fin]
  rw [hmarkedUnmarked] at hmarkedComposition
  change i * Nat.card A = _
  rw [Nat.card_eq_fintype_card]
  calc
    i * Fintype.card A =
        2 * n * (Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1)) :=
      hmarkedComposition
    _ = 2 * n * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) := by
      simp only [Nat.mul_assoc]

private theorem actualOddCycleBlocks_card_even (n : ℕ) [NeZero (2 * n)]
    (P : ConnectedCyclePartition (2 * n)) :
    Even (actualOddCycleBlocks P).card := by
  classical
  have himage :
      Finset.univ.image (fun v : Fin (2 * n) =>
        (Quotient.mk'' v : Quotient P.toSetoid)) = Finset.univ := by
    ext C
    refine Quotient.inductionOn C ?_
    intro v
    simp
  have hfiber (C : Quotient P.toSetoid) :
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} =
        (Finset.univ.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext v
    simp
  have hsum :
      (∑ C : Quotient P.toSetoid,
          Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C}) = 2 * n := by
    simp_rw [hfiber]
    symm
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ)
      (f := fun v : Fin (2 * n) => (Quotient.mk'' v : Quotient P.toSetoid)) (by simp))
  unfold actualOddCycleBlocks
  rw [himage]
  apply (Finset.even_sum_iff_even_card_odd
    (s := Finset.univ)
    (fun C : Quotient P.toSetoid =>
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C})).mp
  simpa [hsum]

private theorem quotient_card_eq_boundaryCuts_card {N : ℕ} [NeZero N]
    (hN : 3 ≤ N) (P : ConnectedCyclePartition N)
    (hcuts : 2 ≤ (cycleBoundaryCuts P).card) :
    Nat.card (Quotient P.toSetoid) = (cycleBoundaryCuts P).card := by
  classical
  obtain ⟨root, hroot⟩ := Finset.card_pos.mp (by omega : 0 < (cycleBoundaryCuts P).card)
  let M : MarkedConnectedCyclePartition N (cycleBoundaryCuts P).card :=
    { partition := P
      root := root
      root_mem := hroot
      boundary_card := rfl }
  let data := markedCyclePartitionCompositionEquiv N (cycleBoundaryCuts P).card hN hcuts M
  have hpartition : compositionCyclePartition data.1 data.2 = P :=
    compositionCyclePartition_eq_marked hN hcuts M
  calc
    Nat.card (Quotient P.toSetoid) =
        Nat.card (Quotient (compositionCyclePartition data.1 data.2).toSetoid) := by
      rw [hpartition]
    _ = Nat.card (Fin (cycleBoundaryCuts P).card) :=
      Nat.card_congr (compositionBlockQuotientEquiv data.1 data.2).symm
    _ = (cycleBoundaryCuts P).card := Nat.card_fin _

private abbrev CompatibleConnectedCyclePartition (n blocks : ℕ) [NeZero (2 * n)] :=
  {P : ConnectedCyclePartition (2 * n) //
    (cycleBoundaryCuts P).card = blocks ∧ crownCycleCompatible P}

private noncomputable def compatibleConnectedCyclePartitionProfileEquiv
    (n i : ℕ) [NeZero (2 * n)] (hn : 2 ≤ n) (hi : 2 ≤ i) :
    CompatibleConnectedCyclePartition n i ≃
      Σ m : {m : ℕ // m ∈ Finset.Icc 1 (i / 2)},
        PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1) where
  toFun P := by
    classical
    have hnontrivial : ∃ u v, ¬ P.1.toSetoid.r u v := by
      by_contra h
      push Not at h
      have hempty := (cycleBoundaryCuts_eq_empty_iff (by omega) P.1).mpr h
      have : (cycleBoundaryCuts P.1).card = 0 := by rw [hempty]; simp
      omega
    have heven := actualOddCycleBlocks_card_even n P.1
    let m := (actualOddCycleBlocks P.1).card / 2
    have htwice : 2 * m = (actualOddCycleBlocks P.1).card := by
      exact Nat.two_mul_div_two_of_even heven
    let C := ((crownCycleCompatible_iff_exists_oddBlock hn P.1 hnontrivial).mp
      P.2.2).choose
    have hC : Set.ncard {v : Fin (2 * n) |
        (Quotient.mk'' v : Quotient P.1.toSetoid) = C} % 2 = 1 :=
      ((crownCycleCompatible_iff_exists_oddBlock hn P.1 hnontrivial).mp
        P.2.2).choose_spec
    have hCmem : C ∈ actualOddCycleBlocks P.1 := by
      revert hC
      refine Quotient.inductionOn C ?_
      intro v hv
      unfold actualOddCycleBlocks
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
        Nat.odd_iff.mpr hv⟩
    have hmpos : 1 ≤ m := by
      have := Finset.card_pos.mpr ⟨C, hCmem⟩
      omega
    have hoddLe : (actualOddCycleBlocks P.1).card ≤
        Nat.card (Quotient P.1.toSetoid) := by
      rw [Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    rw [quotient_card_eq_boundaryCuts_card (by omega) P.1 (by rw [P.2.1]; exact hi),
      P.2.1] at hoddLe
    have hmle : m ≤ i / 2 := by omega
    exact ⟨⟨m, Finset.mem_Icc.mpr ⟨hmpos, hmle⟩⟩,
      ⟨P.1, P.2.1, htwice.symm⟩⟩
  invFun data := by
    classical
    let P := data.2
    have hnontrivial : ∃ u v, ¬ P.1.toSetoid.r u v := by
      by_contra h
      push Not at h
      have hempty := (cycleBoundaryCuts_eq_empty_iff (by omega) P.1).mpr h
      have : (cycleBoundaryCuts P.1).card = 0 := by rw [hempty]; simp
      omega
    have hpos : 0 < (actualOddCycleBlocks P.1).card := by
      rw [P.2.2]
      have hmpos := (Finset.mem_Icc.mp data.1.2).1
      omega
    let C := (Finset.card_pos.mp hpos).choose
    have hCmem : C ∈ actualOddCycleBlocks P.1 :=
      (Finset.card_pos.mp hpos).choose_spec
    have hodd : Odd (Set.ncard {v : Fin (2 * n) |
        (Quotient.mk'' v : Quotient P.1.toSetoid) = C}) := by
      unfold actualOddCycleBlocks at hCmem
      exact (Finset.mem_filter.mp hCmem).2
    have hcompatible : crownCycleCompatible P.1 :=
      (crownCycleCompatible_iff_exists_oddBlock hn P.1 hnontrivial).mpr
        ⟨C, Nat.odd_iff.mp hodd⟩
    exact ⟨P.1, P.2.1, hcompatible⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv data := by
    rcases data with ⟨m, P⟩
    apply Sigma.ext
    · apply Subtype.ext
      dsimp
      rw [P.2.2]
      simp
    · simp +contextual [Subtype.heq_iff_coe_eq, P.2.2]

private theorem card_compatibleConnectedCyclePartition_eq_profile_sum
    (n i : ℕ) [NeZero (2 * n)] (hn : 2 ≤ n) (hi : 2 ≤ i) :
    Nat.card (CompatibleConnectedCyclePartition n i) =
      ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (i / 2)},
        Nat.card (PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1)) := by
  classical
  let I := {m : ℕ // m ∈ Finset.Icc 1 (i / 2)}
  letI : Fintype I := Fintype.ofFinset (Finset.Icc 1 (i / 2)) (fun _ => Iff.rfl)
  letI (m : I) : Finite
      (PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1)) := by
    let toCuts : PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1) →
        Finset (Fin (2 * n)) := fun P => cycleBoundaryCuts P.1
    apply Finite.of_injective toCuts
    intro P Q hcuts
    have hP : 2 ≤ (cycleBoundaryCuts P.1).card := by rw [P.2.1]; exact hi
    have hQ : 2 ≤ (cycleBoundaryCuts Q.1).card := by rw [Q.2.1]; exact hi
    have hsubtype :
        (⟨P.1, hP⟩ : {R : ConnectedCyclePartition (2 * n) //
          2 ≤ (cycleBoundaryCuts R).card}) = ⟨Q.1, hQ⟩ := by
      apply (connectedCyclePartitionCutsEquiv (2 * n) (by omega)).injective
      exact Subtype.ext hcuts
    have hval : P.1 = Q.1 := congrArg
      (fun X : {R : ConnectedCyclePartition (2 * n) //
        2 ≤ (cycleBoundaryCuts R).card} => X.1) hsubtype
    exact Subtype.ext hval
  calc
    Nat.card (CompatibleConnectedCyclePartition n i) =
        Nat.card (Σ m : I,
          PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1)) :=
      Nat.card_congr (compatibleConnectedCyclePartitionProfileEquiv n i hn hi)
    _ = ∑ m : I,
        Nat.card (PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1)) :=
      by simpa only using (Nat.card_sigma (α := I)
        (β := fun m : I => PrescribedOddConnectedCyclePartition (2 * n) i (2 * m.1)))

private theorem card_compatibleConnectedCyclePartition_identity
    (n i : ℕ) [NeZero (2 * n)] (hn : 2 ≤ n) (hi : 2 ≤ i) :
    i * Nat.card (CompatibleConnectedCyclePartition n i) =
      ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (i / 2)},
        2 * n * Nat.choose i (2 * m.1) * Nat.choose (n + m.1 - 1) (i - 1) := by
  rw [card_compatibleConnectedCyclePartition_eq_profile_sum n i hn hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact card_prescribedOddConnectedCyclePartition_identity n i m.1 hn hi

#print axioms card_compatibleConnectedCyclePartition_identity

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
