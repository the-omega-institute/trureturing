/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeCCP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytope,
     mathlib/module/Mathlib/Order/Extension/Linear]
   utility: none
   digest: Crown exposed faces and connected compatible partitions are inverse constructions. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytope
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Extension.Linear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytope

open scoped BigOperators

/-- The blocks cut out by the tight comparable-pair graph of an actual crown face. -/
abbrev CrownFaceBlock {n : ℕ} (F : CrownExposedFace n) :=
  (crownFaceTightGraph F).ConnectedComponent

/-- A block precedes another when some augmented crown comparison crosses between them. -/
def crownFaceBlockRel {n : ℕ} (F : CrownExposedFace n)
    (C D : CrownFaceBlock F) : Prop :=
  ∃ u v : CrownAugmentedVertex n,
    (crownFaceTightGraph F).connectedComponentMk u = C ∧
      (crownFaceTightGraph F).connectedComponentMk v = D ∧ crownAugmentedLE u v

/-- The quotient order candidate on tight blocks is the reflexive transitive closure of the
    comparisons crossing between blocks. -/
def crownFaceBlockLE {n : ℕ} (F : CrownExposedFace n) :
    CrownFaceBlock F → CrownFaceBlock F → Prop :=
  Relation.ReflTransGen (crownFaceBlockRel F)

private theorem augmentedCoordinate_le_of_faceBlockRel {n : ℕ} (F : CrownExposedFace n)
    {C D : CrownFaceBlock F} (hCD : crownFaceBlockRel F C D)
    {a b : CrownAugmentedVertex n}
    (ha : (crownFaceTightGraph F).connectedComponentMk a = C)
    (hb : (crownFaceTightGraph F).connectedComponentMk b = D)
    {x : Fin (2 * n) → ℝ} (hx : x ∈ F.1) :
    augmentedCoordinate x a ≤ augmentedCoordinate x b := by
  obtain ⟨u, v, hu, hv, huv⟩ := hCD
  have hau : augmentedCoordinate x a = augmentedCoordinate x u :=
    augmentedCoordinate_eq_of_tightComponent F (ha.trans hu.symm) hx
  have hbv : augmentedCoordinate x b = augmentedCoordinate x v :=
    augmentedCoordinate_eq_of_tightComponent F (hb.trans hv.symm) hx
  rw [hau, hbv]
  exact augmentedCoordinate_mono (F.2.subset hx) huv

private theorem augmentedCoordinate_le_of_faceBlockLE {n : ℕ} (F : CrownExposedFace n)
    {C D : CrownFaceBlock F} (hCD : crownFaceBlockLE F C D)
    {a b : CrownAugmentedVertex n}
    (ha : (crownFaceTightGraph F).connectedComponentMk a = C)
    (hb : (crownFaceTightGraph F).connectedComponentMk b = D)
    {x : Fin (2 * n) → ℝ} (hx : x ∈ F.1) :
    augmentedCoordinate x a ≤ augmentedCoordinate x b := by
  induction hCD generalizing a b with
  | refl =>
      exact le_of_eq (augmentedCoordinate_eq_of_tightComponent F (ha.trans hb.symm) hx)
  | @tail E D hCE hED ih =>
      obtain ⟨e, he⟩ := Quot.exists_rep E
      exact (ih ha he).trans (augmentedCoordinate_le_of_faceBlockRel F hED he hb hx)

private theorem faceBlockRel_eq_of_reverse {n : ℕ} (F : CrownExposedFace n)
    {C D : CrownFaceBlock F} (hCD : crownFaceBlockRel F C D)
    (hDC : crownFaceBlockLE F D C) : C = D := by
  obtain ⟨u, v, hu, hv, huv⟩ := hCD
  by_cases huv_eq : u = v
  · subst v
    exact hu.symm.trans hv
  have heq : ∀ x, x ∈ F.1 → augmentedCoordinate x u = augmentedCoordinate x v := by
    intro x hx
    apply le_antisymm
    · exact augmentedCoordinate_mono (F.2.subset hx) huv
    · exact augmentedCoordinate_le_of_faceBlockLE F hDC hv hu hx
  have hadj : (crownFaceTightGraph F).Adj u v := by
    rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
    exact ⟨huv_eq, Or.inl ⟨huv, heq⟩⟩
  exact hu.symm.trans <|
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv

/-- For every actual face, directed cycles in the quotient block relation collapse to
    one tight component.  Thus the reflexive transitive quotient relation is antisymmetric. -/
theorem crownFaceBlockLE_antisymm {n : ℕ} (F : CrownExposedFace n) :
    ∀ {C D : CrownFaceBlock F}, crownFaceBlockLE F C D →
      crownFaceBlockLE F D C → C = D := by
  intro C D hCD hDC
  induction hCD with
  | refl => rfl
  | @tail E D hCE hED ih =>
      have hEC : crownFaceBlockLE F E C :=
        (Relation.ReflTransGen.single hED).trans hDC
      have hCE_eq : C = E := ih hEC
      subst E
      exact faceBlockRel_eq_of_reverse F hED hDC

/-- An actual crown face has a finite partial order of tight connected blocks. -/
noncomputable def crownFaceBlockPartialOrder {n : ℕ} (F : CrownExposedFace n) :
    PartialOrder (CrownFaceBlock F) where
  le := crownFaceBlockLE F
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := crownFaceBlockLE_antisymm F

/-- The graph of comparable pairs that lie in the same block of a partition. -/
def crownPartitionGraph {n : ℕ} (s : Setoid (CrownAugmentedVertex n)) :
    SimpleGraph (CrownAugmentedVertex n) :=
  SimpleGraph.fromRel fun u v => s.r u v ∧ crownAugmentedLE u v

/-- The directed relation induced between the quotient blocks of an augmented-crown partition. -/
def crownPartitionBlockRel {n : ℕ} (s : Setoid (CrownAugmentedVertex n))
    (C D : Quotient s) : Prop :=
  ∃ u v : CrownAugmentedVertex n,
    Quotient.mk'' u = C ∧ Quotient.mk'' v = D ∧ crownAugmentedLE u v

/-- Reachability in the directed quotient relation of an augmented-crown partition. -/
def crownPartitionBlockLE {n : ℕ} (s : Setoid (CrownAugmentedVertex n)) :
    Quotient s → Quotient s → Prop :=
  Relation.ReflTransGen (crownPartitionBlockRel s)

/-- A source-specific connected compatible partition of the augmented crown.  Connectedness says
    that each equivalence class is generated by comparable pairs internal to that class;
    compatibility says that the induced directed quotient relation has no nontrivial cycle. -/
structure CrownConnectedCompatiblePartition (n : ℕ) where
  toSetoid : Setoid (CrownAugmentedVertex n)
  connected : ∀ u v, toSetoid.r u v ↔ (crownPartitionGraph toSetoid).Reachable u v
  compatible : ∀ {C D : Quotient toSetoid}, crownPartitionBlockLE toSetoid C D →
    crownPartitionBlockLE toSetoid D C → C = D

/-- Compatibility equips the finite quotient blocks of a CCP with their induced partial order. -/
noncomputable def CrownConnectedCompatiblePartition.blockPartialOrder {n : ℕ}
    (P : CrownConnectedCompatiblePartition n) : PartialOrder (Quotient P.toSetoid) where
  le := crownPartitionBlockLE P.toSetoid
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := P.compatible

private def crownFaceSetoid {n : ℕ} (F : CrownExposedFace n) :
    Setoid (CrownAugmentedVertex n) :=
  (crownFaceTightGraph F).reachableSetoid

private theorem crownFace_partitionGraph_reachable {n : ℕ} (F : CrownExposedFace n)
    (u v : CrownAugmentedVertex n) :
    (crownPartitionGraph (crownFaceSetoid F)).Reachable u v ↔
      (crownFaceTightGraph F).Reachable u v := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | @cons a b c hab p ih =>
        have hab' : (crownFaceTightGraph F).Reachable a b := by
          rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
          · exact h.1
          · exact h.1.symm
        exact hab'.trans ih
  · intro huv
    apply huv.mono
    intro a b hab
    rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
    rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl ⟨hab.reachable, h.1⟩⟩
    · exact ⟨hne, Or.inr ⟨hab.reachable.symm, h.1⟩⟩

/-- Every actual crown exposed face determines a connected compatible partition: its blocks are
    exactly the connected components of the tight comparable-pair graph. -/
noncomputable def crownFacePartition {n : ℕ} (F : CrownExposedFace n) :
    CrownConnectedCompatiblePartition n where
  toSetoid := crownFaceSetoid F
  connected u v := (crownFace_partitionGraph_reachable F u v).symm
  compatible := by
    intro C D hCD hDC
    exact crownFaceBlockLE_antisymm F hCD hDC

/-- The quotient block containing the augmented bottom vertex. -/
def crownPartitionBottomBlock {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Quotient P.toSetoid :=
  Quotient.mk'' CrownAugmentedVertex.bottom

/-- The quotient block containing the augmented top vertex. -/
def crownPartitionTopBlock {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Quotient P.toSetoid :=
  Quotient.mk'' CrownAugmentedVertex.top

private theorem crownPartition_bottom_le {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (C : Quotient P.toSetoid) :
    crownPartitionBlockLE P.toSetoid (crownPartitionBottomBlock P) C := by
  refine Quotient.inductionOn C ?_
  intro v
  apply Relation.ReflTransGen.single
  exact ⟨.bottom, v, rfl, rfl, by simp [crownAugmentedLE]⟩

private theorem crownPartition_le_top {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (C : Quotient P.toSetoid) :
    crownPartitionBlockLE P.toSetoid C (crownPartitionTopBlock P) := by
  refine Quotient.inductionOn C ?_
  intro v
  apply Relation.ReflTransGen.single
  refine ⟨v, .top, rfl, rfl, ?_⟩
  cases v <;> simp [crownAugmentedLE]

private def linearExtensionFintype (α : Type*) [Fintype α] : Fintype (LinearExtension α) :=
  Fintype.ofEquiv α
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The strict integer rank of a block in a fixed linear extension of the finite quotient order. -/
noncomputable def crownPartitionBlockRank {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (C : Quotient P.toSetoid) : ℕ := by
  letI := P.blockPartialOrder
  letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
  letI : Fintype (LinearExtension (Quotient P.toSetoid)) := linearExtensionFintype _
  exact ((monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl).symm
    (toLinearExtension C)).val

private theorem crownPartitionBlockRank_mono {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    {C D : Quotient P.toSetoid} (hCD : crownPartitionBlockLE P.toSetoid C D) :
    crownPartitionBlockRank P C ≤ crownPartitionBlockRank P D := by
  letI := P.blockPartialOrder
  letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
  letI : Fintype (LinearExtension (Quotient P.toSetoid)) := linearExtensionFintype _
  let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
  have hlinear : toLinearExtension C ≤ toLinearExtension D := toLinearExtension.monotone hCD
  have hfin : e.symm (toLinearExtension C) ≤ e.symm (toLinearExtension D) :=
    e.symm.monotone hlinear
  change (e.symm (toLinearExtension C)).val ≤ (e.symm (toLinearExtension D)).val
  exact hfin

private theorem crownPartitionBlockRank_injective {n : ℕ}
    (P : CrownConnectedCompatiblePartition n) :
    Function.Injective (crownPartitionBlockRank P) := by
  intro C D h
  letI := P.blockPartialOrder
  letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
  letI : Fintype (LinearExtension (Quotient P.toSetoid)) := linearExtensionFintype _
  let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
  have hfin : e.symm (toLinearExtension C) = e.symm (toLinearExtension D) := by
    apply Fin.ext
    simpa only [crownPartitionBlockRank] using h
  exact e.symm.injective hfin

/-- Normalize linear-extension ranks so that the bottom and top blocks have coordinates zero and
    one.  It is used only when those endpoint blocks are distinct. -/
noncomputable def crownPartitionRankPoint {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Fin (2 * n) → ℝ := fun i =>
  ((crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) -
      crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
    ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
      crownPartitionBlockRank P (crownPartitionBottomBlock P))

private theorem crownPartition_rank_denominator_pos {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
    (0 : ℝ) < (crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
      crownPartitionBlockRank P (crownPartitionBottomBlock P) := by
  have hle := crownPartitionBlockRank_mono P
    (crownPartition_bottom_le P (crownPartitionTopBlock P))
  have hne : crownPartitionBlockRank P (crownPartitionBottomBlock P) ≠
      crownPartitionBlockRank P (crownPartitionTopBlock P) :=
    fun h => hendpoints (crownPartitionBlockRank_injective P h)
  have hlt := lt_of_le_of_ne hle hne
  have hltR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) <
      crownPartitionBlockRank P (crownPartitionTopBlock P) := by
    exact_mod_cast hlt
  linarith

private theorem crownPartition_block_le_of_augmentedLE {n : ℕ}
    (P : CrownConnectedCompatiblePartition n) {u v : CrownAugmentedVertex n}
    (huv : crownAugmentedLE u v) :
    crownPartitionBlockLE P.toSetoid (Quotient.mk'' u) (Quotient.mk'' v) :=
  Relation.ReflTransGen.single ⟨u, v, rfl, rfl, huv⟩

/-- The normalized linear-extension rank point is an actual point of the crown order polytope
    whenever the endpoint blocks are distinct. -/
theorem crownPartitionRankPoint_mem {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P) :
    crownPartitionRankPoint P ∈ crownOrderPolytope n := by
  have hden := crownPartition_rank_denominator_pos P hendpoints
  constructor
  · intro i
    have hbottom := crownPartitionBlockRank_mono P
      (crownPartition_bottom_le P (Quotient.mk'' (.vertex i)))
    have htop := crownPartitionBlockRank_mono P
      (crownPartition_le_top P (Quotient.mk'' (.vertex i)))
    have hbottomR : (crownPartitionBlockRank P (crownPartitionBottomBlock P) : ℝ) ≤
        crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) := by
      exact_mod_cast hbottom
    have htopR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
        crownPartitionBlockRank P (crownPartitionTopBlock P) := by
      exact_mod_cast htop
    constructor
    · apply div_nonneg
      · exact sub_nonneg.mpr hbottomR
      · exact le_of_lt hden
    · apply (div_le_one hden).2
      linarith
  · intro i j hij
    have hmono := crownPartitionBlockRank_mono P
      (crownPartition_block_le_of_augmentedLE P
        (u := CrownAugmentedVertex.vertex i) (v := CrownAugmentedVertex.vertex j) (Or.inr hij))
    have hmonoR : (crownPartitionBlockRank P (Quotient.mk'' (.vertex i)) : ℝ) ≤
        crownPartitionBlockRank P (Quotient.mk'' (.vertex j)) := by
      exact_mod_cast hmono
    apply (div_le_div_iff_of_pos_right hden).2
    linarith

private theorem augmentedCoordinate_crownPartitionRankPoint {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
    (u : CrownAugmentedVertex n) :
    augmentedCoordinate (crownPartitionRankPoint P) u =
      ((crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
        ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P)) := by
  have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
  cases u with
  | bottom => simp [augmentedCoordinate, crownPartitionBottomBlock]
  | vertex i => rfl
  | top =>
      simp only [augmentedCoordinate, crownPartitionTopBlock]
      exact (div_self hden).symm

/-- The normalized rank point has no accidental equality between distinct quotient blocks. -/
theorem augmentedCoordinate_crownPartitionRankPoint_eq_iff {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P ≠ crownPartitionTopBlock P)
    (u v : CrownAugmentedVertex n) :
    augmentedCoordinate (crownPartitionRankPoint P) u =
      augmentedCoordinate (crownPartitionRankPoint P) v ↔ P.toSetoid.r u v := by
  rw [augmentedCoordinate_crownPartitionRankPoint P hendpoints u,
    augmentedCoordinate_crownPartitionRankPoint P hendpoints v]
  have hden := (crownPartition_rank_denominator_pos P hendpoints).ne'
  constructor
  · intro h
    have hnum : (crownPartitionBlockRank P (Quotient.mk'' u) : ℝ) -
        crownPartitionBlockRank P (crownPartitionBottomBlock P) =
        (crownPartitionBlockRank P (Quotient.mk'' v) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P) :=
      (div_left_inj' hden).mp h
    have hrank : crownPartitionBlockRank P (Quotient.mk'' u) =
        crownPartitionBlockRank P (Quotient.mk'' v) := by
      exact_mod_cast (sub_left_inj.mp hnum)
    exact Quotient.exact (crownPartitionBlockRank_injective P hrank)
  · intro huv
    exact congrArg (fun C =>
      ((crownPartitionBlockRank P C : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P)) /
        ((crownPartitionBlockRank P (crownPartitionTopBlock P) : ℝ) -
          crownPartitionBlockRank P (crownPartitionBottomBlock P))) (Quotient.sound huv)

private def crownComparableTightSet {n : ℕ} (u v : CrownAugmentedVertex n) :
    Set (Fin (2 * n) → ℝ) :=
  {x | x ∈ crownOrderPolytope n ∧ augmentedCoordinate x u = augmentedCoordinate x v}

private theorem crownComparableTightSet_isExposed {n : ℕ} {u v : CrownAugmentedVertex n}
    (huv : crownAugmentedLE u v) :
    IsExposed ℝ (crownOrderPolytope n) (crownComparableTightSet u v) := by
  cases u with
  | bottom =>
      cases v with
      | bottom =>
          simpa [crownComparableTightSet, augmentedCoordinate] using
            (IsExposed.refl (𝕜 := ℝ) (crownOrderPolytope n))
      | vertex j =>
          intro _
          refine ⟨-(ContinuousLinearMap.proj j), ?_⟩
          ext x
          constructor
          · rintro ⟨hx, heq⟩
            refine ⟨hx, ?_⟩
            intro y hy
            simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.proj_apply]
            have hxj : x j = 0 := by simpa [augmentedCoordinate] using heq.symm
            linarith [(hy.1 j).1]
          · rintro ⟨hx, hmax⟩
            refine ⟨hx, ?_⟩
            have hzero := hmax 0 (zero_mem_crown_order_polytope n)
            simp only [map_zero, ContinuousLinearMap.neg_apply,
              ContinuousLinearMap.proj_apply, Pi.zero_apply, neg_zero] at hzero
            have hxnonneg := (hx.1 j).1
            simp only [augmentedCoordinate]
            linarith
      | top =>
          simpa [crownComparableTightSet, augmentedCoordinate] using
            (isExposed_empty (𝕜 := ℝ) (A := crownOrderPolytope n))
  | vertex i =>
      cases v with
      | bottom => simp [crownAugmentedLE] at huv
      | top =>
          intro _
          refine ⟨ContinuousLinearMap.proj i, ?_⟩
          ext x
          constructor
          · rintro ⟨hx, heq⟩
            refine ⟨hx, ?_⟩
            intro y hy
            simp only [ContinuousLinearMap.proj_apply]
            have hxi : x i = 1 := by simpa [augmentedCoordinate] using heq
            linarith [(hy.1 i).2]
          · rintro ⟨hx, hmax⟩
            refine ⟨hx, ?_⟩
            have hone := hmax 1 (one_mem_crown_order_polytope n)
            simp only [ContinuousLinearMap.proj_apply, Pi.one_apply] at hone
            have hxle := (hx.1 i).2
            simp only [augmentedCoordinate]
            linarith
      | vertex j =>
          rcases huv with rfl | hij
          · simpa [crownComparableTightSet] using
              (IsExposed.refl (𝕜 := ℝ) (crownOrderPolytope n))
          · intro _
            refine ⟨(ContinuousLinearMap.proj (R := ℝ) i :
              (Fin (2 * n) → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j, ?_⟩
            ext x
            constructor
            · rintro ⟨hx, heq⟩
              refine ⟨hx, ?_⟩
              intro y hy
              simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply]
              have hxy : x i = x j := by simpa [augmentedCoordinate] using heq
              linarith [hy.2 i j hij]
            · rintro ⟨hx, hmax⟩
              refine ⟨hx, ?_⟩
              have hzero := hmax 0 (zero_mem_crown_order_polytope n)
              simp only [map_zero, ContinuousLinearMap.sub_apply,
                ContinuousLinearMap.proj_apply, Pi.zero_apply, sub_self] at hzero
              have hxle := hx.2 i j hij
              simp only [augmentedCoordinate]
              linarith
  | top =>
      cases v with
      | bottom => simp [crownAugmentedLE] at huv
      | vertex j => simp [crownAugmentedLE] at huv
      | top =>
          simpa [crownComparableTightSet, augmentedCoordinate] using
            (IsExposed.refl (𝕜 := ℝ) (crownOrderPolytope n))

private noncomputable def crownPartitionInternalPairs {n : ℕ}
    (P : CrownConnectedCompatiblePartition n) :
    Finset (CrownAugmentedVertex n × CrownAugmentedVertex n) := by
  classical
  exact Finset.univ.filter fun p => P.toSetoid.r p.1 p.2 ∧ crownAugmentedLE p.1 p.2

/-- The actual polytope subset cut out by all comparable equalities internal to a CCP. -/
noncomputable def crownPartitionFaceSet {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Set (Fin (2 * n) → ℝ) :=
  ⋂₀ ((crownPartitionInternalPairs P).image fun p => crownComparableTightSet p.1 p.2 :
    Finset (Set (Fin (2 * n) → ℝ)))

/-- The inverse subset attached to a CCP is an actual exposed face of the crown order polytope. -/
theorem crownPartitionFaceSet_isExposed {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    IsExposed ℝ (crownOrderPolytope n) (crownPartitionFaceSet P) := by
  classical
  apply IsExposed.sInter
  · refine Finset.image_nonempty.mpr ⟨(.bottom, .bottom), ?_⟩
    rw [crownPartitionInternalPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, P.toSetoid.refl _, by simp [crownAugmentedLE]⟩
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨p, hp, rfl⟩
    exact crownComparableTightSet_isExposed (Finset.mem_filter.mp hp).2.2

/-- Membership in the inverse face means feasibility together with constancy on every CCP block. -/
theorem mem_crownPartitionFaceSet_iff {n : ℕ} (P : CrownConnectedCompatiblePartition n)
    (x : Fin (2 * n) → ℝ) :
    x ∈ crownPartitionFaceSet P ↔
      x ∈ crownOrderPolytope n ∧ ∀ u v, P.toSetoid.r u v →
        augmentedCoordinate x u = augmentedCoordinate x v := by
  classical
  constructor
  · intro hx
    have hmem (u v : CrownAugmentedVertex n) (hrel : P.toSetoid.r u v)
        (hle : crownAugmentedLE u v) : x ∈ crownComparableTightSet u v := by
      rw [crownPartitionFaceSet, Set.mem_sInter] at hx
      apply hx
      apply Finset.mem_coe.mpr
      apply Finset.mem_image.mpr
      refine ⟨(u, v), ?_, rfl⟩
      rw [crownPartitionInternalPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hrel, hle⟩
    have hpoly : x ∈ crownOrderPolytope n :=
      (hmem .bottom .bottom (P.toSetoid.refl _) (by simp [crownAugmentedLE])).1
    refine ⟨hpoly, ?_⟩
    intro u v huv
    have hreach := (P.connected u v).mp huv
    have walk_eq {a b : CrownAugmentedVertex n}
        (p : (crownPartitionGraph P.toSetoid).Walk a b) :
        augmentedCoordinate x a = augmentedCoordinate x b := by
      induction p with
      | nil => rfl
      | @cons a b c hab p ih =>
          have hab_eq : augmentedCoordinate x a = augmentedCoordinate x b := by
            rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
            · exact (hmem a b h.1 h.2).2
            · exact (hmem b a h.1 h.2).2.symm
          exact hab_eq.trans ih
    exact walk_eq hreach.some
  · rintro ⟨hpoly, hblocks⟩
    rw [crownPartitionFaceSet, Set.mem_sInter]
    intro B hB
    have hB' := Finset.mem_coe.mp hB
    rcases Finset.mem_image.mp hB' with ⟨p, hp, rfl⟩
    exact ⟨hpoly, hblocks p.1 p.2 (Finset.mem_filter.mp hp).2.1⟩

/-- The actual exposed face inverse to a connected compatible partition. -/
noncomputable def crownPartitionFace {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    CrownExposedFace n :=
  ⟨crownPartitionFaceSet P, crownPartitionFaceSet_isExposed P⟩

private theorem crownPartition_all_related_of_endpoints_eq {n : ℕ}
    (P : CrownConnectedCompatiblePartition n)
    (hendpoints : crownPartitionBottomBlock P = crownPartitionTopBlock P)
    (u v : CrownAugmentedVertex n) : P.toSetoid.r u v := by
  apply Quotient.exact
  apply P.compatible
  · exact (crownPartition_le_top P (Quotient.mk'' u)).trans <|
      hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' v)
  · exact (crownPartition_le_top P (Quotient.mk'' v)).trans <|
      hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' u)

/-- The tight graph of the inverse face has exactly the prescribed connected blocks. -/
theorem crownPartitionFace_tightComponent_iff {n : ℕ}
    (P : CrownConnectedCompatiblePartition n) (u v : CrownAugmentedVertex n) :
    (crownFaceTightGraph (crownPartitionFace P)).Reachable u v ↔ P.toSetoid.r u v := by
  classical
  constructor
  · intro huv
    by_cases hendpoints : crownPartitionBottomBlock P = crownPartitionTopBlock P
    · exact crownPartition_all_related_of_endpoints_eq P hendpoints u v
    · have hrank_mem : crownPartitionRankPoint P ∈ (crownPartitionFace P).1 :=
        (mem_crownPartitionFaceSet_iff P _).2
          ⟨crownPartitionRankPoint_mem P hendpoints,
            fun a b hab => (augmentedCoordinate_crownPartitionRankPoint_eq_iff
              P hendpoints a b).2 hab⟩
      have walk_rel {a b : CrownAugmentedVertex n}
          (p : (crownFaceTightGraph (crownPartitionFace P)).Walk a b) :
          P.toSetoid.r a b := by
        induction p with
        | nil => exact P.toSetoid.refl _
        | @cons a b c hab p ih =>
            have hab_eq := crownFaceTightGraph_adj_eq (crownPartitionFace P) hab hrank_mem
            exact P.toSetoid.trans
              ((augmentedCoordinate_crownPartitionRankPoint_eq_iff P hendpoints a b).1 hab_eq) ih
      exact walk_rel huv.some
  · intro huv
    have hreach := (P.connected u v).mp huv
    apply hreach.mono
    intro a b hab
    rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
    · rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
      refine ⟨hne, Or.inl ⟨h.2, ?_⟩⟩
      intro x hx
      exact (mem_crownPartitionFaceSet_iff P x).1 hx |>.2 a b h.1
    · rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
      refine ⟨hne, Or.inr ⟨h.2, ?_⟩⟩
      intro x hx
      exact (mem_crownPartitionFaceSet_iff P x).1 hx |>.2 b a h.1

/-- The inverse face is nonempty exactly when its bottom and top blocks are distinct. -/
theorem crownPartitionFace_nonempty_iff {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    (crownPartitionFace P).1.Nonempty ↔
      crownPartitionBottomBlock P ≠ crownPartitionTopBlock P := by
  constructor
  · rintro ⟨x, hx⟩ hendpoints
    have hall := crownPartition_all_related_of_endpoints_eq P hendpoints
      CrownAugmentedVertex.bottom CrownAugmentedVertex.top
    have heq := (mem_crownPartitionFaceSet_iff P x).1 hx |>.2 _ _ hall
    norm_num [augmentedCoordinate] at heq
  · intro hendpoints
    refine ⟨crownPartitionRankPoint P, ?_⟩
    exact (mem_crownPartitionFaceSet_iff P _).2
      ⟨crownPartitionRankPoint_mem P hendpoints,
        fun u v huv => (augmentedCoordinate_crownPartitionRankPoint_eq_iff
          P hendpoints u v).2 huv⟩

private theorem crownFace_mem_of_partition_constraints {n : ℕ} (F : CrownExposedFace n)
    (hF : F.1.Nonempty) {x : Fin (2 * n) → ℝ}
    (hxpoly : x ∈ crownOrderPolytope n)
    (hxblocks : ∀ u v, (crownFaceTightGraph F).Reachable u v →
      augmentedCoordinate x u = augmentedCoordinate x v) : x ∈ F.1 := by
  classical
  obtain ⟨anchor, hanchor⟩ := hF
  have hFex : IsExposed ℝ (crownAffineSlackFamily n).feasible F.1 := by
    simpa [crown_affine_slack_feasible_eq] using F.2
  rw [exposed_eq_active_of_finite_slacks (crownAffineSlackFamily n) F.1 hFex
    anchor hanchor]
  refine ⟨?_, ?_⟩
  · simpa [crown_affine_slack_feasible_eq] using hxpoly
  · intro i hi
    let e := Fintype.equivFin (CrownConstraint n)
    let c := e.symm i
    have hic : i = e c := by simp [c]
    rw [hic] at hi ⊢
    rcases c with j | j | p
    · have htight : crownFaceTightRel F .bottom (.vertex j) := by
        refine ⟨by simp [crownAugmentedLE], ?_⟩
        intro y hy
        have hz := hi y hy
        simpa [crownAffineSlackFamily, crownConstraintSlack, e,
          augmentedCoordinate] using hz.symm
      have hadj : (crownFaceTightGraph F).Adj .bottom (.vertex j) := by
        rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
        exact ⟨by simp, Or.inl htight⟩
      have heq := hxblocks .bottom (.vertex j) hadj.reachable
      simpa [crownAffineSlackFamily, crownConstraintSlack, e,
        augmentedCoordinate] using heq.symm
    · have htight : crownFaceTightRel F (.vertex j) .top := by
        refine ⟨by simp [crownAugmentedLE], ?_⟩
        intro y hy
        have hz := hi y hy
        have hyj : y j = 1 := by
          have hz' : 1 - y j = 0 := by
            simpa [crownAffineSlackFamily, crownConstraintSlack, e] using hz
          linarith
        simpa [augmentedCoordinate, hyj]
      have hadj : (crownFaceTightGraph F).Adj (.vertex j) .top := by
        rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
        exact ⟨by simp, Or.inl htight⟩
      have heq := hxblocks (.vertex j) .top hadj.reachable
      simpa [crownAffineSlackFamily, crownConstraintSlack, e,
        augmentedCoordinate] using sub_eq_zero.mpr heq.symm
    · by_cases hp : p.1.1 = p.1.2
      · simp [crownAffineSlackFamily, crownConstraintSlack, e, hp]
      · have htight : crownFaceTightRel F (.vertex p.1.1) (.vertex p.1.2) := by
          refine ⟨Or.inr p.2, ?_⟩
          intro y hy
          have hz := hi y hy
          have hyij : y p.1.2 - y p.1.1 = 0 := by
            simpa [crownAffineSlackFamily, crownConstraintSlack, e] using hz
          simp only [augmentedCoordinate]
          linarith
        have hadj : (crownFaceTightGraph F).Adj (.vertex p.1.1) (.vertex p.1.2) := by
          rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
          exact ⟨by simpa using hp, Or.inl htight⟩
        have heq := hxblocks (.vertex p.1.1) (.vertex p.1.2) hadj.reachable
        simpa [crownAffineSlackFamily, crownConstraintSlack, e,
          augmentedCoordinate] using sub_eq_zero.mpr heq.symm

/-- Taking tight blocks of an actual face and then applying the CCP inverse recovers that face. -/
theorem crownPartitionFace_crownFacePartition {n : ℕ} (F : CrownExposedFace n) :
    crownPartitionFace (crownFacePartition F) = F := by
  apply Subtype.ext
  by_cases hF : F.1.Nonempty
  · ext x
    constructor
    · intro hx
      have hx' := (mem_crownPartitionFaceSet_iff (crownFacePartition F) x).1 hx
      exact crownFace_mem_of_partition_constraints F hF hx'.1 hx'.2
    · intro hx
      apply (mem_crownPartitionFaceSet_iff (crownFacePartition F) x).2
      refine ⟨F.2.subset hx, ?_⟩
      intro u v huv
      exact augmentedCoordinate_eq_of_tightComponent F
        (SimpleGraph.ConnectedComponent.sound huv) hx
  · have hFempty : F.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    rw [hFempty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hbottomtop :
        (crownFaceTightGraph F).Reachable .bottom .top := by
      apply SimpleGraph.Adj.reachable
      rw [crownFaceTightGraph, SimpleGraph.fromRel_adj]
      refine ⟨by simp, Or.inl ⟨by simp [crownAugmentedLE], ?_⟩⟩
      intro y hy
      rw [hFempty] at hy
      exact False.elim (by simpa using hy)
    have hendpoints : crownPartitionBottomBlock (crownFacePartition F) =
        crownPartitionTopBlock (crownFacePartition F) :=
      SimpleGraph.ConnectedComponent.sound hbottomtop
    exact ((crownPartitionFace_nonempty_iff (crownFacePartition F)).1 ⟨x, hx⟩) hendpoints


end D5.S3.Combinatorics.Geometry.CrownOrderPolytope
