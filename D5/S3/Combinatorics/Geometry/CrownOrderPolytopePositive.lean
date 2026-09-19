/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopePositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Setoid.Basic]
   utility: none
   digest: Consecutive cuts of the augmented two-vertex crown supply the positive-n boundary. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeFaceCounts
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope
open scoped BigOperators

private def triangleVertex : Fin 4 → CrownAugmentedVertex 1 :=
  ![.bottom, .vertex 0, .vertex 1, .top]

private def triangleIndex : CrownAugmentedVertex 1 → Fin 4
  | .bottom => 0
  | .vertex i => ⟨i.val + 1, by omega⟩
  | .top => 3

private def triangleEquiv : CrownAugmentedVertex 1 ≃ Fin 4 where
  toFun := triangleIndex
  invFun := triangleVertex
  left_inv u := by
    cases u with
    | bottom => rfl
    | top => rfl
    | vertex i => fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def triangleRank (s : Finset (Fin 3)) (u : CrownAugmentedVertex 1) : ℕ :=
  (s.filter (fun j => j.val < (triangleIndex u).val)).card

private def trianglePartition (s : Finset (Fin 3)) :
    CrownConnectedCompatiblePartition 1 := by
  have triangle_order (u v : CrownAugmentedVertex 1) :
      crownAugmentedLE u v ↔ triangleIndex u ≤ triangleIndex v := by
    obtain ⟨i, rfl⟩ := triangleEquiv.symm.surjective u
    obtain ⟨j, rfl⟩ := triangleEquiv.symm.surjective v
    fin_cases i <;> fin_cases j <;>
      norm_num [triangleEquiv, triangleVertex, triangleIndex, crownAugmentedLE,
        crownRelation, Fin.le_def, Fin.lt_def, Fin.ext_iff]
  exact {
  toSetoid := Setoid.ker (triangleRank s)
  connected u v := by
    constructor
    · intro huv
      by_cases he : u = v
      · subst v; exact SimpleGraph.Reachable.rfl
      · apply SimpleGraph.Adj.reachable
        rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
        refine ⟨he, ?_⟩
        rcases le_total (triangleIndex u) (triangleIndex v) with h | h
        · exact Or.inl ⟨huv, (triangle_order u v).mpr h⟩
        · exact Or.inr ⟨huv.symm, (triangle_order v u).mpr h⟩
    · rintro ⟨p⟩
      induction p with
      | nil => rfl
      | @cons a b c hab p ih =>
        rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
        · exact h.1.trans ih
        · exact h.1.symm.trans ih
  compatible := by
    intro C D hCD hDC
    have hmono (u v : CrownAugmentedVertex 1) (h : crownAugmentedLE u v) :
        triangleRank s u ≤ triangleRank s v := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨hjs, hj⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjs, lt_of_lt_of_le hj ((triangle_order u v).mp h)⟩
    have hlift {A B : Quotient (Setoid.ker (triangleRank s))}
        (h : crownPartitionBlockLE (Setoid.ker (triangleRank s)) A B) :
        Setoid.kerLift (triangleRank s) A ≤ Setoid.kerLift (triangleRank s) B := by
      induction h with
      | refl => exact le_rfl
      | @tail E B hAE hEB ih =>
        obtain ⟨u, v, rfl, rfl, huv⟩ := hEB
        exact ih.trans (hmono u v huv)
    exact Setoid.kerLift_injective _ (le_antisymm (hlift hCD) (hlift hDC)) }

private theorem trianglePartition_bijective : Function.Bijective trianglePartition := by
  classical
  have hext (P Q : CrownConnectedCompatiblePartition 1)
      (h : P.toSetoid = Q.toSetoid) : P = Q := by
    cases P; cases Q; cases h; rfl
  have hRanks : ∀ (s : Finset (Fin 3)) (i j : Fin 4),
      triangleRank s (triangleVertex i) = triangleRank s (triangleVertex j) ↔
        ∀ k : Fin 3, (i ≤ k.castSucc ∧ k.succ ≤ j ∨
          j ≤ k.castSucc ∧ k.succ ≤ i) → k ∉ s := by decide
  have hrank (s : Finset (Fin 3)) (i : Fin 3) :
      (trianglePartition s).toSetoid.r (triangleVertex i.castSucc)
        (triangleVertex i.succ) ↔ i ∉ s := by
    change triangleRank s (triangleVertex i.castSucc) =
      triangleRank s (triangleVertex i.succ) ↔ _
    rw [hRanks]
    fin_cases i <;> norm_num [Fin.forall_fin_succ, Fin.le_def] <;> rfl
  constructor
  · intro s t h
    ext i
    have he := congrArg CrownConnectedCompatiblePartition.toSetoid h
    have hrel := Setoid.ext_iff.mp he (triangleVertex i.castSucc) (triangleVertex i.succ)
    rw [hrank, hrank] at hrel
    exact not_iff_not.mp hrel
  · intro P
    let s := Finset.univ.filter (fun i : Fin 3 =>
      ¬ P.toSetoid.r (triangleVertex i.castSucc) (triangleVertex i.succ))
    refine ⟨s, hext _ _ ?_⟩
    have hstep (i j : Fin 4) (hij : i ≤ j) :
        crownPartitionBlockLE P.toSetoid
          (Quotient.mk'' (triangleVertex i)) (Quotient.mk'' (triangleVertex j)) := by
      apply Relation.ReflTransGen.single
      refine ⟨_, _, rfl, rfl, ?_⟩
      fin_cases i <;> fin_cases j <;>
        norm_num [Fin.le_def] at hij <;>
        norm_num [triangleVertex, crownAugmentedLE, crownRelation, Fin.ext_iff]
    have hconv (i j k : Fin 4) (hij : i ≤ j) (hjk : j ≤ k)
        (h : P.toSetoid.r (triangleVertex i) (triangleVertex k)) :
        P.toSetoid.r (triangleVertex i) (triangleVertex j) := by
      apply Quotient.exact
      apply P.compatible (hstep i j hij)
      have hk := hstep j k hjk
      have he : (Quotient.mk'' (triangleVertex i) : Quotient P.toSetoid) =
          Quotient.mk'' (triangleVertex k) := Quotient.sound h
      rw [← he] at hk
      exact hk
    have h02 : P.toSetoid.r (triangleVertex 0) (triangleVertex 2) ↔
        P.toSetoid.r (triangleVertex 0) (triangleVertex 1) ∧
          P.toSetoid.r (triangleVertex 1) (triangleVertex 2) := by
      constructor
      · intro h
        have h01 := hconv 0 1 2 (by decide) (by decide) h
        exact ⟨h01, P.toSetoid.trans (P.toSetoid.symm h01) h⟩
      · exact fun h => P.toSetoid.trans h.1 h.2
    have h13 : P.toSetoid.r (triangleVertex 1) (triangleVertex 3) ↔
        P.toSetoid.r (triangleVertex 1) (triangleVertex 2) ∧
          P.toSetoid.r (triangleVertex 2) (triangleVertex 3) := by
      constructor
      · intro h
        have h12 := hconv 1 2 3 (by decide) (by decide) h
        exact ⟨h12, P.toSetoid.trans (P.toSetoid.symm h12) h⟩
      · exact fun h => P.toSetoid.trans h.1 h.2
    have h03 : P.toSetoid.r (triangleVertex 0) (triangleVertex 3) ↔
        P.toSetoid.r (triangleVertex 0) (triangleVertex 1) ∧
          P.toSetoid.r (triangleVertex 1) (triangleVertex 2) ∧
            P.toSetoid.r (triangleVertex 2) (triangleVertex 3) := by
      constructor
      · intro h
        have h01 := hconv 0 1 3 (by decide) (by decide) h
        exact ⟨h01, h13.mp (P.toSetoid.trans (P.toSetoid.symm h01) h)⟩
      · exact fun h => P.toSetoid.trans h.1 (h13.mpr h.2)
    apply Setoid.ext
    intro u v
    obtain ⟨i, rfl⟩ := triangleEquiv.symm.surjective u
    obtain ⟨j, rfl⟩ := triangleEquiv.symm.surjective v
    change triangleRank s (triangleVertex i) = triangleRank s (triangleVertex j) ↔
      P.toSetoid.r (triangleVertex i) (triangleVertex j)
    have hsym (a b : CrownAugmentedVertex 1) : P.toSetoid.r a b ↔ P.toSetoid.r b a :=
      ⟨P.toSetoid.symm, P.toSetoid.symm⟩
    have h10 := hsym (triangleVertex 1) (triangleVertex 0)
    have h20 := hsym (triangleVertex 2) (triangleVertex 0)
    have h30 := hsym (triangleVertex 3) (triangleVertex 0)
    have h21 := hsym (triangleVertex 2) (triangleVertex 1)
    have h31 := hsym (triangleVertex 3) (triangleVertex 1)
    have h32 := hsym (triangleVertex 3) (triangleVertex 2)
    rw [hRanks]
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.forall_fin_succ, Fin.le_def,
        h10, h20, h30, h21, h31, h32, h02, h13, h03, Setoid.refl] <;>
      simp_all [triangleVertex]

private theorem triangle_geometric_count (d : ℕ) :
    crownGeometricFaceCount 1 d = Nat.choose 3 (d + 1) := by
  have crownPartition_bottom_le {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid (crownPartitionBottomBlock P) C := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    exact ⟨.bottom, v, rfl, rfl, by simp [crownAugmentedLE]⟩
  have crownPartition_le_top {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      (C : Quotient P.toSetoid) :
      crownPartitionBlockLE P.toSetoid C (crownPartitionTopBlock P) := by
    refine Quotient.inductionOn C ?_
    intro v
    apply Relation.ReflTransGen.single
    refine ⟨v, .top, rfl, rfl, ?_⟩
    cases v <;> simp [crownAugmentedLE]
  have crownPartitionBlockRank_mono {n : ℕ} (P : CrownConnectedCompatiblePartition n)
      {C D : Quotient P.toSetoid} (hCD : crownPartitionBlockLE P.toSetoid C D) :
      crownPartitionBlockRank P C ≤ crownPartitionBlockRank P D := by
    letI := P.blockPartialOrder
    letI : Fintype (Quotient P.toSetoid) := Fintype.ofFinite _
    letI : Fintype (LinearExtension (Quotient P.toSetoid)) :=
        Fintype.ofEquiv (Quotient P.toSetoid)
          { toFun := fun x => x
            invFun := fun x => x
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    let e := monoEquivOfFin (LinearExtension (Quotient P.toSetoid)) rfl
    have hlinear : toLinearExtension C ≤ toLinearExtension D := toLinearExtension.monotone hCD
    have hfin : e.symm (toLinearExtension C) ≤ e.symm (toLinearExtension D) :=
      e.symm.monotone hlinear
    change (e.symm (toLinearExtension C)).val ≤ (e.symm (toLinearExtension D)).val
    exact hfin
  have crownPartitionBlockRank_injective {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) :
      Function.Injective (crownPartitionBlockRank P) := by
    intro C D h
    letI := P.blockPartialOrder
    unfold crownPartitionBlockRank at h
    have hCD : toLinearExtension C = toLinearExtension D :=
      OrderIso.injective _ (Fin.ext h)
    exact hCD
  have crownPartition_rank_denominator_pos {n : ℕ}
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
  have crownPartition_block_le_of_augmentedLE {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) {u v : CrownAugmentedVertex n}
      (huv : crownAugmentedLE u v) :
      crownPartitionBlockLE P.toSetoid (Quotient.mk'' u) (Quotient.mk'' v) := by
    exact
      Relation.ReflTransGen.single ⟨u, v, rfl, rfl, huv⟩
  have crownPartitionRankPoint_mem {n : ℕ} (P : CrownConnectedCompatiblePartition n)
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
  have augmentedCoordinate_crownPartitionRankPoint {n : ℕ}
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
  have augmentedCoordinate_crownPartitionRankPoint_eq_iff {n : ℕ}
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
  have crownPartition_all_related_of_endpoints_eq {n : ℕ}
      (P : CrownConnectedCompatiblePartition n)
      (hendpoints : crownPartitionBottomBlock P = crownPartitionTopBlock P)
      (u v : CrownAugmentedVertex n) : P.toSetoid.r u v := by
    apply Quotient.exact
    apply P.compatible
    · exact (crownPartition_le_top P (Quotient.mk'' u)).trans <|
        hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' v)
    · exact (crownPartition_le_top P (Quotient.mk'' v)).trans <|
        hendpoints.symm ▸ crownPartition_bottom_le P (Quotient.mk'' u)
  have crownPartitionFace_nonempty_iff {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
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
  have trianglePartition_card (s : Finset (Fin 3)) :
      Nat.card (Quotient (trianglePartition s).toSetoid) = s.card + 1 := by
    classical
    have himage : ∀ t : Finset (Fin 3),
        Finset.univ.image (triangleRank t) = Finset.range (t.card + 1) := by decide
    change Nat.card (Quotient (Setoid.ker (triangleRank s))) = _
    rw [Nat.card_congr (Setoid.quotientKerEquivRange (triangleRank s))]
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_of_finset' (Finset.univ.image (triangleRank s))
      (by intro k; simp)]
    rw [himage, Finset.card_range]
  classical
  let A := {s : Finset (Fin 3) // s.card = d + 1}
  let B := {F : CrownExposedFace 1 // F.val.Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ F.val).direction = d}
  have hsep (s : A) : crownPartitionBottomBlock (trianglePartition s.val) ≠
      crownPartitionTopBlock (trianglePartition s.val) := by
    intro h
    have hr := Quotient.exact h
    change triangleRank s.val .bottom = triangleRank s.val .top at hr
    simp [triangleRank, triangleIndex] at hr
    omega
  let f : A → B := fun s =>
    ⟨crownPartitionFace (trianglePartition s.val),
      (crownPartitionFace_nonempty_iff _).mpr (hsep s), by
      have hd := crownPartitionFace_finrank_direction _ (hsep s)
      rw [← Nat.card_eq_fintype_card, trianglePartition_card, s.property] at hd
      simpa using hd⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro s t h
      have hface := congrArg Subtype.val h
      have he : (trianglePartition s.val).toSetoid = (trianglePartition t.val).toSetoid := by
        apply Setoid.ext
        intro u v
        rw [← crownPartitionFace_tightComponent_iff (trianglePartition s.val) u v,
          ← crownPartitionFace_tightComponent_iff (trianglePartition t.val) u v]
        exact congrArg (fun F => (crownFaceTightGraph F).Reachable u v) hface |>.to_iff
      have hext (P Q : CrownConnectedCompatiblePartition 1)
          (h : P.toSetoid = Q.toSetoid) : P = Q := by
        cases P; cases Q; cases h; rfl
      exact Subtype.ext (trianglePartition_bijective.1 (hext _ _ he))
    · intro F
      obtain ⟨s, hs⟩ := trianglePartition_bijective.2 (crownFacePartition F.val)
      have hface : crownPartitionFace (trianglePartition s) = F.val := by
        rw [hs, crownPartitionFace_crownFacePartition]
      have hends := (crownPartitionFace_nonempty_iff (trianglePartition s)).mp
        (by rw [hface]; exact F.property.1)
      have hnonzero : s.card ≠ 0 := by
        intro hc
        have hsz := Finset.card_eq_zero.mp hc
        apply hends
        apply Quotient.sound
        change triangleRank s .bottom = triangleRank s .top
        simp [hsz, triangleRank]
      have hdim := crownPartitionFace_finrank_direction _ hends
      rw [← Nat.card_eq_fintype_card, trianglePartition_card, hface, F.property.2] at hdim
      have hsc : s.card = d + 1 := by omega
      exact ⟨⟨s, hsc⟩, Subtype.ext hface⟩
  change Nat.card B = _
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp [A, Nat.card_eq_fintype_card, Fintype.card_finset_len]
/-- The full f-vector is indexed by the empty face first, followed by the
    actual geometric dimensions. In particular the whole polytope is included. -/
noncomputable def crownGeometricFVector (n : ℕ) : Fin (2 * n + 2) → ℕ := fun k =>
  if k.val = 0 then 1 else crownGeometricFaceCount n (k.val - 1)

/-- The actual geometric face formula holds for every positive crown size.
    The two-vertex boundary is obtained from the consecutive cuts of its
    augmented chain, and uses the same signed-support convention as the sum. -/
theorem crownGeometricFaceCount_eq_of_pos (n d : ℕ) (hn : 0 < n) :
    crownGeometricFaceCount n d = (if d = 0 then 2 else 0) +
      (if d = 1 then 1 else 0) +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 2 (2 * n)},
          ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (i.val / 2)},
            ((2 * n * Nat.choose i.val (2 * m.val) *
              Nat.choose (n + m.val - 1) (i.val - 1)) *
                (if d ≤ i.val then Nat.choose (2 * m.val) (i.val - d) else 0)) / i.val := by
  by_cases hn2 : 2 ≤ n
  · exact crownGeometricFaceCount_eq n d hn2
  have hn1 : n = 1 := by omega
  subst n
  rw [triangle_geometric_count]
  classical
  have hsum (a : ℕ) (f : {i : ℕ // i ∈ Finset.Icc a a} → ℕ) :
      ∑ i, f i = f ⟨a, by simp⟩ := by
    apply Fintype.sum_eq_single
    intro i hi
    have he : i = ⟨a, by simp⟩ := Subtype.ext (by simpa using i.property)
    exact (hi he).elim
  norm_num only [Nat.reduceMul]
  rw [hsum]
  norm_num only [Nat.reduceDiv]
  change Nat.choose 3 (d + 1) = (if d = 0 then 2 else 0) +
    (if d = 1 then 1 else 0) +
      ∑ m : {m : ℕ // m ∈ Finset.Icc 1 1},
        (2 * Nat.choose 2 (2 * m.val) * Nat.choose (1 + m.val - 1) 1 *
          (if d ≤ 2 then Nat.choose (2 * m.val) (2 - d) else 0)) / 2
  rw [hsum]
  norm_num only [Nat.reduceMul, Finset.Icc_self, Finset.sum_singleton,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.choose_self, Nat.choose_one_right,
    Nat.choose_zero_right, Nat.mul_one, Nat.one_mul]
  by_cases hd : d ≤ 2
  · interval_cases d <;> norm_num
  · have hdc : 3 < d + 1 := by omega
    simp [hd, Nat.choose_eq_zero_of_lt hdc, show d ≠ 0 by omega, show d ≠ 1 by omega]

#print axioms crownGeometricFaceCount_eq_of_pos

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
