/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentNormalizedBoxes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentNormalizedBoxes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: Coordinate permutation normalizes the two possible partitions and realizes each transverse component as a box with descended height. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ProjectedHeightCompatibility
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentStarProducts
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes

/-! Coordinate permutation normalizes the two possible partitions and realizes each transverse component as a box with descended height. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9ProjectedHeightCompatibility

/-- The triple containing coordinates zero and one in either normalized split. -/
def leftPart (p : Bool) (x : Point) : BitVec 3 :=
  BitVec.ofBoolListLE [x.getLsbD 0, x.getLsbD 1, x.getLsbD (if p then 3 else 2)]

/-- The complementary triple in either normalized split. -/
def rightPart (p : Bool) (x : Point) : BitVec 3 :=
  BitVec.ofBoolListLE [x.getLsbD (if p then 2 else 3), x.getLsbD 4, x.getLsbD 5]

/-- Combine the two triple patterns in the coordinate order of the split. -/
def joinParts (p : Bool) (a b : BitVec 3) : Point :=
  BitVec.ofBoolListLE [a.getLsbD 0, a.getLsbD 1,
    if p then b.getLsbD 0 else a.getLsbD 2,
    if p then a.getLsbD 2 else b.getLsbD 0, b.getLsbD 1, b.getLsbD 2]

private theorem left_xor (p : Bool) (c x : Point) :
    leftPart p (x ^^^ c) = leftPart p x ^^^ leftPart p c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    cases p <;> simp only [leftPart, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_ofBoolListLE, BitVec.getLsbD_xor, List.getD_cons_zero, List.getD_cons_succ]

private theorem right_xor (p : Bool) (c x : Point) :
    rightPart p (x ^^^ c) = rightPart p x ^^^ rightPart p c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    cases p <;> simp only [rightPart, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_ofBoolListLE, BitVec.getLsbD_xor, List.getD_cons_zero, List.getD_cons_succ]

private theorem parts_of_join (p : Bool) : ∀ a b : Fin 8,
    leftPart p (joinParts p (BitVec.ofFin a) (BitVec.ofFin b)) = BitVec.ofFin a ∧
    rightPart p (joinParts p (BitVec.ofFin a) (BitVec.ofFin b)) = BitVec.ofFin b := by
  cases p <;> decide +kernel

private theorem zero_box_parts (p : Bool) : ∀ x : Fin 64,
    inBox p 0#6 (BitVec.ofFin x) = true ↔
      (leftPart p (BitVec.ofFin x)).cpop = 1#3 ∧
      (rightPart p (BitVec.ofFin x)).cpop = 1#3 := by
  cases p <;> decide +kernel

/-- The nine-point box is the product of two three-leaf stars with arbitrary
centers in the two corresponding three-cubes. -/
theorem inBox_joinParts_iff (p : Bool) (a b : BitVec 3) (x : Point) :
    inBox p (joinParts p a b) x = true ↔
      Q3StarHeight.isLeaf a (leftPart p x) = true ∧
      Q3StarHeight.isLeaf b (rightPart p x) = true := by
  let c := joinParts p a b
  have h := zero_box_parts p (x ^^^ c).toFin
  change inBox p 0#6 (x ^^^ c) = true ↔ _ at h
  have hL : leftPart p c = a := (parts_of_join p a.toFin b.toFin).1
  have hR : rightPart p c = b := (parts_of_join p a.toFin b.toFin).2
  rw [left_xor, right_xor, hL, hR] at h
  simp only [inBox, BitVec.xor_zero] at h
  simpa only [inBox, Q3StarHeight.isLeaf, beq_iff_eq, BitVec.xor_comm a, BitVec.xor_comm b] using h


end Q9ProjectedHeightCompatibility
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6TwoSplitRelabel

private def membershipPattern (A B : Finset (Fin 6)) (i : Fin 6) : Bool × Bool :=
  (decide (i ∈ A), decide (i ∈ B))

private theorem card_membershipFiber (A B : Finset (Fin 6))
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∩ B).card = 2) (p q : Bool) :
    Fintype.card {i // membershipPattern A B i = (p, q)} = (if p = q then 2 else 1) := by
  have hUnion : (A ∪ B).card = 4 := by
    have h := Finset.card_union_add_card_inter A B
    omega
  have hLeft : (A \ B).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter A B
    omega
  have hRight : (B \ A).card = 1 := by
    have h := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at h
    omega
  cases p <;> cases q
  · calc
      _ = (A ∪ B)ᶜ.card := Fintype.card_of_subtype _ (fun i => by
        simp only [Finset.mem_compl, Finset.mem_union, not_or, membershipPattern,
          Prod.mk.injEq, decide_eq_false_iff_not])
      _ = _ := by
        rw [Finset.card_compl, Fintype.card_fin, hUnion]
        decide
  · calc
      _ = (B \ A).card := Fintype.card_of_subtype _ (fun i => by
        simp only [Finset.mem_sdiff, membershipPattern, Prod.mk.injEq,
          decide_eq_false_iff_not, decide_eq_true_eq, and_comm])
      _ = _ := hRight
  · calc
      _ = (A \ B).card := Fintype.card_of_subtype _ (fun i => by
        simp only [Finset.mem_sdiff, membershipPattern, Prod.mk.injEq,
          decide_eq_true_eq, decide_eq_false_iff_not])
      _ = _ := hLeft
  · calc
      _ = (A ∩ B).card := Fintype.card_of_subtype _ (fun i => by
        simp only [Finset.mem_inter, membershipPattern, Prod.mk.injEq, decide_eq_true_eq])
      _ = _ := hAB

local notation "A₀" => ({0, 1, 2} : Finset (Fin 6))
local notation "B₀" => ({0, 1, 3} : Finset (Fin 6))

/-- Relabel two distinct complementary triple splits by a single permutation.
The first split keeps its chosen side and the second may exchange its sides. -/
theorem exists_relabel_two_splits {A B : Finset (Fin 6)}
    (hA : A.card = 3) (hB : B.card = 3) (hBA : B ≠ A) (hBAc : B ≠ Aᶜ) :
    ∃ σ : Equiv.Perm (Fin 6),
      A.map σ.toEmbedding = {0, 1, 2} ∧ (Aᶜ).map σ.toEmbedding = {3, 4, 5} ∧
      ((B.map σ.toEmbedding = {0, 1, 3} ∧ (Bᶜ).map σ.toEmbedding = {2, 4, 5}) ∨
        (B.map σ.toEmbedding = {2, 4, 5} ∧ (Bᶜ).map σ.toEmbedding = {0, 1, 3})) := by
  have hzero : (A ∩ B).card ≠ 0 := by
    intro h
    have hdisj : Disjoint A B :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h)
    exact hBAc (Finset.compl_eq_of_disjoint_of_card_add_eq hdisj (by simp [hA, hB])).symm
  have hthree : (A ∩ B).card ≠ 3 := by
    intro h
    have hleft := Finset.eq_of_subset_of_card_le
      (Finset.inter_subset_left : A ∩ B ⊆ A) (hA.trans h.symm).le
    have hright := Finset.eq_of_subset_of_card_le
      (Finset.inter_subset_right : A ∩ B ⊆ B) (hB.trans h.symm).le
    exact hBA (hright.symm.trans hleft)
  obtain ⟨C, hC, hAC, hside⟩ : ∃ C : Finset (Fin 6),
      C.card = 3 ∧ (A ∩ C).card = 2 ∧ (C = B ∨ C = Bᶜ) := by
    by_cases htwo : (A ∩ B).card = 2
    · exact ⟨B, hB, htwo, Or.inl rfl⟩
    have hle := Finset.card_le_card (Finset.inter_subset_left : A ∩ B ⊆ A)
    have hone : (A ∩ B).card = 1 := by omega
    refine ⟨Bᶜ, by simp [Finset.card_compl, hB], ?_, Or.inr rfl⟩
    rw [← Finset.sdiff_eq_inter_compl]
    have h := Finset.card_sdiff_add_card_inter A B
    omega
  have hA₀ : (A₀).card = 3 := by decide
  have hB₀ : (B₀).card = 3 := by decide
  have hA₀B₀ : (A₀ ∩ B₀).card = 2 := by decide
  let e (p : Bool × Bool) :
      {i // membershipPattern A C i = p} ≃ {i // membershipPattern A₀ B₀ i = p} :=
    Fintype.equivOfCardEq (by
      rcases p with ⟨p, q⟩
      rw [card_membershipFiber A C hA hC hAC, card_membershipFiber A₀ B₀ hA₀ hB₀ hA₀B₀])
  let σ : Equiv.Perm (Fin 6) := Equiv.ofFiberEquiv e
  have hσ (i : Fin 6) : membershipPattern A₀ B₀ (σ i) = membershipPattern A C i :=
    Equiv.ofFiberEquiv_map e i
  have mapSides {S T : Finset (Fin 6)} (h : ∀ i, σ i ∈ T ↔ i ∈ S) :
      S.map σ.toEmbedding = T ∧ (Sᶜ).map σ.toEmbedding = Tᶜ := by
    constructor
    · ext i
      simpa only [Finset.mem_map_equiv, Equiv.apply_symm_apply] using (h (σ.symm i)).symm
    · ext i
      simpa only [Finset.mem_map_equiv, Finset.mem_compl, Equiv.apply_symm_apply] using
        not_congr (h (σ.symm i)).symm
  obtain ⟨hALeft, hARight⟩ := mapSides (S := A) (T := A₀) (fun i => by
    have hi := congrArg Prod.fst (hσ i)
    change decide (σ i ∈ A₀) = decide (i ∈ A) at hi
    exact decide_eq_decide.mp hi)
  obtain ⟨hCLeft, hCRight⟩ := mapSides (S := C) (T := B₀) (fun i => by
    have hi := congrArg Prod.snd (hσ i)
    change decide (σ i ∈ B₀) = decide (i ∈ C) at hi
    exact decide_eq_decide.mp hi)
  have hLeft : A₀ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  refine ⟨σ, hALeft, hARight.trans hLeft, ?_⟩
  have hRight : B₀ᶜ = ({2, 4, 5} : Finset (Fin 6)) := by decide
  rw [hRight] at hCRight
  rcases hside with hCB | hCB
  · rw [hCB] at hCLeft hCRight
    exact Or.inl ⟨hCLeft, hCRight⟩
  · rw [hCB] at hCLeft
    rw [hCB, compl_compl] at hCRight
    exact Or.inr ⟨hCRight, hCLeft⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6TwoSplitRelabel

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9LaurentCommonTriple

open Finset
open BalancedCriticalSpectrum (Q)

/-- An ordering of a triple extends to a chart for the whole cube. -/
theorem exists_chart (S : Finset (Fin 9)) (hS : S.card = 3) : ∃ e : Axes, commonAxes e = S := by
  classical
  have hSc : (Sᶜ).card = 6 := by rw [card_compl, Fintype.card_fin, hS]
  let l : Fin 3 ≃ ↥S := (S.equivFinOfCardEq hS).symm
  let r : Fin 6 ≃ ↥(Sᶜ) := ((Sᶜ).equivFinOfCardEq hSc).symm
  let f : ↥(Sᶜ) ≃ {i : Fin 9 // i ∉ S} := Equiv.subtypeEquivRight (fun _ => mem_compl)
  let e : Axes := (Equiv.sumCongr l (r.trans f)).trans (Equiv.sumCompl (· ∈ S))
  refine ⟨e, ?_⟩
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact (l j).property
  · intro hi
    exact mem_image.mpr ⟨l.symm ⟨i, hi⟩, mem_univ _, by
      change (l (l.symm ⟨i, hi⟩)).val = i
      rw [Equiv.apply_symm_apply]⟩

/-- Extend a specified ordering of three distinct axes. -/
theorem exists_ordered_chart (l : Fin 3 ↪ Fin 9) :
    ∃ e : Axes, ∀ j : Fin 3, e (.inl j) = l j := by
  classical
  let S := (univ : Finset (Fin 3)).map l
  have hS : S.card = 3 := by simp [S]
  have hSc : (Sᶜ).card = 6 := by rw [card_compl, Fintype.card_fin, hS]
  let L : Fin 3 ≃ ↥S := Equiv.ofBijective
    (fun i => ⟨l i, mem_map.mpr ⟨i, mem_univ _, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact l.injective (congrArg Subtype.val h)
      · intro j
        obtain ⟨i, _, hi⟩ := mem_map.mp j.property
        exact ⟨i, Subtype.ext hi⟩)
  let R : Fin 6 ≃ ↥(Sᶜ) := ((Sᶜ).equivFinOfCardEq hSc).symm
  let f : ↥(Sᶜ) ≃ {i : Fin 9 // i ∉ S} := Equiv.subtypeEquivRight (fun _ => mem_compl)
  exact ⟨(Equiv.sumCongr L (R.trans f)).trans (Equiv.sumCompl (· ∈ S)), fun _ => rfl⟩

private theorem inside_iff {e : Axes} {x y : Q 9} :
    inside e x = inside e y ↔ ∀ i ∈ commonAxes e, x i = y i := by
  constructor
  · intro h i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact congrFun h j
  · intro h
    funext j
    exact h _ (mem_image.mpr ⟨j, mem_univ _, rfl⟩)

private theorem outside_iff {e : Axes} {x y : Q 9} :
    outside e x = outside e y ↔ ∀ i, i ∉ commonAxes e → x i = y i := by
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j => exact (hi (mem_image.mpr ⟨j, mem_univ _, rfl⟩)).elim
    | inr j => exact congrFun h j
  · intro h
    funext j
    apply h
    intro hj
    obtain ⟨i, _, hi⟩ := mem_image.mp hj
    exact Sum.inl_ne_inr (e.injective hi)

/-- On a fixed shared pattern, matching outside one complementary block
is equivalent to matching inside the other complementary block. -/
theorem outside_eq_iff_inside_of_partition {eS eL eR : Axes} {x y : Q 9}
    (hcover : commonAxes eS ∪ commonAxes eL ∪ commonAxes eR = univ)
    (hdisj : Disjoint (commonAxes eL) (commonAxes eR)) (hS : inside eS x = inside eS y) :
    outside eL x = outside eL y ↔ inside eR x = inside eR y := by
  rw [outside_iff, inside_iff]
  constructor
  · intro h i hi
    exact h i (fun hl => disjoint_left.mp hdisj hl hi)
  · intro h i hi
    have hmem : i ∈ commonAxes eS ∪ commonAxes eL ∪ commonAxes eR := by
      rw [hcover]
      exact mem_univ _
    rcases mem_union.mp hmem with hs | hr
    · rcases mem_union.mp hs with hs | hl
      · exact inside_iff.mp hS i hs
      · exact (hi hl).elim
    · exact h i hr


end Q9LaurentCommonTriple
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9ProjectedHeightCompatibility

open Finset
open BalancedCriticalSpectrum (Q)
open Q9LaurentCommonTriple (Axes commonAxes inside outside exists_ordered_chart)

/-- The left triple of each normalized partition. -/
def leftIndex (p : Bool) (i : Fin 3) : Fin 6 := ![0, 1, if p then 3 else 2] i

/-- The right triple of each normalized partition. -/
def rightIndex (p : Bool) (i : Fin 3) : Fin 6 := ![if p then 2 else 3, 4, 5] i

private theorem leftIndex_injective (p : Bool) : Function.Injective (leftIndex p) := by
  cases p <;> decide +kernel

private theorem rightIndex_injective (p : Bool) : Function.Injective (rightIndex p) := by
  cases p <;> decide +kernel

/-- These two triples partition the six coordinates. -/
theorem index_dichotomy (p : Bool) (j : Fin 6) :
    (∃ i, leftIndex p i = j) ∨ (∃ i, rightIndex p i = j) := by
  revert j
  cases p <;> decide +kernel

/-- The two triples of a split are disjoint. -/
theorem leftIndex_ne_rightIndex (p : Bool) (i j : Fin 3) : leftIndex p i ≠ rightIndex p j := by
  revert i j
  cases p <;> decide +kernel

/-- The original-axis triple corresponding to one normalized half. -/
def embeddedAxes (e : Axes) (index : Fin 3 → Fin 6) : Finset (Fin 9) :=
  univ.image fun i => e (.inr (index i))

/-- A chart respecting the order of the chosen half of a normalized split. -/
theorem exists_embedded_chart (e : Axes) (index : Fin 3 → Fin 6)
    (hi : Function.Injective index) :
    ∃ f : Axes, (∀ i : Fin 3, f (.inl i) = e (.inr (index i))) ∧
      commonAxes f = embeddedAxes e index := by
  let l : Fin 3 ↪ Fin 9 := ⟨fun i => e (.inr (index i)), e.injective.comp (Sum.inr_injective.comp hi)⟩
  obtain ⟨f, hf⟩ := exists_ordered_chart l
  refine ⟨f, hf, ?_⟩
  unfold commonAxes embeddedAxes
  apply congrArg (fun funMap : Fin 3 → Fin 9 => univ.image funMap)
  exact funext hf

/-- A normalized split of the transverse axes can be lifted to ordered charts
for both original triples. -/
theorem exists_split_charts (e : Axes) (p : Bool) :
    ∃ l r : Axes,
      (∀ i : Fin 3, l (.inl i) = e (.inr (leftIndex p i))) ∧
      (∀ i : Fin 3, r (.inl i) = e (.inr (rightIndex p i))) ∧
      commonAxes l = embeddedAxes e (leftIndex p) ∧ commonAxes r = embeddedAxes e (rightIndex p) := by
  obtain ⟨l, hl, hlAxes⟩ := exists_embedded_chart e (leftIndex p) (leftIndex_injective p)
  obtain ⟨r, hr, hrAxes⟩ := exists_embedded_chart e (rightIndex p) (rightIndex_injective p)
  exact ⟨l, r, hl, hr, hlAxes, hrAxes⟩

private theorem leftPart_get (p : Bool) (x : Point) (i : Fin 3) :
    (leftPart p x).getLsbD i.val = x.getLsbD (leftIndex p i).val := by
  fin_cases i <;> cases p <;>
    simp only [leftPart, BitVec.getLsbD_ofBoolListLE, Bool.false_eq_true, ite_false, ite_true] <;> rfl

private theorem rightPart_get (p : Bool) (x : Point) (i : Fin 3) :
    (rightPart p x).getLsbD i.val = x.getLsbD (rightIndex p i).val := by
  fin_cases i <;> cases p <;>
    simp only [rightPart, BitVec.getLsbD_ofBoolListLE, Bool.false_eq_true, ite_false, ite_true] <;> rfl

/-- Restricting a projected point to a normalized block agrees with the
original cube's ordered chart on that block. -/
theorem leftPart_projection (e l : Axes) (p : Bool)
    (hl : ∀ i : Fin 3, l (.inl i) = e (.inr (leftIndex p i))) (x : Q 9) :
    leftPart p ((cubeBitVec 6).symm (outside e x)) = (cubeBitVec 3).symm (inside l x) := by
  apply (cubeBitVec 3).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change (leftPart p ((cubeBitVec 6).symm (outside e x))).getLsbD i.val = x (l (.inl i))
  rw [leftPart_get, hl]
  exact congrFun (Equiv.apply_symm_apply (cubeBitVec 6) (outside e x)) (leftIndex p i)

theorem rightPart_projection (e r : Axes) (p : Bool)
    (hr : ∀ i : Fin 3, r (.inl i) = e (.inr (rightIndex p i))) (x : Q 9) :
    rightPart p ((cubeBitVec 6).symm (outside e x)) = (cubeBitVec 3).symm (inside r x) := by
  apply (cubeBitVec 3).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change (rightPart p ((cubeBitVec 6).symm (outside e x))).getLsbD i.val = x (r (.inl i))
  rw [rightPart_get, hr]
  exact congrFun (Equiv.apply_symm_apply (cubeBitVec 6) (outside e x)) (rightIndex p i)


end Q9ProjectedHeightCompatibility
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open Q9LaurentCommonTriple (Axes commonAxes exists_chart)
open Q9ProjectedHeightCompatibility (leftIndex rightIndex embeddedAxes)
open private mem_of_disjoint_from_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes
open Q9ProjectedHeightCompatibility (leftIndex_injective rightIndex_injective)

/-- The three blocks of a normalized neighbor partition. -/
def normalizedPartition (e : Axes) (p : Bool) : Partition :=
  {commonAxes e, embeddedAxes e (leftIndex p), embeddedAxes e (rightIndex p)}

private def transverseAxes (e : Axes) : Fin 6 ↪ Fin 9 := ⟨fun j => e (.inr j),
  e.injective.comp Sum.inr_injective⟩

private def inTransverse (e : Axes) (B : Block) : Finset (Fin 6) :=
  univ.filter fun j => transverseAxes e j ∈ B

private theorem map_transverse {e : Axes} {B : Block} (h : Disjoint B (commonAxes e)) :
    (inTransverse e B).map (transverseAxes e) = B := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    exact (mem_filter.mp hj).2
  · intro hi
    obtain ⟨a, rfl⟩ := e.surjective i
    cases a with
    | inl j => exact (disjoint_left.mp h hi (mem_image.mpr ⟨j, mem_univ _, rfl⟩)).elim
    | inr j => exact mem_map.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩

private theorem exists_other {P : Partition} {S : Block} (hP : IsTriplePartition P) (hS : S ∈ P) :
    ∃ A ∈ P, A ≠ S := by
  have hlt : ({S} : Partition).card < P.card := by simp [hP.card_eq]
  obtain ⟨A, hA, hne⟩ := exists_mem_notMem_of_card_lt_card hlt
  exact ⟨A, hA, fun he => hne (mem_singleton.mpr he)⟩

private theorem normalizedDisjoint (e : Axes) (p : Bool) :
    Disjoint (embeddedAxes e (leftIndex p)) (embeddedAxes e (rightIndex p)) := by
  refine disjoint_left.mpr ?_
  intro i hi hj
  obtain ⟨a, _, ha⟩ := mem_image.mp hi
  obtain ⟨b, _, hb⟩ := mem_image.mp hj
  exact Q9ProjectedHeightCompatibility.leftIndex_ne_rightIndex p a b
    (Sum.inr.inj (e.injective (ha.trans hb.symm)))

/-- Distinct triple partitions with one common block are the two normalized
partitions under one chart of the nine original coordinates. -/
theorem exists_normalized_partitions {P R : Partition} {S : Block}
    (hP : IsTriplePartition P) (hR : IsTriplePartition R)
    (hSP : S ∈ P) (hSR : S ∈ R) (hne : P ≠ R) :
    ∃ e : Axes, commonAxes e = S ∧
      normalizedPartition e false = P ∧ normalizedPartition e true = R := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_chart S (hP.block_card S hSP)
  obtain ⟨A, hAP, hAS⟩ := exists_other hP hSP
  obtain ⟨B, hBR, hBS⟩ := exists_other hR hSR
  have hAd : Disjoint A (commonAxes e₀) := he₀.symm ▸ hP.disjoint_blocks hAP hSP hAS
  have hBd : Disjoint B (commonAxes e₀) := he₀.symm ▸ hR.disjoint_blocks hBR hSR hBS
  let A' := inTransverse e₀ A
  let B' := inTransverse e₀ B
  have hAm : A'.map (transverseAxes e₀) = A := map_transverse hAd
  have hBm : B'.map (transverseAxes e₀) = B := map_transverse hBd
  have hAc : A'.card = 3 := by rw [← card_map (f := transverseAxes e₀), hAm, hP.block_card A hAP]
  have hBc : B'.card = 3 := by rw [← card_map (f := transverseAxes e₀), hBm, hR.block_card B hBR]
  have hBA : B' ≠ A' := by
    intro he
    have hAB : A = B := hAm.symm.trans ((congrArg (fun t => t.map (transverseAxes e₀)) he.symm).trans hBm)
    exact hne (eq_of_two_common_blocks hP hR hAP hSP (hAB.symm ▸ hBR) hSR hAS)
  have hBAc : B' ≠ A'ᶜ := by
    intro he
    have hAB : Disjoint A B := by
      rw [← hAm, ← hBm, he]
      exact (Finset.disjoint_map (transverseAxes e₀)).mpr disjoint_compl_right
    have hBP : B ∈ P := by
      exact mem_of_disjoint_from_two hP hSP hAP hAS.symm (hR.block_card B hBR)
        (hR.disjoint_blocks hBR hSR hBS) hAB.symm
    exact hne (eq_of_two_common_blocks hP hR hBP hSP hBR hSR hBS)
  obtain ⟨σ, hA₁, hA₂, hB⟩ := Q6TwoSplitRelabel.exists_relabel_two_splits hAc hBc hBA hBAc
  let e : Axes := (Equiv.sumCongr (Equiv.refl _) σ.symm).trans e₀
  have he : commonAxes e = S := he₀
  have hcast (T : Finset (Fin 6)) : (T.map σ.toEmbedding).map (transverseAxes e) =
      T.map (transverseAxes e₀) := by
    ext i
    simp only [mem_map]
    constructor
    · rintro ⟨j, ⟨k, hk, rfl⟩, hi⟩
      refine ⟨k, hk, ?_⟩
      change e₀ (.inr (σ.symm (σ k))) = i at hi
      rwa [Equiv.symm_apply_apply] at hi
    · rintro ⟨k, hk, rfl⟩
      refine ⟨σ k, ⟨k, hk, rfl⟩, ?_⟩
      change e₀ (.inr (σ.symm (σ k))) = e₀ (.inr k)
      rw [Equiv.symm_apply_apply]
  have hpart (T : Partition) (hT : IsTriplePartition T) (hST : S ∈ T) (D : Block) (hDT : D ∈ T)
      (p : Bool) (hD : D = embeddedAxes e (leftIndex p) ∨ D = embeddedAxes e (rightIndex p)) :
      normalizedPartition e p = T := by
    have hCard (f : Fin 3 → Fin 6) (hf : Function.Injective f) : (embeddedAxes e f).card = 3 := by
      rw [embeddedAxes, card_image_of_injective, card_univ, Fintype.card_fin]
      exact e.injective.comp (Sum.inr_injective.comp hf)
    have hLeft := hCard (leftIndex p) (leftIndex_injective p)
    have hRight := hCard (rightIndex p) (rightIndex_injective p)
    have hSdis (f : Fin 3 → Fin 6) : Disjoint (embeddedAxes e f) S := by
      rw [← he]
      refine disjoint_left.mpr ?_
      intro i hi hj
      obtain ⟨j, _, hj'⟩ := mem_image.mp hi
      obtain ⟨k, _, hk⟩ := mem_image.mp hj
      exact Sum.inr_ne_inl (e.injective (hj'.trans hk.symm))
    have hNe (f : Fin 3 → Fin 6) (hc : (embeddedAxes e f).card = 3) : embeddedAxes e f ≠ S := by
      intro h
      obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < (embeddedAxes e f).card)
      exact disjoint_left.mp (hSdis f) hi (h ▸ hi)
    rw [normalizedPartition, he]
    apply eq_of_subset_of_card_le
    · intro E hE
      simp only [mem_insert, mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact hST
      · rcases hD with hD | hD
        · exact hD ▸ hDT
        · exact mem_of_disjoint_from_two hT hST (hD ▸ hDT) (hNe _ hRight).symm
            hLeft (hSdis _) (normalizedDisjoint e p)
      · rcases hD with hD | hD
        · exact mem_of_disjoint_from_two hT hST (hD ▸ hDT) (hNe _ hLeft).symm
            hRight (hSdis _) (normalizedDisjoint e p).symm
        · exact hD ▸ hDT
    · rw [hT.card_eq, card_insert_of_notMem, card_pair]
      · intro hEq
        obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < (embeddedAxes e (leftIndex p)).card)
        exact disjoint_left.mp (normalizedDisjoint e p) hi (hEq ▸ hi)
      · simp only [mem_insert, mem_singleton]
        exact fun he => he.elim (hNe _ hLeft).symm (hNe _ hRight).symm
  have normalize (T : Finset (Fin 6)) (f : Fin 3 → Fin 6)
      (hT : T.map σ.toEmbedding = univ.image f) : T.map (transverseAxes e₀) = embeddedAxes e f := by
    rw [← hcast, hT]
    ext i
    simp [embeddedAxes, transverseAxes, mem_map, mem_image]
  have hAL : A = embeddedAxes e (leftIndex false) := by
    rw [← hAm]
    apply normalize A' (leftIndex false)
    exact hA₁.trans (by decide)
  have hBR' : B = embeddedAxes e (leftIndex true) ∨ B = embeddedAxes e (rightIndex true) := by
    rcases hB with hB | hB
    · left
      rw [← hBm]
      exact normalize B' (leftIndex true) (hB.1.trans (by decide))
    · right
      rw [← hBm]
      exact normalize B' (rightIndex true) (hB.1.trans (by decide))
  exact ⟨e, he, hpart P hP hSP A hAP false (Or.inl hAL), hpart R hR hSR B hBR true hBR'⟩


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open Q9LaurentCommonTriple (Axes commonAxes inside outside outside_eq_iff_inside_of_partition)
open Q9ProjectedHeightCompatibility
open private exists_transverseSide_of_selected_mem from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers
open Q9ProjectedHeightCompatibility (leftPart_get rightPart_get)
open Q9ProjectedHeightCompatibility (left_xor right_xor parts_of_join)
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private theorem join_parts_checked (p : Bool) : ∀ x : Fin 64,
    joinParts p (leftPart p (BitVec.ofFin x)) (rightPart p (BitVec.ofFin x)) = BitVec.ofFin x := by
  cases p <;> decide +kernel

private theorem eq_of_parts {p : Bool} {u v : Point} (hl : leftPart p u = leftPart p v)
    (hr : rightPart p u = rightPart p v) : u = v := by
  have hu := join_parts_checked p u.toFin
  have hv := join_parts_checked p v.toFin
  change joinParts p (leftPart p u) (rightPart p u) = u at hu
  change joinParts p (leftPart p v) (rightPart p v) = v at hv
  rw [hl, hr, hv] at hu
  exact hu.symm

private theorem lift_mem_transverse {C : Finset (Q 9)} {b : Bool} {S : Block} {root : Side C b}
    (x : Side (transverseSupport S root) b) : liftTransverse x ∈ transverseSide S root := by
  obtain ⟨y, hy, he⟩ := exists_transverseSide_of_selected_mem x
  exact (Subtype.ext he : y = liftTransverse x) ▸ hy

private theorem mem_transverseSupport_of_side {C : Finset (Q 9)} {b : Bool} {S : Block}
    {root x : Side C b} (hx : x ∈ transverseSide S root) : x.val ∈ transverseSupport S root := by
  classical
  exact mem_union_left _ (mem_image.mpr ⟨x, hx, rfl⟩)

set_option maxHeartbeats 3000000 in
-- The proof applies the product theorem in two chart subtypes and checks its normalized bit encoding.
open scoped Classical in
/-- An actual component after removal of the common triple is one box in
its normalized split, and the original Laurent exponent gives its box height. -/
theorem realize_normalized_component {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (h : LaurentIdentity a)
    (e : Axes) (hpart0 : IsTriplePartition (normalizedPartition e false))
    (hpart1 : IsTriplePartition (normalizedPartition e true))
    (hinter : normalizedPartition e false ∩ normalizedPartition e true = {commonAxes e})
    (htypes : ∀ x : Side C b, neighborPartition C x.val = normalizedPartition e false ∨
      neighborPartition C x.val = normalizedPartition e true)
    (height : Point → Fin 6 → ℤ)
    (hheight : ∀ (x : Side C b) (j : Fin 6),
      height ((cubeBitVec 6).symm (outside e x.val)) j = a x (e (.inr j)))
    (root : Side C b) (p : Bool) (hroot : neighborPartition C root.val = normalizedPartition e p) :
    ∃ c : Point, HasBoxHeight height p c ∧ ∀ x : Point, inBox p c x = true ↔
      ∃ y ∈ transverseSide (commonAxes e) root, (cubeBitVec 6).symm (outside e y.val) = x := by
  classical
  obtain ⟨l, r, hl, hr, hlAxes, hrAxes⟩ := exists_split_charts e p
  let S := commonAxes e
  let T := transverseSupport S root
  have hSP (q : Bool) : S ∈ normalizedPartition e q := by simp [S, normalizedPartition]
  have hparts (q : Bool) : IsTriplePartition (normalizedPartition e q) := by
    cases q
    · exact hpart0
    · exact hpart1
  have hlabel (x : Side C b) (hx : x ∈ transverseSide S root) :
      neighborPartition C x.val = normalizedPartition e p :=
    (neighborPartition_eq_of_transverse_path hinter htypes (mem_transverseSide.mp hx)).symm.trans hroot
  have hlMem : commonAxes l ∈ normalizedPartition e p := by simp [normalizedPartition, hlAxes]
  have hrMem : commonAxes r ∈ normalizedPartition e p := by simp [normalizedPartition, hrAxes]
  have hdisS (f : Axes) (ind : Fin 3 → Fin 6) (hf : ∀ i, f (.inl i) = e (.inr (ind i))) :
      Disjoint (commonAxes f) S := by
    apply disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i, _, hi⟩ := mem_image.mp hj
    obtain ⟨k, _, hk⟩ := mem_image.mp hj'
    rw [hf] at hi
    exact Sum.inr_ne_inl (e.injective (hi.trans hk.symm))
  have hlStar : Q9LaurentCommonTriple.UniqueCommonNeighbor T b l :=
    uniqueCommonNeighbor_transverse hC h hpart0 hpart1 (hSP false) (hSP true) htypes
      (hdisS l (leftIndex p) hl) (fun x hx => hlabel x hx ▸ hlMem)
  have hrStar : Q9LaurentCommonTriple.UniqueCommonNeighbor T b r :=
    uniqueCommonNeighbor_transverse hC h hpart0 hpart1 (hSP false) (hSP true) htypes
      (hdisS r (rightIndex p) hr) (fun x hx => hlabel x hx ▸ hrMem)
  have hpar (f : Axes) (hf : commonAxes f ∈ normalizedPartition e p) (x : Side T b) :
      cubeParity (inside f x.val) = cubeParity (inside f root.val) :=
    blockParity_eq_on_transverseSide (fun y hy => hlabel y hy ▸ hparts p)
      (fun y hy => hlabel y hy ▸ hf) (lift_mem_transverse x)
  have hs (x : Side T b) : inside e x.val = inside e root.val :=
    inside_eq_on_transverseSide rfl (lift_mem_transverse x)
  have hD (i j : Fin 3) : r (.inl i) ≠ l (.inl j) := by
    rw [hr, hl]
    exact fun hEq => leftIndex_ne_rightIndex p j i (Sum.inr.inj (e.injective hEq.symm))
  have hdis : Disjoint (commonAxes l) (commonAxes r) := by
    apply disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i, _, hi⟩ := mem_image.mp hj
    obtain ⟨k, _, hk⟩ := mem_image.mp hj'
    exact hD k i (hk.trans hi.symm)
  have hcover : commonAxes e ∪ commonAxes l ∪ commonAxes r = univ := by
    ext i
    simp only [mem_univ, iff_true]
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j =>
      have hj : e (.inl j) ∈ commonAxes e := mem_image.mpr ⟨j, mem_univ _, rfl⟩
      exact mem_union_left _ (mem_union_left _ hj)
    | inr j =>
      rcases index_dichotomy p j with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hj : e (.inr j) ∈ commonAxes l := by
          exact mem_image.mpr ⟨k, mem_univ _, (hl k).trans (congrArg (fun j => e (.inr j)) hk)⟩
        exact mem_union_left _ (mem_union_right _ hj)
      · have hj : e (.inr j) ∈ commonAxes r := by
          exact mem_image.mpr ⟨k, mem_univ _, (hr k).trans (congrArg (fun j => e (.inr j)) hk)⟩
        exact mem_union_right _ hj
  have hcover' : commonAxes e ∪ commonAxes r ∪ commonAxes l = univ := by
    rw [union_right_comm, hcover]
  have hL (x y : Side T b) : outside l x.val = outside l y.val ↔ inside r x.val = inside r y.val :=
    outside_eq_iff_inside_of_partition hcover hdis ((hs x).trans (hs y).symm)
  have hR (x y : Side T b) : outside r x.val = outside r y.val ↔ inside l x.val = inside l y.val :=
    outside_eq_iff_inside_of_partition hcover' hdis.symm ((hs x).trans (hs y).symm)
  have hbMem : root ∈ transverseSide S root := mem_transverseSide.mpr .refl
  let base : Side T b := ⟨root.val, mem_transverseSupport_of_side hbMem, root.property.2⟩
  obtain ⟨c, d, hprod⟩ := actual_transverse_star_product h l r _ _ base hlStar hrStar
    (hpar l hlMem) (hpar r hrMem) hL hR hD
  obtain ⟨kr, hkr⟩ := right_height_on_transverse_product h l r base c d hlStar hrStar hL hR hD hprod
  have hswap (u v : BitVec 3) :
      Q3StarHeight.isLeaf d u = true ∧ Q3StarHeight.isLeaf c v = true ↔
        ∃ x : Side T b, (cubeBitVec 3).symm (inside r x.val) = u ∧
          (cubeBitVec 3).symm (inside l x.val) = v := by
    constructor
    · intro hleaf
      obtain ⟨x, hx, hy⟩ := (hprod v u).mp hleaf.symm
      exact ⟨x, hy, hx⟩
    · rintro ⟨x, hx, hy⟩
      exact ((hprod v u).mpr ⟨x, hy, hx⟩).symm
  obtain ⟨kl, hkl⟩ := right_height_on_transverse_product h r l base d c hrStar hlStar hR hL
    (fun i j he => hD j i he.symm) hswap
  let center := joinParts p c d
  have hcenterL : leftPart p center = c := (parts_of_join p c.toFin d.toFin).1
  have hcenterR : rightPart p center = d := (parts_of_join p c.toFin d.toFin).2
  have hbox (v : Point) : inBox p center v = true ↔ ∃ x : Side T b,
      (cubeBitVec 6).symm (outside e x.val) = v := by
    rw [inBox_joinParts_iff, hprod]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, eq_of_parts ((leftPart_projection e l p hl _).trans hx)
        ((rightPart_projection e r p hr _).trans hy)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (leftPart_projection e l p hl _).symm, (rightPart_projection e r p hr _).symm⟩
  let off (j : Fin 6) : ℤ :=
    if hl' : ∃ i, leftIndex p i = j then kl hl'.choose else
      kr ((index_dichotomy p j).resolve_left hl').choose
  refine ⟨center, ⟨off, ?_⟩, ?_⟩
  · intro v hv j
    obtain ⟨x, rfl⟩ := (hbox v).mp hv
    let w := (cubeBitVec 6).symm (outside e x.val)
    have hw : height w j = a (liftTransverse x) (e (.inr j)) := hheight (liftTransverse x) j
    change height w j = off j + ((w ^^^ center).getLsbD j.val).toNat
    rw [hw]
    by_cases hLeft : ∃ i, leftIndex p i = j
    · let i := hLeft.choose
      have hi : leftIndex p i = j := hLeft.choose_spec
      have hval := hkl x i
      rw [hl, hi, ← leftPart_projection e l p hl, ← hcenterL, BitVec.xor_comm, ← left_xor,
        leftPart_get, hi] at hval
      exact hval.trans (by simp only [off, dite_eq_left hLeft, i]; rfl)
    · let hRight := (index_dichotomy p j).resolve_left hLeft
      let i := hRight.choose
      have hi : rightIndex p i = j := hRight.choose_spec
      have hval := hkr x i
      rw [hr, hi, ← rightPart_projection e r p hr, ← hcenterR, BitVec.xor_comm, ← right_xor,
        rightPart_get, hi] at hval
      exact hval.trans (by simp only [off, dite_eq_right hLeft, i]; rfl)
  · intro v
    rw [hbox]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨liftTransverse x, lift_mem_transverse x, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, mem_transverseSupport_of_side hx, x.property.2⟩, rfl⟩


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
