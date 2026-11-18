/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual derivative defects and good records control retained endpoint moments. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalGoodRecordCount
import Mathlib.Data.Finset.Lattice.Fold

/-! Count actual retained endpoint pairs and their derivative defects. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def taggedRecords {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (F : α → Finset β) : Finset (α × β) :=
  s.biUnion fun a => (F a).image fun b => (a, b)

private theorem mem_taggedRecords {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {F : α → Finset β} {a : α} {b : β} :
    (a, b) ∈ taggedRecords s F ↔ a ∈ s ∧ b ∈ F a := by
  simp [taggedRecords]

private theorem taggedRecords_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (F : α → Finset β) :
    (taggedRecords s F).card = ∑ a ∈ s, (F a).card := by
  have hd : (s : Set α).PairwiseDisjoint
      (fun a => (F a).image fun b => (a, b)) := by
    intro a _ a' _ haa
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hz
    obtain ⟨b', _, hb'⟩ := Finset.mem_image.mp hz'
    exact haa ((congrArg Prod.fst hb).trans (congrArg Prod.fst hb').symm)
  rw [taggedRecords, Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)

/-- Actual partners at which the pencil has zero derivative modulo p. -/
def actualRecordBadPartners (p : ℕ) (q R V : Coordinate) (E : Finset Endpoint)
    (base : Endpoint) : Finset Endpoint :=
  E.filter fun e => (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
    ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) (recordBeta (p^3) R V)) = 0

/-- The largest actual derivative-zero fiber, with value zero for an empty chart. -/
def actualRecordBadDegree (p : ℕ) (q R V : Coordinate) (E : Finset Endpoint) : ℕ :=
  E.sup fun base => (actualRecordBadPartners p q R V E base).card

/-- Ordered endpoint pairs with an actual simple root at the physical basis slope. -/
def actualRecordGoodPairs (p : ℕ) (q R V : Coordinate)
    (E : Finset Endpoint) : Finset (Endpoint × Endpoint) :=
  taggedRecords E fun base => E.filter fun e =>
    (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
      ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) (recordBeta (p^3) R V)) ≠ 0

private theorem goodPairs_second_moment (p : ℕ) (q R V : Coordinate)
    (E : Finset Endpoint)
    (hlarge : 2 * actualRecordBadDegree p q R V E ≤ E.card) :
    (E.card : ℝ)^2 ≤ 2 * ((actualRecordGoodPairs p q R V E).card : ℝ) := by
  classical
  let D := actualRecordBadDegree p q R V E
  let good := fun base : Endpoint => E.filter fun e =>
    (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
      ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) (recordBeta (p^3) R V)) ≠ 0
  have hbase (base : Endpoint) (hb : base ∈ E) :
      E.card ≤ (good base).card + D := by
    have hsplit : (actualRecordBadPartners p q R V E base).card +
        (good base).card = E.card :=
      Finset.card_filter_add_card_filter_not (s := E)
        (fun e => (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
          ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
            (recordBeta (p^3) R V)) = 0)
    have hsup : (actualRecordBadPartners p q R V E base).card ≤ D :=
      Finset.le_sup (f := fun base => (actualRecordBadPartners p q R V E base).card) hb
    omega
  have hsum : E.card * E.card ≤ (actualRecordGoodPairs p q R V E).card + E.card * D := by
    calc
      _ = ∑ _base ∈ E, E.card := by simp
      _ ≤ ∑ base ∈ E, ((good base).card + D) := Finset.sum_le_sum hbase
      _ = _ := by rw [Finset.sum_add_distrib]; simp [actualRecordGoodPairs,
        taggedRecords_card, good]
  have hsumR : (E.card : ℝ)^2 ≤
      ((actualRecordGoodPairs p q R V E).card : ℝ) + (E.card : ℝ) * D := by
    rw [pow_two]
    exact_mod_cast hsum
  have hlargeR : 2 * (D : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast hlarge
  nlinarith [mul_nonneg (Nat.cast_nonneg E.card) (sub_nonneg.mpr hlargeR)]

/-- At one bounded coordinate scale, the actual large retained fibers satisfy
a second-moment estimate. The defect threshold is the maximum cardinality of
the actual derivative-zero partner sets, not a supplied counting estimate.
Both endpoints obey the original word and retained unit conditions. -/
theorem actual_large_retained_second_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y J₁ J₂ : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      1 ≤ J₁ → 1 ≤ J₂ → IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt, WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, CoordinateBound J₁ J₂ (q wt)) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ wt ∈ s, 2 * actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) ≤
        (E wt).card) →
      (∑ wt ∈ s, ((E wt).card : ℝ)^2) ≤ C*(p : ℝ)^ε*(9*J₁*J₂)^5 := by
  classical
  obtain ⟨C, hC, hrecords⟩ := actual_bounded_good_record_count ε hε
  refine ⟨2*C, by positivity, ?_⟩
  intro p hp X Y J₁ J₂ a₁ a₂ q RV s E hX hXY hsmall h₁ h₂ ha₁ ha₂
    hred hanchor hlong hr ht hword hunit hqbound hebound hlarge
  let F := fun wt => actualRecordGoodPairs p (q wt) (RV wt).1 (RV wt).2 (E wt)
  let T := taggedRecords s F
  have hT (u : Coordinate × Endpoint × Endpoint) (hu : u ∈ T) :
      u.1 ∈ s ∧ u.2.1 ∈ E u.1 ∧ u.2.2 ∈ E u.1 ∧
      (pencil (q u.1) u.2.1 u.2.2).derivative.eval₂ (Int.castRingHom (ZMod p))
        ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) (recordBeta (p^3) (RV u.1).1 (RV u.1).2)) ≠ 0 := by
    obtain ⟨hs, hf⟩ := mem_taggedRecords.mp hu
    obtain ⟨hb, he⟩ := mem_taggedRecords.mp hf
    obtain ⟨he, hd⟩ := Finset.mem_filter.mp he
    exact ⟨hs, hb, he, hd⟩
  have hgood (u : Coordinate × Endpoint × Endpoint) (hu : u ∈ T) :
      GoodRecordRealization p X Y a₁ a₂ (q u.1) u.2.1 u.2.2
        ((RV u.1).1, (RV u.1).2) := by
    obtain ⟨hs, hb, he, hd⟩ := hT u hu
    have hanc := hanchor u.1 hs
    refine ⟨?_, hlong u.1 hs, hr u.1 hs, ?_, hword u.1 hs _ hb,
      hword u.1 hs _ he, (hunit u.1 hs _ hb).1, (hunit u.1 hs _ hb).2, hd⟩
    · have hant : -(physical (RV u.1).1 (RV u.1).2 (q u.1)).2 = u.1.2 := by
        rw [hanc]
        exact neg_neg _
      have hanw : -(physical (RV u.1).1 (RV u.1).2 (q u.1)).1 = u.1.1 := by
        rw [hanc]
        exact neg_neg _
      rw [hant, hanw]
      exact hred u.1 hs
    · rw [hanc]
      simpa using ht u.1 hs
  have hcount : (T.card : ℝ) ≤ C*(p : ℝ)^ε*(9*J₁*J₂)^5 := by
    apply hrecords p hp X Y J₁ J₂ a₁ a₂ q (fun wt => ((RV wt).1, (RV wt).2)) T
      hX hXY hsmall h₁ h₂ ha₁ ha₂ hgood
    · intro u hu
      exact hanchor u.1 (hT u hu).1
    · intro u hu
      obtain ⟨hs, hb, he, _⟩ := hT u hu
      exact ⟨hqbound u.1 hs, (hebound u.1 hs _ hb).1, (hebound u.1 hs _ hb).2,
        (hebound u.1 hs _ he).1, (hebound u.1 hs _ he).2⟩
  calc
    _ ≤ ∑ wt ∈ s, 2 * ((F wt).card : ℝ) := Finset.sum_le_sum fun wt hw =>
      goodPairs_second_moment p (q wt) (RV wt).1 (RV wt).2 (E wt) (hlarge wt hw)
    _ = 2 * (T.card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast (taggedRecords_card s F).symm
    _ ≤ 2 * (C*(p : ℝ)^ε*(9*J₁*J₂)^5) := mul_le_mul_of_nonneg_left hcount (by norm_num)
    _ = (2*C)*(p : ℝ)^ε*(9*J₁*J₂)^5 := by ring

/-- The full retained endpoint count splits into the actual derivative defect
and the square-root contribution of good records. The small/large partition
and Cauchy--Schwarz are proved for the original integer parameter incidences. -/
theorem actual_retained_endpoint_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y J₁ J₂ : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      1 ≤ J₁ → 1 ≤ J₂ → IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt, WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, CoordinateBound J₁ J₂ (q wt)) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∑ wt ∈ s, ((E wt).card : ℝ)) ≤
        2 * (∑ wt ∈ s,
          (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) +
        Real.sqrt ((s.card : ℝ) * C*(p : ℝ)^ε*(9*J₁*J₂)^5) := by
  classical
  obtain ⟨C, hC, hmoment⟩ := actual_large_retained_second_moment ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y J₁ J₂ a₁ a₂ q RV s E hX hXY hsmall h₁ h₂ ha₁ ha₂
    hred hanchor hlong hr ht hword hunit hqbound hebound
  let D := fun wt => actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt)
  let L := s.filter fun wt => 2 * D wt ≤ (E wt).card
  let S := s.filter fun wt => ¬ 2 * D wt ≤ (E wt).card
  have hrestrict {P : Coordinate → Prop} (h : ∀ wt ∈ s, P wt) : ∀ wt ∈ L, P wt :=
    fun wt hw => h wt (Finset.mem_filter.mp hw).1
  have hsecond : (∑ wt ∈ L, ((E wt).card : ℝ)^2) ≤
      C*(p : ℝ)^ε*(9*J₁*J₂)^5 :=
    hmoment p hp X Y J₁ J₂ a₁ a₂ q RV L E hX hXY hsmall h₁ h₂ ha₁ ha₂
      (hrestrict hred) (hrestrict hanchor) (hrestrict hlong) (hrestrict hr) (hrestrict ht)
      (hrestrict hword) (hrestrict hunit) (hrestrict hqbound) (hrestrict hebound)
      (fun wt hw => (Finset.mem_filter.mp hw).2)
  have hcauchy : (∑ wt ∈ L, ((E wt).card : ℝ))^2 ≤
      (L.card : ℝ) * (∑ wt ∈ L, ((E wt).card : ℝ)^2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => (1 : ℝ)) (fun wt => ((E wt).card : ℝ))
  have hcard : (L.card : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le s (fun wt => 2 * D wt ≤ (E wt).card)
  have hroot : (∑ wt ∈ L, ((E wt).card : ℝ)) ≤
      Real.sqrt ((s.card : ℝ) * C*(p : ℝ)^ε*(9*J₁*J₂)^5) := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ ≤ (L.card : ℝ) * (∑ wt ∈ L, ((E wt).card : ℝ)^2) := hcauchy
      _ ≤ (s.card : ℝ) * (C*(p : ℝ)^ε*(9*J₁*J₂)^5) :=
        mul_le_mul hcard hsecond (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Nat.cast_nonneg _)
      _ = _ := by simp only [mul_assoc]
  have hsmall : (∑ wt ∈ S, ((E wt).card : ℝ)) ≤ 2 * (∑ wt ∈ s, (D wt : ℝ)) := by
    calc
      _ ≤ ∑ wt ∈ S, 2 * (D wt : ℝ) := by
        apply Finset.sum_le_sum
        intro wt hw
        have hh := (Finset.mem_filter.mp hw).2
        exact_mod_cast (show (E wt).card ≤ 2 * D wt by omega)
      _ ≤ ∑ wt ∈ s, 2 * (D wt : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsplit : (∑ wt ∈ s, ((E wt).card : ℝ)) =
      (∑ wt ∈ L, ((E wt).card : ℝ)) + (∑ wt ∈ S, ((E wt).card : ℝ)) := by
    exact (Finset.sum_filter_add_sum_filter_not s _ _).symm
  rw [hsplit]
  exact (add_le_add hroot hsmall).trans_eq (add_comm _ _)

end
end D5.S3.Arith.CharacterSums.Original
