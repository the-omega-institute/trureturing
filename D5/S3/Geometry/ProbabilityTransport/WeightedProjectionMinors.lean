/- GID: D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite alternating-array energy and contraction for weighted minors -/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

/-! Finite coordinate operators use all ordered tuples. Pair and triple squared
norms therefore have multiplicities two and six, respectively. -/

noncomputable section
open scoped BigOperators
namespace AlternatingArrayContraction

variable {ι : Type*} [Fintype ι]

def Skew (v : ι → ι → ℝ) : Prop := ∀ i j, v i j = -v j i

def Alt (b : ι → ι → ι → ℝ) : Prop :=
  (∀ i j k, b j i k = -b i j k) ∧ (∀ i j k, b k i j = b i j k)

def lift (z : ι → ℝ) (v : ι → ι → ℝ) (i j k : ι) : ℝ :=
  z i * v j k - z j * v i k + z k * v i j

def lower (z : ι → ℝ) (b : ι → ι → ι → ℝ) (i j : ι) : ℝ :=
  ∑ k, z k * b k i j

def contract (z : ι → ℝ) (v : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ k, z k * v k i

def mass₂ (v : ι → ι → ℝ) : ℝ := (∑ i, ∑ j, v i j ^ 2) / 2

def mass₃ (b : ι → ι → ι → ℝ) : ℝ := (∑ i, ∑ j, ∑ k, b i j k ^ 2) / 6

private theorem sum_rotate (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f k i j := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem sum_swap (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f j i k) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]

omit [Fintype ι] in
private theorem lift_alt (z : ι → ℝ) {v : ι → ι → ℝ} (hv : Skew v) :
    Alt (lift z v) := by
  constructor
  · intro i j k
    simp only [lift, hv j i]
    ring
  · intro i j k
    simp only [lift, hv k j, hv k i]
    ring

private theorem lower_skew (z : ι → ℝ) {b : ι → ι → ι → ℝ} (hb : Alt b) :
    Skew (lower z b) := by
  intro i j
  unfold lower
  have h : ∀ k, b k i j = -b k j i := by
    intro k
    rw [← hb.2 k i j, hb.1 k j i]
  simp_rw [h, mul_neg, Finset.sum_neg_distrib]

private theorem adjoint (z : ι → ℝ) (v : ι → ι → ℝ)
    {b : ι → ι → ι → ℝ} (hb : Alt b) :
    (∑ i, ∑ j, ∑ k, lift z v i j k * b i j k) =
      3 * ∑ i, ∑ j, v i j * lower z b i j := by
  let f : ι → ι → ι → ℝ := fun i j k => z i * v j k * b i j k
  have h₁ : (∑ i, ∑ j, ∑ k, z j * v i k * b i j k) =
      -(∑ i, ∑ j, ∑ k, f i j k) := by
    calc
      _ = -(∑ i, ∑ j, ∑ k, f j i k) := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        dsimp [f]
        rw [hb.1 i j k]
        ring
      _ = _ := congrArg Neg.neg (sum_swap f)
  have h₂ : (∑ i, ∑ j, ∑ k, z k * v i j * b i j k) =
      ∑ i, ∑ j, ∑ k, f i j k := by
    calc
      _ = ∑ i, ∑ j, ∑ k, f k i j := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        dsimp [f]
        rw [hb.2 i j k]
      _ = _ := sum_rotate f
  have h₃ : (∑ i, ∑ j, v i j * lower z b i j) =
      ∑ i, ∑ j, ∑ k, f i j k := by
    simp only [lower, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ k, z k * v i j * b i j k := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        rw [hb.2 i j k]
        ring
      _ = _ := h₂
  simp only [lift, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [h₁, h₂, h₃]
  dsimp [f]
  ring

private theorem lower_lift (z : ι → ℝ) (v : ι → ι → ℝ) (i j : ι) :
    lower z (lift z v) i j =
      (∑ k, z k ^ 2) * v i j - z i * contract z v j + z j * contract z v i := by
  calc
    _ = ∑ k, (z k ^ 2 * v i j - z i * (z k * v k j) + z j * (z k * v k i)) := by
      apply Finset.sum_congr rfl; intro k _
      dsimp [lift]
      ring
    _ = _ := by
      simp only [contract, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.sum_mul]

private theorem energy_raw (z : ι → ℝ) {v : ι → ι → ℝ} (hv : Skew v) :
    (∑ i, ∑ j, ∑ k, lift z v i j k ^ 2) +
      6 * (∑ i, contract z v i ^ 2) =
      3 * (∑ k, z k ^ 2) * (∑ i, ∑ j, v i j ^ 2) := by
  have h := adjoint z v (lift_alt z hv)
  simp only [← sq] at h
  have cross₁ : (∑ i, ∑ j, v i j * (z i * contract z v j)) =
      ∑ j, contract z v j ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    simp only [pow_two, contract, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    ring
  have cross₂ : (∑ i, ∑ j, v i j * (z j * contract z v i)) =
      -(∑ i, contract z v i ^ 2) := by
    calc
      _ = -(∑ j, ∑ i, v j i * (z j * contract z v i)) := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [hv j i]
        ring
      _ = _ := congrArg Neg.neg cross₁
  simp only [lower_lift, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at h
  rw [cross₁, cross₂] at h
  have diag : (∑ i, ∑ j, v i j * ((∑ k, z k ^ 2) * v i j)) =
      (∑ k, z k ^ 2) * (∑ i, ∑ j, v i j ^ 2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [diag] at h
  linarith

/-- Coordinate energy identity, including both ordered-tuple multiplicities. -/
private theorem energy (z : ι → ℝ) {v : ι → ι → ℝ} (hv : Skew v) :
    mass₃ (lift z v) + (∑ i, contract z v i ^ 2) =
      (∑ k, z k ^ 2) * mass₂ v := by
  have h := energy_raw z hv
  unfold mass₂ mass₃
  linarith

/-- Contraction of actual alternating three-arrays by a unit vector. -/
private theorem contraction (z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    {b : ι → ι → ι → ℝ} (hb : Alt b) :
    mass₂ (lower z b) ≤ mass₃ b := by
  let d := lower z b
  let D := ∑ i, ∑ j, d i j ^ 2
  let B := ∑ i, ∑ j, ∑ k, b i j k ^ 2
  let Q := ∑ i, ∑ j, ∑ k, lift z d i j k ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : Q ≤ 3 * D := by
    have he := energy z (lower_skew z hb)
    rw [hz] at he
    unfold mass₂ mass₃ at he
    have hk : 0 ≤ ∑ i, contract z d i ^ 2 := by positivity
    dsimp [Q, D, d]
    dsimp [d] at hk
    linarith
  have hi : (∑ i, ∑ j, ∑ k, b i j k * lift z d i j k) = 3 * D := by
    have ha := adjoint z d hb
    simpa only [d, mul_comm, ← sq] using ha
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (ι × ι × ι))
    (fun p => b p.1 p.2.1 p.2.2)
    (fun p => lift z d p.1 p.2.1 p.2.2)
  simp only [Fintype.sum_prod_type] at hcs
  rw [hi] at hcs
  change (3 * D) ^ 2 ≤ B * Q at hcs
  have hm : B * Q ≤ B * (3 * D) := mul_le_mul_of_nonneg_left hQ hB
  have hfinal : 3 * D ≤ B := by
    rcases eq_or_lt_of_le hD with hzero | hpos
    · rw [← hzero]; linarith
    · nlinarith
  change D / 2 ≤ B / 6
  linarith

def pairMinor (x y : ι → ℝ) (i j : ι) : ℝ := x i * y j - x j * y i

def tripleMinor (x y z : ι → ℝ) (i j k : ι) : ℝ :=
  Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]

omit [Fintype ι] in
private theorem pair_skew (x y : ι → ℝ) : Skew (pairMinor x y) := by
  intro i j
  unfold pairMinor
  ring

omit [Fintype ι] in
private theorem triple_lift (x y z : ι → ℝ) :
    tripleMinor x y z = lift z (pairMinor x y) := by
  funext i j k
  simp [tripleMinor, Matrix.det_fin_three, lift, pairMinor]
  <;> ring

private theorem contract_pair (x y z : ι → ℝ) (i : ι) :
    contract z (pairMinor x y) i =
      (∑ k, z k * x k) * y i - (∑ k, z k * y k) * x i := by
  simp only [contract, pairMinor, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

/-- The literal source determinants recover the pair minors under contraction. -/
private theorem recover_minors (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0) :
    lower z (tripleMinor x y z) = pairMinor x y := by
  rw [triple_lift]
  funext i j
  rw [lower_lift, hz, contract_pair, contract_pair, hzx, hzy]
  ring

def pairProjection (F : ι → ι → Prop) [DecidableRel F]
    (v : ι → ι → ℝ) (i j : ι) : ℝ := if F i j then v i j else 0

def neighborhood (F : ι → ι → Prop) (i j k : ι) : Prop :=
  F i j ∨ F i k ∨ F j k

def tripleProjection (F : ι → ι → Prop) [DecidableRel F]
    (b : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  if F i j ∨ F i k ∨ F j k then b i j k else 0

omit [Fintype ι] in
private theorem projection_alt (F : ι → ι → Prop) [DecidableRel F]
    (hF : ∀ i j, F i j ↔ F j i) {b : ι → ι → ι → ℝ} (hb : Alt b) :
    Alt (tripleProjection F b) := by
  classical
  have hs : ∀ i j k, neighborhood F j i k ↔ neighborhood F i j k := by
    intro i j k
    simp only [neighborhood, hF j i]
    tauto
  have hc : ∀ i j k, neighborhood F k i j ↔ neighborhood F i j k := by
    intro i j k
    simp only [neighborhood, hF k i, hF k j]
    tauto
  constructor
  · intro i j k
    by_cases h : neighborhood F i j k
    · have h' := (hs i j k).mpr h
      dsimp [neighborhood] at h h'
      simp only [tripleProjection, if_pos h, if_pos h', hb.1 i j k]
    · have h' : ¬ neighborhood F j i k := fun hj => h ((hs i j k).mp hj)
      dsimp [neighborhood] at h h'
      simp only [tripleProjection, if_neg h, if_neg h', neg_zero]
  · intro i j k
    by_cases h : neighborhood F i j k
    · have h' := (hc i j k).mpr h
      dsimp [neighborhood] at h h'
      simp only [tripleProjection, if_pos h, if_pos h', hb.2 i j k]
    · have h' : ¬ neighborhood F k i j := fun hj => h ((hc i j k).mp hj)
      dsimp [neighborhood] at h h'
      simp only [tripleProjection, if_neg h, if_neg h']

private theorem projection_locality (z : ι → ℝ) (F : ι → ι → Prop)
    [DecidableRel F] (b : ι → ι → ι → ℝ) :
    pairProjection F (lower z (tripleProjection F b)) =
      pairProjection F (lower z b) := by
  funext i j
  by_cases h : F i j
  · simp only [pairProjection, if_pos h, lower]
    apply Finset.sum_congr rfl; intro k _
    simp [tripleProjection, neighborhood, h]
  · simp [pairProjection, h]

private theorem pair_projection_le (F : ι → ι → Prop) [DecidableRel F]
    (v : ι → ι → ℝ) : mass₂ (pairProjection F v) ≤ mass₂ v := by
  unfold mass₂
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases h : F i j <;> simp [pairProjection, h, sq_nonneg]

/-- Every symmetric pair family is dominated by its triple neighborhood. -/
private theorem family_domination (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0)
    (F : ι → ι → Prop) [DecidableRel F] (hF : ∀ i j, F i j ↔ F j i) :
    mass₂ (pairProjection F (pairMinor x y)) ≤
      mass₃ (tripleProjection F (tripleMinor x y z)) := by
  have hb : Alt (tripleMinor x y z) := by
    rw [triple_lift]
    exact lift_alt z (pair_skew x y)
  calc
    _ = mass₂ (pairProjection F (lower z (tripleProjection F (tripleMinor x y z)))) := by
      rw [projection_locality, recover_minors x y z hz hzx hzy]
    _ ≤ mass₂ (lower z (tripleProjection F (tripleMinor x y z))) := pair_projection_le _ _
    _ ≤ _ := contraction z hz (projection_alt F hF hb)

private theorem threshold_expansion (s : Finset ℝ) (hs : ∀ r ∈ s, 0 ≤ r) :
    ∃ c : ℝ → ℝ, (∀ r, 0 ≤ c r) ∧
      ∀ x ∈ s, (∑ r ∈ s, if r ≤ x then c r else 0) = x := by
  classical
  induction s using Finset.induction_on_max with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a s hlt ih =>
    obtain ⟨c, hc, hrep⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    have ha : a ∉ s := by intro h; exact (lt_irrefl a) (hlt a h)
    by_cases hne : s.Nonempty
    · let m := s.max' hne
      have hm : m ∈ s := Finset.max'_mem s hne
      have hma : m < a := hlt m hm
      have htotal : (∑ r ∈ s, c r) = m := by
        have hr := hrep m hm
        have heq : (∑ r ∈ s, if r ≤ m then c r else 0) = ∑ r ∈ s, c r := by
          apply Finset.sum_congr rfl; intro r hr
          rw [if_pos (Finset.le_max' s r hr)]
        rwa [heq] at hr
      refine ⟨fun r => if r = a then a - m else c r, ?_, ?_⟩
      · intro r
        dsimp only
        split_ifs
        · exact sub_nonneg.mpr hma.le
        · exact hc r
      · intro x hx
        rw [Finset.sum_insert ha]
        have hold : (∑ r ∈ s, if r ≤ x then (if r = a then a - m else c r) else 0) =
            ∑ r ∈ s, if r ≤ x then c r else 0 := by
          apply Finset.sum_congr rfl; intro r hr
          simp only [if_neg (ne_of_lt (hlt r hr))]
        rw [hold]
        rcases Finset.mem_insert.mp hx with hxa | hx
        · subst x
          simp only [le_refl, if_pos, ite_true]
          have hsum : (∑ r ∈ s, if r ≤ a then c r else 0) = ∑ r ∈ s, c r := by
            apply Finset.sum_congr rfl; intro r hr
            rw [if_pos (hlt r hr).le]
          rw [hsum, htotal]
          ring
        · rw [if_neg (not_le.mpr (hlt x hx)), zero_add]
          exact hrep x hx
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      refine ⟨fun r => if r = a then a else 0, ?_, ?_⟩
      · intro r
        dsimp only
        split_ifs
        · exact hs a (by simp)
        · exact le_refl 0
      · intro x hx
        have hxa : x = a := by simpa using hx
        subst x
        simp

private theorem weighted_threshold {α β : Type*} [Fintype α] [Fintype β]
    (a p : α → ℝ) (w q : β → ℝ) (ha : ∀ i, 0 ≤ a i) (hw : ∀ j, 0 ≤ w j)
    (h : ∀ r : ℝ, (∑ i, if r ≤ a i then p i else 0) ≤
      ∑ j, if r ≤ w j then q j else 0) :
    (∑ i, a i * p i) ≤ ∑ j, w j * q j := by
  classical
  let s := Finset.univ.image a ∪ Finset.univ.image w
  have hs : ∀ r ∈ s, 0 ≤ r := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact ha i
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
      exact hw j
  obtain ⟨c, hc, hrep⟩ := threshold_expansion s hs
  have hp : (∑ i, a i * p i) =
      ∑ r ∈ s, c r * (∑ i, if r ≤ a i then p i else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    calc
      _ = (∑ r ∈ s, if r ≤ a i then c r else 0) * p i := by
        rw [hrep (a i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro r _
        split_ifs <;> ring
  have hq : (∑ j, w j * q j) =
      ∑ r ∈ s, c r * (∑ j, if r ≤ w j then q j else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    calc
      _ = (∑ r ∈ s, if r ≤ w j then c r else 0) * q j := by
        rw [hrep (w j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, by simp, rfl⟩))]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro r _
        split_ifs <;> ring
  rw [hp, hq]
  apply Finset.sum_le_sum; intro r _
  exact mul_le_mul_of_nonneg_left (h r) (hc r)

/-- The arbitrary real-weight comparison in ordered-tuple coordinates. -/
private theorem weighted_minors_all_tuples (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 ≤ A i j) :
    3 * (∑ i, ∑ j, A i j * pairMinor x y i j ^ 2) ≤
      ∑ i, ∑ j, ∑ k, max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2 := by
  classical
  have ht (r : ℝ) := family_domination x y z hz hzx hzy
    (fun i j => r ≤ A i j) (fun i j => by rw [hA i j])
  have hthreshold (r : ℝ) :
      (∑ p : ι × ι, if r ≤ A p.1 p.2 then 3 * pairMinor x y p.1 p.2 ^ 2 else 0) ≤
      ∑ p : ι × ι × ι,
        if r ≤ max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2))
        then tripleMinor x y z p.1 p.2.1 p.2.2 ^ 2 else 0 := by
    have h := ht r
    unfold mass₂ mass₃ pairProjection tripleProjection at h
    simp only [Fintype.sum_prod_type]
    have hi (a : ℝ) (P : Prop) [Decidable P] : (if P then a else 0) ^ 2 =
        if P then a ^ 2 else 0 := by split_ifs <;> simp
    simp_rw [hi] at h
    simp only [le_max_iff]
    have hpull : (∑ i, ∑ j, if r ≤ A i j then 3 * pairMinor x y i j ^ 2 else 0) =
        3 * (∑ i, ∑ j, if r ≤ A i j then pairMinor x y i j ^ 2 else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [hpull]
    linarith
  have hw := weighted_threshold
    (fun p : ι × ι => A p.1 p.2)
    (fun p : ι × ι => 3 * pairMinor x y p.1 p.2 ^ 2)
    (fun p : ι × ι × ι => max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2)))
    (fun p : ι × ι × ι => tripleMinor x y z p.1 p.2.1 p.2.2 ^ 2)
    (fun p => hpos _ _)
    (fun p => (hpos p.1 p.2.1).trans (le_max_left _ _)) hthreshold
  simp only [Fintype.sum_prod_type] at hw
  calc
    _ = ∑ i, ∑ j, A i j * (3 * pairMinor x y i j ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ ≤ _ := hw


variable [LinearOrder ι]

private theorem pair_ordering (f : ι → ι → ℝ)
    (hs : ∀ i j, f j i = f i j) (hz : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * (∑ i, ∑ j, if i < j then f i j else 0) := by
  have hp (i j : ι) : f i j = (if i < j then f i j else 0) +
      (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hz]
    · simp [h, not_lt.mpr h.le, hs]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f j i else 0) := by
      calc
        _ = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          exact hp i j
        _ = _ := by simp only [Finset.sum_add_distrib]
    _ = _ := by rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]; ring

private theorem triple_ordering (f : ι → ι → ι → ℝ)
    (hs : ∀ i j k, f j i k = f i j k)
    (hc : ∀ i j k, f k i j = f i j k)
    (hz : ∀ i k, f i i k = 0) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      6 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
  have ht (i j k : ι) : f i k j = f i j k := by rw [← hc i k j, hs j i k]
  have hz' (i k : ι) : f i k i = 0 := by rw [← hc i k i, hz]
  have hz'' (i k : ι) : f k i i = 0 := by rw [hc i i k, hz]
  let g : ι → ι → ι → ℝ := fun i j k => if i < j ∧ i < k then f i j k else 0
  have hp (i j k : ι) : f i j k = g i j k + g j i k + g k i j := by
    by_cases hij : i = j
    · subst j; simp [g, hz, hz'']
    by_cases hik : i = k
    · subst k; simp [g, hz, hz', hs]
    by_cases hjk : j = k
    · subst k; simp [g, hz, hz'', hs]
    rcases lt_or_gt_of_ne hij with hij | hij
    · rcases lt_or_gt_of_ne hik with hik | hik
      · simp [g, hij, hik, not_lt.mpr hij.le, not_lt.mpr hik.le]
      · have hkj := hik.trans hij
        simp [g, hij, hik, hkj, not_lt.mpr hij.le, not_lt.mpr hik.le,
          not_lt.mpr hkj.le, hc i j k]
    · rcases lt_or_gt_of_ne hjk with hjk | hjk
      · simp [g, hij, hjk, not_lt.mpr hij.le, not_lt.mpr hjk.le, hs i j k]
      · have hki := hjk.trans hij
        simp [g, hij, hjk, hki, not_lt.mpr hij.le, not_lt.mpr hjk.le,
          not_lt.mpr hki.le, hc i j k]
  have htotal : (∑ i, ∑ j, ∑ k, f i j k) = 3 * (∑ i, ∑ j, ∑ k, g i j k) := by
    calc
      _ = (∑ i, ∑ j, ∑ k, g i j k) + (∑ i, ∑ j, ∑ k, g j i k) +
          (∑ i, ∑ j, ∑ k, g k i j) := by
        conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [hp]
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        have hswap : (∑ i, ∑ j, ∑ k, g j i k) = ∑ i, ∑ j, ∑ k, g i j k := by
          rw [Finset.sum_comm]
        have hrot : (∑ i, ∑ j, ∑ k, g k i j) = ∑ i, ∑ j, ∑ k, g i j k := by
          calc
            _ = ∑ i, ∑ k, ∑ j, g k i j := by
              apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
        rw [hswap, hrot]; ring
  have hg (i j k : ι) : g i j k =
      (if i < j ∧ j < k then f i j k else 0) +
      (if i < k ∧ k < j then f i k j else 0) := by
    rcases lt_trichotomy j k with hjk | rfl | hjk
    · by_cases hij : i < j
      · simp [g, hij, hjk, hij.trans hjk, not_lt.mpr hjk.le]
      · simp [g, hij, hjk, not_lt.mpr hjk.le]
    · simp [g, ht, hz'']
    · by_cases hik : i < k
      · simp [g, hik, hjk, hik.trans hjk, not_lt.mpr hjk.le, ht]
      · simp [g, hik, hjk, not_lt.mpr hjk.le]
  have hsplit : (∑ i, ∑ j, ∑ k, g i j k) =
      2 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
    have he (i : ι) : (∑ j, ∑ k, g i j k) =
        2 * (∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
      simp_rw [hg]
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j k => if i < k ∧ k < j then f i k j else 0)]
      ring
    simp_rw [he]
    rw [Finset.mul_sum]
  rw [htotal, hsplit]
  ring

/-- The exact increasing-index comparison, with unrestricted real weights. -/
private theorem weighted_minors_coordinates (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 < A i j) :
    (∑ i, ∑ j, if i < j then A i j * pairMinor x y i j ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2 else 0 := by
  let p := fun i j => A i j * pairMinor x y i j ^ 2
  let q := fun i j k => max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2
  have hp : (∑ i, ∑ j, p i j) = 2 * (∑ i, ∑ j, if i < j then p i j else 0) := by
    apply pair_ordering
    · intro i j
      dsimp [p, pairMinor]
      rw [hA j i]
      ring
    · intro i
      simp [p, pairMinor]
  have hb : Alt (tripleMinor x y z) := by
    rw [triple_lift]
    exact lift_alt z (pair_skew x y)
  have hzero (i k : ι) : tripleMinor x y z i i k = 0 := by
    have h := hb.1 i i k
    linarith
  have hq : (∑ i, ∑ j, ∑ k, q i j k) =
      6 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j k else 0) := by
    apply triple_ordering
    · intro i j k
      dsimp [q]
      rw [hA j i, hb.1 i j k, max_comm (A j k) (A i k)]
      ring
    · intro i j k
      dsimp [q]
      rw [hA k i, hA k j, hb.2 i j k]
      congr 1
      simp only [max_assoc, max_left_comm, max_comm]
    · intro i k
      simp only [q, hzero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have h := weighted_minors_all_tuples x y z hz hzx hzy A hA (fun i j => (hpos i j).le)
  change 3 * (∑ i, ∑ j, p i j) ≤ ∑ i, ∑ j, ∑ k, q i j k at h
  rw [hp, hq] at h
  change (∑ i, ∑ j, if i < j then p i j else 0) ≤
    ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j k else 0
  linarith

omit [Fintype ι] [LinearOrder ι] in
/-- The literal MO469781 inequality for an arbitrary real orthonormal triple. -/
theorem weighted_minors {n : ℕ} (x y z : EuclideanSpace ℝ (Fin n))
    (hON : Orthonormal ℝ ![x, y, z])
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, A i j = A j i)
    (hpos : ∀ i j, 0 < A i j) :
    (∑ i, ∑ j, if i < j then A i j * Matrix.det !![x i, x j; y i, y j] ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) *
          Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k] ^ 2 else 0 := by
  have hzn : ‖z‖ = 1 := by simpa using hON.norm_eq_one (2 : Fin 3)
  have hz : ∑ k, z k ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hzn]
    norm_num
  have hzx : ∑ k, z k * x k = 0 := by
    have h := hON.inner_eq_zero (i := (2 : Fin 3)) (j := 0) (by decide)
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h
  have hzy : ∑ k, z k * y k = 0 := by
    have h := hON.inner_eq_zero (i := (2 : Fin 3)) (j := 1) (by decide)
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h
  simpa only [pairMinor, tripleMinor, Matrix.det_fin_two_of] using
    weighted_minors_coordinates (fun i => x i) (fun i => y i) (fun i => z i) hz hzx hzy A hA hpos

#print axioms weighted_minors

end AlternatingArrayContraction
