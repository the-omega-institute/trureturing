/- GID: D5/S3/Geometry/ProbabilityTransport/AlternatingArrayContraction
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/AlternatingArrayContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite alternating-array energy and contraction for weighted minors -/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
theorem energy (z : ι → ℝ) {v : ι → ι → ℝ} (hv : Skew v) :
    mass₃ (lift z v) + (∑ i, contract z v i ^ 2) =
      (∑ k, z k ^ 2) * mass₂ v := by
  have h := energy_raw z hv
  unfold mass₂ mass₃
  linarith

/-- Contraction of actual alternating three-arrays by a unit vector. -/
theorem contraction (z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
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

private theorem pair_skew (x y : ι → ℝ) : Skew (pairMinor x y) := by
  intro i j
  unfold pairMinor
  ring

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
theorem recover_minors (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
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
theorem family_domination (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
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

end AlternatingArrayContraction
