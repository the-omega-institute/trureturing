/- GID: D5/S3/Arith/GeometricProductSetMinimum
   generality: G
   mirror-B: D5/B/S3/Arith/GeometricProductSetMinimum
   mirror-E: none(waiver:ordered-product-structure)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: A positive real set with minimum product cardinality is a geometric progression. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Pointwise

namespace D5.S3.Arith.GeometricProductSetMinimum

private def gridRow (m j k : ℕ) : ℕ :=
  if k < j then 0 else if k ≤ m then 1 else k - m + 1

private def gridCol (m j k : ℕ) : ℕ :=
  if k < j then k else if k ≤ m then k - 1 else m - 1

private theorem grid_bounds {m j k : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hjm : j ≤ m) (hk : k < 2 * m - 1) :
    gridRow m j k < m ∧ gridCol m j k < m ∧
      gridRow m j k + gridCol m j k = k := by
  unfold gridRow gridCol
  split_ifs <;> omega

private theorem grid_mono {m j a b : ℕ} (hm : 2 ≤ m) (_hj : 1 ≤ j)
    (hjm : j ≤ m) (hab : a < b) (_hb : b < 2 * m - 1) :
    gridRow m j a ≤ gridRow m j b ∧ gridCol m j a ≤ gridCol m j b := by
  unfold gridRow gridCol
  split_ifs <;> omega

private def gridProduct {m : ℕ} (x : Fin m → ℝ) (hm : 2 ≤ m)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (k : Fin (2 * m - 1)) : ℝ :=
  x ⟨gridRow m j k, (grid_bounds hm hj hjm k.isLt).1⟩ *
    x ⟨gridCol m j k, (grid_bounds hm hj hjm k.isLt).2.1⟩

private theorem gridProduct_strictMono {m : ℕ} (x : Fin m → ℝ)
    (hm : 2 ≤ m) (hx : StrictMono x) (hp : ∀ i, 0 < x i)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    StrictMono (gridProduct x hm j hj hjm) := by
  intro a b hab
  obtain ⟨hr, hc⟩ := grid_mono hm hj hjm (show a.val < b.val from hab) b.isLt
  have hs₁ := (grid_bounds hm hj hjm a.isLt).2.2
  have hs₂ := (grid_bounds hm hj hjm b.isLt).2.2
  have hr' : (⟨gridRow m j a, (grid_bounds hm hj hjm a.isLt).1⟩ : Fin m) ≤
      ⟨gridRow m j b, (grid_bounds hm hj hjm b.isLt).1⟩ := hr
  have hc' : (⟨gridCol m j a, (grid_bounds hm hj hjm a.isLt).2.1⟩ : Fin m) ≤
      ⟨gridCol m j b, (grid_bounds hm hj hjm b.isLt).2.1⟩ := hc
  unfold gridProduct
  by_cases h : gridRow m j a < gridRow m j b
  · exact (mul_lt_mul_of_pos_right (hx h) (hp _)).trans_le
      (mul_le_mul_of_nonneg_left (hx.monotone hc') (hp _).le)
  · have hh : gridCol m j a < gridCol m j b := by omega
    exact (mul_le_mul_of_nonneg_right (hx.monotone hr') (hp _).le).trans_lt
      (mul_lt_mul_of_pos_left (hx hh) (hp _))

private theorem gridProduct_mem {A : Finset ℝ} {m : ℕ} (x : Fin m → ℝ)
    (hm : 2 ≤ m) (hA : ∀ i, x i ∈ A) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m)
    (k : Fin (2 * m - 1)) : gridProduct x hm j hj hjm k ∈ A * A := by
  exact Finset.mul_mem_mul (hA _) (hA _)

/-- Positive real sets have at least twice their size minus one distinct products. -/
theorem product_card_lower_bound (A : Finset ℝ) (hp : ∀ a ∈ A, 0 < a)
    (hA : A.Nonempty) : 2 * A.card - 1 ≤ (A * A).card := by
  classical
  by_cases hm : 2 ≤ A.card
  · let x := A.orderEmbOfFin rfl
    have hpos : ∀ i, 0 < x i := fun i => hp _ (A.orderEmbOfFin_mem rfl i)
    let f := gridProduct x hm A.card (by omega) le_rfl
    have hf : StrictMono f := gridProduct_strictMono x hm x.strictMono hpos _ _ _
    have hsub : Finset.univ.image f ⊆ A * A := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact gridProduct_mem x hm (fun i => A.orderEmbOfFin_mem rfl i) _ _ _ i
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hf.injective, Finset.card_univ,
      Fintype.card_fin] using hc
  · have hcard : A.card = 1 := by have := Finset.card_pos.mpr hA; omega
    obtain ⟨a, ha⟩ := hA
    have : 0 < (A * A).card := Finset.card_pos.mpr ⟨a * a, Finset.mul_mem_mul ha ha⟩
    omega

private theorem consecutive_product_eq {A : Finset ℝ} {m : ℕ}
    (x : Fin m → ℝ) (hm : 2 ≤ m) (hx : StrictMono x)
    (hp : ∀ i, 0 < x i) (hA : ∀ i, x i ∈ A)
    (hcard : (A * A).card = 2 * m - 1) (j : ℕ) (hj : 1 ≤ j) (hjm : j < m) :
    x ⟨0, by omega⟩ * x ⟨j, hjm⟩ =
      x ⟨1, by omega⟩ * x ⟨j - 1, by omega⟩ := by
  have hbase := Finset.orderEmbOfFin_unique hcard
    (gridProduct_mem x hm hA m (by omega) le_rfl)
    (gridProduct_strictMono x hm hx hp m (by omega) le_rfl)
  have hother := Finset.orderEmbOfFin_unique hcard
    (gridProduct_mem x hm hA j hj hjm.le)
    (gridProduct_strictMono x hm hx hp j hj hjm.le)
  have heq := congrFun (hbase.trans hother.symm) ⟨j, by omega⟩
  simpa only [gridProduct, gridRow, gridCol, if_pos hjm, if_neg (lt_irrefl j),
    if_pos hjm.le] using heq

/-- Equality in the positive-real product bound forces a geometric progression. -/
theorem eq_geometric_of_product_card (A : Finset ℝ) (hp : ∀ a ∈ A, 0 < a)
    (hm : 2 ≤ A.card) (hcard : (A * A).card ≤ 2 * A.card - 1) :
    ∃ b r : ℝ, 0 < b ∧ 1 < r ∧
      A = (Finset.range A.card).image (fun i => b * r ^ i) := by
  classical
  have hcard_eq : (A * A).card = 2 * A.card - 1 :=
    Nat.le_antisymm hcard (product_card_lower_bound A hp
      (Finset.card_pos.mp (by omega)))
  let x := A.orderEmbOfFin rfl
  let z : Fin A.card := ⟨0, by omega⟩
  let o : Fin A.card := ⟨1, by omega⟩
  have hpos : ∀ i, 0 < x i := fun i => hp _ (A.orderEmbOfFin_mem rfl i)
  let b := x z
  let r := x o / b
  have hb : 0 < b := hpos z
  have hr : 1 < r := (one_lt_div hb).mpr (x.strictMono (show z < o by simp [z, o]))
  have hx : ∀ (i : ℕ) (hi : i < A.card), x ⟨i, hi⟩ = b * r ^ i := by
    intro i
    induction i with
    | zero => intro hi; simp [b, z]
    | succ i ih =>
      intro hi
      have heq := consecutive_product_eq x hm x.strictMono hpos
        (fun i => A.orderEmbOfFin_mem rfl i) hcard_eq (i + 1) (by omega) hi
      have hprev := ih (by omega)
      simp only [Nat.add_sub_cancel] at heq
      change b * x ⟨i + 1, hi⟩ = x o * x ⟨i, by omega⟩ at heq
      rw [hprev] at heq
      apply mul_left_cancel₀ hb.ne'
      rw [pow_succ]
      dsimp [r]
      field_simp
      nlinarith [heq]
  refine ⟨b, r, hb, hr, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := (A.orderIsoOfFin rfl).surjective ⟨a, ha⟩
    refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
    have hxi : x i = a := congrArg Subtype.val hi
    exact (hx i.val i.isLt).symm.trans hxi
  · intro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [← hx i (Finset.mem_range.mp hi)]
    exact A.orderEmbOfFin_mem rfl _

end D5.S3.Arith.GeometricProductSetMinimum
