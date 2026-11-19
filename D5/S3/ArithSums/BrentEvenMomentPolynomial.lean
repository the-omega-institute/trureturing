/- GID: D5/S3/ArithSums/BrentEvenMomentPolynomial
   generality: I
   mirror-B: D5/B/S3/ArithSums/BrentEvenMomentPolynomial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Even double binomial moments admit ordinary integer coefficient polynomials. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartitionCollisionExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-! Finite sign counting and two-color moment expansions for the even binomial sum. -/

open scoped BigOperators
open Finset Polynomial

namespace D5.S3.ArithSums.BrentEvenMomentPolynomial

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Binomial coefficients with the source's zero convention for integer lower indices. -/
def binomial (N : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k then (N.choose k.toNat : ℚ) else 0

/-- The original double sum, including both endpoints and the zeroth-power convention. -/
def W (β n : ℕ) : ℚ :=
  ∑ i ∈ Icc (-(n : ℤ)) n, ∑ j ∈ Icc (-(n : ℤ)) n,
    binomial (2 * n) (n + i) * binomial (2 * n) (n + j) *
      |(i : ℚ) ^ 2 - (j : ℚ) ^ 2| ^ β

/-- Ordinary coefficient integrality, with one polynomial for all natural arguments. -/
def claim : Prop :=
  ∀ r : ℕ, ∃ P : ℤ[X], ∀ n : ℕ,
    (2 : ℚ) ^ (4 * n) * P.eval₂ (Int.castRingHom ℚ) (n : ℚ) =
      (2 : ℚ) ^ r * W (2 * r) n

private theorem sum_shift (n : ℕ) (f : ℤ → ℚ) :
    (∑ i ∈ Icc (-(n : ℤ)) n, f i) =
      ∑ k ∈ range (2 * n + 1), f ((k : ℤ) - n) := by
  symm
  refine sum_bij (fun k _ => (k : ℤ) - n) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro a ha b hb h
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    refine ⟨(i + n).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro k hk
    rfl

private theorem w_shift (β n : ℕ) :
    W β n = ∑ k ∈ range (2 * n + 1), ∑ l ∈ range (2 * n + 1),
      ((2 * n).choose k : ℚ) * ((2 * n).choose l : ℚ) *
        |((k : ℚ) - n) ^ 2 - ((l : ℚ) - n) ^ 2| ^ β := by
  unfold W
  rw [sum_shift]
  apply sum_congr rfl
  intro k hk
  rw [sum_shift]
  apply sum_congr rfl
  intro l hl
  simp [binomial, Int.cast_sub, Int.cast_natCast]

private theorem sum_by_card {α : Type*} [Fintype α] (f : ℕ → ℚ) :
    (∑ s : Finset α, f s.card) =
      ∑ k ∈ range (Fintype.card α + 1), (Fintype.card α).choose k * f k := by
  classical
  have h : (univ : Finset (Finset α)) = (univ : Finset α).powerset := by
    ext s
    simp
  rw [h, sum_powerset]
  simp_rw [sum_powersetCard, card_univ, nsmul_eq_mul]

private def sampleEquiv (N : ℕ) :
    (Fin N → Bool × Bool) ≃ (Finset (Fin N) × Finset (Fin N)) where
  toFun s := (univ.filter fun t => (s t).1, univ.filter fun t => (s t).2)
  invFun p t := (decide (t ∈ p.1), decide (t ∈ p.2))
  left_inv s := by
    funext t
    apply Prod.ext <;> simp
  right_inv p := by
    apply Prod.ext <;> ext t <;> simp

private def sign (b : Bool) : ℚ := if b then 1 else -1
private def U (z : Bool × Bool) : ℚ := (sign z.1 + sign z.2) / 2
private def V (z : Bool × Bool) : ℚ := (sign z.1 - sign z.2) / 2

private theorem sum_sign (N : ℕ) (s : Fin N → Bool) :
    (∑ t, sign (s t)) = 2 * ((univ.filter fun t => s t).card : ℚ) - N := by
  simp only [sign, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg, mul_one]
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
    (fun t => s t = true)
  simp only [card_univ, Fintype.card_fin] at h
  have hc := congrArg (fun k : ℕ => (k : ℚ)) h
  push_cast at hc
  linarith

private theorem source_sum (β n : ℕ) :
    W β n = ∑ s : Fin (2 * n) → Bool × Bool,
      |((((sampleEquiv (2 * n)) s).1.card : ℚ) - n) ^ 2 -
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) ^ 2| ^ β := by
  rw [w_shift]
  let f : Finset (Fin (2 * n)) × Finset (Fin (2 * n)) → ℚ := fun p =>
    |((p.1.card : ℚ) - n) ^ 2 - ((p.2.card : ℚ) - n) ^ 2| ^ β
  change _ = ∑ s, f ((sampleEquiv (2 * n)) s)
  rw [(sampleEquiv (2 * n)).sum_comp f]
  dsimp only [f]
  rw [Fintype.sum_prod_type]
  symm
  rw [sum_by_card (fun k => ∑ y : Finset (Fin (2 * n)),
    |((k : ℚ) - n) ^ 2 - ((y.card : ℚ) - n) ^ 2| ^ β)]
  simp only [Fintype.card_fin]
  apply sum_congr rfl
  intro k hk
  rw [sum_by_card (fun l => |((k : ℚ) - n) ^ 2 - ((l : ℚ) - n) ^ 2| ^ β)]
  simp only [Fintype.card_fin]
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  ring

private theorem source_moment (r n : ℕ) :
    W (2 * r) n = ∑ s : Fin (2 * n) → Bool × Bool,
      (∑ t, U (s t)) ^ (2 * r) * (∑ t, V (s t)) ^ (2 * r) := by
  rw [source_sum]
  apply sum_congr rfl
  intro s hs
  have hu : (∑ t, U (s t)) =
      (((sampleEquiv (2 * n)) s).1.card : ℚ) - n +
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) := by
    change (∑ t, (sign (s t).1 + sign (s t).2) / 2) = _
    rw [← sum_div, sum_add_distrib, sum_sign, sum_sign]
    simp only [sampleEquiv, Equiv.coe_fn_mk]
    push_cast
    ring
  have hv : (∑ t, V (s t)) =
      (((sampleEquiv (2 * n)) s).1.card : ℚ) - n -
        ((((sampleEquiv (2 * n)) s).2.card : ℚ) - n) := by
    change (∑ t, (sign (s t).1 - sign (s t).2) / 2) = _
    rw [← sum_div, sum_sub_distrib, sum_sign, sum_sign]
    simp only [sampleEquiv, Equiv.coe_fn_mk]
    push_cast
    ring
  rw [hu, hv, ← mul_pow, sq_sub_sq]
  exact pow_abs_two_mul _

/-- The falling product after removing one factor two at every even index. -/
private def halfFalling : ℕ → ℤ[X]
  | 0 => 1
  | m + 1 => halfFalling m *
      if m % 2 = 0 then X - C ((m / 2 : ℕ) : ℤ) else 2 * X - C (m : ℤ)

private theorem half_falling_eval (m : ℕ) (x : ℚ) :
    (2 : ℚ) ^ ((m + 1) / 2) * (halfFalling m).eval₂ (Int.castRingHom ℚ) x =
      (descPochhammer ℚ m).eval (2 * x) := by
  induction m with
  | zero => simp [halfFalling]
  | succ m ih =>
    rw [halfFalling, eval₂_mul, descPochhammer_succ_eval]
    by_cases hm : m % 2 = 0
    · rw [ite_eq_left hm]
      have he : (m + 1 + 1) / 2 = (m + 1) / 2 + 1 := by omega
      have hc : (m : ℚ) = 2 * (m / 2 : ℕ) := by
        have h : m = 2 * (m / 2) := by omega
        exact_mod_cast h
      rw [he, pow_succ]
      simp only [eval₂_sub, eval₂_X, map_natCast, eval₂_natCast]
      rw [← ih, hc]
      ring
    · rw [ite_eq_right hm]
      have he : (m + 1 + 1) / 2 = (m + 1) / 2 := by omega
      rw [he]
      simp only [eval₂_sub, eval₂_mul, eval₂_X, map_natCast, eval₂_natCast, eval₂_ofNat]
      rw [← ih]
      ring

/-- The integral polynomial which absorbs the rational factor for an m-block term. -/
private def integralBasis (r m : ℕ) : ℤ[X] :=
  C ((2 : ℤ) ^ (r - m / 2)) * halfFalling m

private theorem integral_basis_eval (r m n : ℕ) (hm : m ≤ 2 * r) :
    (2 : ℚ) ^ m * (integralBasis r m).eval₂ (Int.castRingHom ℚ) n =
      (2 : ℚ) ^ r * ((2 * n).descFactorial m : ℚ) := by
  have hb := half_falling_eval m (n : ℚ)
  have he : m + (r - m / 2) = r + (m + 1) / 2 := by omega
  simp only [integralBasis, eval₂_mul, map_pow, map_ofNat, eval₂_pow, eval₂_ofNat]
  rw [← mul_assoc, ← pow_add, he, pow_add, mul_assoc, hb]
  have hn : (2 : ℚ) * n = ((2 * n : ℕ) : ℚ) := by push_cast; ring
  rw [hn, descPochhammer_eval_eq_descFactorial]

private def coord (r : ℕ) (i : Fin (2 * r + 2 * r)) (z : Bool × Bool) : ℚ :=
  if i.val < 2 * r then U z else V z

private def mean {α : Type*} [Fintype α] (f : α → ℚ) : ℚ :=
  (Fintype.card α : ℚ)⁻¹ * ∑ a, f a

private theorem mean_product {α : Type*} [Fintype α] (f : α → (Bool × Bool) → ℚ) :
    mean (fun s : α → Bool × Bool => ∏ a, f a (s a)) =
      ∏ a, mean (f a) := by
  simp only [mean, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]
  rw [← Fintype.prod_sum]
  simp only [prod_mul_distrib, prod_const, card_univ, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_ofNat, inv_pow]

private theorem mean_one : mean (fun _ : Bool × Bool => (1 : ℚ)) = 1 := by
  norm_num [mean, Fintype.sum_prod_type]

private theorem mean_injective_product {α β : Type*} [Fintype α] [Fintype β]
    (φ : α → β) (hφ : Function.Injective φ) (f : α → (Bool × Bool) → ℚ) :
    mean (fun s : β → Bool × Bool => ∏ a, f a (s (φ a))) =
      ∏ a, mean (f a) := by
  let g : β → (Bool × Bool) → ℚ := fun b =>
    if h : ∃ a, φ a = b then f h.choose else fun _ => 1
  have hg (a : α) : g (φ a) = f a := by
    dsimp only [g]
    split
    · next h => exact congrArg f (hφ h.choose_spec)
    · next h => exact (h ⟨a, rfl⟩).elim
  have hnone (b : β) (hb : b ∉ Set.range φ) : g b = fun _ => 1 := by
    dsimp only [g]
    rw [dite_eq_right (by simpa only [Set.mem_range] using hb)]
  have hp (s : β → Bool × Bool) : (∏ a, f a (s (φ a))) = ∏ b, g b (s b) := by
    apply Fintype.prod_of_injective φ hφ
    · intro b hb
      rw [hnone b hb]
    · intro a
      rw [hg]
  simp_rw [hp]
  rw [mean_product]
  symm
  apply Fintype.prod_of_injective φ hφ
  · intro b hb
    rw [hnone b hb, mean_one]
  · intro a
    rw [hg]

private theorem product_expansion (r N : ℕ) (s : Fin N → Bool × Bool) :
    (∑ t, U (s t)) ^ (2 * r) * (∑ t, V (s t)) ^ (2 * r) =
      ∑ d : Fin (2 * r + 2 * r) → Fin N, ∏ i, coord r i (s (d i)) := by
  rw [← Fintype.prod_sum (fun i t => coord r i (s t))]
  rw [Fin.prod_univ_add]
  congr 1
  · simp [coord, Fin.castAdd]
  · simp [coord, Fin.natAdd, Nat.not_lt.mpr (Nat.le_add_right _ _)]

private instance partitionFintype (k : ℕ) : Fintype (Setoid (Fin k)) :=
  Fintype.ofInjective (fun σ : Setoid (Fin k) => σ.r) (by
    intro σ τ h
    apply Setoid.ext
    intro i j
    exact iff_of_eq (congrFun (congrFun h i) j))

private def block {k : ℕ} (σ : Setoid (Fin k)) (B : Quotient σ) : Finset (Fin k) :=
  univ.filter fun i => Quotient.mk σ i = B

private theorem block_nonempty {k : ℕ} (σ : Setoid (Fin k)) (B : Quotient σ) :
    (block σ B).Nonempty := by
  exact ⟨B.out, by simp [block, Quotient.out_eq]⟩

private def blockWeight (r : ℕ) (σ : Setoid (Fin (2 * r + 2 * r)))
    (B : Quotient σ) (z : Bool × Bool) : ℚ :=
  ∏ i ∈ block σ B, coord r i z

private def Pure (r : ℕ) (S : Finset (Fin (2 * r + 2 * r))) : Prop :=
  (∀ i ∈ S, i.val < 2 * r) ∨ (∀ i ∈ S, ¬i.val < 2 * r)

private def Good (r : ℕ) (σ : Setoid (Fin (2 * r + 2 * r))) : Prop :=
  ∀ B : Quotient σ, Even (block σ B).card ∧ Pure r (block σ B)

private theorem local_u (k : ℕ) (hk : 0 < k) :
    mean (fun z : Bool × Bool => U z ^ k) = if Even k then (1 / 2 : ℚ) else 0 := by
  simp only [mean, Fintype.card_prod, Fintype.card_bool, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [U, sign, zero_pow (by omega : k ≠ 0), neg_one_pow_eq_ite]
  split_ifs <;> norm_num

private theorem local_v (k : ℕ) (hk : 0 < k) :
    mean (fun z : Bool × Bool => V z ^ k) = if Even k then (1 / 2 : ℚ) else 0 := by
  simp only [mean, Fintype.card_prod, Fintype.card_bool, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [V, sign, zero_pow (by omega : k ≠ 0), neg_one_pow_eq_ite]
  split_ifs <;> norm_num

private theorem local_block (r : ℕ) (σ : Setoid (Fin (2 * r + 2 * r))) (B : Quotient σ) :
    mean (blockWeight r σ B) =
      if Even (block σ B).card ∧ Pure r (block σ B) then (1 / 2 : ℚ) else 0 := by
  have hpos : 0 < (block σ B).card := card_pos.mpr (block_nonempty σ B)
  by_cases hL : ∀ i ∈ block σ B, i.val < 2 * r
  · have hw (z : Bool × Bool) : blockWeight r σ B z = U z ^ (block σ B).card := by
      simp only [blockWeight]
      rw [prod_eq_pow_card]
      intro i hi
      simp [coord, hL i hi]
    rw [show blockWeight r σ B = (fun z => U z ^ (block σ B).card) from funext hw]
    rw [local_u _ hpos]
    simp only [show Pure r (block σ B) from Or.inl hL, and_true]
  · by_cases hR : ∀ i ∈ block σ B, ¬i.val < 2 * r
    · have hw (z : Bool × Bool) : blockWeight r σ B z = V z ^ (block σ B).card := by
        simp only [blockWeight]
        rw [prod_eq_pow_card]
        intro i hi
        simp [coord, hR i hi]
      rw [show blockWeight r σ B = (fun z => V z ^ (block σ B).card) from funext hw]
      rw [local_v _ hpos]
      simp only [show Pure r (block σ B) from Or.inr hR, and_true]
    · have hnp : ¬Pure r (block σ B) := by simpa only [Pure, not_or] using And.intro hL hR
      push Not at hL hR
      obtain ⟨i, hi, hir⟩ := hL
      obtain ⟨j, hj, hjl⟩ := hR
      have hw (z : Bool × Bool) : blockWeight r σ B z = 0 := by
        rcases z with ⟨a, b⟩
        cases a <;> cases b
        · apply prod_eq_zero hi
          norm_num [coord, hir, U, V, sign]
        · apply prod_eq_zero hj
          norm_num [coord, hjl, U, V, sign]
        · apply prod_eq_zero hj
          norm_num [coord, hjl, U, V, sign]
        · apply prod_eq_zero hi
          norm_num [coord, hir, U, V, sign]
      rw [show blockWeight r σ B = (fun _ => 0) from funext hw]
      simp [mean, hnp]

private theorem good_bound (r : ℕ) (σ : Setoid (Fin (2 * r + 2 * r))) (hσ : Good r σ) :
    Fintype.card (Quotient σ) ≤ 2 * r := by
  have hc : 2 * r + 2 * r = ∑ B : Quotient σ, (block σ B).card := by
    simpa only [block, card_univ, Fintype.card_fin] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset (Fin (2 * r + 2 * r))))
        (t := (univ : Finset (Quotient σ))) (f := Quotient.mk σ) (by simp))
  have hle : (∑ _B : Quotient σ, 2) ≤ ∑ B : Quotient σ, (block σ B).card := by
    apply sum_le_sum
    intro B hB
    have hp := card_pos.mpr (block_nonempty σ B)
    obtain ⟨a, ha⟩ := (hσ B).1
    omega
  simp only [sum_const, card_univ, smul_eq_mul] at hle
  omega

private theorem block_product (r N : ℕ) (σ : Setoid (Fin (2 * r + 2 * r)))
    (φ : Quotient σ → Fin N) (s : Fin N → Bool × Bool) :
    (∏ i, coord r i (s (φ (Quotient.mk σ i)))) =
      ∏ B : Quotient σ, blockWeight r σ B (s (φ B)) := by
  symm
  calc
    _ = ∏ B : Quotient σ, ∏ i ∈ block σ B, coord r i (s (φ (Quotient.mk σ i))) := by
      apply prod_congr rfl
      intro B hB
      apply prod_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := prod_fiberwise univ (Quotient.mk σ) _

private theorem mean_sum {α β : Type*} [Fintype α] (T : Finset β) (f : α → β → ℚ) :
    mean (fun a => ∑ b ∈ T, f a b) = ∑ b ∈ T, mean (fun a => f a b) := by
  simp only [mean]
  rw [sum_comm, mul_sum]

private theorem kernel_assignments {k N : ℕ} (σ : Setoid (Fin k)) (f : Fin k → Fin N → ℚ) :
    (∑ d : Fin k → Fin N with Setoid.ker d = σ, ∏ i, f i (d i)) =
      ∑ φ : Quotient σ → Fin N with Function.Injective φ,
        ∏ i, f i (φ (Quotient.mk σ i)) := by
  have h := D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.kernelDistinctMoment_eq_block_assignments
    (A := ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun _ : Fin N => (1 : ℝ))
    (fun i t => (f i t : ℝ)) σ ∅
  simp only [D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.kernelDistinctMoment,
    prod_empty, LinearMap.id_apply, mul_one] at h
  apply (Rat.cast_injective (α := ℝ))
  push_cast
  convert h using 1 <;> congr 1 <;> ext φ <;> simp

private theorem kernel_group {k N : ℕ} (F : (Fin k → Fin N) → ℚ) :
    (∑ d, F d) = ∑ σ : Setoid (Fin k), ∑ d : Fin k → Fin N with Setoid.ker d = σ, F d := by
  rw [D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.sum_eq_tupleKernel_sums]
  apply sum_subset (by simp)
  intro σ hσ hnot
  apply sum_eq_zero
  intro d hd
  exfalso
  apply hnot
  exact mem_image.mpr ⟨d, mem_univ _, (mem_filter.mp hd).2⟩

private theorem injective_count {α : Type*} [Fintype α] (N : ℕ) :
    (univ.filter (Function.Injective : (α → Fin N) → Prop)).card =
      N.descFactorial (Fintype.card α) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding α (Fin N)),
    Fintype.card_embedding_eq, Fintype.card_fin]

private theorem kernel_mean (r N : ℕ) (σ : Setoid (Fin (2 * r + 2 * r))) :
    mean (fun s : Fin N → Bool × Bool =>
      ∑ d : Fin (2 * r + 2 * r) → Fin N with Setoid.ker d = σ,
        ∏ i, coord r i (s (d i))) =
      (N.descFactorial (Fintype.card (Quotient σ)) : ℚ) *
        ∏ B : Quotient σ, mean (blockWeight r σ B) := by
  have hk (s : Fin N → Bool × Bool) := kernel_assignments σ (fun i t => coord r i (s t))
  simp_rw [hk]
  rw [mean_sum]
  have he (φ : Quotient σ → Fin N) (hφ : Function.Injective φ) :
      mean (fun s : Fin N → Bool × Bool => ∏ i, coord r i (s (φ (Quotient.mk σ i)))) =
        ∏ B : Quotient σ, mean (blockWeight r σ B) := by
    simp_rw [block_product]
    convert mean_injective_product φ hφ (blockWeight r σ) using 1 <;> congr 1 <;>
      exact Subsingleton.elim _ _
  rw [sum_congr rfl (fun φ hφ => he φ (mem_filter.mp hφ).2)]
  simp only [sum_const, nsmul_eq_mul]
  congr 2
  convert injective_count (α := Quotient σ) N using 1 <;> congr 1 <;> ext φ <;> simp

private theorem good_product (r : ℕ) (σ : Setoid (Fin (2 * r + 2 * r))) :
    (∏ B : Quotient σ, mean (blockWeight r σ B)) =
      if Good r σ then (1 / 2 : ℚ) ^ Fintype.card (Quotient σ) else 0 := by
  simp_rw [local_block]
  by_cases hσ : Good r σ
  · simp [hσ, show ∀ B, Even (block σ B).card ∧ Pure r (block σ B) from hσ]
  · rw [ite_eq_right hσ]
    unfold Good at hσ
    push Not at hσ
    obtain ⟨B, hB⟩ := hσ
    exact prod_eq_zero (mem_univ B) (ite_eq_right (not_and.mpr hB))

private theorem finite_expansion (r N : ℕ) :
    mean (fun s : Fin N → Bool × Bool =>
      (∑ t, U (s t)) ^ (2 * r) * (∑ t, V (s t)) ^ (2 * r)) =
      ∑ σ : Setoid (Fin (2 * r + 2 * r)),
        if Good r σ then
          (N.descFactorial (Fintype.card (Quotient σ)) : ℚ) *
            (1 / 2 : ℚ) ^ Fintype.card (Quotient σ) else 0 := by
  simp_rw [product_expansion, kernel_group]
  rw [mean_sum]
  apply sum_congr rfl
  intro σ hσ
  rw [kernel_mean, good_product]
  split_ifs <;> simp

/-- Sum of the integral falling-product terms over pure even two-color partitions. -/
private def polynomial (r : ℕ) : ℤ[X] :=
  ∑ σ : Setoid (Fin (2 * r + 2 * r)),
    if Good r σ then integralBasis r (Fintype.card (Quotient σ)) else 0

private theorem polynomial_mean (r n : ℕ) :
    (polynomial r).eval₂ (Int.castRingHom ℚ) (n : ℚ) =
      (2 : ℚ) ^ r * mean (fun s : Fin (2 * n) → Bool × Bool =>
        (∑ t, U (s t)) ^ (2 * r) * (∑ t, V (s t)) ^ (2 * r)) := by
  rw [finite_expansion]
  simp only [polynomial, eval₂_finsetSum, mul_sum]
  apply sum_congr rfl
  intro σ hσ
  by_cases hg : Good r σ
  · rw [ite_eq_left hg, ite_eq_left hg]
    have h := integral_basis_eval r (Fintype.card (Quotient σ)) n (good_bound r σ hg)
    have hp : (2 : ℚ) ^ Fintype.card (Quotient σ) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply (mul_left_cancel₀ hp)
    rw [h]
    simp only [one_div_pow]
    field_simp
  · simp [hg]

/-- The original all-parameter ordinary integer coefficient polynomial assertion. -/
theorem result : claim := by
  intro r
  refine ⟨polynomial r, ?_⟩
  intro n
  rw [polynomial_mean]
  have hs := source_moment r n
  simp only [mean, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_fin] at *
  have hfour : ((2 : ℚ) * 2) ^ (2 * n) = (2 : ℚ) ^ (4 * n) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    omega
  rw [hfour, ← hs]
  field_simp

#print axioms result

end
end D5.S3.ArithSums.BrentEvenMomentPolynomial
