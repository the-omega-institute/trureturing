/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderProductBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderProductBounds
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Cubic product perturbations and injective sixth-order sum estimates. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Ring.Nat

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Perturbing each factor of a product of three bounded scalars by at most one costs
at most three times the square of the common bound. -/
theorem scalar_prod_diff_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 3) (f g : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
    (hd : ∀ i ∈ s, |f i - g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ 3 * B ^ 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have hm (x y : α) (hx : x ∈ ({a, b, c} : Finset α))
      (hy : y ∈ ({a, b, c} : Finset α)) (F G : α → ℝ)
      (hF : ∀ i ∈ ({a, b, c} : Finset α), |F i| ≤ B)
      (hG : ∀ i ∈ ({a, b, c} : Finset α), |G i| ≤ B) :
      |F x| * |G y| ≤ B ^ 2 := by
    nlinarith [mul_le_mul (hF x hx) (hG y hy) (abs_nonneg (G y)) hB]
  have ha : |(f a - g a) * f b * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * |f b| * |f c| := by gcongr; exact hd a (by simp)
      _ ≤ B ^ 2 := by simpa using hm b c (by simp) (by simp) f f hf hf
  have hb : |g a * (f b - g b) * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * 1 * |f c| := by gcongr; exact hd b (by simp)
      _ ≤ B ^ 2 := by simpa using hm a c (by simp) (by simp) g f hg hf
  have hc : |g a * g b * (f c - g c)| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * |g b| * 1 := by gcongr; exact hd c (by simp)
      _ ≤ B ^ 2 := by simpa using hm a b (by simp) (by simp) g g hg hg
  simp only [Finset.prod_insert (show a ∉ ({b, c} : Finset α) by simp [hab, hac]),
    Finset.prod_insert (show b ∉ ({c} : Finset α) by simp [hbc]), Finset.prod_singleton]
  have he : f a * (f b * f c) - g a * (g b * g c) =
      (f a - g a) * f b * f c + g a * (f b - g b) * f c +
        g a * g b * (f c - g c) := by ring
  rw [he]
  calc
    _ ≤ |(f a - g a) * f b * f c + g a * (f b - g b) * f c| +
        |g a * g b * (f c - g c)| := abs_add_le _ _
    _ ≤ (|(f a - g a) * f b * f c| + |g a * (f b - g b) * f c|) +
        |g a * g b * (f c - g c)| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 * B ^ 2 := by linarith

/-- Removing noninjective assignments from a sixth-order product sum changes it by at
most thirty-six times the fifth power of the number of available labels. -/
theorem inj_sum_product_bound (N : ℕ) (hN : 6 ≤ N)
    (g : Fin 6 → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |(∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
        ∏ i, ∑ d, g i d| ≤ 36 * (N : ℝ)^5 := by
  classical
  let all : Finset (Fin 6 → Fin N) := Finset.univ
  let good : Finset (Fin 6 → Fin N) := all.filter Function.Injective
  let bad : Finset (Fin 6 → Fin N) := all.filter (fun x => ¬Function.Injective x)
  have hsplit :
      (∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) +
        ∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i) =
        ∑ x : Fin 6 → Fin N, ∏ i, g i (x i) := by
    exact Finset.sum_filter_add_sum_filter_not _ Function.Injective _
  have hall : (∑ x : Fin 6 → Fin N, ∏ i, g i (x i)) = ∏ i, ∑ d, g i d := by
    rw [← Fintype.prod_sum]
  have hcardbad : (bad.card : ℝ) ≤ 36 * (N : ℝ)^5 := by
    have hcardgood : good.card = N.descFactorial 6 := by
      let e : {x : Fin 6 → Fin N // Function.Injective x} ≃ (Fin 6 ↪ Fin N) :=
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      have he := Fintype.card_congr e
      rw [Fintype.card_embedding_eq] at he
      simpa only [good, all, Fintype.card_subtype, Fintype.card_fin] using he
    have hcardall : all.card = N ^ 6 := by simp [all, Fintype.card_fun]
    have hdisj : Disjoint good bad := by
      apply Finset.disjoint_left.mpr
      intro x hxg hxb
      exact (Finset.mem_filter.mp hxb).2 (Finset.mem_filter.mp hxg).2
    have hunion : good ∪ bad = all := by
      ext x
      simp only [good, bad, all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    have hc : good.card + bad.card = all.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [hcardall, hcardgood] at hc
    have hcast : (N.descFactorial 6 : ℝ) + (bad.card : ℝ) = (N : ℝ)^6 := by
      exact_mod_cast hc
    have hNreal : (6 : ℝ) ≤ N := by exact_mod_cast hN
    have hlowerNat := Nat.pow_sub_le_descFactorial N 6
    rw [show N + 1 - 6 = N - 5 by omega] at hlowerNat
    have hlower : ((N : ℝ) - 5)^6 ≤ (N.descFactorial 6 : ℝ) := by
      have hcastLower : ((N - 5 : ℕ) : ℝ)^6 ≤ (N.descFactorial 6 : ℝ) := by
        exact_mod_cast hlowerNat
      simpa only [Nat.cast_sub (by omega : 5 ≤ N), Nat.cast_ofNat] using hcastLower
    have hp : |(N : ℝ)^6 - ((N : ℝ) - 5)^6| ≤ 30 * (N : ℝ)^5 := by
      have h := abs_pow_sub_pow_le (a := (N : ℝ)) (b := (N : ℝ) - 5) (n := 6)
      have hm : max |(N : ℝ)| |(N : ℝ) - 5| = (N : ℝ) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith), max_eq_left]
        linarith
      rw [hm, show (N : ℝ) - ((N : ℝ) - 5) = 5 by ring] at h
      norm_num at h ⊢
      nlinarith [h]
    have hle := (le_abs_self ((N : ℝ)^6 - ((N : ℝ) - 5)^6)).trans hp
    nlinarith [show (0 : ℝ) ≤ (N : ℝ)^5 by positivity]
  have hbad :
      |∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i)| ≤
        36 * (N : ℝ)^5 := by
    calc
      _ ≤ ∑ x : Fin 6 → Fin N with ¬Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin 6 → Fin N with ¬Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ = (bad.card : ℝ) := by simp [bad, all]
      _ ≤ _ := hcardbad
  have he : (∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
      ∏ i, ∑ d, g i d =
      -(∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i)) := by
    rw [← hall]
    linarith
  rw [he, abs_neg]
  exact hbad

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
