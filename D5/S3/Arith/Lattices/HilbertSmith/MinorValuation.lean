/- GID: D5/S3/Arith/Lattices/HilbertSmith/MinorValuation
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/HilbertSmith/MinorValuation
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exact valuation of a Hilbert minor product by residue layers. -/

import D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-! # Prime-power layers of Hilbert minors -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.HilbertSmith.MinorValuation

open Finset NestedResidueMatching
open scoped BigOperators

section Counts

variable {α β γ : Type*} [DecidableEq γ]

private theorem cross_layer_count (I : Finset α) (J : Finset β) (t : Finset γ)
    (f : α → γ) (g : β → γ) (hf : ∀ x ∈ I, f x ∈ t) :
    ((I ×ˢ J).filter (fun z => f z.1 = g z.2)).card =
      ∑ c ∈ t, fiber I f c * fiber J g c := by
  classical
  have hmaps : (↑((I ×ˢ J).filter (fun z => f z.1 = g z.2)) :
      Set (α × β)).MapsTo (fun z => f z.1) ↑t :=
    fun z hz => hf z.1 (mem_product.mp (mem_filter.mp (mem_coe.mp hz)).1).1
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro c _
  have h : ((I ×ˢ J).filter (fun z => f z.1 = g z.2)).filter (fun z => f z.1 = c) =
      I.filter (fun x => f x = c) ×ˢ J.filter (fun y => g y = c) := by
    ext z
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, he⟩, hc⟩
      exact ⟨⟨hx, hc⟩, ⟨hy, he.symm.trans hc⟩⟩
    · rintro ⟨⟨hx, hxc⟩, ⟨hy, hyc⟩⟩
      exact ⟨⟨⟨hx, hy⟩, hxc.trans hyc.symm⟩, hxc⟩
  rw [h, card_product]
  rfl

private theorem offDiag_layer_count (I : Finset α) (t : Finset γ)
    (f : α → γ) (hf : ∀ x ∈ I, f x ∈ t) :
    (I.offDiag.filter (fun z => f z.1 = f z.2)).card =
      ∑ c ∈ t, (fiber I f c * fiber I f c - fiber I f c) := by
  classical
  have hmaps : (↑(I.offDiag.filter (fun z => f z.1 = f z.2)) :
      Set (α × α)).MapsTo (fun z => f z.1) ↑t :=
    fun z hz => hf z.1 (mem_offDiag.mp (mem_filter.mp (mem_coe.mp hz)).1).1
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro c _
  have h : (I.offDiag.filter (fun z => f z.1 = f z.2)).filter (fun z => f z.1 = c) =
      (I.filter (fun x => f x = c)).offDiag := by
    ext z
    simp only [mem_filter, mem_offDiag]
    constructor
    · rintro ⟨⟨⟨hx, hy, hne⟩, he⟩, hc⟩
      exact ⟨⟨hx, hc⟩, ⟨hy, he.symm.trans hc⟩, hne⟩
    · rintro ⟨⟨hx, hxc⟩, ⟨hy, hyc⟩, hne⟩
      exact ⟨⟨⟨hx, hy, hne⟩, hxc.trans hyc.symm⟩, hxc⟩
  rw [h, offDiag_card]
  rfl

private theorem gap_cast_sq (u v : ℕ) : (gap u v : ℤ) ^ 2 = ((u : ℤ) - v) ^ 2 := by
  rcases le_total u v with h | h
  · have he : gap u v = v - u := by unfold gap; omega
    rw [he, Nat.cast_sub h]
    ring
  · have he : gap u v = u - v := by unfold gap; omega
    rw [he, Nat.cast_sub h]

private theorem doubled_layer_identity (I : Finset α) (J : Finset β) (t : Finset γ)
    (f : α → γ) (g : β → γ) (hf : ∀ x ∈ I, f x ∈ t) (hg : ∀ y ∈ J, g y ∈ t) :
    ((I.offDiag.filter (fun z => f z.1 = f z.2)).card : ℤ) +
        ((J.offDiag.filter (fun z => g z.1 = g z.2)).card : ℤ) -
        2 * (((I ×ˢ J).filter (fun z => f z.1 = g z.2)).card : ℤ) =
      (loss t I J f g : ℤ) - I.card - J.card := by
  have hI : I.card = ∑ c ∈ t, fiber I f c :=
    card_eq_sum_card_fiberwise (s := I) (t := t) (f := f) (fun x hx => hf x hx)
  have hJ : J.card = ∑ c ∈ t, fiber J g c :=
    card_eq_sum_card_fiberwise (s := J) (t := t) (f := g) (fun y hy => hg y hy)
  rw [offDiag_layer_count I t f hf, offDiag_layer_count J t g hg,
    cross_layer_count I J t f g hf, hI, hJ, loss]
  simp only [Nat.cast_sum]
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  have le_self_mul (u : ℕ) : u ≤ u * u := by
    cases u with
    | zero => simp
    | succ u => simpa only [show Nat.succ 0 = 1 from rfl, mul_one] using
        Nat.mul_le_mul_left (u + 1) (Nat.succ_le_succ (Nat.zero_le u))
  simp only [Nat.cast_sub (le_self_mul _), Nat.cast_mul, Nat.cast_pow, gap_cast_sq]
  ring

end Counts

/-- The product of positive differences between pairs of selected indices. -/
def positiveDifferences (I : Finset ℕ) : ℕ :=
  (I.offDiag.filter (fun z => z.1 < z.2)).prod (fun z => z.2 - z.1)

/-- The product of the unshifted Hilbert denominators for the selected indices. -/
def denominatorProduct (I J : Finset ℕ) : ℕ :=
  (I ×ˢ J).prod (fun z => z.1 + z.2 + 1)

/-- The scaled Hilbert minor in its rational Cauchy product form. -/
def cauchyMinor (L : ℕ) (I J : Finset ℕ) : ℚ :=
  (L : ℚ) ^ I.card * (positiveDifferences I : ℚ) * (positiveDifferences J : ℚ) /
    (denominatorProduct I J : ℚ)

private theorem denominatorProduct_pos (I J : Finset ℕ) : 0 < denominatorProduct I J :=
  Finset.prod_pos fun z _ => by omega

theorem cauchyMinor_pos {L : ℕ} (hL : 0 < L) (I J : Finset ℕ) :
    0 < cauchyMinor L I J := by
  have hdiff (S : Finset ℕ) : 0 < positiveDifferences S :=
    Finset.prod_pos fun _ hz => Nat.sub_pos_of_lt (mem_filter.mp hz).2
  unfold cauchyMinor
  exact div_pos
    (mul_pos (mul_pos (pow_pos (by exact_mod_cast hL) _) (by exact_mod_cast hdiff I))
      (by exact_mod_cast hdiff J))
    (by exact_mod_cast denominatorProduct_pos I J)

private def differences (I : Finset ℕ) : ℕ :=
  ∏ z ∈ I.offDiag, gap z.1 z.2

private theorem differences_eq_sq (I : Finset ℕ) :
    differences I = positiveDifferences I ^ 2 := by
  let lo := I.offDiag.filter (fun z => z.1 < z.2)
  let hi := I.offDiag.filter (fun z => z.2 < z.1)
  have hd : Disjoint lo hi := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hz'
    have h₁ := (mem_filter.mp hz).2
    have h₂ := (mem_filter.mp hz').2
    omega
  have hu : lo ∪ hi = I.offDiag := by
    ext z
    simp only [lo, hi, mem_union, mem_filter]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hz
      rcases lt_or_gt_of_ne (mem_offDiag.mp hz).2.2 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hlo : (∏ z ∈ lo, gap z.1 z.2) = positiveDifferences I := by
    unfold positiveDifferences
    apply prod_congr rfl
    intro z hz
    have hl := (mem_filter.mp hz).2
    unfold gap
    omega
  have hswap : (∏ z ∈ hi, gap z.1 z.2) = ∏ z ∈ lo, gap z.1 z.2 := by
    refine Finset.prod_equiv (Equiv.prodComm ℕ ℕ) ?_ ?_
    · intro z
      simp only [lo, hi, mem_filter, mem_offDiag, Equiv.prodComm_apply]
      exact ⟨fun ⟨⟨ha, hb, hn⟩, ht⟩ => ⟨⟨hb, ha, hn.symm⟩, ht⟩,
        fun ⟨⟨hb, ha, hn⟩, ht⟩ => ⟨⟨ha, hb, hn.symm⟩, ht⟩⟩
    · intro z _
      exact Nat.add_comm _ _
  unfold differences
  rw [← hu, prod_union hd, hswap, hlo, pow_two]

private theorem gap_ne_zero {i j : ℕ} (h : i ≠ j) : gap i j ≠ 0 := by
  unfold gap
  omega

private theorem dvd_gap_iff {q : ℕ} (i j : ℕ) :
    q ∣ gap i j ↔ i % q = j % q := by
  rcases le_total i j with h | h
  · have hg : gap i j = j - i := by unfold gap; omega
    rw [hg]
    exact (Nat.modEq_iff_dvd' (n := q) h).symm
  · have hg : gap i j = i - j := by unfold gap; omega
    rw [hg]
    change q ∣ i - j ↔ i ≡ j [MOD q]
    exact (Nat.modEq_iff_dvd' (n := q) h).symm.trans ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩

private theorem factorization_le_log {p m x : ℕ} (hp : p.Prime)
    (hx : x ≠ 0) (hb : x ≤ m) :
    x.factorization p ≤ Nat.log p m :=
  Nat.le_log_of_pow_le hp.one_lt
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hx) (Nat.ordProj_dvd x p)).trans hb)

private theorem factorization_prod_layers {δ : Type*} (s : Finset δ) (w : δ → ℕ)
    {p e : ℕ} (hp : p.Prime) (h0 : ∀ x ∈ s, w x ≠ 0)
    (he : ∀ x ∈ s, (w x).factorization p ≤ e) :
    (s.prod w).factorization p =
      ∑ a ∈ Icc 1 e, (s.filter (fun z => p ^ a ∣ w z)).card := by
  rw [Nat.factorization_prod_apply h0]
  calc
    _ = ∑ x ∈ s, ∑ a ∈ Icc 1 e, if p ^ a ∣ w x then 1 else 0 := by
      apply sum_congr rfl
      intro x hx
      have hfilter : (Icc 1 e).filter (fun a => p ^ a ∣ w x) =
          Icc 1 ((w x).factorization p) := by
        ext a
        simp only [mem_filter, mem_Icc, hp.pow_dvd_iff_le_factorization (h0 x hx)]
        have := he x hx
        omega
      simp only [Finset.sum_boole, Nat.cast_id, hfilter, Nat.card_Icc, Nat.add_sub_cancel]
    _ = _ := by rw [sum_comm]; simp only [Finset.sum_boole, Nat.cast_id]

private theorem differences_layers {p n : ℕ} (hp : p.Prime) {I : Finset ℕ}
    (hI : I ⊆ range n) :
    (differences I).factorization p =
      ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)),
        (I.offDiag.filter (fun z => z.1 % p ^ a = z.2 % p ^ a)).card := by
  have h0 (z : ℕ × ℕ) (hz : z ∈ I.offDiag) : gap z.1 z.2 ≠ 0 :=
    gap_ne_zero (mem_offDiag.mp hz).2.2
  have hb (z : ℕ × ℕ) (hz : z ∈ I.offDiag) : gap z.1 z.2 ≤ 2 * n - 1 := by
    obtain ⟨hz₁, hz₂, _⟩ := mem_offDiag.mp hz
    have h₁ := mem_range.mp (hI hz₁)
    have h₂ := mem_range.mp (hI hz₂)
    unfold gap
    omega
  unfold differences
  rw [factorization_prod_layers I.offDiag (fun z => gap z.1 z.2) hp h0
    (fun z hz => factorization_le_log hp (h0 z hz) (hb z hz))]
  apply sum_congr rfl
  intro a _
  apply congrArg Finset.card
  ext z
  simp only [mem_filter, dvd_gap_iff]

private theorem denominator_layers {p n : ℕ} (hp : p.Prime) {I J : Finset ℕ}
    (hI : I ⊆ range n) (hJ : J ⊆ range n) :
    (denominatorProduct I J).factorization p =
      ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)),
        ((I ×ˢ J).filter (fun z => z.1 % p ^ a = reflected (p ^ a) z.2)).card := by
  have hb (z : ℕ × ℕ) (hz : z ∈ I ×ˢ J) : z.1 + z.2 + 1 ≤ 2 * n - 1 := by
    obtain ⟨hz₁, hz₂⟩ := mem_product.mp hz
    have h₁ := mem_range.mp (hI hz₁)
    have h₂ := mem_range.mp (hJ hz₂)
    omega
  unfold denominatorProduct
  rw [factorization_prod_layers (I ×ˢ J) (fun z => z.1 + z.2 + 1) hp
    (fun z _ => by omega) (fun z hz => factorization_le_log hp (by omega) (hb z hz))]
  apply sum_congr rfl
  intro a _
  apply congrArg Finset.card
  ext z
  simp only [mem_filter, reflected_eq_iff_dvd (pow_pos hp.pos a)]

private theorem cauchyMinor_sq (L : ℕ) (I J : Finset ℕ) :
    cauchyMinor L I J ^ 2 =
      (L : ℚ) ^ (2 * I.card) * (differences I : ℚ) * (differences J : ℚ) /
        (denominatorProduct I J : ℚ) ^ 2 := by
  unfold cauchyMinor
  rw [differences_eq_sq I, differences_eq_sq J, Nat.cast_pow, Nat.cast_pow,
    mul_comm 2 I.card, pow_mul, div_pow, mul_pow, mul_pow]

/-- The doubled valuation of a Hilbert minor product is a scale term plus
the sum of squared population differences across prime-power layers. -/
theorem cauchyMinor_valuation {p n L k : ℕ} (hp : p.Prime) (hL : L ≠ 0)
    {I J : Finset ℕ} (hI : I ⊆ range n) (hJ : J ⊆ range n)
    (hIk : I.card = k) (hJk : J.card = k) :
    2 * padicValRat p (cauchyMinor L I J) =
      2 * (k : ℤ) * ((L.factorization p : ℤ) - Nat.log p (2 * n - 1)) +
        ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)), (residueLoss (p ^ a) I J : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdiff (S : Finset ℕ) : (differences S : ℚ) ≠ 0 := by
    have h : differences S ≠ 0 :=
      prod_ne_zero_iff.mpr fun _ hz => gap_ne_zero (mem_offDiag.mp hz).2.2
    exact_mod_cast h
  have hdenom : (denominatorProduct I J : ℚ) ≠ 0 := by
    exact_mod_cast (denominatorProduct_pos I J).ne'
  have hscale : (L : ℚ) ≠ 0 := by exact_mod_cast hL
  have hpow : (L : ℚ) ^ (2 * I.card) ≠ 0 := pow_ne_zero _ hscale
  have hterm (a : ℕ) :
      ((I.offDiag.filter (fun z => z.1 % p ^ a = z.2 % p ^ a)).card : ℤ) +
        ((J.offDiag.filter (fun z => z.1 % p ^ a = z.2 % p ^ a)).card : ℤ) -
        2 * (((I ×ˢ J).filter (fun z => z.1 % p ^ a = reflected (p ^ a) z.2)).card : ℤ) =
      (residueLoss (p ^ a) I J : ℤ) - k - k := by
    have hq : 0 < p ^ a := pow_pos hp.pos a
    have hj : J.offDiag.filter (fun z => reflected (p ^ a) z.1 = reflected (p ^ a) z.2) =
        J.offDiag.filter (fun z => z.1 % p ^ a = z.2 % p ^ a) := by
      ext z
      simp only [mem_filter, reflected_eq_reflected_iff hq]
    simpa only [residueLoss, hj, hIk, hJk] using
      doubled_layer_identity I J (range (p ^ a)) (fun i => i % p ^ a) (reflected (p ^ a))
        (fun x _ => mem_range.mpr (Nat.mod_lt x hq))
        (fun x _ => mem_range.mpr (by unfold reflected; exact (Nat.sub_le ..).trans_lt (by omega)))
  calc
    2 * padicValRat p (cauchyMinor L I J) =
        padicValRat p (cauchyMinor L I J ^ 2) := by
      simp only [padicValRat.pow, Nat.cast_ofNat]
    _ = _ := by
      rw [cauchyMinor_sq,
        padicValRat.div (mul_ne_zero (mul_ne_zero hpow (hdiff I)) (hdiff J)) (pow_ne_zero _ hdenom),
        padicValRat.mul (mul_ne_zero hpow (hdiff I)) (hdiff J), padicValRat.mul hpow (hdiff I),
        padicValRat.pow (L : ℚ), padicValRat.pow (denominatorProduct I J : ℚ)]
      simp only [padicValRat.of_nat, ← Nat.factorization_def _ hp, differences_layers hp hI,
        differences_layers hp hJ, denominator_layers hp hI hJ, Nat.cast_sum, Nat.cast_mul,
        Nat.cast_ofNat, hIk]
      rw [show ∀ x y z w : ℤ, x + y + z - w = x + (y + z - w) by intros; ring]
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      simp_rw [hterm]
      simp only [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

end D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
