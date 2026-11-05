/- GID: D5/S3/Combinatorics/Probability/CdsoCapacityCertificate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/CdsoCapacityCertificate
   mirror-E: none(waiver:symbolic-finite-law-certificate)
   anchors: []
   utility: none
   digest: Capacity residuals on every nonempty subset of one finite incidence law. -/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! A subset law retains every nonempty atom, including atoms of zero mass. -/

noncomputable section
open scoped BigOperators
open Finset
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.CdsoCapacityCertificate

abbrev Atom (a : ℕ) := {T : Finset (Fin (a + 2)) // T.Nonempty}

def marginal {a : ℕ} (x : Atom a → ℝ) (i : Fin (a + 2)) : ℝ :=
  ∑ T, if i ∈ T.val then x T else 0

def threshold (a : ℕ) (δ : ℝ) : ℝ :=
  3 * (2 * a + 3) * δ / (a + 1 : ℝ) ^ 2

structure DenseLaw (a : ℕ) (δ : ℝ) where
  mass : Atom a → ℝ
  nonneg : ∀ T, 0 ≤ mass T
  total : ∑ T, mass T = 1
  mean : ∑ T, mass T * (T.val.card : ℝ) = (a + 1 : ℝ) - δ
  dense : ∀ i, threshold a δ ≤ marginal mass i

def weight {a : ℕ} (y : Fin (a + 2) → ℝ) (i : Fin (a + 2)) : ℝ :=
  (y i)⁻¹ ^ 2

def residual {a : ℕ} (α : Fin (a + 2) → ℝ) (ω : ℝ)
    (T : Finset (Fin (a + 2))) : ℝ :=
  ((a + 1 : ℝ) - T.card) *
    ((2 * a + 1 : ℝ) * ((∑ i, α i) - 2 * ω) -
      ((a + 1 : ℝ) + T.card) * ∑ i ∈ T, α i) +
    ∑ i ∈ univ \ T, (2 * a + 1 : ℝ) * max (ω - α i) 0

def energy {a : ℕ} (x : Atom a → ℝ) : ℝ :=
  ∑ T, x T * (T.val.card : ℝ) ^ 2 * ∑ i ∈ T.val, weight (marginal x) i

private lemma positive_part_zero {ι : Type*}
    (J : Finset ι) (α : ι → ℝ) (ω c : ℝ) (hc : 0 < c) :
    (∑ i ∈ J, c * max (ω - α i) 0) = 0 ↔ ∀ i ∈ J, ω ≤ α i := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg hc.le (le_max_right _ _))]
  simp only [mul_eq_zero, hc.ne', false_or, max_eq_right_iff, sub_nonpos]

private lemma reflected_part (z ω : ℝ) :
    z - ω + max (ω - z) 0 = max (z - ω) 0 := by
  rcases le_total z ω with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

private theorem weighted_certificate {a : ℕ} (ha : 7 ≤ a)
    (α : Fin (a + 2) → ℝ) (ω : ℝ)
    (hα : ∀ i, 1 ≤ α i) (hω : 1 ≤ ω) (hωu : ω ≤ 16 / 15)
    (T : Finset (Fin (a + 2))) (hT : T.Nonempty) :
    0 ≤ residual α ω T ∧
      (residual α ω T = 0 ↔
        (T.card = a + 1 ∧ ∀ i ∈ univ \ T, ω ≤ α i) ∨
        (T.card = a ∧ ∀ i ∈ univ \ T, α i ≤ ω)) := by
  let J := univ \ T
  let W := ∑ i, α i
  let A := ∑ i ∈ J, α i
  let P := ∑ i ∈ J, (2 * a + 1 : ℝ) * max (ω - α i) 0
  have hc : (0 : ℝ) < 2 * a + 1 := by positivity
  have hjk : J.card + T.card = a + 2 := by
    simpa [J] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hsum : A + (∑ i ∈ T, α i) = W := by
    exact Finset.sum_sdiff (Finset.subset_univ T)
  have hW : (a + 2 : ℝ) ≤ W := by
    simpa [W] using (Finset.sum_le_sum (s := univ) (fun i _ => hα i))
  have hA : (J.card : ℝ) ≤ A := by
    simpa [A] using (Finset.sum_le_sum (s := J) (fun i _ => hα i))
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ =>
    mul_nonneg hc.le (le_max_right _ _))
  have hr : residual α ω T =
      ((a + 1 : ℝ) - T.card) *
        ((2 * a + 1 : ℝ) * (W - 2 * ω) -
          ((a + 1 : ℝ) + T.card) * (W - A)) + P := by
    have hsub : (∑ i ∈ T, α i) = W - A := by linarith only [hsum]
    unfold residual
    change ((a + 1 : ℝ) - T.card) *
      ((2 * a + 1 : ℝ) * (W - 2 * ω) -
        ((a + 1 : ℝ) + T.card) * ∑ i ∈ T, α i) + P = _
    rw [hsub]
  by_cases hk1 : T.card = a + 1
  · have he : residual α ω T = P := by rw [hr, hk1]; push_cast; ring
    rw [he]
    refine ⟨hP, ?_⟩
    simp only [hk1, true_and, Nat.add_eq_left, one_ne_zero, false_and, or_false]
    exact positive_part_zero J α ω _ hc
  by_cases hk0 : T.card = a
  · have hJ : J.card = 2 := by omega
    have he : residual α ω T =
        (2 * a + 1 : ℝ) * ∑ i ∈ J, max (α i - ω) 0 := by
      rw [hr, hk0]
      have hparts : (∑ i ∈ J, max (α i - ω) 0) =
          ∑ i ∈ J, (α i - ω + max (ω - α i) 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (reflected_part (α i) ω).symm
      rw [hparts]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, hJ, Nat.cast_ofNat]
      dsimp [P]
      rw [← Finset.mul_sum]
      ring
    rw [he]
    refine ⟨mul_nonneg hc.le (Finset.sum_nonneg (fun _ _ => le_max_right _ _)), ?_⟩
    have hz := positive_part_zero J (fun i => -α i) (-ω) _ hc
    simp only [sub_neg_eq_add, neg_add_eq_sub, neg_le_neg_iff] at hz
    rw [Finset.mul_sum]
    simpa [hk0, hk1, J] using hz
  have hk : T.card ≤ a + 2 := by simpa using T.card_le_univ
  by_cases hfull : T.card = a + 2
  · have hJ : J = ∅ := Finset.card_eq_zero.mp (by omega)
    have he : residual α ω T = 2 * W + 2 * (2 * a + 1 : ℝ) * ω := by
      rw [hr, hfull]
      dsimp [P, A]
      simp only [hJ, Finset.sum_empty]
      push_cast
      ring
    have hp : 0 < residual α ω T := by rw [he]; nlinarith
    exact ⟨hp.le, by simp [hp.ne', hk1, hk0]⟩
  have hka : T.card < a := by omega
  have hdlo : 3 ≤ J.card := by omega
  have hdhi : J.card ≤ a + 1 := by have := hT.card_pos; omega
  have hpos : 0 < (a + 1 : ℝ) - T.card := by
    apply sub_pos.mpr
    exact_mod_cast (by omega : T.card < a + 1)
  have hcast : (J.card : ℝ) + T.card = a + 2 := by exact_mod_cast hjk
  have hdlo' : (3 : ℝ) ≤ J.card := by exact_mod_cast hdlo
  have hdhi' : (J.card : ℝ) ≤ a + 1 := by exact_mod_cast hdhi
  have hprod : 0 ≤ ((J.card : ℝ) - 3) * (3 * (a + 2) - 4 - J.card) :=
    mul_nonneg (by linarith) (by linarith)
  have ha' : (7 : ℝ) ≤ a := by exact_mod_cast ha
  have hquad : (7 : ℝ) * (a + 2) - 12 ≤
      3 * (a + 2) * J.card - 2 * (a + 2) - J.card - (J.card : ℝ) ^ 2 := by
    nlinarith
  have hmulW := mul_nonneg (show (0 : ℝ) ≤ J.card - 2 by linarith) (sub_nonneg.mpr hW)
  have hmulA := mul_nonneg (show (0 : ℝ) ≤ 2 * (a + 2) - 1 - J.card by linarith)
    (sub_nonneg.mpr hA)
  have hmulω := mul_nonneg (show (0 : ℝ) ≤ 2 * (2 * a + 1) by positivity)
    (sub_nonneg.mpr hωu)
  have hb : (41 * a - 2 : ℝ) / 15 ≤
      (2 * a + 1 : ℝ) * (W - 2 * ω) -
        ((a + 1 : ℝ) + T.card) * (W - A) := by
    nlinarith [hcast]
  have hbpos : (0 : ℝ) < (41 * a - 2) / 15 := by linarith
  have hp : 0 < residual α ω T := by
    rw [hr]
    exact add_pos_of_pos_of_nonneg (mul_pos hpos (lt_of_lt_of_le hbpos hb)) hP
  exact ⟨hp.le, by simp [hp.ne', hk1, hk0]⟩

private lemma marginal_bounds {a : ℕ} {δ : ℝ} (x : DenseLaw a δ) (hδ : 0 < δ)
    (i : Fin (a + 2)) : 0 < marginal x.mass i ∧ marginal x.mass i ≤ 1 := by
  have ht : 0 < threshold a δ := by unfold threshold; positivity
  refine ⟨lt_of_lt_of_le ht (x.dense i), ?_⟩
  rw [← x.total]
  apply Finset.sum_le_sum
  intro T _
  split_ifs
  · exact le_rfl
  · exact x.nonneg T

private lemma marginal_total {a : ℕ} (x : Atom a → ℝ) :
    ∑ i, marginal x i = ∑ T, x T * (T.val.card : ℝ) := by
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp [← Finset.sum_filter, mul_comm]

private lemma third_marginal_bound {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (x : DenseLaw a δ)
    (hsort : Antitone (marginal x.mass)) :
    let t : Fin (a + 2) := ⟨2, by omega⟩
    (a - 1 - δ : ℝ) / a ≤ marginal x.mass t ∧
      (1 - 2 / (a : ℝ)) ≤ marginal x.mass t ∧
      1 ≤ weight (marginal x.mass) t ∧
      weight (marginal x.mass) t ≤ 16 / 15 := by
  dsimp only
  let y := marginal x.mass
  let t : Fin (a + 2) := ⟨2, by omega⟩
  have haR : (4096 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0 : ℝ) < a := by linarith
  have hδ1 : δ ≤ 1 := le_trans hδu ((div_le_one hap).mpr (by linarith))
  have hsum : (∑ i, y i) = (a + 1 : ℝ) - δ := by
    exact (marginal_total x.mass).trans x.mean
  have htail : (∑ j : Fin a, y j.succ.succ) ≤ (a : ℝ) * y t := by
    calc
      _ ≤ ∑ _j : Fin a, y t := Finset.sum_le_sum (fun j _ =>
        hsort (show t ≤ j.succ.succ by change 2 ≤ j.val + 1 + 1; omega))
      _ = _ := by simp
  have h0 := (marginal_bounds x hδ (⟨0, by omega⟩ : Fin (a + 2))).2
  have h1 := (marginal_bounds x hδ (⟨1, by omega⟩ : Fin (a + 2))).2
  have hsplit : (∑ i, y i) = y ⟨0, by omega⟩ + y ⟨1, by omega⟩ +
      ∑ j : Fin a, y j.succ.succ := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hz : (0 : Fin (a + 2)) = ⟨0, by omega⟩ := by ext; simp
    have ho : (0 : Fin (a + 1)).succ = ⟨1, by omega⟩ := by ext; simp
    rw [hz, ho]
    ring
  have hmean : (a - 1 - δ : ℝ) ≤ a * y t := by linarith [hsplit]
  have hfirst : (a - 1 - δ : ℝ) / a ≤ y t :=
    (div_le_iff₀ hap).mpr (by nlinarith only [hmean])
  have hell : 1 - 2 / (a : ℝ) ≤ y t := by
    apply le_trans _ hfirst
    apply (le_div_iff₀ hap).mpr
    have he : (1 - 2 / (a : ℝ)) * a = a - 2 := by field_simp
    rw [he]
    linarith
  have h31 : (31 / 32 : ℝ) ≤ y t := by
    have : (2 : ℝ) / a ≤ 1 / 32 := (div_le_iff₀ hap).mpr (by linarith)
    linarith
  have hy := marginal_bounds x hδ t
  have hinv : 1 ≤ (y t)⁻¹ := (one_le_inv₀ hy.1).mpr hy.2
  have hinvu : (y t)⁻¹ ≤ 32 / 31 := by
    apply (inv_le_iff_one_le_mul₀ hy.1).mpr
    nlinarith
  refine ⟨hfirst, hell, ?_, ?_⟩
  · change 1 ≤ (y t)⁻¹ ^ 2
    nlinarith
  · change (y t)⁻¹ ^ 2 ≤ 16 / 15
    have hsq := pow_le_pow_left₀ (inv_nonneg.mpr hy.1.le) hinvu 2
    norm_num at hsq ⊢
    linarith

private lemma weight_le_iff {a : ℕ} (y : Fin (a + 2) → ℝ)
    (i j : Fin (a + 2)) (hi : 0 < y i) (hj : 0 < y j) :
    weight y i ≤ weight y j ↔ y j ≤ y i := by
  unfold weight
  rw [sq_le_sq₀ (inv_nonneg.mpr hi.le) (inv_nonneg.mpr hj.le)]
  exact inv_le_inv₀ hi hj

/-- The certificate and its complete zero set use actual marginals of the given law. -/
private theorem capacity_certificate {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (x : DenseLaw a δ)
    (hsort : Antitone (marginal x.mass))
    (T : Finset (Fin (a + 2))) (hT : T.Nonempty) :
    let y := marginal x.mass
    let t : Fin (a + 2) := ⟨2, by omega⟩
    0 ≤ residual (weight y) (weight y t) T ∧
      (residual (weight y) (weight y t) T = 0 ↔
        (T.card = a + 1 ∧ ∃ i, univ \ T = {i} ∧ y i ≤ y t) ∨
        (T.card = a ∧ ∃ i j, i ≠ j ∧ univ \ T = {i, j} ∧
          y t ≤ y i ∧ y t ≤ y j)) := by
  dsimp only
  let y := marginal x.mass
  let t : Fin (a + 2) := ⟨2, by omega⟩
  have hα (i : Fin (a + 2)) : 1 ≤ weight y i := by
    have hi := marginal_bounds x hδ i
    have hinv := (one_le_inv₀ hi.1).mpr hi.2
    change 1 ≤ (y i)⁻¹ ^ 2
    nlinarith [sq_nonneg ((y i)⁻¹ - 1)]
  have hω := third_marginal_bound ha hδ hδu x hsort
  have hcert := weighted_certificate (by omega : 7 ≤ a) (weight y) (weight y t)
    hα hω.2.2.1 hω.2.2.2 T hT
  refine ⟨hcert.1, hcert.2.trans ?_⟩
  have hjk : (univ \ T).card + T.card = a + 2 := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hy (i : Fin (a + 2)) : 0 < y i := (marginal_bounds x hδ i).1
  constructor
  · rintro (⟨hk, h⟩ | ⟨hk, h⟩)
    · left
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show (univ \ T).card = 1 by omega)
      refine ⟨hk, i, hi, ?_⟩
      apply (weight_le_iff y t i (hy t) (hy i)).mp
      exact h i (by simp [hi])
    · right
      obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp
        (show (univ \ T).card = 2 by omega)
      refine ⟨hk, i, j, hij, he, ?_, ?_⟩
      · exact (weight_le_iff y i t (hy i) (hy t)).mp (h i (by simp [he]))
      · exact (weight_le_iff y j t (hy j) (hy t)).mp (h j (by simp [he]))
  · rintro (⟨hk, i, hi, hiy⟩ | ⟨hk, i, j, hij, he, hiy, hjy⟩)
    · left
      refine ⟨hk, ?_⟩
      intro j hj
      have : j = i := by simpa [hi] using hj
      subst j
      exact (weight_le_iff y t i (hy t) (hy i)).mpr hiy
    · right
      refine ⟨hk, ?_⟩
      intro k hk
      have : k = i ∨ k = j := by simpa [he] using hk
      rcases this with hki | hkj
      · subst k; exact (weight_le_iff y i t (hy i) (hy t)).mpr hiy
      · subst k; exact (weight_le_iff y j t (hy j) (hy t)).mpr hjy

def linearPart {a : ℕ} (δ : ℝ) (y : Fin (a + 2) → ℝ) (ω : ℝ) : ℝ :=
  (a + 1 : ℝ) ^ 2 * (∑ i, (y i)⁻¹) -
    (2 * a + 1 : ℝ) * δ * ((∑ i, weight y i) - 2 * ω) -
    ∑ i, (1 - y i) * ((2 * a + 1 : ℝ) * max (ω - weight y i) 0)

private lemma expected_incidence {a : ℕ} (x : Atom a → ℝ)
    (h : Fin (a + 2) → ℝ) :
    (∑ T, x T * ∑ i ∈ T.val, h i) = ∑ i, h i * marginal x i := by
  simp only [marginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp [Finset.sum_ite, mul_ite, mul_comm]

private lemma expected_omission {a : ℕ} {δ : ℝ} (x : DenseLaw a δ)
    (b : Fin (a + 2) → ℝ) :
    (∑ T, x.mass T * ∑ i ∈ univ \ T.val, b i) =
      ∑ i, (1 - marginal x.mass i) * b i := by
  have hc (T : Atom a) : (∑ i ∈ univ \ T.val, b i) =
      (∑ i, b i) - ∑ i ∈ T.val, b i := by
    have h := Finset.sum_sdiff (f := b) (Finset.subset_univ T.val)
    linarith only [h]
  simp_rw [hc, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, x.total, one_mul,
    expected_incidence]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma energy_identity {a : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (x : DenseLaw a δ) (ω : ℝ) :
    energy x.mass = linearPart δ (marginal x.mass) ω +
      ∑ T, x.mass T * residual (weight (marginal x.mass)) ω T.val := by
  let y := marginal x.mass
  let α := weight y
  let W := ∑ i, α i
  let b := fun i => (2 * a + 1 : ℝ) * max (ω - α i) 0
  have hm : (∑ T, x.mass T * ((a + 1 : ℝ) - T.val.card)) = δ := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, x.total,
      x.mean, one_mul]
    ring
  have hi : (∑ T, x.mass T * ∑ i ∈ T.val, α i) = ∑ i, (y i)⁻¹ := by
    rw [expected_incidence]
    apply Finset.sum_congr rfl
    intro i _
    have hy := (marginal_bounds x hδ i).1.ne'
    change (y i)⁻¹ ^ 2 * y i = (y i)⁻¹
    field_simp
  calc
    energy x.mass = ∑ T,
        ((a + 1 : ℝ) ^ 2 * (x.mass T * (∑ i ∈ T.val, α i)) -
        ((2 * a + 1 : ℝ) * (W - 2 * ω)) *
          (x.mass T * ((a + 1 : ℝ) - T.val.card)) -
        x.mass T * (∑ i ∈ univ \ T.val, b i) +
        x.mass T * residual α ω T.val) := by
      apply Finset.sum_congr rfl
      intro T _
      dsimp [residual, W, b]
      ring
    _ = (a + 1 : ℝ) ^ 2 * (∑ T, x.mass T * ∑ i ∈ T.val, α i) -
        ((2 * a + 1 : ℝ) * (W - 2 * ω)) *
          (∑ T, x.mass T * ((a + 1 : ℝ) - T.val.card)) -
        (∑ T, x.mass T * ∑ i ∈ univ \ T.val, b i) +
        ∑ T, x.mass T * residual α ω T.val := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [hm, hi, expected_omission]
      dsimp [linearPart, W, b, α, y]
      ring

/-- Exact expectation decomposition and equality on the actual positive-mass support. -/
private theorem same_law_bound {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (x : DenseLaw a δ)
    (hsort : Antitone (marginal x.mass)) :
    let y := marginal x.mass
    let t : Fin (a + 2) := ⟨2, by omega⟩
    let R := fun T : Atom a => residual (weight y) (weight y t) T.val
    energy x.mass = linearPart δ y (weight y t) + ∑ T, x.mass T * R T ∧
      linearPart δ y (weight y t) ≤ energy x.mass ∧
      (energy x.mass = linearPart δ y (weight y t) ↔
        ∀ T, 0 < x.mass T → R T = 0) := by
  dsimp only
  let y := marginal x.mass
  let t : Fin (a + 2) := ⟨2, by omega⟩
  let R := fun T : Atom a => residual (weight y) (weight y t) T.val
  have hR (T : Atom a) : 0 ≤ R T :=
    (capacity_certificate ha hδ hδu x hsort T.val T.property).1
  have hnonneg (T : Atom a) : 0 ≤ x.mass T * R T := mul_nonneg (x.nonneg T) (hR T)
  have hE : 0 ≤ ∑ T, x.mass T * R T := Finset.sum_nonneg (fun T _ => hnonneg T)
  have hid := energy_identity hδ x (weight y t)
  refine ⟨hid, by linarith, ?_⟩
  constructor
  · intro he T hT
    have hz : (∑ T, x.mass T * R T) = 0 := by linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => hnonneg T)).mp hz
    exact (mul_eq_zero.mp (hzero T (Finset.mem_univ T))).resolve_left hT.ne'
  · intro hs
    have hz : (∑ T, x.mass T * R T) = 0 := by
      apply Finset.sum_eq_zero
      intro T _
      by_cases ht : x.mass T = 0
      · rw [ht, zero_mul]
      · have hRT : R T = 0 := hs T (lt_of_le_of_ne (x.nonneg T) (Ne.symm ht))
        rw [hRT, mul_zero]
    linarith

private def reciprocal (A B z : ℝ) : ℝ := A / z - B / z ^ 2

private lemma reciprocal_deriv (A B z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (reciprocal A B) (-A / z ^ 2 + 2 * B / z ^ 3) z := by
  convert ((hasDerivAt_const z A).div (hasDerivAt_id z) hz).sub
    ((hasDerivAt_const z B).div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz)) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma reciprocal_deriv2 (A B z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun z : ℝ => -A / z ^ 2 + 2 * B / z ^ 3)
      (2 * (A * z - 3 * B) / z ^ 4) z := by
  convert ((hasDerivAt_const z (-A)).div ((hasDerivAt_id z).pow 2)
    (pow_ne_zero 2 hz)).add
    ((hasDerivAt_const z (2 * B)).div ((hasDerivAt_id z).pow 3)
      (pow_ne_zero 3 hz)) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma reciprocal_strict {A B l u : ℝ} (hl : 0 < l)
    (hnum : ∀ z ∈ Set.Icc l u, 0 < A * z - 3 * B) :
    StrictConvexOn ℝ (Set.Icc l u) (reciprocal A B) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc l u)
  · intro z hz
    exact (reciprocal_deriv A B z (ne_of_gt (lt_of_lt_of_le hl hz.1))).continuousAt.continuousWithinAt
  · intro z hz
    have hmem := interior_subset hz
    have hp : 0 < z := lt_of_lt_of_le hl hmem.1
    have he : deriv (reciprocal A B) =ᶠ[nhds z]
        (fun z => -A / z ^ 2 + 2 * B / z ^ 3) := by
      filter_upwards [Ioi_mem_nhds hp] with t ht
      exact (reciprocal_deriv A B t ht.ne').deriv
    rw [Function.iterate_succ_apply', Function.iterate_one, he.deriv_eq,
      (reciprocal_deriv2 A B z hp.ne').deriv]
    exact div_pos (mul_pos (by norm_num) (hnum z hmem)) (pow_pos hp 4)

private lemma finite_jensen {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (D : Set ℝ) (f : ℝ → ℝ) (hf : StrictConvexOn ℝ D f)
    (y : ι → ℝ) (hy : ∀ i ∈ S, y i ∈ D) :
    (S.card : ℝ) * f ((∑ i ∈ S, y i) / S.card) ≤ ∑ i ∈ S, f (y i) ∧
      ((∑ i ∈ S, f (y i)) = (S.card : ℝ) * f ((∑ i ∈ S, y i) / S.card) →
        ∀ i ∈ S, y i = (∑ i ∈ S, y i) / S.card) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  let w := fun _ : ι => (S.card : ℝ)⁻¹
  have hw (i : ι) (_ : i ∈ S) : 0 < w i := inv_pos.mpr hcard
  have hnorm : ∑ i ∈ S, w i = 1 := by simp [w, ne_of_gt hcard]
  have havg : (∑ i ∈ S, w i • y i) = (∑ i ∈ S, y i) / S.card := by
    simp only [w, smul_eq_mul, div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  have hvalue : (∑ i ∈ S, w i • f (y i)) = (∑ i ∈ S, f (y i)) / S.card := by
    simp only [w, smul_eq_mul, div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  have hj := hf.convexOn.map_sum_le (fun i hi => (hw i hi).le) hnorm hy
  rw [havg, hvalue] at hj
  refine ⟨?_, ?_⟩
  · have := (le_div_iff₀ hcard).mp hj
    nlinarith only [this]
  · intro he i hi
    have heq : f (∑ i ∈ S, w i • y i) = ∑ i ∈ S, w i • f (y i) := by
      rw [havg, hvalue, he]
      field_simp
    have hall := (hf.map_sum_eq_iff_of_pos hw hnorm hy).mp heq
    have hsum : (∑ j ∈ S, y j) = (S.card : ℝ) * y i := by
      calc
        _ = ∑ _j ∈ S, y i := Finset.sum_congr rfl (fun j hj => hall hj hi)
        _ = _ := by simp
    rw [hsum]
    field_simp

def g0 (a : ℕ) (z : ℝ) : ℝ := (a + 1 : ℝ) ^ 2 * z⁻¹
def g1 (a : ℕ) (δ z : ℝ) : ℝ :=
  (a + 1 : ℝ) ^ 2 * z⁻¹ - (2 * a + 1 : ℝ) * δ * z⁻¹ ^ 2
def f (a : ℕ) (δ z : ℝ) : ℝ :=
  (a : ℝ) ^ 2 * z⁻¹ + (2 * a + 1 : ℝ) * (1 - δ) * z⁻¹ ^ 2
def groupedV (a : ℕ) (δ u w : ℝ) : ℝ :=
  ((a + 1 : ℝ) - δ - 2 * u - w) / (a - 1 : ℝ)
def Omega (a : ℕ) (δ u w : ℝ) : Prop :=
  threshold a δ ≤ groupedV a δ u w ∧ groupedV a δ u w ≤ w ∧ w ≤ u ∧ u ≤ 1
def F0 (a : ℕ) (δ u w : ℝ) : ℝ :=
  2 * g0 a u + g1 a δ w + (a - 1 : ℝ) * g1 a δ (groupedV a δ u w)
def F1 (a : ℕ) (δ u w : ℝ) : ℝ :=
  2 * f a δ u + (a + 1 : ℝ) ^ 2 * w⁻¹ +
    (2 * a + 1 : ℝ) * (2 * u + δ - 2) * w⁻¹ ^ 2 +
    (a - 1 : ℝ) * g1 a δ (groupedV a δ u w)
def tailSet (a : ℕ) : Finset (Fin (a + 2)) := univ.filter (fun i => 3 ≤ i.val)

private lemma split_three {a : ℕ} (ha : 1 ≤ a) (φ : Fin (a + 2) → ℝ) :
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    (∑ i, φ i) = φ z + φ o + φ t + ∑ i ∈ tailSet a, φ i := by
  dsimp only
  have he : tailSet a = univ \
      {⟨0, by omega⟩, ⟨1, by omega⟩, (⟨2, by omega⟩ : Fin (a + 2))} := by
    ext i
    simp only [tailSet, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert,
      mem_singleton, Fin.ext_iff]
    omega
  have h := Finset.sum_sdiff (f := φ) (Finset.subset_univ
    {⟨0, by omega⟩, ⟨1, by omega⟩, (⟨2, by omega⟩ : Fin (a + 2))})
  rw [← he] at h
  simpa [Fin.ext_iff, add_assoc, add_comm, add_left_comm] using h.symm

private lemma tail_card {a : ℕ} (ha : 1 ≤ a) : (tailSet a).card = a - 1 := by
  have he : tailSet a = univ \
      {⟨0, by omega⟩, ⟨1, by omega⟩, (⟨2, by omega⟩ : Fin (a + 2))} := by
    ext i
    simp only [tailSet, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert,
      mem_singleton, Fin.ext_iff]
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [Fin.ext_iff]

private lemma linear_part_grouping {a : ℕ} (ha : 1 ≤ a) (δ : ℝ)
    (y : Fin (a + 2) → ℝ) (hy : ∀ i, 0 < y i) (hsort : Antitone y) :
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    linearPart δ y (weight y t) =
      f a δ (y z) + f a δ (y o) + (a + 1 : ℝ) ^ 2 * (y t)⁻¹ +
      (2 * a + 1 : ℝ) * (y z + y o + δ - 2) * (y t)⁻¹ ^ 2 +
      ∑ i ∈ tailSet a, g1 a δ (y i) := by
  dsimp only
  let z : Fin (a + 2) := ⟨0, by omega⟩
  let o : Fin (a + 2) := ⟨1, by omega⟩
  let t : Fin (a + 2) := ⟨2, by omega⟩
  have h0 : weight y z ≤ weight y t := (weight_le_iff y z t (hy z) (hy t)).mpr
    (hsort (by change 0 ≤ 2; omega))
  have h1 : weight y o ≤ weight y t := (weight_le_iff y o t (hy o) (hy t)).mpr
    (hsort (by change 1 ≤ 2; omega))
  have htail (i : Fin (a + 2)) (hi : i ∈ tailSet a) :
      max (weight y t - weight y i) 0 = 0 := by
    have hit : t ≤ i := by
      have := (Finset.mem_filter.mp hi).2
      change 2 ≤ i.val
      omega
    have h := (weight_le_iff y t i (hy t) (hy i)).mpr (hsort hit)
    exact max_eq_right (sub_nonpos.mpr h)
  have hb := split_three ha (fun i => (1 - y i) *
    ((2 * a + 1 : ℝ) * max (weight y t - weight y i) 0))
  have htailzero : (∑ i ∈ tailSet a, (1 - y i) *
      ((2 * a + 1 : ℝ) * max (weight y t - weight y i) 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [htail i hi, mul_zero, mul_zero]
  rw [htailzero] at hb
  dsimp only [z, o, t] at h0 h1 hb ⊢
  rw [max_eq_left (sub_nonneg.mpr h0), max_eq_left (sub_nonneg.mpr h1)] at hb
  simp only [sub_self, max_self, mul_zero, add_zero] at hb
  unfold linearPart
  rw [hb, split_three ha (fun i => (y i)⁻¹), split_three ha (weight y)]
  simp only [g1, f, weight, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring_nf
  field_simp [(hy ⟨0, by omega⟩).ne', (hy ⟨1, by omega⟩).ne', (hy ⟨2, by omega⟩).ne']
  ring

private lemma grouping_domain {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (x : DenseLaw a δ) (hsort : Antitone (marginal x.mass)) :
    let y := marginal x.mass
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    let u := (y z + y o) / 2
    let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
    v = groupedV a δ u (y t) ∧ Omega a δ u (y t) := by
  dsimp only
  let y := marginal x.mass
  let z : Fin (a + 2) := ⟨0, by omega⟩
  let o : Fin (a + 2) := ⟨1, by omega⟩
  let t : Fin (a + 2) := ⟨2, by omega⟩
  let u := (y z + y o) / 2
  let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
  have haR : (4096 : ℝ) ≤ a := by exact_mod_cast ha
  have hn : (0 : ℝ) < a - 1 := by linarith
  have hcard : ((tailSet a).card : ℝ) = a - 1 := by
    rw [tail_card (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  have hmean : (∑ i, y i) = (a + 1 : ℝ) - δ :=
    (marginal_total x.mass).trans x.mean
  have hs := split_three (by omega : 1 ≤ a) y
  have hv : v = groupedV a δ u (y t) := by
    unfold groupedV
    change (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ) = _
    congr 1
    dsimp [u]
    linarith only [hmean, hs]
  have hlo : (a - 1 : ℝ) * threshold a δ ≤ ∑ i ∈ tailSet a, y i := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard] using
      Finset.sum_le_sum (s := tailSet a) (fun i _ => x.dense i)
  have hhi : (∑ i ∈ tailSet a, y i) ≤ (a - 1 : ℝ) * y t := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard] using
      Finset.sum_le_sum (s := tailSet a) (fun i hi =>
      hsort (show t ≤ i by
        have := (Finset.mem_filter.mp hi).2
        change 2 ≤ i.val
        omega))
  have hvlo : threshold a δ ≤ v := (le_div_iff₀ hn).mpr (by nlinarith only [hlo])
  have hvhi : v ≤ y t := (div_le_iff₀ hn).mpr (by nlinarith only [hhi])
  have htu : y t ≤ u := by
    have h0 := hsort (show z ≤ t by change 0 ≤ 2; omega)
    have h1 := hsort (show o ≤ t by change 1 ≤ 2; omega)
    dsimp [u]
    linarith
  have hu1 : u ≤ 1 := by
    have h0 := (marginal_bounds x hδ z).2
    have h1 := (marginal_bounds x hδ o).2
    dsimp [u]
    linarith
  exact ⟨hv, by change _ ∧ _ ∧ _ ∧ _; rw [← hv]; exact ⟨hvlo, hvhi, htu, hu1⟩⟩

/-- The second grouped bound, with the original necessary strict equality consequences. -/
private theorem grouped_second_bound {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (x : DenseLaw a δ)
    (hsort : Antitone (marginal x.mass)) :
    let y := marginal x.mass
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    let u := (y z + y o) / 2
    let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
    v = groupedV a δ u (y t) ∧ Omega a δ u (y t) ∧
      F1 a δ u (y t) ≤ energy x.mass ∧
      (energy x.mass = F1 a δ u (y t) →
        y z = u ∧ y o = u ∧ (∀ i ∈ tailSet a, y i = v) ∧
          ∀ T : Atom a, 0 < x.mass T →
            residual (weight y) (weight y t) T.val = 0) := by
  dsimp only
  let y := marginal x.mass
  let z : Fin (a + 2) := ⟨0, by omega⟩
  let o : Fin (a + 2) := ⟨1, by omega⟩
  let t : Fin (a + 2) := ⟨2, by omega⟩
  let u := (y z + y o) / 2
  let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
  let C : Finset (Fin (a + 2)) := {z, o}
  have haR : (4096 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0 : ℝ) < a := by linarith
  have hδ1 : δ < 1 := lt_of_le_of_lt hδu ((div_lt_one hap).mpr (by linarith))
  have hτ : 0 < threshold a δ := by unfold threshold; positivity
  have hmem (i : Fin (a + 2)) : y i ∈ Set.Icc (threshold a δ) 1 :=
    ⟨x.dense i, (marginal_bounds x hδ i).2⟩
  have hfc : StrictConvexOn ℝ (Set.Icc (threshold a δ) 1) (f a δ) := by
    have h := reciprocal_strict (A := (a : ℝ) ^ 2) (u := 1)
      (B := -(2 * a + 1 : ℝ) * (1 - δ)) hτ (fun ξ hξ => by
        have hp : 0 < ξ := lt_of_lt_of_le hτ hξ.1
        have hc : (0 : ℝ) < 2 * a + 1 := by positivity
        nlinarith [mul_pos (sq_pos_of_pos hap) hp, mul_pos hc (sub_pos.mpr hδ1)])
    convert h using 1
    funext ξ
    simp only [f, reciprocal, div_eq_mul_inv, inv_pow]
    ring
  have hgc : StrictConvexOn ℝ (Set.Icc (threshold a δ) 1) (g1 a δ) := by
    have ht : (a + 1 : ℝ) ^ 2 * threshold a δ -
        3 * ((2 * a + 1 : ℝ) * δ) = 6 * δ := by
      unfold threshold
      field_simp
      ring
    have h := reciprocal_strict (A := (a + 1 : ℝ) ^ 2) (u := 1)
      (B := (2 * a + 1 : ℝ) * δ) hτ (fun ξ hξ => by
        have hm := mul_nonneg (sq_nonneg (a + 1 : ℝ)) (sub_nonneg.mpr hξ.1)
        nlinarith only [hm, ht, hδ])
    convert h using 1
    funext ξ
    simp only [g1, reciprocal, div_eq_mul_inv, inv_pow]
  have hCcard : C.card = 2 := by simp [C, z, o, Fin.ext_iff]
  have hCavg : (∑ i ∈ C, y i) / C.card = u := by
    simp [C, z, o, Fin.ext_iff, u]
  have hhead := finite_jensen C (by simp [C]) _ _ hfc y (fun i _ => hmem i)
  rw [hCavg, hCcard] at hhead
  norm_num only [Nat.cast_ofNat] at hhead
  have hQcard : ((tailSet a).card : ℝ) = a - 1 := by
    rw [tail_card (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  have hQne : (tailSet a).Nonempty := Finset.card_pos.mp (by
    rw [tail_card (by omega : 1 ≤ a)]; omega)
  have htail := finite_jensen (tailSet a) hQne _ _ hgc y (fun i _ => hmem i)
  rw [hQcard] at htail
  have hgeom := grouping_domain ha hδ x hsort
  have hbase := same_law_bound ha hδ hδu x hsort
  have hgroup := linear_part_grouping (by omega : 1 ≤ a) δ y
    (fun i => (marginal_bounds x hδ i).1) hsort
  have hCs : (∑ i ∈ C, f a δ (y i)) = f a δ (y z) + f a δ (y o) := by
    simp [C, z, o, Fin.ext_iff]
  rw [hCs] at hhead
  have hform : F1 a δ u (y t) = 2 * f a δ u + (a + 1 : ℝ) ^ 2 * (y t)⁻¹ +
      (2 * a + 1 : ℝ) * (y z + y o + δ - 2) * (y t)⁻¹ ^ 2 +
      (a - 1 : ℝ) * g1 a δ v := by
    unfold F1
    rw [← hgeom.1]
    dsimp only [u]
    ring
  refine ⟨hgeom.1, hgeom.2, ?_, ?_⟩
  · rw [hform]
    linarith only [hhead.1, htail.1, hgroup, hbase.2.1]
  · intro he
    have hheadEq : f a δ (y z) + f a δ (y o) = 2 * f a δ u := by
      rw [hform] at he
      linarith only [he, hhead.1, htail.1, hgroup, hbase.2.1]
    have htailEq : (∑ i ∈ tailSet a, g1 a δ (y i)) = (a - 1 : ℝ) * g1 a δ v := by
      rw [hform] at he
      linarith only [he, hhead.1, htail.1, hgroup, hbase.2.1]
    have hEL : energy x.mass = linearPart δ y (weight y t) := by
      rw [hform] at he
      linarith only [he, hhead.1, htail.1, hgroup, hbase.2.1]
    exact ⟨hhead.2 hheadEq z (by simp [C]), hhead.2 hheadEq o (by simp [C]),
      htail.2 htailEq, hbase.2.2.mp hEL⟩

private lemma omitted_pair_lower {a : ℕ} (α : Fin (a + 2) → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hmono : Monotone α)
    (J : Finset (Fin (a + 2))) (hJ : 2 ≤ J.card) :
    α ⟨0, by omega⟩ + α ⟨1, by omega⟩ ≤ ∑ i ∈ J, α i := by
  obtain ⟨P, hPJ, hP⟩ := Finset.exists_subset_card_eq hJ
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hP
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hPJ (fun k _ _ => hα k)
  simp only [Finset.sum_pair hij] at hsum
  apply le_trans _ hsum
  have hmin (k : Fin (a + 2)) : α ⟨0, by omega⟩ ≤ α k :=
    hmono (show (⟨0, by omega⟩ : Fin (a + 2)) ≤ k by change 0 ≤ k.val; omega)
  by_cases hi : i = ⟨0, by omega⟩
  · rw [hi]
    have hj : (⟨1, by omega⟩ : Fin (a + 2)) ≤ j := by
      have : j.val ≠ 0 := by
        intro h
        apply hij
        apply Fin.ext
        exact (congrArg Fin.val hi).trans h.symm
      change 1 ≤ j.val
      omega
    linarith [hmono hj]
  · have hi' : (⟨1, by omega⟩ : Fin (a + 2)) ≤ i := by
      have : i.val ≠ 0 := by intro h; apply hi; ext; exact h
      change 1 ≤ i.val
      omega
    linarith [hmono hi', hmin j]

/-- The first grouped bound uses the two smallest actual inverse-square weights. -/
private theorem grouped_first_bound {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (x : DenseLaw a δ)
    (hsort : Antitone (marginal x.mass)) :
    let y := marginal x.mass
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    F0 a δ ((y z + y o) / 2) (y t) ≤ energy x.mass := by
  dsimp only
  let y := marginal x.mass
  let z : Fin (a + 2) := ⟨0, by omega⟩
  let o : Fin (a + 2) := ⟨1, by omega⟩
  let t : Fin (a + 2) := ⟨2, by omega⟩
  let α := weight y
  let W := ∑ i, α i
  let M := W - α z - α o
  let G := fun T : Atom a => ((a + 1 : ℝ) - T.val.card) *
    ((2 * a + 1 : ℝ) * M - ((a + 1 : ℝ) + T.val.card) * ∑ i ∈ T.val, α i)
  have hα (i : Fin (a + 2)) : 0 ≤ α i := sq_nonneg _
  have hmono : Monotone α := by
    intro i j hij
    exact (weight_le_iff y i j (marginal_bounds x hδ i).1
      (marginal_bounds x hδ j).1).mpr (hsort hij)
  have hG (T : Atom a) : 0 ≤ G T := by
    let J := univ \ T.val
    have hjk : J.card + T.val.card = a + 2 := by
      simpa [J] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T.val)
    have hs : (∑ i ∈ J, α i) + (∑ i ∈ T.val, α i) = W :=
      Finset.sum_sdiff (Finset.subset_univ T.val)
    have hWT : 0 ≤ ∑ i ∈ T.val, α i := Finset.sum_nonneg (fun i _ => hα i)
    have hc : (0 : ℝ) ≤ 2 * a + 1 := by positivity
    by_cases hk : T.val.card ≤ a
    · have hJ := omitted_pair_lower α hα hmono J (by omega : 2 ≤ J.card)
      have hMT : (∑ i ∈ T.val, α i) ≤ M := by dsimp [M]; linarith only [hs, hJ]
      have hkR : (T.val.card : ℝ) ≤ a := by exact_mod_cast hk
      have hbr : 0 ≤ (2 * a + 1 : ℝ) * M -
          ((a + 1 : ℝ) + T.val.card) * (∑ i ∈ T.val, α i) := by
        nlinarith only [mul_nonneg hc (sub_nonneg.mpr hMT),
          mul_nonneg (show (0 : ℝ) ≤ a - T.val.card by linarith) hWT]
      exact mul_nonneg (by change (0 : ℝ) ≤ a + 1 - T.val.card; linarith) hbr
    · have hkmax : T.val.card ≤ a + 2 := by simpa using T.val.card_le_univ
      rcases (show T.val.card = a + 1 ∨ T.val.card = a + 2 by omega) with hk1 | hk2
      · dsimp [G]
        rw [hk1]
        push_cast
        ring_nf
        exact le_rfl
      · have hJ : J = ∅ := Finset.card_eq_zero.mp (by omega)
        have hTW : (∑ i ∈ T.val, α i) = W := by simpa [hJ] using hs
        have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ => hα i)
        have hMW : M ≤ W := by dsimp [M]; linarith [hα z, hα o]
        dsimp [G]
        rw [hk2, hTW]
        push_cast
        nlinarith only [hW, mul_nonneg hc (sub_nonneg.mpr hMW)]
  have hi : (∑ T, x.mass T * ∑ i ∈ T.val, α i) = ∑ i, (y i)⁻¹ := by
    rw [expected_incidence]
    apply Finset.sum_congr rfl
    intro i _
    have hy := (marginal_bounds x hδ i).1.ne'
    change (y i)⁻¹ ^ 2 * y i = (y i)⁻¹
    field_simp
  have hm : (∑ T, x.mass T * ((a + 1 : ℝ) - T.val.card)) = δ := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, x.total,
      x.mean, one_mul]
    ring
  have hloweq :
      (∑ T, x.mass T * ((a + 1 : ℝ) ^ 2 * (∑ i ∈ T.val, α i) -
        (2 * a + 1 : ℝ) * M * ((a + 1 : ℝ) - T.val.card))) =
      (a + 1 : ℝ) ^ 2 * (∑ T, x.mass T * ∑ i ∈ T.val, α i) -
        ((2 * a + 1 : ℝ) * M) * (∑ T, x.mass T * ((a + 1 : ℝ) - T.val.card)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro T _; ring
    · congr 1 <;> apply Finset.sum_congr rfl <;> intro T _ <;> ring
  have hsum := Finset.sum_le_sum (s := univ) (fun T _ =>
    show x.mass T * ((a + 1 : ℝ) ^ 2 * (∑ i ∈ T.val, α i) -
      (2 * a + 1 : ℝ) * M * ((a + 1 : ℝ) - T.val.card)) ≤
      x.mass T * (T.val.card : ℝ) ^ 2 * (∑ i ∈ T.val, α i) from by
        have h := mul_nonneg (x.nonneg T) (hG T)
        dsimp [G] at h
        nlinarith only [h])
  rw [hloweq, hi, hm] at hsum
  have hraw : (a + 1 : ℝ) ^ 2 * (∑ i, (y i)⁻¹) -
      (2 * a + 1 : ℝ) * δ * M ≤ energy x.mass := by
    change _ ≤ energy x.mass at hsum
    nlinarith only [hsum]
  have hgroup : (a + 1 : ℝ) ^ 2 * (∑ i, (y i)⁻¹) - (2 * a + 1 : ℝ) * δ * M =
      g0 a (y z) + g0 a (y o) + g1 a δ (y t) + ∑ i ∈ tailSet a, g1 a δ (y i) := by
    dsimp [M, W]
    rw [split_three (by omega : 1 ≤ a) (fun i => (y i)⁻¹),
      split_three (by omega : 1 ≤ a) α]
    simp only [g0, g1, α, weight, Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp [z, o, t]
    ring
  have hτ : 0 < threshold a δ := by unfold threshold; positivity
  have hmem (i : Fin (a + 2)) : y i ∈ Set.Icc (threshold a δ) 1 :=
    ⟨x.dense i, (marginal_bounds x hδ i).2⟩
  have hg0 : StrictConvexOn ℝ (Set.Icc (threshold a δ) 1) (g0 a) := by
    have h := reciprocal_strict (A := (a + 1 : ℝ) ^ 2) (B := 0) (u := 1) hτ
      (fun ξ hξ => by
        have hp : 0 < ξ := lt_of_lt_of_le hτ hξ.1
        simpa only [mul_zero, sub_zero] using
          mul_pos (sq_pos_of_pos (show (0 : ℝ) < a + 1 by positivity)) hp)
    convert h using 1
    funext ξ
    simp [g0, reciprocal, div_eq_mul_inv]
  have hg1 : StrictConvexOn ℝ (Set.Icc (threshold a δ) 1) (g1 a δ) := by
    have ht : (a + 1 : ℝ) ^ 2 * threshold a δ -
        3 * ((2 * a + 1 : ℝ) * δ) = 6 * δ := by unfold threshold; field_simp; ring
    have h := reciprocal_strict (A := (a + 1 : ℝ) ^ 2) (B := (2 * a + 1 : ℝ) * δ)
      (u := 1) hτ (fun ξ hξ => by
        have hm := mul_nonneg (sq_nonneg (a + 1 : ℝ)) (sub_nonneg.mpr hξ.1)
        nlinarith only [hm, ht, hδ])
    convert h using 1
    funext ξ
    simp only [g1, reciprocal, div_eq_mul_inv, inv_pow]
  let C : Finset (Fin (a + 2)) := {z, o}
  have hhead := (finite_jensen C (by simp [C]) _ _ hg0 y (fun i _ => hmem i)).1
  have htail := (finite_jensen (tailSet a) (Finset.card_pos.mp (by
    rw [tail_card (by omega : 1 ≤ a)]; omega)) _ _ hg1 y (fun i _ => hmem i)).1
  have hcard : ((tailSet a).card : ℝ) = a - 1 := by
    rw [tail_card (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]; norm_num
  simp only [C, Finset.sum_pair (show z ≠ o by simp [z, o, Fin.ext_iff]),
    Finset.card_pair (show z ≠ o by simp [z, o, Fin.ext_iff]), Nat.cast_ofNat] at hhead
  rw [hcard, (grouping_domain ha hδ x hsort).1] at htail
  unfold F0
  linarith only [hhead, htail, hgroup, hraw]

/-- The whole capacity lemma, on a single native law and all nonempty subsets. -/
theorem capacity_lemma {a : ℕ} (ha : 4096 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ 1 / (a : ℝ)) (mass : Atom a → ℝ)
    (hnonneg : ∀ T, 0 ≤ mass T) (htotal : ∑ T, mass T = 1)
    (hmean : ∑ T, mass T * (T.val.card : ℝ) = (a + 1 : ℝ) - δ)
    (hdense : ∀ i, threshold a δ ≤ marginal mass i)
    (hsort : Antitone (marginal mass)) :
    let y := marginal mass
    let z : Fin (a + 2) := ⟨0, by omega⟩
    let o : Fin (a + 2) := ⟨1, by omega⟩
    let t : Fin (a + 2) := ⟨2, by omega⟩
    let u := (y z + y o) / 2
    let v := (∑ i ∈ tailSet a, y i) / (a - 1 : ℝ)
    (∀ T : Finset (Fin (a + 2)), T.Nonempty →
      0 ≤ residual (weight y) (weight y t) T ∧
        (residual (weight y) (weight y t) T = 0 ↔
          (T.card = a + 1 ∧ ∃ i, univ \ T = {i} ∧ y i ≤ y t) ∨
          (T.card = a ∧ ∃ i j, i ≠ j ∧ univ \ T = {i, j} ∧ y t ≤ y i ∧ y t ≤ y j))) ∧
      v = groupedV a δ u (y t) ∧ Omega a δ u (y t) ∧
      max (F0 a δ u (y t)) (F1 a δ u (y t)) ≤ energy mass ∧
      (energy mass = F1 a δ u (y t) →
        y z = u ∧ y o = u ∧ (∀ i ∈ tailSet a, y i = v) ∧
          ∀ T : Atom a, 0 < mass T → residual (weight y) (weight y t) T.val = 0) ∧
      energy mass = linearPart δ y (weight y t) +
        ∑ T : Atom a, mass T * residual (weight y) (weight y t) T.val := by
  let x : DenseLaw a δ := ⟨mass, hnonneg, htotal, hmean, hdense⟩
  have hp := capacity_certificate ha hδ hδu x hsort
  have hs := grouped_second_bound ha hδ hδu x hsort
  have hf := grouped_first_bound ha hδ hδu x hsort
  have he := same_law_bound ha hδ hδu x hsort
  exact ⟨hp, hs.1, hs.2.1, max_le hf hs.2.2.1, hs.2.2.2, he.1⟩

#print axioms capacity_lemma

end D5.S3.Combinatorics.Probability.CdsoCapacityCertificate
