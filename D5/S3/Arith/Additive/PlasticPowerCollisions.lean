/- GID: D5/S3/Arith/Additive/PlasticPowerCollisions
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticPowerCollisions
   mirror-E: none(waiver:algebraic-power-collisions)
   anchors: []
   utility: none
   digest: Integer powers of a plastic root have exactly four nontrivial normalized sum collisions. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

/-! Integer-exponent difference equations and normalized equal sums for a plastic root. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticPowerCollisions

open scoped Pointwise

private theorem step_identities (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1) :
    r ^ (1 : ℤ) - 1 = r ^ (-4 : ℤ) ∧
    r ^ (2 : ℤ) - 1 = r ^ (-1 : ℤ) ∧ 2 < r ^ (3 : ℤ) := by
  have hr0 : r ≠ 0 := by linarith
  constructor
  · norm_num only [zpow_one, zpow_neg, zpow_ofNat]
    rw [inv_eq_one_div]
    apply (eq_div_iff (pow_ne_zero 4 hr0)).2
    linear_combination (r ^ 2 - r + 1) * hroot
  constructor
  · norm_num only [zpow_neg, zpow_ofNat, pow_one]
    rw [inv_eq_one_div]
    apply (eq_div_iff hr0).2
    linear_combination hroot
  · norm_num only [zpow_ofNat]
    linarith

/-- The complete integer-exponent difference equation, including negative exponents. -/
theorem difference_eq_one_iff (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (u v : ℤ) :
    r ^ u - r ^ v = 1 ↔
      (u = 1 ∧ v = -4) ∨ (u = 2 ∧ v = -1) ∨
      (u = 3 ∧ v = 1) ∨ (u = 5 ∧ v = 4) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hm := zpow_right_strictMono₀ hr
  obtain ⟨hs1, hs2, hs3⟩ := step_identities r hr hroot
  constructor
  · intro h
    have hupos : 0 < u := (one_lt_zpow_iff_right₀ hr).1 (by
      have := zpow_pos hrpos v
      linarith)
    have huv : v < u := hm.lt_iff_lt.1 (by linarith)
    by_cases hv : v < 0
    · have hvone : r ^ v < 1 := zpow_lt_one_of_neg₀ hr hv
      have hu3 : u < 3 := hm.lt_iff_lt.1
        (lt_trans (show r ^ u < 2 by linarith) hs3)
      have hu : u = 1 ∨ u = 2 := by omega
      rcases hu with rfl | rfl
      · left
        refine ⟨rfl, hm.injective ?_⟩
        linarith
      · right; left
        refine ⟨rfl, hm.injective ?_⟩
        linarith
    · have hv0 : 0 ≤ v := by omega
      have hpv : 1 ≤ r ^ v := one_le_zpow₀ (le_of_lt hr) hv0
      have hgap : r ^ (u - v) - 1 = r ^ (-v) := by
        rw [zpow_sub₀ hr0, zpow_neg]
        field_simp
        nlinarith
      have hgap3 : u - v < 3 := hm.lt_iff_lt.1 (show r ^ (u - v) < r ^ (3 : ℤ) from by
        have hinv : r ^ (-v) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hr) (by omega)
        exact lt_of_le_of_lt (show r ^ (u - v) ≤ 2 by linarith) hs3)
      have hgap12 : u - v = 1 ∨ u - v = 2 := by omega
      rcases hgap12 with hg | hg
      · rw [hg, hs1] at hgap
        have hv4 : v = 4 := by have := hm.injective hgap; omega
        right; right; right
        exact ⟨by omega, hv4⟩
      · rw [hg, hs2] at hgap
        have hv1 : v = 1 := by have := hm.injective hgap; omega
        right; right; left
        exact ⟨by omega, hv1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · linarith
    · linarith
    · norm_num only [zpow_ofNat, zpow_one]
      linarith
    · norm_num only [zpow_ofNat]
      linear_combination (r ^ 2 - r + 1) * hroot

/-- All nontrivial normalized equal sums, with the diagonal inner pair retained. -/
theorem normalized_collision_iff (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (d a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b < d) :
    1 + r ^ d = r ^ a + r ^ b ↔
      (d = 4 ∧ a = 2 ∧ b = 3) ∨ (d = 6 ∧ a = 3 ∧ b = 5) ∨
      (d = 7 ∧ a = 5 ∧ b = 5) ∨ (d = 9 ∧ a = 5 ∧ b = 8) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hm := zpow_right_strictMono₀ hr
  obtain ⟨hs1, hs2, hs3⟩ := step_identities r hr hroot
  constructor
  · intro h
    have hgap : r ^ (d - b) = 1 + r ^ (a - b) - r ^ (-b) := by
      rw [zpow_sub₀ hr0, zpow_sub₀ hr0, zpow_neg]
      field_simp
      nlinarith
    have hslt : d - b < 3 := hm.lt_iff_lt.1
      (show r ^ (d - b) < r ^ (3 : ℤ) from by
        have hab1 : r ^ (a - b) ≤ 1 :=
          zpow_le_one_of_nonpos₀ (le_of_lt hr) (by omega)
        have hbinv : 0 < r ^ (-b) := zpow_pos hrpos _
        exact lt_trans (show r ^ (d - b) < 2 by linarith) hs3)
    have hs : d - b = 1 ∨ d - b = 2 := by omega
    rcases hs with hs | hs
    · have hd : d = b + 1 := by omega
      have hshift : r ^ (b - 4) = r ^ b * (r ^ (1 : ℤ) - 1) := by
        rw [show b - 4 = b + (-4) by omega, zpow_add₀ hr0, ← hs1]
      have hdiff : r ^ a - r ^ (b - 4) = 1 := by
        rw [hd, zpow_add₀ hr0] at h
        rw [hshift]
        nlinarith
      have hc := (difference_eq_one_iff r hr hroot a (b - 4)).1 hdiff
      rcases hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · omega
      · left; exact ⟨by omega, ha', by omega⟩
      · right; left; exact ⟨by omega, ha', by omega⟩
      · right; right; right; exact ⟨by omega, ha', by omega⟩
    · have hd : d = b + 2 := by omega
      have hshift : r ^ (b - 1) = r ^ b * (r ^ (2 : ℤ) - 1) := by
        rw [show b - 1 = b + (-1) by omega, zpow_add₀ hr0, ← hs2]
      have hdiff : r ^ a - r ^ (b - 1) = 1 := by
        rw [hd, zpow_add₀ hr0] at h
        rw [hshift]
        nlinarith
      have hc := (difference_eq_one_iff r hr hroot a (b - 1)).1 hdiff
      rcases hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · omega
      · omega
      · omega
      · right; right; left; exact ⟨by omega, ha', by omega⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num only [zpow_ofNat]
    · linear_combination (r - 1) * hroot
    · linear_combination (r ^ 3 - r ^ 2 + r - 1) * hroot
    · linear_combination (r ^ 4 - r ^ 2 + r - 1) * hroot
    · linear_combination
        (r ^ 6 - r ^ 5 + r ^ 4 - r ^ 2 + r - 1) * hroot

/-- Translation of the four templates to two distinct sorted integer-exponent pairs. -/
theorem sorted_collision_iff (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (i j k l : ℤ) (hij : i ≤ j) (hkl : k ≤ l) (hik : i < k) :
    r ^ i + r ^ j = r ^ k + r ^ l ↔
      (j = i + 4 ∧ k = i + 2 ∧ l = i + 3) ∨
      (j = i + 6 ∧ k = i + 3 ∧ l = i + 5) ∨
      (j = i + 7 ∧ k = i + 5 ∧ l = i + 5) ∨
      (j = i + 9 ∧ k = i + 5 ∧ l = i + 8) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hm := zpow_right_strictMono₀ hr
  constructor
  · intro h
    have hlj : l < j := hm.lt_iff_lt.1 (by have := hm hik; linarith)
    have hc : 1 + r ^ (j - i) = r ^ (k - i) + r ^ (l - i) := by
      simp only [zpow_sub₀ hr0]
      field_simp
      nlinarith
    have ht := (normalized_collision_iff r hr hroot (j-i) (k-i) (l-i)
      (by omega) (by omega) (by omega)).1 hc
    rcases ht with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · intro ht
    have hc : 1 + r ^ (j - i) = r ^ (k - i) + r ^ (l - i) := by
      apply (normalized_collision_iff r hr hroot (j-i) (k-i) (l-i)
        (by rcases ht with h | h | h | h <;> omega)
        (by rcases ht with h | h | h | h <;> omega)
        (by rcases ht with h | h | h | h <;> omega)).2
      rcases ht with h | h | h | h
      · left; omega
      · right; left; omega
      · right; right; left; omega
      · right; right; right; omega
    simp only [zpow_sub₀ hr0] at hc
    field_simp at hc
    nlinarith

private theorem sorted_pair_first_ne (r : ℝ) (hr : 1 < r)
    (p q : ℤ × ℤ) (hpq : p ≠ q)
    (h : r ^ p.1 + r ^ p.2 = r ^ q.1 + r ^ q.2) : p.1 ≠ q.1 := by
  intro he
  have he' : p.2 = q.2 := (zpow_right_strictMono₀ hr).injective (by rw [he] at h; linarith)
  exact hpq (Prod.ext he he')

private theorem no_three_sorted_pairs (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (p q s : ℤ × ℤ) (hp : p.1 ≤ p.2) (hq : q.1 ≤ q.2) (hs : s.1 ≤ s.2)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (heq : r ^ p.1 + r ^ p.2 = r ^ q.1 + r ^ q.2)
    (hes : r ^ p.1 + r ^ p.2 = r ^ s.1 + r ^ s.2) : False := by
  have hnq := sorted_pair_first_ne r hr p q hpq heq
  have hns := sorted_pair_first_ne r hr p s hps hes
  have hqs' : r ^ q.1 + r ^ q.2 = r ^ s.1 + r ^ s.2 := heq.symm.trans hes
  have hnqs := sorted_pair_first_ne r hr q s hqs hqs'
  have hc := sorted_collision_iff r hr hroot
  rcases lt_or_gt_of_ne hnq with hlt | hgt
  · have h1 := (hc p.1 p.2 q.1 q.2 hp hq hlt).1 heq
    rcases lt_or_gt_of_ne hnqs with hlt' | hgt'
    · have h2 := (hc q.1 q.2 s.1 s.2 hq hs hlt').1 hqs'
      rcases h1 with h1 | h1 | h1 | h1 <;>
        rcases h2 with h2 | h2 | h2 | h2 <;> omega
    · by_cases hlt'' : p.1 < s.1
      · have h2 := (hc p.1 p.2 s.1 s.2 hp hs hlt'').1 hes
        rcases h1 with h1 | h1 | h1 | h1 <;>
          rcases h2 with h2 | h2 | h2 | h2 <;> omega
      · have h2 := (hc s.1 s.2 p.1 p.2 hs hp (by omega)).1 hes.symm
        rcases h1 with h1 | h1 | h1 | h1 <;>
          rcases h2 with h2 | h2 | h2 | h2 <;> omega
  · have h1 := (hc q.1 q.2 p.1 p.2 hq hp hgt).1 heq.symm
    rcases lt_or_gt_of_ne hns with hlt' | hgt'
    · have h2 := (hc p.1 p.2 s.1 s.2 hp hs hlt').1 hes
      rcases h1 with h1 | h1 | h1 | h1 <;>
        rcases h2 with h2 | h2 | h2 | h2 <;> omega
    · have h2 := (hc s.1 s.2 p.1 p.2 hs hp hgt').1 hes.symm
      rcases h1 with h1 | h1 | h1 | h1 <;>
        rcases h2 with h2 | h2 | h2 | h2 <;> omega

/-- Each actual real sum has at most two unordered representations in any finite integer power set. -/
theorem sum_fiber_card_le_two (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) (x : ℝ) :
    ((E ×ˢ E).filter (fun p => p.1 ≤ p.2 ∧ r ^ p.1 + r ^ p.2 = x)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨p, hp, q, hq, s, hs, hpq, hps, hqs⟩ := Finset.two_lt_card.1 (by omega :
    2 < ((E ×ˢ E).filter (fun p => p.1 ≤ p.2 ∧ r ^ p.1 + r ^ p.2 = x)).card)
  simp only [Finset.mem_filter] at hp hq hs
  exact no_three_sorted_pairs r hr hroot p q s hp.2.1 hq.2.1 hs.2.1 hpq hps hqs
    (hp.2.2.trans hq.2.2.symm) (hp.2.2.trans hs.2.2.symm)

private def outerCollision (E : Finset ℤ) (p : ℤ × ℤ) : Prop :=
  (p.2 = p.1 + 4 ∧ p.1 + 2 ∈ E ∧ p.1 + 3 ∈ E) ∨
  (p.2 = p.1 + 6 ∧ p.1 + 3 ∈ E ∧ p.1 + 5 ∈ E) ∨
  (p.2 = p.1 + 7 ∧ p.1 + 5 ∈ E) ∨
  (p.2 = p.1 + 9 ∧ p.1 + 5 ∈ E ∧ p.1 + 8 ∈ E)

private theorem outer_iff_partner (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) (p : ℤ × ℤ) (hp : p.1 ≤ p.2) :
    outerCollision E p ↔ ∃ q ∈ E ×ˢ E, q.1 ≤ q.2 ∧ p.1 < q.1 ∧
      r ^ p.1 + r ^ p.2 = r ^ q.1 + r ^ q.2 := by
  constructor
  · intro h
    rcases h with ⟨h, ha, hb⟩ | ⟨h, ha, hb⟩ | ⟨h, ha⟩ | ⟨h, ha, hb⟩
    · refine ⟨(p.1+2,p.1+3), Finset.mem_product.2 ⟨ha,hb⟩, by dsimp; omega,
        by dsimp; omega, ?_⟩
      exact (sorted_collision_iff r hr hroot _ _ _ _ hp (by omega) (by omega)).2
        (Or.inl ⟨h,rfl,rfl⟩)
    · refine ⟨(p.1+3,p.1+5), Finset.mem_product.2 ⟨ha,hb⟩, by dsimp; omega,
        by dsimp; omega, ?_⟩
      exact (sorted_collision_iff r hr hroot _ _ _ _ hp (by omega) (by omega)).2
        (Or.inr (Or.inl ⟨h,rfl,rfl⟩))
    · refine ⟨(p.1+5,p.1+5), Finset.mem_product.2 ⟨ha,ha⟩, le_refl _,
        by dsimp; omega, ?_⟩
      exact (sorted_collision_iff r hr hroot _ _ _ _ hp (le_refl _) (by omega)).2
        (Or.inr (Or.inr (Or.inl ⟨h,rfl,rfl⟩)))
    · refine ⟨(p.1+5,p.1+8), Finset.mem_product.2 ⟨ha,hb⟩, by dsimp; omega,
        by dsimp; omega, ?_⟩
      exact (sorted_collision_iff r hr hroot _ _ _ _ hp (by omega) (by omega)).2
        (Or.inr (Or.inr (Or.inr ⟨h,rfl,rfl⟩)))
  · rintro ⟨q, hq, hqs, hpq, he⟩
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.1 hq
    have hc := (sorted_collision_iff r hr hroot _ _ _ _ hp hqs hpq).1 he
    rcases hc with ⟨hd,ha,hb⟩ | ⟨hd,ha,hb⟩ | ⟨hd,ha,hb⟩ | ⟨hd,ha,hb⟩
    · exact Or.inl ⟨hd, ha ▸ hq1, hb ▸ hq2⟩
    · exact Or.inr (Or.inl ⟨hd, ha ▸ hq1, hb ▸ hq2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hd, ha ▸ hq1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hd, ha ▸ hq1, hb ▸ hq2⟩))

/-- Removing the outer representation of each translated template gives precisely one
representative of every actual real sum. The right-hand side counts actual exponent pairs. -/
theorem sumset_card_eq_reduced_pairs (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) :
    ((E.image (fun e => r ^ e)) + (E.image (fun e => r ^ e))).card =
      ((E ×ˢ E).filter (fun p => p.1 ≤ p.2 ∧ ¬ (
        (p.2 = p.1 + 4 ∧ p.1 + 2 ∈ E ∧ p.1 + 3 ∈ E) ∨
        (p.2 = p.1 + 6 ∧ p.1 + 3 ∈ E ∧ p.1 + 5 ∈ E) ∨
        (p.2 = p.1 + 7 ∧ p.1 + 5 ∈ E) ∨
        (p.2 = p.1 + 9 ∧ p.1 + 5 ∈ E ∧ p.1 + 8 ∈ E)))).card := by
  classical
  let P := (E ×ˢ E).filter (fun p => p.1 ≤ p.2 ∧ ¬ outerCollision E p)
  let f : ℤ × ℤ → ℝ := fun p => r ^ p.1 + r ^ p.2
  have hi : Set.InjOn f P := by
    intro p hp q hq he
    obtain ⟨hpE,hp,hpn⟩ := Finset.mem_filter.1 hp
    obtain ⟨hqE,hq,hqn⟩ := Finset.mem_filter.1 hq
    by_contra hn
    have hne := sorted_pair_first_ne r hr p q hn he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hpn ((outer_iff_partner r hr hroot E p hp).2 ⟨q,hqE,hq,hlt,he⟩)
    · exact hqn ((outer_iff_partner r hr hroot E q hq).2 ⟨p,hpE,hp,hgt,he.symm⟩)
  have himage : P.image f = E.image (fun e => r ^ e) + E.image (fun e => r ^ e) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hpE,_,_⟩ := Finset.mem_filter.1 hp
      obtain ⟨hp1,hp2⟩ := Finset.mem_product.1 hpE
      exact Finset.mem_add.2 ⟨r^p.1,Finset.mem_image.2 ⟨_,hp1,rfl⟩,
        r^p.2,Finset.mem_image.2 ⟨_,hp2,rfl⟩,rfl⟩
    · rintro hx
      obtain ⟨u,hu,v,hv,hx⟩ := Finset.mem_add.1 hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hv
      have hpair : ∃ p ∈ E ×ˢ E, p.1 ≤ p.2 ∧ f p = x := by
        by_cases hij : i ≤ j
        · exact ⟨(i,j),Finset.mem_product.2 ⟨hi,hj⟩,hij,hx⟩
        · exact ⟨(j,i),Finset.mem_product.2 ⟨hj,hi⟩,by omega,by dsimp [f]; linarith⟩
      obtain ⟨p,hpE,hp,hpx⟩ := hpair
      by_cases hb : outerCollision E p
      · obtain ⟨q,hqE,hq,hpq,he⟩ := (outer_iff_partner r hr hroot E p hp).1 hb
        have hqn : ¬ outerCollision E q := by
          intro hbad
          obtain ⟨s,_,hs,hqs,he'⟩ := (outer_iff_partner r hr hroot E q hq).1 hbad
          exact no_three_sorted_pairs r hr hroot p q s hp hq hs
            (by intro h; subst q; omega) (by intro h; subst s; omega)
            (by intro h; subst s; omega) he (he.trans he')
        exact Finset.mem_image.2 ⟨q,Finset.mem_filter.2 ⟨hqE,hq,hqn⟩,he.symm.trans hpx⟩
      · exact Finset.mem_image.2 ⟨p,Finset.mem_filter.2 ⟨hpE,hp,hb⟩,hpx⟩
  have hh : (E.image (fun e => r ^ e) + E.image (fun e => r ^ e)).card = P.card := by
    rw [← himage]
    exact Finset.card_image_of_injOn hi
  refine hh.trans ?_
  apply congrArg Finset.card
  ext p
  constructor
  · intro h
    exact Finset.mem_filter.2 (Finset.mem_filter.1 h)
  · intro h
    exact Finset.mem_filter.2 (Finset.mem_filter.1 h)

private def templatePairs (E : Finset ℤ) (d a b : ℤ) : Finset (ℤ × ℤ) :=
  (E.filter (fun t => t+a ∈ E ∧ t+b ∈ E ∧ t+d ∈ E)).image (fun t => (t,t+d))

private theorem templatePairs_mem (E : Finset ℤ) (d a b : ℤ) (p : ℤ × ℤ) :
    p ∈ templatePairs E d a b ↔
      p.1 ∈ E ∧ p.2 = p.1+d ∧ p.1+a ∈ E ∧ p.1+b ∈ E ∧ p.1+d ∈ E := by
  simp only [templatePairs, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t,⟨ht,ha,hb,hd⟩,rfl⟩
    exact ⟨ht,rfl,ha,hb,hd⟩
  · rintro ⟨hp,hd,ha,hb,hdE⟩
    exact ⟨p.1,⟨hp,ha,hb,hdE⟩,Prod.ext rfl hd.symm⟩

private theorem templatePairs_disjoint (E : Finset ℤ) (d a b d' a' b' : ℤ)
    (h : d ≠ d') : Disjoint (templatePairs E d a b) (templatePairs E d' a' b') := by
  apply Finset.disjoint_left.2
  intro p hp hq
  rw [templatePairs_mem] at hp hq
  exact h (by omega)

/-- The exact sumset identity for every finite integer exponent set. All four template
counts refer to translates inside that same set; the additive form has no truncated subtraction. -/
theorem sumset_card_add_template_counts (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) :
    ((E.image (fun e => r ^ e)) + (E.image (fun e => r ^ e))).card +
      (E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E)).card +
      (E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E)).card =
      (E.card+1).choose 2 := by
  classical
  let P := (E ×ˢ E).filter (fun p => p.1 ≤ p.2)
  let O := P.filter (outerCollision E)
  let Q := P.filter (fun p => ¬ outerCollision E p)
  have hsum : ((E.image (fun e => r ^ e)) + (E.image (fun e => r ^ e))).card = Q.card := by
    have hh := sumset_card_eq_reduced_pairs r hr hroot E
    refine hh.trans ?_
    apply congrArg Finset.card
    ext p
    constructor
    · intro h
      obtain ⟨hp,hps,hpn⟩ := Finset.mem_filter.1 h
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp,hps⟩,hpn⟩
    · intro h
      obtain ⟨hp,hpn⟩ := Finset.mem_filter.1 h
      obtain ⟨hp,hps⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨hp,hps,hpn⟩
  have hpartition : Q.card + O.card = P.card := by
    simpa only [Q,O,Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not (s := P) (outerCollision E))
  have hO : O = templatePairs E 4 2 3 ∪ templatePairs E 6 3 5 ∪
      templatePairs E 7 5 5 ∪ templatePairs E 9 5 8 := by
    ext p
    simp only [O,P,Finset.mem_filter,Finset.mem_product,Finset.mem_union,
      templatePairs_mem,outerCollision]
    constructor
    · rintro ⟨⟨⟨hp,hq⟩,hle⟩,h⟩
      rcases h with ⟨hd,ha,hb⟩ | ⟨hd,ha,hb⟩ | ⟨hd,ha⟩ | ⟨hd,ha,hb⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hp,hd,ha,hb,hd ▸ hq⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hp,hd,ha,hb,hd ▸ hq⟩))
      · exact Or.inl (Or.inr ⟨hp,hd,ha,ha,hd ▸ hq⟩)
      · exact Or.inr ⟨hp,hd,ha,hb,hd ▸ hq⟩
    · rintro (((h | h) | h) | h)
      · rcases h with ⟨hp,hd,ha,hb,hq⟩
        exact ⟨⟨⟨hp,hd.symm ▸ hq⟩,by omega⟩,Or.inl ⟨hd,ha,hb⟩⟩
      · rcases h with ⟨hp,hd,ha,hb,hq⟩
        exact ⟨⟨⟨hp,hd.symm ▸ hq⟩,by omega⟩,Or.inr (Or.inl ⟨hd,ha,hb⟩)⟩
      · rcases h with ⟨hp,hd,ha,hb,hq⟩
        exact ⟨⟨⟨hp,hd.symm ▸ hq⟩,by omega⟩,Or.inr (Or.inr (Or.inl ⟨hd,ha⟩))⟩
      · rcases h with ⟨hp,hd,ha,hb,hq⟩
        exact ⟨⟨⟨hp,hd.symm ▸ hq⟩,by omega⟩,Or.inr (Or.inr (Or.inr ⟨hd,ha,hb⟩))⟩
  have hcardO : O.card =
      (E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E)).card +
      (E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E)).card := by
    rw [hO]
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint]
    · have hc (d a b : ℤ) : (templatePairs E d a b).card =
          (E.filter (fun t => t+a ∈ E ∧ t+b ∈ E ∧ t+d ∈ E)).card := by
        apply Finset.card_image_of_injective
        intro x y h
        exact congrArg (fun p : ℤ × ℤ => p.1) h
      rw [hc, hc, hc, hc]
      congr 2
      apply congrArg Finset.card
      ext t
      simp only [Finset.mem_filter, and_self_left]
    · exact templatePairs_disjoint E _ _ _ _ _ _ (by norm_num)
    · exact Finset.disjoint_union_left.2 ⟨
        templatePairs_disjoint E _ _ _ _ _ _ (by norm_num),
        templatePairs_disjoint E _ _ _ _ _ _ (by norm_num)⟩
    · exact Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨
        templatePairs_disjoint E _ _ _ _ _ _ (by norm_num),
        templatePairs_disjoint E _ _ _ _ _ _ (by norm_num)⟩,
        templatePairs_disjoint E _ _ _ _ _ _ (by norm_num)⟩
  have hcardP : P.card = (E.card+1).choose 2 := by
    have hP : P = ((E ×ˢ E).filter (fun p => p.1 < p.2)) ∪ E.diag := by
      ext p
      simp only [P,Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_diag]
      constructor
      · rintro ⟨⟨hp,hq⟩,hle⟩
        by_cases he : p.1 = p.2
        · exact Or.inr ⟨hp,he⟩
        · exact Or.inl ⟨⟨hp,hq⟩,by omega⟩
      · rintro (⟨⟨hp,hq⟩,hlt⟩ | ⟨hp,he⟩)
        · exact ⟨⟨hp,hq⟩,le_of_lt hlt⟩
        · exact ⟨⟨hp,he ▸ hp⟩,le_of_eq he⟩
    rw [hP,Finset.card_union_of_disjoint]
    · rw [Finset.card_product_filter_lt,Finset.diag_card]
      simpa [Nat.add_comm] using (Nat.choose_succ_succ' E.card 1).symm
    · apply Finset.disjoint_left.2
      intro p hp hq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_diag.1 hq).2
      omega
  omega

/-- The source family's exact sumset count, in additive form to certify no truncation.
Here the same E supplies every template count and every element of the real sumset. -/
theorem nested_family_sum_card (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (n : ℕ) (hn : 7 ≤ n) :
    let E : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n : ℤ)+2)
    ((E.image (fun e => r ^ e)) + (E.image (fun e => r ^ e))).card +
      (n-1 + (n-8) + (n-9) + (n-11) + (if 8 ≤ n then 1 else 0) +
        (if 10 ≤ n then 1 else 0)) = n*(n+1)/2 := by
  classical
  dsimp only
  let E : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n : ℤ)+2)
  have hcard : E.card = n := by
    dsimp [E]
    rw [Finset.card_union_of_disjoint]
    · norm_num only [Finset.card_insert_of_notMem (by norm_num : (0 : ℤ) ∉ ({3} : Finset ℤ)),
        Finset.card_singleton, Int.card_Icc]
      omega
    · apply Finset.disjoint_left.2
      intro t ht hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      simp only [Finset.mem_Icc] at hi
      omega
  have h4 : (E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E)).card = n-5 := by
    have hs : E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E) =
        insert 3 (Finset.Icc 5 ((n : ℤ)-2)) := by
      ext t
      simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.mem_Icc]
      omega
    rw [hs,Finset.card_insert_of_notMem (by simp),Int.card_Icc]
    omega
  have h6 : (E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E)).card = 2+(n-8) := by
    have hs : E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E) =
        insert 0 (insert 3 (Finset.Icc 5 ((n : ℤ)-4))) := by
      ext t
      simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.mem_Icc]
      omega
    rw [hs,Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp),Int.card_Icc]
    omega
  have h7 : (E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E)).card =
      1+(if 8 ≤ n then 1 else 0)+(n-9) := by
    by_cases hn8 : 8 ≤ n
    · have hs : E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E) =
          insert 0 (insert 3 (Finset.Icc 5 ((n : ℤ)-5))) := by
        ext t
        simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,Finset.mem_Icc]
        omega
      rw [hs,Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp),Int.card_Icc,if_pos hn8]
      omega
    · have hs : E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E) = {0} := by
        ext t
        simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,Finset.mem_Icc]
        omega
      rw [hs,Finset.card_singleton,if_neg hn8]
      omega
  have h9 : (E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E)).card =
      1+(if 10 ≤ n then 1 else 0)+(n-11) := by
    by_cases hn10 : 10 ≤ n
    · have hs : E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E) =
          insert 0 (insert 3 (Finset.Icc 5 ((n : ℤ)-7))) := by
        ext t
        simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,Finset.mem_Icc]
        omega
      rw [hs,Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp),Int.card_Icc,if_pos hn10]
      omega
    · have hs : E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E) = {0} := by
        ext t
        simp only [E,Finset.mem_filter,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,Finset.mem_Icc]
        omega
      rw [hs,Finset.card_singleton,if_neg hn10]
      omega
  have h := sumset_card_add_template_counts r hr hroot E
  rw [hcard,h4,h6,h7,h9,Nat.choose_two_right] at h
  have hn' : n+1-1 = n := by omega
  rw [hn',Nat.mul_comm (n+1) n] at h
  change (E.image (fun e => r ^ e) + E.image (fun e => r ^ e)).card +
    (n-1 + (n-8) + (n-9) + (n-11) + (if 8 ≤ n then 1 else 0) +
      (if 10 ≤ n then 1 else 0)) = n*(n+1)/2
  omega

end D5.S3.Arith.Additive.PlasticPowerCollisions
