/- GID: D5/S3/Combinatorics/RealRootedPermutations/LogConcave
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RealRootedPermutations/LogConcave
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.BigOperators, mathlib/module/Mathlib.Basic.Real.Basic, mathlib/module/Mathlib.Order.Interval.Set.Monotone, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Strict log concavity forces unimodal weak coefficient sortings. -/

import D5.S3.Combinatorics.RealRootedPermutations.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Strict log concavity and inverse-position inequalities for weak coefficient sortings. -/

open Polynomial
open scoped BigOperators
namespace D5.S3.Combinatorics.RealRootedPermutations.LogConcave

private lemma middle_nonneg {a b c d : ℝ} (hb : 0 < b)
    (hc : 0 < c) (hd : 0 ≤ d) (h₁ : a * c ≤ b ^ 2) (h₂ : b * d ≤ c ^ 2) :
    a * d ≤ b * c := by
  have h₃ := mul_le_mul_of_nonneg_right h₁ hd
  have h₄ := mul_le_mul_of_nonneg_left h₂ hb.le
  have h₅ : c * (a * d) ≤ c * (b * c) := by nlinarith
  exact (mul_le_mul_iff_right₀ hc).mp (by nlinarith [h₅])

private lemma coeff_step_zero (p : ℝ[X]) (s : ℝ) :
    ((1 + C s * X) * p).coeff 0 = p.coeff 0 := by
  simp

private lemma coeff_step_succ (p : ℝ[X]) (s : ℝ) (k : ℕ) :
    ((1 + C s * X) * p).coeff (k + 1) = p.coeff (k + 1) + s * p.coeff k := by
  rw [add_mul, one_mul, mul_assoc, mul_comm X p, ← mul_assoc,
    coeff_add, coeff_mul_X, coeff_C_mul]

private lemma product_shape {ι : Type*} [DecidableEq ι] (t : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ t, 0 < r i) :
    (∀ k, k ≤ t.card → 0 < (∏ i ∈ t, (1 + C (r i) * X)).coeff k) ∧
    (∀ k, t.card < k → (∏ i ∈ t, (1 + C (r i) * X)).coeff k = 0) ∧
    (∀ k, k + 2 ≤ t.card →
      (∏ i ∈ t, (1 + C (r i) * X)).coeff k *
        (∏ i ∈ t, (1 + C (r i) * X)).coeff (k + 2) <
      (∏ i ∈ t, (1 + C (r i) * X)).coeff (k + 1) ^ 2) := by
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have : k = 0 := by omega
        subst k
        norm_num
      · intro k hk
        simp [Polynomial.coeff_one, show k ≠ 0 by omega]
      · intro k hk
        omega
  | @insert a t ha ih =>
      have hs : 0 < r a := hr a (Finset.mem_insert_self a t)
      obtain ⟨hp, hz, hl⟩ := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
      let p : ℝ[X] := ∏ i ∈ t, (1 + C (r i) * X)
      rw [Finset.prod_insert ha]
      change (∀ k, k ≤ (insert a t).card → 0 < ((1 + C (r a) * X) * p).coeff k) ∧
        (∀ k, (insert a t).card < k → ((1 + C (r a) * X) * p).coeff k = 0) ∧
        (∀ k, k + 2 ≤ (insert a t).card →
          ((1 + C (r a) * X) * p).coeff k *
            ((1 + C (r a) * X) * p).coeff (k + 2) <
          ((1 + C (r a) * X) * p).coeff (k + 1) ^ 2)

      simp only [Finset.card_insert_of_notMem ha]
      have hn (k : ℕ) : 0 ≤ p.coeff k := by
        by_cases hk : k ≤ t.card
        · exact (hp k hk).le
        · exact le_of_eq (hz k (by omega)).symm
      have hw (k : ℕ) : p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) ^ 2 := by
        by_cases hk : k + 2 ≤ t.card
        · exact (hl k hk).le
        · rw [show p.coeff (k + 2) = 0 from hz _ (by omega), mul_zero]
          positivity
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => simpa only [coeff_step_zero] using hp 0 (Nat.zero_le _)
        | succ k =>
            rw [coeff_step_succ]
            exact add_pos_of_nonneg_of_pos (hn _) (mul_pos hs (hp k (by omega)))
      · intro k hk
        cases k with
        | zero => omega
        | succ k =>
            rw [coeff_step_succ, hz _ (by omega), hz _ (by omega)]
            ring
      · intro k hk
        cases k with
        | zero =>
            rw [coeff_step_zero, show 0 + 2 = 1 + 1 by rfl, coeff_step_succ,
              coeff_step_succ]
            have h₀ := hp 0 (Nat.zero_le _)
            have h₁ := hn 1
            have h₂ := hw 0
            have hpos : 0 < (r a * p.coeff 0) ^ 2 := sq_pos_of_pos (mul_pos hs h₀)
            have hcross : 0 ≤ r a * p.coeff 0 * p.coeff 1 := by positivity
            nlinarith
        | succ k =>
            have he₂ : k + 1 + 2 = (k + 2) + 1 := by omega
            rw [he₂, coeff_step_succ, coeff_step_succ, coeff_step_succ]
            have hb := hp (k + 1) (by omega)
            have hc := hp (k + 2) (by omega)
            have h₁ := hw k
            have h₂ := hw (k + 1)
            have hmid := middle_nonneg hb hc (hn (k + 3)) h₁ h₂
            have hstrict := hl k (by omega)
            have hpos : 0 < (r a) ^ 2 *
                (p.coeff (k + 1) ^ 2 - p.coeff k * p.coeff (k + 2)) :=
              mul_pos (sq_pos_of_pos hs) (sub_pos.mpr hstrict)
            have hmid' : 0 ≤ r a *
                (p.coeff (k + 1) * p.coeff (k + 2) - p.coeff k * p.coeff (k + 3)) :=
              mul_nonneg hs.le (sub_nonneg.mpr hmid)
            have hf : p.coeff (k + 1) * p.coeff (k + 3) ≤ p.coeff (k + 2) ^ 2 := h₂
            nlinarith

private lemma next_decreases {f : ℕ → ℝ} {N k : ℕ}
    (hp : ∀ i, i ≤ N → 0 < f i)
    (hl : ∀ i, i + 2 ≤ N → f i * f (i + 2) < f (i + 1) ^ 2)
    (hk : k + 2 ≤ N) (hd : f (k + 1) ≤ f k) : f (k + 2) < f (k + 1) := by
  have hm := hp (k + 1) (by omega)
  have he := mul_le_mul_of_nonneg_right hd (hp (k + 2) hk).le
  have hs := hl k hk
  have ht : f (k + 1) * f (k + 2) < f (k + 1) * f (k + 1) := by nlinarith
  exact (mul_lt_mul_iff_right₀ hm).mp (by nlinarith [ht])

private lemma descent_persists {f : ℕ → ℝ} {N a : ℕ}
    (hp : ∀ i, i ≤ N → 0 < f i)
    (hl : ∀ i, i + 2 ≤ N → f i * f (i + 2) < f (i + 1) ^ 2)
    (hd : f (a + 1) ≤ f a) :
    ∀ b, a ≤ b → b + 1 ≤ N →
      f (b + 1) ≤ f b ∧ (a < b → f (b + 1) < f b) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => ⟨hd, by omega⟩
  | succ b hab ih =>
      intro hb
      have hprev := (ih (by omega)).1
      have he := next_decreases hp hl (by omega : b + 2 ≤ N) hprev
      exact ⟨he.le, fun _ => he⟩

private lemma increasing_before_max {f : ℕ → ℝ} {N m : ℕ}
    (hp : ∀ i, i ≤ N → 0 < f i)
    (hl : ∀ i, i + 2 ≤ N → f i * f (i + 2) < f (i + 1) ^ 2)
    (hm : m ≤ N) (hmax : ∀ i, i ≤ N → f i ≤ f m) :
    ∀ a, a + 1 < m → f a < f (a + 1) := by
  intro a ha
  by_contra hn
  have hd : f (a + 1) ≤ f a := le_of_not_gt hn
  have hdec := descent_persists hp hl hd
  have hfirst : f (a + 2) < f (a + 1) := next_decreases hp hl (by omega) hd
  have hbound : ∀ b, a + 2 ≤ b → b ≤ N → f b < f (a + 1) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => exact fun _ => hfirst
    | succ b hb ih =>
        intro hbN
        exact lt_of_le_of_lt (hdec b (by omega) (by omega)).1 (ih (by omega))
  have h := hbound m (by omega) hm
  exact (not_lt_of_ge (hmax (a + 1) (by omega))) h

private lemma decreasing_after_max {f : ℕ → ℝ} {N m : ℕ}
    (hp : ∀ i, i ≤ N → 0 < f i)
    (hl : ∀ i, i + 2 ≤ N → f i * f (i + 2) < f (i + 1) ^ 2)
    (hm : m ≤ N) (hmax : ∀ i, i ≤ N → f i ≤ f m) :
    ∀ a, m < a → a + 1 ≤ N → f (a + 1) < f a := by
  intro a ha haN
  have hstart : f (m + 1) ≤ f m := hmax _ (by omega)
  exact (descent_persists hp hl hstart a ha.le haN).2 ha

private lemma sorting_unimodal {n : ℕ} (f : ℕ → ℝ)
    (hp : ∀ i, i ≤ n → 0 < f i)
    (hl : ∀ i, i + 2 ≤ n → f i * f (i + 2) < f (i + 1) ^ 2)
    (π : Equiv.Perm (Fin (n + 1)))
    (hmono : Monotone (fun t : Fin (n + 1) => f (π t))) : IsUnimodal π := by
  let m := π (Fin.last n)
  have hm : (m : ℕ) ≤ n := Nat.le_of_lt_succ m.isLt
  have hmax (i : ℕ) (hi : i ≤ n) : f i ≤ f m := by
    have he := hmono (Fin.le_last (π.symm ⟨i, by omega⟩))
    simpa only [Equiv.apply_symm_apply] using he
  have hup : StrictMonoOn f (Set.Iio (m : ℕ)) := by
    apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
    intro a _ _ ha
    exact increasing_before_max hp hl hm hmax a ha
  have hdown : StrictAntiOn f (Set.Ioc (m : ℕ) n) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Ioc
    intro a _ ha hnext
    exact decreasing_after_max hp hl hm hmax a ha.1 hnext.2
  have hlast (i : Fin (n + 1)) (hi : i ≠ m) : π.symm i < π.symm m := by
    have hne : π.symm i ≠ Fin.last n := by
      intro he
      apply hi
      simpa only [Equiv.apply_symm_apply] using congrArg π he
    simpa only [m, Equiv.symm_apply_apply] using
      lt_of_le_of_ne (Fin.le_last (π.symm i)) hne
  constructor
  · intro i j hij hj
    by_cases hjm : j = m
    · subst j
      exact hlast i (ne_of_lt hij)
    · have hjm' : (j : ℕ) < m := lt_of_le_of_ne hj (fun he => hjm (Fin.ext he))
      have hi' : (i : ℕ) < m := lt_trans hij hjm'
      have hf := hup hi' hjm' hij
      by_contra hh
      have he := hmono (le_of_not_gt hh)
      simp only [Equiv.apply_symm_apply] at he
      exact (not_lt_of_ge he) hf
  · intro i j hi hij
    by_cases him : i = m
    · subst i
      exact hlast j (ne_of_gt hij)
    · have hmi : (m : ℕ) < i := lt_of_le_of_ne hi (fun he => him (Fin.ext he.symm))
      have hmj : (m : ℕ) < j := lt_trans hmi hij
      have hf := hdown ⟨hmi, Nat.le_of_lt_succ i.isLt⟩
        ⟨hmj, Nat.le_of_lt_succ j.isLt⟩ hij
      by_contra hh
      have he := hmono (le_of_not_gt hh)
      simp only [Equiv.apply_symm_apply] at he
      exact (not_lt_of_ge he) hf

/-- Every weak sorting of the positive product coefficients is unimodal. -/
theorem unimodal_of_arises {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (h : Arises π) : IsUnimodal π := by
  obtain ⟨r, hr, hmono⟩ := h
  obtain ⟨hp, _, hl⟩ := product_shape Finset.univ r (fun i _ => hr i)
  apply sorting_unimodal (fun k => coeffs r (k + 1)) ?_ ?_ π hmono
  · intro i hi
    exact hp (i + 1) (by simpa using Nat.add_le_add_right hi 1)
  · intro i hi
    exact hl (i + 1) (by simpa using Nat.add_le_add_right hi 1)

end D5.S3.Combinatorics.RealRootedPermutations.LogConcave
