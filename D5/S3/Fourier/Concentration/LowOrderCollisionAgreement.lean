/- GID: D5/S3/Fourier/Concentration/LowOrderCollisionAgreement
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/LowOrderCollisionAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identical low-order collision masses can separate at growing degree. -/

import D5.S3.Fourier.Concentration.FiniteCollisionVariance
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-! Low-order collision measurements can agree while higher moments separate. -/

open Finset

set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.LowOrderCollisionAgreement

private abbrev Count := Fin 3 → ℕ

private def tripleFrequency (z : ℝ) (m : Count) : ℝ := (m 1 : ℝ) + z * m 2

private theorem degree_coordinates {m : Count} {p : ℕ}
    (hm : ∑ j, m j = p) : m 0 + m 1 + m 2 = p := by
  simpa only [Fin.sum_univ_three, add_assoc] using hm

private theorem close_pair_same_last {z t : ℝ} {m n : Count} {p : ℕ}
    (hm : ∑ j, m j = p) (hn : ∑ j, n j = p)
    (ht : t < 1) (hlast : m 2 = n 2)
    (h : |tripleFrequency z m - tripleFrequency z n| ≤ t) :
    m = n := by
  have h₁ := degree_coordinates hm
  have h₂ := degree_coordinates hn
  have hg : |((m 1 : ℤ) - n 1 : ℤ)| < 1 := by
    exact_mod_cast (show |(m 1 : ℝ) - n 1| < 1 by
      convert h.trans_lt ht using 2
      simp only [tripleFrequency, hlast]
      ring)
  have hmid : m 1 = n 1 := by have := Int.abs_lt_one_iff.mp hg; omega
  have hhead : m 0 = n 0 := by omega
  ext j
  fin_cases j <;> assumption

private theorem ordered_off_band {z t : ℝ} {m n : Count} {p : ℕ}
    (hm : ∑ j, m j = p) (horder : m 2 < n 2)
    (hz : 0 ≤ z) (hp : (p : ℝ) + t < z) :
    t < |tripleFrequency z m - tripleFrequency z n| := by
  have hmid : m 1 ≤ p := by have := degree_coordinates hm; omega
  have hmR : (m 1 : ℝ) ≤ p := by exact_mod_cast hmid
  have horder' : (m 2 : ℝ) + 1 ≤ n 2 := by exact_mod_cast horder
  have htail := mul_le_mul_of_nonneg_left horder' hz
  have hnr := Nat.cast_nonneg (α := ℝ) (n 1)
  by_contra! h
  have hleft := (abs_le.mp h).1
  dsimp [tripleFrequency] at hleft
  linarith

private theorem close_iff_eq {z t : ℝ} {m n : Count} {p : ℕ}
    (hm : ∑ j, m j = p) (hn : ∑ j, n j = p) (ht : 0 ≤ t) (htone : t < 1)
    (hp : (p : ℝ) + t < z) :
    |tripleFrequency z m - tripleFrequency z n| ≤ t ↔ m = n := by
  constructor
  · intro h
    have hz : 0 ≤ z := by linarith [Nat.cast_nonneg (α := ℝ) p]
    rcases lt_trichotomy (m 2) (n 2) with hlt | heq | hgt
    · exact False.elim ((ordered_off_band hm hlt hz hp).not_ge h)
    · exact close_pair_same_last hm hn htone heq h
    · rw [abs_sub_comm] at h
      exact False.elim ((ordered_off_band hn hgt hz hp).not_ge h)
  · rintro rfl
    simpa using ht

private def pureMiddle (k : ℕ) : Count := ![0, k, 0]
private def oneLast (k : ℕ) : Count := ![k - 1, 0, 1]

private theorem ordered_critical_pair {k : ℕ} (hk : 2 ≤ k) {m n : Count}
    (hm : ∑ j, m j = k) (hn : ∑ j, n j = k) (horder : m 2 < n 2)
    (h : tripleFrequency (k : ℝ) m = tripleFrequency (k : ℝ) n) :
    m = pureMiddle k ∧ n = oneLast k := by
  have hmSum := degree_coordinates hm
  have hnSum := degree_coordinates hn
  have hg : m 1 + k * m 2 = n 1 + k * n 2 := by
    unfold tripleFrequency at h
    exact_mod_cast h
  have hprod := Nat.mul_le_mul_left k (show m 2 + 1 ≤ n 2 by omega)
  rw [Nat.mul_add, mul_one] at hprod
  have hmMid : m 1 = k := by omega
  have hzero : m 0 = 0 ∧ m 2 = 0 ∧ n 1 = 0 := by omega
  obtain ⟨hmZero, hmLast, hnMid⟩ := hzero
  have hnLast : n 2 = 1 := by
    by_contra hne
    have hsucc : 2 ≤ n 2 := by omega
    have ht := Nat.mul_le_mul_left k hsucc
    rw [Nat.mul_two] at ht
    rw [hmMid, hmLast, hnMid, mul_zero, add_zero, zero_add] at hg
    omega
  have hnZero : n 0 = k - 1 := by omega
  constructor <;> ext i <;> fin_cases i
  · exact hmZero
  · exact hmMid
  · exact hmLast
  · exact hnZero
  · exact hnMid
  · exact hnLast

private theorem integral_gap_at_resolution {k : ℕ} {m n : Count} {t : ℝ}
    (ht : 0 ≤ t) (htone : t < 1) :
    |tripleFrequency (k : ℝ) m - tripleFrequency (k : ℝ) n| ≤ t ↔
      tripleFrequency (k : ℝ) m = tripleFrequency (k : ℝ) n := by
  constructor
  · intro h
    have heqZ : (m 1 : ℤ) + (k : ℤ) * m 2 - ((n 1 : ℤ) + (k : ℤ) * n 2) = 0 := by
      apply Int.abs_lt_one_iff.mp
      have hlt := h.trans_lt htone
      unfold tripleFrequency at hlt
      exact_mod_cast hlt
    apply sub_eq_zero.mp
    change (m 1 : ℝ) + (k : ℝ) * m 2 - ((n 1 : ℝ) + (k : ℝ) * n 2) = 0
    exact_mod_cast heqZ
  · intro h
    simp [h, ht]

private theorem critical_incidence {k : ℕ} (hk : 2 ≤ k) {m n : Count}
    (hm : ∑ j, m j = k) (hn : ∑ j, n j = k) {t : ℝ} (ht : 0 ≤ t) (htone : t < 1) :
    |tripleFrequency (k : ℝ) m - tripleFrequency (k : ℝ) n| ≤ t ↔
      m = n ∨ (m = pureMiddle k ∧ n = oneLast k) ∨ (m = oneLast k ∧ n = pureMiddle k) := by
  constructor
  · intro h
    have heq := (integral_gap_at_resolution ht htone).mp h
    rcases lt_trichotomy (m 2) (n 2) with hlt | he | hgt
    · exact Or.inr (Or.inl (ordered_critical_pair hk hm hn hlt heq))
    · exact Or.inl (close_pair_same_last hm hn htone he h)
    · have hh := ordered_critical_pair hk hn hm hgt heq.symm
      exact Or.inr (Or.inr ⟨hh.2, hh.1⟩)
  · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · simpa using ht
    · simpa [tripleFrequency, pureMiddle, oneLast] using ht
    · simpa [tripleFrequency, pureMiddle, oneLast] using ht

open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (tailCollisionMass nearCollisionMass)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight monomialFrequency)

private def triple (z : ℝ) : Fin 3 → ℝ := ![0, 1, z]

private theorem tripleFrequency_eq (z : ℝ) (m : Count) :
    monomialFrequency (triple z) m = tripleFrequency z m := by
  simp [monomialFrequency, tripleFrequency, triple, Fin.sum_univ_three, mul_comm]

private theorem low_order_equality {k p : ℕ} (hp : p < k) (w : Fin 3 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htone : t < 1) :
    tailCollisionMass (triple k) w p t = tailCollisionMass (triple ((k : ℝ) + √2)) w p t := by
  unfold tailCollisionMass nearCollisionMass
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  simp only [tripleFrequency_eq]
  have hpR : (p : ℝ) + t < k := by
    have hsucc : ((p + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hp
    push_cast at hsucc
    linarith
  simp only [close_iff_eq (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1 ht htone hpR,
    close_iff_eq (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1 ht htone
      (hpR.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _)))]

private theorem critical_order_difference {k : ℕ} (hk : 2 ≤ k) (w : Fin 3 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htone : t < 1) :
    tailCollisionMass (triple k) w k t =
      tailCollisionMass (triple ((k : ℝ) + √2)) w k t +
        2 * (monomialWeight w (pureMiddle k) * monomialWeight w (oneLast k)) := by
  classical
  unfold tailCollisionMass nearCollisionMass
  let S := piAntidiag (univ : Finset (Fin 3)) k
  let A := pureMiddle k
  let B := oneLast k
  let v := monomialWeight w
  have ha : A ∈ S := by simp [S, A, pureMiddle, Fin.sum_univ_three]
  have hb : B ∈ S := by
    simp [S, B, oneLast, Fin.sum_univ_three, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hab : A ≠ B := fun eq => by
    have := congrFun eq (2 : Fin 3)
    simp [A, B, pureMiddle, oneLast] at this
  have hsqrt : (1 : ℝ) < √2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hpR : (k : ℝ) + t < (k : ℝ) + √2 := by linarith
  change (∑ m ∈ S, ∑ n ∈ S,
      if |monomialFrequency (triple k) m - monomialFrequency (triple k) n| ≤ t
        then v m * v n else 0) = _
  have hstep (m) (hm : m ∈ S) (n) (hn : n ∈ S) :
      (if |monomialFrequency (triple k) m - monomialFrequency (triple k) n| ≤ t
        then v m * v n else 0) =
      (if |monomialFrequency (triple ((k : ℝ) + √2)) m -
          monomialFrequency (triple ((k : ℝ) + √2)) n| ≤ t then v m * v n else 0) +
        ((if m = A then if n = B then v m * v n else 0 else 0) +
          (if m = B then if n = A then v m * v n else 0 else 0)) := by
    simp only [tripleFrequency_eq]
    simp only [critical_incidence hk (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1 ht htone,
      close_iff_eq (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1 ht htone hpR]
    by_cases hmn : m = n
    · subst n
      by_cases hma : m = A <;> by_cases hmb : m = B <;> simp_all [A, B]
    · by_cases hma : m = A <;> by_cases hmb : m = B <;>
        by_cases hna : n = A <;> by_cases hnb : n = B <;>
        simp_all [A, B]
  calc
    _ = ∑ m ∈ S, ∑ n ∈ S,
        ((if |monomialFrequency (triple ((k : ℝ) + √2)) m -
            monomialFrequency (triple ((k : ℝ) + √2)) n| ≤ t then v m * v n else 0) +
          ((if m = A then if n = B then v m * v n else 0 else 0) +
            (if m = B then if n = A then v m * v n else 0 else 0))) :=
      sum_congr rfl fun m hm => sum_congr rfl fun n hn => hstep m hm n hn
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq', ha, hb, ite_true]
      ring

private theorem pureMiddle_weight (k : ℕ) (w : Fin 3 → ℝ) :
    monomialWeight w (pureMiddle k) = w 1 ^ k := by
  simp [monomialWeight, Nat.multinomial, Fin.sum_univ_three, Fin.prod_univ_three, pureMiddle,
    Nat.factorial_pos]

private theorem oneLast_weight {k : ℕ} (hk : 1 ≤ k) (w : Fin 3 → ℝ) :
    monomialWeight w (oneLast k) = (k : ℝ) * w 0 ^ (k - 1) * w 2 := by
  have hchoose : Nat.multinomial (univ : Finset (Fin 3)) (oneLast k) = k := by
    suffices k.factorial / (k - 1).factorial = k from by
      simpa [Nat.multinomial, Fin.sum_univ_three, Fin.prod_univ_three, oneLast, Nat.sub_add_cancel hk]
    have hfact : k.factorial = k * (k-1).factorial := by
      have h := Nat.factorial_succ (k - 1)
      rw [Nat.sub_add_cancel hk] at h
      exact h
    rw [hfact, Nat.mul_div_cancel _ (Nat.factorial_pos _)]
  rw [monomialWeight, hchoose, Fin.prod_univ_three]
  simp [oneLast]
  ring

private theorem exact_critical_difference {k : ℕ} (hk : 2 ≤ k) (w : Fin 3 → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htone : t < 1) :
    tailCollisionMass (triple k) w k t =
      tailCollisionMass (triple ((k : ℝ) + √2)) w k t +
        2 * (k : ℝ) * w 0 ^ (k - 1) * w 1 ^ k * w 2 := by
  rw [critical_order_difference hk w ht htone, pureMiddle_weight,
    oneLast_weight (by omega : 1 ≤ k)]
  ring

private theorem quadratic_sum_ne_zero (r s : ℤ) (hne : r ≠ 0 ∨ s ≠ 0) :
    (r : ℝ) + (s : ℝ) * √2 ≠ 0 := by
  intro h
  by_cases hs : s = 0
  · have hr0 : r = 0 := by simpa [hs] using h
    exact hne.elim (fun hr => hr hr0) (fun hs' => hs' hs)
  · apply (irrational_iff_ne_rational _).mp irrational_sqrt_two (-r) s hs
    apply (eq_div_iff (by exact_mod_cast hs)).mpr
    push_cast
    linarith

private theorem quadratic_separation (r s : ℤ) (hne : r ≠ 0 ∨ s ≠ 0) :
    1 ≤ |(r : ℝ) + (s : ℝ) * √2| * (|(r : ℝ)| + |(s : ℝ)| * √2) := by
  have hsqrt : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have heq : ((r : ℝ) + (s : ℝ) * √2) * ((r : ℝ) - (s : ℝ) * √2) =
      ((r ^ 2 - 2 * s ^ 2 : ℤ) : ℝ) := by
    push_cast
    calc
      _ = (r : ℝ)^2 - (s : ℝ)^2 * (√2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hpos : r ^ 2 - 2 * s ^ 2 ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at heq
    have hf₁ := quadratic_sum_ne_zero r s hne
    have hf₂ : (r : ℝ) - (s : ℝ) * √2 ≠ 0 := by
      simpa [sub_eq_add_neg, neg_mul] using
        quadratic_sum_ne_zero r (-s) (by simpa using hne)
    exact (mul_ne_zero hf₁ hf₂) heq
  have hnorm : (1 : ℝ) ≤ |((r ^ 2 - 2 * s ^ 2 : ℤ) : ℝ)| := by
    have h : (1 : ℤ) ≤ |r ^ 2 - 2 * s ^ 2| := by
      have := abs_pos.mpr hpos
      omega
    exact_mod_cast h
  rw [← heq, abs_mul] at hnorm
  refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  simpa [abs_mul, abs_of_nonneg hsqrt] using abs_sub (r : ℝ) ((s : ℝ) * √2)

private noncomputable def comparisonWeights : Fin 3 → ℝ := ![1/4, 1/4, 1/2]

private theorem integral_mass_same {k p : ℕ} (w : Fin 3 → ℝ) {t u : ℝ}
    (ht : 0 ≤ t) (htone : t < 1) (hu : 0 ≤ u) (huone : u < 1) :
    tailCollisionMass (triple k) w p t = tailCollisionMass (triple k) w p u := by
  unfold tailCollisionMass nearCollisionMass
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  simp only [tripleFrequency_eq, integral_gap_at_resolution ht htone,
    integral_gap_at_resolution hu huone]

private theorem growing_order_lower {k p : ℕ} (hk : 2 ≤ k) (hp : 0 < p) {t : ℝ}
    (ht : 0 ≤ t) (htone : t < 1) :
    1 / (16 * (k : ℝ) * √(p : ℝ)) ≤ tailCollisionMass (triple k) comparisonWeights p t := by
  have hw : ∀ j, 0 ≤ comparisonWeights j := by intro j; fin_cases j <;> norm_num [comparisonWeights]
  have hW : ∑ j, comparisonWeights j = 1 := by norm_num [comparisonWeights, Fin.sum_univ_three]
  have h := D5.S3.Fourier.Concentration.FiniteCollisionVariance.tailCollisionMass_lower_variance
    (triple k) comparisonWeights hw (by simp [hW]) hp (η := 1/2) (by norm_num)
  dsimp only at h
  simp only [hW, one_pow, mul_one, div_one] at h
  let μ : ℝ := ∑ j, comparisonWeights j * triple (k : ℝ) j
  let V : ℝ := ∑ j, comparisonWeights j * (triple (k : ℝ) j - μ)^2
  change (9 / 16 : ℝ) ≤
    (1 + 4 * √((p : ℝ) * V) / (1/2)) * tailCollisionMass (triple k) comparisonWeights p (1/2) at h
  have hVR : V = ((4 * (k : ℝ)^2 - 4 * k + 3) / 16) := by
    dsimp [V, μ]
    norm_num [comparisonWeights, triple, Fin.sum_univ_three]
    ring
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hVR' : V ≤ (k : ℝ)^2 := by
    rw [hVR]
    nlinarith [sq_nonneg (k : ℝ)]
  have hS : √((p : ℝ) * V) ≤ (k : ℝ) * √(p : ℝ) := by
    calc
      _ ≤ √((p : ℝ) * (k : ℝ)^2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hVR' (Nat.cast_nonneg _))
      _ = _ := by rw [mul_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  have hN : (1 : ℝ) ≤ (k : ℝ) * √(p : ℝ) := by
    have hpS : (1 : ℝ) ≤ √(p : ℝ) := by
      simpa using Real.sqrt_le_sqrt hpR
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (k : ℝ) * √(p : ℝ) := mul_le_mul (by linarith) hpS zero_le_one (by positivity)
  have hMass := integral_mass_same (k := k) (p := p) comparisonWeights ht htone
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) < 1 by norm_num)
  rw [← hMass] at h
  have hTail : 0 ≤ tailCollisionMass (triple k) comparisonWeights p t := by
    unfold tailCollisionMass nearCollisionMass
    refine sum_nonneg fun m _ => sum_nonneg fun n _ => ?_
    split_ifs
    · exact mul_nonneg
        (D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.monomialWeight_nonneg _ hw m)
        (D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.monomialWeight_nonneg _ hw n)
    · exact le_rfl
  have hcap : 1 + 4 * √((p : ℝ) * V) / (1/2) ≤ 9 * ((k : ℝ) * √(p : ℝ)) := by linarith
  have hstrong := h.trans (mul_le_mul_of_nonneg_right hcap hTail)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hstrong]

private noncomputable def centralMass (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

private theorem central_mass_sq (n : ℕ) : (n + 1 : ℝ) * centralMass n ^ 2 ≤ 1 := by
  induction n with
  | zero => norm_num [centralMass, Nat.centralBinom]
  | succ n ih =>
    have hrec : ((n : ℝ) + 1) * (Nat.centralBinom (n+1) : ℝ) =
        2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hratio : centralMass (n+1) =
        ((2*(n : ℝ)+1) / (2*(n+1))) * centralMass n := by
      unfold centralMass
      rw [pow_succ]
      field_simp
      nlinarith only [hrec]
    have hpos : 0 < 2 * ((n : ℝ) + 1) := by positivity
    have hcoe : ((2*(n : ℝ)+1)/(2*(n+1)))^2 * (n + 2 : ℝ) ≤ n+1 := by
      rw [div_pow, mul_comm]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (sq_pos_of_pos hpos)).mpr
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith only [hn]
    rw [Nat.cast_succ, hratio, mul_pow]
    calc
      _ = (((2*(n : ℝ)+1)/(2*(n+1)))^2 * (n + 2 : ℝ)) * centralMass n ^ 2 := by ring
      _ ≤ (n+1 : ℝ) * centralMass n^2 := mul_le_mul_of_nonneg_right hcoe (sq_nonneg _)
      _ ≤ 1 := ih

private noncomputable def comparisonResolution (k p : ℕ) : ℝ :=
  1 / (2 * ((k : ℝ) + 3) * (p : ℝ))

private theorem irrational_at_resolution {k p : ℕ} (hp : 0 < p) {m n : Count}
    (hm : ∑ j, m j = p) (hn : ∑ j, n j = p) :
    |tripleFrequency ((k : ℝ) + √2) m - tripleFrequency ((k : ℝ) + √2) n| ≤
      comparisonResolution k p ↔ m = n := by
  constructor
  · intro h
    by_contra hne
    let s : ℤ := (m 2 : ℤ) - n 2
    let r : ℤ := (m 1 : ℤ) - n 1 + (k : ℤ) * s
    have hsumM := degree_coordinates hm
    have hsumN := degree_coordinates hn
    have hpair : r ≠ 0 ∨ s ≠ 0 := by
      by_contra! hh
      have hmid : m 1 = n 1 := by
        have he := hh.1
        dsimp [r] at he
        rw [hh.2, mul_zero, add_zero] at he
        omega
      have hlast : m 2 = n 2 := by
        have := hh.2
        dsimp [s] at this
        omega
      apply hne
      ext j
      fin_cases j
      · change m 0 = n 0
        omega
      · exact hmid
      · exact hlast
    have hfreq : tripleFrequency ((k : ℝ) + √2) m - tripleFrequency ((k : ℝ) + √2) n =
        (r : ℝ) + (s : ℝ) * √2 := by
      dsimp [tripleFrequency, r,s]
      push_cast
      ring
    rw [hfreq] at h
    have hsz : |(s : ℝ)| ≤ p := by
      dsimp [s]
      push_cast
      have hml : (m 2 : ℝ) ≤ p := by exact_mod_cast (show m 2 ≤ p by omega)
      have hnl : (n 2 : ℝ) ≤ p := by exact_mod_cast (show n 2 ≤ p by omega)
      apply abs_le.mpr
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (m 2), Nat.cast_nonneg (α := ℝ) (n 2)]
    have hmid : |(m 1 : ℝ) - n 1| ≤ p := by
      have hml : (m 1 : ℝ) ≤ p := by exact_mod_cast (show m 1 ≤ p by omega)
      have hnl : (n 1 : ℝ) ≤ p := by exact_mod_cast (show n 1 ≤ p by omega)
      apply abs_le.mpr
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (m 1), Nat.cast_nonneg (α := ℝ) (n 1)]
    have hrz : |(r : ℝ)| ≤ (1 + (k : ℝ)) * p := by
      dsimp only [r]
      push_cast
      calc
        _ ≤ |(m 1 : ℝ) - n 1| + |(k : ℝ) * (s : ℝ)| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_mul, one_mul]
          exact add_le_add hmid (mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg _))
    have hnon : 0 ≤ |(r : ℝ)| + |(s : ℝ)| * √2 := by positivity
    have hcap : |(r : ℝ)| + |(s : ℝ)| * √2 ≤ ((k : ℝ) + 3) * p := by
      have h₂ : √(2 : ℝ) ≤ 2 := by
        have hS := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
        norm_num at hS ⊢
      have htail := mul_le_mul hsz h₂ (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
      linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) p)]
    have hh := quadratic_separation r s hpair
    have hprod := hh.trans ((mul_le_mul_of_nonneg_right h hnon).trans
      (mul_le_mul_of_nonneg_left hcap (by unfold comparisonResolution; positivity)))
    have hHalf : comparisonResolution k p * (((k : ℝ)+3)*p) = 1/2 := by
      unfold comparisonResolution
      field_simp
    rw [hHalf] at hprod
    norm_num at hprod
  · rintro rfl
    simp only [sub_self, abs_zero]
    unfold comparisonResolution
    positivity

private noncomputable def fairMass (n a : ℕ) : ℝ := (n.choose a : ℝ) / 2^n

private theorem fair_nonneg (n a : ℕ) : 0 ≤ fairMass n a := by
  unfold fairMass
  positivity

private theorem fair_peak (n a : ℕ) : fairMass n a ≤ centralMass (n/2) := by
  have heven (m a : ℕ) : fairMass (2*m) a ≤ centralMass m := by
    unfold fairMass centralMass
    rw [pow_mul]
    norm_num
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_centralBinom a m)
      (by positivity)
  let m := n/2
  change fairMass n a ≤ centralMass m
  have hh : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
  rcases hh with h | h
  · rw [h]
    exact heven m a
  · rw [h]
    cases a with
    | zero =>
      have hz : fairMass (2*m+1) 0 ≤ fairMass (2*m) 0 := by
        unfold fairMass
        simp only [Nat.choose_zero_right, Nat.cast_one, pow_succ]
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        linarith [show (0 : ℝ) ≤ 2 ^ (2*m) by positivity]
      exact hz.trans (heven m 0)
    | succ a =>
      have hf : fairMass (2*m+1) (a+1) = (fairMass (2*m) a + fairMass (2*m) (a+1))/2 := by
        unfold fairMass
        rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ, add_div]
        ring
      rw [hf]
      linarith [heven m a, heven m (a+1)]

private theorem fair_sum (n : ℕ) : ∑ a ∈ range (n+1), fairMass n a = 1 := by
  unfold fairMass
  rw [← sum_div]
  have h : (∑ a ∈ range (n+1), (n.choose a : ℝ)) = 2^n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [h, div_self (by positivity : (2 : ℝ) ^ n ≠ 0)]

private theorem fair_le_one (n a : ℕ) (ha : a ≤ n) : fairMass n a ≤ 1 := by
  rw [← fair_sum n]
  exact single_le_sum (fun b _ => fair_nonneg n b) (mem_range_succ_iff.mpr ha)

private theorem fair_tail_pointwise {n a : ℕ} (ha : a ≤ n) (hn : 0 < n)
    (hhigh : 3 * (n : ℝ) / 4 < a) :
    fairMass n a ≤ 4/(n : ℝ) := by
  let I := Icc (n - n/2) a
  have hI : I ⊆ range (n+1) := by
    intro b hb
    exact mem_range_succ_iff.mpr ((mem_Icc.mp hb).2.trans ha)
  have hmono : ∀ b ∈ I, fairMass n a ≤ fairMass n b := by
    intro b hb
    have hab := (mem_Icc.mp hb).2
    have hbmax := hab.trans ha
    have hleft : n-a ≤ n-b := by omega
    have hright : n-b ≤ n/2 := by have := (mem_Icc.mp hb).1; omega
    have hchain (u v : ℕ) (huv : u ≤ v) (hv : v ≤ n/2) : n.choose u ≤ n.choose v := by
      induction v, huv using Nat.le_induction with
      | base => exact le_rfl
      | succ v huv ih =>
        exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    have hchoose := hchain (n-a) (n-b) hleft hright
    rw [Nat.choose_symm ha, Nat.choose_symm hbmax] at hchoose
    exact div_le_div_of_nonneg_right (by exact_mod_cast hchoose)
      (by positivity)
  have hsum : (I.card : ℝ) * fairMass n a ≤ 1 := by
    calc
      _ = ∑ b ∈ I, fairMass n a := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ I, fairMass n b := sum_le_sum hmono
      _ ≤ ∑ b ∈ range (n+1), fairMass n b := sum_le_sum_of_subset_of_nonneg hI
        (fun b _ _ => fair_nonneg n b)
      _ = _ := fair_sum n
  have hcard : (n : ℝ)/4 ≤ I.card := by
    have hnmid : (n : ℝ) ≤ 2 * ((n/2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n ≤ 2*(n/2)+1 by omega)
    have hl : n - n/2 ≤ a + 1 := by
      have hnR : (n : ℝ) < 2*(a : ℝ) := by
        linarith [Nat.cast_nonneg (α:=ℝ) n]
      have hnZ : n < 2*a := by exact_mod_cast hnR
      omega
    dsimp [I]
    rw [Nat.card_Icc, Nat.cast_sub hl, Nat.cast_sub (by omega : n/2 ≤ n)]
    push_cast
    linarith
  have hh := (mul_le_mul_of_nonneg_right hcard (fair_nonneg n a)).trans hsum
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  nlinarith only [hh]

private theorem fair_peak_sq (n a : ℕ) : ((n : ℝ)+1) * fairMass n a^2 ≤ 2 := by
  have hsq : fairMass n a^2 ≤ centralMass (n/2)^2 :=
    pow_le_pow_left₀ (fair_nonneg _ _) (fair_peak n a) 2
  have hhalf : ((n : ℝ)+1) ≤ 2*(((n/2 : ℕ) : ℝ)+1) := by
    exact_mod_cast (show n+1 ≤ 2*(n/2+1) by omega)
  calc
    _ ≤ ((n : ℝ)+1) * centralMass (n/2)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ (2*(((n/2 : ℕ) : ℝ)+1)) * centralMass (n/2)^2 :=
      mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
    _ ≤ 2 := by linarith only [central_mass_sq (n/2)]

private theorem fair_product_le {p a b : ℕ} (hp : 0 < p) (ha : a ≤ p) (hb : b ≤ p-a) :
    fairMass p a * fairMass (p-a) b ≤ 4/(p : ℝ) := by
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  by_cases h : 3 * (p : ℝ) / 4 < a
  · calc
      _ ≤ fairMass p a * 1 := mul_le_mul_of_nonneg_left (fair_le_one _ _ hb) (fair_nonneg _ _)
      _ ≤ _ := by simpa only [mul_one] using fair_tail_pointwise ha hp h
  · have hn : (p : ℝ)/4 ≤ ((p - a : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub ha]
      linarith [not_lt.mp h]
    have hpden : 0 ≤ (p : ℝ)/4 := by positivity
    have hx : (p : ℝ) * fairMass p a^2 ≤ 2 := by
      linarith only [fair_peak_sq p a, sq_nonneg (fairMass p a)]
    have hy : ((p : ℝ)/4) * fairMass (p-a) b^2 ≤ 2 :=
      (mul_le_mul_of_nonneg_right hn (sq_nonneg _)).trans (fair_peak_sq _ _)
    have hh := mul_le_mul hx hy
      (mul_nonneg hpden (sq_nonneg _)) (show (0 : ℝ) ≤ 2 by norm_num)
    have hs : ((p : ℝ)*(fairMass p a * fairMass (p-a) b))^2 ≤ 16 := by nlinarith only [hh]
    apply (le_div_iff₀ hpR).mpr
    have hc : (p : ℝ)*(fairMass p a * fairMass (p-a) b) ≤ 4 := by
      nlinarith [sq_nonneg ((p : ℝ)*(fairMass p a * fairMass (p-a) b) - 4)]
    simpa [mul_comm] using hc

private theorem comparison_weight_factor {m : Count} {p : ℕ} (hm : ∑ j, m j = p) :
    monomialWeight comparisonWeights m = fairMass p (m 2) * fairMass (p - m 2) (m 1) := by
  have hm' := degree_coordinates hm
  have hsum : m 1 + m 0 = p - m 2 := by omega
  have halast : m 2 ≤ p := by omega
  have hcoeff : Nat.multinomial (univ : Finset (Fin 3)) m =
      p.choose (m 2) * (p - m 2).choose (m 1) := by
    have hsplit : (univ : Finset (Fin 3)) = insert 2 (insert 1 {0}) := by decide
    rw [hsplit, Nat.multinomial_insert (by decide), Nat.multinomial_insert (by decide),
      Nat.multinomial_singleton, sum_insert (by decide), sum_singleton, mul_one, hsum]
    rw [show m 2 + (p - m 2) = p by omega]
  have hpow :
      (1 / 4 : ℝ) ^ m 0 * (1 / 4 : ℝ) ^ m 1 * (1 / 2 : ℝ) ^ m 2 =
        (1 / 2 : ℝ) ^ p * (1 / 2 : ℝ) ^ (p - m 2) := by
    rw [← pow_add, show m 0 + m 1 = p - m 2 by omega]
    rw [show (1 / 4 : ℝ) = (1 / 2)^2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold monomialWeight fairMass
  rw [hcoeff, Nat.cast_mul, Fin.prod_univ_three]
  change (p.choose (m 2) : ℝ) * ((p - m 2).choose (m 1) : ℝ) *
      ((1 / 4 : ℝ) ^ m 0 * (1 / 4 : ℝ) ^ m 1 * (1 / 2 : ℝ) ^ m 2) = _
  rw [hpow]
  simp only [div_pow, one_pow]
  ring

private theorem growing_order_upper {k p : ℕ} (hp : 0 < p) :
    tailCollisionMass (triple ((k : ℝ) + √2)) comparisonWeights p (comparisonResolution k p) ≤
      4 / (p : ℝ) := by
  classical
  let S := piAntidiag (univ : Finset (Fin 3)) p
  let w := monomialWeight comparisonWeights
  let t := comparisonResolution k p
  unfold tailCollisionMass nearCollisionMass
  change (∑ m ∈ S, ∑ n ∈ S,
      if |monomialFrequency (triple ((k : ℝ) + √2)) m -
          monomialFrequency (triple ((k : ℝ) + √2)) n| ≤ t then w m * w n else 0) ≤ _
  have h :
      (∑ m ∈ S, ∑ n ∈ S,
        if |monomialFrequency (triple ((k : ℝ) + √2)) m -
            monomialFrequency (triple ((k : ℝ) + √2)) n| ≤ t
          then w m * w n else 0) = ∑ m ∈ S, w m * w m := by
        refine sum_congr rfl fun m hm => ?_
        calc
          _ = ∑ n ∈ S, if m = n then w m * w n else 0 := by
            refine sum_congr rfl fun n hn => ?_
            simp only [t, tripleFrequency_eq, irrational_at_resolution hp
              (mem_piAntidiag.mp hm).1 (mem_piAntidiag.mp hn).1]
          _ = _ := by simp [sum_ite_eq, hm]
  rw [h]
  have hw : ∀ j, 0 ≤ comparisonWeights j := by
    intro j
    fin_cases j <;> norm_num [comparisonWeights]
  have hsum : ∑ m ∈ S, w m = 1 := by
    have hW : ∑ j, comparisonWeights j = 1 := by norm_num [comparisonWeights, Fin.sum_univ_three]
    have hwSum : ∑ m ∈ S, w m = (∑ j, comparisonWeights j) ^ p :=
      (sum_pow_eq_sum_piAntidiag univ comparisonWeights p).symm
    simp [hwSum, hW]
  calc
    _ ≤ ∑ m ∈ S, (4/(p : ℝ)) * w m := by
      refine sum_le_sum fun m hm => ?_
      have hd := (mem_piAntidiag.mp hm).1
      have hd' := degree_coordinates hd
      have hwbound : w m ≤ 4/(p : ℝ) := by
        rw [show w m = monomialWeight comparisonWeights m by rfl, comparison_weight_factor hd]
        exact fair_product_le hp (by omega) (by omega)
      exact mul_le_mul_of_nonneg_right hwbound
        (D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.monomialWeight_nonneg _ hw m)
    _ = 4/(p : ℝ) := by rw [← mul_sum, hsum, mul_one]

/-- Agreement of all collision masses below degree k permits an exact difference
at degree k and a growing disparity at a common positive resolution. -/
theorem low_order_agreement_and_high_order_disparity (k : ℕ) (hk : 2 ≤ k) :
    let g := triple (k : ℝ)
    let g' := triple ((k : ℝ) + √2)
    let w := comparisonWeights
    (∀ p < k, ∀ t : ℝ, 0 ≤ t → t < 1 →
      tailCollisionMass g w p t = tailCollisionMass g' w p t) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 → tailCollisionMass g w k t =
      tailCollisionMass g' w k t + 2 * (k : ℝ) * (1/4 : ℝ)^(k-1) * (1/4 : ℝ)^k * (1/2)) ∧
    (∀ p : ℕ, 0 < p →
      let t := comparisonResolution k p
      1 / (16 * (k : ℝ) * √(p : ℝ)) ≤ tailCollisionMass g w p t ∧
        tailCollisionMass g' w p t ≤ 4 / (p : ℝ)) := by
  refine ⟨fun p hp t ht htone => low_order_equality hp comparisonWeights ht htone, ?_, ?_⟩
  · intro t ht htone
    simpa [comparisonWeights] using exact_critical_difference hk comparisonWeights ht htone
  · intro p hp
    let t := comparisonResolution k p
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have ht : 0 ≤ t := by dsimp [t, comparisonResolution]; positivity
    have htone : t < 1 := by
      dsimp [t, comparisonResolution]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg hkR (show 0 ≤ (p : ℝ) by positivity)]
    exact ⟨growing_order_lower hk hp ht htone, growing_order_upper hp⟩

#print axioms low_order_agreement_and_high_order_disparity

end D5.S3.Fourier.Concentration.LowOrderCollisionAgreement
