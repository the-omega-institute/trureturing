/- GID: D5/S3/Combinatorics/GuardedRentOrBuyAdditive
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GuardedRentOrBuyAdditive
   mirror-E: none(waiver:analytic-additive-bound)
   anchors: []
   utility: none
   digest: Fair-cost comparison for the guarded repeated rent-or-buy rule. -/

import D5.S3.Combinatorics.GuardedRentOrBuy
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
The fair cost and the two potentials follow Schiavo, arXiv:2611.06955v1,
Proposition 6 and Lemmas 7, 8, 14, and 17.
-/

set_option autoImplicit false

namespace GuardedRentOrBuy

noncomputable section

open Classical

private def g (a : ℝ) (n : ℕ) : ℝ := a * n * (n + 1) / 2

private theorem g_zero (a : ℝ) : g a 0 = 0 := by simp [g]

private theorem g_succ (a : ℝ) (n : ℕ) : g a (n + 1) = g a n + (n + 1 : ℕ) * a := by
  push_cast
  unfold g
  push_cast
  ring

private theorem g_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ g a n := by
  unfold g
  positivity

private theorem g_rate_mono {a b : ℝ} (h : a ≤ b) (n : ℕ) : g a n ≤ g b n := by
  unfold g
  gcongr

private theorem g_index_mono {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (h : m ≤ n) :
    g a m ≤ g a n := by
  unfold g
  gcongr

private theorem g_add (a : ℝ) (m n : ℕ) :
    g a (m + n) = g a m + g a n + (n : ℝ) * ((m : ℝ) * a) := by
  unfold g
  push_cast
  ring

private def rent (a e : ℝ) (n : ℕ) : ℝ := g a n + n * e

private theorem rent_succ (a e : ℝ) (n : ℕ) :
    rent a e (n + 1) = rent a (e + a) n + e + a := by
  unfold rent
  rw [g_succ]
  push_cast
  ring

private theorem crossing_exists (K a e A : ℝ) (ha : 0 < a) (he : 0 ≤ e) :
    ∃ n : ℕ, 0 < n ∧ K ≤ A + rent a e n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((K - A) / a)
  refine ⟨n + 1, by omega, ?_⟩
  have hna : ((n : ℝ) + 1) * a ≥ K - A := by
    have h := (div_le_iff₀ ha).mp hn
    linarith
  have htri : ((n : ℝ) + 1) * a ≤ g a (n + 1) := by
    rw [g_succ, Nat.cast_add, Nat.cast_one]
    have := g_nonneg ha.le n
    linarith
  have hprod : 0 ≤ ((n + 1 : ℕ) : ℝ) * e := by positivity
  unfold rent
  linarith

private def cut (K a e A : ℝ) (ha : 0 < a) (he : 0 ≤ e) : ℕ :=
  Nat.find (crossing_exists K a e A ha he)

private theorem cut_spec (K a e A : ℝ) (ha : 0 < a) (he : 0 ≤ e) :
    0 < cut K a e A ha he ∧ K ≤ A + rent a e (cut K a e A ha he) :=
  Nat.find_spec (crossing_exists K a e A ha he)

private theorem cut_le {K a e A : ℝ} {ha : 0 < a} {he : 0 ≤ e} {n : ℕ}
    (hn : 0 < n) (h : K ≤ A + rent a e n) : cut K a e A ha he ≤ n :=
  Nat.find_min' (crossing_exists K a e A ha he) ⟨hn, h⟩

private theorem before_cut {K a e A : ℝ} {ha : 0 < a} {he : 0 ≤ e} {n : ℕ}
    (hn : 0 < n) (h : n < cut K a e A ha he) : A + rent a e n < K :=
  lt_of_not_ge fun hc => (Nat.not_le_of_lt h) (cut_le hn hc)

private def cycleLength (K a : ℝ) (ha : 0 < a) : ℕ := cut K a 0 0 ha le_rfl

private def fair (K a : ℝ) (ha : 0 < a) : ℝ :=
  (K + g a (cycleLength K a ha)) / (cycleLength K a ha : ℝ)

private theorem length_pos {K a : ℝ} (ha : 0 < a) : 0 < cycleLength K a ha :=
  (cut_spec K a 0 0 ha le_rfl).1

private theorem length_crosses {K a : ℝ} (ha : 0 < a) : K ≤ g a (cycleLength K a ha) := by
  simpa [cycleLength, rent] using (cut_spec K a 0 0 ha le_rfl).2

private theorem length_le {K a : ℝ} {ha : 0 < a} {n : ℕ} (hn : 0 < n)
    (h : K ≤ g a n) : cycleLength K a ha ≤ n :=
  cut_le hn (by simpa [rent] using h)

private theorem length_before {K a : ℝ} (hK : 0 < K) {ha : 0 < a}
    {n : ℕ} (hn : n < cycleLength K a ha) : g a n < K := by
  by_cases hz : n = 0
  · simpa [hz, g_zero] using hK
  · simpa [rent] using
      (before_cut (K := K) (a := a) (e := 0) (A := 0)
        (ha := ha) (he := le_rfl) (Nat.pos_of_ne_zero hz) hn)

private theorem fair_mul {K a : ℝ} (ha : 0 < a) :
    (cycleLength K a ha : ℝ) * fair K a ha = K + g a (cycleLength K a ha) := by
  have h : (0 : ℝ) < (cycleLength K a ha : ℝ) := by exact_mod_cast length_pos (K := K) ha
  unfold fair
  field_simp

private theorem fair_bounds {K a : ℝ} (hK : 0 < K) (ha : 0 < a) :
    (cycleLength K a ha : ℝ) * a ≤ fair K a ha ∧
      fair K a ha ≤ ((cycleLength K a ha : ℝ) + 1) * a := by
  let L := cycleLength K a ha
  let f := fair K a ha
  have hL : 0 < L := length_pos ha
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hbefore : g a (L - 1) < K := length_before hK (by omega)
  have hcross : K ≤ g a L := length_crosses ha
  have hcast : ((L - 1 : ℕ) : ℝ) = L - 1 := by simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ L by omega))
  have hf : (L : ℝ) * f = K + g a L := fair_mul ha
  unfold g at hbefore hcross hf
  rw [hcast] at hbefore
  constructor
  · apply le_of_mul_le_mul_left (a := (L : ℝ)) _ hLr
    nlinarith
  · apply le_of_mul_le_mul_left (a := (L : ℝ)) _ hLr
    nlinarith

private theorem rate_le_fair {K a : ℝ} (hK : 0 < K) (ha : 0 < a) :
    a ≤ fair K a ha := by
  have hL : 1 ≤ (cycleLength K a ha : ℝ) := by
    exact_mod_cast length_pos (K := K) ha
  have h := mul_le_mul_of_nonneg_right hL ha.le
  simpa using h.trans (fair_bounds hK ha).1

private def value (K a : ℝ) (ha : 0 < a) (e : ℝ) (n : ℕ) : ℝ :=
  K + rent a e n - n * fair K a ha

private theorem value_zero (K a : ℝ) (ha : 0 < a) (e : ℝ) :
    value K a ha e 0 = K := by simp [value, rent, g_zero]

private theorem value_length {K a : ℝ} (ha : 0 < a) (e : ℝ) :
    value K a ha e (cycleLength K a ha) = (cycleLength K a ha : ℝ) * e := by
  unfold value rent
  rw [fair_mul ha]
  ring

private theorem value_succ (K a : ℝ) (ha : 0 < a) (e : ℝ) (n : ℕ) :
    value K a ha e (n + 1) = value K a ha (e + a) n + e + a - fair K a ha := by
  unfold value
  rw [rent_succ]
  push_cast
  ring

private theorem value_ge {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (e : ℝ) (n : ℕ) :
    (n : ℝ) * e ≤ value K a ha e n := by
  have heq : value K a ha e n = value K a ha 0 n + (n : ℝ) * e := by
    simp [value, rent]
    ring
  rw [heq]
  suffices hv : 0 ≤ value K a ha 0 n by linarith
  let L := cycleLength K a ha
  have hbase : value K a ha 0 L = 0 := by simp [L, value_length ha]
  have hbounds := fair_bounds hK ha
  have hid : value K a ha 0 n =
      ((n : ℝ) - L) * (a * ((n : ℝ) + L + 1) / 2 - fair K a ha) := by
    have hL := fair_mul (K := K) ha
    change (L : ℝ) * fair K a ha = K + g a L at hL
    unfold value rent
    unfold g at hL ⊢
    simp only [mul_zero, add_zero]
    linarith only [show K + a * n * (n + 1) / 2 - n * fair K a ha -
        ((n : ℝ) - L) * (a * ((n : ℝ) + L + 1) / 2 - fair K a ha) =
        K + a * L * (L + 1) / 2 - L * fair K a ha by ring, hL]
  rw [hid]
  rcases lt_trichotomy n L with hn | rfl | hn
  · have h₁ : (n : ℝ) - L ≤ 0 := by exact sub_nonpos.mpr (by exact_mod_cast hn.le)
    have h₂ : (n : ℝ) + 1 ≤ L := by exact_mod_cast Nat.succ_le_of_lt hn
    apply mul_nonneg_of_nonpos_of_nonpos h₁
    have hf : (L : ℝ) * a ≤ fair K a ha := hbounds.1
    nlinarith [mul_nonneg (sub_nonneg.mpr h₂) ha.le]
  · simp
  · have h₁ : 0 ≤ (n : ℝ) - L := by exact sub_nonneg.mpr (by exact_mod_cast hn.le)
    have h₂ : (L : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
    apply mul_nonneg h₁
    have hf : fair K a ha ≤ ((L : ℝ) + 1) * a := hbounds.2
    nlinarith [mul_nonneg (sub_nonneg.mpr h₂) ha.le]

private def policyPotential (K a : ℝ) (ha : 0 < a) (e A : ℝ) (he : 0 ≤ e) : ℝ :=
  value K a ha e (cut K a e A ha he)

private theorem policyPotential_ge {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {e A : ℝ} (he : 0 ≤ e) : e ≤ policyPotential K a ha e A he := by
  have hn : 1 ≤ (cut K a e A ha he : ℝ) := by
    exact_mod_cast (cut_spec K a e A ha he).1
  have h := mul_le_mul_of_nonneg_right hn he
  simpa [policyPotential] using h.trans (value_ge hK ha e _)

private theorem policyPotential_zero (K a : ℝ) (ha : 0 < a) :
    policyPotential K a ha 0 0 le_rfl = 0 := by
  change value K a ha 0 (cycleLength K a ha) = 0
  simp [value_length]

private theorem value_min_exists {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (e : ℝ) (he : 0 ≤ e) :
    ∃ j : ℕ, ∀ n : ℕ, value K a ha e j ≤ value K a ha e n := by
  let L := cycleLength K a ha
  let s := Finset.range (L + 1)
  have hs : s.Nonempty := ⟨0, by simp [s]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s (value K a ha e) hs
  refine ⟨j, fun n => ?_⟩
  by_cases h : n ≤ L
  · exact hmin n (by simpa [s] using Nat.lt_succ_of_le h)
  · have hL : L ∈ s := by simp [s]
    have hn : (L : ℝ) ≤ n := by exact_mod_cast (show L ≤ n by omega)
    exact (hmin L hL).trans ((value_length ha e).le.trans
      ((mul_le_mul_of_nonneg_right hn he).trans (value_ge hK ha e n)))

private def comparatorPotential (K a : ℝ) (hK : 0 < K) (ha : 0 < a)
    (e : ℝ) (he : 0 ≤ e) : ℝ :=
  value K a ha e (value_min_exists hK ha e he).choose

private theorem comparatorPotential_le {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {e : ℝ} (he : 0 ≤ e) (n : ℕ) : comparatorPotential K a hK ha e he ≤ value K a ha e n :=
  (value_min_exists hK ha e he).choose_spec n

private theorem comparatorPotential_nonneg {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {e : ℝ} (he : 0 ≤ e) : 0 ≤ comparatorPotential K a hK ha e he :=
  le_trans (by positivity) (value_ge hK ha e _)

private theorem comparatorPotential_cap {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {e : ℝ} (he : 0 ≤ e) : comparatorPotential K a hK ha e he ≤ K := by
  simpa [value_zero] using comparatorPotential_le hK ha he 0

private theorem comparatorPotential_zero {K a : ℝ} (hK : 0 < K) (ha : 0 < a) :
    comparatorPotential K a hK ha 0 le_rfl = 0 := by
  apply le_antisymm _ (comparatorPotential_nonneg hK ha le_rfl)
  simpa [value_length] using comparatorPotential_le hK ha (e := 0) le_rfl
    (cycleLength K a ha)

private def valid (K : ℝ) (s : State) : Prop := 0 ≤ s.carry ∧ s.carry ≤ s.acc ∧ s.acc < K

private theorem valid_initial {K : ℝ} (hK : 0 < K) : valid K initial := by
  simpa [valid, initial] using hK

private theorem valid_advance {K a : ℝ} {s : State} (hK : 0 < K) (ha : 0 ≤ a)
    (hs : valid K s) : valid K (advance K s a) := by
  rcases hs with ⟨he, hEA, _⟩
  cases hr : reset K s a
  · have hn : ¬ crossing K s a := by
      intro hc
      simp [reset, hc] at hr
    exact ⟨by simpa [advance, hr] using add_nonneg he ha,
      by simp [advance, hr]; linarith, by simpa [advance, hr] using lt_of_not_ge hn⟩
  · simpa [valid, advance, hr] using hK

private theorem nonneg_next (o a : ℝ) (r : Bool) (ho : 0 ≤ o) (ha : 0 ≤ a) :
    0 ≤ nextCarry o a r := by
  cases r <;> simp [nextCarry, add_nonneg ho ha]

private theorem comparatorCost_nonneg {K o : ℝ} (hK : 0 ≤ K) (ho : 0 ≤ o)
    (steps : List (ℝ × Bool)) (ha : ∀ p ∈ steps, 0 ≤ p.1) :
    0 ≤ comparatorCost K o steps := by
  induction steps generalizing o with
  | nil => simp [comparatorCost]
  | cons p rest ih =>
    obtain ⟨a, r⟩ := p
    have h := ha (a, r) (by simp)
    have ht := ih (nonneg_next o a r ho h) (fun p hp => ha p (by simp [hp]))
    cases r <;> simp [comparatorCost, bill] <;> linarith

private theorem cut_shift {K a e A : ℝ} (ha : 0 < a) (he : 0 ≤ e)
    (hn : A + (e + a) < K) :
    cut K a e A ha he = cut K a (e + a) (A + (e + a)) ha (add_nonneg he ha.le) + 1 := by
  let k := cut K a e A ha he
  let j := cut K a (e + a) (A + (e + a)) ha (add_nonneg he ha.le)
  have hk := cut_spec K a e A ha he
  have hj := cut_spec K a (e + a) (A + (e + a)) ha (add_nonneg he ha.le)
  change 0 < k ∧ K ≤ A + rent a e k at hk
  change 0 < j ∧ K ≤ A + (e + a) + rent a (e + a) j at hj
  have h₁ : k ≤ j + 1 := by
    apply cut_le (by omega)
    rw [rent_succ]
    linarith [hj.2]
  have hk' : 1 < k := by
    by_contra! h
    have hk1 : k = 1 := by omega
    have hfirst := hk.2
    rw [hk1] at hfirst
    norm_num [rent, g] at hfirst
    linarith
  obtain ⟨d, hkEq⟩ : ∃ d : ℕ, k = d + 1 := ⟨k - 1, by omega⟩
  have h₂ : j ≤ d := by
    apply cut_le (by omega)
    have hcross := hk.2
    rw [hkEq, rent_succ] at hcross
    linarith
  omega

private theorem potential_congr {K a : ℝ} (ha : 0 < a) {e A e' A' : ℝ}
    (he : 0 ≤ e) (he' : 0 ≤ e') (hcarry : e = e') (hacc : A = A') :
    policyPotential K a ha e A he = policyPotential K a ha e' A' he' := by
  subst e'
  subst A'
  rfl

private theorem ordinary_step {K a : ℝ} (ha : 0 < a) (hK : 0 < K)
    (s : State) (hs : valid K s)
    (hordinary : reset K s a = decide (crossing K s a)) :
    bill K s.carry a (reset K s a) =
      fair K a ha + policyPotential K a ha s.carry s.acc hs.1 -
        policyPotential K a ha (advance K s a).carry (advance K s a).acc
          (valid_advance hK ha.le hs).1 := by
  by_cases hc : crossing K s a
  · have hr : reset K s a = true := by simp [hordinary, hc]
    have hcut : cut K a s.carry s.acc ha hs.1 = 1 := by
      have h₁ := (cut_spec K a s.carry s.acc ha hs.1).1
      have h₂ : cut K a s.carry s.acc ha hs.1 ≤ 1 := by
        apply cut_le (by omega)
        change K ≤ s.acc + (s.carry + a) at hc
        norm_num [rent, g]
        linarith
      omega
    have hzero :
        policyPotential K a ha (advance K s a).carry (advance K s a).acc
          (valid_advance hK ha.le hs).1 = 0 := by
      rw [potential_congr (e' := 0) (A' := 0) ha _ le_rfl
        (by simp [advance, hr]) (by simp [advance, hr]), policyPotential_zero]
    rw [hzero]
    simp only [policyPotential, hcut, bill, hr, ite_true, sub_zero]
    norm_num [value, rent, g]
    ring
  · have hr : reset K s a = false := by simp [hordinary, hc]
    have hshift := cut_shift ha hs.1 (lt_of_not_ge hc)
    have hnext :
        policyPotential K a ha (advance K s a).carry (advance K s a).acc
          (valid_advance hK ha.le hs).1 =
        policyPotential K a ha (s.carry + a) (s.acc + (s.carry + a)) (add_nonneg hs.1 ha.le) := by
      exact potential_congr ha _ _ (by simp [advance, hr]) (by simp [advance, hr])
    rw [hnext]
    simp only [policyPotential, hshift, value_succ, bill, hr, Bool.false_eq_true, ite_false, add_zero]
    ring

private theorem comparator_step {K a o : ℝ} (hK : 0 < K) (ha : 0 < a) (ho : 0 ≤ o)
    (r : Bool) :
    fair K a ha + comparatorPotential K a hK ha o ho -
        comparatorPotential K a hK ha (nextCarry o a r) (nonneg_next o a r ho ha.le) ≤
      bill K o a r := by
  cases r
  · let j := (value_min_exists hK ha (o + a) (add_nonneg ho ha.le)).choose
    have hj := comparatorPotential_le hK ha ho (j + 1)
    rw [value_succ] at hj
    change fair K a ha + comparatorPotential K a hK ha o ho - value K a ha (o + a) j ≤
      o + a + 0
    linarith
  · have hj := comparatorPotential_le hK ha ho 1
    rw [show 1 = 0 + 1 by rfl, value_succ, value_zero] at hj
    change fair K a ha + comparatorPotential K a hK ha o ho -
        comparatorPotential K a hK ha 0 le_rfl ≤ o + a + K
    rw [comparatorPotential_zero]
    linarith

private theorem comparatorPotential_rate {K a b o : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (ho : 0 ≤ o) :
    comparatorPotential K b hK hb o ho ≤ comparatorPotential K a hK ha o ho := by
  let L := cycleLength K b hb
  let j := (value_min_exists hK ha o ho).choose
  change comparatorPotential K b hK hb o ho ≤ value K a ha o j
  by_cases hj : j ≤ L
  · have hfair := value_ge hK ha (0 : ℝ) L
    have hfb : (L : ℝ) * fair K b hb = K + g b L := fair_mul hb
    have hL : 0 < (L : ℝ) := by exact_mod_cast length_pos (K := K) hb
    have hdiff : (b - a) * ((L : ℝ) + 1) / 2 ≤ fair K b hb - fair K a ha := by
      apply le_of_mul_le_mul_left (a := (L : ℝ)) _ hL
      simp [value, rent] at hfair
      unfold g at hfb hfair
      linarith only [hfb, hfair, show
        (L : ℝ) * ((b - a) * ((L : ℝ) + 1) / 2) =
          b * L * (L + 1) / 2 - a * L * (L + 1) / 2 by ring]
    have hjr : (j : ℝ) ≤ L := by exact_mod_cast hj
    have hdiff' : (b - a) * ((j : ℝ) + 1) / 2 ≤ fair K b hb - fair K a ha := by
      have hprod := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hjr)
      linarith only [hprod, hdiff, show (b - a) * ((L : ℝ) - j) =
          (b - a) * ((L : ℝ) + 1) - (b - a) * ((j : ℝ) + 1) by ring]
    refine (comparatorPotential_le hK hb ho j).trans ?_
    have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sub_nonneg.mpr hdiff')
    unfold value rent g
    linarith only [hprod, show
      (j : ℝ) * (fair K b hb - fair K a ha - (b - a) * ((j : ℝ) + 1) / 2) =
        (j : ℝ) * fair K b hb - j * fair K a ha -
          (b * j * (j + 1) / 2 - a * j * (j + 1) / 2) by ring]
  · have hj' : (L : ℝ) ≤ j := by exact_mod_cast (show L ≤ j by omega)
    exact (comparatorPotential_le hK hb ho L).trans ((value_length hb o).le.trans
      ((mul_le_mul_of_nonneg_right hj' ho).trans (value_ge hK ha o j)))

private theorem ordinary_if {K a : ℝ} {s : State}
    (h : ¬ drop s a ∨ s.ordinarySeen = false ∨ s.dropSeen = true) :
    reset K s a = decide (crossing K s a) := by
  rcases h with h | h | h <;> simp [reset, h]

private theorem ordinary_initial (K a : ℝ) :
    reset K initial a = decide (crossing K initial a) :=
  ordinary_if (Or.inl (by simp [drop, initial]))

private theorem ordinary_same (K a : ℝ) (s : State) :
    reset K (advance K s a) a = decide (crossing K (advance K s a) a) :=
  ordinary_if (Or.inl (by simp [drop, advance]))

private def block (a : ℝ) (rs : List Bool) : List (ℝ × Bool) := rs.map (fun r => (a, r))

private theorem block_rates (a : ℝ) (rs : List Bool) :
    (block a rs).map Prod.fst = List.replicate rs.length a := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (a :: (block a rs).map Prod.fst) = List.replicate (rs.length + 1) a
    rw [ih, List.replicate_succ]

private theorem block_nonneg {a : ℝ} (ha : 0 ≤ a) (rs : List Bool) :
    ∀ p ∈ block a rs, 0 ≤ p.1 := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  exact ha

private def finish (K : ℝ) (s : State) (xs : List ℝ) : State := xs.foldl (advance K) s

private def comparatorFinish (o : ℝ) (xs : List (ℝ × Bool)) : ℝ :=
  xs.foldl (fun carry p => nextCarry carry p.1 p.2) o

private theorem valid_block {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (n : ℕ) (s : State)
    (hs : valid K s) : valid K (finish K s (List.replicate n a)) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (advance K s a) (valid_advance hK ha hs)

private theorem comparatorFinish_nonneg_block {a o : ℝ} (ha : 0 ≤ a) (ho : 0 ≤ o)
    (rs : List Bool) : 0 ≤ comparatorFinish o (block a rs) := by
  induction rs generalizing o with
  | nil => exact ho
  | cons r tail ih => exact ih (nonneg_next o a r ho ha)

private theorem policy_segment {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (n : ℕ)
    (s : State) (hs : valid K s) (hord : reset K s a = decide (crossing K s a)) :
    policyCost K s (List.replicate n a) =
      (n : ℝ) * fair K a ha + policyPotential K a ha s.carry s.acc hs.1 -
        policyPotential K a ha (finish K s (List.replicate n a)).carry
          (finish K s (List.replicate n a)).acc (valid_block hK ha.le n s hs).1 := by
  induction n generalizing s with
  | zero => simp [finish, policyCost]
  | succ n ih =>
    have h := ordinary_step ha hK s hs hord
    have ht := ih (advance K s a) (valid_advance hK ha.le hs) (ordinary_same K a s)
    simp only [List.replicate_succ, policyCost, Nat.cast_succ]
    change bill K s.carry a (reset K s a) + policyCost K (advance K s a) (List.replicate n a) =
      ((n : ℝ) + 1) * fair K a ha + policyPotential K a ha s.carry s.acc hs.1 -
        policyPotential K a ha (finish K (advance K s a) (List.replicate n a)).carry
          (finish K (advance K s a) (List.replicate n a)).acc
          (valid_block hK ha.le n (advance K s a) (valid_advance hK ha.le hs)).1
    linarith only [h, ht]

private theorem comparator_segment {K a o : ℝ} (hK : 0 < K) (ha : 0 < a) (ho : 0 ≤ o)
    (rs : List Bool) :
    (rs.length : ℝ) * fair K a ha + comparatorPotential K a hK ha o ho -
      comparatorPotential K a hK ha (comparatorFinish o (block a rs))
        (comparatorFinish_nonneg_block ha.le ho rs) ≤ comparatorCost K o (block a rs) := by
  induction rs generalizing o with
  | nil => simp [block, comparatorFinish, comparatorCost]
  | cons r tail ih =>
    have h := comparator_step hK ha ho r
    have ht := ih (nonneg_next o a r ho ha.le)
    simp only [List.length_cons, Nat.cast_succ]
    change ((tail.length : ℝ) + 1) * fair K a ha + comparatorPotential K a hK ha o ho -
      comparatorPotential K a hK ha (comparatorFinish (nextCarry o a r) (block a tail))
        (comparatorFinish_nonneg_block ha.le (nonneg_next o a r ho ha.le) tail) ≤
          bill K o a r + comparatorCost K (nextCarry o a r) (block a tail)
    linarith only [h, ht]

private theorem zero_block {K : ℝ} (hK : 0 < K) (n : ℕ)
    (s : State) (hcarry : s.carry = 0) (hacc : s.acc = 0)
    (hord : reset K s 0 = decide (crossing K s 0)) :
    policyCost K s (List.replicate n 0) = 0 ∧
      (finish K s (List.replicate n 0)).carry = 0 ∧
      (finish K s (List.replicate n 0)).acc = 0 := by
  induction n generalizing s with
  | zero => exact ⟨rfl, hcarry, hacc⟩
  | succ n ih =>
    have hno : reset K s 0 = false := by simp [hord, crossing, hcarry, hacc, not_le.mpr hK]
    have hcarry' : (advance K s 0).carry = 0 := by simp [advance, hno, hcarry]
    have hacc' : (advance K s 0).acc = 0 := by simp [advance, hno, hcarry, hacc]
    have h := ih (advance K s 0) hcarry' hacc' (ordinary_same K 0 s)
    refine ⟨?_, h.2⟩
    simp [List.replicate_succ, policyCost, bill, hno, hcarry, h.1]

private theorem zero_comparator_finish (rs : List Bool) :
    comparatorFinish 0 (block 0 rs) = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simpa [comparatorFinish, block, nextCarry] using ih

private theorem single_block_bound {K a o : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (ho : 0 ≤ o)
    (s : State) (hcarry : s.carry = 0) (hacc : s.acc = 0)
    (hord : reset K s a = decide (crossing K s a)) (rs : List Bool) :
    policyCost K s (List.replicate rs.length a) ≤ comparatorCost K o (block a rs) + K := by
  rcases ha.eq_or_lt with rfl | ha
  · have h := (zero_block hK rs.length s hcarry hacc hord).1
    have hc := comparatorCost_nonneg hK.le ho (block 0 rs) (block_nonneg le_rfl rs)
    linarith
  have hs : valid K s := by simp [valid, hcarry, hacc, hK]
  have hp := policy_segment hK ha rs.length s hs hord
  have hz := potential_congr (K := K) ha hs.1 le_rfl hcarry hacc
  rw [policyPotential_zero] at hz
  have hpend := policyPotential_ge hK ha
    (valid_block hK ha.le rs.length s hs).1
    (A := (finish K s (List.replicate rs.length a)).acc)
  have hc := comparator_segment hK ha ho rs
  have hc₀ := comparatorPotential_nonneg hK ha ho
  have hc₁ := comparatorPotential_cap hK ha (comparatorFinish_nonneg_block ha.le ho rs)
  have hnv := (valid_block hK ha.le rs.length s hs).1
  linarith only [hp, hz, hpend, hnv, hc, hc₀, hc₁]

private theorem cut_old_rate {K a : ℝ} (ha : 0 < a) (m : ℕ)
    (hm : g a m < K) (he : 0 ≤ (m : ℝ) * a) :
    policyPotential K a ha ((m : ℝ) * a) (g a m) he =
      (m : ℝ) * fair K a ha - g a m := by
  let L := cycleLength K a ha
  have hmL : m < L := by
    by_contra! h
    exact (not_lt_of_ge ((length_crosses (K := K) ha).trans (g_index_mono ha.le h))) hm
  let k := cut K a ((m : ℝ) * a) (g a m) ha he
  have hk := cut_spec K a ((m : ℝ) * a) (g a m) ha he
  change 0 < k ∧ K ≤ g a m + rent a ((m : ℝ) * a) k at hk
  have hadd (n : ℕ) : g a m + rent a ((m : ℝ) * a) n = g a (m + n) := by
    rw [g_add]
    unfold rent
    ring
  have h₁ : k ≤ L - m := by
    apply cut_le (by omega)
    rw [hadd, show m + (L - m) = L by omega]
    exact length_crosses ha
  have h₂ : L ≤ m + k := by
    apply length_le (by omega)
    simpa only [hadd] using hk.2
  have hL : (L : ℝ) = (m : ℝ) + k := by exact_mod_cast (show L = m + k by omega)
  have hf : (L : ℝ) * fair K a ha = K + g a L := fair_mul ha
  rw [hL] at hf
  change K + rent a ((m : ℝ) * a) k - (k : ℝ) * fair K a ha = _
  have hsum := hadd k
  rw [show m + k = L by omega] at hsum
  linarith only [hf, hsum, show ((m : ℝ) + k) * fair K a ha =
       (m : ℝ) * fair K a ha + (k : ℝ) * fair K a ha by ring]

/-- The scaled polynomial inequality from Schiavo's positive-increase comparison. -/
private theorem increase_arithmetic {a b K L B N k : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hk : 0 < k) (hkB : k ≤ B) (hBN : B ≤ N) (hNL : N ≤ L)
    (hgapB : B < L → B + 1 ≤ L) (hgapk : k < B → k + 1 ≤ B)
    (hgapN : N < L → N + 1 ≤ L)
    (hK : a * L * (L - 1) / 2 ≤ K)
    (hcross : K ≤ a * N * (N + 1) / 2 + (b - a) * k * (k + 1) / 2) :
    let σ := k * (N - B) - (B - k) * (L - N)
    0 ≤ (K - a * L * B / 2) * σ +
      a * L * B * (L - N) * (N - B) / 2 + L * B * k * (b - a) * (B - k) / 2 := by
  dsimp only
  let σ := k * (N - B) - (B - k) * (L - N)
  let X := a * L * B * (L - N) * (N - B) / 2
  let Y := L * B * k * (b - a) * (B - k) / 2
  change 0 ≤ (K - a * L * B / 2) * σ + X + Y
  have hB : 0 ≤ B := by linarith
  have hL : 0 ≤ L := by linarith
  have hN : 0 ≤ N := by linarith
  have hd₁ : 0 ≤ L - N := sub_nonneg.mpr hNL
  have hd₂ : 0 ≤ N - B := sub_nonneg.mpr hBN
  have hd₃ : 0 ≤ B - k := sub_nonneg.mpr hkB
  have hd₄ : 0 ≤ b - a := sub_nonneg.mpr hab
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  rcases (show B ≤ L by linarith).eq_or_lt with hBL | hBL
  · have hN' : N = L := by linarith
    have hσ : σ = 0 := by simp [σ, hBL, hN']
    rw [hσ, mul_zero, zero_add]
    exact add_nonneg hX hY
  have hKL : 0 ≤ K - a * L * B / 2 := by
    have hpos := mul_nonneg (mul_nonneg ha hL) (show 0 ≤ L - 1 - B by linarith [hgapB hBL])
    nlinarith only [hK, hpos]
  by_cases hσ : 0 ≤ σ
  · exact add_nonneg (add_nonneg (mul_nonneg hKL hσ) hX) hY
  have hprod : 0 < (B - k) * (L - N) := by
    have ht := mul_nonneg hk.le hd₂
    dsimp [σ] at hσ
    linarith
  have hk' : k < B := by
    by_contra! h
    have heq : B - k = 0 := by linarith
    simp [heq] at hprod
  have hN' : N < L := by
    by_contra! h
    have heq : L - N = 0 := by linarith
    simp [heq] at hprod
  let x₀ := a * L * (L - 1) / 2
  let M := L * B * (B - k)
  let A (x : ℝ) := (k + 1) * (x - a * L * B / 2) * σ +
    (k + 1) * X + M * (x - a * N * (N + 1) / 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hY' : M * (K - a * N * (N + 1) / 2) ≤ (k + 1) * Y := by
    have h := mul_le_mul_of_nonneg_left
      (show K - a * N * (N + 1) / 2 ≤ (b - a) * k * (k + 1) / 2 by linarith) hM
    dsimp only [M, Y] at h ⊢
    nlinarith only [h]
  have htop : A K ≤ (k + 1) * ((K - a * L * B / 2) * σ + X + Y) := by
    dsimp only [A]
    nlinarith only [hY']
  have hgap := hgapk hk'
  have hgap' := hgapN hN'
  have hfactor : 0 ≤ L * B - (k + 1) * (L - N) := by
    have h := mul_nonneg hL (show 0 ≤ B - (k + 1) by linarith)
    have h' := mul_nonneg (show 0 ≤ k + 1 by linarith) hN
    nlinarith only [h, h']
  have hslope : 0 ≤ (k + 1) * σ + M := by
    have hid : (k + 1) * σ + M =
        (k + 1) * k * (N - B) + (B - k) * (L * B - (k + 1) * (L - N)) := by
      dsimp only [σ, M]
      ring
    rw [hid]
    positivity
  have hmono : A x₀ ≤ A K := by
    have h := mul_nonneg (sub_nonneg.mpr hK) hslope
    change 0 ≤ (K - x₀) * ((k + 1) * σ + M) at h
    dsimp only [A]
    nlinarith only [h]
  have hbase : 0 ≤ A x₀ := by
    have hid : A x₀ = a * L / 2 *
        ((k + 1) * k * (N - B) * (2 * L - 1 - B - N) +
         (B - k) * (L - N - 1) * (B * (L + N) - (k + 1) * (L - N))) := by
      dsimp only [A, x₀, σ, X, M]
      ring
    have h₁ : 0 ≤ 2 * L - 1 - B - N := by linarith
    have h₂ : 0 ≤ L - N - 1 := by linarith
    have h₃ : 0 ≤ B * (L + N) - (k + 1) * (L - N) := by
      have h := mul_nonneg hB hN
      nlinarith only [hfactor, h]
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right (hbase.trans (hmono.trans htop)) (by linarith)

private theorem increase_potential {K a b : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hb : 0 < b) (hab : a ≤ b) (m : ℕ) (hm : g a m < K) :
    policyPotential K b hb ((m : ℝ) * a) (g a m) (by positivity) ≤
      policyPotential K a ha ((m : ℝ) * a) (g a m) (by positivity) := by
  let e : ℝ := (m : ℝ) * a
  have he : 0 ≤ e := by dsimp [e]; positivity
  let k := cut K b e (g a m) hb he
  let B := cycleLength K b hb
  let L := cycleLength K a ha
  let N := m + k
  have hk : 0 < k := (cut_spec K b e (g a m) hb he).1
  have hcross : K ≤ g a m + rent b e k := (cut_spec K b e (g a m) hb he).2
  have hmL : m < L := by
    by_contra! h
    exact (not_lt_of_ge ((length_crosses (K := K) ha).trans (g_index_mono ha.le h))) hm
  have hkB : k ≤ B := by
    apply cut_le (length_pos hb)
    unfold rent
    have h₁ := g_nonneg ha.le m
    have h₂ : 0 ≤ (B : ℝ) * e := by positivity
    linarith [length_crosses (K := K) hb]
  have hBN : B ≤ N := by
    apply length_le (by dsimp [N]; omega)
    have h₁ := g_rate_mono hab m
    have h₂ := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg (α := ℝ) m)
    have h₃ := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) k)
    unfold rent at hcross
    dsimp only [N, e] at *
    rw [g_add]
    linarith only [h₁, h₃, hcross]
  have hNL : N ≤ L := by
    have hfirst : k ≤ L - m := by
      apply cut_le (by omega)
      have hg := g_rate_mono hab (L - m)
      unfold rent
      have hsum := g_add a m (L - m)
      rw [show m + (L - m) = L by omega] at hsum
      dsimp only [e]
      linarith only [hg, hsum, length_crosses (K := K) ha]
    dsimp [N]
    omega
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkBr : (k : ℝ) ≤ B := by exact_mod_cast hkB
  have hBNr : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hNLr : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hLn : 0 < L := length_pos ha
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hLn
  have hBr : 0 < (B : ℝ) := lt_of_lt_of_le hkr hkBr
  have hKbound : a * L * ((L : ℝ) - 1) / 2 ≤ K := by
    have hprev : g a (L - 1) < K := length_before hK (by omega)
    have hcast : ((L - 1 : ℕ) : ℝ) = L - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ L by omega))
    unfold g at hprev
    rw [hcast] at hprev
    nlinarith only [hprev]
  have hCr : K ≤ a * N * ((N : ℝ) + 1) / 2 +
      (b - a) * k * ((k : ℝ) + 1) / 2 := by
    have hNr : (N : ℝ) = (m : ℝ) + k := by dsimp [N]; push_cast; rfl
    unfold rent g at hcross
    dsimp only [e] at hcross
    rw [hNr]
    nlinarith only [hcross]
  have hr := increase_arithmetic ha.le hab hkr hkBr hBNr hNLr
    (fun h => by exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast h : B < L)))
    (fun h => by exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast h : k < B)))
    (fun h => by exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast h : N < L)))
    hKbound hCr
  dsimp only at hr
  rw [cut_old_rate ha m hm]
  change value K b hb e k ≤ _
  have hid : (L : ℝ) * B *
        ((m : ℝ) * fair K a ha - g a m - value K b hb e k) =
      (K - a * L * B / 2) * ((k : ℝ) * ((N : ℝ) - B) - (B - (k : ℝ)) * (L - (N : ℝ))) +
        a * L * B * (L - (N : ℝ)) * (N - (B : ℝ)) / 2 +
        L * B * k * (b - a) * (B - (k : ℝ)) / 2 := by
    have hfa : (L : ℝ) * fair K a ha = K + g a L := fair_mul ha
    have hfb : (B : ℝ) * fair K b hb = K + g b B := fair_mul hb
    have hNr : (N : ℝ) = (m : ℝ) + k := by dsimp [N]; push_cast; rfl
    rw [hNr]
    unfold value rent
    unfold g at hfa hfb ⊢
    dsimp only [e]
    linear_combination ((m : ℝ) * B) * hfa + ((k : ℝ) * L) * hfb
  have hnonneg : 0 ≤ (L : ℝ) * B *
      ((m : ℝ) * fair K a ha - g a m - value K b hb e k) := by rw [hid]; exact hr
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg (mul_pos hLr hBr))

private theorem policyCost_append (K : ℝ) (s : State) (xs ys : List ℝ) :
    policyCost K s (xs ++ ys) = policyCost K s xs + policyCost K (finish K s xs) ys := by
  induction xs generalizing s with
  | nil => simp [policyCost, finish]
  | cons a xs ih =>
    simp only [List.cons_append, policyCost, finish, List.foldl_cons]
    rw [ih, finish, add_assoc]

private theorem comparatorCost_append (K o : ℝ) (xs ys : List (ℝ × Bool)) :
    comparatorCost K o (xs ++ ys) =
      comparatorCost K o xs + comparatorCost K (comparatorFinish o xs) ys := by
  induction xs generalizing o with
  | nil => simp [comparatorCost, comparatorFinish]
  | cons p xs ih =>
    obtain ⟨a, r⟩ := p
    simp only [List.cons_append, comparatorCost, comparatorFinish, List.foldl_cons]
    rw [ih, comparatorFinish, add_assoc]

private theorem finish_snoc (K : ℝ) (s : State) (xs : List ℝ) (a : ℝ) :
    finish K s (xs ++ [a]) = advance K (finish K s xs) a := by
  simp [finish]

private theorem replicate_snoc (n : ℕ) (a : ℝ) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  rw [List.replicate_add]
  rfl

private theorem finish_first_block {K a : ℝ} (hK : 0 < K) (n : ℕ) :
    let s := finish K initial (List.replicate n a)
    s.dropSeen = false ∧ (s.previous = if n = 0 then none else some a) ∧
      ∃ m : ℕ, s.carry = (m : ℝ) * a ∧ s.acc = g a m ∧ g a m < K := by
  induction n with
  | zero => exact ⟨rfl, rfl, 0, by simp [finish, initial], by simp [finish, initial, g_zero],
      by simpa [g_zero] using hK⟩
  | succ n ih =>
    let s := finish K initial (List.replicate n a)
    obtain ⟨hd, hp, m, he, hA, _⟩ := ih
    change s.dropSeen = false at hd
    change s.previous = _ at hp
    change s.carry = _ at he
    change s.acc = _ at hA
    rw [replicate_snoc, finish_snoc]
    change (advance K s a).dropSeen = false ∧
      (advance K s a).previous = (if n + 1 = 0 then none else some a) ∧
      ∃ m : ℕ, (advance K s a).carry = (m : ℝ) * a ∧
        (advance K s a).acc = g a m ∧ g a m < K
    have hn : ¬ drop s a := by
      unfold drop
      rw [hp]
      split <;> simp
    refine ⟨by simp [advance, hd, hn], by simp [advance], ?_⟩
    cases hr : reset K s a
    · refine ⟨m + 1, ?_, ?_, ?_⟩
      · simp [advance, hr, he, Nat.cast_add, add_mul]
      · simp [advance, hr, he, hA, g_succ, Nat.cast_add]
        ring
      · have hno : ¬ crossing K s a := by
          intro h
          simp [reset, h] at hr
        have hlt := lt_of_not_ge hno
        change s.acc + (s.carry + a) < K at hlt
        rw [he, hA] at hlt
        rw [g_succ]
        push_cast
        linarith
    · refine ⟨0, by simp [advance, hr], by simp [advance, hr, g_zero], ?_⟩
      simpa [g_zero] using hK

private theorem policy_increase {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (m n : ℕ) :
    policyCost K initial (List.replicate m a ++ List.replicate n b) ≤
      (m : ℝ) * fair K a ha + (n : ℝ) * fair K b hb := by
  let s := finish K initial (List.replicate m a)
  let t := finish K s (List.replicate n b)
  have hs := valid_block hK ha.le m initial (valid_initial hK)
  have hp₁ := policy_segment hK ha m initial (valid_initial hK) (ordinary_initial K a)
  change policyCost K initial (List.replicate m a) =
    (m : ℝ) * fair K a ha + policyPotential K a ha 0 0 le_rfl -
      policyPotential K a ha s.carry s.acc hs.1 at hp₁
  rw [policyPotential_zero] at hp₁
  obtain ⟨_, hprev, j, he, hA, hj⟩ := finish_first_block (a := a) hK m
  have hbOrd : reset K s b = decide (crossing K s b) := by
    apply ordinary_if (Or.inl ?_)
    unfold drop
    rw [hprev]
    split <;> simp [not_lt.mpr hab]
  have hp₂ := policy_segment hK hb n s hs hbOrd
  have hmatch₁ := potential_congr (K := K) ha hs.1 (by positivity) he hA
  have hmatch₂ := potential_congr (K := K) hb hs.1 (by positivity) he hA
  have hjump := increase_potential hK ha hb hab j hj
  have ht := valid_block hK hb.le n s hs
  have hpend := policyPotential_ge hK hb ht.1 (A := t.acc)
  change t.carry ≤ policyPotential K b hb t.carry t.acc ht.1 at hpend
  have ht₀ : 0 ≤ t.carry := ht.1
  rw [policyCost_append]
  change policyCost K initial (List.replicate m a) +
    policyCost K s (List.replicate n b) ≤ _
  change policyCost K s (List.replicate n b) = (n : ℝ) * fair K b hb +
    policyPotential K b hb s.carry s.acc hs.1 -
      policyPotential K b hb t.carry t.acc ht.1 at hp₂
  linarith only [hp₁, hp₂, hmatch₁, hmatch₂, hjump, hpend, ht₀]

private theorem comparator_two_positive {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) (rs ss : List Bool) :
    let u := comparatorFinish 0 (block a rs)
    let v := comparatorFinish u (block b ss)
    let hu := comparatorFinish_nonneg_block ha.le le_rfl rs
    let hv := comparatorFinish_nonneg_block hb.le hu ss
    (rs.length : ℝ) * fair K a ha + (ss.length : ℝ) * fair K b hb +
        comparatorPotential K b hK hb u hu - comparatorPotential K a hK ha u hu -
        comparatorPotential K b hK hb v hv ≤ comparatorCost K 0 (block a rs ++ block b ss) := by
  intro u v hu hv
  have h₁ := comparator_segment hK ha (o := 0) le_rfl rs
  have h₂ := comparator_segment hK hb hu ss
  rw [comparatorPotential_zero] at h₁
  rw [comparatorCost_append]
  change _ ≤ comparatorCost K 0 (block a rs) + comparatorCost K u (block b ss)
  linarith only [h₁, h₂]

private theorem increased_block_bound {K a b : ℝ} (hK : 0 < K)
    (ha : 0 ≤ a) (hab : a ≤ b) (rs ss : List Bool) :
    policyCost K initial (List.replicate rs.length a ++ List.replicate ss.length b) ≤
      comparatorCost K 0 (block a rs ++ block b ss) + 2 * K := by
  rcases ha.eq_or_lt with rfl | ha
  · let s := finish K initial (List.replicate rs.length 0)
    have hp := zero_block hK rs.length initial rfl rfl (ordinary_initial K 0)
    have hprev := (finish_first_block hK (a := 0) rs.length).2.1
    have hord : reset K s b = decide (crossing K s b) := by
      apply ordinary_if (Or.inl ?_)
      unfold drop
      rw [hprev]
      split <;> simp [not_lt.mpr hab]
    have hs := single_block_bound hK hab (o := 0) le_rfl s hp.2.1 hp.2.2 hord ss
    have hc := comparatorCost_nonneg hK.le (o := 0) le_rfl
      (block 0 rs) (block_nonneg le_rfl rs)
    rw [policyCost_append, comparatorCost_append, zero_comparator_finish, hp.1]
    change 0 + policyCost K s (List.replicate ss.length b) ≤ _
    linarith only [hc, hs, hK]
  · have hb := lt_of_lt_of_le ha hab
    have hp := policy_increase hK ha hb hab rs.length ss.length
    have hc := comparator_two_positive hK ha hb rs ss
    have hu := comparatorFinish_nonneg_block ha.le (o := 0) le_rfl rs
    have hv := comparatorFinish_nonneg_block hb.le hu ss
    have h₁ := comparatorPotential_nonneg hK hb hu
    have h₂ := comparatorPotential_cap hK ha hu
    have h₃ := comparatorPotential_cap hK hb hv
    dsimp only at hc
    linarith only [hp, hc, h₁, h₂, h₃]

private theorem guarded_drop_bound {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 ≤ b) (rs : List Bool) (r : Bool) (ss : List Bool)
    (hguard : let s := finish K initial (List.replicate rs.length a)
      drop s b ∧ s.ordinarySeen = true ∧ s.dropSeen = false) :
    policyCost K initial (List.replicate rs.length a ++ List.replicate (ss.length + 1) b) ≤
      comparatorCost K 0 (block a rs ++ block b (r :: ss)) + 2 * K := by
  let s := finish K initial (List.replicate rs.length a)
  let t := advance K s b
  let o := comparatorFinish 0 (block a rs)
  change drop s b ∧ s.ordinarySeen = true ∧ s.dropSeen = false at hguard
  have hs := valid_block hK ha.le rs.length initial (valid_initial hK)
  have hr : reset K s b = true := by simp [reset, hguard.1, hguard.2.1, hguard.2.2]
  have ht₀ : t.carry = 0 := by simp [t, advance, hr]
  have htA : t.acc = 0 := by simp [t, advance, hr]
  have hbOrd := ordinary_same K b s
  have hp₁ := policy_segment hK ha rs.length initial (valid_initial hK) (ordinary_initial K a)
  change policyCost K initial (List.replicate rs.length a) =
    (rs.length : ℝ) * fair K a ha + policyPotential K a ha 0 0 le_rfl -
      policyPotential K a ha s.carry s.acc hs.1 at hp₁
  rw [policyPotential_zero] at hp₁
  have hpend := policyPotential_ge hK ha hs.1 (A := s.acc)
  rw [policyCost_append, List.replicate_succ]
  change policyCost K initial (List.replicate rs.length a) +
    (bill K s.carry b (reset K s b) + policyCost K t (List.replicate ss.length b)) ≤ _
  rw [hr, show bill K s.carry b true = s.carry + b + K from rfl]
  rcases hb.eq_or_lt with rfl | hb
  · have hp₂ := (zero_block hK ss.length t ht₀ htA hbOrd).1
    have hc₁ := comparator_segment hK ha (o := 0) le_rfl rs
    rw [comparatorPotential_zero] at hc₁
    have ho : 0 ≤ o := comparatorFinish_nonneg_block ha.le le_rfl rs
    have hc₀ := comparatorPotential_cap hK ha ho
    have hc₂ := comparatorCost_nonneg hK.le ho (block 0 (r :: ss))
      (block_nonneg le_rfl (r :: ss))
    rw [comparatorCost_append]
    change _ ≤ comparatorCost K 0 (block a rs) + comparatorCost K o (block 0 (r :: ss)) + 2 * K
    linarith only [hp₁, hp₂, hpend, hc₁, hc₀, hc₂]
  · have hab : b ≤ a := by
      have hd := hguard.1
      have hprev := (finish_first_block (a := a) hK rs.length).2.1
      unfold drop at hd
      rw [hprev] at hd
      split at hd
      · exact False.elim hd
      · exact hd.le
    have ht := valid_advance hK hb.le hs
    have hp₂ := policy_segment hK hb ss.length t ht hbOrd
    have htPot := potential_congr (K := K) hb ht.1 le_rfl ht₀ htA
    rw [policyPotential_zero] at htPot
    have hfin := valid_block hK hb.le ss.length t ht
    have hpend₂ := policyPotential_ge hK hb hfin.1
      (A := (finish K t (List.replicate ss.length b)).acc)
    have hpos := hfin.1
    have hrate := rate_le_fair hK hb
    have hc := comparator_two_positive hK ha hb rs (r :: ss)
    have ho : 0 ≤ o := comparatorFinish_nonneg_block ha.le le_rfl rs
    have hjump := comparatorPotential_rate hK hb ha hab ho
    have hcap := comparatorPotential_cap hK hb
      (comparatorFinish_nonneg_block hb.le ho (r :: ss))
    dsimp only at hc
    simp only [List.length_cons, Nat.cast_succ, add_mul, one_mul] at hc
    linarith only [hp₁, hp₂, hpend, htPot, hpend₂, hpos, hrate, hc, hjump, hcap]

private def cycleAccount (K : ℝ) (s : State) (o q : ℝ) : Prop :=
  s.carry + K ≤ q ∨ (s.acc ≤ q ∧ s.carry ≤ o)

private theorem cycleAccount_acc {K : ℝ} {s : State} {o q : ℝ} (hs : valid K s)
    (h : cycleAccount K s o q) : s.acc ≤ q := by
  rcases h with h | h
  · linarith [hs.1, hs.2.2]
  · exact h.1

private theorem no_cross_of_flag_false {K a : ℝ} {s : State}
    (h : (advance K s a).ordinarySeen = false) :
    s.ordinarySeen = false ∧ ¬ crossing K s a := by
  simpa [advance, Bool.or_eq_false_iff] using h

private theorem comparatorFinish_nonneg {o : ℝ} (ho : 0 ≤ o)
    (xs : List (ℝ × Bool)) (ha : ∀ p ∈ xs, 0 ≤ p.1) : 0 ≤ comparatorFinish o xs := by
  induction xs generalizing o with
  | nil => exact ho
  | cons p xs ih =>
    exact ih (nonneg_next o p.1 p.2 ho (ha p (by simp))) (fun p hp => ha p (by simp [hp]))

private theorem valid_finish {K : ℝ} (hK : 0 < K) (ys : List (ℝ × Bool)) (s : State)
    (hs : valid K s) (ha : ∀ p ∈ ys, 0 ≤ p.1) :
    valid K (finish K s (ys.map Prod.fst)) := by
  induction ys generalizing s with
  | nil => exact hs
  | cons p ys ih =>
    exact ih (advance K s p.1) (valid_advance hK (ha p (by simp)) hs)
      (fun p hp => ha p (by simp [hp]))

private theorem prefix_before_reset {K : ℝ} (hK : 0 < K) (xs : List (ℝ × Bool))
    (ha : ∀ p ∈ xs, 0 ≤ p.1) :
    let as := xs.map Prod.fst
    let s := finish K initial as
    let o := comparatorFinish 0 xs
    s.ordinarySeen = false →
      policyCost K initial as = s.acc ∧ cycleAccount K s o (comparatorCost K 0 xs) := by
  induction xs using List.reverseRecOn with
  | nil => intro as s o _; exact ⟨rfl, Or.inr ⟨le_rfl, le_rfl⟩⟩
  | append_singleton xs x ih =>
    obtain ⟨a, r⟩ := x
    have hx := ha (a, r) (by simp)
    have hxs : ∀ p ∈ xs, 0 ≤ p.1 := fun p hp => ha p (by simp [hp])
    let s := finish K initial (xs.map Prod.fst)
    let o := comparatorFinish 0 xs
    let t := advance K s a
    have ho : 0 ≤ o := comparatorFinish_nonneg le_rfl xs hxs
    have hs : valid K s := valid_finish hK xs initial (valid_initial hK) hxs
    simp only [List.map_append, List.map_cons, List.map_nil, finish_snoc, policyCost_append,
      comparatorCost_append]
    rw [show comparatorFinish 0 (xs ++ [(a, r)]) = nextCarry o a r by
      simp [comparatorFinish, List.foldl_append, o]]
    change t.ordinarySeen = false →
      policyCost K initial (xs.map Prod.fst) + policyCost K s [a] = t.acc ∧
        cycleAccount K t (nextCarry o a r) (comparatorCost K 0 xs + comparatorCost K o [(a, r)])
    intro ht
    obtain ⟨hflag, hnc⟩ := no_cross_of_flag_false ht
    have hb : reset K s a = false := by simp [reset, hflag, hnc]
    obtain ⟨hp, hc⟩ := ih hxs hflag
    change policyCost K initial (xs.map Prod.fst) = s.acc at hp
    constructor
    · simp [policyCost, bill, t, advance, hb, hp]
    · simpa [cycleAccount, t, advance, hb, comparatorCost] using
        billed_cycle hK.le hs.2.1 ho (r := r) hc

private theorem first_reset_suffix {K b : ℝ} (hK : 0 < K) (hb : 0 ≤ b)
    (rs : List Bool) (s : State) (o q : ℝ) (hs : valid K s) (ho : 0 ≤ o)
    (hflag : s.ordinarySeen = false)
    (hbudget : cycleAccount K s o q) :
    s.acc + policyCost K s (List.replicate rs.length b) ≤
      q + comparatorCost K o (block b rs) + 2 * K := by
  induction rs generalizing s o q with
  | nil =>
    simpa [policyCost, block, comparatorCost] using
      (cycleAccount_acc hs hbudget).trans (show q ≤ q + 2 * K by linarith)
  | cons r rs ih =>
    let t := advance K s b
    let Q := q + bill K o b r
    let O := nextCarry o b r
    let H := s.carry + b
    have hO : 0 ≤ O := nonneg_next o b r ho hb
    have hQ : H + K ≤ Q ∨ (s.acc + H ≤ Q ∧ H ≤ O) :=
      billed_cycle hK.le hs.2.1 ho hbudget
    change s.acc + (bill K s.carry b (reset K s b) + policyCost K t (List.replicate rs.length b)) ≤
      q + (bill K o b r + comparatorCost K O (block b rs)) + 2 * K
    by_cases hc : crossing K s b
    · have hr : reset K s b = true := by simp [reset, hc]
      have hcharge : s.acc + H + K ≤ Q + K := by
        rcases hQ with h | ⟨h, _⟩ <;> linarith [hs.2.2]
      have ht₀ : t.carry = 0 := by simp [t, advance, hr]
      have htA : t.acc = 0 := by simp [t, advance, hr]
      have ht := single_block_bound hK hb hO t ht₀ htA (ordinary_same K b s) rs
      rw [hr, show bill K s.carry b true = H + K from rfl]
      dsimp only [Q] at hcharge
      linarith only [ht, hcharge]
    · have hr : reset K s b = false := by simp [reset, hc, hflag]
      have ht₀ : t.carry = H := by simp [t, advance, hr, H]
      have htA : t.acc = s.acc + H := by simp [t, advance, hr, H]
      have htFlag : t.ordinarySeen = false := by simp [t, advance, hflag, hc]
      have htBudget : cycleAccount K t O Q := by simpa [cycleAccount, ht₀, htA] using hQ
      have h := ih t O Q (valid_advance hK hb hs) hO htFlag htBudget
      rw [htA] at h
      rw [hr, show bill K s.carry b false = H by simp [bill, H]]
      dsimp only [Q] at h
      linarith only [h]

private theorem two_block_bound {K a b : ℝ} (hK : 0 < K)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (rs ss : List Bool) :
    policyCost K initial (List.replicate rs.length a ++ List.replicate ss.length b) ≤
      comparatorCost K 0 (block a rs ++ block b ss) + 2 * K := by
  by_cases hab : a ≤ b
  · exact increased_block_bound hK ha hab rs ss
  have hba : b < a := lt_of_not_ge hab
  by_cases hz : rs.length = 0
  · have hr : rs = [] := List.length_eq_zero_iff.mp hz
    subst rs
    have h := single_block_bound hK hb (o := 0) le_rfl initial rfl rfl (ordinary_initial K b) ss
    simp only [List.length_nil, List.replicate_zero, List.nil_append, block, List.map_nil] at h ⊢
    linarith only [h, hK]
  cases ss with
  | nil =>
    have h := single_block_bound hK ha (o := 0) le_rfl initial rfl rfl (ordinary_initial K a) rs
    simp only [List.length_nil, List.replicate_zero, List.append_nil, block, List.map_nil] at h ⊢
    linarith only [h, hK]
  | cons r ss =>
    let s := finish K initial (List.replicate rs.length a)
    let o := comparatorFinish 0 (block a rs)
    have hs := valid_block hK ha rs.length initial (valid_initial hK)
    have ho : 0 ≤ o := comparatorFinish_nonneg_block ha le_rfl rs
    obtain ⟨hd₀, hprev, _⟩ := finish_first_block (a := a) hK rs.length
    change s.dropSeen = false at hd₀
    change s.previous = _ at hprev
    cases hflag : s.ordinarySeen
    · have hpre := prefix_before_reset hK (block a rs) (block_nonneg ha rs)
      simp only [block_rates] at hpre
      obtain ⟨hcost, hbudget⟩ := hpre hflag
      have hc := first_reset_suffix hK hb (r :: ss) s o
        (comparatorCost K 0 (block a rs)) hs ho hflag hbudget
      rw [policyCost_append, comparatorCost_append, hcost]
      exact hc
    · have hd : drop s b := by simp [drop, hprev, hz, hba]
      exact guarded_drop_bound hK (hb.trans_lt hba) hb rs r ss ⟨hd, hflag, hd₀⟩

/-- At most two maximal constant consecutive runs, with empty blocks allowed. -/
def AtMostTwoRuns (xs : List ℝ) : Prop :=
  ∃ (a b : ℝ) (m n : ℕ), xs = List.replicate m a ++ List.replicate n b

/-- One first-call decision plus one decision on each visible increment. -/
def sessionCost (K : ℝ) (xs : List ℝ) (first : Bool) (rs : List Bool) : ℝ :=
  bill K 0 0 first + comparatorCost K 0 (xs.zip rs)

/-- Evaluate the deterministic prefix rule at each nonempty visible prefix. -/
def actions (rule : List ℝ → Bool) (xs : List ℝ) : List Bool :=
  List.ofFn fun i : Fin xs.length => rule (xs.take (i.val + 1))

private theorem scheduled_rates (K : ℝ) (s : State) (xs : List ℝ) :
    (scheduled K s xs).map Prod.fst = xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => simp [scheduled, ih]

private theorem zip_actions (K : ℝ) (xs : List ℝ) :
    xs.zip (actions (prefixRule K) xs) = scheduled K initial xs := by
  let sc := scheduled K initial xs
  have hfst : sc.map Prod.fst = xs := scheduled_rates K initial xs
  have hlen : sc.length = xs.length := by simpa using congrArg List.length hfst
  have hacts : sc.map Prod.snd = actions (prefixRule K) xs := by
    apply List.ext_getElem
    · simp [actions, hlen]
    intro i h₁ h₂
    have h₃ : i < sc.length := by simpa using h₁
    have hg : sc[i]? = some sc[i] := List.getElem?_eq_getElem h₃
    have h₄ : (scheduled K ([].foldl (advance K) initial) xs)[i]? =
        some (sc[i].1, sc[i].2) := by
      change sc[i]? = some sc[i]
      exact hg
    have hr := scheduled_prefix K [] xs i sc[i].1 sc[i].2 h₄
    simpa [actions] using hr.symm
  exact (List.zip_of_prod hfst hacts).symm

private theorem zip_replicate (a : ℝ) (rs : List Bool) :
    (List.replicate rs.length a).zip rs = block a rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (a, r) :: (List.replicate rs.length a).zip rs = (a, r) :: block a rs
    rw [ih]

private theorem rates_nonneg_zip {xs : List ℝ} {rs : List Bool}
    (ha : ∀ a ∈ xs, 0 ≤ a) (h : rs.length = xs.length) :
    ∀ p ∈ xs.zip rs, 0 ≤ p.1 := by
  intro p hp
  apply ha
  rw [← List.map_fst_zip (l₁ := xs) (l₂ := rs) h.ge]
  exact List.mem_map_of_mem hp

/-- The additive guarantee on every session with at most two runs. -/
theorem additive_two_runs (K : ℝ) (hK : 0 < K) (xs : List ℝ) (ha : ∀ a ∈ xs, 0 ≤ a)
    (runs : AtMostTwoRuns xs) (first : Bool) (rs : List Bool) (hlen : rs.length = xs.length) :
    sessionCost K xs (prefixRule K []) (actions (prefixRule K) xs) ≤
      sessionCost K xs first rs + 2 * K := by
  obtain ⟨a, b, m, n, rfl⟩ := runs
  simp only [List.length_append, List.length_replicate] at hlen
  let left := rs.take m
  let right := rs.drop m
  have hl : left.length = m := by simp [left, List.length_take, hlen]
  have hr : right.length = n := by simp [right, List.length_drop, hlen]
  have hzip : (List.replicate m a ++ List.replicate n b).zip rs = block a left ++ block b right := by
    have happ : left ++ right = rs := List.take_append_drop m rs
    rw [← happ, List.zip_append (by simp [hl]), ← hl, ← hr, zip_replicate, zip_replicate]
  have hbound : policyCost K initial (List.replicate m a ++ List.replicate n b) ≤
        comparatorCost K 0 (block a left ++ block b right) + 2 * K := by
    by_cases hm : m = 0
    · have hzero : left = [] := List.length_eq_zero_iff.mp (hl.trans hm)
      rw [hm, hzero]
      change policyCost K initial (List.replicate n b) ≤ comparatorCost K 0 (block b right) + 2 * K
      by_cases hn : n = 0
      · have hrzero : right = [] := List.length_eq_zero_iff.mp (hr.trans hn)
        rw [hn, hrzero]
        simp [policyCost, block, comparatorCost, hK.le]
      · have hb : 0 ≤ b := ha b (by simp [List.mem_replicate, hn])
        have hcore := single_block_bound hK hb (o := 0) le_rfl initial rfl rfl
          (ordinary_initial K b) right
        rw [hr] at hcore
        linarith only [hcore, hK]
    · have hpa : 0 ≤ a := ha a (by simp [List.mem_replicate, hm])
      by_cases hn : n = 0
      · have hzero : right = [] := List.length_eq_zero_iff.mp (hr.trans hn)
        rw [hn, hzero]
        change policyCost K initial (List.replicate m a ++ []) ≤
          comparatorCost K 0 (block a left ++ []) + 2 * K
        rw [List.append_nil, List.append_nil]
        have hcore := single_block_bound hK hpa (o := 0) le_rfl initial rfl rfl
          (ordinary_initial K a) left
        rw [hl] at hcore
        linarith only [hcore, hK]
      · have hpb : 0 ≤ b := ha b (by simp [List.mem_replicate, hn])
        simpa only [hl, hr] using two_block_bound hK hpa hpb left right
  have he : comparatorCost K 0 (scheduled K initial (List.replicate m a ++ List.replicate n b)) =
      policyCost K initial (List.replicate m a ++ List.replicate n b) := scheduled_cost K initial _
  rw [sessionCost, zip_actions, he, sessionCost, hzip, prefixRule_nil]
  cases first <;> simp [bill] <;> linarith only [hbound, hK]

/-- The fixed prefix rule simultaneously has universal factor three and two-run loss at most (2K). -/
theorem guarded_prefix_guarantees (K : ℝ) (hK : 0 < K) (xs : List ℝ)
    (ha : ∀ a ∈ xs, 0 ≤ a) (first : Bool) (rs : List Bool) (hlen : rs.length = xs.length) :
    let online := sessionCost K xs (prefixRule K []) (actions (prefixRule K) xs)
    let offline := sessionCost K xs first rs
    online ≤ 3 * offline ∧ (AtMostTwoRuns xs → online ≤ offline + 2 * K) := by
  refine ⟨?_, fun h => additive_two_runs K hK xs ha h first rs hlen⟩
  have h := factor_three K hK (xs.zip rs) (rates_nonneg_zip ha hlen) first
  rw [List.map_fst_zip hlen.ge] at h
  have hzero : bill K 0 0 false = 0 := by simp [bill]
  simpa [sessionCost, zip_actions, hzero, prefixRule_nil] using h

/-- Schiavo's third question in §5.B, with a universal factor of three. -/
theorem schiavo_section5b_third_question :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ K : ℝ, 0 < K →
      ∃ rule : List ℝ → Bool,
        ∀ (xs : List ℝ), (∀ a ∈ xs, 0 ≤ a) →
        ∀ (first : Bool) (rs : List Bool), rs.length = xs.length →
          let online := sessionCost K xs (rule []) (actions rule xs)
          let offline := sessionCost K xs first rs
          online ≤ c * offline ∧ (AtMostTwoRuns xs → online ≤ offline + 2 * K) := by
  exact ⟨3, by norm_num, fun K hK => ⟨prefixRule K, guarded_prefix_guarantees K hK⟩⟩

end

end GuardedRentOrBuy
