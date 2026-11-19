/- GID: D5/S3/Arith/Primes/ShevelevConjectureForty
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/ShevelevConjectureForty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.PrimeCounting]
   utility: none
   digest: Ramanujan and Labos prime minima and their unbounded separation. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import D5.S3.Arith.Primes.PrimeDoubleCompositeWindow
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

namespace D5.S3.Arith.Primes.ShevelevConjectureForty

open Filter
open scoped Topology

/-- The number of primes in the integer dyadic interval. -/
def count (m : ℕ) : ℕ := Nat.primeCounting m - Nat.primeCounting (m / 2)

/-- The subtrahend never exceeds the minuend. -/
theorem subtrahend_le (m : ℕ) : Nat.primeCounting (m / 2) ≤ Nat.primeCounting m :=
  Nat.monotone_primeCounting (Nat.div_le_self m 2)

/-- The counting function increases precisely at primes. -/
theorem primeCounting_succ (m : ℕ) :
    Nat.primeCounting (m + 1) = Nat.primeCounting m + if (m + 1).Prime then 1 else 0 := by
  exact Nat.count_succ Nat.Prime (m + 1)

/-- An upward step of the dyadic count has size at most one. -/
theorem count_succ_le (m : ℕ) : count (m + 1) ≤ count m + 1 := by
  have htop := primeCounting_succ m
  have hbot := Nat.monotone_primeCounting (show m / 2 ≤ (m + 1) / 2 by omega)
  have hn := subtrahend_le m
  unfold count
  split_ifs at htop <;> omega

/-- Every positive level below a terminal value is attained at a positive integer. -/
theorem exists_count_eq {n b : ℕ} (hn : 1 ≤ n) (hb : n ≤ count b) :
    ∃ m, 0 < m ∧ m ≤ b ∧ count m = n := by
  have hex : ∃ m, n ≤ count m := ⟨b, hb⟩
  let m := Nat.find hex
  have hm : n ≤ count m := Nat.find_spec hex
  have hmb : m ≤ b := Nat.find_min' hex hb
  have hmpos : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    simp [hz, count] at hm
    omega
  have hprev : count (m - 1) < n := by
    exact Nat.lt_of_not_ge (Nat.find_min hex (by omega))
  have hstep := count_succ_le (m - 1)
  have heq : m - 1 + 1 = m := by omega
  rw [heq] at hstep
  exact ⟨m, hmpos, hmb, by omega⟩

/-- Prime counting is constant across an interval containing no new prime. -/
theorem primeCounting_eq_of_no_prime {a b : ℕ} (hab : a ≤ b)
    (hfree : ∀ t, a < t → t ≤ b → ¬t.Prime) :
    Nat.primeCounting b = Nat.primeCounting a := by
  apply le_antisymm ?_ (Nat.monotone_primeCounting hab)
  by_contra h
  obtain ⟨t, ht, htp⟩ := Nat.exists_of_count_lt_count (p := Nat.Prime)
    (show Nat.count Nat.Prime (a + 1) < Nat.count Nat.Prime (b + 1) from
      Nat.lt_of_not_ge h)
  exact hfree t (by have := ht.1; omega) (by have := ht.2; omega) htp

/-- The prime p itself is counted immediately before twice p. -/
theorem count_before_double_pos {p : ℕ} (hp : p.Prime) : 1 ≤ count (2 * p - 1) := by
  have hp2 := hp.two_le
  have hjump := primeCounting_succ (p - 1)
  have heq : p - 1 + 1 = p := by omega
  rw [heq, if_pos hp] at hjump
  have htop := Nat.monotone_primeCounting (show p ≤ 2 * p - 1 by omega)
  have hhalf : (2 * p - 1) / 2 = p - 1 := by omega
  unfold count
  rw [hhalf]
  omega

/-- On a prime-free window the earlier dyadic count is no smaller. -/
theorem count_window_left {H p : ℕ} (hH : 1 ≤ H)
    (hfree : ∀ t, 2 * p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime) :
    count (2 * p - 1) ≤ count (2 * p - H) := by
  have ht := primeCounting_eq_of_no_prime
    (show 2 * p - H ≤ 2 * p - 1 by omega)
    (fun t ht ht' => hfree t (by omega) (by omega))
  have hb := Nat.monotone_primeCounting
    (show (2 * p - H) / 2 ≤ (2 * p - 1) / 2 by omega)
  unfold count
  omega

/-- Crossing twice a prime strictly decreases the count on a prime-free window. -/
theorem count_window_right {H p : ℕ} (hpp : p.Prime)
    (hfree : ∀ t, 2 * p - H ≤ t → t ≤ 2 * p + H → ¬t.Prime) :
    count (2 * p + H) < count (2 * p - 1) := by
  have hp2 := hpp.two_le
  have ht := primeCounting_eq_of_no_prime
    (show 2 * p - 1 ≤ 2 * p + H by omega)
    (fun t ht ht' => hfree t (by omega) ht')
  have hjump := primeCounting_succ (p - 1)
  rw [show p - 1 + 1 = p by omega, if_pos hpp] at hjump
  have hb := Nat.monotone_primeCounting (show p ≤ (2 * p + H) / 2 by omega)
  have hn := subtrahend_le (2 * p + H)
  have hhalf : (2 * p - 1) / 2 = p - 1 := by omega
  unfold count
  rw [hhalf]
  omega



/-- The frozen theta asymptotic implies eventual growth in every dyadic interval. -/
theorem eventually_count_ge (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, k ≤ Nat.primeCounting (2 * m) - Nat.primeCounting m := by
  classical
  have htheta := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have hlo : ∀ᶠ x : ℝ in atTop, (5 / 6 : ℝ) * x ≤ Chebyshev.theta x := by
    filter_upwards [htheta.eventually (eventually_gt_nhds (by norm_num : (5 / 6 : ℝ) < 1)),
      eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    exact ((lt_div_iff₀ hxpos).mp hx).le
  have hhi : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (7 / 6 : ℝ) * x := by
    filter_upwards [htheta.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 7 / 6)),
      eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    exact ((div_lt_iff₀ hxpos).mp hx).le
  have htwotop : Tendsto (fun m : ℕ => (2 : ℝ) * m) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlower : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / 2 ≤ Chebyshev.theta (2 * m) - Chebyshev.theta m := by
    filter_upwards [htwotop.eventually hlo, tendsto_natCast_atTop_atTop.eventually hhi]
      with m hm2 hm
    nlinarith
  have hweight (m : ℕ) : Chebyshev.theta (2 * m) - Chebyshev.theta m ≤
      ((Nat.primeCounting (2 * m) - Nat.primeCounting m : ℕ) : ℝ) *
        Real.log (2 * m) := by
    have hsub : Nat.primesLE m ⊆ Nat.primesLE (2 * m) := by
      intro p hp
      obtain ⟨hpm, hpp⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨by omega, hpp⟩
    have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
    have hbound : ∑ p ∈ Nat.primesLE (2 * m) \ Nat.primesLE m, Real.log (p : ℝ) ≤
        ∑ _p ∈ Nat.primesLE (2 * m) \ Nat.primesLE m, Real.log ((2 * m : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpm := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hpm.2.pos) (by exact_mod_cast hpm.1)
    rw [Finset.sum_const, Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting,
      nsmul_eq_mul] at hbound
    rw [← Chebyshev.theta_eq_sum_primesLE_log (2 * m),
      ← Chebyshev.theta_eq_sum_primesLE_log m] at hsum
    push_cast at hsum hbound
    linarith
  have hlog : Tendsto (fun m : ℕ => Real.log (2 * (m : ℝ)) / (m : ℝ))
      atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htwotop).mul_const 2
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    change Real.log (2 * (m : ℝ)) / (2 * (m : ℝ)) * 2 =
      Real.log (2 * (m : ℝ)) / (m : ℝ)
    field_simp
    <;> ring
  have hsmall : ∀ᶠ m : ℕ in atTop,
      (k : ℝ) * (Real.log (2 * (m : ℝ)) / (m : ℝ)) < 1 / 2 := by
    have h := hlog.const_mul (k : ℝ)
    simp only [mul_zero] at h
    exact h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hlower, hsmall, eventually_ge_atTop (1 : ℕ)] with m hm hs hmpos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hm0 : (0 : ℝ) < m := by linarith
  have hprod : (k : ℝ) * Real.log (2 * (m : ℝ)) < (m : ℝ) / 2 := by
    have h := (mul_lt_mul_of_pos_right hs hm0)
    field_simp at h
    nlinarith
  have hw := hweight m
  have hlogpos : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by nlinarith)
  by_contra hnot
  have hc : ((Nat.primeCounting (2 * m) - Nat.primeCounting m : ℕ) : ℝ) ≤ k := by
    exact_mod_cast (show Nat.primeCounting (2 * m) - Nat.primeCounting m ≤ k by omega)
  have hmul := mul_le_mul_of_nonneg_right hc hlogpos.le
  nlinarith

open Nat in
/-- Number of primes in (x/2, x] for real x. -/
noncomputable def ramanujanCount (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊ - Nat.primeCounting ⌊x / 2⌋₊

/-- Journal Definition 1 threshold form and Definition 3 occurrence form. -/
def RamanujanSet (n : ℕ) : Set ℕ := {m | 0 < m ∧ ∀ x : ℝ, (m : ℝ) ≤ x → n ≤ ramanujanCount x}
def LabosSet (n : ℕ) : Set ℕ := {m | 0 < m ∧ ramanujanCount m = n}

noncomputable def ramanujanPrime (n : ℕ) : ℕ := sInf (RamanujanSet n)
noncomputable def labosPrime (n : ℕ) : ℕ := sInf (LabosSet n)

/-- The natural subtraction in the source count does not truncate, even for negative x. -/
theorem primeCounting_half_floor_le (x : ℝ) :
    Nat.primeCounting ⌊x / 2⌋₊ ≤ Nat.primeCounting ⌊x⌋₊ := by
  rw [Nat.floor_div_ofNat]
  exact Nat.monotone_primeCounting (Nat.div_le_self _ _)

/-- Adding the lower endpoint count recovers the upper endpoint count. -/
theorem ramanujanCount_add_half (x : ℝ) :
    ramanujanCount x + Nat.primeCounting ⌊x / 2⌋₊ = Nat.primeCounting ⌊x⌋₊ := by
  exact Nat.sub_add_cancel (primeCounting_half_floor_le x)

/-- The real count is the integer dyadic count at the natural floor. -/
theorem ramanujanCount_eq_count_floor (x : ℝ) :
    ramanujanCount x = count ⌊x⌋₊ := by
  have h := ramanujanCount_add_half x
  rw [Nat.floor_div_ofNat] at h
  unfold count
  omega

/-- Integer inputs recover the integer dyadic count. -/
theorem ramanujanCount_nat (m : ℕ) :
    ramanujanCount m = count m := by
  rw [ramanujanCount_eq_count_floor, Nat.floor_natCast]

/-- The defining Ramanujan set is nonempty, including at level zero. -/
theorem ramanujanSet_nonempty (n : ℕ) : (RamanujanSet n).Nonempty := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (eventually_count_ge n)
  refine ⟨2 * (M + 1), by omega, ?_⟩
  intro x hx
  have hfloor : 2 * (M + 1) ≤ ⌊x⌋₊ := by
    have := Nat.floor_mono hx
    simpa only [Nat.floor_natCast] using this
  have hg := hM (⌊x⌋₊ / 2) (show M ≤ ⌊x⌋₊ / 2 by omega)
  have hp := Nat.monotone_primeCounting (show 2 * (⌊x⌋₊ / 2) ≤ ⌊x⌋₊ by omega)
  rw [ramanujanCount_eq_count_floor]
  unfold count
  omega

/-- Every positive level has a positive integer first occurrence. -/
theorem labosSet_nonempty (n : ℕ) (hn : 1 ≤ n) : (LabosSet n).Nonempty := by
  obtain ⟨b, _hb, hcount⟩ := ramanujanSet_nonempty n
  have hb := hcount b le_rfl
  rw [ramanujanCount_nat] at hb
  obtain ⟨m, hm, _hmb, heq⟩ := exists_count_eq hn hb
  refine ⟨m, hm, ?_⟩
  rw [ramanujanCount_nat, heq]

/-- A composite window around twice a prime separates a first occurrence from stability. -/
theorem exists_separation (H : ℕ) :
    ∃ n, 1 ≤ n ∧ labosPrime n + H < ramanujanPrime n := by
  obtain ⟨p, _hpB, hpH, hpp, hfree⟩ :=
    PrimeDoubleCompositeWindow.exists_prime_double_composite_window (H + 1) 0
  let n := count (2 * p - 1)
  have hn : 1 ≤ n := count_before_double_pos hpp
  have hleft := count_window_left (by omega : 1 ≤ H + 1) hfree
  have hright := count_window_right hpp hfree
  obtain ⟨m, hmpos, hmb, hm⟩ := exists_count_eq hn hleft
  have hL : labosPrime n ≤ 2 * p - (H + 1) := by
    have hmL : m ∈ LabosSet n := by
      refine ⟨hmpos, ?_⟩
      rw [ramanujanCount_nat]
      exact hm
    exact (Nat.sInf_le hmL).trans hmb
  have hR : 2 * p + (H + 1) < ramanujanPrime n := by
    by_contra h
    have hmem := Nat.sInf_mem (ramanujanSet_nonempty n)
    have hbound := hmem.2 ((2 * p + (H + 1) : ℕ) : ℝ) (by exact_mod_cast (show
      ramanujanPrime n ≤ 2 * p + (H + 1) by omega))
    rw [ramanujanCount_nat] at hbound
    omega
  exact ⟨n, hn, by omega⟩

/-- Shevelev 2012 Conjecture 40: lim sup (R_n − L_n) = ∞. -/
theorem result : ∀ H N : ℕ, ∃ n ≥ N, 1 ≤ n ∧ labosPrime n + H < ramanujanPrime n := by
  intro H N
  let K := max H ((Finset.range N).sup ramanujanPrime)
  obtain ⟨n, hn, hsep⟩ := exists_separation K
  have hnN : N ≤ n := by
    by_contra h
    have hR : ramanujanPrime n ≤ (Finset.range N).sup ramanujanPrime :=
      Finset.le_sup (f := ramanujanPrime) (Finset.mem_range.mpr (by omega))
    have hL : 0 < labosPrime n := (Nat.sInf_mem (labosSet_nonempty n hn)).1
    have hK : ramanujanPrime n ≤ K := hR.trans (le_max_right _ _)
    have hlt : K < labosPrime n + K := by omega
    exact (not_lt_of_ge hK) (hlt.trans hsep)
  refine ⟨n, hnN, hn, ?_⟩
  have hHK : H ≤ K := le_max_left _ _
  omega

end D5.S3.Arith.Primes.ShevelevConjectureForty
