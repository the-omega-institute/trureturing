/- GID: D5/S3/Arith/FactorialRatio/CompactFactorialGcd
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/CompactFactorialGcd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: The exact compact factorial gcd lies between the tail LCM and its factorial multiple. -/

module

public import D5.S3.Arith.FactorialRatio.RankOneLCMGcd
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
The compact factorial family uses one integer parameter for a product of
exact factorial quotients. The lower bound counts marks in consecutive
blocks of residues. The upper bound uses two prime-dependent parameters
and Legendre's formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.CompactFactorialGcd

open Finset
open scoped Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)

public theorem div_mod_of_eq {n q d u : ℕ} (hq : 0 < q)
    (hn : n = q * d + u) (hu : u < q) : n / q = d ∧ n % q = u := by
  have hdiv : n / q = d := calc
    n / q = (u + q * d) / q := by rw [hn, add_comm (q * d) u]
    _ = u / q + d := Nat.add_mul_div_left _ _ hq
    _ = d := by rw [Nat.div_eq_of_lt hu, zero_add]
  have h := Nat.div_add_mod n q
  rw [hdiv] at h
  exact ⟨hdiv, by omega⟩

/-- The residue sum is the only source of a carry in the quotient of a sum. -/
public theorem div_mod_add (x y : ℕ) {q : ℕ} (hq : 0 < q) :
    (x + y) / q = x / q + y / q + (x % q + y % q) / q ∧
    (x + y) % q = (x % q + y % q) % q := by
  let u := x % q + y % q
  have heq : x + y = q * (x / q + y / q + u / q) + u % q := calc
    x + y = (q * (x / q) + x % q) + (q * (y / q) + y % q) := by
      rw [Nat.div_add_mod x q, Nat.div_add_mod y q]
    _ = q * (x / q + y / q) + u := by dsimp [u]; ring
    _ = q * (x / q + y / q) + (q * (u / q) + u % q) := by
      rw [Nat.div_add_mod u q]
    _ = _ := by ring
  exact div_mod_of_eq hq heq (Nat.mod_lt u hq)

/-- A carry occurs exactly when the remainder of the sum is smaller than
the remainder of the first addend. -/
private theorem two_floor_carry (x y : ℕ) {q : ℕ} (hq : 0 < q) :
    x / q + y / q + (if x % q ≤ (x + y) % q then 0 else 1) = (x + y) / q := by
  obtain ⟨hdiv, hmod⟩ := div_mod_add x y hq
  by_cases h : x % q + y % q < q
  · rw [Nat.div_eq_of_lt h] at hdiv
    rw [hmod, Nat.mod_eq_of_lt h, ite_eq_left (Nat.le_add_right _ _)]
    exact hdiv.symm
  · have hy := Nat.mod_lt y hq
    have hx := Nat.mod_lt x hq
    have hsum : x % q + y % q = q * 1 + (x % q + y % q - q) := by omega
    obtain ⟨hd, hm⟩ := div_mod_of_eq hq hsum (by omega)
    have hlt : ¬ x % q ≤ (x + y) % q := by rw [hmod, hm]; omega
    rw [ite_eq_right hlt, hdiv, hd]

/-- Number of positive integers at most `t` whose positive residue modulo
`q` lies between `1` and `a`. -/
private def marks (q a t : ℕ) : ℕ := (t / q) * a + min (t % q) a

private theorem marks_density {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) (t : ℕ) :
    t * a ≤ q * marks q a t := by
  have hmin : (t % q) * a ≤ q * min (t % q) a := by
    rcases le_total (t % q) a with h | h
    · rw [min_eq_left h, mul_comm (t % q) a]
      exact Nat.mul_le_mul_right _ ha
    · rw [min_eq_right h]
      exact Nat.mul_le_mul_right _ (Nat.mod_lt t hq).le
  calc
    t * a = (q * (t / q) + t % q) * a := by rw [Nat.div_add_mod]
    _ = q * ((t / q) * a) + (t % q) * a := by ring
    _ ≤ q * ((t / q) * a) + q * min (t % q) a := Nat.add_le_add_left hmin _
    _ = q * marks q a t := by unfold marks; ring

/-- A block of length `w` contributes at most `w` marks. A block
ending at residue at least `a + w` contributes zero marks. -/
private theorem marks_step {q a w : ℕ} (ha : a ≤ q) (hw : w < q) (t : ℕ) :
    marks q a (t + w) ≤
      marks q a t + (if (t + w) % q < a + w then w else 0) := by
  have hq : 0 < q := by omega
  let u := t % q
  have hu : u < q := Nat.mod_lt _ hq
  have ht : t + w = q * (t / q) + (u + w) := by
    have h := Nat.div_add_mod t q
    change q * (t / q) + u = t at h
    omega
  by_cases hwrap : u + w < q
  · obtain ⟨hd, hm⟩ := div_mod_of_eq hq ht hwrap
    unfold marks
    rw [hd, hm]
    change (t / q) * a + min (u + w) a ≤
      (t / q) * a + min u a + (if u + w < a + w then w else 0)
    by_cases hgood : u + w < a + w
    · rw [ite_eq_left hgood, min_eq_left (by omega : u ≤ a)]
      have hmin := min_le_left (u + w) a
      omega
    · simp only [ite_eq_right hgood, min_eq_right (show a ≤ u by omega),
        min_eq_right (show a ≤ u + w by omega), Nat.add_zero, le_rfl]
  · have ht' : t + w = q * (t / q + 1) + (u + w - q) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    obtain ⟨hd, hm⟩ := div_mod_of_eq hq ht' (by omega)
    have hgood : u + w - q < a + w := by omega
    have hloss : a ≤ min u a + (q - u) := by
      rcases le_total u a with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; omega
    have hmin := min_le_left (u + w - q) a
    unfold marks
    rw [hd, hm, ite_eq_left hgood, Nat.add_mul, Nat.one_mul]
    change (t / q) * a + a + min (u + w - q) a ≤ (t / q) * a + min u a + w
    omega

private def goodBlocks (q a w r : ℕ) : ℕ :=
  ∑ i ∈ range r, if ((i + 1) * w) % q < a + w then 1 else 0

private theorem marks_le_goodBlocks {q a w : ℕ} (ha : a ≤ q) (hw : w < q)
    (r : ℕ) : marks q a (r * w) ≤ w * goodBlocks q a w r := by
  induction r with
  | zero => simp [marks, goodBlocks]
  | succ r ih =>
    have hstep : (r + 1) * w = r * w + w := by rw [Nat.add_mul, Nat.one_mul]
    have h := marks_step ha hw (r * w)
    rw [← hstep] at h
    unfold goodBlocks at ih ⊢
    rw [Finset.sum_range_succ, Nat.mul_add]
    refine h.trans (Nat.add_le_add ih ?_)
    by_cases hgood : ((r + 1) * w) % q < a + w <;> simp [hgood]

private theorem goodBlocks_density {q a w : ℕ} (ha : a ≤ q)
    (hw : 0 < w) (hwq : w < q) (r : ℕ) : r * a ≤ q * goodBlocks q a w r := by
  refine Nat.le_of_mul_le_mul_right ?_ hw
  calc
    (r * a) * w = (r * w) * a := by ring
    _ ≤ q * marks q a (r * w) := marks_density (by omega) ha _
    _ ≤ q * (w * goodBlocks q a w r) := Nat.mul_le_mul_left _ (marks_le_goodBlocks ha hwq r)
    _ = (q * goodBlocks q a w r) * w := by ring

@[expose] public def pairedFloor (q s b i : ℕ) : ℕ :=
  (i + 1) * b / q + (s - i * b) / q - b / q

@[expose] public def floorSum (q r s b : ℕ) : ℕ := ∑ i ∈ range r, pairedFloor q s b i

public theorem pairedFloor_carry {q s b i : ℕ} (hq : 0 < q) (hi : i * b ≤ s) :
    (i + 1) * b / q + (s - i * b) / q +
      (if ((i + 1) * (b % q)) % q ≤ (s + b) % q then 0 else 1) = (s + b) / q := by
  have hmul : (i + 1) * b = i * b + b := by rw [Nat.add_mul, Nat.one_mul]
  have hsum : (i + 1) * b + (s - i * b) = s + b := by rw [hmul]; omega
  have hmod : ((i + 1) * b) % q = ((i + 1) * (b % q)) % q := by
    rw [Nat.mul_mod (i + 1) b q, Nat.mul_mod (i + 1) (b % q) q, Nat.mod_mod]
  simpa only [hsum, hmod] using two_floor_carry ((i + 1) * b) (s - i * b) hq

private theorem head_div {q r s : ℕ} (hq : 0 < q) :
    (r * s + (r - 1)) / q = r * (s / q) + (r * (s % q) + (r - 1)) / q := by
  have heq : r * s + (r - 1) = (r * (s % q) + (r - 1)) + q * (r * (s / q)) := calc
    r * s + (r - 1) = r * (q * (s / q) + s % q) + (r - 1) := by rw [Nat.div_add_mod]
    _ = _ := by ring
  rw [heq, Nat.add_mul_div_left _ _ hq, add_comm]

private theorem remainder_head_le {q r v : ℕ} (hq : 0 < q) (hr : 1 ≤ r) (hv : v < q) :
    (r * v + (r - 1)) / q ≤ r - 1 := by
  have hmul := Nat.mul_le_mul_left r (show v + 1 ≤ q by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hdiv := (Nat.div_lt_iff_lt_mul hq).mpr
    (show r * v + (r - 1) < r * q by omega)
  omega

/-- The compact tail count is bounded by the paired floor sum at any
modulus `q ≥ 2`. This holds throughout the admissible parameter range. -/
public theorem selberg_floor_lower {q r s b : ℕ} (hq : 2 ≤ q) (hr : 1 ≤ r)
    (hb : r * b ≤ s) : (r * s + (r - 1)) / q - (r - 1) ≤ floorSum q r s b := by
  have hqpos : 0 < q := by omega
  have hv := Nat.mod_lt s hqpos
  have hw := Nat.mod_lt b hqpos
  have hhead := remainder_head_le hqpos hr hv
  rw [head_div hqpos]
  by_cases hk : s / q = 0
  · rw [hk, mul_zero, zero_add, Nat.sub_eq_zero_of_le hhead]
    exact Nat.zero_le _
  have hkpos : 1 ≤ s / q := Nat.pos_of_ne_zero hk
  have hi (i : ℕ) (hir : i ∈ range r) : i * b ≤ s :=
    (Nat.mul_le_mul_right b (Nat.le_of_lt (Finset.mem_range.mp hir))).trans hb
  obtain ⟨hdiv, hmod⟩ := div_mod_add s b hqpos
  have hfrom (h : ∀ i ∈ range r, s / q ≤ pairedFloor q s b i) :
      r * (s / q) + (r * (s % q) + (r - 1)) / q - (r - 1) ≤ floorSum q r s b := by
    calc
      _ ≤ r * (s / q) := by omega
      _ = ∑ _i ∈ range r, s / q := by simp
      _ ≤ _ := Finset.sum_le_sum h
  by_cases hwrap : q ≤ s % q + b % q
  · apply hfrom
    intro i hir
    have hcarry := pairedFloor_carry hqpos (hi i hir)
    have hpos := Nat.div_pos hwrap hqpos
    rw [hdiv] at hcarry
    unfold pairedFloor
    split at hcarry <;> omega
  · have hnowrap : s % q + b % q < q := by omega
    rw [Nat.div_eq_of_lt hnowrap, add_zero] at hdiv
    rw [Nat.mod_eq_of_lt hnowrap] at hmod
    by_cases hwzero : b % q = 0
    · apply hfrom
      intro i hir
      have hcarry := pairedFloor_carry hqpos (hi i hir)
      rw [hwzero, mul_zero, Nat.zero_mod, ite_eq_left (Nat.zero_le _), add_zero, hdiv] at hcarry
      unfold pairedFloor
      omega
    · let g := goodBlocks q (s % q + 1) (b % q) r
      have hg : r * (s % q + 1) ≤ q * g :=
        goodBlocks_density (by omega) (by omega) hw r
      have hlt : r * (s % q) + (r - 1) < g * q := by
        rw [Nat.mul_add, Nat.mul_one] at hg
        rw [mul_comm g q]
        omega
      have hcount := (Nat.div_lt_iff_lt_mul hqpos).mpr hlt
      have htotal : floorSum q r s b = r * (s / q - 1) + g := by
        unfold floorSum g goodBlocks
        have hconst : (∑ _i ∈ range r, (s / q - 1)) = r * (s / q - 1) := by simp
        rw [← hconst, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hir
        have hcarry := pairedFloor_carry hqpos (hi i hir)
        rw [hdiv, hmod] at hcarry
        unfold pairedFloor
        by_cases hgood : ((i + 1) * (b % q)) % q < s % q + 1 + b % q
        · have hle : ((i + 1) * (b % q)) % q ≤ s % q + b % q := by omega
          rw [ite_eq_left hgood]
          rw [ite_eq_left hle] at hcarry
          omega
        · have hle : ¬ ((i + 1) * (b % q)) % q ≤ s % q + b % q := by omega
          rw [ite_eq_right hgood]
          rw [ite_eq_right hle] at hcarry
          omega
      have hsplit : r * (s / q) = r * (s / q - 1) + r := calc
        r * (s / q) = r * ((s / q - 1) + 1) := by
          rw [Nat.sub_add_cancel hkpos]
        _ = _ := by rw [Nat.mul_add, Nat.mul_one]
      rw [htotal]
      omega

/-- The factorial product at parameter `b`, with indices `j = i + 1`.
The intended range is `r * b ≤ s`. -/
@[expose] public def selbergFactorial (r s b : ℕ) : ℕ :=
  ∏ i ∈ range r, ((i + 1) * b)! / b ! * (s - (r - (i + 1)) * b)!

public theorem selbergFactorial_eq_paired (r s b : ℕ) :
    selbergFactorial r s b = ∏ i ∈ range r, ((i + 1) * b)! / b ! * (s - i * b)! := by
  have hreverse : (∏ i ∈ range r, (s - (r - (i + 1)) * b)!) =
      ∏ i ∈ range r, (s - i * b)! := calc
    _ = ∏ i ∈ range r, (s - (r - 1 - i) * b)! := by
      apply Finset.prod_congr rfl
      intro i _
      rw [show r - (i + 1) = r - 1 - i by omega]
    _ = _ := Finset.prod_range_reflect (fun i => (s - i * b)!) r
  simp only [selbergFactorial, Finset.prod_mul_distrib, hreverse]

/-- Gcd over all admissible nonnegative parameters. -/
@[expose] public def selbergGcd (r s : ℕ) : ℕ :=
  (range (s / r + 1)).gcd (selbergFactorial r s)

public theorem b_le_index_mul (i b : ℕ) : b ≤ (i + 1) * b := by
  simpa using Nat.mul_le_mul_right b (show 1 ≤ i + 1 by omega)

public theorem quotient_ne_zero (i b : ℕ) : ((i + 1) * b)! / b ! ≠ 0 :=
  (Nat.div_pos
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_dvd_factorial (b_le_index_mul i b)))
    (Nat.factorial_pos _)).ne'

public theorem selbergFactorial_ne_zero (r s b : ℕ) : selbergFactorial r s b ≠ 0 := by
  rw [selbergFactorial_eq_paired]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    mul_ne_zero (quotient_ne_zero i b) (Nat.factorial_ne_zero _)

public theorem selbergGcd_ne_zero (r s : ℕ) : selbergGcd r s ≠ 0 := by
  unfold selbergGcd
  exact Finset.gcd_ne_zero_iff.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _),
    selbergFactorial_ne_zero r s 0⟩

private theorem selbergGcd_dvd {r s b : ℕ} (hr : 0 < r) (hb : r * b ≤ s) :
    selbergGcd r s ∣ selbergFactorial r s b := by
  unfold selbergGcd
  have hle : b ≤ s / r := (Nat.le_div_iff_mul_le hr).mpr (by simpa [mul_comm] using hb)
  exact Finset.gcd_dvd (Finset.mem_range.mpr (by omega))

public theorem tail_nonzero (H M : ℕ) : tailLCM H M ≠ 0 := by
  unfold tailLCM
  exact Finset.prod_ne_zero_iff.mpr fun k _ => Nat.lcmUpto_ne_zero (H / k)

private theorem sum_indicator {α : Type} (A B : Finset α) (P : α → Prop) [DecidablePred P]
    (h : A.filter P = B) : (∑ i ∈ A, if P i then 1 else 0) = B.card := by
  rw [← Finset.sum_filter P (fun _ => (1 : ℕ)), h]
  exact (Finset.card_eq_sum_ones B).symm

/-- Count each prime power in the tail by exchanging the order of the
sum over powers and the sum over the tail indices. -/
public theorem tail_factorization_sum {p H M K : ℕ} (hp : p.Prime) (hK : H / p ^ K ≤ M) :
    (tailLCM H M).factorization p = ∑ j ∈ Ico 1 K, (H / p ^ j - M) := by
  have hpow (j : ℕ) : 0 < p ^ j := pow_pos hp.pos _
  have hpowers {k j : ℕ} (hk : 0 < k) : p ^ j ≤ H / k ↔ k ≤ H / p ^ j := by
    rw [Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le (hpow j), mul_comm (p ^ j) k]
  have hlog (k : ℕ) (hk : k ∈ Ioc M H) :
      Nat.log p (H / k) = ∑ j ∈ Ico 1 K, if k ≤ H / p ^ j then 1 else 0 := by
    obtain ⟨hkM, hkH⟩ := Finset.mem_Ioc.mp hk
    have hkpos : 0 < k := by omega
    have hn : H / k ≠ 0 := (Nat.div_pos hkH hkpos).ne'
    have hlt : H / k < p ^ K := by
      apply lt_of_not_ge
      intro h
      exact (not_le_of_gt hkM) (((hpowers hkpos).mp h).trans hK)
    have hlog_lt := (Nat.log_lt_iff_lt_pow hp.one_lt hn).mpr hlt
    have hfilt : (Ico 1 K).filter (fun j => k ≤ H / p ^ j) =
        Ico 1 (Nat.log p (H / k) + 1) := by
      ext j
      rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico, ← hpowers hkpos,
        ← Nat.le_log_iff_pow_le hp.one_lt hn]
      omega
    simpa using (sum_indicator (Ico 1 K) _ (fun j => k ≤ H / p ^ j) hfilt).symm
  unfold tailLCM
  rw [Nat.factorization_prod_apply (fun k _ => Nat.lcmUpto_ne_zero (H / k))]
  calc
    _ = ∑ k ∈ Ioc M H, Nat.log p (H / k) :=
      Finset.sum_congr rfl fun k _ => Nat.factorization_lcmUpto _ hp
    _ = ∑ k ∈ Ioc M H, ∑ j ∈ Ico 1 K, if k ≤ H / p ^ j then 1 else 0 :=
      Finset.sum_congr rfl hlog
    _ = ∑ j ∈ Ico 1 K, ∑ k ∈ Ioc M H, if k ≤ H / p ^ j then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hfilt : (Ioc M H).filter (fun k => k ≤ H / p ^ j) = Ioc M (H / p ^ j) := by
        ext k
        rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
        have h := Nat.div_le_self H (p ^ j)
        omega
      simpa using sum_indicator (Ioc M H) _ (fun k => k ≤ H / p ^ j) hfilt

public theorem compact_tail_factorization {p r s K : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hK : s < p ^ K) :
    (tailLCM (r * s + (r - 1)) (r - 1)).factorization p =
      ∑ j ∈ Ico 1 K, ((r * s + (r - 1)) / p ^ j - (r - 1)) := by
  apply tail_factorization_sum hp
  have hmul := Nat.mul_le_mul_left r (show s + 1 ≤ p ^ K by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hlt : r * s + (r - 1) < r * p ^ K := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr hlt
  omega

private theorem factorial_factorization {p n K : ℕ} (hp : p.Prime) (hK : Nat.log p n < K) :
    (n !).factorization p = ∑ j ∈ Ico 1 K, n / p ^ j := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, padicValNat_factorial hK]

public theorem selberg_factorization {p r s b K : ℕ} (hp : p.Prime)
    (hb : r * b ≤ s) (hK : Nat.log p s < K) :
    (selbergFactorial r s b).factorization p = ∑ j ∈ Ico 1 K, floorSum (p ^ j) r s b := by
  rw [selbergFactorial_eq_paired]
  unfold floorSum
  rw [Nat.factorization_prod_apply (fun i _ =>
    mul_ne_zero (quotient_ne_zero i b) (Nat.factorial_ne_zero _))]
  refine Eq.trans (Finset.sum_congr rfl ?_) Finset.sum_comm
  intro i hi
  have hib : (i + 1) * b ≤ s :=
    (Nat.mul_le_mul_right b (show i + 1 ≤ r from Finset.mem_range.mp hi)).trans hb
  have hlog (n : ℕ) (hn : n ≤ s) : Nat.log p n < K :=
    (Nat.log_mono_right hn).trans_lt hK
  have hdvd : b ! ∣ ((i + 1) * b)! := Nat.factorial_dvd_factorial (b_le_index_mul i b)
  rw [Nat.factorization_mul (quotient_ne_zero i b) (Nat.factorial_ne_zero _), Finsupp.add_apply,
    Nat.factorization_div hdvd, Finsupp.tsub_apply, factorial_factorization hp (hlog _ hib),
    factorial_factorization hp (hlog _ ((b_le_index_mul i b).trans hib)),
    factorial_factorization hp (hlog _ (Nat.sub_le s (i * b)))]
  have hdiv (j : ℕ) : b / p ^ j ≤ (i + 1) * b / p ^ j :=
    Nat.div_le_div_right (b_le_index_mul i b)
  rw [← Finset.sum_tsub_distrib (Ico 1 K) (fun j _ => hdiv j), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold pairedFloor
  rw [add_comm, ← Nat.add_sub_assoc (hdiv j), add_comm]

private theorem tail_dvd_selberg {r s b : ℕ} (hr : 1 ≤ r) (hb : r * b ≤ s) :
    tailLCM (r * s + (r - 1)) (r - 1) ∣ selbergFactorial r s b := by
  apply (Nat.factorization_prime_le_iff_dvd (tail_nonzero _ _) (selbergFactorial_ne_zero _ _ _)).mp
  intro p hp
  rw [compact_tail_factorization hp hr (Nat.lt_pow_succ_log_self hp.one_lt s),
    selberg_factorization hp hb (Nat.lt_succ_self (Nat.log p s))]
  apply Finset.sum_le_sum
  intro j hj
  have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hpow : 2 ≤ p ^ j := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hjpos
  exact selberg_floor_lower hpow hr hb

public theorem gcd_factorization_le {p r s b : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hb : r * b ≤ s) :
    (selbergGcd r s).factorization p ≤ (selbergFactorial r s b).factorization p :=
  (Nat.factorization_prime_le_iff_dvd (selbergGcd_ne_zero _ _)
    (selbergFactorial_ne_zero _ _ _)).mpr (selbergGcd_dvd hr hb) p hp

private theorem floorSum_zero (q r s : ℕ) : floorSum q r s 0 = r * (s / q) := by
  simp [floorSum, pairedFloor]

/-- Legendre's sum contains the first-power contribution. The cutoff is
always at least two, including at factorial arguments below `p`. -/
private theorem first_floor_le_factorial {p : ℕ} (hp : p.Prime) (D : ℕ) :
    D / p ≤ (D !).factorization p := by
  let K := max 2 (Nat.log p D + 1)
  have hK : Nat.log p D < K := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  rw [factorial_factorization hp hK]
  have hmem : 1 ∈ Ico 1 K := Finset.mem_Ico.mpr
    ⟨le_rfl, lt_of_lt_of_le (by decide : 1 < 2) (le_max_left _ _)⟩
  simpa only [pow_one] using
    (Finset.single_le_sum (f := fun j => D / p ^ j) (fun j _ => Nat.zero_le _) hmem)

private theorem four_add_square_le {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    (n + 4) ^ 2 ≤ 16 * p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (n + 1 + 4) ^ 2 ≤ (n + 1 + 4) ^ 2 + (n ^ 2 + 6 * n + 7) := Nat.le_add_right _ _
      _ = 2 * (n + 4) ^ 2 := by ring
      _ ≤ 2 * (16 * p ^ n) := Nat.mul_le_mul_left 2 ih
      _ ≤ p * (16 * p ^ n) := Nat.mul_le_mul_right _ hp
      _ = 16 * p ^ (n + 1) := by rw [pow_succ]; ring

/-- If a small prime has `K` relevant powers, their number costs at most
`2 * r / p`. The case `p = 2, K = 3` uses `r ≥ 3`. -/
private theorem small_prime_power_bound {p r K : ℕ} (hp : 2 ≤ p) (hpr : p ≤ r)
    (hK : p ^ K < r ^ 2) : p * K ≤ 2 * r := by
  have hsq {x y : ℕ} : x ^ 2 ≤ y ^ 2 → x ≤ y :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp
  by_cases h1 : K ≤ 1
  · have hmul := Nat.mul_le_mul_left p h1
    rw [mul_one] at hmul
    omega
  by_cases h2 : K = 2
  · subst K
    have hle := hsq hK.le
    omega
  by_cases h3 : K = 3
  · subst K
    by_cases hp2 : p = 2
    · subst p
      have hr : 3 ≤ r := by
        by_contra h
        have hh : r ^ 2 ≤ 4 := Nat.pow_le_pow_left (show r ≤ 2 by omega) 2
        change 8 < r ^ 2 at hK
        omega
      omega
    · apply hsq
      calc
        (p * 3) ^ 2 = p ^ 2 * 9 := by ring
        _ ≤ p ^ 2 * (4 * p) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * p ^ 3 := by ring
        _ ≤ 4 * r ^ 2 := Nat.mul_le_mul_left _ hK.le
        _ = (2 * r) ^ 2 := by ring
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, K = n + 4 := ⟨K - 4, by omega⟩
  have hp2 : 4 ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  apply hsq
  calc
    (p * (n + 4)) ^ 2 = p ^ 2 * (n + 4) ^ 2 := by rw [mul_pow]
    _ ≤ p ^ 2 * (16 * p ^ n) := Nat.mul_le_mul_left _ (four_add_square_le hp n)
    _ = (4 * p ^ (n + 2)) * 4 := by rw [pow_add p n 2]; ring
    _ ≤ (4 * p ^ (n + 2)) * p ^ 2 := Nat.mul_le_mul_left _ hp2
    _ = 4 * p ^ (n + 4) := by rw [pow_add p n 2, pow_add p n 4]; ring
    _ ≤ 4 * r ^ 2 := Nat.mul_le_mul_left _ hK.le
    _ = (2 * r) ^ 2 := by ring

private theorem small_prime_upper {p r s : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hpr : p ≤ r) (hps : p ≤ s) (hs : s < r ^ 2) :
    (selbergFactorial r s 0).factorization p ≤
      (tailLCM (r * s + (r - 1)) (r - 1)).factorization p + ((2 * r ^ 2)!).factorization p := by
  let K := Nat.log p s
  have hs0 : s ≠ 0 := (hp.pos.trans_le hps).ne'
  have hK : p ^ K < r ^ 2 := (Nat.pow_log_le_self p hs0).trans_lt hs
  have hpK := small_prime_power_bound hp.two_le hpr hK
  have hr1 : 1 ≤ r := by omega
  have hbudget : K * (r - 1) ≤ 2 * r ^ 2 / p := by
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    calc
      K * (r - 1) * p = (p * K) * (r - 1) := by ring
      _ ≤ (2 * r) * (r - 1) := Nat.mul_le_mul_right _ hpK
      _ ≤ (2 * r) * r := Nat.mul_le_mul_left _ (Nat.sub_le r 1)
      _ = 2 * r ^ 2 := by ring
  have hbound : (selbergFactorial r s 0).factorization p ≤
      (tailLCM (r * s + (r - 1)) (r - 1)).factorization p + K * (r - 1) := by
    have hsK : s < p ^ (K + 1) := Nat.lt_pow_succ_log_self hp.one_lt s
    have hlog : Nat.log p s < K + 1 := Nat.lt_succ_self K
    rw [selberg_factorization hp (by simp : r * 0 ≤ s) hlog,
      compact_tail_factorization hp hr1 hsK]
    calc
      _ ≤ ∑ j ∈ Ico 1 (K + 1), (((r * s + (r - 1)) / p ^ j - (r - 1)) + (r - 1)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [floorSum_zero, head_div (pow_pos hp.pos j)]
        generalize (r * (s % p ^ j) + (r - 1)) / p ^ j = remainder
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  exact hbound.trans (Nat.add_le_add_left (hbudget.trans (first_floor_le_factorial hp _)) _)

private theorem large_prime_floor_sum {p r s b : ℕ} (hp : 0 < p) (hr : 1 ≤ r)
    (hb : 0 < b) (hbp : r * b < p) (hps : p ≤ s) :
    floorSum p r s b = r * (s / p - 1) + 1 + min (r - 1) ((s % p) / b) := by
  have hbsmall : b < p := (show b ≤ r * b by simpa using Nat.mul_le_mul_right b hr).trans_lt hbp
  have hk : 0 < s / p := Nat.div_pos hps hp
  have hterm (i : ℕ) (hi : i ∈ range r) :
      pairedFloor p s b i = (s / p - 1) + (if i * b ≤ s % p then 1 else 0) := by
    have hi' : i + 1 ≤ r := Finset.mem_range.mp hi
    have hfirst : (i + 1) * b < p := (Nat.mul_le_mul_right b hi').trans_lt hbp
    have hindex : i * b < p :=
      (Nat.mul_le_mul_right b (show i ≤ r by omega)).trans_lt hbp
    have hsum : i * b + (s - i * b) = s := Nat.add_sub_of_le (hindex.le.trans hps)
    have hcarry := two_floor_carry (i * b) (s - i * b) hp
    rw [hsum, Nat.div_eq_of_lt hindex, Nat.mod_eq_of_lt hindex, zero_add] at hcarry
    unfold pairedFloor
    rw [Nat.div_eq_of_lt hfirst, Nat.div_eq_of_lt hbsmall, zero_add, Nat.sub_zero]
    by_cases hgood : i * b ≤ s % p
    · rw [ite_eq_left hgood] at hcarry ⊢
      omega
    · rw [ite_eq_right hgood] at hcarry ⊢
      omega
  have hfilt : (range r).filter (fun i => i * b ≤ s % p) =
      range (min (r - 1) ((s % p) / b) + 1) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← Nat.le_div_iff_mul_le hb]
    rcases le_total (r - 1) ((s % p) / b) with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hcount : (∑ i ∈ range r, if i * b ≤ s % p then 1 else 0) =
      min (r - 1) ((s % p) / b) + 1 := by
    simpa using sum_indicator (range r) _ (fun i => i * b ≤ s % p) hfilt
  unfold floorSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hcount]
  simp [add_assoc, add_comm, add_left_comm]

private theorem large_prime_upper {p r s : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hrp : r < p) (hps : p ≤ s) (hs : s < r ^ 2) :
    (selbergFactorial r s (p / r)).factorization p ≤
      (tailLCM (r * s + (r - 1)) (r - 1)).factorization p + ((2 * r ^ 2)!).factorization p := by
  let b := p / r
  let h := p % r
  have hr1 : 1 ≤ r := by omega
  have hrpos : 0 < r := by omega
  have hb : 0 < b := Nat.div_pos hrp.le hrpos
  have hpdiv : r * b + h = p := Nat.div_add_mod p r
  have hh : h < r := Nat.mod_lt p hrpos
  have hpos : 0 < h := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hdvd : r ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
    exact (Nat.ne_of_lt hrp) ((Nat.dvd_prime_two_le hp hr).mp hdvd)
  have hbp : r * b < p := by omega
  have hspp : s < p ^ 2 := hs.trans_le (Nat.pow_le_pow_left hrp.le 2)
  have hs0 : s ≠ 0 := (hp.pos.trans_le hps).ne'
  have hlog : Nat.log p s < 2 := (Nat.log_lt_iff_lt_pow hp.one_lt hs0).mpr hspp
  have hIco : Ico (1 : ℕ) 2 = {1} := Nat.Ico_succ_singleton 1
  change (selbergFactorial r s b).factorization p ≤ _
  rw [selberg_factorization hp (hbp.le.trans hps) hlog,
    compact_tail_factorization hp hr1 hspp]
  simp only [hIco, Finset.sum_singleton, pow_one]
  rw [large_prime_floor_sum hp.pos hr1 hb hbp hps]
  let v := s % p
  let B := (r * v + (r - 1)) / p
  let m := min (r - 1) (v / b)
  let D := 2 * r ^ 2
  change r * (s / p - 1) + 1 + m ≤
    (r * s + (r - 1)) / p - (r - 1) + (D !).factorization p
  have hm₁ : m ≤ r - 1 := min_le_left _ _
  have hm₂ : m * b ≤ v := (Nat.le_div_iff_mul_le hb).mp (min_le_right _ _)
  have hmul : p * m ≤ r * v + (r - 1) * (r - 1) := calc
    p * m = (r * b + h) * m := by rw [hpdiv]
    _ = r * (m * b) + h * m := by ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hm₂) (Nat.mul_le_mul (by omega) hm₁)
  have hrem : p * B + (r * v + (r - 1)) % p = r * v + (r - 1) := Nat.div_add_mod _ _
  have hrem_lt := Nat.mod_lt (r * v + (r - 1)) hp.pos
  have hsq : (r - 1) * (r - 1) ≤ r ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hprod : m * p ≤ B * p + D := by
    rw [mul_comm m p, mul_comm B p]
    dsimp [D]
    omega
  have hm : m ≤ B + D / p := by
    by_cases hle : m ≤ B
    · exact hle.trans (Nat.le_add_right _ _)
    · have hsplit := Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))
      have heq : m * p = B * p + (m - B) * p := calc
        m * p = (B + (m - B)) * p := congrArg (· * p) hsplit.symm
        _ = _ := by rw [Nat.add_mul]
      have hd := (Nat.le_div_iff_mul_le hp.pos).mpr (show (m - B) * p ≤ D by omega)
      exact hsplit.symm ▸ Nat.add_le_add_left hd B
  have hk : 1 ≤ s / p := Nat.div_pos hps hp.pos
  have hrk : r * (s / p) = r * (s / p - 1) + r := calc
    r * (s / p) = r * ((s / p - 1) + 1) := by rw [Nat.sub_add_cancel hk]
    _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have hhead : (r * s + (r - 1)) / p = r * (s / p) + B := head_div hp.pos
  have hD := first_floor_le_factorial hp D
  omega

/-- Exact elementary compression of the tail LCM by the compact factorial
gcd. The excess divides the factorial of `2 * r^2`. -/
public theorem compact_factorial_gcd (r s : ℕ) (hr : 2 ≤ r) (hs : s < r ^ 2) :
    tailLCM (r * s + r - 1) (r - 1) ∣ selbergGcd r s ∧
      selbergGcd r s ∣ tailLCM (r * s + r - 1) (r - 1) * (2 * r ^ 2)! := by
  have hr1 : 1 ≤ r := by omega
  have hrpos : 0 < r := by omega
  rw [Nat.add_sub_assoc hr1]
  constructor
  · unfold selbergGcd
    apply Finset.dvd_gcd
    intro b hb
    have hle : b ≤ s / r := by have := Finset.mem_range.mp hb; omega
    have hmul := (Nat.le_div_iff_mul_le hrpos).mp hle
    exact tail_dvd_selberg hr1 (by simpa [mul_comm] using hmul)
  · have htail : tailLCM (r * s + (r - 1)) (r - 1) ≠ 0 := tail_nonzero _ _
    have hfact : (2 * r ^ 2)! ≠ 0 := Nat.factorial_ne_zero _
    apply (Nat.factorization_prime_le_iff_dvd (selbergGcd_ne_zero r s) (mul_ne_zero htail hfact)).mp
    intro p hp
    rw [Nat.factorization_mul htail hfact, Finsupp.add_apply]
    by_cases hps : p ≤ s
    · by_cases hpr : p ≤ r
      · exact (gcd_factorization_le hp hrpos (by simp : r * 0 ≤ s)).trans
          (small_prime_upper hp hr hpr hps hs)
      · have hbp : r * (p / r) ≤ s := by
          have hdiv := Nat.div_add_mod p r
          omega
        exact (gcd_factorization_le hp hrpos hbp).trans (large_prime_upper hp hr (by omega) hps hs)
    · have hzero : (selbergFactorial r s 0).factorization p = 0 := by
        have hlog : Nat.log p s < 1 := by
          simpa only [Nat.log_of_lt (show s < p by omega)] using (by decide : (0 : ℕ) < 1)
        rw [selberg_factorization hp (by simp : r * 0 ≤ s) hlog, Finset.Ico_self, Finset.sum_empty]
      have hg := gcd_factorization_le hp hrpos (by simp : r * 0 ≤ s)
      omega

end D5.S3.Arith.FactorialRatio.CompactFactorialGcd
