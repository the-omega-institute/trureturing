/- GID: D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Data.Nat.Prime.Nth, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim; result=D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.result; claim=D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.claim
   digest: The n = 6298 certificate refutes Cloitre's A072872 prime-index upper bound. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.CloitrePowerMinusIndexPrimeBoundRefutation

/-!
OEIS A072872 defines `a(n)` as "the smallest positive number k such that n
divides 2^k - k." Benoit Cloitre's comment of 2002-07-28 conjectures:
"If n is a power of 2, a(n) = n. Conjecture : if n > 47, a(n) < prime(n)."

The infimum convention below returns zero when the defining set is empty; no
general existence assertion is made here. The OEIS offset is one, so
`prime(n)` is represented by `Nat.nth Nat.Prime (n - 1)`.

At `n = 6298`, a verified modular recurrence checks every positive exponent
below 77742 and verifies the endpoint, while an independent bounded trial
division checker certifies that exactly 6297 primes precede the prime 62753.
Thus `a(6298) = 77742 > 62753 = prime(6298)`.
-/

/-- The literal A072872 sequence definition. If the defining set is empty,
the natural-number `sInf` convention gives zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ n ∣ 2 ^ k - k}

/-- Cloitre's literal prime-index upper-bound conjecture from A072872. -/
def claim : Prop :=
  ∀ n : ℕ, 47 < n → a n < Nat.nth Nat.Prime (n - 1)

private def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range 249).all fun i => decide (i + 2 < n → ¬(i + 2) ∣ n)

private def trialCount (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 =>
      trialCount start len + if trialPrime (start + len) then 1 else 0

private theorem trialPrime_iff_prime {n : ℕ} (hn : n < 62753) :
    trialPrime n = true ↔ Nat.Prime n := by
  have hshape :
      trialPrime n = true ↔
        2 ≤ n ∧ ∀ i, i < 249 → i + 2 < n → ¬(i + 2) ∣ n := by
    simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
  rw [hshape]
  constructor
  · rintro ⟨hn2, htrial⟩
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hn2, fun m hm hmsqrt => ?_⟩
    have hm250 : m ≤ 250 := by
      have hsqrt : Nat.sqrt n < 251 := Nat.sqrt_lt.mpr (hn.trans (by decide))
      omega
    have hindex : m - 2 < 249 := by omega
    have hm_lt : m < n := hmsqrt.trans_lt (Nat.sqrt_lt_self hn2)
    have hres := htrial (m - 2) hindex (by omega)
    simpa only [Nat.sub_add_cancel hm] using hres
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro i _ hdlt hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · have hilower : 2 ≤ i + 2 := by omega
      exact (not_lt_of_ge hilower) (h ▸ by decide)
    · exact (ne_of_lt hdlt) h

private theorem count_add_trialCount (start len : ℕ)
    (hbound : start + len ≤ 62753) :
    Nat.count Nat.Prime (start + len) =
      Nat.count Nat.Prime start + trialCount start len := by
  induction len with
  | zero => simp [trialCount]
  | succ len ih =>
      rw [Nat.add_succ, Nat.count_succ, trialCount, ih (by omega)]
      by_cases hp : Nat.Prime (start + len)
      · have ht : trialPrime (start + len) = true :=
          (trialPrime_iff_prime (by omega)).2 hp
        simp [hp, ht, Nat.add_assoc]
      · have ht : trialPrime (start + len) ≠ true := fun h =>
          hp ((trialPrime_iff_prime (by omega)).1 h)
        simp [hp, ht]

private theorem pc00 : trialCount 0 1000 = 168 := by set_option maxRecDepth 10000 in decide
private theorem pc01 : trialCount 1000 1000 = 135 := by set_option maxRecDepth 10000 in decide
private theorem pc02 : trialCount 2000 1000 = 127 := by set_option maxRecDepth 10000 in decide
private theorem pc03 : trialCount 3000 1000 = 120 := by set_option maxRecDepth 10000 in decide
private theorem pc04 : trialCount 4000 1000 = 119 := by set_option maxRecDepth 10000 in decide
private theorem pc05 : trialCount 5000 1000 = 114 := by set_option maxRecDepth 10000 in decide
private theorem pc06 : trialCount 6000 1000 = 117 := by set_option maxRecDepth 10000 in decide
private theorem pc07 : trialCount 7000 1000 = 107 := by set_option maxRecDepth 10000 in decide
private theorem pc08 : trialCount 8000 1000 = 110 := by set_option maxRecDepth 10000 in decide
private theorem pc09 : trialCount 9000 1000 = 112 := by set_option maxRecDepth 10000 in decide
private theorem pc10 : trialCount 10000 1000 = 106 := by set_option maxRecDepth 10000 in decide
private theorem pc11 : trialCount 11000 1000 = 103 := by set_option maxRecDepth 10000 in decide
private theorem pc12 : trialCount 12000 1000 = 109 := by set_option maxRecDepth 10000 in decide
private theorem pc13 : trialCount 13000 1000 = 105 := by set_option maxRecDepth 10000 in decide
private theorem pc14 : trialCount 14000 1000 = 102 := by set_option maxRecDepth 10000 in decide
private theorem pc15 : trialCount 15000 1000 = 108 := by set_option maxRecDepth 10000 in decide
private theorem pc16 : trialCount 16000 1000 = 98 := by set_option maxRecDepth 10000 in decide
private theorem pc17 : trialCount 17000 1000 = 104 := by set_option maxRecDepth 10000 in decide
private theorem pc18 : trialCount 18000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc19 : trialCount 19000 1000 = 104 := by set_option maxRecDepth 10000 in decide
private theorem pc20 : trialCount 20000 1000 = 98 := by set_option maxRecDepth 10000 in decide
private theorem pc21 : trialCount 21000 1000 = 104 := by set_option maxRecDepth 10000 in decide
private theorem pc22 : trialCount 22000 1000 = 100 := by set_option maxRecDepth 10000 in decide
private theorem pc23 : trialCount 23000 1000 = 104 := by set_option maxRecDepth 10000 in decide
private theorem pc24 : trialCount 24000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc25 : trialCount 25000 1000 = 98 := by set_option maxRecDepth 10000 in decide
private theorem pc26 : trialCount 26000 1000 = 101 := by set_option maxRecDepth 10000 in decide
private theorem pc27 : trialCount 27000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc28 : trialCount 28000 1000 = 98 := by set_option maxRecDepth 10000 in decide
private theorem pc29 : trialCount 29000 1000 = 92 := by set_option maxRecDepth 10000 in decide
private theorem pc30 : trialCount 30000 1000 = 95 := by set_option maxRecDepth 10000 in decide
private theorem pc31 : trialCount 31000 1000 = 92 := by set_option maxRecDepth 10000 in decide
private theorem pc32 : trialCount 32000 1000 = 106 := by set_option maxRecDepth 10000 in decide
private theorem pc33 : trialCount 33000 1000 = 100 := by set_option maxRecDepth 10000 in decide
private theorem pc34 : trialCount 34000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc35 : trialCount 35000 1000 = 92 := by set_option maxRecDepth 10000 in decide
private theorem pc36 : trialCount 36000 1000 = 99 := by set_option maxRecDepth 10000 in decide
private theorem pc37 : trialCount 37000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc38 : trialCount 38000 1000 = 90 := by set_option maxRecDepth 10000 in decide
private theorem pc39 : trialCount 39000 1000 = 96 := by set_option maxRecDepth 10000 in decide
private theorem pc40 : trialCount 40000 1000 = 88 := by set_option maxRecDepth 10000 in decide
private theorem pc41 : trialCount 41000 1000 = 101 := by set_option maxRecDepth 10000 in decide
private theorem pc42 : trialCount 42000 1000 = 102 := by set_option maxRecDepth 10000 in decide
private theorem pc43 : trialCount 43000 1000 = 85 := by set_option maxRecDepth 10000 in decide
private theorem pc44 : trialCount 44000 1000 = 96 := by set_option maxRecDepth 10000 in decide
private theorem pc45 : trialCount 45000 1000 = 86 := by set_option maxRecDepth 10000 in decide
private theorem pc46 : trialCount 46000 1000 = 90 := by set_option maxRecDepth 10000 in decide
private theorem pc47 : trialCount 47000 1000 = 95 := by set_option maxRecDepth 10000 in decide
private theorem pc48 : trialCount 48000 1000 = 89 := by set_option maxRecDepth 10000 in decide
private theorem pc49 : trialCount 49000 1000 = 98 := by set_option maxRecDepth 10000 in decide
private theorem pc50 : trialCount 50000 1000 = 89 := by set_option maxRecDepth 10000 in decide
private theorem pc51 : trialCount 51000 1000 = 97 := by set_option maxRecDepth 10000 in decide
private theorem pc52 : trialCount 52000 1000 = 89 := by set_option maxRecDepth 10000 in decide
private theorem pc53 : trialCount 53000 1000 = 92 := by set_option maxRecDepth 10000 in decide
private theorem pc54 : trialCount 54000 1000 = 90 := by set_option maxRecDepth 10000 in decide
private theorem pc55 : trialCount 55000 1000 = 93 := by set_option maxRecDepth 10000 in decide
private theorem pc56 : trialCount 56000 1000 = 99 := by set_option maxRecDepth 10000 in decide
private theorem pc57 : trialCount 57000 1000 = 91 := by set_option maxRecDepth 10000 in decide
private theorem pc58 : trialCount 58000 1000 = 90 := by set_option maxRecDepth 10000 in decide
private theorem pc59 : trialCount 59000 1000 = 94 := by set_option maxRecDepth 10000 in decide
private theorem pc60 : trialCount 60000 1000 = 88 := by set_option maxRecDepth 10000 in decide
private theorem pc61 : trialCount 61000 1000 = 87 := by set_option maxRecDepth 10000 in decide
private theorem pc62 : trialCount 62000 753 = 65 := by set_option maxRecDepth 10000 in decide

private theorem primeCountCertificate : Nat.count Nat.Prime 62753 = 6297 := by
  have h01 : Nat.count Nat.Prime 1000 = 168 := by simpa [pc00] using count_add_trialCount 0 1000 (by decide)
  have h02 : Nat.count Nat.Prime 2000 = 303 := by simpa [h01, pc01] using count_add_trialCount 1000 1000 (by decide)
  have h03 : Nat.count Nat.Prime 3000 = 430 := by simpa [h02, pc02] using count_add_trialCount 2000 1000 (by decide)
  have h04 : Nat.count Nat.Prime 4000 = 550 := by simpa [h03, pc03] using count_add_trialCount 3000 1000 (by decide)
  have h05 : Nat.count Nat.Prime 5000 = 669 := by simpa [h04, pc04] using count_add_trialCount 4000 1000 (by decide)
  have h06 : Nat.count Nat.Prime 6000 = 783 := by simpa [h05, pc05] using count_add_trialCount 5000 1000 (by decide)
  have h07 : Nat.count Nat.Prime 7000 = 900 := by simpa [h06, pc06] using count_add_trialCount 6000 1000 (by decide)
  have h08 : Nat.count Nat.Prime 8000 = 1007 := by simpa [h07, pc07] using count_add_trialCount 7000 1000 (by decide)
  have h09 : Nat.count Nat.Prime 9000 = 1117 := by simpa [h08, pc08] using count_add_trialCount 8000 1000 (by decide)
  have h10 : Nat.count Nat.Prime 10000 = 1229 := by simpa [h09, pc09] using count_add_trialCount 9000 1000 (by decide)
  have h11 : Nat.count Nat.Prime 11000 = 1335 := by simpa [h10, pc10] using count_add_trialCount 10000 1000 (by decide)
  have h12 : Nat.count Nat.Prime 12000 = 1438 := by simpa [h11, pc11] using count_add_trialCount 11000 1000 (by decide)
  have h13 : Nat.count Nat.Prime 13000 = 1547 := by simpa [h12, pc12] using count_add_trialCount 12000 1000 (by decide)
  have h14 : Nat.count Nat.Prime 14000 = 1652 := by simpa [h13, pc13] using count_add_trialCount 13000 1000 (by decide)
  have h15 : Nat.count Nat.Prime 15000 = 1754 := by simpa [h14, pc14] using count_add_trialCount 14000 1000 (by decide)
  have h16 : Nat.count Nat.Prime 16000 = 1862 := by simpa [h15, pc15] using count_add_trialCount 15000 1000 (by decide)
  have h17 : Nat.count Nat.Prime 17000 = 1960 := by simpa [h16, pc16] using count_add_trialCount 16000 1000 (by decide)
  have h18 : Nat.count Nat.Prime 18000 = 2064 := by simpa [h17, pc17] using count_add_trialCount 17000 1000 (by decide)
  have h19 : Nat.count Nat.Prime 19000 = 2158 := by simpa [h18, pc18] using count_add_trialCount 18000 1000 (by decide)
  have h20 : Nat.count Nat.Prime 20000 = 2262 := by simpa [h19, pc19] using count_add_trialCount 19000 1000 (by decide)
  have h21 : Nat.count Nat.Prime 21000 = 2360 := by simpa [h20, pc20] using count_add_trialCount 20000 1000 (by decide)
  have h22 : Nat.count Nat.Prime 22000 = 2464 := by simpa [h21, pc21] using count_add_trialCount 21000 1000 (by decide)
  have h23 : Nat.count Nat.Prime 23000 = 2564 := by simpa [h22, pc22] using count_add_trialCount 22000 1000 (by decide)
  have h24 : Nat.count Nat.Prime 24000 = 2668 := by simpa [h23, pc23] using count_add_trialCount 23000 1000 (by decide)
  have h25 : Nat.count Nat.Prime 25000 = 2762 := by simpa [h24, pc24] using count_add_trialCount 24000 1000 (by decide)
  have h26 : Nat.count Nat.Prime 26000 = 2860 := by simpa [h25, pc25] using count_add_trialCount 25000 1000 (by decide)
  have h27 : Nat.count Nat.Prime 27000 = 2961 := by simpa [h26, pc26] using count_add_trialCount 26000 1000 (by decide)
  have h28 : Nat.count Nat.Prime 28000 = 3055 := by simpa [h27, pc27] using count_add_trialCount 27000 1000 (by decide)
  have h29 : Nat.count Nat.Prime 29000 = 3153 := by simpa [h28, pc28] using count_add_trialCount 28000 1000 (by decide)
  have h30 : Nat.count Nat.Prime 30000 = 3245 := by simpa [h29, pc29] using count_add_trialCount 29000 1000 (by decide)
  have h31 : Nat.count Nat.Prime 31000 = 3340 := by simpa [h30, pc30] using count_add_trialCount 30000 1000 (by decide)
  have h32 : Nat.count Nat.Prime 32000 = 3432 := by simpa [h31, pc31] using count_add_trialCount 31000 1000 (by decide)
  have h33 : Nat.count Nat.Prime 33000 = 3538 := by simpa [h32, pc32] using count_add_trialCount 32000 1000 (by decide)
  have h34 : Nat.count Nat.Prime 34000 = 3638 := by simpa [h33, pc33] using count_add_trialCount 33000 1000 (by decide)
  have h35 : Nat.count Nat.Prime 35000 = 3732 := by simpa [h34, pc34] using count_add_trialCount 34000 1000 (by decide)
  have h36 : Nat.count Nat.Prime 36000 = 3824 := by simpa [h35, pc35] using count_add_trialCount 35000 1000 (by decide)
  have h37 : Nat.count Nat.Prime 37000 = 3923 := by simpa [h36, pc36] using count_add_trialCount 36000 1000 (by decide)
  have h38 : Nat.count Nat.Prime 38000 = 4017 := by simpa [h37, pc37] using count_add_trialCount 37000 1000 (by decide)
  have h39 : Nat.count Nat.Prime 39000 = 4107 := by simpa [h38, pc38] using count_add_trialCount 38000 1000 (by decide)
  have h40 : Nat.count Nat.Prime 40000 = 4203 := by simpa [h39, pc39] using count_add_trialCount 39000 1000 (by decide)
  have h41 : Nat.count Nat.Prime 41000 = 4291 := by simpa [h40, pc40] using count_add_trialCount 40000 1000 (by decide)
  have h42 : Nat.count Nat.Prime 42000 = 4392 := by simpa [h41, pc41] using count_add_trialCount 41000 1000 (by decide)
  have h43 : Nat.count Nat.Prime 43000 = 4494 := by simpa [h42, pc42] using count_add_trialCount 42000 1000 (by decide)
  have h44 : Nat.count Nat.Prime 44000 = 4579 := by simpa [h43, pc43] using count_add_trialCount 43000 1000 (by decide)
  have h45 : Nat.count Nat.Prime 45000 = 4675 := by simpa [h44, pc44] using count_add_trialCount 44000 1000 (by decide)
  have h46 : Nat.count Nat.Prime 46000 = 4761 := by simpa [h45, pc45] using count_add_trialCount 45000 1000 (by decide)
  have h47 : Nat.count Nat.Prime 47000 = 4851 := by simpa [h46, pc46] using count_add_trialCount 46000 1000 (by decide)
  have h48 : Nat.count Nat.Prime 48000 = 4946 := by simpa [h47, pc47] using count_add_trialCount 47000 1000 (by decide)
  have h49 : Nat.count Nat.Prime 49000 = 5035 := by simpa [h48, pc48] using count_add_trialCount 48000 1000 (by decide)
  have h50 : Nat.count Nat.Prime 50000 = 5133 := by simpa [h49, pc49] using count_add_trialCount 49000 1000 (by decide)
  have h51 : Nat.count Nat.Prime 51000 = 5222 := by simpa [h50, pc50] using count_add_trialCount 50000 1000 (by decide)
  have h52 : Nat.count Nat.Prime 52000 = 5319 := by simpa [h51, pc51] using count_add_trialCount 51000 1000 (by decide)
  have h53 : Nat.count Nat.Prime 53000 = 5408 := by simpa [h52, pc52] using count_add_trialCount 52000 1000 (by decide)
  have h54 : Nat.count Nat.Prime 54000 = 5500 := by simpa [h53, pc53] using count_add_trialCount 53000 1000 (by decide)
  have h55 : Nat.count Nat.Prime 55000 = 5590 := by simpa [h54, pc54] using count_add_trialCount 54000 1000 (by decide)
  have h56 : Nat.count Nat.Prime 56000 = 5683 := by simpa [h55, pc55] using count_add_trialCount 55000 1000 (by decide)
  have h57 : Nat.count Nat.Prime 57000 = 5782 := by simpa [h56, pc56] using count_add_trialCount 56000 1000 (by decide)
  have h58 : Nat.count Nat.Prime 58000 = 5873 := by simpa [h57, pc57] using count_add_trialCount 57000 1000 (by decide)
  have h59 : Nat.count Nat.Prime 59000 = 5963 := by simpa [h58, pc58] using count_add_trialCount 58000 1000 (by decide)
  have h60 : Nat.count Nat.Prime 60000 = 6057 := by simpa [h59, pc59] using count_add_trialCount 59000 1000 (by decide)
  have h61 : Nat.count Nat.Prime 61000 = 6145 := by simpa [h60, pc60] using count_add_trialCount 60000 1000 (by decide)
  have h62 : Nat.count Nat.Prime 62000 = 6232 := by simpa [h61, pc61] using count_add_trialCount 61000 1000 (by decide)
  simpa [h62, pc62] using count_add_trialCount 62000 753 (by decide)

private def advance : ℕ → ℕ → ℕ
  | r, 0 => r
  | r, len + 1 => advance ((2 * r) % 6298) len

private def scan : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => true
  | k, r, len + 1 =>
      decide (r ≠ k % 6298) && scan (k + 1) ((2 * r) % 6298) len

private theorem advance_add (r m n : ℕ) :
    advance r (m + n) = advance (advance r m) n := by
  induction m generalizing r with
  | zero => simp [advance]
  | succ m ih => simpa [advance, Nat.succ_add] using ih ((2 * r) % 6298)

private theorem scan_add (k r m n : ℕ) :
    scan k r (m + n) =
      (scan k r m && scan (k + m) (advance r m) n) := by
  induction m generalizing k r with
  | zero => simp [scan, advance]
  | succ m ih =>
      simp only [Nat.succ_add, scan]
      rw [ih]
      simp [advance, Bool.and_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem scan_sound : ∀ {len k r : ℕ},
    scan k r len = true →
    r = 2 ^ k % 6298 →
    ∀ i, k ≤ i → i < k + len → ¬6298 ∣ 2 ^ i - i := by
  intro len
  induction len with
  | zero =>
      intro k r _ _ i _ hi
      omega
  | succ len ih =>
      intro k r hscan hr i hki hi hdiv
      rw [scan, Bool.and_eq_true, decide_eq_true_eq] at hscan
      by_cases hik : i = k
      · subst i
        apply hscan.1
        rw [hr]
        have hmod : k ≡ 2 ^ k [MOD 6298] :=
          (Nat.modEq_iff_dvd' k.lt_two_pow_self.le).2 hdiv
        exact hmod.symm
      · apply ih hscan.2 ?_ i (by omega) (by omega) hdiv
        simp only [hr, Nat.pow_succ]
        simp only [Nat.mul_mod, Nat.mod_mod,
          Nat.mod_eq_of_lt (by decide : 2 < 6298)]
        rw [Nat.mul_comm]

private theorem sc00 : scan 1 2 5000 = true ∧ advance 2 5000 = 4784 := by set_option maxRecDepth 30000 in decide
private theorem sc01 : scan 5001 4784 5000 = true ∧ advance 4784 5000 = 6160 := by set_option maxRecDepth 30000 in decide
private theorem sc02 : scan 10001 6160 5000 = true ∧ advance 6160 5000 = 3698 := by set_option maxRecDepth 30000 in decide
private theorem sc03 : scan 15001 3698 5000 = true ∧ advance 3698 5000 = 3224 := by set_option maxRecDepth 30000 in decide
private theorem sc04 : scan 20001 3224 5000 = true ∧ advance 3224 5000 = 3056 := by set_option maxRecDepth 30000 in decide
private theorem sc05 : scan 25001 3056 5000 = true ∧ advance 3056 5000 = 4272 := by set_option maxRecDepth 30000 in decide
private theorem sc06 : scan 30001 4272 5000 = true ∧ advance 4272 5000 = 3268 := by set_option maxRecDepth 30000 in decide
private theorem sc07 : scan 35001 3268 5000 = true ∧ advance 3268 5000 = 1238 := by set_option maxRecDepth 30000 in decide
private theorem sc08 : scan 40001 1238 5000 = true ∧ advance 1238 5000 = 1236 := by set_option maxRecDepth 30000 in decide
private theorem sc09 : scan 45001 1236 5000 = true ∧ advance 1236 5000 = 2750 := by set_option maxRecDepth 30000 in decide
private theorem sc10 : scan 50001 2750 5000 = true ∧ advance 2750 5000 = 2888 := by set_option maxRecDepth 30000 in decide
private theorem sc11 : scan 55001 2888 5000 = true ∧ advance 2888 5000 = 5488 := by set_option maxRecDepth 30000 in decide
private theorem sc12 : scan 60001 5488 5000 = true ∧ advance 5488 5000 = 2264 := by set_option maxRecDepth 30000 in decide
private theorem sc13 : scan 65001 2264 5000 = true ∧ advance 2264 5000 = 5506 := by set_option maxRecDepth 30000 in decide
private theorem sc14 : scan 70001 5506 5000 = true ∧ advance 5506 5000 = 1234 := by set_option maxRecDepth 30000 in decide
private theorem sc15 : scan 75001 1234 2741 = true ∧ advance 1234 2741 = 2166 := by set_option maxRecDepth 20000 in decide

private theorem fullScan : scan 1 2 77741 = true := by
  have prepend {k r m n r' : ℕ}
      (hchunk : scan k r m = true ∧ advance r m = r')
      (htail : scan (k + m) r' n = true) :
      scan k r (m + n) = true := by
    rw [scan_add, hchunk.1, hchunk.2, htail]
    rfl
  refine prepend (n := 72741) sc00 ?_
  refine prepend (n := 67741) sc01 ?_
  refine prepend (n := 62741) sc02 ?_
  refine prepend (n := 57741) sc03 ?_
  refine prepend (n := 52741) sc04 ?_
  refine prepend (n := 47741) sc05 ?_
  refine prepend (n := 42741) sc06 ?_
  refine prepend (n := 37741) sc07 ?_
  refine prepend (n := 32741) sc08 ?_
  refine prepend (n := 27741) sc09 ?_
  refine prepend (n := 22741) sc10 ?_
  refine prepend (n := 17741) sc11 ?_
  refine prepend (n := 12741) sc12 ?_
  refine prepend (n := 7741) sc13 ?_
  refine prepend (n := 2741) sc14 ?_
  exact sc15.1

private theorem endpointMember : 6298 ∣ 2 ^ 77742 - 77742 := by
  set_option exponentiation.threshold 100000 in
  set_option maxRecDepth 1000000 in
  decide

private theorem aCertificate : a 6298 = 77742 := by
  have hmember : 0 < 77742 ∧ 6298 ∣ 2 ^ 77742 - 77742 :=
    ⟨by decide, endpointMember⟩
  unfold a
  apply le_antisymm (Nat.sInf_le hmember)
  by_contra hnot
  have hslt : sInf {k : ℕ | 0 < k ∧ 6298 ∣ 2 ^ k - k} < 77742 := by omega
  have hsMem := Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ 6298 ∣ 2 ^ k - k})
    ⟨77742, hmember⟩
  have hsOne : 1 ≤ sInf {k : ℕ | 0 < k ∧ 6298 ∣ 2 ^ k - k} := hsMem.1
  have hsUpper : sInf {k : ℕ | 0 < k ∧ 6298 ∣ 2 ^ k - k} < 1 + 77741 := by
    simpa using hslt
  exact (scan_sound fullScan (by decide) _ hsOne hsUpper) hsMem.2

private theorem primeIndexCertificate : Nat.nth Nat.Prime 6297 = 62753 := by
  have hp : Nat.Prime 62753 := by norm_num
  simpa [primeCountCertificate] using Nat.nth_count hp

/-- The certified counterexample `n = 6298` refutes Cloitre's conjecture. -/
theorem result : ¬ claim := by
  intro hclaim
  have hbound := hclaim 6298 (by decide)
  rw [aCertificate, primeIndexCertificate] at hbound
  omega

#print axioms a
#print axioms claim
#print axioms result

end D5.S3.Arith.Congruence.CloitrePowerMinusIndexPrimeBoundRefutation
