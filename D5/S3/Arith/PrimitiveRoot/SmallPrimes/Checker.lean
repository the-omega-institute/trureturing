/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Checker
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SmallPrimes/Checker
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0000.checked0000
   digest: Sound modular-order certificates with complete consecutive odd coverage. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.SplitIfs

/-! Mathematical soundness for the lightweight literal-certificate kernel. -/

set_option autoImplicit false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem powLoop_cast (k b e m r : ℕ) :
    (powLoop k b e m r : ZMod m) = (r : ZMod m) * (b : ZMod m) ^ e := by
  induction k generalizing b e r with
  | zero => simp [powLoop, ZMod.natCast_mod]
  | succ k ih =>
    simp only [powLoop]
    split
    next he =>
      have he : e = 0 := by simpa using he
      subst e
      simp [ZMod.natCast_mod]
    next he =>
      rw [ih]
      split
      next ho =>
        have ho : e % 2 = 1 := by simpa using ho
        have heq : e = e / 2 * 2 + 1 := by omega
        simp only [ZMod.natCast_mod, Nat.cast_mul]
        conv_rhs => rw [heq]
        rw [pow_add, pow_mul, pow_two, pow_one]
        simp only [mul_pow, mul_assoc, mul_comm, mul_left_comm]
      next ho =>
        have ho : e % 2 = 0 := by
          have : e % 2 ≠ 1 := by simpa using ho
          omega
        have heq : e = e / 2 * 2 := by omega
        simp only [ZMod.natCast_mod, Nat.cast_mul]
        conv_rhs => rw [heq]
        rw [pow_mul, pow_two, mul_pow]

private theorem powLoop_lt (k b e m r : ℕ) (hm : 0 < m) :
    powLoop k b e m r < m := by
  induction k generalizing b e r with
  | zero => exact Nat.mod_lt _ hm
  | succ k ih =>
    simp only [powLoop]
    split
    · exact Nat.mod_lt _ hm
    · exact ih _ _ _

private theorem powMod_cast (a e m : ℕ) :
    (powMod a e m : ZMod m) = (a : ZMod m) ^ e := by
  simp [powMod, powLoop_cast, ZMod.natCast_mod]

private theorem stripOne_preserves {r l : ℕ} (hr : r.Prime) (hl : l.Prime)
    (hne : r ≠ l) (k n : ℕ) (hd : r ∣ n) : r ∣ stripOne k n l := by
  induction k generalizing n with
  | zero => exact dvd_zero _
  | succ k ih =>
    simp only [stripOne]
    split_ifs with h
    · have hld : l ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h)
      have hm : r ∣ l * (n / l) := by rwa [Nat.mul_div_cancel' hld]
      have hrl : ¬ r ∣ l := by
        intro hrl
        exact hne ((Nat.prime_dvd_prime_iff_eq hr hl).mp hrl)
      exact ih _ ((hr.dvd_mul.mp hm).resolve_left hrl)
    · exact hd

private theorem stripAllNat_preserves {r n : ℕ} (hr : r.Prime)
    (ls : List ℕ) (hls : ∀ l ∈ ls, l.Prime) (hne : ∀ l ∈ ls, r ≠ l)
    (hd : r ∣ n) : r ∣ stripAllNat n ls := by
  induction ls generalizing n with
  | nil => exact hd
  | cons l ls ih =>
    apply ih (fun a ha => hls a (List.mem_cons_of_mem l ha))
      (fun a ha => hne a (List.mem_cons_of_mem l ha))
    exact stripOne_preserves hr (hls l (by simp)) (hne l (by simp)) 24 n hd

private theorem stripAllNat_covers {n : ℕ} {ls : List ℕ}
    (hls : ∀ l ∈ ls, l.Prime) (h : stripAllNat n ls = 1)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ n) : r ∈ ls := by
  by_contra hx
  have hne : ∀ l ∈ ls, r ≠ l := by
    intro l hl he
    exact hx (he.symm ▸ hl)
  have hdiv := stripAllNat_preserves hr ls hls hne hd
  rw [h] at hdiv
  exact hr.not_dvd_one hdiv

private theorem checkPrimeNat_sound {p q : ℕ} {ls : List ℕ}
    (hq : q.Prime) (hls : ∀ l ∈ ls, l.Prime)
    (h : checkPrimeNat p q ls = true) :
    q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  simp only [checkPrimeNat, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hp, hlt⟩, hs⟩, hpow⟩, htests⟩ := h
  refine ⟨hq, hlt, orderOf_eq_of_pow_and_pow_div_prime (by omega) ?_ ?_⟩
  · rw [← powMod_cast, hpow]
    simp
  · intro r hr hd
    have hrmem := stripAllNat_covers hls hs hr hd
    have ht := (List.all_eq_true.mp htests) r hrmem
    have hne : powMod q ((p - 1) / r) p ≠ 1 := by simpa using ht
    intro heq
    apply hne
    have hc := powMod_cast q ((p - 1) / r) p
    rw [heq] at hc
    have hv := congrArg ZMod.val hc
    have hbound : powMod q ((p - 1) / r) p < p :=
      powLoop_lt _ _ _ _ _ (by omega)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound,
      ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < p)] at hv
    exact hv

private theorem checkPrimeNat_prime {p q : ℕ} {ls : List ℕ}
    (hq : q.Prime) (hls : ∀ l ∈ ls, l.Prime)
    (h : checkPrimeNat p q ls = true) : p.Prime := by
  obtain ⟨hq, hlt, ho⟩ := checkPrimeNat_sound hq hls h
  have hm : 0 < p - 1 := by have := hq.two_le; omega
  apply lucas_primality p (q : ZMod p)
  · rw [← ho]
    exact pow_orderOf_eq_one _
  · intro r hr hd hx
    have hdiv := orderOf_dvd_of_pow_eq_one hx
    rw [ho] at hdiv
    exact Nat.not_dvd_of_pos_of_lt
      (Nat.div_pos (Nat.le_of_dvd hm hd) hr.pos) (Nat.div_lt_self hm hr.one_lt) hdiv

private theorem PrimeCertificate.sound {p : ℕ} (h : PrimeCertificate p) : p.Prime := by
  induction h with
  | two => exact Nat.prime_two
  | @step p q ls hq hls hcheck ihq ihls =>
    exact checkPrimeNat_prime ihq ihls hcheck

private theorem primeValue_prime (q : PrimeValue) : q.val.Prime :=
  q.certificate.sound

/-- Successful prime slots have the exact multiplicative order, not just a divisor. -/
theorem checkPrime_sound {p : ℕ} {q : PrimeValue} {ls : List PrimeValue}
    (h : checkPrime p q ls = true) :
    q.val.Prime ∧ q.val < p ∧ orderOf (q.val : ZMod p) = p - 1 := by
  apply checkPrimeNat_sound (primeValue_prime q) ?_ h
  intro l hl
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hl
  subst l
  exact primeValue_prime a

/-- The same returning-order certificate is a Lucas primality certificate. -/
theorem checkPrime_prime {p : ℕ} {q : PrimeValue} {ls : List PrimeValue}
    (h : checkPrime p q ls = true) : p.Prime := by
  apply checkPrimeNat_prime (primeValue_prime q) ?_ h
  intro l hl
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hl
  subst l
  exact primeValue_prime a

private theorem checkRows_sound {start : ℕ} {rows : List Row}
    (h : checkRows start rows = true) :
    ∀ k, k < rows.length → (start + 2 * k).Prime →
      ∃ q, q.Prime ∧ q < start + 2 * k ∧
        orderOf (q : ZMod (start + 2 * k)) = start + 2 * k - 1 := by
  induction rows generalizing start with
  | nil => simp
  | cons row rows ih =>
    cases row with
    | c d =>
      simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      intro k hk hp
      cases k with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero] at hp ⊢
        have hd : d ∣ start := Nat.dvd_of_mod_eq_zero h.1.2
        have he := (Nat.dvd_prime hp).mp hd
        rcases he with he | he <;> omega
      | succ k =>
        have he : start + 2 * (k + 1) = (start + 2) + 2 * k := by omega
        rw [he] at hp ⊢
        exact ih h.2 k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk) hp
    | p q ls =>
      simp only [checkRows, Bool.and_eq_true] at h
      intro k hk hp
      cases k with
      | zero =>
        simpa using (show ∃ a, a.Prime ∧ a < start ∧
          orderOf (a : ZMod start) = start - 1 from ⟨q.val, checkPrime_sound h.1⟩)
      | succ k =>
        have he : start + 2 * (k + 1) = (start + 2) + 2 * k := by omega
        rw [he] at hp ⊢
        exact ih h.2 k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk) hp

/-- Every prime in every checked odd slot has a certified smaller prime primitive root. -/
theorem checkBlock_sound {start count : ℕ} {rows : List Row}
    (h : checkBlock start count rows = true) :
    ∀ k, k < count → (start + 2 * k).Prime →
      ∃ q, q.Prime ∧ q < start + 2 * k ∧
        orderOf (q : ZMod (start + 2 * k)) = start + 2 * k - 1 := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.1]
  exact checkRows_sound h.2

#print axioms checkPrime_prime
#print axioms checkBlock_append
#print axioms checkPrime_sound
#print axioms checkBlock_sound

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
