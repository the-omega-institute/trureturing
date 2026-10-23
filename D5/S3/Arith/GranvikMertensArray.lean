/- GID: D5/S3/Arith/GranvikMertensArray
   generality: I
   mirror-B: D5/B/S3/Arith/GranvikMertensArray
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Somos's rational recurrence for the Granvik Mertens array. -/

import D5.S3.Arith.RoldanCirculantEnergyP2Q3
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Arith.GranvikMertensArray

/-- Somos's recurrence for OEIS A192763, with positive indices.
Cells with a zero index are extended by zero. All divisions are rational. -/
def T (n k : ℕ) : ℚ :=
  if hz : n = 0 ∨ k = 0 then 0
  else if hs : n < k then T k n
  else if hb : k = 1 then
    if hn : n ≤ 2 then n
    else
      (-T (n - 1) 1 -
        ∑ i ∈ (Icc 2 (n - 1)).attach, T n i) / (n + 1) + T (n - 1) 1
  else if hi : k < n then T k ((n - 1) % k + 1)
  else -∑ i ∈ (Icc 1 (n - 1)).attach, T n i
termination_by 4 * max n k +
  if n < k then 3 else if n = k then 2 else if k = 1 then 1 else 0
decreasing_by
  all_goals simp_wf
  all_goals try (have := Nat.mod_lt (n - 1) (by omega : 0 < k))
  all_goals try (have := Finset.mem_Icc.mp i.property)
  all_goals split_ifs <;> omega


private theorem coprime_mertens_cancel (n : ℕ) (hn : 1 < n) :
    (∑ j ∈ (Icc 1 (n - 1)).filter (fun j => j.Coprime n),
      ∑ d ∈ Icc 1 ((n - 1) / j), (ArithmeticFunction.moebius d : ℚ)) =
        -(ArithmeticFunction.moebius n : ℚ) := by
  classical
  have hn0 : n ≠ 0 := by omega
  let r : ArithmeticFunction ℚ :=
    ⟨fun d => if d ∣ n then (ArithmeticFunction.moebius d : ℚ) else 0, by simp⟩
  let c : ArithmeticFunction ℚ := (ArithmeticFunction.zeta : ArithmeticFunction ℚ) * r
  have hc (j : ℕ) (hj : 0 < j) : c j = if j.Coprime n then 1 else 0 := by
    change ((ArithmeticFunction.zeta : ArithmeticFunction ℚ) * r) j = _
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    change (∑ d ∈ j.divisors,
      if d ∣ n then (ArithmeticFunction.moebius d : ℚ) else 0) = _
    rw [← Finset.sum_filter]
    have hg0 : j.gcd n ≠ 0 := (Nat.gcd_pos_of_pos_left n hj).ne'
    have hcommon : j.divisors.filter (fun d => d ∣ n) = (j.gcd n).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      simp [hj.ne', hg0, and_assoc]
    rw [hcommon]
    have hmu := congrArg (fun f : ArithmeticFunction ℚ => f (j.gcd n))
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
    rw [ArithmeticFunction.coe_mul_zeta_apply] at hmu
    simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply,
      Nat.Coprime] using hmu
  have hcancel : c * (ArithmeticFunction.moebius : ArithmeticFunction ℚ) = r := by
    dsimp [c]
    rw [mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℚ) r, mul_assoc,
      ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
  have hinterval (m : ℕ) : Icc 1 m = Ioc 0 m :=
    Finset.Icc_succ_left_eq_Ioc 0 m
  simp_rw [hinterval]
  have hproper : (Ioc 0 (n - 1)).filter (fun d => d ∣ n) = n.properDivisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.properDivisors, Finset.mem_Ico]
    omega
  calc
    _ = ∑ j ∈ Ioc 0 (n - 1),
        c j * ∑ d ∈ Ioc 0 ((n - 1) / j), (ArithmeticFunction.moebius d : ℚ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc j (Finset.mem_Ioc.mp hj).1]
      split_ifs <;> simp
    _ = ∑ m ∈ Ioc 0 (n - 1),
        (c * (ArithmeticFunction.moebius : ArithmeticFunction ℚ)) m := by
      simpa only [ArithmeticFunction.intCoe_apply] using
        (ArithmeticFunction.sum_Ioc_mul_eq_sum_sum c
          (ArithmeticFunction.moebius : ArithmeticFunction ℚ) (n - 1)).symm
    _ = ∑ m ∈ Ioc 0 (n - 1), r m := by rw [hcancel]
    _ = ∑ d ∈ n.properDivisors, (ArithmeticFunction.moebius d : ℚ) := by
      change (∑ m ∈ Ioc 0 (n - 1),
        if m ∣ n then (ArithmeticFunction.moebius m : ℚ) else 0) = _
      rw [← Finset.sum_filter, hproper]
    _ = -(ArithmeticFunction.moebius n : ℚ) := by
      have hmu := congrArg (fun f : ArithmeticFunction ℚ => f n)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℚ))
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
        if_neg (show n ≠ 1 by omega)] at hmu
      simp only [ArithmeticFunction.intCoe_apply] at hmu
      rw [← Nat.insert_self_properDivisors hn0,
        Finset.sum_insert Nat.self_notMem_properDivisors] at hmu
      linarith

private theorem totient_weighted_moebius (n : ℕ) :
    (∑ d ∈ n.divisors,
      (Nat.totient (n / d) : ℚ) * d * (ArithmeticFunction.moebius d : ℚ)) =
        (ArithmeticFunction.moebius n : ℚ) := by
  classical
  let ident : ArithmeticFunction ℚ := ⟨fun d => (d : ℚ), by simp⟩
  let weighted : ArithmeticFunction ℚ :=
    ⟨fun d => (d : ℚ) * (ArithmeticFunction.moebius d : ℚ), by simp⟩
  let phi : ArithmeticFunction ℚ := ⟨fun d => (Nat.totient d : ℚ), by simp⟩
  have hinv : ident * weighted = 1 := by
    ext m
    calc
      (ident * weighted) m =
          (m : ℚ) * ((ArithmeticFunction.zeta : ArithmeticFunction ℚ) *
            (ArithmeticFunction.moebius : ArithmeticFunction ℚ)) m := by
        rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hp0 : p.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
        change (p.1 : ℚ) * ((p.2 : ℚ) * (ArithmeticFunction.moebius p.2 : ℚ)) =
          (m : ℚ) * ((ArithmeticFunction.zeta p.1 : ℚ) *
            (ArithmeticFunction.moebius p.2 : ℚ))
        rw [ArithmeticFunction.zeta_apply_ne hp0]
        simp only [Nat.cast_one, one_mul]
        rw [← mul_assoc, ← Nat.cast_mul, hprod]
      _ = (1 : ArithmeticFunction ℚ) m := by
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, ArithmeticFunction.one_apply]
        split_ifs with hm <;> simp [hm]
  have hphi : phi = (ArithmeticFunction.moebius : ArithmeticFunction ℚ) * ident := by
    have hsum : (ArithmeticFunction.zeta : ArithmeticFunction ℚ) * phi = ident := by
      ext m
      rw [ArithmeticFunction.coe_zeta_mul_apply]
      change (∑ d ∈ m.divisors, (Nat.totient d : ℚ)) = (m : ℚ)
      exact_mod_cast Nat.sum_totient m
    rw [← hsum, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  have hmain : phi * weighted = (ArithmeticFunction.moebius : ArithmeticFunction ℚ) := by
    rw [hphi, mul_assoc, hinv, mul_one]
  have he := congrArg (fun f : ArithmeticFunction ℚ => f n) hmain
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b => phi a * weighted b)] at he
  change (∑ d ∈ n.divisors,
    (Nat.totient (n / d) : ℚ) * ((d : ℚ) * (ArithmeticFunction.moebius d : ℚ))) =
      (ArithmeticFunction.moebius n : ℚ) at he
  simpa only [mul_assoc] using he


private theorem T_symm (n k : ℕ) : T n k = T k n := by
  by_cases hn : n = 0
  · subst n
    rw [T.eq_def, T.eq_def]
    simp
  by_cases hk : k = 0
  · subst k
    rw [T.eq_def, T.eq_def]
    simp
  rcases lt_trichotomy n k with h | rfl | h
  · rw [T.eq_def]
    simp only [hn, hk, or_self, ↓reduceDIte, h]
  · rfl
  · symm
    rw [T.eq_def]
    simp only [hn, hk, or_self, ↓reduceDIte, h]

private theorem T_border (n : ℕ) (hn : 3 ≤ n) :
    T n 1 = (-T (n - 1) 1 - ∑ i ∈ Icc 2 (n - 1), T n i) /
      (n + 1) + T (n - 1) 1 := by
  rw [T.eq_def]
  simp only [show ¬ (n = 0 ∨ 1 = 0) by omega, show ¬n < 1 by omega,
    show ¬n ≤ 2 by omega, ↓reduceDIte, sum_attach]

private theorem T_diagonal (n : ℕ) (hn : 2 ≤ n) :
    T n n = -∑ i ∈ Icc 1 (n - 1), T n i := by
  rw [T.eq_def]
  simp only [show ¬ (n = 0 ∨ n = 0) by omega, lt_self_iff_false,
    show n ≠ 1 by omega, ↓reduceDIte, sum_attach]

private theorem T_interior (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n k = T k ((n - 1) % k + 1) := by
  rw [T.eq_def]
  simp only [show ¬ (n = 0 ∨ k = 0) by omega, show ¬n < k by omega,
    show k ≠ 1 by omega, hkn, ↓reduceDIte]



private def lastQuotient (n k : ℕ) : ℕ :=
  if hk : k ≤ 1 then n else lastQuotient k (n % k)
termination_by k
decreasing_by exact Nat.mod_lt _ (by omega)

private lemma positive_quotient_transport {n k a b : ℕ}
    (ha : 1 < a) (hb : 0 < b)
    (hd : k * a = n * b + 1 ∨ (k * a + 1 = n * b ∧ 1 < b)) :
    (n - 1) / a = (k - 1) / b := by
  let q := (k - 1) / b
  have hk : 0 < k := by
    by_contra hz
    have hkzero : k = 0 := by omega
    rcases hd with hd | ⟨hd, hb'⟩
    · simp [hkzero] at hd
    · have hmul : n * b = 1 := by simpa [hkzero] using hd.symm
      have := Nat.eq_one_of_mul_eq_one_left hmul
      omega
  have hn : 0 < n := by
    by_contra hz
    have hnzero : n = 0 := by omega
    rcases hd with hd | ⟨hd, hb'⟩
    · have hmul : k * a = 1 := by simpa [hnzero] using hd
      have := Nat.eq_one_of_mul_eq_one_left hmul
      omega
    · simp [hnzero] at hd
  have lo : q * b < k := by
    have := Nat.div_mul_le_self (k - 1) b
    dsimp [q]
    omega
  have hi : k ≤ (q + 1) * b := by
    have hh : k - 1 < (q + 1) * b := by
      simpa only [q, Nat.mul_comm] using Nat.lt_mul_div_succ (k - 1) hb
    omega
  have lower : q * a < n := by
    by_contra bad
    have bad : n ≤ q * a := by omega
    have badmul := Nat.mul_le_mul_right b bad
    have lomul := Nat.mul_le_mul_right a (show q * b + 1 ≤ k by omega)
    rcases hd with hd | ⟨hd, hb'⟩ <;> nlinarith
  have upper : n ≤ (q + 1) * a := by
    by_contra bad
    have bad : (q + 1) * a + 1 ≤ n := by omega
    have badmul := Nat.mul_le_mul_right b bad
    have himul := Nat.mul_le_mul_right a hi
    rcases hd with hd | ⟨hd, hb'⟩ <;> nlinarith
  change (n - 1) / a = q
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma signed_bezout_step {n k a b : ℕ}
    (hk : 1 < k) (hkn : k < n) (ha : 0 < a) (hhalf : 2 * a ≤ n)
    (hd : k * a = n * b + 1 ∨ k * a + 1 = n * b) :
    0 < n % k ∧ 0 < b ∧ 2 * b ≤ k ∧
      (if n % k = 1 then (n - 1) / a = k else
        ∃ c, ((n % k) * b = k * c + 1 ∨ (n % k) * b + 1 = k * c) ∧
          (n - 1) / a = (k - 1) / b) := by
  have hb : 0 < b := by
    by_contra hb
    have hb : b = 0 := by omega
    rcases hd with hd | hd <;> simp only [hb, Nat.mul_zero, Nat.zero_add] at hd
    · nlinarith
    · omega
  have hbhalf : 2 * b ≤ k := by
    by_contra bad
    have bad : k + 1 ≤ 2 * b := by omega
    have bmul := Nat.mul_le_mul_left n bad
    have amul := Nat.mul_le_mul_left k hhalf
    rcases hd with hd | hd <;> nlinarith
  have hs : 0 < n % k := by
    by_contra hs
    have hs : n % k = 0 := by omega
    rcases hd with hd | hd
    · have hm := congrArg (fun v : ℕ => v % k) hd
      simp [Nat.add_mod, Nat.mul_mod, hs, Nat.mod_eq_of_lt hk] at hm
    · have hm := congrArg (fun v : ℕ => v % k) hd
      simp [Nat.add_mod, Nat.mul_mod, hs, Nat.mod_eq_of_lt hk] at hm
  let q := n / k
  have hdiv : n = q * k + n % k := by
    dsimp [q]
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n k).symm
  have hdivmul := congrArg (fun v : ℕ => v * b) hdiv
  have hqb : q * b ≤ a := by
    by_contra bad
    have bad : a + 1 ≤ q * b := by omega
    have badmul := Nat.mul_le_mul_left k bad
    have hsb : 1 ≤ (n % k) * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rcases hd with hd | hd <;> nlinarith
  let c := a - q * b
  have hc : c + q * b = a := by
    dsimp [c]
    exact Nat.sub_add_cancel hqb
  have hcmul := congrArg (fun v : ℕ => k * v) hc
  have hcDet : (n % k) * b = k * c + 1 ∨ (n % k) * b + 1 = k * c := by
    rcases hd with hd | hd
    · right
      nlinarith
    · left
      nlinarith
  refine ⟨hs, hb, hbhalf, ?_⟩
  split_ifs with hsone
  · rcases hcDet with hcDet | hcDet
    · have hczero : c = 0 := by
        by_contra hczero
        have hcle := Nat.le_mul_of_pos_right k (show 0 < c by omega)
        simp only [hsone, Nat.one_mul] at hcDet
        nlinarith
      have hbone : b = 1 := by simpa [hczero, hsone] using hcDet
      have hdiag : n - 1 = k * a := by
        rcases hd with hd | hd <;> simp only [hbone, Nat.mul_one] at hd
        · have : a = q := by simpa [hczero, hbone] using hc.symm
          nlinarith
        · omega
      rw [hdiag, Nat.mul_div_cancel _ ha]
    · have hcbounds : b + 1 ≤ k := by omega
      have hcpos : 0 < c := by
        by_contra hczero
        have hczero : c = 0 := by omega
        have hbad : b + 1 = 0 := by
          simpa only [hsone, Nat.one_mul, hczero, Nat.mul_zero] using hcDet
        omega
      have hcle := Nat.le_mul_of_pos_right k hcpos
      have hceq : c = 1 := by
        by_contra hcne
        have hctwo : 2 ≤ c := by omega
        have hcmul := Nat.mul_le_mul_left k hctwo
        simp only [hsone, Nat.one_mul] at hcDet
        nlinarith
      have hbone : b = 1 := by
        simp only [hceq, hsone, Nat.one_mul, Nat.mul_one] at hcDet
        omega
      have hktwo : k = 2 := by
        simpa [hceq, hsone, hbone] using hcDet.symm
      simp only [hceq, hbone, Nat.mul_one] at hc
      simp only [hktwo, hsone] at hdiv
      omega
  · refine ⟨c, hcDet, ?_⟩
    have hatwo : 1 < a := by
      by_contra han
      have haone : a = 1 := by omega
      rcases hd with hd | hd <;> simp only [haone, Nat.mul_one] at hd
      · nlinarith
      · have hbone : b = 1 := by
          by_contra hbn
          have hbtwo : 2 ≤ b := by omega
          have hprod := Nat.mul_le_mul_left n hbtwo
          nlinarith
        have hn : n = k + 1 := by simpa [hbone] using hd.symm
        have : n % k = 1 := by simp [hn, Nat.add_mod, Nat.mod_eq_of_lt hk]
        contradiction
    apply positive_quotient_transport hatwo hb
    rcases hd with hd | hd
    · exact Or.inl hd
    · right
      refine ⟨hd, ?_⟩
      by_contra hbn
      have hbone : b = 1 := by omega
      have hn : n = a * k + 1 := by nlinarith
      have : n % k = 1 := by simp [hn, Nat.add_mod, Nat.mod_eq_of_lt hk]
      contradiction

private lemma lastQuotient_of_signed_bezout {n k a b : ℕ}
    (hk : 1 < k) (hkn : k < n) (ha : 0 < a) (hhalf : 2 * a ≤ n)
    (hd : k * a = n * b + 1 ∨ k * a + 1 = n * b) :
    lastQuotient n k = (n - 1) / a := by
  induction k using Nat.strong_induction_on generalizing n a b with
  | h k ih =>
    have step := signed_bezout_step hk hkn ha hhalf hd
    rcases step with ⟨hs, hb, hbhalf, hstep⟩
    rw [lastQuotient, dif_neg (by omega)]
    by_cases hsone : n % k = 1
    · simp only [hsone, ↓reduceIte] at hstep
      rw [hsone, lastQuotient, dif_pos (by omega), hstep]
    · simp only [hsone, ↓reduceIte] at hstep
      obtain ⟨c, hcDet, hquot⟩ := hstep
      rw [ih (n % k) (Nat.mod_lt _ (by omega)) (by omega)
        (Nat.mod_lt _ (by omega)) hb hbhalf hcDet, hquot]

private lemma min_inverse_signed_bezout {n k : ℕ} (hn : 1 < n)
    (hk : 1 < k) (hkn : k < n) (hcop : k.Coprime n) :
    let u := ((k : ZMod n)⁻¹).val
    let a := min u (n - u)
    0 < a ∧ 2 * a ≤ n ∧
      ∃ b, k * a = n * b + 1 ∨ k * a + 1 = n * b := by
  haveI : NeZero n := ⟨by omega⟩
  let u := ((k : ZMod n)⁻¹).val
  have hult : u < n := ZMod.val_lt _
  have humod : (k * u) % n = 1 := by
    have hcast : ((k * u : ℕ) : ZMod n) = (1 : ℕ) := by
      simpa only [Nat.cast_mul, Nat.cast_one] using ZMod.mul_val_inv hcop
    have hmod := (ZMod.natCast_eq_natCast_iff' (k * u) 1 n).mp hcast
    simpa [Nat.mod_eq_of_lt hn] using hmod
  have hup : 0 < u := by
    by_contra hup
    have : u = 0 := by omega
    simp_all
  let b := k * u / n
  have hdet : k * u = n * b + 1 := by
    dsimp [b]
    have := Nat.mod_add_div (k * u) n
    omega
  have hblt : b < k := by
    dsimp [b]
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    nlinarith [Nat.mul_lt_mul_of_pos_left hult (show 0 < k by omega)]
  change 0 < min u (n - u) ∧ 2 * min u (n - u) ≤ n ∧ _
  by_cases hlow : u ≤ n - u
  · rw [min_eq_left hlow]
    exact ⟨hup, by omega, b, Or.inl hdet⟩
  · rw [min_eq_right (by omega)]
    refine ⟨by omega, by omega, k - b, Or.inr ?_⟩
    have huadd := Nat.sub_add_cancel hult.le
    have hbadd := Nat.sub_add_cancel hblt.le
    have huaddmul := congrArg (fun v : ℕ => k * v) huadd
    have hbaddmul := congrArg (fun v : ℕ => n * v) hbadd
    nlinarith

private theorem lastQuotient_eq_inverse {n k : ℕ} (hk : 1 < k)
    (hkn : k < n) (hcop : k.Coprime n) :
    lastQuotient n k =
      (n - 1) / min (((k : ZMod n)⁻¹).val) (n - ((k : ZMod n)⁻¹).val) := by
  have hh := min_inverse_signed_bezout (by omega : 1 < n) hk hkn hcop
  dsimp only at hh
  obtain ⟨ha, hhalf, b, hd⟩ := hh
  exact lastQuotient_of_signed_bezout hk hkn ha hhalf hd


private theorem granvik_interior_of_somos
    (A : ℕ → ℕ → ℚ)
    (hsym : ∀ a b, A a b = A b a)
    (hred : ∀ n k, 2 ≤ k → k < n → A n k = A k ((n - 1) % k + 1))
    (hdiag : ∀ k, 2 ≤ k → A k k = -∑ i ∈ Icc 1 (k - 1), A k i)
    (n k : ℕ) (hk : 2 ≤ k) (hn : k ≤ n) :
    A n k = -∑ i ∈ Icc 1 (k - 1), A (n - i) k := by
  have hnorm (m : ℕ) (hm : 1 ≤ m) :
      A m k = A ((m - 1) % k + 1) k := by
    by_cases hmk : k < m
    · rw [hred m k hk hmk, hsym k]
    · rw [Nat.mod_eq_of_lt (by omega : m - 1 < k), Nat.sub_add_cancel hm]
  let f : ℕ → ℚ := fun i => A (i + 1) k
  have hper : Function.Periodic f k := by
    intro t
    change A (t + k + 1) k = A (t + 1) k
    rw [hnorm (t + k + 1) (by omega), hnorm (t + 1) (by omega)]
    simp
  have hshift (t : ℕ) :
      (∑ i ∈ range k, f (i + t)) = ∑ i ∈ range k, f i := by
    calc
      (∑ i ∈ range k, f (i + t)) = ∑ i ∈ Ico t (t + k), f i := by
        simpa only [zero_add, Nat.Ico_zero_eq_range, Nat.add_comm k t] using
          (Finset.sum_Ico_add' f 0 k t)
      _ = ∑ i ∈ Ico t (t + k), f (i % k) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hper.map_mod_nat i).symm
      _ = ∑ i ∈ (Ico t (t + k)).image (· % k), f i := by
        exact (Finset.sum_image (fun i hi j hj hij =>
          Nat.mod_injOn_Ico t k hi hj hij)).symm
      _ = ∑ i ∈ range k, f i := by rw [Nat.image_Ico_mod]
  have hfund : (∑ i ∈ range k, f i) = 0 := by
    have hzero : (∑ i ∈ Ico 1 (k + 1), A i k) = 0 := by
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k)]
      have heq : Ico 1 k = Icc 1 (k - 1) := by
        ext i
        simp only [mem_Ico, mem_Icc]
        omega
      rw [heq, hdiag k hk]
      have hs : (∑ i ∈ Icc 1 (k - 1), A i k) =
          ∑ i ∈ Icc 1 (k - 1), A k i := by
        exact Finset.sum_congr rfl (fun i _ => hsym i k)
      rw [hs]
      simp
    have heq := Finset.sum_Ico_add' (fun i => A i k) 0 k 1
    simpa only [zero_add, Nat.Ico_zero_eq_range, f] using heq.trans hzero
  have hwindow : (∑ i ∈ Ico (n + 1 - k) (n + 1), A i k) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 - (n + 1 - k) = k := by omega
    rw [hlen]
    have heq : (∑ j ∈ range k, A (n + 1 - k + j) k) =
        ∑ j ∈ range k, f (j + (n - k)) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [f]
      congr 1
      omega
    rw [heq, hshift, hfund]
  have hreflect : (∑ i ∈ Icc 1 (k - 1), A (n - i) k) =
      ∑ j ∈ Ico (n + 1 - k) n, A j k := by
    have heq : Icc 1 (k - 1) = Ico 1 k := by
      ext i
      simp only [mem_Ico, mem_Icc]
      omega
    rw [heq]
    simpa only [Nat.add_sub_cancel] using
      (Finset.sum_Ico_reflect (fun j => A j k) 1
        (m := k) (n := n) (by omega : k ≤ n + 1))
  rw [Finset.sum_Ico_succ_top (by omega : n + 1 - k ≤ n)] at hwindow
  rw [hreflect]
  linarith

private theorem reduced_border_sum (n : ℕ) (hn : 1 < n) :
    (∑ u ∈ (Finset.Icc 1 (n - 1)).filter (fun u => u.Coprime n),
      (2 + ∑ d ∈ Finset.Icc 1 ((n - 1) / min u (n - u)),
        (ArithmeticFunction.moebius d : ℚ))) =
      (Nat.totient n : ℚ) - 2 * (ArithmeticFunction.moebius n : ℚ) := by
  classical
  let U := (Finset.Icc 1 (n - 1)).filter (fun u => u.Coprime n)
  let B : ℕ → ℚ := fun m => 2 + ∑ d ∈ Finset.Icc 1 m,
    (ArithmeticFunction.moebius d : ℚ)
  change (∑ u ∈ U, B ((n - 1) / min u (n - u))) = _
  have hB1 : B 1 = 3 := by
    norm_num [B, ArithmeticFunction.moebius_apply_one]
  have hubound (u : ℕ) (hu : u ∈ U) : 1 ≤ u ∧ u < n := by
    have h := (Finset.mem_filter.mp hu).1
    simp only [Finset.mem_Icc] at h
    omega
  have hpoint (u : ℕ) (hu : u ∈ U) :
      B ((n - 1) / min u (n - u)) + 3 =
        B ((n - 1) / u) + B ((n - 1) / (n - u)) := by
    obtain ⟨hu1, hun⟩ := hubound u hu
    by_cases hle : u ≤ n - u
    · have hdiv : (n - 1) / (n - u) = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [min_eq_left hle, hdiv, hB1]
    · have hdiv : (n - 1) / u = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [min_eq_right (by omega : n - u ≤ u), hdiv, hB1]
      ring
  have hreflect (u : ℕ) (hu : u ∈ U) : n - u ∈ U := by
    obtain ⟨hu1, hun⟩ := hubound u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    exact (Nat.coprime_self_sub_left (by omega : u ≤ n)).mpr
      (Finset.mem_filter.mp hu).2
  have hsymm :
      (∑ u ∈ U, B ((n - 1) / (n - u))) =
        ∑ u ∈ U, B ((n - 1) / u) := by
    refine Finset.sum_bij (fun u _ => n - u) hreflect ?_ ?_ ?_
    · intro a ha b hb hab
      have ha' := hubound a ha
      have hb' := hubound b hb
      omega
    · intro b hb
      refine ⟨n - b, hreflect b hb, ?_⟩
      have hb' := hubound b hb
      omega
    · intro u hu
      rfl
  have hcard : U.card = Nat.totient n := by
    change U.card = ((Finset.range n).filter (fun u => n.Coprime u)).card
    congr 1
    ext u
    simp only [U, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hu1, huN⟩, hcop⟩
      exact ⟨by omega, hcop.symm⟩
    · rintro ⟨hun, hcop⟩
      have hu0 : u ≠ 0 := by
        intro hu0
        subst u
        have hn1 : n = 1 := (Nat.coprime_zero_right n).mp hcop
        omega
      exact ⟨⟨by omega, by omega⟩, hcop.symm⟩
  have hplain : (∑ u ∈ U, B ((n - 1) / u)) =
      2 * (U.card : ℚ) - (ArithmeticFunction.moebius n : ℚ) := by
    change (∑ u ∈ U,
      (2 + ∑ d ∈ Finset.Icc 1 ((n - 1) / u),
        (ArithmeticFunction.moebius d : ℚ))) = _
    rw [Finset.sum_add_distrib]
    have hc := coprime_mertens_cancel n hn
    change (∑ u ∈ U, ∑ d ∈ Finset.Icc 1 ((n - 1) / u),
      (ArithmeticFunction.moebius d : ℚ)) =
        -(ArithmeticFunction.moebius n : ℚ) at hc
    rw [hc]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hsum := Finset.sum_congr rfl hpoint
  simp only [Finset.sum_add_distrib] at hsum
  rw [hsymm] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  simp only [hplain, hcard] at hsum
  linarith

private def border (n : ℕ) : ℚ :=
  2 + ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℚ)

private def model (n k : ℕ) : ℚ :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else if n = 1 ∨ k = 1 then border (max n k)
  else if 1 < n.gcd k then (n.gcd k : ℚ) * (ArithmeticFunction.moebius (n.gcd k) : ℚ)
  else border (lastQuotient (max n k) (min n k))

private theorem model_symm (n k : ℕ) : model n k = model k n := by
  simp only [model, or_comm, and_comm, Nat.gcd_comm, max_comm, min_comm]

private theorem model_border (n : ℕ) (hn : 2 ≤ n) : model n 1 = border n := by
  simp [model, show n ≠ 0 by omega, show n ≠ 1 by omega, max_eq_left (by omega : 1 ≤ n)]

private theorem model_diagonal (n : ℕ) (hn : 2 ≤ n) :
    model n n = (n : ℚ) * (ArithmeticFunction.moebius n : ℚ) := by
  simp [model, show n ≠ 0 by omega, show n ≠ 1 by omega, show 1 < n by omega]

private theorem model_interior (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    model n k = model k ((n - 1) % k + 1) := by
  let r := (n - 1) % k + 1
  have hr0 : 0 < r := by dsimp [r]; omega
  have hrk : r ≤ k := by
    have := Nat.mod_lt (n - 1) (by omega : 0 < k)
    dsimp [r]
    omega
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hn : n = r + k * ((n - 1) / k) := by
    have := Nat.mod_add_div (n - 1) k
    dsimp [r]
    omega
  have hg : k.gcd r = n.gcd k := by
    conv_rhs => rw [hn, Nat.gcd_add_mul_left_left, Nat.gcd_comm]
  change model n k = model k r
  have hleft : model n k =
      if 1 < n.gcd k then (n.gcd k : ℚ) * (ArithmeticFunction.moebius (n.gcd k) : ℚ)
      else border (lastQuotient n k) := by
    simp [model, hn0, hn1, hk0, hk1, max_eq_left hkn.le, min_eq_right hkn.le]
  rw [hleft]
  by_cases hc : 1 < n.gcd k
  · have hr1 : r ≠ 1 := by intro h; simp [h] at hg; omega
    simp [model, hk0, hk1, hr0.ne', hr1, hg, hc]
  · have hg1 : n.gcd k = 1 := by
      have := Nat.gcd_pos_of_pos_left k (by omega : 0 < n)
      omega
    have hrlt : r < k := by
      by_contra h
      have : r = k := by omega
      simp [this, hg1] at hg
      omega
    have hmod : n % k = r := by
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
    have hlast : lastQuotient n k = lastQuotient k r := by
      rw [lastQuotient, dif_neg (by omega), hmod]
    rw [if_neg hc, hlast]
    by_cases hr1 : r = 1
    · rw [hr1, model_border k hk]
      simp [lastQuotient]
    · simp [model, hk0, hk1, hr0.ne', hr1, hg, hc,
        max_eq_left hrk, min_eq_right hrk]

private theorem sum_inverse (n : ℕ) (hn : 1 < n) (f : ℕ → ℚ) :
    (∑ k ∈ (Icc 1 (n - 1)).filter (fun k => k.Coprime n),
      f (((k : ZMod n)⁻¹).val)) =
      ∑ k ∈ (Icc 1 (n - 1)).filter (fun k => k.Coprime n), f k := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let U := (Icc 1 (n - 1)).filter (fun k => k.Coprime n)
  let p : ℕ → ℕ := fun k => ((k : ZMod n)⁻¹).val
  have hp (k : ℕ) (hk : k ∈ U) : p k ∈ U := by
    have hc := (mem_filter.mp hk).2
    have hu := ZMod.val_coe_unit_coprime (ZMod.unitOfCoprime k hc)⁻¹
    have he : p k = (((ZMod.unitOfCoprime k hc)⁻¹ : (ZMod n)ˣ) : ZMod n).val := by
      simp only [p, ← ZMod.coe_unitOfCoprime k hc, ZMod.inv_coe_unit]
    rw [he]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, hu⟩
    · by_contra h
      have hz : (((ZMod.unitOfCoprime k hc)⁻¹ : (ZMod n)ˣ) : ZMod n).val = 0 := by omega
      rw [hz, Nat.coprime_zero_left] at hu
      omega
    · have := ZMod.val_lt (((ZMod.unitOfCoprime k hc)⁻¹ : (ZMod n)ˣ) : ZMod n)
      omega
  have hpp (k : ℕ) (hk : k ∈ U) : p (p k) = k := by
    have hc := (mem_filter.mp hk).2
    have hkn := (mem_Icc.mp (mem_filter.mp hk).1).2
    change ((((k : ZMod n)⁻¹).val : ZMod n)⁻¹).val = k
    rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime k hc,
      ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_inv,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  refine sum_bij (fun k _ => p k) hp ?_ ?_ (fun _ _ => rfl)
  · intro k hk l hl hkl
    have := congrArg p hkl
    simpa only [hpp k hk, hpp l hl] using this
  · intro k hk
    exact ⟨p k, hp k hk, hpp k hk⟩

private def granvik (n k : ℕ) : ℚ :=
  if hz : n = 0 ∨ k = 0 then 0
  else if hn : n = 1 then
    if hk : k ≤ 2 then k
    else (-granvik 1 (k - 1) -
      ∑ i ∈ (Icc 2 (k - 1)).attach, granvik i k) / (k + 1) + granvik 1 (k - 1)
  else if hk : k = 1 then
    if hn : n ≤ 2 then n
    else (-granvik (n - 1) 1 -
      ∑ i ∈ (Icc 2 (n - 1)).attach, granvik n i) / (n + 1) + granvik (n - 1) 1
  else if hnk : k ≤ n then -∑ i ∈ (Icc 1 (k - 1)).attach, granvik (n - i) k
  else -∑ i ∈ (Icc 1 (n - 1)).attach, granvik (k - i) n
termination_by 3 * max n k +
  if n = 1 ∨ k = 1 then 1 else if n = k then 2 else 0
decreasing_by
  all_goals simp_wf
  all_goals try (have := Finset.mem_Icc.mp i.property)
  all_goals split_ifs <;> omega

private def granvikRule (A : ℕ → ℕ → ℚ) (n k : ℕ) : ℚ :=
  if hz : n = 0 ∨ k = 0 then 0
  else if hn : n = 1 then
    if hk : k ≤ 2 then k
    else (-A 1 (k - 1) -
      ∑ i ∈ (Icc 2 (k - 1)).attach, A i k) / (k + 1) + A 1 (k - 1)
  else if hk : k = 1 then
    if hn : n ≤ 2 then n
    else (-A (n - 1) 1 -
      ∑ i ∈ (Icc 2 (n - 1)).attach, A n i) / (n + 1) + A (n - 1) 1
  else if hnk : k ≤ n then -∑ i ∈ (Icc 1 (k - 1)).attach, A (n - i) k
  else -∑ i ∈ (Icc 1 (n - 1)).attach, A (k - i) n

private theorem T_granvikRule (n k : ℕ) : T n k = granvikRule T n k := by
  unfold granvikRule
  by_cases hz : n = 0 ∨ k = 0
  · rw [T.eq_def]
    simp only [hz, ↓reduceDIte]
  simp only [hz, ↓reduceDIte]
  by_cases hn : n = 1
  · simp only [hn, ↓reduceDIte]
    subst n
    by_cases hk : k ≤ 2
    · simp only [hk, ↓reduceDIte]
      interval_cases k <;> norm_num [T.eq_def] at *
    · simp only [hk, ↓reduceDIte]
      rw [Finset.sum_attach (Icc 2 (k - 1)) (fun i => T i k)]
      rw [T_symm 1 k, T_border k (by omega), T_symm (k - 1) 1]
      have hs : (∑ i ∈ Icc 2 (k - 1), T k i) =
          ∑ i ∈ Icc 2 (k - 1), T i k := by
        exact Finset.sum_congr rfl (fun i _ => T_symm k i)
      rw [hs]
  · simp only [hn, ↓reduceDIte]
    by_cases hk : k = 1
    · simp only [hk, ↓reduceDIte]
      subst k
      by_cases hn2 : n ≤ 2
      · simp only [hn2, ↓reduceDIte]
        interval_cases n <;> norm_num [T.eq_def] at *
      · simp only [hn2, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 2 (n - 1)) (fun i => T n i)]
        exact T_border n (by omega)
    · simp only [hk, ↓reduceDIte]
      by_cases hnk : k ≤ n
      · simp only [hnk, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 1 (k - 1)) (fun i => T (n - i) k)]
        exact granvik_interior_of_somos T T_symm T_interior T_diagonal n k (by omega) hnk
      · simp only [hnk, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 1 (n - 1)) (fun i => T (k - i) n)]
        rw [T_symm n k]
        exact granvik_interior_of_somos T T_symm T_interior T_diagonal k n (by omega) (by omega)

private theorem granvik_unique (A : ℕ → ℕ → ℚ)
    (hA : ∀ n k, A n k = granvikRule A n k) (n k : ℕ) :
    A n k = granvik n k := by
  fun_induction granvik n k <;>
    rw [hA] <;>
    clear hA <;>
    simp_all only [granvikRule, ↓reduceDIte]

private theorem T_eq_granvik (n k : ℕ) : T n k = granvik n k :=
  granvik_unique T T_granvikRule n k

private theorem T_published_unique (A : ℕ → ℕ → ℚ)
    (hA : ∀ n k, A n k = granvikRule A n k) (n k : ℕ) :
    T n k = A n k :=
  (T_eq_granvik n k).trans (granvik_unique A hA n k).symm

private theorem border_step (n : ℕ) (hn : 1 < n) :
    border n = border (n - 1) + (ArithmeticFunction.moebius n : ℚ) := by
  have hs := Finset.sum_Icc_succ_top (a := 1) (b := n - 1)
    (by omega : 1 ≤ n - 1 + 1) (fun d => (ArithmeticFunction.moebius d : ℚ))
  have hlast : n - 1 + 1 = n := by omega
  rw [hlast] at hs
  simp only [border]
  rw [hs]
  ring

private theorem model_coprime_sum (n : ℕ) (hn : 1 < n) :
    (∑ k ∈ (Icc 1 (n - 1)).filter (fun k => k.Coprime n), model n k) =
      (Nat.totient n : ℚ) - (ArithmeticFunction.moebius n : ℚ) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let U := (Icc 1 (n - 1)).filter (fun k => k.Coprime n)
  let f : ℕ → ℚ := fun u => border ((n - 1) / min u (n - u))
  have hstep := border_step n hn
  have hpoint (k : ℕ) (hk : k ∈ U) :
      model n k = f (((k : ZMod n)⁻¹).val) +
        if k = 1 then (ArithmeticFunction.moebius n : ℚ) else 0 := by
    obtain ⟨hki, hcop⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hki
    have hkn : k < n := by omega
    by_cases hkone : k = 1
    · subst k
      have hinv : (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
        simp only [Nat.cast_one, ZMod.inv_one, ZMod.val_one'' (by omega : n ≠ 1)]
      change model n 1 = border ((n - 1) /
        min (((1 : ℕ) : ZMod n)⁻¹).val (n - (((1 : ℕ) : ZMod n)⁻¹).val)) + _
      rw [model_border n (by omega), hinv]
      simp only [min_eq_left (by omega : 1 ≤ n - 1), Nat.div_one, if_pos rfl]
      exact hstep
    · have hg : n.gcd k = 1 := hcop.symm
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hk0 : k ≠ 0 := by omega
      have hmodel : model n k = border (lastQuotient n k) := by
        simp [model, hn0, hn1, hk0, hkone, hg,
          max_eq_left hkn.le, min_eq_right hkn.le]
      rw [hmodel, lastQuotient_eq_inverse (by omega : 1 < k) hkn hcop]
      simp only [f, if_neg hkone, add_zero]
  have hsum : (∑ k ∈ U, model n k) =
      (∑ k ∈ U, f (((k : ZMod n)⁻¹).val)) +
        ∑ k ∈ U, if k = 1 then (ArithmeticFunction.moebius n : ℚ) else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpoint
  have hinverse : (∑ k ∈ U, f (((k : ZMod n)⁻¹).val)) =
      ∑ k ∈ U, f k := sum_inverse n hn f
  have hborder : (∑ k ∈ U, f k) =
      (Nat.totient n : ℚ) - 2 * (ArithmeticFunction.moebius n : ℚ) := by
    simpa only [U, f, border] using reduced_border_sum n hn
  have hone : 1 ∈ U := by
    simp [U, show 1 ≤ n - 1 by omega]
  have hsingle : (∑ k ∈ U,
      if k = 1 then (ArithmeticFunction.moebius n : ℚ) else 0) =
        (ArithmeticFunction.moebius n : ℚ) := by
    simp [hone]
  change (∑ k ∈ U, model n k) = _
  rw [hsum, hinverse, hborder, hsingle]
  ring

private theorem model_row_sum (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Icc 1 (n - 1), model n k) =
      -(n : ℚ) * (ArithmeticFunction.moebius n : ℚ) := by
  classical
  have hn0 : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  let U := (Icc 1 (n - 1)).filter (fun k => k.Coprime n)
  let w : ℕ → ℚ := fun d => (d : ℚ) * (ArithmeticFunction.moebius d : ℚ)
  have hU : (range n).filter (fun k => k.Coprime n) = U := by
    ext k
    simp only [mem_filter, mem_range, U, mem_Icc]
    constructor
    · rintro ⟨hkn, hc⟩
      have hk0 : k ≠ 0 := by
        intro hk
        subst k
        simpa [Nat.coprime_zero_left, hn1] using hc
      exact ⟨⟨by omega, by omega⟩, hc⟩
    · rintro ⟨⟨hk0, hkn⟩, hc⟩
      exact ⟨by omega, hc⟩
  have hcard : U.card = Nat.totient n := by
    rw [← hU]
    simpa only [Nat.coprime_comm] using (Nat.totient_eq_card_coprime n).symm
  have hgcd : (∑ k ∈ range n, w (n.gcd k)) = (ArithmeticFunction.moebius n : ℚ) := by
    rw [← totient_weighted_moebius n]
    have h := D5.S3.Arith.RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity n hn0
      (fun d => ((w d : ℚ) : ℝ))
    apply (Rat.cast_injective (α := ℝ))
    push_cast
    simpa only [w, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, mul_assoc] using h
  have hpoint (k : ℕ) (_hk : k ∈ range n) :
      model n k = w (n.gcd k) - (if k = 0 then w n else 0) +
        if k.Coprime n then model n k - 1 else 0 := by
    by_cases hk0 : k = 0
    · subst k
      simp [model, w, Nat.coprime_zero_left, hn1]
    by_cases hc : k.Coprime n
    · have hg : n.gcd k = 1 := hc.symm
      rw [if_pos hc, if_neg hk0]
      simp only [w, hg, Nat.cast_one, ArithmeticFunction.moebius_apply_one,
        Int.cast_one, mul_one, sub_zero]
      ring
    · have hk1 : k ≠ 1 := by intro hk; simp [hk] at hc
      have hg : 1 < n.gcd k := by
        have hgpos := Nat.gcd_pos_of_pos_left k hn0
        have hg1 : n.gcd k ≠ 1 := by
          intro hg1
          exact hc (by simpa only [Nat.Coprime, Nat.gcd_comm] using hg1)
        omega
      simp [model, w, hk0, hc, hn0.ne', hn1, hk1, hg]
  have hcorrection :
      (∑ k ∈ range n, if k.Coprime n then model n k - 1 else 0) =
        -(ArithmeticFunction.moebius n : ℚ) := by
    rw [← sum_filter, hU, sum_sub_distrib]
    have hc := model_coprime_sum n (by omega)
    change (∑ k ∈ U, model n k) = _ at hc
    rw [hc]
    simp only [sum_const, nsmul_eq_mul, mul_one, hcard]
    ring
  have hzero : (∑ k ∈ range n, if k = 0 then w n else 0) = w n := by
    simp [hn0]
  have hsum := sum_congr rfl hpoint
  simp only [sum_add_distrib, sum_sub_distrib] at hsum
  rw [hgcd, hzero, hcorrection] at hsum
  have hinterval : range n = insert 0 (Icc 1 (n - 1)) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hinterval, sum_insert (by simp), show model n 0 = 0 by simp [model], zero_add] at hsum
  dsimp only [w] at hsum
  linarith

private theorem model_granvikRule (n k : ℕ) :
    model n k = granvikRule model n k := by
  have hdiag (m : ℕ) (hm : 2 ≤ m) :
      model m m = -∑ i ∈ Icc 1 (m - 1), model m i := by
    rw [model_diagonal m hm, model_row_sum m hm]
    ring
  have hborder (m : ℕ) (hm : 3 ≤ m) :
      model m 1 = (-model (m - 1) 1 -
        ∑ i ∈ Icc 2 (m - 1), model m i) / (m + 1) + model (m - 1) 1 := by
    have hsplit : (∑ i ∈ Icc 1 (m - 1), model m i) =
        model m 1 + ∑ i ∈ Icc 2 (m - 1), model m i := by
      simpa only [← Finset.Ico_add_one_right_eq_Icc,
        Nat.sub_add_cancel (by omega : 1 ≤ m)] using
        (Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m) (fun i => model m i))
    have hsum : (∑ i ∈ Icc 2 (m - 1), model m i) =
        -(m : ℚ) * (ArithmeticFunction.moebius m : ℚ) - border m := by
      have hrow := model_row_sum m (by omega : 2 ≤ m)
      rw [hsplit, model_border m (by omega)] at hrow
      linarith
    rw [model_border m (by omega), model_border (m - 1) (by omega), hsum,
      border_step m (by omega)]
    field_simp [show (m : ℚ) + 1 ≠ 0 by positivity]
    ring
  unfold granvikRule
  by_cases hz : n = 0 ∨ k = 0
  · simp only [model, hz, ↓reduceIte, ↓reduceDIte]
  simp only [hz, ↓reduceDIte]
  by_cases hn : n = 1
  · simp only [hn, ↓reduceDIte]
    subst n
    by_cases hk : k ≤ 2
    · simp only [hk, ↓reduceDIte]
      interval_cases k <;>
        norm_num [model, border, show Icc 1 2 = {1, 2} by decide,
          ArithmeticFunction.moebius_apply_prime Nat.prime_two] at *
    · simp only [hk, ↓reduceDIte]
      rw [Finset.sum_attach (Icc 2 (k - 1)) (fun i => model i k)]
      rw [model_symm 1 k, hborder k (by omega), model_symm (k - 1) 1]
      have hs : (∑ i ∈ Icc 2 (k - 1), model k i) =
          ∑ i ∈ Icc 2 (k - 1), model i k := by
        exact Finset.sum_congr rfl (fun i _ => model_symm k i)
      rw [hs]
  · simp only [hn, ↓reduceDIte]
    by_cases hk : k = 1
    · simp only [hk, ↓reduceDIte]
      subst k
      by_cases hn2 : n ≤ 2
      · simp only [hn2, ↓reduceDIte]
        interval_cases n <;>
          norm_num [model, border, show Icc 1 2 = {1, 2} by decide,
            ArithmeticFunction.moebius_apply_prime Nat.prime_two] at *
      · simp only [hn2, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 2 (n - 1)) (fun i => model n i)]
        exact hborder n (by omega)
    · simp only [hk, ↓reduceDIte]
      by_cases hnk : k ≤ n
      · simp only [hnk, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 1 (k - 1)) (fun i => model (n - i) k)]
        exact granvik_interior_of_somos model model_symm model_interior hdiag n k (by omega) hnk
      · simp only [hnk, ↓reduceDIte]
        rw [Finset.sum_attach (Icc 1 (n - 1)) (fun i => model (k - i) n)]
        rw [model_symm n k]
        exact granvik_interior_of_somos model model_symm model_interior hdiag k n
          (by omega) (by omega)

/-- The diagonal is n times the Möbius function, and the first row beyond its
initial cell is two plus the Möbius summatory function. -/
theorem result :
    (∀ n : ℕ, 1 ≤ n → T n n = (n : ℚ) * (ArithmeticFunction.moebius n : ℚ)) ∧
    (∀ k : ℕ, 2 ≤ k → T 1 k =
      2 + ∑ j ∈ Icc 1 k, (ArithmeticFunction.moebius j : ℚ)) := by
  have heq : ∀ n k, T n k = model n k :=
    T_published_unique model model_granvikRule
  constructor
  · intro n hn
    rw [heq n n]
    by_cases hn1 : n = 1
    · subst n
      norm_num [model]
    · exact model_diagonal n (by omega)
  · intro k hk
    rw [heq 1 k, model_symm 1 k, model_border k hk]
    rfl

end D5.S3.Arith.GranvikMertensArray
