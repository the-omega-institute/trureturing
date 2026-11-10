/- GID: D5/S1/Recurrence/Residue/HannaA365771
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA365771
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Base-five digit descent classifies Hanna's residues and proves congruence (1). -/

/-
admission_basis: open-problem-resolution (#18656; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22018
Direct frozen dependencies: none.
The sequence and digit predicate use the source expressions fixed by #18656.
The public digits_step and residue_classification are used by both companion results.
The multinomial product is written inline, without a forwarding definition.
Declaration judgement (consumers named within this family):
a, InA033042, claim: definitions; escape_witness: none.
lucas5: proof_shape: bind-only; consumer: M_step_good, M_step_bad, a_mod_four.
digits_step: proof_shape: bind-only; consumer: M_mod, residue_classification, all results.
M_step_good, M_step_bad: proof_shape: bind-only; consumer: M_mod.
M_mod: proof_shape: content; escape_witness: M_mod; consumer: residue_classification.
catalan_balance: proof_shape: bind-only; consumer: a_balance.
a_balance, a_mod_four: proof_shape: bind-only; consumer: residue_classification.
residue_classification: proof_shape: content; escape_witness: M_mod; consumer: all three results.
result: proof_shape: content; escape_witness: M_mod.
Every bind-only theorem above has escape_witness: none.
All theorem rows have Direct frozen dependencies: none.
The new induction in M_mod is shared by the three settling proofs.
-/

import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false

namespace D5.S1.Recurrence.Residue.HannaA365771

/-- A365771: `a(n) = binomial(2n+1, n)/(2n+1) * binomial(3n-1, n)` (the first factor is a Catalan number, so the
division is exact; `3*0 - 1 = 0` in `ℕ` gives `a(0) = 1`). -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n + 1) n / (2 * n + 1)) * Nat.choose (3 * n - 1) n

/-- Membership in A033042, the sums of distinct powers of 5: all base-5 digits are 0 or 1 (this includes 0). -/
def InA033042 (m : ℕ) : Prop := ∀ d ∈ Nat.digits 5 m, d ≤ 1

/-- A365771 ("(1) a(5*A033042(n)) == 4 (mod 5) for n > 0"). -/
def claim : Prop := ∀ m : ℕ, 0 < m → InA033042 m → a (5 * m) % 5 = 4

end D5.S1.Recurrence.Residue.HannaA365771

namespace D5.S1.Recurrence.Residue.HannaA365771

open scoped Classical

private theorem lucas5 (N K : ℕ) :
    Nat.choose N K % 5 =
      (Nat.choose (N % 5) (K % 5) * Nat.choose (N / 5) (K / 5)) % 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

theorem digits_step (n : ℕ) (hn : 0 < n) :
    InA033042 n ↔ n % 5 ≤ 1 ∧ InA033042 (n / 5) := by
  unfold InA033042
  rw [Nat.digits_def' (by decide : 1 < 5) hn]
  simp only [List.mem_cons, forall_eq_or_imp]

private theorem M_step_good (n : ℕ) (hn : n % 5 ≤ 1) :
    (Nat.choose (3 * n) n * Nat.choose (2 * n) n) % 5 = (Nat.choose (3 * (n / 5)) (n / 5) * Nat.choose (2 * (n / 5)) (n / 5)) % 5 := by
  have h31 : (3 * n) % 5 = 3 * (n % 5) := by omega
  have h32 : (3 * n) / 5 = 3 * (n / 5) := by omega
  have h21 : (2 * n) % 5 = 2 * (n % 5) := by omega
  have h22 : (2 * n) / 5 = 2 * (n / 5) := by omega
  have h3 := lucas5 (3 * n) n
  have h2 := lucas5 (2 * n) n
  rw [h31, h32] at h3
  rw [h21, h22] at h2
  have hd : n % 5 = 0 ∨ n % 5 = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hn
  have hc : Nat.ModEq 5
      (Nat.choose (3 * (n % 5)) (n % 5) * Nat.choose (2 * (n % 5)) (n % 5)) 1 := by
    rcases hd with hd | hd <;> norm_num [hd, Nat.choose, Nat.ModEq]
  change Nat.ModEq 5 ((Nat.choose (3 * n) n * Nat.choose (2 * n) n)) ((Nat.choose (3 * (n / 5)) (n / 5) * Nat.choose (2 * (n / 5)) (n / 5)))
  calc
    (Nat.choose (3 * n) n * Nat.choose (2 * n) n) ≡
        (Nat.choose (3 * (n % 5)) (n % 5) * Nat.choose (3 * (n / 5)) (n / 5)) *
        (Nat.choose (2 * (n % 5)) (n % 5) * Nat.choose (2 * (n / 5)) (n / 5)) [MOD 5] :=
      Nat.ModEq.mul h3 h2
    _ = (Nat.choose (3 * (n % 5)) (n % 5) * Nat.choose (2 * (n % 5)) (n % 5)) *
        (Nat.choose (3 * (n / 5)) (n / 5) * Nat.choose (2 * (n / 5)) (n / 5)) := by ring
    _ ≡ 1 * (Nat.choose (3 * (n / 5)) (n / 5) * Nat.choose (2 * (n / 5)) (n / 5)) [MOD 5] := Nat.ModEq.mul hc (Nat.ModEq.refl _)
    _ = (Nat.choose (3 * (n / 5)) (n / 5) * Nat.choose (2 * (n / 5)) (n / 5)) := one_mul _

private theorem M_step_bad (n : ℕ) (hn : 2 ≤ n % 5) :
    (Nat.choose (3 * n) n * Nat.choose (2 * n) n) % 5 = 0 := by
  have hd : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have h3 := lucas5 (3 * n) n
  have h2 := lucas5 (2 * n) n
  have h31 : (3 * n) % 5 = (3 * (n % 5)) % 5 :=
    (Nat.mul_mod_mod 3 n 5).symm
  have h21 : (2 * n) % 5 = (2 * (n % 5)) % 5 :=
    (Nat.mul_mod_mod 2 n 5).symm
  rw [h31] at h3
  rw [h21] at h2
  interval_cases h : n % 5
  · norm_num [h, Nat.choose] at h3
    simp [Nat.mul_mod, h3]
  · norm_num [h, Nat.choose] at h2
    simp [Nat.mul_mod, h2]
  · norm_num [h, Nat.choose] at h2
    simp [Nat.mul_mod, h2]

private theorem M_mod (n : ℕ) :
    (Nat.choose (3 * n) n * Nat.choose (2 * n) n) % 5 = if InA033042 n then 1 else 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [InA033042, Nat.digits_zero]
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    have hs := digits_step n hp
    by_cases hd : n % 5 ≤ 1
    · rw [M_step_good n hd, ih (n / 5) (Nat.div_lt_self hp (by decide))]
      simp only [hs, hd, true_and]
    · rw [M_step_bad n (by omega)]
      simp only [hs, hd, false_and, ite_false]

private theorem catalan_balance (n : ℕ) :
    (n + 1) * (Nat.choose (2 * n + 1) n / (2 * n + 1)) = Nat.choose (2 * n) n := by
  obtain ⟨c, hc⟩ := Nat.succ_dvd_centralBinom n
  change Nat.choose (2 * n) n = (n + 1) * c at hc
  have hb := Nat.choose_mul_succ_eq (2 * n) n
  rw [show 2 * n + 1 - n = n + 1 by omega, hc] at hb
  have ho : Nat.choose (2 * n + 1) n = (2 * n + 1) * c := by nlinarith
  rw [ho, Nat.mul_div_right _ (by omega), hc]

private theorem a_balance (n : ℕ) (hn : 0 < n) :
    3 * (n + 1) * a n = 2 * (Nat.choose (3 * n) n * Nat.choose (2 * n) n) := by
  have hb : Nat.choose (3 * n - 1) n * (3 * n) =
      Nat.choose (3 * n) n * (2 * n) := by
    simpa only [show 3 * n - 1 + 1 = 3 * n by omega,
      show 3 * n - n = 2 * n by omega] using
      Nat.choose_mul_succ_eq (3 * n - 1) n
  have ht : 3 * Nat.choose (3 * n - 1) n = 2 * Nat.choose (3 * n) n := by nlinarith
  calc
    3 * (n + 1) * a n =
        ((n + 1) * (Nat.choose (2 * n + 1) n / (2 * n + 1))) *
        (3 * Nat.choose (3 * n - 1) n) := by simp only [a]; ring
    _ = 2 * (Nat.choose (3 * n) n * Nat.choose (2 * n) n) := by rw [catalan_balance, ht]; ring

end D5.S1.Recurrence.Residue.HannaA365771

namespace D5.S1.Recurrence.Residue.HannaA365771

open scoped Classical

private theorem a_mod_four (n : ℕ) (hn : n % 5 = 4) : a n % 5 = 0 := by
  have hh : (3 * n - 1) % 5 = 1 := by omega
  have hc := lucas5 (3 * n - 1) n
  rw [hh, hn] at hc
  norm_num [Nat.choose] at hc
  simp [a, Nat.mul_mod, hc]

theorem residue_classification (n : ℕ) (hn : 0 < n) :
    a n % 5 = if InA033042 n then (if n % 5 = 0 then 4 else 2) else 0 := by
  classical
  have hb := congrArg (fun k : ℕ => k % 5) (a_balance n hn)
  have ha : a n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hd : n % 5 < 5 := Nat.mod_lt _ (by decide)
  by_cases hmem : InA033042 n
  · rw [ite_eq_left hmem]
    have hm := (digits_step n hn).mp hmem
    have hM : (Nat.choose (3 * n) n * Nat.choose (2 * n) n) % 5 = 1 := by simpa [hmem] using M_mod n
    rcases (by omega : n % 5 = 0 ∨ n % 5 = 1) with h | h
    · rw [ite_eq_left h]
      simp [Nat.mul_mod, Nat.add_mod, h, hM] at hb
      omega
    · rw [ite_eq_right (by omega : ¬ n % 5 = 0)]
      simp [Nat.mul_mod, Nat.add_mod, h, hM] at hb
      omega
  · rw [ite_eq_right hmem]
    by_cases h4 : n % 5 = 4
    · exact a_mod_four n h4
    have hM : (Nat.choose (3 * n) n * Nat.choose (2 * n) n) % 5 = 0 := by simpa [hmem] using M_mod n
    interval_cases h : n % 5 <;> simp_all [Nat.mul_mod, Nat.add_mod] <;> omega

theorem result : claim := by
  intro m hm hd
  have hi : InA033042 (5 * m) := by
    apply (digits_step (5 * m) (by omega)).mpr
    exact ⟨by omega, by simpa using hd⟩
  simpa [hi] using residue_classification (5 * m) (by omega)

end D5.S1.Recurrence.Residue.HannaA365771
