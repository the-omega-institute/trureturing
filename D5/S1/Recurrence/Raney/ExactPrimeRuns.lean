/- GID: D5/S1/Recurrence/Raney/ExactPrimeRuns
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/ExactPrimeRuns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact prime-at-least-five components of the literal ternary Raney sequence. -/

import D5.S1.Recurrence.Raney.ZeroRunFamilies
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Exact components and record values for primes at least five. -/

namespace TrureTuring.Raney.ExactPrime

open Finset

private theorem factorial_identity (n : ℕ) :
    raneyNumber 3 1 n * n.factorial * (2 * n + 1).factorial = (3 * n).factorial := by
  have cross : (3 * n + 1) * raneyNumber 3 1 n = Nat.choose (3 * n + 1) n := by
    cases n with
    | zero => simp [raneyNumber]
    | succ n =>
      let N := 3 * (n + 1) + 1
      let C := Nat.choose N (n + 1)
      let D := Nat.choose (3 * (n + 1)) (n + 1)
      let B := Nat.choose (3 * (n + 1)) n
      have hN : 0 < N := by dsimp [N]; omega
      have hP : N * B = C * (n + 1) := by
        simpa [N, B, C] using Nat.add_one_mul_choose_eq (3 * (n + 1)) n
      have hD : D * N = C * (2 * (n + 1) + 1) := by
        simpa [N, D, C, show 3 * (n + 1) + 1 - (n + 1) = 2 * (n + 1) + 1 by omega]
          using Nat.choose_mul_succ_eq (3 * (n + 1)) (n + 1)
      have hDecomp : D * N = (2 * B) * N + C := by
        calc
          D * N = C * (2 * (n + 1) + 1) := hD
          _ = 2 * (C * (n + 1)) + C := by ring
          _ = (2 * B) * N + C := by rw [← hP]; ring
      have hLe : 2 * B ≤ D := by
        exact Nat.le_of_mul_le_mul_right (by omega : 2 * B * N ≤ D * N) hN
      have hCross : N * (D - 2 * B) = C := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_comm N D, Nat.mul_comm N (2 * B)]
        omega
      have hQuot : C / N = D - 2 * B := by
        rw [← hCross, Nat.mul_div_right _ hN]
      simpa only [raneyNumber, one_mul] using (show N * (C / N) = C by rw [hQuot, hCross])
  have hc := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n + 1 by omega)
  rw [show 3 * n + 1 - n = 2 * n + 1 by omega, ← cross,
    Nat.factorial_succ] at hc
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 * n + 1 by omega)
  calc
    (3 * n + 1) * (raneyNumber 3 1 n * n.factorial * (2 * n + 1).factorial) =
        (3 * n + 1) * raneyNumber 3 1 n * n.factorial * (2 * n + 1).factorial := by ring
    _ = (3 * n + 1) * (3 * n).factorial := hc

private theorem raney_pos (n : ℕ) : 0 < raneyNumber 3 1 n := by
  have h := factorial_identity n
  have hf := Nat.factorial_pos (3 * n)
  by_contra hh
  have hz : raneyNumber 3 1 n = 0 := by omega
  simp [hz] at h
  omega

/-- One Legendre summand, evaluated on the residue at its scale. -/
private def charge (q x : ℕ) : ℕ := (3 * x) / q - (2 * x + 1) / q

private theorem charge_bounds (q x : ℕ) (hq : 2 ≤ q) (hx : x < q) :
    (2 * x + 1) / q ≤ (3 * x) / q ∧ charge q x ≤ 1 := by
  by_cases hz : x = 0
  · subst x
    simp [charge, Nat.div_eq_of_lt (by omega : 1 < q)]
  · have h₁ := Nat.div_le_div_right (show 2 * x + 1 ≤ 3 * x by omega) (c := q)
    have h₂ : 3 * x < (2 * x + 1) + q := by omega
    have h₃ := Nat.div_le_div_right (Nat.le_of_lt h₂) (c := q)
    rw [Nat.add_div_right _ (by omega : 0 < q)] at h₃
    dsimp [charge]
    omega

private theorem quotient_decomp (q n : ℕ) (hq : 2 ≤ q) :
    (3 * n) / q = n / q + (2 * n + 1) / q + charge q (n % q) := by
  have hq0 : 0 < q := by omega
  have hn := Nat.mod_add_div n q
  have h3 : 3 * n = 3 * (n % q) + q * (3 * (n / q)) := by nlinarith [hn]
  have h2 : 2 * n + 1 = (2 * (n % q) + 1) + q * (2 * (n / q)) := by nlinarith [hn]
  rw [h3, h2, Nat.add_mul_div_left _ _ hq0, Nat.add_mul_div_left _ _ hq0]
  have hb := charge_bounds q (n % q) hq (Nat.mod_lt _ hq0)
  dsimp [charge]
  omega

private theorem valuation_formula (p n b : ℕ) (hp : p.Prime)
    (hb : Nat.log p (3 * n + 1) < b) :
    padicValNat p (raneyNumber 3 1 n) =
      ∑ h ∈ Ico 1 b, charge (p ^ h) (n % p ^ h) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpos := (raney_pos n).ne'
  have hval := congrArg (padicValNat p) (factorial_identity n)
  rw [padicValNat.mul (Nat.mul_ne_zero hpos (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), padicValNat.mul hpos (Nat.factorial_ne_zero _)] at hval
  have bound (k : ℕ) (hk : k ≤ 3 * n + 1) : Nat.log p k < b :=
    (Nat.log_mono_right hk).trans_lt hb
  rw [padicValNat_factorial (p := p) (bound n (by omega)),
    padicValNat_factorial (p := p) (bound (2 * n + 1) (by omega)),
    padicValNat_factorial (p := p) (bound (3 * n) (by omega))] at hval
  have hsum : (∑ h ∈ Ico 1 b, (3 * n) / p ^ h) =
      (∑ h ∈ Ico 1 b, n / p ^ h) + (∑ h ∈ Ico 1 b, (2 * n + 1) / p ^ h) +
        ∑ h ∈ Ico 1 b, charge (p ^ h) (n % p ^ h) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro h hh
    apply quotient_decomp
    have hh1 := (mem_Ico.mp hh).1
    exact (hp.two_le.trans (Nat.le_self_pow (by omega : h ≠ 0) p))
  omega

private theorem zero_iff_charge (p n : ℕ) (hp : p.Prime) :
    (raneyNumber 3 1 n : ZMod p) = 0 ↔
      ∃ h : ℕ, 1 ≤ h ∧ charge (p ^ h) (n % p ^ h) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [ZMod.natCast_eq_zero_iff, dvd_iff_padicValNat_ne_zero (raney_pos n).ne']
  let b := Nat.log p (3 * n + 1) + 1
  rw [valuation_formula p n b hp (by dsimp [b]; omega)]
  constructor
  · intro hs
    have hh : ∃ h ∈ Ico 1 b, charge (p ^ h) (n % p ^ h) ≠ 0 := by
      by_contra hx
      push Not at hx
      exact hs (sum_eq_zero hx)
    obtain ⟨h, hh, hc⟩ := hh
    have hb := charge_bounds (p ^ h) (n % p ^ h)
      (hp.two_le.trans (Nat.le_self_pow (by have := (mem_Ico.mp hh).1; omega) p))
      (Nat.mod_lt _ (pow_pos hp.pos _))
    exact ⟨h, (mem_Ico.mp hh).1, by omega⟩
  · rintro ⟨h, hh, hc⟩
    have hlt : h < b := by
      by_contra hx
      have hlog : Nat.log p (3 * n + 1) < h := by dsimp [b] at hx; omega
      have hpow : 3 * n + 1 < p ^ h := (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).mp hlog
      have hn : n < p ^ h := by omega
      rw [Nat.mod_eq_of_lt hn] at hc
      simp [charge, Nat.div_eq_of_lt (by omega : 3 * n < p ^ h),
        Nat.div_eq_of_lt (by omega : 2 * n + 1 < p ^ h)] at hc
    have hone := single_le_sum (f := fun h => charge (p ^ h) (n % p ^ h))
      (fun h _ => Nat.zero_le _) (mem_Ico.mpr ⟨hh, hlt⟩)
    omega

private theorem charge_iff (q x : ℕ) (hq : 2 ≤ q) (hx : x < q) :
    charge q x = 1 ↔
      (q ≤ 3 * x ∧ 2 * x + 1 < q) ∨ (2 * q ≤ 3 * x ∧ 2 * x + 1 < 2 * q) := by
  have hq0 : 0 < q := by omega
  have ha : (3 * x) / q < 3 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
  have hb : (2 * x + 1) / q < 3 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
  have h₁ := Nat.div_add_mod (3 * x) q
  have h₂ := Nat.div_add_mod (2 * x + 1) q
  have h₃ := Nat.mod_lt (3 * x) hq0
  have h₄ := Nat.mod_lt (2 * x + 1) hq0
  generalize ha' : (3 * x) / q = a at *
  generalize hb' : (2 * x + 1) / q = b at *
  dsimp [charge]
  rw [ha', hb']
  interval_cases a <;> interval_cases b <;> simp_all <;> omega

private theorem charge_left_boundary (P n s : ℕ) (hP : 5 ≤ P)
    (hs : 1 ≤ s ∧ s ≤ 2) (hd : P ∣ 3 * n + s) :
    charge P (n % P) = 0 := by
  have hP0 : 0 < P := by omega
  let x := n % P
  have hx : x < P := Nat.mod_lt _ hP0
  have hmod : (3 * x + s) % P = 0 := by
    simpa [x, Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_zero_of_dvd hd
  obtain ⟨e, he⟩ := Nat.dvd_of_mod_eq_zero hmod
  have he0 : 1 ≤ e := by nlinarith
  have he2 : e ≤ 2 := by nlinarith
  have hb := charge_bounds P x (by omega) hx
  by_contra hh
  have hc : charge P x = 1 := by dsimp [x] at *; omega
  rcases (charge_iff P x (by omega) hx).mp hc with hc | hc
  · interval_cases e <;> simp_all <;> omega
  · interval_cases e <;> simp_all <;> omega

private theorem charge_right_boundary (P n : ℕ) (hP : 5 ≤ P)
    (hd : P ∣ 2 * n + 1) : charge P (n % P) = 0 := by
  have hP0 : 0 < P := by omega
  let x := n % P
  have hx : x < P := Nat.mod_lt _ hP0
  have hmod : (2 * x + 1) % P = 0 := by
    simpa [x, Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_zero_of_dvd hd
  obtain ⟨e, he⟩ := Nat.dvd_of_mod_eq_zero hmod
  have he1 : e = 1 := by nlinarith
  subst e
  have hb := charge_bounds P x (by omega) hx
  by_contra hh
  have hc : charge P x = 1 := by dsimp [x] at *; omega
  rcases (charge_iff P x (by omega) hx).mp hc with hc | hc <;> omega

private def first (q j : ℕ) : ℕ := (j * q + 2) / 3
private def last (q j : ℕ) : ℕ := if j = 1 then (q - 3) / 2 else q - 1

private theorem scale_residues (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ^ m % 2 = 1 ∧ p ^ m % 3 ≠ 0 := by
  have h2 := hp.eq_two_or_odd.resolve_left (by omega)
  have h3 : ¬ 3 ∣ p := by
    intro hh
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hh
    omega
  constructor
  · simp [Nat.pow_mod, h2]
  · intro hh
    exact h3 (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hh))

private theorem endpoints (q j : ℕ) (hq : 5 ≤ q) (h2 : q % 2 = 1)
    (h3 : q % 3 ≠ 0) (hj : j = 1 ∨ j = 2) :
    1 ≤ first q j ∧ last q j < q ∧ last q j + 1 ≤ q ∧
    (∃ s, 1 ≤ s ∧ s ≤ 2 ∧ 3 * (first q j - 1) + s = j * q) ∧
    (j = 1 → 2 * (last q j + 1) + 1 = q) ∧
    (j = 2 → last q j + 1 = q) := by
  rcases hj with rfl | rfl <;> dsimp [first, last]
  · refine ⟨by omega, by omega, by omega, ?_, by omega, by omega⟩
    by_cases hr : q % 3 = 1
    · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨2, by omega, by omega, by omega⟩
  · refine ⟨by omega, by omega, by omega, ?_, by omega, by omega⟩
    by_cases hr : q % 3 = 1
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, by omega⟩

private theorem charge_interval (q x : ℕ) (hq : 5 ≤ q) (h2 : q % 2 = 1)
    (hx : x < q) :
    charge q x = 1 ↔ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ first q j ≤ x ∧ x ≤ last q j := by
  rw [charge_iff q x (by omega) hx]
  constructor
  · rintro (h | h)
    · exact ⟨1, Or.inl rfl, by dsimp [first]; omega, by dsimp [last]; omega⟩
    · exact ⟨2, Or.inr rfl, by dsimp [first]; omega, by dsimp [last]; omega⟩
  · rintro ⟨j, hj, ha, hb⟩
    rcases hj with rfl | rfl
    · left; dsimp [first, last] at *; omega
    · right; dsimp [first, last] at *; omega

private theorem high_charge (p m n h : ℕ) (hp : 5 ≤ p)
    (hn : n ≤ p ^ m) (hh : m < h) : charge (p ^ h) (n % p ^ h) = 0 := by
  have hp0 : 0 < p := by omega
  have hq0 := pow_pos hp0 m
  have hpow := Nat.pow_le_pow_right hp0 (Nat.succ_le_of_lt hh)
  rw [pow_succ] at hpow
  have hb : 3 * n + 1 < p ^ h := by nlinarith
  have hn' : n < p ^ h := by omega
  simp [charge, Nat.mod_eq_of_lt hn', Nat.div_eq_of_lt (by omega : 3 * n < p ^ h),
    Nat.div_eq_of_lt (by omega : 2 * n + 1 < p ^ h)]

private theorem zero_upto (p m n : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : n ≤ p ^ m) :
    (raneyNumber 3 1 n : ZMod p) = 0 ↔
      ∃ h, 1 ≤ h ∧ h ≤ m ∧ charge (p ^ h) (n % p ^ h) = 1 := by
  rw [zero_iff_charge p n hp]
  constructor
  · rintro ⟨h, hh, hc⟩
    refine ⟨h, hh, ?_, hc⟩
    by_contra hx
    have := high_charge p m n h hp5 hn (by omega)
    omega
  · rintro ⟨h, hh, _, hc⟩
    exact ⟨h, hh, hc⟩

private theorem boundaries_nonzero (p m j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hj : j = 1 ∨ j = 2) :
    (raneyNumber 3 1 (first (p ^ m) j - 1) : ZMod p) ≠ 0 ∧
      (raneyNumber 3 1 (last (p ^ m) j + 1) : ZMod p) ≠ 0 := by
  have hq : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow (by omega) _)
  obtain ⟨h2, h3⟩ := scale_residues p m hp hp5
  obtain ⟨ha, hb, hbq, ⟨s, hs1, hs2, hseq⟩, he1, he2⟩ := endpoints (p ^ m) j hq h2 h3 hj
  have haq : first (p ^ m) j - 1 ≤ p ^ m := by
    dsimp [first]
    rcases hj with rfl | rfl <;> omega
  constructor
  · intro hz
    obtain ⟨h, hh, hhm, hc⟩ := (zero_upto p m _ hp hp5 haq).mp hz
    have hP : 5 ≤ p ^ h := hp5.trans (Nat.le_self_pow (by omega) _)
    have hd : p ^ h ∣ 3 * (first (p ^ m) j - 1) + s := by
      rw [hseq]
      exact dvd_mul_of_dvd_right (pow_dvd_pow p hhm) j
    have := charge_left_boundary (p ^ h) (first (p ^ m) j - 1) s hP ⟨hs1, hs2⟩ hd
    omega
  · intro hz
    obtain ⟨h, hh, hhm, hc⟩ := (zero_upto p m _ hp hp5 hbq).mp hz
    have hP : 5 ≤ p ^ h := hp5.trans (Nat.le_self_pow (by omega) _)
    rcases hj with hj | hj
    · have hd : p ^ h ∣ 2 * (last (p ^ m) j + 1) + 1 := by
        rw [he1 hj]
        exact pow_dvd_pow p hhm
      have := charge_right_boundary (p ^ h) (last (p ^ m) j + 1) hP hd
      omega
    · rw [he2 hj, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hhm)] at hc
      simp [charge, Nat.div_eq_of_lt (by omega : 1 < p ^ h)] at hc

private theorem interval_actual (p m j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hj : j = 1 ∨ j = 2)
    (hne : first (p ^ m) j ≤ last (p ^ m) j) :
    IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p))
      (first (p ^ m) j) (last (p ^ m) j) := by
  have hq : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow (by omega) _)
  obtain ⟨h2, h3⟩ := scale_residues p m hp hp5
  have he := endpoints (p ^ m) j hq h2 h3 hj
  have hb := boundaries_nonzero p m j hp hp5 hm hj
  simp only [IsMaximalDeltaInterval, mem_singleton]
  refine ⟨hne, ?_, Or.inr hb.1, hb.2⟩
  intro n ha hn
  apply (zero_iff_charge p n hp).mpr
  refine ⟨m, hm, ?_⟩
  have hnq : n < p ^ m := hn.trans_lt he.2.1
  rw [Nat.mod_eq_of_lt hnq]
  exact (charge_interval (p ^ m) n hq h2 hnq).mpr ⟨j, hj, ha, hn⟩

private theorem maximal_overlap (p a b c d n : ℕ)
    (hab : IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b)
    (hcd : IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) c d)
    (han : a ≤ n) (hnb : n ≤ b) (hcn : c ≤ n) (hnd : n ≤ d) : a = c ∧ b = d := by
  simp only [IsMaximalDeltaInterval, mem_singleton] at hab hcd
  obtain ⟨hab, hin, hl, hr⟩ := hab
  obtain ⟨hcd, hinc, hlc, hrc⟩ := hcd
  have hac : a = c := by
    rcases le_total a c with hh | hh
    · by_contra heq
      have hc0 : c ≠ 0 := by omega
      exact (hlc.resolve_left hc0) (hin (c - 1) (by omega) (by omega))
    · by_contra heq
      have ha0 : a ≠ 0 := by omega
      exact (hl.resolve_left ha0) (hinc (a - 1) (by omega) (by omega))
  refine ⟨hac, ?_⟩
  rcases le_total b d with hh | hh
  · by_contra heq
    exact hr (hinc (b + 1) (by omega) (by omega))
  · by_contra heq
    exact hrc (hin (d + 1) (by omega) (by omega))

private theorem lower_zero_lift (p m n : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hz : (raneyNumber 3 1 (n % p ^ m) : ZMod p) = 0) :
    (raneyNumber 3 1 n : ZMod p) = 0 := by
  obtain ⟨h, hh, hhm, hc⟩ := (zero_upto p m _ hp hp5
    (Nat.le_of_lt (Nat.mod_lt _ (pow_pos hp.pos _)))).mp hz
  apply (zero_iff_charge p n hp).mpr
  refine ⟨h, hh, ?_⟩
  rwa [Nat.mod_mod_of_dvd n (pow_dvd_pow p hhm)] at hc

private theorem power_nonzero (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (raneyNumber 3 1 (p ^ m) : ZMod p) ≠ 0 := by
  intro hz
  obtain ⟨h, hh, hhm, hc⟩ := (zero_upto p m _ hp hp5 le_rfl).mp hz
  rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hhm)] at hc
  have hP : 2 ≤ p ^ h := hp.two_le.trans (Nat.le_self_pow (by omega) _)
  simp [charge, Nat.div_eq_of_lt (by omega : 1 < p ^ h)] at hc

/-- Each actual component in a prime-power prefix retains one scale length;
its start is at least the first unshifted interval with that length. -/
private theorem prefix_components (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ a b : ℕ,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b →
      b < p ^ m → ∃ h j : ℕ, 1 ≤ h ∧ h ≤ m ∧ (j = 1 ∨ j = 2) ∧
        first (p ^ h) j ≤ last (p ^ h) j ∧ first (p ^ h) j ≤ a ∧
        b + 1 - a = last (p ^ h) j + 1 - first (p ^ h) j := by
  induction m with
  | zero =>
    intro a b hab hb
    have ha := hab.1
    have hz := hab.2.1 a le_rfl ha
    have ha0 : a = 0 := by simpa using (show a < 1 by simpa using ha.trans_lt hb)
    subst a
    simp only [mem_singleton] at hz
    have : (raneyNumber 3 1 0 : ZMod p) ≠ 0 := by
      intro hz
      exact hp.not_dvd_one (by simpa [raneyNumber] using (ZMod.natCast_eq_zero_iff _ p).mp hz)
    exact (this hz).elim
  | succ m ih =>
    intro a b hab hb
    have hab' := hab
    simp only [IsMaximalDeltaInterval, mem_singleton] at hab'
    obtain ⟨habOrder, habIn, habLeft, habRight⟩ := hab'
    let q := p ^ (m + 1)
    let Q := p ^ m
    have hQ : 0 < Q := pow_pos hp.pos _
    have hq : 5 ≤ q := hp5.trans (Nat.le_self_pow (by omega) _)
    have hq2 := (scale_residues p (m + 1) hp hp5).1
    by_cases hmeet : ∃ j n : ℕ, (j = 1 ∨ j = 2) ∧ a ≤ n ∧ n ≤ b ∧
        first q j ≤ n ∧ n ≤ last q j
    · obtain ⟨j, n, hj, han, hnb, hfn, hnl⟩ := hmeet
      have hne : first q j ≤ last q j := hfn.trans hnl
      have heq := maximal_overlap p a b (first q j) (last q j) n hab
        (interval_actual p (m + 1) j hp hp5 (by omega) hj hne) han hnb hfn hnl
      exact ⟨m + 1, j, by omega, le_rfl, hj, hne, heq.1.ge, by rw [heq.1, heq.2]⟩
    · have noTop (n : ℕ) (han : a ≤ n) (hnb : n ≤ b) : charge q n = 0 := by
        have hnq : n < q := hnb.trans_lt hb
        have hc := charge_bounds q n (by omega) hnq
        by_contra hx
        obtain ⟨j, hj, hf, hl⟩ := (charge_interval q n hq hq2 hnq).mp (by omega)
        exact hmeet ⟨j, n, hj, han, hnb, hf, hl⟩
      have lower (n : ℕ) (han : a ≤ n) (hnb : n ≤ b) :
          (raneyNumber 3 1 (n % Q) : ZMod p) = 0 := by
        obtain ⟨h, hh, hhm, hc⟩ := (zero_upto p (m + 1) n hp hp5
          (Nat.le_of_lt (hnb.trans_lt hb))).mp (habIn n han hnb)
        have hle : h ≤ m := by
          by_contra hx
          have heq : h = m + 1 := by omega
          subst h
          have hnq : n < q := hnb.trans_lt hb
          rw [Nat.mod_eq_of_lt hnq] at hc
          have hnz := noTop n han hnb
          rw [hnz] at hc
          omega
        apply (zero_iff_charge p (n % Q) hp).mpr
        refine ⟨h, hh, ?_⟩
        change charge (p ^ h) ((n % p ^ m) % p ^ h) = 1
        rwa [Nat.mod_mod_of_dvd n (pow_dvd_pow p hle)]
      let t := a / Q
      let r := a % Q
      let s := b % Q
      have hr : r < Q := Nat.mod_lt _ hQ
      have hs : s < Q := Nat.mod_lt _ hQ
      have haEq : a = Q * t + r := by simpa [t, r] using (Nat.div_add_mod a Q).symm
      have hdiv : b / Q = t := by
        have hle : t ≤ b / Q := Nat.div_le_div_right habOrder
        by_contra hx
        have ht : t + 1 ≤ b / Q := by omega
        have hmul := Nat.mul_le_mul_left Q ht
        have hbMul := Nat.div_mul_le_self b Q
        have han : a ≤ Q * (t + 1) := by nlinarith
        have hnb : Q * (t + 1) ≤ b := by nlinarith
        have hz := lower (Q * (t + 1)) han hnb
        rw [Nat.mul_mod_right] at hz
        have hz0 : (raneyNumber 3 1 0 : ZMod p) ≠ 0 := by
          intro hz
          exact hp.not_dvd_one (by simpa [raneyNumber] using (ZMod.natCast_eq_zero_iff _ p).mp hz)
        exact hz0 hz
      have hbEq : b = Q * t + s := by
        have := (Nat.div_add_mod b Q).symm
        rwa [hdiv] at this
      have hrs : r ≤ s := by omega
      have hr0 : 0 < r := by
        by_contra hx
        have hz := lower a le_rfl habOrder
        have hrz : r = 0 := by omega
        change (raneyNumber 3 1 r : ZMod p) = 0 at hz
        rw [hrz, ZMod.natCast_eq_zero_iff] at hz
        simpa [raneyNumber] using (hp.not_dvd_one hz)
      have small : IsMaximalDeltaInterval {0}
          (fun n => (raneyNumber 3 1 n : ZMod p)) r s := by
        simp only [IsMaximalDeltaInterval, mem_singleton]
        refine ⟨hrs, ?_, Or.inr ?_, ?_⟩
        · intro n hrn hns
          have hnQ : n < Q := hns.trans_lt hs
          have hz := lower (Q * t + n) (by omega) (by omega)
          simpa [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hnQ] using hz
        · intro hz
          have hpred : (a - 1) % Q = r - 1 := by
            have heq : a - 1 = Q * t + (r - 1) := by omega
            rw [heq]
            simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt (by omega : r - 1 < Q)]
          have hz' : (raneyNumber 3 1 ((a - 1) % p ^ m) : ZMod p) = 0 := by
            change (raneyNumber 3 1 ((a - 1) % Q) : ZMod p) = 0
            rwa [hpred]
          have ha0 : a ≠ 0 := by omega
          exact (habLeft.resolve_left ha0) (lower_zero_lift p m (a - 1) hp hp5 hz')
        · by_cases hsQ : s + 1 < Q
          · intro hz
            have hsucc : (b + 1) % Q = s + 1 := by
              rw [show b + 1 = Q * t + (s + 1) by omega]
              simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hsQ]
            have hz' : (raneyNumber 3 1 ((b + 1) % p ^ m) : ZMod p) = 0 := by
              change (raneyNumber 3 1 ((b + 1) % Q) : ZMod p) = 0
              rwa [hsucc]
            exact habRight (lower_zero_lift p m (b + 1) hp hp5 hz')
          · have heq : s + 1 = p ^ m := by change s + 1 = Q; omega
            rw [heq]
            exact power_nonzero p m hp hp5
      obtain ⟨h, j, hh, hhm, hj, hne, hstart, hlen⟩ := ih r s small hs
      refine ⟨h, j, hh, by omega, hj, hne, ?_, ?_⟩
      · exact hstart.trans (by omega)
      · omega

private theorem interval_arithmetic (q j : ℕ) (hq : 5 ≤ q) (h2 : q % 2 = 1)
    (h3 : q % 3 ≠ 0) (hj : j = 1 ∨ j = 2) :
    (first q j ≤ last q j ↔ j = 2 ∨ (q ≠ 5 ∧ q ≠ 7)) ∧
    last q j + 1 - first q j =
      if j = 1 then (if q % 6 = 1 then (q - 7) / 6 else (q - 5) / 6) else q / 3 := by
  have h6 : q % 6 = 1 ∨ q % 6 = 5 := by omega
  rcases hj with rfl | rfl <;> dsimp [first, last]
  · rcases h6 with h6 | h6 <;> simp only [h6] <;> norm_num <;> omega
  · omega

private theorem order_same (q : ℕ) (hq : 5 ≤ q) :
    first q 1 < first q 2 ∧
      last q 1 + 1 - first q 1 < last q 2 + 1 - first q 2 := by
  dsimp [first, last]
  omega

private theorem order_across (Q q j k : ℕ) (hQ : 5 ≤ Q) (hq : 5 * Q ≤ q)
    (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) :
    first Q j < first q k ∧
      last Q j + 1 - first Q j < last q k + 1 - first q k := by
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> dsimp [first, last] <;> omega

private theorem scale_growth (p h m : ℕ) (hp5 : 5 ≤ p) (hhm : h < m) :
    5 * p ^ h ≤ p ^ m := by
  have hp0 : 0 < p := by omega
  have hg := Nat.pow_le_pow_right hp0 (Nat.succ_le_of_lt hhm)
  rw [pow_succ] at hg
  have hmul : 5 * p ^ h ≤ p ^ h * p := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (p ^ h) hp5
  exact hmul.trans hg

private theorem earlier_shorter (p m j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hj : j = 1 ∨ j = 2)
    (hne : first (p ^ m) j ≤ last (p ^ m) j) :
    ∀ a b : ℕ,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b →
      a < first (p ^ m) j →
      b + 1 - a < last (p ^ m) j + 1 - first (p ^ m) j := by
  intro a b hab ha
  have target := interval_actual p m j hp hp5 hm hj hne
  have hb : b < first (p ^ m) j := by
    by_contra hx
    have heq := maximal_overlap p a b (first (p ^ m) j) (last (p ^ m) j)
      (first (p ^ m) j) hab target (by omega) (by omega) le_rfl hne
    omega
  have hq : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow (by omega) _)
  have he := endpoints (p ^ m) j hq (scale_residues p m hp hp5).1
    (scale_residues p m hp hp5).2 hj
  obtain ⟨h, k, hh, hhm, hk, hkne, hka, hlen⟩ := prefix_components p m hp hp5 a b hab
    (hb.trans_le (hne.trans (Nat.le_of_lt he.2.1)))
  rw [hlen]
  rcases lt_or_eq_of_le hhm with hlt | rfl
  · exact (order_across (p ^ h) (p ^ m) k j
      (hp5.trans (Nat.le_self_pow (by omega) _)) (scale_growth p h m hp5 hlt) hk hj).2
  · have hord := order_same (p ^ h) hq
    rcases hk with rfl | rfl <;> rcases hj with rfl | rfl
    · omega
    · exact hord.2
    · omega
    · omega

/-- The prime-at-least-five branch of the exact R31 run and record spectrum.
The displayed nonempty intervals are actual maximal runs and are strictly
longer than every earlier run. Every maximal run has one of their lengths,
and the lengths strictly increase in exponent-then-interval order. -/
theorem raney_prime_ge_five_spectrum (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, (j = 1 ∨ j = 2) →
      let q := p ^ m
      let a := (j * q + 2) / 3
      let b := if j = 1 then (q - 3) / 2 else q - 1
      (a ≤ b ↔ j = 2 ∨ (q ≠ 5 ∧ q ≠ 7)) ∧
      b + 1 - a =
        (if j = 1 then (if q % 6 = 1 then (q - 7) / 6 else (q - 5) / 6) else q / 3) ∧
      (a ≤ b →
        IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b ∧
        ∀ c d : ℕ,
          IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) c d →
          c < a → d + 1 - c < b + 1 - a)) ∧
    (∀ a b : ℕ,
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b →
      ∃ m j : ℕ, 1 ≤ m ∧ (j = 1 ∨ j = 2) ∧
        let q := p ^ m
        let c := (j * q + 2) / 3
        let d := if j = 1 then (q - 3) / 2 else q - 1
        c ≤ d ∧ b + 1 - a = d + 1 - c) ∧
    (∀ m h j k : ℕ, 1 ≤ m → 1 ≤ h → (j = 1 ∨ j = 2) → (k = 1 ∨ k = 2) →
      (m < h ∨ (m = h ∧ j < k)) →
      (if j = 1 then (p ^ m - 3) / 2 else p ^ m - 1) + 1 - (j * p ^ m + 2) / 3 <
        (if k = 1 then (p ^ h - 3) / 2 else p ^ h - 1) + 1 - (k * p ^ h + 2) / 3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm j hj
    change (first (p ^ m) j ≤ last (p ^ m) j ↔ _) ∧
      last (p ^ m) j + 1 - first (p ^ m) j = _ ∧ _
    have hq : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow (by omega) _)
    have he := interval_arithmetic (p ^ m) j hq (scale_residues p m hp hp5).1
      (scale_residues p m hp hp5).2 hj
    refine ⟨he.1, he.2, ?_⟩
    intro hne
    exact ⟨interval_actual p m j hp hp5 hm hj hne, earlier_shorter p m j hp hp5 hm hj hne⟩
  · intro a b hab
    have hb : b < p ^ (b + 1) :=
      (Nat.lt_succ_self b).trans (Nat.lt_pow_self hp.one_lt)
    obtain ⟨m, j, hm, _, hj, hne, _, hlen⟩ := prefix_components p (b + 1) hp hp5 a b hab hb
    exact ⟨m, j, hm, hj, hne, hlen⟩
  · intro m h j k hm hh hj hk horder
    change last (p ^ m) j + 1 - first (p ^ m) j < last (p ^ h) k + 1 - first (p ^ h) k
    have hq : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow (by omega) _)
    rcases horder with hlt | ⟨rfl, hjk⟩
    · exact (order_across (p ^ m) (p ^ h) j k hq (scale_growth p m h hp5 hlt) hj hk).2
    · have hord := order_same (p ^ m) hq
      rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> first | omega | exact hord.2

#print axioms raney_prime_ge_five_spectrum

end TrureTuring.Raney.ExactPrime
