/- GID: D5/S1/Recurrence/Algebraic/HannaA181070Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181070Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's OEIS A181070 formal exponential. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22220; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22605
The claim expands IntegralSeries with its literal quantifiers; proofs use the existing predicate.
Utility is none: all coefficient, divisibility and congruence statements are unbounded.
Direct frozen dependencies (declaration identities):
A: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.integral_exp_of_dold
   GID: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   statement_id: ASSUMED-UNVERIFIED (not present in the available Lean report)
B: D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.logInput
   GID: D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality
   statement_id: ASSUMED-UNVERIFIED (not present in the available Lean report)
C: D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
   GID: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
   statement_id: sha256:63e70f464749e368856bfaa91133b0adfeda478327572310319dbf6077b632cb
D: D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
   GID: D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
   statement_id: sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
E: D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff
   GID: D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators
   statement_id: sha256:8c1882146ae6e181a5d76db021c447d3d876e2310da5375697c52f0bb35ef4a1
F: D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform.coeff_one_add_pow
   GID: D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform
   statement_id: ASSUMED-UNVERIFIED (public declaration identity awaits the scoped report)
Declaration inventory: name | proof_shape | consumers | Direct frozen dependencies.
Every theorem below has escape_witness: none.
logarithm | definition | A, result | none
A | definition | claim, result | none
claim | definition (Prop-valued predicate, not a proof) | result | none
coeffLiftBase | bind-only | coeffLift | E, D
coeffLift | bind-only | binomCong, HannaA181074Integrality.negbinomCong | E, D
variableExponent | bind-only | cong70, HannaA181074Integrality.cong74, HannaA181080Integrality.cong80 | none
term | definition | c, termIdentity, termOff, termPair, cDold, logIdentification | none
c | definition | cDold, logIdentification, integralGeneric | none
L | definition | logIdentification, integralGeneric, literalUnbounded, literalBounded, result, HannaA181074Integrality.result, HannaA181080Integrality.result | none
termIdentity | bind-only | termOff, termPair, logIdentification | none
valuationTransfer | bind-only | termPair | none
unitCancel | bind-only | termOff | none
termOff | bind-only | cDold | none
termPair | bind-only | cDold | none
cDold | bind-only | integralGeneric | none
logIdentification | bind-only | integralGeneric | B
integralGeneric | bind-only | result, HannaA181074Integrality.result, HannaA181080Integrality.result | C, B, A
binomDiv | bind-only | cong70, result, HannaA181080Integrality.cong80, HannaA181080Integrality.result | F
binomCong | bind-only | cong70, HannaA181080Integrality.cong80 | E, D, F
F70 | definition | cong70, result | none
divPower | bind-only | result, HannaA181074Integrality.result, HannaA181080Integrality.result | none
cong70 | bind-only | result | E, D, F
literalUnbounded | bind-only | literalBounded, HannaA181074Integrality.result | none
literalBounded | bind-only | result, HannaA181080Integrality.result | none
result | bind-only | settling result | C, B, A, E, D, F
coefficientDivisibility | bind-only | binomDiv, HannaA181074Integrality.negbinomDiv | none
-/

import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform
import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import Mathlib.NumberTheory.Basic

open Finset PowerSeries
open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
namespace D5.S1.Recurrence.Algebraic.HannaA181070Integrality

open Finset PowerSeries

/-- The literal rational logarithm in the NAME of OEIS A181070.
At degree m, only 1 <= n <= m and 0 <= k <= m can contribute. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        if 0 < n ∧ n + k = m then
          ((n.choose k : ℕ) : ℚ) ^ (k + 1) / (n : ℚ)
        else 0

/-- The source exponential, using the same Mathlib substitution and exp
as DoldExponentialIntegrality.integral_exp_of_dold. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- The source integrality assertion, with IntegralSeries's quantifiers expanded. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private theorem coeffLiftBase (U : PowerSeries ℤ) (p : ℕ) (hp : p.Prime) :
    C (p : ℤ) ∣ U^p - expand p hp.ne_zero U := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff _ _).mpr
  intro k
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hf := (D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst
    p (U.map (Int.castRingHom (ZMod p)))).trans
      (PowerSeries.expand_apply p hp.ne_zero (U.map (Int.castRingHom (ZMod p)))).symm
  have hm : (U^p - expand p hp.ne_zero U).map (Int.castRingHom (ZMod p)) = 0 := by
    simp only [map_sub, map_pow, map_expand, hf, sub_self]
  have hc := congrArg (coeff k) hm
  simpa only [coeff_map, Int.coe_castRingHom, map_zero] using hc

theorem coeffLift (U : PowerSeries ℤ) (p n k : ℕ) (hp : p.Prime) :
    (p : ℤ)^(padicValNat p n+1) ∣
      coeff (p*k) (U^(p*n)) - coeff k (U^n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := dvd_sub_pow_of_dvd_sub
    (by simpa using coeffLiftBase U p hp :
      (p : PowerSeries ℤ) ∣ U^p - expand p hp.ne_zero U) (padicValNat p n)
  have he : p ^ padicValNat p n * (n / p ^ padicValNat p n) = n :=
    Nat.mul_div_cancel' pow_padicValNat_dvd
  have hpow := h.trans (sub_dvd_pow_sub_pow _ _ (n / p^padicValNat p n))
  have hh : C ((p : ℤ)^(padicValNat p n+1)) ∣
      U^(p*n) - expand p hp.ne_zero (U^n) := by
    simpa only [map_pow, map_natCast, ← pow_mul, mul_assoc, he] using hpow
  have hc := (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff _ _).mp hh (p*k)
  simpa only [map_sub, coeff_expand_mul] using hc

theorem variableExponent (p n k b : ℕ) (hp : p.Prime)
    (hdiv : n ∣ k*b) :
    Nat.ModEq (p^(padicValNat p n+1)) (b^(p*k+1)) (b^(k+1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hk : k = 0
  · subst k; rfl
  by_cases hb0 : b = 0
  · subst b
    simp only [zero_pow (by omega : p*k+1 ≠ 0), zero_pow (by omega : k+1 ≠ 0)]
    rfl
  by_cases hb : p ∣ b
  · have ha : padicValNat p n ≤ padicValNat p k + padicValNat p b := by
      have hh := (padicValNat_dvd_iff_le (p := p) (Nat.mul_ne_zero hk hb0)).mp
        (pow_padicValNat_dvd.trans hdiv)
      rwa [padicValNat.mul hk hb0] at hh
    have hbval : 1 ≤ padicValNat p b := one_le_padicValNat_of_dvd hb0 hb
    have hkv := Nat.padicValNat_lt_self (p := p) hk
    have hl : padicValNat p n+1 ≤ (k+1)*padicValNat p b := by
      have hm := Nat.mul_le_mul_left k hbval
      simp only [mul_one] at hm
      rw [add_mul, one_mul]
      omega
    have hz : p^(padicValNat p n+1) ∣ b^(k+1) :=
      (padicValNat_dvd_iff_le (p := p) (pow_ne_zero _ hb0)).mpr (by rwa [padicValNat.pow])
    have hle : k+1 ≤ p*k+1 := Nat.add_le_add_right (Nat.le_mul_of_pos_left k hp.pos) 1
    exact (Nat.modEq_zero_iff_dvd.mpr
      (hz.trans (pow_dvd_pow b hle))).trans (Nat.modEq_zero_iff_dvd.mpr hz).symm
  · have hcop : p.Coprime b := hp.coprime_iff_not_dvd.mpr hb
    have hkpow : p^padicValNat p n ∣ k :=
      (hcop.pow_left _).dvd_of_dvd_mul_right (pow_padicValNat_dvd.trans hdiv)
    obtain ⟨t, ht⟩ := hkpow
    have hc : b.Coprime (p^(padicValNat p n+1)) := (hcop.pow_left _).symm
    have hu := (Nat.ModEq.pow_totient hc).pow t
    rw [← pow_mul, Nat.totient_prime_pow_succ hp, one_pow] at hu
    have hexp : p*k+1 = (k+1) + (p^padicValNat p n*(p-1))*t := by
      rw [ht]
      have hp1 : p = (p-1)+1 := (Nat.succ_pred_prime hp).symm
      conv_lhs => lhs; lhs; rw [hp1]
      ring
    rw [hexp]
    simpa only [← pow_add, mul_one] using hu.mul_left (b^(k+1))

private def term (F : ℕ → ℕ → ℕ) (n k : ℕ) : ℤ :=
  if n=0 then 0 else (F n k : ℤ) + (k*F n k : ℤ)/(n : ℤ)

private def c (F : ℕ → ℕ → ℕ) (m : ℕ) : ℤ :=
  ∑ n ∈ range (m+1), term F n (m-n)

noncomputable def L (F : ℕ → ℕ → ℕ) : PowerSeries ℚ :=
  mk fun m => ∑ n ∈ range (m+1), (F n (m-n) : ℚ)/(n : ℚ)

private theorem termIdentity (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k) (n k : ℕ) (hn : n ≠ 0) :
    (n : ℤ)*term F n k = (n+k : ℕ)* (F n k : ℤ) := by
  have hd : (n : ℤ) ∣ (k : ℤ) * (F n k : ℤ) := Int.ofNat_dvd_left.mpr (hF n k hn)
  dsimp [term]
  rw [ite_eq_right hn, mul_add, Int.mul_ediv_cancel' hd]
  ring

private theorem valuationTransfer (p n m : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (hm : m ≠ 0) (d e : ℤ) (he : (n : ℤ)*d = (m : ℤ)*e)
    (hd : (p : ℤ)^(padicValNat p n+1) ∣ e) :
    (p : ℤ)^(padicValNat p m+1) ∣ d := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hd0 : d = 0
  · simp [hd0]
  have he0 : e ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact (mul_ne_zero (by exact_mod_cast hn) hd0) he
  have hv := congrArg (padicValInt p) he
  rw [padicValInt.mul (by exact_mod_cast hn) hd0,
    padicValInt.mul (by exact_mod_cast hm) he0,
    padicValInt.of_nat, padicValInt.of_nat] at hv
  have hdv := ((padicValInt_dvd_iff _ _).mp hd).resolve_left he0
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))

private theorem unitCancel (p n r : ℕ) (hp : p.Prime) (hn : ¬ p ∣ n)
    (d : ℤ) (hd : (p : ℤ)^r ∣ (n : ℤ)*d) : (p : ℤ)^r ∣ d := by
  exact ((hp.coprime_iff_not_dvd.mpr hn).isCoprime.pow_left).dvd_of_dvd_mul_left hd

private theorem termOff (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k)
    (p m n : ℕ) (hp : p.Prime) (hnm : n ≤ p*m)
    (hnp : ¬ p ∣ n) :
    (p : ℤ)^(padicValNat p m+1) ∣ term F n (p*m-n) := by
  have hn : n ≠ 0 := by rintro rfl; exact hnp (dvd_zero _)
  apply unitCancel p n _ hp hnp
  rw [termIdentity F hF n _ hn, Nat.add_sub_of_le hnm]
  apply dvd_mul_of_dvd_left
  have hd : (p : ℤ)^padicValNat p m ∣ (m : ℤ) := by exact_mod_cast pow_padicValNat_dvd (p := p) (n := m)
  simpa only [pow_succ', Nat.cast_mul] using mul_dvd_mul_left (p : ℤ) hd

private theorem termPair (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k)
    (hcong : ∀ (p : ℕ), p.Prime → ∀ (n k : ℕ), n ≠ 0 →
      (p : ℤ)^(padicValNat p n+1) ∣ (F (p*n) (p*k) : ℤ)-F n k)
    (p m n : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hnm : n ≤ m) :
    (p : ℤ)^(padicValNat p m+1) ∣
      term F (p*n) (p*m-p*n) - term F n (m-n) := by
  by_cases hn : n=0
  · simp [hn, term]
  rw [← Nat.mul_sub_left_distrib]
  apply valuationTransfer p n m hp hn hm
    _ ((F (p*n) (p*(m-n)) : ℤ) - F n (m-n))
  · have hs := termIdentity F hF n (m-n) hn
    rw [Nat.add_sub_of_le hnm] at hs
    have hb := termIdentity F hF (p*n) (p*(m-n)) (Nat.mul_ne_zero hp.ne_zero hn)
    have he : p*n+p*(m-n) = p*m := by rw [← Nat.mul_add, Nat.add_sub_of_le hnm]
    rw [he] at hb
    push_cast at hb
    have hb' : (n : ℤ)*term F (p*n) (p*(m-n)) =
        (m : ℤ) * F (p*n) (p*(m-n)) := by
      apply (mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0))
      linear_combination hb
    rw [mul_sub, hb', hs]
    ring
  · exact hcong p hp n (m-n) hn

private theorem cDold (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k)
    (hcong : ∀ (p : ℕ), p.Prime → ∀ (n k : ℕ), n ≠ 0 →
      (p : ℤ)^(padicValNat p n+1) ∣ (F (p*n) (p*k) : ℤ)-F n k) :
    Dold (c F) := by
  intro p hp m hm
  let q := p^(padicValNat p m+1)
  rw [← Nat.cast_pow]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change ((c F (p*m)-c F m : ℤ) : ZMod q) = 0
  rw [Int.cast_sub, sub_eq_zero]
  simp only [c, Int.cast_sum]
  calc
    ∑ n ∈ range (p*m+1), (term F n (p*m-n) : ZMod q) =
        ∑ n ∈ (range (p*m+1)).filter (fun n => p ∣ n),
          (term F n (p*m-n) : ZMod q) := by
      symm
      apply sum_subset (filter_subset _ _)
      intro n hn hn'
      have hnp : ¬p ∣ n := by simpa only [mem_filter, hn, true_and] using hn'
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      simpa only [q, Nat.cast_pow] using termOff F hF p m n hp
        (by have := mem_range.mp hn; omega) hnp
    _ = ∑ n ∈ range (m+1), (term F (p*n) (p*m-p*n) : ZMod q) := by
      symm
      apply sum_bij (fun n _ => p*n)
      · intro n hn
        simp only [mem_filter, mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.mul_le_mul_left p (Nat.le_of_lt_succ (mem_range.mp hn))), dvd_mul_right _ _⟩
      · intro n₁ hn₁ n₂ hn₂ he
        exact Nat.eq_of_mul_eq_mul_left hp.pos he
      · intro n hn
        rcases mem_filter.mp hn with ⟨hbound, ⟨d, rfl⟩⟩
        refine ⟨d, mem_range.mpr ?_, rfl⟩
        have hdm : p*d ≤ p*m := Nat.le_of_lt_succ (mem_range.mp hbound)
        exact Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left hdm hp.pos)
      · intro n hn; rfl
    _ = ∑ n ∈ range (m+1), (term F n (m-n) : ZMod q) := by
      apply sum_congr rfl
      intro n hn
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      simpa only [q, Nat.cast_pow] using termPair F hF hcong p m n hp hm
        (Nat.le_of_lt_succ (mem_range.mp hn))

private theorem logIdentification (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k) : L F = logInput (c F) := by
  ext m
  simp only [L, logInput, coeff_mk]
  by_cases hm : m=0
  · simp [hm, c, term]
  apply (eq_div_iff (by exact_mod_cast hm : (m : ℚ) ≠ 0)).mpr
  rw [c, Int.cast_sum, sum_mul]
  apply sum_congr rfl
  intro n hn
  by_cases hn0 : n=0
  · simp [hn0, term]
  have hnm : n ≤ m := Nat.le_of_lt_succ (mem_range.mp hn)
  have hi := congrArg (Int.castRingHom ℚ) (termIdentity F hF n (m-n) hn0)
  rw [Nat.add_sub_of_le hnm] at hi
  simp only [map_mul, Int.coe_castRingHom, Int.cast_natCast] at hi
  apply (mul_left_cancel₀ (by exact_mod_cast hn0 : (n : ℚ) ≠ 0))
  rw [← mul_assoc, hi]
  field_simp

theorem integralGeneric (F : ℕ → ℕ → ℕ)
    (hF : ∀ n k, n ≠ 0 → n ∣ k*F n k)
    (hcong : ∀ (p : ℕ), p.Prime → ∀ (n k : ℕ), n ≠ 0 →
      (p : ℤ)^(padicValNat p n+1) ∣ (F (p*n) (p*k) : ℤ)-F n k) :
    D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure.IntegralSeries
      (PowerSeries.subst (L F) (PowerSeries.exp ℚ)) := by
  rw [logIdentification F hF]
  exact integral_exp_of_dold (c F) (cDold F hF hcong)

theorem coefficientDivisibility (U : PowerSeries ℤ) (n k : ℕ) :
    (n : ℤ) ∣ (k : ℤ) * coeff k (U^n) := by
  cases k
  · simp
  rename_i k
  have h := congrArg (coeff k) (derivative_pow U n)
  rw [coeff_derivative] at h
  have hh : ((k+1 : ℕ) : ℤ) * coeff (k+1) (U^n) =
      (n : ℤ) * coeff k (U^(n-1) * derivative U) := by
    rw [mul_assoc, ← map_natCast C n, coeff_C_mul] at h
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  rw [hh]
  exact dvd_mul_right _ _

theorem binomDiv (n k : ℕ) : n ∣ k*n.choose k := by
  have h := coefficientDivisibility ((1+X) : PowerSeries ℤ) n k
  rw [D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform.coeff_one_add_pow] at h
  exact_mod_cast h

theorem binomCong (p n k : ℕ) (hp : p.Prime) :
    Nat.ModEq (p^(padicValNat p n+1)) ((p*n).choose (p*k)) (n.choose k) := by
  have h := coeffLift ((1+X) : PowerSeries ℤ) p n k hp
  rw [D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform.coeff_one_add_pow,
    D5.S1.Recurrence.Invariants.HannaLegendreCentralBinomialTransform.coeff_one_add_pow] at h
  apply Nat.modEq_of_dvd
  simpa only [Nat.cast_pow, neg_sub] using (dvd_neg.mpr h)

private def F70 (n k : ℕ) : ℕ := (n.choose k)^(k+1)

theorem divPower (B e : ℕ → ℕ → ℕ)
    (hB : ∀ n k, n ≠ 0 → n ∣ k*B n k) :
    ∀ n k, n ≠ 0 → n ∣ k*(B n k)^(e n k+1) := by
  intro n k hn
  simpa only [pow_succ', ← mul_assoc] using dvd_mul_of_dvd_left (hB n k hn) ((B n k)^(e n k))

private theorem cong70 (p : ℕ) (hp : p.Prime) (n k : ℕ) :
    (p : ℤ)^(padicValNat p n+1) ∣ (F70 (p*n) (p*k) : ℤ)-F70 n k := by
  have hc := (binomCong p n k hp).pow (p*k+1)
  have he := variableExponent p n k (n.choose k) hp (binomDiv n k)
  have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
  simpa only [F70, Nat.cast_pow] using h

theorem literalUnbounded (F : ℕ → ℕ → ℕ) (m : ℕ) :
    (∑ n ∈ range (m+1), ∑ k ∈ range (m+1),
      if 0 < n ∧ n+k=m then (F n k : ℚ)/(n : ℚ) else 0) =
    coeff m (L F) := by
  rw [L, coeff_mk]
  apply sum_congr rfl
  intro n hn
  by_cases hn0 : n=0
  · simp [hn0]
  have hnm : n ≤ m := Nat.le_of_lt_succ (mem_range.mp hn)
  rw [sum_eq_single (m-n)]
  · rw [ite_eq_left ⟨Nat.pos_of_ne_zero hn0, Nat.add_sub_of_le hnm⟩]
  · intro k hk hkn
    rw [ite_eq_right]
    rintro ⟨hpos, he⟩
    exact hkn (by omega)
  · intro h
    exact (h (mem_range.mpr (by omega))).elim

theorem literalBounded (F : ℕ → ℕ → ℕ) (hF : ∀ n k, n<k → F n k=0) (m : ℕ) :
    (∑ n ∈ range (m+1), ∑ k ∈ range (n+1),
      if 0 < n ∧ n+k=m then (F n k : ℚ)/(n : ℚ) else 0) =
    coeff m (L F) := by
  rw [← literalUnbounded F m]
  apply sum_congr rfl
  intro n hn
  apply sum_subset (range_mono (by have := mem_range.mp hn; omega))
  intro k hk hkn
  have hnk : n < k := by have := mem_range.not.mp hkn; omega
  simp [hF n k hnk]

theorem result : claim := by
  have hl : logarithm = L F70 := by
    ext m
    simpa only [logarithm, coeff_mk, F70, Nat.cast_pow] using
      literalBounded F70
        (fun n k h => by simp [F70, Nat.choose_eq_zero_of_lt h]) m
  unfold claim A
  rw [hl]
  exact integralGeneric _
    (divPower (fun n k => n.choose k) (fun _ k => k)
      (fun n k _ => binomDiv n k)) (fun p hp n k _ => cong70 p hp n k)

end D5.S1.Recurrence.Algebraic.HannaA181070Integrality
