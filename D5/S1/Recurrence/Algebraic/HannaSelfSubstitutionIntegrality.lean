/- GID: D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral exponential inputs give integral Hanna self-substitution fixed points. -/

/-
admission_basis: open-problem-resolution (#18709; Proved)
escape_witness: none.
logSum: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.SolvesHanna, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_agree, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_agree, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.solves_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.input_coeff, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_constants, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_sub, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_subst_power, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.preserve_integer_ghost, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.integral_input_ghost, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.input_pow_eq, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.geometric_input.
SolvesHanna: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.solves_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exists_unique_solves, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675.claim.
claim: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result.
logSum_zero: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_agree, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.input_pow_eq.
step: proof_shape: definition; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_agree, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exists_unique_solves, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result.
step_zero: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.solves_zero, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exists_unique_solves.
rescale_agree: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_agree.
logSum_agree: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.step_agree.
step_agree: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exists_unique_solves, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation.
solves_zero: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exists_unique_solves, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation.
exists_unique_solves: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation.
integral_one: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.claim_of_preservation.
claim_of_preservation: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result.
input_coeff: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.logSum_constants, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.input_pow_eq.
integral_iff_map: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.integral_inv, D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.geometric_input.
logSum_constants: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.integral_input_ghost.
power_lift: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.preserve_integer_ghost.
rescale_frobenius: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.preserve_integer_ghost.
logSum_sub: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility.
logSum_subst_power: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility.
exp_logSum_integral_of_divisibility: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.preserve_integer_ghost.
preserve_integer_ghost: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result.
integral_input_ghost: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.result.
result: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675.result.
integral_inv: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.geometric_input.
input_pow_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.geometric_input.
geometric_input: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegralityA157675.result.
The claim inlines the source exponential input; the proof uses
HannaDiagonalGhostPowerIntegrality.logarithmicInput through logSum_constants.
The formal exponential is PowerSeries.subst, without a forwarding definition.
The proof reuses the frozen private Dold suppliers through open private.
claim_of_preservation carries the integral-iterate and coefficient-agreement induction.
This is consumed bind-only reasoning: the frozen integer instance of
PowerSeriesNormalizedContraction.exists_unique_fixed already supplies the
integral fixed point under preservation, with rational uniqueness identifying
every solution. It supplies no escape witness or new proof content.
The public result settles the external tier-1 assertion preregistered in
#18709 before probes; the consumed geometric_input supports the separate
#18710 settlement. Literature completeness remains ASSUMED-UNVERIFIED.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24041.
-/
import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality

open PowerSeries
open private integral_of_local expSeries_constant local_exp_of_log_difference
  local_int_div_nat IsRIntegralRat.sum
  from D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

noncomputable def logSum (f : ℕ → PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun N => ∑ n ∈ Finset.Icc 1 N, coeff (N - n) (f n) / (n : ℚ)

def SolvesHanna (L : ℕ → ℚ) (G : PowerSeries ℚ) : Prop :=
  G = ((exp ℚ).subst) (logSum fun n => rescale (L n) G ^ n)

def claim : Prop :=
  ∀ L : ℕ → ℚ, IntegralSeries ((exp ℚ).subst (logSum fun n => C (L n))) →
    (∃ G, SolvesHanna L G) ∧ ∀ G, SolvesHanna L G → IntegralSeries G

private theorem logSum_zero (f : ℕ → PowerSeries ℚ) : constantCoeff (logSum f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [logSum]

private noncomputable def step (L : ℕ → ℚ) (B : PowerSeries ℚ) : PowerSeries ℚ :=
  ((exp ℚ).subst) (logSum fun n => rescale (L n) B ^ n)

private theorem step_zero (L : ℕ → ℚ) (B : PowerSeries ℚ) :
    constantCoeff (step L B) = 1 :=
  expSeries_constant (logSum_zero _)

private theorem rescale_agree {d : ℕ} {B C : PowerSeries ℚ}
    (h : Agree d B C) (a : ℚ) : Agree d (rescale a B) (rescale a C) := by
  intro n hn
  simp only [coeff_rescale]
  rw [h n hn]

private theorem logSum_agree (L : ℕ → ℚ) {d : ℕ} {B C : PowerSeries ℚ}
    (h : Agree d B C) :
    Agree (d + 1) (logSum fun n => rescale (L n) B ^ n)
      (logSum fun n => rescale (L n) C ^ n) := by
  intro N hN
  simp only [logSum, coeff_mk]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  rw [agree_pow (rescale_agree h (L n)) n (N - n) (by omega)]

private theorem step_agree (L : ℕ → ℚ) {d : ℕ} {B C : PowerSeries ℚ}
    (h : Agree d B C) : Agree (d + 1) (step L B) (step L C) := by
  exact subst_inner_agree (logSum_agree L h) (exp ℚ) (logSum_zero _) (logSum_zero _)

private theorem solves_zero (L : ℕ → ℚ) (G : PowerSeries ℚ) (h : SolvesHanna L G) :
    constantCoeff G = 1 := by
  rw [h]
  exact step_zero L G

private theorem exists_unique_solves (L : ℕ → ℚ) : ∃! G, SolvesHanna L G := by
  obtain ⟨G, hG0, hG, huniq⟩ := exists_unique_fixed (step L)
    (fun B _ => step_zero L B) (fun _ _ _ h => step_agree L h)
  refine ⟨G, hG, ?_⟩
  intro H hH
  exact huniq H (solves_zero L H hH) hH

private theorem integral_one : IntegralSeries (1 : PowerSeries ℚ) := by
  intro n
  by_cases hn : n = 0
  · subst n; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hn]⟩

private theorem claim_of_preservation
    (hpres : ∀ L : ℕ → ℚ, IntegralSeries ((exp ℚ).subst (logSum fun n => C (L n))) →
      ∀ B : PowerSeries ℚ, IntegralSeries B → IntegralSeries (step L B)) : claim := by
  intro L hL
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hG, _⟩ := exists_unique_solves L
    exact ⟨G, hG⟩
  · intro G hG
    change G = step L G at hG
    let a : ℕ → PowerSeries ℚ := Nat.rec (1 : PowerSeries ℚ) (fun _ prev => step L prev)
    have ha (n : ℕ) : IntegralSeries (a n) := by
      induction n with
      | zero => exact integral_one
      | succ n ih => exact hpres L hL _ ih
    have hagree (n : ℕ) : Agree (n + 1) G (a n) := by
      induction n with
      | zero =>
        intro k hk
        have hk0 : k = 0 := by
          exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        subst k
        simpa [a, coeff_zero_eq_constantCoeff] using solves_zero L G hG
      | succ n ih =>
        simpa only [← hG] using step_agree L ih
    intro n
    obtain ⟨z, hz⟩ := ha n n
    exact ⟨z, (hagree n n (by omega)).trans hz⟩

private theorem input_coeff (L : ℕ → ℚ) (N : ℕ) :
    coeff N (logSum fun n => C (L n)) = L N / (N : ℚ) := by
  classical
  by_cases hN : N = 0
  · subst N; simp [logSum]
  · simp only [logSum, coeff_mk]
    rw [Finset.sum_eq_single N]
    · simp
    · intro n hn hnN
      have hn' := Finset.mem_Icc.mp hn
      have hne : N - n ≠ 0 :=
        Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_of_le_of_ne hn'.2 hnN))
      simp [coeff_C, hne]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hN, le_rfl⟩)).elim

private theorem integral_iff_map (f : PowerSeries ℚ) :
    IntegralSeries f ↔ ∃ g : PowerSeries ℤ, g.map (Int.castRingHom ℚ) = f := by
  constructor
  · intro h
    choose z hz using h
    refine ⟨mk z, ?_⟩
    ext n
    simpa using (hz n).symm
  · rintro ⟨g, rfl⟩
    exact fun n => ⟨coeff n g, by simp⟩

private theorem logSum_constants (L : ℕ → ℚ) :
    logSum (fun n => C (L n)) =
      D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.logarithmicInput L := by
  ext n
  rw [input_coeff]
  simp only [D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.logarithmicInput, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

theorem power_lift {R : Type*} [CommRing R] (p : ℕ)
    {U V : R} (h : (p : R) ∣ U - V) (m : ℕ) :
    (p : R) ^ (padicValNat p m + 1) ∣ U ^ m - V ^ m := by
  let I : Ideal R := Ideal.span {(p : R)}
  have hm : U ≡ V [SMOD I] := SModEq.sub_mem.mpr (Ideal.mem_span_singleton.mpr h)
  have hpI : (p : R) ∈ I := Ideal.subset_span (by simp)
  have hpow := hm.pow_pow_add_one hpI (padicValNat p m)
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hpow
  obtain ⟨b, hb⟩ := pow_padicValNat_dvd (p := p) (n := m)
  simpa only [← pow_mul, ← hb] using hpow.trans (sub_dvd_pow_sub_pow _ _ b)

private theorem rescale_frobenius (p : ℕ) (hp : p.Prime) (B : PowerSeries ℤ)
    (a b : ℤ) (hab : (p : ℤ) ∣ a - b) :
    (p : PowerSeries ℤ) ∣ rescale a B ^ p - (rescale b B).subst ((X : PowerSeries ℤ) ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff (p : ℤ) _).mpr
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hmap : (rescale a B ^ p - (rescale b B).subst ((X : PowerSeries ℤ) ^ p)).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, ← rescale_map,
      D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst]
    have hab' : (a : ZMod p) = b :=
      ((ZMod.intCast_eq_intCast_iff_dvd_sub b a p).mpr hab).symm
    simp only [Int.coe_castRingHom]
    rw [hab']
    have hs := map_subst (h := Int.castRingHom (ZMod p))
      (PowerSeries.HasSubst.X_pow hp.ne_zero) (rescale b B)
    change (PowerSeries.map (Int.castRingHom (ZMod p))) ((rescale b B).subst (X^p)) =
      ((rescale b B).map (Int.castRingHom (ZMod p))).subst
        ((PowerSeries.map (Int.castRingHom (ZMod p))) (X^p)) at hs
    simp only [map_pow, PowerSeries.map_X, ← rescale_map, Int.coe_castRingHom] at hs
    rw [hs, sub_self]
  have hh := congrArg (coeff n) hmap
  simpa only [coeff_map, Int.coe_castRingHom, map_zero] using hh

private theorem logSum_sub (f g : ℕ → PowerSeries ℚ) :
    logSum (fun n => f n - g n) = logSum f - logSum g := by
  ext N
  simp [logSum, sub_div, Finset.sum_sub_distrib]

private theorem logSum_subst_power (p : ℕ) (hp : p ≠ 0) (f : ℕ → PowerSeries ℚ) :
    (logSum f).subst ((X : PowerSeries ℚ)^p) =
      C (p : ℚ) * logSum (fun n => if p ∣ n then (f (n/p)).subst (X^p) else 0) := by
  classical
  ext N
  rw [coeff_subst_X_pow hp, coeff_C_mul]
  simp only [logSum, coeff_mk, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hN : p ∣ N
  · rw [if_pos hN]
    simp only [apply_ite, map_zero, ite_div, zero_div, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_bij (fun m _ => p*m)
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right p m⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp (by omega))
      · have h := Nat.mul_le_mul_left p hm'.2
        simpa [Nat.mul_div_cancel' hN] using h
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) hab
    · intro n hn
      obtain ⟨hnI, hpn⟩ := Finset.mem_filter.mp hn
      have hn' := Finset.mem_Icc.mp hnI
      refine ⟨n/p, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn'.2⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) hpn) (Nat.pos_of_ne_zero hp)
      · exact Nat.mul_div_cancel' hpn
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      have hpm : p*m ≤ N := by
        have h := Nat.mul_le_mul_left p hm'.2
        simpa [Nat.mul_div_cancel' hN] using h
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_subst_X_pow hp,
        if_pos (Nat.dvd_sub hN (dvd_mul_right p m)), Nat.sub_mul_div_of_le N p m hpm]
      have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
      have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · rw [if_neg hN]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, coeff_subst_X_pow hp]
      have hnn : ¬ p ∣ N - n := fun h =>
        hN ((Nat.dvd_sub_iff_left (Finset.mem_Icc.mp hn).2 hpn).mp h)
      simp [hnn]
    · simp [hpn]

private theorem exp_logSum_integral_of_divisibility
    (f : ℕ → PowerSeries ℤ)
    (hf : ∀ p : ℕ, p.Prime → ∀ n : ℕ, n ≠ 0 →
      (p : PowerSeries ℤ) ^ padicValNat p n ∣
        f n - if p ∣ n then (f (n/p)).subst ((X : PowerSeries ℤ)^p) else 0) :
    IntegralSeries (((exp ℚ).subst) (logSum fun n => (f n).map (Int.castRingHom ℚ))) := by
  apply integral_of_local
  intro p hp
  apply local_exp_of_log_difference p hp _ (logSum_zero _)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [logSum_subst_power p hp.ne_zero, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hpQ, map_one, one_mul, ← logSum_sub]
  intro N
  simp only [logSum, coeff_mk]
  apply IsRIntegralRat.sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  let t : PowerSeries ℤ := f n - if p ∣ n then (f (n/p)).subst (X^p) else 0
  have hdiv : (p : ℤ) ^ padicValNat p n ∣ coeff (N-n) t := by
    exact (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff _ _).mp (by simpa only [map_pow, map_natCast] using hf p hp n hn0) (N-n)
  have ht : ((f n).map (Int.castRingHom ℚ) -
      (if p ∣ n then ((f (n/p)).map (Int.castRingHom ℚ)).subst ((X : PowerSeries ℚ)^p) else 0)) =
      t.map (Int.castRingHom ℚ) := by
    dsimp [t]
    simp only [map_sub, apply_ite (PowerSeries.map (Int.castRingHom ℚ)),
      map_zero]
    by_cases hpn : p ∣ n
    · simp only [if_pos hpn]
      congr 1
      exact (map_subst_pow (Int.castRingHom ℚ) (f (n/p)) p hp.ne_zero).symm
    · simp [hpn]
  rw [ht, coeff_map]
  exact local_int_div_nat p hp _ n hn0 hdiv

private theorem preserve_integer_ghost
    (L : ℕ → ℤ)
    (hL : ∀ p : ℕ, p.Prime → ∀ m : ℕ, m ≠ 0 → (p : ℤ) ∣ L (p*m) - L m)
    (B : PowerSeries ℤ) :
    IntegralSeries (((exp ℚ).subst) (logSum fun n =>
      rescale (L n : ℚ) (B.map (Int.castRingHom ℚ)) ^ n)) := by
  have he : (fun n => rescale (L n : ℚ) (B.map (Int.castRingHom ℚ)) ^ n) =
      (fun n => ((rescale (L n) B)^n).map (Int.castRingHom ℚ)) := by
    funext n
    rw [map_pow, ← rescale_map]
    rfl
  rw [he]
  apply exp_logSum_integral_of_divisibility
  intro p hp n hn
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    let m := n/p
    have hm : m ≠ 0 := Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn) hp.pos)
    have hn' : n = p*m := (Nat.mul_div_cancel' hpn).symm
    have hv : padicValNat p n = padicValNat p m + 1 := by
      letI : Fact p.Prime := ⟨hp⟩
      rw [hn', padicValNat.mul hp.ne_zero hm, padicValNat.self hp.one_lt]
      omega
    have hres := rescale_frobenius p hp B (L n) (L m) (by simpa only [hn'] using hL p hp m hm)
    have hlift := power_lift p hres m
    rw [hv]
    convert hlift using 1
    rw [← pow_mul, ← subst_pow (.X_pow hp.ne_zero), ← hn']
  · rw [if_neg hpn, sub_zero, padicValNat.eq_zero_of_not_dvd hpn, pow_zero]
    exact one_dvd _

private theorem integral_input_ghost (L : ℕ → ℚ)
    (hF : IntegralSeries ((exp ℚ).subst (logSum fun n => C (L n)))) :
    ∃ c : ℕ → ℤ, (∀ n, n ≠ 0 → L n = (c n : ℚ)) ∧
      ∀ p : ℕ, p.Prime → ∀ m : ℕ, m ≠ 0 → (p : ℤ) ∣ c (p*m) - c m := by
  rw [logSum_constants] at hF
  obtain ⟨b, hb⟩ := D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.integral_input_ledger L hF
  refine ⟨D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.divisorGhost b, ?_, ?_⟩
  · intro n hn
    exact hb n (Nat.pos_of_ne_zero hn)
  · intro p hp m hm
    simpa only [Nat.zero_add, pow_zero, pow_one, mul_one, mul_comm] using
      D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.divisor_ghost_gauss b p hp 0 m (Nat.pos_of_ne_zero hm)

theorem result : claim := by
  apply claim_of_preservation
  intro L hF B hB
  obtain ⟨c, hc, hcp⟩ := integral_input_ghost L hF
  obtain ⟨b, hb⟩ := (integral_iff_map B).mp hB
  have he : logSum (fun n => rescale (L n) B ^ n) =
      logSum (fun n => rescale (c n : ℚ) (b.map (Int.castRingHom ℚ)) ^ n) := by
    ext N
    simp only [logSum, coeff_mk]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hc n (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1), hb]
  change IntegralSeries (((exp ℚ).subst) (logSum fun n => rescale (L n) B ^ n))
  rw [he]
  exact preserve_integer_ghost c hcp b

private theorem integral_inv {f : PowerSeries ℚ} (hf : IntegralSeries f)
    (hf0 : constantCoeff f = 1) : IntegralSeries f⁻¹ := by
  obtain ⟨g, hg⟩ := (integral_iff_map f).mp hf
  have hg0 : constantCoeff g = 1 := by
    have h : ((constantCoeff g : ℤ) : ℚ) = 1 := by
      change constantCoeff (g.map (Int.castRingHom ℚ)) = 1
      rw [hg, hf0]
    exact_mod_cast h
  apply (integral_iff_map _).mpr
  refine ⟨invOfUnit g 1, ?_⟩
  apply (eq_inv_iff_mul_eq_one (by rw [hf0]; norm_num)).mpr
  rw [← hg, ← map_mul, invOfUnit_mul g 1 (by simpa using hg0), map_one]

private theorem input_pow_eq (a : ℚ) :
    ((exp ℚ).subst (logSum fun n => C (a ^ n))) = (1 - C a * X)⁻¹ := by
  let g : PowerSeries ℚ := (1 - C a * X)⁻¹
  have hg0 : constantCoeff g = 1 := by simp [g]
  have hc (k : ℕ) : coeff k (derivative (logSum fun n => C (a ^ n))) = a ^ (k+1) := by
    rw [coeff_derivative, input_coeff]
    have hk : ((k+1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    push_cast
    field_simp
  have hlog : derivative (logSum fun n => C (a ^ n)) = C a * g := by
    apply (eq_mul_inv_iff_mul_eq (by simp : constantCoeff (1-C a*X) ≠ 0)).mpr
    have hr : derivative (logSum fun n => C (a ^ n)) * (C a * X) =
        C a * (derivative (logSum fun n => C (a ^ n)) * X) := by exact mul_left_comm _ _ _
    rw [mul_sub, mul_one, hr]
    ext n
    cases n with
    | zero => simpa only [map_sub, coeff_zero_mul_X, coeff_C_mul, hc, Nat.zero_add, pow_one,
        mul_zero, sub_zero, coeff_C, ite_true]
    | succ n =>
      simp only [map_sub, coeff_C_mul, coeff_succ_mul_X, hc, coeff_C,
        Nat.succ_ne_zero, ite_false, pow_succ]
      ring
  apply D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique
    (((exp ℚ).subst (logSum fun n => C (a ^ n)))) g (C a * g)
  · simp only [coeff_zero_eq_constantCoeff, expSeries_constant (logSum_zero _), hg0]
  · rw [derivative_subst (.of_constantCoeff_zero (logSum_zero _)),
      derivative_exp, hlog]
    ring
  · dsimp [g]
    rw [derivative_inv']
    simp only [map_sub, derivative_one, Derivation.leibniz, derivative_C, zero_smul,
      zero_add, derivative_X, smul_eq_mul, mul_one, zero_sub, neg_mul, neg_neg]
    ring

theorem geometric_input (a : ℤ) : IntegralSeries (((exp ℚ).subst (logSum fun n => C ((a : ℚ)^n)))) := by
  rw [input_pow_eq]
  apply integral_inv
  · apply (integral_iff_map _).mpr
    refine ⟨1 - C a * X, ?_⟩
    simp
  · simp


end D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
