/- GID: D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness
   mirror-E: none(waiver:actual-arithmetic-column-faithfulness)
   anchors: []
   utility: none
   digest: Exterior nullity of the actual arithmetic divided-difference columns forces every finite head coefficient to vanish. -/

import D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
SOURCE_ONLY_UNCOMPILED. This file is a complete source proof candidate, not a
kernel-checked result. WeilArithmeticCouplingJet, ActualColumnRemainder and
ActualFullSymbolTail are pinned UNCOMPILED dependency candidates. Their actual
definitions and the exact public paired-column lower bound are consumed here.
Elaboration, kernel and proof-trust checks, Reg source selection/enrollment, Scribe and
required CI remain caller-owned and unresolved.

The diagonal is totalized exactly as in couplingColumn. The recurrence keeps
the essential 1/pi factor. The head radius and every analytic cutoff are
constructed internally; neither moment vanishing nor positive energy is an
assumption. Both exterior signs, all finite sets (including the empty set),
arbitrary complex coefficients and the cutoff M=0 are retained.

The finite reconstruction step consumes the existing Vandermonde matrix
result. This file makes no physical-operator identification, signed Weil
positivity, Robin5040 or RH claim. The saved higher-order-jet route is separate.
Utility none: the declarations prove parameterized arithmetic-column identities
and faithfulness; they supply no bounded checker, certificate or fixed instance.
-/

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

-- This identity also holds at m=n: both divided-difference numerators vanish.
private theorem coupling_summand_recurrence (c : ℕ) (v : ℤ → ℂ) (m n : ℤ) :
    ((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
        (Real.pi * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ) * ((n : ℂ) * v n)) =
      (m : ℂ) *
          (((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
            (Real.pi * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ)) * v n) -
        ((arithmeticBoundarySymbol c n : ℂ) * v n -
          (arithmeticBoundarySymbol c m : ℂ) * v n) / (Real.pi : ℂ) := by
  by_cases hmn : m = n
  · subst m
    simp
  · have hdiff : (m : ℂ) - (n : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hmn
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp [hpi, hdiff] <;> ring

private theorem coupling_column_recurrence
    (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :
    couplingColumn c S (fun n => (n : ℂ) * v n) m =
      (m : ℂ) * couplingColumn c S v m -
        ((∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) -
          (arithmeticBoundarySymbol c m : ℂ) * ∑ n ∈ S, v n) /
            (Real.pi : ℂ) := by
  classical
  unfold couplingColumn
  simp_rw [coupling_summand_recurrence c v m]
  simp only [sub_div, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

-- Positive q would force a strictly positive tail beyond the null cutoff.
-- No positivity of q, radius or nonzero moment is assumed by this helper.
private theorem exterior_null_moments {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (M : ℕ)
    (hnull : ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      couplingColumn c S v m = 0) :
    (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) = 0 ∧
      (∑ n ∈ S, v n) = 0 := by
  classical
  let alpha : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
  let beta : ℂ := ∑ n ∈ S, v n
  let q : ℝ := ‖alpha‖ ^ 2 + smoothFloor c ^ 2 * ‖beta‖ ^ 2
  have hL : 0 < logLength c := PrimeSymbolMeanSquare.logLength_pos hc
  have hfloor : 0 < smoothFloor c := by
    have he : Real.exp (-logLength c / 2) < 1 := by
      calc
        _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith only [hL])
        _ = 1 := Real.exp_zero
    exact div_pos (sub_pos.mpr he) (by norm_num : (0 : ℝ) < 10)
  have hqnonneg : 0 ≤ q :=
    add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hqnot : ¬0 < q := by
    intro hq
    let A : ℝ := ∑ n ∈ S, |(n : ℝ)|
    have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => abs_nonneg (n : ℝ))
    have hS : ∀ n ∈ S, |(n : ℝ)| ≤ A := by
      intro n hn
      calc
        |(n : ℝ)| = ∑ k ∈ S, if k = n then |(k : ℝ)| else 0 := by
          simp [hn]
        _ ≤ ∑ k ∈ S, |(k : ℝ)| := Finset.sum_le_sum (fun k _ => by
          by_cases hkn : k = n
          · simp only [if_pos hkn]
            exact le_rfl
          · simpa only [if_neg hkn] using (abs_nonneg (k : ℝ)))
    let U : ℝ :=
      2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
    let D0 : ℝ := 2 * ActualFullSymbolTail.primeFirstMoment c * (2 + U)
    let mix : ℝ := 2 * ‖beta‖ ^ 2 * D0 / q
    let K : ℝ :=
      256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2 / (3 * q)
    let B : ℝ := max ((M : ℝ) + 1)
      (max 1 (max (2 * A) (max (logLength c / (2 * Real.pi)) (max mix K))))
    obtain ⟨N, hN⟩ := exists_nat_gt B
    have hbounds : (M : ℝ) + 1 ≤ (N : ℝ) ∧
        1 ≤ (N : ℝ) ∧ 2 * A ≤ (N : ℝ) ∧
        logLength c / (2 * Real.pi) ≤ (N : ℝ) ∧
        mix ≤ (N : ℝ) ∧ K ≤ (N : ℝ) := by
      simpa only [B, max_le_iff] using (le_of_lt hN)
    obtain ⟨hMN, hN1, hNA, hNL, hNMix, hNK⟩ := hbounds
    have hNpos : 0 < N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN1)
    have hfreq : 1 ≤ frequency c ((N + 1 : ℕ) : ℤ) := by
      have hLN : logLength c ≤ (N : ℝ) * (2 * Real.pi) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hNL
      unfold frequency
      apply (le_div_iff₀ hL).mpr
      push_cast
      nlinarith only [hLN, Real.pi_pos]
    have hgap : 2 * A ≤ (N : ℝ) + 1 := by linarith only [hNA]
    have hmix : 2 * ‖beta‖ ^ 2 * D0 / q ≤ (N : ℝ) + 1 := by
      change mix ≤ (N : ℝ) + 1
      linarith only [hNMix]
    have hNsquare : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hp := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hN1)
      nlinarith only [hp]
    have hcut :
        256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2 / (3 * q) ≤
          (N : ℝ) ^ 2 := hNK.trans hNsquare
    -- Exact let order of the pinned public theorem: alpha, beta, q, U, D0;
    -- then frequency, gap, positive q, mixed cutoff, weighted remainder cutoff.
    have hlower : q / (4 * Real.pi ^ 2 * ((N : ℝ) + 1)) ≤
        ∑' j : ℕ, (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) :=
      (ActualFullSymbolTail.paired_coupling_column_tail_lower
        hc hNpos S v hA hS hfreq hgap hq hmix hcut).2
    have hterm (j : ℕ) :
        ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2 = 0 := by
      have hmode : (M : ℝ) < ((N + j + 1 : ℕ) : ℝ) := by
        push_cast
        linarith only [hMN, Nat.cast_nonneg (α := ℝ) j]
      have hmode_nonneg : (0 : ℝ) ≤ ((N + j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpos : couplingColumn c S v ((N + j + 1 : ℕ) : ℤ) = 0 :=
        hnull _ (by
          simpa only [Int.cast_natCast, abs_of_nonneg hmode_nonneg] using hmode)
      have hneg : couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ)) = 0 :=
        hnull _ (by
          simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
            abs_of_nonneg hmode_nonneg] using hmode)
      rw [hpos, hneg]
      simp
    have htailzero :
        (∑' j : ℕ, (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)) = 0 := by
      calc
        _ = ∑' _ : ℕ, (0 : ℝ) := tsum_congr hterm
        _ = 0 := tsum_zero
    rw [htailzero] at hlower
    have hleft : 0 < q / (4 * Real.pi ^ 2 * ((N : ℝ) + 1)) :=
      div_pos hq (by positivity)
    exact (not_le_of_gt hleft) hlower
  have hqzero : q = 0 := le_antisymm (le_of_not_gt hqnot) hqnonneg
  have hqzero' : ‖alpha‖ ^ 2 + smoothFloor c ^ 2 * ‖beta‖ ^ 2 = 0 := hqzero
  have ha2 : ‖alpha‖ ^ 2 = 0 := by
    apply le_antisymm
    · linarith only [hqzero',
        mul_nonneg (sq_nonneg (smoothFloor c)) (sq_nonneg ‖beta‖)]
    · exact sq_nonneg _
  have hbprod : smoothFloor c ^ 2 * ‖beta‖ ^ 2 = 0 := by
    linarith only [hqzero', ha2]
  have hb2 : ‖beta‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hbprod).resolve_left (ne_of_gt (pow_pos hfloor 2))
  have ha : alpha = 0 := by
    apply norm_eq_zero.mp
    rcases mul_eq_zero.mp
      (show ‖alpha‖ * ‖alpha‖ = 0 by simpa only [pow_two] using ha2) with h | h <;>
      exact h
  have hb : beta = 0 := by
    apply norm_eq_zero.mp
    rcases mul_eq_zero.mp
      (show ‖beta‖ * ‖beta‖ = 0 by simpa only [pow_two] using hb2) with h | h <;>
      exact h
  exact ⟨ha, hb⟩

private theorem exterior_null_mul {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (M : ℕ)
    (hnull : ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      couplingColumn c S v m = 0) :
    ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      couplingColumn c S (fun n => (n : ℂ) * v n) m = 0 := by
  obtain ⟨ha, hb⟩ := exterior_null_moments hc S v M hnull
  intro m hm
  rw [coupling_column_recurrence c S v m, hnull m hm, ha, hb]
  simp

private theorem exterior_null_powers {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (M : ℕ)
    (hnull : ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      couplingColumn c S v m = 0) :
    ∀ k : ℕ, ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      couplingColumn c S (fun n => (n : ℂ) ^ k * v n) m = 0 := by
  intro k
  induction k with
  | zero => simpa only [pow_zero, one_mul] using hnull
  | succ k ih =>
      have hstep := exterior_null_mul hc S (fun n => (n : ℂ) ^ k * v n) M ih
      have hfun : (fun n : ℤ => (n : ℂ) * ((n : ℂ) ^ k * v n)) =
          (fun n : ℤ => (n : ℂ) ^ (k + 1) * v n) := by
        funext n
        rw [pow_succ]
        ring
      rw [hfun] at hstep
      exact hstep

/-- The actual arithmetic exterior columns are faithful on every finite integer head. -/
theorem actual_finite_head_faithful {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (M : ℕ)
    (hnull : ∀ m : ℤ, (M : ℝ) < |(m : ℝ)| →
      D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.couplingColumn c S v m = 0) :
    ∀ n ∈ S, v n = 0 := by
  classical
  have hmoments (k : ℕ) : (∑ n ∈ S, (n : ℂ) ^ k * v n) = 0 :=
    (exterior_null_moments hc S (fun n => (n : ℂ) ^ k * v n) M
      (exterior_null_powers hc S v M hnull k)).2
  let e : Fin S.card ≃ S := S.equivFin.symm
  let nodes : Fin S.card → ℂ := fun i => ((e i : ℤ) : ℂ)
  let amplitudes : Fin S.card → ℂ := fun i => v (e i)
  have hnodes : Function.Injective nodes := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    have hcast : ((e i : ℤ) : ℂ) = ((e j : ℤ) : ℂ) := hij
    exact_mod_cast hcast
  have hread : finiteMomentReadout nodes amplitudes =
      finiteMomentReadout nodes (0 : Fin S.card → ℂ) := by
    funext k
    rw [finite_moment_readout_apply, finite_moment_readout_apply]
    have hsum : (∑ i : Fin S.card, amplitudes i * nodes i ^ (k : ℕ)) =
        ∑ n ∈ S, (n : ℂ) ^ (k : ℕ) * v n := by
      apply Finset.sum_bij (fun i _ => (e i : ℤ))
      · intro i _
        exact (e i).property
      · intro i _ j _ hij
        exact e.injective (Subtype.ext hij)
      · intro n hn
        refine ⟨e.symm ⟨n, hn⟩, Finset.mem_univ _, ?_⟩
        exact congrArg Subtype.val (e.apply_symm_apply ⟨n, hn⟩)
      · intro i _
        change v (e i) * ((e i : ℤ) : ℂ) ^ (k : ℕ) =
          ((e i : ℤ) : ℂ) ^ (k : ℕ) * v (e i)
        exact mul_comm _ _
    rw [hsum, hmoments (k : ℕ)]
    simp
  have hamp : amplitudes = (0 : Fin S.card → ℂ) :=
    finite_moment_readout_injective hnodes hread
  intro n hn
  simpa only [amplitudes, Pi.zero_apply, Equiv.apply_symm_apply] using
    congrFun hamp (e.symm ⟨n, hn⟩)

/-!
Quantitative continuation (isolated source candidate, not natively validated).
The original source above is preserved byte for byte. Its older UNCOMPILED
comments predate inputs/actual-qualitative-acceptance.json: the pinned original
D5 and Reg are recorded there as compiled with standard3 axioms, and the
original registration as declared_validated. That evidence does not validate
any declaration in this continuation.

The argument is the standard least-moment/Vandermonde argument followed by an
actual-symbol envelope and finite-annulus tail subtraction. Constants depend
on the particular head. No novelty or physical/signed Weil/RH claim is made.
-/

private def powerHead (v : ℤ → ℂ) (k : ℕ) : ℤ → ℂ :=
  fun n => (n : ℂ) ^ k * v n

private def momentEnergy (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (k : ℕ) : ℝ :=
  ‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v k n‖ ^ 2 +
    smoothFloor c ^ 2 * ‖∑ n ∈ S, powerHead v k n‖ ^ 2

private theorem quantitative_floor_pos {c : ℕ} (hc : 2 ≤ c) :
    0 < smoothFloor c := by
  have hL : 0 < logLength c := PrimeSymbolMeanSquare.logLength_pos hc
  have he : Real.exp (-logLength c / 2) < 1 := by
    calc
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith only [hL])
      _ = 1 := Real.exp_zero
  exact div_pos (sub_pos.mpr he) (by norm_num : (0 : ℝ) < 10)

private theorem moments_vanish_of_energy_nonpos {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (k : ℕ) (hq : momentEnergy c S v k ≤ 0) :
    (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v k n) = 0 ∧
      (∑ n ∈ S, powerHead v k n) = 0 := by
  let a : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v k n
  let b : ℂ := ∑ n ∈ S, powerHead v k n
  change ‖a‖ ^ 2 + smoothFloor c ^ 2 * ‖b‖ ^ 2 ≤ 0 at hq
  have ha : ‖a‖ ^ 2 = 0 := le_antisymm
    (by linarith only [hq, mul_nonneg (sq_nonneg (smoothFloor c)) (sq_nonneg ‖b‖)])
    (sq_nonneg _)
  have hbprod : smoothFloor c ^ 2 * ‖b‖ ^ 2 = 0 := le_antisymm
    (by linarith only [hq, sq_nonneg ‖a‖])
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb : ‖b‖ ^ 2 = 0 := (mul_eq_zero.mp hbprod).resolve_left
    (ne_of_gt (pow_pos (quantitative_floor_pos hc) 2))
  have han : ‖a‖ = 0 := by
    rcases mul_eq_zero.mp (show ‖a‖ * ‖a‖ = 0 by simpa only [pow_two] using ha)
      with h | h <;> exact h
  have hbn : ‖b‖ = 0 := by
    rcases mul_eq_zero.mp (show ‖b‖ * ‖b‖ = 0 by simpa only [pow_two] using hb)
      with h | h <;> exact h
  exact ⟨norm_eq_zero.mp han, norm_eq_zero.mp hbn⟩

-- Only the first card(S) beta moments are used in this Vandermonde step.
private theorem positive_moment_below_card {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (hnonzero : ∃ n ∈ S, v n ≠ 0) :
    ∃ k : ℕ, k < S.card ∧ 0 < momentEnergy c S v k := by
  classical
  by_contra hnone
  have hmoments (j : ℕ) (hj : j < S.card) :
      (∑ n ∈ S, (n : ℂ) ^ j * v n) = 0 := by
    have hq : momentEnergy c S v j ≤ 0 := le_of_not_gt (by
      intro hp
      exact hnone ⟨j, hj, hp⟩)
    exact (moments_vanish_of_energy_nonpos hc S v j hq).2
  let e : Fin S.card ≃ S := S.equivFin.symm
  let nodes : Fin S.card → ℂ := fun i => ((e i : ℤ) : ℂ)
  let amplitudes : Fin S.card → ℂ := fun i => v (e i)
  have hnodes : Function.Injective nodes := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    have hcast : ((e i : ℤ) : ℂ) = ((e j : ℤ) : ℂ) := hij
    exact_mod_cast hcast
  have hread : finiteMomentReadout nodes amplitudes =
      finiteMomentReadout nodes (0 : Fin S.card → ℂ) := by
    funext j
    rw [finite_moment_readout_apply, finite_moment_readout_apply]
    have hsum : (∑ i : Fin S.card, amplitudes i * nodes i ^ (j : ℕ)) =
        ∑ n ∈ S, (n : ℂ) ^ (j : ℕ) * v n := by
      apply Finset.sum_bij (fun i _ => (e i : ℤ))
      · intro i _
        exact (e i).property
      · intro i _ l _ hil
        exact e.injective (Subtype.ext hil)
      · intro n hn
        refine ⟨e.symm ⟨n, hn⟩, Finset.mem_univ _, ?_⟩
        exact congrArg Subtype.val (e.apply_symm_apply ⟨n, hn⟩)
      · intro i _
        change v (e i) * ((e i : ℤ) : ℂ) ^ (j : ℕ) =
          ((e i : ℤ) : ℂ) ^ (j : ℕ) * v (e i)
        exact mul_comm _ _
    rw [hsum, hmoments (j : ℕ) j.isLt]
    simp
  have hamp : amplitudes = (0 : Fin S.card → ℂ) :=
    finite_moment_readout_injective hnodes hread
  obtain ⟨n, hn, hvn⟩ := hnonzero
  apply hvn
  simpa only [amplitudes, Pi.zero_apply, Equiv.apply_symm_apply] using
    congrFun hamp (e.symm ⟨n, hn⟩)

-- Reuses the original exact recurrence, including its /pi and diagonal case.
private theorem column_power_of_vanishing (c : ℕ) (S : Finset ℤ)
    (v : ℤ → ℂ) (k : ℕ)
    (hzero : ∀ j < k,
      (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v j n) = 0 ∧
        (∑ n ∈ S, powerHead v j n) = 0) (m : ℤ) :
    couplingColumn c S (powerHead v k) m =
      (m : ℂ) ^ k * couplingColumn c S v m := by
  revert hzero
  induction k with
  | zero =>
      intro _
      have hfun : powerHead v 0 = v := by
        funext n
        simp only [powerHead, pow_zero, one_mul]
      simp only [hfun, pow_zero, one_mul]
  | succ k ih =>
      intro hzero
      have hsmall : ∀ j < k,
          (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v j n) = 0 ∧
            (∑ n ∈ S, powerHead v j n) = 0 := by
        intro j hj
        exact hzero j (Nat.lt_trans hj (Nat.lt_succ_self k))
      have hfun : powerHead v (k + 1) =
          (fun n : ℤ => (n : ℂ) * powerHead v k n) := by
        funext n
        simp only [powerHead, pow_succ]
        ring
      rw [hfun, coupling_column_recurrence,
        (hzero k (Nat.lt_succ_self k)).1,
        (hzero k (Nat.lt_succ_self k)).2]
      simp only [mul_zero, sub_zero, zero_div]
      rw [ih hsmall, pow_succ]
      ring

private theorem paired_power_energy (c : ℕ) (S : Finset ℤ)
    (v : ℤ → ℂ) (k : ℕ)
    (hzero : ∀ j < k,
      (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v j n) = 0 ∧
        (∑ n ∈ S, powerHead v j n) = 0) (m : ℕ) :
    ‖couplingColumn c S (powerHead v k) (m : ℤ)‖ ^ 2 +
      ‖couplingColumn c S (powerHead v k) (-(m : ℤ))‖ ^ 2 =
    (m : ℝ) ^ (2 * k) *
      (‖couplingColumn c S v (m : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-(m : ℤ))‖ ^ 2) := by
  have hposcast : ((m : ℤ) : ℂ) = (m : ℂ) := Int.cast_natCast m
  have hnegcast : ((-(m : ℤ) : ℤ) : ℂ) = -((m : ℤ) : ℂ) :=
    Int.cast_neg (m : ℤ)
  have hp : ‖((m : ℤ) : ℂ)‖ = (m : ℝ) := by
    calc
      ‖((m : ℤ) : ℂ)‖ = ‖(m : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖z‖) hposcast
      _ = (m : ℝ) := Complex.norm_natCast m
  have hn : ‖((-(m : ℤ) : ℤ) : ℂ)‖ = (m : ℝ) := by
    calc
      ‖((-(m : ℤ) : ℤ) : ℂ)‖ = ‖-((m : ℤ) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖z‖) hnegcast
      _ = ‖((m : ℤ) : ℂ)‖ := norm_neg _
      _ = (m : ℝ) := hp
  rw [column_power_of_vanishing c S v k hzero (m : ℤ),
    column_power_of_vanishing c S v k hzero (-(m : ℤ))]
  simp only [norm_mul, norm_pow, hp, hn, mul_pow, ← pow_mul]
  rw [Nat.mul_comm k 2]
  ring

-- Uniformity here is in the exterior mode for this fixed actual head.
private theorem column_norm_envelope {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ}
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (m : ℤ)
    (hm : 0 < |(m : ℝ)|) (hhalf : 2 * A ≤ |(m : ℝ)|) :
    ‖couplingColumn c S v m‖ ≤
      4 * arithmeticBoundaryBudget c * (∑ n ∈ S, ‖v n‖) /
        (Real.pi * |(m : ℝ)|) := by
  classical
  have hB : 0 ≤ arithmeticBoundaryBudget c :=
    (abs_nonneg _).trans (arithmetic_boundary_symbol_bound hc 0).2
  have hcoef (n : ℤ) (hn : n ∈ S) :
      ‖((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
        (Real.pi * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ))‖ ≤
        4 * arithmeticBoundaryBudget c / (Real.pi * |(m : ℝ)|) := by
    have htri := abs_add_le ((m : ℝ) - (n : ℝ)) (n : ℝ)
    rw [sub_add_cancel] at htri
    have hdist : |(m : ℝ)| / 2 ≤ |(m : ℝ) - (n : ℝ)| := by
      linarith only [htri, hS n hn, hhalf]
    have hnum : |arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m| ≤
        2 * arithmeticBoundaryBudget c :=
      (abs_sub _ _).trans (by linarith only
        [(arithmetic_boundary_symbol_bound hc n).2,
          (arithmetic_boundary_symbol_bound hc m).2])
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_pos Real.pi_pos]
    calc
      _ ≤ (2 * arithmeticBoundaryBudget c) /
          (Real.pi * |(m : ℝ) - (n : ℝ)|) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * arithmeticBoundaryBudget c) /
          (Real.pi * (|(m : ℝ)| / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hdist Real.pi_pos.le)
      _ = _ := by field_simp [Real.pi_ne_zero, hm.ne'] <;> ring
  unfold couplingColumn
  calc
    _ ≤ ∑ n ∈ S, ‖((((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
        (Real.pi * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ)) * v n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (4 * arithmeticBoundaryBudget c /
        (Real.pi * |(m : ℝ)|)) * ‖v n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcoef n hn) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

-- The explicit upper U is derived, rather than passed as an assumption.
private theorem paired_tail_coarse_upper {c N : ℕ} (hc : 2 ≤ c)
    (hN : 0 < N) (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ}
    (hA : 0 ≤ A) (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hhalf : 2 * A ≤ (N : ℝ)) :
    Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ, (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      (32 * arithmeticBoundaryBudget c ^ 2 * (∑ n ∈ S, ‖v n‖) ^ 2 /
        Real.pi ^ 2) / (N : ℝ) := by
  classical
  let E : ℕ → ℝ := fun j =>
    ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2
  let U : ℝ := 32 * arithmeticBoundaryBudget c ^ 2 *
    (∑ n ∈ S, ‖v n‖) ^ 2 / Real.pi ^ 2
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsep : A < (N : ℝ) + 1 := by linarith only [hhalf, hA]
  have hs : Summable E :=
    (ActualFullSymbolTail.paired_coupling_column_tail hc hN S v hA hS hsep).1
  have hpoint (j : ℕ) : E j ≤ U * (((N : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2 := by
    let t : ℝ := ((N + j + 1 : ℕ) : ℝ)
    have ht : 0 < t := by dsimp [t]; positivity
    have hNt : (N : ℝ) ≤ t := by dsimp [t]; push_cast; linarith
    have hposcast : (((N + j + 1 : ℕ) : ℤ) : ℝ) = t := by
      change (((N + j + 1 : ℕ) : ℤ) : ℝ) = ((N + j + 1 : ℕ) : ℝ)
      exact Int.cast_natCast (N + j + 1)
    have hnegcast : ((-((N + j + 1 : ℕ) : ℤ) : ℤ) : ℝ) = -t := by
      calc
        ((-((N + j + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
            -(((N + j + 1 : ℕ) : ℤ) : ℝ) := Int.cast_neg _
        _ = -t := congrArg (fun x : ℝ => -x) hposcast
    have hposabs : |(((N + j + 1 : ℕ) : ℤ) : ℝ)| = t := by
      rw [hposcast, abs_of_pos ht]
    have hnegabs : |((-((N + j + 1 : ℕ) : ℤ) : ℤ) : ℝ)| = t := by
      rw [hnegcast, abs_neg, abs_of_pos ht]
    have hp := column_norm_envelope hc S v hS ((N + j + 1 : ℕ) : ℤ)
      (by rw [hposabs]; exact ht)
      (by rw [hposabs]; exact hhalf.trans hNt)
    have hn := column_norm_envelope hc S v hS (-((N + j + 1 : ℕ) : ℤ))
      (by rw [hnegabs]; exact ht)
      (by rw [hnegabs]; exact hhalf.trans hNt)
    have hp' : ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ≤
        4 * arithmeticBoundaryBudget c * (∑ n ∈ S, ‖v n‖) / (Real.pi * t) := by
      rw [hposabs] at hp
      exact hp
    have hn' : ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ≤
        4 * arithmeticBoundaryBudget c * (∑ n ∈ S, ‖v n‖) / (Real.pi * t) := by
      rw [hnegabs] at hn
      exact hn
    calc
      E j ≤ 2 * (4 * arithmeticBoundaryBudget c * (∑ n ∈ S, ‖v n‖) /
          (Real.pi * t)) ^ 2 := by
        have hps := pow_le_pow_left₀ (norm_nonneg _) hp' 2
        have hns := pow_le_pow_left₀ (norm_nonneg _) hn' 2
        dsimp only [E]
        linarith only [hps, hns]
      _ = U * (((N : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2 := by
        have htcast : t = (N : ℝ) + (j : ℝ) + 1 := by
          simp only [t, Nat.cast_add, Nat.cast_one]
        rw [← htcast]
        dsimp only [U]
        field_simp [Real.pi_ne_zero, ht.ne'] <;> ring
  have hpartial (r : ℕ) : (∑ j ∈ Finset.range r, E j) ≤ U / (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range r,
          U * (((N : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2 :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = U * ∑ j ∈ Finset.range r, (((N : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ U * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left
        (WeilInfiniteComplementLeakage.inverse_square_partial_le hNR r) hU
      _ = _ := by rw [div_eq_mul_inv]
  exact ⟨hs, Real.tsum_le_of_sum_range_le
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _)) hpartial⟩

-- This is a real finite-annulus comparison, not division of an infinite
-- weighted sum by a purported uniform mode bound.
private theorem finite_annulus_transfer (f g : ℕ → ℝ) (N T p : ℕ)
    (hNT : N ≤ T) (hf : ∀ m, 0 ≤ f m)
    (hfs : Summable (fun j : ℕ => f (N + j + 1)))
    (hgs : Summable (fun j : ℕ => g (N + j + 1)))
    (hcompare : ∀ j < T - N, g (N + j + 1) ≤ (T : ℝ) ^ p * f (N + j + 1)) :
    (∑' j : ℕ, g (N + j + 1)) - (∑' j : ℕ, g (T + j + 1)) ≤
      (T : ℝ) ^ p * ∑' j : ℕ, f (N + j + 1) := by
  have hsplit : (∑ j ∈ Finset.range (T - N), g (N + j + 1)) +
      (∑' j : ℕ, g (T + j + 1)) = ∑' j : ℕ, g (N + j + 1) := by
    calc
      _ = (∑ j ∈ Finset.range (T - N), g (N + j + 1)) +
          (∑' j : ℕ, g (N + (j + (T - N)) + 1)) := by
        congr 1
        apply tsum_congr
        intro j
        congr 1
        omega
      _ = _ := hgs.sum_add_tsum_nat_add (T - N)
  have hdiff : (∑' j : ℕ, g (N + j + 1)) - (∑' j : ℕ, g (T + j + 1)) =
      ∑ j ∈ Finset.range (T - N), g (N + j + 1) := by
    linarith only [hsplit]
  rw [hdiff]
  calc
    _ ≤ ∑ j ∈ Finset.range (T - N), (T : ℝ) ^ p * f (N + j + 1) :=
      Finset.sum_le_sum (fun j hj => hcompare j (Finset.mem_range.mp hj))
    _ = (T : ℝ) ^ p * ∑ j ∈ Finset.range (T - N), f (N + j + 1) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum (Finset.range (T - N)) (fun j _ => hf _) hfs)
      (pow_nonneg (Nat.cast_nonneg T) p)

/-- Every nonzero finite integer head has an eventual polynomial lower tail
for its actual paired exterior-column energy, with exponent below 2*card(S).
All cutoffs and the positive coefficient are constructed from the head. -/
theorem actual_finite_head_polynomial_tail_lower {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) (hnonzero : ∃ n ∈ S, v n ≠ 0) :
    ∃ k : ℕ, k < S.card ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        Summable (fun j : ℕ =>
          ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
        C / ((N : ℝ) + 1) ^ (2 * k + 1) ≤
          ∑' j : ℕ, (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) := by
  classical
  have hex := positive_moment_below_card hc S v hnonzero
  let k : ℕ := Nat.find hex
  have hk : k < S.card ∧ 0 < momentEnergy c S v k := Nat.find_spec hex
  have hzero (j : ℕ) (hj : j < k) :
      (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * powerHead v j n) = 0 ∧
        (∑ n ∈ S, powerHead v j n) = 0 := by
    apply moments_vanish_of_energy_nonpos hc S v j
    apply le_of_not_gt
    intro hp
    exact Nat.find_min hex hj ⟨hj.trans hk.1, hp⟩
  let w : ℤ → ℂ := powerHead v k
  let alpha : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * w n
  let beta : ℂ := ∑ n ∈ S, w n
  let q : ℝ := ‖alpha‖ ^ 2 + smoothFloor c ^ 2 * ‖beta‖ ^ 2
  have hq : 0 < q := hk.2
  let A : ℝ := ∑ n ∈ S, |(n : ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => abs_nonneg (n : ℝ))
  have hS : ∀ n ∈ S, |(n : ℝ)| ≤ A := by
    intro n hn
    calc
      |(n : ℝ)| = ∑ l ∈ S, if l = n then |(l : ℝ)| else 0 := by simp [hn]
      _ ≤ ∑ l ∈ S, |(l : ℝ)| := Finset.sum_le_sum (fun l _ => by
        by_cases hln : l = n
        · simp only [if_pos hln]; exact le_rfl
        · simpa only [if_neg hln] using (abs_nonneg (l : ℝ)))
  let U : ℝ := 32 * arithmeticBoundaryBudget c ^ 2 *
    (∑ n ∈ S, ‖w n‖) ^ 2 / Real.pi ^ 2
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (8 * Real.pi ^ 2 * U / q))
  have hL1 : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL.le
  have hLcut : 8 * Real.pi ^ 2 * U / q ≤ (L : ℝ) :=
    (le_max_right _ _).trans hL.le
  have hLR : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL1
  have hLnat : 1 ≤ L := by exact_mod_cast hL1
  let C : ℝ := q / (8 * Real.pi ^ 2 * (L : ℝ) ^ (2 * k))
  have hC : 0 < C := div_pos hq (by positivity)
  let P : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
  let D0 : ℝ := 2 * ActualFullSymbolTail.primeFirstMoment c * (2 + P)
  let mix : ℝ := 2 * ‖beta‖ ^ 2 * D0 / q
  let K : ℝ := 256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S w ^ 2 / (3 * q)
  let B : ℝ := max 1 (max (2 * A) (max (logLength c / (2 * Real.pi)) (max mix K)))
  obtain ⟨N0, hN0⟩ := exists_nat_gt B
  refine ⟨k, hk.1, C, hC, N0, ?_⟩
  intro N hNN
  have hBN : B ≤ (N : ℝ) := hN0.le.trans (by exact_mod_cast hNN)
  have hbounds : 1 ≤ (N : ℝ) ∧ 2 * A ≤ (N : ℝ) ∧
      logLength c / (2 * Real.pi) ≤ (N : ℝ) ∧
      mix ≤ (N : ℝ) ∧ K ≤ (N : ℝ) := by
    simpa only [B, max_le_iff] using hBN
  obtain ⟨hN1, hNA, hNL, hNMix, hNK⟩ := hbounds
  have hNpos : 0 < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN1)
  have hlog : 0 < logLength c := PrimeSymbolMeanSquare.logLength_pos hc
  have hfreq : 1 ≤ frequency c ((N + 1 : ℕ) : ℤ) := by
    have hLN : logLength c ≤ (N : ℝ) * (2 * Real.pi) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hNL
    unfold frequency
    apply (le_div_iff₀ hlog).mpr
    push_cast
    nlinarith only [hLN, Real.pi_pos]
  have hgap : 2 * A ≤ (N : ℝ) + 1 := by linarith only [hNA]
  have hmix : 2 * ‖beta‖ ^ 2 * D0 / q ≤ (N : ℝ) + 1 := by
    change mix ≤ (N : ℝ) + 1
    linarith only [hNMix]
  have hNsquare : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hp := mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hN1)
    nlinarith only [hp]
  have hcut : 256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S w ^ 2 / (3 * q) ≤
      (N : ℝ) ^ 2 := hNK.trans hNsquare
  have hlower := ActualFullSymbolTail.paired_coupling_column_tail_lower
    hc hNpos S w hA hS hfreq hgap hq hmix hcut
  have hvsum := (paired_tail_coarse_upper hc hNpos S v hA hS hNA).1
  let f : ℕ → ℝ := fun m =>
    ‖couplingColumn c S v (m : ℤ)‖ ^ 2 + ‖couplingColumn c S v (-(m : ℤ))‖ ^ 2
  let g : ℕ → ℝ := fun m =>
    ‖couplingColumn c S w (m : ℤ)‖ ^ 2 + ‖couplingColumn c S w (-(m : ℤ))‖ ^ 2
  let t : ℝ := (N : ℝ) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let T : ℕ := L * (N + 1)
  have hNT : N ≤ T := by
    have hmul : N + 1 ≤ T := by
      dsimp only [T]
      simpa only [one_mul] using Nat.mul_le_mul_right (N + 1) hLnat
    exact (Nat.le_succ N).trans hmul
  have hTpos : 0 < T := lt_of_lt_of_le hNpos hNT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hTcast : (T : ℝ) = (L : ℝ) * t := by
    simp only [T, t, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hTA : 2 * A ≤ (T : ℝ) := hNA.trans (by exact_mod_cast hNT)
  have hupper : (∑' j : ℕ, g (T + j + 1)) ≤ U / (T : ℝ) :=
    (paired_tail_coarse_upper hc hTpos S w hA hS hTA).2
  have hupper_small : (∑' j : ℕ, g (T + j + 1)) ≤ q / (8 * Real.pi ^ 2 * t) := by
    apply hupper.trans
    apply (div_le_div_iff₀ hTR (by positivity)).2
    rw [hTcast]
    have hscale : 8 * Real.pi ^ 2 * U ≤ (L : ℝ) * q :=
      (div_le_iff₀ hq).1 hLcut
    nlinarith only [mul_le_mul_of_nonneg_right hscale ht.le]
  have hlower' : q / (4 * Real.pi ^ 2 * t) ≤ ∑' j : ℕ, g (N + j + 1) := hlower.2
  have hdiff : q / (8 * Real.pi ^ 2 * t) ≤
      (∑' j : ℕ, g (N + j + 1)) - (∑' j : ℕ, g (T + j + 1)) := by
    have hid : q / (4 * Real.pi ^ 2 * t) = 2 * (q / (8 * Real.pi ^ 2 * t)) := by
      field_simp [Real.pi_ne_zero, ht.ne'] <;> ring
    linarith only [hlower', hupper_small, hid]
  have hcompare (j : ℕ) (hj : j < T - N) :
      g (N + j + 1) ≤ (T : ℝ) ^ (2 * k) * f (N + j + 1) := by
    change (‖couplingColumn c S (powerHead v k) ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingColumn c S (powerHead v k) (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ≤ _
    rw [paired_power_energy c S v k hzero]
    have hmT : N + j + 1 ≤ T := by omega
    have hcast : ((N + j + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hmT
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcast (2 * k))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hannulus := finite_annulus_transfer f g N T (2 * k) hNT
    (fun m => add_nonneg (sq_nonneg _) (sq_nonneg _)) hvsum hlower.1 hcompare
  have hproduct : q / (8 * Real.pi ^ 2 * t) ≤
      (T : ℝ) ^ (2 * k) * ∑' j : ℕ, f (N + j + 1) := hdiff.trans hannulus
  have henergy : (q / (8 * Real.pi ^ 2 * t)) / (T : ℝ) ^ (2 * k) ≤
      ∑' j : ℕ, f (N + j + 1) :=
    (div_le_iff₀ (pow_pos hTR (2 * k))).2 (by simpa only [mul_comm] using hproduct)
  refine ⟨hvsum, ?_⟩
  calc
    C / ((N : ℝ) + 1) ^ (2 * k + 1) =
        (q / (8 * Real.pi ^ 2 * t)) / (T : ℝ) ^ (2 * k) := by
      change C / t ^ (2 * k + 1) = _
      rw [hTcast, mul_pow, pow_succ]
      dsimp only [C]
      field_simp [Real.pi_ne_zero, hLR.ne', ht.ne'] <;> ring
    _ ≤ _ := henergy

end D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
