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
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

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

end D5.S3.Weil.ZetaBridge.ActualFiniteHeadFaithfulness
