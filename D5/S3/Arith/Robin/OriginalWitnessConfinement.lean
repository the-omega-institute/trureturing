/- GID: D5/S3/Arith/Robin/OriginalWitnessConfinement
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalWitnessConfinement
   mirror-E: none(waiver:analytic-attainment)
   anchors: []
   utility: none
   digest: Positive witnesses supply complete original windows and confine all maximizing ties. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.MertensExplicitEnvelope
import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Weil.GronwallUpperEnvelope

/-!
The full-domain attainment argument consumes the weak Gronwall/Mertens bound,
an actual padded integer and a finite maximum with a strict global tail gap.
The original objective, label interval and selected domain remain literal.
-/

noncomputable section

namespace D5.S3.Arith.Robin.OriginalWitnessConfinement

open Finset
open D5.S3.Arith.Robin.OriginalFirstClockTransport

private theorem weak_envelope {n : ℕ} (hn : 0 < n)
    (hA : 286 ≤ Real.log (n : ℝ)) :
    originalObjective n - Real.eulerMascheroniConstant ≤
      39 / (10 * Real.log (Real.log (n : ℝ))) := by
  let A := Real.log (n : ℝ)
  have hA0 : 0 < A := by dsimp [A]; linarith
  have hA1 : 1 < A := by dsimp [A]; linarith
  have hl : 0 < Real.log A := Real.log_pos hA1
  have hs : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  have hsplit := D5.S3.Weil.GronwallUpperEnvelope.sigma_split hn
    (y := A) (by dsimp [A]; linarith)
  have hm := D5.S3.Arith.Robin.MertensExplicitEnvelope.prime_product_upper_effective hA
  rw [← Finset.prod_inv_distrib] at hm
  have hb : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      Real.exp Real.eulerMascheroniConstant * Real.log A *
        Real.exp (39 / (10 * Real.log A)) := by
    calc
      _ ≤ (Real.exp Real.eulerMascheroniConstant * Real.log A *
          Real.exp ((19 / 10 : ℝ) / Real.log A)) *
          Real.exp (2 * Real.log n / (A * Real.log A)) :=
        hsplit.trans (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le)
      _ = _ := by
        have he : (19 / 10 : ℝ) / Real.log A +
            2 * Real.log n / (A * Real.log A) = 39 / (10 * Real.log A) := by
          change (19 / 10 : ℝ) / Real.log A + 2 * A / (A * Real.log A) =
            39 / (10 * Real.log A)
          field_simp [hA0.ne', hl.ne']
          ring
        rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add, he]
  have hlog := Real.log_le_log hs hb
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hl).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' hl.ne', Real.log_exp, Real.log_exp] at hlog
  change Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) -
    Real.log (Real.log A) - Real.eulerMascheroniConstant ≤ _
  linarith

private theorem strict_tail {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (hcut : 286 ≤ Real.exp (39 / (5 * δ)))
    (htail : Real.exp (39 / (5 * δ)) < Real.log (n : ℝ)) :
    originalObjective n < Real.eulerMascheroniConstant + δ / 2 := by
  have hA := hcut.trans htail.le
  have hlogA : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos (by linarith)
  have hc : 39 / (5 * δ) < Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_lt_log (Real.exp_pos (39 / (5 * δ))) htail
    simpa only [Real.log_exp] using h
  have hprod := (div_lt_iff₀ (by positivity : 0 < 5 * δ)).mp hc
  have herr : 39 / (10 * Real.log (Real.log (n : ℝ))) < δ / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.log (Real.log (n : ℝ)))).mpr
    nlinarith
  linarith [weak_envelope hn hA]

private theorem padded_witness {m p : ℕ} {δ ell : ℝ}
    (hm : 1 < Real.log (m : ℝ)) (hp : p.Prime)
    (hpupper : Real.log (p : ℝ) ≤ 2 * ell)
    (hw : Real.eulerMascheroniConstant + δ ≤ originalObjective m)
    (hpad : (Real.log (5040 : ℝ) + 2 * ell) /
      (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) ≤ δ / 2) :
    ∃ D : ℕ, 1 ≤ D ∧ 5040 * p ∣ D ∧
      Real.eulerMascheroniConstant + δ / 2 ≤ originalObjective D := by
  have hm0 : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    norm_num [this] at hm
  let L := Nat.lcm 5040 m
  let D := p * L
  have hL0 : 0 < L := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by norm_num) hm0.ne')
  have hD0 : 0 < D := Nat.mul_pos hp.pos hL0
  have hmL : m ≤ L := Nat.le_of_dvd hL0 (Nat.dvd_lcm_right 5040 m)
  have hmD : m ∣ D := (Nat.dvd_lcm_right 5040 m).trans (dvd_mul_left L p)
  have hforced : 5040 * p ∣ D := by
    change 5040 * p ∣ p * L
    rw [Nat.mul_comm p L]
    exact Nat.mul_dvd_mul_right (Nat.dvd_lcm_left 5040 m) p
  have hmDlt : m < D := by
    have : 2 * L ≤ D := Nat.mul_le_mul_right L hp.two_le
    omega
  have hclock : Real.log (m : ℝ) < Real.log (D : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hm0) (by exact_mod_cast hmDlt)
  have hDclock : 1 < Real.log (D : ℝ) := hm.trans hclock
  have hLle : L ≤ 5040 * m := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 5040 m)
  have hDle : D ≤ p * (5040 * m) := Nat.mul_le_mul_left p hLle
  have hclockle : Real.log (D : ℝ) - Real.log (m : ℝ) ≤
      Real.log (5040 : ℝ) + 2 * ell := by
    have hb := Real.log_le_log (by exact_mod_cast hD0 : 0 < (D : ℝ))
      (by exact_mod_cast hDle : (D : ℝ) ≤ (p : ℝ) * ((5040 : ℝ) * m))
    have heq : Real.log ((p : ℝ) * ((5040 : ℝ) * m)) =
        Real.log (p : ℝ) + (Real.log (5040 : ℝ) + Real.log (m : ℝ)) := by
      rw [Real.log_mul (by exact_mod_cast hp.ne_zero) (by positivity),
        Real.log_mul (by norm_num) (by exact_mod_cast hm0.ne')]
    rw [heq] at hb
    linarith
  have hden : 0 < Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) :=
    mul_pos (by linarith) (Real.log_pos hm)
  have hcost := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
    hm hDclock (ne_of_lt hclock)
  have hcost' : Real.log (Real.log (Real.log (D : ℝ))) -
      Real.log (Real.log (Real.log (m : ℝ))) ≤ δ / 2 := by
    have heq : (Real.log (D : ℝ) - Real.log (m : ℝ)) *
        D5.S3.Arith.Robin.ActualRobinClockCovariance.g (Real.log (m : ℝ)) =
        (Real.log (D : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) := by
      unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
      simp only [div_eq_mul_inv, one_mul]
    exact hcost.le.trans (heq.trans_le
      ((div_le_div_of_nonneg_right hclockle hden.le).trans hpad))
  have hab := D5.S3.Arith.Robin.GA2ForcedPrimeSource.abundancy_mono
    (by omega : 1 ≤ m) (by omega : 1 ≤ D) hmD
  have hW := Real.log_le_log
    (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm0.ne')
      (by exact_mod_cast hm0) : 0 < (ArithmeticFunction.sigma 1 m : ℝ) / m) hab
  refine ⟨D, by omega, hforced, ?_⟩
  unfold originalObjective at hw ⊢
  linarith

private theorem attained_and_confined {m p : ℕ} {δ ell : ℝ}
    (hm : 1 < Real.log (m : ℝ)) (hδ : 0 < δ) (hp : p.Prime)
    (hplower : Real.exp ell ≤ (p : ℝ)) (hpupper : Real.log (p : ℝ) ≤ 2 * ell)
    (hw : Real.eulerMascheroniConstant + δ ≤ originalObjective m)
    (hpad : (Real.log (5040 : ℝ) + 2 * ell) /
      (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) ≤ δ / 2)
    (hcut : 286 ≤ Real.exp (39 / (5 * δ))) :
    (∃ N, originalMaximizes p N) ∧
      ∀ N, originalMaximizes p N →
        Real.eulerMascheroniConstant + δ / 2 ≤ originalObjective N ∧
        ell ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ Real.exp (39 / (5 * δ)) := by
  classical
  let R := Real.exp (39 / (5 * δ))
  obtain ⟨D, hD, hdD, hfD⟩ := padded_witness hm hp hpupper hw hpad
  have hDR : Real.log (D : ℝ) ≤ R := by
    by_contra h
    exact (not_lt_of_ge hfD) (strict_tail (by omega) hδ hcut (lt_of_not_ge h))
  let S := (Finset.Icc 1 ⌊Real.exp R⌋₊).filter (fun n => 5040 * p ∣ n)
  have hmem (n : ℕ) (hn : 1 ≤ n) (hdn : 5040 * p ∣ n) :
      n ∈ S ↔ Real.log (n : ℝ) ≤ R := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc, hn, true_and, hdn, and_true]
    exact (Nat.le_floor_iff (Real.exp_pos R).le).trans
      (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < n by omega))).symm
  have hDS : D ∈ S := (hmem D hD hdD).mpr hDR
  obtain ⟨N, hNS, hmax⟩ := S.exists_max_image originalObjective ⟨D, hDS⟩
  have hN : 1 ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hNS).1).1
  have hdN : 5040 * p ∣ N := (Finset.mem_filter.mp hNS).2
  have hfN := hfD.trans (hmax D hDS)
  have hfull : originalMaximizes p N := by
    refine ⟨hN, hdN, ?_⟩
    intro n hn hdn
    by_cases hR : Real.log (n : ℝ) ≤ R
    · exact hmax n ((hmem n hn hdn).mpr hR)
    · exact (strict_tail (by omega) hδ hcut (lt_of_not_ge hR)).le.trans hfN
  refine ⟨⟨N, hfull⟩, ?_⟩
  intro M hM
  have hfM := hfD.trans (hM.2.2 D hD hdD)
  have hMR : Real.log (M : ℝ) ≤ R := by
    by_contra h
    exact (not_lt_of_ge hfM) (strict_tail (by have := hM.1; omega) hδ hcut
      (lt_of_not_ge h))
  have hpM : p ≤ M := by
    have hbase := Nat.le_of_dvd (by have := hM.1; omega : 0 < M) hM.2.1
    nlinarith [hp.pos]
  have hlow : ell ≤ Real.log (M : ℝ) := by
    have hpMR : (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast hpM
    have hlog := Real.log_le_log (Real.exp_pos ell)
      (hplower.trans hpMR)
    simpa only [Real.log_exp] using hlog
  exact ⟨hfM, hlow, hMR⟩

/-- A positive-excess actual integer, an explicit padding budget and separated
labels supply the literal complete original window. Every full-domain tie has
the stated floor and closed clock bounds, including every canonical source.
No GA2 witness, prime absence, source order or positive selected mass is assumed. -/
theorem original_window_of_positive_witness
    {m : ℕ} {δ ell : ℝ}
    (hm : 1 < Real.log (m : ℝ)) (hδ : 0 < δ)
    (hw : Real.eulerMascheroniConstant + δ ≤ originalObjective m)
    (hpad : (Real.log (5040 : ℝ) + 2 * ell) /
      (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) ≤ δ / 2)
    (hcut : 286 ≤ Real.exp (39 / (5 * δ)))
    (hsep : 2 * Real.exp (39 / (5 * δ)) < Real.exp ell) :
    ∃ W : OriginalWindow,
      W.labelStart = ell ∧ W.labels = originalLabelWindow ell ∧
      (∀ p ∈ W.labels, ∀ N : ℕ, originalMaximizes p N →
        Real.eulerMascheroniConstant + δ / 2 ≤ originalObjective N ∧
        ell ≤ Real.log (N : ℝ) ∧
        Real.log (N : ℝ) ≤ Real.exp (39 / (5 * δ))) ∧
      OriginalBounds W ell (Real.exp (39 / (5 * δ))) := by
  classical
  have hlabels (p : ℕ) (hp : p ∈ originalLabelWindow ell) :
      p.Prime ∧ Real.exp ell ≤ (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * ell := by
    obtain ⟨hprime, hlow⟩ := Finset.mem_filter.mp hp
    obtain ⟨hup, hp⟩ := Nat.mem_primesLE.mp hprime
    refine ⟨hp, hlow, ?_⟩
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr
      ((Nat.le_floor_iff (Real.exp_pos (2 * ell)).le).mp hup)
  have hsupply (p : ℕ) (hp : p ∈ originalLabelWindow ell) :=
    attained_and_confined hm hδ (hlabels p hp).1 (hlabels p hp).2.1
      (hlabels p hp).2.2 hw hpad hcut
  let W : OriginalWindow := {
    labelStart := ell
    labels := originalLabelWindow ell
    complete_labels := rfl
    prime_labels := fun p hp => (hlabels p hp).1
    attained := fun p hp => (hsupply p hp).1 }
  refine ⟨W, rfl, rfl, fun p hp N hN => (hsupply p hp).2 N hN, ?_⟩
  intro e he
  have hedge : GoodEdge W e.1 e.2 := (Finset.mem_filter.mp he).2
  have hp := hedge.1
  have hr := hedge.2.1
  have hpc := (canonical_source_spec (W.attained e.1 hp)).1
  have hrc := (canonical_source_spec (W.attained e.2 hr)).1
  exact ⟨((hsupply e.1 hp).2 _ hpc).2.1,
    ((hsupply e.2 hr).2 _ hrc).2.2,
    hsep.trans_le (hlabels e.1 hp).2.1, hsep.trans_le (hlabels e.2 hr).2.1⟩

#print axioms original_window_of_positive_witness

end D5.S3.Arith.Robin.OriginalWitnessConfinement
