/- GID: D5/S3/Quantum/ShorContinuedFractions
   generality: G
   mirror-B: D5/B/S3/Quantum/ShorContinuedFractions
   mirror-E: none(waiver:general-rational-recursion-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.Basic]
   utility: none
   digest: Circular nearest Shor samples place the reduced phase in observable candidates. -/

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/HilbertOperators/aicyberg2026shor.md. Authors: aicyberg.
Source: solanaqubits/leanbook, commit 9b742770a2a5dbcf30cf9abc44e711194e957a00,
Verification/QuantumShorContinuedFractions.lean.
Retire this slice when equivalent declarations exist in the receiving pinned
Mathlib, replacing the slice with direct imports at that repository pin.
-/

import D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents
import D5.S3.Quantum.ShorCountingMarginal
import Mathlib.RingTheory.Fintype
import Mathlib.Tactic.FieldSimp

namespace QuantumShorContinuedFractions

private theorem candidate_divisor_property (s r : ℕ) (hr : 0 < r) :
    (reduced s r).den = r / Nat.gcd s r ∧ (reduced s r).den ∣ r := by
  rw [reduced_den s r hr]
  exact ⟨rfl, Nat.div_dvd_of_dvd (Nat.gcd_dvd_right s r)⟩

private theorem reduced_den_le (s r : ℕ) (hr : 0 < r) : (reduced s r).den ≤ r := by
  rw [reduced_den s r hr]; exact Nat.div_le_self _ _

private theorem legendre_approximation_condition {N Q r s y : ℕ}
    (hr : 0 < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q)
    (hnear : |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ))) :
    |(y : ℝ) / Q - (reduced s r : ℝ)| <
      1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by
  have hd := (reduced s r).pos
  have hle := reduced_den_le s r hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (r : ℝ) < N := by exact_mod_cast hrN
  have hqR : (N : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQ
  have hdR : (0 : ℝ) < (reduced s r).den := by exact_mod_cast hd
  have hlR : ((reduced s r).den : ℝ) ≤ r := by exact_mod_cast hle
  have hsquare : ((reduced s r).den : ℝ) ^ 2 < Q := by nlinarith
  have hb : 1 / (2 * (Q : ℝ)) < 1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have heq : (reduced s r : ℝ) = (s : ℝ) / r := by simp [reduced]
  rw [heq]
  exact hnear.trans_lt hb

private theorem convergent_recovery_soundness {N Q r s y : ℕ}
    (hr : 0 < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q)
    (hnear : |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ))) :
    reduced s r ∈ candidates y Q N := by
  have h := legendre_approximation_condition hr hrN hQ hnear
  have hc : |(((y : ℚ) / Q : ℚ) : ℝ) - (reduced s r : ℝ)| <
      1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by simpa using h
  obtain ⟨k, hk⟩ := Real.exists_rat_eq_convergent hc
  apply List.mem_filter.mpr
  exact ⟨(mem_convergents_iff _ _).mpr ⟨k, hk.symm⟩, by
    simpa using (lt_of_le_of_lt (reduced_den_le s r hr) hrN)⟩

private theorem exact_order_recovery_when_coprime (s r : ℕ) (hr : 0 < r)
    (hcop : Nat.Coprime s r) : (reduced s r).den = r := by
  simp [reduced_den s r hr, hcop.gcd_eq_one]

/-- In the sufficiently resolved order-finding setting a modular nearest sample
has no wrap-around ambiguity, even for s=0 or either rounding tie. -/
private theorem nearest_has_no_wrap {N Q r s y : ℕ}
    (hr : 0 < r) (hs : s < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q) (hy : y < Q)
    (hnear : ∃ z : ℤ, |(s : ℝ) / r - (y : ℝ) / Q - z| ≤ 1 / (2 * (Q : ℝ))) :
    |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ)) := by
  have hN : 0 < N := by omega
  have hQp : 0 < Q := lt_of_lt_of_le (pow_pos hN 2) hQ
  have hrQ : r < Q := by nlinarith
  have rpos : (0 : ℝ) < r := by exact_mod_cast hr
  have Qpos : (0 : ℝ) < Q := by exact_mod_cast hQp
  have sr : (s : ℝ) + 1 ≤ r := by exact_mod_cast (show s + 1 ≤ r by omega)
  have yQ : (y : ℝ) + 1 ≤ Q := by exact_mod_cast (show y + 1 ≤ Q by omega)
  have rq : (r : ℝ) < Q := by exact_mod_cast hrQ
  have slow : (0 : ℝ) ≤ (s : ℝ) / r := by positivity
  have ylow : (0 : ℝ) ≤ (y : ℝ) / Q := by positivity
  have sup : (s : ℝ) / r ≤ 1 - 1 / (r : ℝ) := by
    apply (div_le_iff₀ rpos).mpr
    field_simp
    nlinarith
  have yup : (y : ℝ) / Q ≤ 1 - 1 / (Q : ℝ) := by
    apply (div_le_iff₀ Qpos).mpr
    field_simp
    nlinarith
  have epsQ : 1 / (2 * (Q : ℝ)) < 1 / (Q : ℝ) :=
    one_div_lt_one_div_of_lt Qpos (by linarith)
  have epsr : 1 / (2 * (Q : ℝ)) < 1 / (r : ℝ) :=
    one_div_lt_one_div_of_lt rpos (by linarith)
  obtain ⟨z, hz⟩ := hnear
  have hzlo := (abs_le.mp hz).1
  have hzhi := (abs_le.mp hz).2
  have zlo : (-1 : ℝ) < z := by linarith
  have zhi : (z : ℝ) < 1 := by linarith
  have zz : z = 0 := by
    have : (-1 : ℤ) < z := by exact_mod_cast zlo
    have : z < (1 : ℤ) := by exact_mod_cast zhi
    omega
  simpa [zz, abs_sub_comm] using hz

open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral

private theorem period_lt_modulus (c : Parameters) : c.period < c.modulus :=
  ZMod.orderOf_lt c.modulus_ge_two _

/-- The measured modular-nearest event from the existing QPE model supplies the
entire deterministic recovery contract, with no period input to candidates. -/
theorem shor_nearest_candidate (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y) :
    reduced s.val c.period ∈ candidates y.val (2 ^ n) c.modulus ∧
      (reduced s.val c.period).den ∣ c.period := by
  refine ⟨convergent_recovery_soundness c.period_pos (period_lt_modulus c) hsize ?_,
    (candidate_divisor_property s.val c.period c.period_pos).2⟩
  exact nearest_has_no_wrap c.period_pos s.isLt (period_lt_modulus c) hsize y.isLt hnear

/-- The reduced candidate is the order exactly when its numerator is coprime.
Other entries in the candidate list are not asserted to divide the order. -/
theorem shor_coprime_candidate (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y)
    (hcop : Nat.Coprime s.val c.period) :
    c.period ∈ (candidates y.val (2 ^ n) c.modulus).map Rat.den := by
  obtain ⟨hmem, _⟩ := shor_nearest_candidate c n hsize s y hnear
  exact List.mem_map.mpr ⟨_, hmem,
    exact_order_recovery_when_coprime s.val c.period c.period_pos hcop⟩


end QuantumShorContinuedFractions
