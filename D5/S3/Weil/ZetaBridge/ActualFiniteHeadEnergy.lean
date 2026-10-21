/- GID: D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The complete paired arithmetic tail has exactly the retained finite coefficients as its zero-energy kernel at every cutoff. -/

import D5.S3.Weil.ZetaBridge.ActualExplicit336
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open scoped BigOperators
open Polynomial Set MeasureTheory
open D5.S3.Analytic.PolynomialReciprocalBounds
open D5.S3.Weil.ZetaBridge
open D5.S3.Weil.ZetaBridge.ActualExplicit336
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

private lemma actual_mean_pos {c : ℕ} (hc : 3 ≤ c) : 0 < mean c := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact (div_pos (sq_pos_of_pos hl) (by norm_num)).trans_le
    (prime_symbol_mean_lower_bound hc)

/-- A nonzero complex polynomial cannot vanish on a real interval. -/
private lemma exists_nonzero_value (F : ℂ[X]) (hF : F ≠ 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, value F t ≠ 0 := by
  by_contra h
  push_neg at h
  apply hF
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hi : (Complex.ofReal '' Ioo (0 : ℝ) 1).Infinite :=
    (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn
  apply hi.mono
  rintro z ⟨t, ht, rfl⟩
  exact h t ht

/-- Strict positivity in the existing [0,1] integral normalization. -/
private lemma polynomial_energy_pos (F : ℂ[X]) (hF : F ≠ 0) : 0 < energy F := by
  obtain ⟨t, ht, hFt⟩ := exists_nonzero_value F hF
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    (((value_continuous F).norm.pow 2).continuousOn)
  · intro u hu
    exact sq_nonneg _
  · exact ⟨t, ⟨ht.1.le, ht.2.le⟩,
      sq_pos_of_pos (norm_pos_iff.mpr hFt)⟩

/-- Reversal/dilation preserves a nonzero polynomial of the stated degree. -/
private lemma reciprocal_nonzero {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N)
    (F : ℂ[X]) (hdeg : F.natDegree < d) (hF : F ≠ 0) :
    reciprocalPolynomial d N F ≠ 0 := by
  obtain ⟨t, ht, hFt⟩ := exists_nonzero_value F hF
  intro hz
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have h := reciprocalPolynomial_exact hd hN F hdeg (t : ℂ) htC
  rw [hz, Polynomial.eval_zero, mul_zero] at h
  exact hFt h.symm

/-- The positive mean controls the actual reciprocal Q polynomial energy. -/
private lemma mean_mul_energy_le_paired {c : ℕ} (hc : 3 ≤ c) (A B : ℂ[X]) :
    mean c * energy B ≤ pairedEnergy c A B := by
  rw [energy, pairedEnergy_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · exact (continuous_const.mul ((value_continuous B).norm.pow 2)).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      ‖value A t + ((Real.pi / 4 : ℝ) : ℂ) * value B t‖ ^ 2 +
      ‖value A (-t) - ((Real.pi / 4 : ℝ) : ℂ) * value B (-t)‖ ^ 2 +
      mean c * (‖value B t‖ ^ 2 + ‖value B (-t)‖ ^ 2))).intervalIntegrable 0 1
  · intro t ht
    have hm := (actual_mean_pos hc).le
    have hB := mul_nonneg hm (sq_nonneg (‖value B (-t)‖))
    nlinarith only [hB,
      sq_nonneg (‖value A t + ((Real.pi / 4 : ℝ) : ℂ) * value B t‖),
      sq_nonneg (‖value A (-t) - ((Real.pi / 4 : ℝ) : ℂ) * value B (-t)‖)]

private lemma paired_energy_pos_of_right_nonzero {c : ℕ} (hc : 3 ≤ c)
    (A B : ℂ[X]) (hB : B ≠ 0) : 0 < pairedEnergy c A B :=
  (mul_pos (actual_mean_pos hc) (polynomial_energy_pos B hB)).trans_le
    (mean_mul_energy_le_paired hc A B)

/-- No arithmetic symbol hypothesis is needed for nodal reconstruction. -/
private lemma actual_Q_nonzero (S : Finset ℤ) (v : ℤ → ℂ)
    (hv : ∃ k ∈ S, v k ≠ 0) : ActualNodalCoercivity.Q S v ≠ 0 := by
  classical
  obtain ⟨k, hk, hvk⟩ := hv
  intro hQ
  have he := ActualNodalCoercivity.numerator_eval_node S v k hk
  rw [hQ, Polynomial.eval_zero] at he
  have hn : (Lagrange.nodal (S.erase k) (fun j : ℤ => (j : ℂ))).eval (k : ℂ) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro j hj hkj
    have hkj' : k = j := by exact_mod_cast hkj
    exact (Finset.mem_erase.mp hj).1 hkj'.symm
  exact (mul_ne_zero hvk hn) he.symm

/-- Literal cropping of BOTH signed exterior columns. -/
private lemma actual_tail_crop (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) :
    pairedColumnTerm c (N + J) S v j = pairedColumnTerm c N S v (j + J) := by
  simp [pairedColumnTerm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The unscaled complete tail energy decreases with its cutoff. -/
private lemma actual_tail_crop_le (c N J : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (hs : Summable (pairedColumnTerm c N S v)) :
    (∑' j : ℕ, pairedColumnTerm c (N + J) S v j) ≤
      ∑' j : ℕ, pairedColumnTerm c N S v j := by
  simp_rw [actual_tail_crop]
  exact tsum_comp_le_tsum_of_inj hs
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i j h => Nat.add_right_cancel h)

/-- The finite radius is chosen before the vector and original cutoff. -/
private lemma finite_node_radius (S : Finset ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ S, |(k : ℝ)| ≤ B := by
  classical
  refine ⟨∑ k ∈ S, |(k : ℝ)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk
  exact Finset.single_le_sum (s := S) (f := fun j : ℤ => |(j : ℝ)|)
    (fun j _ => abs_nonneg (j : ℝ)) hk

/-- An actual enclosure at a later cutoff also proves summability at N=0. -/
lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ)
    (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) :
    Summable (pairedColumnTerm c N S v) := by
  obtain ⟨B, hB, hbound⟩ := finite_node_radius S
  obtain ⟨M, hM⟩ := actual_paired_column_uniform_enclosure_explicit336
    hc S hS hB hbound (η := 1) zero_lt_one
  have hbig := hM v (N + M) (by omega)
  have hshift : Summable (fun j : ℕ => pairedColumnTerm c N S v (j + M)) := by
    convert hbig.1 using 1
    funext j
    exact (actual_tail_crop c N M S v j).symm
  exact Summable.comp_nat_add hshift

/-- Nonzero on the retained finite head implies positive COMPLETE actual
tail energy at every cutoff. No sorted spectral limit is a premise. -/
theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) :
    0 < ∑' j : ℕ, pairedColumnTerm c N S v j := by
  have hS : S.Nonempty := by obtain ⟨k, hk, _⟩ := hv; exact ⟨k, hk⟩
  obtain ⟨B, hB, hbound⟩ := finite_node_radius S
  obtain ⟨M, hM⟩ := actual_paired_column_uniform_enclosure_explicit336 hc S hS hB hbound
    (η := (1 / 2 : ℝ)) (by norm_num)
  let K : ℕ := max 1 (max N M)
  have hKpos : 0 < K := by dsimp [K]; omega
  have hNK : N ≤ K := by dsimp [K]; omega
  have hMK : M ≤ K := by dsimp [K]; omega
  have henc := hM v K hMK
  dsimp only at henc
  have hdeg := (ActualNodalCoercivity.actual_nodal_polynomial_model c S hS v).2.1
  have hright : reciprocalPolynomial S.card K (ActualNodalCoercivity.Q S v) ≠ 0 :=
    reciprocal_nonzero (Nat.one_le_iff_ne_zero.mpr hS.card_pos.ne') hKpos
      (ActualNodalCoercivity.Q S v) hdeg (actual_Q_nonzero S v hv)
  have hE := paired_energy_pos_of_right_nonzero hc
    (reciprocalPolynomial S.card K (ActualNodalCoercivity.P c S v))
    (reciprocalPolynomial S.card K (ActualNodalCoercivity.Q S v)) hright
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hlo : 0 <
      (1 - (1 / 2 : ℝ)) * pairedEnergy c
        (reciprocalPolynomial S.card K (ActualNodalCoercivity.P c S v))
        (reciprocalPolynomial S.card K (ActualNodalCoercivity.Q S v)) /
      (Real.pi ^ 2 * (K : ℝ) * (1 + B / (K : ℝ)) ^ (2 * S.card)) := by
    positivity
  have hpos : 0 < ∑' j : ℕ, pairedColumnTerm c K S v j := hlo.trans_le henc.2.1
  have hcrop := actual_tail_crop_le c N (K - N) S v
    (actual_tail_summable_all hc S hS N v)
  have hsum : N + (K - N) = K := by omega
  rw [hsum] at hcrop
  exact hpos.trans_le hcrop

/-- Exact kernel on the original finite coefficients, including an empty
head and the zero vector. This does not claim injectivity on all Z->C. -/
theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) :
    (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0 := by
  constructor
  · intro hz k hk
    by_contra hvk
    have hp := actual_finite_head_tail_pos hc S N v ⟨k, hk, hvk⟩
    exact hp.ne' hz
  · intro hv
    have hcol : ∀ m : ℤ, couplingColumn c S v m = 0 := by
      intro m
      unfold couplingColumn
      apply Finset.sum_eq_zero
      intro k hk
      rw [hv k hk, mul_zero]
    simp [pairedColumnTerm, hcol]

end D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
