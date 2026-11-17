/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionAutomaticity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual halving counts and every weighted specialization are nonautomatic in all power-of-two representation bases, for canonical MSDF and genuine all-word LSDF machines, including every composite modulus. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionWeightedNonregularity
import D5.S1.Recurrence.KernelDecimation
import D5.S0.Automata.CanonicalDFAOKernel
import Mathlib.Data.ZMod.Basic

/-! The output sequence remains the actual source count. Canonical MSDF
machines are excluded even if their zero output is unconstrained. The adopted
LSDF equivalence covers every word, including empty, zero and padding words. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

open D5.S0.Automata.FiniteKernelDFAO
open D5.S0.Automata.CanonicalDFAOKernel

private theorem powerBase_ge_two (h : ℕ) (hh : 1 ≤ h) : 2 ≤ 2 ^ h := by
  simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) hh)

/-- No ordinary finite machine computes even the positive canonical MSDF inputs.
This is stronger than either standard zero-word convention. -/
theorem weighted_not_canonical_automatic {R : Type*} [CommRing R] [Nontrivial R]
    (t : R) (h : ℕ) (hh : 1 ≤ h) :
    ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh) (weightedCount t) := by
  intro ha
  exact weighted_powerBase_nonregularity t h hh
    (BinaryDecimation.finite_kernel_baseFamily _ _ (canonical_finite_kernel _ _ _ ha))

/-- Finite nonzero rings, arbitrary weights and all-word LSDF semantics. -/
theorem weighted_not_lsdf_automatic {R : Type} [CommRing R] [Nontrivial R] [Fintype R]
    (t : R) (h : ℕ) (hh : 1 ≤ h) :
    ¬ IsKAutomaticSequence (2 ^ h) (weightedCount t) := by
  intro ha
  have hf := ((isKAutomatic_iff_isKAutomaticSequence _ _).mpr ha).2
  exact weighted_powerBase_nonregularity t h hh
    (BinaryDecimation.finite_kernel_baseFamily _ _ hf)

private theorem finite_kernel_map {A B : Type*} (k : ℕ) (a : ℕ → A) (f : A → B)
    (hf : Finite ↥(kKernel k a)) : Finite ↥(kKernel k (fun n => f (a n))) := by
  have hs : (kKernel k a).Finite := Set.finite_coe_iff.mp hf
  rw [Set.finite_coe_iff]
  apply (hs.image (fun u n => f (u n))).subset
  rintro b ⟨e, r, hr, rfl⟩
  exact ⟨(fun n => a (k ^ e * n + r)), ⟨e, r, hr, rfl⟩, rfl⟩

/-- The ordinary natural-valued remainder sequence, for every modulus q>=2,
including composites, cannot be produced from canonical base-2^h digits. -/
theorem count_mod_not_canonical (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh)
      (fun n => count n % q) := by
  intro ha
  letI : Fact (1 < q) := ⟨by omega⟩
  have hf := finite_kernel_map (2 ^ h) (fun n => count n % q)
    (fun x : ℕ => (x : ZMod q)) (canonical_finite_kernel _ _ _ ha)
  have he : (fun n => ((count n % q : ℕ) : ZMod q)) = fun n => (count n : ZMod q) := by
    funext n
    exact ZMod.natCast_mod _ _
  rw [he] at hf
  apply nonregularity_over (ZMod q)
  exact (BinaryDecimation.arbitrary_matrix_iff _).mp
    (BinaryDecimation.powerBase_binary h hh _ (BinaryDecimation.finite_kernel_baseFamily _ _ hf))

/-- In Z/qZ the quotient output is the actual count; no prime-modulus premise. -/
theorem count_mod_not_lsdf (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) :
    letI : NeZero q := ⟨by omega⟩
    ¬ IsKAutomaticSequence (2 ^ h) (fun n => (count n : ZMod q)) := by
  letI : Fact (1 < q) := ⟨by omega⟩
  letI : NeZero q := ⟨by omega⟩
  have he : weightedCount (1 : ZMod q) = fun n => (count n : ZMod q) :=
    funext weightedCount_one
  rw [← he]
  exact weighted_not_lsdf_automatic (1 : ZMod q) h hh

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
