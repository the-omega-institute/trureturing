/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The paired edge-record law has exact entropy and conditional mutual information. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordLaw

/-! The paired edge-record law has exact entropy and conditional mutual information. -/

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

noncomputable section

variable {n : ℕ}

/-- The dimension of the full computational basis. There are n edges and n+1 sites. -/
def dimension (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem dimension_pos (n : ℕ) : 0 < dimension n := by unfold dimension; positivity

theorem card_sites (n : ℕ) : (Fintype.card (Word (n + 1)) : ℝ) = dimension n := by
  rw [card_word, Nat.cast_pow, Nat.cast_ofNat, dimension]

theorem kernel_sum (b : Bit) (x : Word (n + 1)) : ∑ y, kernel b x y = 1 :=
  sum_push (localOutput b x)

theorem kernel_nonneg (b : Bit) (x y : Word (n + 1)) : 0 ≤ kernel b x y :=
  push_nonneg (localOutput b x) y

theorem kernel_formula (b : Bit) (x y : Word (n + 1)) :
    kernel b x y =
      if x = allOn then (if parity y = b then 2 / dimension n else 0)
      else (dimension n)⁻¹ := by
  by_cases hx : x = allOn
  · subst x
    simpa [dimension] using kernel_allOn b y
  · simpa [hx, dimension] using kernel_inactive b hx y

def pairedWeight (b : Bit) (p : Word (n + 1) × Word (n + 1)) : ℝ :=
  kernel b p.1 p.2 / dimension n

theorem pairedWeight_entropy (b : Bit) :
    (∑ p : Word (n + 1) × Word (n + 1), Real.negMulLog (pairedWeight b p)) =
      2 * Real.log (dimension n) - Real.log 2 / dimension n := by
  let d := dimension n
  have hd : 0 < d := dimension_pos n
  have hterm (x y : Word (n + 1)) :
      Real.negMulLog (pairedWeight b (x,y)) =
      (2 * Real.log d - (if x = allOn then Real.log 2 else 0)) *
        (kernel b x y / d) := by
    unfold pairedWeight
    rw [kernel_formula]
    by_cases hx : x = allOn
    · by_cases hy : parity y = b
      · simp only [hx, hy, ite_true, Real.negMulLog_def]
        rw [Real.log_div (by positivity) hd.ne', Real.log_div (by positivity) hd.ne']
        ring
      · simp [hx, hy]
    · simp only [hx, ite_false, sub_zero, Real.negMulLog_def]
      rw [Real.log_div (inv_ne_zero hd.ne') hd.ne', Real.log_inv]
      ring
  rw [Fintype.sum_prod_type]
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_div, kernel_sum]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_sites]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
  change d * 2 * Real.log d * (1 / d) - Real.log 2 * (1 / d) = 2 * Real.log d - Real.log 2 / d
  field_simp

theorem card_kept (s : Mask n) : Fintype.card (Kept s) = 2 ^ s.card := by
  simp

theorem log_pairedDimension (s : Mask n) :
    Real.log (Fintype.card (Kept s × Kept s) : ℝ) = 2 * s.card * Real.log 2 := by
  rw [Fintype.card_prod, card_kept, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

/-- Entropy of a paired marginal, expressed as the mixed-state entropy minus the
full-register deficit. The quantum bridge identifies this with von Neumann entropy. -/
def pairedEntropyProfile (s : Mask n) : ℝ :=
  2 * s.card * Real.log 2 - if s = Finset.univ then Real.log 2 / dimension n else 0

theorem profile_full (n : ℕ) :
    pairedEntropyProfile (Finset.univ : Mask n) =
      2 * Real.log (dimension n) - Real.log 2 / dimension n := by
  simp [pairedEntropyProfile, dimension, Real.log_pow, Nat.cast_add]
  ring

/-- The four-term paired CMI identity for every pairwise disjoint triple. -/
theorem pairedCMI_profile (L M R : Mask n)
    (hLM : Disjoint L M) (hLR : Disjoint L R) (hMR : Disjoint M R) :
    pairedEntropyProfile (L ∪ M) + pairedEntropyProfile (M ∪ R) -
      pairedEntropyProfile M - pairedEntropyProfile (L ∪ M ∪ R) =
      if L = ∅ ∨ R = ∅ then 0
      else if L ∪ M ∪ R = Finset.univ then Real.log 2 / dimension n else 0 := by
  by_cases hL : L = ∅
  · subst L
    simp
  by_cases hR : R = ∅
  · subst R
    simp
  have hLMR : Disjoint (L ∪ M) R := Finset.disjoint_union_left.mpr ⟨hLR,hMR⟩
  have hLMproper : L ∪ M ≠ Finset.univ := by
    intro h
    apply hR
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact Finset.disjoint_left.mp hLMR (by rw [h]; exact Finset.mem_univ k) hk
  have hMRproper : M ∪ R ≠ Finset.univ := by
    intro h
    have h' := Finset.disjoint_union_right.mpr ⟨hLM,hLR⟩
    apply hL
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact Finset.disjoint_left.mp h' hk (by rw [h]; exact Finset.mem_univ k)
  have hMproper : M ≠ Finset.univ := by
    intro h
    apply hL
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact Finset.disjoint_left.mp hLM hk (by rw [h]; exact Finset.mem_univ k)
  simp only [pairedEntropyProfile, hLMproper, hMRproper, hMproper, hL, hR, or_self,
    ite_false, sub_zero, Finset.card_union_of_disjoint hLMR,
    Finset.card_union_of_disjoint hLM, Finset.card_union_of_disjoint hMR, Nat.cast_add]
  ring

end

end D5.S3.Quantum.EnvironmentRecords.EdgePath
