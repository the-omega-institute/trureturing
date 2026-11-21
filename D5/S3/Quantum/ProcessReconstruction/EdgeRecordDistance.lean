/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The edge-record channels have maximal diamond distance despite identical proper data. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordQuantum

/-! The edge-record channels have maximal diamond distance despite identical proper data. -/

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

open Matrix UnitaryReconstruction
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi pairMatrix)

noncomputable section

variable {n : ℕ}

theorem opposite_parity_disjoint (y : Word (n + 1)) :
    kernel 0 allOn y * kernel 1 allOn y = 0 := by
  rw [kernel_allOn, kernel_allOn]
  by_cases hy : parity y = 0
  · simp [hy]
  · simp [hy]

private theorem traceNorm_diagonal_disjoint {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hd : ∀ x, p x * q x = 0) :
    traceNorm (diagonal (fun x => (p x : ℂ)) - diagonal (fun x => (q x : ℂ))) =
      (∑ x, p x) + ∑ x, q x := by
  have hpos (w : A → ℝ) (hw : ∀ x, 0 ≤ w x) :
      (diagonal (fun x => (w x : ℂ))).PosSemidef := by
    exact Matrix.posSemidef_diagonal_iff.mpr (fun x => by exact_mod_cast hw x)
  rw [traceNorm_sub_orthogonal _ _ (hpos p hp) (hpos q hq)]
  · simp [Matrix.trace_diagonal]
  · rw [Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases h : x = y
    · subst y
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply, ← Complex.ofReal_mul]
      rw [hd, Complex.ofReal_zero]
    · simp [h]

def choiParityBlock (b : Bit) (p : Word (n + 1) × Word (n + 1)) : ℝ :=
  if p.1 = allOn then kernel b allOn p.2 / dimension n else 0

theorem choi_traceNorm :
    traceNorm (pairMatrix (normalizedChoi (channel (n := n) 0)) -
      pairMatrix (normalizedChoi (channel 1))) = 2 / dimension n := by
  have hw (p : Word (n + 1) × Word (n + 1)) :
      pairedWeight 0 p - pairedWeight 1 p = choiParityBlock 0 p - choiParityBlock 1 p := by
    by_cases h : p.1 = allOn
    · simp [pairedWeight, choiParityBlock, h]
    · simp [pairedWeight, choiParityBlock, h, kernel_inactive _ h]
  have he :
      diagonal (fun p : Word (n + 1) × Word (n + 1) => (pairedWeight 0 p : ℂ)) -
        diagonal (fun p => (pairedWeight 1 p : ℂ)) =
      diagonal (fun p => (choiParityBlock 0 p : ℂ)) -
        diagonal (fun p => (choiParityBlock 1 p : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simpa using congrArg (fun r : ℝ => (r : ℂ)) (hw i)
    · simp [h]
  have hs (b : Bit) : ∑ p : Word (n + 1) × Word (n + 1), choiParityBlock b p =
      1 / dimension n := by
    rw [Fintype.sum_prod_type]
    simp_rw [choiParityBlock, ← Finset.ite_sum_zero, ← Finset.sum_div, kernel_sum]
    simp
  rw [choi_diagonal, choi_diagonal, he, traceNorm_diagonal_disjoint, hs, hs]
  · ring
  · intro p
    unfold choiParityBlock
    split
    · exact div_nonneg (kernel_nonneg _ _ _) (dimension_pos _).le
    · exact le_rfl
  · intro p
    unfold choiParityBlock
    split
    · exact div_nonneg (kernel_nonneg _ _ _) (dimension_pos _).le
    · exact le_rfl
  · intro p
    by_cases hp : p.1 = allOn
    · simp [choiParityBlock, hp, div_mul_div_comm, opposite_parity_disjoint p.2]
    · simp [choiParityBlock, hp]

def probeVector (n : ℕ) : Unit × Word (n + 1) → ℂ := Pi.single ((), allOn) 1

/-- Each site contributes the one-qubit computational-basis vector for bit one. -/
theorem probeVector_product (p : Unit × Word (n + 1)) :
    probeVector n p = ∏ i, if p.2 i = 1 then (1 : ℂ) else 0 := by
  obtain ⟨⟨⟩, x⟩ := p
  by_cases h : x = allOn
  · subst x
    simp [probeVector, allOn]
  · have hk : ∃ k, x k ≠ 1 := by
      by_contra! he
      exact h (funext he)
    obtain ⟨k,hk⟩ := hk
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)]
    simp [probeVector, h]

/-- Computational all-ones product input with a trivial spectator. -/
def allOnProbe (n : ℕ) : DensityState (Unit × Word (n + 1)) :=
  pureState (probeVector n) (by simp [probeVector, dotProduct, Pi.single_apply])

theorem allOnProbe_output (b : Bit) :
    pairMatrix (referenceState (channel b) (allOnProbe n)) =
      diagonal (fun p : Unit × Word (n + 1) => (kernel b allOn p.2 : ℂ)) := by
  ext ⟨⟨⟩, y⟩ ⟨⟨⟩, z⟩
  change referenceMatrix (channel b) (vecMulVec (probeVector n) (star (probeVector n)))
    ((),y) ((),z) = _
  rw [referenceMatrix_apply]
  let X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ :=
    Matrix.of fun i j => vecMulVec (probeVector n) (star (probeVector n)) ((),i) ((),j)
  change Action (channel b) X y z = _
  rw [channel_action]
  by_cases h : y = z
  · subst z
    simp [X, probeVector, Pi.single_apply, vecMulVec_apply, ite_mul, mul_ite]
  · simp [h]

theorem product_probe_distance :
    referenceError (channel 0) (channel 1) (allOnProbe n) = 2 := by
  change traceNorm (pairMatrix (referenceState (channel 0) (allOnProbe n)) -
    pairMatrix (referenceState (channel 1) (allOnProbe n))) = 2
  rw [allOnProbe_output, allOnProbe_output, traceNorm_diagonal_disjoint]
  · norm_num [Fintype.sum_prod_type, kernel_sum]
  · exact fun p => kernel_nonneg _ _ p.2
  · exact fun p => kernel_nonneg _ _ p.2
  · exact fun p => opposite_parity_disjoint p.2

/-- Global parity of the measured output identifies the channel on the all-ones input. -/
theorem product_probe_parity (b : Bit) :
    ∑ y : Word (n + 1), (if parity y = b then kernel b allOn y else 0) = 1 := by
  convert kernel_sum b (allOn (n := n)) using 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : parity y = b
  · simp [h]
  · simp [kernel_allOn, h]

theorem maximal_diamond : diamondDistance (channel (n := n) 0) (channel 1) = 2 := by
  apply le_antisymm
  · exact diamondDistance_le _ _ (by norm_num) fun _ => referenceError_le_two _ _
  · simpa only [product_probe_distance] using
      referenceError_le_diamond (channel 0) (channel 1) (allOnProbe n)

def properPairedData (C : QuantumChannel (Word (n + 1)) (Word (n + 1)))
    (s : {s : Mask n // s ≠ Finset.univ}) : DensityState (Kept s.val × Kept s.val) :=
  pairedMarginal s.val (normalizedChoi C)

theorem properPairedData_eq : properPairedData (channel (n := n) 0) =
    properPairedData (channel 1) := by
  funext s
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact (proper_paired_mixed 0 s.val s.property).trans
    (proper_paired_mixed 1 s.val s.property).symm

theorem diamond_minimax (C : QuantumChannel (Word (n + 1)) (Word (n + 1))) :
    1 ≤ max (diamondDistance (channel 0) C) (diamondDistance (channel 1) C) := by
  let ρ := allOnProbe n
  let A := pairMatrix (referenceState (channel 0) ρ)
  let B := pairMatrix (referenceState (channel 1) ρ)
  let T := pairMatrix (referenceState C ρ)
  have ha := referenceError_le_diamond (channel 0) C ρ
  have hb := referenceError_le_diamond (channel 1) C ρ
  change traceNorm (A - T) ≤ _ at ha
  change traceNorm (B - T) ≤ _ at hb
  have h₂ : traceNorm (A - B) = 2 := product_probe_distance
  have h := traceNorm_add_le (A - T) (-(B - T))
  rw [traceNorm_neg, show (A - T) + -(B - T) = A - B by abel, h₂] at h
  linarith [le_max_left (diamondDistance (channel 0) C) (diamondDistance (channel 1) C),
    le_max_right (diamondDistance (channel 0) C) (diamondDistance (channel 1) C)]

theorem pairedData_minimax
    (estimate : ((s : {s : Mask n // s ≠ Finset.univ}) → DensityState (Kept s.val × Kept s.val)) →
      QuantumChannel (Word (n + 1)) (Word (n + 1))) :
    1 ≤ max (diamondDistance (channel 0) (estimate (properPairedData (channel 0))))
      (diamondDistance (channel 1) (estimate (properPairedData (channel 1)))) := by
  rw [← properPairedData_eq]
  exact diamond_minimax _

theorem choi_pairedCMI_decay (b : Bit) (L M R : Mask n)
    (hLM : Disjoint L M) (hLR : Disjoint L R) (hMR : Disjoint M R) :
    pairedCMI (normalizedChoi (channel b)) L M R ≤
      Real.log 2 * Real.exp (-Real.log 2 * M.card) := by
  rw [choi_pairedCMI b L M R hLM hLR hMR]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexp : (dimension n)⁻¹ = Real.exp (-Real.log 2 * (n + 1 : ℕ)) := by
    rw [show -Real.log 2 * (n + 1 : ℕ) = -(Real.log 2 * (n + 1 : ℕ)) by ring,
      Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rfl
  have hcard : (M.card : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (show M.card ≤ n + 1 by simpa using M.card_le_univ)
  have hdec : Real.log 2 / dimension n ≤ Real.log 2 * Real.exp (-Real.log 2 * M.card) := by
    rw [div_eq_mul_inv, hexp]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcard (neg_nonpos.mpr hlog))) hlog
  split <;> try positivity
  split <;> first | exact hdec | positivity

end

end D5.S3.Quantum.EnvironmentRecords.EdgePath
