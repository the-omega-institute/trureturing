/- GID: D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/StationaryOccupationResidualStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit residual transitions attain the product-minus-maximum memory dimension with one fixed physical unitary. -/

import D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualStep

open D5.S3.Quantum.StationaryPreparation.PaddingMemory
open D5.S3.Quantum.StationaryPreparation.ResidualCalculus
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

section ResidualMatrix

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def residualMemoryIndex (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount (maximalHead a) b) (h : Fin (b.count (maximalHead a) + 1)) :
    Fin (proposedDimension a) :=
  physicalMemoryEquiv a (some (residualPositiveTail (maximalHead a) a b hb hr,
    residualHeadIndex (maximalHead a) a b hb h))

theorem physical_residual_gate_formula (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount (maximalHead a) b) (i : A) (k : Fin (proposedDimension a)) :
    physicalGate a (blankMemory (maximalHead a) (physicalResidual a b)) (i, k) =
      ∑ h : Fin (b.count (maximalHead a) + 1),
        (Real.sqrt (lastTailMass (maximalHead a) (headSlice (maximalHead a) b h.val)) : ℂ) *
          physicalMatrix a (i, k) (residualMemoryIndex a b hb hr h) := by
  have he (s : OccupationMemory a (maximalHead a)) :
      coordinateEmbedding (physicalMemoryEquiv a).toEmbedding (basis s) =
        basis (physicalMemoryEquiv a s) := coordinate_embedding_basis _ _
  have hm (j : Fin (proposedDimension a)) :
      blankMemory (maximalHead a) (basis j) = basis (maximalHead a, j) :=
    coordinate_embedding_basis _ _
  rw [physicalResidual, paddingResidual, dif_pos hb, dif_pos hr]
  simp only [map_sum, map_smul, he, hm, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]
  change (∑ h : Fin (b.count (maximalHead a) + 1),
    (Real.sqrt (lastTailMass (maximalHead a) (headSlice (maximalHead a) b h.val)) : ℂ) *
      physicalGate a (basis (maximalHead a, residualMemoryIndex a b hb hr h)) (i, k)) = _
  simp_rw [physical_gate_coefficients]

theorem physical_residual_matrix_absent (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount (maximalHead a) b) (i : A) (hi : i ∉ b)
    (k : Fin (proposedDimension a)) (h : Fin (b.count (maximalHead a) + 1)) :
    physicalMatrix a (i, k) (residualMemoryIndex a b hb hr h) = 0 := by
  have hc : b.count i = 0 := Multiset.count_eq_zero.mpr hi
  by_cases hih : i = maximalHead a
  · subst i
    have hh : h.val = 0 := by have := h.isLt; omega
    simp [physicalMatrix, relabelMatrix, weightedMatrix, relabelProbability,
      residualMemoryIndex, Equiv.optionSubtypeNe_symm_self, paddingProbability,
      residualHeadIndex, hh, headProbability]
  · simp [physicalMatrix, relabelMatrix, weightedMatrix, relabelProbability,
      residualMemoryIndex, Equiv.optionSubtypeNe_symm_of_ne hih, paddingProbability,
      residualPositiveTail, residualTail, tailProbability, hc]

theorem physical_residual_step_absent (a b : Multiset A) (hb : b ≤ a)
    (hb0 : b ≠ 0) (i : A) (hi : i ∉ b) (k : Fin (proposedDimension a)) :
    physicalGate a (blankMemory (maximalHead a) (physicalResidual a b)) (i, k) = 0 := by
  by_cases hr : 0 < tailCount (maximalHead a) b
  · rw [physical_residual_gate_formula a b hb hr]
    simp only [physical_residual_matrix_absent a b hb hr i hi k, mul_zero, Finset.sum_const_zero]
  · simpa only [if_neg hi] using physical_residual_step_tail_free a b hb hb0 (by omega) i k

/-- Legal emissions from residuals with positive tail count. -/
def PositiveResidualStep (a : Multiset A) : Prop :=
  ∀ b, b ≤ a → 0 < tailCount (maximalHead a) b → ∀ i, i ∈ b →
    ∀ k : Fin (proposedDimension a),
      physicalGate a (blankMemory (maximalHead a) (physicalResidual a b)) (i, k) =
        physicalResidual a (b.erase i) k

theorem target_of_positive_residual_step (a : Multiset A)
    (hs : PositiveResidualStep a) : Target a := by
  apply target_of_residual_step
  intro b hb hb0 i k
  by_cases hr : 0 < tailCount (maximalHead a) b
  · by_cases hi : i ∈ b
    · rw [if_pos hi]
      exact hs b hb hr i hi k
    · rw [if_neg hi]
      exact physical_residual_step_absent a b hb hb0 i hi k
  · exact physical_residual_step_tail_free a b hb hb0 (by omega) i k

end ResidualMatrix

section ResidualTail

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem residual_tail_erase (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : TailAlphabet head) :
    decrement (fun j : TailAlphabet head => a.count j.val)
      (residualTail head a b hb) i =
      residualTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) := by
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    simp [residualTail]
  · have hval : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp [decrement_other, hji, residualTail, Multiset.count_erase_of_ne hval]

theorem residual_positive_tail_erase (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : TailAlphabet head) (hi : i.val ∈ b) (hr : 2 ≤ tailCount head b)
    (he : 0 < tailCount head (b.erase i.val)) :
    decrementPositive (fun j : TailAlphabet head => a.count j.val)
      (residualPositiveTail head a b hb (by omega)) i (Multiset.count_pos.mpr hi)
      (by exact hr) =
      residualPositiveTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) he := by
  apply Subtype.ext
  exact residual_tail_erase head a b hb i

variable [Nonempty A]

theorem residual_tail_matrix (a b : Multiset A) (hb : b ≤ a)
    (i : A) (hi : i ≠ maximalHead a) (hib : i ∈ b)
    (hr : 2 ≤ tailCount (maximalHead a) b)
    (he : 0 < tailCount (maximalHead a) (b.erase i))
    (h : Fin (b.count (maximalHead a) + 1)) (k : Fin (proposedDimension a)) :
    physicalMatrix a (i, k) (residualMemoryIndex a b hb (by omega) h) =
      (Real.sqrt (tailProbability h.val (tailCount (maximalHead a) b) (b.count i)) : ℂ) *
        basis (physicalMemoryEquiv a (some
          (residualPositiveTail (maximalHead a) a (b.erase i)
            ((Multiset.erase_le _ _).trans hb) he,
           residualHeadIndex (maximalHead a) a b hb h))) k := by
  have hd := residual_positive_tail_erase (maximalHead a) a b hb ⟨i, hi⟩ hib hr he
  have hc : 0 < b.count i := Multiset.count_pos.mpr hib
  have hp : paddingProbability (a.count (maximalHead a))
      (fun j : TailAlphabet (maximalHead a) => a.count j.val)
      (some (residualPositiveTail (maximalHead a) a b hb (by omega),
        residualHeadIndex (maximalHead a) a b hb h)) (some ⟨i, hi⟩) =
      tailProbability h.val (tailCount (maximalHead a) b) (b.count i) := by
    change (if tailCount (maximalHead a) b = 1 then _ else _) = _
    rw [if_neg (by omega)]
    rfl
  have hn : paddingNext (a.count (maximalHead a))
      (fun j : TailAlphabet (maximalHead a) => a.count j.val)
      (some (residualPositiveTail (maximalHead a) a b hb (by omega),
        residualHeadIndex (maximalHead a) a b hb h)) (some ⟨i, hi⟩) =
      some (residualPositiveTail (maximalHead a) a (b.erase i)
        ((Multiset.erase_le _ _).trans hb) he,
        residualHeadIndex (maximalHead a) a b hb h) := by
    dsimp only [paddingNext]
    rw [dif_pos (show 0 < ((residualPositiveTail (maximalHead a) a b hb (by omega)).val
        ⟨i, hi⟩).val from hc)]
    rw [dif_pos (show 1 < tailSum
        (residualPositiveTail (maximalHead a) a b hb (by omega)).val from hr), hd]
  simp only [physicalMatrix, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply,
    Equiv.optionSubtypeNe_symm_of_ne hi]
  rw [hp, hn]
  simp [basis_apply, eq_comm]

theorem physical_residual_step_tail (a b : Multiset A) (hb : b ≤ a)
    (i : A) (hi : i ≠ maximalHead a) (hib : i ∈ b)
    (hr : 2 ≤ tailCount (maximalHead a) b) (k : Fin (proposedDimension a)) :
    physicalGate a (blankMemory (maximalHead a) (physicalResidual a b)) (i, k) =
      physicalResidual a (b.erase i) k := by
  have he : 0 < tailCount (maximalHead a) (b.erase i) := by
    have := tail_count_erase_tail (maximalHead a) b i hi hib
    omega
  have hbe : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
  have hh : (b.erase i).count (maximalHead a) = b.count (maximalHead a) :=
    Multiset.count_erase_of_ne (Ne.symm hi) b
  rw [physical_residual_gate_formula a b hb (by omega)]
  simp_rw [residual_tail_matrix a b hb i hi hib hr he]
  have hemb (s : OccupationMemory a (maximalHead a)) :
      coordinateEmbedding (physicalMemoryEquiv a).toEmbedding (basis s) =
        basis (physicalMemoryEquiv a s) := coordinate_embedding_basis _ _
  rw [physicalResidual, paddingResidual, dif_pos hbe, dif_pos he]
  simp only [map_sum, map_smul, hemb, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]
  have hs := head_slice_tail_amplitude (maximalHead a) b
  simp_rw [← mul_assoc, mul_comm _ (Real.sqrt (tailProbability _ _ _) : ℂ),
    hs _ i hi hib hr]
  apply Fintype.sum_equiv (finCongr (congrArg (fun n => n + 1) hh.symm))
  intro h
  rfl

end ResidualTail

section ResidualHead

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

set_option maxHeartbeats 800000 in
theorem physical_residual_step_head (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount (maximalHead a) b) (hh : maximalHead a ∈ b)
    (k : Fin (proposedDimension a)) :
      physicalGate a (blankMemory (maximalHead a) (physicalResidual a b))
        (maximalHead a, k) =
      physicalResidual a (b.erase (maximalHead a)) k := by
  rw [physical_residual_gate_formula a b hb hr]
  have hbe : b.erase (maximalHead a) ≤ a :=
    (Multiset.erase_le _ _).trans hb
  have hre : 0 < tailCount (maximalHead a) (b.erase (maximalHead a)) := by
    simpa only [tail_count_erase_head] using hr
  rw [physicalResidual, paddingResidual, dif_pos hbe, dif_pos hre]
  simp only [map_sum, map_smul, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have hemb (s : OccupationMemory a (maximalHead a)) :
      coordinateEmbedding (physicalMemoryEquiv a).toEmbedding (basis s) =
        basis (physicalMemoryEquiv a s) := coordinate_embedding_basis _ _
  simp_rw [hemb]
  have hc : (b.erase (maximalHead a)).count (maximalHead a) + 1 =
      b.count (maximalHead a) := by
    have hbc := congrArg (Multiset.count (maximalHead a))
      (Multiset.cons_erase hh)
    simp only [Multiset.count_cons_self] at hbc
    rw [hbc]
  rw [Fin.sum_univ_succ]
  let e : Fin (b.count (maximalHead a)) ≃
      Fin ((b.erase (maximalHead a)).count (maximalHead a) + 1) := finCongr hc.symm
  have hzero : (Real.sqrt (lastTailMass (maximalHead a)
      (headSlice (maximalHead a) b 0)) : ℂ) *
      physicalMatrix a (maximalHead a, k)
        (residualMemoryIndex a b hb hr 0) = 0 := by
    simp [physicalMatrix, relabelMatrix, weightedMatrix, relabelProbability,
      paddingProbability, residualMemoryIndex,
      residualHeadIndex, headProbability]
  have hzero' : (Real.sqrt (lastTailMass (maximalHead a)
      (headSlice (maximalHead a) b (↑(0 : Fin (b.count (maximalHead a) + 1))))) : ℂ) *
      physicalMatrix a (maximalHead a, k)
        (residualMemoryIndex a b hb hr (0 : Fin (b.count (maximalHead a) + 1))) = 0 := by
    exact hzero
  rw [hzero', zero_add]
  apply Fintype.sum_equiv e
  intro c
  have htail : residualPositiveTail (maximalHead a) a b hb hr =
      residualPositiveTail (maximalHead a) a (b.erase (maximalHead a)) hbe hre := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp [residualPositiveTail, residualTail, Multiset.count_erase_of_ne i.property]
  have hhead : headPredecessor
      (residualHeadIndex (maximalHead a) a b hb c.succ) =
      residualHeadIndex (maximalHead a) a (b.erase (maximalHead a)) hbe (e c) := by
    apply Fin.ext
    change c.val + 1 - 1 = c.val
    exact Nat.add_sub_cancel _ _
  have hp : paddingProbability (a.count (maximalHead a))
      (fun j : TailAlphabet (maximalHead a) => a.count j.val)
      (some (residualPositiveTail (maximalHead a) a b hb hr,
        residualHeadIndex (maximalHead a) a b hb c.succ)) none =
      headProbability c.succ.val (tailCount (maximalHead a) b) := by
    change (if tailCount (maximalHead a) b = 1 then _ else _) = _
    by_cases hR : tailCount (maximalHead a) b = 1
    · have hidxval : (residualHeadIndex (maximalHead a) a b hb c.succ).val ≠ 0 :=
        Nat.succ_ne_zero c.val
      rw [if_pos hR, if_neg hidxval]
      simp only [headProbability, hR, Nat.cast_one, add_sub_cancel_right]
      have hpos : (0 : ℝ) < (c.val : ℝ) + 1 := by positivity
      simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using (div_self hpos.ne').symm
    · rw [if_neg hR]
      rfl
  have hn : paddingNext (a.count (maximalHead a))
      (fun j : TailAlphabet (maximalHead a) => a.count j.val)
      (some (residualPositiveTail (maximalHead a) a b hb hr,
        residualHeadIndex (maximalHead a) a b hb c.succ)) none =
      some (residualPositiveTail (maximalHead a) a (b.erase (maximalHead a)) hbe hre,
        residualHeadIndex (maximalHead a) a (b.erase (maximalHead a)) hbe (e c)) := by
    dsimp only [paddingNext]
    rw [htail, hhead]
  simp only [physicalMatrix, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply,
    Equiv.optionSubtypeNe_symm_self]
  rw [hp, hn]
  by_cases hmem : (physicalMemoryEquiv a)
      (some (residualPositiveTail (maximalHead a) a (b.erase (maximalHead a)) hbe hre,
        residualHeadIndex (maximalHead a) a (b.erase (maximalHead a)) hbe (e c))) = k
  · rw [if_pos hmem]
    simp only [basis_apply, if_pos hmem.symm, mul_one]
    have ha := head_slice_head_amplitude (maximalHead a) b c.succ.val
      (Nat.succ_pos c.val) hr
    rw [head_slice_erase_head_source (maximalHead a) b ((e c).val)]
    have hec : (e c).val = c.val := rfl
    rw [hec]
    simpa only [Fin.val_succ, Nat.add_sub_cancel] using (mul_comm _ _).trans ha
  · rw [if_neg hmem]
    simp only [basis_apply, if_neg (Ne.symm hmem), mul_zero]

end ResidualHead

section ResidualSink

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S1.Ledger.BoundedTimeSlice

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The one-tail branch sends the unique remaining tail letter to the sink.
The residual on the erased multiset is tail-free, hence is the sink basis. -/
theorem physical_residual_step_one_tail (a b : Multiset A) (hb : b ≤ a)
    (hr : tailCount (maximalHead a) b = 1) (i : A) (hib : i ∈ b)
    (hi : i ≠ maximalHead a) (k : Fin (proposedDimension a)) :
    physicalGate a (blankMemory (maximalHead a) (physicalResidual a b)) (i, k) =
      physicalResidual a (b.erase i) k := by
  rw [physical_residual_gate_formula a b hb (by omega) i k]
  simp_rw [head_slice_one_amplitude (maximalHead a) b _ hr]
  have htail : tailSum (residualTail (maximalHead a) a b hb) = 1 := by
    exact hr
  have hbi : 0 < (residualTail (maximalHead a) a b hb ⟨i, hi⟩).val := by
    simpa [residualTail] using (Multiset.count_pos.mpr hib)
  have hcoords := sum_one_coordinate
    (fun j : TailAlphabet (maximalHead a) => a.count j.val)
    (residualTail (maximalHead a) a b hb) htail ⟨i, hi⟩ hbi
  have hcount : b.count i = 1 := by
    simpa [residualTail] using hcoords ⟨i, hi⟩
  have herase : tailCount (maximalHead a) (b.erase i) = 0 := by
    have ht := tail_count_erase_tail (maximalHead a) b i hi hib
    omega
  have hberase : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
  have hsum : ∑ x : Fin (b.count (maximalHead a) + 1),
      (Real.sqrt (if x = 0 then (1 : ℝ) else 0) : ℂ) = 1 := by
    rw [Fin.sum_univ_succ]
    simp
  rw [physical_residual_tail_free a (b.erase i) hberase herase]
  simp [physicalMatrix, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, paddingNext, paddingProbability, residualMemoryIndex,
    residualPositiveTail, residualTail, hcount, htail, hi,
    physicalFinal, residualHeadIndex, hsum]
  by_cases hk : physicalMemoryEquiv a none = k
  · simp [hk]
  · simp [hk]
    exact fun h => hk h.symm

end ResidualSink

section Attainment

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem positive_residual_step (a : Multiset A) : PositiveResidualStep a := by
  intro b hb hr i hib k
  by_cases hi : i = maximalHead a
  · subst i
    exact physical_residual_step_head a b hb hr hib k
  · by_cases hR : tailCount (maximalHead a) b = 1
    · exact physical_residual_step_one_tail a b hb hR i hib hi k
    · exact physical_residual_step_tail a b hb i hi hib (by omega) k

theorem stationary_memory_dimension_attained (a : Multiset A) :
    let d := (Finset.univ.prod fun i : A => a.count i + 1) - Finset.univ.sup a.count
    ∃ (blank : A) (U : Unitary (A × Fin d)) (x f : Space (Fin d)),
      ‖x‖ = 1 ∧ ‖f‖ = 1 ∧
      ∀ (w : Fin a.card → A) (k : Fin d),
        circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
          sectorVector a.card a w * f k := by
  simpa [Target] using target_of_positive_residual_step a (positive_residual_step a)

end Attainment

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualStep
