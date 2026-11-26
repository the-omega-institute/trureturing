/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordQueryBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hidden-input reconstruction takes exponentially many coherent calls. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordQueryChannels
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Adaptive discrimination of the hidden-input oracles with arbitrary finite quantum memory. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.EnvironmentRecords.HiddenInput

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance

section Measurement

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The effect for reporting zero, together with positivity of both POVM effects. -/
structure BinaryPOVM (Q : Type*) [Fintype Q] [DecidableEq Q] where
  zeroEffect : Matrix Q Q ℂ
  positive : zeroEffect.PosSemidef
  complement_positive : (1 - zeroEffect).PosSemidef

/-- The Born probability of reporting zero. -/
def BinaryPOVM.probZero (E : BinaryPOVM Q) (ρ : DensityState Q) : ℝ :=
  (E.zeroEffect * CStarMatrix.ofMatrix.symm ρ.1).trace.re

/-- The Born probability of reporting one, evaluated using the complementary effect. -/
def BinaryPOVM.probOne (E : BinaryPOVM Q) (ρ : DensityState Q) : ℝ :=
  ((1 - E.zeroEffect) * CStarMatrix.ofMatrix.symm ρ.1).trace.re

theorem BinaryPOVM.probOne_eq (E : BinaryPOVM Q) (ρ : DensityState Q) :
    E.probOne ρ = 1 - E.probZero ρ := by
  unfold BinaryPOVM.probOne BinaryPOVM.probZero
  rw [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re]
  change (Matrix.trace ρ.1).re - _ = _
  rw [ρ.2.2, Complex.one_re]

/-- The signed difference of the Born probabilities of any binary event is bounded by
the halved trace norm. Both Jordan parts have the same trace on a state difference. -/
theorem BinaryPOVM.probZero_sub_le (E : BinaryPOVM Q) (ρ σ : DensityState Q) :
    E.probZero ρ - E.probZero σ ≤ traceDistance ρ σ := by
  let A := CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1
  let P := posPart A
  let N := negPart A
  have hpos (τ : DensityState Q) : (CStarMatrix.ofMatrix.symm τ.1).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm τ.2.1).posSemidef
  have hA : A.IsHermitian := (hpos ρ).isHermitian.sub (hpos σ).isHermitian
  have hsplit : P - N = A := CFC.posPart_sub_negPart A hA
  have hP : P.PosSemidef := (CFC.posPart_nonneg A).posSemidef
  have hN : N.PosSemidef := (CFC.negPart_nonneg A).posSemidef
  have htrA : A.trace = 0 := by
    dsimp only [A]
    rw [Matrix.trace_sub]
    change Matrix.trace ρ.1 - Matrix.trace σ.1 = 0
    rw [ρ.2.2, σ.2.2, sub_self]
  have hbalance : P.trace = N.trace := by
    have h := congrArg Matrix.trace hsplit
    rw [Matrix.trace_sub, htrA] at h
    exact sub_eq_zero.mp h
  have hnorm : traceDistance ρ σ = P.trace.re := by
    change traceNorm A / 2 = _
    rw [trace_norm_jordan_mass A hA, ← hbalance]
    ring
  have hcomplement := RHLinalg.trace_mul_nonneg_of_posSemidef E.complement_positive hP
  change 0 ≤ ((1 - E.zeroEffect) * P).trace.re at hcomplement
  rw [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re] at hcomplement
  have hnegative := RHLinalg.trace_mul_nonneg_of_posSemidef E.positive hN
  change 0 ≤ (E.zeroEffect * N).trace.re at hnegative
  have hleft : E.probZero ρ - E.probZero σ =
      (E.zeroEffect * P).trace.re - (E.zeroEffect * N).trace.re := by
    simpa only [BinaryPOVM.probZero, A, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using
      congrArg (fun X : Matrix Q Q ℂ => (E.zeroEffect * X).trace.re) hsplit.symm
  rw [hleft, hnorm]
  linarith

theorem BinaryPOVM.traceDistance_of_success (E : BinaryPOVM Q) (ρ σ : DensityState Q)
    (hρ : 2 / 3 ≤ E.probZero ρ) (hσ : 2 / 3 ≤ E.probOne σ) :
    1 / 3 ≤ traceDistance ρ σ := by
  have h := E.probZero_sub_le ρ σ
  rw [E.probOne_eq] at hσ
  linarith

/-- Coarsen a finite POVM by an arbitrary classical decision rule. -/
def BinaryPOVM.ofFiniteDecision {Ω : Type*} [Fintype Ω] (effect : Ω → Matrix Q Q ℂ)
    (positive : ∀ o, (effect o).PosSemidef) (complete : ∑ o, effect o = 1)
    (reportsZero : Ω → Bool) : BinaryPOVM Q := by
  let yes := Finset.univ.filter fun o => reportsZero o = true
  let no := Finset.univ.filter fun o => ¬ reportsZero o = true
  have hsum : (∑ o ∈ yes, effect o) + (∑ o ∈ no, effect o) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, complete]
  refine ⟨∑ o ∈ yes, effect o, Matrix.posSemidef_sum _ fun o _ => positive o, ?_⟩
  rw [← hsum, add_sub_cancel_left]
  exact Matrix.posSemidef_sum _ fun o _ => positive o

/-- Born probability of an outcome with the given effect. -/
def bornMass {Ω : Type*} (effect : Ω → Matrix Q Q ℂ) (ρ : DensityState Q) (o : Ω) : ℝ :=
  (effect o * CStarMatrix.ofMatrix.symm ρ.1).trace.re

theorem bornMass_nonneg {Ω : Type*} (effect : Ω → Matrix Q Q ℂ)
    (positive : ∀ o, (effect o).PosSemidef) (ρ : DensityState Q) (o : Ω) :
    0 ≤ bornMass effect ρ o :=
  RHLinalg.trace_mul_nonneg_of_posSemidef (positive o)
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef

theorem BinaryPOVM.ofFiniteDecision_probZero {Ω : Type*} [Fintype Ω]
    (effect : Ω → Matrix Q Q ℂ) (positive : ∀ o, (effect o).PosSemidef)
    (complete : ∑ o, effect o = 1) (reportsZero : Ω → Bool) (ρ : DensityState Q) :
    (ofFiniteDecision effect positive complete reportsZero).probZero ρ =
      ∑ o ∈ Finset.univ.filter (fun o => reportsZero o = true), bornMass effect ρ o := by
  unfold probZero bornMass
  change ((∑ o ∈ Finset.univ.filter (fun o => reportsZero o = true), effect o) *
    CStarMatrix.ofMatrix.symm ρ.1).trace.re = _
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem BinaryPOVM.ofFiniteDecision_probOne {Ω : Type*} [Fintype Ω]
    (effect : Ω → Matrix Q Q ℂ) (positive : ∀ o, (effect o).PosSemidef)
    (complete : ∑ o, effect o = 1) (reportsZero : Ω → Bool) (ρ : DensityState Q) :
    (ofFiniteDecision effect positive complete reportsZero).probOne ρ =
      ∑ o ∈ Finset.univ.filter (fun o => ¬ reportsZero o = true), bornMass effect ρ o := by
  let yes := Finset.univ.filter fun o => reportsZero o = true
  let no := Finset.univ.filter fun o => ¬ reportsZero o = true
  have hsum : (∑ o ∈ yes, effect o) + (∑ o ∈ no, effect o) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, complete]
  change ((1 - ∑ o ∈ yes, effect o) * CStarMatrix.ofMatrix.symm ρ.1).trace.re =
    ∑ o ∈ no, bornMass effect ρ o
  rw [← hsum, add_sub_cancel_left, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rfl

end Measurement

section Protocol

variable {n T : ℕ} {R : Type} [Fintype R] [DecidableEq R]

/-- The initial probe may be entangled with any finite memory. Each interleaving map is
an arbitrary CPTP map on both registers, and can use adaptive information stored in memory.
The register `R` can include padding for the entire finite protocol. -/
structure AdaptiveProtocol (n T : ℕ) (R : Type) [Fintype R] [DecidableEq R] where
  initial : DensityState (R × Word (n + 1))
  interleave : Fin T → QuantumChannel (R × Word (n + 1)) (R × Word (n + 1))

namespace AdaptiveProtocol

variable (P : AdaptiveProtocol n T R)

/-- The state after `k` calls and their interleaving operations. For `k < T` this is
the input to the next call. At `k = T` it is the terminal state. -/
def run (C : QuantumChannel (Word (n + 1)) (Word (n + 1))) :
    (k : ℕ) → k ≤ T → DensityState (R × Word (n + 1))
  | 0, _ => P.initial
  | k + 1, h => (P.interleave ⟨k, h⟩).mapState (referenceState C (run C k (by omega)))

def terminal (C : QuantumChannel (Word (n + 1)) (Word (n + 1))) :
    DensityState (R × Word (n + 1)) :=
  P.run C T le_rfl

/-- Total baseline probability assigned to the marked word through the first `k` calls. -/
def baselineMass (a : Word (n + 1)) : (k : ℕ) → k ≤ T → ℝ
  | 0, _ => 0
  | k + 1, h => baselineMass a k (by omega) +
      queryMass (P.run (uniformChannel (n + 1)) k (by omega)) a

theorem sum_baselineMass (k : ℕ) (hk : k ≤ T) :
    ∑ a, P.baselineMass a k hk = (k : ℝ) := by
  induction k with
  | zero => simp [baselineMass]
  | succ k ih =>
    simp only [baselineMass, Finset.sum_add_distrib, sum_queryMass, Nat.cast_succ]
    rw [ih]

private theorem distance_self (ρ : DensityState (R × Word (n + 1))) :
    traceDistance ρ ρ = 0 := by
  have h := congrArg Complex.re
    (traceNorm_of_posSemidef (Matrix.PosSemidef.zero (n := R × Word (n + 1)) (R := ℂ)))
  change (Complex.ofReal (traceNorm (0 : Matrix (R × Word (n + 1)) _ ℂ))).re = _ at h
  rw [Complex.ofReal_re, Matrix.trace_zero, Complex.zero_re] at h
  simp [traceDistance, h]

/-- The state-distance recurrence uses the all-uniform input at each call. -/
theorem distance_to_uniform (a : Word (n + 1)) (b : Bit) (k : ℕ) (hk : k ≤ T) :
    traceDistance (P.run (markedChannel a b) k hk) (P.run (uniformChannel (n + 1)) k hk) ≤
      P.baselineMass a k hk / 2 := by
  induction k with
  | zero => simp [run, baselineMass, distance_self]
  | succ k ih =>
    let ρ := P.run (markedChannel a b) k (by omega)
    let σ := P.run (uniformChannel (n + 1)) k (by omega)
    let L := P.interleave ⟨k, hk⟩
    change traceDistance (L.mapState (referenceState (markedChannel a b) ρ))
      (L.mapState (referenceState (uniformChannel (n + 1)) σ)) ≤
        (P.baselineMass a k (by omega) + queryMass σ a) / 2
    calc
      _ ≤ traceDistance (referenceState (markedChannel a b) ρ)
          (referenceState (uniformChannel (n + 1)) σ) := traceDistance_contract L _ _
      _ ≤ traceDistance (referenceState (markedChannel a b) ρ)
            (referenceState (markedChannel a b) σ) +
          traceDistance (referenceState (markedChannel a b) σ)
            (referenceState (uniformChannel (n + 1)) σ) := traceDistance_triangle _ _ _
      _ ≤ traceDistance ρ σ + queryMass σ a / 2 := by
        rw [reference_traceDistance_exact]
        exact add_le_add (preparation_reference_contract (markedPrepared a b) ρ σ) le_rfl
      _ ≤ _ := by
        rw [add_div]
        exact add_le_add (ih (by omega)) le_rfl

/-- The two branch distances to a common baseline add to at most the total marked mass. -/
theorem terminal_branch_distance (a : Word (n + 1)) :
    traceDistance (P.terminal (markedChannel a 0)) (P.terminal (markedChannel a 1)) ≤
      P.baselineMass a T le_rfl := by
  calc
    _ ≤ traceDistance (P.terminal (markedChannel a 0)) (P.terminal (uniformChannel (n + 1))) +
        traceDistance (P.terminal (uniformChannel (n + 1))) (P.terminal (markedChannel a 1)) :=
      traceDistance_triangle _ _ _
    _ ≤ P.baselineMass a T le_rfl / 2 + P.baselineMass a T le_rfl / 2 := by
      rw [traceDistance_symm (P.terminal (uniformChannel (n + 1)))]
      exact add_le_add (P.distance_to_uniform a 0 T le_rfl) (P.distance_to_uniform a 1 T le_rfl)
    _ = _ := by ring

/-- The bound from terminal trace-distance separation, for every number of calls including zero. -/
theorem query_lower_bound_of_terminal_distance
    (h : ∀ a, (1 / 3 : ℝ) ≤
      traceDistance (P.terminal (markedChannel a 0)) (P.terminal (markedChannel a 1))) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T := by
  have hsum := Finset.sum_le_sum
    (fun a (_ : a ∈ Finset.univ) => (h a).trans (P.terminal_branch_distance a))
  rw [P.sum_baselineMass] at hsum
  simpa [card_word, nsmul_eq_mul, div_eq_mul_inv] using hsum

/-- The mark can be revealed to the terminal decision after all calls. Any such decision
succeeding with probability at least two thirds on every branch uses at least one third
of the number of words in calls. A fixed terminal measurement is a special case. -/
theorem query_lower_bound (E : Word (n + 1) → BinaryPOVM (R × Word (n + 1)))
    (h0 : ∀ a, 2 / 3 ≤ (E a).probZero (P.terminal (markedChannel a 0)))
    (h1 : ∀ a, 2 / 3 ≤ (E a).probOne (P.terminal (markedChannel a 1))) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T :=
  P.query_lower_bound_of_terminal_distance fun a =>
    (E a).traceDistance_of_success _ _ (h0 a) (h1 a)

/-- Any finite POVM and classical decision rule have the same query lower bound. -/
theorem finite_povm_query_lower_bound {Ω : Type*} [Fintype Ω]
    (effect : Ω → Matrix (R × Word (n + 1)) (R × Word (n + 1)) ℂ)
    (positive : ∀ o, (effect o).PosSemidef) (complete : ∑ o, effect o = 1)
    (reportsZero : Word (n + 1) → Ω → Bool)
    (h0 : ∀ a, 2 / 3 ≤ ∑ o ∈ Finset.univ.filter (fun o => reportsZero a o = true),
      bornMass effect (P.terminal (markedChannel a 0)) o)
    (h1 : ∀ a, 2 / 3 ≤ ∑ o ∈ Finset.univ.filter (fun o => ¬ reportsZero a o = true),
      bornMass effect (P.terminal (markedChannel a 1)) o) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T := by
  apply P.query_lower_bound (fun a => BinaryPOVM.ofFiniteDecision effect positive complete
    (reportsZero a))
  · intro a
    rw [BinaryPOVM.ofFiniteDecision_probZero]
    exact h0 a
  · intro a
    rw [BinaryPOVM.ofFiniteDecision_probOne]
    exact h1 a

/-- A finite outcome reconstruction with error below one on both branches yields a
terminal decision by reporting zero exactly when the estimate is within one of branch zero. -/
theorem reconstruction_query_lower_bound {Ω : Type*} [Fintype Ω]
    (effect : Ω → Matrix (R × Word (n + 1)) (R × Word (n + 1)) ℂ)
    (positive : ∀ o, (effect o).PosSemidef) (complete : ∑ o, effect o = 1)
    (estimate : Ω → QuantumChannel (Word (n + 1)) (Word (n + 1)))
    (success : ∀ a b, 2 / 3 ≤
      ∑ o ∈ Finset.univ.filter (fun o => diamondDistance (markedChannel a b) (estimate o) < 1),
        bornMass effect (P.terminal (markedChannel a b)) o) :
    (2 : ℝ) ^ (n + 1) / 3 ≤ T := by
  classical
  let reportsZero (a : Word (n + 1)) (o : Ω) :=
    decide (diamondDistance (markedChannel a 0) (estimate o) < 1)
  apply P.finite_povm_query_lower_bound effect positive complete reportsZero
  · intro a
    simpa only [reportsZero, decide_eq_true_eq] using success a 0
  · intro a
    refine (success a 1).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · intro o ho
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, reportsZero, decide_eq_true_eq] at *
      exact fun hz => markedPair_diamond_balls_disjoint a (estimate o) hz ho
    · intro o _ _
      exact bornMass_nonneg effect positive _ o

end AdaptiveProtocol
end Protocol


end D5.S3.Quantum.EnvironmentRecords.HiddenInput
