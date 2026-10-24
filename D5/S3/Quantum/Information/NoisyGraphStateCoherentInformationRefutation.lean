/- GID: D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim; result=D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result; claim=D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim
   digest: A noisy graph state on five plus four qubits reverses subsystem coherent information. -/

import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.CStarAlgebra.Projection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation

open scoped BigOperators
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- Independent dephasing of the state `|+⟩`, with survival probability `P`. -/
noncomputable def noisyQubit (P : ℝ) : Matrix Bool Bool ℂ :=
  let plus : Bool → ℂ := fun b =>
    D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.plusState 1 (fun _ => b)
  let minus : Bool → ℂ := fun b => (if b then -1 else 1) * plus b
  (P : ℂ) • Matrix.vecMulVec plus (star plus) +
    ((1 - P : ℝ) : ℂ) • Matrix.vecMulVec minus (star minus)

/-- The product of the diagonal controlled-Z entries over every graph edge. -/
noncomputable def czPhase {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (x : Fin nA ⊕ Fin nB → Bool) : ℂ :=
  ∏ e ∈ G.edgeFinset,
    D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase
      (e.map finSumFinEquiv) (x ∘ finSumFinEquiv.symm)

/-- The uniformly dephased graph state, in the product computational basis. -/
noncomputable def graphState {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) :
    Matrix ((Fin nA → Bool) × (Fin nB → Bool))
      ((Fin nA → Bool) × (Fin nB → Bool)) ℂ :=
  fun x y => czPhase G (Sum.elim x.1 x.2) *
    (∏ v, noisyQubit P (Sum.elim x.1 x.2 v) (Sum.elim y.1 y.2 v)) *
    star (czPhase G (Sum.elim y.1 y.2))

/-- Base-two von Neumann entropy, using the continuous functional calculus logarithm. -/
noncomputable def entropy2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : Matrix ι ι ℂ) : ℝ :=
  -(Matrix.trace (CStarMatrix.ofMatrix rho * CFC.log (CStarMatrix.ofMatrix rho))).re /
    Real.log 2

noncomputable def coherentInfoA {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) : ℝ :=
  entropy2 (partialTraceRight (graphState G P)) - entropy2 (graphState G P)

noncomputable def coherentInfoB {nA nB : ℕ} (G : SimpleGraph (Fin nA ⊕ Fin nB))
    [DecidableRel G.Adj] (P : ℝ) : ℝ :=
  entropy2 (partialTraceLeft (graphState G P)) - entropy2 (graphState G P)

/-- The subsystem-size conjecture for every graph and uniform dephasing probability. -/
def claim : Prop :=
  ∀ (nA nB : ℕ), nB < nA →
    ∀ (G : SimpleGraph (Fin nA ⊕ Fin nB)) [DecidableRel G.Adj] (P : ℝ),
      P ∈ Set.Icc 0 1 → coherentInfoB G P ≤ coherentInfoA G P

private def bipartiteGraph {m n : ℕ} (M : Fin m → Fin n → Bool) :
    SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inr j => M i j = true
    | Sum.inr j, Sum.inl i => M i j = true
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> simp

private instance bipartiteDecidable {m n : ℕ} (M : Fin m → Fin n → Bool) :
    DecidableRel (bipartiteGraph M).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp only [bipartiteGraph] <;> infer_instance

private def distance {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  ∑ i, if x i = y i then 0 else 1

private lemma reduced_A {m n : ℕ} (M : Fin m → Fin n → Bool) (P : ℝ)
    (a a' : Fin m → Bool) :
    partialTraceRight (graphState (bipartiteGraph M) P) a a' =
      (2 : ℂ)⁻¹ ^ m * (2 * (P : ℂ) - 1) ^ distance a a' *
        (if ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
          then 1 else 0) := by
  sorry

private lemma reduced_B {m n : ℕ} (M : Fin m → Fin n → Bool) (P : ℝ)
    (b b' : Fin n → Bool) :
    partialTraceLeft (graphState (bipartiteGraph M) P) b b' =
      (2 : ℂ)⁻¹ ^ n * (2 * (P : ℂ) - 1) ^ distance b b' *
        (if ∀ i, Even (∑ j, (M i j && Bool.xor (b j) (b' j)).toNat)
          then 1 else 0) := by
  sorry

private def M : Fin 5 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, true, false, false],
    ![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true]]

private def projectionA : Matrix (Fin 5 → Bool) (Fin 5 → Bool) ℂ :=
  fun a a' => if ∀ j, Even (∑ i, (M i j && Bool.xor (a i) (a' i)).toNat)
    then 1 / 4 else 0

private def flipB : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℂ :=
  fun b b' => if ∀ i, b i ≠ b' i then 1 else 0

private def projectionB : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℂ :=
  (1 + flipB) / 2

private def u : ℝ := (127 / 128) ^ 2
private def a₁ : ℝ := (1 + 3 * u) / 32
private def a₂ : ℝ := (1 - u) / 32
private def b₁ : ℝ := (1 + u ^ 2) / 16
private def b₂ : ℝ := (1 - u ^ 2) / 16

private lemma spectral_data :
    IsStarProjection (CStarMatrix.ofMatrix projectionA) ∧
    Matrix.trace projectionA = 8 ∧
    IsStarProjection (CStarMatrix.ofMatrix projectionB) ∧
    Matrix.trace projectionB = 8 ∧
    partialTraceRight (graphState (bipartiteGraph M) (255 / 256)) =
      a₁ • projectionA + a₂ • (1 - projectionA) ∧
    partialTraceLeft (graphState (bipartiteGraph M) (255 / 256)) =
      b₁ • projectionB + b₂ • (1 - projectionB) := by
  have hA := reduced_A M (255 / 256)
  have hB := reduced_B M (255 / 256)
  sorry

private lemma two_projection_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : IsStarProjection (CStarMatrix.ofMatrix Q))
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    entropy2 (r • Q + s • (1 - Q)) =
      (-(Matrix.trace Q).re * r * Real.log r -
        (Fintype.card ι - (Matrix.trace Q).re) * s * Real.log s) / Real.log 2 := by
  sorry

private lemma witness_entropies :
    entropy2 (partialTraceRight (graphState (bipartiteGraph M) (255 / 256))) =
      (-8 * a₁ * Real.log a₁ - 24 * a₂ * Real.log a₂) / Real.log 2 ∧
    entropy2 (partialTraceLeft (graphState (bipartiteGraph M) (255 / 256))) =
      (-8 * b₁ * Real.log b₁ - 8 * b₂ * Real.log b₂) / Real.log 2 := by
  obtain ⟨hQA, htA, hQB, htB, hA, hB⟩ := spectral_data
  rw [hA, hB]
  constructor
  · rw [two_projection_entropy projectionA hQA a₁ a₂
      (by norm_num [a₁, u]) (by norm_num [a₂, u]), htA]
    norm_num
  · rw [two_projection_entropy projectionB hQB b₁ b₂
      (by norm_num [b₁, u]) (by norm_num [b₂, u]), htB]
    norm_num

private lemma numerical_inequality :
    -8 * a₁ * Real.log a₁ - 24 * a₂ * Real.log a₂ <
      -8 * b₁ * Real.log b₁ - 8 * b₂ * Real.log b₂ := by
  sorry

private lemma witness_entropy_comparison :
    entropy2 (partialTraceRight (graphState (bipartiteGraph M) (255 / 256))) <
      entropy2 (partialTraceLeft (graphState (bipartiteGraph M) (255 / 256))) := by
  rw [witness_entropies.1, witness_entropies.2]
  exact div_lt_div_of_pos_right numerical_inequality (Real.log_pos (by norm_num))

/-- A nine-qubit bipartite graph reverses the proposed ordering. -/
theorem result : ¬ claim := by
  intro h
  have hle := h 5 4 (by norm_num) (bipartiteGraph M) (255 / 256) (by norm_num)
  unfold coherentInfoA coherentInfoB at hle
  exact (not_le_of_gt witness_entropy_comparison) ((sub_le_sub_iff_right _).mp hle)

end D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation
