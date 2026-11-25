/- GID: D5/S3/Quantum/PureState/PhaseMemoryCompact
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseMemoryCompact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The set of scores of finite CPTP memory and POVM strategies is compact. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.PureState.PureStateHandshake

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality (channel_kraus_stinespring)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

namespace PhaseMemoryOptimized

noncomputable section

variable {a b x : Type} [Fintype a] [Fintype b] [Fintype x]
  [DecidableEq a] [DecidableEq b]

/-- A finite measurement on the memory. -/
def IsPOVM (D : x → Matrix b b ℂ) : Prop :=
  (∀ j, (D j).PosSemidef) ∧ ∑ j, D j = 1

/-- Mean probability of correct decoding, with uniform prior on the labels. -/
def score (ψ : x → a → ℂ) (Φ : QuantumChannel a b) (D : x → Matrix b b ℂ) : ℝ :=
  (∑ j, (trace (D j * CStarMatrix.ofMatrix.symm
    (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rankOneDensity (ψ j)))))).re) /
    Fintype.card x

/-- Scores realized by a single CPTP encoder and a POVM. -/
def successSet (b : Type) [Fintype b] [DecidableEq b] (ψ : x → a → ℂ) : Set ℝ :=
  {s | ∃ (Φ : QuantumChannel a b) (D : x → Matrix b b ℂ), IsPOVM D ∧ s = score ψ Φ D}

private abbrev Kraus (a b : Type) := (b × a) → Matrix b a ℂ

private def normalized : Set (Kraus a b) :=
  {K | ∑ k, (K k).conjTranspose * K k = 1}

omit [DecidableEq b] in
private theorem normalized_isCompact : IsCompact (normalized (a := a) (b := b)) := by
  have hclosed : IsClosed (normalized (a := a) (b := b)) :=
    isClosed_eq (by fun_prop) continuous_const
  have hball := isCompact_closedBall (0 : ℂ) 1
  have hcube := isCompact_pi_infinite (fun _ : b × a =>
    isCompact_pi_infinite (fun _ : b => isCompact_pi_infinite (fun _ : a => hball)))
  apply hcube.of_isClosed_subset hclosed
  intro K hK k i j
  rw [Metric.mem_closedBall, dist_zero_right]
  have hdiag : ∑ l, ∑ r, ‖K l r j‖ ^ 2 = 1 := by
    have h := congrArg (fun A : Matrix a a ℂ => A j j)
      (show (∑ l, (Matrix.of (K l)).conjTranspose * Matrix.of (K l)) = 1 from hK)
    change (∑ l, (Matrix.of (K l)).conjTranspose * Matrix.of (K l)) j j = (1 : Matrix a a ℂ) j j at h
    rw [Matrix.one_apply_eq] at h
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum, Matrix.of_apply] at h
    exact_mod_cast h
  have hk : ‖K k i j‖ ^ 2 ≤ 1 := calc
    _ ≤ ∑ r, ‖K k r j‖ ^ 2 :=
      Finset.single_le_sum (fun r _ => sq_nonneg ‖K k r j‖) (Finset.mem_univ i)
    _ ≤ ∑ l, ∑ r, ‖K l r j‖ ^ 2 :=
      Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg fun r _ => sq_nonneg ‖K l r j‖) (Finset.mem_univ k)
    _ = 1 := hdiag
  nlinarith [norm_nonneg (K k i j)]

private theorem povm_isCompact : IsCompact {D : x → Matrix b b ℂ | IsPOVM D} := by
  have hpos : IsClosed {D : x → Matrix b b ℂ | ∀ j, (D j).PosSemidef} := by
    convert isClosed_iInter (fun j : x => Matrix.posSemidef_is_closed.preimage
      (continuous_apply j : Continuous (fun D : x → Matrix b b ℂ => D j))) using 1
    ext D
    simp
  have hsum : IsClosed {D : x → Matrix b b ℂ | ∑ j, D j = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hball := isCompact_closedBall (0 : Matrix b b ℂ) 1
  apply (isCompact_pi_infinite (fun _ : x => hball)).of_isClosed_subset (hpos.inter hsum)
  intro D hD j
  rw [Metric.mem_closedBall, dist_zero_right]
  have hle : D j ≤ 1 := calc
    _ ≤ ∑ k, D k :=
      Finset.single_le_sum (fun k _ => (hD.1 k).nonneg) (Finset.mem_univ j)
    _ = 1 := hD.2
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (D j) (hD.1 j).nonneg).2 hle

private def krausScore (ψ : x → a → ℂ) (p : Kraus a b × (x → Matrix b b ℂ)) : ℝ :=
  (∑ j, (trace (p.2 j * ∑ k, p.1 k * rankOneDensity (ψ j) * (p.1 k).conjTranspose)).re) /
    Fintype.card x

omit [DecidableEq a] [DecidableEq b] in
private theorem krausScore_continuous (ψ : x → a → ℂ) :
    Continuous (krausScore (b := b) ψ) := by
  unfold krausScore Matrix.trace Matrix.diag
  fun_prop

private theorem successSet_eq_image (ψ : x → a → ℂ) :
    successSet b ψ =
      krausScore ψ '' (normalized ×ˢ {D : x → Matrix b b ℂ | IsPOVM D}) := by
  ext s
  constructor
  · rintro ⟨Φ, D, hD, rfl⟩
    obtain ⟨K, hK, hΦ⟩ := channel_kraus_stinespring.1 Φ
    exact ⟨(K, D), ⟨hK, hD⟩, by simp only [krausScore, score, hΦ]⟩
  · rintro ⟨⟨K, D⟩, ⟨hK, hD⟩, rfl⟩
    obtain ⟨Φ, hΦ⟩ := finite_kraus_quantum_channel K hK
    exact ⟨Φ, D, hD, by simp only [krausScore, score, hΦ]⟩

/-- All scores of the finite CPTP and POVM model form a compact set. -/
theorem successSet_isCompact (ψ : x → a → ℂ) : IsCompact (successSet b ψ) := by
  rw [successSet_eq_image]
  exact (normalized_isCompact.prod povm_isCompact).image (krausScore_continuous ψ)

/-- A finite nonempty label set and memory admit a physical strategy of maximum score. -/
theorem exists_isGreatest_successSet [Nonempty b] [Nonempty x] (ψ : x → a → ℂ) :
    ∃ s, IsGreatest (successSet b ψ) s := by
  classical
  let i : b := Classical.choice ‹Nonempty b›
  let j : x := Classical.choice ‹Nonempty x›
  let K (k : a) : Matrix b a ℂ := Matrix.single i k 1
  have hK : ∑ k, (K k).conjTranspose * K k = 1 := by
    ext p q
    simp only [K, Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same,
      mul_one, Matrix.sum_apply]
    by_cases hp : p = q
    · subst q
      simp [Matrix.single, eq_comm]
    · simp [Matrix.single, hp,
        show ∀ k : a, ¬(k = p ∧ k = q) from fun k h => hp (h.1.symm.trans h.2)]
  obtain ⟨Φ, _⟩ := finite_kraus_quantum_channel K hK
  let D (k : x) : Matrix b b ℂ := if k = j then 1 else 0
  have hD : IsPOVM D := ⟨fun k => by by_cases h : k = j <;> simp [D, h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero], by simp [D]⟩
  exact (successSet_isCompact ψ).exists_isGreatest ⟨_, Φ, D, hD, rfl⟩

end

end PhaseMemoryOptimized
