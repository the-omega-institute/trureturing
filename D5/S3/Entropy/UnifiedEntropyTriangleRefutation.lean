/- GID: D5/S3/Entropy/UnifiedEntropyTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/UnifiedEntropyTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim; result=D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result; claim=D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim
   digest: Unified entropy correlations violate the triangle inequality at (2, -1). -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Information.PartialTraceMutualInformation

/-! A rational two-qubit state violates the universal triangle-like correlation inequality. -/

open scoped BigOperators Kronecker ComplexOrder
open Matrix
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Observer.Conditioning (unreadState)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (isHermitian_kronecker)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Entropy.UnifiedEntropyTriangleRefutation

/-- Spectral power trace, with real powers on the spectrum. -/
def genPurity {α : Type} [Fintype α] [DecidableEq α]
    (q : ℝ) (σ : Matrix α α ℂ) : ℝ :=
  (D5.S3.Quantum.Matrix.SpectralPower.mpow σ q).trace.re

/-- Unified entropy away from its limiting indices. -/
def unifiedEntropy {α : Type} [Fintype α] [DecidableEq α]
    (q s : ℝ) (σ : Matrix α α ℂ) : ℝ :=
  (genPurity q σ ^ s - 1) / ((1 - q) * s)

/-- Unread rank-one projective measurement on the first factor. -/
def measureA {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : Matrix.unitaryGroup α ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :=
  unreadState (fun i => rankOneDensity (fun a => u a i) ⊗ₖ (1 : Matrix β β ℂ)) ρ

/-- Unread rank-one projective measurement on the second factor. -/
def measureB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (v : Matrix.unitaryGroup β ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :=
  unreadState (fun j => (1 : Matrix α α ℂ) ⊗ₖ rankOneDensity (fun b => v b j)) ρ

/-- Unread local rank-one projective measurement on both factors. -/
def measureAB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : Matrix.unitaryGroup α ℂ) (v : Matrix.unitaryGroup β ℂ)
    (ρ : Matrix (α × β) (α × β) ℂ) :=
  ∑ i, unreadState
    (fun j => rankOneDensity (fun a => u a i) ⊗ₖ rankOneDensity (fun b => v b j)) ρ

/-- Entropic disturbance normalized by the original spectral power trace. -/
def disturbance {α : Type} [Fintype α] [DecidableEq α]
    (q s : ℝ) (σ ρ : Matrix α α ℂ) : ℝ :=
  (unifiedEntropy q s σ - unifiedEntropy q s ρ) / genPurity q ρ ^ s

/-- Infimum over every local measurement on the first factor. -/
def correlationA {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun u : Matrix.unitaryGroup α ℂ => disturbance q s (measureA u ρ) ρ)

/-- Infimum over every local measurement on the second factor. -/
def correlationB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun v : Matrix.unitaryGroup β ℂ => disturbance q s (measureB v ρ) ρ)

/-- Infimum over all pairs of local rank-one measurements. -/
def correlationAB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun uv : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup β ℂ =>
    disturbance q s (measureAB uv.1 uv.2 ρ) ρ)

/-- The triangle-like inequality for every admissible unified entropy and finite state. -/
def claim : Prop :=
  ∀ q s : ℝ, 0 < q → q ≠ 1 → s ≠ 0 →
    ∀ (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (ρ : Matrix (α × β) (α × β) ℂ),
      ρ.PosSemidef → ρ.trace = 1 →
      correlationAB q s ρ ≤ correlationA q s ρ + correlationB q s ρ

private def witness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a b =>
    ( !![!![6, 1; 1, 2], !![1, 0; 0, 1];
         !![1, 0; 0, 1], !![2, 1; 1, 6]] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) a.1 b.1 a.2 b.2 / 16

private lemma witness_entries (a b : Fin 2 × Fin 2) : witness a b =
    ( !![!![6, 1; 1, 2], !![1, 0; 0, 1];
         !![1, 0; 0, 1], !![2, 1; 1, 6]] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) a.1 b.1 a.2 b.2 / 16 := rfl

private lemma witness_posSemidef : witness.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    rcases a with ⟨a, c⟩
    rcases b with ⟨b, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp only [Matrix.conjTranspose_apply, witness_entries] <;> norm_num
  · intro z
    have he : star z ⬝ᵥ (witness *ᵥ z) =
        (((Complex.normSq (z (0, 0) + z (0, 1)) +
          Complex.normSq (z (0, 0) + z (1, 0)) +
          Complex.normSq (z (0, 1) + z (1, 1)) +
          Complex.normSq (z (1, 0) + z (1, 1)) +
          4 * Complex.normSq (z (0, 0)) + 4 * Complex.normSq (z (1, 1))) / 16 : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
        Pi.star_apply, witness_entries]
      apply Complex.ext <;>
        simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im] <;> ring
    rw [he]
    have h1 := Complex.normSq_nonneg (z (0, 0) + z (0, 1))
    have h2 := Complex.normSq_nonneg (z (0, 0) + z (1, 0))
    have h3 := Complex.normSq_nonneg (z (0, 1) + z (1, 1))
    have h4 := Complex.normSq_nonneg (z (1, 0) + z (1, 1))
    have h5 := Complex.normSq_nonneg (z (0, 0))
    have h6 := Complex.normSq_nonneg (z (1, 1))
    exact_mod_cast div_nonneg
      (by linarith : (0 : ℝ) ≤ Complex.normSq (z (0, 0) + z (0, 1)) +
        Complex.normSq (z (0, 0) + z (1, 0)) +
        Complex.normSq (z (0, 1) + z (1, 1)) +
        Complex.normSq (z (1, 0) + z (1, 1)) +
        4 * Complex.normSq (z (0, 0)) + 4 * Complex.normSq (z (1, 1)))
      (by norm_num : (0 : ℝ) ≤ 16)

private lemma witness_trace : witness.trace = 1 := by
  have he : witness = (fun a b =>
      ( !![!![6, 1; 1, 2], !![1, 0; 0, 1];
           !![1, 0; 0, 1], !![2, 1; 1, 6]] :
        Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) a.1 b.1 a.2 b.2 / 16) :=
    funext fun a => funext fun b => witness_entries a b
  exact (congrArg Matrix.trace he).trans (by
    change (∑ a : Fin 2 × Fin 2,
      ( !![!![6, 1; 1, 2], !![1, 0; 0, 1];
           !![1, 0; 0, 1], !![2, 1; 1, 6]] :
        Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) a.1 a.1 a.2 a.2 / 16) = 1
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num)

private lemma witness_purity : (witness * witness).trace.re = 11 / 32 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, witness_entries]
  norm_num

private lemma genPurity_two {α : Type} [Fintype α] [DecidableEq α]
    (σ : Matrix α α ℂ) (hσ : σ.IsHermitian) :
    genPurity 2 σ = (σ * σ).trace.re :=
  congrArg (fun a : Matrix α α ℂ => a.trace.re)
    (D5.S3.Quantum.Matrix.SpectralPower.mpow_two hσ)

private lemma disturbance_two_neg_one {α : Type} [Fintype α] [DecidableEq α]
    (σ ρ : Matrix α α ℂ) (hσ : σ.IsHermitian) (hρ : ρ.IsHermitian)
    (hp : (ρ * ρ).trace.re ≠ 0) :
    disturbance 2 (-1) σ ρ = (ρ * ρ).trace.re / (σ * σ).trace.re - 1 := by
  change ((genPurity 2 σ ^ (-1 : ℝ) - 1) / ((1 - 2) * (-1)) -
    (genPurity 2 ρ ^ (-1 : ℝ) - 1) / ((1 - 2) * (-1))) /
    genPurity 2 ρ ^ (-1 : ℝ) = _
  rw [genPurity_two σ hσ, genPurity_two ρ hρ]
  simp only [Real.rpow_neg_one, show ((1 : ℝ) - 2) * (-1) = 1 by norm_num, div_one]
  rw [div_inv_eq_mul]
  simp only [sub_sub_sub_cancel_right, sub_mul, inv_mul_cancel₀ hp]
  rw [div_eq_mul_inv, mul_comm]

private lemma qubit_projectors (u : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧
      rankOneDensity (fun a => u a 0) = blochMatrix 1 n ∧
      rankOneDensity (fun a => u a 1) = 1 - rankOneDensity (fun a => u a 0) := by
  have hcol : ∑ k, star (u k 0) * u k 0 = (1 : ℂ) := by
    simpa only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
      Matrix.one_apply, ite_true] using congrFun (congrFun u.prop.1 0) 0
  have hh : (rankOneDensity (fun a => u a 0)).IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star (fun a => u a 0)).isHermitian
  have ht : (rankOneDensity (fun a => u a 0)).trace = 1 := by
    change ∑ k, u k 0 * star (u k 0) = 1
    simpa only [mul_comm] using hcol
  have hp : rankOneDensity (fun a => u a 0) * rankOneDensity (fun a => u a 0) =
      rankOneDensity (fun a => u a 0) :=
    (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
      (fun k => u k 0) hcol 0).1
  have hc : rankOneDensity (fun a => u a 0) + rankOneDensity (fun a => u a 1) = 1 := by
    ext a b
    change u a 0 * star (u b 0) + u a 1 * star (u b 1) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) a b
    simpa only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] using
      congrFun (congrFun u.prop.2 a) b
  have hg := bloch_geometry_of_isHermitian (rankOneDensity (fun a => u a 0)) hh
  refine ⟨bloch (rankOneDensity (fun a => u a 0)), hg.2 ht hp, ?_, ?_⟩
  · simpa only [ht, Complex.one_re] using hg.1
  · exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hc)

private lemma measured_hermitian (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    (measureA u witness).IsHermitian ∧ (measureB v witness).IsHermitian ∧
      (measureAB u v witness).IsHermitian := by
  have hp (w : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
      (rankOneDensity (fun a => w a i)).IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star (fun a => w a i)).isHermitian
  have hs (p : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h : p.IsHermitian) :
      (p * witness * p).IsHermitian := by
    simpa only [h.eq] using Matrix.isHermitian_mul_mul_conjTranspose p
      witness_posSemidef.isHermitian
  refine ⟨?_, ?_, ?_⟩
  · change IsSelfAdjoint (∑ i,
      (rankOneDensity (fun a => u a i) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      witness * (rankOneDensity (fun a => u a i) ⊗ₖ 1))
    exact isSelfAdjoint_sum _ fun i _ => hs _ (isHermitian_kronecker (hp u i) Matrix.isHermitian_one)
  · change IsSelfAdjoint (∑ j,
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rankOneDensity (fun a => v a j)) *
      witness * (1 ⊗ₖ rankOneDensity (fun a => v a j)))
    exact isSelfAdjoint_sum _ fun j _ => hs _ (isHermitian_kronecker Matrix.isHermitian_one (hp v j))
  · change IsSelfAdjoint (∑ i, ∑ j,
      (rankOneDensity (fun a => u a i) ⊗ₖ rankOneDensity (fun a => v a j)) *
      witness * (rankOneDensity (fun a => u a i) ⊗ₖ rankOneDensity (fun a => v a j)))
    exact isSelfAdjoint_sum _ fun i _ => isSelfAdjoint_sum _ fun j _ =>
      hs _ (isHermitian_kronecker (hp u i) (hp v j))

private lemma measurement_expansions (u v : Matrix.unitaryGroup (Fin 2) ℂ)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    measureA u ρ = ∑ i, (rankOneDensity (fun a => u a i) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ρ * (rankOneDensity (fun a => u a i) ⊗ₖ 1) ∧
    measureB v ρ = ∑ j, ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rankOneDensity (fun a => v a j)) *
      ρ * (1 ⊗ₖ rankOneDensity (fun a => v a j)) ∧
    measureAB u v ρ = ∑ i, ∑ j,
      (rankOneDensity (fun a => u a i) ⊗ₖ rankOneDensity (fun a => v a j)) *
      ρ * (rankOneDensity (fun a => u a i) ⊗ₖ rankOneDensity (fun a => v a j)) := ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
-- Four local outcome blocks expand to polynomial traces of degree eight.
private lemma measured_purities (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ n m : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧ ‖m‖ = 1 ∧
      (measureA u witness * measureA u witness).trace.re =
        (1 + 1 / 16 + (n 0)^2 / 16 + (n 2)^2 / 4) / 4 ∧
      (measureB v witness * measureB v witness).trace.re =
        (1 + 1 / 16 + (m 0)^2 / 16 + (m 2)^2 / 4) / 4 ∧
      (measureAB u v witness * measureAB u v witness).trace.re =
        (1 + ((n 0)^2 + (m 0)^2) / 16 + (n 2)^2 * (m 2)^2 / 4) / 4 := by
  obtain ⟨n, hn, hn0, hn1⟩ := qubit_projectors u
  obtain ⟨m, hm, hm0, hm1⟩ := qubit_projectors v
  have hn0 := hn0.trans (blochMatrix.eq_1 1 n)
  have hm0 := hm0.trans (blochMatrix.eq_1 1 m)
  have hnz : (n 2)^2 = 1 - (n 0)^2 - (n 1)^2 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    simp only [Fin.sum_univ_three, hn, one_pow] at h
    linarith
  have hmz : (m 2)^2 = 1 - (m 0)^2 - (m 1)^2 := by
    have h := EuclideanSpace.real_norm_sq_eq m
    simp only [Fin.sum_univ_three, hm, one_pow] at h
    linarith
  obtain ⟨ha, hb, hab⟩ := measurement_expansions u v witness
  refine ⟨n, m, hn, hm, ?_, ?_, ?_⟩
  all_goals
    first | rw [ha] | rw [hb] | rw [hab]
    simp only [Fin.sum_univ_two, hn1, hn0, hm1, hm0,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, witness_entries]
    simp [Complex.mul_re, Complex.mul_im]
    ring_nf
    simp only [show (n 2)^4 = ((n 2)^2)^2 by ring,
      show (m 2)^4 = ((m 2)^2)^2 by ring,
      hnz, hmz]
    ring

private lemma bloch_purity_bounds (n m : EuclideanSpace ℝ (Fin 3))
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) :
    (1 / 4 ≤ (1 + 1 / 16 + (n 0)^2 / 16 + (n 2)^2 / 4) / 4 ∧
      (1 + 1 / 16 + (n 0)^2 / 16 + (n 2)^2 / 4) / 4 ≤ 21 / 64) ∧
    (1 / 4 ≤ (1 + 1 / 16 + (m 0)^2 / 16 + (m 2)^2 / 4) / 4 ∧
      (1 + 1 / 16 + (m 0)^2 / 16 + (m 2)^2 / 4) / 4 ≤ 21 / 64) ∧
    (1 / 4 ≤ (1 + ((n 0)^2 + (m 0)^2) / 16 + (n 2)^2 * (m 2)^2 / 4) / 4 ∧
      (1 + ((n 0)^2 + (m 0)^2) / 16 + (n 2)^2 * (m 2)^2 / 4) / 4 ≤ 5 / 16) := by
  have hn2 : (n 0)^2 + (n 1)^2 + (n 2)^2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    simpa only [Fin.sum_univ_three, hn, one_pow] using h.symm
  have hm2 : (m 0)^2 + (m 1)^2 + (m 2)^2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq m
    simpa only [Fin.sum_univ_three, hm, one_pow] using h.symm
  have hnx : (n 0)^2 ≤ 1 := by nlinarith [sq_nonneg (n 1), sq_nonneg (n 2)]
  have hmx : (m 0)^2 ≤ 1 := by nlinarith [sq_nonneg (m 1), sq_nonneg (m 2)]
  have hnz : (n 2)^2 ≤ 1 - (n 0)^2 := by nlinarith [sq_nonneg (n 1)]
  have hmz : (m 2)^2 ≤ 1 - (m 0)^2 := by nlinarith [sq_nonneg (m 1)]
  have hj := mul_le_mul hnz hmz (sq_nonneg (m 2)) (by linarith : 0 ≤ 1 - (n 0)^2)
  have hx := mul_nonneg (sq_nonneg (n 0)) (sub_nonneg.mpr hmx)
  have hy := mul_nonneg (sq_nonneg (m 0)) (sub_nonneg.mpr hnx)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    nlinarith [sq_nonneg (n 0), sq_nonneg (n 1), sq_nonneg (n 2),
      sq_nonneg (m 0), sq_nonneg (m 1), sq_nonneg (m 2),
      mul_nonneg (sq_nonneg (n 2)) (sq_nonneg (m 2))]

private lemma measured_purity_bounds (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    (1 / 4 ≤ (measureA u witness * measureA u witness).trace.re ∧
      (measureA u witness * measureA u witness).trace.re ≤ 21 / 64) ∧
    (1 / 4 ≤ (measureB v witness * measureB v witness).trace.re ∧
      (measureB v witness * measureB v witness).trace.re ≤ 21 / 64) ∧
    (1 / 4 ≤ (measureAB u v witness * measureAB u v witness).trace.re ∧
      (measureAB u v witness * measureAB u v witness).trace.re ≤ 5 / 16) := by
  obtain ⟨n, m, hn, hm, ha, hb, hab⟩ := measured_purities u v
  obtain ⟨hpa, hpb, hpab⟩ := bloch_purity_bounds n m hn hm
  exact ⟨Eq.mpr (congrArg (fun p : ℝ => 1 / 4 ≤ p ∧ p ≤ 21 / 64) ha) hpa,
    Eq.mpr (congrArg (fun p : ℝ => 1 / 4 ≤ p ∧ p ≤ 21 / 64) hb) hpb,
    Eq.mpr (congrArg (fun p : ℝ => 1 / 4 ≤ p ∧ p ≤ 5 / 16) hab) hpab⟩

private lemma computational_purities :
    (measureA 1 witness * measureA 1 witness).trace.re = 21 / 64 ∧
    (measureB 1 witness * measureB 1 witness).trace.re = 21 / 64 ∧
    (measureAB 1 1 witness * measureAB 1 1 witness).trace.re = 5 / 16 := by
  obtain ⟨ha, hb, hab⟩ := measurement_expansions 1 1 witness
  rw [ha, hb, hab]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.one_apply, witness_entries]

private lemma correlations : correlationA 2 (-1) witness = 1 / 21 ∧
    correlationB 2 (-1) witness = 1 / 21 ∧ correlationAB 2 (-1) witness = 1 / 10 := by
  have hr (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : σ.IsHermitian) :
      disturbance 2 (-1) σ witness = (11 / 32) / (σ * σ).trace.re - 1 := by
    rw [disturbance_two_neg_one σ witness hσ witness_posSemidef.isHermitian
      (by rw [witness_purity]; norm_num), witness_purity]
  have ha (u : Matrix.unitaryGroup (Fin 2) ℂ) :
      1 / 21 ≤ disturbance 2 (-1) (measureA u witness) witness := by
    rw [hr _ (measured_hermitian u 1).1]
    obtain ⟨hl, hu⟩ := (measured_purity_bounds u 1).1
    exact le_sub_iff_add_le.mpr ((le_div_iff₀
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hl)).mpr
      (le_trans (mul_le_mul_of_nonneg_left hu (by norm_num)) (by norm_num)))
  have hb (v : Matrix.unitaryGroup (Fin 2) ℂ) :
      1 / 21 ≤ disturbance 2 (-1) (measureB v witness) witness := by
    rw [hr _ (measured_hermitian 1 v).2.1]
    obtain ⟨hl, hu⟩ := (measured_purity_bounds 1 v).2.1
    exact le_sub_iff_add_le.mpr ((le_div_iff₀
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hl)).mpr
      (le_trans (mul_le_mul_of_nonneg_left hu (by norm_num)) (by norm_num)))
  have hab (uv : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ) :
      1 / 10 ≤ disturbance 2 (-1) (measureAB uv.1 uv.2 witness) witness := by
    rw [hr _ (measured_hermitian uv.1 uv.2).2.2]
    obtain ⟨hl, hu⟩ := (measured_purity_bounds uv.1 uv.2).2.2
    exact le_sub_iff_add_le.mpr ((le_div_iff₀
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hl)).mpr
      (le_trans (mul_le_mul_of_nonneg_left hu (by norm_num)) (by norm_num)))
  have hinf {ι : Type} (f : ι → ℝ) (a : ℝ) (i : ι)
      (hl : ∀ j, a ≤ f j) (he : f i = a) : sInf (Set.range f) = a :=
    IsLeast.csInf_eq ⟨⟨i, he⟩, by rintro _ ⟨j, rfl⟩; exact hl j⟩
  obtain ⟨hca, hcb, hcab⟩ := computational_purities
  refine ⟨hinf _ _ 1 ha ?_, hinf _ _ 1 hb ?_, hinf _ _ (1, 1) hab ?_⟩
  · rw [hr _ (measured_hermitian 1 1).1, hca]
    norm_num
  · rw [hr _ (measured_hermitian 1 1).2.1, hcb]
    norm_num
  · rw [hr _ (measured_hermitian 1 1).2.2, hcab]
    norm_num

/-- Correlations 1/21, 1/21 and 1/10 of the rational two-qubit state refute the inequality. -/
theorem result : ¬ claim := by
  intro h
  have hv := h 2 (-1) (by norm_num) (by norm_num) (by norm_num)
    (Fin 2) (Fin 2) witness witness_posSemidef witness_trace
  obtain ⟨ha, hb, hab⟩ := correlations
  rw [ha, hb, hab] at hv
  norm_num at hv

end D5.S3.Entropy.UnifiedEntropyTriangleRefutation
