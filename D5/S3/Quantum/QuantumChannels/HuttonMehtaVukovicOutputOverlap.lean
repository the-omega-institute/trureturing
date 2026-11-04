/- GID: D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Orthogonal C–Q inputs exceed the minimum distinct-basis output overlap. -/

/-
admission_basis: open-problem-resolution (#20116; Proved)
Public theorem: D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.result
proof_shape: bind-only
escape_witness: none
Direct frozen dependencies:
* cauchyBinet (D5/S3/Quantum/Schatten/CompoundMatrices), declaration statement_id
  sha256:6fb332c198d4506b8775454dff648409222d03ae0a60e7dbf5fca62ea37506df
* D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity, declaration statement_id
  sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988

The state hypothesis in claim directly uses the existing public IsDensity owner,
whose condition is positive semidefiniteness and trace one; orthonormality uses
the source coordinate definition.
The finite-subset carrier, row submatrix and conjugate-row dot products are used directly.
All private lemmas below have proof_shape: bind-only and escape_witness: none.
Their consumers are:
* HMV.weighted_cauchy: total_prob, avoid_prob
* HMV.total_prob: pair_prob, min_le_expected
* HMV.sum_rows: score_as_injection
* HMV.prod_rows: avoid_prob
* HMV.rank_two_det: avoid_one, avoid_two
* HMV.avoid_prob: avoid_one, avoid_two
* HMV.avoid_one: pair_prob
* HMV.avoid_two: pair_prob
* HMV.pair_prob: expected_score
* HMVResidual.off_eq_sub: residual_identity
* HMVResidual.trace_combo: cross_total, output_total
* HMVResidual.cross_star: cross_total, residual_identity
* HMVResidual.cross_total: residual_identity
* HMVResidual.output_total: residual_identity
* HMVResidual.cross_diag: residual_identity
* HMVResidual.residual_identity: subset_residual
* HMVResidual.cross_nonneg: result
* HMV.score_as_full: expected_score
* HMV.expected_score: subset_residual
* HMV.score_as_injection: min_le_expected
* HMV.min_le_expected: result
* HMV.subset_residual: result
The frozen Cauchy–Binet dependency reaches result through weighted_cauchy,
total_prob, avoid_prob, avoid_one, avoid_two, pair_prob, expected_score,
min_le_expected and subset_residual. Other private lemmas use pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21962
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Schatten.CompoundMatrices
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-! Binding conventions for K. Hutton, A. Mehta and A. Vukovic, "Deciding whether a C–Q channel preserves a bit is
QCMA-complete", arXiv:2508.10664v1 (14 August 2025).

* Definition 1.3: a C–Q channel is specified by states `σ₁, …, σₙ` and acts as `Φ(ρ) = Σᵢ Tr(|i⟩⟨i| ρ) σᵢ`; for a
  pure input `|u⟩ = Σᵢ αᵢ |i⟩` this is `Σᵢ |αᵢ|² σᵢ`.
* Conjecture 1.5: "Let σ₁, …, σₙ ∈ M_d(ℂ) be arbitrary quantum states. Then for any collection of k ≤ n of pairwise
  orthogonal pure states |u₁⟩, …, |u_k⟩ ∈ ℂⁿ, the following bound holds:
  (1/(k(k−1))) Σ_{r≠s} Tr((Σᵢ |⟨i|u_r⟩|² σᵢ)(Σⱼ |⟨j|u_s⟩|² σⱼ)) ≥ min_{i₁,…,i_k ∈ [n] distinct} (1/(k(k−1))) Σ_{r≠s}
  Tr(σ_{i_r} σ_{i_s})." The normalization `1/(k(k−1))` requires `k ≥ 2`. Traces of products of states are real; the
  bound compares real parts. -/

namespace D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap

open Matrix ComplexOrder

/-- Definition 1.3 on a pure input `u`: `Φ(|u⟩⟨u|) = Σᵢ |⟨i|u⟩|² σᵢ`. -/
noncomputable def channelOutput {n d : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : Fin n → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, ((Complex.normSq (u i) : ℝ) : ℂ) • σ i

/-- `u₁, …, u_k` are pairwise orthogonal pure states (unit vectors) in `ℂⁿ`. -/
def IsOrthonormalFamily {n k : ℕ} (u : Fin k → Fin n → ℂ) : Prop :=
  ∀ r s, ∑ i, star (u r i) * u s i = if r = s then 1 else 0

/-- The left side of Conjecture 1.5. -/
noncomputable def averageOutputOverlap {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : Fin k → Fin n → ℂ) : ℝ :=
  (1 / ((k : ℝ) * ((k : ℝ) - 1))) *
    ∑ r : Fin k, ∑ s : Fin k, if r = s then 0 else ((channelOutput σ (u r)) * (channelOutput σ (u s))).trace.re

/-- The right side of Conjecture 1.5: the minimum over distinct indices `i₁, …, i_k ∈ [n]`. -/
noncomputable def minDistinctOverlap {n d : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ) (k : ℕ) : ℝ :=
  ⨅ ι : {ι : Fin k → Fin n // Function.Injective ι},
    (1 / ((k : ℝ) * ((k : ℝ) - 1))) *
      ∑ r : Fin k, ∑ s : Fin k, if r = s then 0 else (σ (ι.1 r) * σ (ι.1 s)).trace.re

/-- Conjecture 1.5. -/
def claim : Prop :=
  ∀ (n d k : ℕ) (σ : Fin n → Matrix (Fin d) (Fin d) ℂ), (∀ i, D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity (σ i)) → 2 ≤ k → k ≤ n →
    ∀ u : Fin k → Fin n → ℂ, IsOrthonormalFamily u →
      minDistinctOverlap σ k ≤ averageOutputOverlap σ u

end D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap

set_option backward.isDefEq.respectTransparency false
open Matrix Finset ComplexOrder
open scoped BigOperators
noncomputable section
namespace D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV
private def prob {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ) (S : {S : Finset (Fin n) // S.card = k}) : ℝ :=
  Complex.normSq (U.submatrix (S.1.orderEmbOfFin S.2) id).det
private lemma weighted_cauchy {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ) (z : Fin n → ℂ) :
    (Uᴴ * diagonal z * U).det =
      ∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) * ∏ a : Fin k, z (S.1.orderEmbOfFin S.2 a) := by
  rw [Matrix.mul_assoc, cauchyBinet]
  apply Finset.sum_congr rfl
  intro S _
  have hleft : Uᴴ.submatrix id (S.1.orderEmbOfFin S.2) = (U.submatrix (S.1.orderEmbOfFin S.2) id)ᴴ := by
    exact (Matrix.conjTranspose_submatrix U (S.1.orderEmbOfFin S.2) id).symm
  have hright : (diagonal z * U).submatrix (S.1.orderEmbOfFin S.2) id =
      Matrix.of (fun a b => z (S.1.orderEmbOfFin S.2 a) * (U.submatrix (S.1.orderEmbOfFin S.2) id) a b) := by
    ext a b
    simp [Matrix.diagonal_mul]
  rw [hleft, hright, Matrix.det_conjTranspose, Matrix.det_mul_column]
  simp only [prob, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

private lemma total_prob {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ) (hU : Uᴴ * U = 1) :
    ∑ S : {S : Finset (Fin n) // S.card = k}, prob U S = 1 := by
  have h := weighted_cauchy U (fun _ => 1)
  simp only [Matrix.diagonal_one, Matrix.mul_one, hU, Matrix.det_one,
    Finset.prod_const_one, mul_one] at h
  exact_mod_cast h.symm

private lemma sum_rows {n k : ℕ} (S : {S : Finset (Fin n) // S.card = k}) (f : Fin n → ℂ) :
    ∑ a : Fin k, f (S.1.orderEmbOfFin S.2 a) = ∑ i ∈ S.1, f i := by
  rw [← Finset.sum_image (S.1.orderEmbOfFin S.2).injective.injOn,
    Finset.image_orderEmbOfFin_univ]

private lemma prod_rows {n k : ℕ} (S : {S : Finset (Fin n) // S.card = k}) (f : Fin n → ℂ) :
    ∏ a : Fin k, f (S.1.orderEmbOfFin S.2 a) = ∏ i ∈ S.1, f i := by
  rw [← Finset.prod_image (S.1.orderEmbOfFin S.2).injective.injOn,
    Finset.image_orderEmbOfFin_univ]

private lemma rank_two_det {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (i j : Fin n) (x y : ℂ) :
    (Uᴴ * diagonal (fun l => 1 + (if l = i then x else 0) +
      (if l = j then y else 0)) * U).det =
    (1 + x * ((star (U i)) ⬝ᵥ (U i))) * (1 + y * ((star (U j)) ⬝ᵥ (U j))) - x * y * ((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i)) := by
  have h10 : (1 : Fin 2) ≠ 0 := Ne.symm Fin.zero_ne_one
  let A : Matrix (Fin k) (Fin 2) ℂ := fun r t => if t = 0 then star (U i r) else star (U j r)
  let B : Matrix (Fin 2) (Fin k) ℂ := fun t r => if t = 0 then x * U i r else y * U j r
  have hmat : Uᴴ * diagonal (fun l => 1 + (if l = i then x else 0) +
      (if l = j then y else 0)) * U = 1 + A * B := by
    ext r s
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M r s) hU
    change (∑ l, star (U l r) * U l s) = (1 : Matrix (Fin k) (Fin k) ℂ) r s at h
    change (∑ l, (∑ t, star (U t r) * (diagonal (fun l =>
      1 + (if l = i then x else 0) + (if l = j then y else 0))) t l) * U l s) =
      (1 : Matrix (Fin k) (Fin k) ℂ) r s +
      ∑ t : Fin 2, (if t = 0 then star (U i r) else star (U j r)) *
        (if t = 0 then x * U i s else y * U j s)
    simp only [diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Fin.sum_univ_two, Fin.isValue, h10, ite_false, ite_true]
    simp only [mul_add, add_mul, mul_one, Finset.sum_add_distrib]
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, h]
    ring
  rw [hmat, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]
  change ((1 + ∑ r, (x * U i r) * star (U i r)) *
    (1 + ∑ r, (y * U j r) * star (U j r)) -
    (0 + ∑ r, (x * U i r) * star (U j r)) *
    (0 + ∑ r, (y * U j r) * star (U i r))) = _
  have hq (a b : Fin n) : (∑ r, U a r * star (U b r)) = ((star (U b)) ⬝ᵥ (U a)) := by
    exact dotProduct_comm (U a) (star (U b))
  simp only [zero_add, mul_assoc, ← Finset.mul_sum, hq]
  dsimp only [dotProduct]
  ring

private lemma avoid_prob {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ) (E : Finset (Fin n)) :
    (Uᴴ * diagonal (fun l => if l ∉ E then (1 : ℂ) else 0) * U).det =
      ∑ S : {S : Finset (Fin n) // S.card = k}, if Disjoint S.1 E then (prob U S : ℂ) else 0 := by
  classical
  rw [weighted_cauchy]
  apply Finset.sum_congr rfl
  intro S _
  rw [prod_rows S (fun l => if l ∉ E then (1 : ℂ) else 0), Finset.prod_boole]
  have he : (∀ i ∈ S.1, i ∉ E) ↔ Disjoint S.1 E := Finset.disjoint_left.symm
  simp only [he]
  split_ifs <;> simp

private lemma avoid_one {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (i : Fin n) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∉ S.1 then (prob U S : ℂ) else 0) = 1 - ((star (U i)) ⬝ᵥ (U i)) := by
  classical
  have hm : (fun l => if l ∉ ({i} : Finset (Fin n)) then (1 : ℂ) else 0) =
      (fun l => 1 + (if l = i then (-1 : ℂ) else 0) + (if l = i then (0 : ℂ) else 0)) := by
    funext l
    by_cases hl : l = i <;> simp [hl]
  have h := avoid_prob U {i}
  rw [hm, rank_two_det U hU] at h
  simpa [sub_eq_add_neg] using h.symm

private lemma avoid_two {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (i j : Fin n) (hij : i ≠ j) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∉ S.1 ∧ j ∉ S.1 then (prob U S : ℂ) else 0) =
      1 - ((star (U i)) ⬝ᵥ (U i)) - ((star (U j)) ⬝ᵥ (U j)) + ((star (U i)) ⬝ᵥ (U i)) * ((star (U j)) ⬝ᵥ (U j)) - ((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i)) := by
  classical
  have hm : (fun l => if l ∉ ({i,j} : Finset (Fin n)) then (1 : ℂ) else 0) =
      (fun l => 1 + (if l = i then (-1 : ℂ) else 0) + (if l = j then (-1 : ℂ) else 0)) := by
    funext l
    by_cases hi : l = i
    · subst l; simp [hij]
    · by_cases hj : l = j
      · subst l; simp [Ne.symm hij]
      · simp [hi,hj]
  have h := avoid_prob U {i,j}
  rw [hm, rank_two_det U hU] at h
  simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] at h
  rw [← h]
  ring

private lemma pair_prob {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (i j : Fin n) (hij : i ≠ j) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∈ S.1 ∧ j ∈ S.1 then (prob U S : ℂ) else 0) =
      ((star (U i)) ⬝ᵥ (U i)) * ((star (U j)) ⬝ᵥ (U j)) - ((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i)) := by
  classical
  have hp : (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ)) = 1 := by
    exact_mod_cast total_prob U hU
  have hi := avoid_one U hU i
  have hj := avoid_one U hU j
  have hab := avoid_two U hU i j hij
  have hinc : (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∈ S.1 ∧ j ∈ S.1 then (prob U S : ℂ) else 0) =
      (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ)) -
      (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∉ S.1 then (prob U S : ℂ) else 0) -
      (∑ S : {S : Finset (Fin n) // S.card = k}, if j ∉ S.1 then (prob U S : ℂ) else 0) +
      (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∉ S.1 ∧ j ∉ S.1 then (prob U S : ℂ) else 0) := by
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hi : i ∈ S.1 <;> by_cases hj : j ∈ S.1 <;> simp [hi,hj]
  rw [hinc, hp, hi, hj, hab]
  ring
end D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV

namespace D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMVResidual
open D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap


private def offSum {k : ℕ} (f : Fin k → Fin k → ℂ) : ℂ :=
  ∑ r, ∑ s, if r = s then 0 else f r s

private lemma off_eq_sub {k : ℕ} (f : Fin k → Fin k → ℂ) :
    offSum f = (∑ r, ∑ s, f r s) - ∑ r, f r r := by
  classical
  have hp (r s : Fin k) : (if r = s then 0 else f r s) =
      f r s - (if r = s then f r r else 0) := by
    split_ifs with h
    · subst s; simp
    · simp
  simp only [offSum, hp, Finset.sum_sub_distrib]
  simp

private lemma trace_combo {n d : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin n → ℂ) :
    ((∑ i, a i • σ i) * (∑ j, b j • σ j)).trace =
      ∑ i, ∑ j, (a i * b j) * (σ i * σ j).trace := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]
  ring

private lemma cross_star {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).IsHermitian) (U : Matrix (Fin n) (Fin k) ℂ) (r s : Fin k) :
    ((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s)))ᴴ = ∑ i, (U i r * star (U i s)) • σ i := by
  simp only [Fintype.linearCombination_apply, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_mul, star_star, (hσ _).eq, mul_comm]

private lemma cross_total {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).IsHermitian) (U : Matrix (Fin n) (Fin k) ℂ) :
    (∑ r, ∑ s, (((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s)))ᴴ * (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s))).trace) =
      ∑ i, ∑ j, (((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i))) * (σ i * σ j).trace := by
  simp_rw [cross_star σ hσ, Fintype.linearCombination_apply, trace_combo]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset (Fin n)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [dotProduct, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma output_total {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin n) (Fin k) ℂ) :
    (∑ r, ∑ s, (channelOutput σ (fun i => U i r) *
      channelOutput σ (fun i => U i s)).trace) =
      ∑ i, ∑ j, (((star (U i)) ⬝ᵥ (U i)) * ((star (U j)) ⬝ᵥ (U j))) * (σ i * σ j).trace := by
  simp_rw [channelOutput, trace_combo]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset (Fin n)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [dotProduct, Pi.star_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma cross_diag {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin n) (Fin k) ℂ) (r : Fin k) :
    (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i r)) = channelOutput σ (fun i => U i r) := by
  simp only [Fintype.linearCombination_apply, channelOutput, Complex.normSq_eq_conj_mul_self, Complex.star_def]

private lemma residual_identity {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).IsHermitian) (U : Matrix (Fin n) (Fin k) ℂ) :
    offSum (fun r s => (channelOutput σ (fun i => U i r) *
      channelOutput σ (fun i => U i s)).trace) -
      (∑ i, ∑ j, (((star (U i)) ⬝ᵥ (U i)) * ((star (U j)) ⬝ᵥ (U j)) - ((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i))) * (σ i * σ j).trace) =
      offSum (fun r s => (((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s)))ᴴ * (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s))).trace) := by
  have hd (r : Fin k) : (((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i r)))ᴴ * (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i r))).trace =
      (channelOutput σ (fun i => U i r) * channelOutput σ (fun i => U i r)).trace := by
    rw [cross_star σ hσ]
    have hc : (∑ i, (U i r * star (U i r)) • σ i) = channelOutput σ (fun i => U i r) := by
      simpa only [Fintype.linearCombination_apply, mul_comm] using cross_diag σ U r
    rw [hc, cross_diag]
  rw [off_eq_sub, off_eq_sub, output_total, cross_total σ hσ U]
  simp_rw [hd, sub_mul, Finset.sum_sub_distrib]
  ring

private lemma cross_nonneg {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ (Tᴴ * T).trace.re := by
  exact (Matrix.posSemidef_conjTranspose_mul_self T).trace_nonneg.1
end D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMVResidual


namespace D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV
open D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap

private def score {n k : ℕ} (G : Fin n → Fin n → ℂ) (S : {S : Finset (Fin n) // S.card = k}) : ℂ :=
  ∑ i ∈ S.1, ∑ j ∈ S.1, if i = j then 0 else G i j

private lemma score_as_full {n k : ℕ} (G : Fin n → Fin n → ℂ) (S : {S : Finset (Fin n) // S.card = k}) :
    score G S = ∑ i, ∑ j, if i ∈ S.1 ∧ j ∈ S.1 then (if i = j then 0 else G i j) else 0 := by
  classical
  calc
    score G S = ∑ i : Fin n, if i ∈ S.1 then (∑ j ∈ S.1, if i = j then 0 else G i j) else 0 :=
      (Fintype.sum_ite_mem S.1 _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S.1
      · simp only [hi, ite_true, true_and]
        exact (Fintype.sum_ite_mem S.1 _).symm
      · simp [hi]

private lemma expected_score {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (G : Fin n → Fin n → ℂ) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) * score G S) =
      ∑ i, ∑ j, (((star (U i)) ⬝ᵥ (U i)) * ((star (U j)) ⬝ᵥ (U j)) - ((star (U i)) ⬝ᵥ (U j)) * ((star (U j)) ⬝ᵥ (U i))) * G i j := by
  classical
  simp_rw [score_as_full, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ({S : Finset (Fin n) // S.card = k})))
    (t := (Finset.univ : Finset (Fin n)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp [dotProduct]
  · calc
      (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) *
          (if i ∈ S.1 ∧ j ∈ S.1 then (if i = j then 0 else G i j) else 0)) =
          (∑ S : {S : Finset (Fin n) // S.card = k}, if i ∈ S.1 ∧ j ∈ S.1 then (prob U S : ℂ) else 0) * G i j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S _
        split_ifs <;> simp_all
      _ = _ := by rw [pair_prob U hU i j hij]

private lemma score_as_injection {n k : ℕ} (G : Fin n → Fin n → ℂ) (S : {S : Finset (Fin n) // S.card = k}) :
    score G S = ∑ r : Fin k, ∑ s : Fin k,
      if r = s then 0 else G (S.1.orderEmbOfFin S.2 r) (S.1.orderEmbOfFin S.2 s) := by
  classical
  symm
  calc
    _ = ∑ r : Fin k, ∑ s : Fin k,
        if S.1.orderEmbOfFin S.2 r = S.1.orderEmbOfFin S.2 s then 0
        else G (S.1.orderEmbOfFin S.2 r) (S.1.orderEmbOfFin S.2 s) := by
      simp only [(S.1.orderEmbOfFin S.2).injective.eq_iff]
    _ = ∑ r : Fin k, ∑ j ∈ S.1, if S.1.orderEmbOfFin S.2 r = j then 0
        else G (S.1.orderEmbOfFin S.2 r) j := by
      apply Finset.sum_congr rfl
      intro r _
      exact sum_rows S (fun j => if S.1.orderEmbOfFin S.2 r = j then 0
        else G (S.1.orderEmbOfFin S.2 r) j)
    _ = score G S := sum_rows S (fun i => ∑ j ∈ S.1, if i = j then 0 else G i j)

private lemma min_le_expected {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin n) (Fin k) ℂ) (hU : Uᴴ * U = 1) :
    minDistinctOverlap σ k ≤
      (1 / ((k : ℝ) * ((k : ℝ) - 1))) *
      (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) * score (fun i j => (σ i * σ j).trace) S).re := by
  classical
  let c : ℝ := 1 / ((k : ℝ) * ((k : ℝ) - 1))
  have hmin (S : {S : Finset (Fin n) // S.card = k}) : minDistinctOverlap σ k ≤
      c * (score (fun i j => (σ i * σ j).trace) S).re := by
    let F : {ι : Fin k → Fin n // Function.Injective ι} → ℝ := fun ι =>
      c * ∑ r : Fin k, ∑ s : Fin k, if r = s then 0 else (σ (ι.1 r) * σ (ι.1 s)).trace.re
    let ι : {ι : Fin k → Fin n // Function.Injective ι} :=
      ⟨fun r => S.1.orderEmbOfFin S.2 r, (S.1.orderEmbOfFin S.2).injective⟩
    have hb : BddBelow (Set.range F) := (Set.finite_range F).bddBelow
    have h := ciInf_le hb ι
    change (⨅ ι, F ι) ≤ c * (score (fun i j => (σ i * σ j).trace) S).re
    simpa only [F, ι, score_as_injection, Complex.re_sum, apply_ite, Complex.zero_re] using h

  calc
    minDistinctOverlap σ k = (∑ S : {S : Finset (Fin n) // S.card = k}, prob U S) * minDistinctOverlap σ k := by
      rw [total_prob U hU, one_mul]
    _ = ∑ S : {S : Finset (Fin n) // S.card = k}, prob U S * minDistinctOverlap σ k := Finset.sum_mul _ _ _
    _ ≤ ∑ S : {S : Finset (Fin n) // S.card = k}, prob U S *
        (c * (score (fun i j => (σ i * σ j).trace) S).re) := by
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_mul_of_nonneg_left (hmin S) (Complex.normSq_nonneg _)
    _ = _ := by
      simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

private lemma subset_residual {n d k : ℕ} (σ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hσ : ∀ i, (σ i).IsHermitian) (U : Matrix (Fin n) (Fin k) ℂ) (hU : Uᴴ * U = 1) :
    HMVResidual.offSum (fun r s => (channelOutput σ (fun i => U i r) *
      channelOutput σ (fun i => U i s)).trace) -
      (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) * score (fun i j => (σ i * σ j).trace) S) =
      HMVResidual.offSum (fun r s => (((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s)))ᴴ * (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s))).trace) := by
  rw [expected_score U hU]
  simpa only [dotProduct, Complex.normSq_eq_conj_mul_self, Complex.star_def] using HMVResidual.residual_identity σ hσ U
end D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV

namespace D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap
open HMV
theorem result : claim := by
  classical
  intro n d k σ hσ hk _hkn u hu
  let U : Matrix (Fin n) (Fin k) ℂ := fun i r => u r i
  have hU : Uᴴ * U = 1 := Matrix.ext hu
  have hherm : ∀ i, (σ i).IsHermitian := fun i => (hσ i).1.isHermitian
  have hr := subset_residual σ hherm U hU
  have hpos : 0 ≤ (HMVResidual.offSum (fun r s =>
      (((Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s)))ᴴ * (Fintype.linearCombination ℂ σ (fun i => star (U i r) * U i s))).trace)).re := by
    simp only [HMVResidual.offSum, Complex.re_sum, apply_ite, Complex.zero_re]
    apply Finset.sum_nonneg
    intro r _
    apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact le_rfl
    · exact HMVResidual.cross_nonneg _
  have hle : (∑ S : {S : Finset (Fin n) // S.card = k}, (prob U S : ℂ) *
      score (fun i j => (σ i * σ j).trace) S).re ≤
      (HMVResidual.offSum (fun r s => (channelOutput σ (fun i => U i r) *
        channelOutput σ (fun i => U i s)).trace)).re := by
    have h := congrArg Complex.re hr
    rw [Complex.sub_re] at h
    linarith
  have hkR : (2 : ℝ) ≤ k := Nat.ofNat_le_cast.mpr hk
  have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hc : 0 ≤ (1 / ((k : ℝ) * ((k : ℝ) - 1))) := le_of_lt (one_div_pos.mpr hden)
  apply (min_le_expected σ U hU).trans
  have h := mul_le_mul_of_nonneg_left hle hc
  simpa only [averageOutputOverlap, HMVResidual.offSum, Complex.re_sum, apply_ite,
    Complex.zero_re, U] using h
end D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap
