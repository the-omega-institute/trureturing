/- GID: D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/FlatPairEndpointHomomorphisms
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Flat-pair endpoint and negative tropical homomorphisms fail monotonicity. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19032; Proved)
Private auxiliary statements (escape_witness: none):
  t_pos: proof_shape: bind-only; consumer: phi_x, y_inner_ne, phiT_x, x_eo.
  s_pos: proof_shape: bind-only; consumer: y_inner_ne.
  t_sq: proof_shape: bind-only; consumer: tC_sq, y_data, x_data.
  s_sq: proof_shape: bind-only; consumer: sC_sq, y_data.
  x_inner: proof_shape: bind-only; consumer: phi_x, phiT_x, x_eo, x_data.
  y_inner: proof_shape: bind-only; consumer: y_inner_ne, y_data.
  erasure_inner: proof_shape: bind-only; consumer: phi_erasure, erasure_eo.
  x_eo: proof_shape: bind-only; consumer: endpoint_zero, result.
  y_inner_ne: proof_shape: bind-only; consumer: y_eo, phiT_y, phi_y.
  y_eo: proof_shape: bind-only; consumer: endpoint_zero, result.
  erasure_eo: proof_shape: bind-only; consumer: endpoint_zero.
  x_data: proof_shape: bind-only; consumer: phi_x, phiT_x.
  y_data: proof_shape: bind-only; consumer: phiT_y, phi_y.
  erasure_data: proof_shape: bind-only; consumer: phi_erasure.
  jensen_pos: proof_shape: bind-only; consumer: endpoint_zero.
  jensen_neg: proof_shape: bind-only; consumer: endpoint_zero.
  tC_sq: proof_shape: bind-only; consumer: erase_B.
  sC_sq: proof_shape: bind-only; consumer: flag_complete.
  flag_complete: proof_shape: bind-only; consumer: x_majorizes_y.
  erase_complete: proof_shape: bind-only; consumer: x_majorizes_erasure.
  flag_A: proof_shape: bind-only; consumer: x_majorizes_y.
  flag_B: proof_shape: bind-only; consumer: x_majorizes_y.
  erase_A: proof_shape: bind-only; consumer: x_majorizes_erasure.
  erase_B: proof_shape: bind-only; consumer: x_majorizes_erasure.
  majorizes_kraus: proof_shape: bind-only; consumer: x_majorizes_erasure, x_majorizes_y.
  x_majorizes_y: proof_shape: bind-only; consumer: endpoint_zero, result.
  x_majorizes_erasure: proof_shape: bind-only; consumer: endpoint_zero.
  phi_x: proof_shape: bind-only; consumer: endpoint_zero.
  phi_y: proof_shape: bind-only; consumer: endpoint_zero.
  phi_erasure: proof_shape: bind-only; consumer: endpoint_zero.
  phiT_x: proof_shape: bind-only; consumer: result.
  phiT_y: proof_shape: bind-only; consumer: result.
  swap_inner: proof_shape: bind-only; consumer: swap_eo, swap_overlap, phi_swap.
  swap_eo: proof_shape: bind-only; consumer: result.
  swap_majorizes: proof_shape: bind-only; consumer: result.
  swap_overlap: proof_shape: bind-only; consumer: phi_swap.
  phi_swap: proof_shape: bind-only; consumer: result.
  endpoint_zero: proof_shape: bind-only; consumer: result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19845.
Direct frozen dependencies:
  D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel
    statement_id: sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
    statement_id: sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
  D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    statement_id: sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0
  D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq
    statement_id: sha256:83f2f9c9f892ddcca215026b9ed3047d813401aeb0ba3b2ed6ec964dff2d3cd4
The index carriers use sigma types directly, with coordinate projections.
The claim keeps the source's finite-block expressions and parameter ranges.
The scalar and matrix identities support inequalities for arbitrary real z;
no finite decision procedure proves or refutes the proposition claim.
-/

import D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteStateChannel

/-! Binding conventions for F. Verhagen, M. Tomamichel and E. Haapasalo, "Conditions for Large-Sample Majorization of
Pairs of Flat States in Terms of α-z Relative Entropies", arXiv:2507.07520v3, Section 4.1, Eqs. (30)–(35), (37),
Section 4.3, Eqs. (84)–(85) and Remark 15. -/

noncomputable section
namespace D5.S3.QuantumChannels.FlatPairEndpointHomomorphisms

open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open Matrix
open scoped ComplexOrder

/-- Eqs. (30)–(31): a pair `A = ⊕ᵢ |αᵢ⟩⟨αᵢ|`, `B = ⊕ᵢ |βᵢ⟩⟨βᵢ|` on `H = ⊕ᵢ Hᵢ`, `Hᵢ = ℂ^{dᵢ}`; the vectors may be zero. -/
structure FlatPair where
  n : ℕ
  d : Fin n → ℕ
  α : (i : Fin n) → Fin (d i) → ℂ
  β : (i : Fin n) → Fin (d i) → ℂ

namespace FlatPair

/-- `A = ⊕ᵢ |αᵢ⟩⟨αᵢ|`. -/
def A (x : FlatPair) : Matrix (Σ i : Fin x.n, Fin (x.d i)) (Σ i : Fin x.n, Fin (x.d i)) ℂ := blockDiagonal' fun i => vecMulVec (x.α i) (star (x.α i))

/-- `B = ⊕ᵢ |βᵢ⟩⟨βᵢ|`. -/
def B (x : FlatPair) : Matrix (Σ i : Fin x.n, Fin (x.d i)) (Σ i : Fin x.n, Fin (x.d i)) ℂ := blockDiagonal' fun i => vecMulVec (x.β i) (star (x.β i))

/-- Eqs. (32)–(34): everywhere overlapping, `⟨αᵢ, βᵢ⟩ ≠ 0` or `αᵢ = 0 = βᵢ` for every block. -/
def IsEverywhereOverlapping (x : FlatPair) : Prop :=
  ∀ i, star (x.α i) ⬝ᵥ x.β i ≠ 0 ∨ (x.α i = 0 ∧ x.β i = 0)

/-- Eq. (37): the weights `pᵢ = ‖αᵢ‖²`, `qᵢ = ‖βᵢ‖²`. -/
def p (x : FlatPair) (i : Fin x.n) : ℝ := (star (x.α i) ⬝ᵥ x.α i).re
def q (x : FlatPair) (i : Fin x.n) : ℝ := (star (x.β i) ⬝ᵥ x.β i).re

/-- The squared overlap of the normalized block vectors, `|⟨α̂ᵢ, β̂ᵢ⟩|² = |⟨αᵢ, βᵢ⟩|² / (pᵢ qᵢ)`. -/
def overlapSq (x : FlatPair) (i : Fin x.n) : ℝ := Complex.normSq (star (x.α i) ⬝ᵥ x.β i) / (x.p i * x.q i)

end FlatPair

/-- `(A, B) ≽ (C, D)`: one quantum channel sends `A` to `C` and `B` to `D` (Section 4.1). -/
def Majorizes (x y : FlatPair) : Prop :=
  ∃ C : QuantumChannel (Σ i : Fin x.n, Fin (x.d i)) (Σ i : Fin y.n, Fin (y.d i)),
    C.toCompletelyPositiveMap (CStarMatrix.ofMatrix x.A) = CStarMatrix.ofMatrix y.A ∧
    C.toCompletelyPositiveMap (CStarMatrix.ofMatrix x.B) = CStarMatrix.ofMatrix y.B

/-- Eq. (84) form: `Φ_{α,z}(A, B) = Σᵢ pᵢ^α qᵢ^{1−α} |⟨α̂ᵢ, β̂ᵢ⟩|^{2z}`, the sum over the nonzero blocks. -/
def Phi (a z : ℝ) (x : FlatPair) : ℝ :=
  ∑ i, if star (x.α i) ⬝ᵥ x.β i = 0 then 0 else
    x.p i ^ a * x.q i ^ (1 - a) * x.overlapSq i ^ z

/-- Eq. (85) form: `Φ^𝕋_z(A, B) = maxᵢ |⟨α̂ᵢ, β̂ᵢ⟩|^{2z}`, the maximum over the nonzero blocks (`0` for the zero pair). -/
def PhiT (z : ℝ) (x : FlatPair) : ℝ :=
  Finset.univ.fold max 0 fun i => if star (x.α i) ⬝ᵥ x.β i = 0 then 0 else x.overlapSq i ^ z

/-- Monotone into `ℝ₊` (and into `𝕋ℝ₊`, which carries the same order): `y ≼ x ⇒ Φ(y) ≤ Φ(x)` on `S_e.o.`. -/
def IsMonotone (Φ : FlatPair → ℝ) : Prop :=
  ∀ x y : FlatPair, x.IsEverywhereOverlapping → y.IsEverywhereOverlapping → Majorizes x y → Φ y ≤ Φ x

/-- Monotone into `ℝ₊^op`: `y ≼ x ⇒ Φ(x) ≤ Φ(y)` on `S_e.o.`. -/
def IsMonotoneOp (Φ : FlatPair → ℝ) : Prop :=
  ∀ x y : FlatPair, x.IsEverywhereOverlapping → y.IsEverywhereOverlapping → Majorizes x y → Φ x ≤ Φ y

/-- Remark 15: "We suspect that these additional homomorphisms are in fact not monotone either": the maps of the
form (84) with `α = 0` or `α = 1` and `z < 1` (`z ≠ 0`, where they are the degenerate maps `tr B`, `tr A`) are
monotone neither into `ℝ₊` nor into `ℝ₊^op`, and the maps of the form (85) with `z < 0` are not monotone into `𝕋ℝ₊`. -/
def claim : Prop :=
  (∀ a : ℝ, (a = 0 ∨ a = 1) → ∀ z : ℝ, z < 1 → z ≠ 0 →
      ¬ IsMonotone (Phi a z) ∧ ¬ IsMonotoneOp (Phi a z)) ∧
    ∀ z : ℝ, z < 0 → ¬ IsMonotone (PhiT z)

end D5.S3.QuantumChannels.FlatPairEndpointHomomorphisms

namespace D5.S3.QuantumChannels.FlatPairEndpointHomomorphisms
open Matrix
open scoped ComplexOrder
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

private def t : ℝ := Real.sqrt 2 / 2
private def s : ℝ := Real.sqrt 3 / 2

private abbrev x : FlatPair := ⟨1, fun _ => 2, fun _ => ![1, 0], fun _ => ![(t : ℂ), (t : ℂ)]⟩
private abbrev y : FlatPair := ⟨2, fun _ => 2,
  fun i => if i = 0 then ![1/2, 0] else ![(s : ℂ), 0],
  fun i => if i = 0 then ![(t : ℂ)/2, (t : ℂ)*(s : ℂ)]
    else ![(t : ℂ)*(s : ℂ), (t : ℂ)/2]⟩
private abbrev erasure : FlatPair := ⟨1, fun _ => 1, fun _ _ => 1, fun _ _ => 1⟩

private lemma t_pos : 0 < t := by dsimp [t]; positivity
private lemma s_pos : 0 < s := by dsimp [s]; positivity
private lemma t_sq : t ^ 2 = 1/2 := by
  simpa only [t, pow_two] using
    D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq
private lemma s_sq : s ^ 2 = 3/4 := by dsimp [s]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 from zero_le_three)]


private lemma x_inner (i : Fin x.n) : star (x.α i) ⬝ᵥ x.β i = (t : ℂ) := by
  fin_cases i
  simp [x, dotProduct, Fin.sum_univ_two]
private lemma y_inner (i : Fin y.n) : star (y.α i) ⬝ᵥ y.β i = if i = 0 then (t : ℂ)/4 else (s : ℂ)*(t : ℂ)*(s : ℂ) := by
  fin_cases i <;> dsimp [y, dotProduct] <;> norm_num [Fin.sum_univ_two, map_ofNat, map_inv₀] <;> ring
private lemma erasure_inner (i : Fin erasure.n) : star (erasure.α i) ⬝ᵥ erasure.β i = 1 := by
  fin_cases i
  simp [erasure, dotProduct]
private lemma x_eo : x.IsEverywhereOverlapping := by
  intro i
  left
  rw [x_inner]
  exact_mod_cast t_pos.ne'
private lemma y_inner_ne (i : Fin y.n) : star (y.α i) ⬝ᵥ y.β i ≠ 0 := by
  rw [y_inner]
  split_ifs
  · exact div_ne_zero (by exact_mod_cast t_pos.ne') (by norm_num)
  · exact mul_ne_zero (mul_ne_zero (by exact_mod_cast s_pos.ne') (by exact_mod_cast t_pos.ne')) (by exact_mod_cast s_pos.ne')

private lemma y_eo : y.IsEverywhereOverlapping := by
  intro i
  exact Or.inl (y_inner_ne i)
private lemma erasure_eo : erasure.IsEverywhereOverlapping := by
  intro i
  exact Or.inl (by rw [erasure_inner]; norm_num)
private lemma x_data (i : Fin x.n) : x.p i = 1 ∧ x.q i = 1 ∧ x.overlapSq i = 1/2 := by
  have hp : x.p i = 1 := by
    dsimp [FlatPair.p, x, dotProduct]
    norm_num [Fin.sum_univ_two]
  have hq : x.q i = 1 := by
    dsimp [FlatPair.q, x, dotProduct]
    norm_num [Fin.sum_univ_two]
    nlinarith [t_sq]
  refine ⟨hp, hq, ?_⟩
  unfold FlatPair.overlapSq
  rw [hp, hq, x_inner]
  norm_num [Complex.normSq]
  nlinarith [t_sq]
private lemma y_data (i : Fin y.n) :
    y.p i = (if i = 0 then 1/4 else 3/4) ∧ y.q i = 1/2 ∧
    y.overlapSq i = (if i = 0 then 1/4 else 3/4) := by
  have hp : y.p i = (if i = 0 then 1/4 else 3/4) := by
    fin_cases i <;> dsimp [FlatPair.p, y, dotProduct] <;> norm_num [Fin.sum_univ_two] <;> nlinarith [s_sq]
  have hs4 : s^4 = (3/4:ℝ)^2 := calc
    s^4 = (s^2)^2 := pow_mul s 2 2
    _ = (3/4:ℝ)^2 := congrArg (fun r : ℝ => r^2) s_sq
  have hq : y.q i = 1/2 := by
    fin_cases i <;> dsimp [FlatPair.q, y, dotProduct] <;> norm_num [Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [t_sq, s_sq, hs4] <;> nlinarith [t_sq]
  refine ⟨hp, hq, ?_⟩
  unfold FlatPair.overlapSq
  rw [hp, hq, y_inner]
  fin_cases i <;> norm_num [Complex.normSq] <;> ring_nf <;> norm_num [t_sq, s_sq, hs4] <;> nlinarith [t_sq]
private lemma erasure_data (i : Fin erasure.n) : erasure.p i = 1 ∧ erasure.q i = 1 ∧ erasure.overlapSq i = 1 := by
  norm_num [FlatPair.p, FlatPair.q, FlatPair.overlapSq, erasure, dotProduct, Complex.normSq]

private lemma jensen_pos (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    ((1/4:ℝ)^z+(3/4:ℝ)^z)/2 < (1/2:ℝ)^z := by
  have h := (Real.strictConcaveOn_rpow hz hz1).2
    (show (1/4:ℝ) ∈ Set.Ici 0 by norm_num) (show (3/4:ℝ) ∈ Set.Ici 0 by norm_num)
    (show (1/4:ℝ) ≠ 3/4 by norm_num)
    (show (0:ℝ)<1/2 from one_half_pos) (show (0:ℝ)<1/2 from one_half_pos)
    (show (1/2:ℝ)+1/2=1 from add_halves 1)
  norm_num [smul_eq_mul] at h
  linarith

private lemma jensen_neg (z : ℝ) (hz : z < 0) :
    (1/2:ℝ)^z < ((1/4:ℝ)^z+(3/4:ℝ)^z)/2 := by
  have hc : StrictConvexOn ℝ (Set.Ioi 0) (fun u : ℝ => u^z) := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    · intro u hu
      exact (Real.continuousAt_rpow_const u z (Or.inl (ne_of_gt hu))).continuousWithinAt
    intro u hu v hv huv
    simp only [interior_Ioi, Set.mem_Ioi] at hu hv
    rw [Real.deriv_rpow_const, Real.deriv_rpow_const]
    exact mul_lt_mul_of_neg_left
      (Real.rpow_lt_rpow_of_neg hu huv (sub_neg.mpr (lt_trans hz zero_lt_one))) hz
  have h := hc.2
    (show (1/4:ℝ) ∈ Set.Ioi 0 by norm_num) (show (3/4:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (1/4:ℝ) ≠ 3/4 by norm_num)
    (show (0:ℝ)<1/2 from one_half_pos) (show (0:ℝ)<1/2 from one_half_pos)
    (show (1/2:ℝ)+1/2=1 from add_halves 1)
  norm_num [smul_eq_mul] at h
  linarith
private lemma tC_sq : (t : ℂ)^2 = 1/2 := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) t_sq
  push_cast at h
  exact h
private lemma sC_sq : (s : ℂ)^2 = 3/4 := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) s_sq
  push_cast at h
  exact h

private def flagK (k : Fin 2) : Matrix (Σ i : Fin y.n, Fin (y.d i)) (Σ i : Fin x.n, Fin (x.d i)) ℂ := fun i j =>
  if i.1 = k ∧ i.2 = j.2 then
    if k = 0 then (if j.2 = 0 then 1/2 else (s:ℂ))
    else (if j.2 = 0 then (s:ℂ) else 1/2)
  else 0

private def eraseK (k : Fin 2) : Matrix (Σ i : Fin erasure.n, Fin (erasure.d i)) (Σ i : Fin x.n, Fin (x.d i)) ℂ := fun _ j =>
  if j.2 = k then 1 else 0

private lemma flag_complete : (∑ k : Fin 2, (flagK k)ᴴ * flagK k) = 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i; fin_cases k
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    dsimp only [flagK, x, y] <;>
    norm_num [Fintype.sum_sigma, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_inv₀] <;>
    linear_combination sC_sq

private lemma erase_complete : (∑ k : Fin 2, (eraseK k)ᴴ * eraseK k) = 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i; fin_cases k
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    dsimp only [eraseK, x, erasure] <;>
    norm_num [Fintype.sum_sigma, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_inv₀]

private lemma flag_A : (∑ k : Fin 2, flagK k * x.A * (flagK k)ᴴ) = y.A := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, FlatPair.A,
      Matrix.blockDiagonal'_apply, Matrix.vecMulVec_apply] <;>
    dsimp only [flagK, x, y] <;>
    norm_num [Fintype.sum_sigma, Fin.sum_univ_two, map_ofNat, map_inv₀] <;>
    ring

private lemma flag_B : (∑ k : Fin 2, flagK k * x.B * (flagK k)ᴴ) = y.B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, FlatPair.B,
      Matrix.blockDiagonal'_apply, Matrix.vecMulVec_apply] <;>
    dsimp only [flagK, x, y] <;>
    norm_num [Fintype.sum_sigma, Fin.sum_univ_two, map_ofNat, map_inv₀] <;>
    ring

private lemma erase_A : (∑ k : Fin 2, eraseK k * x.A * (eraseK k)ᴴ) = erasure.A := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i; fin_cases k; fin_cases j; fin_cases l
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, FlatPair.A,
    Matrix.blockDiagonal'_apply, Matrix.vecMulVec_apply]
  dsimp only [eraseK, x, erasure]
  norm_num [Fintype.sum_sigma, Fin.sum_univ_two, map_ofNat, map_inv₀]

private lemma erase_B : (∑ k : Fin 2, eraseK k * x.B * (eraseK k)ᴴ) = erasure.B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i; fin_cases k; fin_cases j; fin_cases l
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, FlatPair.B,
    Matrix.blockDiagonal'_apply, Matrix.vecMulVec_apply]
  dsimp only [eraseK, x, erasure]
  norm_num [Fintype.sum_sigma, Fin.sum_univ_two, map_ofNat, map_inv₀]
  linear_combination 2 * tC_sq

private lemma majorizes_kraus {u v : FlatPair} {κ : Type} [Fintype κ]
    (K : κ → Matrix (Σ i : Fin v.n, Fin (v.d i)) (Σ i : Fin u.n, Fin (u.d i)) ℂ) (hK : ∑ k, (K k)ᴴ*K k = 1)
    (hA : ∑ k, K k*u.A*(K k)ᴴ=v.A) (hB : ∑ k, K k*u.B*(K k)ᴴ=v.B) :
    Majorizes u v := by
  obtain ⟨C,hC⟩ := D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  refine ⟨C, ?_, ?_⟩
  · apply CStarMatrix.ofMatrix.symm.injective
    exact (hC u.A).trans hA
  · apply CStarMatrix.ofMatrix.symm.injective
    exact (hC u.B).trans hB
private lemma x_majorizes_y : Majorizes x y := majorizes_kraus flagK flag_complete flag_A flag_B
private lemma x_majorizes_erasure : Majorizes x erasure := majorizes_kraus eraseK erase_complete erase_A erase_B

private lemma phi_x (a z : ℝ) : Phi a z x = (1/2:ℝ)^z := by
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast t_pos.ne'
  unfold Phi
  rw [Fin.sum_univ_one, x_inner]
  simp only [hn, ↓reduceIte, (x_data _).1, (x_data _).2.1,
    (x_data _).2.2, Real.one_rpow, one_mul]
private lemma phi_y (z : ℝ) : Phi 0 z y = ((1/4:ℝ)^z+(3/4:ℝ)^z)/2 := by
  unfold Phi
  rw [Fin.sum_univ_two, if_neg (y_inner_ne 0), if_neg (y_inner_ne 1)]
  rw [(y_data 0).2.1, (y_data 0).2.2, (y_data 1).2.1, (y_data 1).2.2]
  norm_num
  ring
private lemma phi_erasure (a z : ℝ) : Phi a z erasure = 1 := by
  unfold Phi
  rw [Fin.sum_univ_one, erasure_inner]
  simp only [one_ne_zero, ↓reduceIte, (erasure_data _).1,
    (erasure_data _).2.1, (erasure_data _).2.2, Real.one_rpow, one_mul]

private lemma phiT_x (z : ℝ) : PhiT z x = (1/2:ℝ)^z := by
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast t_pos.ne'
  have hu : (Finset.univ : Finset (Fin x.n)) = {0} := Finset.univ_unique
  rw [PhiT, hu, Finset.fold_singleton, x_inner, if_neg hn, (x_data _).2.2]
  exact max_eq_left (Real.rpow_nonneg (by norm_num) _)
private lemma phiT_y (z : ℝ) (hz : z < 0) : PhiT z y = (1/4:ℝ)^z := by
  have hu : (Finset.univ : Finset (Fin y.n)) = {0,1} := Finset.univ_fin2
  rw [PhiT, hu, Finset.fold_insert (by simp), Finset.fold_singleton,
    if_neg (y_inner_ne 0), if_neg (y_inner_ne 1), (y_data 0).2.2, (y_data 1).2.2]
  norm_num only [Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, one_ne_zero]
  rw [max_eq_left (Real.rpow_nonneg (by norm_num) _)]
  exact max_eq_left (Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) hz.le)

private abbrev swap (u : FlatPair) : FlatPair := {u with α := u.β, β := u.α}
private lemma swap_inner (u : FlatPair) (i : Fin u.n) :
    star ((swap u).α i) ⬝ᵥ (swap u).β i = star (star (u.α i) ⬝ᵥ u.β i) := by
  exact star_dotProduct ((swap u).α i) ((swap u).β i)
private lemma swap_eo {u : FlatPair} (hu : u.IsEverywhereOverlapping) :
    (swap u).IsEverywhereOverlapping := by
  intro i
  rcases hu i with h | ⟨ha,hb⟩
  · left
    rw [swap_inner u i]
    exact star_ne_zero.mpr h
  · exact Or.inr ⟨hb,ha⟩
private lemma swap_majorizes {u v : FlatPair} (h : Majorizes u v) : Majorizes (swap u) (swap v) := by
  rcases h with ⟨C,ha,hb⟩
  exact ⟨C,hb,ha⟩
private lemma swap_overlap (u : FlatPair) (i : Fin u.n) : (swap u).overlapSq i = u.overlapSq i := by
  unfold FlatPair.overlapSq
  rw [swap_inner u i]
  simp [swap, FlatPair.p, FlatPair.q, mul_comm]
private lemma phi_swap (u : FlatPair) (z : ℝ) : Phi 1 z (swap u) = Phi 0 z u := by
  unfold Phi
  apply Finset.sum_congr rfl
  intro i hi
  rw [swap_inner u i, swap_overlap u i]
  simp [swap, FlatPair.p, FlatPair.q]


private lemma endpoint_zero (z : ℝ) (hz1 : z < 1) (hz0 : z ≠ 0) :
    ¬ IsMonotone (Phi 0 z) ∧ ¬ IsMonotoneOp (Phi 0 z) := by
  rcases lt_or_gt_of_ne hz0 with hz | hz
  · constructor
    · intro h
      have hh := h x y x_eo y_eo x_majorizes_y
      rw [phi_y, phi_x] at hh
      exact (not_le_of_gt (jensen_neg z hz)) hh
    · intro h
      have hh := h x erasure x_eo erasure_eo x_majorizes_erasure
      rw [phi_x, phi_erasure] at hh
      exact (not_le_of_gt (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hz)) hh
  · constructor
    · intro h
      have hh := h x erasure x_eo erasure_eo x_majorizes_erasure
      rw [phi_x, phi_erasure] at hh
      exact (not_le_of_gt (Real.rpow_lt_one (by norm_num) (by norm_num) hz)) hh
    · intro h
      have hh := h x y x_eo y_eo x_majorizes_y
      rw [phi_y, phi_x] at hh
      exact (not_le_of_gt (jensen_pos z hz hz1)) hh

theorem result : claim := by
  constructor
  · intro a ha z hz1 hz0
    rcases ha with rfl | rfl
    · exact endpoint_zero z hz1 hz0
    · constructor
      · intro h
        apply (endpoint_zero z hz1 hz0).1
        intro u v hu hv huv
        have hh := h (swap u) (swap v) (swap_eo hu) (swap_eo hv) (swap_majorizes huv)
        simpa only [phi_swap] using hh
      · intro h
        apply (endpoint_zero z hz1 hz0).2
        intro u v hu hv huv
        have hh := h (swap u) (swap v) (swap_eo hu) (swap_eo hv) (swap_majorizes huv)
        simpa only [phi_swap] using hh
  · intro z hz h
    have hh := h x y x_eo y_eo x_majorizes_y
    rw [phiT_y z hz, phiT_x] at hh
    exact (not_le_of_gt (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) hz)) hh

end D5.S3.QuantumChannels.FlatPairEndpointHomomorphisms
