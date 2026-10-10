/- GID: D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.claim; result=D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result; claim=D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.claim
   digest: Equal minimal Renyi profiles do not imply positive interconversion. -/

/-
proof_shape: weighted_charpoly_eq: bind-only; escape_witness=none
  consumers: weighted_trace_power_eq
proof_shape: trace_cfc_eq_of_charpoly_eq: bind-only; escape_witness=none
  consumers: weighted_trace_power_eq
proof_shape: weighted_trace_power_eq: bind-only; escape_witness=none
  consumers: Dmin_eq_bouquet
proof_shape: Dmin_eq_bouquet: bind-only; escape_witness=none
  consumers: checkpoint_profiles
proof_shape: rho_isDensity: bind-only; escape_witness=none
  consumers: result
proof_shape: sigma_isDensity: bind-only; escape_witness=none
  consumers: result
proof_shape: DminFinite_bouquet: bind-only; escape_witness=none
  consumers: result, checkpoint_profiles
proof_shape: checkpoint_profiles: bind-only; escape_witness=none
  consumers: result
proof_shape: result: content; escape_witness=result
  consumers: none (designated refutation result)
escape_witness: result
admission_basis: open-problem-resolution (#14827; Refuted)
Direct frozen dependencies:
  D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity
  declaration statement_id: sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.scaled_dominance_posDef
  declaration statement_id: sha256:7d9e0a8c810f16ac7b4672a154a2adebe215dd86737857fc62f1861e22deed95
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.QuantumChannels.RenyiSufficiency.BouquetHolonomy
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction

noncomputable section
open D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum
open D5.S3.QuantumChannels.RenyiSufficiency.BouquetHolonomy
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
namespace D5.S3.QuantumChannels.RenyiSufficiency.RenyiSufficiencyRefutation

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section
open Matrix Polynomial
open scoped ComplexOrder MatrixOrder
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem weighted_charpoly_eq (e : ℂ) (d : Fin 5 → ℂ) :
    (weightedRho false e d).charpoly = (weightedRho true e d).charpoly := by
  simp [Matrix.charpoly, Matrix.det_succ_row_zero, Matrix.det_fin_two,
    Matrix.det_fin_one, Matrix.charmatrix_apply, Matrix.submatrix_apply,
    Fin.sum_univ_succ, weightedRho, rho, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Fin.succAbove]
  ring

private theorem trace_cfc_eq_of_charpoly_eq {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) (f : ℝ → ℝ) :
    (hA.cfc f).trace = (hB.cfc f).trace := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h
  have ht (C : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
      (Unitary.conjStarAlgAut ℂ _ U C).trace = C.trace := by
    simp only [Unitary.conjStarAlgAut_apply]
    rw [Matrix.trace_mul_cycle]
    rw [Unitary.star_mul_self_of_mem U.prop, Matrix.one_mul]
  rw [IsHermitian.cfc, IsHermitian.cfc, ht, ht, he]
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
private theorem sigma_trace : sigma.trace = 1 := by
  norm_num [sigma, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

private theorem rho_trace (minus : Bool) (e : ℂ) : (rho minus e).trace = 1 := by
  cases minus <;> norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

private theorem rho_posDef (minus : Bool) : (rho minus (1/1000)).PosDef := by
  have hH : (rho minus (1/1000)).IsHermitian := by simpa using rho_hermitian minus (1/1000)
  apply D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.scaled_dominance_posDef
    hH (fun _ => 1) (by simp)
  intro i
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  cases minus <;> fin_cases i <;>
    norm_num [rho, Fin.sum_univ_succ, Finset.sum_erase_eq_sub, norm_div, norm_mul, Complex.norm_I,
      Complex.norm_ofNat, norm_one]
end
private theorem weighted_trace_power_eq (e : ℝ) (d : Fin 5 → ℝ) (alpha : ℝ) :
    (matrixPower (weightedRho false e (fun i => (d i : ℂ))) alpha).trace =
    (matrixPower (weightedRho true e (fun i => (d i : ℂ))) alpha).trace := by
  rw [matrixPower_eq (weightedRho_hermitian false e d), matrixPower_eq (weightedRho_hermitian true e d)]
  exact trace_cfc_eq_of_charpoly_eq (weightedRho_hermitian false e d)
    (weightedRho_hermitian true e d) (weighted_charpoly_eq _ _) _

private theorem Dmin_eq_bouquet (e : ℝ) (alpha : ℝ) (ha : alpha ≠ 1) :
    Dmin (rho false e) sigma alpha = Dmin (rho true e) sigma alpha := by
  let d : Fin 5 → ℝ := fun i => (((i.val + 1 : ℕ) : ℝ) / 15) ^ ((1-alpha)/(2*alpha))
  have hs : matrixPower sigma ((1-alpha)/(2*alpha)) =
      diagonal (fun i => (d i : ℂ)) :=
    matrixPower_diagonal (fun i : Fin 5 => ((i.val + 1 : ℕ) : ℝ) / 15) ((1-alpha)/(2*alpha))
  have ht := weighted_trace_power_eq e d alpha
  have ht' := congrArg (fun z : ℂ => (alpha-1)⁻¹ * Real.log z.re) ht
  simpa only [Dmin, if_neg ha, hs, weightedRho] using ht'

theorem rho_isDensity (minus : Bool) : IsDensity (rho minus (1/1000)) :=
  ⟨(rho_posDef minus).posSemidef, rho_trace minus _⟩

theorem sigma_isDensity : IsDensity sigma := ⟨sigma_posDef.posSemidef, sigma_trace⟩

theorem DminFinite_bouquet (minus : Bool) (alpha : ℝ) :
    DminFinite (rho minus (1/1000)) sigma alpha := by
  constructor
  · intro _
    have hs : LinearMap.range sigma.toLin' = ⊤ :=
      LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr sigma_posDef.isUnit)
    rw [hs]
    exact le_top
  · intro _
    exact ((rho_posDef minus).isUnit.mul sigma_posDef.isUnit).ne_zero

theorem checkpoint_profiles (alpha : ℝ) (ha : alpha ∈ Set.Ioo (2 : ℝ) 3) :
    Dmin (rho false (1/1000)) sigma alpha = Dmin (rho true (1/1000)) sigma alpha ∧
      DminFinite (rho false (1/1000)) sigma alpha ∧
      DminFinite (rho true (1/1000)) sigma alpha := by
  refine ⟨?_, DminFinite_bouquet false alpha, DminFinite_bouquet true alpha⟩
  have hne : alpha ≠ 1 := by rcases ha with ⟨ha, _⟩; linarith
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    Dmin_eq_bouquet (1/1000) alpha hne

section
open Matrix

def claim : Prop := ∀ (n m : ℕ) (rho1 sigma1 : Matrix (Fin n) (Fin n) ℂ) (rho2 sigma2 : Matrix (Fin m) (Fin m) ℂ),
  IsDensity rho1 → IsDensity sigma1 → IsDensity rho2 → IsDensity sigma2 →
  ∀ a b : ℝ, 1/2 ≤ a → a < b →
  (∀ alpha ∈ Set.Ioo a b, DminFinite rho1 sigma1 alpha ∧ DminFinite rho2 sigma2 alpha) →
  (Interconvertible rho1 sigma1 rho2 sigma2 ↔
    ∀ alpha ∈ Set.Ioo a b, Dmin rho1 sigma1 alpha = Dmin rho2 sigma2 alpha)

theorem result : ¬ claim := by
  intro h
  have hc := h 5 5 (rho false (1/1000)) sigma (rho true (1/1000)) sigma
    (rho_isDensity false) sigma_isDensity (rho_isDensity true) sigma_isDensity
    2 3 (by norm_num) (by norm_num)
    (fun alpha _ => ⟨DminFinite_bouquet false alpha, DminFinite_bouquet true alpha⟩)
  apply bouquet_not_interconvertible
  exact hc.mpr (fun alpha ha => (checkpoint_profiles alpha ha).1)
end


end D5.S3.QuantumChannels.RenyiSufficiency.RenyiSufficiencyRefutation
