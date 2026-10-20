/- GID: D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.claim; result=D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.result; claim=D5/S3/Quantum/Entanglement/PartialNegativity/GuoHatSubadditivityRefutation.claim
   digest: Two maximally entangled components refute partial-negativity subadditivity. -/

/-
proof_shape: hHat, claim: bind-only definitions; consumers: claim, result.
proof_shape: v, rho: bind-only witness definitions; consumers: rho and the state identities.
proof_shape: rho_pos: bind-only; consumers: rho_density, rho_eigenvalue, rho_top_two, rho_hHat.
proof_shape: v_dot: bind-only; consumers: rho_trace, rho_squared.
proof_shape: rho_trace: bind-only; consumers: rho_density, rho_top_two.
proof_shape: rho_squared: bind-only; consumer: rho_eigenvalue.
proof_shape: rho_density, rho_right, rho_left: bind-only; consumer: result.
proof_shape: rho_eigenvalue: bind-only; consumer: rho_top_two.
proof_shape: rho_top_two: bind-only; consumer: rho_hHat.
proof_shape: rho_hHat: bind-only; consumer: result.
proof_shape: uniform_eigenvalues: bind-only; consumer: marginal_hHat.
proof_shape: marginal_hHat: bind-only; consumer: result.
proof_shape: result: bind-only; the settling result for the external conjecture.
escape_witness: none.
admission_basis: open-problem-resolution (#19494; Refuted).
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity
    statement_id: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
  D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst
    statement_id: sha256:60de08083a292a636d655dff7f5b06843146c051021ffe2d0b604db457edc565
  D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex (Lean namespace RHLinalg)
    statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
The partial traces and density predicate use their existing owners. Matrix.traceRight
and its Hermitian theorem belong to the closed, unfrozen FiniteDensityPurification;
no pinned Mathlib partial trace provides the literal expression required by #19494.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19585.
-/

import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound

/-! Binding conventions for Y. Guo, "Complete Genuine Multipartite Entanglement Monotone", arXiv:2301.00334v3
(Results Phys. 57 (2024) 107430): the reduced function `ĥ(ρ) = √(δ₁ δ₂)` of the partial negativity, with `δ₁, δ₂` the
two largest eigenvalues of `ρ`, the reduced states `ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB`, and the conjectured
subadditivity (24) `ĥ(ρ_AB) ≤ ĥ(ρ_A) + ĥ(ρ_B)` for every bipartite state `ρ_AB`. -/

namespace D5.S3.Quantum.Entanglement.PartialNegativity.GuoHatSubadditivityRefutation

open Matrix
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence (partialTraceFirst)

/-- `δ₁(X), δ₂(X)`: the two largest eigenvalues of a Hermitian matrix, counted with multiplicity (`0` for `δ₂` on a
one-dimensional space), and `ĥ(X) = √(δ₁ δ₂)`. -/
noncomputable def hHat {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) : ℝ :=
  if h : 2 ≤ Fintype.card n then
    Real.sqrt (hX.eigenvalues₀ ⟨0, by omega⟩ * hX.eigenvalues₀ ⟨1, by omega⟩)
  else 0

/-- Conjecture (24): `ĥ(ρ_AB) ⩽ ĥ(ρ_A) + ĥ(ρ_B)` holds for any bipartite state `ρ_AB` on `ℂ^{d_A} ⊗ ℂ^{d_B}`, with
`ρ_A = Tr_B ρ_AB` and `ρ_B = Tr_A ρ_AB`. -/
def claim : Prop :=
  ∀ (dA dB : ℕ) (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hρ : IsDensity ρ),
    hHat ρ hρ.1.1 ≤ hHat ρ.traceRight hρ.1.1.traceRight +
      hHat (partialTraceFirst ρ) (by
        apply Matrix.IsHermitian.ext; intro i j
        simp only [partialTraceFirst, star_sum]
        exact Finset.sum_congr rfl fun a _ => hρ.1.1.apply (a, i) (a, j))

end D5.S3.Quantum.Entanglement.PartialNegativity.GuoHatSubadditivityRefutation

noncomputable section
namespace D5.S3.Quantum.Entanglement.PartialNegativity.GuoHatSubadditivityRefutation
open Matrix
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence (partialTraceFirst)
open scoped ComplexOrder
set_option maxHeartbeats 1000000

private def v (r : Fin 5) : (Fin 5 × Fin 5) → ℂ :=
  ({x | x.2 = x.1 + r} : Set (Fin 5 × Fin 5)).indicator (fun _ => 1)

private def rho : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ := (1/10 : ℂ) •
  (vecMulVec (v 0) (star (v 0)) + vecMulVec (v 1) (star (v 1)))

private theorem rho_pos : rho.PosSemidef := by
  exact ((posSemidef_vecMulVec_self_star (v 0)).add
    (posSemidef_vecMulVec_self_star (v 1))).smul (by norm_num [Complex.le_def])

private theorem v_dot : star (v 0) ⬝ᵥ v 0 = 5 ∧ star (v 0) ⬝ᵥ v 1 = 0 ∧
    star (v 1) ⬝ᵥ v 0 = 0 ∧ star (v 1) ⬝ᵥ v 1 = 5 := by
  norm_num [v, Set.indicator, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem rho_trace : rho.trace = 1 := by
  simp only [rho, Matrix.trace_smul, Matrix.trace_add, trace_vecMulVec,
    dotProduct_comm (v 0) (star (v 0)), dotProduct_comm (v 1) (star (v 1)),
    v_dot.1, v_dot.2.2.2, smul_eq_mul]
  norm_num

private theorem rho_squared : rho * rho = (1/2 : ℂ) • rho := by
  have h00 := v_dot.1
  have h01 := v_dot.2.1
  have h10 := v_dot.2.2.1
  have h11 := v_dot.2.2.2
  simp only [rho, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    vecMulVec_mul_vecMulVec, h00, h01, h10, h11,
    vecMulVec_smul, zero_smul, smul_add, smul_smul]
  norm_num

private theorem rho_density : IsDensity rho := by
  exact ⟨rho_pos, rho_trace⟩

private theorem rho_right : rho.traceRight = (1/5 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.traceRight, rho, v, Set.indicator, Matrix.vecMulVec, Matrix.one_apply, Fin.sum_univ_succ]

private theorem rho_left : partialTraceFirst rho = (1/5 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceFirst, rho, v, Set.indicator, Matrix.vecMulVec, Matrix.one_apply, Fin.sum_univ_succ]


private theorem rho_eigenvalue (i : Fin 5 × Fin 5) : rho_pos.isHermitian.eigenvalues i = 0 ∨
    rho_pos.isHermitian.eigenvalues i = 1/2 := by
  let H := rho_pos.isHermitian
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ) (star H.eigenvectorUnitary)
  have hd := congrArg e rho_squared
  rw [map_mul, map_smul, H.conjStarAlgAut_star_eigenvectorUnitary] at hd
  have hi := congrArg (fun M : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ => M i i) hd
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Matrix.smul_apply, smul_eq_mul, Function.comp_apply] at hi
  have hr : H.eigenvalues i * H.eigenvalues i = (1/2 : ℝ) * H.eigenvalues i := by
    simpa using congrArg Complex.re hi
  have hz : H.eigenvalues i * (H.eigenvalues i - 1/2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem rho_top_two : rho_pos.isHermitian.eigenvalues₀ ⟨0, by decide⟩ = 1/2 ∧
    rho_pos.isHermitian.eigenvalues₀ ⟨1, by decide⟩ = 1/2 := by
  let H := rho_pos.isHermitian
  let e : Fin (Fintype.card (Fin 5 × Fin 5)) ≃ (Fin 5 × Fin 5) := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hd (i : Fin (Fintype.card (Fin 5 × Fin 5))) : H.eigenvalues₀ i = 0 ∨ H.eigenvalues₀ i = 1/2 := by
    simpa only [Matrix.IsHermitian.eigenvalues, e, H, Equiv.symm_apply_apply] using rho_eigenvalue (e i)
  have hs : ∑ i : Fin 5 × Fin 5, H.eigenvalues i = 1 := by
    have ht := congrArg Complex.re H.trace_eq_sum_eigenvalues
    rw [rho_trace] at ht
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
      Complex.one_re] using ht.symm
  have hs0 : ∑ i : Fin (Fintype.card (Fin 5 × Fin 5)), H.eigenvalues₀ i = 1 := by
    exact (RHLinalg.sum_eigenvalues_reindex H id).symm.trans hs
  have hnonneg (i : Fin (Fintype.card (Fin 5 × Fin 5))) : 0 ≤ H.eigenvalues₀ i := by
    simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      rho_pos.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  have hcap (i : Fin (Fintype.card (Fin 5 × Fin 5))) : H.eigenvalues₀ i ≤ 1/2 := by
    rcases hd i with hi | hi <;> norm_num [hi]
  have hsecond : H.eigenvalues₀ ⟨1, by decide⟩ = 1/2 := by
    rcases hd ⟨1, by decide⟩ with hz | hh
    · have hrest (i : Fin (Fintype.card (Fin 5 × Fin 5))) (hi : i ≠ 0) : H.eigenvalues₀ i = 0 := by
        have hi1 : (⟨1, by decide⟩ : Fin (Fintype.card (Fin 5 × Fin 5))) ≤ i := by
          exact Fin.one_le_of_ne_zero hi
        exact le_antisymm ((H.eigenvalues₀_antitone hi1).trans_eq hz) (hnonneg i)
      have hone : (∑ i : Fin (Fintype.card (Fin 5 × Fin 5)), H.eigenvalues₀ i) = H.eigenvalues₀ 0 := by
        exact Fintype.sum_eq_single 0 hrest
      have := hcap 0
      linarith
    · exact hh
  refine ⟨?_, hsecond⟩
  change H.eigenvalues₀ 0 = 1/2
  have hm := H.eigenvalues₀_antitone
    (show (0 : Fin (Fintype.card (Fin 5 × Fin 5))) ≤ ⟨1, by decide⟩ from Fin.zero_le _)
  have hc := hcap 0
  linarith

private theorem rho_hHat : hHat rho rho_pos.isHermitian = 1/2 := by
  simp only [hHat, show 2 ≤ Fintype.card (Fin 5 × Fin 5) from Nat.le_of_ble_eq_true rfl, ↓reduceDIte,
    rho_top_two.1, rho_top_two.2]
  norm_num

private theorem uniform_eigenvalues {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (c : ℂ) (H : (c • (1 : Matrix n n ℂ)).IsHermitian) (i : n) :
    (H.eigenvalues i : ℂ) = c := by
  have hm : (H.eigenvalues i : ℂ) ∈ spectrum ℂ (c • (1 : Matrix n n ℂ)) := by
    exact spectrum.algebraMap_mem ℂ (H.eigenvalues_mem_spectrum_real i)
  have hs : spectrum ℂ (c • (1 : Matrix n n ℂ)) = {c} := by
    rw [← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq]
  simpa only [hs, Set.mem_singleton_iff] using hm

private theorem marginal_hHat (M : Matrix (Fin 5) (Fin 5) ℂ) (H : M.IsHermitian)
    (hM : M = (1/5 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) : hHat M H = 1/5 := by
  subst M
  have he (i : Fin (Fintype.card (Fin 5))) : H.eigenvalues₀ i = 1/5 := by
    have hi := uniform_eigenvalues (n := Fin 5) (1/5) H
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
    have hr := congrArg Complex.re hi
    norm_num at hr
    simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hr
  simp only [hHat, show 2 ≤ Fintype.card (Fin 5) from Nat.le_of_ble_eq_true rfl, ↓reduceDIte, he]
  norm_num

theorem result : ¬ claim := by
  intro hc
  have h := hc 5 5 rho rho_density
  rw [rho_hHat, marginal_hHat _ _ rho_right, marginal_hHat _ _ rho_left] at h
  norm_num at h


end D5.S3.Quantum.Entanglement.PartialNegativity.GuoHatSubadditivityRefutation
