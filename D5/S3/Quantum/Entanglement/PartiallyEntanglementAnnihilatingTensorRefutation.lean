/- GID: D5/S3/Quantum/Entanglement/PartiallyEntanglementAnnihilatingTensorRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/PartiallyEntanglementAnnihilatingTensorRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/PartiallyEntanglementAnnihilatingTensorRefutation.claim; result=D5/S3/Quantum/Entanglement/PartiallyEntanglementAnnihilatingTensorRefutation.result; claim=D5/S3/Quantum/Entanglement/PartiallyEntanglementAnnihilatingTensorRefutation.claim
   digest: Non-local Schmidt-number annihilating channels need not remain so under tensor products. -/

import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
  (BipartiteOp coeff proj SchmidtNumberLE)

namespace D5.S3.Quantum.Entanglement.PartiallyEntanglementAnnihilatingTensorRefutation

def NonLocal {d : ℕ} (e : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ¬ ∃ e₁ e₂ : MatrixMap (Fin d) (Fin d) ℂ,
    IsCPTP e₁ ∧ IsCPTP e₂ ∧ e = MatrixMap.kron e₁ e₂

def IsPEA (d r : ℕ) (e : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsCPTP e ∧ NonLocal e ∧ r < d ∧
    ∀ ρ : BipartiteOp d, ρ.PosSemidef → ρ.trace = 1 → SchmidtNumberLE (e ρ) r

def alignedTensor {d : ℕ}
    (e f : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    MatrixMap (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ :=
  let a := (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin d) (Fin d)).trans
    (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  let t := Matrix.reindexLinearEquiv ℂ ℂ a a
  t.toLinearMap.comp ((MatrixMap.kron e f).comp t.symm.toLinearMap)

def claim : Prop :=
  ∀ (d r : ℕ) (e f : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ),
    IsPEA d r e → IsPEA d r f → IsPEA (d * d) r (alignedTensor e f)

private def phi : Ket (Fin 3 × Fin 3) :=
  ⟨fun x => if x.1 = x.2 ∧ x.1 < 2 then (1 : ℂ) / (Real.sqrt 2 : ℂ) else 0,
    by sorry⟩

private def replacement : MatrixMap (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (Matrix.traceLinearMap (Fin 3 × Fin 3) ℂ ℂ).smulRight (proj phi)

private theorem phi_rank : (coeff phi).rank = 2 := by
  sorry

private theorem replacement_cptp : IsCPTP replacement := by
  sorry

private theorem replacement_nonlocal : NonLocal replacement := by
  sorry

private theorem replacement_schmidt (ρ : BipartiteOp 3) (hρ : ρ.trace = 1) :
    SchmidtNumberLE (replacement ρ) 2 := by
  refine ⟨1, fun _ => 1, fun _ => phi, ?_, ?_, ?_, ?_⟩
  · intro k; norm_num
  · simp
  · intro k; exact phi_rank.le
  · simp [replacement, LinearMap.smulRight_apply, hρ]

private theorem replacement_pea : IsPEA 3 2 replacement := by
  refine ⟨replacement_cptp, replacement_nonlocal, by norm_num, ?_⟩
  intro ρ _ hρ
  exact replacement_schmidt ρ hρ

private def psi : Ket (Fin 9 × Fin 9) :=
  ⟨fun x =>
    let a := finProdFinEquiv.symm x.1
    let b := finProdFinEquiv.symm x.2
    phi.vec (a.1, b.1) * phi.vec (a.2, b.2), by sorry⟩

private theorem psi_rank : (coeff psi).rank = 4 := by
  sorry

private theorem pure_rank_le {d r : ℕ} (u : Ket (Fin d × Fin d))
    (h : SchmidtNumberLE (proj u) r) : (coeff u).rank ≤ r := by
  sorry

private theorem tensor_output :
    alignedTensor replacement replacement (proj psi) = proj psi := by
  sorry

private theorem tensor_not_pea : ¬ IsPEA 9 2 (alignedTensor replacement replacement) := by
  intro h
  have hs := h.2.2.2 (proj psi) (MState.psd (MState.pure psi))
    (MState.tr' (MState.pure psi))
  rw [tensor_output] at hs
  have hr := pure_rank_le psi hs
  rw [psi_rank] at hr
  omega

theorem result : ¬ claim := by
  intro h
  exact tensor_not_pea (h 3 2 replacement replacement replacement_pea replacement_pea)

end D5.S3.Quantum.Entanglement.PartiallyEntanglementAnnihilatingTensorRefutation
