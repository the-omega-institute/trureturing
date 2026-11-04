/- GID: D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.claim; result=D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.result; claim=D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.claim
   digest: No superchannel has precisely the qutrit dephasing-covariant fixed channels. -/

/-
Per-declaration proof organization; direct frozen dependencies inline same-module helpers.
IsDestruction: proof_shape: bind-only; escape_witness: none; consumers: claim, result.
Direct frozen dependencies: D02, D17.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D02, D17, D31.
perm: proof_shape: bind-only; escape_witness: none; consumers: U, monomial_covariant, overlap_base, overlap_hub, perm_covers, phase_difference, spanning, unitary, v_normalized.
Direct frozen dependencies: none.
phase: proof_shape: bind-only; escape_witness: none; consumers: U, monomial_covariant, overlap_base, overlap_hub, phase_difference, unitary, v_normalized.
Direct frozen dependencies: none.
U: proof_shape: bind-only; escape_witness: none; consumers: dot_scaled, fixes_dio_identity, monomial_covariant, overlap_base, overlap_hub, phase_difference, probe_choi, unitary, v, v_normalized.
Direct frozen dependencies: D11.
unitary: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D11, D13.
conj_channel: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity, result.
Direct frozen dependencies: D04, D17, D28.
monomial_covariant: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D02, D04, D11, D12, D14, D15, D16, D18.
dephase_apply: proof_shape: bind-only; escape_witness: none; consumers: R_not_covariant, depol_covariant.
Direct frozen dependencies: D02, D18.
dephase_kraus: proof_shape: bind-only; escape_witness: none; consumers: dephase_channel.
Direct frozen dependencies: D02, D06, D07, D08, D18.
dephase_channel: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D02, D03, D06, D07, D08, D09, D17, D18.
dephase_idem: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D18.
faithful_fixed: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D02, D18, D19.
choi_conj: proof_shape: bind-only; escape_witness: none; consumers: probe_choi.
Direct frozen dependencies: D02, D04, D05, D06, D07, D08, D33.
c: proof_shape: bind-only; escape_witness: none; consumers: cstar, dot_scaled, phase_difference, probe_choi, spanning, v.
Direct frozen dependencies: none.
cstar: proof_shape: bind-only; escape_witness: none; consumers: dot_scaled, probe_choi.
Direct frozen dependencies: D01.
c_ne: proof_shape: bind-only; escape_witness: none; consumers: spanning.
Direct frozen dependencies: none.
v: proof_shape: bind-only; escape_witness: none; consumers: connected, dot_scaled, fixes_dio_identity, overlap_base, overlap_hub, phase_difference, probe_choi, spanning, v_normalized.
Direct frozen dependencies: D11.
dot_scaled: proof_shape: bind-only; escape_witness: none; consumers: overlap_base, overlap_hub, v_normalized.
Direct frozen dependencies: D01, D11.
v_normalized: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D01, D11.
overlap_base: proof_shape: bind-only; escape_witness: none; consumers: connected.
Direct frozen dependencies: D01, D11.
overlap_hub: proof_shape: bind-only; escape_witness: none; consumers: connected.
Direct frozen dependencies: D01, D11.
connected: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D01, D11, D25.
perm_covers: proof_shape: bind-only; escape_witness: none; consumers: spanning.
Direct frozen dependencies: none.
phase_difference: proof_shape: bind-only; escape_witness: none; consumers: spanning.
Direct frozen dependencies: D11.
spanning: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D11.
probe_choi: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D01, D02, D04, D05, D06, D07, D08, D11, D27, D33.
depol_choi: proof_shape: bind-only; escape_witness: none; consumers: depol_channel, fixes_dio_identity.
Direct frozen dependencies: D20, D23, D33.
depol_channel: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D02, D03, D17, D20, D23, D33.
depol_covariant: proof_shape: bind-only; escape_witness: none; consumers: fixes_dio_identity.
Direct frozen dependencies: D02, D18, D20, D21, D22.
R: proof_shape: bind-only; escape_witness: none; consumers: R_not_covariant, R_unitary, result.
Direct frozen dependencies: none.
R_unitary: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: none.
R_not_covariant: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D02, D04, D18.
fixes_dio_identity: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: D01, D02, D03, D04, D05, D06, D07, D08, D10, D11, D12, D13, D14, D15, D16, D17, D18, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30, D31, D32, D33, D34, D35, D36, D37, D38.
result: proof_shape: bind-only; escape_witness: none; consumers: none (settling result).
Direct frozen dependencies: D01, D02, D03, D04, D05, D06, D07, D08, D09, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30, D31, D32, D33, D34, D35, D36, D37, D38.
admission_basis: open-problem-resolution (#24013; Refuted).
Owner publication escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25799
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Dependency identities below are declaration statement_ids from the canonical scoped Lean report.
Published owners use their public declaration identities; module pins are separate identities.
D01: D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.sqrt3_sq
  statement_id: sha256:c18076146017460c0664cc760f33eb5d976501bf57026a84e8a3a3a34cc9d38d.
D02: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
  statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7.
D03: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
  statement_id: sha256:31bd68fc3c839750d1a8ac1474555b08fcd9579b1627c81db36a58f3172e1252.
D04: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj
  statement_id: sha256:beb687a7629ceb256c23382ba2a92cbaaf9290eb18c04844c530f5be33c31fcc.
D05: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply
  statement_id: sha256:065ec62ed35c9f042b51d14ac7534229d83240f7252faec6805576b51b620645.
D06: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
  statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287.
D07: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1
  statement_id: sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb.
D08: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2
  statement_id: sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1.
D09: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
  statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f.
D10: D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5.
D11: D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial
  statement_id: sha256:91a2ea4a89443261afe41a296d1228bcf63a579dbe6969848318d4bcd458c431.
D12: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.monomial_projection
  statement_id: sha256:05d3273e254314be21cef3137844dc221322e26ce73ac10bf2e490f9a1d19cc7.
D13: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.monomial_unitary
  statement_id: sha256:3e38cf3c10e2ea89ac2b93766606bcb37de267d5251db2586d73433c37adc457.
D14: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.offDiag
  statement_id: sha256:ea7a0a31457931e608b08a970c766b92af0a56412db472f62ba193461b5b25cb.
D15: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.offDiag._proof_1
  statement_id: sha256:bea2169ab18f862c3dd8ff0b1afe17f5f21013d56e6b30906aea576d2c61384a.
D16: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment.offDiag._proof_2
  statement_id: sha256:7dbe0e00e231b1835ab124ac3af9c8020f29b5f02b13fff19398064bc310c910.
D17: D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.IsChannel
  statement_id: sha256:40ecbbfc56930a33b279d0ffc7c0f4514119d3a67cd1c1598d9e51bee0591fd4.
D18: D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.dephase
  statement_id: sha256:f554079a152b5b5a321d72b7f3bfa5e23928681d90a06220460f4a8e1f962309.
D19: D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.dephase._proof_1
  statement_id: sha256:b6ae60d5ac5a967075c3ad38da41f44cd26de92ee3b8975d12b8c6e9bc96d675.
D20: D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol
  statement_id: sha256:2fe78b6bace96157a34f16b53eab4c23d91f43c8d43ed29444c8ea8d5891d68d.
D21: D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol._proof_1
  statement_id: sha256:7eed76a9ea515bb87bd0eb888c88e77004df16dc898371f5729b2b396c38285c.
D22: D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol._proof_2
  statement_id: sha256:924769e7c1b6bf2f622067a17fd172d50bfc2176ec9b45f3da9e873968360504.
D23: D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.depol_single_eq_dmat
  statement_id: sha256:c9d1b29ce0c12c35205d556f5c25b97464c36cfbd6b7cd9b66d1a5b14ad9c37b.
D24: D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi
  statement_id: sha256:7620ae518a39944b6825fd260cd713177187b28856493804968f5ddc77f33bd0.
D25: D5/S3/Quantum/Reduction/ProbeComponentRigidity.SameComponent
  statement_id: sha256:8c46113b6da2bb04c319a11ac6a4dbbcb24f65f44ab3d3414af1b7f523bdbed0.
D26: D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity
  statement_id: sha256:cec0e0d93f9dbf25108054b00d304749737a61a5811591b7af74bca5431f43d5.
D27: D5/S3/Quantum/Reduction/ProbeComponentRigidity.probe
  statement_id: sha256:f5b3b039ec347372b8b6448078a180419ab9681a2991f506e66c5cd8ba39b684.
D28: D5/S3/QuantumChannels/ChannelTimeReversalNoGo.unitaryChannel_cptp
  statement_id: sha256:1d83f1b6aec04cd27d1dd30bad22c466c15d030fd8f373e303311d4a7d475acd.
D29: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQSC._proof_1
  statement_id: sha256:6ef2c7d381a411da6a04520cac950635d9b32da20a0eeddd6402bd880ad07671.
D30: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQSC._proof_2
  statement_id: sha256:96a9d7c070d9e208b8907b757a69e7300efa6158f84ecdff8c805da3c3de9c80.
D31: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.IsQuantumSuperchannel
  statement_id: sha256:fc4b908cbfb791ecf24bb679ccc53d73be13e16bbe9cfa4ed0f776a101cdc910.
D32: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.SCPTP._proof_1
  statement_id: sha256:77b6b34214a2354e8c38a24701cd601972b801e31294d178fdbe91dec1a8f325.
D33: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choi
  statement_id: sha256:3df8f4e69ae95ac81eeb922c6bcf6fd0ca32e5e60eee6a2be12a0fe360a945af.
D34: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choiEquiv
  statement_id: sha256:e8b177b08bdafa9a115d6c3d7d68fd5d915d41a63401e9cb6e182033818771e6.
D35: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.choi_induced_apply
  statement_id: sha256:2cf5a97ca634156dbff5dcc33c9f3afdb693da416e274843bf4133e9201754c5.
D36: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.induced
  statement_id: sha256:a1dc11151c44435499e78e9632613d16a7668165e781565e170b37abe62f126a.
D37: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.kronLift
  statement_id: sha256:d048232c75323b97efe433f0932533465c505ae2c0d9946708e9cc463d78873b.
D38: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.preserving_cp_induced
  statement_id: sha256:e0951fe3e223ddc0897ee9fe1977496a76ab819c9ce1a9f071bc5671065e0db4.
The admissibility predicate and covariance equation retain the source expressions;
complete dephasing, CPTP maps and quantum superchannels use existing owners.
-/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
import D5.S3.QuantumChannels.DalySuperchannelMinimalExtension
import D5.S3.Quantum.Reduction.ProbeComponentRigidity
import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
import D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
import D5.S3.QuantumChannels.ChannelTimeReversalNoGo
import D5.S3.Quantum.Algebra.CStarSmaleHigherOrder
import D5.S3.Quantum.Matrix.MonomialDiagonalPreserving
import D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue (IsChannel)
open D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful (dephase)
open D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum (depol)
open D5.S3.QuantumChannels.DalySuperchannelMinimalExtension
open D5.S3.Quantum.Reduction.ProbeComponentRigidity

namespace D5.S3.QuantumChannels.YoeliGourDestructionSuperchannelRefutation
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-- The source's admissible system: an idempotent CPTP destruction map
fixing at least one full-rank density state. -/
def IsDestruction {d : ℕ} (Δ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  IsChannel Δ ∧ Δ.comp Δ = Δ ∧
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ,
      ρ.PosDef ∧ Matrix.trace ρ = 1 ∧ Δ ρ = ρ

/-- The affirmative answer to the source's unnumbered open question:
for every admissible pair, the destruction-covariant CPTP channels are exactly
the fixed CPTP channels of some idempotent deterministic superchannel. -/
def claim : Prop :=
  ∀ a : ℕ, 0 < a → ∀ b : ℕ, 0 < b →
    ∀ ΔA : MatrixMap (Fin a) (Fin a) ℂ,
      ∀ ΔB : MatrixMap (Fin b) (Fin b) ℂ,
        IsDestruction ΔA → IsDestruction ΔB →
          ∃ Θ : MatrixMap (Fin a) (Fin b) ℂ →ₗ[ℂ]
              MatrixMap (Fin a) (Fin b) ℂ,
            IsQuantumSuperchannel Θ ∧ Θ.comp Θ = Θ ∧
              ∀ N : MatrixMap (Fin a) (Fin b) ℂ,
                IsChannel N → (Θ N = N ↔ N.comp ΔA = ΔB.comp N)


private def perm (p : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := ![![0,1,2], ![1,2,0], ![2,0,1], ![1,0,2]] p
  invFun := ![![0,1,2], ![2,0,1], ![1,2,0], ![1,0,2]] p
  left_inv := by fin_cases p <;> decide
  right_inv := by fin_cases p <;> decide

private def phase (q : Fin 4) (c : Fin 3) : ℂ :=
  if q.val = c.val + 1 then Complex.I else 1

private def U (p q : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  D5.S3.Quantum.Matrix.MonomialDiagonalPreserving.monomial
    (perm p).symm (phase q ∘ (perm p).symm)

private theorem unitary (p q : Fin 4) : (U p q)ᴴ * U p q = 1 := by
  apply Matrix.mem_unitaryGroup_iff'.mp
  exact D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.monomial_unitary
    (perm p) (phase q) (by
      intro i
      fin_cases q <;> fin_cases i <;> norm_num [phase])

private theorem conj_channel {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) : IsChannel (MatrixMap.conj V) := by
  have hU : V ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr hV
  exact D5.S3.QuantumChannels.ChannelTimeReversalNoGo.unitaryChannel_cptp hU

private theorem monomial_covariant (p q : Fin 4) :
    (MatrixMap.conj (U p q)).comp dephase = dephase.comp (MatrixMap.conj (U p q)) := by
  have hoff (X : Matrix (Fin 3) (Fin 3) ℂ) :
      D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag X = X - dephase X := by
    ext i j
    by_cases h : i = j <;>
      simp [D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag,
        dephase, LinearMap.comp_apply, Matrix.diagLinearMap, Matrix.diagonalLinearMap,
        Matrix.diagonal, h]
  apply LinearMap.ext
  intro X
  have h := D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.monomial_projection
    (perm p) (phase q) X
  change D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag
      (MatrixMap.conj (U p q) X) = MatrixMap.conj (U p q)
        (D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.offDiag X) at h
  rw [hoff, hoff, map_sub] at h
  have hh := congrArg (fun Z => MatrixMap.conj (U p q) X - Z) h
  simpa only [LinearMap.comp_apply, sub_sub_cancel] using hh.symm

private theorem dephase_apply (X : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    dephase X i j = if i = j then X i i else 0 := by
  rfl

private theorem dephase_kraus : (dephase : MatrixMap (Fin 3) (Fin 3) ℂ) =
    MatrixMap.of_kraus (fun i : Fin 3 => Matrix.single i i (1 : ℂ))
      (fun i : Fin 3 => Matrix.single i i (1 : ℂ)) := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [dephase, MatrixMap.of_kraus, LinearMap.comp_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
      Fin.sum_univ_succ]

private theorem dephase_channel : IsChannel (dephase : MatrixMap (Fin 3) (Fin 3) ℂ) := by
  constructor
  · rw [dephase_kraus]
    exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro X
    rfl

private theorem dephase_idem :
    (dephase : MatrixMap (Fin 3) (Fin 3) ℂ).comp dephase = dephase := by
  ext X i j
  change diagonal (diag (diagonal (diag X))) i j = diagonal (diag X) i j
  rw [diag_diagonal]

private theorem faithful_fixed : ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, ρ.PosDef ∧ trace ρ = 1 ∧ dephase ρ = ρ := by
  refine ⟨diagonal (fun _ => (1/3 : ℂ)), ?_, ?_, ?_⟩
  · apply Matrix.PosDef.diagonal
    intro i
    norm_num
  · norm_num [Matrix.trace, Fin.sum_univ_succ]
  · simp [dephase]

private theorem choi_conj (V : Matrix (Fin 3) (Fin 3) ℂ) : choi (MatrixMap.conj V) =
    vecMulVec (fun x : Fin 3 × Fin 3 => V x.2 x.1)
      (star (fun x : Fin 3 × Fin 3 => V x.2 x.1)) := by
  have hk : MatrixMap.conj V = MatrixMap.of_kraus (fun _ : Unit => V) (fun _ : Unit => V) := by
    ext X i j
    simp [MatrixMap.conj, MatrixMap.of_kraus]
  have hh := MatrixMap.choi_of_kraus (fun _ : Unit => V)
  rw [← hk] at hh
  ext x y
  have he := congrArg (fun M => M (x.2,x.1) (y.2,y.1)) hh
  simpa [choi, MatrixMap.choi_matrix, Matrix.vecMulVec_apply] using he


private def c : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹

private theorem cstar : star c * c = (1/3 : ℂ) := by
  have hs : ((Real.sqrt 3 : ℝ) : ℂ)^2 = 3 := by
    exact D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
  simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← pow_two, hs]
  norm_num

private theorem c_ne : c ≠ 0 := by
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))

private def v (pq : Fin 4 × Fin 4) : (Fin 3 × Fin 3) → ℂ :=
  c • Matrix.vec (U pq.1 pq.2)

private theorem dot_scaled (s t : Fin 4 × Fin 4) :
    star (v s) ⬝ᵥ v t = (1/3 : ℂ) * (star ((fun x : Fin 3 × Fin 3 => U s.1 s.2 x.2 x.1)) ⬝ᵥ (fun x : Fin 3 × Fin 3 => U t.1 t.2 x.2 x.1)) := by
  simp only [v, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, mul_comm c, cstar]
  rfl

private theorem v_normalized (pq : Fin 4 × Fin 4) : star (v pq) ⬝ᵥ v pq = 1 := by
  rw [dot_scaled]
  rcases pq with ⟨p,q⟩
  fin_cases p <;> fin_cases q <;>
    norm_num [U, D5.S3.Quantum.Matrix.MonomialDiagonalPreserving.monomial, perm, phase, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem overlap_base (p q : Fin 4) : star (v (p,q)) ⬝ᵥ v (p,0) ≠ 0 := by
  rw [dot_scaled]
  fin_cases p <;> fin_cases q <;>
    norm_num [U, D5.S3.Quantum.Matrix.MonomialDiagonalPreserving.monomial, perm, phase, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Complex.ext_iff]

private theorem overlap_hub (p : Fin 4) : star (v (p,0)) ⬝ᵥ v (3,0) ≠ 0 := by
  rw [dot_scaled]
  fin_cases p <;>
    norm_num [U, D5.S3.Quantum.Matrix.MonomialDiagonalPreserving.monomial, perm, phase, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Complex.ext_iff]

private theorem connected (s t : Fin 4 × Fin 4) : SameComponent v s t := by
  have h (s : Fin 4 × Fin 4) : SameComponent v s (3,0) := by
    exact Relation.EqvGen.trans s (s.1,0) (3,0)
      (Relation.EqvGen.rel s (s.1,0) (overlap_base s.1 s.2))
      (Relation.EqvGen.rel (s.1,0) (3,0) (overlap_hub s.1))
  exact Relation.EqvGen.trans s (3,0) t (h s) (Relation.EqvGen.symm t (3,0) (h t))

private theorem perm_covers (i j : Fin 3) : ∃ p : Fin 4, perm p i = j := by
  fin_cases i <;> fin_cases j
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

private theorem phase_difference (p : Fin 4) (i : Fin 3) :
    v (p,⟨i.val+1, by omega⟩) - v (p,0) =
      (c * (Complex.I - 1)) • Pi.single (i,perm p i) (1 : ℂ) := by
  ext x
  rcases x with ⟨j,k⟩
  fin_cases p <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [v, U, D5.S3.Quantum.Matrix.MonomialDiagonalPreserving.monomial,
      perm, phase, Prod.ext_iff, flip] <;> ring

private theorem spanning : Submodule.span ℂ (Set.range v) = ⊤ := by
  let W := Submodule.span ℂ (Set.range v)
  have he (x : Fin 3 × Fin 3) : Pi.single x (1 : ℂ) ∈ W := by
    rcases x with ⟨i,j⟩
    obtain ⟨p,hp⟩ := perm_covers i j
    have hd : v (p,⟨i.val+1, by omega⟩) - v (p,0) ∈ W :=
      W.sub_mem (Submodule.subset_span ⟨_,rfl⟩) (Submodule.subset_span ⟨_,rfl⟩)
    rw [phase_difference, hp] at hd
    have hz : c * (Complex.I - 1) ≠ 0 := mul_ne_zero c_ne (by norm_num [Complex.ext_iff])
    have hh := W.smul_mem ((c * (Complex.I - 1))⁻¹) hd
    simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hh
  apply top_unique
  intro x _
  rw [← Finset.univ_sum_single x]
  apply W.sum_mem
  intro i _
  have hs := W.smul_mem (x i) (he i)
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using hs

private theorem probe_choi (pq : Fin 4 × Fin 4) :
    probe (v pq) = (1/3 : ℂ) • choi (MatrixMap.conj (U pq.1 pq.2)) := by
  rw [choi_conj]
  ext x y
  change (c * (fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) x) * star (c * (fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) y) =
    (1/3 : ℂ) * ((fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) x * star ((fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) y))
  rw [star_mul]
  calc
    _ = (star c * c) * ((fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) x * star ((fun x : Fin 3 × Fin 3 => U pq.1 pq.2 x.2 x.1) y)) := by ring
    _ = _ := by rw [cstar]

private theorem depol_choi : choi (depol 3) = (1/3 : ℂ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) := by
  ext ⟨i,r⟩ ⟨j,s⟩
  exact D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.depol_single_eq_dmat 3 i j r s

private theorem depol_channel : IsChannel (depol 3) := by
  constructor
  · apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
    have h : (depol 3).choi_matrix = diagonal (fun _ : Fin 3 × Fin 3 => (1/3 : ℂ)) := by
      ext ⟨r,i⟩ ⟨s,j⟩
      change choi (depol 3) (i,r) (j,s) = _
      rw [depol_choi]
      simp [Matrix.one_apply, Matrix.diagonal, Prod.ext_iff, and_comm]
    rw [h]
    exact Matrix.PosSemidef.diagonal (fun _ => by norm_num [Complex.nonneg_iff])
  · intro X
    simp [depol, Matrix.trace_smul]

private theorem depol_covariant : (depol 3).comp dephase = dephase.comp (depol 3) := by
  ext X i j
  change depol 3 (dephase X) i j = dephase (depol 3 X) i j
  by_cases h : i = j
  · subst j
    simp [dephase_apply, depol, Matrix.trace]
  · simp [dephase_apply, depol, h]


private def R : Matrix (Fin 3) (Fin 3) ℂ := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0,0,1]

private theorem R_unitary : Rᴴ * R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply, map_ofNat]

private theorem R_not_covariant : (MatrixMap.conj R).comp dephase ≠ dephase.comp (MatrixMap.conj R) := by
  intro h
  have he := congrArg (fun L : MatrixMap (Fin 3) (Fin 3) ℂ => L (Matrix.single 0 0 1) 0 1) h
  have he0 : dephase (Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.single 0 0 1 := by
    change diagonal (diag (Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = _
    rw [Matrix.diag_single_same, Matrix.diagonal_single]
  change ((R * dephase (Matrix.single (0 : Fin 3) 0 (1 : ℂ)) * Rᴴ) : Matrix (Fin 3) (Fin 3) ℂ) 0 1 =
    dephase ((R * Matrix.single (0 : Fin 3) 0 (1 : ℂ) * Rᴴ) : Matrix (Fin 3) (Fin 3) ℂ) 0 1 at he
  rw [he0, dephase_apply] at he
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] at he
  norm_num [R, Matrix.single, map_ofNat] at he



private theorem fixes_dio_identity
    (Θ : MatrixMap (Fin 3) (Fin 3) ℂ →ₗ[ℂ] MatrixMap (Fin 3) (Fin 3) ℂ)
    (hΘ : IsQuantumSuperchannel Θ)
    (hfree : ∀ N : MatrixMap (Fin 3) (Fin 3) ℂ,
      IsChannel N → N.comp dephase = dephase.comp N → Θ N = N) :
    Θ = LinearMap.id := by
  let T := induced Θ
  have hcp : T.IsCompletelyPositive := preserving_cp_induced Θ hΘ.2.1
  obtain ⟨A,hA⟩ := MatrixMap.IsCompletelyPositive.exists_kraus T hcp
  have act (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : T X = ∑ a, A a * X * (A a)ᴴ := by
    rw [hA]
    simp [MatrixMap.of_kraus]
  have transport (N : MatrixMap (Fin 3) (Fin 3) ℂ) : T (choi N) = choi (Θ N) :=
    (choi_induced_apply Θ N).symm
  have hR : Θ (depol 3) = depol 3 :=
    hfree _ depol_channel depol_covariant
  have hOne : T 1 = 1 := by
    have h := transport (depol 3)
    simp only [hR, depol_choi, map_smul] at h
    have h' := congrArg (fun X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ => (3 : ℂ) • X) h
    simpa only [smul_smul, show (3 : ℂ) * (1/3) = 1 by norm_num, one_smul] using h'
  have hP (pq : Fin 4 × Fin 4) : T (probe (v pq)) = probe (v pq) := by
    simp only [probe_choi, map_smul, transport]
    have hf : Θ (MatrixMap.conj (U pq.1 pq.2)) = MatrixMap.conj (U pq.1 pq.2) :=
      hfree _ (conj_channel _ (unitary _ _)) (monomial_covariant _ _)
    rw [hf]
  let K := fun a => (A a)ᴴ
  have hn : (∑ a, (K a)ᴴ * K a) = 1 := by
    have h := act (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    rw [hOne] at h
    simpa only [K, conjTranspose_conjTranspose, mul_one] using h.symm
  have hprob : ∀ pq (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Fin 3 × Fin 3)),
      trace (probe (v pq) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v pq) * CStarMatrix.ofMatrix.symm ρ.1) := by
    intro pq ρ
    let X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := CStarMatrix.ofMatrix.symm ρ.1
    simp only [K, conjTranspose_conjTranspose]
    change trace (probe (v pq) * (∑ a, (A a)ᴴ * X * A a)) = trace (probe (v pq) * X)
    calc
      _ = trace ((∑ a, A a * probe (v pq) * (A a)ᴴ) * X) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum]
        apply Finset.sum_congr rfl
        intro a _
        simpa only [mul_assoc] using
          (trace_mul_comm (probe (v pq) * (A a)ᴴ * X) (A a))
      _ = trace (T (probe (v pq)) * X) := by rw [act]
      _ = _ := by rw [hP]
  have hi := (connected_probability_preserving_identity K hn v v_normalized spanning
    connected (0,0) (0,0) hprob).1
  have hT (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : T X = X := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    calc
      trace (T X * Y) = trace (X * (∑ a, K a * Y * (K a)ᴴ)) := by
        rw [act]
        simp only [Matrix.sum_mul, Matrix.mul_sum, trace_sum, K,
          conjTranspose_conjTranspose]
        apply Finset.sum_congr rfl
        intro a _
        simpa only [mul_assoc] using
          (trace_mul_comm (A a) (X * (A a)ᴴ * Y))
      _ = trace (X * Y) := by rw [hi]
  apply LinearMap.ext
  intro N
  apply (choiEquiv (Fin 3) (Fin 3)).injective
  change choi (Θ N) = choi N
  rw [← transport, hT]

theorem result : ¬ claim := by
  intro hclaim
  have hd : IsDestruction (dephase : MatrixMap (Fin 3) (Fin 3) ℂ) :=
    ⟨dephase_channel, dephase_idem, faithful_fixed⟩
  obtain ⟨Θ,hΘ,_hid,hfix⟩ := hclaim 3 (by norm_num) 3 (by norm_num) dephase dephase hd hd
  have hi := fixes_dio_identity Θ hΘ (fun N hN hd => (hfix N hN).mpr hd)
  have hf : Θ (MatrixMap.conj R) = MatrixMap.conj R := by rw [hi]; rfl
  exact R_not_covariant ((hfix _ (conj_channel R R_unitary)).mp hf)

end D5.S3.QuantumChannels.YoeliGourDestructionSuperchannelRefutation
