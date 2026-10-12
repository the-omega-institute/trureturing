/- GID: D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: AntidistinguishabilityOverlapNonTight supports the overlap bound. -/

/-
proof_shape: IsTight: bind-only; consumer: not_tight_of_quantitative, claim
escape_witness: IsTight: none
Direct frozen dependencies: IsTight: none
proof_shape: not_tight_of_quantitative: bind-only; consumer: result
escape_witness: not_tight_of_quantitative: none
Direct frozen dependencies: not_tight_of_quantitative: none
proof_shape: quantitative_spectral_condition: content; consumer: quantitative_state_spectral_condition
escape_witness: quantitative_spectral_condition: quantitative_spectral_condition
Direct frozen dependencies: quantitative_spectral_condition: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20
proof_shape: claim: bind-only; consumer: result
escape_witness: claim: none
Direct frozen dependencies: claim: none
proof_shape: quantitative_state_spectral_condition: content; consumer: quantitative_antidistinguishability
escape_witness: quantitative_state_spectral_condition: quantitative_spectral_condition
Direct frozen dependencies: quantitative_state_spectral_condition: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20
proof_shape: quantitative_antidistinguishability: content; consumer: result
escape_witness: quantitative_antidistinguishability: quantitative_spectral_condition
Direct frozen dependencies: quantitative_antidistinguishability: F1, F21, F22, F23, F24, F25, F26, F27, F28, F4, F14, F9, F10, F11, F29, F30, F31, F32, F33, F34, F35, F36, F37, F3, F38, F39, F5, F2, F6, F7, F8, F12, F13, F15, F16, F17, F18, F19, F20
proof_shape: result: content
escape_witness: result: quantitative_spectral_condition
Direct frozen dependencies: result: F1, F21, F22, F23, F24, F25, F26, F27, F28, F4, F14, F9, F10, F11, F29, F30, F31, F32, F33, F34, F35, F36, F37, F3, F38, F39, F5, F2, F6, F7, F8, F12, F13, F15, F16, F17, F18, F19, F20
admission_basis: open-problem-resolution (#15573; Proved)
Frozen declaration identities:
F1: D5/S3/Weil/ZetaLinear/PosIndex.eigEquiv
  statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
F2: D5/S3/Weil/ZetaLinear/PosIndex.frobSq
  statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
F3: D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix
  statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
F4: D5/S3/Weil/ZetaLinear/PosIndex.rtrace
  statement_id: sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F5: D5/S3/Weil/ZetaLinear/PosIndex.eigenvalues_eigEquiv
  statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
F6: D5/S3/Weil/ZetaLinear/PosIndex.rtrace_eq_sum_eigenvalues
  statement_id: sha256:7de56e963243100cb0d7ed9e3a63e24c1f7a82297129182e1158ce2a9aa88e58
F7: D5/S3/Weil/ZetaLinear/PosIndex.frobSq_hermitian_eq_sum_sq_eigenvalues
  statement_id: sha256:8517f9a9ec34b3ab0b7f30f5025ab007ce87f585c396c39fa4b953498c3fd325
F8: D5/S3/Quantum/Matrix/CartesianVariance.frobSq_eq_sum
  statement_id: sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
F9: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap
  statement_id: sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F10: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_isHermitian
  statement_id: sha256:8eaaf395a5d8810c697d036c8729b5974aade8efbc4111a5132de5a598ab00b6
F11: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_mul
  statement_id: sha256:7676c10505b22f0e9db5f08c8be82f86e9eb4db5a663554bc93b31c13a2aa6dc
F12: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right
  statement_id: sha256:63c2cd1b86c23c2972e5bf796750663ea1953eea0946f6abb48832ba5fa201e7
F13: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_left
  statement_id: sha256:d9ce203c282453198c2624036829bda9574a995fb51c1fbb98744a0940d93b8d
F14: D5/S3/Quantum/Matrix/CartesianVariance.vectorize
  statement_id: sha256:965518d7298ad8acdfeb6d0b33fc04a6e526724592513da04e49a30b340e8ddb
F15: D5/S3/Quantum/Matrix/CartesianVariance.vectorize_norm_sq
  statement_id: sha256:6c5f3c08cd68a8eaf88971cbe045c165f849a18949357cf6c63724d4581b30e5
F16: D5/S3/Weil/ZetaLinear/PosIndex.card_eigenvalues_reindex
  statement_id: sha256:587f80758b75110c6e73f0a75200f7e8fa58b12f878eb09edb2705914a3be32b
F17: D5/S3/Weil/ZetaLinear/RankTrace.frobSq_add_hermitian
  statement_id: sha256:2455ef94b9a3b384dead727978c5badae8178b7c4419a88c4ecd0cef405a3e0c
F18: D5/S3/Weil/ZetaLinear/PosIndex.sum_eigenvalues_reindex
  statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
F19: D5/S3/Weil/ZetaLinear/VonNeumann.vonNeumann_trace_ineq
  statement_id: sha256:62c803a8caa4f496d67cb6aab1077ed04427bd78c6be62d5430e5aa1486bdc8e
F20: D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound.rank_map_algebraMap
  statement_id: sha256:3c0973d77e8d73cecffdd9c8e8632a097717e8411d9c2704171e0f19d376a740
F21: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.moorePenroseInverse
  statement_id: sha256:d0c42c7ebe852755b1e0ac182e1eba16a13f9d7bc80db23d35a6e897dc56df5a
F22: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.IsMoorePenroseInverse
  statement_id: sha256:2a6c958072ca7dbf1881d1a83e4066dd700c1cbf16aa0e16badfd03daf7b570f
F23: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse
  statement_id: sha256:18736e4b1629c6ccacac40723a79c65171780f9e9f6296b93251162549f27768
F24: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.comp_comp_self
  statement_id: sha256:5d4cb4f02e32fbc6a78b9f61a1422f801c136bab622aa301506fd1fe73fb83e3
F25: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.comp_comp_self'
  statement_id: sha256:96b5ec221bccb262c6327be49075e74bd10e17611a518a8716f2105adeba5e0a
F26: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.isSymmetric_comp
  statement_id: sha256:6f091bad6d67a58d7e870f0ac224732ce51ad0562376da86bee4ab6097c546cc
F27: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.isSymmetric_comp'
  statement_id: sha256:6e455107e336f3d6977f59a532bc341a759522fedd448aa883c77865efa182f3
F28: D5/S3/Weil/ZetaLinear/Sylvester.hermForm
  statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
F29: D5/S3/Quantum/Matrix/CartesianVariance.matrix_pairing
  statement_id: sha256:bc7f3a1d092a6b296a75b0e9d5c7f8c0d2698b6b92d137a30a311713b8e68880
F30: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
  statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
F31: D5/S3/Weil/ZetaLinear/PosIndex.negIndex
  statement_id: sha256:b5905a543106ad41223ab3c0f6f31f7fb0632341c5e830350ec889bee1806429
F32: D5/S3/Weil/ZetaLinear/HermitianPosPart.hermNegPart
  statement_id: sha256:ad2a8390443bab24ec786ac6b42ded024195da37fd6d90578e441e73bf03e026
F33: D5/S3/Weil/ZetaLinear/Sylvester.PosDefOn
  statement_id: sha256:9ca9d30055bd50eda8453689225e563d10cdccb3278a2b8225dc9957a0890cc7
F34: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.negDefOn_range_hermNegPart
  statement_id: sha256:70d3c448a772227785663f0117c0f159426907edd543b564aa470d834558dd8d
F35: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  statement_id: sha256:e7d3fba989f8d1191d850ac68b17f943aea8d31ca3e6e460fb7f05749ab26485
F36: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_id
  statement_id: sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F37: D5/S3/Weil/ZetaLinear/HermitianPosPart.rtrace_specMap
  statement_id: sha256:efa5f0bbdc4f0443275c16da086085a95c6f4e6395761aa1fadb48ed96f8ca46
F38: D5/S3/Weil/ZetaLinear/VonNeumann.re_trace_mul_eq_eigenvalue_bilinear
  statement_id: sha256:2f34172916d220c9b2829e523338125a57ebec289094c5be9cef75eb5b11ec2a
F39: D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix_mem_doublyStochastic_of_unitary
  statement_id: sha256:10d84d7748c4e7f110f57a63c8faf31b2da6ecba24f5cdf67b5b36281d5a0757
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Published owner references use the protected baseline private declaration identities.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module. The result Reg candidate has DTR-Undeclared.
The candidate diagnostic is IE-C050 ClosedTruthReadout: unclassified_form under
source.residual_requires_open; no source-bound escape certificate is produced.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
import D5.S3.Quantum.Measurement.OverlapSpectralTruncation
import D5.S3.Quantum.Measurement.OverlapLowRankDistance

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram
open D5.S3.Quantum.Measurement.IncoherentCone
open D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
open D5.S3.Quantum.Measurement.OverlapSpectralTruncation
open D5.S3.Quantum.Measurement.OverlapLowRankDistance

section


def IsTight (n : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ (d : ℕ) (ψ : Fin n → EuclideanSpace ℂ (Fin d)),
      (∀ i, ‖ψ i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + ε) ∧
      ¬ IsAntidistinguishable ψ

end

section


private theorem not_tight_of_quantitative
    (n : ℕ) (hn : 10 ≤ n)
    (h : ∀ (d : ℕ) (ψ : Fin n → EuclideanSpace ℂ (Fin d)),
      (∀ i, ‖ψ i‖ = 1) →
      (∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) →
      IsAntidistinguishable ψ) : ¬ IsTight n := by
  intro ht
  obtain ⟨d, ψ, hnorm, hbound, hnot⟩ := ht (delta n) (delta_pos n hn)
  exact hnot (h d ψ hnorm hbound)

end

section


private theorem quantitative_spectral_condition (n : ℕ) (hn : 10 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1)
    (hcap : ∀ i j, i ≠ j → ‖G i j‖ ^ 2 ≤ cSq n + delta n) :
    Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0, by omega⟩) ≤
      ∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n), Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k) := by
  by_contra! hfail
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  let D : ℝ := RHLinalg.frobSq G - (n : ℝ)^2/2
  let H : Matrix (Fin n) (Fin n) ℂ := (RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ)
  let K : Matrix (Fin n) (Fin n) ℂ := (RHLinalg.normSqMatrix (topThree hG.isHermitian)).map (algebraMap ℝ ℂ)
  let H0 : Matrix (Fin n) (Fin n) ℂ := equalOverlap n (cSq n)
  have htrace : RHLinalg.rtrace G = n := by
    simp [RHLinalg.rtrace, Matrix.trace, hdiag]
  have hfourth := spectral_failure_fourth_bound n (by omega) ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)))
    (orderedSpectrum_nonneg hG) (orderedSpectrum_antitone hG.isHermitian) hfail
  rw [sum_orderedSpectrum hG.isHermitian (fun x => x^2),
    sum_orderedSpectrum hG.isHermitian (fun x => x),
    ← RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hG.isHermitian,
    ← RHLinalg.rtrace_eq_sum_eigenvalues hG.isHermitian, htrace] at hfourth
  have hD0 : 0 ≤ D := (by positivity : 0 ≤ 12*(fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨3, by omega⟩ ^ 2) |>.trans hfourth
  have hDu : D ≤ (n : ℝ)*((n : ℝ)-1)*delta n := by
    have he := overlap_excess_identity n (by omega) G hdiag
    have hs : (∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2-cSq n)) ≤
        ∑ _p ∈ ((univ : Finset (Fin n)).offDiag), delta n := by
      apply sum_le_sum
      intro p hp
      have hne : p.1 ≠ p.2 := by simpa only [Finset.mem_offDiag, mem_univ, true_and] using hp
      linarith [hcap p.1 p.2 hne]
    rw [he] at hs
    simpa only [sum_const, nsmul_eq_mul, D5.S3.Quantum.Measurement.OverlapLowRankDistance.offDiag_card, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hs
  have hGnorm : ∀ i j, ‖G i j‖ ≤ 1 := psd_entry_bound hG (by simp [hdiag])
  have hTnorm : ∀ i j, ‖topThree hG.isHermitian i j‖ ≤ 1 :=
    psd_entry_bound (topThree_psd hG) (topThree_diag_le hG hdiag)
  have hHK : RHLinalg.frobSq (H-K) ≤ ((n : ℝ)-9)/16 := by
    have hs := norm_square_frob_distance_le G (topThree hG.isHermitian) hGnorm hTnorm
    have ht := topThree_failure_distance hG (by omega) hfail
    rw [htrace] at ht
    have hmul := mul_le_mul_of_nonneg_left hDu (show 0 ≤ (n : ℝ)-3 by linarith)
    rw [← mul_assoc ((n : ℝ)-3) ((n : ℝ)*((n : ℝ)-1)) (delta n), delta_budget n hn] at hmul
    change RHLinalg.frobSq (H-K) ≤ _ at hs
    change RHLinalg.frobSq (G-topThree hG.isHermitian) ≤ ((n : ℝ)-3)*D/4 at ht
    nlinarith
  have hHH0 : RHLinalg.frobSq (H-H0) ≤ ((n : ℝ)-9)/64 := by
    exact (overlap_target_distance_bound n (by omega) G hdiag (delta n)
      (delta_pos n hn).le hcap hD0).trans (delta_overlap_budget n hn)
  have hH0H : RHLinalg.frobSq (H0-H) = RHLinalg.frobSq (H-H0) := by
    rw [show H0-H = -(H-H0) by abel]
    simp only [RHLinalg.frobSq, Matrix.conjTranspose_neg, neg_mul_neg]
  have hsum := frobSq_add_le_twice n (H0-H) (H-K)
  rw [show (H0-H)+(H-K) = H0-K by abel, hH0H] at hsum
  have hu : RHLinalg.frobSq (H0-K) ≤
      2*(((n : ℝ)-9)/16)+2*(((n : ℝ)-9)/64) := by linarith
  have hc0 := cSq_nonneg n (by omega)
  have hc1 := (cSq_lt_half n (by omega)).le.trans (by norm_num : (1/2 : ℝ) ≤ 1)
  have hl := equalOverlap_low_rank_distance n 9 (cSq n) hc0 hc1 K
    (topThree_square_psd hG (by omega)).isHermitian (topThree_square_rank hG (by omega))
  exact quantitative_rank_contradiction n hn (RHLinalg.frobSq (H0-K)) hu hl

end

section


def claim : Prop := ∀ n : ℕ, 10 ≤ n → ¬ IsTight n

end

section


private theorem quantitative_state_spectral_condition (n : ℕ) (hn : 10 ≤ n) (d : ℕ)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖ψ i‖ = 1)
    (hcap : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) :
    Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0, by omega⟩) ≤
      ∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n),
        Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k) := by
  exact quantitative_spectral_condition n hn ((Matrix.gram ℂ ψ)) (gramPsd ψ)
    (stateGram_diag ψ hnorm) hcap

end

section


theorem quantitative_antidistinguishability (n : ℕ) (hn : 10 ≤ n) (d : ℕ)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖ψ i‖ = 1)
    (hcap : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) :
    IsAntidistinguishable ψ := by
  apply spectral_sufficient_antidistinguishable (by omega)
  exact quantitative_state_spectral_condition n hn d ψ hnorm hcap

end

section


theorem result : claim := by
  intro n hn
  exact not_tight_of_quantitative n hn (quantitative_antidistinguishability n hn)

end

end
end D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
