/- GID: D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/AntidistinguishabilitySpectrum
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: AntidistinguishabilitySpectrum supports the overlap bound. -/

/-
proof_shape: weighted_sqrt_sum_lower: bind-only; consumer: spectral_dual_nonneg
escape_witness: weighted_sqrt_sum_lower: none
Direct frozen dependencies: weighted_sqrt_sum_lower: none
proof_shape: SpectralBalanced: bind-only; consumer: spectral_balanced_incoherent, spectral_balanced_pairing_nonneg
escape_witness: SpectralBalanced: none
Direct frozen dependencies: SpectralBalanced: none
proof_shape: spectral_balanced_of_ordered: bind-only; consumer: spectral_sufficient_incoherent
escape_witness: spectral_balanced_of_ordered: none
Direct frozen dependencies: spectral_balanced_of_ordered: F13, F14
proof_shape: bilinear_nonneg_of_permutations: bind-only; consumer: spectral_balanced_pairing_nonneg
escape_witness: bilinear_nonneg_of_permutations: none
Direct frozen dependencies: bilinear_nonneg_of_permutations: none
proof_shape: spectral_dual_nonneg: bind-only; consumer: spectral_balanced_pairing_nonneg
escape_witness: spectral_dual_nonneg: none
Direct frozen dependencies: spectral_dual_nonneg: none
proof_shape: spectral_balanced_pairing_nonneg: content; consumer: spectral_balanced_incoherent
escape_witness: spectral_balanced_pairing_nonneg: spectral_balanced_pairing_nonneg
Direct frozen dependencies: spectral_balanced_pairing_nonneg: F10, F11, F12, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F28, F29
proof_shape: spectral_balanced_incoherent: content; consumer: spectral_sufficient_incoherent
escape_witness: spectral_balanced_incoherent: spectral_balanced_incoherent
Direct frozen dependencies: spectral_balanced_incoherent: F8, F9, F10, F11, F12, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29
proof_shape: spectral_sufficient_incoherent: content; consumer: spectral_sufficient_antidistinguishable
escape_witness: spectral_sufficient_incoherent: spectral_sufficient_incoherent
Direct frozen dependencies: spectral_sufficient_incoherent: F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29
proof_shape: spectral_sufficient_antidistinguishable: content; consumer: quantitative_antidistinguishability
escape_witness: spectral_sufficient_antidistinguishable: spectral_sufficient_antidistinguishable
Direct frozen dependencies: spectral_sufficient_antidistinguishable: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29
admission_basis: escape-witness
Frozen declaration identities:
F1: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse
  declaration statement_id: sha256:2a6c958072ca7dbf1881d1a83e4066dd700c1cbf16aa0e16badfd03daf7b570f
F2: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self
  declaration statement_id: sha256:5d4cb4f02e32fbc6a78b9f61a1422f801c136bab622aa301506fd1fe73fb83e3
F3: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self'
  declaration statement_id: sha256:96b5ec221bccb262c6327be49075e74bd10e17611a518a8716f2105adeba5e0a
F4: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp
  declaration statement_id: sha256:6f091bad6d67a58d7e870f0ac224732ce51ad0562376da86bee4ab6097c546cc
F5: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp'
  declaration statement_id: sha256:6e455107e336f3d6977f59a532bc341a759522fedd448aa883c77865efa182f3
F6: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse
  declaration statement_id: sha256:18736e4b1629c6ccacac40723a79c65171780f9e9f6296b93251162549f27768
F7: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.moorePenroseInverse
  declaration statement_id: sha256:d0c42c7ebe852755b1e0ac182e1eba16a13f9d7bc80db23d35a6e897dc56df5a
F8: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.matrix_pairing
  declaration statement_id: sha256:bc7f3a1d092a6b296a75b0e9d5c7f8c0d2698b6b92d137a30a311713b8e68880
F9: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.vectorize
  declaration statement_id: sha256:965518d7298ad8acdfeb6d0b33fc04a6e526724592513da04e49a30b340e8ddb
F10: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration statement_id: sha256:70d3c448a772227785663f0117c0f159426907edd543b564aa470d834558dd8d
  current declaration statement_id: sha256:fa2079feef1191a452c3d4dbf8a1703c836eb544be648e3d7e26f7c50d152c41
F11: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration statement_id: sha256:e7d3fba989f8d1191d850ac68b17f943aea8d31ca3e6e460fb7f05749ab26485
  current declaration statement_id: sha256:76ab22395c4e18ba0d43115f458e8587cc482420784a2490c224e68f89700709
F12: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.PosDefOn
  declaration statement_id: sha256:9ca9d30055bd50eda8453689225e563d10cdccb3278a2b8225dc9957a0890cc7
F13: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigEquiv
  declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
F14: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigenvalues_eigEquiv
  declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
F15: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.hermForm
  declaration statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
F16: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.hermNegPart
  declaration statement_id: sha256:ad2a8390443bab24ec786ac6b42ded024195da37fd6d90578e441e73bf03e026
F17: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.negIndex
  declaration statement_id: sha256:b5905a543106ad41223ab3c0f6f31f7fb0632341c5e830350ec889bee1806429
F18: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.normSqMatrix
  declaration statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
F19: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
  declaration statement_id: sha256:10d84d7748c4e7f110f57a63c8faf31b2da6ecba24f5cdf67b5b36281d5a0757
F20: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.re_trace_mul_eq_eigenvalue_bilinear
  declaration statement_id: sha256:2f34172916d220c9b2829e523338125a57ebec289094c5be9cef75eb5b11ec2a
F21: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.rtrace
  declaration statement_id: sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F22: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.rtrace_specMap
  declaration statement_id: sha256:efa5f0bbdc4f0443275c16da086085a95c6f4e6395761aa1fadb48ed96f8ca46
F23: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap
  declaration statement_id: sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F24: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_1
  declaration statement_id: sha256:4505c32a9d334197dcdfbfe76a2b9041ae47c40d056e290040f762933ca6facf
F25: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_2
  declaration statement_id: sha256:71a8beda364a4cfc5bb497eb18cfcd54f8c12abc40e9a37962ca4f717d42c1e5
F26: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_id
  declaration statement_id: sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F27: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_isHermitian
  declaration statement_id: sha256:8eaaf395a5d8810c697d036c8729b5974aade8efbc4111a5132de5a598ab00b6
F28: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_mul
  declaration statement_id: sha256:7676c10505b22f0e9db5f08c8be82f86e9eb4db5a663554bc93b31c13a2aa6dc
F29: owner GID: D5/S3/Weil/ZetaLinear/RankTrace; declaration: RHLinalg.trace_mul_nonneg_of_posSemidef
  declaration statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Published owner references use the protected baseline private declaration identities.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
-/

import D5.S3.Quantum.Measurement.IncoherentCone
import D5.S3.Quantum.Measurement.LocallyPositiveSpectrum
import D5.S3.Weil.ZetaLinear.RankTrace

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram
open D5.S3.Quantum.Measurement.IncoherentCone
open D5.S3.Quantum.Measurement.LocallyPositiveSpectrum

section
variable {ι : Type*} [DecidableEq ι]

private theorem weighted_sqrt_sum_lower (s : Finset ι) (lam b : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, Real.sqrt (lam i)) ^ 2 ≤
      (∑ i ∈ s, b i * lam i) * (∑ i ∈ s, (b i)⁻¹) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (b i * lam i)) (fun i => Real.sqrt ((b i)⁻¹))
  have hs : (∑ i ∈ s, Real.sqrt (b i * lam i) * Real.sqrt ((b i)⁻¹)) =
      ∑ i ∈ s, Real.sqrt (lam i) := by
    apply sum_congr rfl
    intro i hi
    rw [← Real.sqrt_mul (mul_nonneg (hb i hi).le (hlam i hi))]
    congr 1
    field_simp [(hb i hi).ne']
  have hq1 : (∑ i ∈ s, Real.sqrt (b i * lam i) ^ 2) = ∑ i ∈ s, b i * lam i := by
    apply sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (mul_nonneg (hb i hi).le (hlam i hi))
  have hq2 : (∑ i ∈ s, Real.sqrt ((b i)⁻¹) ^ 2) = ∑ i ∈ s, (b i)⁻¹ := by
    apply sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (inv_nonneg.mpr (hb i hi).le)
  rw [hs, hq1, hq2] at hc
  exact hc

end

section
variable {n : ℕ}

def SpectralBalanced {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) : Prop :=
  ∀ j, Real.sqrt (hG.eigenvalues j) ≤
    ∑ i ∈ univ.erase j, Real.sqrt (hG.eigenvalues i)

end

section
variable {n : ℕ}

private theorem spectral_balanced_of_ordered {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosSemidef) (hn : 1 ≤ n)
    (hcond : Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0,by omega⟩) ≤
      ∑ i ∈ univ.erase (⟨0,by omega⟩ : Fin n), Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) i)) :
    SpectralBalanced hG.isHermitian := by
  intro j
  let z : Fin n := ⟨0,by omega⟩
  have hj : Real.sqrt (hG.isHermitian.eigenvalues j) ≤
      Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) z) := by
    apply Real.sqrt_le_sqrt
    have h := orderedSpectrum_antitone hG.isHermitian
      (show z ≤ (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).symm j by change (0 : ℕ) ≤ _;exact Nat.zero_le _)
    simpa [Equiv.trans_apply,z] using h
  have htotal : 2*Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) z) ≤
      ∑ i, Real.sqrt (hG.isHermitian.eigenvalues i) := by
    have hs := sum_erase_add (univ : Finset (Fin n))
      (fun i => Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) i)) (mem_univ z)
    rw [sum_orderedSpectrum hG.isHermitian Real.sqrt] at hs
    change Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) z) ≤ _ at hcond
    linarith
  have hs := sum_erase_add (univ : Finset (Fin n))
    (fun i => Real.sqrt (hG.isHermitian.eigenvalues i)) (mem_univ j)
  linarith

end

section
variable {n : ℕ}

private theorem bilinear_nonneg_of_permutations {a b : Fin n → ℝ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin n))
    (hp : ∀ σ : Equiv.Perm (Fin n), 0 ≤ ∑ k,a k*b (σ k)) :
    0 ≤ ∑ k,∑ l,a k*S k l*b l := by
  have hlhs : (∑ k,∑ l,a k*S k l*b l) = ∑ k,a k*(S *ᵥ b) k := by
    simp only [mulVec,dotProduct,mul_sum,mul_assoc]
  rw [hlhs]
  obtain ⟨w,hw,hws,heq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  rw [← heq]
  simp only [sum_mulVec,smul_mulVec,permMatrix_mulVec,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Function.comp_apply,mul_sum]
  rw [sum_comm]
  apply sum_nonneg
  intro σ _
  rw [show (∑ k,a k*(w σ*b (σ k)))=w σ*∑ k,a k*b (σ k) by
    rw [mul_sum];apply sum_congr rfl;intro k _;ring]
  exact mul_nonneg (hw σ) (hp σ)

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem spectral_dual_nonneg (s : Finset ι) (lam b : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hb : ∀ i ∈ s, 0 < b i)
    (lead a : ℝ) (ha : 0 < a)
    (hbudget : (∑ i ∈ s, (b i)⁻¹) ≤ a⁻¹)
    (hcondition : Real.sqrt lead ≤ ∑ i ∈ s, Real.sqrt (lam i)) :
    0 ≤ -a*lead + ∑ i ∈ s, b i * lam i := by
  have hw := weighted_sqrt_sum_lower s lam b hlam hb
  have hs : 0 ≤ ∑ i ∈ s, b i * lam i := sum_nonneg fun i hi =>
    mul_nonneg (hb i hi).le (hlam i hi)
  have htop : lead ≤ (∑ i ∈ s, Real.sqrt (lam i)) ^ 2 :=
    (Real.sqrt_le_iff.mp hcondition).2
  have hmul := mul_le_mul_of_nonneg_left hbudget hs
  have hprod : lead ≤ (∑ i ∈ s, b i * lam i) * a⁻¹ := htop.trans (hw.trans hmul)
  have hcancel : ((∑ i ∈ s, b i * lam i) * a⁻¹)*a = ∑ i ∈ s, b i * lam i := by
    field_simp
  have hfinal := mul_le_mul_of_nonneg_right hprod ha.le
  rw [hcancel] at hfinal
  nlinarith

end

section
variable {n : ℕ}

theorem spectral_balanced_pairing_nonneg (hn : 1 ≤ n)
    (G Y : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef)
    (hbal : SpectralBalanced hG.isHermitian) (hY : LocallyPsd Y) :
    RHLinalg.rtrace (G*Y) ≥ 0 := by
  cases n with
  | zero => omega
  | succ m =>
    by_cases hYP : Y.PosSemidef
    · exact RHLinalg.trace_mul_nonneg_of_posSemidef hG hYP
    have hp0 : ∃ p, hY.1.eigenvalues p < 0 := by
      by_contra! hh
      exact hYP (hY.1.posSemidef_iff_eigenvalues_nonneg.mpr hh)
    obtain ⟨p,hp⟩ := hp0
    obtain ⟨hpos,hbudget⟩ := local_psd_reciprocal_budget Y hY p hp
    let W := star (hG.isHermitian.eigenvectorUnitary : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) *
      (hY.1.eigenvectorUnitary : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
    have hW : W ∈ Matrix.unitaryGroup (Fin (m+1)) ℂ :=
      mul_mem (Unitary.star_mem hG.isHermitian.eigenvectorUnitary.2) hY.1.eigenvectorUnitary.2
    change 0 ≤ RCLike.re (G*Y).trace
    rw [RHLinalg.re_trace_mul_eq_eigenvalue_bilinear hG.isHermitian hY.1]
    apply bilinear_nonneg_of_permutations (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hW)
    intro σ
    let q := σ.symm p
    have hb : ∀ i ∈ univ.erase q, 0 < hY.1.eigenvalues (σ i) := by
      intro i hi
      apply hpos
      intro he
      have : i=q := by dsimp [q];rw [← he,Equiv.symm_apply_apply]
      exact (mem_erase.mp hi).1 this
    have hbeq : (∑ i ∈ univ.erase q, (hY.1.eigenvalues (σ i))⁻¹) =
        ∑ i ∈ univ.erase p, (hY.1.eigenvalues i)⁻¹ := by
      apply sum_nbij' σ σ.symm
      · intro i hi
        simp only [mem_erase,mem_univ,and_true] at hi ⊢
        intro he;apply hi;dsimp [q];rw [← he,Equiv.symm_apply_apply]
      · intro i hi
        simp only [mem_erase,mem_univ,and_true] at hi ⊢
        intro he;apply hi
        have := congrArg σ he
        simpa [q] using this
      · intro i _;exact σ.symm_apply_apply i
      · intro i _;exact σ.apply_symm_apply i
      · intro i _;rfl
    have hs := spectral_dual_nonneg (univ.erase q) hG.isHermitian.eigenvalues
      (fun i => hY.1.eigenvalues (σ i)) (fun i _ => hG.eigenvalues_nonneg i) hb
      (hG.isHermitian.eigenvalues q) (-hY.1.eigenvalues p) (neg_pos.mpr hp)
      (by rw [hbeq];exact hbudget) (hbal q)
    rw [← sum_erase_add _ _ (mem_univ q)]
    have hq : σ q=p := σ.apply_symm_apply p
    rw [hq]
    simpa only [neg_neg,mul_comm,add_comm] using hs

end

section
variable {n d : ℕ}

private theorem spectral_balanced_incoherent (hn : 1 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef)
    (hbal : SpectralBalanced hG.isHermitian) : IsIncoherent G := by
  by_contra hnot
  obtain ⟨Y,hY,hneg⟩ := incoherent_separation G hG.isHermitian hnot
  exact hneg.not_ge (spectral_balanced_pairing_nonneg hn G Y hG hbal hY)

end

section
variable {n d : ℕ}

private theorem spectral_sufficient_incoherent (hn : 2 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef)
    (hcond : Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0,by omega⟩) ≤
      ∑ i ∈ univ.erase (⟨0,by omega⟩ : Fin n), Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) i)) :
    IsIncoherent G := by
  exact spectral_balanced_incoherent (by omega) G hG
    (spectral_balanced_of_ordered hG (by omega) hcond)

end

section
variable {n d : ℕ}

theorem spectral_sufficient_antidistinguishable (hn : 2 ≤ n)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hcond : Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0,by omega⟩) ≤
      ∑ i ∈ univ.erase (⟨0,by omega⟩ : Fin n),
        Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) i)) :
    IsAntidistinguishable ψ := by
  apply incoherent_gram_antidistinguishable (by omega)
  exact spectral_sufficient_incoherent hn ((Matrix.gram ℂ ψ)) (gramPsd ψ) hcond

end

end
end D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
