/- GID: D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.claim; result=D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result; claim=D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.claim
   digest: Selective LOCC increases Shirokov's Moreau-Yosida entanglement of formation. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#11557; Refuted)
Direct frozen dependencies (owner-module pins):
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    (statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5).
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
    (statement_id: sha256:ec2ace26dd8d3b1f1b18defca9f881e75ab25f3e1a67abd2b14cdc72e2702569).
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
    (statement_id: sha256:3487611db943d93cce4a86af60f6499c8a001bc73fe819953d9bfd08a4e811b1).
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le
    (statement_id: sha256:3db8d0cc1aa28c78624e69d989ca938ee9442b2409e1ba0ba39d593ce49d5512).
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg
    (statement_id: sha256:d7a81ef774c91a733d963a18aa1a998fd412bb6e352db4f96b70ec875b1b00ec).
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef
    (statement_id: sha256:f9f5b54d2f389f80229204551ad9217b56fb75ef8f081925f568f00cccca0db8).
  D5/S3/Resource/CompositeConeDuality.CompositeMatrix
    (statement_id: sha256:7a29fd6ddedc893a8299b05b64f937d370c58bd2bf2a55f00650bc8c2716be7f).
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    (statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3).
  D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState
    (statement_id: sha256:3f0325bbd16e53be1d3f66e42df64a5e4d0d1a72062a3e81b05aa51a01c3d6d6).
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
    (statement_id: sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7).
  D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy
    (statement_id: sha256:9cf1e21822d8f3f61a5d349f41c4287a3ef43a0e8a600534b28ab8d06f437cd1).
  D5/S3/Quantum/Information/InputInformationBalance.entropy_eq_sum
    (statement_id: sha256:655056efc1d061df5e496e03f8a5d0cee21724e63d0432d939650c1cc0d461ae).
  D5/S3/Quantum/Reduction/IsometricCompression.support
    (statement_id: sha256:51c93b150f99dbe2204f83e7a5e419d5482256fcf3f69999b00e3c68b5030706).
  D5/S3/Entropy/MaxEntropy.shannonEntropy
    (statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87).
The explicit local projective protocol and affine estimates use the existing
spectral, logarithm and trace-norm results with finite algebraic certificates.
Information-escape registration is paused under CLAUDE.md §3.9
「信息逃逸登记暂缓」.
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Resource.CompositeConeDuality
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.InputInformationBalance
import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.Reduction.IsometricCompression
import D5.S3.Entropy.MaxEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Resource.CompositeConeDuality
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Reduction.IsometricCompression
open D5.S3.Entropy.MaxEntropy
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
namespace D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation
abbrev Coeff (a b : ℕ) := Matrix (Fin a) (Fin b) ℂ
def mass {a b : ℕ} (M : Coeff a b) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)
abbrev Pure (a b : ℕ) := {M : Coeff a b // mass M = 1}
structure Ensemble {a b : ℕ} (N : ℕ) (ρ : DensityState (Fin a × Fin b)) where
  p : Fin N → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i, p i = 1
  ψ : Fin N → Pure a b
  average : ∑ i, (p i : ℂ) • rankOneDensity (fun x => (ψ i).val x.1 x.2) = CStarMatrix.ofMatrix.symm ρ.val

def cost {a b N : ℕ} {ρ : DensityState (Fin a × Fin b)} (e : Ensemble N ρ) : ℝ :=
  ∑ i, e.p i * vonNeumannEntropy (marginalRight
    (pureDensityState (fun x => (e.ψ i).val x.1 x.2) (by
      simpa [dotProduct, Fintype.sum_prod_type, Complex.mul_conj, mul_comm, mass]
        using congrArg (fun r : ℝ => (r : ℂ)) (e.ψ i).property)))

def E_F {a b : ℕ} (ρ : DensityState (Fin a × Fin b)) : ENNReal :=
  ⨅ N, ⨅ e : Ensemble N ρ, ENNReal.ofReal (cost e)

def E_F_my {a b : ℕ} (lam : ℝ) (ρ : DensityState (Fin a × Fin b)) : ENNReal :=
  ⨅ σ : DensityState (Fin a × Fin b), E_F σ + ENNReal.ofReal
    (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm ((CStarMatrix.ofMatrix.symm ρ.val)-(CStarMatrix.ofMatrix.symm σ.val)) / (2*lam))

-- Finite Kraus instruments permit several Kraus operators for the same classical outcome.
structure LocalInstrument (d : ℕ) where
  outcomes : ℕ
  krausCount : Fin outcomes → ℕ
  K : (i : Fin outcomes) → Fin (krausCount i) → Matrix (Fin d) (Fin d) ℂ
  complete : ∑ i, ∑ j, (K i j)ᴴ * K i j = 1

-- A tree describes alternating local instruments with complete classical outcome history.
inductive Protocol (a b : ℕ) where
  | done
  | alice (I : LocalInstrument a) (next : Fin I.outcomes → Protocol a b)
  | bob (I : LocalInstrument b) (next : Fin I.outcomes → Protocol a b)

def branchList {a b : ℕ} : Protocol a b → CompositeMatrix a b → List (CompositeMatrix a b)
  | .done, ρ => [ρ]
  | .alice I next, ρ => (List.finRange I.outcomes).flatMap fun i =>
      branchList (next i) (∑ j, Matrix.kronecker (I.K i j) (1 : Matrix (Fin b) (Fin b) ℂ) * ρ *
        (Matrix.kronecker (I.K i j) (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ)
  | .bob I next, ρ => (List.finRange I.outcomes).flatMap fun i =>
      branchList (next i) (∑ j, Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (I.K i j) * ρ *
        (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (I.K i j))ᴴ)

-- Zero-probability outputs may be assigned any normalized state.
def claim : Prop := ∀ (a b : ℕ), 0 < a → 0 < b →
  ∀ lam : ℝ, 0 < lam → ∀ ρ : DensityState (Fin a × Fin b), ∀ T : Protocol a b,
  ∀ (N : ℕ) (p : Fin N → ℝ) (out : Fin N → DensityState (Fin a × Fin b)),
    (∀ i, 0 ≤ p i) →
    (∑ i, p i = 1) →
    branchList T (CStarMatrix.ofMatrix.symm ρ.val) = (List.finRange N).map (fun i => (p i : ℂ) • CStarMatrix.ofMatrix.symm (out i).val) →
    (∑ i, ENNReal.ofReal (p i) * E_F_my lam (out i)) ≤ E_F_my lam ρ


private def v2 (x : Fin 5 × Fin 3) : ℂ := if (x.1.val=0 ∧ x.2.val=0) ∨ (x.1.val=1 ∧ x.2.val=1) then 1 else 0
private def v3 (x : Fin 5 × Fin 3) : ℂ := if (x.1.val=2 ∧ x.2.val=0) ∨ (x.1.val=3 ∧ x.2.val=1) ∨ (x.1.val=4 ∧ x.2.val=2) then 1 else 0
private def phi2 : DensityState (Fin 5 × Fin 3) := by
  refine ⟨CStarMatrix.ofMatrix ((1/2 : ℂ) • rankOneDensity v2), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.posSemidef_vecMulVec_self_star v2).smul (by norm_num [Complex.nonneg_iff])).nonneg
  · change Matrix.trace ((1/2 : ℂ) • rankOneDensity v2) = 1
    norm_num [rankOneDensity, v2, Matrix.trace, Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.val_succ]
private def phi3 : DensityState (Fin 5 × Fin 3) := by
  refine ⟨CStarMatrix.ofMatrix ((1/3 : ℂ) • rankOneDensity v3), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.posSemidef_vecMulVec_self_star v3).smul (by norm_num [Complex.nonneg_iff])).nonneg
  · change Matrix.trace ((1/3 : ℂ) • rankOneDensity v3) = 1
    norm_num [rankOneDensity, v3, Matrix.trace, Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.val_succ]
private def omega : DensityState (Fin 5 × Fin 3) := by
  refine ⟨CStarMatrix.ofMatrix ((1/2 : ℂ) • ((CStarMatrix.ofMatrix.symm phi2.val) + (CStarMatrix.ofMatrix.symm phi3.val))), ?_, ?_⟩
  · have h2 : (CStarMatrix.ofMatrix.symm phi2.val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm phi2.property.1)
    have h3 : (CStarMatrix.ofMatrix.symm phi3.val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm phi3.property.1)
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((h2.add h3).smul (by norm_num [Complex.nonneg_iff])).nonneg
  · change Matrix.trace ((1/2 : ℂ) • ((CStarMatrix.ofMatrix.symm phi2.val) + (CStarMatrix.ofMatrix.symm phi3.val))) = 1
    rw [Matrix.trace_smul, Matrix.trace_add]
    have ht2 : ((CStarMatrix.ofMatrix.symm phi2.val)).trace = 1 := phi2.property.2
    have ht3 : ((CStarMatrix.ofMatrix.symm phi3.val)).trace = 1 := phi3.property.2
    rw [ht2, ht3]
    norm_num


private def productCoeff (k : Fin 2) (i : Fin 5) (j : Fin 3) : ℂ :=
  if i.val=k.val ∧ j.val=k.val then 1 else 0

private def productPure (k : Fin 2) : Pure 5 3 := by
  refine ⟨productCoeff k, ?_⟩
  simp only [mass, Fin.sum_univ_succ]
  fin_cases k <;> norm_num [productCoeff]

private def sigma : DensityState (Fin 5 × Fin 3) := by
  refine ⟨CStarMatrix.ofMatrix ((1/2 : ℂ) • (rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 0 x.1 x.2)+rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 1 x.1 x.2))), ?_, ?_⟩
  · have h0 : (rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 0 x.1 x.2)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star (fun x : Fin 5 × Fin 3 => productCoeff 0 x.1 x.2)
    have h1 : (rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 1 x.1 x.2)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star (fun x : Fin 5 × Fin 3 => productCoeff 1 x.1 x.2)
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv ((h0.add h1).smul (by norm_num [Complex.nonneg_iff])).nonneg
  · change Matrix.trace ((1/2 : ℂ) • (rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 0 x.1 x.2)+rankOneDensity (fun x : Fin 5 × Fin 3 => productCoeff 1 x.1 x.2))) = 1
    norm_num [rankOneDensity,productCoeff,Matrix.trace,Matrix.vecMulVec,
      Fintype.sum_prod_type,Fin.sum_univ_succ]

private def separableEnsemble : Ensemble 2 sigma where
  p := fun _ => 1/2
  p_nonneg := by intro i; norm_num
  p_sum := by norm_num [Fin.sum_univ_succ]
  ψ := productPure
  average := by
    simp [Fin.sum_univ_succ,productPure,sigma]


private def vMinus (x : Fin 5 × Fin 3) : ℂ :=
  if x.1.val=0 ∧ x.2.val=0 then 1 else if x.1.val=1 ∧ x.2.val=1 then -1 else 0


private def PA : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (fun i => if i.val < 2 then 1 else 0)
private def witnessInstrument : LocalInstrument 5 where
  outcomes := 2
  krausCount := fun _ => 1
  K := fun i _ => if i.val=0 then PA else 1-PA
  complete := by
    have hPstar : PAᴴ = PA := by simp [PA]
    have hP2 : PA*PA=PA := by
      rw [PA,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    simp [Fin.sum_univ_succ,hPstar,sub_mul,mul_sub,hP2]

private def witnessProtocol : Protocol 5 3 := .alice witnessInstrument (fun _ => .done)

private def minor {a b : ℕ} (M : Coeff a b) (i k : Fin a) (j l : Fin b) : ℂ :=
  M i j * M k l - M i l * M k j

private def minors (M : Coeff 5 3) : ℝ := ∑ i, ∑ k, ∑ j, ∑ l,
  if i < k ∧ j < l then Complex.normSq (minor M i k j l) else 0



open D5.S3.Quantum.Foundation.FiniteTraceDistance

private def fidelity (P S : CompositeMatrix 5 3) : ℝ := (P*S).trace.re

theorem result : ¬ claim := by
  have hCostSpectral {a b N : ℕ} {ρ : DensityState (Fin a × Fin b)}
      (e : Ensemble N ρ) : cost e =
        ∑ i, e.p i * shannonEntropy
          (Matrix.isHermitian_mul_conjTranspose_self (e.ψ i).val).eigenvalues := by
    unfold cost
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [entropy_eq_sum]
    rfl
  have hAffine (M : Coeff 5 3) (hm : mass M = 1) :
      (3/10 : ℝ) * (Complex.normSq (M 0 0 + M 1 1)/2 - 11/20) ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues ∧
      (3/10 : ℝ) * (Complex.normSq (M 2 0 + M 3 1 + M 4 2)/3 - 2/5) ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues := by
    have hentropy : 1 - (support M * support M).trace.re ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues := by
      let G := support M
      let hG := Matrix.isHermitian_mul_conjTranspose_self M
      have htr : G.trace.re = 1 := by
        have hPartial : (fun i k => ∑ j, rankOneDensity (fun x => M x.1 x.2) (i,j) (k,j)) = G := by rfl
        rw [← hPartial]
        change (∑ i, ∑ j, M i j * star (M i j)).re = 1
        simpa [mass, Complex.re_sum, Complex.mul_conj] using hm
      have hsum : ∑ i, hG.eigenvalues i = 1 := by
        have ht := congrArg Complex.re hG.trace_eq_sum_eigenvalues
        have hs : ∑ i, hG.eigenvalues i = G.trace.re := by
          simpa [G, support] using ht.symm
        exact hs.trans htr
      have hpos (i : Fin 5) : 0 ≤ hG.eigenvalues i :=
        (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg i
      have hquad : (G * G).trace.re = ∑ i, (hG.eigenvalues i)^2 := by
        let U := hG.eigenvectorUnitary
        let D : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (fun i => (hG.eigenvalues i : ℂ))
        have hs : G = (U : Matrix (Fin 5) (Fin 5) ℂ) * D * star U := hG.spectral_theorem
        change G = (U : Matrix (Fin 5) (Fin 5) ℂ) * D * star (U : Matrix (Fin 5) (Fin 5) ℂ) at hs
        have hu : star (U : Matrix (Fin 5) (Fin 5) ℂ) * U = 1 := Unitary.coe_star_mul_self U
        have hGG : G * G = (U : Matrix (Fin 5) (Fin 5) ℂ) * (D * D) * star U := by
          calc
            G * G = (U : Matrix (Fin 5) (Fin 5) ℂ) * D *
              (star (U : Matrix (Fin 5) (Fin 5) ℂ) * U) * D * star U := by
                rw [hs]
                noncomm_ring
            _ = _ := by rw [hu]; noncomm_ring
        change G * G = (U : Matrix (Fin 5) (Fin 5) ℂ) * (D * D) * star (U : Matrix (Fin 5) (Fin 5) ℂ) at hGG
        rw [hGG, Matrix.trace_mul_comm]
        rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
        simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace, Complex.re_sum, pow_two]
      have hlog (i : Fin 5) : hG.eigenvalues i - (hG.eigenvalues i)^2 ≤
          Real.negMulLog (hG.eigenvalues i) := by
        by_cases hz : hG.eigenvalues i = 0
        · simp [hz]
        · have hp : 0 < hG.eigenvalues i := lt_of_le_of_ne (hpos i) (Ne.symm hz)
          have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) (hpos i)
          simp only [Real.negMulLog_def]
          nlinarith
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlog i)
      change 1 - (G * G).trace.re ≤ ∑ i, Real.negMulLog (hG.eigenvalues i)
      rw [hquad]
      rw [Finset.sum_sub_distrib, hsum] at this
      linarith
    have hId : mass M ^ 2 - (support M * support M).trace.re = 2 * minors M := by
      have hRow (i k : Fin 5) :
          (∑ j, Complex.normSq (M i j)) * (∑ j, Complex.normSq (M k j)) -
          Complex.normSq (∑ j, M i j * star (M k j)) =
          ∑ j : Fin 3, ∑ l : Fin 3,
            if j < l then Complex.normSq (minor M i k j l) else 0 := by
        simp [minor, Fin.sum_univ_succ, Complex.normSq, Complex.mul_re, Complex.mul_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.conj_re, Complex.conj_im]
        ring
      have hTrace : (support M * support M).trace.re =
          ∑ i, ∑ k, Complex.normSq (∑ j, M i j * star (M k j)) := by
        change (∑ i, ∑ k, support M i k * support M k i).re = _
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hstar : support M k i = star (support M i k) :=
          (Matrix.isHermitian_mul_conjTranspose_self M).apply k i |>.symm
        rw [hstar]
        change ((∑ j, M i j * star (M k j)) * star (∑ j, M i j * star (M k j))).re = _
        simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      have hMass : mass M ^ 2 =
          ∑ i, ∑ k, (∑ j, Complex.normSq (M i j)) * (∑ j, Complex.normSq (M k j)) := by
        unfold mass
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      rw [hMass, hTrace, ← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib, hRow]
      have hSwap (i k : Fin 5) (j l : Fin 3) :
          Complex.normSq (minor M k i j l) = Complex.normSq (minor M i k j l) := by
        have he : minor M k i j l = -minor M i k j l := by unfold minor; ring
        rw [he, Complex.normSq_neg]
      have hDiag (i : Fin 5) (j l : Fin 3) : minor M i i j l = 0 := by unfold minor; ring
      simp only [minors, Fin.sum_univ_succ]
      simp [hDiag, hSwap, Complex.normSq_zero]
      ring
    have hpair (a b c d : ℂ) :
        Complex.normSq (a + d) ≤ Complex.normSq a + Complex.normSq b +
          Complex.normSq c + Complex.normSq d + 2 * ‖a*d-b*c‖ := by
      have htriangle : ‖a*d‖ ≤ ‖a*d-b*c‖ + ‖b*c‖ := by
        calc
          ‖a*d‖ = ‖(a*d-b*c)+b*c‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have hadd : ‖a+d‖^2 ≤ (‖a‖+‖d‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      simp only [norm_mul] at htriangle
      simp only [Complex.normSq_eq_norm_sq]
      nlinarith [sq_nonneg (‖b‖-‖c‖)]
    have htriple (a b c d e f g h i : ℂ) :
        Complex.normSq (a+e+i) ≤
          Complex.normSq a + Complex.normSq b + Complex.normSq c +
          Complex.normSq d + Complex.normSq e + Complex.normSq f +
          Complex.normSq g + Complex.normSq h + Complex.normSq i +
          2*(‖a*e-b*d‖+‖a*i-c*g‖+‖e*i-f*h‖) := by
      have ht (x y u v : ℂ) : ‖x*y‖ ≤ ‖x*y-u*v‖+‖u*v‖ := by
        calc
          ‖x*y‖ = ‖(x*y-u*v)+u*v‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have h1 := ht a e b d
      have h2 := ht a i c g
      have h3 := ht e i f h
      simp only [norm_mul] at h1 h2 h3
      have hadd : ‖a+e+i‖ ≤ ‖a‖+‖e‖+‖i‖ := by
        calc
          ‖a+e+i‖ ≤ ‖a+e‖+‖i‖ := norm_add_le _ _
          _ ≤ _ := by linarith [norm_add_le a e]
      have hadd2 := pow_le_pow_left₀ (norm_nonneg _) hadd 2
      simp only [Complex.normSq_eq_norm_sq]
      nlinarith [sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖g‖),sq_nonneg (‖f‖-‖h‖)]
    have hminor2 : 2 * (‖minor M 0 1 0 1‖^2) ≤ 1 - (support M * support M).trace.re := by
      rw [hm] at hId
      simp [minors, Fin.sum_univ_succ, Complex.normSq_eq_norm_sq] at hId
      nlinarith only [hId,
        sq_nonneg ‖minor M 0 1 0 2‖,
        sq_nonneg ‖minor M 0 1 1 2‖,
        sq_nonneg ‖minor M 0 2 0 1‖,
        sq_nonneg ‖minor M 0 2 0 2‖,
        sq_nonneg ‖minor M 0 2 1 2‖,
        sq_nonneg ‖minor M 0 3 0 1‖,
        sq_nonneg ‖minor M 0 3 0 2‖,
        sq_nonneg ‖minor M 0 3 1 2‖,
        sq_nonneg ‖minor M 0 4 0 1‖,
        sq_nonneg ‖minor M 0 4 0 2‖,
        sq_nonneg ‖minor M 0 4 1 2‖,
        sq_nonneg ‖minor M 1 2 0 1‖,
        sq_nonneg ‖minor M 1 2 0 2‖,
        sq_nonneg ‖minor M 1 2 1 2‖,
        sq_nonneg ‖minor M 1 3 0 1‖,
        sq_nonneg ‖minor M 1 3 0 2‖,
        sq_nonneg ‖minor M 1 3 1 2‖,
        sq_nonneg ‖minor M 1 4 0 1‖,
        sq_nonneg ‖minor M 1 4 0 2‖,
        sq_nonneg ‖minor M 1 4 1 2‖,
        sq_nonneg ‖minor M 2 3 0 1‖,
        sq_nonneg ‖minor M 2 3 0 2‖,
        sq_nonneg ‖minor M 2 3 1 2‖,
        sq_nonneg ‖minor M 2 4 0 1‖,
        sq_nonneg ‖minor M 2 4 0 2‖,
        sq_nonneg ‖minor M 2 4 1 2‖,
        sq_nonneg ‖minor M 3 4 0 1‖,
        sq_nonneg ‖minor M 3 4 0 2‖,
        sq_nonneg ‖minor M 3 4 1 2‖]
    have hminor3 : 2 * (‖minor M 2 3 0 1‖^2 + ‖minor M 2 4 0 2‖^2 + ‖minor M 3 4 1 2‖^2) ≤ 1 - (support M * support M).trace.re := by
      rw [hm] at hId
      simp [minors, Fin.sum_univ_succ, Complex.normSq_eq_norm_sq] at hId
      nlinarith only [hId,
        sq_nonneg ‖minor M 0 1 0 1‖,
        sq_nonneg ‖minor M 0 1 0 2‖,
        sq_nonneg ‖minor M 0 1 1 2‖,
        sq_nonneg ‖minor M 0 2 0 1‖,
        sq_nonneg ‖minor M 0 2 0 2‖,
        sq_nonneg ‖minor M 0 2 1 2‖,
        sq_nonneg ‖minor M 0 3 0 1‖,
        sq_nonneg ‖minor M 0 3 0 2‖,
        sq_nonneg ‖minor M 0 3 1 2‖,
        sq_nonneg ‖minor M 0 4 0 1‖,
        sq_nonneg ‖minor M 0 4 0 2‖,
        sq_nonneg ‖minor M 0 4 1 2‖,
        sq_nonneg ‖minor M 1 2 0 1‖,
        sq_nonneg ‖minor M 1 2 0 2‖,
        sq_nonneg ‖minor M 1 2 1 2‖,
        sq_nonneg ‖minor M 1 3 0 1‖,
        sq_nonneg ‖minor M 1 3 0 2‖,
        sq_nonneg ‖minor M 1 3 1 2‖,
        sq_nonneg ‖minor M 1 4 0 1‖,
        sq_nonneg ‖minor M 1 4 0 2‖,
        sq_nonneg ‖minor M 1 4 1 2‖,
        sq_nonneg ‖minor M 2 3 0 2‖,
        sq_nonneg ‖minor M 2 3 1 2‖,
        sq_nonneg ‖minor M 2 4 0 1‖,
        sq_nonneg ‖minor M 2 4 1 2‖,
        sq_nonneg ‖minor M 3 4 0 1‖,
        sq_nonneg ‖minor M 3 4 0 2‖]
    have hmass2 : Complex.normSq (M 0 0) + Complex.normSq (M 0 1) + Complex.normSq (M 1 0) + Complex.normSq (M 1 1) ≤ 1 := by
      simp [mass, Fin.sum_univ_succ] at hm
      nlinarith only [hm, Complex.normSq_nonneg (M 0 2), Complex.normSq_nonneg (M 1 2), Complex.normSq_nonneg (M 2 0), Complex.normSq_nonneg (M 2 1), Complex.normSq_nonneg (M 2 2), Complex.normSq_nonneg (M 3 0), Complex.normSq_nonneg (M 3 1), Complex.normSq_nonneg (M 3 2), Complex.normSq_nonneg (M 4 0), Complex.normSq_nonneg (M 4 1), Complex.normSq_nonneg (M 4 2)]
    have hmass3 : Complex.normSq (M 2 0) + Complex.normSq (M 2 1) + Complex.normSq (M 2 2) + Complex.normSq (M 3 0) + Complex.normSq (M 3 1) + Complex.normSq (M 3 2) + Complex.normSq (M 4 0) + Complex.normSq (M 4 1) + Complex.normSq (M 4 2) ≤ 1 := by
      simp [mass, Fin.sum_univ_succ] at hm
      nlinarith only [hm, Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 0 1), Complex.normSq_nonneg (M 0 2), Complex.normSq_nonneg (M 1 0), Complex.normSq_nonneg (M 1 1), Complex.normSq_nonneg (M 1 2)]
    constructor
    · have hp := hpair (M 0 0) (M 0 1) (M 1 0) (M 1 1)
      change Complex.normSq (M 0 0 + M 1 1) ≤ _ + 2 * ‖minor M 0 1 0 1‖ at hp
      nlinarith [sq_nonneg (‖minor M 0 1 0 1‖ - 3/40)]
    · have hp := htriple (M 2 0) (M 2 1) (M 2 2) (M 3 0) (M 3 1) (M 3 2)
          (M 4 0) (M 4 1) (M 4 2)
      change Complex.normSq (M 2 0 + M 3 1 + M 4 2) ≤ _ +
        2*(‖minor M 2 3 0 1‖+‖minor M 2 4 0 2‖+‖minor M 3 4 1 2‖) at hp
      nlinarith [sq_nonneg (‖minor M 2 3 0 1‖-‖minor M 2 4 0 2‖),
        sq_nonneg (‖minor M 2 3 0 1‖-‖minor M 3 4 1 2‖),
        sq_nonneg (‖minor M 2 4 0 2‖-‖minor M 3 4 1 2‖),
        sq_nonneg (‖minor M 2 3 0 1‖+‖minor M 2 4 0 2‖+‖minor M 3 4 1 2‖-3/20)]
  intro hclaim
  have hEntropyNN (M : Pure 5 3) : 0 ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M.val).eigenvalues := by
    let hG := Matrix.isHermitian_mul_conjTranspose_self M.val
    have htr : (support M.val).trace.re = 1 := by
      simpa [support, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        map_sum, Complex.mul_conj, mass] using M.property
    have hsum : ∑ i, hG.eigenvalues i = 1 := by
      have ht := congrArg Complex.re hG.trace_eq_sum_eigenvalues
      have hs : ∑ i, hG.eigenvalues i = (support M.val).trace.re := by
        simpa [support] using ht.symm
      exact hs.trans htr
    have hpos (i : Fin 5) : 0 ≤ hG.eigenvalues i :=
      (Matrix.posSemidef_self_mul_conjTranspose M.val).eigenvalues_nonneg i
    apply Finset.sum_nonneg
    intro i hi
    have hle : hG.eigenvalues i ≤ 1 := by
      have ht := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hpos j) (Finset.mem_univ i)
      rwa [hsum] at ht
    exact Real.negMulLog_nonneg (hpos i) hle
  have hP2 : (CStarMatrix.ofMatrix.symm phi2.val)*(CStarMatrix.ofMatrix.symm phi2.val)=(CStarMatrix.ofMatrix.symm phi2.val) := by
    simp [phi2,rankOneDensity,smul_mul_assoc,mul_smul_comm,Matrix.vecMulVec_mul_vecMulVec,
      dotProduct,v2,Fintype.sum_prod_type,Fin.sum_univ_succ]
    module
  have hP3 : (CStarMatrix.ofMatrix.symm phi3.val)*(CStarMatrix.ofMatrix.symm phi3.val)=(CStarMatrix.ofMatrix.symm phi3.val) := by
    simp [phi3,rankOneDensity,smul_mul_assoc,mul_smul_comm,Matrix.vecMulVec_mul_vecMulVec,
      dotProduct,v3,Fintype.sum_prod_type,Fin.sum_univ_succ]
    module
  have hF2 (M : Coeff 5 3) : fidelity (CStarMatrix.ofMatrix.symm phi2.val) (rankOneDensity (fun x => M x.1 x.2)) = Complex.normSq (M 0 0 + M 1 1)/2 := by
    unfold fidelity
    simp [phi2,rankOneDensity,smul_mul_assoc,Matrix.vecMulVec_mul_vecMulVec,
      Matrix.trace_smul,Matrix.trace_vecMulVec,dotProduct,v2,Fintype.sum_prod_type,
      Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im,Complex.normSq,
      Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im]
    ring
  have hF3 (M : Coeff 5 3) : fidelity (CStarMatrix.ofMatrix.symm phi3.val) (rankOneDensity (fun x => M x.1 x.2)) = Complex.normSq (M 2 0 + M 3 1 + M 4 2)/3 := by
    unfold fidelity
    simp [phi3,rankOneDensity,smul_mul_assoc,Matrix.vecMulVec_mul_vecMulVec,
      Matrix.trace_smul,Matrix.trace_vecMulVec,dotProduct,v3,Fintype.sum_prod_type,
      Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im,Complex.normSq,
      Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im]
    ring
  have hPure2 (M : Pure 5 3) : (2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm phi2.val) (rankOneDensity (fun x => M.val x.1 x.2))-11/20) ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M.val).eigenvalues := by
    rw [hF2]
    have ha := (hAffine M.val M.property).1
    have hn := hEntropyNN M
    by_cases h : 0 ≤ Complex.normSq (M.val 0 0+M.val 1 1)/2 - 11/20
    · nlinarith
    · nlinarith
  have hPure3 (M : Pure 5 3) : (2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm phi3.val) (rankOneDensity (fun x => M.val x.1 x.2))-2/5) ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M.val).eigenvalues := by
    rw [hF3]
    have ha := (hAffine M.val M.property).2
    have hn := hEntropyNN M
    by_cases h : 0 ≤ Complex.normSq (M.val 2 0+M.val 3 1+M.val 4 2)/3 - 2/5
    · nlinarith
    · nlinarith

  have hTrace (P S : DensityState (Fin 5 × Fin 3)) (hproj : (CStarMatrix.ofMatrix.symm P.val)*(CStarMatrix.ofMatrix.symm P.val)=(CStarMatrix.ofMatrix.symm P.val)) :
      2*(1-fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)) ≤ traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val)) := by
    have hPpos : (CStarMatrix.ofMatrix.symm P.val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm P.property.1)
    let hP := hPpos.isHermitian
    have htrP := P.property.2
    change Matrix.trace (CStarMatrix.ofMatrix.symm P.val) = 1 at htrP
    have htrS := S.property.2
    change Matrix.trace (CStarMatrix.ofMatrix.symm S.val) = 1 at htrS
    let R := (2 : ℂ) • (CStarMatrix.ofMatrix.symm P.val) - 1
    have hRstar : Rᴴ = R := by simp [R, hP.eq]
    have hR2 : R*R=1 := by
      dsimp [R]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
        Matrix.one_mul, Matrix.mul_one]
      rw [hproj]
      module
    let U : Matrix.unitaryGroup (Fin 5 × Fin 3) ℂ := ⟨R, by
      change Rᴴ*R=1 ∧ R*Rᴴ=1
      rw [hRstar]
      exact ⟨hR2,hR2⟩⟩
    have h := (traceNorm_eq_max_re_tr_U ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))).right ⟨U,rfl⟩
    have htrace : (R*((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))).trace.re = 2*(1-((CStarMatrix.ofMatrix.symm P.val)*(CStarMatrix.ofMatrix.symm S.val)).trace.re) := by
      simp [R,sub_mul,mul_sub,smul_mul_assoc,Matrix.trace_sub,Matrix.trace_smul,
        hproj,htrP,htrS,Complex.mul_re]
    change (R*((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))).trace.re ≤ _ at h
    simpa only [htrace, fidelity] using h
  have hLower (P : DensityState (Fin 5 × Fin 3)) (f : ℝ)
      (hPure : ∀ M : Pure 5 3, (2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (rankOneDensity (fun x => M.val x.1 x.2))-f) ≤ shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M.val).eigenvalues)
      (hproj : (CStarMatrix.ofMatrix.symm P.val)*(CStarMatrix.ofMatrix.symm P.val)=(CStarMatrix.ofMatrix.symm P.val)) :
      ENNReal.ofReal ((2/7 : ℝ)*(1-f)) ≤ E_F_my (7/2) P := by
    unfold E_F_my
    refine le_iInf fun S => ?_
    have hEF : ENNReal.ofReal ((2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)-f)) ≤ E_F S := by
      unfold E_F
      refine le_iInf fun N => le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
      have hF : fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val) = ∑ i, e.p i * fidelity (CStarMatrix.ofMatrix.symm P.val) (rankOneDensity (fun x => (e.ψ i).val x.1 x.2)) := by
        unfold fidelity
        rw [← e.average, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        simp [mul_smul_comm, Matrix.trace_smul, Complex.mul_re]
      have hsum : (2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)-f) =
          ∑ i, e.p i*((2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (rankOneDensity (fun x => (e.ψ i).val x.1 x.2))-f)) := by
        have heach (i : Fin N) : e.p i*((2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (rankOneDensity (fun x => (e.ψ i).val x.1 x.2))-f)) =
            (2/7 : ℝ)*(e.p i*fidelity (CStarMatrix.ofMatrix.symm P.val) (rankOneDensity (fun x => (e.ψ i).val x.1 x.2))) - ((2/7 : ℝ)*f)*e.p i := by ring
        simp_rw [heach]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e.p_sum, hF]
        ring
      rw [hsum]
      rw [hCostSpectral]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hPure (e.ψ i)) (e.p_nonneg i))
    have hp : (2/7 : ℝ)*(1-fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)) ≤ traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))/7 := by
      linarith [hTrace P S hproj]
    have harith : (2/7 : ℝ)*(1-f) ≤
        (2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)-f) + traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))/7 := by linarith
    calc
      ENNReal.ofReal ((2/7 : ℝ)*(1-f)) ≤ ENNReal.ofReal
        ((2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)-f) + traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))/7) :=
          ENNReal.ofReal_le_ofReal harith
      _ ≤ ENNReal.ofReal ((2/7 : ℝ)*(fidelity (CStarMatrix.ofMatrix.symm P.val) (CStarMatrix.ofMatrix.symm S.val)-f)) +
        ENNReal.ofReal (traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))/7) := ENNReal.ofReal_add_le
      _ ≤ E_F S + ENNReal.ofReal (traceNorm ((CStarMatrix.ofMatrix.symm P.val)-(CStarMatrix.ofMatrix.symm S.val))/(2*(7/2))) := by
        norm_num only [show (2 : ℝ)*(7/2)=7 by norm_num]
        exact add_le_add hEF le_rfl
  have hLow2 : ENNReal.ofReal (9/70 : ℝ) ≤ E_F_my (7/2) phi2 := by
    convert hLower phi2 (11/20) hPure2 hP2 using 1 <;> norm_num
  have hLow3 : ENNReal.ofReal (6/35 : ℝ) ≤ E_F_my (7/2) phi3 := by
    convert hLower phi3 (2/5) hPure3 hP3 using 1 <;> norm_num

  have hProjEntropy (M : Coeff 5 3) (hproj : (M*Mᴴ)*(M*Mᴴ)=M*Mᴴ) : shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues = 0 := by
    unfold shannonEntropy
    let G := M*Mᴴ
    let hG := Matrix.isHermitian_mul_conjTranspose_self M
    let D : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hG.eigenvalues)
    have hD : D*D=D := by
      have hp := congrArg (Unitary.conjStarAlgAut ℂ _ (star hG.eigenvectorUnitary)) hproj
      simpa only [map_mul, hG.conjStarAlgAut_star_eigenvectorUnitary] using hp
    apply Finset.sum_eq_zero
    intro i hi
    have hx := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ => (A i i).re) hD
    have he : (hG.eigenvalues i)^2 = hG.eigenvalues i := by
      simpa [D, Matrix.diagonal_mul_diagonal, pow_two] using hx
    by_cases hz : hG.eigenvalues i = 0
    · simp [hz]
    · have hone : hG.eigenvalues i = 1 := by
        have hfactor : hG.eigenvalues i * (hG.eigenvalues i-1)=0 := by nlinarith [he]
        rcases mul_eq_zero.mp hfactor with h0 | h1
        · exact False.elim (hz h0)
        · linarith
      simp [hone]
  have hProductProj (k : Fin 2) : support (productCoeff k)*support (productCoeff k)=support (productCoeff k) := by
    let i : Fin 5 := ⟨k.val, by omega⟩
    let j : Fin 3 := ⟨k.val, by omega⟩
    have hM : productCoeff k = Matrix.single i j (1 : ℂ) := by
      ext r c
      simp only [productCoeff, Matrix.single, Matrix.of_apply, Fin.ext_iff]
      simp only [i,j,eq_comm]
    unfold support
    rw [hM,Matrix.conjTranspose_single]
    simp [Matrix.single_mul_single_same]
  have hProductEntropy (k : Fin 2) : shannonEntropy (Matrix.isHermitian_mul_conjTranspose_self (productCoeff k)).eigenvalues=0 :=
    hProjEntropy (productCoeff k) (hProductProj k)
  have hCost : cost separableEnsemble = 0 := by
    rw [hCostSpectral]
    simp [separableEnsemble,productPure,hProductEntropy]
  have hEFS : E_F sigma = 0 := by
    apply le_antisymm
    · unfold E_F
      exact iInf_le_of_le 2 (iInf_le_of_le separableEnsemble (by simp [hCost]))
    · exact bot_le
  have hNorm : traceNorm ((CStarMatrix.ofMatrix.symm omega.val)-(CStarMatrix.ofMatrix.symm sigma.val)) ≤ 1 := by
    let A := (1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi3.val)
    let B := (1/4 : ℂ) • rankOneDensity vMinus
    have hA : A.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm phi3.property.1)).smul (by norm_num [Complex.nonneg_iff])
    have hB : B.PosSemidef := (Matrix.posSemidef_vecMulVec_self_star vMinus).smul
      (by norm_num [Complex.nonneg_iff])
    have hAtr : A.trace=(1/2 : ℂ) := by
      change Matrix.trace ((1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi3.val)) = _
      rw [Matrix.trace_smul]
      have ht := phi3.property.2
      change Matrix.trace (CStarMatrix.ofMatrix.symm phi3.val) = 1 at ht
      rw [ht]
      norm_num
    have hBtr : B.trace=(1/2 : ℂ) := by
      norm_num [B,rankOneDensity,vMinus,Matrix.trace,Matrix.vecMulVec,Fintype.sum_prod_type,Fin.sum_univ_succ]
    have hid : (CStarMatrix.ofMatrix.symm omega.val)-(CStarMatrix.ofMatrix.symm sigma.val)=A + -B := by
      ext ⟨i,j⟩ ⟨k,l⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        norm_num [omega,sigma,phi2,phi3,A,B,rankOneDensity,v2,v3,vMinus,rankOneDensity,productCoeff,Matrix.vecMulVec]
    rw [hid]
    have hnA : traceNorm A = 1/2 := by
      have ht := congrArg Complex.re (traceNorm_of_posSemidef hA)
      simpa [hAtr] using ht
    have hnB : traceNorm B = 1/2 := by
      have ht := congrArg Complex.re (traceNorm_of_posSemidef hB)
      simpa [hBtr] using ht
    have h := traceNorm_add_le A (-B)
    rw [traceNorm_neg,hnA,hnB] at h
    norm_num at h
    exact h
  have hUpper : E_F_my (7/2) omega ≤ ENNReal.ofReal (1/7 : ℝ) := by
    unfold E_F_my
    apply iInf_le_of_le sigma
    rw [hEFS,zero_add]
    apply ENNReal.ofReal_le_ofReal
    norm_num only [show (2 : ℝ)*(7/2)=7 by norm_num]
    linarith
  have hBranch1 : Matrix.kronecker PA (1 : Matrix (Fin 3) (Fin 3) ℂ) * (CStarMatrix.ofMatrix.symm omega.val) *
    (Matrix.kronecker PA (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = (1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi2.val)  := by
    have hK : Matrix.kronecker PA (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        Matrix.diagonal (fun x : Fin 5 × Fin 3 => if x.1.val<2 then 1 else 0) := by
      simp [PA,← Matrix.diagonal_one,Matrix.kronecker,Matrix.diagonal_kronecker_diagonal]
    rw [hK]
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [Matrix.diagonal_conjTranspose,Matrix.mul_diagonal,Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [omega,phi2,phi3,rankOneDensity,v2,v3,Matrix.vecMulVec]
  have hBranch2 : Matrix.kronecker (1-PA) (1 : Matrix (Fin 3) (Fin 3) ℂ) * (CStarMatrix.ofMatrix.symm omega.val) *
    (Matrix.kronecker (1-PA) (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = (1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi3.val)  := by
    have hQ : 1-PA = Matrix.diagonal (fun i : Fin 5 => 1-(if i.val<2 then 1 else 0)) := by
      rw [PA,← Matrix.diagonal_one,← Matrix.diagonal_sub]
    have hK : Matrix.kronecker (1-PA) (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        Matrix.diagonal (fun x : Fin 5 × Fin 3 => 1-(if x.1.val<2 then 1 else 0)) := by
      rw [hQ]
      change Matrix.kroneckerMap (fun x y : ℂ => x*y)
        (Matrix.diagonal (fun i : Fin 5 => 1-(if i.val<2 then 1 else 0)))
        (Matrix.diagonal (fun _ : Fin 3 => 1)) = _
      rw [Matrix.diagonal_kronecker_diagonal]
      simp
    rw [hK]
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [Matrix.diagonal_conjTranspose,Matrix.mul_diagonal,Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [omega,phi2,phi3,rankOneDensity,v2,v3,Matrix.vecMulVec]
  have hBranches : branchList witnessProtocol (CStarMatrix.ofMatrix.symm omega.val) =
      [(1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi2.val),(1/2 : ℂ) • (CStarMatrix.ofMatrix.symm phi3.val)] := by
    simp only [Matrix.kronecker] at hBranch1 hBranch2
    simp [branchList,witnessProtocol,witnessInstrument,List.finRange,List.ofFn_succ,
      Fin.sum_univ_succ,hBranch1,hBranch2]
  let p : Fin 2 → ℝ := fun _ => 1/2
  let out : Fin 2 → DensityState (Fin 5 × Fin 3) := fun i => if i.val=0 then phi2 else phi3
  have hBL : branchList witnessProtocol (CStarMatrix.ofMatrix.symm omega.val) =
      (List.finRange 2).map (fun i => (p i : ℂ) • CStarMatrix.ofMatrix.symm (out i).val) := by
    simpa [p,out,List.finRange,List.ofFn_succ] using hBranches
  have hMono := hclaim 5 3 (by decide) (by decide) (7/2) (by norm_num)
    omega witnessProtocol 2 p out (by intro i; norm_num [p])
    (by norm_num [p,Fin.sum_univ_succ]) hBL
  have hAverage : ENNReal.ofReal (3/20 : ℝ) ≤
      ∑ i, ENNReal.ofReal (p i) * E_F_my (7/2) (out i) := by
    have h := add_le_add (mul_le_mul_right hLow2 (ENNReal.ofReal (1/2 : ℝ)))
      (mul_le_mul_right hLow3 (ENNReal.ofReal (1/2 : ℝ)))
    have hval : ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (9/70 : ℝ) +
        ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (6/35 : ℝ) = ENNReal.ofReal (3/20 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num),← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [hval] at h
    simpa [p,out,Fin.sum_univ_succ] using h
  have hFalse := hAverage.trans (hMono.trans hUpper)
  have hReal : (3/20 : ℝ) ≤ 1/7 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hFalse
  norm_num at hReal

#print axioms result
end D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation
