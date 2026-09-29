/- GID: D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorChannelOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual sector encodings, local quantum channels and passive-reference optimality. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
import D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
import D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Entanglement.FiniteSectorFlatFeasibility
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import Mathlib.Data.Matrix.Composition
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic
/-
The physical and rectangular proof owners imported below adapt
leanprover-community/physlib and AIQ-Kitware/aiq-dkps-formalization.
Their immutable revisions, copyrights, modifications, and full Apache-2.0
license texts are in docs/reports/licenses/finite-sector-channel-third-party.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open SectorSchmidtEncoding
open Matrix RHLinalg
open _root_.LinearMap
open Module (finrank)
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
  {spectralSize : ℕ}

set_option maxHeartbeats 40000000 in
/-- Exact full-operation sector coarse-graining optimum. -/
theorem result [Nonempty Sector] (M : Model Sector spectralSize) :
    FullOptimalityClaim M ∧ ConstructiveOptimalityClaim M ∧
      FlatFeasibilityClaim (Sector := Sector) := by
  classical
  obtain ⟨encoding, splitting, splittingJoint, hProductExists, hMixtureExists,
    hSplittingJoint, hSplittingAction, hSplittingSchurAction⟩ := physical_encoding M
  obtain ⟨hKernelProperties, r, hr, hSpectralMinimum, hEncodedDiamondUpper⟩ :=
    schur_upper M encoding
  have hActualMixtureLower {Sector : Type u} [Fintype Sector] [DecidableEq Sector] {J : ℕ}
      (M : Model Sector J) (encoding : EncodingChannels M)
      {m : ℕ} (weight : Fin m → ℝ) (hWeight : weight ∈ stdSimplex ℝ (Fin m))
      (left right : Fin m → QuantumChannel
        (SourceLocal (Coord := Fin J) M.d) (TargetLocal M.d))
      (product : Fin m → QuantumChannel
        (SourceLocal (Coord := Fin J) M.d × SourceLocal (Coord := Fin J) M.d)
        (TargetLocal M.d × TargetLocal M.d))
      (hProduct : ∀ i, TensorRealization (left i) (right i) (product i))
      (joint : QuantumChannel
        (SourceLocal (Coord := Fin J) M.d × SourceLocal (Coord := Fin J) M.d)
        (TargetLocal M.d × TargetLocal M.d))
      (hJoint : MixtureRealization weight left right joint)
      (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector) :
      let Omega : Sector × Sector → ℂ := fun si =>
        if si.1 = si.2 then (Real.sqrt (p si.1) : ℂ) else 0
      let Theta : Sector × (TargetLocal M.d × TargetLocal M.d) → ℂ := fun so =>
        (Real.sqrt (p so.1) : ℂ) * targetEncoding M.d so.2 so.1
      ∃ rho : DensityState (Sector × Sector),
        rho.1 = CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)) ∧
        2 * (1 - ∑ s, ∑ t, p s * p t * kernel M s t) ≤
          referenceError (joint.comp encoding.source) encoding.target rho := by
    classical
    intro Omega Theta
    have hProductLower {Sector : Type u} [Fintype Sector] [DecidableEq Sector] {J : ℕ}
        (M : Model Sector J) (encoding : EncodingChannels M)
        (left right : QuantumChannel (SourceLocal (Coord := Fin J) M.d) (TargetLocal M.d))
        (joint : QuantumChannel
          (SourceLocal (Coord := Fin J) M.d × SourceLocal (Coord := Fin J) M.d)
          (TargetLocal M.d × TargetLocal M.d))
        (hJoint : TensorRealization left right joint)
        (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector) :
        let Omega : Sector × Sector → ℂ := fun si =>
          if si.1 = si.2 then (Real.sqrt (p si.1) : ℂ) else 0
        ∃ rho : DensityState (Sector × Sector),
          rho.1 = CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)) ∧
          2 * (1 - ∑ s, ∑ t, p s * p t * kernel M s t) ≤
            referenceError (joint.comp encoding.source) encoding.target rho ∧
          (let Theta : Sector × (TargetLocal M.d × TargetLocal M.d) → ℂ := fun so =>
            (Real.sqrt (p so.1) : ℂ) * targetEncoding M.d so.2 so.1
           (star Theta ⬝ᵥ (CStarMatrix.ofMatrix.symm
             (referenceState (joint.comp encoding.source) rho).1).mulVec Theta).re ≤
               ∑ s, ∑ t, p s * p t * kernel M s t) := by
      classical
      intro Omega
      have hReference {Sector Out : Type u} [Fintype Sector] [DecidableEq Sector]
          [Fintype Out] [DecidableEq Out]
          (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector)
          (channel : QuantumChannel Sector Out)
          (H : Matrix Out Sector ℂ)
          (hAction : ∀ X : Matrix Sector Sector ℂ,
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = H * X * Hᴴ) :
          let Omega : Sector × Sector → ℂ := fun si =>
            if si.1 = si.2 then (Real.sqrt (p si.1) : ℂ) else 0
          let Theta : Sector × Out → ℂ := fun so =>
            (Real.sqrt (p so.1) : ℂ) * H so.2 so.1
          star Omega ⬝ᵥ Omega = 1 ∧ star Theta ⬝ᵥ Theta = 1 ∧
            referenceAction channel (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega))) =
              CStarMatrix.ofMatrix (Matrix.vecMulVec Theta (star Theta)) := by
        classical
        intro Omega Theta
        have hp0 : ∀ s, 0 ≤ p s := hp.1
        have hpsum : ∑ s, p s = 1 := hp.2
        have hsqrt (s : Sector) :
            (Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ) = (p s : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp0 s)]
        have hSingle (s t : Sector) :
            H * Matrix.single s t (1 : ℂ) * Hᴴ =
              Matrix.vecMulVec (fun o => H o s) (star (fun o => H o t)) := by
          ext o u
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, ite_and,
            Matrix.vecMulVec_apply, Pi.star_apply]
        have hNorm (s : Sector) : star (fun o => H o s) ⬝ᵥ (fun o => H o s) = 1 := by
          have h := channel.trace_preserving (CStarMatrix.ofMatrix (Matrix.single s s 1))
          change Matrix.trace (CStarMatrix.ofMatrix.symm
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s s 1)))) =
            Matrix.trace (Matrix.single s s 1) at h
          rw [hAction, hSingle, Matrix.trace_vecMulVec, dotProduct_comm] at h
          simpa using h
        have hOmega : star Omega ⬝ᵥ Omega = 1 := by
          simp only [dotProduct, Fintype.sum_prod_type, Omega, Pi.star_apply]
          have hterm (s : Sector) :
              (∑ i : Sector, star (if s = i then (Real.sqrt (p s) : ℂ) else 0) *
                (if s = i then (Real.sqrt (p s) : ℂ) else 0)) = (p s : ℂ) := by
            simp only [apply_ite, star_zero, Complex.star_def, Complex.conj_ofReal]
            simpa only [ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq,
              Finset.mem_univ, if_true] using hsqrt s
          simp_rw [hterm]
          exact_mod_cast hpsum
        have hTheta : star Theta ⬝ᵥ Theta = 1 := by
          rw [dotProduct, Fintype.sum_prod_type]
          change (∑ s, ∑ o, star ((Real.sqrt (p s) : ℂ) * H o s) *
            ((Real.sqrt (p s) : ℂ) * H o s)) = 1
          simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
          have hterm (s : Sector) :
              (∑ o : Out, star (H o s) * (Real.sqrt (p s) : ℂ) *
                ((Real.sqrt (p s) : ℂ) * H o s)) = (p s : ℂ) := by
            calc
              _ = (p s : ℂ) * (star (fun o => H o s) ⬝ᵥ (fun o => H o s)) := by
                rw [dotProduct, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro o _
                calc
                  _ = ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ)) *
                      (star (H o s) * H o s) := by ring
                  _ = _ := by rw [hsqrt]; rfl
              _ = _ := by rw [hNorm, mul_one]
          calc
            _ = ∑ s, (p s : ℂ) := Finset.sum_congr rfl (fun s _ => hterm s)
            _ = 1 := by exact_mod_cast hpsum
        refine ⟨hOmega, hTheta, ?_⟩
        apply CStarMatrix.ext
        rintro ⟨s, o⟩ ⟨t, u⟩
        change channel.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j)))) o u =
          Theta (s, o) * star (Theta (t, u))
        have hBlock : CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j))) =
            ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) •
              CStarMatrix.ofMatrix (Matrix.single s t 1) := by
          apply CStarMatrix.ext
          intro i j
          change Omega (s, i) * star (Omega (t, j)) =
            ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) * Matrix.single s t 1 i j
          by_cases hsi : s = i <;> by_cases htj : t = j <;>
            simp [Omega, Matrix.single, hsi, htj, eq_comm]
        rw [hBlock, map_smul]
        change ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) *
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s t 1))) o u = _
        rw [hAction, hSingle]
        simp only [Matrix.vecMulVec_apply, Pi.star_apply, Theta, star_mul,
          Complex.star_def, Complex.conj_ofReal]
        ring
      have hPassive {Sector Env Out : Type u}
          [Fintype Sector] [Fintype Env] [Fintype Out]
          [DecidableEq Sector] [DecidableEq Env] [DecidableEq Out]
          (p : Sector → ℝ) (hp : ∀ s, 0 ≤ p s)
          (H : Matrix Out Sector ℂ) (Xi : Sector → Matrix Env Out ℂ)
          (K : Sector → Sector → ℝ)
          (hcross : ∀ s t, (∑ e,
            star (∑ o, star (H o s) * Xi s e o) *
              (∑ o, star (H o t) * Xi t e o)).re ≤ K s t) :
          let Theta : Sector × Out → ℂ := fun so =>
            (Real.sqrt (p so.1) : ℂ) * H so.2 so.1
          let A : Matrix (Sector × Out) (Sector × Out) ℂ := Matrix.of fun so tu =>
            (Real.sqrt (p so.1) : ℂ) * (Real.sqrt (p tu.1) : ℂ) *
              ∑ e, Xi so.1 e so.2 * star (Xi tu.1 e tu.2)
          star Theta ⬝ᵥ Theta = 1 → A.trace = 1 →
            (star Theta ⬝ᵥ A.mulVec Theta).re ≤ ∑ s, ∑ t, p s * p t * K s t ∧
              2 * (1 - ∑ s, ∑ t, p s * p t * K s t) ≤
                traceNorm (A - Matrix.vecMulVec Theta (star Theta)) := by
        classical
        intro Theta A hTheta hTrace
        let zeta : Sector → Env → ℂ := fun s e => ∑ o, star (H o s) * Xi s e o
        have hFid : star Theta ⬝ᵥ A.mulVec Theta =
            ∑ e, star (∑ s, (p s : ℂ) * zeta s e) * (∑ s, (p s : ℂ) * zeta s e) := by
          let Phi : Env → Sector × Out → ℂ := fun e so =>
            (Real.sqrt (p so.1) : ℂ) * Xi so.1 e so.2
          have hA : A = ∑ e, Matrix.vecMulVec (Phi e) (star (Phi e)) := by
            ext ⟨s, o⟩ ⟨t, u⟩
            simp only [A, Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
              Phi, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
              Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            ring
          have hInner (e : Env) : star Theta ⬝ᵥ Phi e =
              ∑ s, (p s : ℂ) * zeta s e := by
            simp only [dotProduct, Theta, Phi, Fintype.sum_prod_type, Pi.star_apply,
              star_mul, Complex.star_def, Complex.conj_ofReal]
            apply Finset.sum_congr rfl
            intro s _
            have hs : (Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ) = (p s : ℂ) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp s)]
            dsimp [zeta]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro o _
            calc
              _ =
                  ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ)) *
                    (star (H o s) * Xi s e o) := by simp only [Complex.star_def]; ring
              _ = _ := by rw [hs]; simp only [Complex.star_def]
          rw [hA, Matrix.sum_mulVec, dotProduct_sum]
          apply Finset.sum_congr rfl
          intro e _
          rw [Matrix.vecMulVec_mulVec, dotProduct_smul,
            star_dotProduct (Phi e) Theta, hInner]
          simp [op_smul_eq_mul, mul_comm]
        have hzsum :
            (∑ e, star (∑ s, (p s : ℂ) * zeta s e) * (∑ t, (p t : ℂ) * zeta t e)) =
            ∑ s, ∑ t, (p s : ℂ) * (p t : ℂ) *
              (∑ e, star (zeta s e) * zeta t e) := by
          simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
            Finset.sum_mul, Finset.mul_sum]
          conv_lhs => rw [Finset.sum_comm]
          conv_lhs =>
            arg 2
            ext s
            rw [Finset.sum_comm]
          conv_rhs => rw [Finset.sum_comm]
          repeat' (apply Finset.sum_congr rfl; intro x hx)
          ring
        have hEnergy : (star Theta ⬝ᵥ A.mulVec Theta).re ≤
            ∑ s, ∑ t, p s * p t * K s t := by
          rw [hFid, hzsum, Complex.re_sum]
          apply Finset.sum_le_sum
          intro s hs
          rw [Complex.re_sum]
          apply Finset.sum_le_sum
          intro t ht
          change ((p s : ℂ) * (p t : ℂ) * (∑ e, star (zeta s e) * zeta t e)).re ≤ _
          rw [mul_assoc, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (hcross s t) (mul_nonneg (hp s) (hp t))
        have hReflection : 2 * (1 - (star Theta ⬝ᵥ A.mulVec Theta).re) ≤
            traceNorm (A - Matrix.vecMulVec Theta (star Theta)) := by
          classical
          let P : Matrix (Sector × Out) (Sector × Out) ℂ := Matrix.vecMulVec Theta (star Theta)
          have hPH : Pᴴ = P := by simp [P]
          have hP2 : P * P = P := by
            simp [P, Matrix.vecMulVec_mul_vecMulVec, hTheta]
          have hPtr : P.trace = 1 := by
            simpa [P, Matrix.trace_vecMulVec, dotProduct_comm] using hTheta
          let U : Matrix (Sector × Out) (Sector × Out) ℂ := 1 - (2 : ℂ) • P
          have hUH : Uᴴ = U := by
            simp [U, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hPH]
          have hU2 : U * U = 1 := by
            dsimp [U]
            simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.mul_smul, hP2]
            simp only [two_smul]
            module
          let u : Matrix.unitaryGroup (Sector × Out) ℂ := ⟨U, by
            rw [Matrix.mem_unitaryGroup_iff]
            change U * Uᴴ = 1
            rw [hUH, hU2]⟩
          have hPA : (P * A).trace = star Theta ⬝ᵥ A.mulVec Theta := by
            rw [show P * A = Matrix.vecMulVec Theta ((star Theta) ᵥ* A) from
              Matrix.vecMulVec_mul Theta (star Theta) A, Matrix.trace_vecMulVec]
            exact dotProduct_comm _ _ |>.trans (Matrix.dotProduct_mulVec _ _ _).symm
          have hTrace : (U * (A - P)).trace =
              2 * (1 - star Theta ⬝ᵥ A.mulVec Theta) := by
            dsimp [U]
            rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
              hP2, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
              Matrix.trace_sub, hTrace, hPtr, hPA]
            ring
          have hUpper := (traceNorm_eq_max_re_tr_U (A - P)).2
          have hBound := hUpper
            (a := ((U * (A - P)).trace).re) ⟨u, rfl⟩
          rw [hTrace] at hBound
          simpa [P, Complex.mul_re] using hBound
        refine ⟨hEnergy, ?_⟩
        exact (by linarith [hEnergy] :
          2 * (1 - ∑ s, ∑ t, p s * p t * K s t) ≤
            2 * (1 - (star Theta ⬝ᵥ A.mulVec Theta).re)).trans hReflection
      let S := SourceLocal (Coord := Fin J) M.d
      let O := TargetLocal M.d
      let EX := O × S
      let EY := O × S
      let H : Matrix (O × O) Sector ℂ := targetEncoding M.d
      let Theta : Sector × (O × O) → ℂ := fun so =>
        (Real.sqrt (p so.1) : ℂ) * H so.2 so.1
      have hTarget := hReference p hp encoding.target H encoding.targetAction
      change (star Omega ⬝ᵥ Omega = 1) ∧ (star Theta ⬝ᵥ Theta = 1) ∧
        referenceAction encoding.target (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega))) =
          CStarMatrix.ofMatrix (Matrix.vecMulVec Theta (star Theta)) at hTarget
      let rho : DensityState (Sector × Sector) := pureState Omega hTarget.1
      obtain ⟨VX, hVX, hLX⟩ := (channel_kraus_stinespring).2 left
      obtain ⟨VY, hVY, hLY⟩ := (channel_kraus_stinespring).2 right
      let Xi : Sector → Matrix (EX × EY) (O × O) ℂ := fun s e o =>
        ∑ i : S, ∑ j : S, VX (e.1, o.1) i * sourceEncoding M.d M.spectrum (i, j) s * VY (e.2, o.2) j
      let C : Sector → Matrix S S ℂ := fun s => Matrix.diagonal fun i =>
        if i.1 = s then (Real.sqrt (M.spectrum s i.2.2 / (M.d s : ℝ)) : ℂ) else 0
      let Q := fun s => VX * C s * VY.transpose
      let Z : Sector → Matrix EX EY ℂ := fun s ex ey =>
        (((Real.sqrt (M.d s : ℝ))⁻¹ : ℝ) : ℂ) *
          ∑ a : Fin (M.d s), Q s (ex, ⟨s, a⟩) (ey, ⟨s, a⟩)
      let A : Matrix (Sector × (O × O)) (Sector × (O × O)) ℂ := Matrix.of fun so tu =>
        (Real.sqrt (p so.1) : ℂ) * (Real.sqrt (p tu.1) : ℂ) *
          ∑ e, Xi so.1 e so.2 * star (Xi tu.1 e tu.2)
      have hTensor' (s t : Sector) (o v : O × O) :
          tensorRawAction left right
            (Matrix.vecMulVec (fun i => sourceEncoding M.d M.spectrum i s)
              (star (fun i => sourceEncoding M.d M.spectrum i t))) o v =
            ∑ e, Xi s e o * star (Xi t e v) := by
        have hLeft (i j : S) (a b : O) :
            CStarMatrix.ofMatrix.symm
              (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) a b =
              ∑ ex : O × S, VX (ex, a) i * star (VX (ex, b) j) := by
          rw [← hLX]
          simp [partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.single, ite_and]
          rfl
        have hRight (i j : S) (a b : O) :
            CStarMatrix.ofMatrix.symm
              (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) a b =
              ∑ ey : O × S, VY (ey, a) i * star (VY (ey, b) j) := by
          rw [← hLY]
          simp [partialTraceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.single, ite_and]
          rfl
        rw [Fintype.sum_prod_type]
        simp only [tensorRawAction, Matrix.vecMulVec_apply, Pi.star_apply, hLeft, hRight,
          Xi, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
        conv_rhs =>
          arg 2
          ext ex
          rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext ex
          arg 2
          ext ey
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext ex
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext j
          arg 2
          ext ex
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext j
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext j
          arg 2
          ext a
          arg 2
          ext ex
          rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext j
          arg 2
          ext a
          rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        conv_rhs =>
          arg 2
          ext i
          arg 2
          ext j
          rw [Finset.sum_comm]
        conv_lhs =>
          arg 2
          ext i
          arg 2
          ext j
          arg 2
          ext a
          arg 2
          ext b
          rw [Finset.sum_comm]
        repeat' (apply Finset.sum_congr rfl; intro x hx)
        ring
      have hRefBlock {Out : Type u} [Fintype Out] [DecidableEq Out]
          (channel : QuantumChannel Sector Out) (s t : Sector) (o v : Out) :
          referenceAction channel (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)))
            (s, o) (t, v) =
          ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) *
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s t 1))) o v := by
        change channel.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j)))) o v = _
        have hBlock : CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j))) =
            ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) •
              CStarMatrix.ofMatrix (Matrix.single s t 1) := by
          apply CStarMatrix.ext
          intro i j
          change Omega (s, i) * star (Omega (t, j)) =
            ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) * Matrix.single s t 1 i j
          by_cases hsi : s = i <;> by_cases htj : t = j <;>
            simp [Omega, Matrix.single, hsi, htj, eq_comm]
        rw [hBlock, map_smul]
        rfl
      have hSourceSingle (s t : Sector) :
          sourceEncoding M.d M.spectrum * Matrix.single s t (1 : ℂ) * (sourceEncoding M.d M.spectrum)ᴴ =
            Matrix.vecMulVec (fun i => sourceEncoding M.d M.spectrum i s)
              (star (fun i => sourceEncoding M.d M.spectrum i t)) := by
        ext i j
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, ite_and,
          Matrix.vecMulVec_apply, Pi.star_apply]
      have hSourceAsRank (s t : Sector) :
          encoding.source.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s t 1)) =
            CStarMatrix.ofMatrix (Matrix.vecMulVec (fun i => sourceEncoding M.d M.spectrum i s)
              (star (fun i => sourceEncoding M.d M.spectrum i t))) := by
        apply CStarMatrix.ofMatrix.symm.injective
        rw [encoding.sourceAction, hSourceSingle]
        rfl
      have hActual : CStarMatrix.ofMatrix.symm
          (referenceState (joint.comp encoding.source) rho).1 = A := by
        ext ⟨s, o⟩ ⟨t, v⟩
        change referenceAction (joint.comp encoding.source)
          (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega))) (s, o) (t, v) = A (s, o) (t, v)
        rw [hRefBlock, QuantumChannel.comp_apply, hSourceAsRank, hJoint, hTensor']
        rfl
      have hActualTrace : A.trace = 1 := by
        have h := (referenceState (joint.comp encoding.source) rho).2.2
        change Matrix.trace (CStarMatrix.ofMatrix.symm
          (referenceState (joint.comp encoding.source) rho).1) = 1 at h
        rw [hActual] at h
        exact h
      have hTargetState : CStarMatrix.ofMatrix.symm (referenceState encoding.target rho).1 =
          Matrix.vecMulVec Theta (star Theta) := by
        change CStarMatrix.ofMatrix.symm (referenceAction encoding.target
          (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)))) = _
        rw [hTarget.2.2]
        rfl
      have hDiagonal (s : Sector) (i j : S) :
          sourceEncoding M.d M.spectrum (i, j) s = C s i j := by
        by_cases hij : i = j
        · subst j
          by_cases hi : i.1 = s <;> simp [sourceEncoding, C, hi]
        · simp [sourceEncoding, C, Matrix.diagonal_apply, hij]
      have hQXi (s : Sector) (e : EX × EY) (o : O × O) :
          Xi s e o = Q s (e.1, o.1) (e.2, o.2) := by
        simp only [Xi, hDiagonal, Q, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
      have hContract (s : Sector) (e : EX × EY) :
          (∑ o : O × O, star (H o s) * Xi s e o) = Z s e.1 e.2 := by
        rw [Fintype.sum_prod_type]
        have hdiag (x : O) : (∑ y : O, star (H (x, y) s) * Xi s e (x, y)) =
            if x.1 = s then (Real.sqrt ((M.d x.1 : ℝ)⁻¹) : ℂ) * Xi s e (x, x) else 0 := by
          rw [Finset.sum_eq_single x]
          · by_cases hx : x.1 = s <;> simp [H, targetEncoding, hx]
          · intro y hy hne
            simp [H, targetEncoding, Ne.symm hne]
          · intro h
            exact False.elim (h (Finset.mem_univ x))
        simp_rw [hdiag]
        rw [Fintype.sum_sigma]
        have hsector (t : Sector) :
            (∑ a : Fin (M.d t), if t = s then
              (Real.sqrt ((M.d t : ℝ)⁻¹) : ℂ) * Xi s e (⟨t, a⟩, ⟨t, a⟩) else 0) =
            if t = s then (Real.sqrt ((M.d t : ℝ)⁻¹) : ℂ) *
              ∑ a : Fin (M.d t), Xi s e (⟨t, a⟩, ⟨t, a⟩) else 0 := by
          by_cases ht : t = s <;> simp [ht, Finset.mul_sum]
        simp_rw [hsector]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        change (Real.sqrt ((M.d s : ℝ)⁻¹) : ℂ) *
          (∑ a : Fin (M.d s), Xi s e (⟨s, a⟩, ⟨s, a⟩)) = _
        rw [Real.sqrt_inv]
        simp_rw [hQXi]
        rfl
      have hCross (s t : Sector) :
          (∑ e, star (∑ o, star (H o s) * Xi s e o) *
            (∑ o, star (H o t) * Xi t e o)).re ≤ kernel M s t := by
        simp_rw [hContract]
        rw [Fintype.sum_prod_type]
        exact sector_pair M VX VY hVX hVY s t
      have hLower := hPassive p hp.1 H Xi (kernel M) hCross hTarget.2.1 hActualTrace
      refine ⟨rho, rfl, ?_, ?_⟩
      · change 2 * (1 - ∑ s, ∑ t, p s * p t * kernel M s t) ≤
          traceNorm (CStarMatrix.ofMatrix.symm (referenceState (joint.comp encoding.source) rho).1 -
            CStarMatrix.ofMatrix.symm (referenceState encoding.target rho).1)
        rw [hActual, hTargetState]
        exact hLower.2
      · change (star Theta ⬝ᵥ (CStarMatrix.ofMatrix.symm
            (referenceState (joint.comp encoding.source) rho).1).mulVec Theta).re ≤ _
        rw [hActual]
        exact hLower.1

    have hReflection {n : Type u} [Fintype n] [DecidableEq n]
        (A : Matrix n n ℂ) (hA : A.trace = 1)
        (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) :
        2 * (1 - (star v ⬝ᵥ A.mulVec v).re) ≤
          traceNorm (A - Matrix.vecMulVec v (star v)) := by
      classical
      let P : Matrix n n ℂ := Matrix.vecMulVec v (star v)
      have hPH : Pᴴ = P := by simp [P]
      have hP2 : P * P = P := by
        simp [P, Matrix.vecMulVec_mul_vecMulVec, hv]
      have hPtr : P.trace = 1 := by
        simpa [P, Matrix.trace_vecMulVec, dotProduct_comm] using hv
      let U : Matrix n n ℂ := 1 - (2 : ℂ) • P
      have hUH : Uᴴ = U := by
        simp [U, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hPH]
      have hU2 : U * U = 1 := by
        dsimp [U]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, hP2]
        simp only [two_smul]
        module
      let u : Matrix.unitaryGroup n ℂ := ⟨U, by
        rw [Matrix.mem_unitaryGroup_iff]
        change U * Uᴴ = 1
        rw [hUH, hU2]⟩
      have hPA : (P * A).trace = star v ⬝ᵥ A.mulVec v := by
        rw [show P * A = Matrix.vecMulVec v ((star v) ᵥ* A) from
          Matrix.vecMulVec_mul v (star v) A, Matrix.trace_vecMulVec]
        exact dotProduct_comm _ _ |>.trans (Matrix.dotProduct_mulVec _ _ _).symm
      have hTrace : (U * (A - P)).trace =
          2 * (1 - star v ⬝ᵥ A.mulVec v) := by
        dsimp [U]
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
          hP2, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
          Matrix.trace_sub, hA, hPtr, hPA]
        ring
      have hUpper := (traceNorm_eq_max_re_tr_U (A - P)).2
      have hBound := hUpper
        (a := ((U * (A - P)).trace).re) ⟨u, rfl⟩
      rw [hTrace] at hBound
      simpa [P, Complex.mul_re] using hBound

    have hReference {Sector Out : Type u} [Fintype Sector] [DecidableEq Sector]
        [Fintype Out] [DecidableEq Out]
        (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector)
        (channel : QuantumChannel Sector Out)
        (H : Matrix Out Sector ℂ)
        (hAction : ∀ X : Matrix Sector Sector ℂ,
          CStarMatrix.ofMatrix.symm
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = H * X * Hᴴ) :
        let Omega : Sector × Sector → ℂ := fun si =>
          if si.1 = si.2 then (Real.sqrt (p si.1) : ℂ) else 0
        let Theta : Sector × Out → ℂ := fun so =>
          (Real.sqrt (p so.1) : ℂ) * H so.2 so.1
        star Omega ⬝ᵥ Omega = 1 ∧ star Theta ⬝ᵥ Theta = 1 ∧
          referenceAction channel (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega))) =
            CStarMatrix.ofMatrix (Matrix.vecMulVec Theta (star Theta)) := by
      classical
      intro Omega Theta
      have hp0 : ∀ s, 0 ≤ p s := hp.1
      have hpsum : ∑ s, p s = 1 := hp.2
      have hsqrt (s : Sector) :
          (Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ) = (p s : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp0 s)]
      have hSingle (s t : Sector) :
          H * Matrix.single s t (1 : ℂ) * Hᴴ =
            Matrix.vecMulVec (fun o => H o s) (star (fun o => H o t)) := by
        ext o u
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single, ite_and,
          Matrix.vecMulVec_apply, Pi.star_apply]
      have hNorm (s : Sector) : star (fun o => H o s) ⬝ᵥ (fun o => H o s) = 1 := by
        have h := channel.trace_preserving (CStarMatrix.ofMatrix (Matrix.single s s 1))
        change Matrix.trace (CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s s 1)))) =
          Matrix.trace (Matrix.single s s 1) at h
        rw [hAction, hSingle, Matrix.trace_vecMulVec, dotProduct_comm] at h
        simpa using h
      have hOmega : star Omega ⬝ᵥ Omega = 1 := by
        simp only [dotProduct, Fintype.sum_prod_type, Omega, Pi.star_apply]
        have hterm (s : Sector) :
            (∑ i : Sector, star (if s = i then (Real.sqrt (p s) : ℂ) else 0) *
              (if s = i then (Real.sqrt (p s) : ℂ) else 0)) = (p s : ℂ) := by
          simp only [apply_ite, star_zero, Complex.star_def, Complex.conj_ofReal]
          simpa only [ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq,
            Finset.mem_univ, if_true] using hsqrt s
        simp_rw [hterm]
        exact_mod_cast hpsum
      have hTheta : star Theta ⬝ᵥ Theta = 1 := by
        rw [dotProduct, Fintype.sum_prod_type]
        change (∑ s, ∑ o, star ((Real.sqrt (p s) : ℂ) * H o s) *
          ((Real.sqrt (p s) : ℂ) * H o s)) = 1
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
        have hterm (s : Sector) :
            (∑ o : Out, star (H o s) * (Real.sqrt (p s) : ℂ) *
              ((Real.sqrt (p s) : ℂ) * H o s)) = (p s : ℂ) := by
          calc
            _ = (p s : ℂ) * (star (fun o => H o s) ⬝ᵥ (fun o => H o s)) := by
              rw [dotProduct, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro o _
              calc
                _ = ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p s) : ℂ)) *
                    (star (H o s) * H o s) := by ring
                _ = _ := by rw [hsqrt]; rfl
            _ = _ := by rw [hNorm, mul_one]
        calc
          _ = ∑ s, (p s : ℂ) := Finset.sum_congr rfl (fun s _ => hterm s)
          _ = 1 := by exact_mod_cast hpsum
      refine ⟨hOmega, hTheta, ?_⟩
      apply CStarMatrix.ext
      rintro ⟨s, o⟩ ⟨t, u⟩
      change channel.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j)))) o u =
        Theta (s, o) * star (Theta (t, u))
      have hBlock : CStarMatrix.ofMatrix (fun i j => Omega (s, i) * star (Omega (t, j))) =
          ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) •
            CStarMatrix.ofMatrix (Matrix.single s t 1) := by
        apply CStarMatrix.ext
        intro i j
        change Omega (s, i) * star (Omega (t, j)) =
          ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) * Matrix.single s t 1 i j
        by_cases hsi : s = i <;> by_cases htj : t = j <;>
          simp [Omega, Matrix.single, hsi, htj, eq_comm]
      rw [hBlock, map_smul]
      change ((Real.sqrt (p s) : ℂ) * (Real.sqrt (p t) : ℂ)) *
          CStarMatrix.ofMatrix.symm
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s t 1))) o u = _
      rw [hAction, hSingle]
      simp only [Matrix.vecMulVec_apply, Pi.star_apply, Theta, star_mul,
        Complex.star_def, Complex.conj_ofReal]
      ring

    have hMixtureReference {r a ax ay bx oy : Type u}
        [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
        [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
        [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
        {m : ℕ} (weight : Fin m → ℝ)
        (source : QuantumChannel a (ax × ay))
        (left : Fin m → QuantumChannel ax bx)
        (right : Fin m → QuantumChannel ay oy)
        (product : Fin m → QuantumChannel (ax × ay) (bx × oy))
        (hProduct : ∀ i, TensorRealization (left i) (right i) (product i))
        (joint : QuantumChannel (ax × ay) (bx × oy))
        (hJoint : MixtureRealization weight left right joint)
        (rho : DensityState (r × a)) :
        CStarMatrix.ofMatrix.symm (referenceState (joint.comp source) rho).1 =
          ∑ i, (weight i : ℂ) •
            CStarMatrix.ofMatrix.symm (referenceState ((product i).comp source) rho).1 := by
      classical
      ext ⟨s, o⟩ ⟨t, v⟩
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      change joint.toCompletelyPositiveMap
          (source.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (fun x y => rho.1 (s, x) (t, y)))) o v =
        ∑ i, (weight i : ℂ) * (product i).toCompletelyPositiveMap
          (source.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (fun x y => rho.1 (s, x) (t, y)))) o v
      let Y : Matrix (ax × ay) (ax × ay) ℂ := CStarMatrix.ofMatrix.symm
        (source.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (fun x y => rho.1 (s, x) (t, y))))
      have hP (i : Fin m) : tensorRawAction (left i) (right i) Y =
          CStarMatrix.ofMatrix.symm
            ((product i).toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) :=
        (hProduct i Y).symm
      have hJ := hJoint Y
      simp_rw [hP] at hJ
      have hEval := congrArg (fun Z : Matrix (bx × oy) (bx × oy) ℂ => Z o v) hJ
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Y, CStarMatrix.ofMatrix.apply_symm_apply] at hEval
      change joint.toCompletelyPositiveMap
          (source.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (fun x y => rho.1 (s, x) (t, y)))) o v =
        ∑ i, (weight i : ℂ) * (product i).toCompletelyPositiveMap
          (source.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (fun x y => rho.1 (s, x) (t, y)))) o v at hEval
      exact hEval


    have hProductFidelity (i : Fin m) :
        ∃ rho : DensityState (Sector × Sector),
          rho.1 = CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)) ∧
          (star Theta ⬝ᵥ (CStarMatrix.ofMatrix.symm
            (referenceState ((product i).comp encoding.source) rho).1).mulVec Theta).re ≤
              ∑ s, ∑ t, p s * p t * kernel M s t := by
      obtain ⟨rho_i, hMatrix_i, _, hFid_i⟩ :=
        hProductLower M encoding (left i) (right i) (product i) (hProduct i) p hp
      exact ⟨rho_i, hMatrix_i, hFid_i⟩
    have hTarget := hReference p hp encoding.target (targetEncoding M.d) encoding.targetAction
    change (star Omega ⬝ᵥ Omega = 1) ∧ (star Theta ⬝ᵥ Theta = 1) ∧
      referenceAction encoding.target
        (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega))) =
          CStarMatrix.ofMatrix (Matrix.vecMulVec Theta (star Theta)) at hTarget
    let rho : DensityState (Sector × Sector) := pureState Omega hTarget.1
    let A := CStarMatrix.ofMatrix.symm (referenceState (joint.comp encoding.source) rho).1
    let B := fun i => CStarMatrix.ofMatrix.symm
      (referenceState ((product i).comp encoding.source) rho).1
    have hEach (i : Fin m) : (star Theta ⬝ᵥ (B i).mulVec Theta).re ≤
        ∑ s, ∑ t, p s * p t * kernel M s t := by
      obtain ⟨rho_i, hRho_i, hFid_i⟩ := hProductFidelity i
      have hSame : rho_i = rho := Subtype.ext hRho_i
      subst rho_i
      exact hFid_i
    have hSum : A = ∑ i, (weight i : ℂ) • B i :=
      hMixtureReference weight encoding.source left right product hProduct joint hJoint rho
    have hFidelity : (star Theta ⬝ᵥ A.mulVec Theta).re ≤
        ∑ s, ∑ t, p s * p t * kernel M s t := by
      rw [hSum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
      calc
        _ ≤ ∑ i, weight i * (∑ s, ∑ t, p s * p t * kernel M s t) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hEach i) (hWeight.1 i))
        _ = _ := by rw [← Finset.sum_mul, hWeight.2, one_mul]
    have hTrace : A.trace = 1 := (referenceState (joint.comp encoding.source) rho).2.2
    have hTargetMatrix : CStarMatrix.ofMatrix.symm (referenceState encoding.target rho).1 =
        Matrix.vecMulVec Theta (star Theta) := by
      change CStarMatrix.ofMatrix.symm (referenceAction encoding.target
        (CStarMatrix.ofMatrix (Matrix.vecMulVec Omega (star Omega)))) = _
      rw [hTarget.2.2]
      rfl
    refine ⟨rho, rfl, ?_⟩
    change 2 * (1 - ∑ s, ∑ t, p s * p t * kernel M s t) ≤
      traceNorm (A - CStarMatrix.ofMatrix.symm (referenceState encoding.target rho).1)
    rw [hTargetMatrix]
    have hReflect := hReflection A hTrace Theta hTarget.2.1
    linarith

  have hFiniteReferenceLeDiamond
      (first second : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d))
      (n : ℕ) (rho : DensityState (Fin n × Sector)) :
      referenceError first second rho ≤ diamondDistance first second := by
    have hBound (m : ℕ) (tau : DensityState (Fin m × Sector)) :
        referenceError first second tau ≤ 2 := by
      have h := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance_le_one
        (referenceState first tau) (referenceState second tau)
      change referenceError first second tau / 2 ≤ 1 at h
      linarith
    have hBdd : BddAbove ({0} ∪ {x : ℝ | ∃ m : ℕ,
        ∃ tau : DensityState (Fin m × Sector), x = referenceError first second tau}) := by
      refine ⟨2, ?_⟩
      intro x hx
      rcases hx with hx | ⟨m, tau, rfl⟩
      · rcases hx with rfl
        norm_num
      · exact hBound m tau
    exact le_csSup hBdd (Or.inr ⟨n, rho, rfl⟩)

  have hMixtureErrorLower :
      ∀ x ∈ mixtureErrors M encoding, 2 * (1 - spectralMinimum M) ≤ x := by
    intro x hx
    rcases hx with ⟨m, weight, hWeight, left, right, joint, hJoint, rfl⟩
    let product := fun i : Fin m => (hProductExists (left i) (right i)).choose
    have hProduct : ∀ i, TensorRealization (left i) (right i) (product i) :=
      fun i => (hProductExists (left i) (right i)).choose_spec
    obtain ⟨rho, _hRho, hLower⟩ :=
      hActualMixtureLower M encoding weight hWeight left right product hProduct joint hJoint r hr
    rw [← hSpectralMinimum] at hLower
    obtain ⟨tau, _hPure, hCompressed⟩ :=
      (D5.S3.Quantum.Foundation.FiniteDiamondDistance.result
        (joint.comp encoding.source) encoding.target).2.1 rho
    exact hLower.trans (hCompressed.trans
      (hFiniteReferenceLeDiamond _ _ (Fintype.card Sector) tau))

  have hProductErrorLower :
      ∀ x ∈ productErrors M encoding, 2 * (1 - spectralMinimum M) ≤ x := by
    intro x hx
    rcases hx with ⟨left, right, joint, hJoint, hError⟩
    have hWeight : (fun _ : Fin 1 => (1 : ℝ)) ∈ stdSimplex ℝ (Fin 1) := by
      constructor
      · intro i
        norm_num
      · simp
    apply hMixtureErrorLower x
    refine ⟨1, (fun _ => 1), hWeight, (fun _ => left), (fun _ => right),
      joint, ?_, hError⟩
    intro X
    rw [hJoint X]
    simp

  have hSplitMem : diamondDistance (splittingJoint.comp encoding.source) encoding.target ∈
      productErrors M encoding := ⟨splitting, splitting, splittingJoint, hSplittingJoint, rfl⟩
  have hSplitEqual : diamondDistance (splittingJoint.comp encoding.source) encoding.target =
      2 * (1 - spectralMinimum M) :=
    le_antisymm (hEncodedDiamondUpper _ hSplittingSchurAction) (hProductErrorLower _ hSplitMem)
  have hAttained : 2 * (1 - spectralMinimum M) ∈ productErrors M encoding := by
    rw [← hSplitEqual]
    exact hSplitMem
  have hOneWeight : (fun _ : Fin 1 => (1 : ℝ)) ∈ stdSimplex ℝ (Fin 1) := by
    constructor
    · intro i
      norm_num
    · simp
  have hOneMixture : MixtureRealization (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => splitting) (fun _ => splitting) splittingJoint := by
    intro X
    change CStarMatrix.ofMatrix.symm
        (splittingJoint.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ _i : Fin 1, (1 : ℂ) • tensorRawAction splitting splitting X
    simp only [Fin.sum_univ_one, one_smul]
    exact hSplittingJoint X
  have hMixtureMem : 2 * (1 - spectralMinimum M) ∈ mixtureErrors M encoding :=
    ⟨1, (fun _ => 1), hOneWeight, (fun _ => splitting), (fun _ => splitting),
      splittingJoint, hOneMixture, hSplitEqual.symm⟩
  have hProductInf : sInf (productErrors M encoding) = 2 * (1 - spectralMinimum M) :=
    le_antisymm (csInf_le ⟨_, hProductErrorLower⟩ hAttained)
      (le_csInf ⟨_, hAttained⟩ hProductErrorLower)
  have hMixtureInf : sInf (mixtureErrors M encoding) = 2 * (1 - spectralMinimum M) :=
    le_antisymm (csInf_le ⟨_, hMixtureErrorLower⟩ hMixtureMem)
      (le_csInf ⟨_, hMixtureMem⟩ hMixtureErrorLower)
  have hBasisExact (s : Sector) :
      (splittingJoint.comp encoding.source).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single s s 1)) =
      encoding.target.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single s s 1)) := by
    apply CStarMatrix.ofMatrix.symm.injective
    have hSchurBasis :
        (Matrix.of fun a b => (kernel M a b : ℂ) * Matrix.single s s (1 : ℂ) a b) =
        Matrix.single s s (1 : ℂ) := by
      ext a b
      change (kernel M a b : ℂ) * Matrix.single s s (1 : ℂ) a b =
        Matrix.single s s (1 : ℂ) a b
      by_cases ha : s = a
      · subst a
        by_cases hb : s = b
        · subst b
          simp [hKernelProperties.2.1]
        · simp [Matrix.single, hb]
      · simp [Matrix.single, ha]
    rw [hSplittingSchurAction, hSchurBasis, encoding.targetAction]
  have hFull : FullOptimalityClaim M :=
    ⟨encoding, hProductExists, hMixtureExists, hProductInf, hMixtureInf, hAttained⟩
  have hConstructive : ConstructiveOptimalityClaim M := by
    refine ⟨encoding, splitting, splittingJoint, hSplittingJoint, ?_,
      hSplittingSchurAction, hBasisExact, hSplitEqual, hProductInf, hMixtureInf⟩
    exact hSplittingAction
  exact ⟨hFull, hConstructive, flat_feasibility (Sector := Sector)⟩

end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
