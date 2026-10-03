/- GID: D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorSchurUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure-reference Schur channel diamond upper bound at the common spectral minimum. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
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
/-- The spectral minimum gives the exact upper bound for the physical Schur channel. -/
theorem schur_upper [Nonempty Sector] (M : Model Sector spectralSize)
    (encoding : EncodingChannels M) :
    ((Matrix.of fun s t => (kernel M s t : ℂ)).PosSemidef ∧
      (∀ s, kernel M s s = 1) ∧ (∀ s t, kernel M s t ≤ 1)) ∧
    ∃ r : Sector → ℝ, r ∈ stdSimplex ℝ Sector ∧
      spectralMinimum M = ∑ s, ∑ t, r s * r t * kernel M s t ∧
      ∀ (C : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d)),
        (∀ X : Matrix Sector Sector ℂ,
          CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
            targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
              (targetEncoding M.d)ᴴ) →
        diamondDistance C encoding.target ≤ 2 * (1 - spectralMinimum M) := by
  classical
  have hKernelProperties :
      (Matrix.of fun s t => (kernel M s t : ℂ)).PosSemidef ∧
        (∀ s, kernel M s s = 1) ∧ (∀ s t, kernel M s t ≤ 1) := by
    let G : Matrix (Fin spectralSize) Sector ℂ :=
      Matrix.of fun j s => (Real.sqrt (M.spectrum s j) : ℂ)
    have hGram : Gᴴ * G = Matrix.of fun s t => (kernel M s t : ℂ) := by
      ext s t
      simp [G, kernel, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.ofReal_sum, Complex.ofReal_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hGram]
      exact Matrix.posSemidef_conjTranspose_mul_self G
    · intro s
      change (∑ j, Real.sqrt (M.spectrum s j) * Real.sqrt (M.spectrum s j)) = 1
      simpa only [Real.mul_self_sqrt (M.spectrumNonneg s _)] using M.spectrumSum s
    · intro s t
      have h := Real.sum_sqrt_mul_sqrt_le Finset.univ
        (M.spectrumNonneg s) (M.spectrumNonneg t)
      simpa [kernel, M.spectrumSum] using h

  have hIsometricNorm {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
      (V : Matrix A B ℂ) (hV : Vᴴ * V = 1) (X : Matrix B B ℂ) :
      traceNorm (V * X * Vᴴ) = traceNorm X := by
    let P := CFC.sqrt (Xᴴ * X)
    have hXX : 0 ≤ Xᴴ * X := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
    have hgram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * Xᴴ * (Vᴴ * V) * X * Vᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
        _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hP : 0 ≤ P := CFC.sqrt_nonneg _
    have hsquare : (V * P * Vᴴ) * (V * P * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = V * (P * P) * Vᴴ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by rw [show P * P = Xᴴ * X from CFC.sqrt_mul_sqrt_self _ hXX]
    have hpositive : 0 ≤ V * P * Vᴴ :=
      ((Matrix.nonneg_iff_posSemidef.mp hP).mul_mul_conjTranspose_same V).nonneg
    have hsqrt : CFC.sqrt (V * (Xᴴ * X) * Vᴴ) = V * P * Vᴴ :=
      CFC.sqrt_unique hsquare hpositive
    change (CFC.sqrt ((V * X * Vᴴ)ᴴ * (V * X * Vᴴ))).trace.re =
      (CFC.sqrt (Xᴴ * X)).trace.re
    rw [hgram, hsqrt, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

  have hReferenceSchurLift {R : Type} {I O : Type u} [Fintype R] [DecidableEq R]
      [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (C : QuantumChannel I O) (W : Matrix O I ℂ) (K : I → I → ℂ)
      (hC : ∀ X : Matrix I I ℂ,
        CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          W * (Matrix.of fun i j => K i j * X i j) * Wᴴ)
      (X : Matrix (R × I) (R × I) ℂ) :
      CStarMatrix.ofMatrix.symm (referenceAction C (CStarMatrix.ofMatrix X)) =
        ((1 : Matrix R R ℂ) ⊗ₖ W) *
          (Matrix.of fun z w => K z.2 w.2 * X z w) *
            ((1 : Matrix R R ℂ) ⊗ₖ W)ᴴ := by
    classical
    ext ⟨r, o⟩ ⟨s, p⟩
    have hblock :
        CStarMatrix.ofMatrix.symm (referenceAction C (CStarMatrix.ofMatrix X)) (r, o) (s, p) =
          CStarMatrix.ofMatrix.symm
            (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix
              (Matrix.of fun i j => X (r, i) (s, j)))) o p := rfl
    rw [hblock]
    have h := congrArg (fun Y : Matrix O O ℂ => Y o p)
      (hC (Matrix.of fun i j => X (r, i) (s, j)))
    rw [h]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite, mul_assoc]

  have hSchurPureUpper (K : Sector → Sector → ℝ)
      (hK : Matrix.PosSemidef (fun s t => (K s t : ℂ)))
      (hdiag : ∀ s, K s s = 1) (hone : ∀ s t, K s t ≤ 1) :
      ∃ r ∈ stdSimplex ℝ Sector,
        (∀ w ∈ stdSimplex ℝ Sector,
          (∑ s, ∑ t, (1 - K s t) * w s * w t) ≤
            ∑ s, ∑ t, (1 - K s t) * r s * r t) ∧
        (∀ {R : Type} [Fintype R] [DecidableEq R],
          ∀ v : R × Sector → ℂ, (∑ z, ‖v z‖ ^ 2) = 1 →
          traceNorm (fun z w => ((1 - K z.2 w.2 : ℝ) : ℂ) * v z * star (v w)) ≤
            2 * (∑ s, ∑ t, (1 - K s t) * r s * r t)) := by
    classical
    have hRayleighMax
        (A : Sector → Sector → ℝ) (hA : ∀ i j, 0 ≤ A i j) :
        ∃ r ∈ stdSimplex ℝ Sector,
          (∀ w ∈ stdSimplex ℝ Sector,
            (∑ i, ∑ j, A i j * w i * w j) ≤ ∑ i, ∑ j, A i j * r i * r j) ∧
          (∀ p ∈ stdSimplex ℝ Sector,
            ∀ hB : Matrix.IsHermitian (fun i j =>
              ((Real.sqrt (p i) * Real.sqrt (p j) * A i j : ℝ) : ℂ)),
            ∀ k, hB.eigenvalues k ≤ ∑ i, ∑ j, A i j * r i * r j) := by
      classical
      let quadratic (y : Sector → ℝ) : ℝ := ∑ i, ∑ j, A i j * y i * y j
      let weighted (p : Sector → ℝ) (x : Sector → ℂ) : ℝ :=
        ∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (p j) * A i j * (star (x i) * x j).re
      let i₀ : Sector := Classical.arbitrary Sector
      have hsimplex : (stdSimplex ℝ Sector).Nonempty :=
        ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
      have hcontinuous : Continuous quadratic := by
        dsimp [quadratic]
        fun_prop
      obtain ⟨r, hr, hmax⟩ :=
        (isCompact_stdSimplex ℝ Sector).exists_isMaxOn hsimplex hcontinuous.continuousOn
      have hRayleigh (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector) (x : Sector → ℂ)
          (hx : (∑ i, ‖x i‖ ^ 2) = 1) : weighted p x ≤ quadratic r := by
        let y : Sector → ℝ := fun i => Real.sqrt (p i) * ‖x i‖
        let m : ℝ := ∑ i, y i
        have hy (i : Sector) : 0 ≤ y i :=
          mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
        have hm : m ≤ 1 := by
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun i => Real.sqrt (p i)) (fun i => ‖x i‖)
          have hroot : (∑ i, Real.sqrt (p i) ^ 2) = 1 := by
            simp_rw [Real.sq_sqrt (hp.1 _)]
            exact hp.2
          rw [hroot, hx, one_mul] at hcs
          change m ^ 2 ≤ 1 at hcs
          nlinarith
        let w : Sector → ℝ := fun i => y i + (1 - m) * (Pi.single i₀ (1 : ℝ) : Sector → ℝ) i
        have hw : w ∈ stdSimplex ℝ Sector := by
          constructor
          · intro i
            exact add_nonneg (hy i) (mul_nonneg (sub_nonneg.mpr hm)
              ((single_mem_stdSimplex ℝ i₀).1 i))
          · change (∑ i : Sector, (y i + (1 - m) * (Pi.single i₀ (1 : ℝ) : Sector → ℝ) i)) = 1
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            have hs : (∑ i : Sector, Pi.single i₀ (1 : ℝ) i) = 1 :=
              (single_mem_stdSimplex ℝ i₀).2
            rw [hs]
            change m + (1 - m) * 1 = 1
            ring
        have hyw (i : Sector) : y i ≤ w i := by
          exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hm)
            ((single_mem_stdSimplex ℝ i₀).1 i))
        have hphase (i j : Sector) : (star (x i) * x j).re ≤ ‖x i‖ * ‖x j‖ := by
          calc
            (star (x i) * x j).re ≤ ‖star (x i) * x j‖ := Complex.re_le_norm _
            _ = ‖x i‖ * ‖x j‖ := by rw [norm_mul, norm_star]
        calc
          weighted p x ≤ quadratic y := by
            dsimp [weighted, quadratic]
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            have hcoeff : 0 ≤ Real.sqrt (p i) * Real.sqrt (p j) * A i j :=
              mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hA i j)
            have h := mul_le_mul_of_nonneg_left (hphase i j) hcoeff
            calc
              _ ≤ Real.sqrt (p i) * Real.sqrt (p j) * A i j * (‖x i‖ * ‖x j‖) := h
              _ = _ := by dsimp [y]; ring
          _ ≤ quadratic w := by
            dsimp [quadratic]
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hyw i) (hA i j))
              (hyw j) (hy j) (mul_nonneg (hA i j) (hw.1 i))
          _ ≤ quadratic r := hmax hw
      refine ⟨r, hr, (fun w hw => hmax hw), ?_⟩
      intro p hp hB k
      let x : Sector → ℂ := ⇑(hB.eigenvectorBasis k)
      have hx : (∑ i, ‖x i‖ ^ 2) = 1 := by
        change (∑ i, ‖(hB.eigenvectorBasis k) i‖ ^ 2) = 1
        rw [← EuclideanSpace.norm_sq_eq, hB.eigenvectorBasis.orthonormal.1 k]
        norm_num
      have hform :
          (star x ⬝ᵥ ((fun i j =>
            ((Real.sqrt (p i) * Real.sqrt (p j) * A i j : ℝ) : ℂ)) *ᵥ x)).re = weighted p x := by
        dsimp [weighted]
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
          Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [starRingEnd_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_mul, sub_zero]
        ring
      calc
        hB.eigenvalues k =
            (star x ⬝ᵥ ((fun i j =>
              ((Real.sqrt (p i) * Real.sqrt (p j) * A i j : ℝ) : ℂ)) *ᵥ x)).re := hB.eigenvalues_eq k
        _ = weighted p x := hform
        _ ≤ quadratic r := hRayleigh p hp x hx
    have hEmbedding {R : Type} [Fintype R] [DecidableEq R]
        (v : R × Sector → ℂ) (hv : (∑ z, ‖v z‖ ^ 2) = 1) :
        ∃ p ∈ stdSimplex ℝ Sector,
          ∃ U : Matrix (R × Sector) Sector ℂ,
            Uᴴ * U = 1 ∧
            v = U *ᵥ (fun i => (Real.sqrt (p i) : ℂ)) ∧
            (∀ z i, z.2 ≠ i → U z i = 0) := by
      classical
      have hR : Nonempty R := by
        by_contra h
        have : IsEmpty R := not_nonempty_iff.mp h
        simp at hv
      let r₀ : R := Classical.choice hR
      let p : Sector → ℝ := fun i => ∑ r, ‖v (r, i)‖ ^ 2
      have hpnonneg (i : Sector) : 0 ≤ p i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hpsum : (∑ i, p i) = 1 := by
        change (∑ i, ∑ r, ‖v (r, i)‖ ^ 2) = 1
        rw [Finset.sum_comm]
        simpa only [Fintype.sum_prod_type] using hv
      have hp : p ∈ stdSimplex ℝ Sector := ⟨hpnonneg, hpsum⟩
      have hzero (i : Sector) (hi : p i = 0) (r : R) : v (r, i) = 0 := by
        have hterm : ‖v (r, i)‖ ^ 2 ≤ p i := by
          dsimp [p]
          exact Finset.single_le_sum (fun r _ => sq_nonneg ‖v (r, i)‖) (Finset.mem_univ r)
        rw [hi] at hterm
        have hn : ‖v (r, i)‖ = 0 := by nlinarith [norm_nonneg (v (r, i))]
        exact norm_eq_zero.mp hn
      let g : Sector → R → ℂ := fun i r =>
        if 0 < p i then v (r, i) / (Real.sqrt (p i) : ℂ)
        else (Pi.single r₀ (1 : ℂ) : R → ℂ) r
      have hg (i : Sector) : (∑ r, ‖g i r‖ ^ 2) = 1 := by
        by_cases hi : 0 < p i
        · have hs : Real.sqrt (p i) ^ 2 = p i := Real.sq_sqrt (hpnonneg i)
          have hn : p i ≠ 0 := ne_of_gt hi
          simp only [g, if_pos hi, norm_div, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
          rw [← Finset.sum_div, hs]
          change p i / p i = 1
          exact div_self hn
        · simp only [g, if_neg hi]
          rw [Finset.sum_eq_single r₀]
          · simp
          · intro r _ hr
            simp [Pi.single_apply, hr]
          · intro hr
            exact False.elim (hr (Finset.mem_univ r₀))
      have hvector (r : R) (i : Sector) :
          v (r, i) = g i r * (Real.sqrt (p i) : ℂ) := by
        by_cases hi : 0 < p i
        · have hs : (Real.sqrt (p i) : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hi))
          simp [g, hi, hs]
        · have hpi : p i = 0 := le_antisymm (not_lt.mp hi) (hpnonneg i)
          simp [g, hi, hpi, hzero i hpi r]
      let U : Matrix (R × Sector) Sector ℂ := fun z i => if z.2 = i then g i z.1 else 0
      have hU : Uᴴ * U = 1 := by
        ext i j
        change (∑ z : R × Sector, star (U z i) * U z j) =
          (if i = j then 1 else 0)
        rw [Fintype.sum_prod_type]
        by_cases hij : i = j
        · subst j
          simp only [U, apply_ite, star_zero,
            ite_mul, mul_ite, zero_mul, mul_zero]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          simp only [Complex.star_def, Complex.conj_mul']
          have hc : (∑ r, ((‖g i r‖ ^ 2 : ℝ) : ℂ)) = 1 := by
            exact_mod_cast hg i
          simpa using hc
        · simp only [if_neg hij]
          apply Finset.sum_eq_zero
          intro r _
          apply Finset.sum_eq_zero
          intro t _
          by_cases ht : t = i
          · have htj : t ≠ j := by simpa [ht] using hij
            simp [U, ht, hij]
          · simp [U, ht]
      refine ⟨p, hp, U, hU, ?_, ?_⟩
      · funext z
        rcases z with ⟨r, i⟩
        simp only [Matrix.mulVec, dotProduct, U]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hvector r i
      · intro z i hzi
        simp [U, hzi]
    have hReconstruct {R : Type} [Fintype R] [DecidableEq R]
        (v : R × Sector → ℂ) (p : Sector → ℝ) (U : Matrix (R × Sector) Sector ℂ)
        (hv : v = U *ᵥ (fun i => (Real.sqrt (p i) : ℂ)))
        (hzero : ∀ z i, z.2 ≠ i → U z i = 0)
        (K : Sector → Sector → ℝ) :
        (fun z w => ((1 - K z.2 w.2 : ℝ) : ℂ) * v z * star (v w) :
          Matrix (R × Sector) (R × Sector) ℂ) =
        (U * (Matrix.of fun i j =>
          ((Real.sqrt (p i) * Real.sqrt (p j) * (1 - K i j) : ℝ) : ℂ)) :
            Matrix (R × Sector) Sector ℂ) * Uᴴ := by
      classical
      have hentry (z : R × Sector) : v z = U z z.2 * (Real.sqrt (p z.2) : ℂ) := by
        rw [hv]
        change (∑ i, U z i * (Real.sqrt (p i) : ℂ)) = _
        apply Finset.sum_eq_single
        · intro i _ hi
          rw [hzero z i (Ne.symm hi), zero_mul]
        · intro hi
          exact False.elim (hi (Finset.mem_univ z.2))
      ext z w
      change ((1 - K z.2 w.2 : ℝ) : ℂ) * v z * star (v w) = _
      rw [hentry z, hentry w, star_mul, Complex.star_def, Complex.conj_ofReal]
      have hproduct :
          ((U * (Matrix.of fun i j =>
            ((Real.sqrt (p i) * Real.sqrt (p j) * (1 - K i j) : ℝ) : ℂ)) :
              Matrix (R × Sector) Sector ℂ) * Uᴴ) z w =
          U z z.2 *
            ((Real.sqrt (p z.2) * Real.sqrt (p w.2) * (1 - K z.2 w.2) : ℝ) : ℂ) *
            star (U w w.2) := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single w.2]
        · rw [Matrix.mul_apply, Finset.sum_eq_single z.2]
          · rfl
          · intro i _ hi
            rw [hzero z i (Ne.symm hi), zero_mul]
          · intro hi
            exact False.elim (hi (Finset.mem_univ z.2))
        · intro i _ hi
          rw [Matrix.conjTranspose_apply, hzero w i (Ne.symm hi), star_zero, mul_zero]
        · intro hi
          exact False.elim (hi (Finset.mem_univ w.2))
      rw [hproduct]
      push_cast
      simp only [starRingEnd_apply]
      ring
    have hInertia
        (P N : Matrix Sector Sector ℂ) (hP : P.PosSemidef) (hN : N.PosSemidef)
        (hrank : P.rank ≤ 1) (htrace : (P - N).trace = 0)
        (q : ℝ) (hq : 0 ≤ q)
        (hbound : ∀ i, (hP.isHermitian.sub hN.isHermitian).eigenvalues i ≤ q) :
        traceNorm (P - N) ≤ 2 * q := by
      classical
      let B := P - N
      have hB : B.IsHermitian := hP.isHermitian.sub hN.isHermitian
      have hcount : posIndex hB ≤ 1 := by
        let W := LinearMap.range (hermPosPart hB).mulVecLin
        have hW : PosDefOn P W := by
          intro x hx hne
          have hpositive := posDefOn_range_hermPosPart hB x hx hne
          have hnonnegative := hermForm_nonneg_of_posSemidef hN x
          change 0 < hermForm (P - N) x at hpositive
          rw [hermForm_sub] at hpositive
          linarith
        calc
          posIndex hB = Module.finrank ℂ W := (finrank_range_hermPosPart hB).symm
          _ ≤ posIndex hP.isHermitian := finrank_le_posIndex_of_posDefOn hP.isHermitian hW
          _ = P.rank := posIndex_eq_rank_of_posSemidef hP
          _ ≤ 1 := hrank
      have hmass : (∑ i, (hB.eigenvalues i)⁺) ≤ q := by
        let S := Finset.univ.filter (fun i => 0 < hB.eigenvalues i)
        have hS : S.card ≤ 1 := hcount
        have hsum : (∑ i, (hB.eigenvalues i)⁺) = ∑ i ∈ S, hB.eigenvalues i := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : 0 < hB.eigenvalues i
          · simp [hi, posPart_eq_self.mpr hi.le]
          · simp [hi, posPart_eq_zero.mpr (not_lt.mp hi)]
        rw [hsum]
        calc
          (∑ i ∈ S, hB.eigenvalues i) ≤ ∑ _i ∈ S, q :=
            Finset.sum_le_sum fun i _ => hbound i
          _ = (S.card : ℝ) * q := by simp
          _ ≤ 1 * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hq
          _ = q := one_mul _
      have hpos : (posPart B : Matrix Sector Sector ℂ) = hermPosPart hB := by
        rw [CFC.posPart_def, cfcₙ_eq_cfc, hB.cfc_eq]
        rfl
      have hneg : (negPart B : Matrix Sector Sector ℂ) = hermNegPart hB := by
        rw [CFC.negPart_def, cfcₙ_eq_cfc, hB.cfc_eq]
        rfl
      have hzero : rtrace B = 0 := by simp [rtrace, B, htrace]
      have hbalance : rtrace (hermNegPart hB) = rtrace (hermPosPart hB) := by
        have h := rtrace_sub_decomp hB
        rw [hzero] at h
        linarith
      have hnorm : traceNorm B = rtrace (hermPosPart hB) + rtrace (hermNegPart hB) := by
        have h := congrArg (fun A : Matrix Sector Sector ℂ => (Matrix.trace A).re)
          (CFC.posPart_add_negPart B hB)
        simpa [hpos, hneg, rtrace, Matrix.trace_add, CFC.abs,
          Matrix.star_eq_conjTranspose, traceNorm] using h.symm
      change traceNorm B ≤ 2 * q
      rw [hnorm, hbalance, rtrace_hermPosPart]
      linarith
    obtain ⟨r, hr, hmax, heigen⟩ := hRayleighMax (fun i j => 1 - K i j)
      (fun i j => sub_nonneg.mpr (hone i j))
    refine ⟨r, hr, hmax, ?_⟩
    intro R _ _ v hv
    obtain ⟨p, hp, U, hU, hvec, hzero⟩ := hEmbedding v hv
    let c : Sector → ℂ := fun i => (Real.sqrt (p i) : ℂ)
    let P : Matrix Sector Sector ℂ := Matrix.vecMulVec c (star c)
    let D : Matrix Sector Sector ℂ := Matrix.diagonal c
    let N : Matrix Sector Sector ℂ := D * (Matrix.of fun i j => (K i j : ℂ)) * Dᴴ
    have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star c
    have hN : N.PosSemidef := hK.mul_mul_conjTranspose_same D
    have hB : P - N = (Matrix.of fun i j =>
        ((Real.sqrt (p i) * Real.sqrt (p j) * (1 - K i j) : ℝ) : ℂ)) := by
      ext i j
      simp [P, N, D, c, Matrix.vecMulVec_apply, Matrix.diagonal_mul,
        Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Complex.star_def]
      ring
    have htrace : (P - N).trace = 0 := by
      rw [hB]
      simp [Matrix.trace, hdiag]
    let q : ℝ := ∑ i, ∑ j, (1 - K i j) * r i * r j
    have hq : 0 ≤ q := by
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (sub_nonneg.mpr (hone i j)) (hr.1 i)) (hr.1 j)
    have hbound : ∀ i, (hP.isHermitian.sub hN.isHermitian).eigenvalues i ≤ q := by
      intro i
      have hHermitian := hP.isHermitian.sub hN.isHermitian
      rw [hB] at hHermitian
      have h := heigen p hp hHermitian i
      have htransport (A B : Matrix Sector Sector ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
          (heq : A = B) : hA.eigenvalues = hB.eigenvalues := by
        subst B
        rfl
      have heq := htransport _ _ hHermitian (hP.isHermitian.sub hN.isHermitian) hB.symm
      calc
        _ = hHermitian.eigenvalues i := (congrFun heq i).symm
        _ ≤ q := h
    have hmatrix : traceNorm (P - N) ≤ 2 * q :=
      hInertia P N hP hN (Matrix.rank_vecMulVec_le c (star c)) htrace q hq hbound
    have hraw := hReconstruct v p U hvec hzero K
    rw [← hB] at hraw
    rw [hraw, hIsometricNorm U hU]
    exact hmatrix

  obtain ⟨r, hr, hQuadraticMax, hPureSchurBound⟩ :=
    hSchurPureUpper (kernel M) hKernelProperties.1
      hKernelProperties.2.1 hKernelProperties.2.2
  have hQuadraticComplement (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector) :
      (∑ s, ∑ t, (1 - kernel M s t) * p s * p t) =
        1 - ∑ s, ∑ t, p s * p t * kernel M s t := by
    calc
      _ = ∑ s, ∑ t, (p s * p t - p s * p t * kernel M s t) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = (∑ s, p s) * (∑ t, p t) - ∑ s, ∑ t, p s * p t * kernel M s t := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
      _ = _ := by rw [hp.2]; ring
  have hSpectralMinimum : spectralMinimum M = ∑ s, ∑ t, r s * r t * kernel M s t := by
    let values : Set ℝ := {q : ℝ | ∃ p ∈ stdSimplex ℝ Sector,
      q = ∑ s, ∑ t, p s * p t * kernel M s t}
    have hmem : (∑ s, ∑ t, r s * r t * kernel M s t) ∈ values := ⟨r, hr, rfl⟩
    have hLower : ∀ q ∈ values, (∑ s, ∑ t, r s * r t * kernel M s t) ≤ q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := hq
      have h := hQuadraticMax p hp
      rw [hQuadraticComplement p hp, hQuadraticComplement r hr] at h
      linarith
    change sInf values = _
    exact le_antisymm (csInf_le ⟨_, hLower⟩ hmem) (le_csInf ⟨_, hmem⟩ hLower)
  have hOptimalValueNonneg : 0 ≤ 2 * (1 - spectralMinimum M) := by
    rw [hSpectralMinimum, ← hQuadraticComplement r hr]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ =>
      Finset.sum_nonneg fun t _ =>
        mul_nonneg (mul_nonneg (sub_nonneg.mpr (hKernelProperties.2.2 s t)) (hr.1 s))
          (hr.1 t))

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

  have hEncodedDiamondUpper
      (C : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d))
      (hC : ∀ X : Matrix Sector Sector ℂ,
        CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
            (targetEncoding M.d)ᴴ) :
      diamondDistance C encoding.target ≤ 2 * (1 - spectralMinimum M) := by
    have hTargetOne : ∀ X : Matrix Sector Sector ℂ,
        CStarMatrix.ofMatrix.symm
          (encoding.target.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
            targetEncoding M.d * (Matrix.of fun s t => (1 : ℂ) * X s t) *
              (targetEncoding M.d)ᴴ := by
      intro X
      have hX : (Matrix.of fun s t => (1 : ℂ) * X s t) = X := by ext s t; simp
      rw [hX]
      exact encoding.targetAction X
    have hTargetIsometry :
        (targetEncoding M.d)ᴴ * targetEncoding M.d = 1 := by
      ext s t
      let E : Matrix Sector Sector ℂ := Matrix.single t s 1
      have htrace := encoding.target.trace_preserving (CStarMatrix.ofMatrix E)
      change Matrix.trace (CStarMatrix.ofMatrix.symm
        (encoding.target.toCompletelyPositiveMap (CStarMatrix.ofMatrix E))) =
          Matrix.trace E at htrace
      rw [encoding.targetAction E, Matrix.trace_mul_cycle] at htrace
      have hentry : ((targetEncoding M.d)ᴴ * targetEncoding M.d) s t =
          (Matrix.single t s (1 : ℂ)).trace := by
        simpa [E, Matrix.trace_mul_single] using htrace
      by_cases hst : s = t
      · subst t
        simpa using hentry
      · simpa [Matrix.one_apply, hst, Ne.symm hst] using hentry
    have hPure {R : Type} [Fintype R] [DecidableEq R]
        (tau : DensityState (R × Sector)) (htau : IsPure tau) :
        referenceError C encoding.target tau ≤ 2 * (1 - spectralMinimum M) := by
      obtain ⟨v, hv⟩ := htau
      let T : Matrix (R × (TargetLocal M.d × TargetLocal M.d)) (R × Sector) ℂ :=
        (1 : Matrix R R ℂ) ⊗ₖ targetEncoding M.d
      have hT : Tᴴ * T = 1 := by
        dsimp only [T]
        rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul]
        have hW : (targetEncoding M.d)ᴴ * targetEncoding M.d = 1 := hTargetIsometry
        rw [hW, Matrix.one_kronecker_one]
      let B : Matrix (R × Sector) (R × Sector) ℂ :=
        Matrix.of fun z w => ((1 - kernel M z.2 w.2 : ℝ) : ℂ) * v z * star (v w)
      have hFirst := hReferenceSchurLift C (targetEncoding M.d)
        (fun s t => (kernel M s t : ℂ)) hC (Matrix.vecMulVec v (star v))
      have hSecond := hReferenceSchurLift encoding.target (targetEncoding M.d)
        (fun _ _ => (1 : ℂ)) hTargetOne (Matrix.vecMulVec v (star v))
      have hDiff : CStarMatrix.ofMatrix.symm (referenceState C tau).1 -
          CStarMatrix.ofMatrix.symm (referenceState encoding.target tau).1 = T * (-B) * Tᴴ := by
        change CStarMatrix.ofMatrix.symm (referenceAction C tau.1) -
          CStarMatrix.ofMatrix.symm (referenceAction encoding.target tau.1) = _
        rw [hv, hFirst, hSecond]
        change T * _ * Tᴴ - T * _ * Tᴴ = _
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        congr 2
        ext z w
        simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.neg_apply, B,
          Matrix.vecMulVec_apply, Pi.star_apply]
        push_cast
        ring
      have htrace : (Matrix.vecMulVec v (star v)).trace = 1 := by
        change Matrix.trace (CStarMatrix.ofMatrix (Matrix.vecMulVec v (star v))) = 1
        rw [← hv]
        exact tau.2.2
      have hvComplex : ((∑ z, ‖v z‖ ^ 2 : ℝ) : ℂ) = 1 := by
        calc
          _ = (Matrix.vecMulVec v (star v)).trace := by
            simp [Matrix.trace, Matrix.vecMulVec_apply, Complex.mul_conj,
              Complex.normSq_eq_norm_sq, Complex.ofReal_sum]
          _ = 1 := htrace
      have hvNorm : (∑ z, ‖v z‖ ^ 2) = 1 := by exact_mod_cast hvComplex
      change traceNorm (CStarMatrix.ofMatrix.symm (referenceState C tau).1 -
        CStarMatrix.ofMatrix.symm (referenceState encoding.target tau).1) ≤ _
      rw [hDiff, hIsometricNorm T hT]
      rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg]
      have h := hPureSchurBound v hvNorm
      rw [hQuadraticComplement r hr, ← hSpectralMinimum] at h
      exact h
    change sSup _ ≤ _
    apply csSup_le (by exact ⟨0, Or.inl rfl⟩)
    intro x hx
    rcases hx with hx | ⟨n, rho, rfl⟩
    · rcases hx with rfl
      exact hOptimalValueNonneg
    · obtain ⟨tau, htau, hle⟩ := (D5.S3.Quantum.Foundation.FiniteDiamondDistance.result C encoding.target).1 rho
      exact hle.trans (hPure tau htau)

  exact ⟨hKernelProperties, r, hr, hSpectralMinimum, hEncodedDiamondUpper⟩

end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
