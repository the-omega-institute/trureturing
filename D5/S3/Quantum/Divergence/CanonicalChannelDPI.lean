/- GID: D5/S3/Quantum/Divergence/CanonicalChannelDPI
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CanonicalChannelDPI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support-aware relative entropy decreases under finite quantum channels. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Topology
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Divergence.CanonicalChannelDPI

-- Nested finite carrier and spectral sums require a larger elaboration budget.

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

open scoped Classical



-- This is the original support-independent comparison proof and its original budget.
set_option maxHeartbeats 2000000 in
/-- The diagonal comparison used by the canonical DPI after its physical model is built. -/
theorem diagonal_log_comparison
    {n : Type u} {m : Type v} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (p : n → ℝ) (q : m → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (V : Matrix n m ℂ) (ξ : n → ℂ) (η : m → ℂ)
    (hV : Vᴴ * V ≤ 1)
    (hVA : Vᴴ * diagonal (fun i => (p i : ℂ)) * V ≤ diagonal (fun i => (q i : ℂ)))
    (hVX : V *ᵥ η = ξ) (hξ : ∑ i, ‖ξ i‖ ^ 2 = 1) (hη : ∑ i, ‖η i‖ ^ 2 = 1) :
    (star ξ ⬝ᵥ (cfc Real.log (diagonal (fun i => (p i : ℂ))) *ᵥ ξ)).re ≤
      (star η ⬝ᵥ (cfc Real.log (diagonal (fun i => (q i : ℂ))) *ᵥ η)).re := by
  classical
  have rectangularCFCAmbient {n m : Type (max u v)} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (hZ : Z.IsHermitian) (hC : C.IsHermitian)
      (W : Matrix n m ℂ) (h : Z * W = W * C) (f : ℝ → ℝ) : cfc f Z * W = W * cfc f C := by
    classical
    let U : Matrix n n ℂ := hZ.eigenvectorUnitary; let T : Matrix m m ℂ := hC.eigenvectorUnitary; let E : Matrix n m ℂ := Uᴴ * W * T; have hU : Uᴴ * U = 1 := hZ.eigenvectorUnitary.2.1
    have hu : U * Uᴴ = 1 := hZ.eigenvectorUnitary.2.2; have hT : Tᴴ * T = 1 := hC.eigenvectorUnitary.2.1; have ht : T * Tᴴ = 1 := hC.eigenvectorUnitary.2.2
    have zs : Z = U * diagonal (fun i => (hZ.eigenvalues i : ℂ)) * Uᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hZ.spectral_theorem
    have cs : C = T * diagonal (fun i => (hC.eigenvalues i : ℂ)) * Tᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
    have coeff : diagonal (fun i => (hZ.eigenvalues i : ℂ)) * E = E * diagonal (fun j => (hC.eigenvalues j : ℂ)) := by
      calc
        _ = Uᴴ * (Z * W) * T := by
          conv_rhs => { rw [zs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
        _ = Uᴴ * (W * C) * T := by rw [h]
        _ = _ := by
          conv_lhs => { rw [cs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
    have fcoeff : diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * E = E * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) := by
      ext i j; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]; have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
      by_cases he : hZ.eigenvalues i = hC.eigenvalues j
      · rw [he, mul_comm]
      · have hz : E i j = 0 := by
          have hn : (hZ.eigenvalues i : ℂ) ≠ (hC.eigenvalues j : ℂ) := by { exact_mod_cast he }; have heq : ((hZ.eigenvalues i : ℂ) - (hC.eigenvalues j : ℂ)) * E i j = 0 := by
            linear_combination eq
          exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
        simp only [hz, mul_zero, zero_mul]
    have reconstruct : U * E * Tᴴ = W := by
      simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu, Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
    rw [hZ.cfc_eq, hC.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
    change (U * diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * Uᴴ) * W = W * (T * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) * Tᴴ)
    conv_lhs => { rw [← reconstruct] }; conv_rhs => { rw [← reconstruct] }; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
      ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc _ E, fcoeff]; simp only [Matrix.mul_assoc]
  have rectangularCFCOutput {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
      (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (hZ : Z.IsHermitian) (hC : C.IsHermitian) (W : Matrix n m ℂ) (h : Z * W = W * C) (f : ℝ → ℝ) : cfc f Z * W = W * cfc f C := by
    classical
    let U : Matrix n n ℂ := hZ.eigenvectorUnitary; let T : Matrix m m ℂ := hC.eigenvectorUnitary; let E : Matrix n m ℂ := Uᴴ * W * T; have hU : Uᴴ * U = 1 := hZ.eigenvectorUnitary.2.1
    have hu : U * Uᴴ = 1 := hZ.eigenvectorUnitary.2.2; have hT : Tᴴ * T = 1 := hC.eigenvectorUnitary.2.1; have ht : T * Tᴴ = 1 := hC.eigenvectorUnitary.2.2
    have zs : Z = U * diagonal (fun i => (hZ.eigenvalues i : ℂ)) * Uᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hZ.spectral_theorem
    have cs : C = T * diagonal (fun i => (hC.eigenvalues i : ℂ)) * Tᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, U, T, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hC.spectral_theorem
    have coeff : diagonal (fun i => (hZ.eigenvalues i : ℂ)) * E = E * diagonal (fun j => (hC.eigenvalues j : ℂ)) := by
      calc
        _ = Uᴴ * (Z * W) * T := by
          conv_rhs => { rw [zs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
        _ = Uᴴ * (W * C) * T := by rw [h]
        _ = _ := by
          conv_lhs => { rw [cs] }; simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
    have fcoeff : diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * E = E * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) := by
      ext i j; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]; have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff; simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
      by_cases he : hZ.eigenvalues i = hC.eigenvalues j
      · rw [he, mul_comm]
      · have hz : E i j = 0 := by
          have hn : (hZ.eigenvalues i : ℂ) ≠ (hC.eigenvalues j : ℂ) := by { exact_mod_cast he }; have heq : ((hZ.eigenvalues i : ℂ) - (hC.eigenvalues j : ℂ)) * E i j = 0 := by
            linear_combination eq
          exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
        simp only [hz, mul_zero, zero_mul]
    have reconstruct : U * E * Tᴴ = W := by
      simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu, Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
    rw [hZ.cfc_eq, hC.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
    change (U * diagonal (fun i => (f (hZ.eigenvalues i) : ℂ)) * Uᴴ) * W = W * (T * diagonal (fun j => (f (hC.eigenvalues j) : ℂ)) * Tᴴ)
    conv_lhs => { rw [← reconstruct] }; conv_rhs => { rw [← reconstruct] }; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
      ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc _ E, fcoeff]; simp only [Matrix.mul_assoc]
  have matrixLogOrder {n : Type v} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hA : A.PosDef) (hab : A ≤ B) : cfc Real.log A ≤ cfc Real.log B := by
    classical
    let e := CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ); have hB : B.PosSemidef := (hA.posSemidef.nonneg.trans hab).posSemidef
    have logMap (X : Matrix n n ℂ) (hX : X.IsHermitian) : e (cfc Real.log X) = CFC.log (e X) := by
      exact StarAlgHomClass.map_cfc e Real.log X (X.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have posA : IsStrictlyPositive (e A) := by
      exact (hA.isUnit.map e.toAlgEquiv.toAlgHom).isStrictlyPositive (map_nonneg e hA.posSemidef.nonneg)
    have hAB : e A ≤ e B := by
      have h := map_nonneg e (sub_nonneg.mpr hab); apply sub_nonneg.mp; simpa only [map_sub] using h
    have h := CFC.log_le_log hAB posA; rw [← logMap A hA.1, ← logMap B hB.1] at h; have h' := map_nonneg e.symm (sub_nonneg.mpr h)
    simpa only [map_sub, StarAlgEquiv.symm_apply_apply, sub_nonneg] using h'
  have matrixLogMidpoint {n : Type (max u v)} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) : (1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B ≤
        cfc Real.log ((1/2 : ℝ) • A + (1/2 : ℝ) • B) := by
    classical
    let e := CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ); have pos (X : Matrix n n ℂ) (hX : X.PosDef) : IsStrictlyPositive (e X) := by
      exact (hX.isUnit.map e.toAlgEquiv.toAlgHom).isStrictlyPositive (map_nonneg e hX.posSemidef.nonneg)
    have midpoint : ((1/2 : ℝ) • A + (1/2 : ℝ) • B).IsHermitian := by
      exact (hA.1.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)).add (hB.1.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl))
    have logMap (X : Matrix n n ℂ) (hX : X.IsHermitian) : e (cfc Real.log X) = CFC.log (e X) := by
      exact StarAlgHomClass.map_cfc e Real.log X (X.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hX (by exact hX)
    have h := (CFC.concaveOn_log (A := CStarMatrix n n ℂ)).2 (pos A hA) (pos B hB) (show 0 ≤ (1/2 : ℝ) by norm_num) (show 0 ≤ (1/2 : ℝ) by norm_num) (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
    rw [← logMap A hA.1, ← logMap B hB.1] at h; change e ((1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B) ≤ CFC.log (e ((1/2 : ℝ) • A + (1/2 : ℝ) • B)) at h
    rw [← logMap _ midpoint] at h; have h' := map_nonneg e.symm (sub_nonneg.mpr h); change 0 ≤ (cfc Real.log ((1/2 : ℝ) • A + (1/2 : ℝ) • B) -
      ((1/2 : ℝ) • cfc Real.log A + (1/2 : ℝ) • cfc Real.log B)) at h'
    exact sub_nonneg.mp h'
  have compressedPositiveAmbient {n m : Type (max u v)} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
      (hW : Wᴴ * W = 1) : (Wᴴ * F * W).PosDef := by
    classical
    apply hF.conjTranspose_mul_mul_same; intro x y hxy; have h := congrArg (fun z => Wᴴ *ᵥ z) hxy; simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using h
  have compressedPositiveOutput {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
      (hW : Wᴴ * W = 1) : (Wᴴ * F * W).PosDef := by
    classical
    apply hF.conjTranspose_mul_mul_same; intro x y hxy; have h := congrArg (fun z => Wᴴ *ᵥ z) hxy; simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using h

  have reflectionFacts {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) :
      let P := W * Wᴴ
      let U := P + P - 1
      Uᴴ = U ∧ U * U = 1 ∧ U * W = W ∧ ((1 / 2 : ℝ) • (F + U * F * U)) * W = W * (Wᴴ * F * W) := by
    classical
    dsimp only; let P := W * Wᴴ; let U := P + P - 1; have hp : P * P = P := by
      change (W * Wᴴ) * (W * Wᴴ) = _; rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
    have hpW : P * W = W := by
      change (W * Wᴴ) * W = _; rw [Matrix.mul_assoc, hW, Matrix.mul_one]
    have hs : Uᴴ = U := by
      simp only [U, P, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hu : U * U = 1 := by
      simp only [U, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hp]
      abel
    have hUW : U * W = W := by
      simp only [U, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, hpW]; abel
    refine ⟨hs, hu, hUW, ?_⟩; change ((1 / 2 : ℝ) • (F + U * F * U)) * W = _; rw [Matrix.smul_mul, Matrix.add_mul]; simp only [Matrix.mul_assoc, hUW]; rw [← Matrix.mul_assoc U F W]
    have twice : F * W + U * F * W = (W * (Wᴴ * F * W)) + (W * (Wᴴ * F * W)) := by
      simp only [U, P, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]; abel
    rw [twice, ← two_smul ℝ, smul_smul]; norm_num <;> simp only [Matrix.mul_assoc]
  have isometryLogCompression {n : Type (max u v)} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (F : Matrix n n ℂ) (W : Matrix n m ℂ) (hF : F.PosDef)
      (hW : Wᴴ * W = 1) : Wᴴ * cfc Real.log F * W ≤ cfc Real.log (Wᴴ * F * W) := by
    classical
    let P := W * Wᴴ; let U := P + P - 1; let C := Wᴴ * F * W; let Z := (1/2 : ℝ) • (F + U * F * U); obtain ⟨hs, hu, hUW, hZW⟩ := reflectionFacts F W hW; change Uᴴ = U at hs
    change U * U = 1 at hu; change U * W = W at hUW; change Z * W = W * C at hZW; have hUiso : Uᴴ * U = 1 := by { rw [hs, hu] }; have hUF : (U * F * U).PosDef := by
      have h := compressedPositiveAmbient F U hF hUiso; simpa only [hs] using h
    have hC : C.PosDef := compressedPositiveOutput F W hF hW; have hZ : Z.IsHermitian := by
      exact (hF.1.add hUF.1).smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)
    have cov : cfc Real.log (U * F * U) = U * cfc Real.log F * U := by
      have he : (U * F * U) * U = U * F := by
        simp only [Matrix.mul_assoc, hu, Matrix.mul_one]
      have h := rectangularCFCAmbient (U * F * U) F hUF.1 hF.1 U he Real.log; have h' := congrArg (fun M : Matrix n n ℂ => M * U) h
      simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using h'
    have compression : Wᴴ * cfc Real.log Z * W = cfc Real.log C := by
      have h := rectangularCFCOutput Z C hZ hC.1 W hZW Real.log; have h' := congrArg (fun M : Matrix n m ℂ => Wᴴ * M) h; simpa only [← Matrix.mul_assoc, hW, Matrix.one_mul] using h'
    have hWU : Wᴴ * U = Wᴴ := by
      have h := congrArg Matrix.conjTranspose hUW; simpa only [Matrix.conjTranspose_mul, hs] using h
    have midpoint := matrixLogMidpoint F (U * F * U) hF hUF; have hz : (1/2 : ℝ) • F + (1/2 : ℝ) • (U * F * U) = Z := by
      rw [← smul_add]
    rw [hz] at midpoint; have ps := (Matrix.le_iff.mp midpoint).conjTranspose_mul_mul_same W; have hleft : Wᴴ * ((1/2 : ℝ) • cfc Real.log F + (1/2 : ℝ) • cfc Real.log (U * F * U)) * W =
        Wᴴ * cfc Real.log F * W := by
      rw [cov]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hUW, ← Matrix.mul_assoc Wᴴ U, hWU]
      rw [← add_smul]; norm_num
    apply Matrix.le_iff.mpr; simpa only [Matrix.mul_sub, Matrix.sub_mul, compression, hleft] using ps

  have defectFacts {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (V : Matrix n m ℂ) (ξ : n → ℂ) (η : m → ℂ) (hV : Vᴴ * V ≤ 1) (hVX : V *ᵥ η = ξ)
      (hξ : ∑ i, ‖ξ i‖ ^ 2 = 1) (hη : ∑ i, ‖η i‖ ^ 2 = 1) :
      let D := CFC.sqrt (1 - Vᴴ * V)
      let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
      Wᴴ * W = 1 ∧ D *ᵥ η = 0 ∧ W *ᵥ η = Sum.elim ξ 0 := by
    classical
    let E : Matrix m m ℂ := 1 - Vᴴ * V; let D : Matrix m m ℂ := CFC.sqrt E; let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
    change Wᴴ * W = 1 ∧ D *ᵥ η = 0 ∧ W *ᵥ η = Sum.elim ξ 0; have hE : 0 ≤ E := sub_nonneg.mpr hV; have hD : D.PosSemidef := (CFC.sqrt_nonneg E).posSemidef; have hDD : Dᴴ * D = E := by
      rw [hD.1.eq]; exact CFC.sqrt_mul_sqrt_self E hE
    have hW : Wᴴ * W = Vᴴ * V + Dᴴ * D := by
      ext i j; change (∑ t : n ⊕ m, star (W t i) * W t j) = _; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply]
    have hw : Wᴴ * W = 1 := by
      rw [hW, hDD]; change Vᴴ * V + (1 - Vᴴ * V) = 1; abel
    have hnormξ : star ξ ⬝ᵥ ξ = 1 := by
      calc
        _ = ((∑ i, ‖ξ i‖ ^ 2 : ℝ) : ℂ) := by
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow, Complex.ofReal_sum]
        _ = 1 := by rw [hξ]; rfl
    have hnormη : star η ⬝ᵥ η = 1 := by
      calc
        _ = ((∑ i, ‖η i‖ ^ 2 : ℝ) : ℂ) := by
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow, Complex.ofReal_sum]
        _ = 1 := by rw [hη]; rfl
    have gram : star η ⬝ᵥ ((Vᴴ * V) *ᵥ η) = star (V *ᵥ η) ⬝ᵥ (V *ᵥ η) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
    have hz : star η ⬝ᵥ (E *ᵥ η) = 0 := by
      simp only [E, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, gram, hVX, hnormη, hnormξ, sub_self]
    have hd : D *ᵥ η = 0 := by
      have hg : star (D *ᵥ η) ⬝ᵥ (D *ᵥ η) = 0 := by
        calc
          _ = star η ⬝ᵥ ((Dᴴ * D) *ᵥ η) := by
            symm; rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
          _ = 0 := by rw [hDD]; exact hz
      exact dotProduct_star_self_eq_zero.mp hg
    refine ⟨hw, hd, ?_⟩; ext i; cases i with
    | inl i => exact congrFun hVX i
    | inr i => exact congrFun hd i
  have blockCompression {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (V : Matrix n m ℂ) (D : Matrix m m ℂ) (a : n → ℝ) (ε : ℝ) :
      let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i)
      let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim a (fun _ => ε) i : ℝ) : ℂ))
      Wᴴ * F * W = Vᴴ * diagonal (fun i => (a i : ℂ)) * V + ε • (Dᴴ * D) := by
    classical
    let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i); let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim a (fun _ => ε) i : ℝ) : ℂ))
    change Wᴴ * F * W = Vᴴ * diagonal (fun i => (a i : ℂ)) * V + ε • (Dᴴ * D); ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, F, Matrix.diagonal_apply]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Fintype.sum_sum_type]; simp only [W, Sum.elim_inl, Sum.elim_inr]; congr 1; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
    change star (D k i) * (ε : ℂ) * D k j = (ε : ℂ) * (star (D k i) * D k j); ring
  have finiteLogLimit {m : Type v} [Fintype m] (b c : m → ℝ) (hb : ∀ i, 0 < b i) (r : ℝ) (h : ∀ ε : ℝ, 0 < ε → r ≤ ∑ i, Real.log (b i + ε) * c i) : r ≤ ∑ i, Real.log (b i) * c i := by
    classical
    have ht : Filter.Tendsto (fun ε : ℝ => ∑ i, Real.log (b i + ε) * c i) (𝓝[>] 0) (𝓝 (∑ i, Real.log (b i) * c i)) := by
      apply tendsto_finsetSum; intro i _; have hi : ContinuousAt (fun ε : ℝ => Real.log (b i + ε) * c i) 0 := by
        apply ContinuousAt.mul _ continuousAt_const; exact (Real.continuousAt_log (by simpa only [add_zero] using ne_of_gt (hb i))).comp (continuousAt_const.add continuousAt_id)
      simpa only [add_zero] using hi.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, r ≤ ∑ i, Real.log (b i + ε) * c i := by
      filter_upwards [self_mem_nhdsWithin] with ε hε; exact h ε hε
    simpa only [add_zero] using ge_of_tendsto ht he
  have diagonalLogFormAmbient {m : Type (max u v)} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
      ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
    have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
      exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
    rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
    have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
    have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
    rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have diagonalLogFormInput {m : Type u} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
      ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
    have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
      exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
    rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
    have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
    have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
    rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have diagonalLogFormOutput {m : Type v} [Fintype m] [DecidableEq m] (d : m → ℝ) (x : m → ℂ) : (star x ⬝ᵥ (cfc Real.log (diagonal (fun i => (d i : ℂ))) *ᵥ x)).re =
      ∑ i, Real.log (d i) * ‖x i‖ ^ 2 := by
    have hlog : cfc Real.log (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (Real.log (d i) : ℂ)) := by
      exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal d
    rw [hlog]; change (RCLike.re : ℂ →+ ℝ) _ = _; simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]; apply Finset.sum_congr rfl; intro i _
    have term : star (x i) * ((Real.log (d i) : ℂ) * x i) = (Real.log (d i) : ℂ) * (star (x i) * x i) := by ring
    have eqnorm : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using RCLike.conj_mul (x i)
    rw [term, eqnorm, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

  have regularizedCore {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (p : n → ℝ) (q : m → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
      (V : Matrix n m ℂ) (ξ : n → ℂ) (η : m → ℂ) (hV : Vᴴ * V ≤ 1) (hVA : Vᴴ * diagonal (fun i => (p i : ℂ)) * V ≤ diagonal (fun i => (q i : ℂ)))
      (hVX : V *ᵥ η = ξ) (hξ : ∑ i, ‖ξ i‖ ^ 2 = 1) (hη : ∑ i, ‖η i‖ ^ 2 = 1) : (star ξ ⬝ᵥ (cfc Real.log (diagonal (fun i => (p i : ℂ))) *ᵥ ξ)).re ≤
        (star η ⬝ᵥ (cfc Real.log (diagonal (fun i => (q i : ℂ))) *ᵥ η)).re := by
    classical
    let A : Matrix n n ℂ := diagonal (fun i => (p i : ℂ)); let B : Matrix m m ℂ := diagonal (fun i => (q i : ℂ)); let E : Matrix m m ℂ := 1 - Vᴴ * V; let D := CFC.sqrt E
    let W : Matrix (n ⊕ m) m ℂ := Sum.elim (fun i => V i) (fun i => D i); obtain ⟨hW, hdη, hWη⟩ := defectFacts V ξ η hV hVX hξ hη; change Wᴴ * W = 1 at hW
    change W *ᵥ η = Sum.elim ξ 0 at hWη; have hE : 0 ≤ E := sub_nonneg.mpr hV; have hD : D.PosSemidef := (CFC.sqrt_nonneg E).posSemidef; have hDD : Dᴴ * D = E := by
      rw [hD.1.eq]; exact CFC.sqrt_mul_sqrt_self E hE
    have hbound (ε : ℝ) (hε : 0 < ε) : (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re ≤ ∑ i, Real.log (q i + ε) * ‖η i‖ ^ 2 := by
      let F : Matrix (n ⊕ m) (n ⊕ m) ℂ := diagonal (fun i => ((Sum.elim p (fun _ => ε) i : ℝ) : ℂ))
      let C := Wᴴ * F * W; have hF : F.PosDef := by
        apply Matrix.PosDef.diagonal; intro i; cases i with
        | inl i => exact_mod_cast hp i
        | inr i => exact_mod_cast hε
      have hC : C.PosDef := compressedPositiveOutput F W hF hW; have cf : C = Vᴴ * A * V + ε • E := by
        have h := blockCompression V D p ε; simpa only [hDD] using h
      have eLe : E ≤ 1 := sub_le_self _ (Matrix.posSemidef_conjTranspose_mul_self V).nonneg; have cLe : C ≤ B + ε • (1 : Matrix m m ℂ) := by
        rw [cf]; exact add_le_add hVA (smul_le_smul_of_nonneg_left eLe hε.le)
      have ord := (isometryLogCompression F W hF hW).trans (matrixLogOrder C (B + ε • (1 : Matrix m m ℂ)) hC cLe)
      have hr := (Matrix.le_iff.mp ord).re_dotProduct_nonneg η; rw [Matrix.sub_mulVec, dotProduct_sub, RCLike.re_to_complex, Complex.sub_re] at hr
      have gram : star η ⬝ᵥ (Wᴴ * cfc Real.log F * W) *ᵥ η = star (W *ᵥ η) ⬝ᵥ (cfc Real.log F *ᵥ (W *ᵥ η)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
      have ambient : (star (W *ᵥ η) ⬝ᵥ (cfc Real.log F *ᵥ (W *ᵥ η))).re = (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re := by
        rw [hWη]; rw [diagonalLogFormAmbient, diagonalLogFormInput]; simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
          norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]
      have bl : B + ε • (1 : Matrix m m ℂ) = diagonal (fun i => ((q i + ε : ℝ) : ℂ)) := by
        ext i j; by_cases h : i = j <;> simp [B, Matrix.diagonal_apply, Matrix.one_apply, h]
      rw [gram, ambient, bl, diagonalLogFormOutput] at hr; exact sub_nonneg.mp hr
    change (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re ≤ (star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re
    conv_rhs => { rw [diagonalLogFormOutput] }; exact finiteLogLimit q (fun i => ‖η i‖ ^ 2) hq _ hbound

  exact regularizedCore p q hp hq V ξ η hV hVA hVX hξ hη

#print axioms diagonal_log_comparison

-- The physical model provides the canonical positive-spectrum carriers.
set_option maxHeartbeats 2000000 in
/-- Data processing for the canonical support-aware relative entropy, in natural logarithms. -/
theorem extended_quantum_relative_entropy_channel_dpi
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) :
    extendedQuantumRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) ≤
      extendedQuantumRelativeEntropy ρ σ := by
  classical
  by_cases support : SupportContained ρ σ
  · let M := supported_relative_modular_model Φ ρ σ support
    let D := M.data
    rw [extendedQuantumRelativeEntropy_eq_coe_of_support M.outputSupport,
      extendedQuantumRelativeEntropy_eq_coe_of_support support]
    apply WithTop.coe_le_coe.mpr
    rw [M.canonicalTraceT, M.canonicalTraceR]
    apply neg_le_neg
    exact diagonal_log_comparison
      (fun ji : D.J × D.I => D.sj ji.1 / D.ri ji.2)
      (fun lk : D.L × D.K => D.ql lk.1 / D.pk lk.2)
      (fun ji => div_pos ji.1.2 ji.2.2) (fun lk => div_pos lk.1.2 lk.2.2)
      D.V D.ξ D.η M.hVnorm M.hVA M.mapsη M.normξ M.normη
  · rw [extendedQuantumRelativeEntropy_eq_top_of_not_support support]
    exact le_top

#print axioms extended_quantum_relative_entropy_channel_dpi

end D5.S3.Quantum.Divergence.CanonicalChannelDPI
