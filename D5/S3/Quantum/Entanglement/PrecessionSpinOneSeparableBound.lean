/- GID: D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Huynh-Vu–Zaw–Scarani Conjecture 2: the spin-1 tensor spin-K/2 precession separable bound. -/
/-
proof_shape: result: content
escape_witness: full_compression_identity (local proposition on the live path):
  ∀ (L : ℕ), 3 ≤ L → ∀ (a : SpinVector 2), ‖a‖ = 1 →
    compression (2*L+1) a ((2:ℂ) • Q (2*L+1)-1) =
      scatterBlock (2*L+1) (by omega) (compressionScale L • compressionM (2*L+1) a)
admission_basis: open-problem-resolution (#11873; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Real.Sign
noncomputable section
open scoped BigOperators Matrix Kronecker InnerProductSpace Matrix.Norms.Frobenius
open Matrix Complex
namespace D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
private abbrev SpinIndex (n : ℕ) := Fin (n + 1)
private abbrev SpinVector (n : ℕ) := EuclideanSpace ℂ (SpinIndex n)
private abbrev SpinMatrix (n : ℕ) := Matrix (SpinIndex n) (SpinIndex n) ℂ
def Jplus (n : ℕ) : SpinMatrix n := fun i r =>
  let j : ℝ := (n : ℝ) / 2
  let m : ℝ := j - r.val
  if i.val + 1 = r.val then (Real.sqrt (j * (j + 1) - m * (m + 1)) : ℂ) else 0
def Jx (n : ℕ) : SpinMatrix n := (1 / 2 : ℂ) • (Jplus n + (Jplus n)ᴴ)
def Jy (n : ℕ) : SpinMatrix n := (1 / (2 * I) : ℂ) • (Jplus n - (Jplus n)ᴴ)
def Jz (n : ℕ) : SpinMatrix n := diagonal fun i => ((n : ℝ) / 2 - i.val : ℝ)
def total (K : ℕ) (A : SpinMatrix 2) (B : SpinMatrix K) : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ := A ⊗ₖ (1 : SpinMatrix K) + (1 : SpinMatrix 2) ⊗ₖ B
def theta (K : ℕ) (k : Fin K) : ℝ := 2 * Real.pi * k.val / K
def Jk (K : ℕ) (k : Fin K) : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ := (Real.cos (theta K k) : ℂ) • total K (Jx 2) (Jx K) + (Real.sin (theta K k) : ℂ) • total K (Jy 2) (Jy K)
def positiveWeight (x : ℝ) : ℝ := if 0 < x then 1 else if x = 0 then 1 / 2 else 0
def pos {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := if h : H.IsHermitian then h.cfc positiveWeight else 0
private def signOp {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := if h : H.IsHermitian then h.cfc Real.sign else 0
def Q (K : ℕ) : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ := (1 / K : ℂ) • ∑ k : Fin K, pos (Jk K k)
def productVector (K : ℕ) (a : SpinVector 2) (b : SpinVector K) : EuclideanSpace ℂ (SpinIndex 2 × SpinIndex K) := WithLp.toLp 2 fun i => a i.1 * b i.2
def scores (K : ℕ) : Set ℝ := {t | ∃ (a : SpinVector 2) (b : SpinVector K), ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ t = (star (productVector K a b).ofLp ⬝ᵥ (Q K *ᵥ (productVector K a b).ofLp)).re}
private def separableBound (K : ℕ) : ℝ := sSup (scores K)
def c (K : ℕ) : ℝ := ((2 : ℝ) ^ (K - 1))⁻¹ * (Nat.choose (K - 1) ((K - 1) / 2) : ℝ)
def claim : Prop := ∀ K : ℕ, Odd K → 7 ≤ K → IsGreatest (scores K) (1 / 2 * (1 + c K * (K - 1 : ℕ) / (K + 1 : ℕ)))
private def f (k y : ℝ) : ℝ := (1 - k * y) ^ 2 + 8 * k * y * (1 - y) + (k ^ 2 - k + 1) * (1 - y) ^ 2 / 4 - (k - 1) ^ 2
private def rotation (n : ℕ) (angle : ℝ) : SpinMatrix n := diagonal fun i => Complex.exp (-I * (angle : ℂ) * (((n : ℝ) / 2 - i.val : ℝ) : ℂ))
private def totalRotation (K : ℕ) (angle : ℝ) : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ := rotation 2 angle ⊗ₖ rotation K angle
private def totalRotationAverage (K : ℕ) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ := (1 / K : ℂ) • ∑ k : Fin K, totalRotation K (theta K k) * H * totalRotation K (-theta K k)
private def compression (K : ℕ) (a : SpinVector 2) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) : SpinMatrix K := fun i j => ∑ p : SpinIndex 2, ∑ q : SpinIndex 2, star (a p) * H (p, i) (q, j) * a q
private def middleState : SpinVector 2 := EuclideanSpace.single 1 1
open Polynomial
private def spinEigenPolynomial (u v : ℕ) : ℂ[X] := (1 - X) ^ u * (1 + X) ^ v
private def eigenCoeff (n r t : ℕ) : ℂ := (spinEigenPolynomial t (n-t)).coeff r
private def R (n : ℕ) : SpinMatrix n := fun i j => (if i.val + 1 = j.val then (j.val : ℂ) / 2 else 0) + (if j.val + 1 = i.val then ((n : ℂ) + 1 - i.val) / 2 else 0)
private def coeffMatrix (n : ℕ) : SpinMatrix n := fun r t => eigenCoeff n r.val t.val
private def spinEigenvalue (n : ℕ) (t : SpinIndex n) : ℝ := (n : ℝ) / 2 - t.val
private def spinRad (n : ℕ) (i : SpinIndex n) : ℝ := Real.sqrt (Nat.choose n i.val : ℝ)
private def spinD (n : ℕ) : SpinMatrix n := diagonal fun i => (spinRad n i : ℂ)
private def spinDinv (n : ℕ) : SpinMatrix n := diagonal fun i => (spinRad n i : ℂ)⁻¹
private def spinW (n : ℕ) : SpinMatrix n := spinDinv n * coeffMatrix n
private def binomTransform (n : ℕ) (p : ℂ[X]) : ℂ[X] := MvPolynomial.aeval ![1-X,1+X] (p.homogenize n)
private def homogeneousRotation : Fin 2 → MvPolynomial (Fin 2) ℂ := ![MvPolynomial.X 1 - MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 0]
private def levelProjector (n : ℕ) (t : ℕ) : SpinMatrix n := spinW n * diagonal (fun i => if i.val=t then 1 else 0) * (spinW n)⁻¹
private def stateY (a : SpinVector 2) : ℝ := ‖a 1‖^2
private def stateW (a : SpinVector 2) : ℂ := star (a 0) * a 1 + star (a 1) * a 2
private def stateZ (a : SpinVector 2) : ℂ := star (a 0) * a 2
private def compressionM (K : ℕ) (a : SpinVector 2) : Matrix (Fin 3) (Fin 3) ℂ := !![(1-(K:ℝ)*stateY a : ℝ), (Real.sqrt (2*K:ℝ):ℂ)*stateW a, (Real.sqrt ((K:ℝ)*(K-1:ℝ)/2):ℂ)*stateZ a; (Real.sqrt (2*K:ℝ):ℂ)*stateW a, -stateZ a, 0; (Real.sqrt ((K:ℝ)*(K-1:ℝ)/2):ℂ)*stateZ a, 0, 0]
private def entryNormSq {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖^2
private def spinV (n : ℕ) : SpinMatrix n := ((2 : ℂ)^n)⁻¹ • coeffMatrix n * spinD n
private def spinWeight (n : ℕ) (t : SpinIndex n) : ℂ := ((2 : ℂ)^n)⁻¹ * (Nat.choose n t.val : ℂ)
private def edgeTop (K : ℕ) (hK : 2 ≤ K) (r : Fin 3) : SpinIndex K := ⟨r.val, by have := r.isLt ; omega⟩
private def edgeBottom (K : ℕ) (hK : 2 ≤ K) (r : Fin 3) : SpinIndex K := ⟨K-r.val, by omega⟩
private def centralPlus (L : ℕ) : SpinIndex (2*L+1) := ⟨L, by omega⟩
private def centralMinus (L : ℕ) : SpinIndex (2*L+1) := ⟨L+1, by omega⟩
private def spinOneRad (p : SpinIndex 2) : ℝ := if p.val=1 then Real.sqrt 2 else 1
private def centralEdgeVector (L : ℕ) (epsilon : ℂ) : Fin 3 → ℂ := ![1, epsilon*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹, -(L:ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹]
private def scatterBlock (K : ℕ) (hK : 2 ≤ K) (C : Matrix (Fin 3) (Fin 3) ℂ) : SpinMatrix K := ∑ r, ∑ s, (Matrix.single (edgeTop K hK r) (edgeBottom K hK s) (C r s) + Matrix.single (edgeBottom K hK s) (edgeTop K hK r) (star (C r s)))
private def edgeVectorTop (K : ℕ) (hK : 2 ≤ K) (b : SpinVector K) : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 fun r => b (edgeTop K hK r)
private def edgeVectorBottom (K : ℕ) (hK : 2 ≤ K) (b : SpinVector K) : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 fun r => b (edgeBottom K hK r)
private def edgeMap (K : ℕ) (hK : 2 ≤ K) : Fin 3 ⊕ Fin 3 → SpinIndex K := Sum.elim (edgeTop K hK) (edgeBottom K hK)
private def compressionScale (L : ℕ) : ℂ := (-1:ℂ)^L * ((c (2*L+1)/(2*L+2):ℝ):ℂ)
private def compressionRadius (K : ℕ) : ℝ := c K*(K-1:ℕ)/(K+1:ℕ)
private def endpointState (L : ℕ) : SpinVector (2*L+1) := EuclideanSpace.single 0 (Real.sqrt 2:ℂ)⁻¹ + EuclideanSpace.single (Fin.last (2*L+1)) (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹)
private def rawCompressionC (L : ℕ) (a : SpinVector 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  let w := spinWeight (2*L+1) (centralPlus L)
  let x := (Real.sqrt (2*L+1:ℝ):ℂ)⁻¹
  let v := (L:ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹
  (-1:ℂ)^L •
  !![(c (2*L+1):ℂ)*(star (a 0)*a 0+star (a 1)*a 1+star (a 2)*a 2)-w*(star (a 0)*a 0+2*star (a 1)*a 1+star (a 2)*a 2),
      w*(Real.sqrt 2:ℂ)*x*stateW a, w*v*stateZ a;
     w*(Real.sqrt 2:ℂ)*x*stateW a, -w*x^2*stateZ a, 0;
     w*v*stateZ a, 0, 0]
set_option maxHeartbeats 2000000 in theorem result : claim := by
  have Jx_hermitian (n : ℕ) : (Jx n).IsHermitian := (by exact (isHermitian_add_transpose_self (Jplus n)).smul (by simp))
  have Jy_hermitian (n : ℕ) : (Jy n).IsHermitian := (by change ((1 / (2 * I) : ℂ) • (Jplus n - (Jplus n)ᴴ))ᴴ = _ ; rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose] ; have hc : star (1 / (2 * I) : ℂ) = -(1 / (2 * I) : ℂ) := (by simp) ; rw [hc, ← neg_sub (Jplus n) (Jplus n)ᴴ, neg_smul, smul_neg, neg_neg] ; rfl)
  have total_hermitian (K : ℕ) (A : SpinMatrix 2) (B : SpinMatrix K) (hA : A.IsHermitian) (hB : B.IsHermitian) : (total K A B).IsHermitian := (by change (A ⊗ₖ (1 : SpinMatrix K) + (1 : SpinMatrix 2) ⊗ₖ B)ᴴ = _ ; rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, hA.eq, hB.eq, conjTranspose_one, conjTranspose_one] ; rfl)
  have Jk_hermitian (K : ℕ) (k : Fin K) : (Jk K k).IsHermitian := (by exact ((total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K)).smul (by simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])).add ((total_hermitian K _ _ (Jy_hermitian 2) (Jy_hermitian K)).smul (by simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]))); clear Jy_hermitian
  have convexity_bound (k y : ℝ) (hk : 7 ≤ k) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : f k y ≤ 0 := (by have hc : 0 ≤ (5 * k ^ 2 - 33 * k + 1) / 4 := (by nlinarith [sq_nonneg (k - 7)]) ; have he : (1 - y) * f k 0 - f k y = ((5 * k ^ 2 - 33 * k + 1) / 4) * y * (1 - y) := (by unfold f ; ring) ; have h0 : f k 0 ≤ 0 := (by unfold f ; nlinarith [sq_nonneg (k - 7)]) ; have hr : 0 ≤ ((5 * k ^ 2 - 33 * k + 1) / 4) * y * (1 - y) := mul_nonneg (mul_nonneg hc hy0) (sub_nonneg.mpr hy1) ; have hl : (1 - y) * f k 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy1) h0 ; linarith)
  have cfc_eq_of_diagonalization {ι : Type} [Fintype ι] [DecidableEq ι] {A W V : Matrix ι ι ℂ} (hA : A.IsHermitian) (lam : ι → ℝ) (hAW : A * W = W * diagonal (fun j => (lam j : ℂ))) (hWV : W * V = 1) (g : ℝ → ℝ) : Matrix.IsHermitian.cfc hA g = W * diagonal (fun j => (g (lam j) : ℂ)) * V := by
    let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
    have hUU : Uᴴ * U = 1 := (by exact Unitary.coe_star_mul_self hA.eigenvectorUnitary)
    have hUU' : U * Uᴴ = 1 := (by exact Unitary.coe_mul_star_self hA.eigenvectorUnitary)
    have hs : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := (by simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, U] using hA.spectral_theorem)
    have hR : diagonal (fun i => (hA.eigenvalues i : ℂ)) * (Uᴴ * W) = (Uᴴ * W) * diagonal (fun j => (lam j : ℂ)) := (by have h := congrArg (fun M => Uᴴ * M) hAW; rw [hs] at h; simpa only [← Matrix.mul_assoc, hUU, Matrix.one_mul] using h)
    have hgR : diagonal (fun i => (g (hA.eigenvalues i) : ℂ)) * (Uᴴ * W) = (Uᴴ * W) * diagonal (fun j => (g (lam j) : ℂ)) := by
      ext i j
      have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hR
      simp only [diagonal_mul, mul_diagonal] at h ⊢
      by_cases he : hA.eigenvalues i = lam j
      · rw [he, mul_comm]
      · have he' : (hA.eigenvalues i : ℂ) - (lam j : ℂ) ≠ 0 := by
          exact sub_ne_zero.mpr (by exact_mod_cast he)
        have hz : (Uᴴ * W) i j = 0 := (mul_eq_zero.mp (by
          calc ((hA.eigenvalues i : ℂ) - (lam j : ℂ)) * (Uᴴ * W) i j = (hA.eigenvalues i : ℂ) * (Uᴴ * W) i j - (Uᴴ * W) i j * (lam j : ℂ) := by ring
            _ = 0 := sub_eq_zero.mpr h)).resolve_left he'
        rw [hz, mul_zero, zero_mul]
    have hfc : hA.cfc g = U * diagonal (fun i => (g (hA.eigenvalues i) : ℂ)) * Uᴴ := rfl
    have hgW : Matrix.IsHermitian.cfc hA g * W = W * diagonal (fun j => (g (lam j) : ℂ)) := (by rw [hfc]; rw [Matrix.mul_assoc, Matrix.mul_assoc, hgR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul])
    calc Matrix.IsHermitian.cfc hA g = (Matrix.IsHermitian.cfc hA g * W) * V := by rw [Matrix.mul_assoc, hWV, Matrix.mul_one]
      _ = W * diagonal (fun j => (g (lam j) : ℂ)) * V := by rw [hgW]
  have rotation_inverse (n : ℕ) (angle : ℝ) : rotation n angle * rotation n (-angle) = 1 := by
    rw [rotation, rotation, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, Matrix.one_apply_eq, ← Complex.exp_add]
      have hz : -I * (angle : ℂ) * (((n : ℝ) / 2 - i.val : ℝ) : ℂ) + -I * ((-angle : ℝ) : ℂ) * (((n : ℝ) / 2 - i.val : ℝ) : ℂ) = 0 := (by push_cast; ring)
      rw [hz, Complex.exp_zero]
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have cfc_conjugation {ι : Type} [Fintype ι] [DecidableEq ι] {A B R S : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hBdef : B = R * A * S) (hRS : R * S = 1) (hSR : S * R = 1) (g : ℝ → ℝ) : Matrix.IsHermitian.cfc hB g = R * Matrix.IsHermitian.cfc hA g * S := by
    let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
    have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    have hUU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have hs : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, U] using hA.spectral_theorem
    have hAU : A * U = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by calc A * U = (U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ) * U := congrArg (fun M => M * U) hs
        _ = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one]
    have hBW : B * (R * U) = (R * U) * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by rw [hBdef]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc S, hSR, Matrix.one_mul, hAU]
    have hWV : (R * U) * (Uᴴ * S) = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc U, hUU', Matrix.one_mul, hRS]
    rw [cfc_eq_of_diagonalization (ι := ι) (A := B) (W := R * U) (V := Uᴴ * S) hB hA.eigenvalues hBW hWV g]; simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose, U, Matrix.mul_assoc]
  have spectral_sign_eq_two_pos_sub_one {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : signOp H = (2 : ℂ) • pos H - 1 := by
    have hw : ∀ x : ℝ, (Real.sign x : ℂ) = 2 * (positiveWeight x : ℂ) - 1 := by
      intro x
      rcases lt_trichotomy x 0 with hn | rfl | hp
      · norm_num [Real.sign_of_neg hn, positiveWeight, hn.not_gt, ne_of_lt hn]
      · norm_num [positiveWeight]
      · norm_num [Real.sign_of_pos hp, positiveWeight, hp]
    rw [signOp, pos, dif_pos hH, dif_pos hH]; simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
    simp_rw [hw]
    rw [← diagonal_sub]
    have hd : diagonal (fun i => 2 * (positiveWeight (hH.eigenvalues i) : ℂ)) = (2 : ℂ) • diagonal (fun i => (positiveWeight (hH.eigenvalues i) : ℂ)) := by ext i j; by_cases h : i = j <;> simp [diagonal, h]
    rw [hd, diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    have hu : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    rw [hu]
  have rotation_entry (n : ℕ) (angle : ℝ) (H : SpinMatrix n) (i j : SpinIndex n) : (rotation n angle * H * rotation n (-angle)) i j = Complex.exp (I * (angle : ℂ) * ((i.val : ℂ) - (j.val : ℂ))) * H i j := (by simp only [rotation, diagonal_mul, mul_diagonal] ; rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add] ; have he : -I * (angle : ℂ) * (((n : ℝ) / 2 - i.val : ℝ) : ℂ) + -I * ((-angle : ℝ) : ℂ) * (((n : ℝ) / 2 - j.val : ℝ) : ℂ) = I * (angle : ℂ) * ((i.val : ℂ) - (j.val : ℂ)) := (by push_cast ; ring) ; rw [he, mul_comm])
  have rotation_Jplus (n : ℕ) (angle : ℝ) : rotation n angle * Jplus n * rotation n (-angle) = Complex.exp (-I * (angle : ℂ)) • Jplus n := by
    ext i j
    rw [rotation_entry]; simp only [Matrix.smul_apply, smul_eq_mul, Jplus]
    by_cases hij : i.val + 1 = j.val
    · rw [if_pos hij]
      have hdiff : (i.val : ℂ) - (j.val : ℂ) = -1 := (by exact_mod_cast (show (i.val : ℤ) - (j.val : ℤ) = -1 by omega))
      rw [hdiff, mul_neg_one]; congr 2; ring
    · simp [hij]
  clear rotation_entry
  have rotation_Jminus (n : ℕ) (angle : ℝ) : rotation n angle * (Jplus n)ᴴ * rotation n (-angle) = Complex.exp (I * (angle : ℂ)) • (Jplus n)ᴴ := by
    have rotation_conjTranspose (n : ℕ) (angle : ℝ) : (rotation n angle)ᴴ = rotation n (-angle) := by rw [rotation, rotation, diagonal_conjTranspose]; congr 1; funext i; simp only [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; congr 1; ring
    have h := congrArg Matrix.conjTranspose (rotation_Jplus n angle) ; rw [conjTranspose_mul, conjTranspose_mul, rotation_conjTranspose, rotation_conjTranspose, neg_neg, conjTranspose_smul] at h ; have he : star (Complex.exp (-I * (angle : ℂ))) = Complex.exp (I * (angle : ℂ)) := (by simp only [Complex.star_def, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]) ; simpa only [he, Matrix.mul_assoc] using h
  have rotation_Jx (n : ℕ) (angle : ℝ) : rotation n angle * Jx n * rotation n (-angle) = (Real.cos angle : ℂ) • Jx n + (Real.sin angle : ℂ) • Jy n := (by unfold Jx Jy ; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, rotation_Jplus, rotation_Jminus] ; have hp : Complex.exp (-I * (angle : ℂ)) = (Real.cos angle : ℂ) - (Real.sin angle : ℂ) * I := (by rw [show -I * (angle : ℂ) = ((-angle : ℝ) : ℂ) * I by push_cast ; ring, Complex.exp_ofReal_mul_I] ; simp [sub_eq_add_neg]) ; have hm : Complex.exp (I * (angle : ℂ)) = (Real.cos angle : ℂ) + (Real.sin angle : ℂ) * I := (by rw [mul_comm, Complex.exp_ofReal_mul_I]) ; rw [hp, hm] ; have hi : (1 / (2 * I) : ℂ) = -I / 2 := (by norm_num [div_eq_mul_inv]) ; rw [hi] ; ext i j ; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul] ; ring); clear rotation_Jminus rotation_Jplus
  have totalRotation_inverse (K : ℕ) (angle : ℝ) : totalRotation K angle * totalRotation K (-angle) = 1 := (by rw [totalRotation, totalRotation, ← mul_kronecker_mul, rotation_inverse, rotation_inverse, one_kronecker_one])
  have totalRotation_Jx (K : ℕ) (angle : ℝ) : totalRotation K angle * total K (Jx 2) (Jx K) * totalRotation K (-angle) = (Real.cos angle : ℂ) • total K (Jx 2) (Jx K) + (Real.sin angle : ℂ) • total K (Jy 2) (Jy K) := (by unfold totalRotation total ; rw [Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one, rotation_inverse, rotation_inverse, rotation_Jx, rotation_Jx] ; simp only [add_kronecker, kronecker_add, smul_kronecker, kronecker_smul, smul_add] ; abel); clear rotation_Jx rotation_inverse
  have pos_Jk_covariance (K : ℕ) (k : Fin K) : pos (Jk K k) = totalRotation K (theta K k) * pos (total K (Jx 2) (Jx K)) * totalRotation K (-theta K k) := (by have hA := total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K) ; rw [pos, dif_pos (Jk_hermitian K k), pos, dif_pos hA] ; apply cfc_conjugation hA (Jk_hermitian K k) (totalRotation_Jx K (theta K k)).symm (totalRotation_inverse K (theta K k)) ; simpa only [neg_neg] using totalRotation_inverse K (-theta K k)); clear Jk_hermitian
  have Q_rotation_average (K : ℕ) : Q K = totalRotationAverage K (pos (total K (Jx 2) (Jx K))) := (by unfold Q totalRotationAverage ; simp_rw [pos_Jk_covariance]); clear pos_Jk_covariance
  have root_average (K : ℕ) (hK : K ≠ 0) (d : ℤ) : (1 / K : ℂ) * ∑ k : Fin K, Complex.exp (I * (theta K k : ℂ) * (d : ℂ)) = if (K : ℤ) ∣ d then 1 else 0 := by
    let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I / K)
    have hζ : IsPrimitiveRoot ζ K := Complex.isPrimitiveRoot_exp K hK
    have hp : ∀ k : Fin K, Complex.exp (I * (theta K k : ℂ) * (d : ℂ)) = (ζ ^ d) ^ k.val := (by intro k; rw [← Complex.exp_int_mul, ← Complex.exp_nat_mul]; congr 1; unfold theta; push_cast; ring)
    simp_rw [hp]
    by_cases hd : (K : ℤ) ∣ d
    · rw [if_pos hd, hζ.zpow_eq_one_iff_dvd d |>.mpr hd]
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, one_div]
      exact inv_mul_cancel₀ (by exact_mod_cast hK)
    · rw [if_neg hd]
      have hz : ζ ^ d ≠ 1 := fun h => hd ((hζ.zpow_eq_one_iff_dvd d).mp h)
      have hpow : (ζ ^ d) ^ K = 1 := (by rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm d, _root_.zpow_mul, hζ.zpow_eq_one, _root_.one_zpow])
      have hs : ∑ k : Fin K, (ζ ^ d) ^ k.val = 0 := by
        rw [Finset.sum_fin_eq_sum_range]
        have he := geom_sum_mul (ζ ^ d) K
        rw [hpow, sub_self] at he
        calc (∑ i ∈ Finset.range K, if h : i < K then (ζ ^ d) ^ (⟨i, h⟩ : Fin K).val else 0) = ∑ i ∈ Finset.range K, (ζ ^ d) ^ i := by
                apply Finset.sum_congr rfl; intro i hi; simp [Finset.mem_range.mp hi]
             _ = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hz)
      rw [hs, mul_zero]
  have totalRotation_entry (K : ℕ) (angle : ℝ) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) (p q : SpinIndex 2) (i j : SpinIndex K) : (totalRotation K angle * H * totalRotation K (-angle)) (p,i) (q,j) = Complex.exp (I * (angle : ℂ) * ((p.val : ℂ) + (i.val : ℂ) - (q.val : ℂ) - (j.val : ℂ))) * H (p,i) (q,j) := (by simp only [totalRotation, rotation, diagonal_kronecker_diagonal, diagonal_mul, mul_diagonal] ; have hc : ∀ a b c d h : ℂ, (a * b) * h * (c * d) = (a * b * c * d) * h := (by intros ; ring) ; rw [hc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add] ; congr 2 ; push_cast ; ring)
  have totalRotationAverage_selection (K : ℕ) (hK : K ≠ 0) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) (p q : SpinIndex 2) (i j : SpinIndex K) : totalRotationAverage K H (p,i) (q,j) = if (K : ℤ) ∣ ((p.val : ℤ) + i.val - q.val - j.val) then H (p,i) (q,j) else 0 := (by simp only [totalRotationAverage, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, totalRotation_entry] ; have hd : (p.val : ℂ) + (i.val : ℂ) - (q.val : ℂ) - (j.val : ℂ) = (((p.val : ℤ) + i.val - q.val - j.val : ℤ) : ℂ) := (by push_cast ; rfl) ; simp_rw [hd] ; rw [← Finset.sum_mul, ← mul_assoc, root_average K hK] ; split_ifs <;> simp); clear root_average
  have spinEigenPolynomial_differential (u v : ℕ) : (1 - X ^ 2) * (spinEigenPolynomial u v).derivative + C ((u : ℂ) + (v : ℂ)) * X * spinEigenPolynomial u v = C ((v : ℂ) - (u : ℂ)) * spinEigenPolynomial u v := by
    cases u with
    | zero =>
      cases v with
      | zero => simp [spinEigenPolynomial]
      | succ v =>
        simp only [spinEigenPolynomial, pow_zero, one_mul, derivative_pow_succ,
           derivative_one, derivative_X, zero_add, mul_one,
          Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, sub_zero, map_add, map_one]
        simp only [pow_succ]; ring
    | succ u =>
      cases v with
      | zero =>
        simp only [spinEigenPolynomial, pow_zero, mul_one, derivative_pow_succ,
          derivative_sub, derivative_one, derivative_X, zero_sub, mul_neg, mul_one,
          Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero, zero_sub, map_add, map_one, map_neg]
        simp only [pow_succ]; ring
      | succ v =>
        simp only [spinEigenPolynomial, derivative_mul, derivative_pow_succ,
            derivative_one, derivative_X, zero_sub,
          zero_add, mul_one, mul_neg, Nat.cast_add, Nat.cast_one, map_add, map_sub, map_one]
        simp only [pow_succ]; ring
  have spinEigenPolynomial_const (u v : ℕ) : (spinEigenPolynomial u v).coeff 0 = 1 := (by simp [spinEigenPolynomial, coeff_zero_eq_eval_zero])
  have spinEigenPolynomial_row_zero (u v : ℕ) : (spinEigenPolynomial u v).coeff 1 = ((v : ℂ) - (u : ℂ)) := (by have h := congrArg (fun p : ℂ[X] => p.coeff 0) (spinEigenPolynomial_differential u v) ; simpa [sub_mul, coeff_derivative, spinEigenPolynomial_const, coeff_X_pow_mul'] using h)
  have spinEigenPolynomial_row_succ (u v r : ℕ) : (r + 2 : ℕ) * (spinEigenPolynomial u v).coeff (r + 2) + ((u : ℂ) + (v : ℂ) - r) * (spinEigenPolynomial u v).coeff r = ((v : ℂ) - (u : ℂ)) * (spinEigenPolynomial u v).coeff (r + 1) := by
    have h := congrArg (fun p : ℂ[X] => p.coeff (r + 1)) (spinEigenPolynomial_differential u v)
    simp only [sub_mul, one_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_derivative, mul_assoc, coeff_X_mul] at h
    have hs : (X ^ 2 * (spinEigenPolynomial u v).derivative).coeff (r + 1) = (r : ℂ) * (spinEigenPolynomial u v).coeff r := by
      cases r with
      | zero => simp [coeff_X_pow_mul']
      | succ r => rw [show r + 1 + 1 = r + 2 by omega, coeff_X_pow_mul, coeff_derivative]; push_cast; ring
    rw [hs] at h; push_cast at h ⊢
    linear_combination h
  clear spinEigenPolynomial_differential
  have spinEigenPolynomial_degree (u v : ℕ) : (spinEigenPolynomial u v).natDegree ≤ u + v := by
    apply (Polynomial.natDegree_mul_le).trans; apply add_le_add
    · calc ((1-X : ℂ[X]) ^ u).natDegree ≤ u * (1-X : ℂ[X]).natDegree := natDegree_pow_le
           _ ≤ u * 1 := Nat.mul_le_mul_left u (by compute_degree)
           _ = u := Nat.mul_one u
    · calc ((1+X : ℂ[X]) ^ v).natDegree ≤ v * (1+X : ℂ[X]).natDegree := natDegree_pow_le
           _ ≤ v * 1 := Nat.mul_le_mul_left v (by compute_degree)
           _ = v := Nat.mul_one v
  have sum_upper_coeff (n : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ n) (i : SpinIndex n) : (∑ j : SpinIndex n, if i.val + 1 = j.val then (j.val : ℂ) * p.coeff j.val else 0) = (i.val + 1 : ℂ) * p.coeff (i.val + 1) := by
    by_cases h : i.val + 1 < n + 1
    · let j : SpinIndex n := ⟨i.val+1,h⟩
      rw [Finset.sum_eq_single j]
      · simp [j]
      · intro k hk hkj
        have hk' : i.val+1 ≠ k.val := (by intro he; apply hkj; apply Fin.ext; exact he.symm)
        simp [hk']
      · simp
    · have hz : p.coeff (i.val+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, mul_zero]; apply Finset.sum_eq_zero; intro j hj
      have h' : i.val+1 ≠ j.val := by have := j.isLt ; omega
      simp [h']
  have sum_lower_coeff (n : ℕ) (p : ℂ[X]) (i : SpinIndex n) : (∑ j : SpinIndex n, if j.val + 1 = i.val then ((n : ℂ) + 1 - i.val) * p.coeff j.val else 0) = if i.val = 0 then 0 else ((n : ℂ) + 1 - i.val) * p.coeff (i.val - 1) := by
    by_cases hi : i.val = 0
    · rw [if_pos hi]
      apply Finset.sum_eq_zero; intro j hj
      have h' : ¬j.val+1 = i.val := by omega
      simp [h']
    · rw [if_neg hi]
      let j : SpinIndex n := ⟨i.val-1, by have := i.isLt ; omega⟩
      rw [Finset.sum_eq_single j]
      · simp [j, show i.val-1+1=i.val by omega]
      · intro k hk hkj
        have hk' : k.val+1 ≠ i.val := (by intro he; apply hkj; apply Fin.ext; simp only [j]; omega)
        simp [hk']
      · simp
  have R_coeffMatrix_eigen (n : ℕ) : R n * coeffMatrix n = coeffMatrix n * diagonal (fun t => (spinEigenvalue n t : ℂ)) := by
    ext i t
    rw [Matrix.mul_apply, Matrix.mul_diagonal]; simp only [R, coeffMatrix, eigenCoeff, add_mul, Finset.sum_add_distrib]
    have ht : t.val ≤ n := by have := t.isLt ; omega
    have hp : (spinEigenPolynomial t.val (n-t.val)).natDegree ≤ n := by
      convert spinEigenPolynomial_degree t.val (n-t.val) using 1
      omega
    have hu : (∑ j : SpinIndex n, (if i.val+1=j.val then (j.val : ℂ)/2 else 0) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val) = ((i.val+1 : ℂ) * (spinEigenPolynomial t.val (n-t.val)).coeff (i.val+1))/2 := (by have he : ∀ j : SpinIndex n, (if i.val+1=j.val then (j.val : ℂ)/2 else 0) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val = (if i.val+1=j.val then (j.val : ℂ) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val else 0)/2 := (by intro j; split_ifs <;> simp [div_mul_eq_mul_div]); simp_rw [he]; rw [← Finset.sum_div, sum_upper_coeff n _ hp])
    have hl : (∑ j : SpinIndex n, (if j.val+1=i.val then ((n : ℂ)+1-i.val)/2 else 0) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val) = (if i.val=0 then 0 else ((n : ℂ)+1-i.val) * (spinEigenPolynomial t.val (n-t.val)).coeff (i.val-1))/2 := (by have he : ∀ j : SpinIndex n, (if j.val+1=i.val then ((n : ℂ)+1-i.val)/2 else 0) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val = (if j.val+1=i.val then ((n : ℂ)+1-i.val) * (spinEigenPolynomial t.val (n-t.val)).coeff j.val else 0)/2 := (by intro j; split_ifs <;> simp [div_mul_eq_mul_div]); simp_rw [he]; rw [← Finset.sum_div, sum_lower_coeff])
    rw [hu, hl]
    have hn : ((n-t.val : ℕ) : ℂ) = (n : ℂ) - t.val := Nat.cast_sub ht
    by_cases hi : i.val = 0
    · rw [if_pos hi, hi, spinEigenPolynomial_row_zero, spinEigenPolynomial_const]
      unfold spinEigenvalue; push_cast; rw [hn]; ring
    · obtain ⟨r, hr⟩ : ∃ r, i.val=r+1 := ⟨i.val-1, by omega⟩
      rw [if_neg hi, hr]
      have h := spinEigenPolynomial_row_succ t.val (n-t.val) r
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at *; unfold spinEigenvalue; push_cast; rw [hn] at h; simp only [show r+1+1=r+2 by omega]
      linear_combination h / 2
  clear sum_lower_coeff sum_upper_coeff
  have spinRad_pos (n : ℕ) (i : SpinIndex n) : 0 < spinRad n i := (by apply Real.sqrt_pos.mpr ; exact_mod_cast Nat.choose_pos (show i.val ≤ n by have := i.isLt ; omega))
  have spinD_inverse (n : ℕ) : spinDinv n * spinD n = 1 := by
    rw [spinDinv, spinD, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [diagonal_apply_eq, Matrix.one_apply_eq]; apply inv_mul_cancel₀
      exact_mod_cast (spinRad_pos n i).ne'
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have spinD_inverse' (n : ℕ) : spinD n * spinDinv n = 1 := (by have h := spinD_inverse n ; rw [spinDinv, spinD, diagonal_mul_diagonal] at h ; rw [spinD, spinDinv, diagonal_mul_diagonal] ; simpa only [mul_comm] using h)
  have Jx_scaled (n : ℕ) : Jx n = spinDinv n * R n * spinD n := by
    have raising_factorization (r : ℕ) :
        (n : ℝ) / 2 * ((n : ℝ) / 2 + 1) -
          ((n : ℝ) / 2 - r) * ((n : ℝ) / 2 - r + 1) =
            (r : ℝ) * ((n : ℝ) + 1 - r) := by ring
    have sqrt_scale (x a b r : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hr : 0 ≤ r) (h : x * a = r ^ 2 * b) : (1 / 2 : ℂ) * (Real.sqrt x : ℂ) = (Real.sqrt a : ℂ)⁻¹ * ((r : ℂ) / 2) * (Real.sqrt b : ℂ) := by
      have hprod : Real.sqrt x * Real.sqrt a = r * Real.sqrt b := by rw [← Real.sqrt_mul hx, h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
      have ha' : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
      have haC : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast ha'
      have hprodC : (Real.sqrt x : ℂ) * (Real.sqrt a : ℂ) = (r : ℂ) * (Real.sqrt b : ℂ) := by exact_mod_cast hprod
      apply mul_right_cancel₀ haC
      calc (1 / 2 : ℂ) * (Real.sqrt x : ℂ) * (Real.sqrt a : ℂ) = (1 / 2 : ℂ) * ((r : ℂ) * (Real.sqrt b : ℂ)) := by rw [mul_assoc, hprodC]
        _ = ((Real.sqrt a : ℂ)⁻¹ * ((r : ℂ) / 2) * (Real.sqrt b : ℂ)) * (Real.sqrt a : ℂ) := by field_simp
    ext i j
    have hi : i.val ≤ n := by have := i.isLt ; omega
    have hj : j.val ≤ n := by have := j.isLt ; omega
    simp only [Jx, Jplus, raising_factorization, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      conjTranspose_apply, apply_ite, Complex.star_def, Complex.conj_ofReal, map_zero,
      spinDinv, spinD, diagonal_mul, mul_diagonal, R, spinRad]
    by_cases hup : i.val+1=j.val
    · have hdn : ¬j.val+1=i.val := by omega
      simp only [if_pos hup, if_neg hdn, add_zero]
      have hx : 0 ≤ (j.val : ℝ) * ((n : ℝ)+1-j.val) := (by apply mul_nonneg (by positivity); exact sub_nonneg.mpr (by exact_mod_cast (show j.val ≤ n+1 by omega)))
      have ha : 0 < (Nat.choose n i.val : ℝ) := by exact_mod_cast Nat.choose_pos hi
      have he : (j.val : ℝ) * ((n : ℝ)+1-j.val) * (Nat.choose n i.val : ℝ) = (j.val : ℝ)^2 * (Nat.choose n j.val : ℝ) := by
        have hb := congrArg (fun q : ℕ => (q : ℝ)) (Nat.choose_succ_right_eq n i.val)
        simp only [Nat.cast_mul, Nat.cast_sub hi, hup] at hb
        have hv : (j.val : ℝ) = (i.val : ℝ)+1 := by exact_mod_cast hup.symm
        rw [hv] at hb ⊢
        linear_combination - ((i.val : ℝ)+1) * hb
      have hs := sqrt_scale (j.val * ((n : ℝ)+1-j.val)) (Nat.choose n i.val)
        (Nat.choose n j.val) j.val hx ha (by positivity) he
      simpa only [Complex.ofReal_natCast] using hs
    · by_cases hdn : j.val+1=i.val
      · simp only [if_neg hup, if_pos hdn, zero_add]
        have hr : 0 ≤ (n : ℝ)+1-i.val := (by exact sub_nonneg.mpr (by exact_mod_cast (show i.val ≤ n+1 by omega)))
        have hx : 0 ≤ (i.val : ℝ) * ((n : ℝ)+1-i.val) := mul_nonneg (by positivity) hr
        have ha : 0 < (Nat.choose n i.val : ℝ) := by exact_mod_cast Nat.choose_pos hi
        have he : (i.val : ℝ) * ((n : ℝ)+1-i.val) * (Nat.choose n i.val : ℝ) = ((n : ℝ)+1-i.val)^2 * (Nat.choose n j.val : ℝ) := by
          have hb := congrArg (fun q : ℕ => (q : ℝ)) (Nat.choose_succ_right_eq n j.val)
          simp only [Nat.cast_mul, Nat.cast_sub hj, hdn] at hb
          have hv : (i.val : ℝ) = (j.val : ℝ)+1 := by exact_mod_cast hdn.symm
          rw [hv] at hb ⊢
          linear_combination ((n : ℝ)-j.val) * hb
        have hs := sqrt_scale (i.val * ((n : ℝ)+1-i.val)) (Nat.choose n i.val)
          (Nat.choose n j.val) ((n : ℝ)+1-i.val) hx ha hr he
        simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
          Complex.ofReal_natCast] using hs
      · simp [hup, hdn]
  have spinW_eigen (n : ℕ) : Jx n * spinW n = spinW n * diagonal (fun t => (spinEigenvalue n t : ℂ)) := by
    rw [Jx_scaled, spinW]
    calc (spinDinv n * R n * spinD n) * (spinDinv n * coeffMatrix n) = spinDinv n * (R n * coeffMatrix n) := by
            simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (spinD n), spinD_inverse', Matrix.one_mul]
         _ = (spinDinv n * coeffMatrix n) * diagonal (fun t => (spinEigenvalue n t : ℂ)) := by
           rw [R_coeffMatrix_eigen, ← Matrix.mul_assoc]
  clear Jx_scaled spinD_inverse' R_coeffMatrix_eigen
  have spinW_col_zero (n : ℕ) (t : SpinIndex n) : spinW n 0 t = 1 := (by simp [spinW, spinDinv, Matrix.diagonal_mul, coeffMatrix, eigenCoeff, spinEigenPolynomial_const, spinRad])
  have spinW_isUnit (n : ℕ) : IsUnit (spinW n) := by
    have spinEigenvalue_injective (n : ℕ) : Function.Injective (spinEigenvalue n) := by intro t s h ; apply Fin.ext ; have hcast : (t.val : ℝ) = s.val := (by unfold spinEigenvalue at h ; linarith) ; exact_mod_cast hcast
    apply Matrix.linearIndependent_cols_iff_isUnit.mp; apply Module.End.eigenvectors_linearIndependent' (Jx n).mulVecLin
      (fun t => (spinEigenvalue n t : ℂ))
    · intro i j hij
      apply spinEigenvalue_injective n; exact Complex.ofReal_injective hij
    · intro t
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        ext i
        have h := congrArg (fun M : SpinMatrix n => M i t) (spinW_eigen n)
        simp only [Matrix.mul_diagonal] at h
        simpa [Matrix.mulVecLin_apply, Matrix.col, Matrix.transpose_apply,
          Matrix.mul_diagonal, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
      · intro hz
        have h := congrArg (fun v : SpinIndex n → ℂ => v 0) hz
        change spinW n 0 t = 0 at h; rw [spinW_col_zero] at h; exact one_ne_zero h
  have spinW_inverse (n : ℕ) : spinW n * (spinW n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (spinW_isUnit n))
  have spin_spectral_formula (n : ℕ) (g : ℝ → ℝ) : Matrix.IsHermitian.cfc (Jx_hermitian n) g = spinW n * diagonal (fun t => (g (spinEigenvalue n t) : ℂ)) * (spinW n)⁻¹ := cfc_eq_of_diagonalization (Jx_hermitian n) (spinEigenvalue n)
      (spinW_eigen n) (spinW_inverse n) g
  have homogeneousRotation_homogeneous (i : Fin 2) : (homogeneousRotation i).IsHomogeneous 1 := by
    fin_cases i
    · exact (MvPolynomial.isHomogeneous_X _ 1).sub (MvPolynomial.isHomogeneous_X _ 0)
    · exact (MvPolynomial.isHomogeneous_X _ 1).add (MvPolynomial.isHomogeneous_X _ 0)
  have binomTransform_homogenize (n : ℕ) (p : ℂ[X]) : (binomTransform n p).homogenize n = MvPolynomial.aeval homogeneousRotation (p.homogenize n) := by
    apply homogenize_eq_of_isHomogeneous
    · simpa only [one_mul] using (isHomogeneous_homogenize p).aeval
        homogeneousRotation homogeneousRotation_homogeneous
    · unfold binomTransform
      rw [MvPolynomial.comp_aeval_apply]; congr 2
      funext i
      fin_cases i <;> simp [homogeneousRotation]
  clear homogeneousRotation_homogeneous
  have homogenize_scaled_eval (n : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ n) (a : ℂ) : MvPolynomial.aeval ![C a * X,C a] (p.homogenize n) = C (a^n) * p := by
    apply Polynomial.induction_with_natDegree_le
      (fun p => MvPolynomial.aeval ![C a * X,C a] (p.homogenize n) = C (a^n) * p) (N:=n)
    · simp
    · intro k c hc hk
      rw [homogenize_C_mul, homogenize_X_pow hk]
      simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      have he : (C a * X)^k * (C a)^(n-k) = C (a^n) * X^k := by
        rw [mul_pow]
        calc C a ^ k * X ^ k * C a ^ (n-k) = (C a ^ k * C a ^ (n-k)) * X ^ k := by ring
             _ = C (a^n) * X^k := by rw [← pow_add, Nat.add_sub_of_le hk, ← C_pow]
      rw [he, Polynomial.algebraMap_eq]; simp only [C_pow]; ring
    · intro p q hpq hq ihp ihq
      simp [ihp, ihq, mul_add]
    · exact hp
  have binomTransform_involution (n : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ n) : binomTransform n (binomTransform n p) = C ((2 : ℂ)^n) * p := by
    change MvPolynomial.aeval ![1-X,1+X] ((binomTransform n p).homogenize n) = _; rw [binomTransform_homogenize, MvPolynomial.comp_aeval_apply]
    have hg : (fun i : Fin 2 => (MvPolynomial.aeval (![1-X,1+X] : Fin 2 → ℂ[X])) (homogeneousRotation i)) = (![C (2 : ℂ) * X, C (2 : ℂ)] : Fin 2 → ℂ[X]) := (by funext i; fin_cases i <;> simp [homogeneousRotation, Polynomial.C_ofNat] <;> ring)
    rw [hg, homogenize_scaled_eval n p hp]
  clear homogenize_scaled_eval binomTransform_homogenize
  have binomTransform_as_sum (n : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ n) : binomTransform n p = ∑ t : SpinIndex n, C (p.coeff t.val) * spinEigenPolynomial t.val (n-t.val) := by
    have hs : p = ∑ t : SpinIndex n, C (p.coeff t.val) * X^t.val := by
      rw [Finset.sum_fin_eq_sum_range]
      calc p = ∑ t ∈ Finset.range (n+1), C (p.coeff t) * X^t := p.as_sum_range_C_mul_X_pow' (by omega)
           _ = ∑ t ∈ Finset.range (n+1),
                if h : t<n+1 then C (p.coeff (⟨t,h⟩ : SpinIndex n).val) * X^(⟨t,h⟩ : SpinIndex n).val else 0 := by
                    apply Finset.sum_congr rfl; intro t ht; simp [Finset.mem_range.mp ht]
    calc binomTransform n p = binomTransform n (∑ t : SpinIndex n, C (p.coeff t.val) * X^t.val) := congrArg (binomTransform n) hs
         _ = ∑ t : SpinIndex n, C (p.coeff t.val) * spinEigenPolynomial t.val (n-t.val) := by
            unfold binomTransform; rw [homogenize_finsetSum, map_sum]; apply Finset.sum_congr rfl; intro t ht; rw [homogenize_C_mul, homogenize_X_pow (show t.val ≤ n by have := t.isLt ; omega)]; simp [spinEigenPolynomial]
  have coeffMatrix_square (n : ℕ) : coeffMatrix n * coeffMatrix n = (2 : ℂ)^n • (1 : SpinMatrix n) := by
    ext i j
    have hj : j.val ≤ n := by have := j.isLt ; omega
    have hp : (X^j.val : ℂ[X]).natDegree ≤ n := (by simpa only [natDegree_X_pow] using hj)
    have hX : binomTransform n (X^j.val : ℂ[X]) = spinEigenPolynomial j.val (n-j.val) := (by simp [binomTransform, homogenize_X_pow hj, spinEigenPolynomial])
    have h := congrArg (fun p : ℂ[X] => p.coeff i.val) (binomTransform_involution n (X^j.val) hp)
    rw [hX, binomTransform_as_sum n _ (by
      convert spinEigenPolynomial_degree j.val (n-j.val) using 1
      omega)] at h
    simp only [ coeff_C_mul, coeff_X_pow] at h
    simpa [Matrix.mul_apply, coeffMatrix, eigenCoeff, finsetSum_coeff, coeff_C_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, coeff_X_pow, eq_comm, mul_comm, Fin.ext_iff] using h.symm
  clear binomTransform_as_sum binomTransform_involution spinEigenPolynomial_degree
  have total_diagonal (K : ℕ) (a : SpinIndex 2 → ℂ) (b : SpinIndex K → ℂ) : total K (diagonal a) (diagonal b) = diagonal (fun i => a i.1 + b i.2) := (by unfold total ; rw [← Matrix.diagonal_one, ← Matrix.diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal, ← diagonal_add] ; simp only [one_mul, mul_one])
  have total_spinW_eigen (K : ℕ) : total K (Jx 2) (Jx K) * (spinW 2 ⊗ₖ spinW K) = (spinW 2 ⊗ₖ spinW K) * diagonal (fun t => ((spinEigenvalue 2 t.1 + spinEigenvalue K t.2 : ℝ) : ℂ)) := (by have hdiag : diagonal (fun t => ((spinEigenvalue 2 t.1 + spinEigenvalue K t.2 : ℝ) : ℂ)) = total K (diagonal fun t => (spinEigenvalue 2 t : ℂ)) (diagonal fun t => (spinEigenvalue K t : ℂ)) := (by rw [total_diagonal] ; push_cast ; rfl) ; rw [hdiag, total, total, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, spinW_eigen, spinW_eigen]); clear total_diagonal
  have total_spinW_inverse (K : ℕ) : (spinW 2 ⊗ₖ spinW K) * ((spinW 2)⁻¹ ⊗ₖ (spinW K)⁻¹) = 1 := (by rw [← mul_kronecker_mul, spinW_inverse, spinW_inverse, one_kronecker_one])
  have total_spin_spectral_formula (K : ℕ) (g : ℝ → ℝ) : Matrix.IsHermitian.cfc (total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K)) g = (spinW 2 ⊗ₖ spinW K) * diagonal (fun t => (g (spinEigenvalue 2 t.1 + spinEigenvalue K t.2) : ℂ)) * ((spinW 2)⁻¹ ⊗ₖ (spinW K)⁻¹) := (by exact cfc_eq_of_diagonalization _ _ (total_spinW_eigen K) (total_spinW_inverse K) g); clear total_spinW_inverse total_spinW_eigen
  have sign_halfInteger_levels (L : ℕ) (p : SpinIndex 2) (t : SpinIndex (2*L+1)) : Real.sign (spinEigenvalue 2 p + spinEigenvalue (2*L+1) t) = Real.sign (spinEigenvalue (2*L+1) t) + 2 * (if p.val=0 then 1 else 0) * (if t.val=L+1 then 1 else 0) - 2 * (if p.val=2 then 1 else 0) * (if t.val=L then 1 else 0) := by
    have scalar_sign_decomposition (x : ℝ) (m : ℤ) (hx : x = -1 ∨ x = 0 ∨ x = 1) : Real.sign (x + (m : ℝ) + 1 / 2) = Real.sign ((m : ℝ) + 1 / 2) + 2 * (if x = 1 then 1 else 0) * (if m = -1 then 1 else 0) - 2 * (if x = -1 then 1 else 0) * (if m = 0 then 1 else 0) := by
      have hm : m ≤ -2 ∨ m = -1 ∨ m = 0 ∨ 1 ≤ m := by omega
      rcases hx with rfl | rfl | rfl <;> rcases hm with hm | hm | hm | hm
      all_goals try { subst m; norm_num [Real.sign] }
      all_goals have hm0 : m ≠ 0 := by omega
      all_goals have hm1 : m ≠ -1 := by omega
      all_goals first
        | have hr : (m : ℝ) ≤ -2 := by exact_mod_cast hm
          simp only [Real.sign_of_neg (show -1 + (m : ℝ) + 1/2 < 0 by linarith),
            Real.sign_of_neg (show 0 + (m : ℝ) + 1/2 < 0 by linarith),
            Real.sign_of_neg (show 1 + (m : ℝ) + 1/2 < 0 by linarith),
            Real.sign_of_neg (show (m : ℝ) + 1/2 < 0 by linarith)]
          norm_num [hm0, hm1]
        | have hr : (1 : ℝ) ≤ m := by exact_mod_cast hm
          simp only [Real.sign_of_pos (show 0 < -1 + (m : ℝ) + 1/2 by linarith),
            Real.sign_of_pos (show 0 < 0 + (m : ℝ) + 1/2 by linarith),
            Real.sign_of_pos (show 0 < 1 + (m : ℝ) + 1/2 by linarith),
            Real.sign_of_pos (show 0 < (m : ℝ) + 1/2 by linarith)]
          norm_num [hm0, hm1]
    have hlam : spinEigenvalue (2*L+1) t = ((L : ℤ)-t.val : ℤ) + (1/2 : ℝ) := (by unfold spinEigenvalue ; push_cast ; ring) ; have hx : spinEigenvalue 2 p = -1 ∨ spinEigenvalue 2 p = 0 ∨ spinEigenvalue 2 p = 1 := (by fin_cases p <;> norm_num [spinEigenvalue]) ; have h := scalar_sign_decomposition (spinEigenvalue 2 p) ((L : ℤ)-t.val) hx ; have h0 : ((L : ℤ)-t.val) = -1 ↔ t.val=L+1 := (by omega) ; have h1 : ((L : ℤ)-t.val) = 0 ↔ t.val=L := (by omega) ; rw [hlam] ; have hlam2 : ∀ x : ℝ, x + (((L : ℤ)-t.val : ℤ) : ℝ) + 1/2 = x + ((((L : ℤ)-t.val : ℤ) : ℝ)+1/2) := (by intro x ; ring) ; rw [hlam2] at h ; simp only [h0, h1] at h ; fin_cases p <;> norm_num [spinEigenvalue] at h ⊢ <;> exact h
  have tensor_sign_decomposition (L : ℕ) : signOp (total (2*L+1) (Jx 2) (Jx (2*L+1))) = (1 : SpinMatrix 2) ⊗ₖ signOp (Jx (2*L+1)) + (2 : ℂ) • (levelProjector 2 0 ⊗ₖ levelProjector (2*L+1) (L+1)) - (2 : ℂ) • (levelProjector 2 2 ⊗ₖ levelProjector (2*L+1) L) := by
    have hA := total_hermitian (2*L+1) _ _ (Jx_hermitian 2) (Jx_hermitian (2*L+1))
    rw [signOp, dif_pos hA, total_spin_spectral_formula]; rw [signOp, dif_pos (Jx_hermitian (2*L+1)), spin_spectral_formula]
    have hW2 : (1 : SpinMatrix 2) = spinW 2 * (1 : SpinMatrix 2) * (spinW 2)⁻¹ := (by rw [Matrix.mul_one, spinW_inverse])
    rw [hW2]; unfold levelProjector
    rw [mul_kronecker_mul, mul_kronecker_mul, mul_kronecker_mul,
      mul_kronecker_mul, mul_kronecker_mul, mul_kronecker_mul]
    have hd : diagonal (fun t : SpinIndex 2 × SpinIndex (2*L+1) =>
        (Real.sign (spinEigenvalue 2 t.1 + spinEigenvalue (2*L+1) t.2) : ℂ)) = (1 : SpinMatrix 2) ⊗ₖ diagonal (fun t => (Real.sign (spinEigenvalue (2*L+1) t) : ℂ)) + (2 : ℂ) • (diagonal (fun i : SpinIndex 2 => if i.val=0 then (1 : ℂ) else 0) ⊗ₖ
          diagonal (fun i : SpinIndex (2*L+1) => if i.val=L+1 then (1 : ℂ) else 0)) - (2 : ℂ) • (diagonal (fun i : SpinIndex 2 => if i.val=2 then (1 : ℂ) else 0) ⊗ₖ
          diagonal (fun i : SpinIndex (2*L+1) => if i.val=L then (1 : ℂ) else 0)) := by
      rw [← Matrix.diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_kronecker_diagonal]
      ext i j
      by_cases hij : i=j
      · subst j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          diagonal_apply_eq, one_mul]
        have hc := congrArg (fun x : ℝ => (x : ℂ)) (sign_halfInteger_levels L i.1 i.2)
        split_ifs at hc ⊢ <;> norm_num at hc ⊢ <;>
          simpa [mul_assoc] using hc
      · simp [ hij]
    rw [hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  clear sign_halfInteger_levels total_spin_spectral_formula spin_spectral_formula spinW_inverse
  have spinOne_unit_norm_sq (a : SpinVector 2) (ha : ‖a‖=1) : ‖a 0‖^2 + ‖a 1‖^2 + ‖a 2‖^2 = 1 := (by have h := EuclideanSpace.norm_sq_eq a ; rw [ha] at h ; simpa [Fin.sum_univ_succ, add_assoc] using h.symm)
  have stateZ_bound (a : SpinVector 2) (ha : ‖a‖=1) : ‖stateZ a‖^2 ≤ (1-stateY a)^2 / 4 := (by have h := spinOne_unit_norm_sq a ha ; simp only [stateZ, norm_mul, norm_star, mul_pow, stateY] ; nlinarith [sq_nonneg (‖a 0‖^2 - ‖a 2‖^2)])
  have stateW_bound (a : SpinVector 2) (ha : ‖a‖=1) : ‖stateW a‖^2 ≤ 2 * stateY a * (1-stateY a) := by
    have h := spinOne_unit_norm_sq a ha
    have hnorm : ‖stateW a‖ ≤ (‖a 0‖+‖a 2‖)*‖a 1‖ := by
      calc ‖stateW a‖ ≤ ‖star (a 0)*a 1‖ + ‖star (a 1)*a 2‖ := norm_add_le _ _
           _ = (‖a 0‖+‖a 2‖)*‖a 1‖ := by simp only [norm_mul, norm_star] ; ring
    have hs : ‖stateW a‖^2 ≤ ((‖a 0‖+‖a 2‖)*‖a 1‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hd : 0 ≤ (‖a 0‖-‖a 2‖)^2 * ‖a 1‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    unfold stateY; nlinarith [hs,hd]
  have compressionM_normSq (K : ℕ) (hK : 1 ≤ K) (a : SpinVector 2) : entryNormSq (compressionM K a) = (1-(K:ℝ)*stateY a)^2 + 4*K*‖stateW a‖^2 + ((K:ℝ)^2-K+1)*‖stateZ a‖^2 := (by have hkr : (1:ℝ) ≤ K := (by exact_mod_cast hK) ; have h1 : 0 ≤ (2*K:ℝ) := (by positivity) ; have h2 : 0 ≤ (K:ℝ)*(K-1:ℝ)/2 := (by positivity) ; unfold entryNormSq compressionM ; simp only [Fin.sum_univ_succ, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, norm_mul, norm_neg, norm_zero, zero_pow (by decide : 2 ≠ 0), norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, Fin.sum_univ_zero, add_zero] ; ring)
  have compressionM_normSq_bound (K : ℕ) (hK : 7 ≤ K) (a : SpinVector 2) (ha : ‖a‖=1) : entryNormSq (compressionM K a) ≤ (K-1:ℝ)^2 := by
    have stateY_bounds (a : SpinVector 2) (ha : ‖a‖=1) : 0 ≤ stateY a ∧ stateY a ≤ 1 := by
      have h := spinOne_unit_norm_sq a ha
      unfold stateY
      constructor
      · positivity
      · nlinarith [sq_nonneg ‖a 0‖, sq_nonneg ‖a 2‖]
    have hkr : (7:ℝ) ≤ K := (by exact_mod_cast hK) ; have hy := stateY_bounds a ha ; have hw := stateW_bound a ha ; have hz := stateZ_bound a ha ; rw [compressionM_normSq K (by omega)] ; have hkpos : 0 ≤ (4*K:ℝ) := (by positivity) ; have hcoef : 0 ≤ (K:ℝ)^2-K+1 := (by nlinarith [sq_nonneg ((K:ℝ)-1)]) ; have hw' := mul_le_mul_of_nonneg_left hw hkpos ; have hz' := mul_le_mul_of_nonneg_left hz hcoef ; have hc := convexity_bound (K:ℝ) (stateY a) hkr hy.1 hy.2 ; unfold f at hc ; nlinarith [hw',hz']
  clear compressionM_normSq stateW_bound stateZ_bound convexity_bound
  have frobenius_norm_sq {ι κ : Type} [Fintype ι] [Fintype κ] (C : Matrix ι κ ℂ) : ‖C‖^2 = entryNormSq C := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]; simp only [Real.rpow_two]; rw [Real.sq_sqrt]
    · rfl
    · positivity
  have mulVec_frobenius_bound {ι κ : Type} [Fintype ι] [Fintype κ] (C : Matrix ι κ ℂ) (y : EuclideanSpace ℂ κ) : ‖(WithLp.toLp 2 (C *ᵥ y.ofLp) : EuclideanSpace ℂ ι)‖ ≤ ‖C‖*‖y‖ := (by have hmat : C * (Matrix.replicateCol Unit y.ofLp) = Matrix.replicateCol Unit (C *ᵥ y.ofLp) := (by ext i j ; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]) ; have h := Matrix.frobenius_norm_mul C (Matrix.replicateCol Unit y.ofLp) ; rw [hmat, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h ; exact h)
  have block_quadratic_bound {ι κ : Type} [Fintype ι] [Fintype κ] (C : Matrix ι κ ℂ) (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ) (r : ℝ) (hr : 0 ≤ r) (hC : entryNormSq C ≤ r^2) (hxy : ‖x‖^2+‖y‖^2 ≤ 1) : 2 * (star x.ofLp ⬝ᵥ (C *ᵥ y.ofLp)).re ≤ r := (by let Cy : EuclideanSpace ℂ ι := WithLp.toLp 2 (C *ᵥ y.ofLp) ; have hCn : ‖C‖ ≤ r := (by have h := frobenius_norm_sq C ; nlinarith [norm_nonneg C]) ; have hnCy : ‖Cy‖ ≤ r*‖y‖ := (mulVec_frobenius_bound C y).trans (mul_le_mul_of_nonneg_right hCn (norm_nonneg _)) ; have hinner : (star x.ofLp ⬝ᵥ (C *ᵥ y.ofLp)).re ≤ ‖x‖*‖Cy‖ := (by rw [dotProduct_comm] ; change (inner ℂ x Cy).re ≤ ‖x‖*‖Cy‖ ; exact (Complex.re_le_norm _).trans (norm_inner_le_norm x Cy)) ; have hmul := mul_le_mul_of_nonneg_left hnCy (norm_nonneg x) ; have hdiff := sq_nonneg (‖x‖-‖y‖) ; have hfinal : 2*‖x‖*‖y‖ ≤ 1 := (by nlinarith) ; have hscale := mul_le_mul_of_nonneg_left hfinal hr ; nlinarith [hinner,hmul,hscale]); clear mulVec_frobenius_bound frobenius_norm_sq
  have spinWV_inverse (n : ℕ) : spinW n * spinV n = 1 := by
    calc spinW n * spinV n = ((2 : ℂ)^n)⁻¹ •
          (spinDinv n * (coeffMatrix n * coeffMatrix n) * spinD n) := by
            unfold spinW spinV; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
         _ = ((2 : ℂ)^n)⁻¹ •
          (spinDinv n * ((2 : ℂ)^n • (1 : SpinMatrix n)) * spinD n) := by
            rw [coeffMatrix_square]
         _ = 1 := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]; rw [spinD_inverse, inv_mul_cancel₀ (by norm_num : (2 : ℂ)^n ≠ 0), one_smul]
  clear coeffMatrix_square spinD_inverse
  have spinV_eq_inverse (n : ℕ) : spinV n = (spinW n)⁻¹ := (by have h := congrArg (fun M : SpinMatrix n => (spinW n)⁻¹ * M) (spinWV_inverse n) ; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (spinW_isUnit n)), Matrix.one_mul, Matrix.mul_one] at h ; exact h); clear spinW_isUnit
  have spin_spectral_explicit (n : ℕ) (g : ℝ → ℝ) : Matrix.IsHermitian.cfc (Jx_hermitian n) g = spinW n * diagonal (fun t => (g (spinEigenvalue n t) : ℂ)) * spinV n := cfc_eq_of_diagonalization (Jx_hermitian n) (spinEigenvalue n)
      (spinW_eigen n) (spinWV_inverse n) g
  have eigenCoeff_col_zero (n r : ℕ) : eigenCoeff n r 0 = (Nat.choose n r : ℂ) := (by simp [eigenCoeff, spinEigenPolynomial, coeff_one_add_X_pow])
  have coeff_comp_scale (p : ℂ[X]) (a : ℂ) (k : ℕ) : (p.comp (C a * X)).coeff k = a^k * p.coeff k := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq, mul_add]
    | monomial n r =>
      simp only [← C_mul_X_pow_eq_monomial]; rw [mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]; simp only [coeff_C_mul_X_pow]
      by_cases h : n=k
      · subst k
        simp [mul_comm]
      · simp [ Ne.symm h]
  have coeff_one_sub_X_pow (n r : ℕ) : ((1-X : ℂ[X])^n).coeff r = (-1 : ℂ)^r * (Nat.choose n r : ℂ) := (by have hp : ((1+X : ℂ[X])^n).comp (C (-1 : ℂ)*X) = (1-X)^n := (by simp [sub_eq_add_neg]) ; rw [← hp, coeff_comp_scale, coeff_one_add_X_pow]); clear coeff_comp_scale
  have eigenCoeff_col_last (n r : ℕ) : eigenCoeff n r n = (-1 : ℂ)^r * (Nat.choose n r : ℂ) := (by simp only [eigenCoeff, spinEigenPolynomial, Nat.sub_self, pow_zero, mul_one, coeff_one_sub_X_pow]); clear coeff_one_sub_X_pow
  have spinV_col_zero (n : ℕ) (t : SpinIndex n) : spinV n t 0 = ((2 : ℂ)^n)⁻¹ * (Nat.choose n t.val : ℂ) := (by simp [spinV, spinD, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, coeffMatrix, eigenCoeff_col_zero, spinRad])
  have spinV_col_last (n : ℕ) (t : SpinIndex n) : spinV n t (Fin.last n) = ((2 : ℂ)^n)⁻¹ * (-1 : ℂ)^t.val * (Nat.choose n t.val : ℂ) := (by simp [spinV, spinD, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, coeffMatrix, eigenCoeff_col_last, spinRad, mul_assoc])
  have c_positive (K : ℕ) : 0 < c K := by
    unfold c; apply mul_pos
    · positivity
    · exact_mod_cast Nat.choose_pos (Nat.div_le_self (K-1) 2)
  have spinW_gram_diagonal (n : ℕ) : (spinW n)ᴴ * spinW n = diagonal (fun t => ((spinW n)ᴴ * spinW n) t t) := by
    have spinEigenvalue_injective (n : ℕ) : Function.Injective (spinEigenvalue n) := by intro t s h ; apply Fin.ext ; have hcast : (t.val : ℝ) = s.val := (by unfold spinEigenvalue at h ; linarith) ; exact_mod_cast hcast
    let D : SpinMatrix n := diagonal (fun t => (spinEigenvalue n t : ℂ))
    have hD : Dᴴ = D := (by simp only [D, diagonal_conjTranspose]; congr 1; funext i; simp)
    have hJ : (Jx n)ᴴ = Jx n := (Jx_hermitian n).eq
    have he := congrArg Matrix.conjTranspose (spinW_eigen n)
    change (Jx n * spinW n)ᴴ = (spinW n * D)ᴴ at he; rw [conjTranspose_mul, conjTranspose_mul, hD, hJ] at he
    have hG : ((spinW n)ᴴ * spinW n) * D = D * ((spinW n)ᴴ * spinW n) := by
      calc ((spinW n)ᴴ * spinW n) * D = (spinW n)ᴴ * (Jx n * spinW n) := by
            rw [spinW_eigen, Matrix.mul_assoc]
           _ = ((spinW n)ᴴ * Jx n) * spinW n := by rw [Matrix.mul_assoc]
           _ = D * ((spinW n)ᴴ * spinW n) := by rw [he, Matrix.mul_assoc]
    ext i j
    by_cases hij : i=j
    · subst j
      simp
    · rw [diagonal_apply_ne _ hij]
      have h := congrArg (fun M : SpinMatrix n => M i j) hG
      simp only [D, mul_diagonal, diagonal_mul] at h
      have hd : (spinEigenvalue n j : ℂ) - (spinEigenvalue n i : ℂ) ≠ 0 := (by apply sub_ne_zero.mpr; intro hv; have hs := spinEigenvalue_injective n (Complex.ofReal_injective hv); exact hij hs.symm)
      have hz : ((spinW n)ᴴ * spinW n) i j * ((spinEigenvalue n j : ℂ)-(spinEigenvalue n i : ℂ)) = 0 := (by linear_combination h)
      exact (mul_eq_zero.mp hz).resolve_right hd
  clear spinW_eigen
  have spinV_weighted_adjoint (n : ℕ) (t j : SpinIndex n) : spinV n t j = spinWeight n t * star (spinW n j t) := by
    let d : SpinIndex n → ℂ := fun t => ((spinW n)ᴴ * spinW n) t t
    have hWV := spinWV_inverse n
    have he : (spinW n)ᴴ = diagonal d * spinV n := by
      calc (spinW n)ᴴ = (spinW n)ᴴ * (spinW n * spinV n) := by rw [hWV, Matrix.mul_one]
           _ = diagonal d * spinV n := by rw [← Matrix.mul_assoc, spinW_gram_diagonal]
    have ht := congrArg (fun M : SpinMatrix n => M t 0) he
    simp only [conjTranspose_apply, diagonal_mul, spinV_col_zero,
      spinW_col_zero, star_one] at ht
    change 1 = d t * spinWeight n t at ht
    have hj := congrArg (fun M : SpinMatrix n => M t j) he
    simp only [conjTranspose_apply, diagonal_mul] at hj; change star (spinW n j t) = d t * spinV n t j at hj; rw [hj, ← mul_assoc, mul_comm (spinWeight n t), ← ht, one_mul]
  clear spinW_gram_diagonal spinV_col_zero spinWV_inverse
  have reflect_linear_power (q : ℂ[X]) (hq : q.natDegree ≤ 1) (n : ℕ) : (q^n).reflect n = (q.reflect 1)^n := by
    induction n with
    | zero => simp [reflect_one]
    | succ n ih =>
      rw [pow_succ, reflect_mul, ih, pow_succ]
      · exact (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left n hq)
      · exact hq
  have spinEigenPolynomial_reflect (u v : ℕ) : (spinEigenPolynomial u v).reflect (u+v) = C ((-1 : ℂ)^u) * spinEigenPolynomial u v := by
    have hminus : (1-X : ℂ[X]).reflect 1 = -(1-X) := (by rw [reflect_sub, reflect_one, reflect_one_X, pow_one]; ring)
    have hplus : (1+X : ℂ[X]).reflect 1 = 1+X := (by rw [reflect_add, reflect_one, reflect_one_X, pow_one]; ring)
    unfold spinEigenPolynomial
    rw [reflect_mul, reflect_linear_power _ (by compute_degree),
      reflect_linear_power _ (by compute_degree), hminus, hplus, neg_pow]
    · rw [C_pow]
      simp only [C_neg, C_1]; ring
    · exact (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left u (show (1-X : ℂ[X]).natDegree ≤ 1 by compute_degree))
    · exact (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left v (show (1+X : ℂ[X]).natDegree ≤ 1 by compute_degree))
  clear reflect_linear_power
  have eigenCoeff_reflection (n t r : ℕ) (ht : t ≤ n) (hr : r ≤ n) : eigenCoeff n (n-r) t = (-1 : ℂ)^t * eigenCoeff n r t := (by have h := spinEigenPolynomial_reflect t (n-t) ; rw [Nat.add_sub_of_le ht] at h ; have hc := congrArg (fun p : ℂ[X] => p.coeff r) h ; rw [coeff_reflect, revAt_le hr, coeff_C_mul] at hc ; exact hc); clear spinEigenPolynomial_reflect
  have eigenCoeff_one (n t : ℕ) (ht : t ≤ n) : eigenCoeff n 1 t = (n : ℂ) - 2*t := (by rw [eigenCoeff, spinEigenPolynomial_row_zero, Nat.cast_sub ht] ; ring)
  have eigenCoeff_two_central_plus (L : ℕ) : eigenCoeff (2*L+1) 2 L = -(L : ℂ) := (by have h := spinEigenPolynomial_row_succ L (L+1) 0 ; have hn : 2*L+1-L=L+1 := (by omega) ; have hc0 := spinEigenPolynomial_const L (L+1) ; have hc1 := spinEigenPolynomial_row_zero L (L+1) ; simp only [hc0, hc1, Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_one] at h ; unfold eigenCoeff ; rw [hn] ; linear_combination h / 2)
  have eigenCoeff_two_central_minus (L : ℕ) : eigenCoeff (2*L+1) 2 (L+1) = -(L : ℂ) := (by have h := spinEigenPolynomial_row_succ (L+1) L 0 ; have hn : 2*L+1-(L+1)=L := (by omega) ; have hc0 := spinEigenPolynomial_const (L+1) L ; have hc1 := spinEigenPolynomial_row_zero (L+1) L ; simp only [hc0, hc1, Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_one] at h ; unfold eigenCoeff ; rw [hn] ; linear_combination h / 2); clear spinEigenPolynomial_row_succ spinEigenPolynomial_row_zero spinEigenPolynomial_const
  have Q_sign_average (K : ℕ) (hK : K ≠ 0) : (2 : ℂ) • Q K - 1 = totalRotationAverage K (signOp (total K (Jx 2) (Jx K))) := by
    have totalRotationAverage_one (K : ℕ) (hK : K ≠ 0) : totalRotationAverage K 1 = 1 := by unfold totalRotationAverage ; simp only [Matrix.mul_one, totalRotation_inverse, Finset.sum_const, Finset.card_univ, Fintype.card_fin] ; rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul] ; have hKC : (K : ℂ) ≠ 0 := (by exact_mod_cast hK) ; simp [hKC]
    have totalRotationAverage_sub (K : ℕ) (H G : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) : totalRotationAverage K (H-G) = totalRotationAverage K H - totalRotationAverage K G := by simp [totalRotationAverage, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, smul_sub]
    have totalRotationAverage_smul (K : ℕ) (r : ℂ) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) : totalRotationAverage K (r • H) = r • totalRotationAverage K H := by simp only [totalRotationAverage, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum] ; rw [smul_comm]
    have hA := total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K) ; rw [spectral_sign_eq_two_pos_sub_one hA, totalRotationAverage_sub, totalRotationAverage_smul, totalRotationAverage_one K hK, ← Q_rotation_average]
  clear Q_rotation_average spectral_sign_eq_two_pos_sub_one
  have product_quadratic_compression (K : ℕ) (a : SpinVector 2) (b : SpinVector K) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) : star (productVector K a b).ofLp ⬝ᵥ (H *ᵥ (productVector K a b).ofLp) = star b.ofLp ⬝ᵥ (compression K a H *ᵥ b.ofLp) := by
    simp only [productVector, dotProduct, Matrix.mulVec, compression, Pi.star_apply, star_mul, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi
    conv_lhs =>
      arg 2
      ext p
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j hj; apply Finset.sum_congr rfl; intro p hp; apply Finset.sum_congr rfl; intro q hq; ring
  have sum_sign_half_grid (L : ℕ) (f : ℕ → ℂ) : (∑ t ∈ Finset.range (2*L+2), (Real.sign ((L:ℝ)+1/2-t) : ℂ) * f t) = 2 * (∑ t ∈ Finset.range (L+1), f t) - ∑ t ∈ Finset.range (2*L+2), f t := by
    have hn : 2*L+2 = (L+1)+(L+1) := by omega
    rw [hn]; rw [Finset.sum_range_add _ (L+1) (L+1)]
    conv_rhs => rw [Finset.sum_range_add _ (L+1) (L+1)]
    have hfirst : (∑ t ∈ Finset.range (L+1), (Real.sign ((L:ℝ)+1/2-t) : ℂ) * f t) = ∑ t ∈ Finset.range (L+1), f t := by
      apply Finset.sum_congr rfl; intro t ht
      have htR : (t:ℝ) ≤ L := by exact_mod_cast (show t ≤ L from Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
      have hp : 0 < (L:ℝ)+1/2-t := by linarith
      simp only [Real.sign_of_pos hp, Complex.ofReal_one, one_mul]
    have hsecond : (∑ t ∈ Finset.range (L+1),
        (Real.sign ((L:ℝ)+1/2-(L+1+t:ℕ)) : ℂ)*f (L+1+t)) = -∑ t ∈ Finset.range (L+1), f (L+1+t) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro t ht
      have hp : ¬0 < (L:ℝ)+1/2-(L+1+t:ℕ) := by push_cast ; have := (Nat.cast_nonneg t : (0:ℝ) ≤ t) ; linarith
      have hz : (L:ℝ)+1/2-(L+1+t:ℕ) ≠ 0 := by push_cast ; have := (Nat.cast_nonneg t : (0:ℝ) ≤ t) ; linarith
      simp only [Real.sign_of_neg (lt_of_le_of_ne (le_of_not_gt hp) hz), Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
    rw [hfirst,hsecond]; ring
  have sign_spin_endpoint (L : ℕ) : signOp (Jx (2*L+1)) 0 (Fin.last (2*L+1)) = ((-1 : ℂ)^L) * (c (2*L+1) : ℂ) := by
    rw [signOp, dif_pos (Jx_hermitian (2*L+1)), spin_spectral_explicit, Matrix.mul_apply]; simp only [Matrix.mul_diagonal, spinW_col_zero, one_mul, spinV_col_last]
    have hlam : ∀ t : SpinIndex (2*L+1), spinEigenvalue (2*L+1) t = (L:ℝ)+1/2-t.val := by intro t; unfold spinEigenvalue; push_cast; ring
    simp_rw [hlam]
    have hf : (∑ t : SpinIndex (2*L+1), (Real.sign ((L:ℝ)+1/2-t.val) : ℂ) * (((2 : ℂ)^(2*L+1))⁻¹ * (-1 : ℂ)^t.val * (Nat.choose (2*L+1) t.val : ℂ))) = (((2 : ℂ)^(2*L+1))⁻¹) * ∑ t : SpinIndex (2*L+1), (Real.sign ((L:ℝ)+1/2-t.val) : ℂ) * ((-1 : ℂ)^t.val * (Nat.choose (2*L+1) t.val : ℂ)) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht; ring
    rw [hf]
    change ((2 : ℂ)^(2*L+1))⁻¹ * (∑ t : Fin (2*L+2),
      (Real.sign ((L:ℝ)+1/2-t.val) : ℂ) * ((-1 : ℂ)^t.val * (Nat.choose (2*L+1) t.val : ℂ))) = _
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
      (Real.sign ((L:ℝ)+1/2-t) : ℂ) * ((-1 : ℂ)^t * (Nat.choose (2*L+1) t : ℂ)))]
    have hn : 2*L+1+1=2*L+2 := by omega
    rw [hn, sum_sign_half_grid]
    have hhalf : (∑ t ∈ Finset.range (L+1), (-1 : ℂ)^t * (Nat.choose (2*L+1) t : ℂ)) = (-1 : ℂ)^L * (Nat.choose (2*L) L : ℂ) := by exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n:=2*L) (m:=L))
    have hall : (∑ t ∈ Finset.range (2*L+2), (-1 : ℂ)^t * (Nat.choose (2*L+1) t : ℂ)) = 0 := by exact_mod_cast (Int.alternating_sum_range_choose_of_ne (n:=2*L+1) (by omega))
    rw [hhalf,hall,sub_zero]; unfold c
    have hsub : 2*L+1-1=2*L := by omega
    have hdiv : (2*L)/2=L := by omega
    rw [hsub,hdiv]; push_cast; rw [pow_add,pow_one]; field_simp
  clear sum_sign_half_grid spinV_col_last spin_spectral_explicit
  have levelProjector_rankone (n : ℕ) (t : SpinIndex n) (i j : SpinIndex n) : levelProjector n t.val i j = spinWeight n t * spinW n i t * star (spinW n j t) := (by rw [levelProjector, ← spinV_eq_inverse, Matrix.mul_apply] ; simp only [Matrix.mul_diagonal] ; have he : ∀ a : SpinIndex n, (a.val=t.val) ↔ a=t := (by intro a ; exact Fin.val_inj) ; simp only [he, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, spinV_weighted_adjoint] ; ring); clear spinV_weighted_adjoint spinV_eq_inverse
  have spinW_entry (n : ℕ) (i t : SpinIndex n) : spinW n i t = (spinRad n i : ℂ)⁻¹ * eigenCoeff n i.val t.val := (by simp [spinW, spinDinv, Matrix.diagonal_mul, coeffMatrix])
  have spinRad_reflection (n : ℕ) (i j : SpinIndex n) (hj : j.val=n-i.val) : spinRad n j = spinRad n i := (by simp only [spinRad, hj, Nat.choose_symm (Nat.le_of_lt_succ i.isLt)])
  have spinW_reflection (n : ℕ) (i j t : SpinIndex n) (hj : j.val=n-i.val) : spinW n j t = (-1 : ℂ)^t.val * spinW n i t := (by rw [spinW_entry, spinW_entry, spinRad_reflection n i j hj, hj, eigenCoeff_reflection n t.val i.val (Nat.le_of_lt_succ t.isLt) (Nat.le_of_lt_succ i.isLt)] ; ring); clear spinRad_reflection eigenCoeff_reflection
  have spinWeight_central (L : ℕ) (t : SpinIndex (2*L+1)) (ht : t.val=L ∨ t.val=L+1) : spinWeight (2*L+1) t = ((c (2*L+1) * (2*L+1)/(2*L+2) : ℝ) : ℂ) := by
    have hc : Nat.choose (2*L+1) (L+1) = Nat.choose (2*L+1) L := (by have h := Nat.choose_symm (show L ≤ 2*L+1 by omega); have hn : 2*L+1-L=L+1 := (by omega); rwa [hn] at h)
    have hb : (Nat.choose (2*L+1) L : ℂ) * (L+1) = (2*L+1) * (Nat.choose (2*L) L : ℂ) := (by have h := Nat.choose_mul_succ_eq (2*L) L; have hn : 2*L+1-L=L+1 := (by omega); rw [hn] at h; have hh : (Nat.choose (2*L+1) L)*(L+1)=(2*L+1)*Nat.choose (2*L) L := (by nlinarith [h]); exact_mod_cast hh)
    unfold spinWeight c
    rcases ht with ht|ht <;> rw [ht]
    all_goals try rw [hc]
    all_goals have hs : 2*L+1-1=2*L := (by omega)
    all_goals have hd : 2*L/2=L := (by omega)
    all_goals rw [hs,hd]
    all_goals push_cast
    all_goals rw [pow_add,pow_one]
    all_goals have hL : (L:ℂ)+1 ≠ 0 := (by exact_mod_cast (show (L:ℝ)+1 ≠ 0 by positivity))
    all_goals have hL2 : 2*(L:ℂ)+2 ≠ 0 := (by exact_mod_cast (show 2*(L:ℝ)+2 ≠ 0 by positivity))
    all_goals field_simp
    all_goals linear_combination hb
  have spinW_firstColumn (n : ℕ) (i : SpinIndex n) : spinW n i 0 = (spinRad n i : ℂ) := (by rw [spinW_entry] ; simp only [Fin.val_zero, eigenCoeff_col_zero] ; have hr : (spinRad n i : ℂ)^2 = (Nat.choose n i.val : ℂ) := (by norm_cast ; exact Real.sq_sqrt (Nat.cast_nonneg _)) ; rw [← hr, pow_two] ; have hz : (spinRad n i : ℂ) ≠ 0 := (by exact_mod_cast ne_of_gt (spinRad_pos n i)) ; field_simp); clear spinRad_pos
  have spinW_lastColumn (n : ℕ) (i : SpinIndex n) : spinW n i (Fin.last n) = (-1 : ℂ)^i.val * (spinRad n i : ℂ) := by
    rw [spinW_entry]; simp only [Fin.val_last, eigenCoeff_col_last]
    have hf := spinW_firstColumn n i
    rw [spinW_entry] at hf; simp only [Fin.val_zero, eigenCoeff_col_zero] at hf
    calc _ = (-1 : ℂ)^i.val * ((spinRad n i : ℂ)⁻¹ * (Nat.choose n i.val : ℂ)) := by ring
         _ = _ := by rw [hf]
  clear eigenCoeff_col_last eigenCoeff_col_zero
  have spinRad_two (p : SpinIndex 2) : spinRad 2 p = spinOneRad p := (by fin_cases p <;> norm_num [spinRad, spinOneRad, Nat.choose])
  have levelProjector_two_plus (p q : SpinIndex 2) : levelProjector 2 0 p q = (1/4:ℂ) * (spinOneRad p : ℂ) * (spinOneRad q : ℂ) := (by rw [show (0:ℕ)=(0:SpinIndex 2).val by rfl, levelProjector_rankone] ; norm_num [spinWeight, spinW_firstColumn, spinRad_two]); clear spinW_firstColumn
  have levelProjector_two_minus (p q : SpinIndex 2) : levelProjector 2 2 p q = (1/4:ℂ) * (-1:ℂ)^(p.val+q.val) * (spinOneRad p : ℂ) * (spinOneRad q : ℂ) := (by change levelProjector 2 (Fin.last 2).val p q = _ ; rw [levelProjector_rankone] ; simp only [spinWeight, Fin.val_last, Nat.choose_self, Nat.cast_one, mul_one, spinW_lastColumn, star_mul, star_pow, star_neg, star_one, Complex.star_def, Complex.conj_ofReal] ; rw [spinRad_two, spinRad_two, pow_add] ; norm_num ; ring); clear spinRad_two spinW_lastColumn
  have choose_two_real (n : ℕ) : (Nat.choose n 2 : ℝ) = (n:ℝ)*(n-1:ℝ)/2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      have hc := Nat.choose_succ_right_eq (n+1) 1
      simp only [Nat.choose_one_right, Nat.add_sub_cancel] at hc
      have hr := congrArg (fun x:ℕ => (x:ℝ)) hc
      push_cast at hr ⊢; nlinarith
  have spinRad_top_one (L : ℕ) (hL : 1 ≤ L) : spinRad (2*L+1) (edgeTop (2*L+1) (by omega) 1) = Real.sqrt (2*L+1:ℝ) := (by simp [spinRad, edgeTop, Nat.choose_one_right])
  have spinRad_top_two (L : ℕ) (hL : 1 ≤ L) : spinRad (2*L+1) (edgeTop (2*L+1) (by omega) 2) = Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2) := (by change Real.sqrt (Nat.choose (2*L+1) 2 : ℝ) = _ ; rw [choose_two_real] ; congr 1 ; push_cast ; ring); clear choose_two_real
  have centralPlus_top (L : ℕ) (hL : 1 ≤ L) (r : Fin 3) : spinW (2*L+1) (edgeTop (2*L+1) (by omega) r) (centralPlus L) = centralEdgeVector L 1 r := by
    fin_cases r
    · simp [spinW_col_zero, edgeTop, centralEdgeVector]
    · change spinW (2*L+1) (edgeTop (2*L+1) (by omega) 1) (centralPlus L) = _
      rw [spinW_entry, spinRad_top_one L hL]; change (Real.sqrt (2*L+1:ℝ):ℂ)⁻¹ * eigenCoeff (2*L+1) 1 L = _; rw [eigenCoeff_one _ _ (by omega)]; dsimp [centralEdgeVector]; push_cast; ring
    · change spinW (2*L+1) (edgeTop (2*L+1) (by omega) 2) (centralPlus L) = _
      rw [spinW_entry, spinRad_top_two L hL]; change (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹ * eigenCoeff (2*L+1) 2 L = _; rw [eigenCoeff_two_central_plus]; dsimp [centralEdgeVector]; ring
  clear eigenCoeff_two_central_plus
  have centralMinus_top (L : ℕ) (hL : 1 ≤ L) (r : Fin 3) : spinW (2*L+1) (edgeTop (2*L+1) (by omega) r) (centralMinus L) = centralEdgeVector L (-1) r := by
    fin_cases r
    · simp [spinW_col_zero, edgeTop, centralEdgeVector]
    · change spinW (2*L+1) (edgeTop (2*L+1) (by omega) 1) (centralMinus L) = _
      rw [spinW_entry, spinRad_top_one L hL]; change (Real.sqrt (2*L+1:ℝ):ℂ)⁻¹ * eigenCoeff (2*L+1) 1 (L+1) = _; rw [eigenCoeff_one _ _ (by omega)]; dsimp [centralEdgeVector]; push_cast; ring
    · change spinW (2*L+1) (edgeTop (2*L+1) (by omega) 2) (centralMinus L) = _
      rw [spinW_entry, spinRad_top_two L hL]; change (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹ * eigenCoeff (2*L+1) 2 (L+1) = _; rw [eigenCoeff_two_central_minus]; dsimp [centralEdgeVector]; ring
  clear spinRad_top_two spinRad_top_one spinW_entry eigenCoeff_two_central_minus eigenCoeff_one spinW_col_zero
  have signOp_neg {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : signOp (-H) = -signOp H := by
    have hn : (-H).IsHermitian := hH.neg
    let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
    have hUV : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    have hVU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have hs : H = U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := (by simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, U] using hH.spectral_theorem)
    have he : (-H) * U = U * diagonal (fun i => ((-hH.eigenvalues i : ℝ) : ℂ)) := by
      conv_lhs => rw [hs]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]; rw [hVU, Matrix.mul_one]; simp only [Complex.ofReal_neg]
      have hd : diagonal (fun i => -(hH.eigenvalues i : ℂ)) = -diagonal (fun i => (hH.eigenvalues i : ℂ)) := (by ext i j; by_cases h : i=j <;> simp [diagonal,h])
      rw [hd, Matrix.mul_neg]
    rw [signOp, dif_pos hn, signOp, dif_pos hH,
      cfc_eq_of_diagonalization hn (fun i => -hH.eigenvalues i) he hUV]
    simp only [Real.sign_neg, Complex.ofReal_neg, ← diagonal_neg,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose, U]
  clear cfc_eq_of_diagonalization
  have sign_total_entry_zero (K : ℕ) (p q : SpinIndex 2) (i j : SpinIndex K) (he : (p.val : ℤ)+i.val-q.val-j.val=0) : signOp (total K (Jx 2) (Jx K)) (p,i) (q,j) = 0 := by
    let H := total K (Jx 2) (Jx K)
    have hH : H.IsHermitian := total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K)
    have hr : -H = totalRotation K Real.pi * H * totalRotation K (-Real.pi) := (by rw [totalRotation_Jx]; simp [H])
    have hs : signOp (-H) = totalRotation K Real.pi * signOp H * totalRotation K (-Real.pi) := (by rw [signOp, dif_pos hH.neg, signOp, dif_pos hH]; exact cfc_conjugation hH hH.neg hr (totalRotation_inverse K Real.pi) (by simpa using totalRotation_inverse K (-Real.pi)) Real.sign)
    have hc := congrArg (fun M => M (p,i) (q,j)) hs
    rw [signOp_neg hH, totalRotation_entry] at hc
    have hC : (p.val : ℂ)+i.val-q.val-j.val=0 := by exact_mod_cast he
    simp only [hC, mul_zero, Complex.exp_zero, one_mul, Matrix.neg_apply] at hc; change -signOp H (p,i) (q,j) = signOp H (p,i) (q,j) at hc
    linear_combination -hc / 2
  clear signOp_neg totalRotation_entry totalRotation_Jx totalRotation_inverse cfc_conjugation
  have selected_total_sign (K : ℕ) (hK : 7 ≤ K) (p q : SpinIndex 2) (i j : SpinIndex K) : totalRotationAverage K (signOp (total K (Jx 2) (Jx K))) (p,i) (q,j) = if (p.val : ℤ)+i.val-q.val-j.val = K ∨ (p.val : ℤ)+i.val-q.val-j.val = -(K : ℤ) then signOp (total K (Jx 2) (Jx K)) (p,i) (q,j) else 0 := by
    rw [totalRotationAverage_selection K (by omega)]
    let d : ℤ := (p.val : ℤ)+i.val-q.val-j.val
    have hdl : -(K : ℤ)-2 ≤ d := by dsimp [d] ; have := p.isLt ; have := q.isLt ; have := i.isLt ; have := j.isLt ; omega
    have hdu : d ≤ (K : ℤ)+2 := by dsimp [d] ; have := p.isLt ; have := q.isLt ; have := i.isLt ; have := j.isLt ; omega
    have hKR : (7 : ℤ) ≤ K := by exact_mod_cast hK
    by_cases hv : (K : ℤ) ∣ d
    · obtain ⟨z, hz⟩ := hv
      have hz0 : -1 ≤ z := by
        by_contra h ; have : z ≤ -2 := by omega
        have hm : (K : ℤ)*z ≤ (K : ℤ)*(-2) := mul_le_mul_of_nonneg_left this (by omega)
        nlinarith
      have hz1 : z ≤ 1 := by
        by_contra h ; have : 2 ≤ z := by omega
        have hm : (K : ℤ)*2 ≤ (K : ℤ)*z := mul_le_mul_of_nonneg_left this (by omega)
        nlinarith
      have hd : d=-(K : ℤ) ∨ d=0 ∨ d=K := by
        have : z = -1 ∨ z=0 ∨ z=1 := by omega
        rcases this with h|h|h <;> simp [h] at hz <;> omega
      rw [if_pos (show (K : ℤ) ∣ ((p.val : ℤ)+i.val-q.val-j.val) from ⟨z,hz⟩)]
      rcases hd with h|h|h
      · rw [if_pos (Or.inr h)]
      · rw [if_neg (show ¬(d=K ∨ d=-(K:ℤ)) by omega)]
        exact sign_total_entry_zero K p q i j h
      · rw [if_pos (Or.inl h)]
    · rw [if_neg hv]
      rw [if_neg]
      rintro (h|h)
      · exact hv (by change (K : ℤ) ∣ ((p.val : ℤ)+i.val-q.val-j.val) ; rw [h])
      · exact hv (by change (K : ℤ) ∣ ((p.val : ℤ)+i.val-q.val-j.val) ; rw [h] ; exact dvd_neg.mpr (dvd_refl _))
  have centralEdgeVector_star (L : ℕ) (epsilon : ℝ) (r : Fin 3) : star (centralEdgeVector L (epsilon:ℂ) r) = centralEdgeVector L (epsilon:ℂ) r := (by fin_cases r <;> simp [centralEdgeVector])
  have centralPlus_edge_projector (L : ℕ) (hL : 1 ≤ L) (r s : Fin 3) : levelProjector (2*L+1) L (edgeTop (2*L+1) (by omega) r) (edgeBottom (2*L+1) (by omega) s) = spinWeight (2*L+1) (centralPlus L) * (-1:ℂ)^L * centralEdgeVector L 1 r * centralEdgeVector L 1 s := (by change levelProjector (2*L+1) (centralPlus L).val _ _ = _ ; rw [levelProjector_rankone, spinW_reflection (2*L+1) (edgeTop (2*L+1) (by omega) s) (edgeBottom (2*L+1) (by omega) s) (centralPlus L) (by rfl), centralPlus_top L hL, centralPlus_top L hL] ; simp only [centralPlus, star_mul, star_pow, star_neg, star_one] ; rw [show (1:ℂ)=(1:ℝ) by norm_num, centralEdgeVector_star] ; ring); clear centralPlus_top
  have centralMinus_edge_projector (L : ℕ) (hL : 1 ≤ L) (r s : Fin 3) : levelProjector (2*L+1) (L+1) (edgeTop (2*L+1) (by omega) r) (edgeBottom (2*L+1) (by omega) s) = -spinWeight (2*L+1) (centralMinus L) * (-1:ℂ)^L * centralEdgeVector L (-1) r * centralEdgeVector L (-1) s := (by change levelProjector (2*L+1) (centralMinus L).val _ _ = _ ; rw [levelProjector_rankone, spinW_reflection (2*L+1) (edgeTop (2*L+1) (by omega) s) (edgeBottom (2*L+1) (by omega) s) (centralMinus L) (by rfl), centralMinus_top L hL, centralMinus_top L hL] ; simp only [centralMinus, star_mul, star_pow, star_neg, star_one, pow_succ] ; have he := centralEdgeVector_star L (-1) s ; norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at he ; simp only [he] ; ring); clear centralEdgeVector_star centralMinus_top spinW_reflection levelProjector_rankone
  have total_top_bottom_selection (L : ℕ) (hL : 3 ≤ L) (p q : SpinIndex 2) (r s : Fin 3) : totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1)))) (p,edgeTop (2*L+1) (by omega) r) (q,edgeBottom (2*L+1) (by omega) s) = if q.val = p.val+r.val+s.val then signOp (total (2*L+1) (Jx 2) (Jx (2*L+1))) (p,edgeTop (2*L+1) (by omega) r) (q,edgeBottom (2*L+1) (by omega) s) else 0 := (by rw [selected_total_sign _ (by omega)] ; have hp := p.isLt ; have hq := q.isLt ; have hr := r.isLt ; have hs := s.isLt ; have he : ((p.val:ℤ)+(edgeTop (2*L+1) (by omega) r).val-q.val- (edgeBottom (2*L+1) (by omega) s).val = (2*L+1:ℕ) ∨ (p.val:ℤ)+(edgeTop (2*L+1) (by omega) r).val-q.val- (edgeBottom (2*L+1) (by omega) s).val = -((2*L+1:ℕ):ℤ)) ↔ q.val=p.val+r.val+s.val := (by simp only [edgeTop, edgeBottom] ; omega) ; simp only [he])
  have selected_baseline_edge (L : ℕ) (hL : 3 ≤ L) (p q : SpinIndex 2) (r s : Fin 3) : (if q.val=p.val+r.val+s.val then ((1 : SpinMatrix 2) ⊗ₖ signOp (Jx (2*L+1))) (p,edgeTop (2*L+1) (by omega) r) (q,edgeBottom (2*L+1) (by omega) s) else 0) = if r=0 ∧ s=0 ∧ p=q then (-1:ℂ)^L*(c (2*L+1):ℂ) else 0 := by
    by_cases hpq : p=q
    · subst q
      by_cases hr : r=0
      · subst r
        by_cases hs : s=0
        · subst s
          simp only [Fin.val_zero, add_zero, if_true, Matrix.kronecker_apply,
            Matrix.one_apply_eq, one_mul, and_self, eq_self]
          change signOp (Jx (2*L+1)) 0 (Fin.last (2*L+1)) = _; exact sign_spin_endpoint L
        · have hc : ¬p.val=p.val+(0:Fin 3).val+s.val := by
            have : s.val ≠ 0 := by simpa using hs
            simp only [Fin.val_zero]
            omega
          simp [hs]
      · have hc : ¬p.val=p.val+r.val+s.val := by
          have : r.val ≠ 0 := by simpa using hr
          omega
        simp [hc,hr]
    · simp [ Matrix.one_apply_ne hpq, hpq]
  clear sign_spin_endpoint
  have averaged_sign_edge (L : ℕ) (hL : 3 ≤ L) (p q : SpinIndex 2) (r s : Fin 3) : totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1)))) (p,edgeTop (2*L+1) (by omega) r) (q,edgeBottom (2*L+1) (by omega) s) = (if r=0 ∧ s=0 ∧ p=q then (-1:ℂ)^L*(c (2*L+1):ℂ) else 0) - (if q.val=p.val+r.val+s.val then 2*(-1:ℂ)^L*spinWeight (2*L+1) (centralPlus L)* (levelProjector 2 0 p q*centralEdgeVector L (-1) r*centralEdgeVector L (-1) s + levelProjector 2 2 p q*centralEdgeVector L 1 r*centralEdgeVector L 1 s) else 0) := by
    rw [total_top_bottom_selection L hL]
    have hb := selected_baseline_edge L hL p q r s
    have hw : spinWeight (2*L+1) (centralMinus L) = spinWeight (2*L+1) (centralPlus L) := (by rw [spinWeight_central L _ (Or.inr rfl), spinWeight_central L _ (Or.inl rfl)])
    by_cases hc : q.val=p.val+r.val+s.val
    · simp only [if_pos hc] at hb ⊢
      rw [tensor_sign_decomposition]
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.kronecker_apply]
      rw [centralMinus_edge_projector L (by omega), centralPlus_edge_projector L (by omega), hw]; change (1 : SpinMatrix 2) p q * signOp (Jx (2*L+1))
        (edgeTop (2*L+1) (by omega) r) (edgeBottom (2*L+1) (by omega) s) = _ at hb
      rw [hb]; ring
    · rw [if_neg hc] at hb
      rw [if_neg hc, if_neg hc, ← hb]; simp
  clear selected_baseline_edge total_top_bottom_selection centralMinus_edge_projector centralPlus_edge_projector tensor_sign_decomposition
  have averaged_sign_hermitian (K : ℕ) (hK : K ≠ 0) : (totalRotationAverage K (signOp (total K (Jx 2) (Jx K)))).IsHermitian := by
    have hH := total_hermitian K _ _ (Jx_hermitian 2) (Jx_hermitian K)
    have hs : (signOp (total K (Jx 2) (Jx K))).IsHermitian := (by rw [signOp, dif_pos hH, ← hH.cfc_eq]; exact cfc_predicate Real.sign _)
    ext u v
    obtain ⟨p,i⟩ := u
    obtain ⟨q,j⟩ := v
    simp only [conjTranspose_apply, totalRotationAverage_selection K hK]
    have hd : ((K:ℤ) ∣ ((q.val:ℤ)+j.val-p.val-i.val)) ↔ ((K:ℤ) ∣ ((p.val:ℤ)+i.val-q.val-j.val)) := (by rw [show (q.val:ℤ)+j.val-p.val-i.val = -((p.val:ℤ)+i.val-q.val-j.val) by ring]; exact dvd_neg)
    simp only [hd]
    split_ifs
    · exact congrArg (fun M => M (p,i) (q,j)) hs.eq
    · simp
  clear total_hermitian Jx_hermitian
  have compression_hermitian (K : ℕ) (a : SpinVector 2) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) (hH : H.IsHermitian) : (compression K a H).IsHermitian := (by ext i j ; simp only [conjTranspose_apply, compression, star_sum, star_mul, star_star] ; rw [Finset.sum_comm] ; apply Finset.sum_congr rfl ; intro p hp ; apply Finset.sum_congr rfl ; intro q hq ; have he := congrArg (fun M => M (p,i) (q,j)) hH.eq ; simp only [conjTranspose_apply] at he ; rw [he] ; ring)
  have compression_sign_support (K : ℕ) (hK : 7 ≤ K) (a : SpinVector 2) (i j : SpinIndex K) (hij : ¬(i.val<3 ∧ K-j.val<3) ∧ ¬(K-i.val<3 ∧ j.val<3)) : compression K a (totalRotationAverage K (signOp (total K (Jx 2) (Jx K)))) i j = 0 := (by unfold compression ; apply Finset.sum_eq_zero ; intro p hp ; apply Finset.sum_eq_zero ; intro q hq ; rw [selected_total_sign K hK] ; have hd : ¬((p.val:ℤ)+i.val-q.val-j.val = (K:ℤ) ∨ (p.val:ℤ)+i.val-q.val-j.val = -(K:ℤ)) := (by have := p.isLt ; have := q.isLt ; have := i.isLt ; have := j.isLt ; omega) ; rw [if_neg hd] ; simp); clear selected_total_sign
  have single_quadratic {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) (z : ℂ) (b : ι → ℂ) : star b ⬝ᵥ (Matrix.single i j z *ᵥ b) = star (b i) * z * b j := (by rw [Matrix.single_mulVec_eq] ; simp only [dotProduct_smul, dotProduct_single, Pi.star_apply, mul_one] ; ring)
  have scatterBlock_quadratic (K : ℕ) (hK : 2 ≤ K) (C : Matrix (Fin 3) (Fin 3) ℂ) (b : SpinVector K) : (star b.ofLp ⬝ᵥ (scatterBlock K hK C *ᵥ b.ofLp)).re = 2 * (star (edgeVectorTop K hK b).ofLp ⬝ᵥ (C *ᵥ (edgeVectorBottom K hK b).ofLp)).re := (by simp only [scatterBlock, Matrix.sum_mulVec, Matrix.add_mulVec, dotProduct_sum, dotProduct_add, single_quadratic] ; simp only [ edgeVectorTop, edgeVectorBottom, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum] ; simp only [Complex.re_sum, Complex.add_re] ; rw [Finset.mul_sum] ; apply Finset.sum_congr rfl ; intro r hr ; rw [Finset.mul_sum] ; apply Finset.sum_congr rfl ; intro s hs ; have he : star (b (edgeBottom K hK s)) * star (C r s) * b (edgeTop K hK r) = star (star (b (edgeTop K hK r)) * C r s * b (edgeBottom K hK s)) := (by simp only [star_mul, star_star] ; ring) ; rw [he] ; simp only [Complex.star_def, Complex.conj_re] ; ring); clear single_quadratic
  have edgeMap_injective (K : ℕ) (hK : 7 ≤ K) : Function.Injective (edgeMap K (by omega)) := by
    intro u v h
    have he := congrArg Fin.val h
    cases u with
    | inl r =>
      cases v with
      | inl s => apply congrArg Sum.inl ; apply Fin.ext ; exact he
      | inr s => have := r.isLt ; have := s.isLt ; simp only [edgeMap, Sum.elim_inl, Sum.elim_inr, edgeTop, edgeBottom] at he ; omega
    | inr r =>
      cases v with
      | inl s => have := r.isLt ; have := s.isLt ; simp only [edgeMap, Sum.elim_inl, Sum.elim_inr, edgeTop, edgeBottom] at he ; omega
      | inr s => apply congrArg Sum.inr ; apply Fin.ext ; have := r.isLt ; have := s.isLt ; simp only [edgeMap, Sum.elim_inr, edgeBottom] at he ; omega
  have edgeVector_norm_sq (K : ℕ) (hK : 7 ≤ K) (b : SpinVector K) (hb : ‖b‖=1) : ‖edgeVectorTop K (by omega) b‖^2 + ‖edgeVectorBottom K (by omega) b‖^2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]; simp only [edgeVectorTop, edgeVectorBottom]
    have hsum : (∑ r : Fin 3, ‖b (edgeTop K (by omega) r)‖^2) + (∑ r : Fin 3, ‖b (edgeBottom K (by omega) r)‖^2) = ∑ u : Fin 3 ⊕ Fin 3, ‖b (edgeMap K (by omega) u)‖^2 := (by rw [Fintype.sum_sum_type]; rfl)
    rw [hsum]
    have him := Finset.sum_image (f := fun i : SpinIndex K => ‖b i‖^2)
      (s := (Finset.univ : Finset (Fin 3 ⊕ Fin 3))) (g := edgeMap K (by omega))
      (fun u _ v _ h => edgeMap_injective K hK h)
    rw [← him]
    calc _ ≤ ∑ i : SpinIndex K, ‖b i‖^2 := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
         _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hb] ; norm_num
  clear edgeMap_injective
  have edgeTop_injective (K : ℕ) (hK : 2 ≤ K) : Function.Injective (edgeTop K hK) := (by intro r s h ; apply Fin.ext ; exact congrArg (fun i : SpinIndex K => i.val) h)
  have edgeBottom_injective (K : ℕ) (hK : 2 ≤ K) : Function.Injective (edgeBottom K hK) := (by intro r s h ; have he := congrArg Fin.val h ; apply Fin.ext ; simp only [edgeBottom] at he ; have := r.isLt ; have := s.isLt ; omega)
  have edgeTop_ne_bottom (K : ℕ) (hK : 7 ≤ K) (r s : Fin 3) : edgeTop K (by omega) r ≠ edgeBottom K (by omega) s := (by intro h ; have he := congrArg Fin.val h ; simp only [edgeTop, edgeBottom] at he ; have := r.isLt ; have := s.isLt ; omega)
  have scatterBlock_top_bottom (K : ℕ) (hK : 7 ≤ K) (C : Matrix (Fin 3) (Fin 3) ℂ) (r s : Fin 3) : scatterBlock K (by omega) C (edgeTop K (by omega) r) (edgeBottom K (by omega) s) = C r s := (by have ht : ∀ u : Fin 3, edgeTop K (by omega) u = edgeTop K (by omega) r ↔ u=r := (by intro u ; exact (edgeTop_injective K (by omega)).eq_iff) ; have hb : ∀ u : Fin 3, edgeBottom K (by omega) u = edgeBottom K (by omega) s ↔ u=s := (by intro u ; exact (edgeBottom_injective K (by omega)).eq_iff) ; have hz : ∀ u : Fin 3, edgeBottom K (by omega) u ≠ edgeTop K (by omega) r := (by intro u ; exact (edgeTop_ne_bottom K hK r u).symm) ; simp [scatterBlock, Matrix.sum_apply, Matrix.single, ht, hb, hz, ite_and])
  have scatterBlock_bottom_top (K : ℕ) (hK : 7 ≤ K) (C : Matrix (Fin 3) (Fin 3) ℂ) (r s : Fin 3) : scatterBlock K (by omega) C (edgeBottom K (by omega) s) (edgeTop K (by omega) r) = star (C r s) := (by have ht : ∀ u : Fin 3, edgeTop K (by omega) u = edgeTop K (by omega) r ↔ u=r := (by intro u ; exact (edgeTop_injective K (by omega)).eq_iff) ; have hb : ∀ u : Fin 3, edgeBottom K (by omega) u = edgeBottom K (by omega) s ↔ u=s := (by intro u ; exact (edgeBottom_injective K (by omega)).eq_iff) ; have hz : ∀ u : Fin 3, edgeTop K (by omega) u ≠ edgeBottom K (by omega) s := (by intro u ; exact edgeTop_ne_bottom K hK u s) ; simp [scatterBlock, Matrix.sum_apply, Matrix.single, ht, hb, hz, ite_and]); clear edgeTop_ne_bottom edgeBottom_injective edgeTop_injective
  have scatterBlock_support (K : ℕ) (hK : 7 ≤ K) (C : Matrix (Fin 3) (Fin 3) ℂ) (i j : SpinIndex K) (hij : ¬(i.val<3 ∧ K-j.val<3) ∧ ¬(K-i.val<3 ∧ j.val<3)) : scatterBlock K (by omega) C i j = 0 := (by simp only [scatterBlock, Matrix.sum_apply, Matrix.add_apply] ; apply Finset.sum_eq_zero ; intro r hr ; apply Finset.sum_eq_zero ; intro s hs ; have ht : ¬(edgeTop K (by omega) r=i ∧ edgeBottom K (by omega) s=j) := (by rintro ⟨hi,hj⟩ ; have hri := congrArg Fin.val hi ; have hsj := congrArg Fin.val hj ; simp only [edgeTop, edgeBottom] at hri hsj ; have := r.isLt ; have := s.isLt ; have := i.isLt ; have := j.isLt ; omega) ; have hb : ¬(edgeBottom K (by omega) s=i ∧ edgeTop K (by omega) r=j) := (by rintro ⟨hi,hj⟩ ; have hsi := congrArg Fin.val hi ; have hrj := congrArg Fin.val hj ; simp only [edgeTop, edgeBottom] at hsi hrj ; have := r.isLt ; have := s.isLt ; have := i.isLt ; have := j.isLt ; omega) ; simp [Matrix.single, ht,hb])
  have eq_scatterBlock_of_edges (K : ℕ) (hK : 7 ≤ K) (H : SpinMatrix K) (hH : H.IsHermitian) (C : Matrix (Fin 3) (Fin 3) ℂ) (hsupp : ∀ i j, (¬(i.val<3 ∧ K-j.val<3) ∧ ¬(K-i.val<3 ∧ j.val<3)) → H i j=0) (hedge : ∀ r s : Fin 3, H (edgeTop K (by omega) r) (edgeBottom K (by omega) s)=C r s) : H = scatterBlock K (by omega) C := by
    ext i j
    by_cases ht : i.val<3 ∧ K-j.val<3
    · let r : Fin 3 := ⟨i.val,ht.1⟩
      let s : Fin 3 := ⟨K-j.val,ht.2⟩
      have hi : edgeTop K (by omega) r=i := by apply Fin.ext ; rfl
      have hj : edgeBottom K (by omega) s=j := by apply Fin.ext ; dsimp [edgeBottom,s] ; have := j.isLt ; omega
      rw [← hi, ← hj, hedge, scatterBlock_top_bottom K hK]
    · by_cases hb : K-i.val<3 ∧ j.val<3
      · let r : Fin 3 := ⟨j.val,hb.2⟩
        let s : Fin 3 := ⟨K-i.val,hb.1⟩
        have hi : edgeBottom K (by omega) s=i := by apply Fin.ext ; dsimp [edgeBottom,s] ; have := i.isLt ; omega
        have hj : edgeTop K (by omega) r=j := by apply Fin.ext ; rfl
        rw [← hi, ← hj, scatterBlock_bottom_top K hK]
        have he := congrArg (fun M => M (edgeBottom K (by omega) s) (edgeTop K (by omega) r)) hH.eq
        simp only [conjTranspose_apply] at he; rw [hedge] at he; exact he.symm
      · rw [hsupp i j ⟨ht,hb⟩, scatterBlock_support K hK C i j ⟨ht,hb⟩]
  clear scatterBlock_support scatterBlock_bottom_top scatterBlock_top_bottom
  have entryNormSq_smul {ι κ : Type} [Fintype ι] [Fintype κ] (C : Matrix ι κ ℂ) (z : ℂ) : entryNormSq (z • C) = ‖z‖^2*entryNormSq C := (by simp [entryNormSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum])
  have compressionScale_norm (L : ℕ) : ‖compressionScale L‖=c (2*L+1)/(2*L+2) := (by unfold compressionScale ; rw [norm_mul, norm_pow] ; norm_num only [norm_neg, norm_one, one_pow, one_mul, norm_real, Real.norm_eq_abs] ; rw [abs_of_pos (div_pos (c_positive _) (by positivity))])
  have compressionRadius_nonneg (K : ℕ) : 0 ≤ compressionRadius K := (by unfold compressionRadius ; exact div_nonneg (mul_nonneg (le_of_lt (c_positive K)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)); clear c_positive
  have compressionC_normSq_bound (L : ℕ) (hL : 3 ≤ L) (a : SpinVector 2) (ha : ‖a‖=1) : entryNormSq (compressionScale L • compressionM (2*L+1) a) ≤ (compressionRadius (2*L+1))^2 := by
    rw [entryNormSq_smul, compressionScale_norm]
    have hM := compressionM_normSq_bound (2*L+1) (by omega) a ha
    have hscale := mul_le_mul_of_nonneg_left hM (sq_nonneg (c (2*L+1)/(2*L+2)))
    unfold compressionRadius
    have hn : 2*L+1-1=2*L := by omega
    rw [hn]; push_cast at hscale ⊢
    calc _ ≤ (c (2*L+1)/(2*(L:ℝ)+2))^2 * (2*(L:ℝ)+1-1)^2 := hscale
         _ = _ := by ring
  clear compressionScale_norm entryNormSq_smul compressionM_normSq_bound
  have two_score_sub_one (K : ℕ) (a : SpinVector 2) (b : SpinVector K) (ha : ‖a‖=1) (hb : ‖b‖=1) : (star b.ofLp ⬝ᵥ (compression K a ((2:ℂ) • Q K-1) *ᵥ b.ofLp)).re = 2*(star (productVector K a b).ofLp ⬝ᵥ (Q K *ᵥ (productVector K a b).ofLp)).re-1 := by
    have productVector_norm_sq (K : ℕ) (a : SpinVector 2) (b : SpinVector K) : ‖productVector K a b‖^2 = ‖a‖^2*‖b‖^2 := by simp only [EuclideanSpace.norm_sq_eq, productVector, Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]
    rw [← product_quadratic_compression] ; have hn : ‖productVector K a b‖^2=1 := (by rw [productVector_norm_sq,ha,hb] ; norm_num) ; have hdot : (star (productVector K a b).ofLp ⬝ᵥ (productVector K a b).ofLp).re=1 := (by rw [dotProduct_comm] ; change RCLike.re (inner ℂ (productVector K a b) (productVector K a b))=1 ; rw [inner_self_eq_norm_sq,hn]) ; simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, hdot]
  clear product_quadratic_compression
  have radical_first (L : ℕ) : (2*(L:ℂ)+1)*(Real.sqrt 2:ℂ)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹ = (Real.sqrt (2*(2*L+1):ℝ):ℂ) := (by have hsq : (Real.sqrt (2*L+1:ℝ):ℂ)^2=2*(L:ℂ)+1 := (by norm_cast ; exact Real.sq_sqrt (by positivity)) ; have hmul : (Real.sqrt (2*(2*L+1):ℝ):ℂ) = (Real.sqrt 2:ℂ)*(Real.sqrt (2*L+1:ℝ):ℂ) := (by exact_mod_cast (Real.sqrt_mul (show (0:ℝ)≤2 by norm_num) ((2:ℝ)*L+1))) ; rw [hmul,←hsq] ; have hz : (Real.sqrt (2*L+1:ℝ):ℂ) ≠ 0 := (by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<2*L+1))) ; field_simp)
  have radical_second (L : ℕ) (hL : 1 ≤ L) : (2*(L:ℂ)+1)*(L:ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹ = (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ) := (by have hsq : (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)^2=(2*(L:ℂ)+1)*(L:ℂ) := (by have hs := Real.sq_sqrt (show (0:ℝ)≤(2*L+1:ℝ)*(2*L:ℝ)/2 by positivity) ; have hh : (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2))^2=(2*(L:ℝ)+1)*(L:ℝ) := (by nlinarith [hs]) ; exact_mod_cast hh) ; rw [←hsq,pow_two] ; have hz : (Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ) ≠ 0 := (by have hp : (0:ℝ)<L := (by exact_mod_cast (show 0<L by omega)) ; exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<(2*L+1:ℝ)*(2*L:ℝ)/2))) ; field_simp)
  have radical_inverse_square (L : ℕ) : (2*(L:ℂ)+1)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹^2=1 := (by have hsq : (Real.sqrt (2*L+1:ℝ):ℂ)^2=2*(L:ℂ)+1 := (by norm_cast ; exact Real.sq_sqrt (by positivity)) ; rw [←hsq] ; have hz : (Real.sqrt (2*L+1:ℝ):ℂ) ≠ 0 := (by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<2*L+1))) ; field_simp)
  have endpointState_unit (L : ℕ) : ‖endpointState L‖=1 := (by have h0 : (0 : SpinIndex (2*L+1)) ≠ Fin.last (2*L+1) := (by intro h ; have he := congrArg Fin.val h ; simp only [Fin.val_zero, Fin.val_last] at he ; omega) ; have hroot : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num) ; have hn : ‖endpointState L‖^2=1 := (by unfold endpointState ; rw [@norm_add_sq ℂ] ; simp only [PiLp.norm_single, EuclideanSpace.inner_single_left, PiLp.single_apply, if_neg h0, mul_zero, map_zero, add_zero, norm_mul, norm_neg, norm_pow, norm_one, one_pow, one_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] ; field_simp ; nlinarith) ; nlinarith [norm_nonneg (endpointState L)])
  have middle_endpoint_compression (L : ℕ) (hL : 3 ≤ L) : compression (2*L+1) middleState (totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1))))) 0 (Fin.last (2*L+1)) = -(-1:ℂ)^L * ((c (2*L+1)*(2*L)/(2*L+2):ℝ):ℂ) := by
    have compression_middle (K : ℕ) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) (i j : SpinIndex K) : compression K middleState H i j = H (1,i) (1,j) := by simp [compression, middleState, PiLp.single_apply]
    rw [compression_middle] ; change totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1)))) (1,edgeTop (2*L+1) (by omega) 0) (1,edgeBottom (2*L+1) (by omega) 0) = _ ; rw [averaged_sign_edge L hL, levelProjector_two_plus, levelProjector_two_minus, spinWeight_central L _ (Or.inl rfl)] ; norm_num [centralEdgeVector, spinOneRad] ; have hroot : (Real.sqrt 2:ℂ)^2=2 := (by norm_cast ; exact Real.sq_sqrt (by norm_num)) ; have hd : (2:ℂ)*(L:ℂ)+2 ≠ 0 := (by exact_mod_cast (show (2:ℝ)*(L:ℝ)+2 ≠ 0 by positivity)) ; field_simp ; ring_nf ; rw [hroot] ; ring
  have single_bilinear {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (i j : ι) (u v : ℂ) : star (Pi.single i u) ⬝ᵥ (H *ᵥ Pi.single j v) = star u * H i j * v := (by rw [← Pi.single_star, Matrix.mulVec_single] ; simp [dotProduct, Pi.single_apply, mul_assoc, ite_mul])
  have two_single_quadratic {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (i j : ι) (u v : ℂ) : star (Pi.single i u+Pi.single j v) ⬝ᵥ (H *ᵥ (Pi.single i u+Pi.single j v)) = star u*H i i*u + star u*H i j*v + star v*H j i*u + star v*H j j*v := (by simp only [Matrix.mulVec_add, star_add, dotProduct_add, add_dotProduct, single_bilinear] ; ring); clear single_bilinear
  have endpoint_attainment (L : ℕ) (hL : 3 ≤ L) : (star (endpointState L).ofLp ⬝ᵥ (compression (2*L+1) middleState ((2:ℂ) • Q (2*L+1)-1) *ᵥ (endpointState L).ofLp)).re = compressionRadius (2*L+1) := by
    have compression_middle (K : ℕ) (H : Matrix (SpinIndex 2 × SpinIndex K) (SpinIndex 2 × SpinIndex K) ℂ) (i j : SpinIndex K) : compression K middleState H i j = H (1,i) (1,j) := by simp [compression, middleState, PiLp.single_apply]
    rw [Q_sign_average (2*L+1) (by omega)]
    let H := compression (2*L+1) middleState
        (totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1)))))
    have hH : H.IsHermitian := compression_hermitian _ middleState _ (averaged_sign_hermitian _ (by omega))
    have hd0 : H 0 0=0 := by dsimp only [H]; rw [compression_middle, totalRotationAverage_selection _ (by omega)]; norm_num only [Fin.val_one, Fin.val_zero, sub_self, add_zero, zero_sub, dvd_zero, if_true]; exact sign_total_entry_zero _ _ _ _ _ (by norm_num)
    have hd1 : H (Fin.last (2*L+1)) (Fin.last (2*L+1))=0 := (by dsimp only [H]; rw [compression_middle, totalRotationAverage_selection _ (by omega)]; have he : ((1:SpinIndex 2).val:ℤ)+(Fin.last (2*L+1)).val-(1:SpinIndex 2).val-(Fin.last (2*L+1)).val=0 := (by ring); rw [he, if_pos (dvd_zero _)]; exact sign_total_entry_zero _ _ _ _ _ he)
    have h01 : H 0 (Fin.last (2*L+1)) = -(-1:ℂ)^L*(compressionRadius (2*L+1):ℂ) := (by have h := middle_endpoint_compression L hL; have hn : 2*L+1-1=2*L := (by omega); have hr : compressionRadius (2*L+1) = c (2*L+1)*(2*L:ℝ)/(2*L+2) := (by unfold compressionRadius; rw [hn]; push_cast; ring); simpa only [hr] using h)
    have h10 : H (Fin.last (2*L+1)) 0 = -(-1:ℂ)^L*(compressionRadius (2*L+1):ℂ) := (by have h := congrArg (fun M => M (Fin.last (2*L+1)) 0) hH.eq; simp only [conjTranspose_apply,h01,star_mul,star_neg,star_pow,star_one, Complex.star_def,Complex.conj_ofReal] at h; simpa only [mul_comm] using h.symm)
    change (star (endpointState L).ofLp ⬝ᵥ (H *ᵥ (endpointState L).ofLp)).re = _
    have he : (endpointState L).ofLp = Pi.single 0 (Real.sqrt 2:ℂ)⁻¹ + Pi.single (Fin.last (2*L+1)) (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹) := by ext i; simp [endpointState, PiLp.single_apply, Pi.single_apply]
    rw [he, two_single_quadratic,hd0,hd1,h01,h10]
    have hsign : ((-1:ℂ)^L)^2=1 := by rw [←pow_mul,mul_comm L 2,pow_mul] ; norm_num
    have hsign2 : (-1:ℂ)^(L*2)=1 := by simpa only [pow_mul] using hsign
    have hroot : (Real.sqrt 2:ℂ)^2=2 := by norm_cast ; exact Real.sq_sqrt (by norm_num)
    have hz : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
    have hc : star (Real.sqrt 2:ℂ)⁻¹ = (Real.sqrt 2:ℂ)⁻¹ := by simp
    have hcomplex : star (Real.sqrt 2:ℂ)⁻¹ * 0 * (Real.sqrt 2:ℂ)⁻¹ + star (Real.sqrt 2:ℂ)⁻¹ * (-(-1:ℂ)^L*(compressionRadius (2*L+1):ℂ)) * (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹) + star (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹) * (-(-1:ℂ)^L*(compressionRadius (2*L+1):ℂ)) * (Real.sqrt 2:ℂ)⁻¹ + star (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹) * 0 * (-(-1:ℂ)^L*(Real.sqrt 2:ℂ)⁻¹) = (compressionRadius (2*L+1):ℂ) := by simp only [hc,star_neg,star_mul,star_pow,star_one]; field_simp; ring_nf; rw [hsign2,hroot]; ring
    rw [hcomplex]; rfl
  clear two_single_quadratic middle_endpoint_compression sign_total_entry_zero totalRotationAverage_selection
  have compression_edge_block_raw (L : ℕ) (hL : 3 ≤ L) (a : SpinVector 2) (r s : Fin 3) : compression (2*L+1) a (totalRotationAverage (2*L+1) (signOp (total (2*L+1) (Jx 2) (Jx (2*L+1))))) (edgeTop (2*L+1) (by omega) r) (edgeBottom (2*L+1) (by omega) s) = rawCompressionC L a r s := by
    have hrt : (Real.sqrt 2:ℂ)^2=2 := by norm_cast ; exact Real.sq_sqrt (by norm_num)
    fin_cases r <;> fin_cases s
    all_goals
      simp only [compression, averaged_sign_edge L hL,
        levelProjector_two_plus, levelProjector_two_minus,
        Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      norm_num only [spinOneRad, centralEdgeVector, rawCompressionC, stateW, stateZ,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
        Fin.val_zero, Fin.val_succ, Fin.reduceFinMk, Matrix.cons_val_succ',
        ite_true, ite_false, and_true, true_and, and_false, false_and]
      dsimp! only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases]
      simp only [one_mul, zero_add, sub_zero]
      try simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.mk_eq_mk]
      norm_num [Fin.ext_iff]
      try ring_nf
      try rw [hrt]
      try ring
      try rfl
  clear averaged_sign_edge levelProjector_two_minus levelProjector_two_plus
  have rawCompressionC_normalized (L : ℕ) (hL : 3 ≤ L) (a : SpinVector 2) (ha : ‖a‖=1) : rawCompressionC L a = compressionScale L • compressionM (2*L+1) a := by
    have unit_complex_norm (a : SpinVector 2) (ha : ‖a‖=1) : star (a 0)*a 0 + star (a 1)*a 1 + star (a 2)*a 2 = 1 := by have h := spinOne_unit_norm_sq a ha ; simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_add] ; exact_mod_cast h
    have hn := unit_complex_norm a ha
    have hy : star (a 1)*a 1=(stateY a:ℂ) := by simp [stateY, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hw := spinWeight_central L (centralPlus L) (Or.inl rfl)
    have hf := radical_first L
    have hs := radical_second L (by omega)
    have hi := radical_inverse_square L
    have hd : (2:ℂ)*(L:ℂ)+2 ≠ 0 := by exact_mod_cast (show (2:ℝ)*(L:ℝ)+2 ≠ 0 by positivity)
    have hweight : spinWeight (2*L+1) (centralPlus L) = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*(2*(L:ℂ)+1) := by rw [hw]; push_cast; ring
    have hw1 : spinWeight (2*L+1) (centralPlus L)*(Real.sqrt 2:ℂ)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹ = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*(Real.sqrt (2*(2*L+1):ℝ):ℂ) := by rw [hweight]; calc _ = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*((2*(L:ℂ)+1)*(Real.sqrt 2:ℂ)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹) := by ring
      _ = _ := by rw [hf]
    have hw2 : spinWeight (2*L+1) (centralPlus L)*((L:ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹) = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ) := by rw [hweight]; calc _ = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*((2*(L:ℂ)+1)*(L:ℂ)*(Real.sqrt ((2*L+1:ℝ)*(2*L:ℝ)/2):ℂ)⁻¹) := by ring
      _ = _ := by rw [hs]
    have hw3 : spinWeight (2*L+1) (centralPlus L)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹^2 = ((c (2*L+1)/(2*L+2):ℝ):ℂ) := by rw [hweight]; calc _ = ((c (2*L+1)/(2*L+2):ℝ):ℂ)*((2*(L:ℂ)+1)*(Real.sqrt (2*L+1:ℝ):ℂ)⁻¹^2) := by ring
      _ = _ := by rw [hi,mul_one]
    have hrad : Real.sqrt ((2*(L:ℝ)+1)*(2*(L:ℝ)+1-1)/2)=Real.sqrt ((2*(L:ℝ)+1)*(2*(L:ℝ))/2) := by congr 1; ring
    ext r s
    fin_cases r <;> fin_cases s
    all_goals simp only [rawCompressionC, compressionScale, compressionM, Matrix.smul_apply,
      smul_eq_mul, Matrix.of_apply, Matrix.cons_val_succ', Matrix.cons_val_zero']
    all_goals try rw [hw1]
    all_goals try rw [hw2]
    all_goals try simp only [neg_mul,hw3]
    all_goals push_cast
    all_goals try rw [hrad]
    all_goals try rw [hweight]
    all_goals push_cast
    all_goals try rw [← hy]
    all_goals try field_simp [hd]
    all_goals try ring
    all_goals
      calc _ = (c (1+L*2):ℂ)*(star (a 0)*a 0+star (a 1)*a 1+star (a 2)*a 2) - (c (1+L*2):ℂ)*star (a 1)*a 1*(1+2*(L:ℂ)) := by ring
           _ = _ := by rw [hn]; ring
  clear radical_inverse_square radical_second radical_first spinWeight_central spinOne_unit_norm_sq
  have full_compression_identity (L : ℕ) (hL : 3 ≤ L) (a : SpinVector 2) (ha : ‖a‖=1) : compression (2*L+1) a ((2:ℂ) • Q (2*L+1)-1) = scatterBlock (2*L+1) (by omega) (compressionScale L • compressionM (2*L+1) a) := by
    rw [Q_sign_average (2*L+1) (by omega)]
    refine eq_scatterBlock_of_edges (2*L+1) (by omega) _
      (compression_hermitian _ a _ (averaged_sign_hermitian _ (by omega)))
      (compressionScale L • compressionM (2*L+1) a) ?_ ?_
    · intro i j hij
      exact compression_sign_support (2*L+1) (by omega) a i j hij
    · intro r s
      rw [compression_edge_block_raw L hL, rawCompressionC_normalized L hL a ha]
  clear rawCompressionC_normalized compression_edge_block_raw eq_scatterBlock_of_edges compression_sign_support compression_hermitian averaged_sign_hermitian Q_sign_average
  have product_score_upper (L : ℕ) (hL : 3 ≤ L) (a : SpinVector 2) (b : SpinVector (2*L+1)) (ha : ‖a‖=1) (hb : ‖b‖=1) : (star (productVector (2*L+1) a b).ofLp ⬝ᵥ (Q (2*L+1) *ᵥ (productVector (2*L+1) a b).ofLp)).re ≤ 1/2*(1+compressionRadius (2*L+1)) := (by have hblock := block_quadratic_bound (compressionScale L • compressionM (2*L+1) a) (edgeVectorTop (2*L+1) (by omega) b) (edgeVectorBottom (2*L+1) (by omega) b) (compressionRadius (2*L+1)) (compressionRadius_nonneg _) (compressionC_normSq_bound L hL a ha) (edgeVector_norm_sq _ (by omega) b hb) ; rw [← scatterBlock_quadratic] at hblock ; rw [← full_compression_identity L hL a ha, two_score_sub_one _ a b ha hb] at hblock ; linarith); clear full_compression_identity compressionC_normSq_bound compressionRadius_nonneg edgeVector_norm_sq scatterBlock_quadratic block_quadratic_bound
  have middleState_unit : ‖middleState‖ = 1 := (by simp [middleState])
  intro K hOdd hK
  obtain ⟨L,hL⟩ := hOdd
  have hk : K=2*L+1 := (by omega)
  subst K
  have hL3 : 3 ≤ L := (by omega)
  change IsGreatest (scores (2*L+1)) (1/2*(1+compressionRadius (2*L+1)))
  constructor
  · refine ⟨middleState,endpointState L,middleState_unit,endpointState_unit L,?_⟩
    have h := two_score_sub_one (2*L+1) middleState (endpointState L)
      middleState_unit (endpointState_unit L)
    rw [endpoint_attainment L hL3] at h; linarith
  · intro t ht
    obtain ⟨a,b,ha,hb,rfl⟩ := ht
    exact product_score_upper L hL3 a b ha hb
end D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
