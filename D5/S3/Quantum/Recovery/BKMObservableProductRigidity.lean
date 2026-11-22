/- GID: D5/S3/Quantum/Recovery/BKMObservableProductRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMObservableProductRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Grouped modular observability and connected product rigidity for the actual BKM gap. -/

import D5.S3.Quantum.Recovery.BKMObservableRigidity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Modular observability and product rigidity for the actual BKM gap -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open D5.S3.Quantum.Recovery.BKMObservableRigidity
  (modular weightedVec weightedLift weightedLift_compression bkmGap_rigidity mpow_add mpow_zero)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceLeft partialTraceLeft_kronecker trace_partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Quantum.Divergence.ResolventFunctionalRigidity (cfc_vector_expansion)

namespace D5.S3.Quantum.Recovery.BKMObservableProductRigidity

universe u
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]

/-- All entries of a given modular ratio in a diagonalizing basis. -/
def ratioPiece (s : n → ℝ) (v : ℝ) (K : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => if s i = v * s j then K i j else 0

/-- The complete ratio component of an observable, in the original basis. -/
def modularPiece {S : Matrix n n ℂ} (hS : S.IsHermitian) (v : ℝ) (K : Matrix n n ℂ) :
    Matrix n n ℂ :=
  let U : Matrix n n ℂ := hS.eigenvectorUnitary
  U * ratioPiece hS.eigenvalues v (Uᴴ * K * U) * Uᴴ

private def ratios (s : n → ℝ) : Finset ℝ :=
  Finset.univ.image fun ij : n × n => s ij.1 / s ij.2

omit [Fintype n] [DecidableEq n] in
private theorem ratioPiece_apply (s : n → ℝ) (v : ℝ) (K : Matrix n n ℂ) (i j : n) :
    ratioPiece s v K i j = if s i = v * s j then K i j else 0 := rfl

omit [DecidableEq n] in
private theorem ratioPiece_eq_zero {s : n → ℝ} (hs : ∀ i, 0 < s i) {v : ℝ}
    (hv : v ∉ ratios s) (K : Matrix n n ℂ) : ratioPiece s v K = 0 := by
  ext i j
  have h : s i ≠ v * s j := fun he =>
    hv (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, (div_eq_iff (hs j).ne').mpr he⟩)
  simp [ratioPiece_apply, h]

omit [DecidableEq n] in
private theorem sum_ratioPiece {s : n → ℝ} (hs : ∀ i, 0 < s i) (K : Matrix n n ℂ) :
    ∑ v ∈ ratios s, ratioPiece s v K = K := by
  ext i j
  simp only [Matrix.sum_apply, ratioPiece_apply, ← div_eq_iff (hs j).ne']
  rw [Finset.sum_eq_single (s i / s j)]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · intro h
    exact (h (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)).elim

private theorem sum_modularPiece {S : Matrix n n ℂ} (hS : S.PosDef) (K : Matrix n n ℂ) :
    ∑ v ∈ ratios hS.isHermitian.eigenvalues, modularPiece hS.isHermitian v K = K := by
  let U := hS.isHermitian.eigenvectorUnitary
  simp only [modularPiece, ← Matrix.sum_mul, ← Matrix.mul_sum, sum_ratioPiece hS.eigenvalues_pos]
  change U.val * (U.valᴴ * K * U.val) * U.valᴴ = K
  have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  calc
    _ = (U.val * U.valᴴ) * K * (U.val * U.valᴴ) := by simp only [Matrix.mul_assoc]
    _ = K := by rw [hU, Matrix.one_mul, Matrix.mul_one]

private theorem mpow_half_inverse {X : Matrix n n ℂ} (hX : X.PosDef) :
    mpow X (1 / 2) * mpow X (-(1 / 2)) = 1 ∧
      mpow X (-(1 / 2)) * mpow X (1 / 2) = 1 := by
  constructor
  · rw [mpow_add hX, add_neg_cancel, mpow_zero hX]
  · rw [mpow_add hX, neg_add_cancel, mpow_zero hX]

private theorem weighted_eigen_iff {X : Matrix n n ℂ} (hX : X.PosDef)
    (L : Matrix n n ℂ) (v : ℝ) :
    modular X *ᵥ weightedVec X L = (v : ℂ) • weightedVec X L ↔
      X * L = (v : ℂ) • (L * X) := by
  let H := mpow X (1 / 2)
  let J := mpow X (-(1 / 2))
  have hHJ : H * J = 1 := (mpow_half_inverse hX).1
  have hHX : H * X = X * H := by
    simpa only [H, mpow, cfc_id ℝ X hX.isHermitian.isSelfAdjoint] using
      (cfc_commute_cfc (fun t : ℝ => t ^ (1 / 2 : ℝ)) (id : ℝ → ℝ) X).eq
  have hdet := (Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit
  change ((X⁻¹)ᵀ ⊗ₖ X) *ᵥ vec (L * H) = (v : ℂ) • vec (L * H) ↔ _
  rw [Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, ← Matrix.vec_smul, Matrix.vec_inj]
  constructor
  · intro h
    have h' := congrArg (fun T => T * X) h
    simp only [Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul X hdet,
      Matrix.mul_one, hHX] at h'
    have h'' := congrArg (fun T => T * J) h'
    simpa only [Matrix.smul_mul, Matrix.mul_assoc, hHJ, Matrix.mul_one] using h''
  · intro h
    calc
      X * (L * H) * X⁻¹ = (X * L) * H * X⁻¹ := by rw [Matrix.mul_assoc X L]
      _ = (v : ℂ) • (L * H) := by
        rw [h, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc L X H, ← hHX,
          Matrix.mul_assoc, Matrix.mul_assoc H X X⁻¹, Matrix.mul_nonsing_inv X hdet,
          Matrix.mul_one]

private theorem cfc_eigen {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (z : n → ℂ) (v : ℝ) (hz : P *ᵥ z = (v : ℂ) • z) (f : ℝ → ℝ) :
    cfc f P *ᵥ z = (f v : ℂ) • z := by
  let U := hP.eigenvectorUnitary
  let D := Matrix.diagonal fun i => (hP.eigenvalues i : ℂ)
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  have hPdiag : P = U.val * D * U.valᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def, U, D] using hP.spectral_theorem
  let y := U.valᴴ *ᵥ z
  have hy : D *ᵥ y = (v : ℂ) • y := by
    have h := congrArg (fun w => U.valᴴ *ᵥ w) hz
    change U.valᴴ *ᵥ (P *ᵥ z) = _ at h
    rw [hPdiag, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    have hD : U.valᴴ * (U.val * D * U.valᴴ) = D * U.valᴴ := by
      calc
        _ = ((U.valᴴ * U.val) * D) * U.valᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul]
    rw [hD, ← Matrix.mulVec_mulVec] at h
    exact h
  have hterm (j : n) : (f (hP.eigenvalues j) : ℂ) * y j = (f v : ℂ) * y j := by
    by_cases hj : y j = 0
    · simp [hj]
    · have he : (hP.eigenvalues j : ℂ) * y j = (v : ℂ) * y j := by
        simpa only [D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using congrFun hy j
      rw [show hP.eigenvalues j = v by exact_mod_cast mul_right_cancel₀ hj he]
  have hconst := cfc_vector_expansion P hP (fun _ => f v) z
  have heq : cfc f P *ᵥ z = cfc (fun _ : ℝ => f v) P *ᵥ z := by
    funext i
    rw [cfc_vector_expansion P hP f, hconst]
    apply Finset.sum_congr rfl
    intro j _
    change (f (hP.eigenvalues j) : ℂ) * U.val i j * y j = (f v : ℂ) * U.val i j * y j
    rw [mul_right_comm, hterm, mul_right_comm]
  rw [heq, cfc_const (R := ℝ) (f v) P hP.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  change ((f v : ℂ) • (1 : Matrix n n ℂ)) *ᵥ z = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem cfc_modularPiece {S : Matrix n n ℂ} (hS : S.PosDef) (K : Matrix n n ℂ)
    {v w : ℝ} (f : ℝ → ℝ) (hf : ∀ i j, hS.isHermitian.eigenvalues i = v *
      hS.isHermitian.eigenvalues j → f (hS.isHermitian.eigenvalues i) =
        w * f (hS.isHermitian.eigenvalues j)) :
    cfc f S * modularPiece hS.isHermitian v K =
      (w : ℂ) • (modularPiece hS.isHermitian v K * cfc f S) := by
  let U := hS.isHermitian.eigenvectorUnitary
  let X := ratioPiece hS.isHermitian.eigenvalues v (U.valᴴ * K * U.val)
  let D := diagonal fun i => (f (hS.isHermitian.eigenvalues i) : ℂ)
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  have hD : cfc f S = U.val * D * U.valᴴ := by
    rw [hS.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  have hDX : D * X = (w : ℂ) • (X * D) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    change (f (hS.isHermitian.eigenvalues i) : ℂ) * X i j =
      (w : ℂ) * (X i j * (f (hS.isHermitian.eigenvalues j) : ℂ))
    dsimp only [X, ratioPiece_apply]
    split
    · rename_i h
      rw [hf _ _ h, Complex.ofReal_mul]
      ring
    · simp
  change cfc f S * (U.val * X * U.valᴴ) =
    (w : ℂ) • ((U.val * X * U.valᴴ) * cfc f S)
  rw [hD]
  have sandwich (L T : Matrix n n ℂ) :
      (U.val * L * U.valᴴ) * (U.val * T * U.valᴴ) = U.val * (L * T) * U.valᴴ := by
    calc
      _ = U.val * (L * ((U.valᴴ * U.val) * (T * U.valᴴ))) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [sandwich, sandwich, hDX, Matrix.mul_smul, Matrix.smul_mul]

private theorem lift_half_inverse (S : Matrix R R ℂ) (hS : S.PosDef) :
    lift (ι := E) (mpow S (1 / 2)) * lift (mpow S (-(1 / 2))) = 1 ∧
      lift (ι := E) (mpow S (-(1 / 2))) * lift (mpow S (1 / 2)) = 1 := by
  obtain ⟨hHJ, hJH⟩ := mpow_half_inverse hS
  constructor
  · simp only [lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hHJ, Matrix.one_kronecker_one]
  · simp only [lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hJH, Matrix.one_kronecker_one]

/-- Joint density normalized on both sides by the inverse square root of its actual marginal. -/
def relativeDensity (A : Matrix (R × E) (R × E) ℂ) : Matrix (R × E) (R × E) ℂ :=
  let J := lift (mpow (partialTraceRight A) (-(1 / 2)))
  J * A * J

private theorem restore_density (A : Matrix (R × E) (R × E) ℂ)
    (hS : (partialTraceRight A).PosDef) :
    let H := lift (mpow (partialTraceRight A) (1 / 2))
    H * relativeDensity A * H = A := by
  intro H
  let J := lift (ι := E) (mpow (partialTraceRight A) (-(1 / 2)))
  obtain ⟨hHJ, hJH⟩ := lift_half_inverse (E := E) _ hS
  change H * J = 1 at hHJ
  change J * H = 1 at hJH
  change H * (J * A * J) * H = A
  calc
    _ = (H * J) * A * (J * H) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hHJ, hJH, Matrix.one_mul, Matrix.mul_one]

private theorem commute_relativeDensity_iff (A : Matrix (R × E) (R × E) ℂ)
    (hS : (partialTraceRight A).PosDef) (K : Matrix R R ℂ) (v : ℝ) :
    Commute (relativeDensity A) (lift (modularPiece hS.isHermitian v K)) ↔
      A * lift (modularPiece hS.isHermitian v K) =
        (v : ℂ) • (lift (modularPiece hS.isHermitian v K) * A) := by
  let S := partialTraceRight A
  let L := lift (ι := E) (modularPiece hS.isHermitian v K)
  let H := lift (ι := E) (mpow S (1 / 2))
  let J := lift (ι := E) (mpow S (-(1 / 2)))
  let B := relativeDensity A
  change Commute B L ↔ A * L = (v : ℂ) • (L * A)
  by_cases hv : v ∈ ratios hS.isHermitian.eigenvalues
  · obtain ⟨ij, _, he⟩ := Finset.mem_image.mp hv
    have hvpos : 0 < v := he ▸ div_pos (hS.eigenvalues_pos _) (hS.eigenvalues_pos _)
    let c : ℂ := Real.sqrt v
    have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast (Real.sqrt_pos.2 hvpos).ne'
    have hcc : c * c = (v : ℂ) := by
      dsimp [c]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hvpos.le]
    have hHL : H * L = c • (L * H) := by
      have h := cfc_modularPiece hS K (fun t => t ^ (1 / 2 : ℝ)) (v := v) (w := Real.sqrt v)
        (fun i j hi => by
          rw [hi, Real.mul_rpow hvpos.le (hS.eigenvalues_pos j).le, Real.sqrt_eq_rpow])
      have h' := congrArg (lift (ι := E)) h
      have hl (T : Matrix R R ℂ) : lift (ι := E) (c • T) = c • lift T := by
        simp only [lift, Matrix.smul_kronecker]
      rw [hl] at h'
      simpa only [H, L, mpow, lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one] using h'
    have hA : H * B * H = A := restore_density A hS
    have hleft : A * L = c • (H * (B * L) * H) := by
      rw [← hA, Matrix.mul_assoc (H * B) H L, hHL, Matrix.mul_smul]
      simp only [Matrix.mul_assoc]
    have hright : (v : ℂ) • (L * A) = c • (H * (L * B) * H) := by
      calc
        _ = c • ((c • (L * H)) * B * H) := by
          rw [← hcc, ← smul_smul, ← hA, Matrix.smul_mul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hHL, Matrix.mul_assoc H L]
    rw [hleft, hright]
    constructor
    · intro h
      rw [h.eq]
    · intro h
      have h' := (smul_right_injective (M := Matrix (R × E) (R × E) ℂ) hc) h
      have h'' := congrArg (fun T => J * T * J) h'
      obtain ⟨hHJ, hJH⟩ := lift_half_inverse (E := E) S hS
      change H * J = 1 at hHJ
      change J * H = 1 at hJH
      change B * L = L * B
      have cancel (T : Matrix (R × E) (R × E) ℂ) : J * (H * T * H) * J = T := by
        calc
          _ = (J * H) * T * (H * J) := by simp only [Matrix.mul_assoc]
          _ = T := by rw [hJH, hHJ, Matrix.one_mul, Matrix.mul_one]
      simpa only [cancel] using h''
  · have hL : L = 0 := by
      simp [L, modularPiece, ratioPiece_eq_zero hS.eigenvalues_pos hv, lift]
    simp [hL, Commute.zero_right]

private theorem weightedVec_sum {ι : Type*} (X : Matrix n n ℂ) (s : Finset ι)
    (K : ι → Matrix n n ℂ) :
    weightedVec X (∑ v ∈ s, K v) = ∑ v ∈ s, weightedVec X (K v) := by
  simp only [weightedVec, Matrix.sum_mul, Matrix.vec_sum]

/-- The actual BKM gap vanishes precisely when the relative density commutes with every
complete retained modular ratio group. The groups include all coincident ratios. -/
theorem bkmGap_eq_zero_iff_commute_ratioPieces [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (K : Matrix R R ℂ) (hK : K.IsHermitian) :
    bkmGap A K = 0 ↔ ∀ v : ℝ, Commute (relativeDensity A)
      (lift (modularPiece (partialTraceRight_posDef A hA).isHermitian v K)) := by
  classical
  let S := partialTraceRight A
  have hS : S.PosDef := partialTraceRight_posDef A hA
  let V := weightedLift A hA
  let M := modular A
  let N := modular S
  let b := weightedVec S K
  let s := ratios hS.isHermitian.eigenvalues
  let L := fun v => modularPiece hS.isHermitian v K
  let z := fun v => weightedVec S (L v)
  have hM : M.IsHermitian := (hA.inv.transpose.kronecker hA).isHermitian
  have hN : N.IsHermitian := (hS.inv.transpose.kronecker hS).isHermitian
  have hlift (T : Matrix R R ℂ) : V *ᵥ weightedVec S T = weightedVec A (lift T) :=
    (weightedLift_compression A hA).1 T
  have hze (v : ℝ) : N *ᵥ z v = (v : ℂ) • z v := by
    apply (weighted_eigen_iff hS _ _).mpr
    simpa only [cfc_id ℝ S hS.isHermitian.isSelfAdjoint] using
      cfc_modularPiece hS K (id : ℝ → ℝ) (v := v) (w := v) (fun _ _ h => h)
  have hb : ∑ v ∈ s, z v = b := by
    rw [← weightedVec_sum, show ∑ v ∈ s, L v = K from sum_modularPiece hS K]
  have hcalc (f : ℝ → ℝ) : cfc f N *ᵥ b = ∑ v ∈ s, (f v : ℂ) • z v := by
    rw [← hb, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun v _ => cfc_eigen hN _ _ (hze v) f
  have hsum (v : ℝ) (w : ℝ) :
      (∑ t ∈ s, ((if t = v then w else 0 : ℝ) : ℂ) • z t) = (w : ℂ) • z v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro t _ ht
      simp [ht]
    · intro hv
      have hz : z v = 0 := by
        simp [z, L, modularPiece, ratioPiece_eq_zero hS.eigenvalues_pos hv, weightedVec]
      simp [hz]
  change bkmGap A K = 0 ↔ ∀ v, Commute (relativeDensity A) (lift (L v))
  have hmode (v : ℝ) : Commute (relativeDensity A) (lift (L v)) ↔
      M *ᵥ (V *ᵥ z v) = (v : ℂ) • (V *ᵥ z v) := by
    change Commute (relativeDensity A) (lift (L v)) ↔
      modular A *ᵥ (V *ᵥ weightedVec S (L v)) = (v : ℂ) • (V *ᵥ weightedVec S (L v))
    rw [hlift, weighted_eigen_iff hA]
    exact commute_relativeDensity_iff A hS K v
  simp_rw [hmode]
  rw [(bkmGap_rigidity A hA K hK).2.2]
  change (∀ f : ℝ → ℝ, cfc f M *ᵥ (V *ᵥ b) = V *ᵥ (cfc f N *ᵥ b)) ↔ _
  constructor
  · intro h v
    let d : ℝ → ℝ := fun t => if t = v then 1 else 0
    have hd : cfc d M *ᵥ (V *ᵥ b) = V *ᵥ z v := by
      rw [h, hcalc]
      simp only [d, hsum, Complex.ofReal_one, one_smul]
    have he : cfc (fun t => t * d t) M *ᵥ (V *ᵥ b) = (v : ℂ) • (V *ᵥ z v) := by
      have hpoint (t : ℝ) : t * d t = if t = v then v else 0 := by
        by_cases ht : t = v <;> simp [d, ht]
      rw [h, hcalc]
      simp only [hpoint, hsum, Matrix.mulVec_smul]
    have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ M) :=
      M.finite_real_spectrum.continuousOn f
    have hdc : cfc (fun t => t * d t) M = M * cfc d M := by
      change cfc (fun t => id t * d t) M = _
      rw [cfc_mul id d M (hcont id) (hcont d), cfc_id ℝ M hM.isSelfAdjoint]
    calc
      M *ᵥ (V *ᵥ z v) = cfc (fun t => t * d t) M *ᵥ (V *ᵥ b) := by
        rw [← hd, Matrix.mulVec_mulVec, hdc]
      _ = _ := he
  · intro h f
    calc
      cfc f M *ᵥ (V *ᵥ b) = ∑ v ∈ s, (f v : ℂ) • (V *ᵥ z v) := by
        rw [← hb, Matrix.mulVec_sum, Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun v _ => cfc_eigen hM _ _ (h v) f
      _ = V *ᵥ (cfc f N *ᵥ b) := by rw [hcalc, Matrix.mulVec_sum]; simp only [Matrix.mulVec_smul]

#print axioms bkmGap_eq_zero_iff_commute_ratioPieces


/-- The graph of nonzero off-diagonal entries of a Hermitian matrix. -/
def observableGraph (K : Matrix n n ℂ) (hK : K.IsHermitian) : SimpleGraph n where
  Adj i j := i ≠ j ∧ K i j ≠ 0
  symm := by
    constructor
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    intro hz
    apply h.2
    have he := congrArg (fun (T : Matrix n n ℂ) => T j i) hK.eq
    simpa [Matrix.conjTranspose_apply, hz] using he
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq n] in
private theorem ratioPiece_mul_piece {s : n → ℝ}
    (X K : Matrix n n ℂ) (q v : ℝ) :
    ratioPiece s (q * v) (X * ratioPiece s v K) =
      ratioPiece s q X * ratioPiece s v K := by
  ext i j
  simp only [ratioPiece_apply, Matrix.mul_apply]
  rw [Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hv : s k = v * s j
  · have he : s i = (q * v) * s j ↔ s i = q * s k := by rw [hv, mul_assoc]
    simp [hv, he, ite_mul]
  · change (if s i = (q * v) * s j then X i k * ratioPiece s v K k j else 0) =
      (if s i = q * s k then X i k else 0) * ratioPiece s v K k j
    simp [ratioPiece_apply, hv]

omit [DecidableEq n] in
private theorem ratioPiece_piece_mul {s : n → ℝ} (hs : ∀ i, 0 < s i)
    (X K : Matrix n n ℂ) (q v : ℝ) :
    ratioPiece s (q * v) (ratioPiece s v K * X) =
      ratioPiece s v K * ratioPiece s q X := by
  ext i j
  simp only [ratioPiece_apply, Matrix.mul_apply]
  rw [Finset.ite_sum_zero]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hv : s i = v * s k
  · have hv0 : v ≠ 0 := by intro hz; simp [hz, (hs i).ne'] at hv
    have he : s i = (q * v) * s j ↔ s k = q * s j := by
      rw [hv, mul_comm q v, mul_assoc, mul_right_inj' hv0]
    simp only [if_pos hv, he, mul_ite, mul_zero]
  · change (if s i = (q * v) * s j then ratioPiece s v K i k * X k j else 0) =
      ratioPiece s v K i k * (if s k = q * s j then X k j else 0)
    simp [ratioPiece_apply, hv]

omit [Fintype n] [DecidableEq n] in
private theorem ratioPiece_adjoint (s : n → ℝ) (K : Matrix n n ℂ) (hK : K.IsHermitian)
    {v : ℝ} (hv : v ≠ 0) : (ratioPiece s v K)ᴴ = ratioPiece s v⁻¹ K := by
  ext i j
  have he : s j = v * s i ↔ s i = v⁻¹ * s j := by
    constructor
    · intro h
      rw [h, inv_mul_cancel_left₀ hv]
    · intro h
      rw [h, mul_inv_cancel_left₀ hv]
  have hj := congrArg (fun (T : Matrix n n ℂ) => T i j) hK.eq
  simp only [Matrix.conjTranspose_apply] at hj
  by_cases h : s i = v⁻¹ * s j
  · simp only [Matrix.conjTranspose_apply, ratioPiece_apply, if_pos h, if_pos (he.mpr h), hj]
  · simp only [Matrix.conjTranspose_apply, ratioPiece_apply, if_neg h, if_neg (he.not.mpr h), star_zero]

private theorem diagonal_scalar_of_connected {K : Matrix n n ℂ} {hK : K.IsHermitian}
    (hc : (observableGraph K hK).Connected) {D : Matrix n n ℂ}
    (hD : ∀ i j, i ≠ j → D i j = 0) (h : Commute D K) (o : n) :
    D = D o o • (1 : Matrix n n ℂ) := by
  have hd : D = Matrix.diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hD i j hij, Matrix.diagonal_apply_ne _ hij]
  have hedge {i j : n} (ha : (observableGraph K hK).Adj i j) : D i i = D j j := by
    have he := h.eq
    rw [hd] at he
    have hij := congrArg (fun (T : Matrix n n ℂ) => T i j) he
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
    rw [mul_comm (K i j)] at hij
    exact mul_right_cancel₀ ha.2 hij
  have heq (i : n) : D i i = D o o := (hc i o).elim fun w => by
    induction w with
    | nil => rfl
    | cons ha _ ih => exact (hedge ha).trans ih
  calc
    D = Matrix.diagonal (fun i => D i i) := hd
    _ = _ := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [heq]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem scalar_of_commute_pieces {s : n → ℝ} (hs : ∀ i, 0 < s i)
    (hsimple : Function.Injective s) {K : Matrix n n ℂ} {hK : K.IsHermitian}
    (hc : (observableGraph K hK).Connected) (X : Matrix n n ℂ)
    (hX : ∀ v, Commute X (ratioPiece s v K)) (o : n) :
    X = X o o • (1 : Matrix n n ℂ) := by
  have hsum (D : Matrix n n ℂ) (hd : ∀ v, Commute D (ratioPiece s v K)) : Commute D K := by
    change D * K = K * D
    rw [← sum_ratioPiece hs K, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl (fun v _ => (hd v).eq)
  have hpiece (q v : ℝ) : Commute (ratioPiece s q X) (ratioPiece s v K) :=
    show _ = _ from
      (ratioPiece_mul_piece X K q v).symm.trans <|
        (congrArg (ratioPiece s (q * v)) (hX v).eq).trans (ratioPiece_piece_mul hs X K q v)
  have hvanish (q : ℝ) (hq : 0 < q) (hneq : q ≠ 1) : ratioPiece s q X = 0 := by
    let Y := ratioPiece s q X
    have hdiag (i j : n) (hij : i ≠ j) : (Yᴴ * Y) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hi : s k = q * s i
      · have hj : s k ≠ q * s j := fun he =>
          hij (hsimple (mul_left_cancel₀ hq.ne' (hi.symm.trans he)))
        simp [Y, Matrix.conjTranspose_apply, ratioPiece_apply, hj]
      · simp [Y, Matrix.conjTranspose_apply, ratioPiece_apply, hi]
    have hadj (v : ℝ) : Commute Yᴴ (ratioPiece s v K) := by
      by_cases hv : v = 0
      · subst v
        have hz : ratioPiece s 0 K = 0 := by
          ext i j
          simp [ratioPiece_apply, (hs i).ne']
        rw [hz]
        exact Commute.zero_right _
      · have hh := (hpiece q v⁻¹).star_star
        rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
          ratioPiece_adjoint s K hK (inv_ne_zero hv), inv_inv] at hh
        exact hh
    have hscalar := diagonal_scalar_of_connected hc hdiag
      (hsum (Yᴴ * Y) (fun v => (hadj v).mul_left (hpiece q v))) o
    haveI : Nonempty n := hc.nonempty
    have hcol : ∃ j, ∀ i, Y i j = 0 := by
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · obtain ⟨j, hj⟩ := Finite.exists_min s
        refine ⟨j, fun i => ?_⟩
        have hqj : q * s j < s j := by simpa using mul_lt_mul_of_pos_right hlt (hs j)
        have hqi := hqj.trans_le (hj i)
        simp [Y, ratioPiece_apply, hqi.ne']
      · obtain ⟨j, hj⟩ := Finite.exists_max s
        refine ⟨j, fun i => ?_⟩
        have hqi : s i < q * s j := (hj i).trans_lt (by
          simpa using mul_lt_mul_of_pos_right hgt (hs j))
        simp [Y, ratioPiece_apply, hqi.ne]
    obtain ⟨j, hj⟩ := hcol
    have hz : (Yᴴ * Y) j j = 0 := by simp [Matrix.mul_apply, hj]
    have coeff : (Yᴴ * Y) o o = 0 := by
      have he := congrArg (fun (T : Matrix n n ℂ) => T j j) hscalar
      simpa [hz] using he.symm
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hscalar, coeff, zero_smul]
  have hdiag (i j : n) (hij : i ≠ j) : X i j = 0 := by
    have hq : 0 < s i / s j := div_pos (hs i) (hs j)
    have hneq : s i / s j ≠ 1 := by
      intro he
      exact hij (hsimple (by simpa using (div_eq_iff (hs j).ne').mp he))
    have he := congrArg (fun (T : Matrix n n ℂ) => T i j) (hvanish _ hq hneq)
    simpa [ratioPiece_apply, div_mul_cancel₀ _ (hs j).ne'] using he
  exact diagonal_scalar_of_connected hc hdiag (hsum X hX) o

omit [DecidableEq R] in
private theorem commute_slice {B : Matrix (R × E) (R × E) ℂ} {K : Matrix R R ℂ}
    (h : Commute B (lift K)) (e f : E) :
    Commute (Matrix.of fun i j => B (i, e) (j, f)) K := by
  change (Matrix.of fun i j => B (i, e) (j, f)) * K =
    K * (Matrix.of fun i j => B (i, e) (j, f))
  ext i j
  have he := congrArg (fun (T : Matrix (R × E) (R × E) ℂ) => T (i, e) (j, f)) h.eq
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, lift, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, ite_mul, mul_assoc] using he

/-- For a faithful normalized joint state, a simple retained spectrum and a connected
observable graph make zero BKM gap equivalent to the product of its actual marginals. -/
theorem bkmGap_eq_zero_iff_eq_marginals_kronecker [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (K : Matrix R R ℂ) (hK : K.IsHermitian)
    (htrace : A.trace = 1) :
    let S := partialTraceRight A
    let hS := partialTraceRight_posDef A hA
    let U : Matrix R R ℂ := hS.isHermitian.eigenvectorUnitary
    let K₀ := Uᴴ * K * U
    let hK₀ : K₀.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U hK
    Function.Injective hS.isHermitian.eigenvalues →
      (observableGraph K₀ hK₀).Connected →
        (bkmGap A K = 0 ↔ A = S ⊗ₖ partialTraceLeft A) := by
  classical
  intro S hS U K₀ hK₀ hsimple hc
  change S.PosDef at hS
  let B := relativeDensity A
  let W := lift (ι := E) U
  let W' := lift (ι := E) Uᴴ
  let B₀ := W' * B * W
  let H := lift (ι := E) (mpow S (1 / 2))
  let J := lift (ι := E) (mpow S (-(1 / 2)))
  have hWW' : W * W' = 1 := by
    simp only [W, W', lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      show U * Uᴴ = 1 from Unitary.coe_mul_star_self _, Matrix.one_kronecker_one]
  have hW'W : W' * W = 1 := by
    simp only [W, W', lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      show Uᴴ * U = 1 from Unitary.coe_star_mul_self _, Matrix.one_kronecker_one]
  have hHH : mpow S (1 / 2) * mpow S (1 / 2) = S := by
    rw [mpow_add hS, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, mpow_one hS.isHermitian]
  have hS_trace : S.trace = 1 := (trace_partialTraceRight A).trans htrace
  rw [bkmGap_eq_zero_iff_commute_ratioPieces A hA K hK]
  constructor
  · intro h
    let o : R := Classical.choice hc.nonempty
    let T : Matrix E E ℂ := Matrix.of fun e f => B₀ (o, e) (o, f)
    have hcomm (v : ℝ) : Commute B₀ (lift (ratioPiece hS.isHermitian.eigenvalues v K₀)) := by
      let L := lift (ι := E) (ratioPiece hS.isHermitian.eigenvalues v K₀)
      have he : B * (W * L * W') = (W * L * W') * B := by
        simpa only [modularPiece, W, L, W', lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
          using (h v).eq
      change B₀ * L = L * B₀
      calc
        _ = W' * (B * (W * L)) := by simp only [B₀, Matrix.mul_assoc]
        _ = W' * (B * (W * L * W')) * W := by
          have hu : W * L * W' * W = W * L := by
            rw [Matrix.mul_assoc (W * L), hW'W, Matrix.mul_one]
          calc
            _ = W' * (B * (W * L * W' * W)) := by rw [hu]
            _ = _ := by simp only [Matrix.mul_assoc]
        _ = W' * ((W * L * W') * B) * W := by rw [he]
        _ = _ := by
          have hu : W' * (W * L * W') = L * W' := by
            calc
              _ = (W' * W) * L * W' := by simp only [Matrix.mul_assoc]
              _ = _ := by rw [hW'W, Matrix.one_mul]
          rw [← Matrix.mul_assoc W' (W * L * W') B, hu]
          simp only [B₀, Matrix.mul_assoc]
    have hT : B₀ = (1 : Matrix R R ℂ) ⊗ₖ T := by
      ext ⟨i,e⟩ ⟨j,f⟩
      have hs := scalar_of_commute_pieces hS.eigenvalues_pos hsimple hc
        (Matrix.of fun i j => B₀ (i,e) (j,f)) (fun v => commute_slice (hcomm v) e f) o
      have he := congrArg (fun (X : Matrix R R ℂ) => X i j) hs
      simpa [T, Matrix.kronecker_apply, mul_comm] using he
    have hB : B = (1 : Matrix R R ℂ) ⊗ₖ T := by
      have hr : W * B₀ * W' = B := by
        calc
          _ = (W * W') * B * (W * W') := by simp only [B₀, Matrix.mul_assoc]
          _ = _ := by rw [hWW', Matrix.one_mul, Matrix.mul_one]
      rw [← hr, hT]
      change (U ⊗ₖ (1 : Matrix E E ℂ)) * ((1 : Matrix R R ℂ) ⊗ₖ T) *
        (Uᴴ ⊗ₖ (1 : Matrix E E ℂ)) = _
      simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
        show U * Uᴴ = 1 from Unitary.coe_mul_star_self _]
    have hprod : A = S ⊗ₖ T := by
      calc
        A = H * B * H := (restore_density A hS).symm
        _ = _ := by
          rw [hB]
          change (mpow S (1 / 2) ⊗ₖ (1 : Matrix E E ℂ)) *
            ((1 : Matrix R R ℂ) ⊗ₖ T) * (mpow S (1 / 2) ⊗ₖ (1 : Matrix E E ℂ)) = _
          simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, hHH]
    have hleft : partialTraceLeft A = T := by
      calc
        partialTraceLeft A = partialTraceLeft (S ⊗ₖ T) :=
          congrArg (partialTraceLeft (A := R) (B := E)) hprod
        _ = S.trace • T := partialTraceLeft_kronecker S T
        _ = T := by rw [hS_trace, one_smul]
    rw [hleft]
    exact hprod
  · intro hp v
    let T := partialTraceLeft A
    obtain ⟨hHJ, hJH⟩ := lift_half_inverse (E := E) S hS
    change H * J = 1 at hHJ
    change J * H = 1 at hJH
    have hA' : A = H * ((1 : Matrix R R ℂ) ⊗ₖ T) * H := by
      rw [show A = S ⊗ₖ T from hp]
      change _ = (mpow S (1 / 2) ⊗ₖ (1 : Matrix E E ℂ)) *
        ((1 : Matrix R R ℂ) ⊗ₖ T) * (mpow S (1 / 2) ⊗ₖ (1 : Matrix E E ℂ))
      simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, hHH]
    have hB : B = (1 : Matrix R R ℂ) ⊗ₖ T := by
      change J * A * J = _
      rw [hA']
      calc
        _ = (J * H) * ((1 : Matrix R R ℂ) ⊗ₖ T) * (H * J) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hJH, hHJ, Matrix.one_mul, Matrix.mul_one]
    change Commute B _
    rw [hB]
    change _ * _ = _ * _
    simp only [lift, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

#print axioms bkmGap_eq_zero_iff_eq_marginals_kronecker

end D5.S3.Quantum.Recovery.BKMObservableProductRigidity
