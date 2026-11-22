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
  (modular weightedVec weightedLift weightedLift_compression bkmGap_rigidity)
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
  simp only [mpow, ← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]
  exact ⟨CFC.rpow_mul_rpow_neg _ hX.isStrictlyPositive,
    CFC.rpow_neg_mul_rpow _ hX.isStrictlyPositive⟩

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

private theorem lift_mul {ι : Type*} [Fintype ι] {m : Type*} [Fintype m] [DecidableEq m]
    (X Y : Matrix ι ι ℂ) : lift (ι := m) (X * Y) = lift X * lift Y := by
  simpa only [lift, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul X Y (1 : Matrix m m ℂ) 1)

private theorem lift_half_inverse (S : Matrix R R ℂ) (hS : S.PosDef) :
    lift (ι := E) (mpow S (1 / 2)) * lift (mpow S (-(1 / 2))) = 1 ∧
      lift (ι := E) (mpow S (-(1 / 2))) * lift (mpow S (1 / 2)) = 1 := by
  rw [← lift_mul, ← lift_mul, (mpow_half_inverse hS).1, (mpow_half_inverse hS).2,
    lift, Matrix.one_kronecker_one]
  exact ⟨rfl, rfl⟩

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
        simp only [lift, Matrix.smul_kronecker, RingHom.id_apply]
      rw [hl] at h'
      simp only [lift_mul] at h'
      exact h'
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

end D5.S3.Quantum.Recovery.BKMObservableProductRigidity
