/- GID: D5/S3/Quantum/Divergence/UniversalPositiveScalarizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UniversalPositiveScalarizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One positive state controls both completely amplified channel residual Grams. -/

import D5.S3.Quantum.Divergence.PositiveKrausCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open Matrix

namespace D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.UniversalCommonCenter

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

private def amp {R m n : Type*} [DecidableEq R]
    (M : Matrix m n ℂ) : Matrix (R × m) (R × n) ℂ :=
  (1 : Matrix R R ℂ) ⊗ₖ M

private def piAmp {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × (b × Env a b)) (R × (b × Env a b)) ℂ :=
  (Y ⊗ₖ (1 : Matrix (Env a b) (Env a b) ℂ)).submatrix
    (Equiv.prodAssoc R b (Env a b)).symm (Equiv.prodAssoc R b (Env a b)).symm

private lemma amp_mul {R m n p : Type*} [Fintype R] [DecidableEq R]
    [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    amp (R := R) A * amp (R := R) B = amp (R := R) (A * B) := by
  simp only [amp]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

private lemma amp_star {R m n : Type*} [DecidableEq R]
    (A : Matrix m n ℂ) : (amp (R := R) A)ᴴ = amp (R := R) Aᴴ := by
  simp [amp, Matrix.conjTranspose_kronecker]

private lemma piAmp_mul {R : Type u} [Fintype R] [DecidableEq R]
    (Y Z : Matrix (R × b) (R × b) ℂ) :
    piAmp (a := a) Y * piAmp (a := a) Z = piAmp (a := a) (Y * Z) := by
  unfold piAmp
  rw [Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc R b (Env a b)).symm,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

private lemma piAmp_star {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    (piAmp (a := a) Y)ᴴ = piAmp (a := a) Yᴴ := by
  simp [piAmp, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

private lemma piAmp_mul_amp {R : Type u} [Fintype R] [DecidableEq R]
    (B : Matrix (b × Env a b) a ℂ) (Y : Matrix (R × b) (R × b) ℂ)
    (r s : R) (p : b × Env a b) (y : a) :
    (piAmp (a := a) Y * amp (R := R) B) (r,p) (s,y) =
      (pi (a := a) (Y.submatrix (fun u => (r,u)) (fun v => (s,v))) * B) p y := by
  rcases p with ⟨u,c⟩
  simp only [Matrix.mul_apply, piAmp, amp, Matrix.kronecker_apply,
    Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Fintype.sum_prod_type]
  simp [pi, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum]

private lemma amp_compression {R : Type u} [Fintype R] [DecidableEq R]
    (A B : Matrix (b × Env a b) a ℂ)
    (Y : Matrix (R × b) (R × b) ℂ) (r s : R) (x y : a) :
    ((amp (R := R) A)ᴴ * piAmp (a := a) Y * amp (R := R) B) (r,x) (s,y) =
      (Aᴴ * pi (a := a) (Y.submatrix (fun u => (r,u)) (fun v => (s,v))) * B) x y := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp_rw [piAmp_mul_amp]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp [amp, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.kronecker_apply,
    apply_ite, ite_mul, Matrix.mul_apply, Fintype.sum_prod_type]

private lemma PhiR_factor {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    PhiR Φ Y = (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) (J Φ) := by
  ext ⟨r,x⟩ ⟨s,y⟩
  rw [amp_compression]
  exact congrArg (fun M : Matrix a a ℂ => M x y)
    (Phi_factor Φ (Y.submatrix (fun u => (r,u)) (fun v => (s,v))))

/-- The weighted ordinary partial-trace center. -/
def stateCenter {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) : Matrix R R ℂ :=
  fun r s => ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
    Y.submatrix (fun u => (r,u)) (fun v => (s,v))).trace

private lemma stateCenter_partialTrace {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) :
    stateCenter σ Y =
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
        (((1 : Matrix R R ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ)) * Y) := by
  ext r s
  simp [stateCenter, Matrix.trace, Matrix.mul_apply, Matrix.kronecker_apply,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul]

private lemma amp_state_compression {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (σ : DensityState b)
    (W : Matrix (b × Env a b) a ℂ)
    (hW : ∀ Z : Matrix b b ℂ, (J Φ)ᴴ * pi (a := a) Z * W =
      ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace • (1 : Matrix a a ℂ))
    (Y : Matrix (R × b) (R × b) ℂ) :
    (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) W =
      stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ) := by
  ext ⟨r,x⟩ ⟨s,y⟩
  rw [amp_compression, hW]
  rfl

private lemma amp_sub {R m n : Type*} [DecidableEq R]
    (A B : Matrix m n ℂ) : amp (R := R) (A - B) =
      amp (R := R) A - amp (R := R) B := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp [amp, mul_sub]

private lemma amp_smul {R m n : Type*} [DecidableEq R]
    (c : ℂ) (A : Matrix m n ℂ) : amp (R := R) (c • A) =
      c • amp (R := R) A := by
  simp [amp, Matrix.kronecker_smul]

private lemma amp_one {R m : Type*} [DecidableEq R] [DecidableEq m] :
    amp (R := R) (1 : Matrix m m ℂ) = 1 := Matrix.one_kronecker_one

private lemma amp_pos {R m : Type*} [Fintype R] [DecidableEq R]
    [Fintype m] [DecidableEq m] {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (amp (R := R) A).PosSemidef := by
  exact Matrix.PosSemidef.one.kronecker hA

private lemma amp_supported_flip {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (K : Matrix (b × Env a b) a ℂ) (k : ℝ)
    (hK : ((k : ℂ) • e Φ - K * Kᴴ).PosSemidef) :
    ((k : ℂ) • amp (R := R) (e Φ) -
      amp (R := R) K * (amp (R := R) K)ᴴ).PosSemidef := by
  have h := amp_pos (R := R) hK
  rw [amp_sub, amp_smul, ← amp_mul, ← amp_star] at h
  exact h

private lemma amplified_defect {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    defectR Φ Y =
      (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y *
        amp (R := R) (e Φ) * (piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ) := by
  rw [defectR, PhiR_factor, PhiR_factor]
  rw [← piAmp_mul, ← piAmp_star]
  simp [e, amp_sub, amp_one, ← amp_mul, ← amp_star, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.mul_sub, Matrix.sub_mul]

set_option maxHeartbeats 800000 in
lemma defectR_posSemidef {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    (defectR Φ Y).PosSemidef := by
  rw [amplified_defect]
  have he : (e Φ).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (e Φ)
    rw [e_star Φ, e_mul_self Φ] at h
    exact h
  have h := (amp_pos (R := R) he).conjTranspose_mul_mul_same
    ((piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ))
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

private lemma amplified_state_bound {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (k : ℝ) (σ : DensityState b)
    (W K : Matrix (b × Env a b) a ℂ) (hK : K = J Φ - W)
    (hKflip : ((k : ℂ) • e Φ - K * Kᴴ).PosSemidef)
    (hcompress : ∀ Z : Matrix b b ℂ, (J Φ)ᴴ * pi (a := a) Z * W =
      ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace • (1 : Matrix a a ℂ))
    (Y : Matrix (R × b) (R × b) ℂ) :
    let X := stateCenter σ Y;
      ((k : ℂ) • defectR Φ Y -
        (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          Matrix.conjTranspose (PhiR Φ Y - Matrix.kronecker X
            (1 : Matrix a a ℂ))).PosSemidef := by
  dsimp only
  let X := stateCenter σ Y
  have hX : PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ) =
      (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) K := by
    rw [PhiR_factor]
    change _ - stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ) = _
    rw [← amp_state_compression Φ σ W hcompress Y, hK, amp_sub, Matrix.mul_sub]
  have hflip := amp_supported_flip (R := R) (a := a) Φ K k hKflip
  have hcong := hflip.conjTranspose_mul_mul_same
    ((piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ))
  change ((k : ℂ) • defectR Φ Y -
    (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
      (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ).PosSemidef
  rw [hX, amplified_defect]
  convert hcong using 1 <;>
    simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

private lemma stateCenter_star {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) :
    stateCenter σ Yᴴ = (stateCenter σ Y)ᴴ := by
  have hσ : (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.nonnegative)).isHermitian
  ext r s
  change ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
    Yᴴ.submatrix (fun u => (r,u)) (fun v => (s,v))).trace =
    star (((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
      Y.submatrix (fun u => (s,u)) (fun v => (r,v))).trace)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hσ.eq,
    Matrix.trace_mul_comm]
  rfl

/-- One positive trace-one state controls both actual completely amplified
residual Grams at the same weighted ordinary partial-trace center. -/
theorem common_positive_state_scalarizer
    (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ σ : DensityState b,
      ∀ {R : Type u} [Fintype R] [DecidableEq R]
        (Y : Matrix (R × b) (R × b) ℂ),
        let X := stateCenter σ Y;
        let Δ := PhiR Φ Y - X ⊗ₖ (1 : Matrix a a ℂ);
        X = D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
          (((1 : Matrix R R ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ)) * Y) ∧
        (((k : ℂ) • (PhiR Φ (Y * Yᴴ) - PhiR Φ Y * (PhiR Φ Y)ᴴ)) -
          Δ * Δᴴ).PosSemidef ∧
        (((k : ℂ) • (PhiR Φ (Yᴴ * Y) - (PhiR Φ Y)ᴴ * PhiR Φ Y)) -
          Δᴴ * Δ).PosSemidef := by
  obtain ⟨σ,W,K,hW,heW,hK,hKorth,heK,hKflip,hcompress⟩ :=
    common_positive_state_compression Φ k hk hUniversal
  refine ⟨σ,?_⟩
  intro R _ _ Y
  refine ⟨stateCenter_partialTrace σ Y,
    amplified_state_bound Φ k σ W K hK hKflip hcompress Y, ?_⟩
  have h := amplified_state_bound Φ k σ W K hK hKflip hcompress Yᴴ
  have hΔ : PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ) =
      (PhiR Φ Y - stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ))ᴴ := by
    simp only [PhiR_star, stateCenter_star, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  dsimp only at h ⊢
  change (((k : ℂ) • defectR Φ Yᴴ) -
    (PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ)) *
      (PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ))ᴴ).PosSemidef at h
  rw [hΔ] at h
  simpa only [defectR, Matrix.conjTranspose_conjTranspose, PhiR_star] using h

#print axioms common_positive_state_scalarizer

end D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
