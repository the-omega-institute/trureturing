/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Strict positivity of the original total mass on the common interior corner. -/


import D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
import D5.S3.Quantum.Divergence.MaximalHockeyStickSupport

/-! The common interior corner inherits a faithful total-mass weight. -/


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickCorner

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalue labels in the genuine common interior support. -/
abbrev InteriorIndex {C : Matrix n n ℂ} (hC : C.IsHermitian) :=
  {i // 0 < hC.eigenvalues i ∧ hC.eigenvalues i < 1}

/-- Isometric inclusion of the actual interior spectral subspace. -/
def interiorEmbedding {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    Matrix n (InteriorIndex hC) ℂ := by
  classical
  exact (hC.eigenvectorUnitary : Matrix n n ℂ) *
    inclusion (fun i => 0 < hC.eigenvalues i ∧ hC.eigenvalues i < 1)

theorem embedding_isometry {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    (interiorEmbedding hC)ᴴ * interiorEmbedding hC = 1 := by
  classical
  simp only [interiorEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (star (hC.eigenvectorUnitary : Matrix n n ℂ))
      (hC.eigenvectorUnitary : Matrix n n ℂ),
    ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]
  exact inclusion_isometry _

theorem embedding_eigenvectors {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    C * interiorEmbedding hC = interiorEmbedding hC *
      diagonal (fun i : InteriorIndex hC => (hC.eigenvalues i.val : ℂ)) := by
  classical
  let J := inclusion (fun i => 0 < hC.eigenvalues i ∧ hC.eigenvalues i < 1)
  have hdiag : diagonal (fun i => (hC.eigenvalues i : ℂ)) * J =
      J * diagonal (fun i : InteriorIndex hC => (hC.eigenvalues i.val : ℂ)) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, J, inclusion]
    split_ifs with hij
    · rw [hij, mul_one, one_mul]
    · simp
  have hs : C = (hC.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (hC.eigenvalues i : ℂ)) * star (hC.eigenvectorUnitary : Matrix n n ℂ) := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal] using hC.spectral_theorem
  change C * ((hC.eigenvectorUnitary : Matrix n n ℂ) * J) = _
  calc
    _ = ((hC.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (hC.eigenvalues i : ℂ)) * star (hC.eigenvectorUnitary : Matrix n n ℂ)) *
        ((hC.eigenvectorUnitary : Matrix n n ℂ) * J) := congrArg
          (fun M : Matrix n n ℂ => M * ((hC.eigenvectorUnitary : Matrix n n ℂ) * J)) hs
    _ = (hC.eigenvectorUnitary : Matrix n n ℂ) * (J *
        diagonal (fun i : InteriorIndex hC => (hC.eigenvalues i.val : ℂ))) := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (hC.eigenvectorUnitary : Matrix n n ℂ))
        (hC.eigenvectorUnitary : Matrix n n ℂ), Unitary.coe_star_mul_self, Matrix.one_mul, hdiag]
    _ = _ := by simp only [interiorEmbedding, J, Matrix.mul_assoc]

private theorem regularized_posDef (S : Matrix n n ℂ) (hS : S.PosSemidef) :
    (S + (1 - spectralSupport S)).PosDef := by
  let f : ℝ → ℝ := fun x => x + (1 - if x = 0 then 0 else 1)
  have he : cfc f S = S + (1 - spectralSupport S) := by
    rw [show f = (fun x : ℝ => x + (1 - if x = 0 then 0 else 1)) from rfl,
      cfc_add S _ _ (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _),
      cfc_id' ℝ S hS.isHermitian.isSelfAdjoint,
      cfc_sub _ _ S (S.finite_real_spectrum.continuousOn _) (S.finite_real_spectrum.continuousOn _),
      cfc_const 1 S hS.isHermitian.isSelfAdjoint]
    rfl
  rw [← he]
  apply Matrix.IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff f S (S.finite_real_spectrum.continuousOn f)
    hS.isHermitian.isSelfAdjoint).2
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [hS.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hS.eigenvalues_nonneg i
  dsimp only [f]
  by_cases hz : x = 0
  · simp [hz]
  · simp only [if_neg hz, sub_self, add_zero]
    exact lt_of_le_of_ne hx0 (Ne.symm hz)

/-- Support inclusion, rather than invertibility of the ambient total mass,
implies a strictly positive compressed trace weight. -/
theorem compressed_weight_posDef (S C : Matrix n n ℂ) (hS : S.PosSemidef)
    (hC : C.IsHermitian) (hQC : spectralSupport S * C = C) :
    ((interiorEmbedding hC)ᴴ * S * interiorEmbedding hC).PosDef := by
  classical
  let E := interiorEmbedding hC
  let D := diagonal (fun i : InteriorIndex hC => (hC.eigenvalues i.val : ℂ))
  have hCE : C * E = E * D := embedding_eigenvectors hC
  have hQE : spectralSupport S * E = E := by
    have he : (spectralSupport S * E - E) * D = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hCE, ← Matrix.mul_assoc, hQC, hCE, sub_self]
    ext i j
    have hh := congrArg (fun M => M i j) he
    simp only [Matrix.mul_diagonal, Matrix.zero_apply, D] at hh
    have hj : (hC.eigenvalues j.val : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt j.property.1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hj)
  have hEinj : Function.Injective E.mulVec := by
    intro x y he
    have hh := congrArg (fun v => Eᴴ *ᵥ v) he
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at hh
    simpa only [E, embedding_isometry hC, Matrix.one_mulVec] using hh
  have hp := (regularized_posDef S hS).conjTranspose_mul_mul_same hEinj
  have he : Eᴴ * (S + (1 - spectralSupport S)) * E = Eᴴ * S * E := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc, Matrix.one_mul, hQE, sub_self, add_zero]
  exact he ▸ hp

/-- For every original singular PSD pair, its normalized common interior
corner carries a strictly positive compression of the original sum `A+B`.
The statement includes the zero pair and the empty corner. -/
theorem original_pair_weight_posDef (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let C := normalize (A + B) A
    let hC := (normalized_pair A B hA hB).1.isHermitian
    ((interiorEmbedding hC)ᴴ * (A + B) * interiorEmbedding hC).PosDef := by
  dsimp only
  apply compressed_weight_posDef (A + B) (normalize (A + B) A) (hA.add hB)
    (normalized_pair A B hA hB).1.isHermitian
  obtain ⟨-, -, hPK, -⟩ := spectral_sqrt_inverse_products (A + B) (hA.add hB)
  simp only [MaximalHockeyStickSupport.normalize, ← Matrix.mul_assoc, hPK]

end D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
