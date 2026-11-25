/- GID: D5/S3/Quantum/Matrix/Spectral/IsometricCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Spectral/IsometricCalculus
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Finite Hermitian intertwining and orthonormal extension of a contraction. -/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
universe u v

namespace D5.S3.Quantum.Lieb.PositiveMapJensen
variable {n : Type u} {m : Type v}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Rectangular congruence preserves the finite Loewner order. -/
theorem congruence_mono {A B : Matrix n n ℂ} (hAB : A ≤ B)
    (V : Matrix n m ℂ) : Vᴴ * A * V ≤ Vᴴ * B * V := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same V

/-- Intertwining of Hermitian matrices is preserved by every real spectral
function. Finiteness makes every such function continuous on these spectra. -/
theorem cfc_intertwining (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix n m ℂ)
    (hAV : A * V = V * B) (f : ℝ → ℝ) :
    cfc f A * V = V * cfc f B := by
  classical
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let T : Matrix m m ℂ := hB.eigenvectorUnitary
  let E : Matrix n m ℂ := Uᴴ * V * T
  have hU : Uᴴ * U = 1 := hA.eigenvectorUnitary.2.1
  have hu : U * Uᴴ = 1 := hA.eigenvectorUnitary.2.2
  have hT : Tᴴ * T = 1 := hB.eigenvectorUnitary.2.1
  have ht : T * Tᴴ = 1 := hB.eigenvectorUnitary.2.2
  have hsA : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using hA.spectral_theorem
  have hsB : B = T * diagonal (fun i => (hB.eigenvalues i : ℂ)) * Tᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, T, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using hB.spectral_theorem
  have coeff : diagonal (fun i => (hA.eigenvalues i : ℂ)) * E =
      E * diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
    calc
      _ = Uᴴ * (A * V) * T := by
        conv_rhs => rw [hsA]
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU,
          Matrix.one_mul]
      _ = Uᴴ * (V * B) * T := by rw [hAV]
      _ = _ := by
        conv_lhs => rw [hsB]
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT,
          Matrix.one_mul, Matrix.mul_one]
  have fcoeff : diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * E =
      E * diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
    by_cases he : hA.eigenvalues i = hB.eigenvalues j
    · rw [he, mul_comm]
    · have hz : E i j = 0 := by
        have hn : (hA.eigenvalues i : ℂ) ≠ (hB.eigenvalues j : ℂ) := by
          exact_mod_cast he
        have heq : ((hA.eigenvalues i : ℂ) - (hB.eigenvalues j : ℂ)) * E i j = 0 := by
          linear_combination eq
        exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
      simp only [hz, mul_zero, zero_mul]
  have reconstruct : U * E * Tᴴ = V := by
    simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu,
      Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
  rw [hA.cfc_eq, hB.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  change (U * diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ) * V =
    V * (T * diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) * Tᴴ)
  conv_lhs => rw [← reconstruct]
  conv_rhs => rw [← reconstruct]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
    ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc _ E, fcoeff]
  simp only [Matrix.mul_assoc]

end D5.S3.Quantum.Lieb.PositiveMapJensen

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks

theorem exists_unitary_dilation {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      U ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ i j, U (Sum.inl i) (Sum.inl j) = C i j := by
  classical
  let R := CFC.sqrt (1 - Cᴴ * C)
  have hR : R.IsHermitian := (CFC.sqrt_nonneg (1 - Cᴴ * C)).posSemidef.isHermitian
  have hRR : Rᴴ * R = 1 - Cᴴ * C := by
    rw [hR.eq]
    exact CFC.sqrt_mul_sqrt_self _ hC.nonneg
  let v : (Fin n ⊕ Fin n) → EuclideanSpace ℂ (Fin n ⊕ Fin n) :=
    Sum.elim (fun j => WithLp.toLp 2 (Sum.elim (fun i => C i j) (fun i => R i j)))
      (fun _ => 0)
  let s : Set (Fin n ⊕ Fin n) := Set.range Sum.inl
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    obtain ⟨i, rfl⟩ := hi
    obtain ⟨j, rfl⟩ := hj
    have hsum : Cᴴ * C + Rᴴ * R = 1 := by rw [hRR]; abel
    have hm := congrArg (fun M => M i j) hsum
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at hm
    simpa [Set.domRestrict_apply, v, PiLp.inner_apply, Fintype.sum_sum_type,
      Subtype.ext_iff, Sum.elim_inl, Sum.elim_inr, mul_comm] using hm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp)
  let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℂ).toBasis.toMatrix b
  refine ⟨U, (EuclideanSpace.basisFun _ ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  intro i j
  have he := hb (Sum.inl j) (by exact ⟨j, rfl⟩)
  change (b (Sum.inl j)) (Sum.inl i) = C i j
  simpa only [v, Sum.elim_inl] using
    congrArg (fun w => w (Sum.inl i)) he

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
