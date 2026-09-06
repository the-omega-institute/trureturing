/- GID: D5/S3/Observer/Hankel/PositiveGramianBalancing
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/PositiveGramianBalancing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct mutually inverse balancing coordinates from two positive definite Gramians. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.PositiveGramianBalancing

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinates produced by simultaneous balancing. The existence theorem below
constructs these fields from positive definite matrices, rather than requiring
balancing identities as assumptions on an input realization. -/
structure Coordinates (P Q : Matrix ι ι ℝ) where
  weight : ι → ℝ
  toOriginal : Matrix ι ι ℝ
  fromOriginal : Matrix ι ι ℝ
  positive : ∀ i, 0 < weight i
  from_to : fromOriginal * toOriginal = 1
  to_from : toOriginal * fromOriginal = 1
  controllability : fromOriginal * P * fromOriginalᴴ = diagonal weight
  observability : toOriginalᴴ * Q * toOriginal = diagonal weight

/-- The positive square root is an actual Mathlib functional-calculus value. -/
def gramianRoot (P : Matrix ι ι ℝ) : Matrix ι ι ℝ := CFC.sqrt P

theorem gramianRoot_spec (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    (gramianRoot P).PosDef ∧ (gramianRoot P)ᴴ = gramianRoot P ∧
      gramianRoot P * gramianRoot P = P := by
  let L := gramianRoot P
  have hn : L.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hs : L * L = P := by
    simpa only [L, gramianRoot, pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hd : L.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hs
    rw [Matrix.det_mul, hz, zero_mul] at he
    exact (ne_of_gt hP.det_pos) he.symm
  have hu : IsUnit L := Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)
  exact ⟨hn.posDef_iff_isUnit.mpr hu, hn.isHermitian, hs⟩

private theorem diagonal_scalings (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    let D := diagonal w
    let H := diagonal (fun i => Real.sqrt (w i))
    let I := diagonal (fun i => (Real.sqrt (w i))⁻¹)
    H * I = 1 ∧ I * H = 1 ∧ I * D * I = 1 ∧
      I * diagonal (fun i => (w i) ^ 2) * I = D := by
  dsimp only
  have hn (i : ι) : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw i))
  have hs (i : ι) := Real.sq_sqrt (le_of_lt (hw i))
  constructor
  · simp [diagonal_mul_diagonal, hn]
  constructor
  · simp [diagonal_mul_diagonal, hn]
  constructor
  · rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    have he : (fun i => (Real.sqrt (w i))⁻¹ * w i * (Real.sqrt (w i))⁻¹) =
        (fun _ : ι => (1 : ℝ)) := by
      funext i
      field_simp [hn i]
      nlinarith [hs i]
    rw [he, diagonal_one]
  · rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    field_simp [hn i]
    nlinarith [hs i, congrArg (fun t : ℝ => w i * t) (hs i)]

/-- Every pair of real positive definite matrices admits balancing coordinates.
The construction is L=sqrt(P), K=L Q L, an orthonormal eigendecomposition of K,
and diagonal fourth-root rescaling. Repeated eigenvalues are allowed. -/
theorem coordinates_nonempty (P Q : Matrix ι ι ℝ) (hP : P.PosDef) (hQ : Q.PosDef) :
    Nonempty (Coordinates P Q) := by
  let L := gramianRoot P
  obtain ⟨hLp, hLs, hLL⟩ := gramianRoot_spec P hP
  change L.PosDef at hLp
  change Lᴴ = L at hLs
  change L * L = P at hLL
  have hLi : Function.Injective L.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hLp.isUnit
  have hLd : IsUnit L.det := Matrix.isUnit_iff_isUnit_det.mp hLp.isUnit
  have hLR : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hLd
  have hRL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hLd
  let K := L * Q * L
  have hK : K.PosDef := by
    simpa only [hLs] using hQ.conjTranspose_mul_mul_same hLi
  let U := hK.isHermitian.eigenvectorUnitary
  let lam := hK.isHermitian.eigenvalues
  let w : ι → ℝ := fun i => Real.sqrt (lam i)
  have hw (i : ι) : 0 < w i := Real.sqrt_pos.mpr (hK.eigenvalues_pos i)
  have hsq : (fun i => (w i) ^ 2) = lam := by
    funext i
    exact Real.sq_sqrt (le_of_lt (hK.eigenvalues_pos i))
  have hUU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hUU' : (U : Matrix ι ι ℝ)ᴴ * (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hKU : (U : Matrix ι ι ℝ)ᴴ * K * (U : Matrix ι ι ℝ) = diagonal lam := by
    simpa [U, lam, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hK.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  let D := diagonal w
  let H := diagonal (fun i => Real.sqrt (w i))
  let I := diagonal (fun i => (Real.sqrt (w i))⁻¹)
  obtain ⟨hHI, hIH, hIDI, hIWI⟩ := diagonal_scalings w hw
  change H * I = 1 at hHI
  change I * H = 1 at hIH
  change I * D * I = 1 at hIDI
  change I * diagonal (fun i => (w i) ^ 2) * I = D at hIWI
  have hIs : Iᴴ = I := by simp [I]
  let T := L * (U : Matrix ι ι ℝ) * I
  let S := H * (U : Matrix ι ι ℝ)ᴴ * L⁻¹
  have hST : S * T = 1 := by
    calc
      S * T = H * ((U : Matrix ι ι ℝ)ᴴ * (L⁻¹ * L) * (U : Matrix ι ι ℝ)) * I := by
        simp only [S, T, Matrix.mul_assoc]
      _ = H * I := by rw [hRL, mul_one, hUU', mul_one]
      _ = 1 := hHI
  have hTS : T * S = 1 := by
    calc
      T * S = L * ((U : Matrix ι ι ℝ) * (I * H) * (U : Matrix ι ι ℝ)ᴴ) * L⁻¹ := by
        simp only [S, T, Matrix.mul_assoc]
      _ = L * L⁻¹ := by rw [hIH, mul_one, hUU, mul_one]
      _ = 1 := hLR
  have hPfactor : T * D * Tᴴ = P := by
    calc
      T * D * Tᴴ = L * ((U : Matrix ι ι ℝ) * (I * D * I) *
          (U : Matrix ι ι ℝ)ᴴ) * L := by
        simp only [T, conjTranspose_mul, hLs, hIs, Matrix.mul_assoc]
      _ = L * L := by rw [hIDI, mul_one, hUU, mul_one]
      _ = P := hLL
  have hObs : Tᴴ * Q * T = D := by
    calc
      Tᴴ * Q * T = I * ((U : Matrix ι ι ℝ)ᴴ * K * (U : Matrix ι ι ℝ)) * I := by
        simp only [T, K, conjTranspose_mul, hLs, hIs, Matrix.mul_assoc]
      _ = I * diagonal lam * I := by rw [hKU]
      _ = D := by rw [← hsq]; exact hIWI
  have hReach : S * P * Sᴴ = D := by
    rw [← hPfactor]
    calc
      S * (T * D * Tᴴ) * Sᴴ = (S * T) * D * (S * T)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = D := by rw [hST]; simp
  exact ⟨⟨w, T, S, hw, hST, hTS, hReach, hObs⟩⟩

/-- A chosen output of the proved square-root/eigenvector construction. -/
def coordinates (P Q : Matrix ι ι ℝ) (hP : P.PosDef) (hQ : Q.PosDef) : Coordinates P Q :=
  Classical.choice (coordinates_nonempty P Q hP hQ)

namespace Coordinates

variable {P Q : Matrix ι ι ℝ} (b : Coordinates P Q)

/-- Exact recovery of the original controllability Gramian. -/
theorem controllability_factor :
    P = b.toOriginal * diagonal b.weight * b.toOriginalᴴ := by
  rw [← b.controllability]
  calc
    P = (b.toOriginal * b.fromOriginal) * P * (b.toOriginal * b.fromOriginal)ᴴ := by
      rw [b.to_from]; simp
    _ = b.toOriginal * (b.fromOriginal * P * b.fromOriginalᴴ) * b.toOriginalᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- The balanced diagonal squares give the Gramian-product characteristic
polynomial with multiplicities, without calling the nonsymmetric product Hermitian. -/
theorem gramian_product_charpoly :
    (P * Q).charpoly = ∏ i, (Polynomial.X - Polynomial.C ((b.weight i) ^ 2)) := by
  have hconj : b.fromOriginal * (P * Q) * b.toOriginal =
      diagonal (fun i => (b.weight i) ^ 2) := by
    rw [b.controllability_factor]
    calc
      b.fromOriginal * ((b.toOriginal * diagonal b.weight * b.toOriginalᴴ) * Q) *
          b.toOriginal = (b.fromOriginal * b.toOriginal) * diagonal b.weight *
            (b.toOriginalᴴ * Q * b.toOriginal) := by simp only [Matrix.mul_assoc]
      _ = diagonal b.weight * diagonal b.weight := by rw [b.from_to, one_mul, b.observability]
      _ = diagonal (fun i => (b.weight i) ^ 2) := by simp only [diagonal_mul_diagonal, pow_two]
  have hchar : (b.fromOriginal * (P * Q) * b.toOriginal).charpoly = (P * Q).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, b.to_from, one_mul]
  rw [← hchar, hconj, Matrix.charpoly_diagonal]

end Coordinates

#print axioms coordinates_nonempty
#print axioms Coordinates.gramian_product_charpoly

end D5.S3.Observer.Hankel.PositiveGramianBalancing
