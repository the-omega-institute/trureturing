/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/Kernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positivity of the cubic trace with a centered scalar Gram kernel. -/

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Basic.Complex.BigOperators
import D5.S3.Quantum.Analysis.RefinedBMV43Kernel
import D5.S3.Quantum.Analysis.RefinedBMVDimThreeInteger

/-! Positivity of the cubic trace with a centered scalar Gram kernel. -/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.Tracial

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

/-- A single centered cubic trace is nonnegative for a real Gram factorization. -/
theorem centeredTrace_nonneg_of_factor
    {κ : Type*} [Fintype κ]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (hP : ∀ j, 0 ≤ P j) (hB : 0 ≤ B)
    (i : ι) (K : Matrix ι ι ℝ) (c : κ → ι → ℝ)
    (hc : ∀ j k, K j k = ∑ l, c l j * c l k) :
    0 ≤ ∑ j, ∑ k, (K j k : ℂ) * τ (P i * B * P j * B * P k * B) := by
  classical
  let Z (l : κ) : A := ∑ j, (c l j : ℂ) • P j
  let C : A := ∑ j, ∑ k, (K j k : ℂ) • (P j * B * P k)

  have hPstar (j : ι) : star (P j) = P j := (hP j).star_eq
  have hZ (l : κ) : star (Z l) = Z l := by
    simp only [Z, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, hPstar]

  have hcComplex (j k : ι) :
      (K j k : ℂ) = ∑ l, (c l j : ℂ) * (c l k : ℂ) := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
      congrArg Complex.ofReal (hc j k)

  have hExpand (l : κ) :
      Z l * B * Z l =
        ∑ j, ∑ k, ((c l j : ℂ) * (c l k : ℂ)) • (P j * B * P k) := by
    simp only [Z, Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [smul_mul_assoc]
    simp only [mul_smul_comm, mul_smul]

  have hC : C = ∑ l, Z l * B * Z l := by
    let term (l : κ) (j k : ι) : A :=
      ((c l j : ℂ) * (c l k : ℂ)) • (P j * B * P k)
    calc
      C = ∑ j, ∑ k, ∑ l, term l j k := by
        simp only [C, hcComplex, Finset.sum_smul, term]
      _ = ∑ j, ∑ l, ∑ k, term l j k :=
        Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
      _ = ∑ l, ∑ j, ∑ k, term l j k := Finset.sum_comm
      _ = ∑ l, Z l * B * Z l :=
        Finset.sum_congr rfl fun l _ ↦ (hExpand l).symm

  have hCpos : 0 ≤ C := by
    rw [hC]
    refine Finset.sum_nonneg fun l _ ↦ ?_
    simpa only [hZ l] using star_left_conjugate_nonneg hB (Z l)

  have hBCB : 0 ≤ B * C * B := conjugate_nonneg_of_nonneg hCpos hB
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hP i)
  have hTrace : 0 ≤ τ (P i * B * C * B) := by
    calc
      0 ≤ τ (R * (B * C * B) * star R) :=
        τ.map_nonneg (star_right_conjugate_nonneg hBCB R)
      _ = τ (P i * B * C * B) := by
        simpa only [hR, mul_assoc] using hτ (R * (B * C * B)) (star R)

  simpa only [C, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, map_sum, map_smul, smul_eq_mul, mul_assoc] using hTrace

/-- Finite operator Gram positivity for a PSD matrix at every center. -/
theorem centeredCubicTrace_nonneg
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (hP : ∀ i, 0 ≤ P i) (hB : 0 ≤ B)
    (K : ι → Matrix ι ι ℝ) (hK : ∀ i, (K i).PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ k, (K i j k : ℂ) * τ (P i * B * P j * B * P k * B) := by
  classical
  refine Finset.sum_nonneg fun i _ ↦ ?_
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hK i).nonneg
  apply centeredTrace_nonneg_of_factor τ hτ P B hP hB i (K i) (fun l j ↦ S l j)
  intro j k
  calc
    K i j k = (star S * S) j k :=
      congrArg (fun M : Matrix ι ι ℝ ↦ M j k) hS
    _ = ∑ l, S l j * S l k := by
      simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial]

/-- Degree four uses the existing scalar kernel and a diagonal congruence. -/
theorem centeredCubicTrace43_nonneg
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (hP : ∀ i, 0 ≤ P i) (hB : 0 ≤ B)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ ∑ i, ∑ j, ∑ k,
      (((x i - x j) * (x i - x k) * centeredKernel43 (x i) (x j) (x k) : ℝ) : ℂ) *
        τ (P i * B * P j * B * P k * B) := by
  classical
  let d (i j : ι) := x i - x j
  let G (i : ι) : Matrix ι ι ℝ :=
    Matrix.of fun j k ↦ centeredKernel43 (x i) (x j) (x k)
  let K (i : ι) : Matrix ι ι ℝ :=
    diagonal (d i) * G i * (diagonal (d i))ᴴ
  have hK (i : ι) : (K i).PosSemidef := by
    have hG : (G i).PosSemidef := centeredKernel43_psd (x i) (hx i) x hx
    exact hG.mul_mul_conjTranspose_same (diagonal (d i))
  have hEntry (i j k : ι) :
      K i j k = d i j * d i k * centeredKernel43 (x i) (x j) (x k) := by
    simp only [K, G, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.of_apply, star_trivial]
    exact mul_right_comm _ _ _
  simpa only [hEntry, d] using centeredCubicTrace_nonneg τ hτ P B hP hB K hK


/-- A cyclic decomposition into centered PSD matrices controls the cubic trace defect. -/
theorem cubicTrace_nonneg_of_cyclic
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (hP : ∀ i, 0 ≤ P i) (hB : 0 ≤ B)
    (d : ι → ι → ι → ℝ) (K : ι → Matrix ι ι ℝ)
    (hD : ∀ i j k, d i j k = K i j k + K j k i + K k i j)
    (hK : ∀ i, (K i).PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ k, (d i j k : ℂ) * τ (P i * B * P j * B * P k * B) := by
  classical
  let walk (f : ι → ι → ι → ℝ) : ℂ :=
    ∑ i, ∑ j, ∑ k, (f i j k : ℂ) * τ (P i * B * P j * B * P k * B)
  have hRotate (f : ι → ι → ι → ℝ) : walk (fun i j k => f j k i) = walk f := by
    unfold walk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simpa only [mul_assoc] using hτ (P i * B) (P j * B * P k * B)
  have hDefect : walk d =
      walk (fun i j k => K i j k) +
      walk (fun i j k => K j k i) +
      walk (fun i j k => K k i j) := by
    simp only [walk, hD, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  change 0 ≤ walk d
  rw [hDefect, hRotate (fun i j k => K j k i), hRotate (fun i j k => K i j k)]
  have hPos : 0 ≤ walk (fun i j k => K i j k) := centeredCubicTrace_nonneg τ hτ P B hP hB K hK
  exact add_nonneg (add_nonneg hPos hPos) hPos


/-- The mixed moments of a finite positive family in a tracial algebra. -/
noncomputable def moment (x : ι → ℝ) (P : ι → A) (k : ℕ) : A :=
  ∑ i, ((x i ^ k : ℝ) : ℂ) • P i

/-- The cubic trace of three mixed moments expands as the same scalar walk as in matrices. -/
theorem mixedMomentTrace
    (τ : A →P[ℂ] ℂ) (P : ι → A) (B : A) (x : ι → ℝ) (r s t : ℕ) :
    τ (moment x P r * B * moment x P s * B * moment x P t * B) =
      ∑ i, ∑ j, ∑ k, ((x i ^ r * x j ^ s * x k ^ t : ℝ) : ℂ) *
        τ (P i * B * P j * B * P k * B) := by
  classical
  simp only [moment, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring


open DimThree (gaps defect)

/-- A positive cyclic decomposition of the scalar defect gives the trace comparison
for finite positive functional-calculus approximants. -/
theorem momentTrace_defect_nonneg
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : ι → A) (B : A) (hP : ∀ i, 0 ≤ P i) (hB : 0 ≤ B)
    (p : ℕ) (x : ι → ℝ) (K : ι → Matrix ι ι ℝ)
    (hD : ∀ i j k, defect p (x i) (x j) (x k) = K i j k + K j k i + K k i j)
    (hK : ∀ i, (K i).PosSemidef) :
    0 ≤ ((gaps p).map fun g =>
      τ (moment x P (3 * g.1) * B * moment x P (3 * g.2.1) * B *
        moment x P (3 * g.2.2) * B)).sum -
      ((gaps p).length : ℂ) * τ ((moment x P p * B) ^ 3) := by
  classical
  let walk : (ι → ι → ι → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ i, ∑ j, ∑ k, f i j k * τ (P i * B * P j * B * P k * B)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a f
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply] }
  let coefficient (g : ℕ × ℕ × ℕ) (i j k : ι) : ℂ :=
    ((x i ^ (3 * g.1) * x j ^ (3 * g.2.1) * x k ^ (3 * g.2.2) : ℝ) : ℂ)
  have htrace (g : ℕ × ℕ × ℕ) :
      τ (moment x P (3 * g.1) * B * moment x P (3 * g.2.1) * B *
        moment x P (3 * g.2.2) * B) = walk (coefficient g) :=
    mixedMomentTrace τ P B x _ _ _
  have hsum (l : List (ℕ × ℕ × ℕ)) :
      (l.map fun g => walk (coefficient g)).sum =
        walk (fun i j k => (l.map fun g => coefficient g i j k).sum) := by
    induction l with
    | nil => exact (map_zero walk).symm
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons, ih, ← map_add]
      rfl
  have hcube : τ ((moment x P p * B) ^ 3) =
      walk (fun i j k => ((x i ^ p * x j ^ p * x k ^ p : ℝ) : ℂ)) := by
    simpa only [walk, LinearMap.coe_mk, AddHom.coe_mk, pow_succ, pow_zero, one_mul, mul_assoc] using
      mixedMomentTrace τ P B x p p p
  simp only [htrace, hsum, hcube]
  change 0 ≤ walk _ - ((gaps p).length : ℂ) • walk _
  rw [← map_smul, ← map_sub]
  have he : (fun i j k => ((gaps p).map fun g => coefficient g i j k).sum) -
      ((gaps p).length : ℂ) • (fun i j k => ((x i ^ p * x j ^ p * x k ^ p : ℝ) : ℂ)) =
        (fun i j k => ((defect p (x i) (x j) (x k) : ℝ) : ℂ)) := by
    funext i j k
    change _ = Complex.ofRealHom (defect p (x i) (x j) (x k))
    simp only [defect, map_sub, map_list_sum, map_pow, map_mul, map_natCast, List.map_map,
      Function.comp_def, Complex.ofRealHom_eq_coe, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, coefficient, mul_pow, pow_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [he]
  exact cubicTrace_nonneg_of_cyclic τ hτ P B hP hB
    (fun i j k => defect p (x i) (x j) (x k)) K hD hK

end RefinedBMV.Tracial
