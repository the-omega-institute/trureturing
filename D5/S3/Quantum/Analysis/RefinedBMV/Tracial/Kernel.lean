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
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

/-! Positivity of the cubic trace with a centered scalar Gram kernel. -/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.Tracial

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

/-- After summing the two lower slots, the fourth-order mixed trace is
controlled by the compressed product and the outer fourth moments. -/
theorem exceptional_residue_sq_le
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (C E F Z S : A) :
    let R := S * S
    let Y := E * R * F * S
    ‖τ (C * E * R * F * R * star Z)‖ ^ 2 ≤
      (τ (star Y * Y)).re * (‖S‖ ^ 2 *
        (Real.sqrt (τ ((Z * star Z) ^ 2)).re *
          Real.sqrt (τ ((C * star C) ^ 2)).re)) := by
  dsimp only
  let R := S * S
  let Y := E * R * F * S
  let W := star Z * C
  have hnorm {a : A} (ha : 0 ≤ a) : ‖τ a‖ = (τ a).re := by
    simpa only [Complex.ofReal_re] using
      (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (τ.map_nonneg ha))).symm
  have hrotate : τ (Y * (S * W)) = τ (C * E * R * F * R * star Z) := by
    simpa only [W, Y, R, mul_assoc] using (hτ C (Y * S * star Z)).symm
  have hY : τ (Y * star Y) = τ (star Y * Y) := hτ _ _
  have hcs := PositiveLinearMap.norm_map_star_mul_sq_le τ (star Y) (S * W)
  rw [star_star, hrotate, hY, hnorm (star_mul_self_nonneg Y),
    hnorm (star_mul_self_nonneg (S * W))] at hcs
  have hideal : (τ (star (S * W) * (S * W))).re ≤ ‖S‖ ^ 2 * (τ (star W * W)).re := by
    have h := Complex.re_le_re (τ.monotone
      (star_left_conjugate_le_conjugate (CStarAlgebra.star_mul_le_algebraMap_norm_sq S) W))
    change (τ (star W * (star S * S) * W)).re ≤
      (τ (star W * algebraMap ℝ A (‖S‖ ^ 2) * W)).re at h
    simpa only [star_mul, mul_assoc, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      mul_smul_comm, one_mul, ← Complex.coe_smul, map_smul, smul_eq_mul,
      Complex.re_ofReal_mul] using h
  have hW : τ (star W * W) = τ ((Z * star Z) * (C * star C)) := by
    simpa only [W, star_mul, star_star, mul_assoc] using
      (hτ (star C) (Z * star Z * C))
  have hZsa : star (Z * star Z) = Z * star Z := by simp
  have hCsa : star (C * star C) = C * star C := by simp
  have hZpos : 0 ≤ (Z * star Z) ^ 2 := by
    simpa only [hZsa, ← pow_two] using star_mul_self_nonneg (Z * star Z)
  have hCpos : 0 ≤ (C * star C) ^ 2 := by
    simpa only [hCsa, ← pow_two] using star_mul_self_nonneg (C * star C)
  have hgram := PositiveLinearMap.norm_map_star_mul_le τ (Z * star Z) (C * star C)
  rw [hZsa, hCsa, ← hW, hnorm (star_mul_self_nonneg W)] at hgram
  have hgram' : (τ (star W * W)).re ≤
      Real.sqrt (τ ((Z * star Z) ^ 2)).re * Real.sqrt (τ ((C * star C) ^ 2)).re := by
    simpa only [← pow_two, hnorm hZpos, hnorm hCpos] using hgram
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (hideal.trans (mul_le_mul_of_nonneg_left hgram' (sq_nonneg _)))
    (τ.map_nonneg (star_mul_self_nonneg Y)).1)

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

open private DimThree.runBeforeB from D5.S3.Quantum.Analysis.RefinedBMVUniformWords
open private FourCopyGap.sum_words_cyclic FourCopyGap.rotate FourCopyGap.word_count
  FourCopyGap.count_relation FourCopyGap.gaps_card_pos
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

/-- In a tracial algebra, the mean over ordered words with four second
factors equals the mean over their four cyclic gaps. -/
theorem fourthWordMean_eq_gapMean
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (p : ℕ) :
    ((balancedWords p 4).map fun w =>
        τ ((w.map fun letter => if letter then a else b).prod)).sum /
        ((balancedWords p 4).length : ℂ) =
      (∑ g ∈ FourCopyGap.gaps p,
        τ ((a ^ g.1 * b) * (a ^ g.2.1 * b) * (a ^ g.2.2.1 * b) * (a ^ g.2.2.2 * b))) /
        ((FourCopyGap.gaps p).card : ℂ) := by
  let v (w : List Bool) : ℂ := τ ((w.map fun letter => if letter then a else b).prod)
  let F (g : FourCopyGap.Gap) : ℂ :=
    τ ((a ^ g.1 * b) * (a ^ g.2.1 * b) * (a ^ g.2.2.1 * b) * (a ^ g.2.2.2 * b))
  have hcut (i j k l m : ℕ) : v (DimThree.runBeforeB i (DimThree.runBeforeB j
      (DimThree.runBeforeB k (DimThree.runBeforeB l (List.replicate m true))))) =
        F (j, k, l, m + i) := by
    simpa only [v, F, DimThree.runBeforeB, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, Bool.false_eq_true, if_false, if_true,
      List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil,
      mul_one, pow_add, mul_assoc] using
        hτ (a ^ i * b) (a ^ j * b * a ^ k * b * a ^ l * b * a ^ m)
  have hcycle (g : FourCopyGap.Gap) : F (FourCopyGap.rotate g) = F g := by
    simpa only [F, FourCopyGap.rotate, mul_assoc] using
      hτ ((a ^ g.2.1 * b) * (a ^ g.2.2.1 * b) * (a ^ g.2.2.2 * b)) (a ^ g.1 * b)
  have hs := FourCopyGap.sum_words_cyclic p v F hcut hcycle
  have hwNat : (balancedWords p 4).length ≠ 0 := by
    rw [FourCopyGap.word_count]
    exact (Nat.choose_pos (show 4 ≤ p + 4 by omega)).ne'
  have hw : ((balancedWords p 4).length : ℂ) ≠ 0 := by exact_mod_cast hwNat
  have hg : ((FourCopyGap.gaps p).card : ℂ) ≠ 0 :=
    by exact_mod_cast (FourCopyGap.gaps_card_pos p).ne'
  change ((balancedWords p 4).map v).sum / (balancedWords p 4).length =
    (∑ g ∈ FourCopyGap.gaps p, F g) / (FourCopyGap.gaps p).card
  apply (div_eq_div_iff hw hg).mpr
  linear_combination ((FourCopyGap.gaps p).card : ℂ) / 4 * hs -
    (∑ g ∈ FourCopyGap.gaps p, F g) / 4 * FourCopyGap.count_relation p

private theorem weightedFourthTrace (τ : A →P[ℂ] ℂ) (P : ι → A) (B : A)
    (u v w z : ι → ℂ) :
    τ (((∑ i, u i • P i) * B) * ((∑ j, v j • P j) * B) *
      ((∑ k, w k • P k) * B) * ((∑ l, z l • P l) * B)) =
      ∑ i, ∑ j, ∑ k, ∑ l, u i * v j * w k * z l *
        τ ((P i * B) * (P j * B) * (P k * B) * (P l * B)) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul, mul_assoc]
  let f (i j k l : ι) :=
    u i * v j * w k * z l * τ ((P i * B) * (P j * B) * (P k * B) * (P l * B))
  calc
    _ = ∑ l, ∑ k, ∑ j, ∑ i, f i j k l := by
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [f, mul_assoc]
      <;> ring
    _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j k l := by
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j k l := by
      exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ k, ∑ j, f i j k l := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j k l := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f i j k l := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by simp only [f, mul_assoc]

open private FourCopyGap.monomial FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap in
/-- Four moments in a tracial algebra contract against the same deficit
kernel as the finite matrix comparison. This applies to arbitrary finite
spectral families and to positive moment approximants. -/
theorem fourthMomentTrace_defect_eq
    (τ : A →P[ℂ] ℂ) (P : ι → A) (B : A) (x : ι → ℝ) (p : ℕ) :
    (∑ g ∈ FourCopyGap.gaps p,
      τ ((moment x P g.1 * B) * (moment x P g.2.1 * B) *
        (moment x P g.2.2.1 * B) * (moment x P g.2.2.2 * B))) -
      ((FourCopyGap.gaps p).card : ℂ) *
        τ (((∑ i, ((x i ^ ((p : ℝ) / 4) : ℝ) : ℂ) • P i) * B) ^ 4) =
      ∑ i, ∑ j, ∑ k, ∑ l, (FourCopyGap.gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
        τ ((P i * B) * (P j * B) * (P k * B) * (P l * B)) := by
  let walk : (ι → ι → ι → ι → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑ i, ∑ j, ∑ k, ∑ l,
        f i j k l * τ ((P i * B) * (P j * B) * (P k * B) * (P l * B))
      map_add' := by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hgap (g : FourCopyGap.Gap) :
      τ ((moment x P g.1 * B) * (moment x P g.2.1 * B) *
        (moment x P g.2.2.1 * B) * (moment x P g.2.2.2 * B)) =
      walk (fun i j k l ↦ (FourCopyGap.monomial (x i) (x j) (x k) (x l) g : ℂ)) := by
    simpa only [walk, moment, FourCopyGap.monomial, Complex.ofReal_mul, LinearMap.coe_mk,
      AddHom.coe_mk] using weightedFourthTrace τ P B
        (fun i ↦ (x i ^ g.1 : ℝ)) (fun j ↦ (x j ^ g.2.1 : ℝ))
        (fun k ↦ (x k ^ g.2.2.1 : ℝ)) (fun l ↦ (x l ^ g.2.2.2 : ℝ))
  let q (i : ι) : ℂ := (x i ^ ((p : ℝ) / 4) : ℝ)
  have hroot : τ (((∑ i, q i • P i) * B) ^ 4) =
      walk (fun i j k l ↦ (FourCopyGap.balanced p (x i) (x j) (x k) (x l) : ℂ)) := by
    simpa only [q, walk, FourCopyGap.balanced, Complex.ofReal_mul, LinearMap.coe_mk, AddHom.coe_mk,
      pow_succ, pow_zero, one_mul] using weightedFourthTrace τ P B q q q q
  simp_rw [hgap]
  change _ - ((FourCopyGap.gaps p).card : ℂ) * τ (((∑ i, q i • P i) * B) ^ 4) =
    walk (fun i j k l ↦ (FourCopyGap.gapDefect p (x i) (x j) (x k) (x l) : ℂ))
  rw [hroot, ← map_sum]
  change walk _ - ((FourCopyGap.gaps p).card : ℂ) • walk _ = _
  rw [← map_smul, ← map_sub]
  congr 1
  funext i j k l
  simp only [FourCopyGap.gapDefect, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_sum, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]

/-- The actual four-copy word deficit of a finite spectral decomposition
is the contraction of the scalar gap kernel in a tracial algebra. -/
theorem fourthWordDefect_eq_of_orthogonal
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (P : ι → A) (B : A) (x : ι → ℝ) (p : ℕ) [DecidableEq ι]
    (hsum : ∑ i, P i = 1)
    (horth : ∀ i j, P i * P j = if i = j then P i else 0) :
    let A₁ := moment x P 1
    let A₂ := ∑ i, ((x i ^ ((p : ℝ) / 4) : ℝ) : ℂ) • P i
    ((FourCopyGap.gaps p).card : ℂ) *
      (((balancedWords p 4).map fun w =>
        τ ((w.map fun letter => if letter then A₁ else B).prod)).sum /
        ((balancedWords p 4).length : ℂ) - τ ((A₂ * B) ^ 4)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (FourCopyGap.gapDefect p (x i) (x j) (x k) (x l) : ℂ) *
        τ ((P i * B) * (P j * B) * (P k * B) * (P l * B)) := by
  dsimp only
  have hmul (r s : ℕ) : moment x P r * moment x P s = moment x P (r+s) := by
    simp only [moment, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [horth, if_pos rfl, smul_smul, ← Complex.ofReal_mul, ← pow_add, Nat.add_comm]
    · intro i _ hij
      rw [horth, if_neg hij, smul_zero]
    · simp
  have hpow (k : ℕ) : (moment x P 1)^k = moment x P k := by
    induction k with
    | zero => simp [moment, hsum]
    | succ k ih => rw [pow_succ, ih, hmul]
  have hn : ((FourCopyGap.gaps p).card : ℂ) ≠ 0 :=
    by exact_mod_cast (FourCopyGap.gaps_card_pos p).ne'
  rw [fourthWordMean_eq_gapMean τ hτ, mul_sub, mul_div_cancel₀ _ hn]
  simp_rw [hpow]
  exact fourthMomentTrace_defect_eq τ P B x p

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
