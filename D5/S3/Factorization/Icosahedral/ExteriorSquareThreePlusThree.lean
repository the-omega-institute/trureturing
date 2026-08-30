/- GID: D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree
   generality: I
   mirror-B: D5/B/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real exterior square of centered A5 splits into conjugate irreducible threes. -/

import D5.S3.Factorization.Icosahedral.ExteriorSquareRepresentations

/- Library-search audit trail (2026-08-30):
   * Repository and pinned-Mathlib searches found no prior A5 exterior-square split.
   * Pinned Mathlib supplies irreducibility and representation equivalences, reused here.
   * No pinned A5 character table or equal-character converse was found; exact orbit-frame
     certificates prove irreducibility and the quadratic charts prove conjugacy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree

open scoped MatrixGroups MonoidAlgebra
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open Module

set_option maxHeartbeats 2000000 in
-- Kernel reduction evaluates the exact integral quadratic orbit frame.
set_option maxRecDepth 20000 in
private lemma z5_positive_frame_coefficients : ∀ i j a b,
    ∑ g : A5, z5PositiveActionScaled g i a * z5PositiveActionScaled g j b =
      100 * z5FrameLeftScaled i j * z5FrameRightDivThree a b := by
  decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction evaluates the conjugate integral quadratic orbit frame.
set_option maxRecDepth 20000 in
private lemma z5_negative_frame_coefficients : ∀ i j a b,
    ∑ g : A5, z5NegativeActionScaled g i a * z5NegativeActionScaled g j b =
      100 * z5FrameLeftScaled i j * z5FrameRightDivThree a b := by
  decide
private lemma positiveActionMatrix_eq_geometric (g : A5) :
    positiveActionMatrix g = fun i j =>
      (realWedgeActionMatrix g * positiveEigenbasisMatrix) (Fin.natAdd 3 i) j := by
  ext i j
  fin_cases j <;>
    simp [positiveActionMatrix, z5PositiveActionScaled, z5PositiveEigenbasisScaled,
      z5ToReal, realWedgeActionMatrix, positiveEigenbasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

private lemma negativeActionMatrix_eq_geometric (g : A5) :
    negativeActionMatrix g = fun i j =>
      (realWedgeActionMatrix g * negativeEigenbasisMatrix) (Fin.natAdd 3 i) j := by
  ext i j
  fin_cases j <;>
    simp [negativeActionMatrix, z5NegativeActionScaled, z5PositiveActionScaled,
      z5PositiveEigenbasisScaled, z5ToReal, realWedgeActionMatrix,
      negativeEigenbasisMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private lemma positiveActionMatrix_eq_q5 (g : A5) :
    positiveActionMatrix g = (q5PositiveActionMatrix g).map q5ToReal := by
  ext i j
  fin_cases j <;>
    simp [positiveActionMatrix, z5PositiveActionScaled, z5PositiveEigenbasisScaled,
      z5ToReal, q5PositiveActionMatrix, q5PositiveEigenbasisMatrix, q5ToReal,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private lemma negativeActionMatrix_eq_q5 (g : A5) :
    negativeActionMatrix g = (q5PositiveActionMatrix g).map q5ConjugateToReal := by
  ext i j
  fin_cases j <;>
    simp [negativeActionMatrix, z5NegativeActionScaled, z5PositiveActionScaled,
      z5PositiveEigenbasisScaled, z5ToReal, q5PositiveActionMatrix,
      q5PositiveEigenbasisMatrix, q5ConjugateToReal, q5ToReal, Matrix.mul_apply,
      Fin.sum_univ_succ, starRingEnd_apply, QuadraticAlgebra.star_mk] <;>
    ring

set_option maxHeartbeats 2000000 in
-- The finite coordinate normalization expands all four frame indices.
private lemma positive_frame_coefficients (i j a b : Fin 3) :
    ∑ g : A5, positiveActionMatrix g i a * positiveActionMatrix g j b =
      frameLeft i j * frameRight a b := by
  have h := congrArg z5ToReal (z5_positive_frame_coefficients i j a b)
  simp only [map_sum, map_mul, map_ofNat] at h
  calc
    _ = (1 / 100 : ℝ) * ∑ g : A5,
        z5ToReal (z5PositiveActionScaled g i a) *
          z5ToReal (z5PositiveActionScaled g j b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [positiveActionMatrix]
      ring
    _ = _ := by
      rw [h]
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [frameLeft, frameRight, z5FrameLeftScaled,
          z5FrameRightDivThree, z5ToReal]

set_option maxHeartbeats 2000000 in
-- The conjugate finite coordinate normalization expands all four frame indices.
private lemma negative_frame_coefficients (i j a b : Fin 3) :
    ∑ g : A5, negativeActionMatrix g i a * negativeActionMatrix g j b =
      frameLeft i j * frameRight a b := by
  have h := congrArg z5ToReal (z5_negative_frame_coefficients i j a b)
  simp only [map_sum, map_mul, map_ofNat] at h
  calc
    _ = (1 / 100 : ℝ) * ∑ g : A5,
        z5ToReal (z5NegativeActionScaled g i a) *
          z5ToReal (z5NegativeActionScaled g j b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [negativeActionMatrix]
      ring
    _ = _ := by
      rw [h]
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [frameLeft, frameRight, z5FrameLeftScaled,
          z5FrameRightDivThree, z5ToReal]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Reassociating five nested finite sums needs additional elaboration budget.
private lemma sum_first_to_last
    {R I₀ I₁ I₂ I₃ I₄ : Type*} [AddCommMonoid R]
    [Fintype I₀] [Fintype I₁] [Fintype I₂] [Fintype I₃] [Fintype I₄]
    (f : I₀ → I₁ → I₂ → I₃ → I₄ → R) :
    (∑ i₀, ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₄, f i₀ i₁ i₂ i₃ i₄) =
      ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₄, ∑ i₀, f i₀ i₁ i₂ i₃ i₄ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₂ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₃ _
  rw [Finset.sum_comm]

private lemma sum_pair_interchange
    {R I J K L : Type*} [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : I → J → K → L → R) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

private lemma sum_first_to_last_four
    {R I₀ I₁ I₂ I₃ : Type*} [AddCommMonoid R]
    [Fintype I₀] [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (f : I₀ → I₁ → I₂ → I₃ → R) :
    (∑ i₀, ∑ i₁, ∑ i₂, ∑ i₃, f i₀ i₁ i₂ i₃) =
      ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₀, f i₀ i₁ i₂ i₃ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₂ _
  rw [Finset.sum_comm]

private lemma sum_pairs_commute
    {R I J K L : Type*} [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : I → J → K → L → R) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ j, ∑ k, ∑ l, ∑ i, f i j k l := sum_first_to_last_four f
    _ = _ := sum_first_to_last_four fun j k l i => f i j k l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Expanding the squared orbit pairing produces five nested finite sums.
private lemma orbit_frame_identity
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b)
    (u v : Fin 3 → ℝ) :
    ∑ g : A5, (dotProduct u (Matrix.mulVec (B g) v)) ^ 2 =
      dotProduct u (Matrix.mulVec frameLeft u) *
        dotProduct v (Matrix.mulVec frameRight v) := by
  classical
  calc
    _ = ∑ g : A5, ∑ j, ∑ b, ∑ i, ∑ a,
        u i * (B g i a * v a) * (u j * (B g j b * v b)) := by
      simp only [dotProduct, Matrix.mulVec, pow_two, Finset.sum_mul,
        Finset.mul_sum]
    _ = ∑ j, ∑ b, ∑ i, ∑ a, ∑ g : A5,
        u i * (B g i a * v a) * (u j * (B g j b * v b)) :=
      sum_first_to_last fun g j b i a =>
        u i * (B g i a * v a) * (u j * (B g j b * v b))
    _ = ∑ j, ∑ b, ∑ i, ∑ a,
        u i * v a * u j * v b * ∑ g : A5, B g i a * B g j b := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ j, ∑ b, ∑ i, ∑ a,
        u i * v a * u j * v b * (frameLeft i j * frameRight a b) := by
      simp_rw [hB]
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
        u i * v a * u j * v b * (frameLeft i j * frameRight a b) :=
      sum_pair_interchange fun j b i a =>
        u i * v a * u j * v b * (frameLeft i j * frameRight a b)
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
        u a * v i * u b * v j * (frameLeft a b * frameRight i j) :=
      sum_pairs_commute fun i j a b =>
        u i * v a * u j * v b * (frameLeft i j * frameRight a b)
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

private lemma three_coordinates_sq_pos {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    fin_cases i <;> simp_all
  rcases hne with h0 | h1 | h2
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (u 1), sq_nonneg (u 2)]
  · nlinarith [sq_nonneg (u 0), sq_pos_of_ne_zero h1, sq_nonneg (u 2)]
  · nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_pos_of_ne_zero h2]

private lemma frameLeft_pos {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    0 < dotProduct u (Matrix.mulVec frameLeft u) := by
  have hnorm := three_coordinates_sq_pos hu
  norm_num [dotProduct, Matrix.mulVec, frameLeft, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (u 0 - u 1), sq_nonneg (u 0 + u 2),
    sq_nonneg (u 1 - u 2)]

private lemma frameRight_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v (Matrix.mulVec frameRight v) := by
  have hnorm := three_coordinates_sq_pos hv
  norm_num [dotProduct, Matrix.mulVec, frameRight, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 2),
    sq_nonneg (v 1 + v 2)]

private lemma orbit_frame_pos
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b)
    {u v : Fin 3 → ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < ∑ g : A5, (dotProduct u (Matrix.mulVec (B g) v)) ^ 2 := by
  rw [orbit_frame_identity B hB]
  exact mul_pos (frameLeft_pos hu) (frameRight_pos hv)

/-- Standard coordinate dot product as a bilinear form. -/
def coordinateDot : LinearMap.BilinForm ℝ (Fin 3 → ℝ) :=
  dotProductBilin ℝ ℝ

private lemma coordinateDot_refl : coordinateDot.IsRefl := by
  intro x y h
  simpa [coordinateDot, dotProduct_comm] using h

private lemma coordinateDot_nondegenerate : coordinateDot.Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_self_eq_zero.mp (hx x)
  · intro x hx
    exact dotProduct_self_eq_zero.mp (hx x)

/-- Positive eigenbasis parametrization by three real coordinates. -/
noncomputable def positiveParametrization : (Fin 3 → ℝ) →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin positiveEigenbasisMatrix

/-- Negative eigenbasis parametrization by three real coordinates. -/
noncomputable def negativeParametrization : (Fin 3 → ℝ) →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin negativeEigenbasisMatrix

/-- The last three coordinates in the ordered six-dimensional basis. -/
def lastThreeCoordinates : AmbientSpace →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x (Fin.natAdd 3 i)
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp]
private lemma fin_addNat_zero_three :
    Fin.addNat (0 : Fin 3) 3 = (3 : Fin 6) := by
  decide

@[simp]
private lemma fin_addNat_one_three :
    Fin.addNat (1 : Fin 3) 3 = (4 : Fin 6) := by
  decide

@[simp]
private lemma fin_addNat_two_three :
    Fin.addNat (2 : Fin 3) 3 = (5 : Fin 6) := by
  decide

private lemma positiveParametrization_eigen (x : Fin 3 → ℝ) :
    hodgeEndomorphism (positiveParametrization x) =
      Real.sqrt 5 • positiveParametrization x := by
  ext i
  fin_cases i <;>
    norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
      positiveParametrization, positiveEigenbasisMatrix, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

private lemma negativeParametrization_eigen (x : Fin 3 → ℝ) :
    hodgeEndomorphism (negativeParametrization x) =
      -(Real.sqrt 5 • negativeParametrization x) := by
  ext i
  fin_cases i <;>
    norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
      negativeParametrization, negativeEigenbasisMatrix, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

private lemma lastThree_positiveParametrization (x : Fin 3 → ℝ) :
    lastThreeCoordinates (positiveParametrization x) = x := by
  ext i
  fin_cases i <;>
    norm_num [lastThreeCoordinates, positiveParametrization, positiveEigenbasisMatrix,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.natAdd, Fin.addNat]; congr

private lemma lastThree_negativeParametrization (x : Fin 3 → ℝ) :
    lastThreeCoordinates (negativeParametrization x) = x := by
  ext i
  fin_cases i <;>
    norm_num [lastThreeCoordinates, negativeParametrization, negativeEigenbasisMatrix,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.natAdd, Fin.addNat]; congr

private lemma positiveParametrization_reconstructs (x : V₃Space) :
    positiveParametrization (lastThreeCoordinates x.1) = x.1 := by
  have h : hodgeEndomorphism x.1 = Real.sqrt 5 • x.1 := by
    exact sub_eq_zero.mp x.2
  have hsquare : Real.sqrt 5 * Real.sqrt 5 = 5 := by norm_num
  have h0 := congrFun h (0 : Fin 6)
  have h1 := congrFun h (1 : Fin 6)
  have h2 := congrFun h (2 : Fin 6)
  norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two] at h0 h1 h2
  rw [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 4)).succ = (4 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 3)).succ.succ = (5 : Fin 6) by decide] at h0 h1 h2
  have hw0 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h0
  have hw1 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h1
  have hw2 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h2
  have hs0 := congrArg (fun y : ℝ => y * x.1 0) hsquare
  have hs1 := congrArg (fun y : ℝ => y * x.1 1) hsquare
  have hs2 := congrArg (fun y : ℝ => y * x.1 2) hsquare
  ext i
  fin_cases i <;>
    norm_num [positiveParametrization, positiveEigenbasisMatrix, lastThreeCoordinates,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination (norm := ring_nf) 1 / 8 * h1 - 1 / 8 * h2 + 3 / 20 * hw0 +
      1 / 40 * hw1 + 1 / 40 * hw2 + 3 / 20 * hs0 + 1 / 40 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) -1 / 8 * h0 + 1 / 8 * h2 + 1 / 40 * hw0 +
      3 / 20 * hw1 + 1 / 40 * hw2 + 1 / 40 * hs0 + 3 / 20 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) 1 / 8 * h0 - 1 / 8 * h1 + 1 / 40 * hw0 +
      1 / 40 * hw1 + 3 / 20 * hw2 + 1 / 40 * hs0 + 1 / 40 * hs1 +
      3 / 20 * hs2
    apply sub_eq_zero.mpr
    congr
  all_goals congr

private lemma negativeParametrization_reconstructs (x : V₃PrimeSpace) :
    negativeParametrization (lastThreeCoordinates x.1) = x.1 := by
  have h : hodgeEndomorphism x.1 = -(Real.sqrt 5 • x.1) := by
    exact eq_neg_of_add_eq_zero_left x.2
  have hsquare : Real.sqrt 5 * Real.sqrt 5 = 5 := by norm_num
  have h0 := congrFun h (0 : Fin 6)
  have h1 := congrFun h (1 : Fin 6)
  have h2 := congrFun h (2 : Fin 6)
  norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two] at h0 h1 h2
  rw [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 4)).succ = (4 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 3)).succ.succ = (5 : Fin 6) by decide] at h0 h1 h2
  have hw0 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h0
  have hw1 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h1
  have hw2 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h2
  have hs0 := congrArg (fun y : ℝ => y * x.1 0) hsquare
  have hs1 := congrArg (fun y : ℝ => y * x.1 1) hsquare
  have hs2 := congrArg (fun y : ℝ => y * x.1 2) hsquare
  ext i
  fin_cases i <;>
    norm_num [negativeParametrization, negativeEigenbasisMatrix, lastThreeCoordinates,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination (norm := ring_nf) 1 / 8 * h1 - 1 / 8 * h2 - 3 / 20 * hw0 -
      1 / 40 * hw1 - 1 / 40 * hw2 + 3 / 20 * hs0 + 1 / 40 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) -1 / 8 * h0 + 1 / 8 * h2 - 1 / 40 * hw0 -
      3 / 20 * hw1 - 1 / 40 * hw2 + 1 / 40 * hs0 + 3 / 20 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) 1 / 8 * h0 - 1 / 8 * h1 - 1 / 40 * hw0 -
      1 / 40 * hw1 - 3 / 20 * hw2 + 1 / 40 * hs0 + 1 / 40 * hs1 +
      3 / 20 * hs2
    apply sub_eq_zero.mpr
    congr
  all_goals congr

/-- Last-three-coordinate map on the positive eigenspace. -/
noncomputable def V₃CoordinateMap : V₃Space →ₗ[ℝ] (Fin 3 → ℝ) :=
  lastThreeCoordinates.comp V₃Space.subtype

/-- Last-three-coordinate map on the negative eigenspace. -/
noncomputable def V₃PrimeCoordinateMap : V₃PrimeSpace →ₗ[ℝ] (Fin 3 → ℝ) :=
  lastThreeCoordinates.comp V₃PrimeSpace.subtype

/-- Explicit three-coordinate chart for `V₃`. -/
noncomputable def V₃Coordinates : V₃Space ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofBijective V₃CoordinateMap <| by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← positiveParametrization_reconstructs x,
        ← positiveParametrization_reconstructs y]
      exact congrArg positiveParametrization h
    · intro y
      refine ⟨⟨positiveParametrization y, ?_⟩, ?_⟩
      · change hodgeEndomorphism (positiveParametrization y) -
          Real.sqrt 5 • positiveParametrization y = 0
        rw [positiveParametrization_eigen, sub_self]
      · exact lastThree_positiveParametrization y

/-- Explicit three-coordinate chart for `V₃'`. -/
noncomputable def V₃PrimeCoordinates : V₃PrimeSpace ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofBijective V₃PrimeCoordinateMap <| by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← negativeParametrization_reconstructs x,
        ← negativeParametrization_reconstructs y]
      exact congrArg negativeParametrization h
    · intro y
      refine ⟨⟨negativeParametrization y, ?_⟩, ?_⟩
      · change hodgeEndomorphism (negativeParametrization y) +
          Real.sqrt 5 • negativeParametrization y = 0
        rw [negativeParametrization_eigen]
        module
      · exact lastThree_negativeParametrization y

private lemma V₃Coordinates_action (g : A5) (x : V₃Space) :
    V₃Coordinates (V₃ g x) =
      Matrix.mulVec (positiveActionMatrix g) (V₃Coordinates x) := by
  ext i
  change lastThreeCoordinates (coordinateExteriorSquare g x.1) i = _
  rw [coordinateExteriorSquare_apply]
  rw [← positiveParametrization_reconstructs x]
  rw [positiveActionMatrix_eq_geometric]
  change Matrix.mulVec (realWedgeActionMatrix g)
      (Matrix.mulVec positiveEigenbasisMatrix (lastThreeCoordinates x.1))
        (Fin.natAdd 3 i) = _
  rw [Matrix.mulVec_mulVec]
  rfl

private lemma V₃PrimeCoordinates_action (g : A5) (x : V₃PrimeSpace) :
    V₃PrimeCoordinates (V₃Prime g x) =
      Matrix.mulVec (negativeActionMatrix g) (V₃PrimeCoordinates x) := by
  ext i
  change lastThreeCoordinates (coordinateExteriorSquare g x.1) i = _
  rw [coordinateExteriorSquare_apply]
  rw [← negativeParametrization_reconstructs x]
  rw [negativeActionMatrix_eq_geometric]
  change Matrix.mulVec (realWedgeActionMatrix g)
      (Matrix.mulVec negativeEigenbasisMatrix (lastThreeCoordinates x.1))
        (Fin.natAdd 3 i) = _
  rw [Matrix.mulVec_mulVec]
  rfl

/-- The positive icosahedral summand is three-dimensional. -/
theorem V3_finrank : Module.finrank ℝ V₃Space = 3 := by
  rw [LinearEquiv.finrank_eq V₃Coordinates]
  simp

#print axioms V3_finrank

/-- The negative icosahedral summand is three-dimensional. -/
theorem V3Prime_finrank : Module.finrank ℝ V₃PrimeSpace = 3 := by
  rw [LinearEquiv.finrank_eq V₃PrimeCoordinates]
  simp

#print axioms V3Prime_finrank

private lemma irreducible_of_orbit_frame
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (rho : Representation ℝ A5 M)
    (chart : M ≃ₗ[ℝ] (Fin 3 → ℝ))
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hAction : ∀ g x, chart (rho g x) = Matrix.mulVec (B g) (chart x))
    (hFrame : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b) :
    Representation.IsIrreducible rho := by
  letI : Nontrivial M := chart.toEquiv.nontrivial
  letI : Nontrivial (Subrepresentation rho) := ⟨⟨⊥, ⊤, by
    intro h
    have hm := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hm⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSmod : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    exact h
  obtain ⟨v, hvS, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSmod
  let K := S.toSubmodule.map chart.toLinearMap
  have hvcoord : chart v ≠ 0 := by
    intro h
    apply hv
    exact chart.injective (by simpa using h)
  have horth : coordinateDot.orthogonal K = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy0
    have hpos := orbit_frame_pos B hFrame hy0 hvcoord
    have hzero : ∀ g : A5,
        dotProduct y (Matrix.mulVec (B g) (chart v)) = 0 := by
      intro g
      have horbitS := S.apply_mem_toSubmodule g hvS
      have horbitK : chart (rho g v) ∈ K :=
        Submodule.mem_map_of_mem horbitS
      have hortho := hy _ horbitK
      change dotProduct (chart (rho g v)) y = 0 at hortho
      rw [hAction] at hortho
      rw [dotProduct_comm]
      exact hortho
    simp [hzero] at hpos
  have hKtop : K = ⊤ := by
    have hdouble := coordinateDot.orthogonal_orthogonal
      coordinateDot_nondegenerate coordinateDot_refl K
    rw [horth] at hdouble
    simpa using hdouble.symm
  apply Subrepresentation.toSubmodule_injective
  ext x
  constructor
  · intro
    trivial
  · intro
    have hxK : chart x ∈ K := by
      rw [hKtop]
      trivial
    obtain ⟨y, hyS, hy⟩ := Submodule.mem_map.mp hxK
    have hyx : y = x := chart.injective hy
    simpa [hyx] using hyS

/-- The positive three-dimensional icosahedral representation is irreducible. -/
theorem V3_irreducible : Representation.IsIrreducible V₃ :=
  irreducible_of_orbit_frame V₃ V₃Coordinates positiveActionMatrix
    V₃Coordinates_action positive_frame_coefficients

#print axioms V3_irreducible

/-- The negative three-dimensional icosahedral representation is irreducible. -/
theorem V3Prime_irreducible : Representation.IsIrreducible V₃Prime :=
  irreducible_of_orbit_frame V₃Prime V₃PrimeCoordinates negativeActionMatrix
    V₃PrimeCoordinates_action negative_frame_coefficients

#print axioms V3Prime_irreducible

/-- The two irreducible threes are the conjugate real embeddings of one exact action. -/
theorem V3_V3Prime_galois_conjugate :
    RepresentationsAreQ5GaloisConjugate
      V₃ V₃Prime V₃Coordinates V₃PrimeCoordinates := by
  refine ⟨q5PositiveActionMatrix, ?_, ?_⟩
  · intro g x
    rw [V₃Coordinates_action, positiveActionMatrix_eq_q5]
  · intro g x
    rw [V₃PrimeCoordinates_action, negativeActionMatrix_eq_q5]

#print axioms V3_V3Prime_galois_conjugate
/-- The exterior square of the centered `A₅` representation splits into the two threes. -/
theorem exteriorSquareV4_equiv_V3_prod_V3Prime :
    Nonempty (exteriorSquareV₄.Equiv (V₃.prod V₃Prime)) :=
  ⟨exteriorSquareDecomposition⟩

#print axioms exteriorSquareV4_equiv_V3_prod_V3Prime

/-- The full fivefold second-order decomposition theorem, including its source qualifiers. -/
theorem exteriorSquareV4_three_plus_three :
    Nonempty (exteriorSquareV₄.Equiv (V₃.prod V₃Prime)) ∧
      Module.finrank ℝ V₃Space = 3 ∧
      Module.finrank ℝ V₃PrimeSpace = 3 ∧
      Representation.IsIrreducible V₃ ∧
      Representation.IsIrreducible V₃Prime ∧
      RepresentationsAreQ5GaloisConjugate
        V₃ V₃Prime V₃Coordinates V₃PrimeCoordinates := by
  exact ⟨exteriorSquareV4_equiv_V3_prod_V3Prime, V3_finrank,
    V3Prime_finrank, V3_irreducible, V3Prime_irreducible,
    V3_V3Prime_galois_conjugate⟩

#print axioms exteriorSquareV4_three_plus_three

end D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree
