/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Analytic Hessian and determinant-square structure of regular tournaments. -/

/-
The utility classification is none: the objects and intended conclusion are
general theorems over arbitrary finite tournaments, not finite computations.
This is an unfinished implementation of Conjecture 6; no resolution is asserted.
Definitions have proof_shape bind-only (definition), escape_witness none.
Frozen D5 dependencies: none (Mathlib-only imports).
Module admission_basis: none; WIP, the settling result has not been proved.
The definitions and all helpers have proof_shape: bind-only; escape_witness: none.
Helper consumers:
  skewDiag -> shiftedDetNeZero, shiftedDetPureImaginary
  skewNormLe -> shiftedDetNeZero
  shiftedDetNeZero -> algebraicRatioRational
  shiftedDetPureImaginary -> imaginaryShiftIntegral
  imaginaryShiftIntegral -> algebraicRatioRational
  algebraicRatioRational -> algebraicSquareIdentity
  regularOdd -> regularAlgebraicSquare
  algebraicSquareIdentity -> regularAlgebraicSquare
  regularAlgebraicSquare -> none (unfinished analytic bridge).
This is a staged source checkpoint, not an admissible completed settlement.
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # The tournament determinant and its analytic Hessian -/

public section

open scoped Topology
open Matrix Filter

namespace D5.S3.Combinatorics.WormaldTournamentHessian.Result

/-- An irreflexive orientation of every pair, with constant out-degree. -/
def IsRegularTournament {d : ℕ} (A : Fin d → Fin d → Bool) : Prop :=
  (∀ i, A i i = false) ∧
  (∀ i j, i ≠ j → (A i j = true ↔ A j i = false)) ∧
  ∃ r : ℕ, ∀ i, ∑ j, (if A i j then 1 else 0) = r

/-- The integral adjacency matrix. -/
def adjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => if A i j then 1 else 0

/-- The integral skew adjacency matrix. -/
def skewAdjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  adjacency A - (adjacency A).transpose

/-- The point at which the implicit equation is expanded. -/
noncomputable def z (d : ℕ) : ℂ := 2 / d

/-- The determinant polynomial in the paper. -/
noncomputable def K {d : ℕ} (A : Fin d → Fin d → Bool) (y : Fin d → ℂ) : ℂ :=
  (1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
    (adjacency A).map (Int.castRingHom ℂ)) * diagonal y).det

/-- Append the last coordinate, retaining the paper's vertex order. -/
def appendLast {d : ℕ} (y : Fin (d - 1) → ℂ) (t : ℂ) : Fin d → ℂ :=
  fun i => @Fin.snoc (d - 1) (fun _ => ℂ) y t
    (Fin.ofNat (d - 1 + 1) i.val)

/-- The local solution has the stated value, complex C² regularity and equation germ. -/
def IsLocalSolution {d : ℕ} (A : Fin d → Fin d → Bool)
    (h : (Fin (d - 1) → ℂ) → ℂ) : Prop :=
  h (fun _ => z d) = z d ∧
  ContDiffAt ℂ 2 h (fun _ => z d) ∧
  ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), K A (appendLast y (h y)) = 0

/-- The complex-valued phase function on real angular coordinates. -/
noncomputable def phase {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ)
    (θ : Fin (d - 1) → ℝ) : ℂ :=
  Complex.log (h (fun j => z d * Complex.exp (Complex.I * θ j)))

/-- Second real Fréchet derivatives, evaluated in the two coordinate directions. -/
noncomputable def hessian {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ :=
  fun j k => fderiv ℝ (fun θ => fderiv ℝ (phase h) θ (Pi.single j 1)) 0 (Pi.single k 1)

/-- Wormald's Hessian determinant. -/
noncomputable def calH {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) : ℂ :=
  (hessian h).det

/-- Conjecture 6, including existence and independence of the local solution. -/
def claim : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ A : Fin d → Fin d → Bool, IsRegularTournament A →
    (∃ h, IsLocalSolution A h) ∧
    ∀ h, IsLocalSolution A h → calH h ≠ 0 ∧ ∃ q : ℚ, (d : ℂ) / calH h = (q : ℂ) ^ 2

private theorem skewDiag {d : ℕ} (A : Fin d → Fin d → Bool) (i : Fin d) :
    skewAdjacency A i i = 0 := by simp [skewAdjacency]

private theorem skewNormLe {d : ℕ} (A : Fin d → Fin d → Bool) (i j : Fin d) :
    ‖(skewAdjacency A i j : ℂ)‖ ≤ 1 := by
  simp only [skewAdjacency, Matrix.sub_apply, Matrix.transpose_apply, adjacency]
  split <;> split <;> norm_num

private theorem shiftedDetNeZero {d : ℕ} (A : Fin d → Fin d → Bool) (c : ℂ)
    (hc : ‖c‖ = d) :
    ((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i,
      ‖((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1) i j‖) ≤ (d - 1 : ℕ) := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using
          skewNormLe A i j
      _ = _ := by simp
  have hdiag : ((skewAdjacency A).map (Int.castRingHom ℂ) + c • 1) i i = c := by
    simp [skewDiag]
  rw [hdiag, hc]
  have hd : 0 < d := Fin.pos i
  exact lt_of_le_of_lt hsum (by exact_mod_cast Nat.sub_lt hd (by omega : 0 < 1))

private theorem shiftedDetPureImaginary {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : Odd d) :
    (((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det).re = 0 := by
  let M := (skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1
  have hstar : M.conjTranspose = -M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.conjTranspose_apply, skewDiag]
    · simp [M, Matrix.conjTranspose_apply, skewAdjacency, adjacency,
        hij, Ne.symm hij]
  have heq : star M.det = -M.det := by
    rw [← Matrix.det_conjTranspose, hstar, Matrix.det_neg]
    simp only [Fintype.card_fin, hd.neg_one_pow, neg_one_mul]
  have hr := congrArg Complex.re heq
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  linarith

private theorem imaginaryShiftIntegral {d : ℕ} (A : Fin d → Fin d → Bool) (hd : Odd d) :
    ∃ b : ℤ, ((skewAdjacency A).map (Int.castRingHom ℂ) +
      (Complex.I * d) • 1).det = (b : ℂ) * Complex.I := by
  let Z : Matrix (Fin d) (Fin d) GaussianInt := fun i j =>
    ⟨skewAdjacency A i j, if i = j then (d : ℤ) else 0⟩
  have hm : Z.map GaussianInt.toComplex =
      (skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1 := by
    ext i j
    change GaussianInt.toComplex ⟨skewAdjacency A i j,
      if i = j then (d : ℤ) else 0⟩ = _
    by_cases hij : i = j
    · simp [GaussianInt.toComplex_def', hij, Matrix.smul_apply]
      ring
    · simp [GaussianInt.toComplex_def', hij, Matrix.smul_apply]
  have hdet : (Z.det : ℂ) =
      ((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det := by
    rw [RingHom.map_det]
    change (Z.map GaussianInt.toComplex).det = _
    rw [hm]
  have hr := shiftedDetPureImaginary A hd
  rw [← hdet] at hr
  have hre : Z.det.re = 0 := by
    have hr' : (Z.det.re : ℝ) = 0 := (GaussianInt.intCast_re Z.det).trans hr
    exact_mod_cast hr'
  refine ⟨Z.det.im, ?_⟩
  rw [← hdet, GaussianInt.toComplex_def, hre]
  simp

private theorem algebraicRatioRational {d : ℕ} (A : Fin d → Fin d → Bool) (hd : Odd d) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ)).det /
        (((skewAdjacency A).map (Int.castRingHom ℂ) + (Complex.I * d) • 1).det /
          Complex.I)) = (q : ℂ) := by
  obtain ⟨b, hb⟩ := imaginaryShiftIntegral A hd
  have hI : ‖Complex.I * (d : ℂ)‖ = (d : ℝ) := by simp
  have hD : ‖(d : ℂ)‖ = (d : ℝ) := by simp
  have hb0 : b ≠ 0 := by
    intro h
    have := shiftedDetNeZero A (Complex.I * d) hI
    exact this (by simpa only [h, Int.cast_zero, zero_mul] using hb)
  let a : ℤ := ((d : ℤ) • (1 : Matrix (Fin d) (Fin d) ℤ) + skewAdjacency A).det
  have ha : (a : ℂ) = ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (skewAdjacency A).map (Int.castRingHom ℂ)).det := by
    dsimp [a]
    rw [Int.cast_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, Matrix.natCast_apply, hij]
  have ha0 : a ≠ 0 := by
    intro h
    have hn := shiftedDetNeZero A (d : ℂ) hD
    rw [add_comm] at hn
    rw [← ha, h, Int.cast_zero] at hn
    exact hn rfl
  refine ⟨(a : ℚ) / b, div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hb0), ?_⟩
  rw [← ha, hb]
  push_cast
  rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]

private theorem regularOdd {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : Odd d := by
  obtain ⟨hdiag, hdir, r, hr⟩ := hA
  have hpair : ∀ i j, adjacency A i j + adjacency A j i =
      (if i = j then 0 else 1 : ℤ) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [adjacency, hdiag]
    · have h := hdir i j hij
      cases hai : A i j <;> cases haj : A j i <;> simp_all [adjacency]
  have hrow : ∀ i, ∑ j, adjacency A i j = (r : ℤ) := by
    intro i
    have h := hr i
    simp only [adjacency]
    exact_mod_cast h
  have hswap : (∑ i : Fin d, ∑ j : Fin d, adjacency A j i) =
      (∑ i : Fin d, ∑ j : Fin d, adjacency A i j) := Finset.sum_comm
  have hpairsum : ∀ i : Fin d, (∑ j : Fin d, (if i = j then 0 else 1 : ℤ)) = d - 1 := by
    intro i
    calc
      _ = ∑ j : Fin d, (1 - (if i = j then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro j _
        split <;> simp_all
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hcount : (d : ℤ) * (2 * r) = d * (d - 1) := by
    calc
      (d : ℤ) * (2 * r) =
          (∑ i : Fin d, ∑ j : Fin d, adjacency A i j) +
            (∑ i : Fin d, ∑ j : Fin d, adjacency A j i) := by
              rw [hswap]
              simp_rw [hrow]
              simp
              ring
      _ = ∑ i : Fin d, ∑ j : Fin d, (adjacency A i j + adjacency A j i) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ i : Fin d, ∑ j : Fin d, (if i = j then 0 else 1 : ℤ) := by simp_rw [hpair]
      _ = d * (d - 1) := by simp_rw [hpairsum]; simp; ring
  have heq : (d : ℤ) = 2 * r + 1 := by
    have hpos : (0 : ℤ) < d := by omega
    nlinarith
  refine ⟨r, ?_⟩
  exact_mod_cast heq


private theorem algebraicSquareIdentity {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : Odd d) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det) = (q : ℂ)^2 := by
  let S := (skewAdjacency A).map (Int.castRingHom ℂ)
  have hst : S.transpose = -S := by
    ext i j
    simp [S, skewAdjacency, adjacency]
  have hreal : ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - S).det =
      ((d : ℂ) • 1 + S).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, hst, sub_neg_eq_add]
  have himag : (S - (Complex.I * d) • 1).det =
      -(S + (Complex.I * d) • 1).det := by
    have heq : S - (Complex.I * d) • 1 = -(S + (Complex.I * d) • 1).transpose := by
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hst]
      abel
    rw [heq, Matrix.det_neg, Matrix.det_transpose]
    simp [hd.neg_one_pow]
  have hm : ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + S) *
      ((d : ℂ) • 1 - S) = (d : ℂ)^2 • 1 - S*S := by
    simp [add_mul, mul_sub, smul_smul, pow_two]
    abel
  have hp : (S + (Complex.I * d) • 1) * (S - (Complex.I * d) • 1) =
      (d : ℂ)^2 • 1 + S*S := by
    simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      smul_smul]
    have hc : (Complex.I * (d : ℂ)) * (Complex.I * d) = -(d : ℂ)^2 := by
      calc
        _ = Complex.I^2 * (d : ℂ)^2 := by ring
        _ = _ := by simp
    rw [hc, neg_smul]
    abel
  have hnum : ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) - S*S).det =
      (((d : ℂ) • 1 + S).det)^2 := by
    rw [← hm, Matrix.det_mul, hreal, pow_two]
  have hden : ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) + S*S).det =
      ((S + (Complex.I*d) • 1).det / Complex.I)^2 := by
    rw [← hp, Matrix.det_mul, himag, div_pow, Complex.I_sq]
    ring
  obtain ⟨q, hq, heq⟩ := algebraicRatioRational A hd
  refine ⟨q, hq, ?_⟩
  change ((d : ℂ)^2 • 1 - S*S).det / ((d : ℂ)^2 • 1 + S*S).det = _
  rw [hnum, hden, ← div_pow]
  exact congrArg (fun x : ℂ => x^2) heq

private theorem regularAlgebraicSquare {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∃ q : ℚ, q ≠ 0 ∧
      (((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det) = (q : ℂ)^2 :=
  algebraicSquareIdentity A (regularOdd A hd hA)

end D5.S3.Combinatorics.WormaldTournamentHessian.Result
