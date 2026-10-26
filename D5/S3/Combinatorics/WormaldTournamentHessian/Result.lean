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
  regularDegree -> regularOdd, determinantAtBase
  regularOdd -> regularAlgebraicSquare
  algebraicSquareIdentity -> regularAlgebraicSquare
  regularAlgebraicSquare -> none (unfinished analytic bridge)
  determinantAtBase -> localSolutionOfInvertible
  polynomialSmooth -> localSolutionOfInvertible
  localSolutionOfInvertible -> none (nonzero derivative not yet proved).
This is a staged source checkpoint, not an admissible completed settlement.
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # The tournament determinant and its analytic Hessian -/

public section

open scoped Topology ContDiff
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

private theorem regularDegree {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : ∃ r : ℕ, d = 2 * r + 1 ∧ ∀ i, ∑ j, adjacency A i j = (r : ℤ) := by
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
  refine ⟨r, ?_, hrow⟩
  exact_mod_cast heq


private theorem regularOdd {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : Odd d := by
  obtain ⟨r, hdr, _⟩ := regularDegree A hd hA
  exact ⟨r, hdr⟩

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

private theorem determinantAtBase {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : K A (fun _ => z d) = 0 := by
  obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hrow : ∀ i, ∑ j, ((adjacency A i j : ℤ) : ℂ) = r := by
    intro i
    exact_mod_cast hr i
  have hker : (1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) * diagonal (fun _ => z d)) *ᵥ
        (fun _ => (1 : ℂ)) = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Matrix.map_apply, Pi.zero_apply]
    have hrow' : (∑ j, (Int.castRingHom ℂ) (adjacency A i j)) = (r : ℂ) := hrow i
    simp only [hrow']
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold z
    have hdc : (d : ℂ) = 2 * r + 1 := by exact_mod_cast hdr
    field_simp
    linear_combination hdc
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
    (i := ⟨0, by omega⟩) (by simp)

private theorem polynomialSmooth {d : ℕ} (A : Fin d → Fin d → Bool) :
    ContDiff ℂ 2 (K A) := by
  classical
  unfold K
  simp only [Matrix.det_apply, Matrix.sub_apply, Matrix.mul_diagonal]
  fun_prop

private theorem localSolutionOfInvertible {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (hi : (fderiv ℂ
      (fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2))
      ((fun _ => z d), z d) ∘L
        ContinuousLinearMap.inr ℂ (Fin (d-1) → ℂ) ℂ).IsInvertible) :
    ∃ h, IsLocalSolution A h := by
  have happ : appendLast (fun _ : Fin (d-1) => z d) (z d) = (fun _ => z d) := by
    funext i
    simp [appendLast, Fin.snoc]
  have hK : K A (appendLast (fun _ => z d) (z d)) = 0 := by
    rw [happ]
    exact determinantAtBase A hd hA
  have hc : ContDiffAt ℂ 2
      (fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2))
      ((fun _ => z d), z d) := by
    apply (polynomialSmooth A).contDiffAt.comp
    apply contDiffAt_pi.2
    intro i
    unfold appendLast Fin.snoc
    split_ifs <;> simp only [cast_eq] <;> fun_prop
  have hn : (2 : ℕ∞ω) ≠ 0 := by norm_num
  refine ⟨hc.implicitFunction hn hi, hc.implicitFunction_apply_self hn hi,
    hc.contDiffAt_implicitFunction hn hi, ?_⟩
  have he := hc.eventually_apply_implicitFunction hn hi
  simpa only [hK] using he

private theorem det_const_perturb (n : ℕ) (c : ℂ) :
    (1 + (Matrix.of (fun _ _ : Fin n => c)) : Matrix (Fin n) (Fin n) ℂ).det = 1 + n * c := by
  have he : (Matrix.of (fun _ _ : Fin n => c)) =
      Matrix.replicateCol Unit (fun _ : Fin n => c) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]

private theorem det_projection_update (n : ℕ) (l : Fin (n+1)) (v : Fin (n+1) → ℂ) :
    ((1 - (Matrix.of (fun _ _ : Fin (n+1) => (1 / (n+1 : ℂ)))) :
      Matrix (Fin (n+1)) (Fin (n+1)) ℂ).updateCol l v).det =
      (∑ i, v i) / (n+1 : ℂ) := by
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    (1 - (Matrix.of (fun _ _ : Fin (n+1) => (1 / (n+1 : ℂ))))).updateCol l v
  have hc : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hcol : ∀ j ≠ l, ∑ i, M i j = 0 := by
    intro j hj
    simp [M, Matrix.updateCol_apply, hj, Matrix.sub_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, hc]
  have hh := Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
    M l l hcol
  have hminor : M.submatrix l.succAbove l.succAbove =
      1 + (Matrix.of (fun _ _ : Fin n => -(1 / (n+1 : ℂ)))) := by
    ext i j
    simp [M, Matrix.submatrix_apply, Matrix.updateCol_apply,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Fin.succAbove_ne,
      Fin.succAbove_right_inj, sub_eq_add_neg]
  have hsign : (-1 : ℂ) ^ ((l : ℕ) + (l : ℕ)) = 1 := by
    exact Even.neg_one_pow ⟨l.val, rfl⟩
  dsimp [M] at hh ⊢
  rw [hsign, one_mul, hminor, det_const_perturb] at hh
  simp only [Matrix.updateCol_self] at hh
  rw [hh]
  field_simp
  ring

private theorem det_doubly_stochastic_cofactor (n : ℕ) (l : Fin (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hdet : A.det ≠ 0)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    ((A - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).updateCol l
      (Pi.single l 1)).det = A.det / (n+1 : ℂ) := by
  let P : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    1 - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))
  let v : Fin (n+1) → ℂ := A⁻¹ *ᵥ Pi.single l 1
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hv : A *ᵥ v = Pi.single l 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hsum : ∑ i, v i = 1 := by
    calc
      _ = ∑ i, (A *ᵥ v) i := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hcol, one_mul]
      _ = 1 := by rw [hv]; simp
  have hAP : A * P = A - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [← Finset.sum_mul, hrow, one_mul]
  have he := Matrix.mul_updateCol A P l v
  rw [hv, hAP] at he
  rw [← he, Matrix.det_mul]
  rw [show P = 1 - (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) from rfl,
    det_projection_update, hsum]
  ring

private theorem cofactor_eq_of_zero_sums (n : ℕ) (l : Fin (n+1))
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hdet : (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det ≠ 0)
    (hrow : ∀ i, ∑ j, B i j = 0) (hcol : ∀ j, ∑ i, B i j = 0) :
    (B.updateCol l (Pi.single l 1)).det =
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det / (n+1 : ℂ) := by
  have hc : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have ha : ∀ i, (∑ j : Fin (n+1),
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) i j) = 1 := by
    intro i
    simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib, hrow, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hb : ∀ j, (∑ i : Fin (n+1),
      (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) i j) = 1 := by
    intro j
    simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib, hcol, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  simpa only [add_sub_cancel_right] using
    det_doubly_stochastic_cofactor n l (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))) hdet ha hb

private theorem regularColumnSlopeValue {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) (l : Fin d) :
    ((1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) * diagonal (fun _ => z d)).updateCol l
        (fun i => ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) i l)).det =
      (((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det) / (2 * (d : ℂ)^d) := by
  cases d with
  | zero => omega
  | succ n =>
    obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
    let C : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      (1 / 2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
    let B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      1 - C * diagonal (fun _ => z (n+1))
    let S := (skewAdjacency A).map (Int.castRingHom ℂ)
    have hd0 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hdc : (n+1 : ℂ) = 2 * r + 1 := by exact_mod_cast hdr
    have hrowC : ∀ i, ∑ j, C i j = 1 / 2 + (r : ℂ) := by
      intro i
      have hi : (∑ j, ((adjacency A i j : ℤ) : ℂ)) = r := by exact_mod_cast hr i
      simp only [C, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.map_apply]
      simpa [Matrix.one_apply] using congrArg (fun x : ℂ => 1 / 2 + x) hi
    have hpair : ∀ i j, C i j + C j i = 1 := by
      intro i j
      by_cases hij : i = j
      · subst j
        norm_num [C, adjacency, hA.1]
      · have h := hA.2.1 i j hij
        cases hai : A i j <;> cases haj : A j i <;>
          simp_all [C, Matrix.one_apply, adjacency, hij, Ne.symm hij]
    have hcolC : ∀ j, ∑ i, C i j = 1 / 2 + (r : ℂ) := by
      intro j
      have hh : (∑ i, C i j) + (∑ i, C j i) = (n+1 : ℂ) := by
        rw [← Finset.sum_add_distrib]
        simp_rw [hpair]
        simp
      rw [hrowC] at hh
      linear_combination hh + hdc
    have hnorm : (1 / 2 + (r : ℂ)) * z (n+1) = 1 := by
      unfold z
      push_cast
      field_simp
      linear_combination -hdc
    have hrowB : ∀ i, ∑ j, B i j = 0 := by
      intro i
      simp only [B, Matrix.sub_apply, Matrix.mul_diagonal, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hrowC, hnorm]
      simp [Matrix.one_apply]
    have hcolB : ∀ j, ∑ i, B i j = 0 := by
      intro j
      simp only [B, Matrix.sub_apply, Matrix.mul_diagonal, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hcolC, hnorm]
      simp [Matrix.one_apply]
    have htwo : ∀ i j, 2 * C i j = 1 + S i j := by
      intro i j
      have hh : C i j - C j i = S i j := by
        simp only [C, S, skewAdjacency, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul, Matrix.map_apply, Matrix.sub_apply, Matrix.transpose_apply,
          map_sub]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · simp [hij]
        · simp [hij, Ne.symm hij]
      linear_combination hpair i j + hh
    have hmat : B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ))) =
        (1 / (n+1 : ℂ)) • ((n+1 : ℂ) • 1 - S) := by
      ext i j
      simp only [B, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.smul_apply, smul_eq_mul]
      unfold z
      push_cast
      field_simp
      linear_combination -(htwo i j)
    have ht : (S + (n+1 : ℂ) • 1).transpose = (n+1 : ℂ) • 1 - S := by
      have hs : S.transpose = -S := by
        ext i j
        simp [S, skewAdjacency, adjacency]
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hs]
      abel
    have hdetQ : ((n+1 : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S).det ≠ 0 := by
      rw [← ht, Matrix.det_transpose]
      simpa only [Nat.cast_add, Nat.cast_one] using
        shiftedDetNeZero A ((n+1 : ℕ) : ℂ) (Complex.norm_natCast (n+1))
    have hdetB : (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det ≠ 0 := by
      rw [hmat, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (div_ne_zero one_ne_zero hd0)) hdetQ
    have hcof := cofactor_eq_of_zero_sums n l B hdetB hrowB hcolB
    have hB : B.det = 0 := determinantAtBase A hd hA
    have he : (Pi.single l 1 : Fin (n+1) → ℂ) =
        (fun i => B i l) + z (n+1) • (fun i => C i l) := by
      ext i
      simp [B, Matrix.mul_diagonal, Matrix.one_apply, Pi.single_apply, eq_comm] <;> ring
    have hlinear : (B.updateCol l (Pi.single l 1)).det =
        z (n+1) * (B.updateCol l (fun i => C i l)).det := by
      rw [he, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
        Matrix.updateCol_eq_self, hB, zero_add]
    have hz0 : z (n+1) ≠ 0 := by
      simpa only [z, Nat.cast_add, Nat.cast_one] using
        div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hd0
    simp only [Nat.cast_add, Nat.cast_one]
    change (B.updateCol l (fun i => C i l)).det =
      (((n+1 : ℂ) • 1 - S).det) / (2 * (n+1 : ℂ)^(n+1))
    apply (mul_left_cancel₀ hz0)
    calc
      z (n+1) * (B.updateCol l (fun i => C i l)).det =
          (B.updateCol l (Pi.single l 1)).det := hlinear.symm
      _ = (B + (Matrix.of (fun _ _ : Fin (n+1) => 1 / (n+1 : ℂ)))).det / (n+1 : ℂ) := hcof
      _ = z (n+1) * (((n+1 : ℂ) • 1 - S).det /
          (2 * (n+1 : ℂ) ^ (n+1))) := by
        rw [hmat, Matrix.det_smul, Fintype.card_fin, one_div_pow]
        unfold z
        push_cast
        field_simp
        <;> ring


private noncomputable def appendLastLinear (d : ℕ) :
    ((Fin (d-1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    @Fin.snoc (d-1) (fun _ => ((Fin (d-1) → ℂ) × ℂ) →L[ℂ] ℂ)
      (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _))
      (ContinuousLinearMap.snd ℂ _ _) (Fin.ofNat (d-1+1) i.val)

private theorem appendLastLinearApply {d : ℕ} (p : (Fin (d-1) → ℂ) × ℂ) :
    appendLastLinear d p = appendLast p.1 p.2 := by
  ext i
  simp only [appendLastLinear, ContinuousLinearMap.pi_apply, appendLast]
  unfold Fin.snoc
  split_ifs <;> rfl

private theorem appendLast_update {d : ℕ} (hd : 1 ≤ d) (t : ℂ) :
    appendLast (fun _ => z d) t =
      Function.update (fun _ => z d) (⟨d-1, by omega⟩ : Fin d) t := by
  classical
  ext i
  have hd' : d - 1 + 1 = d := by omega
  have hi : i.val < d-1+1 := by omega
  by_cases h : i.val < d-1
  · have hn : i ≠ (⟨d-1, by omega⟩ : Fin d) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = d-1 at hv
      omega
    simp [appendLast, Fin.snoc, Fin.ofNat, Nat.mod_eq_of_lt hi, h, hn]
  · have he : i = (⟨d-1, by omega⟩ : Fin d) := by
      apply Fin.ext
      change i.val = d-1
      omega
    rw [he]
    simp [appendLast, Fin.snoc, Fin.ofNat, Nat.mod_eq_of_lt hi]

private theorem determinant_column_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (j : n) (u v : n → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => (B.updateCol j (u + s • v)).det)
      (B.updateCol j v).det t := by
  simp_rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  simpa using ((hasDerivAt_id t).mul_const (B.updateCol j v).det).const_add
    (B.updateCol j u).det

private theorem K_coordinate_deriv {d : ℕ} (A : Fin d → Fin d → Bool)
    (y : Fin d → ℂ) (j : Fin d) (t : ℂ) :
    HasDerivAt (fun s : ℂ => K A (Function.update y j s))
      (-((1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) * diagonal y).updateCol j
        (fun i => ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
          (adjacency A).map (Int.castRingHom ℂ)) i j)).det) t := by
  let C : Matrix (Fin d) (Fin d) ℂ :=
    (1 / 2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
  let B : Matrix (Fin d) (Fin d) ℂ := 1 - C * diagonal y
  have he (s : ℂ) : K A (Function.update y j s) =
      (B.updateCol j ((fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j) +
        s • (fun i => -C i j))).det := by
    change (1 - C * diagonal (Function.update y j s)).det = _
    congr 1
    ext i k
    by_cases hk : k = j
    · subst k
      simp [K, B, Matrix.updateCol, Matrix.mul_diagonal, C]
      ring
    · simp [K, B, Matrix.updateCol, Matrix.mul_diagonal, hk, Ne.symm hk, C]
  simp_rw [he]
  convert determinant_column_deriv B j (fun i => (1 : Matrix (Fin d) (Fin d) ℂ) i j)
    (fun i => -C i j) t using 1
  symm
  have hneg : (fun i => -C i j) = (-1 : ℂ) • (fun i => C i j) := by ext i; simp
  rw [hneg, Matrix.det_updateCol_smul]
  simp [B, C]

private theorem scalar_map_invertible (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) :
    L.IsInvertible := by
  have hx (x : ℂ) : L x = x * L 1 := by simpa using L.map_smul x 1
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [hx ((L 1)⁻¹ * x)]
    field_simp [hL]
    <;> ring
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [hx x]
    field_simp [hL]
    <;> ring

private theorem scalar_partial_invertible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E × ℂ → ℂ) (y : E) (t c : ℂ)
    (hF : DifferentiableAt ℂ F (y,t))
    (hc : HasDerivAt (fun s : ℂ => F (y,s)) c t) (hc0 : c ≠ 0) :
    (fderiv ℂ F (y,t) ∘L ContinuousLinearMap.inr ℂ E ℂ).IsInvertible := by
  apply scalar_map_invertible
  have he := hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t))
  have hu := he.unique hc
  simpa using hu.trans_ne hc0

private theorem det_rank_one_sub {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q.det ≠ 0) :
    (Q - Matrix.of (fun _ _ => 1)).det =
      Q.det * (1 - ∑ i, ∑ j, Q⁻¹ i j) := by
  have he : (Q - Matrix.of (fun _ _ => 1)) = Q +
      Matrix.replicateCol Unit (fun _ : Fin d => (-1 : ℂ)) *
        Matrix.replicateRow Unit (fun _ : Fin d => (1 : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [he, Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hQ)]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, Finset.sum_neg_distrib, Finset.sum_comm, sub_eq_add_neg]

private theorem tournamentCoefficientIdentity {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) :
    (2 : ℂ) • ((1/2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) =
        Matrix.of (fun _ _ => 1) + (skewAdjacency A).map (Int.castRingHom ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, hA.1, adjacency, skewAdjacency]
  · have h := hA.2.1 i j hij
    cases hai : A i j <;> cases haj : A j i <;>
      simp_all [Matrix.smul_apply, Matrix.one_apply, adjacency, skewAdjacency] <;> norm_num

private theorem K_resolvent_factorization {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) (y : Fin d → ℂ) (hy : ∀ j, y j ≠ 0)
    (hQ : (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    K A y = (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det *
      (1 - ∑ i, ∑ j, (diagonal (fun j => 2 / y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j) * ∏ j, (y j / 2) := by
  let C : Matrix (Fin d) (Fin d) ℂ :=
    (1/2 : ℂ) • 1 + (adjacency A).map (Int.castRingHom ℂ)
  let Q := diagonal (fun j => 2 / y j) -
    (skewAdjacency A).map (Int.castRingHom ℂ)
  have hf : 1 - C * diagonal y =
      (diagonal (fun j => 2 / y j) - (2 : ℂ) • C) * diagonal (fun j => y j / 2) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Matrix.one_apply_eq]
      field_simp [hy i]
      <;> ring
    · simp only [hij, ite_false, Matrix.one_apply_ne hij]
      ring
  have hc : (2 : ℂ) • C = Matrix.of (fun _ _ => 1) +
      (skewAdjacency A).map (Int.castRingHom ℂ) := tournamentCoefficientIdentity A hA
  change (1 - C * diagonal y).det = _
  rw [hf, hc]
  have he : diagonal (fun j => 2 / y j) -
      (Matrix.of (fun _ _ => 1) + (skewAdjacency A).map (Int.castRingHom ℂ)) =
        Q - Matrix.of (fun _ _ => 1) := by dsimp [Q]; abel
  rw [he, Matrix.det_mul, det_rank_one_sub Q hQ, Matrix.det_diagonal]

private theorem K_eq_zero_iff_resolvent_sum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hA : IsRegularTournament A) (y : Fin d → ℂ) (hy : ∀ j, y j ≠ 0)
    (hQ : (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    K A y = 0 ↔ ∑ i, ∑ j, (diagonal (fun j => 2 / y j) -
      (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j = 1 := by
  rw [K_resolvent_factorization A hA y hy hQ]
  have hp : (∏ j, y j / 2) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ =>
    div_ne_zero (hy j) (by norm_num)
  simp only [mul_eq_zero, hQ, hp, false_or, or_false, sub_eq_zero]
  exact eq_comm

private theorem localSolution_resolvent_eq {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (h : (Fin (d-1) → ℂ) → ℂ) (hh : IsLocalSolution A h)
    (hQ0 : (diagonal (fun _ : Fin d => 2 / z d) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0) :
    ∀ᶠ y in 𝓝 (fun _ : Fin (d-1) => z d),
      ∑ i, ∑ j, (diagonal (fun j => 2 / appendLast y (h y) j) -
        (skewAdjacency A).map (Int.castRingHom ℂ))⁻¹ i j = 1 := by
  let g := fun y : Fin (d-1) → ℂ => appendLast y (h y)
  let y0 := fun _ : Fin (d-1) => z d
  have hz0 : z d ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast (by omega : d ≠ 0))
  have hg0 : g y0 = (fun _ => z d) := by
    dsimp [g, y0]
    rw [hh.1]
    ext i
    simp [appendLast, Fin.snoc]
  have hg : ContinuousAt g y0 := by
    apply continuousAt_pi.2
    intro i
    dsimp [g]
    unfold appendLast Fin.snoc
    split_ifs <;> simp only [cast_eq]
    · exact (continuous_apply _).continuousAt
    · exact hh.2.1.continuousAt
  have hn (i : Fin d) : g y0 i ≠ 0 := by rw [hg0]; exact hz0
  have hy : ∀ᶠ y in 𝓝 y0, ∀ i, g y i ≠ 0 :=
    eventually_all.2 fun i => ((continuous_apply i).continuousAt.comp hg).eventually_ne (hn i)
  have hcont : ContinuousAt (fun y =>
      (diagonal (fun j => 2 / g y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det) y0 := by
    apply continuous_id.matrix_det.continuousAt.comp
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact (continuousAt_const.div ((continuous_apply j).continuousAt.comp hg) (hn j)).sub
        continuousAt_const
    · simp only [hij, ite_false]
      exact continuousAt_const
  have hdet : ∀ᶠ y in 𝓝 y0,
      (diagonal (fun j => 2 / g y j) -
        (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0 := by
    apply hcont.eventually_ne
    simpa only [hg0] using hQ0
  filter_upwards [hh.2.2, hy, hdet] with y hK hny hdy
  exact (K_eq_zero_iff_resolvent_sum A hA (g y) hny hdy).mp hK



private theorem regularSkewRowSum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∀ i, ∑ j, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j = 0 := by
  obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
  have hpair : ∀ i j, adjacency A i j + adjacency A j i =
      (if i = j then 0 else 1 : ℤ) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [adjacency, hA.1]
    · have h := hA.2.1 i j hij
      cases hai : A i j <;> cases haj : A j i <;> simp_all [adjacency]
  have hcol : ∀ j, ∑ i, adjacency A i j = (r : ℤ) := by
    intro j
    have hpairsum : (∑ i : Fin d, (if i = j then 0 else 1 : ℤ)) = d - 1 := by
      calc
        _ = ∑ i : Fin d, (1 - (if i = j then 1 else 0) : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> simp_all
        _ = _ := by simp [Finset.sum_sub_distrib]
    have hh : (∑ i, adjacency A i j) + (∑ i, adjacency A j i) = (d : ℤ) - 1 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hpair]
      exact hpairsum
    have hdc : (d : ℤ) = 2 * r + 1 := by exact_mod_cast hdr
    rw [hr] at hh
    linarith
  intro i
  have hh : ∑ j, skewAdjacency A i j = 0 := by
    simp only [skewAdjacency, Matrix.sub_apply, Matrix.transpose_apply,
      Finset.sum_sub_distrib, hr, hcol, sub_self]
  change (∑ j, (skewAdjacency A i j : ℂ)) = 0
  exact_mod_cast hh

private theorem regularSkewColSum {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) :
    ∀ j, ∑ i, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j = 0 := by
  intro j
  have hs : ∀ i, ((skewAdjacency A).map (Int.castRingHom ℂ)) i j =
      -((skewAdjacency A).map (Int.castRingHom ℂ)) j i := by
    intro i
    simp [skewAdjacency, adjacency]
  simp_rw [hs, Finset.sum_neg_distrib, regularSkewRowSum A hd hA, neg_zero]

private theorem shiftedNegativeDetNeZero {d : ℕ} (A : Fin d → Fin d → Bool) :
    ((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
      (skewAdjacency A).map (Int.castRingHom ℂ)).det ≠ 0 := by
  let S := (skewAdjacency A).map (Int.castRingHom ℂ)
  have hs : S.transpose = -S := by
    ext i j
    simp [S, skewAdjacency, adjacency]
  have ht : (S + (d : ℂ) • 1).transpose = (d : ℂ) • 1 - S := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hs]
    abel
  rw [← ht, Matrix.det_transpose]
  exact shiftedDetNeZero A (d : ℂ) (Complex.norm_natCast d)

private theorem regularLocalSolution {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : ∃ h, IsLocalSolution A h := by
  let l : Fin d := ⟨d-1, by omega⟩
  let c : ℂ := -(((d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
    (skewAdjacency A).map (Int.castRingHom ℂ)).det / (2 * (d : ℂ)^d))
  have hc : c ≠ 0 := by
    apply neg_ne_zero.mpr
    exact div_ne_zero (shiftedNegativeDetNeZero A)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast (by omega : d ≠ 0))))
  have hlast : HasDerivAt (fun s : ℂ => K A (appendLast (fun _ => z d) s)) c (z d) := by
    have he := K_coordinate_deriv A (fun _ => z d) l (z d)
    rw [regularColumnSlopeValue A hd hA l] at he
    simpa only [appendLast_update (by omega : 1 ≤ d)] using he
  let F := fun p : (Fin (d-1) → ℂ) × ℂ => K A (appendLast p.1 p.2)
  have hF : DifferentiableAt ℂ F ((fun _ => z d), z d) := by
    have he := ((polynomialSmooth A).differentiable (by norm_num)).comp
      (appendLastLinear d).differentiable
    have hp := he.differentiableAt (x := ((fun _ => z d), z d))
    simpa only [Function.comp_def, appendLastLinearApply] using hp
  exact localSolutionOfInvertible A hd hA
    (scalar_partial_invertible F (fun _ => z d) (z d) c hF hlast hc)

end D5.S3.Combinatorics.WormaldTournamentHessian.Result
