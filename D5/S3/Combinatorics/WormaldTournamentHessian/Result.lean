/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Analytic Hessian and determinant-square structure of regular tournaments. -/

/-
admission_basis: open-problem-resolution (#21941; Proved)
escape_witness: none
Utility is none: the result is a general theorem over arbitrary finite
regular tournaments and every complex C2 local solution, not a finite certificate.
Frozen D5 dependencies: none (Mathlib-only imports).
All definitions have proof_shape: bind-only (definition), escape_witness: none.
All theorems and lemmas have proof_shape: bind-only, escape_witness: none.
The proof composes pinned Mathlib determinant, finite-sum and calculus theorems
with scalar algebra and coordinate normalization. No new escape witness is claimed.
The external named conjecture supplies the module admission basis.
Every auxiliary declaration is consumed on the proof path to result.
Principal consumers:
  skewDiag, skewNormLe -> shiftedDetNeZero, shiftedDetPureImaginary
  shiftedDetPureImaginary -> imaginaryShiftIntegral -> algebraicRatioRational
  algebraicRatioRational -> algebraicSquareIdentity -> regularAlgebraicSquare
  regularDegree -> regularOdd, determinantAtBase, regularSkewRowSum
  determinantAtBase, polynomialSmooth -> localSolutionOfInvertible
  cofactor_eq_of_zero_sums -> regularColumnSlopeValue -> regularLocalSolution
  determinant_column_deriv -> K_coordinate_deriv -> regularLocalSolution
  scalar_map_invertible -> scalar_partial_invertible -> regularLocalSolution
  det_rank_one_sub -> K_resolvent_factorization -> K_eq_zero_iff_resolvent_sum
  K_eq_zero_iff_resolvent_sum -> localSolution_resolvent_eq -> calH_closedForm
  WormaldAnalytic.second_comp -> WormaldAnalytic.hessian_of_implicit_coordinates
  alpha_second_const, alpha_first_const -> calH_closedForm
  bridge_det -> differenceMinor_det -> skew_difference_det -> calH_closedForm
  regularLocalSolution, regularAlgebraicSquare, calH_closedForm -> result
The original analytic definitions of claim, K, phase, hessian and calH are retained.
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

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


open scoped Topology ContDiff
open Filter

namespace WormaldAnalytic

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private noncomputable def second (f : E → F) (x v w : E) : F :=
  fderiv 𝕜 (fun y => fderiv 𝕜 f y v) x w

private theorem second_comp (f : E → F) (g : F → G) (x v w : E)
    (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g (f x)) :
    second (𝕜 := 𝕜) (g ∘ f) x v w =
      second (𝕜 := 𝕜) g (f x) (fderiv 𝕜 f x v) (fderiv 𝕜 f x w) +
      fderiv 𝕜 g (f x) (second (𝕜 := 𝕜) f x v w) := by
  have hf₁ := hf.differentiableAt (by norm_num)
  have hg₁ := hg.differentiableAt (by norm_num)
  have hf₂ : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hg₂ : DifferentiableAt 𝕜 (fderiv 𝕜 g) (f x) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have heq : (fun y => fderiv 𝕜 (g ∘ f) y v) =ᶠ[𝓝 x]
      (fun y => fderiv 𝕜 g (f y) (fderiv 𝕜 f y v)) := by
    filter_upwards [hf.eventually (by norm_num),
      hf₁.continuousAt (hg.eventually (by norm_num))] with y hyf hyg
    have hyg' : ContDiffAt 𝕜 2 g (f y) := hyg
    rw [fderiv_comp y (hyg'.differentiableAt (by norm_num))
      (hyf.differentiableAt (by norm_num))]
    rfl
  unfold second
  rw [heq.fderiv_eq]
  have hc : DifferentiableAt 𝕜 (fun y => fderiv 𝕜 g (f y)) x := hg₂.comp x hf₁
  have hu : DifferentiableAt 𝕜 (fun y => fderiv 𝕜 f y v) x :=
    hf₂.clm_apply (differentiableAt_const v)
  rw [fderiv_clm_apply hc hu]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hgapp : fderiv 𝕜 (fun y => fderiv 𝕜 g y (fderiv 𝕜 f x v)) (f x) =
      (fderiv 𝕜 (fderiv 𝕜 g) (f x)).flip (fderiv 𝕜 f x v) := by
    rw [fderiv_clm_apply hg₂ (differentiableAt_const (fderiv 𝕜 f x v))]
    simp
  rw [hgapp]
  rw [fderiv_fun_comp x hg₂ hf₁]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

private theorem second_eq_zero_of_eventually {f : E → F} {x : E}
    (hf : f =ᶠ[𝓝 x] fun _ => 0) (v w : E) : second (𝕜 := 𝕜) f x v w = 0 := by
  have he : (fun y => fderiv 𝕜 f y v) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hf.fderiv (𝕜 := 𝕜)] with y hy
    rw [hy]
    simpa using congrArg (fun L : E →L[𝕜] F => L v)
      (hasFDerivAt_const (𝕜 := 𝕜) (0 : F) y).fderiv
  unfold second
  rw [he.fderiv_eq]
  simp

private theorem second_graph {h : E → F} {x : E} (hh : ContDiffAt 𝕜 2 h x) (v w : E) :
    second (𝕜 := 𝕜) (fun y => (y, h y)) x v w =
      (0, second (𝕜 := 𝕜) h x v w) := by
  have he : (fun y => fderiv 𝕜 (fun y => (y, h y)) y v) =ᶠ[𝓝 x]
      (fun y => (v, fderiv 𝕜 h y v)) := by
    filter_upwards [hh.eventually (by norm_num)] with y hy
    have hp := (hasFDerivAt_id y).prodMk (hy.differentiableAt (by norm_num)).hasFDerivAt
    change HasFDerivAt (fun y : E => (y, h y)) _ y at hp
    rw [hp.fderiv]
    simp
  unfold second
  rw [he.fderiv_eq]
  have hh₂ : DifferentiableAt 𝕜 (fderiv 𝕜 h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hp := (hasFDerivAt_const (𝕜 := 𝕜) v x).prodMk
    (hh₂.clm_apply (differentiableAt_const v)).hasFDerivAt
  rw [hp.fderiv]
  simp

private theorem implicit_first_graph {h : E → F} {F₀ : E × F → G} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0) (v : E) :
    fderiv 𝕜 F₀ (x, h x) (v, fderiv 𝕜 h x v) = 0 := by
  have hh₁ := hh.differentiableAt (by norm_num)
  have hF₁ := hF.differentiableAt (by norm_num)
  have hd : fderiv 𝕜 (fun y => F₀ (y, h y)) x = 0 := by
    rw [he.fderiv_eq]
    simp
  have hp := (hasFDerivAt_id x).prodMk hh₁.hasFDerivAt
  change HasFDerivAt (fun y : E => (y, h y)) _ x at hp
  have hc := hF₁.hasFDerivAt.comp x hp
  change HasFDerivAt (fun y : E => F₀ (y, h y)) _ x at hc
  rw [hc.fderiv] at hd
  have hv := congrArg (fun L : E →L[𝕜] G => L v) hd
  simpa using hv

private theorem implicit_second_graph {h : E → F} {F₀ : E × F → G} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0) (v w : E) :
    second (𝕜 := 𝕜) F₀ (x, h x) (v, fderiv 𝕜 h x v) (w, fderiv 𝕜 h x w) +
      fderiv 𝕜 F₀ (x, h x) (0, second (𝕜 := 𝕜) h x v w) = 0 := by
  have hh₁ := hh.differentiableAt (by norm_num)
  have hp : ContDiffAt 𝕜 2 (fun y => (y, h y)) x := contDiffAt_id.prodMk hh
  have hs := second_comp (𝕜 := 𝕜) (fun y => (y, h y)) F₀ x v w hp hF
  have hp' := (hasFDerivAt_id x).prodMk hh₁.hasFDerivAt
  change HasFDerivAt (fun y : E => (y, h y)) _ x at hp'
  rw [second_graph hh v w, hp'.fderiv] at hs
  simp only [fderiv_id, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at hs
  rw [← hs]
  exact second_eq_zero_of_eventually he v w

private theorem implicit_first_scalar {h : E → 𝕜} {F₀ : E × 𝕜 → 𝕜} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0)
    (hq : fderiv 𝕜 F₀ (x, h x) (0, 1) ≠ 0) (v : E) :
    fderiv 𝕜 h x v = -fderiv 𝕜 F₀ (x, h x) (v, 0) /
      fderiv 𝕜 F₀ (x, h x) (0, 1) := by
  have H := implicit_first_graph hh hF he v
  have hp : (v, fderiv 𝕜 h x v) =
      (v, (0 : 𝕜)) + (fderiv 𝕜 h x v) • ((0 : E), (1 : 𝕜)) := by simp
  rw [hp, map_add, map_smul, smul_eq_mul] at H
  apply (eq_div_iff hq).mpr
  linear_combination H

private theorem implicit_second_scalar {h : E → 𝕜} {F₀ : E × 𝕜 → 𝕜} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0)
    (hq : fderiv 𝕜 F₀ (x, h x) (0, 1) ≠ 0) (v w : E) :
    second (𝕜 := 𝕜) h x v w =
      -second (𝕜 := 𝕜) F₀ (x, h x)
        (v, fderiv 𝕜 h x v) (w, fderiv 𝕜 h x w) /
          fderiv 𝕜 F₀ (x, h x) (0, 1) := by
  have H := implicit_second_graph hh hF he v w
  have hp : ((0 : E), second (𝕜 := 𝕜) h x v w) =
      (second (𝕜 := 𝕜) h x v w) • ((0 : E), (1 : 𝕜)) := by simp
  rw [hp, map_smul, smul_eq_mul] at H
  apply (eq_div_iff hq).mpr
  linear_combination H

private theorem second_sub_const (f : E → F) (c : F) (x v w : E) :
    second (𝕜 := 𝕜) (fun y => f y - c) x v w = second (𝕜 := 𝕜) f x v w := by
  unfold second
  simp_rw [fderiv_sub_const]

private theorem second_comp_clm (L : E →L[𝕜] F) (f : F → G) (x v w : E)
    (hf : ContDiffAt 𝕜 2 f (L x)) :
    second (𝕜 := 𝕜) (f ∘ L) x v w = second (𝕜 := 𝕜) f (L x) (L v) (L w) := by
  have hL : ContDiffAt 𝕜 2 L x := L.contDiff.contDiffAt
  have hs := second_comp (𝕜 := 𝕜) L f x v w hL hf
  have hsecond : second (𝕜 := 𝕜) L x v w = 0 := by
    unfold second
    simp [L.fderiv]
  simpa only [L.fderiv, hsecond, map_zero, add_zero] using hs

section Angular

variable {n : ℕ}

private theorem second_eq_derivative {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) f x v w = fderiv ℂ (fderiv ℂ f) x w v := by
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  unfold second
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

private theorem second_sub_sub {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (a b c d : Fin n → ℂ) :
    second (𝕜 := ℂ) f x (a - b) (c - d) =
      second (𝕜 := ℂ) f x a c - second (𝕜 := ℂ) f x a d -
        second (𝕜 := ℂ) f x b c + second (𝕜 := ℂ) f x b d := by
  simp only [second_eq_derivative hf, map_sub, _root_.sub_apply]
  abel

private theorem second_complex_to_real {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (v w : Fin n → ℂ) :
    second (𝕜 := ℝ) f x v w = second (𝕜 := ℂ) f x v w := by
  have he : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y => fderiv ℂ f y v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdv := hd.clm_apply (differentiableAt_const (c := v))
  unfold second
  rw [he.fderiv_eq, hdv.fderiv_restrictScalars ℝ]
  rfl

private noncomputable def angularMap : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

@[simp] private theorem angularMap_apply (θ : Fin n → ℝ) (j : Fin n) :
    angularMap θ j = Complex.I * (θ j : ℂ) := rfl

private theorem second_angular_substitution {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiffAt ℂ 2 f 0) (j k : Fin n) :
    second (𝕜 := ℝ) (fun θ : Fin n → ℝ => f (angularMap θ)) 0
      (Pi.single j 1) (Pi.single k 1) =
      -second (𝕜 := ℂ) f 0 (Pi.single j 1) (Pi.single k 1) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) := angularMap
  have hL : ContDiffAt ℝ 2 L 0 := L.contDiff.contDiffAt
  have hs := second_comp (𝕜 := ℝ) L f 0 (Pi.single j 1) (Pi.single k 1)
    hL (by simpa using hf.restrict_scalars ℝ)
  have hsecond : second (𝕜 := ℝ) L 0 (Pi.single j 1) (Pi.single k 1) = 0 := by
    unfold second
    simp [L.fderiv]
  rw [hsecond] at hs
  simp only [map_zero, add_zero, L.fderiv] at hs
  change second (𝕜 := ℝ) (f ∘ L) 0 (Pi.single j 1) (Pi.single k 1) = _
  rw [hs, second_complex_to_real hf]
  have hLj : L (Pi.single j 1) = Complex.I • (Pi.single j (1 : ℂ)) := by
    ext i
    by_cases hij : i = j <;> simp [L, Pi.single_apply, hij]
  have hLk : L (Pi.single k 1) = Complex.I • (Pi.single k (1 : ℂ)) := by
    ext i
    by_cases hik : i = k <;> simp [L, Pi.single_apply, hik]
  rw [hLj, hLk, second_eq_derivative hf, second_eq_derivative hf]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

private noncomputable def logarithmicPhase (a : ℂ) (h : (Fin n → ℂ) → ℂ)
    (u : Fin n → ℂ) : ℂ := Complex.log (h (fun j => a * Complex.exp (u j)))

private theorem logarithmicPhase_smooth {a : ℂ} {h : (Fin n → ℂ) → ℂ}
    (hh : ContDiffAt ℂ 2 h (fun _ => a))
    (ha : h (fun _ => a) ∈ Complex.slitPlane) :
    ContDiffAt ℂ 2 (logarithmicPhase a h) 0 := by
  have he : ContDiff ℂ 2 (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) := by
    fun_prop
  have hs : ContDiffAt ℂ 2 (fun u : Fin n → ℂ => h (fun j => a * Complex.exp (u j))) 0 := by
    have hh' : ContDiffAt ℂ 2 h ((fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) 0) := by simpa using hh
    exact hh'.comp 0 he.contDiffAt
  have hl : ContDiffAt ℂ 2 Complex.log ((fun u : Fin n → ℂ => h (fun j => a * Complex.exp (u j))) 0) := by simpa using Complex.contDiffAt_log (n := 2) ha
  exact hl.comp 0 hs

private noncomputable def exponentialChart (a : ℂ) (u : Fin n → ℂ) : Fin n → ℂ :=
  fun j => a * Complex.exp (u j)

private theorem fderiv_exponentialChart (a : ℂ) (u v : Fin n → ℂ) :
    fderiv ℂ (exponentialChart a) u v = fun j => a * Complex.exp (u j) * v j := by
  have hd : HasFDerivAt (exponentialChart a)
      (ContinuousLinearMap.pi fun j => a • (Complex.exp (u j) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ))) u := by
    change HasFDerivAt (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) _ u
    apply hasFDerivAt_pi.mpr
    intro j
    exact ((hasFDerivAt_apply (𝕜 := ℂ) j u).cexp).const_mul a
  rw [hd.fderiv]
  ext j
  simp [mul_assoc]

private theorem second_exponentialChart (a : ℂ) (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) (exponentialChart a) 0 v w = fun j => a * v j * w j := by
  unfold second
  simp_rw [fderiv_exponentialChart]
  have hd : HasFDerivAt (fun u : Fin n → ℂ => fun j =>
      a * Complex.exp (u j) * v j)
      (ContinuousLinearMap.pi fun j => (v j) • (a •
        (Complex.exp ((0 : Fin n → ℂ) j) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)))) 0 := by
    apply hasFDerivAt_pi.mpr
    intro j
    exact (((hasFDerivAt_apply (𝕜 := ℂ) j (0 : Fin n → ℂ)).cexp).const_mul a).mul_const (v j)
  rw [hd.fderiv]
  ext j
  simp [mul_assoc, mul_left_comm, mul_comm]

private theorem second_clog {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hg : ContDiffAt ℂ 2 g x) (hslit : g x ∈ Complex.slitPlane)
    (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) (fun y => Complex.log (g y)) x v w =
      -(g x ^ 2)⁻¹ * fderiv ℂ g x w * fderiv ℂ g x v +
      (g x)⁻¹ * second (𝕜 := ℂ) g x v w := by
  have hg₁ := hg.differentiableAt (by norm_num)
  have hg₂ : DifferentiableAt ℂ (fderiv ℂ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have he : (fun y => fderiv ℂ (fun y => Complex.log (g y)) y v) =ᶠ[𝓝 x]
      (fun y => (g y)⁻¹ * fderiv ℂ g y v) := by
    filter_upwards [hg.eventually (by norm_num),
      hg₁.continuousAt (Complex.isOpen_slitPlane.mem_nhds hslit)] with y hy hys
    have hys' : g y ∈ Complex.slitPlane := hys
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.clog hys').fderiv]
    simp
  have hg0 : g x ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hi := (hasDerivAt_inv hg0).comp_hasFDerivAt x hg₁.hasFDerivAt
  have hdv := hg₂.clm_apply (differentiableAt_const (c := v))
  change HasFDerivAt (fun y => (g y)⁻¹) _ x at hi
  have hp := hi.mul hdv.hasFDerivAt
  change HasFDerivAt (fun y => (g y)⁻¹ * fderiv ℂ g y v) _ x at hp
  unfold second
  rw [he.fderiv_eq, hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

private theorem logarithmicPhase_second {a : ℂ} {h : (Fin n → ℂ) → ℂ}
    (ha : a ≠ 0) (hh : ContDiffAt ℂ 2 h (fun _ => a))
    (hh0 : h (fun _ => a) = a) (hslit : a ∈ Complex.slitPlane)
    (j k : Fin n) :
    second (𝕜 := ℂ) (logarithmicPhase a h) 0 (Pi.single j 1) (Pi.single k 1) =
      a * second (𝕜 := ℂ) h (fun _ => a) (Pi.single j 1) (Pi.single k 1) +
        (if j = k then fderiv ℂ h (fun _ => a) (Pi.single j 1) else 0) -
          fderiv ℂ h (fun _ => a) (Pi.single j 1) *
            fderiv ℂ h (fun _ => a) (Pi.single k 1) := by
  let e : (Fin n → ℂ) → (Fin n → ℂ) := exponentialChart a
  have he0 : e 0 = (fun _ => a) := by ext i; simp [e, exponentialChart]
  have he : ContDiffAt ℂ 2 e 0 := by
    change ContDiffAt ℂ 2 (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) 0
    fun_prop
  have hh' : ContDiffAt ℂ 2 h (e 0) := by simpa [he0] using hh
  have hg : ContDiffAt ℂ 2 (h ∘ e) 0 := hh'.comp 0 he
  have hD1 (v : Fin n → ℂ) : fderiv ℂ (h ∘ e) 0 v =
      a * fderiv ℂ h (fun _ => a) v := by
    rw [fderiv_comp 0 (by simpa [he0] using hh.differentiableAt (by norm_num))
      (he.differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.comp_apply, he0]
    have heD : fderiv ℂ e 0 v = a • v := by
      ext i
      simp [e, fderiv_exponentialChart]
    rw [heD, map_smul, smul_eq_mul]
  have hD2 := second_comp (𝕜 := ℂ) e h 0 (Pi.single j 1) (Pi.single k 1) he
    (by simpa [he0] using hh)
  rw [he0] at hD2
  have heDj : fderiv ℂ e 0 (Pi.single j 1) = a • (Pi.single j (1 : ℂ)) := by
    ext i
    simp [e, fderiv_exponentialChart]
  have heDk : fderiv ℂ e 0 (Pi.single k 1) = a • (Pi.single k (1 : ℂ)) := by
    ext i
    simp [e, fderiv_exponentialChart]
  rw [heDj, heDk] at hD2
  have hscale : second (𝕜 := ℂ) h (fun _ => a)
      (a • (Pi.single j (1 : ℂ))) (a • (Pi.single k (1 : ℂ))) =
      a * a * second (𝕜 := ℂ) h (fun _ => a) (Pi.single j 1) (Pi.single k 1) := by
    simp only [second_eq_derivative hh, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hscale] at hD2
  have heD2 : second (𝕜 := ℂ) e 0 (Pi.single j 1) (Pi.single k 1) =
      if j = k then a • (Pi.single j (1 : ℂ)) else 0 := by
    rw [show e = exponentialChart a from rfl, second_exponentialChart]
    split_ifs with hjk
    · subst k; ext i; by_cases hi : i = j <;> simp [hi]
    · ext i; by_cases hi : i = j <;> by_cases hk : i = k <;> simp_all
  rw [heD2] at hD2
  have hlog := second_clog hg (by simp [he0, hh0]; exact hslit)
    (Pi.single j 1) (Pi.single k 1)
  change second (𝕜 := ℂ) (logarithmicPhase a h) 0 (Pi.single j 1) (Pi.single k 1) = _ at hlog
  rw [hlog, hD2, hD1, hD1]
  simp only [Function.comp_apply, he0, hh0]
  split_ifs with hjk
  · simp only [map_smul, smul_eq_mul]
    field_simp
    ring
  · simp only [map_zero, add_zero]
    field_simp
    ring

end Angular

end WormaldAnalytic


namespace WormaldAnalytic

private theorem actual_hessian {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (j k : Fin (d - 1)) :
    hessian h j k =
      fderiv ℂ h (fun _ => z d) (Pi.single j 1) *
          fderiv ℂ h (fun _ => z d) (Pi.single k 1) -
        z d * second (𝕜 := ℂ) h (fun _ => z d) (Pi.single j 1) (Pi.single k 1) -
          (if j = k then fderiv ℂ h (fun _ => z d) (Pi.single j 1) else 0) := by
  have hz0 : z d ≠ 0 := by
    unfold z
    apply div_ne_zero (by norm_num)
    exact_mod_cast (by omega : d ≠ 0)
  have hzs : z d ∈ Complex.slitPlane := by
    rw [show z d = (((2 : ℝ) / d : ℝ) : ℂ) by simp [z]]
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (by norm_num) (by exact_mod_cast (by omega : 0 < d))
  have hsm := logarithmicPhase_smooth hh.2.1 (by rw [hh.1]; exact hzs)
  have hang := second_angular_substitution hsm j k
  change hessian h j k =
    -second (𝕜 := ℂ) (logarithmicPhase (z d) h) 0 (Pi.single j 1) (Pi.single k 1) at hang
  rw [hang, logarithmicPhase_second hz0 hh.2.1 hh.1 hzs]
  ring

end WormaldAnalytic

namespace WormaldAnalytic

private theorem hessian_of_implicit_scalar {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (L : ((Fin (d - 1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ))
    (α : (Fin d → ℂ) → ℂ)
    (hα : ContDiffAt ℂ 2 α (L ((fun _ => z d), z d)))
    (he : ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), α (L (y, h y)) = 1)
    (c : ℂ) (hc : c ≠ 0)
    (hfirst : ∀ j, fderiv ℂ α (L ((fun _ => z d), z d))
      (L (Pi.single j 1, 0)) = c)
    (hlast : fderiv ℂ α (L ((fun _ => z d), z d)) (L (0, 1)) = c)
    (j k : Fin (d - 1)) :
    hessian h j k = 1 + (if j = k then 1 else 0) + (z d / c) *
      second (𝕜 := ℂ) α (L ((fun _ => z d), z d))
        (L (Pi.single j 1, -1)) (L (Pi.single k 1, -1)) := by
  let x : Fin (d - 1) → ℂ := fun _ => z d
  let F₀ : ((Fin (d - 1) → ℂ) × ℂ) → ℂ := fun p => α (L p) - 1
  change (∀ j, fderiv ℂ α (L (x, z d)) (L (Pi.single j 1, 0)) = c) at hfirst
  change fderiv ℂ α (L (x, z d)) (L (0, 1)) = c at hlast
  have hh0 : h x = z d := hh.1
  have hhC : ContDiffAt ℂ 2 h x := hh.2.1
  have hα' : ContDiffAt ℂ 2 α (L (x, h x)) := by simpa [hh0] using hα
  have hF : ContDiffAt ℂ 2 F₀ (x, h x) := by
    exact (hα'.comp (x, h x) L.contDiff.contDiffAt).sub contDiffAt_const
  have hzero : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he] with y hy
    dsimp [F₀]
    rw [hy, sub_self]
  have dF (v : (Fin (d - 1) → ℂ) × ℂ) :
      fderiv ℂ F₀ (x, h x) v = fderiv ℂ α (L (x, z d)) (L v) := by
    change fderiv ℂ (fun p => α (L p) - 1) (x, h x) v = _
    rw [fderiv_sub_const]
    have hcomp := (hα'.differentiableAt (by norm_num)).hasFDerivAt.comp (x, h x)
      L.hasFDerivAt
    change HasFDerivAt (fun p => α (L p)) _ (x, h x) at hcomp
    rw [hcomp.fderiv]
    simp [hh0]
  have hq : fderiv ℂ F₀ (x, h x) (0, 1) ≠ 0 := by
    rw [dF, hlast]
    exact hc
  have dh (i : Fin (d - 1)) : fderiv ℂ h x (Pi.single i 1) = -1 := by
    have H := implicit_first_scalar hhC hF hzero hq (Pi.single i 1)
    rw [dF, dF, hfirst, hlast] at H
    simpa [hc] using H
  have h2F (v w : (Fin (d - 1) → ℂ) × ℂ) :
      second (𝕜 := ℂ) F₀ (x, h x) v w =
        second (𝕜 := ℂ) α (L (x, z d)) (L v) (L w) := by
    change second (𝕜 := ℂ) (fun p => α (L p) - 1) (x, h x) v w = _
    rw [second_sub_const]
    have H := second_comp_clm L α (x, h x) v w hα'
    change second (𝕜 := ℂ) (fun p => α (L p)) (x, h x) v w = _ at H
    simpa [hh0] using H
  have dh2 := implicit_second_scalar hhC hF hzero hq (Pi.single j 1) (Pi.single k 1)
  rw [dh j, dh k, dF, hlast, h2F] at dh2
  dsimp only [x] at dh dh2
  rw [actual_hessian hd hh, dh j, dh k, dh2]
  split_ifs <;> ring

end WormaldAnalytic

namespace WormaldAnalytic

private theorem hessian_of_implicit_coordinates {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (L : ((Fin (d - 1) → ℂ) × ℂ) →L[ℂ] (Fin d → ℂ))
    (ι : Fin (d - 1) → Fin d) (last : Fin d)
    (hLj : ∀ j, L (Pi.single j 1, 0) = Pi.single (ι j) 1)
    (hLl : L (0, 1) = Pi.single last 1)
    (α : (Fin d → ℂ) → ℂ)
    (hα : ContDiffAt ℂ 2 α (L ((fun _ => z d), z d)))
    (he : ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), α (L (y, h y)) = 1)
    (c : ℂ) (hc : c ≠ 0)
    (hfirst : ∀ i, fderiv ℂ α (L ((fun _ => z d), z d)) (Pi.single i 1) = c)
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hsecond : ∀ i l, second (𝕜 := ℂ) α (L ((fun _ => z d), z d))
      (Pi.single i 1) (Pi.single l 1) = M i l)
    (j k : Fin (d - 1)) :
    hessian h j k = 1 + (if j = k then 1 else 0) + (z d / c) *
      (M (ι j) (ι k) - M (ι j) last - M last (ι k) + M last last) := by
  have hFj (i : Fin (d - 1)) : fderiv ℂ α (L ((fun _ => z d), z d))
      (L (Pi.single i 1, 0)) = c := by rw [hLj]; exact hfirst (ι i)
  have hFl : fderiv ℂ α (L ((fun _ => z d), z d)) (L (0, 1)) = c := by
    rw [hLl]; exact hfirst last
  rw [hessian_of_implicit_scalar hd hh L α hα he c hc hFj hFl]
  have hdiff (i : Fin (d - 1)) : L (Pi.single i 1, -1) =
      Pi.single (ι i) (1 : ℂ) - Pi.single last 1 := by
    have hp : (Pi.single i (1 : ℂ), (-1 : ℂ)) =
        (Pi.single i (1 : ℂ), (0 : ℂ)) - ((0 : Fin (d - 1) → ℂ), (1 : ℂ)) := by simp
    rw [hp, map_sub, hLj, hLl]
  rw [hdiff, hdiff, second_sub_sub hα, hsecond, hsecond, hsecond, hsecond]

end WormaldAnalytic



open Matrix
open scoped Matrix

section
variable {m : Type*} [Fintype m] [DecidableEq m]

private noncomputable def bridgeU : Matrix (Sum m Unit) (Sum m Unit) ℂ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => -1) 1

private lemma bridgeU_det : (bridgeU (m := m)).det = (Fintype.card m : ℂ) + 1 := by
  unfold bridgeU
  rw [Matrix.det_fromBlocks_one₁₁, Matrix.det_unique]
  simp [Matrix.mul_apply] <;> ring

private noncomputable def bridgeH (T : Matrix (Sum m Unit) (Sum m Unit) ℂ) : Matrix m m ℂ :=
  fun j k => T (.inl j) (.inl k) - T (.inl j) (.inr ()) - T (.inr ()) (.inl k) + T (.inr ()) (.inr ())

private lemma bridgeU_entry_left (i : Sum m Unit) (j : m) :
    bridgeU i (.inl j) = (if i = .inl j then 1 else 0) - (if i = .inr () then 1 else 0) := by
  cases i <;> simp [bridgeU, Matrix.fromBlocks, Matrix.one_apply]

private lemma bridgeU_entry_right (i : Sum m Unit) : bridgeU (m := m) i (.inr ()) = 1 := by
  cases i <;> simp [bridgeU, Matrix.fromBlocks]

private lemma bridgeU_congr (T : Matrix (Sum m Unit) (Sum m Unit) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (bridgeU (m := m)).transpose * T * bridgeU =
      Matrix.fromBlocks (bridgeH T) 0 0 (Matrix.of fun (_ _ : Unit) => -((Fintype.card m : ℂ) + 1)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        bridgeU, Matrix.fromBlocks, Matrix.one_apply, bridgeH,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    | inr j =>
      cases j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, mul_one]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow]
      simp [bridgeU_entry_left, Fintype.sum_sum_type, Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, one_mul,
        hcol, bridgeU_entry_left, mul_sub, Finset.sum_sub_distrib, Fintype.sum_sum_type]
      simp [Matrix.fromBlocks]
    | inr j =>
      cases j
      simp [Matrix.mul_apply, Matrix.transpose_apply, bridgeU_entry_right, hcol,
        Matrix.fromBlocks, Fintype.card_sum]

private lemma bridge_det (T : Matrix (Sum m Unit) (Sum m Unit) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (bridgeH T).det = -((Fintype.card m : ℂ) + 1) * T.det := by
  have hd := congrArg Matrix.det (bridgeU_congr T hrow hcol)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, bridgeU_det,
    Matrix.det_fromBlocks_zero₂₁] at hd
  rw [Matrix.det_unique (Matrix.of fun (_ _ : Unit) => -((Fintype.card m : ℂ) + 1))] at hd
  simp only [Matrix.of_apply] at hd
  have hn : (Fintype.card m : ℂ) + 1 ≠ 0 := by
    have h : (0 : ℝ) < (Fintype.card m : ℝ) + 1 := by positivity
    exact_mod_cast ne_of_gt h
  have heq : ((Fintype.card m : ℂ) + 1) *
      ((bridgeH T).det + ((Fintype.card m : ℂ) + 1) * T.det) = 0 := by
    linear_combination hd
  have := (mul_eq_zero.mp heq).resolve_left hn
  linear_combination this
end

section Skew
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma skew_resolvent_det (S : Matrix n n ℂ) (c : ℂ)
    (hS : S.transpose = -S) (hn : Odd (Fintype.card n))
    (hq : (c • (1 : Matrix n n ℂ) - S).det ≠ 0) :
    (1 - c • ((c • (1 : Matrix n n ℂ) - S)⁻¹ +
      ((c • (1 : Matrix n n ℂ) - S)⁻¹).transpose)).det =
      -(c^2 • (1 : Matrix n n ℂ) + S*S).det /
        (c^2 • (1 : Matrix n n ℂ) - S*S).det := by
  let Q : Matrix n n ℂ := c • 1 - S
  let P : Matrix n n ℂ := c • 1 + S
  have hQT : Q.transpose = P := by
    simp [Q, P, Matrix.transpose_sub, Matrix.transpose_smul, hS]
  have hq' : Q.det ≠ 0 := hq
  have hp : P.det ≠ 0 := by rw [← hQT, Matrix.det_transpose]; exact hq'
  have hqp : Q*P = c^2 • 1 - S*S := by
    simp [Q, P, sub_mul, mul_add, smul_add, smul_sub, smul_smul, pow_two] <;> abel
  have hpq : P*Q = c^2 • 1 - S*S := by
    simp [Q, P, add_mul, mul_sub, smul_smul, pow_two]
    abel
  have hqi : Q⁻¹ * (Q*P) = P :=
    Matrix.nonsing_inv_mul_cancel_left Q P (isUnit_iff_ne_zero.mpr hq')
  have hpi : P⁻¹ * (Q*P) = Q := by
    rw [show Q*P=P*Q from hqp.trans hpq.symm]
    exact Matrix.nonsing_inv_mul_cancel_left P Q (isUnit_iff_ne_zero.mpr hp)
  have hid : (1 - c • (Q⁻¹ + P⁻¹)) * (Q*P) = -(c^2 • 1 + S*S) := by
    calc
      _ = Q*P - c • (Q⁻¹*(Q*P) + P⁻¹*(Q*P)) := by
        simp [sub_mul, Matrix.smul_mul, add_mul]
      _ = Q*P - c • (P+Q) := by rw [hqi,hpi]
      _ = _ := by
        rw [hqp]
        simp [Q, P, smul_add, smul_sub, smul_smul, pow_two]
        abel
  have hd : (c^2 • (1 : Matrix n n ℂ) - S*S).det ≠ 0 := by
    rw [← hqp, Matrix.det_mul]
    exact mul_ne_zero hq' hp
  rw [Matrix.transpose_nonsing_inv, hQT]
  change (1-c • (Q⁻¹+P⁻¹)).det = _
  apply (eq_div_iff hd).mpr
  have hh := congrArg Matrix.det hid
  rw [Matrix.det_mul, hqp, Matrix.det_neg] at hh
  simpa [hn.neg_one_pow] using hh
end Skew

section Fin
private noncomputable def bridgeFinEquiv (n : ℕ) : (Fin n ⊕ Unit) ≃ Fin (n+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

@[simp] private lemma bridgeFinEquiv_inl (n : ℕ) (i : Fin n) :
    bridgeFinEquiv n (.inl i) = i.castSucc := rfl
@[simp] private lemma bridgeFinEquiv_inr (n : ℕ) :
    bridgeFinEquiv n (.inr ()) = Fin.last n := rfl

private lemma differenceMinor_det (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hrow : ∀ i, ∑ j, T i j = -1) (hcol : ∀ j, ∑ i, T i j = -1) :
    (Matrix.of fun j k : Fin n =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det =
      -((n : ℂ)+1) * T.det := by
  let e := bridgeFinEquiv n
  let T' := T.submatrix e e
  have hr : ∀ i, ∑ j, T' i j = -1 := by
    intro i
    exact (e.sum_comp (fun j => T (e i) j)).trans (hrow (e i))
  have hc : ∀ j, ∑ i, T' i j = -1 := by
    intro j
    exact (e.sum_comp (fun i => T i (e j))).trans (hcol (e j))
  have h := bridge_det T' hr hc
  rw [Matrix.det_submatrix_equiv_self] at h
  have hh : bridgeH T' = (Matrix.of fun j k : Fin n =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)) := by
    ext j k
    simp [bridgeH, T', e, Matrix.submatrix_apply]
  rw [hh] at h
  simpa using h
end Fin

section RowSum
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma inverse_row_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ i, ∑ j, Q i j = c) :
    ∀ i, ∑ j, Q⁻¹ i j = c⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet Q (isUnit_iff_ne_zero.mpr hQ)
  have hu : (fun _ : n => (1 : ℂ)) = Q *ᵥ (fun _ => c⁻¹) := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hr, hc]
  have hv := Matrix.inv_mulVec_eq_vec hu
  intro i
  simpa [Matrix.mulVec, dotProduct] using congrFun hv i

private lemma inverse_col_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ j, ∑ i, Q i j = c) :
    ∀ j, ∑ i, Q⁻¹ i j = c⁻¹ := by
  have hv := inverse_row_sum Q.transpose c hc (by simpa using hQ) hr
  simpa [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply] using hv

private lemma resolvent_row_col_sum (Q : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0)
    (hQ : Q.det ≠ 0) (hr : ∀ i, ∑ j, Q i j = c) (hcol : ∀ j, ∑ i, Q i j = c) :
    (∀ i, ∑ j, (1-c • (Q⁻¹+(Q⁻¹).transpose)) i j = -1) ∧
    (∀ j, ∑ i, (1-c • (Q⁻¹+(Q⁻¹).transpose)) i j = -1) := by
  have hri := inverse_row_sum Q c hc hQ hr
  have hci := inverse_col_sum Q c hc hQ hcol
  constructor
  · intro i
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Matrix.transpose_apply, Matrix.one_apply, hri, hci, hc, mul_add]
  · intro j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Matrix.transpose_apply, Matrix.one_apply, hri, hci, hc, mul_add]
end RowSum

private lemma skew_difference_det (n : ℕ) (S : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (c : ℂ) (hc : c ≠ 0) (hS : S.transpose = -S) (hn : Odd (n+1))
    (hq : (c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S).det ≠ 0)
    (hr : ∀ i, ∑ j, S i j = 0) :
    let T := 1-c • ((c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S)⁻¹ +
      ((c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S)⁻¹).transpose)
    (Matrix.of fun j k : Fin n => T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
      T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det =
      ((n : ℂ)+1) * (c^2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) + S*S).det /
        (c^2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S*S).det := by
  let Q := c • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) - S
  let T := 1-c • (Q⁻¹ + (Q⁻¹).transpose)
  have hcol : ∀ j, ∑ i, S i j = 0 := by
    intro j
    calc
      _ = ∑ i, -S j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M j i) hS
      _ = -(∑ i, S j i) := Finset.sum_neg_distrib (fun i => S j i)
      _ = 0 := neg_eq_zero.mpr (hr j)
  have hqr : ∀ i, ∑ j, Q i j = c := by
    intro i
    simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hr]
  have hqc : ∀ j, ∑ i, Q i j = c := by
    intro j
    simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hcol]
  have hsum := resolvent_row_col_sum Q c hc hq hqr hqc
  have hdet := differenceMinor_det n T hsum.1 hsum.2
  have hid := skew_resolvent_det S c hS (by simpa using hn) hq
  change (Matrix.of fun j k : Fin n => T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
      T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)).det = _
  rw [hdet]
  change -((n : ℂ)+1) * (1-c • (Q⁻¹+(Q⁻¹).transpose)).det = _
  rw [hid]
  ring

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology ContDiff

section
variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  ({ toFun := Matrix.diagonal
     map_add' := by intro u v; exact (Matrix.diagonal_add u v).symm
     map_smul' := by intro c u; exact Matrix.diagonal_smul c u } :
    (n → ℂ) →ₗ[ℂ] Matrix n n ℂ).toContinuousLinearMap

private noncomputable def sumEntriesCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ i, ∑ j, M i j
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private lemma matrixInverse_hasFDerivAt (Q : Matrix n n ℂ) (hQ : Q.det ≠ 0) :
    HasFDerivAt (fun M : Matrix n n ℂ => M⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) Q⁻¹ Q⁻¹) Q := by
  rw [show (fun M : Matrix n n ℂ => M⁻¹) = Ring.inverse from
    funext fun M => Matrix.nonsing_inv_eq_ringInverse M]
  exact hasFDerivAt_ringInverse (𝕜 := ℂ)
    (Matrix.nonsingInvUnit Q (isUnit_iff_ne_zero.mpr hQ))

private noncomputable def inverseQ (S : Matrix n n ℂ) (y : n → ℂ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => 2 / y i) - S
private noncomputable def alpha (S : Matrix n n ℂ) (y : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((inverseQ S y)⁻¹) i j

private noncomputable def inverseQDeriv (y : n → ℂ) :
    (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  diagonalCLM ∘L ContinuousLinearMap.pi (fun i =>
    (-(2 : ℂ) / (y i)^2) • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ))

private lemma inverseQ_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) :
    HasFDerivAt (inverseQ S) (inverseQDeriv y) y := by
  have hscalar : HasFDerivAt (fun y : n → ℂ => fun i => 2 / y i)
      (ContinuousLinearMap.pi (fun i =>
        (-(2 : ℂ) / (y i)^2) • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ))) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    convert (((hasDerivAt_inv (hy i)).comp_hasFDerivAt y ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ)).hasFDerivAt).const_mul 2) using 1
    · ext y; simp [div_eq_mul_inv]
    · ext t; simp [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  exact ((diagonalCLM (n := n)).hasFDerivAt.comp y hscalar).sub_const S

private lemma inverse_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    HasFDerivAt (fun y => (inverseQ S y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
        (inverseQ S y)⁻¹ (inverseQ S y)⁻¹) ∘L inverseQDeriv y) y :=
  (matrixInverse_hasFDerivAt (inverseQ S y) hQ).comp y (inverseQ_hasFDerivAt S y hy)

private lemma alpha_hasFDerivAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    HasFDerivAt (alpha S)
      (sumEntriesCLM ∘L ((-ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
        (inverseQ S y)⁻¹ (inverseQ S y)⁻¹) ∘L inverseQDeriv y)) y := by
  change HasFDerivAt ((sumEntriesCLM (n := n)) ∘ (fun u => (inverseQ S u)⁻¹)) _ y
  exact (sumEntriesCLM (n := n)).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
private lemma inverseQ_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ) (hy : ∀ i, y i ≠ 0) :
    ContDiffAt ℂ 2 (inverseQ S) y := by
  have hs : ContDiffAt ℂ 2 (fun y : n → ℂ => fun i => 2 / y i) y := by
    apply contDiffAt_pi.mpr
    intro i
    have hi : ContDiffAt ℂ 2 (fun u : n → ℂ => (u i)⁻¹) y :=
      (contDiffAt_apply ℂ (fun _ : n => ℂ) i y).inv (hy i)
    have hm : ContDiffAt ℂ 2 (fun u : n → ℂ => (2 : ℂ) * (u i)⁻¹) y :=
      contDiffAt_const.mul hi
    simpa [div_eq_mul_inv] using hm
  exact ((diagonalCLM (n := n)).contDiff.contDiffAt.comp y hs).sub contDiffAt_const

private lemma inverse_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    ContDiffAt ℂ 2 (fun y => (inverseQ S y)⁻¹) y := by
  have h := (contDiffAt_ringInverse ℂ
    (Matrix.nonsingInvUnit (inverseQ S y) (isUnit_iff_ne_zero.mpr hQ))).comp y
      (inverseQ_contDiffAt S y hy)
  rw [show (fun u => (inverseQ S u)⁻¹) = Ring.inverse ∘ inverseQ S from
    funext fun u => Matrix.nonsing_inv_eq_ringInverse (inverseQ S u)]
  exact h

private lemma alpha_contDiffAt (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) :
    ContDiffAt ℂ 2 (alpha S) y := by
  change ContDiffAt ℂ 2 ((sumEntriesCLM (n := n)) ∘ (fun u => (inverseQ S u)⁻¹)) y
  exact (sumEntriesCLM (n := n)).contDiff.contDiffAt.comp y (inverse_contDiffAt S y hy hQ)

private lemma inverseQDeriv_single (y : n → ℂ) (j : n) :
    inverseQDeriv y (Pi.single j 1) =
      (-(2 : ℂ) / (y j)^2) • Matrix.diagonal (Pi.single j 1) := by
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j
    · subst j; simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, Pi.single_apply]
    · simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, Pi.single_apply,
        hij, Ne.symm hij]
  · simp [inverseQDeriv, diagonalCLM, Matrix.diagonal_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, hik]

private lemma inverse_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j : n) :
    fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single j 1) =
      (2 / (y j)^2) • Matrix.of (fun i k =>
        ((inverseQ S y)⁻¹) i j * ((inverseQ S y)⁻¹) j k) := by
  rw [(inverse_hasFDerivAt S y hy hQ).fderiv]
  let V := (inverseQ S y)⁻¹
  change -(V * inverseQDeriv y (Pi.single j 1) * V) =
    (2 / (y j)^2) • Matrix.of (fun i k => V i j * V j k)
  rw [inverseQDeriv_single]
  ext i k
  simp [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.single_apply, Matrix.neg_apply]
  ring

private noncomputable def rowSumCLM (j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ k, M j k
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
private noncomputable def colSumCLM (j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M => ∑ k, M k j
     map_add' := by intro M N; simp [Finset.sum_add_distrib]
     map_smul' := by intro c M; simp [← Finset.mul_sum] } :
    Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private lemma row_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun y => ∑ l, ((inverseQ S y)⁻¹) j l) y (Pi.single k 1) =
      (2 / (y k)^2) * ((inverseQ S y)⁻¹) j k *
        (∑ l, ((inverseQ S y)⁻¹) k l) := by
  have hd := (rowSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) j l) _ y at hd
  rw [hd.fderiv]
  rw [← (inverse_hasFDerivAt S y hy hQ).fderiv]
  change rowSumCLM j (fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single k 1)) = _
  rw [inverse_fderiv_single S y hy hQ k]
  simp [rowSumCLM, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

private lemma col_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun y => ∑ l, ((inverseQ S y)⁻¹) l j) y (Pi.single k 1) =
      (2 / (y k)^2) * ((inverseQ S y)⁻¹) k j *
        (∑ l, ((inverseQ S y)⁻¹) l k) := by
  have hd := (colSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) l j) _ y at hd
  rw [hd.fderiv]
  rw [← (inverse_hasFDerivAt S y hy hQ).fderiv]
  change colSumCLM j (fderiv ℂ (fun y => (inverseQ S y)⁻¹) y (Pi.single k 1)) = _
  rw [inverse_fderiv_single S y hy hQ k]
  simp [colSumCLM, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma alpha_fderiv_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j : n) :
    fderiv ℂ (alpha S) y (Pi.single j 1) =
      (2 / (y j)^2) * (∑ k, ((inverseQ S y)⁻¹) j k) *
        (∑ i, ((inverseQ S y)⁻¹) i j) := by
  rw [(alpha_hasFDerivAt S y hy hQ).fderiv]
  let V := (inverseQ S y)⁻¹
  change (∑ i, ∑ k, (-(V * inverseQDeriv y (Pi.single j 1) * V)) i k) = _
  rw [inverseQDeriv_single]
  have he : -(V * ((-(2 : ℂ) / (y j)^2) • Matrix.diagonal (Pi.single j 1)) * V) =
      (2 / (y j)^2) • Matrix.of (fun i k => V i j * V j k) := by
    ext i k
    simp [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Pi.single_apply, Matrix.neg_apply]
    ring
  rw [he]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma inverse_square_hasDerivAt (t : ℂ) (ht : t ≠ 0) :
    HasDerivAt (fun t : ℂ => 2 / t^2) (-(4 : ℂ) / t^3) t := by
  have hd := (((hasDerivAt_id t).inv ht).pow 2).const_mul (2 : ℂ)
  convert hd using 1
  · ext u
    simp [div_eq_mul_inv]
  · dsimp
    field_simp [ht] <;> ring

private lemma alpha_second_single (S : Matrix n n ℂ) (y : n → ℂ)
    (hy : ∀ i, y i ≠ 0) (hQ : (inverseQ S y).det ≠ 0) (j k : n) :
    fderiv ℂ (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) y (Pi.single k 1) =
      (-(4 : ℂ) / (y j)^3) * (if k = j then 1 else 0) *
        (∑ l, ((inverseQ S y)⁻¹) j l) * (∑ l, ((inverseQ S y)⁻¹) l j) +
      (4 / ((y j)^2 * (y k)^2)) *
        (((inverseQ S y)⁻¹) j k * (∑ l, ((inverseQ S y)⁻¹) k l) *
          (∑ l, ((inverseQ S y)⁻¹) l j) +
        ((inverseQ S y)⁻¹) k j * (∑ l, ((inverseQ S y)⁻¹) j l) *
          (∑ l, ((inverseQ S y)⁻¹) l k)) := by
  have hys : ∀ᶠ u in 𝓝 y, ∀ i, u i ≠ 0 :=
    Filter.eventually_all.mpr fun i => (continuous_apply i).continuousAt.eventually_ne (hy i)
  have hdet : ContinuousAt (fun u => (inverseQ S u).det) y :=
    (show Continuous (Matrix.det : Matrix n n ℂ → ℂ) from continuous_id.matrix_det).continuousAt.comp
      (inverseQ_contDiffAt S y hy).continuousAt
  have heq : (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) =ᶠ[𝓝 y]
      (fun u => (2 / (u j)^2) * (∑ l, ((inverseQ S u)⁻¹) j l) *
        (∑ l, ((inverseQ S u)⁻¹) l j)) := by
    filter_upwards [hys, hdet.eventually_ne hQ] with u hu hqu
    exact alpha_fderiv_single S u hu hqu j
  have hcoef := (inverse_square_hasDerivAt (y j) (hy j)).comp_hasFDerivAt y
    ((ContinuousLinearMap.proj j : (n → ℂ) →L[ℂ] ℂ)).hasFDerivAt
  change HasFDerivAt (fun u : n → ℂ => 2 / (u j)^2) _ y at hcoef
  have hrow := (rowSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  have hcol := (colSumCLM j).hasFDerivAt.comp y (inverse_hasFDerivAt S y hy hQ)
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) j l) _ y at hrow
  change HasFDerivAt (fun u => ∑ l, ((inverseQ S u)⁻¹) l j) _ y at hcol
  have hh := ((hcoef.mul hrow).mul hcol).congr_of_eventuallyEq heq
  rw [hh.fderiv]
  have hr := row_fderiv_single S y hy hQ j k
  have hc := col_fderiv_single S y hy hQ j k
  rw [hrow.fderiv] at hr
  rw [hcol.fderiv] at hc
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.one_apply] at *
  rw [hr, hc]
  dsimp [rowSumCLM, colSumCLM]
  by_cases hjk : j = k
  · subst k
    simp <;> ring
  · simp [hjk, Ne.symm hjk] <;> ring

private lemma alpha_first_const (S : Matrix n n ℂ) (b : ℂ) (hb : b ≠ 0)
    (hQ : (inverseQ S (fun _ => b)).det ≠ 0)
    (hr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2)
    (hc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2) (j : n) :
    fderiv ℂ (alpha S) (fun _ => b) (Pi.single j 1) = 1 / 2 := by
  rw [alpha_fderiv_single S (fun _ => b) (fun _ => hb) hQ j, hr, hc]
  field_simp <;> ring

private lemma alpha_second_const (S : Matrix n n ℂ) (b : ℂ) (hb : b ≠ 0)
    (hQ : (inverseQ S (fun _ => b)).det ≠ 0)
    (hr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2)
    (hc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2) (j k : n) :
    fderiv ℂ (fun u => fderiv ℂ (alpha S) u (Pi.single j 1)) (fun _ => b) (Pi.single k 1) =
      (b^2)⁻¹ * (((inverseQ S (fun _ => b))⁻¹) j k +
        ((inverseQ S (fun _ => b))⁻¹) k j) - (if j = k then b⁻¹ else 0) := by
  rw [alpha_second_single S (fun _ => b) (fun _ => hb) hQ j k]
  simp_rw [hr, hc]
  by_cases hjk : j = k
  · subst k
    simp only [ite_true]
    field_simp <;> ring
  · simp only [hjk, Ne.symm hjk, ite_false, mul_zero, zero_mul, zero_add, sub_zero]
    field_simp <;> ring

end


theorem calH_closedForm {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A)
    (h : (Fin (d-1) → ℂ) → ℂ) (hh : IsLocalSolution A h) :
    calH h = (d : ℂ) *
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det /
      ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
        (skewAdjacency A).map (Int.castRingHom ℂ) *
          (skewAdjacency A).map (Int.castRingHom ℂ)).det := by
  cases d with
  | zero => omega
  | succ n =>
    let D : ℂ := ((n+1 : ℕ) : ℂ)
    let b : ℂ := z (n+1)
    let S := (skewAdjacency A).map (Int.castRingHom ℂ)
    let Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := D • 1 - S
    let V := Q⁻¹
    let T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := 1-D • (V+V.transpose)
    let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j k =>
      T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
        T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n)
    let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := Matrix.of fun i l =>
      (b^2)⁻¹ * (V i l + V l i) - (if i = l then b⁻¹ else 0)
    let L := appendLastLinear (n+1)
    have hD : D ≠ 0 := by
      dsimp [D]
      exact_mod_cast Nat.succ_ne_zero n
    have hb : b ≠ 0 := div_ne_zero (by norm_num) hD
    have htwo : 2 / b = D := by
      dsimp [b, z, D]
      field_simp
    have hrec : D⁻¹ = b / 2 := by
      dsimp [b, z, D]
      field_simp
      <;> ring
    have hQ : Q.det ≠ 0 := shiftedNegativeDetNeZero A
    have hQeq : inverseQ S (fun _ => b) = Q := by
      ext i j
      simp only [inverseQ, Q, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, htwo]
      split_ifs <;> simp
    have hQi : (inverseQ S (fun _ => b)).det ≠ 0 := by rwa [hQeq]
    have hSr : ∀ i, ∑ j, S i j = 0 := regularSkewRowSum A hd hA
    have hSc : ∀ j, ∑ i, S i j = 0 := regularSkewColSum A hd hA
    have hQr : ∀ i, ∑ j, Q i j = D := by
      intro i
      simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hSr]
    have hQc : ∀ j, ∑ i, Q i j = D := by
      intro j
      simp [Q, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply, hSc]
    have hVr : ∀ i, ∑ j, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2 := by
      simpa only [hQeq, hrec] using inverse_row_sum Q D hD hQ hQr
    have hVc : ∀ j, ∑ i, ((inverseQ S (fun _ => b))⁻¹) i j = b / 2 := by
      simpa only [hQeq, hrec] using inverse_col_sum Q D hD hQ hQc
    have hLsnoc (v : Fin n → ℂ) (s : ℂ) : L (v,s) = Fin.snoc v s := by
      rw [show L = appendLastLinear (n+1) from rfl, appendLastLinearApply]
      ext i
      change (@Fin.snoc n (fun _ => ℂ) v s) (Fin.ofNat (n+1) i.val) =
        (@Fin.snoc n (fun _ => ℂ) v s) i
      congr 1
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
    have hL0 : L ((fun _ => b), b) = (fun _ => b) := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    have hLj (j : Fin n) : L (Pi.single j 1, 0) = Pi.single j.castSucc 1 := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp
      · simp [Pi.single_apply]
    have hLl : L (0, 1) = Pi.single (Fin.last n) 1 := by
      rw [hLsnoc]
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [Pi.single_apply]
    have hα : ContDiffAt ℂ 2 (alpha S) (L ((fun _ => b), b)) := by
      rw [hL0]
      exact alpha_contDiffAt S (fun _ => b) (fun _ => hb) hQi
    have hg : ∀ᶠ y in 𝓝 (fun _ : Fin n => b), alpha S (L (y, h y)) = 1 := by
      have he := localSolution_resolvent_eq A hd hA h hh hQi
      filter_upwards [he] with y hy
      simpa only [show L = appendLastLinear (n+1) from rfl,
        appendLastLinearApply, alpha, inverseQ] using hy
    have hfirst (i : Fin (n+1)) :
        fderiv ℂ (alpha S) (L ((fun _ => b), b)) (Pi.single i 1) = 1/2 := by
      rw [hL0]
      exact alpha_first_const S b hb hQi hVr hVc i
    have hsecond (i l : Fin (n+1)) :
        WormaldAnalytic.second (𝕜 := ℂ) (alpha S) (L ((fun _ => b), b))
          (Pi.single i 1) (Pi.single l 1) = M i l := by
      rw [hL0]
      simpa only [WormaldAnalytic.second, M, Matrix.of_apply, hQeq] using
        alpha_second_const S b hb hQi hVr hVc i l
    have hlastne (i : Fin n) : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    have hcastlast (i : Fin n) : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
    have hmat : hessian (d := n+1) h = -H := by
      ext j k
      have he := WormaldAnalytic.hessian_of_implicit_coordinates hd hh L
        (fun j : Fin n => j.castSucc) (Fin.last n) hLj hLl
        (alpha S) hα hg (1/2) (by norm_num) hfirst M hsecond j k
      simp only [H, Matrix.neg_apply, Matrix.of_apply]
      rw [he]
      change 1 + (if j = k then 1 else 0) + (b / (1/2)) *
        (M j.castSucc k.castSucc - M j.castSucc (Fin.last n) -
          M (Fin.last n) k.castSucc + M (Fin.last n) (Fin.last n)) =
        -(T j.castSucc k.castSucc - T j.castSucc (Fin.last n) -
          T (Fin.last n) k.castSucc + T (Fin.last n) (Fin.last n))
      simp only [M, T, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.one_apply,
        Fin.castSucc_inj, hcastlast, hlastne, ite_false, ite_true]
      rw [← htwo]
      by_cases hjk : j = k <;> simp only [hjk, ite_true, ite_false]
      <;> field_simp [hb] <;> ring
    have hS : S.transpose = -S := by
      ext i j
      simp [S, skewAdjacency, adjacency]
    have hn : Even n := by
      obtain ⟨r, hr⟩ := regularOdd A hd hA
      refine ⟨r, ?_⟩
      omega
    have hdet := skew_difference_det n S D hD hS (regularOdd A hd hA) hQ hSr
    change (hessian (d := n+1) h).det = D * (D^2 • 1 + S*S).det / (D^2 • 1-S*S).det
    rw [hmat, Matrix.det_neg, Fintype.card_fin]
    simp only [Nat.add_sub_cancel, hn.neg_one_pow, one_mul]
    simpa only [H, T, V, Q, D, Nat.cast_add, Nat.cast_one] using hdet

theorem result : claim := by
  intro d hd A hA
  refine ⟨regularLocalSolution A hd hA, ?_⟩
  intro h hh
  let N : ℂ := ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) -
    (skewAdjacency A).map (Int.castRingHom ℂ) *
      (skewAdjacency A).map (Int.castRingHom ℂ)).det
  let D : ℂ := ((d : ℂ)^2 • (1 : Matrix (Fin d) (Fin d) ℂ) +
    (skewAdjacency A).map (Int.castRingHom ℂ) *
      (skewAdjacency A).map (Int.castRingHom ℂ)).det
  obtain ⟨q, hq0, hq⟩ := regularAlgebraicSquare A hd hA
  change N / D = (q : ℂ)^2 at hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hratio : N / D ≠ 0 := by rw [hq]; exact pow_ne_zero _ hqc
  have hN : N ≠ 0 := by
    intro hn
    exact hratio (by rw [hn, zero_div])
  have hD : D ≠ 0 := by
    intro hd
    exact hratio (by rw [hd, div_zero])
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hclosed : calH h = (d : ℂ) * D / N := calH_closedForm A hd hA h hh
  refine ⟨?_, q, ?_⟩
  · rw [hclosed]
    exact div_ne_zero (mul_ne_zero hd0 hD) hN
  · rw [hclosed, ← hq]
    field_simp [hd0, hN, hD]

end D5.S3.Combinatorics.WormaldTournamentHessian.Result
