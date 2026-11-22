/- GID: D5/S3/Analytic/PetzDyadicStripEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzDyadicStripEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A faithful partial-trace entropy loss has an exact finite dyadic decomposition. -/

import D5.S3.Analytic.PetzStripGramRemainder
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz

/-! # Dyadic decomposition of faithful partial-trace entropy loss -/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace PetzDyadicStripEnergy

open PetzStripGramRemainder (stripGram logistic remainder remainder_quadratic_nonneg)
open ExponentialGramWeightedEvaluation (exponentialSum frequency)
open PetzExponentialBoundaryEvaluation (petzWeight petzWeight_pos)
open private cothFactor energy_integral logistic_gram_entry verticalExponential from
  D5.S3.Analytic.PetzStripGramRemainder
open private coth_half_sub_coth from D5.S3.Analytic.PetzStripFiniteSeries

noncomputable section

private theorem half_kernel (d : ℝ) :
    logistic (d / 2) = Real.cosh (d / 4) * logistic d ∧
      2 * cothFactor (d / 2) - cothFactor d = logistic d := by
  by_cases hd : d = 0
  · norm_num [hd, logistic, cothFactor]
  have hd' : d / 2 ≠ 0 := div_ne_zero hd (by norm_num)
  have hs : Real.sinh (d / 4) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero hd (by norm_num))
  have hc : Real.cosh (d / 4) ≠ 0 := (Real.cosh_pos _).ne'
  have hhalf : d / 2 / 2 = d / 4 := by ring
  have hsh : Real.sinh (d / 2) = 2 * Real.sinh (d / 4) * Real.cosh (d / 4) := by
    rw [← Real.sinh_two_mul]
    congr 1
    ring
  constructor
  · simp only [logistic, ite_eq_right hd, ite_eq_right hd', hhalf, hsh]
    field_simp [hs, hc]
    ring
  · simp only [logistic, cothFactor, ite_eq_right hd, ite_eq_right hd', hhalf]
    have h := coth_half_sub_coth hd'
    rw [hhalf] at h
    linear_combination (d / 2) * h

private theorem exp_half_add (x y : ℝ) :
    2 * (Real.exp (x / 4) * Real.exp (y / 4)) * Real.cosh ((y - x) / 4) =
      Real.exp (x / 2) + Real.exp (y / 2) := by
  rw [Real.cosh_eq]
  calc
    _ = Real.exp (x / 4 + y / 4 + (y - x) / 4) +
        Real.exp (x / 4 + y / 4 + -((y - x) / 4)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by
      rw [show x / 4 + y / 4 + (y - x) / 4 = y / 2 by ring,
        show x / 4 + y / 4 + -((y - x) / 4) = x / 2 by ring, add_comm]

/-- The remainder of the logistic jump is twice the strip Gram at half frequency. -/
theorem remainder_eq_two_mul_stripGram_half (x y : ℝ) :
    remainder x y = 2 * stripGram (x / 2) (y / 2) := by
  obtain ⟨hlog, hcoth⟩ := half_kernel (y - x)
  unfold remainder stripGram
  rw [show y / 2 - x / 2 = (y - x) / 2 by ring,
    show x / 2 / 2 = x / 4 by ring, show y / 2 / 2 = y / 4 by ring, hlog]
  linear_combination
    -(exp_half_add x y) * logistic (y - x) + hcoth

variable {ι : Type*} [Fintype ι]

/-- The real quadratic energy of the exact strip Gram. -/
def stripEnergy (x : ι → ℝ) (c : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, (star (c i) * c j) * (stripGram (x i) (x j) : ℂ)).re

private def jumpCoefficients (x : ι → ℝ) (c : ι → ℂ) (i : ι) : ℂ :=
  c i * (1 - (Real.exp (x i / 2) : ℂ))

/-- The logistic-weighted squared norm of the upper-minus-lower boundary amplitude. -/
def logisticEnergy (x : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ t : ℝ, petzWeight t * ‖exponentialSum x (jumpCoefficients x c) (t : ℂ)‖ ^ 2

private theorem logisticEnergy_eq_quadratic (x : ι → ℝ) (c : ι → ℂ) :
    (logisticEnergy x c : ℂ) =
      ∑ i, ∑ j, (star (c i) * c j) *
        (((1 - Real.exp (x i / 2)) * (1 - Real.exp (x j / 2)) * logistic (x j - x i) : ℝ) : ℂ) := by
  have h := energy_integral (jumpCoefficients x c) (fun i => verticalExponential 0 (x i))
    PetzLogisticMidline.upperWeight (fun i j => (logistic_gram_entry (x i) (x j)).1)
  have hexp (t : ℝ) :
      exponentialSum x (jumpCoefficients x c) (t : ℂ) =
        ∑ i, jumpCoefficients x c i * verticalExponential 0 (x i) t := by
    simp only [exponentialSum, frequency, verticalExponential, PetzLogisticMidline.line,
      Complex.ofReal_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_rotate Complex.I, mul_assoc (x i : ℂ)]
  unfold logisticEnergy
  simp_rw [hexp]
  change ((∫ t : ℝ, PetzLogisticMidline.upperWeight t *
    ‖∑ i, jumpCoefficients x c i * verticalExponential 0 (x i) t‖ ^ 2 : ℝ) : ℂ) = _
  rw [h.2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(logistic_gram_entry (x i) (x j)).2]
  simp only [jumpCoefficients, star_mul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

private theorem remainderEnergy_eq (x : ι → ℝ) (c : ι → ℂ) :
    (∑ i, ∑ j, (star (c i) * c j) * (remainder (x i) (x j) : ℂ)).re =
      2 * stripEnergy (fun i => x i / 2) c := by
  unfold stripEnergy
  simp_rw [remainder_eq_two_mul_stripGram_half, Complex.ofReal_mul, Complex.ofReal_ofNat,
    show ∀ a b : ℂ, a * (2 * b) = 2 * (a * b) by intro a b; ring, ← Finset.mul_sum]
  simp

private theorem stripEnergy_step (x : ι → ℝ) (c : ι → ℂ) :
    stripEnergy x c = logisticEnergy x c + 2 * stripEnergy (fun i => x i / 2) c := by
  rw [← remainderEnergy_eq x c, ← Complex.ofReal_re (logisticEnergy x c)]
  simp only [logisticEnergy_eq_quadratic, stripEnergy, remainder, Complex.ofReal_sub, mul_sub,
    Finset.sum_sub_distrib, Complex.sub_re]
  ring

private theorem stripEnergy_nonneg (x : ι → ℝ) (c : ι → ℂ) : 0 ≤ stripEnergy x c := by
  have h := remainder_quadratic_nonneg (fun i => 2 * x i) c
  rw [remainderEnergy_eq, show (fun i => 2 * x i / 2) = x by funext i; ring] at h
  linarith

private theorem logisticEnergy_nonneg (x : ι → ℝ) (c : ι → ℂ) : 0 ≤ logisticEnergy x c :=
  integral_nonneg fun t => mul_nonneg (petzWeight_pos t).le (sq_nonneg _)

/-- The exact strip energy is the sum of the first M dyadic logistic energies
and the strip energy of the remaining scaled family, with its exact weight. -/
theorem stripEnergy_dyadic (x : ι → ℝ) (c : ι → ℂ) (M : ℕ) :
    stripEnergy x c =
      (∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c) +
        (2 : ℝ) ^ M * stripEnergy (fun i => x i / 2 ^ M) c := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) M,
      stripEnergy_step (fun i => x i / 2 ^ M) c]
    simp_rw [div_mul_eq_div_div]
    ring

/-- At every finite cutoff the partial dyadic sum is nonnegative and bounded by
the original strip energy. -/
theorem stripEnergy_dyadic_lower_bound (x : ι → ℝ) (c : ι → ℂ) (M : ℕ) :
    0 ≤ ∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c ∧
      (∑ m ∈ Finset.range M, (2 : ℝ) ^ m * logisticEnergy (fun i => x i / 2 ^ m) c) ≤
        stripEnergy x c := by
  constructor
  · exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (logisticEnergy_nonneg _ c)
  · rw [stripEnergy_dyadic x c M]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (stripEnergy_nonneg _ c))

section Physical

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
open D5.S3.Quantum.Recovery.BKMFlagRefinement (relativeEntropyOfMatrices)

universe u

variable {n : Type*} {r e : Type u} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e]

private def spectralConj {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary

private def projection {X : Matrix n n ℂ} (hX : X.IsHermitian) (i : n) :
    Matrix n n ℂ :=
  spectralConj hX (diagonal (Pi.single i 1))

private def spectralFunction {X : Matrix n n ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    Matrix n n ℂ :=
  spectralConj hX (diagonal fun i => (f (hX.eigenvalues i) : ℂ))

private theorem spectralFunction_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    spectralFunction hX f = cfc f X := (hX.cfc_eq f).symm

private theorem spectralFunction_id {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    spectralFunction hX id = X := hX.spectral_theorem.symm

private theorem spectralFunction_sum {X : Matrix n n ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, (f (hX.eigenvalues i) : ℂ) • projection hX i = spectralFunction hX f := by
  simp only [projection, spectralFunction, ← map_smul, ← map_sum]
  congr 1
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply]
  · simp [Matrix.sum_apply, Matrix.smul_apply, hab]

private theorem projection_sum {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    ∑ i, projection hX i = 1 := by
  simpa [spectralFunction, Matrix.diagonal_one] using spectralFunction_sum hX (fun _ => 1)

private theorem projection_star {X : Matrix n n ℂ} (hX : X.IsHermitian) (i : n) :
    (projection hX i)ᴴ = projection hX i := by
  change star (spectralConj hX (diagonal (Pi.single i 1))) = _
  rw [← map_star]
  congr 1
  ext a b
  by_cases ha : a = b
  · subst b
    simp [Matrix.star_apply, Pi.single_apply, apply_ite]
  · simp [Matrix.star_apply, Matrix.diagonal_apply_ne _ ha, Matrix.diagonal_apply_ne _ (Ne.symm ha)]

private theorem projection_mul {X : Matrix n n ℂ} (hX : X.IsHermitian) (i j : n) :
    projection hX i * projection hX j = if i = j then projection hX i else 0 := by
  simp only [projection, ← map_mul, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    congr 2
    funext a
    by_cases he : a = i <;> simp [Pi.single_apply, he]
  · rw [ite_eq_right hij, ← map_zero (spectralConj hX), ← Matrix.diagonal_zero]
    congr 2
    funext a
    by_cases hi : a = i
    · subst a
      simp [Pi.single_apply, hij]
    · simp [Pi.single_apply, hi]

private theorem projection_mul_self {X : Matrix n n ℂ} (hX : X.IsHermitian) (i : n) :
    projection hX i * X = (hX.eigenvalues i : ℂ) • projection hX i := by
  have he : projection hX i * X = projection hX i * spectralFunction hX id :=
    congrArg (fun Y => projection hX i * Y) (spectralFunction_id hX).symm
  rw [he]
  simp only [projection, spectralFunction, ← map_mul, ← map_smul, Matrix.diagonal_mul_diagonal]
  congr 1
  ext a b
  by_cases h : a = b
  · subst b
    by_cases hi : a = i
    · subst a
      simp
    · simp [Pi.single_apply, hi]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply]

private theorem spectralFunction_star {X : Matrix n n ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (spectralFunction hX f)ᴴ = spectralFunction hX f := by
  rw [← spectralFunction_sum]
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, projection_star]

private theorem spectralFunction_mul {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (f g : ℝ → ℝ) :
    spectralFunction hX f * spectralFunction hX g =
      spectralFunction hX (fun x => f x * g x) := by
  simp only [spectralFunction, ← map_mul, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

private def root {X : Matrix n n ℂ} (hX : X.IsHermitian) :=
  spectralFunction hX Real.sqrt

private theorem root_square {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    root hX.isHermitian * root hX.isHermitian = X := by
  rw [root, spectralFunction_mul]
  refine Eq.trans ?_ (spectralFunction_id hX.isHermitian)
  simp only [spectralFunction, id_eq]
  congr 2
  funext i
  rw [Real.mul_self_sqrt (hX.eigenvalues_nonneg i)]

private def lift (X : Matrix r r ℂ) : Matrix (r × e) (r × e) ℂ :=
  X ⊗ₖ (1 : Matrix e e ℂ)

private theorem lift_mul (X Y : Matrix r r ℂ) :
    (lift X * lift Y : Matrix (r × e) (r × e) ℂ) = lift (X * Y) := by
  simp only [lift, ← Matrix.mul_kronecker_mul, mul_one]

private def liftLinear : Matrix r r ℂ →ₗ[ℂ] Matrix (r × e) (r × e) ℂ where
  toFun := lift
  map_add' X Y := by simp only [lift, Matrix.add_kronecker]
  map_smul' c X := by simp only [lift, Matrix.smul_kronecker, RingHom.id_apply]

private theorem trace_lift (X : Matrix r r ℂ) (A : Matrix (r × e) (r × e) ℂ) :
    (lift X * A).trace = (X * partialTraceRight A).trace := by
  rw [← trace_partialTraceRight]
  exact congrArg Matrix.trace (partialTraceRight_embed_mul A X)

private theorem trace_lift_sandwich (X Y Z : Matrix r r ℂ)
    (A : Matrix (r × e) (r × e) ℂ) :
    (lift X * (lift Y * A * lift Z)).trace = (X * (Y * partialTraceRight A * Z)).trace := by
  rw [trace_lift]
  change (X * partialTraceRight
    ((Y ⊗ₖ (1 : Matrix e e ℂ)) * A * (Z ⊗ₖ (1 : Matrix e e ℂ)))).trace = _
  rw [partialTraceRight_mul_embed ((Y ⊗ₖ (1 : Matrix e e ℂ)) * A) Z,
    partialTraceRight_embed_mul A Y]

private theorem lift_projection_star {X : Matrix r r ℂ} (hX : X.IsHermitian) (i : r) :
    (lift (projection hX i) : Matrix (r × e) (r × e) ℂ)ᴴ = lift (projection hX i) := by
  simp only [lift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, projection_star]

private def coordinates {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * X * (hB.eigenvectorUnitary : Matrix n n ℂ)

private theorem coordinates_trace {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (X Y : Matrix n n ℂ) :
    ∑ a, ∑ b, star (coordinates hA hB X a b) * coordinates hA hB Y a b =
      (Xᴴ * Y).trace := by
  have entries (V W : Matrix n n ℂ) :
      ∑ a, ∑ b, star (V a b) * W a b = (Vᴴ * W).trace := by
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [entries]
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hv : V * Vᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  change ((Uᴴ * X * V)ᴴ * (Uᴴ * Y * V)).trace = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h : Vᴴ * (Xᴴ * U) * (Uᴴ * Y * V) = Vᴴ * ((Xᴴ * (U * Uᴴ) * Y) * V) := by
    noncomm_ring
  rw [h, hu, mul_one, Matrix.trace_mul_comm Vᴴ,
    Matrix.mul_assoc (Xᴴ * Y), hv, mul_one]

private theorem coordinates_trace_prod {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (X Y : Matrix n n ℂ) :
    ∑ ab : n × n, star (coordinates hA hB X ab.1 ab.2) * coordinates hA hB Y ab.1 ab.2 =
      (Xᴴ * Y).trace := by
  rw [Fintype.sum_prod_type]
  exact coordinates_trace hA hB X Y

private def sourceEdge (A : Matrix (r × e) (r × e) ℂ) (hA : A.IsHermitian)
    {P Q : Matrix r r ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (k : r × r) :
    Matrix (r × e) (r × e) ℂ :=
  root hA * lift (projection hP k.1) * lift (projection hQ k.2)

private def targetEdge (B : Matrix (r × e) (r × e) ℂ) (hB : B.IsHermitian)
    {P Q : Matrix r r ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (k : r × r) :
    Matrix (r × e) (r × e) ℂ :=
  (Real.sqrt (hP.eigenvalues k.1 / hQ.eigenvalues k.2) : ℂ) •
    (lift (projection hP k.1) * lift (projection hQ k.2) * root hB)

private def edgeDiagonal {P Q : Matrix r r ℂ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (k : r × r) : ℂ :=
  (hP.eigenvalues k.1 : ℂ) * (projection hQ k.2 * projection hP k.1).trace

private theorem projection_sandwich {X : Matrix r r ℂ}
    (hX : X.IsHermitian) (i j : r) :
    projection hX i * X * projection hX j =
      if i = j then (hX.eigenvalues i : ℂ) • projection hX i else 0 := by
  rw [projection_mul_self, smul_mul_assoc, projection_mul]
  split <;> simp

private theorem sourceEdge_gram (A : Matrix (r × e) (r × e) ℂ) (hA : A.PosSemidef)
    (hP : (partialTraceRight A).IsHermitian) {Q : Matrix r r ℂ}
    (hQ : Q.IsHermitian) (k l : r × r) :
    ((sourceEdge A hA.isHermitian hP hQ k)ᴴ * sourceEdge A hA.isHermitian hP hQ l).trace =
      if k = l then edgeDiagonal hP hQ k else 0 := by
  unfold sourceEdge
  simp only [Matrix.conjTranspose_mul, lift_projection_star, root, spectralFunction_star]
  change ((lift (projection hQ k.2) * (lift (projection hP k.1) * root hA.isHermitian)) *
    (root hA.isHermitian * lift (projection hP l.1) * lift (projection hQ l.2))).trace = _
  let E (i : r) : Matrix (r × e) (r × e) ℂ := lift (projection hP i)
  let F (j : r) : Matrix (r × e) (r × e) ℂ := lift (projection hQ j)
  let R := root hA.isHermitian
  change ((F k.2 * (E k.1 * R)) * (R * E l.1 * F l.2)).trace = _
  calc
    _ = (F k.2 * (E k.1 * (R * R) * E l.1) * F l.2).trace := by
      congr 1
      noncomm_ring
    _ = ((F l.2 * F k.2) * (E k.1 * A * E l.1)).trace := by
      rw [Matrix.trace_mul_cycle, root_square hA]
    _ = _ := by
      dsimp only [E, F]
      rw [lift_mul, trace_lift_sandwich, projection_mul, projection_sandwich]
      by_cases hi : k.1 = l.1 <;> by_cases hj : k.2 = l.2
      all_goals
        simp [hi, hj, eq_comm, Prod.ext_iff, mul_smul_comm, Matrix.trace_smul,
          smul_eq_mul, edgeDiagonal]

private theorem targetEdge_gram (B : Matrix (r × e) (r × e) ℂ) (hB : B.PosSemidef)
    {P : Matrix r r ℂ} (hP : P.PosSemidef) (hQ : (partialTraceRight B).PosDef)
    (k l : r × r) :
    ((targetEdge B hB.isHermitian hP.isHermitian hQ.isHermitian k)ᴴ *
      targetEdge B hB.isHermitian hP.isHermitian hQ.isHermitian l).trace =
      if k = l then edgeDiagonal hP.isHermitian hQ.isHermitian k else 0 := by
  unfold targetEdge
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.conjTranspose_mul, lift_projection_star, root, spectralFunction_star,
    smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  let E (i : r) : Matrix (r × e) (r × e) ℂ := lift (projection hP.isHermitian i)
  let F (j : r) : Matrix (r × e) (r × e) ℂ := lift (projection hQ.isHermitian j)
  let R := root hB.isHermitian
  have htrace :
      ((R * (F k.2 * E k.1)) * (E l.1 * F l.2 * R)).trace =
        ((E k.1 * E l.1) * (F l.2 * B * F k.2)).trace := by
    calc
      _ = ((R * F k.2) * ((E k.1 * E l.1) * (F l.2 * R))).trace := by
        congr 1
        noncomm_ring
      _ = (((E k.1 * E l.1) * (F l.2 * R)) * (R * F k.2)).trace :=
        Matrix.trace_mul_comm _ _
      _ = ((E k.1 * E l.1) * (F l.2 * (R * R) * F k.2)).trace := by
        congr 1
        noncomm_ring
      _ = _ := by rw [root_square hB]
  change (Real.sqrt (hP.isHermitian.eigenvalues l.1 / hQ.isHermitian.eigenvalues l.2) : ℂ) *
    ((Real.sqrt (hP.isHermitian.eigenvalues k.1 / hQ.isHermitian.eigenvalues k.2) : ℂ) *
      ((R * (F k.2 * E k.1)) * (E l.1 * F l.2 * R)).trace) = _
  rw [htrace]
  dsimp only [E, F]
  rw [lift_mul, trace_lift_sandwich, projection_mul, projection_sandwich]
  by_cases hi : k.1 = l.1 <;> by_cases hj : k.2 = l.2
  · have hkl : k = l := Prod.ext hi hj
    subst l
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, mul_smul_comm, Matrix.trace_smul,
      smul_eq_mul, edgeDiagonal, Matrix.trace_mul_comm (projection hP.isHermitian k.1)]
    have hq := hQ.eigenvalues_pos k.2
    have hp := hP.eigenvalues_nonneg k.1
    rw [← mul_assoc (Real.sqrt _ : ℂ), ← Complex.ofReal_mul,
      Real.mul_self_sqrt (div_nonneg hp hq.le), ← mul_assoc, ← Complex.ofReal_mul,
      div_mul_cancel₀ _ hq.ne']
  all_goals simp [hi, hj, eq_comm, Prod.ext_iff]

private theorem spectralDiag_left {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * spectralFunction hA f =
      diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have hu : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
  rw [spectralFunction, spectralConj, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, one_mul]
  rfl

private theorem spectralDiag_right {B : Matrix n n ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    spectralFunction hB f * (hB.eigenvectorUnitary : Matrix n n ℂ) =
      (hB.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (f (hB.eigenvalues i) : ℂ)) := by
  have hu : (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hB.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
  rw [spectralFunction, spectralConj, Unitary.conjStarAlgAut_apply]
  change (_ * (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ) *
    (hB.eigenvectorUnitary : Matrix n n ℂ) = _
  rw [Matrix.mul_assoc, hu, mul_one]

private theorem coordinates_left {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (X : Matrix n n ℂ) (a b : n) :
    coordinates hA hB (spectralFunction hA f * X) a b =
      (f (hA.eigenvalues a) : ℂ) * coordinates hA hB X a b := by
  unfold coordinates
  rw [← Matrix.mul_assoc _ (spectralFunction hA f), spectralDiag_left,
    Matrix.mul_assoc (diagonal _), Matrix.mul_assoc (diagonal _), Matrix.diagonal_mul]

private theorem coordinates_right {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (X : Matrix n n ℂ) (a b : n) :
    coordinates hA hB (X * spectralFunction hB f) a b =
      (f (hB.eigenvalues b) : ℂ) * coordinates hA hB X a b := by
  unfold coordinates
  rw [Matrix.mul_assoc _ (X * spectralFunction hB f), Matrix.mul_assoc X,
    spectralDiag_right, ← Matrix.mul_assoc X, ← Matrix.mul_assoc _ (X * _),
    Matrix.mul_assoc _ X, Matrix.mul_diagonal, mul_comm]

private def coordinateLinear {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (a b : n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun X := coordinates hA hB X a b
  map_add' X Y := by simp only [coordinates, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c X := by
    simp only [coordinates, mul_smul_comm, smul_mul_assoc, Matrix.smul_apply,
      RingHom.id_apply]

private theorem sumEdge {A : Matrix (r × e) (r × e) ℂ} (hA : A.IsHermitian)
    {P Q : Matrix r r ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f g : r → ℂ) :
    ∑ k : r × r, (f k.1 * g k.2) • sourceEdge A hA hP hQ k =
      root hA * lift (∑ i, f i • projection hP i) * lift (∑ j, g j • projection hQ j) := by
  change _ = root hA * liftLinear (∑ i, f i • projection hP i) *
    liftLinear (∑ j, g j • projection hQ j)
  have hl (W : Matrix r r ℂ) : (liftLinear W : Matrix (r × e) (r × e) ℂ) = lift W := rfl
  rw [map_sum liftLinear, map_sum liftLinear]
  simp_rw [map_smul liftLinear]
  simp only [Fintype.sum_prod_type, sourceEdge, hl]
  simp only [Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [mul_comm (f i)]

variable [Nonempty e]

private theorem marginal_posDef {A : Matrix (r × e) (r × e) ℂ} (hA : A.PosDef) :
    (partialTraceRight A).PosDef := partialTraceRight_posDef A hA

/-- Logarithmic frequency for a joint eigenvector pair and a retained eigenvector pair. -/
def physicalFrequency {A B : Matrix (r × e) (r × e) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ab : (r × e) × (r × e)) (k : r × r) : ℝ :=
  (Real.log (hB.isHermitian.eigenvalues ab.2) - Real.log (hA.isHermitian.eigenvalues ab.1)) +
    (Real.log ((marginal_posDef hA).isHermitian.eigenvalues k.1) -
      Real.log ((marginal_posDef hB).isHermitian.eigenvalues k.2))

/-- Joint eigenbasis entry of the source square root times the product of the
lifted retained eigenprojections. Each eigenvector contributes its own index. -/
def physicalCoefficient {A B : Matrix (r × e) (r × e) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ab : (r × e) × (r × e)) (k : r × r) : ℂ :=
  coordinates hA.isHermitian hB.isHermitian
    (sourceEdge A hA.isHermitian (marginal_posDef hA).isHermitian
      (marginal_posDef hB).isHermitian k) ab.1 ab.2

private theorem exp_log_score {a b p q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) :
    Real.exp (((Real.log b - Real.log a) + (Real.log p - Real.log q)) / 2) *
      Real.sqrt a = Real.sqrt (p / q) * Real.sqrt b := by
  rw [Real.exp_half, Real.exp_add, Real.exp_sub, Real.exp_sub,
    Real.exp_log ha, Real.exp_log hb, Real.exp_log hp, Real.exp_log hq,
    ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

private theorem target_coordinates {A B : Matrix (r × e) (r × e) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (ab : (r × e) × (r × e)) (k : r × r) :
    (Real.exp (physicalFrequency hA hB ab k / 2) : ℂ) * physicalCoefficient hA hB ab k =
      coordinates hA.isHermitian hB.isHermitian
        (targetEdge B hB.isHermitian (marginal_posDef hA).isHermitian
          (marginal_posDef hB).isHermitian k) ab.1 ab.2 := by
  let hP := marginal_posDef hA
  let hQ := marginal_posDef hB
  let M : Matrix (r × e) (r × e) ℂ :=
    lift (projection hP.isHermitian k.1) * lift (projection hQ.isHermitian k.2)
  let L := coordinateLinear hA.isHermitian hB.isHermitian ab.1 ab.2
  change _ * coordinates hA.isHermitian hB.isHermitian
      (root hA.isHermitian * lift (projection hP.isHermitian k.1) *
        lift (projection hQ.isHermitian k.2)) ab.1 ab.2 =
    L ((Real.sqrt (hP.isHermitian.eigenvalues k.1 / hQ.isHermitian.eigenvalues k.2) : ℂ) •
      (M * root hB.isHermitian))
  rw [Matrix.mul_assoc, map_smul]
  change _ * coordinates hA.isHermitian hB.isHermitian
      (spectralFunction hA.isHermitian Real.sqrt * M) ab.1 ab.2 =
    _ * coordinates hA.isHermitian hB.isHermitian
      (M * spectralFunction hB.isHermitian Real.sqrt) ab.1 ab.2
  rw [coordinates_left, coordinates_right, ← mul_assoc, ← Complex.ofReal_mul,
    ← mul_assoc, ← Complex.ofReal_mul, physicalFrequency,
    exp_log_score (hA.eigenvalues_pos _) (hB.eigenvalues_pos _)
      (hP.eigenvalues_pos _) (hQ.eigenvalues_pos _)]

private theorem sumSource {A : Matrix (r × e) (r × e) ℂ} (hA : A.IsHermitian)
    {P Q : Matrix r r ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ∑ k, sourceEdge A hA hP hQ k = root hA := by
  simpa only [one_mul, one_smul, projection_sum, lift, Matrix.one_kronecker_one, mul_one]
    using sumEdge hA hP hQ (fun _ => 1) (fun _ => 1)

private theorem sumSourceLog {A : Matrix (r × e) (r × e) ℂ} (hA : A.IsHermitian)
    {P Q : Matrix r r ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ∑ k : r × r, ((Real.log (hP.eigenvalues k.1) -
      Real.log (hQ.eigenvalues k.2) : ℝ) : ℂ) • sourceEdge A hA hP hQ k =
      root hA * lift (spectralFunction hP Real.log - spectralFunction hQ Real.log) := by
  simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  have hp := sumEdge hA hP hQ (fun i => (Real.log (hP.eigenvalues i) : ℂ)) (fun _ => 1)
  have hq := sumEdge hA hP hQ (fun _ => 1) (fun j => (Real.log (hQ.eigenvalues j) : ℂ))
  simp only [mul_one, one_mul, one_smul, projection_sum, spectralFunction_sum,
    show (lift (1 : Matrix r r ℂ) : Matrix (r × e) (r × e) ℂ) = 1 by
      rw [lift, Matrix.one_kronecker_one]] at hp hq
  rw [hp, hq, ← Matrix.mul_sub]
  congr 1
  exact (map_sub liftLinear _ _).symm

private theorem physicalLinear {A B : Matrix (r × e) (r × e) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (∑ ab, ∑ k, ∑ l, (star (physicalCoefficient hA hB ab k) *
        physicalCoefficient hA hB ab l) *
      ((-(physicalFrequency hA hB ab k + physicalFrequency hA hB ab l) / 2 : ℝ) : ℂ)).re =
      relativeEntropyOfMatrices A B -
        relativeEntropyOfMatrices (partialTraceRight A) (partialTraceRight B) := by
  let hP := (marginal_posDef hA).isHermitian
  let hQ := (marginal_posDef hB).isHermitian
  let R := root hA.isHermitian
  let L := spectralFunction hA.isHermitian Real.log
  let M := spectralFunction hB.isHermitian Real.log
  let N := spectralFunction hP Real.log - spectralFunction hQ Real.log
  let Z := R * M - L * R + R * lift N
  have hc (ab : (r × e) × (r × e)) :
      ∑ k, physicalCoefficient hA hB ab k =
        coordinates hA.isHermitian hB.isHermitian R ab.1 ab.2 := by
    let F := coordinateLinear hA.isHermitian hB.isHermitian ab.1 ab.2
    change ∑ k, F (sourceEdge A hA.isHermitian hP hQ k) = F R
    rw [← map_sum, sumSource]
  have hx (ab : (r × e) × (r × e)) :
      ∑ k, (physicalFrequency hA hB ab k : ℂ) * physicalCoefficient hA hB ab k =
        coordinates hA.isHermitian hB.isHermitian Z ab.1 ab.2 := by
    let F := coordinateLinear hA.isHermitian hB.isHermitian ab.1 ab.2
    let d : ℂ := (Real.log (hB.isHermitian.eigenvalues ab.2) - Real.log (hA.isHermitian.eigenvalues ab.1) : ℝ)
    simp only [physicalFrequency, Complex.ofReal_add]
    change ∑ k : r × r, (d + ((Real.log (hP.eigenvalues k.1) -
      Real.log (hQ.eigenvalues k.2) : ℝ) : ℂ)) *
      F (sourceEdge A hA.isHermitian hP hQ k) = F Z
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← map_sum]
    simp_rw [← smul_eq_mul (α := ℂ), ← map_smul F]
    rw [← map_sum, sumSourceLog]
    rw [sumSource, map_smul]
    change d * coordinates hA.isHermitian hB.isHermitian R ab.1 ab.2 +
      F (R * lift N) = F Z
    simp only [Z, map_add, map_sub]
    change _ = coordinates hA.isHermitian hB.isHermitian (R * M) ab.1 ab.2 -
      coordinates hA.isHermitian hB.isHermitian (L * R) ab.1 ab.2 + F (R * lift N)
    rw [coordinates_right, coordinates_left]
    simp only [d, Complex.ofReal_sub]
    ring
  have hlinear (ab : (r × e) × (r × e)) :
      (∑ k, ∑ l, (star (physicalCoefficient hA hB ab k) *
        physicalCoefficient hA hB ab l) *
      ((-(physicalFrequency hA hB ab k + physicalFrequency hA hB ab l) / 2 : ℝ) : ℂ)).re =
      -(star (coordinates hA.isHermitian hB.isHermitian R ab.1 ab.2) *
        coordinates hA.isHermitian hB.isHermitian Z ab.1 ab.2).re := by
    let c := physicalCoefficient hA hB ab
    let x := physicalFrequency hA hB ab
    rw [← hc, ← hx]
    change (∑ k, ∑ l, (star (c k) * c l) * ((-(x k + x l) / 2 : ℝ) : ℂ)).re = _
    have h (k l : r × r) :
        (star (c k) * c l) * ((-(x k + x l) / 2 : ℝ) : ℂ) =
          (-1 / 2 : ℂ) * (star ((x k : ℂ) * c k) * c l +
            star (c k) * ((x l : ℂ) * c l)) := by
      push_cast
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    simp_rw [h, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← star_sum]
    set w : ℂ := star (∑ k, c k) * (∑ l, (x l : ℂ) * c l)
    have hw : star (∑ k, (x k : ℂ) * c k) * (∑ l, c l) = star w := by
      simp [w, star_mul, mul_comm]
    rw [hw]
    simp [Complex.mul_re, Complex.add_re, Complex.div_re]
    ring
  rw [Complex.re_sum]
  simp_rw [hlinear]
  rw [Finset.sum_neg_distrib, ← Complex.re_sum, coordinates_trace_prod]
  have hr : Rᴴ = R := spectralFunction_star _ _
  have hs : R * R = A := root_square hA.posSemidef
  have hcomm : R * L = L * R := by
    change spectralFunction _ _ * spectralFunction _ _ = spectralFunction _ _ * spectralFunction _ _
    rw [spectralFunction_mul, spectralFunction_mul]
    congr 1
    funext u
    exact mul_comm _ _
  rw [hr]
  have htrace : (R * Z).trace = (A * M).trace - (A * L).trace +
      (partialTraceRight A * N).trace := by
    have he : R * Z = A * M - A * L + A * lift N := by
      calc
        R * Z = (R * R) * M - (R * L) * R + (R * R) * lift N := by
          dsimp only [Z]
          noncomm_ring
        _ = _ := by
          have hmid : (R * L) * R = (R * R) * L := by
            rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc]
          rw [hmid, hs]
    rw [he, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_mul_comm A (lift N),
      trace_lift, Matrix.trace_mul_comm N (partialTraceRight A)]
  rw [htrace]
  unfold relativeEntropyOfMatrices CFC.log
  simp only [L, M, N, spectralFunction_cfc, Matrix.mul_sub, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re]
  ring

private theorem sumKernel {a k : Type*} [Fintype a] [Fintype k]
    (c : a → k → ℂ) (K : k → k → ℂ) :
    ∑ p, ∑ i, ∑ j, (star (c p i) * c p j) * K i j =
      ∑ i, ∑ j, (∑ p, star (c p i) * c p j) * K i j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- For faithful joint matrices the Umegaki loss under the actual partial trace
is the sum of the joint spectral strip quadratics, with eigenvector multiplicities. -/
theorem umegakiLoss_eq_stripEnergy {A B : Matrix (r × e) (r × e) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    relativeEntropyOfMatrices A B -
      relativeEntropyOfMatrices (partialTraceRight A) (partialTraceRight B) =
      ∑ ab, stripEnergy (physicalFrequency hA hB ab) (physicalCoefficient hA hB ab) := by
  classical
  let hP := marginal_posDef hA
  let hQ := marginal_posDef hB
  let d (k : r × r) :=
    Real.log (hP.isHermitian.eigenvalues k.1) - Real.log (hQ.isHermitian.eigenvalues k.2)
  let x := physicalFrequency hA hB
  let z := physicalCoefficient hA hB
  let w (ab : (r × e) × (r × e)) (k : r × r) :=
    (Real.exp (x ab k / 2) : ℂ) * z ab k
  have hg (k l : r × r) :
      ∑ ab, star (w ab k) * w ab l = ∑ ab, star (z ab k) * z ab l := by
    have hw (ab : (r × e) × (r × e)) (i : r × r) :
        w ab i = coordinates hA.isHermitian hB.isHermitian
          (targetEdge B hB.isHermitian hP.isHermitian hQ.isHermitian i) ab.1 ab.2 :=
      target_coordinates hA hB ab i
    simp only [hw, z, physicalCoefficient, coordinates_trace_prod]
    rw [sourceEdge_gram A hA.posSemidef, targetEdge_gram B hB.posSemidef
      hP.posSemidef hQ]
  have hd (ab : (r × e) × (r × e)) (k l : r × r) :
      x ab l - x ab k = d l - d k := by
    change physicalFrequency hA hB ab l - physicalFrequency hA hB ab k = _
    unfold physicalFrequency
    dsimp only [d, hP, hQ]
    ring
  let K (k l : r × r) := (logistic (d l - d k) : ℂ)
  let C (k l : r × r) := (cothFactor (d l - d k) : ℂ)
  have h (ab : (r × e) × (r × e)) (k l : r × r) :
      (star (z ab k) * z ab l) * (stripGram (x ab k) (x ab l) : ℂ) =
        (star (z ab k) * z ab l) * ((-(x ab k + x ab l) / 2 : ℝ) : ℂ) +
          (star (w ab k) * w ab l) * K k l - (star (z ab k) * z ab l) * C k l := by
    simp only [stripGram, hd, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
      w, K, C, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hdiag (k l : r × r) :
      ∑ ab, star (z ab k) * z ab l =
        if k = l then edgeDiagonal hP.isHermitian hQ.isHermitian k else 0 := by
    simp only [z, physicalCoefficient, coordinates_trace_prod]
    exact sourceEdge_gram A hA.posSemidef hP.isHermitian hQ.isHermitian k l
  have hcancel :
      (∑ ab, ∑ k, ∑ l, (star (w ab k) * w ab l) * K k l) =
        ∑ ab, ∑ k, ∑ l, (star (z ab k) * z ab l) * C k l := by
    rw [sumKernel, sumKernel]
    simp_rw [hg, hdiag]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hkl : k = l
    · subst l
      simp [K, C, logistic, cothFactor]
    · simp [hkl]
  rw [← physicalLinear hA hB]
  change _ = ∑ ab, stripEnergy (x ab) (z ab)
  simp only [stripEnergy, h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Complex.re_sum]
  rw [← hcancel]
  congr 1
  ring

/-- At any finite cutoff, the physical dyadic energies give a nonnegative lower
estimate for the Umegaki loss. The scaled spectral quadratics are the exact remainder. -/
theorem umegakiLoss_dyadic {A B : Matrix (r × e) (r × e) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (M : ℕ) :
    let loss := relativeEntropyOfMatrices A B -
      relativeEntropyOfMatrices (partialTraceRight A) (partialTraceRight B)
    let partialEnergy := ∑ ab, ∑ m ∈ Finset.range M, (2 : ℝ) ^ m *
      logisticEnergy (fun k => physicalFrequency hA hB ab k / 2 ^ m)
        (physicalCoefficient hA hB ab)
    let tail := ∑ ab, (2 : ℝ) ^ M *
      stripEnergy (fun k => physicalFrequency hA hB ab k / 2 ^ M)
        (physicalCoefficient hA hB ab)
    loss = partialEnergy + tail ∧ 0 ≤ partialEnergy ∧ partialEnergy ≤ loss := by
  dsimp only
  rw [umegakiLoss_eq_stripEnergy hA hB]
  constructor
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ab _ =>
      stripEnergy_dyadic (physicalFrequency hA hB ab) (physicalCoefficient hA hB ab) M
  · constructor
    · exact Finset.sum_nonneg fun ab _ =>
        (stripEnergy_dyadic_lower_bound (physicalFrequency hA hB ab)
          (physicalCoefficient hA hB ab) M).1
    · exact Finset.sum_le_sum fun ab _ =>
        (stripEnergy_dyadic_lower_bound (physicalFrequency hA hB ab)
          (physicalCoefficient hA hB ab) M).2

#print axioms umegakiLoss_eq_stripEnergy
#print axioms umegakiLoss_dyadic

end Physical

#print axioms stripEnergy
#print axioms logisticEnergy
#print axioms remainder_eq_two_mul_stripGram_half
#print axioms stripEnergy_dyadic
#print axioms stripEnergy_dyadic_lower_bound

end

end PetzDyadicStripEnergy
