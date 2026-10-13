/- GID: D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Universal rational coefficients for the Camassa–Holm peakon transfer expansion. -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion

open scoped BigOperators
open Matrix

noncomputable section

private abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℂ
private abbrev PS := PowerSeries ℂ

/-- The hyperbolic phase, with real positions and a complex parameter. -/
def phase {N : ℕ} (q : Fin N → ℝ) (ν : ℂ) (i j : Fin N) : ℂ :=
  ν * ((q i - q j : ℝ) : ℂ) / 2

/-- The antisymmetric source matrix with factorized weights. -/
def A {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) : Mat N :=
  Matrix.of fun i j => w i * w j * Complex.sinh (phase q ν i j)

/-- The symmetric hyperbolic source matrix. -/
def T {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) : Mat N :=
  Matrix.of fun i j => w i * w j * Complex.cosh (phase q ν i j)

/-- The position sign is zero on the diagonal and at coincident positions. -/
def S {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) : Mat N :=
  Matrix.of fun i j => (SignType.sign (q i - q j) : ℂ) * A w q ν i j

def Lambda (γ z : ℂ) : ℂ := (z ^ 2 - 1) / (2 * z + γ)

def xi (γ z : ℂ) : ℂ := (z ^ 2 + γ * z + 1) / (2 * z + γ)

/-- The spectral Lax matrix uses ordinary, rather than conjugate, transpose. -/
def L {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ z : ℂ) : Mat N :=
  S w q ν + Lambda γ z • T w q ν + xi γ z • A w q ν

def tau {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ z : ℂ) (m : ℕ) : ℂ :=
  Matrix.trace (L w q ν γ z ^ m)

def h {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ : ℂ) (k : ℕ) : ℂ :=
  (k : ℂ) * Matrix.trace
    ((T w q ν + (γ / 2) • A w q ν) * (S w q ν + A w q ν) ^ (k - 1))

abbrev CoeffFamily := (m : ℕ) → Nat.Partition m → ℚ

def multiplicityFactor {m : ℕ} (π : Nat.Partition m) : ℕ :=
  ∏ r ∈ π.parts.toFinset, Nat.factorial (π.parts.count r)

def universalCoeff (m : ℕ) (π : Nat.Partition m) : ℚ :=
  (m : ℚ) * (Nat.factorial (π.parts.card - 1) : ℚ) /
    ((π.parts.prod : ℚ) * (multiplicityFactor π : ℚ))

def partMonomial {m : ℕ} (f : ℕ → ℂ) (π : Nat.Partition m) : ℂ :=
  (π.parts.map f).prod

def prescribedValues (a : CoeffFamily) : Prop :=
  (∀ (m : ℕ) (π : Nat.Partition m), 0 < m → π.parts = {m} → a m π = 1) ∧
  (∀ (m : ℕ) (π : Nat.Partition m),
    0 < m → π.parts = Multiset.replicate m 1 → a m π = 1) ∧
  (∀ (m j : ℕ) (π : Nat.Partition m), j < m - 1 →
    π.parts = (m - j) ::ₘ Multiset.replicate j 1 → a m π = (m : ℚ) / ((m - j : ℕ) : ℚ))

def expansion (a : CoeffFamily) : Prop :=
  ∀ (N m : ℕ) (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ z : ℂ),
    0 < m → 2 * z + γ ≠ 0 →
    tau w q ν γ z m = ∑ π : Nat.Partition m,
      Lambda γ z ^ π.parts.card * (a m π : ℂ) * partMonomial (h w q ν γ) π

def claim : Prop := ∃ a : CoeffFamily,
  a = universalCoeff ∧ prescribedValues a ∧ expansion a

private lemma B_entry_eq_zero_of_le {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ)
    (ν : ℂ) (i j : Fin N) (hq : q i ≤ q j) : (S w q ν + A w q ν) i j = 0 := by
  rcases hq.lt_or_eq with hlt | heq
  · simp only [Matrix.add_apply, S, Matrix.of_apply,
      sign_neg (sub_neg.mpr hlt), SignType.coe_neg_one, neg_one_mul, neg_add_cancel]
  · simp [S, A, phase, heq]

private def u {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) (i : Fin N) : ℂ :=
  w i * Complex.exp (ν * (q i : ℂ) / 2)

private def v {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) (i : Fin N) : ℂ :=
  w i * Complex.exp (-(ν * (q i : ℂ) / 2))

private def U {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) : Mat N :=
  Matrix.vecMulVec (u w q ν) (v w q ν)

private def V {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) : Mat N :=
  Matrix.vecMulVec (v w q ν) (u w q ν)

private lemma source_rank_two {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) :
    T w q ν = (1 / 2 : ℂ) • (U w q ν + V w q ν) ∧
    A w q ν = (1 / 2 : ℂ) • (U w q ν - V w q ν) := by
  have hp (i j : Fin N) : phase q ν i j = ν * (q i : ℂ) / 2 + -(ν * (q j : ℂ) / 2) := by
    simp only [phase, Complex.ofReal_sub]; ring
  have hn (i j : Fin N) : -phase q ν i j = -(ν * (q i : ℂ) / 2) + ν * (q j : ℂ) / 2 := by
    rw [hp]; ring
  constructor <;> ext i j <;>
    simp only [T, A, U, V, u, v, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, Complex.cosh, Complex.sinh] <;>
      rw [hn, hp] <;> simp only [Complex.exp_add] <;> ring

private lemma B_sub_transpose {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) :
    (S w q ν + A w q ν) - (S w q ν + A w q ν)ᵀ = U w q ν - V w q ν := by
  have ha (i j : Fin N) : A w q ν j i = -A w q ν i j := by
    have hp : phase q ν j i = -phase q ν i j := by
      simp only [phase, Complex.ofReal_sub]; ring
    simp only [A, Matrix.of_apply, hp, Complex.sinh_neg]; ring
  have hs (i j : Fin N) : S w q ν j i = S w q ν i j := by
    have he : q j - q i = -(q i - q j) := by ring
    change (SignType.sign (q j - q i) : ℂ) * A w q ν j i =
      (SignType.sign (q i - q j) : ℂ) * A w q ν i j
    rw [he, Left.sign_neg, SignType.coe_neg, ha i j]; ring
  have hh := (source_rank_two w q ν).2
  ext i j
  have he := congrArg (fun M : Mat N => M i j) hh
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at he
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
  rw [hs i j, ha i j]
  linear_combination 2 * he

private lemma spectral_conic (γ z : ℂ) (hz : 2 * z + γ ≠ 0) :
    xi γ z ^ 2 = Lambda γ z ^ 2 + γ * Lambda γ z + 1 := by
  unfold xi Lambda
  rw [div_pow, div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hz)).2
  rw [add_mul, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hz), one_mul]
  have hc : γ * ((z ^ 2 - 1) / (2 * z + γ)) * (2 * z + γ) ^ 2 =
      γ * (z ^ 2 - 1) * (2 * z + γ) := by
    calc
      _ = γ * (((z ^ 2 - 1) / (2 * z + γ)) * (2 * z + γ)) * (2 * z + γ) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hz]
  rw [hc]
  ring

private lemma det_one_sub_smul_of_strict_support {ι α R : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder α] [CommRing R]
    (r : ι → α) (M : Matrix ι ι R) (t : R)
    (hM : ∀ i j, r i ≤ r j → M i j = 0) : Matrix.det (1 - t • M) = 1 := by
  classical
  let b : ι → OrderDual α := OrderDual.toDual ∘ r
  have hb : Matrix.BlockTriangular (1 - t • M) b := by
    intro i j hij
    have hr : r i < r j := hij
    have hn : i ≠ j := fun he => by subst j; exact lt_irrefl _ hr
    simp [Matrix.sub_apply, Matrix.smul_apply, hn, hM i j hr.le]
  rw [hb.det]
  apply Finset.prod_eq_one
  intro a _
  have he : (1 - t • M).toSquareBlock b a = 1 := by
    ext i j
    have hr : r i = r j := congrArg OrderDual.ofDual (i.property.trans j.property.symm)
    simp [Matrix.toSquareBlock_def, Matrix.sub_apply,
      Matrix.smul_apply, hM i j hr.le, Matrix.one_apply, Subtype.ext_iff]
  rw [he, Matrix.det_one]

private def liftMat {N : ℕ} (M : Mat N) : Matrix (Fin N) (Fin N) PS :=
  M.map PowerSeries.C

private def pencil {N : ℕ} (M : Mat N) : Matrix (Fin N) (Fin N) PS :=
  1 - (PowerSeries.X : PS) • liftMat M

private def geom {N : ℕ} (M : Mat N) : Matrix (Fin N) (Fin N) PS :=
  Matrix.of fun i j => PowerSeries.mk fun n => (M ^ n) i j

private lemma coeff_lift_mul_geom {N : ℕ} (K M : Mat N) (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n ((liftMat K * geom M) i j) = (K * M ^ n) i j := by
  simp only [Matrix.mul_apply, map_sum, liftMat, Matrix.map_apply,
    PowerSeries.coeff_C_mul, geom, Matrix.of_apply, PowerSeries.coeff_mk]

private lemma coeff_geom {N : ℕ} (M : Mat N) (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n (geom M i j) = (M ^ n) i j := by
  simp only [geom, Matrix.of_apply, PowerSeries.coeff_mk]

private lemma coeff_matrix_one {N : ℕ} (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n ((1 : Matrix (Fin N) (Fin N) PS) i j) =
      if n = 0 then (1 : Mat N) i j else 0 := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private lemma pencil_mul_geom {N : ℕ} (M : Mat N) : pencil M * geom M = 1 := by
  rw [pencil, sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_geom,
    coeff_matrix_one]
  rcases n with _ | n
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_lift_mul_geom, ← pow_succ']
    simp

private lemma geom_mul_pencil {N : ℕ} (M : Mat N) : geom M * pencil M = 1 := by
  rw [pencil, mul_sub, mul_one, Matrix.mul_smul]
  ext i j n
  have hc (n : ℕ) : PowerSeries.coeff n ((geom M * liftMat M) i j) = (M ^ n * M) i j := by
    simp only [Matrix.mul_apply, map_sum, liftMat, Matrix.map_apply,
      PowerSeries.coeff_mul_C, geom, Matrix.of_apply, PowerSeries.coeff_mk]
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_geom,
    coeff_matrix_one]
  rcases n with _ | n
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [PowerSeries.coeff_succ_X_mul, hc, ← pow_succ]
    simp

private lemma det_rank_two {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (E Rm : Matrix ι ι R) (hRE : Rm * E = 1) (u v : ι → R) (a b : R) :
    Matrix.det (E - a • Matrix.vecMulVec u v - b • Matrix.vecMulVec v u) =
      Matrix.det E *
        (1 - a * Matrix.trace (Matrix.vecMulVec u v * Rm) -
          b * Matrix.trace (Matrix.vecMulVec v u * Rm) + a * b *
          (Matrix.trace (Matrix.vecMulVec u v * Rm) *
            Matrix.trace (Matrix.vecMulVec v u * Rm) -
            Matrix.trace (Matrix.vecMulVec v v * Rm) *
              Matrix.trace (Matrix.vecMulVec u u * Rm))) := by
  classical
  let P : Matrix ι (Fin 2) R := fun i k => if k = 0 then a * u i else b * v i
  let Q : Matrix (Fin 2) ι R := fun k j =>
    if k = 0 then (v ᵥ* Rm) j else (u ᵥ* Rm) j
  have hPQ : P * Q = a • Matrix.vecMulVec u (v ᵥ* Rm) +
      b • Matrix.vecMulVec v (u ᵥ* Rm) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [P, Q, Matrix.vecMulVec_apply, mul_assoc]
  have hfactor : E - a • Matrix.vecMulVec u v - b • Matrix.vecMulVec v u =
      (1 - P * Q) * E := by
    rw [hPQ, sub_mul, one_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul, hRE, Matrix.vecMul_one, Matrix.vecMul_one]
    abel
  rw [hfactor, Matrix.det_mul, Matrix.det_one_sub_mul_comm]
  have hQP : Q * P =
      !![a * ((v ᵥ* Rm) ⬝ᵥ u), b * ((v ᵥ* Rm) ⬝ᵥ v);
         a * ((u ᵥ* Rm) ⬝ᵥ u), b * ((u ᵥ* Rm) ⬝ᵥ v)] := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, dotProduct, Finset.mul_sum, mul_comm, mul_assoc]
  rw [hQP, Matrix.det_fin_two]
  simp [Matrix.sub_apply, Matrix.vecMulVec_mul,
    Matrix.trace_vecMulVec, dotProduct_comm]
  ring

private lemma liftMat_add {N : ℕ} (M K : Mat N) :
    liftMat (M + K) = liftMat M + liftMat K := by
  apply Matrix.ext
  intro i j
  exact map_add (PowerSeries.C : ℂ →+* PS) (M i j) (K i j)

private lemma liftMat_smul {N : ℕ} (a : ℂ) (M : Mat N) :
    liftMat (a • M) = PowerSeries.C a • liftMat M := by
  apply Matrix.ext
  intro i j
  exact map_mul (PowerSeries.C : ℂ →+* PS) _ _

private lemma liftMat_vecMulVec {N : ℕ} (u v : Fin N → ℂ) :
    liftMat (Matrix.vecMulVec u v) =
      Matrix.vecMulVec (PowerSeries.C ∘ u) (PowerSeries.C ∘ v) := by
  apply Matrix.ext
  intro i j
  exact map_mul (PowerSeries.C : ℂ →+* PS) _ _

private lemma pencil_perturbation {N : ℕ} (B K J : Mat N) (a b : ℂ) :
    pencil (B + a • K + b • J) = pencil B -
      ((PowerSeries.X : PS) * PowerSeries.C a) • liftMat K -
      ((PowerSeries.X : PS) * PowerSeries.C b) • liftMat J := by
  simp only [pencil, liftMat_add, liftMat_smul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private def rankTrace {N : ℕ} (B K : Mat N) : PS :=
  PowerSeries.X * Matrix.trace (liftMat K * geom B)

private def rankCross {N : ℕ} (B : Mat N) (u v : Fin N → ℂ) : PS :=
  (PowerSeries.X : PS) ^ 2 *
    (Matrix.trace (liftMat (Matrix.vecMulVec u v) * geom B) *
      Matrix.trace (liftMat (Matrix.vecMulVec v u) * geom B) -
      Matrix.trace (liftMat (Matrix.vecMulVec v v) * geom B) *
        Matrix.trace (liftMat (Matrix.vecMulVec u u) * geom B))

private lemma det_pencil_rank_two {N : ℕ} (B : Mat N) (u v : Fin N → ℂ)
    (hB : Matrix.det (pencil B) = 1) (a b : ℂ) :
    Matrix.det (pencil (B + a • Matrix.vecMulVec u v + b • Matrix.vecMulVec v u)) =
      1 - PowerSeries.C a * rankTrace B (Matrix.vecMulVec u v) -
        PowerSeries.C b * rankTrace B (Matrix.vecMulVec v u) +
        PowerSeries.C a * PowerSeries.C b * rankCross B u v := by
  rw [pencil_perturbation, liftMat_vecMulVec, liftMat_vecMulVec,
    det_rank_two (pencil B) (geom B) (geom_mul_pencil B), hB, one_mul]
  simp only [rankTrace, rankCross, liftMat_vecMulVec]
  ring

private lemma det_pencil_transpose {N : ℕ} (M : Mat N) :
    Matrix.det (pencil Mᵀ) = Matrix.det (pencil M) := by
  have he : pencil Mᵀ = (pencil M)ᵀ := by
    apply Matrix.ext
    intro i j
    simp only [pencil, liftMat, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.transpose_apply, smul_eq_mul]
    simp [Matrix.one_apply, eq_comm]
  rw [he, Matrix.det_transpose]

private lemma det_pencil_B {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) :
    Matrix.det (pencil (S w q ν + A w q ν)) = 1 := by
  apply det_one_sub_smul_of_strict_support q
  intro i j hij
  change PowerSeries.C ((S w q ν + A w q ν) i j) = 0
  rw [B_entry_eq_zero_of_le w q ν i j hij, map_zero]

private lemma rankCross_eq_sub {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) :
    rankCross (S w q ν + A w q ν) (u w q ν) (v w q ν) =
      rankTrace (S w q ν + A w q ν) (U w q ν) -
        rankTrace (S w q ν + A w q ν) (V w q ν) := by
  let B := S w q ν + A w q ν
  have he : B + (-1 : ℂ) • U w q ν + (1 : ℂ) • V w q ν = Bᵀ := by
    have hb := B_sub_transpose w q ν
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Mat N => M i j) hb
    simp only [Matrix.sub_apply, Matrix.transpose_apply] at hh
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    dsimp only [B] at *
    linear_combination hh
  have hd := det_pencil_rank_two B (u w q ν) (v w q ν) (det_pencil_B w q ν) (-1) 1
  change Matrix.det (pencil (B + (-1 : ℂ) • U w q ν + (1 : ℂ) • V w q ν)) = _ at hd
  rw [he, det_pencil_transpose, det_pencil_B, map_neg, map_one] at hd
  dsimp only [B, U, V] at *
  linear_combination hd

private lemma L_rank_two {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ z : ℂ) :
    L w q ν γ z = (S w q ν + A w q ν) +
      ((Lambda γ z + xi γ z - 1) / 2) • U w q ν +
      ((Lambda γ z - xi γ z + 1) / 2) • V w q ν := by
  have ht := (source_rank_two w q ν).1
  have ha := (source_rank_two w q ν).2
  rw [L, ht, ha]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma rankTrace_linear {N : ℕ} (B K J : Mat N) (a b : ℂ) :
    rankTrace B (a • K + b • J) =
      PowerSeries.C a * rankTrace B K + PowerSeries.C b * rankTrace B J := by
  simp only [rankTrace, liftMat_add, liftMat_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

private def H {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ : ℂ) : PS :=
  PowerSeries.X * Matrix.trace
    (liftMat (T w q ν + (γ / 2) • A w q ν) * geom (S w q ν + A w q ν))

private lemma det_pencil_L {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ)
    (ν γ z : ℂ) (hz : 2 * z + γ ≠ 0) :
    Matrix.det (pencil (L w q ν γ z)) =
      1 - PowerSeries.C (Lambda γ z) *
        (PowerSeries.X * Matrix.trace
          (liftMat (T w q ν + (γ / 2) • A w q ν) * geom (S w q ν + A w q ν))) := by
  let a := (Lambda γ z + xi γ z - 1) / 2
  let b := (Lambda γ z - xi γ z + 1) / 2
  let f := rankTrace (S w q ν + A w q ν) (U w q ν)
  let g := rankTrace (S w q ν + A w q ν) (V w q ν)
  have hc := spectral_conic γ z hz
  have ha : a - a * b = Lambda γ z * ((2 + γ) / 4) := by
    dsimp only [a, b]
    linear_combination (1 / 4 : ℂ) * hc
  have hb : b + a * b = Lambda γ z * ((2 - γ) / 4) := by
    dsimp only [a, b]
    linear_combination (-1 / 4 : ℂ) * hc
  have hd := det_pencil_rank_two (S w q ν + A w q ν)
    (u w q ν) (v w q ν) (det_pencil_B w q ν) a b
  rw [rankCross_eq_sub] at hd
  change Matrix.det (pencil ((S w q ν + A w q ν) + a • U w q ν + b • V w q ν)) =
    1 - PowerSeries.C a * f - PowerSeries.C b * g +
      PowerSeries.C a * PowerSeries.C b * (f - g) at hd
  have hk : T w q ν + (γ / 2) • A w q ν =
      ((2 + γ) / 4) • U w q ν + ((2 - γ) / 4) • V w q ν := by
    rw [(source_rank_two w q ν).1, (source_rank_two w q ν).2]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hh : H w q ν γ = PowerSeries.C ((2 + γ) / 4) * f +
      PowerSeries.C ((2 - γ) / 4) * g := by
    change rankTrace (S w q ν + A w q ν) (T w q ν + (γ / 2) • A w q ν) = _
    rw [hk, rankTrace_linear]
  have hap := congrArg (PowerSeries.C : ℂ →+* PS) ha
  have hbp := congrArg (PowerSeries.C : ℂ →+* PS) hb
  simp only [map_sub, map_add, map_mul] at hap hbp
  change Matrix.det (pencil (L w q ν γ z)) = 1 - PowerSeries.C (Lambda γ z) * H w q ν γ
  rw [L_rank_two, hd, hh]
  linear_combination -f * hap - g * hbp

private lemma coeff_H_zero {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ : ℂ) :
    PowerSeries.coeff 0 (H w q ν γ) = 0 := by
  exact PowerSeries.coeff_zero_X_mul _

private lemma coeff_H {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν γ : ℂ)
    (k : ℕ) (hk : 0 < k) : PowerSeries.coeff k (H w q ν γ) = h w q ν γ k / (k : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [H, PowerSeries.coeff_succ_X_mul]
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, coeff_lift_mul_geom]
  rw [h, Nat.succ_sub_one]
  change Matrix.trace _ = (n.succ : ℂ) * Matrix.trace _ / (n.succ : ℂ)
  exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).symm

end
end D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
