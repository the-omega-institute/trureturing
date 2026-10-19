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
import Mathlib.RingTheory.PowerSeries.Derivative
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
  · unfold S
    simp only [Matrix.add_apply, Matrix.of_apply,
      sign_neg (sub_neg.mpr hlt), SignType.coe_neg_one, neg_one_mul, neg_add_cancel]
  · unfold S A phase
    simp [heq]

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
    unfold phase; simp only [Complex.ofReal_sub]; ring
  have hn (i j : Fin N) : -phase q ν i j = -(ν * (q i : ℂ) / 2) + ν * (q j : ℂ) / 2 := by
    rw [hp]; ring
  constructor <;> ext i j <;>
    dsimp only [T, A, U, V] <;>
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, Complex.cosh, Complex.sinh] <;>
      unfold u v <;> rw [hn, hp] <;> simp only [Complex.exp_add] <;> ring

private lemma B_sub_transpose {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ) (ν : ℂ) :
    (S w q ν + A w q ν) - (S w q ν + A w q ν)ᵀ = U w q ν - V w q ν := by
  have ha (i j : Fin N) : A w q ν j i = -A w q ν i j := by
    have hp : phase q ν j i = -phase q ν i j := by
      unfold phase; simp only [Complex.ofReal_sub]; ring
    unfold A
    simp only [Matrix.of_apply, hp, Complex.sinh_neg]; ring
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
  unfold liftMat geom
  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply,
    PowerSeries.coeff_C_mul, Matrix.of_apply, PowerSeries.coeff_mk]

private lemma coeff_geom {N : ℕ} (M : Mat N) (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n (geom M i j) = (M ^ n) i j := by
  unfold geom
  simp only [Matrix.of_apply, PowerSeries.coeff_mk]

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
  exact _root_.mul_eq_one_comm.mp (pencil_mul_geom M)

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
  unfold rankTrace rankCross
  simp only [liftMat_vecMulVec]
  ring

private lemma det_pencil_transpose {N : ℕ} (M : Mat N) :
    Matrix.det (pencil Mᵀ) = Matrix.det (pencil M) := by
  have he : pencil Mᵀ = (pencil M)ᵀ := by
    apply Matrix.ext
    intro i j
    unfold pencil liftMat
    simp only [Matrix.sub_apply, Matrix.smul_apply,
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
  unfold rankTrace
  simp only [liftMat_add, liftMat_smul, Matrix.add_mul, Matrix.smul_mul,
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

private lemma derivative_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → PS) :
    PowerSeries.derivative (∏ i ∈ s, f i) =
      ∑ i ∈ s, PowerSeries.derivative (f i) * ∏ k ∈ s.erase i, f k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    apply congrArg₂ (· + ·)
    · exact mul_comm _ _
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert]
    · ring
    · exact fun h => ha (Finset.mem_of_mem_erase h)

private lemma derivative_det_rows {N : ℕ} (M : Matrix (Fin N) (Fin N) PS) :
    PowerSeries.derivative (Matrix.det M) =
      ∑ i, Matrix.det (M.updateRow i (fun j => PowerSeries.derivative (M i j))) := by
  classical
  have hd (K : Matrix (Fin N) (Fin N) PS) :
      Matrix.det K = ∑ σ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤ) : PS)) * ∏ i, K i (σ i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hd, map_sum]
  simp_rw [Derivation.leibniz, Derivation.map_intCast, smul_zero, add_zero,
    smul_eq_mul, derivative_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have he : (fun k => (M.updateRow i (fun j => PowerSeries.derivative (M i j)))
      k (σ k)) = Function.update (fun k => M k (σ k)) i
        (PowerSeries.derivative (M i (σ i))) := by
    funext k
    by_cases hk : k = i
    · subst k; rw [Matrix.updateRow_self, Function.update_self]
    · rw [Matrix.updateRow_ne hk, Function.update_of_ne hk]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

private lemma derivative_det_of_inverse {N : ℕ}
    (M R : Matrix (Fin N) (Fin N) PS) (hRM : R * M = 1) :
    PowerSeries.derivative (Matrix.det M) =
      Matrix.det M * Matrix.trace ((M.map (PowerSeries.derivative)) * R) := by
  classical
  let D := M.map (PowerSeries.derivative)
  have he : D * R * M = D := by rw [Matrix.mul_assoc, hRM, Matrix.mul_one]
  rw [derivative_det_rows, Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (fun j => PowerSeries.derivative (M i j)) =
      ∑ k, ((D * R) i k) • M k := by
    funext j
    have hh := congrArg (fun K : Matrix (Fin N) (Fin N) PS => K i j) he
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      D, Matrix.map_apply] using hh.symm
  rw [hr, Matrix.det_updateRow_sum]
  change (D * R) i i * Matrix.det M = Matrix.det M * (D * R) i i
  exact mul_comm _ _

private def detSeries {N : ℕ} (M : Mat N) : PS := Matrix.det (pencil M)
private def traceSeries {N : ℕ} (M : Mat N) : PS :=
  PowerSeries.mk fun n => Matrix.trace (M ^ (n + 1))

private lemma detSeries_mul_traceSeries {N : ℕ} (M : Mat N) :
    detSeries M * traceSeries M = -PowerSeries.derivative (detSeries M) := by
  have hd : (pencil M).map (PowerSeries.derivative) = -liftMat M := by
    apply Matrix.ext
    intro i j
    unfold pencil liftMat
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, Derivation.leibniz, PowerSeries.derivative_X,
      PowerSeries.derivative_C, Matrix.neg_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have ht : Matrix.trace (liftMat M * geom M) = traceSeries M := by
    unfold traceSeries
    ext n
    simp only [Matrix.trace, map_sum, Matrix.diag_apply, coeff_lift_mul_geom,
      PowerSeries.coeff_mk, ← pow_succ']
  rw [detSeries, derivative_det_of_inverse _ _ (geom_mul_pencil M), hd,
    Matrix.neg_mul, Matrix.trace_neg, ht, mul_neg, neg_neg]

private lemma coeff_logderiv_of_one_sub (F G : PS)
    (hF : PowerSeries.coeff 0 F = 0)
    (hFG : (1 - F) * G = PowerSeries.derivative F)
    (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff (m - 1) G = (m : ℂ) *
      ∑ j ∈ Finset.Icc 1 m, PowerSeries.coeff m (F ^ j) / (j : ℂ) := by
  have hx : (PowerSeries.X : PS) ∣ F := PowerSeries.X_dvd_iff.mpr
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF)
  have hz : PowerSeries.coeff (m - 1) (F ^ m * G) = 0 :=
    PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hx m) G)
      _ (by omega)
  have he : G = (∑ r ∈ Finset.range m, F ^ r) * PowerSeries.derivative F + F ^ m * G := by
    rw [← hFG, ← mul_assoc, geom_sum_mul_neg]
    ring
  have hc : PowerSeries.coeff (m - 1) G =
      ∑ r ∈ Finset.range m, PowerSeries.coeff (m - 1)
        (F ^ r * PowerSeries.derivative F) := by
    rw [he, map_add, hz, add_zero, Finset.sum_mul, map_sum]
  rw [hc, Finset.mul_sum]
  have hs : (Finset.range m).sum (fun r => PowerSeries.coeff (m - 1)
      (F ^ r * PowerSeries.derivative F)) =
      (Finset.Icc 1 m).sum (fun j => PowerSeries.coeff (m - 1)
        (F ^ (j - 1) * PowerSeries.derivative F)) := by
    apply Finset.sum_bij (fun r _ => r + 1)
    · intro r hr; simp only [Finset.mem_range] at hr; exact Finset.mem_Icc.mpr (by omega)
    · intro a _ b _ hab; omega
    · intro b hb
      have := Finset.mem_Icc.mp hb
      refine ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro r _; simp only [Nat.add_sub_cancel]
  rw [hs]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Finset.mem_Icc.mp hj; omega)
  have hp := congrArg (PowerSeries.coeff (m - 1)) (PowerSeries.derivative_pow F j)
  rw [PowerSeries.coeff_derivative, show m - 1 + 1 = m by omega] at hp
  have hcast : (j : PS) = PowerSeries.C (j : ℂ) := by simp
  rw [hcast, mul_assoc, PowerSeries.coeff_C_mul] at hp
  have hmcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by
    exact_mod_cast (show m - 1 + 1 = m by omega)
  rw [hmcast] at hp
  rw [← mul_div_assoc]
  apply (eq_div_iff hj0).mpr
  linear_combination -hp

private lemma prod_monomial (s : Multiset ℕ) (f : ℕ → ℂ) :
    (s.map (fun k => PowerSeries.monomial k (f k))).prod =
      PowerSeries.monomial s.sum (s.map f).prod := by
  classical
  simpa only [Fin.prod_univ_fun_getElem s.toList (fun k => PowerSeries.monomial k (f k)),
    Fin.prod_univ_fun_getElem s.toList f, Fin.sum_univ_getElem,
    Multiset.prod_map_toList, Multiset.sum_toList] using
    (PowerSeries.prod_monomial (fun i : Fin s.toList.length => s.toList[i.1])
      (fun i => f s.toList[i.1]) Finset.univ)

private lemma coeff_pow_eq_partition_sum (F : PS) (hF : PowerSeries.coeff 0 F = 0)
    (m j : ℕ) :
    PowerSeries.coeff m (F ^ j) = ∑ π : Nat.Partition m,
      if π.parts.card = j then (π.parts.countPerms : ℂ) *
        (π.parts.map (fun k => PowerSeries.coeff k F)).prod else 0 := by
  classical
  let Q : PS := ∑ k ∈ Finset.Icc 1 m, PowerSeries.monomial k (PowerSeries.coeff k F)
  have htrunc : (PowerSeries.trunc (m + 1) F : PS) = Q := by
    change Polynomial.coeToPowerSeries.ringHom (PowerSeries.trunc (m + 1) F) = Q
    rw [PowerSeries.trunc_apply, map_sum]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial]
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m)]
    simp only [hF, map_zero, zero_add]
    rfl
  have hpow : PowerSeries.coeff m (F ^ j) = PowerSeries.coeff m (Q ^ j) := by
    have ht := congrArg (fun p : Polynomial ℂ => p.coeff m)
      (PowerSeries.trunc_trunc_pow F (m + 1) j)
    simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_self, if_true, htrunc] using ht.symm
  rw [hpow]
  dsimp only [Q]
  rw [Finset.sum_pow, map_sum]
  have hterm (s : Sym ℕ j) :
      PowerSeries.coeff m ((s.val.countPerms : PS) *
        (s.val.map (fun k => PowerSeries.monomial k (PowerSeries.coeff k F))).prod) =
      if s.val.sum = m then (s.val.countPerms : ℂ) *
        (s.val.map (fun k => PowerSeries.coeff k F)).prod else 0 := by
    rw [prod_monomial]
    have hc : (s.val.countPerms : PS) = PowerSeries.C (s.val.countPerms : ℂ) := by simp
    rw [hc, PowerSeries.coeff_C_mul, PowerSeries.coeff_monomial]
    by_cases hs : m = s.val.sum
    · rw [if_pos hs, if_pos hs.symm]
    · rw [if_neg hs, if_neg (Ne.symm hs), mul_zero]
  simp_rw [hterm]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun s hs => (⟨s.val,
    fun {k} hk => (Finset.mem_Icc.mp (Finset.mem_sym_iff.mp
      (Finset.mem_filter.mp hs).1 k hk)).1,
    (Finset.mem_filter.mp hs).2⟩ : Nat.Partition m))
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.property⟩
  · intro a _ b _ hab
    apply Subtype.ext
    exact congrArg Nat.Partition.parts hab
  · intro π hπ
    have hc := (Finset.mem_filter.mp hπ).2
    let s : Sym ℕ j := ⟨π.parts, hc⟩
    have hs : s ∈ (Finset.Icc 1 m).sym j := by
      apply Finset.mem_sym_iff.mpr
      intro k hk
      exact Finset.mem_Icc.mpr ⟨π.parts_pos hk, Nat.Partition.le_of_mem_parts hk⟩
    refine ⟨s, Finset.mem_filter.mpr ⟨hs, π.parts_sum⟩, ?_⟩
    exact Nat.Partition.ext rfl
  · intro s _; rfl

private lemma multiplicity_countPerms {m : ℕ} (π : Nat.Partition m) :
    multiplicityFactor π * π.parts.countPerms = Nat.factorial π.parts.card := by
  unfold multiplicityFactor Multiset.countPerms
  rw [Finsupp.multinomial_eq, Multiset.toFinsupp_support]
  change (∏ r ∈ π.parts.toFinset, (π.parts.count r).factorial) *
    Nat.multinomial π.parts.toFinset (fun r => π.parts.count r) = _
  rw [Nat.multinomial_spec, Multiset.toFinset_sum_count_eq]

private lemma universalCoeff_prescribed : prescribedValues universalCoeff := by
  unfold prescribedValues
  refine ⟨?_, ?_, ?_⟩
  · intro m π hm hp
    unfold universalCoeff multiplicityFactor
    rw [hp]
    simp [Nat.cast_ne_zero.mpr hm.ne']
  · intro m π hm hp
    have hmult : multiplicityFactor π = Nat.factorial m := by
      unfold multiplicityFactor
      rw [hp]
      simp [Multiset.toFinset_replicate, hm.ne']
    unfold universalCoeff
    rw [hp, hmult]
    simp only [Multiset.card_replicate, Multiset.prod_replicate, one_pow, Nat.cast_one,
      one_mul]
    have hf : (m : ℚ) * (Nat.factorial (m - 1) : ℚ) = (Nat.factorial m : ℚ) := by
      exact_mod_cast (Nat.mul_factorial_pred hm.ne')
    rw [hf, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))]
  · intro m j π hj hp
    have hd : 1 < m - j := by omega
    have hmult : multiplicityFactor π = Nat.factorial j := by
      unfold multiplicityFactor
      rw [hp]
      by_cases hj0 : j = 0
      · subst j; simp
      · simp [Multiset.toFinset_replicate, hj0, Multiset.count_cons,
          Multiset.count_replicate, ne_of_gt hd, (ne_of_gt hd).symm]
    unfold universalCoeff
    rw [hp, hmult]
    simp only [Multiset.card_cons, Multiset.card_replicate, Nat.add_sub_cancel,
      Multiset.prod_cons, Multiset.prod_replicate, one_pow, mul_one]
    exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

private lemma trace_power_log_sum {N : ℕ} (w : Fin N → ℂ) (q : Fin N → ℝ)
    (ν γ z : ℂ) (hz : 2 * z + γ ≠ 0) (m : ℕ) (hm : 0 < m) :
    tau w q ν γ z m = (m : ℂ) * ∑ j ∈ Finset.Icc 1 m,
      (Lambda γ z ^ j / (j : ℂ)) * PowerSeries.coeff m (H w q ν γ ^ j) := by
  have hd := detSeries_mul_traceSeries (L w q ν γ z)
  unfold detSeries at hd
  rw [det_pencil_L w q ν γ z hz] at hd
  change (1 - PowerSeries.C (Lambda γ z) * H w q ν γ) * traceSeries (L w q ν γ z) =
    -PowerSeries.derivative (1 - PowerSeries.C (Lambda γ z) * H w q ν γ) at hd
  have hf : PowerSeries.coeff 0 (PowerSeries.C (Lambda γ z) * H w q ν γ) = 0 := by
    rw [PowerSeries.coeff_C_mul, coeff_H_zero, mul_zero]
  have he := coeff_logderiv_of_one_sub _ _ hf
    (by simpa only [map_sub, PowerSeries.derivative_one, zero_sub, neg_neg] using hd) m hm
  have hc : PowerSeries.coeff (m - 1) (traceSeries (L w q ν γ z)) =
      tau w q ν γ z m := by
    unfold traceSeries tau
    simp only [PowerSeries.coeff_mk, show m - 1 + 1 = m by omega]
  rw [hc] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul]
  ring

private lemma partition_card_bounds {m : ℕ} (π : Nat.Partition m) (hm : 0 < m) :
    π.parts.card ∈ Finset.Icc 1 m := by
  have hn : π.parts.card ≠ 0 := by
    intro hc
    have hs := π.parts_sum
    rw [Multiset.card_eq_zero.mp hc, Multiset.sum_zero] at hs
    omega
  have hl : π.parts.card • (1 : ℕ) ≤ π.parts.sum :=
    Multiset.card_nsmul_le_sum (fun k hk => π.parts_pos hk)
  simp only [nsmul_eq_mul, mul_one, π.parts_sum] at hl
  exact Finset.mem_Icc.mpr ⟨by omega, hl⟩

private lemma partition_coefficient {m : ℕ} (π : Nat.Partition m) (hm : 0 < m)
    (f : ℕ → ℂ) :
    ((m : ℂ) / (π.parts.card : ℂ)) * (π.parts.countPerms : ℂ) *
      (π.parts.map (fun k => f k / (k : ℂ))).prod =
      (universalCoeff m π : ℂ) * (π.parts.map f).prod := by
  have hc : (π.parts.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (by have := Finset.mem_Icc.mp (partition_card_bounds π hm); omega)
  have hmult : (multiplicityFactor π : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero _) )
  have hcount : (multiplicityFactor π : ℂ) * (π.parts.countPerms : ℂ) =
      (π.parts.card : ℂ) * (Nat.factorial (π.parts.card - 1) : ℂ) := by
    exact_mod_cast (multiplicity_countPerms π).trans
      (Nat.mul_factorial_pred (Nat.cast_ne_zero.mp hc)).symm
  have ha : (m : ℂ) / (π.parts.card : ℂ) * (π.parts.countPerms : ℂ) =
      (m : ℂ) * (Nat.factorial (π.parts.card - 1) : ℂ) / (multiplicityFactor π : ℂ) := by
    apply (eq_div_iff hmult).mpr
    calc
      _ = ((m : ℂ) / (π.parts.card : ℂ)) *
          ((multiplicityFactor π : ℂ) * (π.parts.countPerms : ℂ)) := by ring
      _ = ((m : ℂ) / (π.parts.card : ℂ)) *
          ((π.parts.card : ℂ) * (Nat.factorial (π.parts.card - 1) : ℂ)) := by rw [hcount]
      _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hc]
  rw [Multiset.prod_map_div, ← Nat.cast_multiset_prod, ha]
  unfold universalCoeff
  rw [Rat.cast_div]
  simp only [Rat.cast_mul, Rat.cast_natCast, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

private lemma universalCoeff_expansion : expansion universalCoeff := by
  unfold expansion
  intro N m w q ν γ z hm hz
  rw [trace_power_log_sum w q ν γ z hz m hm]
  simp_rw [coeff_pow_eq_partition_sum _ (coeff_H_zero w q ν γ) m]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  have hc := partition_card_bounds π hm
  rw [Finset.sum_eq_single π.parts.card]
  · rw [if_pos rfl]
    have he : (π.parts.map (fun k => PowerSeries.coeff k (H w q ν γ))).prod =
        (π.parts.map (fun k => h w q ν γ k / (k : ℂ))).prod := by
      congr 1
      exact Multiset.map_congr rfl (fun k hk => coeff_H w q ν γ k (π.parts_pos hk))
    rw [he]
    calc
      _ = Lambda γ z ^ π.parts.card *
          (((m : ℂ) / (π.parts.card : ℂ)) * (π.parts.countPerms : ℂ) *
            (π.parts.map (fun k => h w q ν γ k / (k : ℂ))).prod) := by ring
      _ = _ := by rw [partition_coefficient π hm]; unfold partMonomial; ring
  · intro j _ hj
    rw [if_neg (Ne.symm hj), mul_zero, mul_zero]
  · exact fun hnot => (hnot hc).elim

/-- The universal formula gives the peakon transfer expansion and prescribed coefficient values. -/
theorem result : claim :=
  ⟨universalCoeff, rfl, universalCoeff_prescribed, universalCoeff_expansion⟩

end
end D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
