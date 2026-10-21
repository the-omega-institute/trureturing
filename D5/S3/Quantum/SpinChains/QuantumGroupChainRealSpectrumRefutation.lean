/- GID: D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim; result=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result; claim=D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim
   digest: A positive U_q(sl_2) spin chain can have nonreal eigenvalues. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000

open scoped BigOperators Matrix
open Matrix

namespace D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation

noncomputable section

def digit {n N : ℕ} (x : Fin ((n + 1) ^ N)) (k : Fin N) : Fin (n + 1) :=
  ⟨x.val / (n + 1) ^ (N - 1 - k.val) % (n + 1), by
    exact Nat.mod_lt _ (by omega)⟩

def qnum (γ t : ℝ) : ℝ := Real.sin (γ * t) / Real.sin γ

def q (γ : ℝ) : ℂ := (Real.cos γ : ℂ) + Complex.I * (Real.sin γ : ℂ)

def γ₀ : ℝ := Real.arccos (4 / 5)

def weight (n : ℕ) (i : Fin (n + 1)) : ℝ := (i.val : ℝ) - (n : ℝ) / 2

def E (n : ℕ) (γ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i.val = j.val + 1 then
    (Real.sqrt (qnum γ ((n - j.val : ℕ) : ℝ) * qnum γ ((j.val + 1 : ℕ) : ℝ)) : ℂ)
    else 0

def F (n : ℕ) (γ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if j.val = i.val + 1 then
    (Real.sqrt (qnum γ ((j.val : ℝ)) * qnum γ ((n - j.val + 1 : ℕ) : ℝ)) : ℂ)
    else 0

def K (n : ℕ) (γ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i => q (γ * weight n i))

def Kinv (n : ℕ) (γ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i => q (-(γ * weight n i)))

def tensorCasimir (n : ℕ) (γ : ℝ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  let de := Matrix.kroneckerMap (· * ·) (E n γ) (Kinv n γ) +
    Matrix.kroneckerMap (· * ·) (K n γ) (E n γ)
  let df := Matrix.kroneckerMap (· * ·) (F n γ) (Kinv n γ) +
    Matrix.kroneckerMap (· * ·) (K n γ) (F n γ)
  let dk := Matrix.kroneckerMap (· * ·) (K n γ) (K n γ)
  let dki := Matrix.kroneckerMap (· * ·) (Kinv n γ) (Kinv n γ)
  (1 / 2 : ℂ) • (de * df + df * de) -
    ((Real.cos γ / (4 * Real.sin γ ^ 2) : ℝ) : ℂ) • ((dk - dki) * (dk - dki))

def casimirValue (γ : ℝ) (l : ℕ) : ℝ := qnum γ (l : ℝ) * qnum γ ((l + 1 : ℕ) : ℝ)

def orderedProduct {α : Type} [Monoid α] (f : ℕ → α) : ℕ → α
  | 0 => 1
  | k + 1 => orderedProduct f k * f k

def projector (n s : ℕ) (γ : ℝ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  orderedProduct (fun l =>
    if l ≠ s then
      ((qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ))⁻¹ : ℂ) •
        (tensorCasimir n γ - (casimirValue γ l : ℂ) • 1)
    else 1) (n + 1)

def siteOperator {R : Type} [Zero R] {n N : ℕ} (m : Fin (N - 1))
    (P : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) R) :
    Matrix (Fin ((n + 1) ^ N)) (Fin ((n + 1) ^ N)) R :=
  fun x y =>
    if (∀ k : Fin N, k ≠ ⟨m.val, by omega⟩ → k ≠ ⟨m.val + 1, by omega⟩ →
        digit x k = digit y k) then
      P (digit x ⟨m.val, by omega⟩, digit x ⟨m.val + 1, by omega⟩)
        (digit y ⟨m.val, by omega⟩, digit y ⟨m.val + 1, by omega⟩)
    else 0

def hamiltonian (n s N : ℕ) (γ : ℝ) (a : Fin (N - 1) → ℝ) :
    Matrix (Fin ((n + 1) ^ N)) (Fin ((n + 1) ^ N)) ℂ :=
  ∑ m, (a m : ℂ) • siteOperator m (projector n s γ)

def claim : Prop :=
  ∀ (n s N : ℕ) (γ : ℝ),
    1 ≤ n → s ≤ n → 2 ≤ N → 0 < |γ| → n * |γ| < Real.pi →
    (∀ l : ℕ, l ≤ n → l ≠ s →
      qnum γ ((s : ℝ) - l) * qnum γ ((s + l + 1 : ℕ) : ℝ) ≠ 0) →
    ∀ (a : Fin (N - 1) → ℝ), (∀ m, 0 < a m) →
    ∀ (v : Fin ((n + 1) ^ N) → ℂ) (z : ℂ), v ≠ 0 →
      hamiltonian n s N γ a *ᵥ v = z • v → z.im = 0

private theorem sin_γ₀ : Real.sin γ₀ = 3 / 5 := by
  rw [γ₀, Real.sin_arccos]
  norm_num

private theorem cos_γ₀ : Real.cos γ₀ = 4 / 5 := by
  rw [γ₀, Real.cos_arccos] <;> norm_num

private theorem sin_two_γ₀ : Real.sin (2 * γ₀) = 24 / 25 := by
  rw [Real.sin_two_mul, sin_γ₀, cos_γ₀]
  norm_num

private theorem sin_three_γ₀ : Real.sin (3 * γ₀) = 117 / 125 := by
  rw [Real.sin_three_mul, sin_γ₀]
  norm_num

private theorem sin_four_γ₀ : Real.sin (4 * γ₀) = 336 / 625 := by
  rw [show (4 : ℝ) * γ₀ = 2 * (2 * γ₀) by ring, Real.sin_two_mul,
    sin_two_γ₀]
  rw [show Real.cos (2 * γ₀) = 2 * Real.cos γ₀ ^ 2 - 1 by
    exact Real.cos_two_mul γ₀, cos_γ₀]
  norm_num

private theorem qnum_γ₀ (t : ℝ) :
    (t = 0 → qnum γ₀ t = 0) ∧
    (t = 1 → qnum γ₀ t = 1) ∧
    (t = 2 → qnum γ₀ t = 8 / 5) ∧
    (t = 3 → qnum γ₀ t = 39 / 25) ∧
    (t = 4 → qnum γ₀ t = 112 / 125) ∧
    (t = -1 → qnum γ₀ t = -1) := by
  constructor
  · intro h; subst t; simp [qnum, sin_γ₀]
  constructor
  · intro h; subst t; simp [qnum, sin_γ₀]
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 2 = 2 * γ₀ by ring, sin_two_γ₀, sin_γ₀]; norm_num
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 3 = 3 * γ₀ by ring, sin_three_γ₀, sin_γ₀]; norm_num
  constructor
  · intro h; subst t; rw [qnum, show γ₀ * 4 = 4 * γ₀ by ring, sin_four_γ₀, sin_γ₀]; norm_num
  · intro h; subst t
    rw [qnum, show γ₀ * (-1 : ℝ) = -(γ₀ * 1) by ring, Real.sin_neg,
      show γ₀ * 1 = γ₀ by ring, sin_γ₀]
    norm_num

private theorem qnum0 : qnum γ₀ 0 = 0 := (qnum_γ₀ 0).1 rfl
private theorem qnum1 : qnum γ₀ 1 = 1 := (qnum_γ₀ 1).2.1 rfl
private theorem qnum2 : qnum γ₀ 2 = 8 / 5 := (qnum_γ₀ 2).2.2.1 rfl
private theorem qnum3 : qnum γ₀ 3 = 39 / 25 := (qnum_γ₀ 3).2.2.2.1 rfl
private theorem qnum4 : qnum γ₀ 4 = 112 / 125 := (qnum_γ₀ 4).2.2.2.2.1 rfl
private theorem qnumNeg1 : qnum γ₀ (-1) = -1 := (qnum_γ₀ (-1)).2.2.2.2.2 rfl

private def flatten (i : Fin 3 × Fin 3) : Fin 9 :=
  ⟨3 * i.1.val + i.2.val, by omega⟩

private def c125G : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) GaussianInt :=
  fun i j => (!![312, 0, 0, 0, 0, 0, 0, 0, 0;
    0, ⟨256, -192⟩, 0, 200, 0, 0, 0, 0, 0;
    0, 0, ⟨56, -192⟩, 0, ⟨160, -120⟩, 0, 0, 0, 0;
    0, 200, 0, ⟨256, 192⟩, 0, 0, 0, 0, 0;
    0, 0, ⟨160, -120⟩, 0, 400, 0, ⟨160, 120⟩, 0, 0;
    0, 0, 0, 0, 0, ⟨256, -192⟩, 0, 200, 0;
    0, 0, 0, 0, ⟨160, 120⟩, 0, ⟨56, 192⟩, 0, 0;
    0, 0, 0, 0, 0, 200, 0, ⟨256, 192⟩, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 312]) (flatten i) (flatten j)

private def p14G : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) GaussianInt :=
  fun i j => (!![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, ⟨7, 24⟩, 0, (-25), 0, 0, 0, 0, 0;
    0, 0, 25, 0, ⟨0, 30⟩, 0, (-25), 0, 0;
    0, (-25), 0, ⟨7, -24⟩, 0, 0, 0, 0, 0;
    0, 0, ⟨0, 30⟩, 0, (-36), 0, ⟨0, -30⟩, 0, 0;
    0, 0, 0, 0, 0, ⟨7, 24⟩, 0, (-25), 0;
    0, 0, (-25), 0, ⟨0, -30⟩, 0, 25, 0, 0;
    0, 0, 0, 0, 0, (-25), 0, ⟨7, -24⟩, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]) (flatten i) (flatten j)

private def wG : Matrix (Fin 81) (Fin 2) GaussianInt :=
  fun x j => match x.val, j.val with
    | 26, 1 => 4900
    | 44, 0 => ⟨-5500, -4125⟩
    | 44, 1 => ⟨3080, 8190⟩
    | 50, 0 => ⟨5500, -4125⟩
    | 50, 1 => ⟨-7000, 5250⟩
    | 62, 0 => ⟨8800, -6600⟩
    | 62, 1 => ⟨-9828, 3696⟩
    | 68, 0 => ⟨7920, 10560⟩
    | 68, 1 => ⟨-10080, -13440⟩
    | 70, 0 => ⟨-5500, 4125⟩
    | 70, 1 => ⟨7000, -5250⟩
    | 74, 0 => ⟨-8800, 6600⟩
    | 74, 1 => ⟨6300, -8400⟩
    | 76, 0 => ⟨-2420, -6435⟩
    | 76, 1 => ⟨7000, 5250⟩
    | 78, 1 => ⟨-1372, 4704⟩
    | _, _ => 0

private def a196G : Matrix (Fin 2) (Fin 2) GaussianInt := !![-154, 196; -275, 350]

private def bG : Matrix (Fin 2) (Fin 2) GaussianInt := !![1, 0; 0, 0]

private def root : ℂ := (Real.sqrt (8 / 5 : ℝ) : ℂ)

private theorem root_sq : root ^ 2 = 8 / 5 := by
  dsimp [root]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 8 / 5 by norm_num)]
  norm_num

private theorem local_E :
    E 2 γ₀ = root • !![0, 0, 0; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [E, root, qnum1, qnum2]

private theorem local_F :
    F 2 γ₀ = root • !![0, 1, 0; 0, 0, 1; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, root, qnum1, qnum2]

private theorem local_K :
    K 2 γ₀ = !![(4 - 3 * Complex.I) / 5, 0, 0; 0, 1, 0;
      0, 0, (4 + 3 * Complex.I) / 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, weight, q, ← Complex.ofReal_cos, ← Complex.ofReal_sin, sin_γ₀, cos_γ₀] <;> ring

private theorem local_Kinv :
    Kinv 2 γ₀ = !![(4 + 3 * Complex.I) / 5, 0, 0; 0, 1, 0;
      0, 0, (4 - 3 * Complex.I) / 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kinv, weight, q, ← Complex.ofReal_cos, ← Complex.ofReal_sin, sin_γ₀, cos_γ₀] <;> ring

set_option maxHeartbeats 0 in
private theorem casimir_certificate :
    (125 : ℂ) • tensorCasimir 2 γ₀ = c125G.map GaussianInt.toComplex := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [tensorCasimir, local_E, local_F, local_K, local_Kinv,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.kroneckerMap_apply, c125G, flatten, GaussianInt.toComplex_def,
      sin_γ₀, cos_γ₀] <;>
    ring_nf <;> norm_num [root_sq, Complex.I_sq] <;> ring

set_option maxHeartbeats 0 in
private theorem projector_integer_certificate :
    (-22400 : GaussianInt) • p14G =
      (14 : GaussianInt) • (c125G * (c125G - (312 : GaussianInt) • 1)) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem chain_outer_integer_certificate :
    (196 : GaussianInt) • ((siteOperator (n := 2) (N := 4) (0 : Fin 3) p14G + siteOperator (n := 2) (N := 4) (2 : Fin 3) p14G) * wG) =
      (14 : GaussianInt) • (wG * a196G) := by
  apply Matrix.ext
  intro x j
  fin_cases x <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem chain_middle_integer_certificate :
    siteOperator (n := 2) (N := 4) (1 : Fin 3) p14G * wG = (14 : GaussianInt) • (wG * bG) := by
  apply Matrix.ext
  intro x j
  fin_cases x <;> fin_cases j <;> decide +kernel

private theorem projector_polynomial :
    projector 2 1 γ₀ = (-625 / 896 : ℂ) •
      (tensorCasimir 2 γ₀ * (tensorCasimir 2 γ₀ - (312 / 125 : ℂ) • 1)) := by
  norm_num [projector, orderedProduct, casimirValue, qnum0, qnum1, qnum2,
    qnum3, qnum4, qnumNeg1, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem projector_certificate :
    (14 : ℂ) • projector 2 1 γ₀ = p14G.map GaussianInt.toComplex := by
  let C := c125G.map GaussianInt.toComplex
  let P := p14G.map GaussianInt.toComplex
  have hC : tensorCasimir 2 γ₀ = (1 / 125 : ℂ) • C := by
    have h := congrArg (fun M => (1 / 125 : ℂ) • M) casimir_certificate
    norm_num [smul_smul] at h
    exact h
  have hi : (-22400 : ℂ) • P = (14 : ℂ) • (C * (C - (312 : ℂ) • 1)) := by
    ext i j
    have h := congrArg GaussianInt.toComplex
      (congrFun (congrFun projector_integer_certificate i) j)
    simpa [C, P, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
      map_sum, map_mul, map_sub, map_ofNat, Matrix.one_apply, apply_ite] using h
  have hf : (1 / 125 : ℂ) • C - (312 / 125 : ℂ) • 1 =
      (1 / 125 : ℂ) • (C - (312 : ℂ) • 1) := by
    norm_num [smul_sub, smul_smul]
  calc
    (14 : ℂ) • projector 2 1 γ₀ =
        (-1 / 1600 : ℂ) • (C * (C - (312 : ℂ) • 1)) := by
      rw [projector_polynomial, hC, hf, Matrix.smul_mul, Matrix.mul_smul]
      norm_num [smul_smul]
    _ = P := by
      have h := congrArg (fun M => (-1 / 22400 : ℂ) • M) hi
      norm_num [smul_smul] at h
      simpa only [neg_smul, neg_div] using h.symm

private theorem siteOperator_smul {n N : ℕ} (m : Fin (N - 1)) (a : ℂ)
    (P : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ) :
    siteOperator m (a • P) = a • siteOperator m P := by
  ext x y
  simp only [siteOperator, Matrix.smul_apply]
  split <;> simp_all

private theorem siteOperator_map {n N : ℕ} (m : Fin (N - 1))
    (P : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) GaussianInt) :
    (siteOperator m P).map GaussianInt.toComplex =
      siteOperator m (P.map GaussianInt.toComplex) := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.map_apply, siteOperator]
  split <;> simp_all

private theorem gaussian_map_smul {m n : Type} (a : GaussianInt) (M : Matrix m n GaussianInt) :
    (a • M).map GaussianInt.toComplex =
      GaussianInt.toComplex a • M.map GaussianInt.toComplex :=
  Matrix.map_smulₛₗ GaussianInt.toComplex GaussianInt.toComplex a
    (fun b => GaussianInt.toComplex.map_mul a b) M

private def block : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 196 : ℂ) • a196G.map GaussianInt.toComplex + bG.map GaussianInt.toComplex

set_option maxHeartbeats 0 in
private theorem chain_certificate :
    hamiltonian 2 1 4 γ₀ (fun _ => 1) * wG.map GaussianInt.toComplex =
      wG.map GaussianInt.toComplex * block := by
  let P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    p14G.map GaussianInt.toComplex
  let W : Matrix (Fin 81) (Fin 2) ℂ := wG.map GaussianInt.toComplex
  have hp : projector 2 1 γ₀ = (1 / 14 : ℂ) • P := by
    have h := congrArg (fun M => (1 / 14 : ℂ) • M) projector_certificate
    norm_num [smul_smul] at h
    exact h
  have hh : hamiltonian 2 1 4 γ₀ (fun _ => 1) =
      (1 / 14 : ℂ) • (siteOperator (n := 2) (N := 4) (0 : Fin 3) P + siteOperator (n := 2) (N := 4) (1 : Fin 3) P +
        siteOperator (n := 2) (N := 4) (2 : Fin 3) P) := by
    simp [hamiltonian, hp, siteOperator_smul, Fin.sum_univ_succ, smul_add, add_assoc]
  ext x j
  have ho : (196 : ℂ) * ((siteOperator (n := 2) (N := 4) (0 : Fin 3) P * W) x j +
      (siteOperator (n := 2) (N := 4) (2 : Fin 3) P * W) x j) =
      14 * (W * a196G.map GaussianInt.toComplex) x j := by
    have h := congrArg (fun M => M.map GaussianInt.toComplex) chain_outer_integer_certificate
    simp only [gaussian_map_smul, Matrix.map_mul,
      Matrix.map_add _ GaussianInt.toComplex.map_add, siteOperator_map, map_ofNat] at h
    simpa only [Matrix.smul_apply, Matrix.add_mul, Matrix.add_apply, smul_eq_mul] using
      congrFun (congrFun h x) j
  have hm : (siteOperator (n := 2) (N := 4) (1 : Fin 3) P * W) x j =
      14 * (W * bG.map GaussianInt.toComplex) x j := by
    have h := congrArg (fun M => M.map GaussianInt.toComplex) chain_middle_integer_certificate
    simp only [gaussian_map_smul, Matrix.map_mul, siteOperator_map, map_ofNat] at h
    simpa only [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h x) j
  rw [hh, Matrix.smul_mul, Matrix.add_mul, Matrix.add_mul, block,
    Matrix.mul_add, Matrix.mul_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  change (1 / 14 : ℂ) * (((siteOperator (n := 2) (N := 4) (0 : Fin 3) P * W) x j +
      (siteOperator (n := 2) (N := 4) (1 : Fin 3) P * W) x j) + (siteOperator (n := 2) (N := 4) (2 : Fin 3) P * W) x j) =
      (1 / 196 : ℂ) * (W * a196G.map GaussianInt.toComplex) x j +
        (W * bG.map GaussianInt.toComplex) x j
  linear_combination (1 / 2744 : ℂ) * ho + (1 / 14 : ℂ) * hm

private def eigenvalue : ℂ := 1 + Complex.I * (Real.sqrt (22 / 7 : ℝ) : ℂ) / 2

private def eigenvector : Fin 2 → ℂ := ![1, eigenvalue - 1 + 11 / 14]

private theorem eigenvalue_quadratic : eigenvalue ^ 2 - 2 * eigenvalue + 25 / 14 = 0 := by
  have hr : (Real.sqrt (22 / 7 : ℝ) : ℂ) ^ 2 = 22 / 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 22 / 7 by norm_num)]
    norm_num
  dsimp [eigenvalue]
  generalize he : (Real.sqrt (22 / 7 : ℝ) : ℂ) = r at *
  ring_nf
  norm_num [Complex.I_sq, hr]

private theorem block_eigenvector : block *ᵥ eigenvector = eigenvalue • eigenvector := by
  ext j
  fin_cases j <;>
    norm_num [block, a196G, bG, eigenvector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, GaussianInt.toComplex_def]
  · ring
  · linear_combination -eigenvalue_quadratic

private theorem eigenvalue_nonreal : eigenvalue.im ≠ 0 := by
  have hr : 0 < Real.sqrt (22 / 7 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h := ne_of_gt (div_pos hr (show (0 : ℝ) < 2 by norm_num))
  simpa [eigenvalue] using h

private theorem chain_eigenvector_nonzero :
    wG.map GaussianInt.toComplex *ᵥ eigenvector ≠ 0 := by
  intro h
  have he := congrArg (fun v : Fin 81 → ℂ => (v ⟨26, by decide⟩).im) h
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, wG, eigenvector,
    GaussianInt.toComplex_def] at he
  apply eigenvalue_nonreal
  linarith

theorem result : ¬ claim := by
  intro h
  have hγ : 0 < γ₀ := by
    dsimp [γ₀]
    exact Real.arccos_pos.mpr (by norm_num)
  have hpi : 2 * |γ₀| < Real.pi := by
    rw [abs_of_pos hγ]
    have hh : γ₀ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr (by norm_num)
    linarith
  have hden : ∀ l : ℕ, l ≤ 2 → l ≠ 1 →
      qnum γ₀ ((1 : ℝ) - l) * qnum γ₀ ((1 + l + 1 : ℕ) : ℝ) ≠ 0 := by
    intro l hl hls
    interval_cases l
    · norm_num [qnum0, qnum1, qnum2, qnum4, qnumNeg1]
    · omega
    · norm_num [qnum0, qnum1, qnum2, qnum4, qnumNeg1]
  have hc := h 2 1 4 γ₀ (by norm_num) (by norm_num) (by norm_num)
    (by simpa [abs_of_pos hγ] using hγ) hpi (by simpa using hden)
  have he : hamiltonian 2 1 4 γ₀ (fun _ => 1) *ᵥ
      (wG.map GaussianInt.toComplex *ᵥ eigenvector) =
      eigenvalue • (wG.map GaussianInt.toComplex *ᵥ eigenvector) := by
    rw [Matrix.mulVec_mulVec, chain_certificate, ← Matrix.mulVec_mulVec,
      block_eigenvector, Matrix.mulVec_smul]
  exact eigenvalue_nonreal
    (hc (fun _ => 1) (by norm_num) _ eigenvalue chain_eigenvector_nonzero he)

end
end D5.S3.Quantum.SpinChains.QuantumGroupChainRealSpectrumRefutation
