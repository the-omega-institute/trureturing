/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateCore
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_eq_sum_gram; instance=D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.coefficient_equality
   digest: Exact Weyl coefficients and polynomial normalization reflect covariance identities into complex matrices. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
Exact coefficients and polynomial reflection for the qutrit covariance certificate.
The coefficient ring is ℚ[s]/(s² + 3), with s mapped to √3 I.
-/

set_option autoImplicit false

open scoped BigOperators ComplexOrder
open Matrix

namespace QianACC.CovarianceCertificate

abbrev Coeff := QuadraticAlgebra ℚ (-3) 0
abbrev Weight := Fin 9
abbrev Test := Fin 4
abbrev TermIndex := Fin 20

def rat (q : ℚ) : Coeff := ⟨q, 0⟩

private noncomputable def complexValue (z : Coeff) : ℂ :=
  ⟨(z.re : ℝ), (z.im : ℝ) * Real.sqrt 3⟩

/-- The rational quadratic coefficient embedding used by both replays. -/
noncomputable def toComplex : Coeff →+* ℂ where
  toFun := complexValue
  map_zero' := by apply Complex.ext <;> simp [complexValue]
  map_one' := by apply Complex.ext <;> simp [complexValue, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]
  map_add' x y := by
    apply Complex.ext <;> simp [complexValue, Complex.add_re, Complex.add_im, add_mul]
  map_mul' x y := by
    have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
    apply Complex.ext
    · simp only [complexValue, QuadraticAlgebra.re_mul, Complex.mul_re]
      push_cast
      linear_combination ((x.im : ℝ) * (y.im : ℝ)) * hs
    · simp only [complexValue, QuadraticAlgebra.im_mul, Complex.mul_im]
      push_cast
      ring

@[simp] theorem toComplex_rat (q : ℚ) : toComplex (rat q) = ((q : ℝ) : ℂ) := by
  change complexValue (rat q) = _
  apply Complex.ext <;> simp [complexValue, rat]

@[simp] theorem toComplex_star (z : Coeff) : toComplex (star z) = star (toComplex z) := by
  change complexValue (star z) = star (complexValue z)
  apply Complex.ext <;> simp [complexValue, neg_mul]

noncomputable def complexMatrix {m n : Type} (A : Matrix m n Coeff) : Matrix m n ℂ :=
  A.map toComplex

@[simp] theorem complexMatrix_mul {m n p : Type} [Fintype n]
    (A : Matrix m n Coeff) (B : Matrix n p Coeff) :
    complexMatrix (A * B) = complexMatrix A * complexMatrix B := by
  exact Matrix.map_mul

@[simp] theorem complexMatrix_adjoint {m n : Type} (A : Matrix m n Coeff) :
    complexMatrix Aᴴ = (complexMatrix A)ᴴ := by
  apply Matrix.ext
  intro i j
  exact toComplex_star (A j i)

theorem complexMatrix_diag {n : Type} [DecidableEq n] (d : n → ℚ) :
    complexMatrix (Matrix.diagonal (fun i => rat (d i))) =
      Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [complexMatrix, hij]

/-- A list sum gives the kernel a direct enumeration of a finite ordinal. -/
def sumFin {R : Type} [AddMonoid R] {n : ℕ} (f : Fin n → R) : R :=
  (List.ofFn f).sum

theorem sumFin_eq {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) :
    sumFin f = ∑ i, f i := List.sum_ofFn

private def firstAxis (w : Weight) : Fin 3 := Fin.ofNat 3 (w.val / 3)
private def secondAxis (w : Weight) : Fin 3 := Fin.ofNat 3 w.val

private def weight (a b : Fin 3) : Weight :=
  ⟨3 * a.val + b.val, by
    have ha := a.isLt
    have hb := b.isLt
    omega⟩

def addWeight (w v : Weight) : Weight :=
  weight (firstAxis w + firstAxis v) (secondAxis w + secondAxis v)

def negWeight (w : Weight) : Weight := weight (0 - firstAxis w) (0 - secondAxis w)

/-- Computational-diagonal tests first, Fourier-diagonal tests second. -/
def testWeight (a : Test) : Weight := ![1, 2, 3, 6] a

private def omegaPower (k : Fin 3) : Coeff :=
  ![1, ⟨-1 / 2, 1 / 2⟩, ⟨-1 / 2, -1 / 2⟩] k

private def appendWeight (state : Weight × Fin 3) (v : Weight) : Weight × Fin 3 :=
  let (w, exponent) := state
  (addWeight w v, exponent + 2 * (secondAxis w * firstAxis v - firstAxis w * secondAxis v))

/-- Weyl-word trace for W(a,b) = ω^(2ab) X^a Z^b and ZX = ω XZ. -/
def weylTrace (word : List Weight) : Coeff :=
  let (total, exponent) := word.foldl appendWeight (0, 0)
  if total = 0 then rat 3 * omegaPower exponent else 0

structure Monomial where
  left : Weight
  right : Weight
  test : Test

/-- Row order agrees with combinations with replacement, with test index varying fastest. -/
def monomials (w : Weight) : List Monomial :=
  ((List.finRange 9).flatMap fun i =>
    (List.finRange 9).flatMap fun j =>
      (List.finRange 4).map fun a => Monomial.mk i j a).filter fun m =>
    decide (m.left ≤ m.right ∧
      addWeight (addWeight m.left m.right) (testWeight m.test) = w)

def monomial (w : Weight) (k : TermIndex) : Monomial :=
  (monomials w).getD k.val ⟨0, 0, 0⟩

structure Block where
  dim : ℕ
  basis : Matrix TermIndex (Fin dim) Coeff
  gram : Matrix (Fin dim) (Fin dim) Coeff
  lower : Matrix (Fin dim) (Fin dim) Coeff
  pivots : Fin dim → ℚ

private def tableEntry (rows : List (List Coeff)) (i j : ℕ) : Coeff :=
  (rows.getD i []).getD j 0

/-- The JSON stores basis columns and upper Gram triangles. The lower LDL triangle
includes its unit diagonal. Missing upper LDL entries are zero. -/
def Block.ofTables (dim : ℕ) (basisColumns gramUpper ldlLower : List (List Coeff))
    (pivots : List ℚ) : Block where
  dim := dim
  basis i k := tableEntry basisColumns k.val i.val
  gram i j :=
    if i ≤ j then tableEntry gramUpper i.val (j.val - i.val)
    else star (tableEntry gramUpper j.val (i.val - j.val))
  lower i j := tableEntry ldlLower i.val j.val
  pivots i := pivots.getD i.val 0

namespace Polynomial

abbrev Key := List Weight
abbrev Term := Key × Coeff
abbrev Terms := List Term

noncomputable def evalKey (x : Weight → ℂ) (key : Key) : ℂ := (key.map x).prod

noncomputable def evalTerm (x : Weight → ℂ) (t : Term) : ℂ :=
  toComplex t.2 * evalKey x t.1

noncomputable def eval (x : Weight → ℂ) (terms : Terms) : ℂ := (terms.map (evalTerm x)).sum

@[simp] theorem eval_nil (x : Weight → ℂ) : eval x [] = 0 := rfl

@[simp] theorem eval_cons (x : Weight → ℂ) (t : Term) (p : Terms) :
    eval x (t :: p) = evalTerm x t + eval x p := rfl

@[simp] theorem eval_append (x : Weight → ℂ) (p q : Terms) :
    eval x (p ++ q) = eval x p + eval x q := by
  simp [eval, List.sum_append]

theorem eval_map {ι : Type} (x : Weight → ℂ) (s : List ι) (f : ι → Term) :
    eval x (s.map f) = (s.map fun i => evalTerm x (f i)).sum := by
  simp [eval, Function.comp_def]

theorem eval_flatMap {ι : Type} (x : Weight → ℂ) (s : List ι) (f : ι → Terms) :
    eval x (s.flatMap f) = (s.map (fun i => eval x (f i))).sum := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [List.flatMap_cons, ih]

/-- Drop zero coefficients using the decidable coefficient ring. -/
def omitZeros (p : Terms) : Terms := p.filter (fun t => decide (t.2 ≠ 0))

@[simp] theorem eval_omitZeros (x : Weight → ℂ) (p : Terms) :
    eval x (omitZeros p) = eval x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    by_cases h : t.2 = 0
    · have hc : omitZeros (t :: p) = omitZeros p := by simp [omitZeros, h]
      rw [hc, ih, eval_cons]
      simp [evalTerm, h]
    · have hc : omitZeros (t :: p) = t :: omitZeros p := by simp [omitZeros, h]
      rw [hc, eval_cons, eval_cons, ih]

def scale (c : Coeff) (p : Terms) : Terms := p.map (fun t => (t.1, c * t.2))

theorem eval_scale (x : Weight → ℂ) (c : Coeff) (p : Terms) :
    eval x (scale c p) = toComplex c * eval x p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
    change evalTerm x (t.1, c * t.2) + eval x (scale c p) =
      toComplex c * (evalTerm x t + eval x p)
    rw [ih, mul_add]
    simp [evalTerm, mul_assoc]

def mul (p q : Terms) : Terms :=
  p.flatMap fun t => q.map fun u => (t.1 ++ u.1, t.2 * u.2)

private theorem eval_mulTerm (x : Weight → ℂ) (t : Term) (q : Terms) :
    eval x (q.map fun u => (t.1 ++ u.1, t.2 * u.2)) = evalTerm x t * eval x q := by
  induction q with
  | nil => simp
  | cons u q ih =>
    rw [List.map_cons, eval_cons, eval_cons, ih, mul_add]
    congr 1
    simp only [evalTerm, evalKey, List.map_append, List.prod_append, map_mul]
    ac_rfl

theorem eval_mul (x : Weight → ℂ) (p q : Terms) :
    eval x (mul p q) = eval x p * eval x q := by
  rw [mul, eval_flatMap]
  simp only [eval_mulTerm]
  change _ = (p.map (evalTerm x)).sum * eval x q
  exact List.sum_map_mul_right p (evalTerm x) (eval x q)

private def sortKey (k : Key) : Key := k.insertionSort (· ≤ ·)

private theorem evalKey_sort (x : Weight → ℂ) (k : Key) :
    evalKey x (sortKey k) = evalKey x k :=
  ((List.perm_insertionSort (· ≤ ·) k).map x).prod_eq

/-- The reflected monomials all have degree four. This code orders their lists. -/
private def keyCode (k : Key) : ℕ := k.foldl (fun n i => 10 * n + i.val + 1) 0

private def insert (t : Term) : Terms → Terms
  | [] => [t]
  | u :: us =>
    if t.1 = u.1 then (u.1, t.2 + u.2) :: us
    else if keyCode t.1 < keyCode u.1 then t :: u :: us
    else u :: insert t us

private theorem eval_insert (x : Weight → ℂ) (t : Term) (p : Terms) :
    eval x (insert t p) = evalTerm x t + eval x p := by
  induction p with
  | nil => simp [insert]
  | cons u p ih =>
    by_cases h : t.1 = u.1
    · simp [insert, h, evalTerm, add_mul, add_assoc]
    · by_cases hk : keyCode t.1 < keyCode u.1
      · simp [insert, h, hk]
      · simp [insert, h, hk, ih, add_left_comm]

private def collect (t : Term) (p : Terms) : Terms := insert (sortKey t.1, t.2) p

private theorem eval_collect (x : Weight → ℂ) (p : Terms) :
    eval x (p.foldr collect []) = eval x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp [collect, eval_insert, evalTerm, evalKey_sort, ih]

/-- Sort the variables in each monomial, add duplicate coefficients and erase zeros. -/
def normalize (p : Terms) : Terms := omitZeros ((omitZeros p).foldr collect [])

theorem eval_normalize (x : Weight → ℂ) (p : Terms) :
    eval x (normalize p) = eval x p := by
  simp only [normalize, eval_omitZeros, eval_collect]

/-- A finite exact equality suffices for every complex substitution. -/
theorem eval_eq_of_normalize_eq {p q : Terms} (h : normalize p = normalize q)
    (x : Weight → ℂ) : eval x p = eval x q := by
  rw [← eval_normalize x p, ← eval_normalize x q, h]

end Polynomial

/-- A quadratic polynomial obtained by inserting two copies of T in a Weyl word. -/
def traceTerms (word : Weight → Weight → List Weight) : Polynomial.Terms :=
  Polynomial.omitZeros ((List.finRange 9).flatMap fun i =>
    (List.finRange 9).map fun j => ([i, j], weylTrace (word i j)))

/-- Quadratic trace in Weyl coordinates. The two variables retain their positions in `word`. -/
noncomputable def traceForm (x : Weight → ℂ) (word : Weight → Weight → List Weight) : ℂ :=
  ∑ i : Weight, ∑ j : Weight, toComplex (weylTrace (word i j)) * (x i * x j)

theorem eval_traceTerms (x : Weight → ℂ) (word : Weight → Weight → List Weight) :
    Polynomial.eval x (traceTerms word) = traceForm x word := by
  rw [traceTerms, Polynomial.eval_omitZeros, Polynomial.eval_flatMap]
  simp only [traceForm, Polynomial.eval_map, Polynomial.evalTerm,
    Polynomial.evalKey, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, ← Fin.sum_univ_def]

private structure EntryWeights where
  first : ℚ
  second : ℚ
  midpoint : ℚ
  means : ℚ

private def entryWeights (a b : Test) : EntryWeights :=
  if a.val / 2 = b.val / 2 then ⟨3 / 2, 3 / 2, -2, -1⟩
  else ⟨5 / 4, -1 / 4, 1, -2⟩

/-- The numerator of the covariance matrix in the four Weyl test directions. -/
noncomputable def covarianceMatrix (x : Weight → ℂ) : Matrix Test Test ℂ :=
  fun a b =>
    let c := negWeight (testWeight a)
    let d := testWeight b
    let k := entryWeights a b
    let tr := traceForm x
    tr (fun i j => [i, j]) *
      ((k.first : ℂ) * tr (fun i j => [i, j, c, d]) +
       (k.second : ℂ) * tr (fun i j => [i, j, d, c]) +
       (k.midpoint : ℂ) * tr (fun i j => [i, c, j, d])) +
    (k.means : ℂ) * (tr (fun i j => [i, j, c]) * tr (fun i j => [i, j, d]))

def targetTerms (a b : Test) : Polynomial.Terms :=
  let c := negWeight (testWeight a)
  let d := testWeight b
  let k := entryWeights a b
  let tr := traceTerms
  let raw := Polynomial.scale (rat k.first) (tr (fun i j => [i, j, c, d])) ++
    Polynomial.scale (rat k.second) (tr (fun i j => [i, j, d, c])) ++
    Polynomial.scale (rat k.midpoint) (tr (fun i j => [i, c, j, d]))
  Polynomial.mul (tr (fun i j => [i, j])) raw ++
    Polynomial.scale (rat k.means)
      (Polynomial.mul (tr (fun i j => [i, j, c])) (tr (fun i j => [i, j, d])))

theorem eval_targetTerms (x : Weight → ℂ) (a b : Test) :
    Polynomial.eval x (targetTerms a b) = covarianceMatrix x a b := by
  simp only [targetTerms, covarianceMatrix, Polynomial.eval_append, Polynomial.eval_mul,
    Polynomial.eval_scale, toComplex_rat, Complex.ofReal_ratCast, eval_traceTerms]

end QianACC.CovarianceCertificate
