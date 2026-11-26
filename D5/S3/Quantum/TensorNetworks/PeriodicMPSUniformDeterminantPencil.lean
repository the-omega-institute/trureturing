/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.LinearAlgebra.Matrix.Kronecker]
   utility: none
   digest: A contracted trace-word flattening detects the squared determinant pencil and gives an exact quartic at the hard-core witness. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The determinant pencil of a periodic binary bond-two trace tensor can be read
from a four-by-four flattening with one physical slot contracted. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil

open scoped BigOperators Kronecker Matrix

noncomputable section

namespace MatrixWords

/-- Multiply the cores in increasing word-index order. -/
def wordMatrix {b d : ℕ} (A : Fin d → Matrix (Fin b) (Fin b) ℂ) {n : ℕ}
    (w : Fin n → Fin d) : Matrix (Fin b) (Fin b) ℂ :=
  (List.ofFn fun i => A (w i)).prod

lemma wordMatrix_snoc {b d : ℕ} (A : Fin d → Matrix (Fin b) (Fin b) ℂ) {n : ℕ}
    (w : Fin n → Fin d) (i : Fin d) :
    wordMatrix A (Fin.snoc w i) = wordMatrix A w * A i := by
  rw [wordMatrix, List.ofFn_succ']
  simp [wordMatrix]

lemma wordMatrix_append {b d : ℕ} (A : Fin d → Matrix (Fin b) (Fin b) ℂ) {m n : ℕ}
    (u : Fin m → Fin d) (v : Fin n → Fin d) :
    wordMatrix A (Fin.append u v) = wordMatrix A u * wordMatrix A v := by
  simp [wordMatrix, List.ofFn_comp', List.ofFn_fin_append, List.prod_append]

end MatrixWords

open MatrixWords (wordMatrix wordMatrix_append wordMatrix_snoc)

local notation "Bond" => Matrix (Fin 2) (Fin 2) ℂ
local notation "Word" n:max => Fin n → Fin 2
local notation "traceWord" n:max A:max =>
  (fun w : Word n => Matrix.trace (wordMatrix (A : Fin 2 → Bond) w))

abbrev Guard := Fin 2 × Fin 2

/-- Each entry reads the two tensor coefficients obtained by filling the slot
between the given prefix and suffix, weighted by the coordinates of `z`. -/
def observedFlattening {m k n : ℕ} (h : m + 1 + k = n) (T : Word n → ℂ)
    (u : Guard → Word m) (v : Guard → Word k) (z : Fin 2 → ℂ) :
    Matrix Guard Guard ℂ :=
  fun i j => ∑ s : Fin 2, z s *
    T (fun t => Fin.append (Fin.snoc (u i) s) (v j) (Fin.cast h.symm t))

def pencil (A : Fin 2 → Bond) (z : Fin 2 → ℂ) : Bond :=
  z 0 • A 0 + z 1 • A 1

/-- The trace pairing with one matrix inserted between the two lists of products. -/
def traceFlattening (L R : Guard → Bond) (C : Bond) : Matrix Guard Guard ℂ :=
  fun i j => (L i * C * R j).trace

def prefixCoordinates (L : Guard → Bond) : Matrix Guard Guard ℂ :=
  fun i a => L i a.1 a.2

def suffixCoordinates (R : Guard → Bond) : Matrix Guard Guard ℂ :=
  fun a j => R j a.2 a.1

/-- Right multiplication by `C` acts on the second bond index. -/
theorem traceFlattening_factor (L R : Guard → Bond) (C : Bond) :
    traceFlattening L R C =
      prefixCoordinates L * ((1 : Bond) ⊗ₖ C) * suffixCoordinates R := by
  have hleft (i : Guard) (a b : Fin 2) :
      (prefixCoordinates L * ((1 : Bond) ⊗ₖ C)) i (a, b) = (L i * C) a b := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, prefixCoordinates,
      Matrix.kronecker_apply, Matrix.one_apply]
    calc
      (∑ x : Fin 2, ∑ y : Fin 2, L i x y * ((if x = a then 1 else 0) * C y b)) =
          ∑ x : Fin 2, if x = a then ∑ y : Fin 2, L i x y * C y b else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : x = a <;> simp [h]
      _ = ∑ y : Fin 2, L i a y * C y b := by simp
  ext i j
  simp only [traceFlattening, Matrix.trace, Matrix.diag, Matrix.mul_apply (M := L i * C),
    Matrix.mul_apply (N := suffixCoordinates R), Fintype.sum_prod_type,
    hleft, suffixCoordinates]

/-- The determinant factorization holds for arbitrary lists of bond matrices. -/
theorem det_traceFlattening (L R : Guard → Bond) (C : Bond) :
    (traceFlattening L R C).det =
      ((prefixCoordinates L).det * (suffixCoordinates R).det) * C.det ^ 2 := by
  rw [traceFlattening_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_kronecker]
  simp [mul_right_comm]

/-- For the literal trace-word tensor, contracting the physical slot inserts the pencil. -/
theorem observedFlattening_traceWord {m k n : ℕ} (h : m + 1 + k = n)
    (A : Fin 2 → Bond) (u : Guard → Word m) (v : Guard → Word k) (z : Fin 2 → ℂ) :
    observedFlattening h (traceWord n A) u v z =
      traceFlattening (fun i => wordMatrix A (u i)) (fun j => wordMatrix A (v j))
        (pencil A z) := by
  subst n
  ext i j
  change (∑ s : Fin 2, z s * (wordMatrix A (Fin.append (Fin.snoc (u i) s) (v j))).trace) =
    (wordMatrix A (u i) * pencil A z * wordMatrix A (v j)).trace
  simp only [wordMatrix_append, wordMatrix_snoc, Fin.sum_univ_two, pencil, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul]

theorem det_observedFlattening_traceWord {m k n : ℕ} (h : m + 1 + k = n)
    (A : Fin 2 → Bond) (u : Guard → Word m) (v : Guard → Word k) (z : Fin 2 → ℂ) :
    (observedFlattening h (traceWord n A) u v z).det =
      ((prefixCoordinates (fun i => wordMatrix A (u i))).det *
        (suffixCoordinates (fun j => wordMatrix A (v j))).det) * (pencil A z).det ^ 2 := by
  rw [observedFlattening_traceWord, det_traceFlattening]

/-- The two guard labels specify the end bits, with `m + 1` zeros between them.
At `m = 0` this gives the prefixes `000, 001, 100, 101` in lexicographic order. -/
def guardWord (m : ℕ) (i : Guard) : Word (m + 3) :=
  Fin.cons i.1 (Fin.snoc (fun _ : Fin (m + 1) => 0) i.2)

/-- The prescribed guards at length `n`, with the insertion following the three-bit prefix. -/
def guardedFlattening (n : ℕ) (hn : 7 ≤ n) (T : Word n → ℂ) (z : Fin 2 → ℂ) :
    Matrix Guard Guard ℂ :=
  observedFlattening (by omega : 3 + 1 + (n - 7 + 3) = n) T
    (guardWord 0) (guardWord (n - 7)) z

/-- The determinant coefficient depends on the guard products and the cores. -/
def guardCoefficient (n : ℕ) (A : Fin 2 → Bond) : ℂ :=
  (prefixCoordinates (fun i => wordMatrix A (guardWord 0 i))).det *
    (suffixCoordinates (fun j => wordMatrix A (guardWord (n - 7) j))).det

theorem det_guardedFlattening_traceWord (n : ℕ) (hn : 7 ≤ n)
    (A : Fin 2 → Bond) (z : Fin 2 → ℂ) :
    (guardedFlattening n hn (traceWord n A) z).det =
      guardCoefficient n A * (pencil A z).det ^ 2 := by
  exact det_observedFlattening_traceWord _ A _ _ z

/-- The two cores of the cyclic independent-set witness. -/
def witnessCore : Fin 2 → Bond := ![!![1, 0; 0, 0], !![1, 1; -1, -1]]

private lemma wordMatrix_cons {b d : ℕ} (A : Fin d → Matrix (Fin b) (Fin b) ℂ) {n : ℕ}
    (i : Fin d) (w : Fin n → Fin d) :
    wordMatrix A (Fin.cons i w) = A i * wordMatrix A w := by
  simp [wordMatrix]

private theorem wordMatrix_guardWord (A : Fin 2 → Bond) (m : ℕ) (i : Guard) :
    wordMatrix A (guardWord m i) = A i.1 * A 0 ^ (m + 1) * A i.2 := by
  rw [guardWord, wordMatrix_cons, wordMatrix_snoc]
  simp only [wordMatrix, List.ofFn_const, List.prod_replicate, Matrix.mul_assoc]

private theorem witnessCore_zero_pow (m : ℕ) :
    witnessCore 0 ^ (m + 1) = witnessCore 0 := by
  have h : witnessCore 0 * witnessCore 0 = witnessCore 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witnessCore, Matrix.mul_apply, Fin.sum_univ_two]
  induction m with
  | zero => exact pow_one _
  | succ m ih => rw [pow_succ, ih, h]

private theorem wordMatrix_witness_guard (m : ℕ) (i : Guard) :
    wordMatrix witnessCore (guardWord m i) =
      witnessCore i.1 * witnessCore 0 * witnessCore i.2 := by
  rw [wordMatrix_guardWord, witnessCore_zero_pow]

theorem det_witnessPencil (z : Fin 2 → ℂ) :
    (pencil witnessCore z).det = -(z 0 * z 1) := by
  rw [Matrix.det_fin_two]
  simp [pencil, witnessCore, Matrix.add_apply, smul_eq_mul]
  ring

private theorem guardedFlattening_witness_one (n : ℕ) (hn : 7 ≤ n) :
    guardedFlattening n hn (traceWord n witnessCore) 1 =
      Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        !![2, 2, 1, 1; 1, 1, 1, 1; 2, 0, 1, 0; 1, 0, 1, 0] := by
  rw [guardedFlattening, observedFlattening_traceWord]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [traceFlattening, wordMatrix_witness_guard]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pencil, witnessCore,
      Matrix.reindex_apply, Matrix.submatrix_apply, finProdFinEquiv, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- The fixed physical vector `(1, 1)` gives determinant `-1` at every witness length. -/
theorem det_guardedFlattening_witness_one (n : ℕ) (hn : 7 ≤ n) :
    (guardedFlattening n hn (traceWord n witnessCore) 1).det = -1 := by
  rw [guardedFlattening_witness_one n hn, Matrix.det_reindex_self,
    Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]

theorem guardedFlattening_witness_nondegenerate (n : ℕ) (hn : 7 ≤ n) :
    (guardedFlattening n hn (traceWord n witnessCore) 1).det ≠ 0 := by
  rw [det_guardedFlattening_witness_one n hn]
  exact neg_ne_zero.mpr one_ne_zero

/-- At the witness, the observed quartic is exactly `-(z₀ z₁)²`. -/
theorem det_guardedFlattening_witness (n : ℕ) (hn : 7 ≤ n) (z : Fin 2 → ℂ) :
    (guardedFlattening n hn (traceWord n witnessCore) z).det = -(z 0 * z 1) ^ 2 := by
  have h := det_guardedFlattening_traceWord n hn witnessCore (1 : Fin 2 → ℂ)
  rw [det_guardedFlattening_witness_one n hn, det_witnessPencil] at h
  have hκ : guardCoefficient n witnessCore = -1 := by
    simpa using h.symm
  rw [det_guardedFlattening_traceWord n hn, hκ, det_witnessPencil]
  ring

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil
