/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: Boundary gluing for injective periodic binary matrix product states. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! The length-two spanning hypothesis is the source's actual injectivity condition.
No individual symbol matrix is assumed invertible. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection

open scoped BigOperators Matrix

noncomputable section

abbrev Bond := Matrix (Fin 2) (Fin 2) ℂ
abbrev Word (n : ℕ) := Fin n → Fin 2

def wordMatrix (A : Fin 2 → Bond) {n : ℕ} (w : Word n) : Bond :=
  (List.ofFn fun i => A (w i)).prod

def gamma (A : Fin 2 → Bond) (n : ℕ) (X : Bond) (w : Word n) : ℂ :=
  (X * wordMatrix A w).trace

def TwoSiteSpanning (A : Fin 2 → Bond) : Prop :=
  Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) = ⊤

private lemma wordMatrix_cons (A : Fin 2 → Bond) {n : ℕ} (i : Fin 2) (w : Word n) :
    wordMatrix A (Fin.cons i w) = A i * wordMatrix A w := by
  simp [wordMatrix, List.ofFn_cons, ← Fin.comp_cons]

private lemma wordMatrix_snoc (A : Fin 2 → Bond) {n : ℕ} (w : Word n) (i : Fin 2) :
    wordMatrix A (Fin.snoc w i) = wordMatrix A w * A i := by
  rw [wordMatrix, List.ofFn_succ']
  simp [wordMatrix, List.prod_concat]

/-- Compatible left and right virtual boundaries glue through one common matrix. -/
theorem boundary_gluing (A : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (X Y : Fin 2 → Bond) (h : ∀ i j, X j * A i = A j * Y i) :
    ∃ Z : Bond, (∀ j, X j = A j * Z) ∧ (∀ i, Y i = Z * A i) := by
  classical
  have hI : (1 : Bond) ∈ Submodule.span ℂ
      (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) := by
    rw [hA]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun.mp hI
  let Z : Bond := ∑ p : Fin 2 × Fin 2, c p • (Y p.1 * A p.2)
  have hX (j : Fin 2) : X j = A j * Z := by
    calc
      X j = X j * (∑ p, c p • (A p.1 * A p.2)) := by rw [hc, mul_one]
      _ = A j * Z := by
        simp only [Z, Finset.mul_sum, Matrix.mul_smul, Matrix.smul_mul_assoc,
          ← Matrix.mul_assoc, h]
  refine ⟨Z, hX, ?_⟩
  intro i
  have hk (j : Fin 2) : A j * Y i = A j * (Z * A i) := by
    rw [← h i j, hX, Matrix.mul_assoc]
  calc
    Y i = (∑ p, c p • (A p.1 * A p.2)) * Y i := by rw [hc, one_mul]
    _ = (∑ p, c p • (A p.1 * A p.2)) * (Z * A i) := by
      simp only [Finset.sum_mul, Matrix.smul_mul_assoc, Matrix.mul_assoc, hk]
    _ = Z * A i := by rw [hc, one_mul]

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
