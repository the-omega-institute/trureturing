/- GID: D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact real support and centralizer obstructions for the minimum nSSP arc problem. -/

import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators DirectSum
open Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs

/-- The non-symmetric strong spectral property, with no extra diagonal constraint. -/
def HasNSSP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, A i j * X i j = 0) →
    A * X.transpose - X.transpose * A = 0 → X = 0

/-- Exact directed support, allowing loops. -/
def ExactSupport {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j ≠ 0 ↔ (i,j) ∈ E

/-- Every real matrix with the exact support must have nSSP. -/
def Requires {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, ExactSupport E A → HasNSSP A

/-- The complete all-positive-order event; the two clauses have the same order. -/
def MinimumArcs : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ E : Finset (Fin n × Fin n), Requires E → 2*n-1 ≤ E.card) ∧
    ∃ E : Finset (Fin n × Fin n), Requires E ∧ E.card = 2*n-1

private theorem end_centralizer_finrank_ge
    {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    Module.finrank K V ≤ Module.finrank K (Subalgebra.centralizer K ({f} : Set _)) := by
  obtain ⟨ι, hι, p, hp, e, ⟨g⟩⟩ :=
    Module.equiv_directSum_of_isTorsion
      (Module.AEval.isTorsion_of_finiteDimensional K V f)
  letI := hι
  let Q := ∀ i : ι, K[X] ⧸ Ideal.span ({p i ^ e i} : Set K[X])
  let h : Module.AEval' f ≃ₗ[K[X]] Q :=
    g.trans (DirectSum.linearEquivFunOnFintype K[X] ι _)
  let k : V ≃ₗ[K] Q := (Module.AEval'.of f).trans (h.restrictScalars K)
  let L : Q →ₗ[K] Module.End K V :=
    k.symm.conj.toLinearMap.comp (Algebra.lmul K Q).toLinearMap
  have hL : Function.Injective L :=
    k.symm.conj.injective.comp Algebra.lmul_injective
  have hc (q : Q) : L q ∈ Subalgebra.centralizer K ({f} : Set _) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ (rfl : _ = f)
    apply LinearMap.ext
    intro v
    have hk (v : V) : k (f v) = (X : K[X]) • k v := by
      change h (Module.AEval'.of f (f v)) = _
      rw [← Module.AEval'.X_smul_of, h.map_smul]
    apply k.injective
    change k (f (k.symm (q * k v))) = k (k.symm (q * k (f v)))
    rw [hk, k.apply_symm_apply, k.apply_symm_apply, hk]
    exact smul_mul_assoc _ _ _
  let T : Q →ₗ[K] Subalgebra.centralizer K ({f} : Set _) :=
    L.codRestrict _ hc
  have hT : Function.Injective T := fun x y hxy => hL (congrArg Subtype.val hxy)
  haveI : FiniteDimensional K Q := k.finiteDimensional
  calc
    Module.finrank K V = Module.finrank K Q := k.finrank_eq
    _ ≤ Module.finrank K (Subalgebra.centralizer K ({f} : Set _)) :=
      LinearMap.finrank_le_finrank_of_injective hT

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
