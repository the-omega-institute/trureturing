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
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity

/-!
Real matrices with exact directed support are tested against every real obstruction matrix.
The centralizer bound uses the polynomial module structure over the original field.
-/

set_option backward.isDefEq.respectTransparency false

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
    intro y hy
    have hyf : y = f := Set.mem_singleton_iff.mp hy
    rw [hyf]
    apply LinearMap.ext
    intro v
    have hk (v : V) : k (f v) = (X : K[X]) • k v := by
      change h (Module.AEval'.of f (f v)) = _
      rw [← Module.AEval'.X_smul_of, h.map_smul]
      rfl
    apply k.injective
    change k (f (k.symm (q * k v))) = k (k.symm (q * k (f v)))
    rw [hk, k.apply_symm_apply, k.apply_symm_apply, hk]
    exact (mul_smul_comm (X : K[X]) q (k v)).symm
  let T : Q →ₗ[K] Subalgebra.centralizer K ({f} : Set _) :=
    LinearMap.codRestrict (Subalgebra.centralizer K ({f} : Set _)).toSubmodule L hc
  have hT : Function.Injective T := fun x y hxy => hL (congrArg Subtype.val hxy)
  haveI : FiniteDimensional K Q := k.finiteDimensional
  calc
    Module.finrank K V = Module.finrank K Q := k.finrank_eq
    _ ≤ Module.finrank K (Subalgebra.centralizer K ({f} : Set _)) :=
      LinearMap.finrank_le_finrank_of_injective hT

private theorem matrix_centralizer_finrank_ge {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    n ≤ Module.finrank ℝ (Subalgebra.centralizer ℝ ({A} : Set _)) := by
  let f : Module.End ℝ (Fin n → ℝ) := Matrix.toLinAlgEquiv' A
  let M : Module.End ℝ (Fin n → ℝ) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toMatrixAlgEquiv'
  let L := M.toLinearMap.comp (Subalgebra.centralizer ℝ ({f} : Set _)).toSubmodule.subtype
  have hc (F : Subalgebra.centralizer ℝ ({f} : Set _)) :
      L F ∈ Subalgebra.centralizer ℝ ({A} : Set _) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    change A * M F.val = M F.val * A
    have he := (Subalgebra.mem_centralizer_iff ℝ).mp F.property f (by simp)
    have hm := congrArg M he
    simpa only [map_mul, M, f, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'] using hm
  let T := LinearMap.codRestrict (Subalgebra.centralizer ℝ ({A} : Set _)).toSubmodule L hc
  have hi : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    apply M.injective
    exact congrArg Subtype.val hxy
  have hdim := end_centralizer_finrank_ge f
  have hcomp := LinearMap.finrank_le_finrank_of_injective hi
  change Module.finrank ℝ (Subalgebra.centralizer ℝ ({f} : Set _)) ≤
    Module.finrank ℝ (Subalgebra.centralizer ℝ ({A} : Set _)) at hcomp
  have hn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  omega

private def supportReadout {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Subalgebra.centralizer ℝ ({A} : Set _) →ₗ[ℝ] (E → ℝ) where
  toFun F e := A e.val.1 e.val.2 * F.val e.val.2 e.val.1
  map_add' F G := by ext e; simp [mul_add]
  map_smul' c F := by ext e; simp [mul_left_comm]

private theorem supportReadout_injective {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ExactSupport E A) (hN : HasNSSP A) :
    Function.Injective (supportReadout E A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  have hz : F.val.transpose = 0 := by
    apply hN
    · intro i j
      by_cases he : (i,j) ∈ E
      · exact congrFun hF ⟨(i,j), he⟩
      · have ha : A i j = 0 := by
          by_contra hz
          exact he ((hA i j).mp hz)
        simp [ha]
    · rw [Matrix.transpose_transpose]
      exact sub_eq_zero.mpr ((Subalgebra.mem_centralizer_iff ℝ).mp F.property A (by simp))
  apply Subtype.ext
  exact Matrix.transpose_injective (by simpa using hz)

/-- The real signed boundary; its loop columns vanish. -/
def incidence {n : ℕ} (E : Finset (Fin n × Fin n)) : Matrix (Fin n) E ℝ :=
  fun v e =>
    (D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence
      (fun e : E => e.val.1) (fun e : E => e.val.2) v e : ℝ)

/-- Edgewise constant real functions are globally constant. -/
def ConnectedSupport {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∀ p : Fin n → ℝ, (∀ e : E, p e.val.1 = p e.val.2) → ∀ i j, p i = p j

private theorem incidence_apply {n : ℕ} (E : Finset (Fin n × Fin n)) (v : Fin n) (e : E) :
    incidence E v e = (if v = e.val.2 then 1 else 0) - (if v = e.val.1 then 1 else 0) := by
  simp only [incidence,
    D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity.signedIncidence,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]

private theorem sum_support {n : ℕ} (E : Finset (Fin n × Fin n))
    (t : (Fin n × Fin n) → ℝ) (ht : ∀ e ∉ E, t e = 0) :
    ∑ e : E, t e.val = ∑ i : Fin n, ∑ j : Fin n, t (i,j) := by
  calc
    _ = ∑ e ∈ E, t e := (Finset.sum_subtype E (fun _ => Iff.rfl) t).symm
    _ = ∑ e : Fin n × Fin n, t e :=
      Finset.sum_subset (Finset.subset_univ _) (fun e _ he => ht e he)
    _ = _ := Fintype.sum_prod_type _

private theorem supportReadout_boundary_zero {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ExactSupport E A)
    (F : Subalgebra.centralizer ℝ ({A} : Set _)) :
    (incidence E).mulVecLin (supportReadout E A F) = 0 := by
  ext v
  change ∑ e : E, incidence E v e * (A e.val.1 e.val.2 * F.val e.val.2 e.val.1) = 0
  simp_rw [incidence_apply]
  rw [sum_support E (fun e =>
    ((if v = e.2 then 1 else 0) - (if v = e.1 then 1 else 0)) * (A e.1 e.2 * F.val e.2 e.1))]
  · simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => (if v = j then 1 else 0) * (A i j * F.val j i))]
    simp only [ite_mul, one_mul, zero_mul]
    change (∑ j : Fin n, ∑ i : Fin n, if v = j then A i j * F.val j i else 0) -
      (∑ i : Fin n, ∑ j : Fin n, if v = i then A i j * F.val j i else 0) = 0
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hc := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M v v)
      ((Subalgebra.mem_centralizer_iff ℝ).mp F.property A (by simp))
    simp only [Matrix.mul_apply] at hc
    simp_rw [mul_comm (A _ v)]
    exact sub_eq_zero.mpr hc.symm
  · intro e he
    have ha : A e.1 e.2 = 0 := by
      by_contra hz
      exact he ((hA e.1 e.2).mp hz)
    simp [ha]

/-- nSSP injects the full real centralizer into the signed cycle space. -/
theorem nssp_centralizer_cycle_bound {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ExactSupport E A) (hN : HasNSSP A) :
    n + (incidence E).rank ≤ E.card := by
  let T := LinearMap.codRestrict (LinearMap.ker (incidence E).mulVecLin)
    (supportReadout E A) (fun F => supportReadout_boundary_zero E A hA F)
  have hi : Function.Injective T := fun x y hxy =>
    supportReadout_injective E A hA hN (congrArg Subtype.val hxy)
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have hc := matrix_centralizer_finrank_ge A
  have hr := (incidence E).mulVecLin.finrank_range_add_finrank_ker
  have he : Module.finrank ℝ (E → ℝ) = E.card := by simp
  change (incidence E).rank + _ = _ at hr
  omega

private theorem transpose_incidence_apply {n : ℕ} (E : Finset (Fin n × Fin n))
    (p : Fin n → ℝ) (e : E) :
    (incidence E).transpose.mulVecLin p e = p e.val.2 - p e.val.1 := by
  change (∑ v : Fin n, incidence E v e * p v) = _
  simp_rw [incidence_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp [ite_mul]

private theorem incidence_rank_ge {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (Fin n × Fin n)) (hconn : ConnectedSupport E) :
    n-1 ≤ (incidence E).rank := by
  let r : Fin n := ⟨0, hn⟩
  let K := LinearMap.ker (incidence E).transpose.mulVecLin
  have hconst (p : K) : ∀ i j : Fin n, p.val i = p.val j := by
    apply hconn
    intro e
    have hz : (incidence E).transpose.mulVecLin p.val = 0 := p.property
    have he := congrFun hz e
    rw [transpose_incidence_apply] at he
    exact (sub_eq_zero.mp he).symm
  let T : K →ₗ[ℝ] ℝ := (LinearMap.proj r).comp K.subtype
  have hi : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    funext i
    calc
      x.val i = x.val r := hconst x i r
      _ = y.val r := hxy
      _ = y.val i := (hconst y i r).symm
  have hk := LinearMap.finrank_le_finrank_of_injective hi
  have hk' : Module.finrank ℝ K ≤ 1 := by simpa using hk
  have hr := (incidence E).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (incidence E).transpose.rank + Module.finrank ℝ K = _ at hr
  rw [Matrix.rank_transpose] at hr
  have hs : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  omega

/-- A connected exact support of one nSSP matrix already has at least 2n-1 arcs. -/
theorem nssp_arc_bound_of_connected {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (Fin n × Fin n)) (hconn : ConnectedSupport E)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ExactSupport E A) (hN : HasNSSP A) :
    2*n-1 ≤ E.card := by
  have hcycle := nssp_centralizer_cycle_bound E A hA hN
  have hr := incidence_rank_ge hn E hconn
  omega

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
