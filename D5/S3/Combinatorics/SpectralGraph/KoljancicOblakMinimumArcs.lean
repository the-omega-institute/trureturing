/- GID: D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact real support and centralizer obstructions for the minimum nSSP arc problem. -/

/-
proof_shape is assessed after expansion of this unit's helpers to frozen or pinned suppliers.
Definitions HasNSSP, ExactSupport, Requires, MinimumArcs, incidence, ConnectedSupport,
endpointSupport, supportReadout and entry introduce the objects consumed below.

| Declaration | proof_shape | Live direct consumer |
| end_centralizer_finrank_ge | content | matrix_centralizer_finrank_ge |
| matrix_centralizer_finrank_ge | bind-only | nssp_centralizer_cycle_bound |
| supportReadout_injective | bind-only | nssp_centralizer_cycle_bound |
| incidence_apply | bind-only | supportReadout_boundary_zero, transpose_incidence_apply |
| sum_support | bind-only | supportReadout_boundary_zero |
| supportReadout_boundary_zero | bind-only | nssp_centralizer_cycle_bound |
| nssp_centralizer_cycle_bound | content | nssp_arc_bound_of_connected |
| transpose_incidence_apply | bind-only | incidence_rank_ge |
| incidence_rank_ge | bind-only | nssp_arc_bound_of_connected |
| nssp_arc_bound_of_connected | content | result |
| entry_eq | bind-only | row_product, endpoint_diagonal, upper_odd_zero, endpoint_commuting_zero |
| entry_left_zero | bind-only | row_product, endpoint_diagonal, endpoint_commuting_zero |
| entry_right_zero | bind-only | row_product, upper_odd_zero, endpoint_commuting_zero |
| sum_fin_fiber | bind-only | row_product |
| row_product | bind-only | col_product, upper_odd_zero, endpoint_commuting_zero |
| entry_transpose | bind-only | col_product, endpoint_commuting_zero |
| col_product | bind-only | upper_odd_zero, endpoint_commuting_zero |
| endpoint_band | bind-only | upper_odd_zero, endpoint_commuting_zero |
| endpoint_diagonal | bind-only | upper_odd_zero, endpoint_commuting_zero |
| endpoint_next_ne_zero | bind-only | upper_odd_zero, endpoint_commuting_zero |
| upper_odd_zero | content | endpoint_commuting_zero |
| endpoint_commuting_zero | content | endpoint_requires |
| endpoint_requires | content | endpoint_attainment |
| endpoint_card | bind-only | endpoint_attainment |
| endpoint_attainment | content | result |
| nssp_level_diagonal | content | requires_level_has_loop |
| requires_level_has_loop | content | requires_connected |
| loop_support_eigenvalue_one | content | loop_realization |
| loop_realization | bind-only | requires_connected |
| two_blocks_obstruction | bind-only | requires_connected |
| requires_connected | content | result |
| result | content | terminal exact external problem |

admission_basis: escape-witness.
Escape content includes upper_odd_zero: its odd-offset induction is needed on the
live path endpoint_commuting_zero → endpoint_requires → endpoint_attainment → result.
The quotient-ring centralizer action and the loop-preserving singular realization
supply additional mathematical bridges. The full event corresponds to Problem 1.8
in preregistration #25108; the endpoint-path upper construction is prior art.
All retained declarations are parametric mathematics. Utility classification is none:
there is no certified finite instance, bounded enumeration, numeric reduction or checker.
endpointSupport is an explicit family at arbitrary order, not a bounded search result.
The only frozen D5 supplier is signedIncidence, with statement_id
sha256:114ad2007c6fbab39d7a155a5cecadd6c60ebce9d41e54a426d2e808cc2c5b87.
Its total-unimodularity result is not used. The PID and matrix suppliers are pinned Mathlib.
-/

import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity

/-!
Real matrices with exact directed support are tested against every real obstruction matrix.
The centralizer bound uses the polynomial module structure over the original field.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators DirectSum Matrix
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

/-- Bidirected consecutive edges and one loop at the first vertex. -/
def endpointSupport (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => (e.1.val = 0 ∧ e.2.val = 0) ∨
    e.1.val + 1 = e.2.val ∨ e.2.val + 1 = e.1.val

private def entry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) : ℝ :=
  if hi : i < n then if hj : j < n then M ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

private theorem entry_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {i j : ℕ} (hi : i < n) (hj : j < n) : entry M i j = M ⟨i,hi⟩ ⟨j,hj⟩ := by
  simp [entry, hi, hj]

private theorem entry_left_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {i j : ℕ} (hi : n ≤ i) : entry M i j = 0 := by simp [entry, Nat.not_lt.mpr hi]

private theorem entry_right_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {i j : ℕ} (hj : n ≤ j) : entry M i j = 0 := by
  simp [entry, Nat.not_lt.mpr hj]

private theorem sum_fin_fiber (n a : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin n, if k.val = a then f k.val else 0) = if a < n then f a else 0 := by
  split_ifs with ha
  · let k : Fin n := ⟨a,ha⟩
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro b _ hb
      have hne : b.val ≠ a := fun h => hb (Fin.ext h)
      simp [hne]
    · simp
  · apply Finset.sum_eq_zero
    intro k _
    have hne : k.val ≠ a := by intro h; exact ha (h ▸ k.isLt)
    simp [hne]

private theorem row_product {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, i.val+1 < j.val ∨ j.val+1 < i.val → A i j = 0)
    (i j : ℕ) :
    entry (A*F) i j =
      (if 0 < i then entry A i (i-1) * entry F (i-1) j else 0) +
      entry A i i * entry F i j + entry A i (i+1) * entry F (i+1) j := by
  by_cases hi : i < n
  · by_cases hj : j < n
    · rw [entry_eq _ hi hj, Matrix.mul_apply]
      have hsum (k : Fin n) :
          A ⟨i,hi⟩ k * F k ⟨j,hj⟩ =
          (if k.val+1 = i then entry A i k.val * entry F k.val j else 0) +
          (if k.val = i then entry A i k.val * entry F k.val j else 0) +
          (if k.val = i+1 then entry A i k.val * entry F k.val j else 0) := by
        rw [entry_eq _ hi k.isLt, entry_eq _ k.isLt hj]
        by_cases h0 : k.val+1 = i
        · simp [h0, show k.val ≠ i by omega, show k.val ≠ i+1 by omega]
        · by_cases h1 : k.val = i
          · have hkeq : k = ⟨i,hi⟩ := Fin.ext h1
            subst k
            simp
          · by_cases h2 : k.val = i+1
            · have hklt : i+1 < n := by omega
              have hkeq : k = ⟨i+1,hklt⟩ := Fin.ext h2
              subst k
              simp [show i+1+1 ≠ i by omega]
            · have hz := hband ⟨i,hi⟩ k (by dsimp; omega)
              simp [h0,h1,h2,hz]
      simp_rw [hsum, Finset.sum_add_distrib]
      by_cases hip : 0 < i
      · have hc (k : Fin n) : k.val+1 = i ↔ k.val = i-1 := by omega
        simp_rw [hc]
        rw [sum_fin_fiber n (i-1) (fun k => entry A i k * entry F k j),
          sum_fin_fiber n i (fun k => entry A i k * entry F k j),
          sum_fin_fiber n (i+1) (fun k => entry A i k * entry F k j)]
        have hp : i-1 < n := by omega
        simp only [hip, hp, hi, ite_true]
        by_cases hnxt : i+1 < n
        · simp [hnxt]
        · simp [hnxt, entry_right_zero A (Nat.le_of_not_gt hnxt)]
      · have hi0 : i = 0 := by omega
        subst i
        have hz (k : Fin n) : ¬ k.val+1 = 0 := by omega
        simp only [hz, ite_false, Finset.sum_const_zero, zero_add]
        rw [sum_fin_fiber n 0 (fun k => entry A 0 k * entry F k j),
          sum_fin_fiber n 1 (fun k => entry A 0 k * entry F k j)]
        simp only [hi, ite_true, lt_self_iff_false, ite_false, zero_add]
        by_cases hnxt : 1 < n
        · simp [hnxt]
        · simp [hnxt, entry_right_zero A (Nat.le_of_not_gt hnxt)]
    · have hj' : n ≤ j := Nat.le_of_not_gt hj
      simp [entry_right_zero _ hj']
  · have hi' : n ≤ i := Nat.le_of_not_gt hi
    simp [entry_left_zero _ hi']

private theorem entry_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    entry M.transpose i j = entry M j i := by
  unfold entry
  split_ifs <;> rfl

private theorem col_product {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, i.val+1 < j.val ∨ j.val+1 < i.val → A i j = 0)
    (i j : ℕ) :
    entry (F*A) i j =
      (if 0 < j then entry F i (j-1) * entry A (j-1) j else 0) +
      entry F i j * entry A j j + entry F i (j+1) * entry A (j+1) j := by
  have ht (i j : Fin n) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
      A.transpose i j = 0 := hband j i h.symm
  have h := row_product A.transpose F.transpose ht j i
  rw [← Matrix.transpose_mul, entry_transpose] at h
  simp_rw [entry_transpose] at h
  simpa only [mul_comm] using h

private theorem endpoint_band {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ExactSupport (endpointSupport n) A) :
    ∀ i j : Fin n, i.val+1 < j.val ∨ j.val+1 < i.val → A i j = 0 := by
  intro i j h
  by_contra hz
  have he := (hA i j).mp hz
  simp only [endpointSupport, Finset.mem_filter, Finset.mem_univ, true_and] at he
  omega

private theorem endpoint_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ExactSupport (endpointSupport n) A) {i : ℕ} (hi : 0 < i) : entry A i i = 0 := by
  by_cases hin : i < n
  · rw [entry_eq _ hin hin]
    by_contra hz
    have he := (hA ⟨i,hin⟩ ⟨i,hin⟩).mp hz
    simp only [endpointSupport, Finset.mem_filter, Finset.mem_univ, true_and] at he
    omega
  · exact entry_left_zero _ (Nat.le_of_not_gt hin)

private theorem endpoint_next_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ExactSupport (endpointSupport n) A) {i : ℕ} (hi : i+1 < n) :
    entry A (i+1) i ≠ 0 := by
  have hi' : i < n := by omega
  rw [entry_eq _ hi hi']
  apply (hA _ _).mpr
  simp [endpointSupport]

private theorem upper_odd_zero {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ExactSupport (endpointSupport n) A)
    (hnear : ∀ i j : Fin n, i.val+1 = j.val → F i j = 0)
    (hcomm : A*F = F*A) :
    ∀ k : ℕ, Odd k → ∀ i : ℕ, entry F i (i+k) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk i
    by_cases hj : i+k < n
    · have hkp : 0 < k := hk.pos
      have hi : i < n := by omega
      by_cases hk1 : k = 1
      · subst k
        rw [entry_eq _ hi hj]
        exact hnear _ _ (by simp)
      · have hk3 : 3 ≤ k := by obtain ⟨r,hr⟩ := hk; omega
        have hks : Odd (k-2) := by obtain ⟨r,hr⟩ := hk; exact ⟨r-1,by omega⟩
        have descend : ∀ r : ℕ, ∀ i : ℕ, n-i = r → entry F i (i+k) = 0 := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r ir =>
            intro i hir
            by_cases hj : i+k < n
            · have hnext := ir (n-(i+1)) (by omega) (i+1) rfl
              have hshift : i+1+k = i+k+1 := by omega
              rw [hshift] at hnext
              have hsmall1 := ih (k-2) (by omega) hks (i+2)
              have hsmall2 := ih (k-2) (by omega) hks (i+1)
              have h1 : i+2+(k-2) = i+k := by omega
              have h2 : i+1+(k-2) = i+k-1 := by omega
              rw [h1] at hsmall1
              rw [h2] at hsmall2
              have hc := congrArg (fun M => entry M (i+1) (i+k)) hcomm
              rw [row_product A F (endpoint_band A hA), col_product A F (endpoint_band A hA)] at hc
              have hd1 := endpoint_diagonal A hA (show 0 < i+1 by omega)
              have hd2 := endpoint_diagonal A hA (show 0 < i+k by omega)
              have hp1 : 0 < i+1 := by omega
              have hp2 : 0 < i+k := by omega
              have him : i+1-1 = i := by omega
              simp only [hp1, hp2, ite_true, him, hsmall1, hsmall2, hnext, hd1, hd2,
                zero_mul, mul_zero, add_zero, zero_add] at hc
              have hne : entry A (i+1) i ≠ 0 :=
                endpoint_next_ne_zero A hA (show i+1 < n by omega)
              exact (mul_eq_zero.mp hc).resolve_left hne
            · exact entry_right_zero _ (Nat.le_of_not_gt hj)
        exact descend (n-i) i rfl
    · exact entry_right_zero _ (Nat.le_of_not_gt hj)

private theorem endpoint_commuting_zero {n : ℕ} (hn : 1 ≤ n)
    (A F : Matrix (Fin n) (Fin n) ℝ) (hA : ExactSupport (endpointSupport n) A)
    (hzero : ∀ i j : Fin n, (i,j) ∈ endpointSupport n → F i j = 0)
    (hcomm : A*F = F*A) : F = 0 := by
  have hnear (i j : Fin n) (h : i.val+1 = j.val) : F i j = 0 := by
    apply hzero
    simp [endpointSupport, h]
  have hAT : ExactSupport (endpointSupport n) A.transpose := by
    intro i j
    rw [Matrix.transpose_apply, hA j i]
    simp only [endpointSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hnearT (i j : Fin n) (h : i.val+1 = j.val) : F.transpose i j = 0 := by
    apply hzero
    simp [endpointSupport, h]
  have hcommT : A.transpose*F.transpose = F.transpose*A.transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hcomm.symm
  have hup := upper_odd_zero A F hA hnear hcomm
  have hlow (k : ℕ) (hk : Odd k) (i : ℕ) : entry F (i+k) i = 0 := by
    have h := upper_odd_zero A.transpose F.transpose hAT hnearT hcommT k hk i
    simpa only [entry_transpose] using h
  have hd : entry A 0 0 ≠ 0 := by
    rw [entry_eq _ hn hn]
    apply (hA _ _).mpr
    simp [endpointSupport]
  have hcol0 : ∀ i : ℕ, entry F i 0 = 0 := by
    intro i
    by_cases hi : i < n
    · by_cases hi0 : i = 0
      · subst i
        rw [entry_eq _ hn hn]
        apply hzero
        simp [endpointSupport]
      · by_cases ho : Odd i
        · simpa only [zero_add] using hlow i ho 0
        · have he : Even i := (Nat.even_or_odd i).resolve_right ho
          have him : Odd (i-1) := by obtain ⟨r,hr⟩ := he; exact ⟨r-1,by omega⟩
          have hip : Odd (i+1) := by obtain ⟨r,hr⟩ := he; exact ⟨r,by omega⟩
          have hm : entry F (i-1) 0 = 0 := by simpa using hlow (i-1) him 0
          have hp : entry F (i+1) 0 = 0 := by simpa using hlow (i+1) hip 0
          have h1 : entry F i 1 = 0 := by
            have h := hlow (i-1) him 1
            have hs : 1+(i-1) = i := by omega
            simpa only [hs] using h
          have hc := congrArg (fun M => entry M i 0) hcomm
          rw [row_product A F (endpoint_band A hA), col_product A F (endpoint_band A hA)] at hc
          have hdiag := endpoint_diagonal A hA (show 0 < i by omega)
          simp only [hm, hp, h1, hdiag, mul_zero, zero_mul, add_zero, zero_add,
            lt_self_iff_false, ite_false, ite_self] at hc
          exact (mul_eq_zero.mp hc.symm).resolve_right hd
    · exact entry_left_zero _ (Nat.le_of_not_gt hi)
  have hcols : ∀ j : ℕ, ∀ i : ℕ, entry F i j = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro i
      by_cases hj : j < n
      · cases j with
        | zero => exact hcol0 i
        | succ k =>
          have hk : k < n := by omega
          have hz : ∀ i : ℕ, entry F i k = 0 := ih k (by omega)
          have hp : entry F i (k-1) = 0 := ih (k-1) (by omega) i
          have hc := congrArg (fun M => entry M i k) hcomm
          rw [row_product A F (endpoint_band A hA), col_product A F (endpoint_band A hA)] at hc
          simp only [hz, hp, mul_zero, zero_mul, add_zero, zero_add, ite_self] at hc
          exact (mul_eq_zero.mp hc.symm).resolve_right (endpoint_next_ne_zero A hA hj)
      · exact entry_right_zero _ (Nat.le_of_not_gt hj)
  ext i j
  change F i j = 0
  simpa only [entry_eq F i.isLt j.isLt] using hcols j.val i.val

/-- Every real weighting of the endpoint-looped double path has nSSP. -/
theorem endpoint_requires (n : ℕ) (hn : 1 ≤ n) : Requires (endpointSupport n) := by
  intro A hA X hX hcomm
  have hzero (i j : Fin n) (he : (i,j) ∈ endpointSupport n) : X.transpose i j = 0 := by
    have hswap : (j,i) ∈ endpointSupport n := by
      simp only [endpointSupport, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      omega
    have ha := (hA j i).mpr hswap
    exact (mul_eq_zero.mp (hX j i)).resolve_left ha
  have hF := endpoint_commuting_zero hn A X.transpose hA hzero (sub_eq_zero.mp hcomm)
  exact Matrix.transpose_injective (by simpa using hF)

private theorem endpoint_card (n : ℕ) (hn : 1 ≤ n) :
    (endpointSupport n).card = 2*n-1 := by
  let z : Fin n := ⟨0,hn⟩
  let g : Unit ⊕ (Fin (n-1) ⊕ Fin (n-1)) → endpointSupport n
    | .inl _ => ⟨(z,z), by simp [endpointSupport,z]⟩
    | .inr (.inl i) => ⟨(⟨i.val,by have := i.isLt; omega⟩,
        ⟨i.val+1,by have := i.isLt; omega⟩), by simp [endpointSupport]⟩
    | .inr (.inr i) => ⟨(⟨i.val+1,by have := i.isLt; omega⟩,
        ⟨i.val,by have := i.isLt; omega⟩), by simp [endpointSupport]⟩
  have hi : Function.Injective g := by
    intro x y h
    rcases x with u | (i | i) <;> rcases y with v | (j | j) <;>
      simp_all [g,z,Subtype.ext_iff,Prod.ext_iff,Fin.ext_iff] <;> omega
  have hs : Function.Surjective g := by
    rintro ⟨⟨i,j⟩,he⟩
    simp only [endpointSupport,Finset.mem_filter,Finset.mem_univ,true_and] at he
    rcases he with he | he | he
    · refine ⟨.inl (),?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp_all [g,z]
    · let k : Fin (n-1) := ⟨i.val,by have := j.isLt; omega⟩
      refine ⟨.inr (.inl k),?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp_all [g,k]
    · let k : Fin (n-1) := ⟨j.val,by have := i.isLt; omega⟩
      refine ⟨.inr (.inr k),?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp_all [g,k]
  have hc := Fintype.card_congr (Equiv.ofBijective g ⟨hi,hs⟩)
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,Fintype.card_coe] at hc
  omega

/-- The endpoint-looped path attains 2n-1 arcs at every positive order. -/
theorem endpoint_attainment (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Finset (Fin n × Fin n), Requires E ∧ E.card = 2*n-1 :=
  ⟨endpointSupport n, endpoint_requires n hn, endpoint_card n hn⟩


private theorem nssp_level_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hN : HasNSSP A) (p : Fin n → ℝ)
    (hp : ∀ i j, A i j ≠ 0 → p i = p j) (r : Fin n) :
    ∃ i : Fin n, p i = p r ∧ A i i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let d : Fin n → ℝ := fun i => if p i = p r then 1 else 0
  let X : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d
  have hX : ∀ i j, A i j * X i j = 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      by_cases hi : p i = p r
      · simp [X, d, hi, h i hi]
      · simp [X, d, hi]
    · simp [X, Matrix.diagonal_apply, hij]
  have hc : A * X = X * A := by
    ext i j
    simp only [X, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : A i j = 0
    · simp [ha]
    · have he := hp i j ha
      have hd : d i = d j := by simp only [d,he]
      rw [hd, mul_comm]
  have hz := hN X hX (by simpa only [X, Matrix.diagonal_transpose] using sub_eq_zero.mpr hc)
  have hb := congrArg (fun M => M r r) hz
  have : (1 : ℝ) = 0 := by simpa [X,d] using hb
  exact one_ne_zero this

/-- Every nonempty edgewise constant level of a requiring support contains a loop. -/
theorem requires_level_has_loop {n : ℕ} (E : Finset (Fin n × Fin n))
    (hE : Requires E) (p : Fin n → ℝ)
    (hp : ∀ e : E, p e.val.1 = p e.val.2) (r : Fin n) :
    ∃ i : Fin n, p i = p r ∧ (i,i) ∈ E := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => if (i,j) ∈ E then 1 else 0
  have hA : ExactSupport E A := by
    intro i j
    simp [A]
  have hconst : ∀ i j, A i j ≠ 0 → p i = p j := by
    intro i j hij
    exact hp ⟨(i,j),(hA i j).mp hij⟩
  obtain ⟨i,hi,hii⟩ := nssp_level_diagonal A (hE A hA) p hconst r
  exact ⟨i,hi,(hA i i).mp hii⟩

/-- A prescribed loop permits eigenvalue one without deleting any prescribed arc. -/
theorem loop_support_eigenvalue_one {n : ℕ} (E : Finset (Fin n × Fin n))
    (r : Fin n) (hr : (r,r) ∈ E) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, ExactSupport E A ∧ (1-A).det = 0 := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if (i,j) ∈ E ∧ (i,j) ≠ (r,r) then 1 else 0
  let N : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => 1 - t • B
  let q : Fin n → ℝ := Pi.single r 1
  let α : ℝ → ℝ := fun t => (N t).det
  let β : ℝ → ℝ := fun t => ((N t).updateRow r q).det
  have hN0 : N 0 = 1 := by simp [N]
  have hq : q = (1 : Matrix (Fin n) (Fin n) ℝ) r := by
    ext j
    simp [q, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hα0 : α 0 = 1 := by simp [α,hN0]
  have hβ0 : β 0 = 1 := by simp [β,hN0,hq]
  have hNc : Continuous N := by dsimp [N]; fun_prop
  have hαc : Continuous α := hNc.matrix_det
  have hβc : Continuous β := (hNc.matrix_updateRow r continuous_const).matrix_det
  have hev : ∀ᶠ t in nhds (0 : ℝ), α t ≠ 0 ∧ β t ≠ 0 :=
    (hαc.continuousAt.eventually_ne (by rw [hα0]; exact one_ne_zero)).and
      (hβc.continuousAt.eventually_ne (by rw [hβ0]; exact one_ne_zero))
  obtain ⟨l,u,hlu,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  let t : ℝ := u/2
  have ht : t ≠ 0 := by dsimp [t]; linarith [hlu.2]
  have hab : α t ≠ 0 ∧ β t ≠ 0 := hsub (by constructor <;> dsimp [t] <;> linarith [hlu.1,hlu.2])
  let a : ℝ := α t / β t
  have ha : a ≠ 0 := div_ne_zero hab.1 hab.2
  let M : Matrix (Fin n) (Fin n) ℝ := (N t).updateRow r ((N t) r + (-a) • q)
  let A : Matrix (Fin n) (Fin n) ℝ := 1-M
  have hdet : M.det = 0 := by
    dsimp only [M]
    rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
    change α t + (-a) * β t = 0
    dsimp only [a]
    field_simp [hab.2]
    <;> ring
  have hspecial : A r r = a := by
    simp [A,M,N,B,q,Matrix.updateRow,Matrix.one_apply,Pi.single_apply]
  have hother (i j : Fin n) (hij : (i,j) ≠ (r,r)) : A i j = t * B i j := by
    by_cases hir : i = r
    · subst i
      have hjr : j ≠ r := by intro h; exact hij (by simp [h])
      simp [A,M,N,q,Matrix.updateRow,Matrix.one_apply,Pi.single_apply,hjr,Ne.symm hjr]
    · simp [A,M,N,Matrix.updateRow,hir]
  refine ⟨A,?_,?_⟩
  · intro i j
    by_cases hij : (i,j) = (r,r)
    · have hi : i = r := congrArg Prod.fst hij
      have hj : j = r := congrArg Prod.snd hij
      subst i
      subst j
      simp [hspecial,ha,hr]
    · rw [hother i j hij]
      by_cases he : (i,j) ∈ E
      · simp only [B, if_pos (And.intro he hij), mul_one]
        exact ⟨fun _ => he,fun _ => ht⟩
      · simp [B,he]
  · have hM : 1-A = M := by dsimp [A]; abel
    rw [hM]
    exact hdet


private theorem loop_realization {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → ι → Prop) (r : ι) (hr : P r r) :
    ∃ A : Matrix ι ι ℝ, (∀ i j, A i j ≠ 0 ↔ P i j) ∧ (1-A).det = 0 := by
  classical
  let e := Fintype.equivFin ι
  let E : Finset (Fin (Fintype.card ι) × Fin (Fintype.card ι)) :=
    Finset.univ.filter (fun ij => P (e.symm ij.1) (e.symm ij.2))
  obtain ⟨A,hA,hd⟩ := loop_support_eigenvalue_one E (e r) (by simp [E,hr])
  let L := Matrix.reindexAlgEquiv ℝ ℝ e.symm
  refine ⟨L A,?_,?_⟩
  · intro i j
    simpa [L,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,E] using hA (e i) (e j)
  · rw [← map_one L, ← map_sub, Matrix.det_reindexAlgEquiv]
    exact hd

private theorem two_blocks_obstruction {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (hC : (1-C).det = 0) (hD : (1-D).det = 0) :
    ∃ F : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ, F ≠ 0 ∧
      (∀ i j, (Matrix.fromBlocks C 0 0 D) i j * F.transpose i j = 0) ∧
      Matrix.fromBlocks C 0 0 D * F = F * Matrix.fromBlocks C 0 0 D := by
  obtain ⟨u,hu,heu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hC
  obtain ⟨v,hv,hev⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hD
  have hCu : C *ᵥ u = u := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec] at heu
    exact (sub_eq_zero.mp heu).symm
  have hvD : v ᵥ* D = v := by
    rw [Matrix.vecMul_sub,Matrix.vecMul_one] at hev
    exact (sub_eq_zero.mp hev).symm
  let R := Matrix.vecMulVec u v
  let F : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks 0 R 0 0
  have hF : F ≠ 0 := by
    intro hz
    obtain ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by contrapose! hu; ext i; exact hu i
    obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by contrapose! hv; ext j; exact hv j
    have h := congrArg (fun M => M (.inl i) (.inr j)) hz
    exact mul_ne_zero hi hj (by simpa [F,R,Matrix.vecMulVec] using h)
  refine ⟨F,hF,?_,?_⟩
  · intro i j
    cases i <;> cases j <;> simp [F,Matrix.transpose_apply]
  · simp only [F,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add]
    congr 1
    simpa only [R,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hCu,hvD]

/-- Every real exact-support requiring pattern is connected. -/
theorem requires_connected {n : ℕ} (E : Finset (Fin n × Fin n))
    (hE : Requires E) : ConnectedSupport E := by
  classical
  intro p hp i j
  by_contra hij
  obtain ⟨r,hr,hrE⟩ := requires_level_has_loop E hE p hp i
  obtain ⟨s,hs,hsE⟩ := requires_level_has_loop E hE p hp j
  let Q : Fin n → Prop := fun v => p v = p i
  let S := {v : Fin n // Q v}
  let T := {v : Fin n // ¬ Q v}
  have hsQ : ¬ Q s := by dsimp [Q]; intro he; exact hij (he.symm.trans hs)
  obtain ⟨C,hC,hdC⟩ := loop_realization
    (fun a b : S => (a.val,b.val) ∈ E) ⟨r,hr⟩ hrE
  obtain ⟨D,hD,hdD⟩ := loop_realization
    (fun a b : T => (a.val,b.val) ∈ E) ⟨s,hsQ⟩ hsE
  have hcST (a : S) (b : T) : (a.val,b.val) ∉ E := by
    intro he
    exact b.property ((hp ⟨(a.val,b.val),he⟩).symm.trans a.property)
  have hcTS (a : T) (b : S) : (a.val,b.val) ∉ E := by
    intro he
    exact a.property ((hp ⟨(a.val,b.val),he⟩).trans b.property)
  let B : Matrix (S ⊕ T) (S ⊕ T) ℝ := Matrix.fromBlocks C 0 0 D
  let e : S ⊕ T ≃ Fin n := Equiv.sumCompl Q
  let L := Matrix.reindexAlgEquiv ℝ ℝ e
  let A := L B
  have hA : ExactSupport E A := by
    intro i j
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    simp only [A,L,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,
      Matrix.submatrix_apply,Equiv.symm_apply_apply]
    cases i with
    | inl a =>
      cases j with
      | inl b => exact hC a b
      | inr b => exact iff_of_false (by simp [B]) (hcST a b)
    | inr a =>
      cases j with
      | inl b => exact iff_of_false (by simp [B]) (hcTS a b)
      | inr b => exact hD a b
  obtain ⟨F,hF,hzero,hcomm⟩ := two_blocks_obstruction C D hdC hdD
  let G := L F
  have hG : G ≠ 0 := by
    intro h
    apply hF
    apply L.injective
    simpa only [map_zero] using (show L F = 0 from h)
  have hz : G.transpose = 0 := by
    apply hE A hA
    · intro i j
      obtain ⟨i,rfl⟩ := e.surjective i
      obtain ⟨j,rfl⟩ := e.surjective j
      simpa only [A,G,L,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,
        Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.transpose_apply] using hzero i j
    · rw [Matrix.transpose_transpose]
      apply sub_eq_zero.mpr
      change L B * L F = L F * L B
      rw [← map_mul,← map_mul,hcomm]
  exact hG (Matrix.transpose_injective (by simpa using hz))

/-- The complete all-positive-order minimum nSSP arc result. -/
theorem result : MinimumArcs := by
  intro n hn
  constructor
  · intro E hE
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j => if (i,j) ∈ E then 1 else 0
    have hA : ExactSupport E A := by intro i j; simp [A]
    exact nssp_arc_bound_of_connected hn E (requires_connected E hE) A hA (hE A hA)
  · exact endpoint_attainment n hn

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
