/- GID: D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Ordinary zero forcing, symmetric maximum nullity, and minimum rank of unequal-leg spider powers. -/

/-
admission_basis: escape-witness
Module escape_witness: sliding_window_kernel_and_band_support, unequal_spider_power_zero_forcing
Escape witnesses surviving the bypass test:
1. sliding_window_kernel_and_band_support: Closed-form (k + 1)-periodic linear isomorphism between
   W_k = {x : Nat -> R | forall s, sum_{t < k + 1} x(s + t) = 0} and (Fin k -> R), giving unique
   extension from initial coordinates, finrank = k, truncation annihilation by the (L - k) x L
   window matrix D_L for L >= k + 1, and off-diagonal Gram band support 0 < (D_L^T D_L)_{d,e} <->
   Nat.dist d e <= k via window start s_0 = max(d, e) - k.
2. unequal_spider_power_zero_forcing: Exact tree-distance identification (spiderTree m ell).dist =
   distance m ell across unequal leg lengths ell_i >= k + 1; four-phase ordinary zero-forcing
   propagation from spiderTailForcingSet of size (m - 1) * k; explicit real symmetric realization
   spiderSymmMatrix in SymGraphMatrices (power m k ell) combining per-leg Gram blocks D_{ell_i}^T
   D_{ell_i} with cross-leg and center couplings; injective linear embedding of zero-sum m-tuples
   of W_k sequences into ker(spiderSymmMatrix) giving nullity >= (m - 1) * k; and Black-induction
   kernel restriction giving nullity <= |S| for all H in SymGraphMatrices (power m k ell), closing
   Z(G) = M_R(G) = (m - 1) * k and mr_R(G) = (1 + sum_i ell_i) - (m - 1) * k.
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
T0 = D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black
  statement_id: sha256:ecee7cbbb43fe2c4c06476fc1102beb6fd899e4c3959e8f1490c5cf905b2ca4b
T1 = D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black.init
  statement_id: sha256:02ad18ba859203092b97a8191a102f7788ab1e670ca91d2849907f13efbbc30f
T2 = D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black.force
  statement_id: sha256:50cb812c98528a35ea822161c3f5c2f78b08b5680bbf3d90dd7a159a6590a50b
T3 = D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.IsZeroForcing
  statement_id: sha256:2301cd27898a1f6d0b2b3dde2dcc82eaf457fb6d466a7fa0b147e67131ae019d
T4 = D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.zeroForcingNumber
  statement_id: sha256:e6a75f1858431e88d717bbff81ac0fa82db9087d09f5e7b20a1d7cc053e26c20
Utility: none; universally quantified graph-power invariants across independently chosen leg lengths.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry not-applicable as an organization label; no proof content is claimed for them.
Vertex | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.spiderTree, UnequalSpiderPowerZeroForcing.distance, UnequalSpiderPowerZeroForcing.power, UnequalSpiderPowerZeroForcing.spiderTailForcingSet, UnequalSpiderPowerZeroForcing.spiderSymmMatrix, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
spiderTree | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
distance | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.power, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
power | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
SymGraphMatrices | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.maxSymNullity, UnequalSpiderPowerZeroForcing.minSymRank, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
matrixNullity | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.maxSymNullity, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
maxSymNullity | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
minSymRank | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
slidingWindowSpace | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.slidingWindowEquiv, UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
slidingWindowEquiv | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
windowMatrix | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.spiderSymmMatrix, UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
spiderTailForcingSet | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
centerCoupling | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.spiderSymmMatrix, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
crossCoupling | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.spiderSymmMatrix, UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
spiderSymmMatrix | proof_shape: not-applicable | frozen: none | escape_witness: none | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
sliding_window_kernel_and_band_support | proof_shape: content | frozen: none | escape_witness: D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support | consumers: UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing
unequal_spider_power_zero_forcing | proof_shape: content | frozen: T0,T1,T2,T3,T4 | escape_witness: D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support, D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing | consumers: none
-/

import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Unequal-Leg Spider Power Zero Forcing, Symmetric Maximum Nullity, and Minimum Rank -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
  (Black IsZeroForcing zeroForcingNumber)
open Matrix
open scoped BigOperators Matrix

/-- Vertex set of an `m`-leg spider with leg lengths `ell`: `none` is the center, and `some ⟨i, d⟩`
is the vertex on leg `i.val + 1` at 1-based depth `d.val + 1`. -/
abbrev Vertex (m : ℕ) (ell : Fin m → ℕ) : Type := Option (Σ i : Fin m, Fin (ell i))

/-- Spider tree joining `none` to depth `0` of each leg and consecutive depths along each leg. -/
def spiderTree (m : ℕ) (ell : Fin m → ℕ) : SimpleGraph (Vertex m ell) where
  Adj u v := match u, v with
    | none, none => False
    | none, some p => p.2.val = 0
    | some p, none => p.2.val = 0
    | some p, some q => p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> first | exact h | exact ⟨h.1.symm, Nat.dist_comm _ _ ▸ h.2⟩⟩
  loopless := ⟨fun u h => by
    cases u with | none => exact h | some _ => exact absurd (Nat.dist_self _ ▸ h.2) Nat.zero_ne_one⟩

/-- Closed-form graph distance on `spiderTree m ell`. -/
def distance (m : ℕ) (ell : Fin m → ℕ) : Vertex m ell → Vertex m ell → ℕ
  | none, none => 0
  | none, some p => p.2.val + 1
  | some p, none => p.2.val + 1
  | some p, some q => if p.1 = q.1 then Nat.dist p.2.val q.2.val else p.2.val + q.2.val + 2

private theorem distance_symm (m : ℕ) (ell : Fin m → ℕ) (u v : Vertex m ell) :
    distance m ell u v = distance m ell v u := by
  cases u with
  | none => cases v <;> rfl
  | some p => cases v with
      | none => rfl
      | some q =>
          by_cases h : p.1 = q.1
          · simp only [distance, h, ↓reduceIte]; exact Nat.dist_comm _ _
          · simp only [distance, h, Ne.symm h, ↓reduceIte]; omega

/-- The ordinary distance-at-most-`k` power of `spiderTree m ell`. -/
def power (m k : ℕ) (ell : Fin m → ℕ) : SimpleGraph (Vertex m ell) where
  Adj u v := u ≠ v ∧ distance m ell u v ≤ k
  symm := ⟨fun u v ⟨hne, hd⟩ => ⟨hne.symm, distance_symm m ell v u ▸ hd⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Real symmetric matrices on `V` whose off-diagonal nonzero pattern matches adjacency in `G`. -/
def SymGraphMatrices {V : Type} (G : SimpleGraph V) : Set (Matrix V V ℝ) :=
  {A | A.IsSymm ∧ ∀ u v : V, u ≠ v → (A u v ≠ 0 ↔ G.Adj u v)}
/-- Dimension of the right kernel of a real square matrix `A`. -/
noncomputable def matrixNullity {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker A.mulVecLin)
/-- Maximum nullity over `SymGraphMatrices G`. -/
noncomputable def maxSymNullity {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sSup (matrixNullity '' SymGraphMatrices G)
/-- Minimum rank over `SymGraphMatrices G`. -/
noncomputable def minSymRank {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf (Matrix.rank '' SymGraphMatrices G)
/-- Subspace of one-sided real sequences whose every `(k + 1)`-term sliding window sums to zero. -/
noncomputable def slidingWindowSpace (k : ℕ) : Submodule ℝ (ℕ → ℝ) where
  carrier := {x : ℕ → ℝ | ∀ s : ℕ, ∑ t ∈ Finset.range (k + 1), x (s + t) = 0}
  zero_mem' := fun _ => by simp
  add_mem' := fun {x y} hx hy s => by simp [Finset.sum_add_distrib, hx s, hy s]
  smul_mem' := fun _ {x} hx s => by simp [← Finset.mul_sum, hx s]

private noncomputable def periodicExtend (k : ℕ) (v : Fin k → ℝ) (n : ℕ) : ℝ :=
  if h : n % (k + 1) < k then v ⟨n % (k + 1), h⟩ else - ∑ i : Fin k, v i
private theorem periodicExtend_lt (k : ℕ) (v : Fin k → ℝ) {n : ℕ} (hn : n < k) :
    periodicExtend k v n = v ⟨n, hn⟩ := by
  have hm : n % (k + 1) = n := Nat.mod_eq_of_lt (by omega)
  unfold periodicExtend; split_ifs with h
  · exact congrArg v (Fin.ext hm)
  · omega
private theorem periodicExtend_mem (k : ℕ) (v : Fin k → ℝ) :
    periodicExtend k v ∈ slidingWindowSpace k := by
  intro s; induction s with
  | zero =>
      rw [Finset.sum_range_succ]
      have hinit : ∑ t ∈ Finset.range k, periodicExtend k v (0 + t) = ∑ i : Fin k, v i :=
        Finset.sum_bij (fun t ht => ⟨t, Finset.mem_range.mp ht⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Fin.val h)
          (fun i _ => ⟨i.val, Finset.mem_range.mpr i.isLt, Fin.ext rfl⟩)
          (fun t ht => by simpa using periodicExtend_lt k v (Finset.mem_range.mp ht))
      have hlast : periodicExtend k v (0 + k) = - ∑ i : Fin k, v i := by
        have hm : (0 + k) % (k + 1) = k := by simp [Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
        unfold periodicExtend; split_ifs <;> first | omega | rfl
      rw [hinit, hlast, add_neg_cancel]
  | succ s ih =>
      have h1 : ∑ t ∈ Finset.range (k + 1), periodicExtend k v (s + t) =
          periodicExtend k v s + ∑ t ∈ Finset.range k, periodicExtend k v (s + 1 + t) := by
        rw [Finset.sum_range_succ', add_comm]; simp [Nat.add_assoc, Nat.add_comm 1]
      have h2 : ∑ t ∈ Finset.range (k + 1), periodicExtend k v (s + 1 + t) =
          (∑ t ∈ Finset.range k, periodicExtend k v (s + 1 + t)) +
            periodicExtend k v (s + (k + 1)) := by
        rw [Finset.sum_range_succ]; congr 1; ring_nf
      have hp : periodicExtend k v (s + (k + 1)) = periodicExtend k v s := by
        simp only [periodicExtend, Nat.add_mod_right]
      rw [hp] at h2; linarith
private theorem mem_slidingWindowSpace_iff_rec (k : ℕ) (x : ℕ → ℝ) :
    x ∈ slidingWindowSpace k ↔ ∀ s : ℕ, x (s + k) = - ∑ t ∈ Finset.range k, x (s + t) := by
  change (∀ s : ℕ, ∑ t ∈ Finset.range (k + 1), x (s + t) = 0) ↔ _
  refine ⟨fun h s => ?_, fun h s => by rw [Finset.sum_range_succ, h s, add_neg_cancel]⟩
  have hs := h s; rw [Finset.sum_range_succ] at hs; linarith
private theorem eq_of_mem_slidingWindowSpace {k : ℕ} {x y : ℕ → ℝ}
    (hx : x ∈ slidingWindowSpace k) (hy : y ∈ slidingWindowSpace k)
    (hinit : ∀ i : Fin k, x i.val = y i.val) : x = y := by
  funext n; induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnk : n < k
      · exact hinit ⟨n, hnk⟩
      · have hsub : n - k + k = n := Nat.sub_add_cancel (Nat.le_of_not_lt hnk)
        rw [← hsub, (mem_slidingWindowSpace_iff_rec k x).mp hx (n - k),
          (mem_slidingWindowSpace_iff_rec k y).mp hy (n - k)]
        congr 1; refine Finset.sum_congr rfl fun t ht => ?_
        have := Finset.mem_range.mp ht; exact ih ((n - k) + t) (by omega)

/-- Initial-coordinate linear equivalence on `slidingWindowSpace k` with periodic inverse. -/
noncomputable def slidingWindowEquiv (k : ℕ) : slidingWindowSpace k ≃ₗ[ℝ] (Fin k → ℝ) where
  toFun x i := x.1 i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨periodicExtend k v, periodicExtend_mem k v⟩
  left_inv x := Subtype.ext <|
    eq_of_mem_slidingWindowSpace (periodicExtend_mem k _) x.2 fun i => periodicExtend_lt k _ i.isLt
  right_inv v := funext fun i => periodicExtend_lt k v i.isLt
private instance (k : ℕ) : FiniteDimensional ℝ (slidingWindowSpace k) :=
  Module.Finite.equiv (slidingWindowEquiv k).symm
/-- The `(L - k) × L` sliding-window indicator matrix `D_L` of width `k + 1`. -/
noncomputable def windowMatrix (k L : ℕ) : Matrix (Fin (L - k)) (Fin L) ℝ :=
  fun s d => if s.val ≤ d.val ∧ d.val ≤ s.val + k then 1 else 0
/-- Initial black set consisting of the last `k` vertices on each of the first `m - 1` legs. -/
def spiderTailForcingSet (m k : ℕ) (ell : Fin m → ℕ) : Finset (Vertex m ell) :=
  (((Finset.univ.filter fun i : Fin m => i.val < m - 1).sigma fun i =>
      Finset.univ.filter fun d : Fin (ell i) => ell i - k ≤ d.val).map
    ⟨Option.some, Option.some_injective _⟩)
/-- Center-to-leg coupling entry `b_d` for 0-based depth `d` (1-based depth `d + 1 ≤ k`). -/
noncomputable def centerCoupling (k d : ℕ) : ℝ := if d + 1 ≤ k then 1 else 0
/-- Cross-leg coupling entry `C_{d,e}` for 0-based depths `d, e` (1-based depths `d + 1, e + 1`). -/
noncomputable def crossCoupling (k d e : ℕ) : ℝ :=
  if d + 1 ≤ k - 1 ∧ e + 1 ≤ k - 1 ∧ (d + 1) + (e + 1) ≤ k then 1 else 0
private theorem crossCoupling_eq (k d e : ℕ) :
    crossCoupling k d e = if d + e + 2 ≤ k then 1 else 0 := by
  unfold crossCoupling; split_ifs <;> first | rfl | omega
/-- Explicit real symmetric matrix in `SymGraphMatrices (power m k ell)` of nullity `(m - 1) * k`. -/
noncomputable def spiderSymmMatrix (m k : ℕ) (ell : Fin m → ℕ) :
    Matrix (Vertex m ell) (Vertex m ell) ℝ
  | none, none => 0
  | none, some p => centerCoupling k p.2.val
  | some p, none => centerCoupling k p.2.val
  | some p, some q =>
      (if h : p.1 = q.1 then ((windowMatrix k (ell p.1))ᵀ * windowMatrix k (ell p.1)) p.2
          (Fin.cast (congrArg ell h.symm) q.2) else 0) + crossCoupling k p.2.val q.2.val
private theorem windowMatrix_mulVec_zero {k L : ℕ} (hL : k + 1 ≤ L)
    {x : ℕ → ℝ} (hx : x ∈ slidingWindowSpace k) :
    windowMatrix k L *ᵥ (fun d : Fin L => x d.val) = 0 := by
  funext s
  simp only [mulVec, dotProduct, windowMatrix, Pi.zero_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hsum : ∑ t ∈ Finset.range (k + 1), x (s.val + t) =
      ∑ d ∈ Finset.univ.filter (fun d : Fin L => s.val ≤ d.val ∧ d.val ≤ s.val + k), x d.val := by
    refine Finset.sum_bij (fun t ht => ⟨s.val + t, by
        have := Finset.mem_range.mp ht; have := s.isLt; omega⟩) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro t ht; have := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro t₁ _ t₂ _ heq; have hval := congrArg Fin.val heq; dsimp at hval; omega
    · intro d hd; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      exact ⟨d.val - s.val, Finset.mem_range.mpr (by omega), Fin.ext (by dsimp; omega)⟩
  rw [← hsum]; exact hx s.val
private theorem windowGram_nonneg (k L : ℕ) (d e : Fin L) :
    0 ≤ ((windowMatrix k L)ᵀ * windowMatrix k L) d e := by
  rw [Matrix.mul_apply]; refine Finset.sum_nonneg fun s _ => ?_
  simp only [transpose_apply, windowMatrix]; split_ifs <;> norm_num
private theorem windowGram_pos_iff {k L : ℕ} (hL : k + 1 ≤ L) (d e : Fin L) :
    0 < ((windowMatrix k L)ᵀ * windowMatrix k L) d e ↔ Nat.dist d.val e.val ≤ k := by
  rw [Matrix.mul_apply]; refine ⟨fun hpos => ?_, fun hdist => ?_⟩
  · obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
    simp only [transpose_apply, windowMatrix] at hs; split_ifs at hs
    · unfold Nat.dist; omega
    · exact absurd (mul_zero _) hs
    · exact absurd (zero_mul _) hs
    · exact absurd (zero_mul _) hs
  · unfold Nat.dist at hdist; have hdL := d.isLt; have heL := e.isLt
    let s0 : Fin (L - k) := ⟨if d.val ≤ e.val then e.val - k else d.val - k,
      by split_ifs <;> omega⟩
    have hs0 : s0.val = if d.val ≤ e.val then e.val - k else d.val - k := rfl
    have hterm : (windowMatrix k L)ᵀ d s0 * windowMatrix k L s0 e = 1 := by
      simp only [transpose_apply, windowMatrix, hs0]
      split_ifs <;> first | exact mul_one 1 | omega
    have hle : (windowMatrix k L)ᵀ d s0 * windowMatrix k L s0 e ≤
        ∑ s : Fin (L - k), (windowMatrix k L)ᵀ d s * windowMatrix k L s e := by
      refine Finset.single_le_sum
        (f := fun s : Fin (L - k) => (windowMatrix k L)ᵀ d s * windowMatrix k L s e)
        (fun s _ => ?_) (Finset.mem_univ s0)
      simp only [transpose_apply, windowMatrix]; split_ifs <;> norm_num
    linarith

/-- Recurrence characterization, initial-coordinate linear equivalence, dimension `k`,
truncation kernel inclusion, and off-diagonal Gram band support of the sliding-window space. -/
theorem sliding_window_kernel_and_band_support (k : ℕ) :
    (∀ x : ℕ → ℝ, x ∈ slidingWindowSpace k ↔
      ∀ s : ℕ, x (s + k) = - ∑ t ∈ Finset.range k, x (s + t)) ∧
    (∀ (x : slidingWindowSpace k) (i : Fin k), slidingWindowEquiv k x i = x.1 i.val) ∧
    (∀ v : Fin k → ℝ, ∃! x : ℕ → ℝ, x ∈ slidingWindowSpace k ∧ ∀ i : Fin k, x i.val = v i) ∧
    Module.finrank ℝ (slidingWindowSpace k) = k ∧
    (∀ L : ℕ, k + 1 ≤ L → ∀ x ∈ slidingWindowSpace k,
      windowMatrix k L *ᵥ (fun d : Fin L => x d.val) = 0) ∧
    (∀ L : ℕ, k + 1 ≤ L → ∀ d e : Fin L, d ≠ e →
      (0 < ((windowMatrix k L)ᵀ * windowMatrix k L) d e ↔ Nat.dist d.val e.val ≤ k)) := by
  refine ⟨mem_slidingWindowSpace_iff_rec k, fun _ _ => rfl, ?_,
    by rw [(slidingWindowEquiv k).finrank_eq, Module.finrank_fin_fun],
    fun L hL x hx => windowMatrix_mulVec_zero hL hx,
    fun L hL d e _ => windowGram_pos_iff hL d e⟩
  intro v; refine ⟨periodicExtend k v, ⟨periodicExtend_mem k v,
    fun i => periodicExtend_lt k v i.isLt⟩, fun y ⟨hy, hyi⟩ => ?_⟩
  exact eq_of_mem_slidingWindowSpace hy (periodicExtend_mem k v) fun i =>
    (hyi i).trans (periodicExtend_lt k v i.isLt).symm

private theorem card_vertex (m : ℕ) (ell : Fin m → ℕ) :
    Fintype.card (Vertex m ell) = 1 + ∑ i : Fin m, ell i := by
  simp [Vertex, Fintype.card_option, Fintype.card_sigma, add_comm]
private theorem distance_self (m : ℕ) (ell : Fin m → ℕ) (u : Vertex m ell) :
    distance m ell u u = 0 := by cases u with | none => rfl | some _ => simp [distance]
private theorem distance_adj {m : ℕ} {ell : Fin m → ℕ} {u v : Vertex m ell}
    (h : (spiderTree m ell).Adj u v) : distance m ell u v = 1 := by
  cases u <;> cases v
  · exact h.elim
  · simp [spiderTree] at h; simp [distance, h]
  · simp [spiderTree] at h; simp [distance, h]
  · simp only [spiderTree] at h; simp [distance, h.1, h.2]
private theorem distance_triangle (m : ℕ) (ell : Fin m → ℕ) (u v w : Vertex m ell) :
    distance m ell u w ≤ distance m ell u v + distance m ell v w := by
  cases u with
  | none => cases v <;> cases w <;> simp only [distance, Nat.dist] <;> (try split_ifs) <;> omega
  | some p => cases v with
      | none => cases w <;> simp only [distance, Nat.dist] <;> (try split_ifs) <;> omega
      | some q => cases w with
          | none => simp only [distance, Nat.dist]; (try split_ifs) <;> omega
          | some r =>
              dsimp only [distance]; split_ifs
              all_goals try unfold Nat.dist
              all_goals omega
private theorem distance_le_walk_length {m : ℕ} {ell : Fin m → ℕ} {u v : Vertex m ell}
    (w : (spiderTree m ell).Walk u v) : distance m ell u v ≤ w.length := by
  induction w with
  | nil => simp [distance_self]
  | @cons a b c hab _ _ =>
      have h1 := distance_triangle m ell a b c; rw [distance_adj hab] at h1
      simp only [SimpleGraph.Walk.length_cons]; omega
private def walkFromCenter (m : ℕ) (ell : Fin m → ℕ) (i : Fin m) :
    ∀ (a : ℕ) (ha : a < ell i),
      {w : (spiderTree m ell).Walk none (some ⟨i, ⟨a, ha⟩⟩) // w.length = a + 1}
  | 0, _ => ⟨SimpleGraph.Walk.cons (by simp [spiderTree]) SimpleGraph.Walk.nil, rfl⟩
  | a + 1, ha =>
      let prev := walkFromCenter m ell i a (Nat.lt_of_succ_lt ha)
      have hadj : (spiderTree m ell).Adj (some ⟨i, ⟨a, Nat.lt_of_succ_lt ha⟩⟩)
          (some ⟨i, ⟨a + 1, ha⟩⟩) := ⟨rfl, by dsimp; unfold Nat.dist; omega⟩
      ⟨prev.1.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), by simp [prev.2]⟩
private theorem exists_walk_same_leg_le (m : ℕ) (ell : Fin m → ℕ) (i : Fin m) :
    ∀ (t a : ℕ) (ha : a < ell i) (hat : a + t < ell i),
      ∃ w : (spiderTree m ell).Walk (some ⟨i, ⟨a, ha⟩⟩) (some ⟨i, ⟨a + t, hat⟩⟩), w.length = t
  | 0, _, _, _ => ⟨SimpleGraph.Walk.nil, rfl⟩
  | t + 1, a, ha, hat => by
      have hat0 : a + t < ell i := Nat.lt_of_succ_lt hat
      obtain ⟨w, hw⟩ := exists_walk_same_leg_le m ell i t a ha hat0
      have hadj : (spiderTree m ell).Adj (some ⟨i, ⟨a + t, hat0⟩⟩)
          (some ⟨i, ⟨a + (t + 1), hat⟩⟩) := ⟨rfl, by dsimp; unfold Nat.dist; omega⟩
      exact ⟨w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), by simp [hw]⟩
private theorem exists_walk_eq_distance (m : ℕ) (ell : Fin m → ℕ) (u v : Vertex m ell) :
    ∃ w : (spiderTree m ell).Walk u v, w.length = distance m ell u v := by
  cases u with
  | none => cases v with
      | none => exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | some q => obtain ⟨w, hw⟩ := walkFromCenter m ell q.1 q.2.val q.2.isLt; exact ⟨w, hw⟩
  | some p =>
      rcases p with ⟨i, ⟨dv, hdv⟩⟩; cases v with
      | none =>
          obtain ⟨w, hw⟩ := walkFromCenter m ell i dv hdv; exact ⟨w.reverse, by simp [hw, distance]⟩
      | some q =>
          rcases q with ⟨j, ⟨ev, hev⟩⟩; by_cases hij : i = j
          · subst hij; by_cases hle : dv ≤ ev
            · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
              obtain ⟨w, hw⟩ := exists_walk_same_leg_le m ell i t dv hdv hev
              exact ⟨w, by rw [hw]; simp only [distance, ↓reduceIte, Nat.dist]; omega⟩
            · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hle)
              obtain ⟨w, hw⟩ := exists_walk_same_leg_le m ell i t ev hev hdv
              exact ⟨w.reverse, by
                rw [SimpleGraph.Walk.length_reverse, hw]
                simp only [distance, ↓reduceIte, Nat.dist]; omega⟩
          · obtain ⟨w1, hw1⟩ := walkFromCenter m ell i dv hdv
            obtain ⟨w2, hw2⟩ := walkFromCenter m ell j ev hev
            exact ⟨w1.reverse.append w2, by
              simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hw1, hw2,
                distance, hij, ↓reduceIte]; omega⟩
private theorem spiderTree_dist_eq_distance (m : ℕ) (ell : Fin m → ℕ) (u v : Vertex m ell) :
    (spiderTree m ell).dist u v = distance m ell u v := by
  obtain ⟨w, hw⟩ := exists_walk_eq_distance m ell u v
  obtain ⟨w', hw'⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist w.reachable
  exact le_antisymm (hw ▸ SimpleGraph.dist_le w) (hw' ▸ distance_le_walk_length w')

private theorem mem_spiderTailForcingSet_iff (m k : ℕ) (ell : Fin m → ℕ)
    (i : Fin m) (d : Fin (ell i)) :
    (some ⟨i, d⟩ : Vertex m ell) ∈ spiderTailForcingSet m k ell ↔
      i.val < m - 1 ∧ ell i - k ≤ d.val := by simp [spiderTailForcingSet]
private theorem spiderTailForcingSet_card {m k : ℕ} {ell : Fin m → ℕ}
    (hm : 2 ≤ m) (_hk : 1 ≤ k) (hell : ∀ i : Fin m, k + 1 ≤ ell i) :
    (spiderTailForcingSet m k ell).card = (m - 1) * k := by
  unfold spiderTailForcingSet; rw [Finset.card_map, Finset.card_sigma]
  have htail : ∀ i : Fin m,
      (Finset.univ.filter fun d : Fin (ell i) => ell i - k ≤ d.val).card = k := by
    intro i; have hi := hell i; trans (Finset.range k).card
    · symm; refine Finset.card_bij (fun t ht => ⟨ell i - k + t, by
          have := Finset.mem_range.mp ht; omega⟩) ?_ ?_ ?_
      · intro t ht; have := Finset.mem_range.mp ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · intro t₁ _ t₂ _ heq; have hval := congrArg Fin.val heq; dsimp at hval; omega
      · intro d hd; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact ⟨d.val - (ell i - k), Finset.mem_range.mpr (by omega), Fin.ext (by dsimp; omega)⟩
    · exact Finset.card_range k
  simp_rw [htail, Finset.sum_const, smul_eq_mul]; congr 1; trans (Finset.range (m - 1)).card
  · symm; refine Finset.card_bij (fun j hj => ⟨j, by have := Finset.mem_range.mp hj; omega⟩)
      (fun j hj => by simpa using Finset.mem_range.mp hj)
      (fun _ _ _ _ heq => congrArg Fin.val heq) ?_
    intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨i.val, Finset.mem_range.mpr hi, Fin.ext rfl⟩
  · exact Finset.card_range (m - 1)
private theorem spiderTailForcingSet_isZeroForcing {m k : ℕ} {ell : Fin m → ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hell : ∀ i : Fin m, k + 1 ≤ ell i) :
    IsZeroForcing (power m k ell) (spiderTailForcingSet m k ell : Set (Vertex m ell)) := by
  let S : Set (Vertex m ell) := (spiderTailForcingSet m k ell : Set (Vertex m ell))
  have hphase1 : ∀ (i : Fin m), i.val < m - 1 → ∀ (r : ℕ) (d : Fin (ell i)),
      ell i - k - r ≤ d.val → Black (power m k ell) S (some ⟨i, d⟩) := by
    intro i hi r; induction r with
    | zero =>
        intro d hd; exact Black.init
          (Finset.mem_coe.mpr ((mem_spiderTailForcingSet_iff m k ell i d).mpr ⟨hi, by omega⟩))
    | succ r ih =>
        intro d hd; by_cases hdr : ell i - k - r ≤ d.val
        · exact ih d hdr
        · have hlt : d.val + k < ell i := by have := hell i; omega
          let u : Vertex m ell := some ⟨i, ⟨d.val + k, hlt⟩⟩
          have hadj : (power m k ell).Adj u (some ⟨i, d⟩) := by
            refine ⟨fun heq => ?_, by simp only [u, distance, ↓reduceIte, Nat.dist]; omega⟩
            have hv := congrArg (fun p : Σ j : Fin m, Fin (ell j) => p.2.val) (Option.some.inj heq)
            dsimp at hv; omega
          refine Black.force (ih ⟨d.val + k, hlt⟩ (by dsimp; omega)) hadj fun x hux hxw => ?_
          rcases hux with ⟨_, hdist⟩; cases x with
          | none => simp only [distance] at hdist; omega
          | some q =>
              rcases q with ⟨j, e⟩; simp only [distance] at hdist; by_cases hij : i = j
              · subst hij; simp only [↓reduceIte, Nat.dist] at hdist
                have hne : e.val ≠ d.val := fun hv => hxw (by congr 2; exact Fin.ext hv)
                exact ih e (by omega)
              · simp only [hij, ↓reduceIte] at hdist; omega
  have hfirst : ∀ (i : Fin m), i.val < m - 1 → ∀ d : Fin (ell i),
      Black (power m k ell) S (some ⟨i, d⟩) := fun i hi d => hphase1 i hi (ell i - k) d (by omega)
  let i0 : Fin m := ⟨0, by omega⟩
  have hi0 : i0.val < m - 1 := by dsimp [i0]; omega
  have hcenter : Black (power m k ell) S none := by
    let d0 : Fin (ell i0) := ⟨k - 1, by have := hell i0; omega⟩
    have hadj0 : (power m k ell).Adj (some ⟨i0, d0⟩) none := ⟨by simp, by simp [d0, distance]; omega⟩
    refine Black.force (hfirst i0 hi0 d0) hadj0 fun x hux hxn => ?_
    cases x with
    | none => exact (hxn rfl).elim
    | some q =>
        rcases q with ⟨j, e⟩; rcases hux with ⟨_, hdist⟩; simp only [distance] at hdist
        by_cases hij : i0 = j
        · subst hij; exact hfirst i0 hi0 e
        · simp only [hij, ↓reduceIte] at hdist
          change (k - 1) + e.val + 2 ≤ k at hdist; omega
  let ilast : Fin m := ⟨m - 1, by omega⟩
  have hphase3 : ∀ (t : ℕ), t < k → ∀ d : Fin (ell ilast), d.val < t →
      Black (power m k ell) S (some ⟨ilast, d⟩) := by
    intro t; induction t with
    | zero => intro _ _ hd; omega
    | succ t ih =>
        intro htk d hdt; by_cases hlt : d.val < t
        · exact ih (Nat.lt_of_succ_lt htk) d hlt
        · have hdeq : d.val = t := by omega
          let u : Vertex m ell := some ⟨i0, ⟨k - t - 2, by have := hell i0; omega⟩⟩
          have hi0_ne : i0 ≠ ilast := fun h => by
            have hv := congrArg Fin.val h; dsimp [i0, ilast] at hv; omega
          have hadj : (power m k ell).Adj u (some ⟨ilast, d⟩) :=
            ⟨fun h => hi0_ne (congrArg Sigma.fst (Option.some.inj h)),
              by simp only [u, distance, hi0_ne, ↓reduceIte, hdeq]; omega⟩
          refine Black.force (hfirst i0 hi0 _) hadj fun x hux hxw => ?_
          cases x with
          | none => exact hcenter
          | some q =>
              rcases q with ⟨j, e⟩; by_cases hj : j.val < m - 1
              · exact hfirst j hj e
              · obtain rfl : j = ilast := Fin.ext (by dsimp [ilast]; omega)
                rcases hux with ⟨_, hdist⟩; simp only [distance, hi0_ne, ↓reduceIte] at hdist
                have hne : e.val ≠ t := fun hev =>
                  hxw (by congr 2; exact Fin.ext (hev.trans hdeq.symm))
                exact ih (Nat.lt_of_succ_lt htk) e (by omega)
  have hlast_km1 : Black (power m k ell) S
      (some ⟨ilast, ⟨k - 1, by have := hell ilast; omega⟩⟩) := by
    refine Black.force hcenter ⟨by simp, by simp [distance]; omega⟩ fun x hux hxw => ?_
    cases x with
    | none => exact (hux.1 rfl).elim
    | some q =>
        rcases q with ⟨j, e⟩; by_cases hj : j.val < m - 1
        · exact hfirst j hj e
        · obtain rfl : j = ilast := Fin.ext (by dsimp [ilast]; omega)
          rcases hux with ⟨_, hdist⟩; simp only [distance] at hdist
          have hne : e.val ≠ k - 1 := fun hev => hxw (by congr 2; exact Fin.ext hev)
          exact hphase3 (k - 1) (by omega) e (by omega)
  have hlast_lt_k : ∀ d : Fin (ell ilast), d.val < k →
      Black (power m k ell) S (some ⟨ilast, d⟩) := fun d hd => by
    by_cases hlt : d.val < k - 1
    · exact hphase3 (k - 1) (by omega) d hlt
    · exact (show d = ⟨k - 1, by have := hell ilast; omega⟩ from Fin.ext (by dsimp; omega)) ▸
        hlast_km1
  have hphase4 : ∀ (t : ℕ), t ≤ ell ilast → ∀ d : Fin (ell ilast), d.val < t →
      Black (power m k ell) S (some ⟨ilast, d⟩) := by
    intro t; induction t with
    | zero => intro _ _ hd; omega
    | succ t ih =>
        intro ht d hdt; by_cases hlt : d.val < t
        · exact ih (Nat.le_of_succ_le ht) d hlt
        · have hdeq : d.val = t := by omega
          by_cases htk : t < k
          · exact hlast_lt_k d (hdeq ▸ htk)
          · let u : Vertex m ell := some ⟨ilast, ⟨t - k, by omega⟩⟩
            have hadj : (power m k ell).Adj u (some ⟨ilast, d⟩) := by
              refine ⟨fun heq => ?_, by simp only [u, distance, ↓reduceIte, Nat.dist, hdeq]; omega⟩
              have hv := congrArg (fun p : Σ j : Fin m, Fin (ell j) => p.2.val)
                (Option.some.inj heq)
              dsimp at hv; omega
            refine Black.force (ih (Nat.le_of_succ_le ht) _ (by dsimp; omega)) hadj
              fun x hux hxw => ?_
            cases x with
            | none => exact hcenter
            | some q =>
                rcases q with ⟨j, e⟩; by_cases hj : j.val < m - 1
                · exact hfirst j hj e
                · obtain rfl : j = ilast := Fin.ext (by dsimp [ilast]; omega)
                  rcases hux with ⟨_, hdist⟩; simp only [distance, ↓reduceIte, Nat.dist] at hdist
                  have hne : e.val ≠ t := fun hev =>
                    hxw (by congr 2; exact Fin.ext (hev.trans hdeq.symm))
                  exact ih (Nat.le_of_succ_le ht) e (by omega)
  intro v; cases v with
  | none => exact hcenter
  | some p =>
      rcases p with ⟨i, d⟩; by_cases hi : i.val < m - 1
      · exact hfirst i hi d
      · obtain rfl : i = ilast := Fin.ext (by dsimp [ilast]; omega)
        exact hphase4 (ell ilast) le_rfl d d.isLt

@[simp] private theorem spiderSymmMatrix_some_same (m k : ℕ) (ell : Fin m → ℕ)
    (i : Fin m) (d e : Fin (ell i)) :
    spiderSymmMatrix m k ell (some ⟨i, d⟩) (some ⟨i, e⟩) =
      ((windowMatrix k (ell i))ᵀ * windowMatrix k (ell i)) d e + crossCoupling k d.val e.val := by
  simp [spiderSymmMatrix]
@[simp] private theorem spiderSymmMatrix_some_ne (m k : ℕ) (ell : Fin m → ℕ)
    {i j : Fin m} (hij : i ≠ j) (d : Fin (ell i)) (e : Fin (ell j)) :
    spiderSymmMatrix m k ell (some ⟨i, d⟩) (some ⟨j, e⟩) = crossCoupling k d.val e.val := by
  simp [spiderSymmMatrix, hij]
private theorem spiderSymmMatrix_mem_symGraphMatrices {m k : ℕ} {ell : Fin m → ℕ}
    (hell : ∀ i : Fin m, k + 1 ≤ ell i) :
    spiderSymmMatrix m k ell ∈ SymGraphMatrices (power m k ell) := by
  refine ⟨Matrix.IsSymm.ext fun u v => ?_, fun u v hne => ?_⟩
  · cases u with
    | none => cases v <;> rfl
    | some p =>
        rcases p with ⟨i, d⟩; cases v with
        | none => rfl
        | some q =>
            rcases q with ⟨j, e⟩; by_cases hij : i = j
            · subst hij; simp only [spiderSymmMatrix_some_same, crossCoupling_eq]; congr 1
              · simp only [Matrix.mul_apply, transpose_apply]
                exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
              · congr 1; exact propext ⟨fun h => by omega, fun h => by omega⟩
            · simp only [spiderSymmMatrix_some_ne m k ell hij,
                spiderSymmMatrix_some_ne m k ell (Ne.symm hij), crossCoupling_eq]
              congr 1; exact propext ⟨fun h => by omega, fun h => by omega⟩
  · have hp : (power m k ell).Adj u v ↔ distance m ell u v ≤ k := ⟨And.right, And.intro hne⟩
    rw [hp]; cases u with
    | none => cases v with
        | none => exact (hne rfl).elim
        | some _ => simp [spiderSymmMatrix, centerCoupling, distance]
    | some p =>
        rcases p with ⟨i, d⟩; cases v with
        | none => simp [spiderSymmMatrix, centerCoupling, distance]
        | some q =>
            rcases q with ⟨j, e⟩; by_cases hij : i = j
            · subst hij; simp only [spiderSymmMatrix_some_same, distance, ↓reduceIte]
              have hgnn := windowGram_nonneg k (ell i) d e
              have hcnn : 0 ≤ crossCoupling k d.val e.val := by
                rw [crossCoupling_eq]; split_ifs <;> norm_num
              refine ⟨fun hnz => ?_, fun hle => ?_⟩
              · by_contra hgt
                have hng : ¬ 0 < ((windowMatrix k (ell i))ᵀ * windowMatrix k (ell i)) d e :=
                  fun hp => hgt ((windowGram_pos_iff (hell i) d e).mp hp)
                have hg0 : ((windowMatrix k (ell i))ᵀ * windowMatrix k (ell i)) d e = 0 :=
                  le_antisymm (not_lt.mp hng) hgnn
                have hc0 : crossCoupling k d.val e.val = 0 := by
                  rw [crossCoupling_eq]; split_ifs <;> first | rfl | (unfold Nat.dist at hgt; omega)
                exact hnz (by linarith)
              · have hp := (windowGram_pos_iff (hell i) d e).mpr hle; linarith
            · simp [spiderSymmMatrix_some_ne m k ell hij, crossCoupling_eq, distance, hij]
private theorem sum_fin_eq_sum_range_of_support (k L : ℕ) (hkL : k ≤ L) (f : ℕ → ℝ)
    (hzero : ∀ n : ℕ, k ≤ n → f n = 0) :
    (∑ e : Fin L, f e.val) = ∑ n ∈ Finset.range k, f n := by
  rw [Fin.sum_univ_eq_sum_range f L]; symm
  refine Finset.sum_subset (Finset.range_mono hkL) fun n _ hnk => ?_
  exact hzero n (Nat.le_of_not_lt fun hlt => hnk (Finset.mem_range.mpr hlt))
private noncomputable def legCoord (m k : ℕ) (v : (Fin (m - 1) × Fin k) → ℝ)
    (j : Fin (m - 1)) : slidingWindowSpace k :=
  (slidingWindowEquiv k).symm (fun r : Fin k => v (j, r))
private noncomputable def legSeq (m k : ℕ) (v : (Fin (m - 1) × Fin k) → ℝ)
    (i : Fin m) : slidingWindowSpace k :=
  if h : i.val < m - 1 then legCoord m k v ⟨i.val, h⟩ else - ∑ j : Fin (m - 1), legCoord m k v j
private theorem legSeq_add (m k : ℕ) (v₁ v₂ : (Fin (m - 1) × Fin k) → ℝ) (i : Fin m) :
    legSeq m k (v₁ + v₂) i = legSeq m k v₁ i + legSeq m k v₂ i := by
  have hca : ∀ j, legCoord m k (v₁ + v₂) j = legCoord m k v₁ j + legCoord m k v₂ j :=
    fun j => (slidingWindowEquiv k).symm.map_add (fun r => v₁ (j, r)) (fun r => v₂ (j, r))
  unfold legSeq; split_ifs with hi
  · exact hca ⟨i.val, hi⟩
  · simp [hca, Finset.sum_add_distrib, neg_add_rev, add_comm]
private theorem legSeq_smul (m k : ℕ) (c : ℝ) (v : (Fin (m - 1) × Fin k) → ℝ) (i : Fin m) :
    legSeq m k (c • v) i = c • legSeq m k v i := by
  have hcs : ∀ j, legCoord m k (c • v) j = c • legCoord m k v j :=
    fun j => (slidingWindowEquiv k).symm.map_smul c (fun r => v (j, r))
  unfold legSeq; split_ifs with hi
  · exact hcs ⟨i.val, hi⟩
  · simp [hcs, ← Finset.smul_sum]
private theorem sum_legSeq_zero {m k : ℕ} (hm : 2 ≤ m)
    (v : (Fin (m - 1) × Fin k) → ℝ) (n : ℕ) :
    (∑ i : Fin m, (legSeq m k v i).1 n) = 0 := by
  let ilast : Fin m := ⟨m - 1, by omega⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ilast)]
  have hlast_sub : legSeq m k v ilast = - ∑ j : Fin (m - 1), legCoord m k v j := by
    unfold legSeq; split_ifs with h <;> first | rfl | (dsimp [ilast] at h; omega)
  have hlast : (legSeq m k v ilast).1 n = - ∑ j : Fin (m - 1), (legCoord m k v j).1 n := by
    rw [hlast_sub, Submodule.coe_neg, Pi.neg_apply]; congr 1
    change (↑(∑ j : Fin (m - 1), legCoord m k v j) : ℕ → ℝ) n = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  have hrest : (∑ i ∈ Finset.univ.erase ilast, (legSeq m k v i).1 n) =
      ∑ j : Fin (m - 1), (legCoord m k v j).1 n := by
    symm; refine Finset.sum_bij (fun j _ => ⟨j.val, by have := j.isLt; omega⟩) ?_ ?_ ?_ ?_
    · intro j _; simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq; have hv := congrArg Fin.val heq; dsimp [ilast] at hv; have := j.isLt; omega
    · intro j₁ _ j₂ _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
    · intro i hi; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
      have hilt : i.val < m - 1 := by
        have := i.isLt; by_contra hge; exact hi (Fin.ext (by dsimp [ilast]; omega))
      exact ⟨⟨i.val, hilt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro j _; have hj : legSeq m k v ⟨j.val, by have := j.isLt; omega⟩ = legCoord m k v j := by
        unfold legSeq; split_ifs with h <;> first | rfl | exact absurd j.isLt h
      rw [hj]
  rw [hlast, hrest, neg_add_cancel]
private noncomputable def spiderKernelVec (m k : ℕ) (ell : Fin m → ℕ)
    (v : (Fin (m - 1) × Fin k) → ℝ) : Vertex m ell → ℝ
  | none => 0
  | some p => (legSeq m k v p.1).1 p.2.val
private theorem spiderSymmMatrix_mulVec_spiderKernelVec {m k : ℕ} {ell : Fin m → ℕ}
    (hm : 2 ≤ m) (hell : ∀ i : Fin m, k + 1 ≤ ell i) (v : (Fin (m - 1) × Fin k) → ℝ) :
    spiderSymmMatrix m k ell *ᵥ spiderKernelVec m k ell v = 0 := by
  funext u
  simp only [mulVec, dotProduct, Pi.zero_apply, Vertex, Fintype.sum_option, Fintype.sum_sigma,
    spiderKernelVec, mul_zero, zero_add]
  cases u with
  | none =>
      have hleg : ∀ j : Fin m,
          (∑ e : Fin (ell j), centerCoupling k e.val * (legSeq m k v j).1 e.val) =
            ∑ n ∈ Finset.range k, centerCoupling k n * (legSeq m k v j).1 n := fun j =>
        sum_fin_eq_sum_range_of_support k (ell j) (by have := hell j; omega)
          (fun n : ℕ => centerCoupling k n * (legSeq m k v j).1 n) fun n hn => by
            unfold centerCoupling; split_ifs <;> first | omega | ring
      simp only [spiderSymmMatrix, hleg]; rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [← Finset.mul_sum, sum_legSeq_zero hm v n, mul_zero]
  | some p =>
      rcases p with ⟨i, d⟩; simp only [spiderSymmMatrix, add_mul, Finset.sum_add_distrib]
      have hgram : (∑ j : Fin m, ∑ e : Fin (ell j),
          (if h : i = j then ((windowMatrix k (ell i))ᵀ * windowMatrix k (ell i)) d
              (Fin.cast (congrArg ell h.symm) e) else 0) * (legSeq m k v j).1 e.val) = 0 := by
        rw [Fintype.sum_eq_single i (fun j hji => by simp [Ne.symm hji])]
        simp only [↓reduceDIte, Fin.cast_refl]
        change (((windowMatrix k (ell i))ᵀ * windowMatrix k (ell i)) *ᵥ
          (fun e : Fin (ell i) => (legSeq m k v i).1 e.val)) d = 0
        rw [← Matrix.mulVec_mulVec,
          windowMatrix_mulVec_zero (hell i) (legSeq m k v i).2, mulVec_zero, Pi.zero_apply]
      rw [hgram, zero_add]
      have hleg : ∀ j : Fin m,
          (∑ e : Fin (ell j), crossCoupling k d.val e.val * (legSeq m k v j).1 e.val) =
            ∑ n ∈ Finset.range k, crossCoupling k d.val n * (legSeq m k v j).1 n := fun j =>
        sum_fin_eq_sum_range_of_support k (ell j) (by have := hell j; omega)
          (fun n : ℕ => crossCoupling k d.val n * (legSeq m k v j).1 n) fun n hn => by
            rw [crossCoupling_eq]; split_ifs <;> first | omega | ring
      simp_rw [hleg]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun n _ => ?_
      rw [← Finset.mul_sum, sum_legSeq_zero hm v n, mul_zero]
private theorem nullity_ge_spiderSymmMatrix {m k : ℕ} {ell : Fin m → ℕ}
    (hm : 2 ≤ m) (hell : ∀ i : Fin m, k + 1 ≤ ell i) :
    (m - 1) * k ≤ matrixNullity (spiderSymmMatrix m k ell) := by
  let embVec : ((Fin (m - 1) × Fin k) → ℝ) →ₗ[ℝ] (Vertex m ell → ℝ) :=
    { toFun := spiderKernelVec m k ell
      map_add' := fun _ _ => by funext u; cases u with
        | none => simp [spiderKernelVec]
        | some _ => simp only [spiderKernelVec, Pi.add_apply]; rw [legSeq_add]; rfl
      map_smul' := fun _ _ => by funext u; cases u with
        | none => simp [spiderKernelVec]
        | some _ => simp only [spiderKernelVec, Pi.smul_apply, RingHom.id_apply]; rw [legSeq_smul]; rfl }
  let emb := LinearMap.codRestrict (LinearMap.ker (spiderSymmMatrix m k ell).mulVecLin) embVec
    fun v => by rw [LinearMap.mem_ker, mulVecLin_apply]; exact spiderSymmMatrix_mulVec_spiderKernelVec hm hell v
  have hinj : Function.Injective emb := by
    rw [injective_iff_map_eq_zero]; intro v hv; funext ⟨j, r⟩; simp only [Pi.zero_apply]
    let i : Fin m := ⟨j.val, by have := j.isLt; omega⟩
    have hval : (emb v).1 (some ⟨i, ⟨r.val, by have := hell i; have := r.isLt; omega⟩⟩) = 0 := by
      rw [hv]; rfl
    change (legSeq m k v i).1 r.val = 0 at hval
    have hls : legSeq m k v i = legCoord m k v j := by
      unfold legSeq; split_ifs with h <;> first | rfl | exact absurd j.isLt h
    rw [hls] at hval
    have heval : slidingWindowEquiv k (legCoord m k v j) r = v (j, r) :=
      congrFun ((slidingWindowEquiv k).apply_symm_apply _) r
    exact heval.symm.trans hval
  simpa [matrixNullity, Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
    LinearMap.finrank_le_finrank_of_injective hinj
private theorem ker_zero_on_black {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {H : Matrix V V ℝ}
    (hH : H ∈ SymGraphMatrices G) {y : V → ℝ}
    (hy : H *ᵥ y = 0) (hyS : ∀ s ∈ S, y s = 0) :
    ∀ {v : V}, Black G (S : Set V) v → y v = 0 := by
  intro v hb; induction hb with
  | init hv => exact hyS _ (Finset.mem_coe.mp hv)
  | @force u w _ huw _ ihu ihall =>
      have hrow : (H *ᵥ y) u = 0 := congrFun hy u; simp only [mulVec, dotProduct] at hrow
      have hsingle : (∑ x : V, H u x * y x) = H u w * y w := by
        refine Fintype.sum_eq_single w fun x hxw => ?_
        by_cases hxu : x = u
        · subst hxu; rw [ihu, mul_zero]
        · by_cases hux : G.Adj u x
          · rw [ihall x hux hxw, mul_zero]
          · rw [show H u x = 0 by by_contra hnz; exact hux ((hH.2 u x (Ne.symm hxu)).mp hnz), zero_mul]
      rw [hsingle] at hrow
      exact (mul_eq_zero.mp hrow).resolve_left ((hH.2 u w (G.ne_of_adj huw)).mpr huw)
private theorem nullity_le_card_of_isZeroForcing {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} (hS : IsZeroForcing G (S : Set V))
    {H : Matrix V V ℝ} (hH : H ∈ SymGraphMatrices G) : matrixNullity H ≤ S.card := by
  let res : LinearMap.ker H.mulVecLin →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y s => y.1 s.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]; intro y hy; apply Subtype.ext; funext v
    exact ker_zero_on_black hH (LinearMap.mem_ker.mp y.2) (fun s hs => congrFun hy ⟨s, hs⟩) (hS v)
  simpa [matrixNullity, Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective hinj
private theorem rank_add_nullity_eq_card {V : Type} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℝ) : H.rank + matrixNullity H = Fintype.card V := by
  simpa [Matrix.rank, matrixNullity, Module.finrank_fintype_fun_eq_card] using
    H.mulVecLin.finrank_range_add_finrank_ker

/-- Ordinary zero forcing number, symmetric maximum nullity, minimum symmetric rank, and explicit
extremal forcing-set and symmetric-matrix realizations for unequal-leg spider powers. -/
theorem unequal_spider_power_zero_forcing (m k : ℕ) (ell : Fin m → ℕ)
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hell : ∀ i : Fin m, k + 1 ≤ ell i) :
    Fintype.card (Vertex m ell) = 1 + ∑ i : Fin m, ell i ∧
    (∀ u v : Vertex m ell, (spiderTree m ell).dist u v = distance m ell u v) ∧
    (∀ u v : Vertex m ell,
      (power m k ell).Adj u v ↔ u ≠ v ∧ (spiderTree m ell).dist u v ≤ k) ∧
    IsZeroForcing (power m k ell) (spiderTailForcingSet m k ell : Set (Vertex m ell)) ∧
    (spiderTailForcingSet m k ell).card = (m - 1) * k ∧
    spiderSymmMatrix m k ell ∈ SymGraphMatrices (power m k ell) ∧
    matrixNullity (spiderSymmMatrix m k ell) = (m - 1) * k ∧
    (spiderSymmMatrix m k ell).rank = (1 + ∑ i : Fin m, ell i) - (m - 1) * k ∧
    (∀ H ∈ SymGraphMatrices (power m k ell),
      matrixNullity H ≤ (m - 1) * k ∧
      (1 + ∑ i : Fin m, ell i) - (m - 1) * k ≤ H.rank) ∧
    IsGreatest (matrixNullity '' SymGraphMatrices (power m k ell)) ((m - 1) * k) ∧
    IsLeast (Matrix.rank '' SymGraphMatrices (power m k ell))
      ((1 + ∑ i : Fin m, ell i) - (m - 1) * k) ∧
    zeroForcingNumber (power m k ell) = (m - 1) * k ∧
    maxSymNullity (power m k ell) = (m - 1) * k ∧
    minSymRank (power m k ell) = (1 + ∑ i : Fin m, ell i) - (m - 1) * k := by
  have hcard := card_vertex m ell
  have hdist := spiderTree_dist_eq_distance m ell
  have hadj : ∀ u v : Vertex m ell,
      (power m k ell).Adj u v ↔ u ≠ v ∧ (spiderTree m ell).dist u v ≤ k := by
    intro u v; rw [hdist u v]; rfl
  have hzf := spiderTailForcingSet_isZeroForcing hm hk hell
  have hScard := spiderTailForcingSet_card hm hk hell
  have hAmem := spiderSymmMatrix_mem_symGraphMatrices (m := m) (k := k) hell
  have hAnull : matrixNullity (spiderSymmMatrix m k ell) = (m - 1) * k :=
    le_antisymm (hScard ▸ nullity_le_card_of_isZeroForcing hzf hAmem)
      (nullity_ge_spiderSymmMatrix hm hell)
  have hArank_sum := rank_add_nullity_eq_card (spiderSymmMatrix m k ell)
  have hArank : (spiderSymmMatrix m k ell).rank = (1 + ∑ i : Fin m, ell i) - (m - 1) * k := by
    rw [hcard, hAnull] at hArank_sum; omega
  have hall : ∀ H ∈ SymGraphMatrices (power m k ell),
      matrixNullity H ≤ (m - 1) * k ∧ (1 + ∑ i : Fin m, ell i) - (m - 1) * k ≤ H.rank := by
    intro H hH
    have hHnull : matrixNullity H ≤ (m - 1) * k :=
      hScard ▸ nullity_le_card_of_isZeroForcing hzf hH
    have hHsum := rank_add_nullity_eq_card H; rw [hcard] at hHsum; exact ⟨hHnull, by omega⟩
  have hgreat : IsGreatest (matrixNullity '' SymGraphMatrices (power m k ell)) ((m - 1) * k) :=
    ⟨⟨spiderSymmMatrix m k ell, hAmem, hAnull⟩, by rintro _ ⟨H, hH, rfl⟩; exact (hall H hH).1⟩
  have hleast : IsLeast (Matrix.rank '' SymGraphMatrices (power m k ell))
      ((1 + ∑ i : Fin m, ell i) - (m - 1) * k) :=
    ⟨⟨spiderSymmMatrix m k ell, hAmem, hArank⟩, by rintro _ ⟨H, hH, rfl⟩; exact (hall H hH).2⟩
  have hzfn_least : IsLeast
      {c : ℕ | ∃ S : Finset (Vertex m ell),
        S.card = c ∧ IsZeroForcing (power m k ell) (S : Set (Vertex m ell))} ((m - 1) * k) :=
    ⟨⟨spiderTailForcingSet m k ell, hScard, hzf⟩, by
      rintro c ⟨S, rfl, hSzf⟩; exact hAnull ▸ nullity_le_card_of_isZeroForcing hSzf hAmem⟩
  exact ⟨hcard, hdist, hadj, hzf, hScard, hAmem, hAnull, hArank, hall,
    hgreat, hleast, hzfn_least.csInf_eq, hgreat.csSup_eq, hleast.csInf_eq⟩

end D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
