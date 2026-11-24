/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Positive Gram kernels and polynomial restrictions to involution-fixed vectors. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-! Perron rigidity and polynomial continuation for a Gram defect commuting with an involution. -/

set_option autoImplicit false

noncomputable section

open scoped Matrix BigOperators

namespace Matrix

/-- The positive entries of `M` give the edges between its row and column types. -/
def positiveBiadjacencyGraph {ι κ : Type*} (M : Matrix ι κ ℝ) : SimpleGraph (ι ⊕ κ) where
  Adj
    | .inl i, .inr k => 0 < M i k
    | .inr k, .inl i => 0 < M i k
    | _, _ => False
  symm := ⟨by
    rintro (i | k) (j | l) h <;> exact h⟩
  loopless := ⟨by
    rintro (i | k) h <;> exact h⟩

/-- A nonnegative biadjacency matrix with connected positive-entry graph has an
irreducible row Gram matrix if every row has a positive entry. A shared column
gives a Gram edge, and each row's neighbor gives a positive diagonal loop. -/
theorem isIrreducible_mul_transpose_of_connected {ι κ : Type*} [Fintype κ]
    (M : Matrix ι κ ℝ) (hM : ∀ i k, 0 ≤ M i k)
    (hconn : (positiveBiadjacencyGraph M).Connected)
    (hneighbor : ∀ i, ∃ k, 0 < M i k) : (M * Mᵀ).IsIrreducible := by
  letI : Quiver ι := (M * Mᵀ).toQuiver
  have termNonneg (i j : ι) (k : κ) : 0 ≤ M i k * M j k :=
    mul_nonneg (hM i k) (hM j k)
  have gramPos (i j : ι) (k : κ) (hi : 0 < M i k) (hj : 0 < M j k) :
      0 < (M * Mᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun l _ => termNonneg i j l) ⟨k, Finset.mem_univ k, mul_pos hi hj⟩
  -- At a column, retain the last row and its edge until the walk returns to a row.
  have collapse (i : ι) {v : ι ⊕ κ}
      (walk : Relation.ReflTransGen (positiveBiadjacencyGraph M).Adj (Sum.inl i) v) :
      match v with
      | .inl j => Nonempty (Quiver.Path i j)
      | .inr k => ∃ j : ι, Nonempty (Quiver.Path i j) ∧ 0 < M j k := by
    induction walk with
    | refl => exact ⟨Quiver.Path.nil⟩
    | @tail v w _ hadj ih =>
      cases v with
      | inl j =>
        cases w with
        | inl l => exact False.elim (show False from hadj)
        | inr k => exact ⟨j, ih, hadj⟩
      | inr k =>
        cases w with
        | inl l =>
          obtain ⟨j, ⟨p⟩, hj⟩ := ih
          exact ⟨p.cons (PLift.up (gramPos j l k hj hadj))⟩
        | inr l => exact False.elim (show False from hadj)
  have hGramConn : Quiver.IsStronglyConnected ι := by
    intro i j
    have walk := (SimpleGraph.reachable_iff_reflTransGen
      (G := positiveBiadjacencyGraph M) (Sum.inl i) (Sum.inl j)).mp (hconn.preconnected _ _)
    exact collapse i walk
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_nonneg fun k _ => termNonneg i j k
  · intro i j
    obtain ⟨k, hik⟩ := hneighbor i
    have loop : i ⟶ i := PLift.up (gramPos i i k hik hik)
    exact (hGramConn.isSStronglyConnected_of_hom loop) i j

end Matrix

open scoped Matrix
open private positive_eigenvector_fixed_by_perm from
  D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition

namespace Matrix

/-- A symmetry of an irreducible nonnegative matrix acts trivially on the
eigenspace belonging to a positive eigenvector. Shift any real eigenvector
by a sufficiently large multiple of the positive vector. -/
theorem eigenvector_fixed_by_perm_of_pos_eigenvector {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (p : Equiv.Perm ι)
    (hp : ∀ i j, A (p i) (p j) = A i j)
    {ρ : ℝ} {u v : ι → ℝ} (hu_pos : ∀ i, 0 < u i)
    (hu : A *ᵥ u = ρ • u) (hv : A *ᵥ v = ρ • v) :
    ∀ x, v (p x) = v x := by
  classical
  intro x
  obtain ⟨m, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun j => -v j / u j) ⟨x, Finset.mem_univ x⟩
  let c := -v m / u m + 1
  let z : ι → ℝ := c • u + v
  have hzPos (j : ι) : 0 < z j := by
    have h := (div_le_iff₀ (hu_pos j)).mp (hmax j (Finset.mem_univ j))
    change 0 < c * u j + v j
    dsimp only [c]
    rw [add_mul, one_mul]
    linarith [hu_pos j]
  have hz : A *ᵥ z = ρ • z := by
    change A *ᵥ (c • u + v) = ρ • (c • u + v)
    rw [mulVec_add, mulVec_smul, hu, hv, smul_add, smul_comm c ρ]
  have hzu := positive_eigenvector_fixed_by_perm hA p hp hzPos hz x
  change c * u (p x) + v (p x) = c * u x + v x at hzu
  rw [positive_eigenvector_fixed_by_perm hA p hp hu_pos hu x] at hzu
  exact add_left_cancel hzu

end Matrix

open scoped Matrix Polynomial

namespace Matrix

/-- Replace the action on the anti-invariant subspace by twice the identity.
The resulting determinant tests exactly the kernel in the fixed sector. -/
theorem exists_fixed_mulVec_eq_zero_of_forall_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (D : Matrix ι ι ℝ[X]) (hP : P * P = 1)
    (hpos : ∀ s : ℝ, 0 < s → ∃ v ≠ 0,
      P *ᵥ v = v ∧ (Polynomial.evalRingHom s).mapMatrix D *ᵥ v = 0)
    (t : ℝ) (hcomm : P * (Polynomial.evalRingHom t).mapMatrix D =
      (Polynomial.evalRingHom t).mapMatrix D * P) :
    ∃ v ≠ 0, P *ᵥ v = v ∧ (Polynomial.evalRingHom t).mapMatrix D *ᵥ v = 0 := by
  let Q := (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix P
  let F := (1 + Q) * D + (1 - Q)
  have hmap (s : ℝ) : (Polynomial.evalRingHom s).mapMatrix F =
      (1 + P) * (Polynomial.evalRingHom s).mapMatrix D + (1 - P) := by
    have hQ : (Polynomial.evalRingHom s).mapMatrix Q = P := by
      ext i j
      exact Polynomial.eval_C
    simp only [F, map_add, map_mul, map_sub, map_one, hQ]
  have hd (s : ℝ) : ((Polynomial.evalRingHom s).mapMatrix F).det = F.det.eval s :=
    ((Polynomial.evalRingHom s).map_det F).symm
  have hz : F.det = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioi_infinite (0 : ℝ)).mono
    intro s hs
    change F.det.eval s = 0
    rw [← hd s, hmap]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    obtain ⟨v, hv, hp, hD⟩ := hpos s hs
    exact ⟨v, hv, by rw [add_mulVec, ← mulVec_mulVec, hD, mulVec_zero,
      sub_mulVec, one_mulVec, hp, sub_self, add_zero]⟩
  have hzero : ((1 + P) * (Polynomial.evalRingHom t).mapMatrix D + (1 - P)).det = 0 := by
    rw [← hmap, hd, hz, Polynomial.eval_zero]
  obtain ⟨v, hv, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  let B := (Polynomial.evalRingHom t).mapMatrix D
  change ((1 + P) * B + (1 - P)) *ᵥ v = 0 at hkernel
  have hcancel : (1 - P) * ((1 + P) * B + (1 - P)) = (1 - P) + (1 - P) := by
    calc
      _ = (1 - P * P) * B + (1 - P) * (1 - P) := by noncomm_ring
      _ = (1 - P * P) * B + (1 - P - P + P * P) := by noncomm_ring
      _ = _ := by rw [hP]; simp only [sub_self, zero_mul, zero_add]; noncomm_ring
  have hsub : (1 - P) *ᵥ v = 0 := by
    have h := congrArg (fun u => (1 - P) *ᵥ u) hkernel
    rw [mulVec_mulVec, hcancel, add_mulVec, mulVec_zero] at h
    funext i
    have hi := congrFun h i
    change ((1 - P) *ᵥ v) i + ((1 - P) *ᵥ v) i = 0 at hi
    change ((1 - P) *ᵥ v) i = 0
    linarith
  have hfix : P *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hsub
    exact hsub.symm
  have hBfix : P *ᵥ (B *ᵥ v) = B *ᵥ v := by
    rw [mulVec_mulVec, show P * B = B * P from hcomm, ← mulVec_mulVec, hfix]
  rw [add_mulVec, hsub, add_zero, ← mulVec_mulVec, add_mulVec, one_mulVec, hBfix] at hkernel
  refine ⟨v, hv, hfix, ?_⟩
  funext i
  have hi := congrFun hkernel i
  change (B *ᵥ v) i + (B *ᵥ v) i = 0 at hi
  change (B *ᵥ v) i = 0
  linarith

end Matrix

open scoped Matrix Polynomial

namespace Matrix

/-- If changing the sign of a parameter conjugates the polynomial family by
an involution that anticommutes with the given symmetry, a fixed-sector
kernel cannot persist if the unit kernel lies entirely in the fixed sector. -/
theorem not_forall_pos_fixed_kernel_of_anticommute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ[X]) (P J : Matrix ι ι ℝ) (hP : P * P = 1) (hJ : J * J = 1)
    (hPJ : P * J = -(J * P))
    (hcomm : P * (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix D =
      (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix D * P)
    (hchange : (Polynomial.evalRingHom (1 : ℝ)).mapMatrix D * J =
      J * (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix D)
    (hfixed : ∀ v : ι → ℝ,
      (Polynomial.evalRingHom (1 : ℝ)).mapMatrix D *ᵥ v = 0 → P *ᵥ v = v) :
    ¬ ∀ s : ℝ, 0 < s → ∃ v ≠ 0,
      P *ᵥ v = v ∧ (Polynomial.evalRingHom s).mapMatrix D *ᵥ v = 0 := by
  intro hp
  obtain ⟨v, hv, hPv, hDv⟩ :=
    exists_fixed_mulVec_eq_zero_of_forall_pos P D hP hp (-1) hcomm
  have hz : (Polynomial.evalRingHom (1 : ℝ)).mapMatrix D *ᵥ (J *ᵥ v) = 0 := by
    rw [mulVec_mulVec, hchange, ← mulVec_mulVec, hDv, mulVec_zero]
  have hplus := hfixed (J *ᵥ v) hz
  have hminus : P *ᵥ (J *ᵥ v) = -(J *ᵥ v) := by
    rw [mulVec_mulVec, hPJ, neg_mulVec, ← mulVec_mulVec, hPv]
  have hzero : J *ᵥ v = 0 := by
    funext i
    have hi := congrFun (hplus.symm.trans hminus) i
    change (J *ᵥ v) i = -(J *ᵥ v) i at hi
    change (J *ᵥ v) i = 0
    linarith
  apply hv
  calc
    v = J *ᵥ (J *ᵥ v) := by rw [mulVec_mulVec, hJ, one_mulVec]
    _ = 0 := by rw [hzero, mulVec_zero]

end Matrix

open scoped BigOperators Matrix

namespace Matrix

/-- A singular real Gram defect of an irreducible matrix has a strictly
positive eigenvector in the kernel of the transposed Gram factor.
`IsIrreducible` provides entrywise nonnegativity, and the Gram identity implies symmetry. -/
theorem exists_positive_gram_kernel_of_det_eq_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A : Matrix ι ι ℝ} {K : Matrix ι κ ℝ} {q : ℝ}
    (hA : A.IsIrreducible) (hGram : q • (1 : Matrix ι ι ℝ) - A = K * Kᵀ)
    (hdet : (q • (1 : Matrix ι ι ℝ) - A).det = 0) :
    ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ Kᵀ *ᵥ u = 0 ∧ A *ᵥ u = q • u := by
  let D := q • (1 : Matrix ι ι ℝ) - A
  have hGramD : D = K * Kᵀ := hGram
  obtain ⟨v, hv, hvDefect⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := D)).mpr hdet
  have gramForm (x : ι → ℝ) :
      x ⬝ᵥ (D *ᵥ x) = ∑ j, (Kᵀ *ᵥ x) j ^ 2 := by
    rw [hGramD, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [dotProduct, pow_two]
  let u : ι → ℝ := fun i => |v i|
  have huNonneg (i : ι) : 0 ≤ u i := abs_nonneg (v i)
  have hNorm : u ⬝ᵥ u = v ⬝ᵥ v := by
    simp only [dotProduct, u, abs_mul_abs_self]
  have hAdjacency : v ⬝ᵥ (A *ᵥ v) ≤ u ⬝ᵥ (A *ᵥ u) := by
    simp only [Matrix.dot_mulVec_eq_sum_sum]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
    simpa only [u, abs_mul, abs_of_nonneg (hA.nonneg i j)] using
      le_abs_self (v i * A i j * v j)
  have hDefectForm : u ⬝ᵥ (D *ᵥ u) ≤ v ⬝ᵥ (D *ᵥ v) := by
    simp only [D, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hNorm]
    exact sub_le_sub_left hAdjacency _
  have hSumLe : (∑ j, (Kᵀ *ᵥ u) j ^ 2) ≤ 0 := by
    rw [← gramForm u]
    simpa only [hvDefect, dotProduct_zero] using hDefectForm
  have hSumZero : (∑ j, (Kᵀ *ᵥ u) j ^ 2) = 0 :=
    le_antisymm hSumLe (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hKernel : Kᵀ *ᵥ u = 0 := by
    funext j
    have hj : (Kᵀ *ᵥ u) j ^ 2 = 0 :=
      Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
        (fun j => sq_nonneg ((Kᵀ *ᵥ u) j)) hSumZero j
    exact eq_zero_of_pow_eq_zero hj
  have huDefect : D *ᵥ u = 0 := by
    rw [hGramD, ← Matrix.mulVec_mulVec, hKernel, Matrix.mulVec_zero]
  have hEigen : A *ᵥ u = q • u := by
    symm
    simpa only [D, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
      using huDefect
  have zeroOfEdge {i j : ι} (hij : 0 < A i j) (hi : u i = 0) : u j = 0 := by
    have hRow : ∑ k, A i k * u k = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hi, mul_zero]
        using congrFun hEigen i
    have hTerm : A i j * u j = 0 :=
      Matrix.forall_eq_zero_of_finset_sum_eq_zero_of_nonneg
        (fun k => mul_nonneg (hA.nonneg i k) (huNonneg k)) hRow j
    exact (mul_eq_zero.mp hTerm).resolve_left (ne_of_gt hij)
  letI : Quiver ι := Matrix.toQuiver A
  have zeroAlongPath {i j : ι} (p : Quiver.Path i j) : u i = 0 → u j = 0 := by
    induction p with
    | nil => exact id
    | cons _ e ih => exact fun hi => zeroOfEdge e.down (ih hi)
  refine ⟨u, ?_, hKernel, hEigen⟩
  intro i
  refine lt_of_le_of_ne (huNonneg i) ?_
  intro hi
  apply hv
  funext j
  obtain ⟨p, _⟩ := hA.connected i j
  exact abs_eq_zero.mp (zeroAlongPath p hi.symm)

end Matrix
