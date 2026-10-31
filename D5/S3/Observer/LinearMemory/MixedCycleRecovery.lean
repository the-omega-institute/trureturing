/- GID: D5/S3/Observer/LinearMemory/MixedCycleRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/MixedCycleRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed cycles expose exactly their coordinate window and determine target-dependent recovery. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.GroupTheory.Perm.List
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Isomorphisms
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.LinearMemory.MixedCycleRecovery

open scoped RealInnerProductSpace
open Submodule

variable {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev Axis (k : ℕ) := Fin 3 ⊕ Fin k

/-- The visible axes and the first `r` hidden axes. -/
def kept (r : ℕ) : Set (Axis k) :=
  {i | match i with | .inl _ => True | .inr j => j.val < r}

/-- Coordinate subspace in the specified orthonormal basis. -/
def window (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) : Submodule ℝ V :=
  span ℝ (b '' kept r)

abbrev visible (b : OrthonormalBasis (Axis k) ℝ V) := window b 0

/-- Intrinsic block-diagonal `SO(E)` with the hidden summand fixed pointwise. -/
def rotations (b : OrthonormalBasis (Axis k) ℝ V) : Set (V ≃ₗᵢ[ℝ] V) :=
  {g | LinearMap.det g.toLinearEquiv.toLinearMap = 1 ∧
    ∀ j : Fin k, g (b (.inr j)) = b (.inr j)}

/-- The ordered cycle `(e₁ f₁ ... fᵣ)`, including its singleton case. -/
def cycleNodes (r : ℕ) (hr : r ≤ k) : List (Axis k) :=
  Sum.inl 0 :: List.ofFn (fun j : Fin r => Sum.inr (Fin.castLE hr j))

def mixedCycle (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (hr : r ≤ k) :
    V ≃ₗᵢ[ℝ] V :=
  b.equiv b (cycleNodes r hr).formPerm

/-- The actual generated group; no finiteness assumption is imposed on it. -/
def generated (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (hr : r ≤ k) :
    Subgroup (V ≃ₗᵢ[ℝ] V) :=
  Subgroup.closure (rotations b ∪ {mixedCycle b r hr})

/-- Sum of all pulled-back visible subspaces. -/
def rowSpace (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (hr : r ≤ k) :
    Submodule ℝ V :=
  ⨆ g : generated b r hr,
    (visible b).map g.val.symm.toLinearEquiv.toLinearMap

/-- All the vector-valued readouts, indexed by the full generated group. -/
def observations (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (hr : r ≤ k) :
    V →ₗ[ℝ] (generated b r hr → visible b) :=
  LinearMap.pi fun g =>
    (visible b).orthogonalProjectionOnto.toLinearMap.comp g.val.toLinearEquiv.toLinearMap

private theorem mem_window_iff (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (x : V) :
    x ∈ window b r ↔ ∀ j : Fin k, r ≤ j.val → b.repr x (.inr j) = 0 := by
  rw [window, b.toBasis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    OrthonormalBasis.coe_toBasis_repr_apply]
  constructor
  · intro h j hj
    by_contra hn
    have := h hn
    change j.val < r at this
    omega
  · intro h i hi
    cases i with
    | inl i => trivial
    | inr j =>
      change j.val < r
      by_contra hn
      exact hi (h j (by omega))

private theorem basis_mem_window (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (i : Axis k) (hi : i ∈ kept r) : b i ∈ window b r :=
  subset_span ⟨i, hi, rfl⟩

private theorem cycle_nodes_nodup (r : ℕ) (hr : r ≤ k) : (cycleNodes r hr).Nodup := by
  simp only [cycleNodes, List.nodup_cons, List.mem_ofFn, not_exists]
  constructor
  · intro i
    simp
  · exact List.nodup_ofFn.mpr (fun i j h => Fin.ext (by
      have := Sum.inr.inj h
      exact congrArg Fin.val this))

private theorem cycle_fixes_tail (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) (j : Fin k) (hj : r ≤ j.val) :
    mixedCycle b r hr (b (.inr j)) = b (.inr j) := by
  rw [mixedCycle, OrthonormalBasis.equiv_apply_basis]
  congr 1
  apply List.formPerm_apply_of_notMem
  simp only [cycleNodes, List.mem_cons, Sum.inr.injEq, List.mem_ofFn,
    Sum.inr.injEq, reduceCtorEq, false_or, not_exists]
  intro i he
  have := congrArg Fin.val he
  simp only [Fin.coe_castLE] at this
  omega

private theorem generated_fixes_tail (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) (g : generated b r hr) (j : Fin k) (hj : r ≤ j.val) :
    g.val (b (.inr j)) = b (.inr j) := by
  have hg := g.property
  change g.val ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact ha.2 j
    · rcases ha with rfl
      exact cycle_fixes_tail b r hr j hj
  | one => rfl
  | mul a c ha hc iha ihc =>
    change a (c (b (.inr j))) = _
    rw [ihc, iha]
  | inv a ha iha =>
    apply a.injective
    simpa using iha.symm

private theorem pullback_rows_le_window (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) : rowSpace b r hr ≤ window b r := by
  refine iSup_le fun g => ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_window_iff b r _).mpr
  intro j hj
  rw [OrthonormalBasis.repr_apply_apply]
  have hg := generated_fixes_tail b r hr g j hj
  have hin := (mem_window_iff b 0 x).mp hx j (Nat.zero_le _)
  rw [OrthonormalBasis.repr_apply_apply] at hin
  calc
    ⟪b (.inr j), g.val.symm x⟫_ℝ = ⟪g.val (b (.inr j)), x⟫_ℝ :=
      (g.val.inner_map_eq_flip _ _).symm
    _ = 0 := by rw [hg]; exact hin

private theorem cycle_pow_basis (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) (n : ℕ) (i : Axis k) :
    (mixedCycle b r hr ^ n) (b i) = b (((cycleNodes r hr).formPerm ^ n) i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', LinearIsometryEquiv.mul_apply, Equiv.Perm.mul_apply, ih]
    exact OrthonormalBasis.equiv_apply_basis b b _ _

private theorem cycle_reaches_hidden (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) (j : Fin r) :
    (mixedCycle b r hr ^ (j.val + 1)) (b (.inl 0)) =
      b (.inr (Fin.castLE hr j)) := by
  rw [cycle_pow_basis]
  congr 1
  have h := List.formPerm_pow_apply_head (Sum.inl (0 : Fin 3))
    (List.ofFn (fun j : Fin r => Sum.inr (Fin.castLE hr j)))
    (cycle_nodes_nodup r hr) (j.val + 1)
  simpa [cycleNodes, Nat.mod_eq_of_lt (show j.val + 1 < r + 1 by omega)] using h

private theorem pullback_rows_eq_window (b : OrthonormalBasis (Axis k) ℝ V)
    (r : ℕ) (hr : r ≤ k) : rowSpace b r hr = window b r := by
  apply le_antisymm (pullback_rows_le_window b r hr)
  apply span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  have hvis : ∀ t : Fin 3, b (.inl t) ∈ visible b :=
    fun t => basis_mem_window b 0 (.inl t) trivial
  have hcycle : mixedCycle b r hr ∈ generated b r hr :=
    Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  cases i with
  | inl t =>
    exact le_iSup_of_le (⟨1, (generated b r hr).one_mem⟩ : generated b r hr)
      (le_rfl) ⟨b (.inl t), hvis t, rfl⟩
  | inr j =>
    have hj : j.val < r := hi
    let j' : Fin r := ⟨j.val, hj⟩
    let a := mixedCycle b r hr ^ (j.val + 1)
    have ha : a ∈ generated b r hr := (generated b r hr).pow_mem hcycle _
    apply (le_iSup_of_le (⟨a⁻¹, (generated b r hr).inv_mem ha⟩ : generated b r hr)
      le_rfl)
    refine ⟨b (.inl 0), hvis 0, ?_⟩
    simpa [a, j', LinearIsometryEquiv.inv_eq_symm] using
      cycle_reaches_hidden b r hr j'

end D5.S3.Observer.LinearMemory.MixedCycleRecovery
