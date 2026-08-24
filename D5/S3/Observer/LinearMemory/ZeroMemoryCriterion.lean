/- GID: D5/S3/Observer/LinearMemory/ZeroMemoryCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ZeroMemoryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero memory iff kernel invariance iff whole-W descent; degeneracies verified. -/
/- Library-search audit trail (2026-08-25): pinned Mathlib supplies
   `Module.End.invtSubmodule`, `Submodule.Quotient.subsingleton_iff`,
   `LinearMap.quotKerEquivRange`, and `LinearMap.exists_extend`; all are used below.
   Searches of `Submodule.map`, `Submodule.comap`, `Submodule.quotientRel`, and
   `Submodule.Quotient` found no packaged greatest invariant submodule inside a kernel.
   Local smart-search for maximal invariant subspaces and extension returned no exact hit;
   source search then found `LinearMap.exists_extend`. LSP LeanSearch/Loogle was unavailable.
   Repository search found only set-level `EffectiveDescent` and observation congruences;
   neither preserves the linear structure needed for the whole-codomain descent here. -/

import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic
import Mathlib.Tactic.TFAE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

private lemma iterate_zero_apply_linear
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (T : V →ₗ[K] V) (k : ℕ) :
    (T^[k]) 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_zero]

private lemma iterate_add_apply_linear
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (T : V →ₗ[K] V) (k : ℕ) (x y : V) :
    (T^[k]) (x + y) = (T^[k]) x + (T^[k]) y := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

private lemma iterate_smul_apply_linear
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (T : V →ₗ[K] V) (k : ℕ) (a : K) (x : V) :
    (T^[k]) (a • x) = a • (T^[k]) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul]

/-- The directions invisible both now and after every finite number of updates. -/
def eventualKernel
    {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) : Submodule K V where
  carrier := {x | ∀ k : ℕ, (T^[k]) x ∈ LinearMap.ker C}
  zero_mem' := by
    intro k
    rw [iterate_zero_apply_linear]
    exact Submodule.zero_mem _
  add_mem' := by
    intro x y hx hy k
    rw [iterate_add_apply_linear]
    exact (LinearMap.ker C).add_mem (hx k) (hy k)
  smul_mem' := by
    intro a x hx k
    rw [iterate_smul_apply_linear]
    exact (LinearMap.ker C).smul_mem a (hx k)

/-- Every eventually invisible direction is currently invisible. -/
theorem eventualKernel_le_ker
    {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    eventualKernel C T ≤ LinearMap.ker C := by
  intro x hx
  simpa only [Function.iterate_zero_apply] using hx 0

#print axioms eventualKernel_le_ker

/-- The eventual kernel is invariant under the update. -/
theorem eventualKernel_invariant
    {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    ∀ x ∈ eventualKernel C T, T x ∈ eventualKernel C T := by
  intro x hx k
  simpa only [Function.iterate_succ_apply] using hx (k + 1)

#print axioms eventualKernel_invariant

/-- The eventual kernel contains every `T`-invariant submodule contained in `ker C`. -/
theorem eventualKernel_is_greatest
    {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) (M : Submodule K V)
    (hM : M ≤ LinearMap.ker C ∧ ∀ x ∈ M, T x ∈ M) :
    M ≤ eventualKernel C T := by
  intro x hx k
  apply hM.1
  induction k with
  | zero =>
      simpa only [Function.iterate_zero_apply] using hx
  | succ k ih =>
      simpa only [Function.iterate_succ_apply'] using hM.2 _ ih

#print axioms eventualKernel_is_greatest

/-- The linear memory residual `ker C / N∞`, with `N∞` regarded as a submodule of `ker C`. -/
def memoryQuotient
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) : Type _ :=
  (LinearMap.ker C) ⧸
    (eventualKernel C T).comap (LinearMap.ker C).subtype

/-- The memory quotient is trivial exactly when the eventual and current kernels coincide. -/
theorem zero_memory_iff_eventualKernel_eq_ker
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    Subsingleton (memoryQuotient C T) ↔
      eventualKernel C T = LinearMap.ker C := by
  change Subsingleton
      ((LinearMap.ker C) ⧸
        (eventualKernel C T).comap (LinearMap.ker C).subtype) ↔ _
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro htop
    apply le_antisymm (eventualKernel_le_ker C T)
    intro x hx
    have hmem :
        (⟨x, hx⟩ : LinearMap.ker C) ∈
          (eventualKernel C T).comap (LinearMap.ker C).subtype := by
      rw [htop]
      exact Submodule.mem_top
    exact hmem
  · intro heq
    apply eq_top_iff.mpr
    intro x hx
    change (x : V) ∈ eventualKernel C T
    rw [heq]
    exact x.property

#print axioms zero_memory_iff_eventualKernel_eq_ker

private lemma zero_memory_of_invariant
    {K V W : Type*} [Ring K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V)
    (hinvariant : ∀ x ∈ LinearMap.ker C, T x ∈ LinearMap.ker C) :
    Subsingleton (memoryQuotient C T) := by
  apply (zero_memory_iff_eventualKernel_eq_ker C T).mpr
  apply le_antisymm (eventualKernel_le_ker C T)
  exact eventualKernel_is_greatest C T (LinearMap.ker C) ⟨le_rfl, hinvariant⟩

/-- Zero memory, kernel invariance, and exact descent to a linear endomorphism of all `W`
are equivalent. -/
theorem zero_memory_criterion
    {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    List.TFAE [
      Subsingleton (memoryQuotient C T),
      ∀ x ∈ LinearMap.ker C, T x ∈ LinearMap.ker C,
      ∃ Tbar : W →ₗ[K] W, ∀ x, C (T x) = Tbar (C x)] := by
  tfae_have 1 → 2 := by
    intro hzero x hx
    have heq := (zero_memory_iff_eventualKernel_eq_ker C T).mp hzero
    have hxEventual : x ∈ eventualKernel C T := by
      rw [heq]
      exact hx
    have hTx := eventualKernel_invariant C T x hxEventual
    rwa [heq] at hTx
  tfae_have 2 → 1 := by
    exact zero_memory_of_invariant C T
  tfae_have 2 → 3 := by
    intro hinvariant
    have hker : LinearMap.ker C ≤ LinearMap.ker (C.comp T) := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact (LinearMap.mem_ker).mp (hinvariant x hx)
    let factor : LinearMap.range C →ₗ[K] W :=
      ((LinearMap.ker C).liftQ (C.comp T) hker).comp
        C.quotKerEquivRange.symm.toLinearMap
    obtain ⟨Tbar, hTbar⟩ := factor.exists_extend
    refine ⟨Tbar, fun x ↦ ?_⟩
    let observed : LinearMap.range C := ⟨C x, C.mem_range_self x⟩
    have hfactor : factor observed = C (T x) := by
      change ((LinearMap.ker C).liftQ (C.comp T) hker)
        (C.quotKerEquivRange.symm observed) = C (T x)
      rw [show observed = ⟨C x, C.mem_range_self x⟩ by rfl]
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      exact LinearMap.congr_fun
        ((LinearMap.ker C).liftQ_mkQ (C.comp T) hker) x
    have hextend : Tbar (C x) = factor observed := by
      simpa [observed] using LinearMap.congr_fun hTbar observed
    exact hfactor.symm.trans hextend.symm
  tfae_have 3 → 2 := by
    rintro ⟨Tbar, hdescends⟩ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    calc
      C (T x) = Tbar (C x) := hdescends x
      _ = Tbar 0 := congrArg Tbar hx
      _ = 0 := map_zero Tbar
  tfae_finish

#print axioms zero_memory_criterion

/-- Over a general ring, kernel invariance need not yield a linear descent on the whole
codomain; this witnesses why the vector-space extension hypothesis cannot simply be dropped. -/
theorem division_ring_assumption_is_necessary :
    ∃ (C T : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ)),
      (∀ x ∈ LinearMap.ker C, T x ∈ LinearMap.ker C) ∧
      ¬ ∃ Tbar : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ),
        ∀ x, C (T x) = Tbar (C x) := by
  let C : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
    { toFun := fun x ↦ (2 * x.1, x.2)
      map_add' := by
        intro x y
        ext <;> simp [mul_add]
      map_smul' := by
        intro a x
        ext <;> simp [mul_assoc, mul_comm] }
  let T : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
    { toFun := fun x ↦ (x.2, x.1)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  refine ⟨C, T, ?_, ?_⟩
  · have hCinjective : Function.Injective C := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      have hfirst := congrArg Prod.fst h
      have hsecond := congrArg Prod.snd h
      change 2 * a = 2 * c at hfirst
      change b = d at hsecond
      have hac : a = c := by omega
      exact Prod.ext hac hsecond
    intro x hx
    have hx0 : x = 0 := hCinjective (by simpa using (LinearMap.mem_ker).mp hx)
    rw [hx0, map_zero]
    exact Submodule.zero_mem _
  · rintro ⟨Tbar, hdescends⟩
    have hAt := congrArg Prod.snd (hdescends (1, 0))
    change (1 : ℤ) = (Tbar (2, 0)).2 at hAt
    have hsmul := congrArg Prod.snd (Tbar.map_smul (2 : ℤ) (1, 0))
    change (Tbar (2, 0)).2 = 2 * (Tbar (1, 0)).2 at hsmul
    omega

#print axioms division_ring_assumption_is_necessary

section DegenerateAudits

variable {K V W : Type*} [DivisionRing K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

example [Subsingleton V] (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    Subsingleton (memoryQuotient C T) := by
  apply zero_memory_of_invariant
  intro x hx
  have hx0 : x = 0 := Subsingleton.elim x 0
  subst x
  simp

example [Subsingleton W] (C : V →ₗ[K] W) (T : V →ₗ[K] V) :
    Subsingleton (memoryQuotient C T) := by
  apply zero_memory_of_invariant
  intro x hx
  rw [LinearMap.mem_ker]
  exact Subsingleton.elim _ _

example (T : V →ₗ[K] V) :
    Subsingleton (memoryQuotient (0 : V →ₗ[K] W) T) := by
  apply zero_memory_of_invariant
  simp

example (C : V →ₗ[K] W) (hC : Function.Injective C) (T : V →ₗ[K] V) :
    Subsingleton (memoryQuotient C T) := by
  apply zero_memory_of_invariant
  intro x hx
  have hx0 : x = 0 := hC (by simpa using (LinearMap.mem_ker).mp hx)
  subst x
  simp

example (C : V →ₗ[K] W) :
    Subsingleton (memoryQuotient C (0 : V →ₗ[K] V)) := by
  apply zero_memory_of_invariant
  simp

example (C : V →ₗ[K] W) :
    Subsingleton (memoryQuotient C LinearMap.id) := by
  apply zero_memory_of_invariant
  simp

end DegenerateAudits

end D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
