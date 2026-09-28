/- GID: D5/S3/Arith/GroupActionInvariantStatistic
   generality: G
   mirror-B: D5/B/S3/Arith/GroupActionInvariantStatistic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite symmetry forces constant statistics and cardinal divisibility. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Sign

/- Library-search audit trail (2026-09-28):
   * `Equiv.Perm.closure_isSwap` is the pinned Mathlib generation theorem for all finite
     permutations. No D5 declaration packages its use for a value-valued statistic.
   * `MulAction.orbit` and `MulAction.mem_orbit_iff` are the pinned orbit interfaces. No
     repository theorem packages the corresponding finite orbit sum as a cardinal multiple.
   * The result below therefore adds a reusable group-action/arithmetic bridge rather than
     restating a definition or binding an existing theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GroupActionInvariantStatistic

universe u v

/-- A statistic is unchanged by every transposition of the finite index set. -/
def SwapInvariant {I : Type u} [DecidableEq I] {A : Type v} (f : I → A) : Prop :=
  ∀ σ : Equiv.Perm I, σ.IsSwap → ∀ i, f (σ i) = f i

/-- A permutation subgroup preserving a statistic pointwise. -/
def preservingSubgroup {I : Type u} {A : Type v} (f : I → A) :
    Subgroup (Equiv.Perm I) := by
  classical
  exact
    { carrier := {σ | ∀ i, f (σ i) = f i}
      one_mem' := by
        intro i
        rfl
      mul_mem' := by
        intro σ τ hσ hτ i
        rw [Equiv.Perm.mul_apply, hσ, hτ]
      inv_mem' := by
        intro σ hσ i
        have h := hσ (σ⁻¹ i)
        simpa using h.symm }

@[simp]
theorem mem_preservingSubgroup {I : Type u} {A : Type v} (f : I → A)
    (σ : Equiv.Perm I) :
    σ ∈ preservingSubgroup f ↔ ∀ i, f (σ i) = f i :=
  Iff.rfl

/-- Since transpositions generate a finite symmetric group, their invariance already implies
invariance under every permutation. -/
theorem swap_invariant_permutation_invariant
    {I : Type u} [Finite I] [DecidableEq I] {A : Type v} {f : I → A}
    (h : SwapInvariant f) :
    ∀ σ : Equiv.Perm I, ∀ i, f (σ i) = f i := by
  classical
  let H : Subgroup (Equiv.Perm I) := preservingSubgroup f
  have hswap : ∀ σ ∈ ({σ : Equiv.Perm I | σ.IsSwap} : Set (Equiv.Perm I)), σ ∈ H := by
    intro σ hσ
    exact h σ hσ
  have hclosure : Subgroup.closure {σ : Equiv.Perm I | σ.IsSwap} ≤ H :=
    (Subgroup.closure_le _).2 hswap
  intro σ i
  have htop : Subgroup.closure {σ : Equiv.Perm I | σ.IsSwap} = ⊤ :=
    Equiv.Perm.closure_isSwap
  have hmem : σ ∈ Subgroup.closure {σ : Equiv.Perm I | σ.IsSwap} := by
    rw [htop]
    trivial
  exact hclosure hmem i

/-- A transposition-invariant statistic on a nonempty finite carrier is constant. -/
theorem swap_invariant_is_constant
    {I : Type u} [Finite I] [DecidableEq I] [Nonempty I] {A : Type v} {f : I → A}
    (h : SwapInvariant f) :
    ∃ c, ∀ i, f i = c := by
  classical
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  refine ⟨f i₀, ?_⟩
  intro i
  have hall := swap_invariant_permutation_invariant h (Equiv.swap i₀ i) i₀
  simpa using hall

/-- The finite orbit of an invariant statistic has a sum equal to orbit cardinality times its
value at the base point. This is the arithmetic content of orbitwise conservation. -/
theorem orbit_sum_eq_card_mul_value
    {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (x : X) [Fintype (MulAction.orbit G x)] (f : X → ℕ)
    (hinv : ∀ (g : G) (y : X), f (g • y) = f y) :
    (∑ y : MulAction.orbit G x, f y) =
      Fintype.card (MulAction.orbit G x) * f x := by
  calc
    (∑ y : MulAction.orbit G x, f y) =
        ∑ y : MulAction.orbit G x, f x := by
      apply Finset.sum_congr rfl
      intro y _
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp y.property
      rw [← hg]
      exact hinv g x
    _ = Fintype.card (MulAction.orbit G x) * f x := by
      simp

/-- The orbit sum of an invariant natural statistic is divisible by the orbit cardinality. -/
theorem orbit_sum_dvd_card
    {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (x : X) [Fintype (MulAction.orbit G x)] (f : X → ℕ)
    (hinv : ∀ (g : G) (y : X), f (g • y) = f y) :
    Fintype.card (MulAction.orbit G x) ∣
      ∑ y : MulAction.orbit G x, f y := by
  rw [orbit_sum_eq_card_mul_value x f hinv]
  exact dvd_mul_right _ _

/-- A nonempty finite transposition-symmetric natural statistic has total divisible by the
number of labels. This is a testable numerical obstruction for proposed universal counts. -/
theorem swap_invariant_sum_dvd_card
    {I : Type u} [Finite I] [Fintype I] [DecidableEq I] [Nonempty I] {f : I → ℕ}
    (h : SwapInvariant f) :
    Fintype.card I ∣ ∑ i, f i := by
  classical
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  have hc : ∀ i, f i = f i₀ := by
    intro i
    have hall := swap_invariant_permutation_invariant h (Equiv.swap i₀ i) i₀
    simpa using hall
  have hsum : ∑ i, f i = Fintype.card I * f i₀ := by
    calc
      (∑ i, f i) = ∑ i, f i₀ := by
        apply Finset.sum_congr rfl
        intro i _
        exact hc i
      _ = Fintype.card I * f i₀ := by simp
  exact ⟨f i₀, hsum⟩

/-- On `Fin n`, a nonempty transposition-symmetric natural statistic has a total divisible by
`n`. This is the finite arithmetic form used by concrete counting problems. -/
theorem fin_sum_dvd_card
    (n : ℕ) (hn : 0 < n) (f : Fin n → ℕ)
    (h : SwapInvariant f) :
    n ∣ ∑ i, f i := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa using (swap_invariant_sum_dvd_card (I := Fin n) h)

example {I : Type} [Finite I] [DecidableEq I] [Nonempty I] (f : I → ℕ)
    (h : SwapInvariant f) :
    ∃ c, ∀ i, f i = c :=
  by
    classical
    exact swap_invariant_is_constant h

#print axioms swap_invariant_permutation_invariant
#print axioms swap_invariant_is_constant
#print axioms orbit_sum_eq_card_mul_value
#print axioms orbit_sum_dvd_card
#print axioms swap_invariant_sum_dvd_card
#print axioms fin_sum_dvd_card

end D5.S3.Arith.GroupActionInvariantStatistic
