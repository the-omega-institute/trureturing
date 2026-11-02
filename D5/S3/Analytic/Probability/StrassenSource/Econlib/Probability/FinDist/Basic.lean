/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Attributes
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.UnitInterval

/-!
# `FinDist α` — probability distribution over a finite type

The structure `FinDist α` is a probability mass function over any `[Fintype α] [DecidableEq α]`;
distributions over `Fin n` are `FinDist (Fin n)`. The nonnegativity and sum-to-one constraints are
baked into the type as fields, so every `FinDist` is a valid distribution by construction. This
file collects the core API together with the elementary constructors: The Dirac point mass `pure`,
the `uniform` distribution, the binary `mixture`, and the finite `finMixture`.

## Main definitions

* `FinDist` — a pmf `α → ℝ` that is nonnegative and sums to one.
* `FinDist.support` — the set of outcomes with positive probability.
* `FinDist.IsMode` — the probability mass is maximized at an outcome.
* `FinDist.pure` — point mass at a single outcome.
* `FinDist.uniform` — the uniform distribution on a nonempty finite type.
* `FinDist.mixture` — convex combination of two distributions.
* `FinDist.finMixture` — finite mixture indexed by a finite type.

## Main statements

* `FinDist.prob_le_one` — each probability is at most one.
* `FinDist.support_mixture` — support of a strict mixture is the union of supports.

## Tags

probability, finite distributions, pmf, dirac, uniform, mixture
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability

/-- A probability distribution over a finite type `α`. -/
structure FinDist (α : Type*) [Fintype α] [DecidableEq α] where
  /-- Probability mass assigned to each outcome. -/
  pmf : α → ℝ
  /-- Probability masses are nonnegative. -/
  nonneg : ∀ a, 0 ≤ pmf a
  /-- Total probability mass is one. -/
  sum_one : ∑ a, pmf a = 1

namespace FinDist

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Coercion allowing `d a` syntax for probability evaluation. -/
instance : CoeFun (FinDist α) (fun _ => α → ℝ) where
  coe d := d.pmf

/-- Bridge between field access and the `CoeFun` coercion, so `simp` can normalize mixed `d.pmf a`
/ `d a` spellings. -/
@[simp] lemma pmf_eq_coe (d : FinDist α) (a : α) : d.pmf a = d a := rfl

/-- The set of outcomes with positive probability. -/
noncomputable def support (d : FinDist α) : Finset α :=
  Finset.univ.filter (fun a => 0 < d.pmf a)

/-- `a` is a mode of `d`: The probability mass is maximized at `a`. A mode need not be unique —
e.g. every outcome is a mode of the uniform distribution. -/
def IsMode (d : FinDist α) (a : α) : Prop :=
  ∀ b, d.pmf b ≤ d.pmf a

/-- Each probability is at most one. -/
lemma prob_le_one (d : FinDist α) (a : α) : d.pmf a ≤ 1 :=
  d.sum_one ▸ Finset.single_le_sum (fun b _ => d.nonneg b) (Finset.mem_univ a)

/-- `sum_one` in binary form: The two masses of a distribution on `Fin 2` sum to one. -/
lemma sum_pmf_two (d : FinDist (Fin 2)) : d.pmf 0 + d.pmf 1 = 1 := by
  have h := d.sum_one
  rwa [Fin.sum_univ_two] at h

/-- Some outcome carries positive mass: The pmf cannot vanish identically under `sum_one`. -/
lemma exists_pmf_pos (d : FinDist α) : ∃ a, 0 < d.pmf a := by
  by_contra h
  push Not at h
  have hzero : ∑ a, d.pmf a = 0 :=
    Finset.sum_eq_zero fun a _ => le_antisymm (h a) (d.nonneg a)
  rw [d.sum_one] at hzero
  norm_num at hzero

/-- Two distributions are equal when their pmfs agree pointwise. -/
@[ext]
lemma ext (d₁ d₂ : FinDist α) (h : ∀ a, d₁.pmf a = d₂.pmf a) : d₁ = d₂ := by
  cases d₁; cases d₂; congr; funext a; exact h a

/-! ### Pure (Dirac) distribution -/

/-- Degenerate distribution placing mass 1 on a single outcome (the monadic unit of the pmf layer;
cf. `PMF.pure`). -/
noncomputable def pure (a : α) : FinDist α where
  pmf b := if a = b then 1 else 0
  nonneg b := by split <;> positivity
  sum_one := by simp

/-- Evaluation of the point mass, in `if`-form. Stated on the coercion — the simp-normal form per
`pmf_eq_coe` — so it fires after `simp` has normalized `.pmf` spellings. -/
@[simp, findist_eval] lemma pure_apply (a b : α) :
    (FinDist.pure a : FinDist α) b = if a = b then 1 else 0 := rfl

/-- `pure_apply` in the `.pmf` spelling, for `rw` against goals that haven't been simp-normalized
to the coercion. -/
@[findist_eval] lemma pure_pmf (a b : α) : (FinDist.pure a).pmf b = if a = b then 1 else 0 := rfl

/-- A point mass assigns probability one to its own outcome. -/
lemma pure_apply_self (a : α) : (FinDist.pure a).pmf a = 1 := by
  dsimp [pure]; rw [if_pos rfl]

/-- A point mass assigns probability zero to every other outcome. -/
lemma pure_apply_ne {a b : α} (h : a ≠ b) : (FinDist.pure a).pmf b = 0 := by
  dsimp [pure]; rw [if_neg h]

/-- A distribution with full mass at one outcome is the point mass there — the converse of
`pure_apply_self`. -/
lemma eq_pure_of_pmf_eq_one {d : FinDist α} {a : α} (h : d.pmf a = 1) :
    d = FinDist.pure a := by
  -- The remaining outcomes share total mass `1 - 1 = 0`, and each term is nonnegative.
  have herase : ∑ b ∈ Finset.univ.erase a, d.pmf b = 0 := by
    have hsplit := Finset.add_sum_erase Finset.univ d.pmf (Finset.mem_univ a)
    have hsum := d.sum_one
    linarith
  have hzero : ∀ b, b ≠ a → d.pmf b = 0 := fun b hb =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => d.nonneg c)).mp herase b
      (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  ext b
  by_cases hb : b = a
  · subst hb; rw [h, pure_apply_self]
  · rw [hzero b hb, pure_apply_ne (fun hab => hb hab.symm)]

/-- Two distributions on `Fin 2` with disjoint supports are opposite point masses. -/
lemma eq_pure_pair_of_disjoint_fin_two {d₁ d₂ : FinDist (Fin 2)}
    (h : ∀ m, ¬(0 < d₁.pmf m ∧ 0 < d₂.pmf m)) :
    ∃ m₁ m₂ : Fin 2, m₁ ≠ m₂ ∧ d₁ = FinDist.pure m₁ ∧ d₂ = FinDist.pure m₂ := by
  obtain ⟨m₁, hm₁⟩ := d₁.exists_pmf_pos
  -- Disjointness kills `d₂` where `d₁` lives, so `d₂` is pure on the other coordinate; then
  -- disjointness back-propagates to make `d₁` pure as well.
  have h₂m₁ : d₂.pmf m₁ = 0 := by
    by_contra hne
    exact h m₁ ⟨hm₁, lt_of_le_of_ne (d₂.nonneg m₁) (Ne.symm hne)⟩
  by_cases hcase : m₁ = 0
  · subst hcase
    have hd₂ : d₂ = FinDist.pure 1 :=
      eq_pure_of_pmf_eq_one (by linarith [d₂.sum_pmf_two])
    have h₁1 : d₁.pmf 1 = 0 := by
      by_contra hne
      refine h 1 ⟨lt_of_le_of_ne (d₁.nonneg 1) (Ne.symm hne), ?_⟩
      rw [hd₂, pure_apply_self]
      norm_num
    have hd₁ : d₁ = FinDist.pure 0 :=
      eq_pure_of_pmf_eq_one (by linarith [d₁.sum_pmf_two])
    exact ⟨0, 1, by decide, hd₁, hd₂⟩
  · have hcase1 : m₁ = 1 := by omega
    subst hcase1
    have hd₂ : d₂ = FinDist.pure 0 :=
      eq_pure_of_pmf_eq_one (by linarith [d₂.sum_pmf_two])
    have h₁0 : d₁.pmf 0 = 0 := by
      by_contra hne
      refine h 0 ⟨lt_of_le_of_ne (d₁.nonneg 0) (Ne.symm hne), ?_⟩
      rw [hd₂, pure_apply_self]
      norm_num
    have hd₁ : d₁ = FinDist.pure 1 :=
      eq_pure_of_pmf_eq_one (by linarith [d₁.sum_pmf_two])
    exact ⟨1, 0, by decide, hd₁, hd₂⟩

/-- The support of a point mass is the singleton at that outcome. -/
lemma support_pure (a : α) : (FinDist.pure a).support = {a} := by
  ext b
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : a = b <;> simp [pure, h, eq_comm]

/-! ### Uniform distribution -/

/-- Uniform distribution over a nonempty finite type. -/
noncomputable def uniform [Nonempty α] : FinDist α where
  pmf _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

@[findist_eval] lemma uniform_apply [Nonempty α] (a : α) :
    (FinDist.uniform (α := α)).pmf a = (Fintype.card α : ℝ)⁻¹ := rfl

/-! ### Mixtures -/

/-- Convex combination `t • d₁ + (1 - t) • d₂`, with mixing weight `t` a point of the
`unitInterval` (so the `[0,1]` bounds are carried by the type). -/
noncomputable def mixture (t : unitInterval) (d₁ d₂ : FinDist α) : FinDist α where
  pmf a := (t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a
  nonneg a := add_nonneg (mul_nonneg t.2.1 (d₁.nonneg a))
    (mul_nonneg (by linarith [t.2.2]) (d₂.nonneg a))
  sum_one := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [d₁.sum_one, d₂.sum_one]; ring

@[findist_eval] lemma mixture_pmf (t : unitInterval) (d₁ d₂ : FinDist α) (a : α) :
    (FinDist.mixture t d₁ d₂).pmf a = (t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a := rfl

/-- The support of a strict mixture is the union of the two supports. -/
lemma support_mixture (t : unitInterval) (d₁ d₂ : FinDist α)
    (h₀ : (0 : ℝ) < (t : ℝ)) (h₁ : (t : ℝ) < 1) :
    (FinDist.mixture t d₁ d₂).support = d₁.support ∪ d₂.support := by
  ext a
  unfold support
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  change (0 < (t : ℝ) * d₁.pmf a + (1 - (t : ℝ)) * d₂.pmf a) ↔
    (0 < d₁.pmf a ∨ 0 < d₂.pmf a)
  constructor
  · intro h
    by_cases h1 : 0 < d₁.pmf a
    · exact Or.inl h1
    by_cases h2 : 0 < d₂.pmf a
    · exact Or.inr h2
    have h1z : d₁.pmf a = 0 := le_antisymm (le_of_not_gt h1) (d₁.nonneg a)
    have h2z : d₂.pmf a = 0 := le_antisymm (le_of_not_gt h2) (d₂.nonneg a)
    rw [h1z, h2z] at h
    linarith
  · rintro (h1 | h2)
    · have ht1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
      exact add_pos_of_pos_of_nonneg (mul_pos h₀ h1)
        (mul_nonneg ht1 (d₂.nonneg a))
    · have ht1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt h₀) (d₁.nonneg a))
        (mul_pos (by linarith [h₁]) h2)

/-- A weighted average of `FinDist`s is again a `FinDist`. Given weights `w : FinDist β` and
beliefs `μ : β → FinDist α`, the function `a ↦ ∑ s, w(s) * μ(s)(a)` is a valid distribution.

This is the core building block for Bayes-plausibility: A Bayes-plausible splitting of a prior
decomposes it as a convex combination of posterior beliefs. -/
noncomputable def finMixture (weights : FinDist β) (beliefs : β → FinDist α) :
    FinDist α where
  pmf a := ∑ s, weights.pmf s * (beliefs s).pmf a
  nonneg a := Finset.sum_nonneg fun s _ => mul_nonneg (weights.nonneg s) ((beliefs s).nonneg a)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [fun s => (beliefs s).sum_one, mul_one, weights.sum_one]

@[simp, findist_eval] lemma finMixture_pmf (weights : FinDist β) (beliefs : β → FinDist α)
    (a : α) :
    (FinDist.finMixture weights beliefs).pmf a = ∑ s, weights.pmf s * (beliefs s).pmf a :=
  rfl

end FinDist

end Econlib.Probability
