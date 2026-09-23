/- GID: D5/S3/Arith/Congruence/ConditionalComparison/FiniteProbability
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Finite rational probability. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/FiniteProbability.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Finite rational probability

The proof is finite before its explicit geometric majorants are introduced.
Keeping the basic probability layer over `ℚ` makes every normalization and
certificate calculation exact.
-/

namespace Erdos7

/-- A probability law on a finite type, represented by exact rational weights. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℚ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Push a finite law forward along an arbitrary map. -/
noncomputable def map {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ where
  weight ξ := ∑ ω, if f ω = ξ then μ.weight ω else 0
  weight_nonneg ξ := by
    exact Finset.sum_nonneg fun ω hω ↦ by
      by_cases h : f ω = ξ
      · simp [h, μ.weight_nonneg ω]
      · simp [h]
  weight_sum := by
    rw [Finset.sum_comm]
    simp [μ.weight_sum]

/-- Product law for a finite dependent family of finite laws. -/
noncomputable def piLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) : FiniteLaw (∀ i, α i) where
  weight x := ∏ i, (μ i).weight (x i)
  weight_nonneg x := Finset.prod_nonneg fun i hi ↦ (μ i).weight_nonneg _
  weight_sum := by
    rw [← Fintype.prod_sum]
    simp [FiniteLaw.weight_sum]

/-- Exact expectation under a finite rational law. -/
def expect (μ : FiniteLaw Ω) (f : Ω → ℚ) : ℚ :=
  ∑ ω, μ.weight ω * f ω

/-- Exact probability of a predicate. -/
def prob (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A] : ℚ :=
  μ.expect fun ω ↦ if A ω then 1 else 0

@[simp] theorem map_weight {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (ξ : Ξ) :
    (μ.map f).weight ξ = ∑ ω, if f ω = ξ then μ.weight ω else 0 := rfl

theorem map_expect {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℚ) :
    (μ.map f).expect g = μ.expect (fun ω ↦ g (f ω)) := by
  classical
  change (∑ ξ, (∑ ω, if f ω = ξ then μ.weight ω else 0) * g ξ) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [Finset.sum_eq_single (f ω)]
  · simp
  · intro ξ hξ hne
    simp [hne.symm]
  · simp

theorem map_prob {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (A : Ξ → Prop) [DecidablePred A] :
    (μ.map f).prob A = μ.prob (fun ω ↦ A (f ω)) := by
  unfold prob
  exact μ.map_expect f _

@[simp] theorem piLaw_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (x : ∀ i, α i) :
    (piLaw μ).weight x = ∏ i, (μ i).weight (x i) := rfl

/-- Fubini decomposition of a product law at its final coordinate. -/
theorem piLaw_expect_snoc {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (μ : Fin (n + 1) → FiniteLaw α)
    (f : (Fin (n + 1) → α) → ℚ) :
    (piLaw μ).expect f =
      (piLaw (fun i : Fin n ↦ μ i.castSucc)).expect (fun x ↦
        (μ (Fin.last n)).expect fun y ↦ f (Fin.snoc x y)) := by
  classical
  unfold expect
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ α))]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  change (∏ i : Fin (n + 1), (μ i).weight
      (Fin.snoc (α := fun _ : Fin (n + 1) ↦ α) x y i)) *
      f (Fin.snoc (α := fun _ : Fin (n + 1) ↦ α) x y) =
    (∏ i : Fin n, (μ i.castSucc).weight (x i)) *
      ((μ (Fin.last n)).weight y *
        f (Fin.snoc (α := fun _ : Fin (n + 1) ↦ α) x y))
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Dependent-type version of final-coordinate Fubini. -/
theorem piLaw_expect_snoc_dep {n : ℕ}
    {α : Fin (n + 1) → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i))
    (f : (∀ i, α i) → ℚ) :
    (piLaw μ).expect f =
      (piLaw (fun i : Fin n ↦ μ i.castSucc)).expect (fun x ↦
        (μ (Fin.last n)).expect fun y ↦
          f (Fin.snoc (α := α) x y)) := by
  classical
  unfold expect
  rw [← Equiv.sum_comp (Fin.snocEquiv α)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  change (∏ i : Fin (n + 1), (μ i).weight
      (Fin.snoc (α := α) x y i)) *
      f (Fin.snoc (α := α) x y) =
    (∏ i : Fin n, (μ i.castSucc).weight (x i)) *
      ((μ (Fin.last n)).weight y *
        f (Fin.snoc (α := α) x y))
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- A product expectation over the empty coordinate type evaluates its
integrand at the unique empty tuple. -/
theorem piLaw_expect_empty
    {α : Fin 0 → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (f : (∀ i, α i) → ℚ) :
    (piLaw μ).expect f = f (fun i ↦ Fin.elim0 i) := by
  simp only [expect, piLaw, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_empty, one_mul]
  rw [Fintype.prod_empty]
  simp only [one_mul]
  apply congrArg f
  funext i
  exact Fin.elim0 i

/-- Fubini decomposition of a product law across two consecutive coordinate
blocks. -/
theorem piLaw_expect_append {α : Type*} [Fintype α] [DecidableEq α]
    {m n : ℕ} (μ : Fin m → FiniteLaw α) (ν : Fin n → FiniteLaw α)
    (f : (Fin (m + n) → α) → ℚ) :
    (piLaw (Fin.append μ ν)).expect f =
      (piLaw μ).expect (fun x ↦
        (piLaw ν).expect fun y ↦ f (Fin.append x y)) := by
  classical
  unfold expect
  rw [← Equiv.sum_comp (Fin.appendEquiv m n)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  change (∏ i : Fin (m + n),
      ((Fin.append μ ν) i).weight (Fin.append x y i)) *
        f (Fin.append x y) =
    (∏ i : Fin m, (μ i).weight (x i)) *
      ((∏ i : Fin n, (ν i).weight (y i)) * f (Fin.append x y))
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- Reindexing coordinates along an equivalence does not change a finite
product expectation. -/
theorem piLaw_expect_reindex
    {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]
    (e : κ ≃ ι) (μ : ι → FiniteLaw α) (f : (ι → α) → ℚ) :
    (piLaw μ).expect f =
      (piLaw (fun k ↦ μ (e k))).expect (fun x ↦
        f (fun i ↦ x (e.symm i))) := by
  classical
  let E : (κ → α) ≃ (ι → α) :=
    { toFun := fun (x : κ → α) (i : ι) ↦ x (e.symm i)
      invFun := fun (y : ι → α) (k : κ) ↦ y (e k)
      left_inv := by intro x; funext k; simp
      right_inv := by intro y; funext i; simp }
  unfold expect
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro x hx
  change (∏ i : ι, (μ i).weight (x (e.symm i))) *
      f (fun i ↦ x (e.symm i)) =
    (∏ k : κ, (μ (e k)).weight (x k)) *
      f (fun i ↦ x (e.symm i))
  congr 1
  apply Fintype.prod_equiv e.symm
  intro i
  simp

/-- A product indexed by a finite sigma type is the product law of its
finite coordinate blocks. -/
theorem piLaw_expect_sigma
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [Fintype α] [DecidableEq α]
    (μ : ∀ i, κ i → FiniteLaw α)
    (f : ((p : (i : ι) × κ i) → α) → ℚ) :
    (piLaw (fun p : (i : ι) × κ i ↦ μ p.1 p.2)).expect f =
      (piLaw (fun i ↦ piLaw (μ i))).expect (fun x ↦
        f (fun p ↦ x p.1 p.2)) := by
  classical
  let E : (∀ i, κ i → α) ≃ ((p : (i : ι) × κ i) → α) :=
    { toFun := fun x p ↦ x p.1 p.2
      invFun := fun y i k ↦ y ⟨i, k⟩
      left_inv := by intro x; funext i k; rfl
      right_inv := by intro y; funext p; cases p; rfl }
  unfold expect
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro x hx
  change (∏ p : (i : ι) × κ i,
      (μ p.1 p.2).weight (x p.1 p.2)) *
        f (fun p ↦ x p.1 p.2) =
    (∏ i : ι, (∏ k : κ i, (μ i k).weight (x i k))) *
      f (fun p ↦ x p.1 p.2)
  rw [Fintype.prod_sigma]

/-- Independence of coordinate events under a finite product law. -/
theorem piLaw_prob_forall_bool {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (A : ∀ i, α i → Bool) :
    (piLaw μ).prob (fun x ↦ ∀ i, A i (x i) = true) =
      ∏ i, (μ i).prob (fun y ↦ A i y = true) := by
  classical
  unfold prob expect
  have hterm : ∀ x : ∀ i, α i,
      (∏ i, (μ i).weight (x i)) *
          (if ∀ i, A i (x i) = true then 1 else 0) =
        ∏ i, (μ i).weight (x i) *
          (if A i (x i) = true then 1 else 0) := by
    intro x
    by_cases hAll : ∀ i, A i (x i) = true
    · simp [hAll]
    · simp only [hAll, ↓reduceIte, mul_zero]
      push_neg at hAll
      obtain ⟨i, hi⟩ := hAll
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases hAi : A i (x i)
      · simp [hAi]
      · exact (hi hAi).elim
  change (∑ x : (∀ i, α i), (∏ i, (μ i).weight (x i)) *
      (if ∀ i, A i (x i) = true then 1 else 0)) =
    ∏ i, ∑ y : α i, (μ i).weight y *
      (if A i y = true then 1 else 0)
  simp_rw [hterm]
  exact (Fintype.prod_sum (fun i y ↦
    (μ i).weight y * (if A i y = true then 1 else 0))).symm

/-- The preceding product formula with the decision procedure for the joint
event made explicit.  This removes irrelevant elaboration differences between
specialized and generic finite-forall deciders. -/
theorem piLaw_prob_forall_bool_with_decider
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (A : ∀ i, α i → Bool)
    (dAll : DecidablePred (fun x : (∀ i, α i) ↦
      ∀ i, A i (x i) = true)) :
    @prob (∀ i, α i) _ (piLaw μ)
        (fun x : (∀ i, α i) ↦ ∀ i, A i (x i) = true) dAll =
      ∏ i, (μ i).prob (fun y ↦ A i y = true) := by
  classical
  unfold prob expect
  have hterm : ∀ x : ∀ i, α i,
      (∏ i, (μ i).weight (x i)) *
          (@ite ℚ (∀ i, A i (x i) = true) (dAll x) 1 0) =
        ∏ i, (μ i).weight (x i) *
          (if A i (x i) = true then 1 else 0) := by
    intro x
    by_cases hAll : ∀ i, A i (x i) = true
    · simp [hAll]
    · simp only [hAll, ↓reduceIte, mul_zero]
      push_neg at hAll
      obtain ⟨i, hi⟩ := hAll
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases hAi : A i (x i)
      · simp [hAi]
      · exact (hi hAi).elim
  change (∑ x : (∀ i, α i), (∏ i, (μ i).weight (x i)) *
      (@ite ℚ (∀ i, A i (x i) = true) (dAll x) 1 0)) =
    ∏ i, ∑ y : α i, (μ i).weight y *
      (if A i y = true then 1 else 0)
  simp_rw [hterm]
  exact (Fintype.prod_sum (fun i y ↦
    (μ i).weight y * (if A i y = true then 1 else 0))).symm

@[simp] theorem expect_const (μ : FiniteLaw Ω) (c : ℚ) :
    μ.expect (fun _ ↦ c) = c := by
  simp [expect, ← Finset.sum_mul, μ.weight_sum]

@[simp] theorem expect_zero (μ : FiniteLaw Ω) :
    μ.expect (fun _ ↦ 0) = 0 := by
  simp [expect]

theorem expect_add (μ : FiniteLaw Ω) (f g : Ω → ℚ) :
    μ.expect (fun ω ↦ f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f g : Ω → ℚ) :
    μ.expect (fun ω ↦ f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_smul (μ : FiniteLaw Ω) (c : ℚ) (f : Ω → ℚ) :
    μ.expect (fun ω ↦ c * f ω) = c * μ.expect f := by
  simp only [expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_finset_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι)
    (f : ι → Ω → ℚ) :
    μ.expect (fun ω ↦ ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Fubini's theorem for two exact finite laws. -/
theorem expect_comm {Ξ : Type*} [Fintype Ξ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω → Ξ → ℚ) :
    μ.expect (fun ω ↦ ν.expect (f ω)) =
      ν.expect (fun ξ ↦ μ.expect (fun ω ↦ f ω ξ)) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro ω hω
  ring

theorem expect_indicator_mul (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A]
    (c : ℚ) :
    μ.expect (fun ω ↦ if A ω then c else 0) = μ.prob A * c := by
  simp only [expect, prob]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h]

theorem expect_ite (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A]
    (c d : ℚ) :
    μ.expect (fun ω ↦ if A ω then c else d) =
      μ.prob A * c + (1 - μ.prob A) * d := by
  have hfun : (fun ω ↦ if A ω then c else d) =
      (fun ω ↦ d + if A ω then c - d else 0) := by
    funext ω
    by_cases h : A ω <;> simp [h]
  rw [hfun, μ.expect_add, μ.expect_const,
    μ.expect_indicator_mul A (c - d)]
  ring

theorem expect_mono {f g : Ω → ℚ} (μ : FiniteLaw Ω)
    (hfg : ∀ ω, f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (μ.weight_nonneg ω)

/-- A pointwise nonnegative payoff has nonnegative finite expectation. -/
theorem expect_nonneg {f : Ω → ℚ} (μ : FiniteLaw Ω)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  unfold expect
  exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (μ.weight_nonneg ω) (hf ω)

theorem expect_congr {f g : Ω → ℚ} (μ : FiniteLaw Ω)
    (hfg : ∀ ω, f ω = g ω) : μ.expect f = μ.expect g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω hω
  rw [hfg ω]

/-- Reversal of three nested finite expectations. -/
theorem expect_reverse_three {Ξ Ψ : Type*} [Fintype Ξ] [Fintype Ψ]
    (mu : FiniteLaw Ω) (nu : FiniteLaw Ξ) (xi : FiniteLaw Ψ)
    (f : Ω → Ξ → Ψ → ℚ) :
    mu.expect (fun a ↦ nu.expect (fun b ↦ xi.expect (fun c ↦ f a b c))) =
      xi.expect (fun c ↦ nu.expect (fun b ↦
        mu.expect (fun a ↦ f a b c))) := by
  calc
    mu.expect (fun a ↦ nu.expect (fun b ↦ xi.expect (fun c ↦ f a b c))) =
        nu.expect (fun b ↦ mu.expect (fun a ↦ xi.expect (fun c ↦ f a b c))) :=
      expect_comm mu nu _
    _ = nu.expect (fun b ↦ xi.expect (fun c ↦
        mu.expect (fun a ↦ f a b c))) := by
      apply nu.expect_congr
      intro b
      exact expect_comm mu xi _
    _ = xi.expect (fun c ↦ nu.expect (fun b ↦
        mu.expect (fun a ↦ f a b c))) :=
      expect_comm nu xi _

/-- Reversal of four nested finite expectations. -/
theorem expect_reverse_four {Ξ Ψ Χ : Type*}
    [Fintype Ξ] [Fintype Ψ] [Fintype Χ]
    (mu : FiniteLaw Ω) (nu : FiniteLaw Ξ) (xi : FiniteLaw Ψ)
    (zeta : FiniteLaw Χ) (f : Ω → Ξ → Ψ → Χ → ℚ) :
    mu.expect (fun a ↦ nu.expect (fun b ↦
        xi.expect (fun c ↦ zeta.expect (fun d ↦ f a b c d)))) =
      zeta.expect (fun d ↦ xi.expect (fun c ↦
        nu.expect (fun b ↦ mu.expect (fun a ↦ f a b c d)))) := by
  calc
    mu.expect (fun a ↦ nu.expect (fun b ↦
        xi.expect (fun c ↦ zeta.expect (fun d ↦ f a b c d)))) =
        nu.expect (fun b ↦ mu.expect (fun a ↦
          xi.expect (fun c ↦ zeta.expect (fun d ↦ f a b c d)))) :=
      expect_comm mu nu _
    _ = nu.expect (fun b ↦ xi.expect (fun c ↦
        mu.expect (fun a ↦ zeta.expect (fun d ↦ f a b c d)))) := by
      apply nu.expect_congr
      intro b
      exact expect_comm mu xi _
    _ = nu.expect (fun b ↦ xi.expect (fun c ↦
        zeta.expect (fun d ↦ mu.expect (fun a ↦ f a b c d)))) := by
      apply nu.expect_congr
      intro b
      apply xi.expect_congr
      intro c
      exact expect_comm mu zeta _
    _ = zeta.expect (fun d ↦ xi.expect (fun c ↦
        nu.expect (fun b ↦ mu.expect (fun a ↦ f a b c d)))) := by
      exact expect_reverse_three nu xi zeta
        (fun b c d ↦ mu.expect (fun a ↦ f a b c d))

@[simp] theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ ↦ True) = 1 := by
  simp [prob, expect, μ.weight_sum]

@[simp] theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ ↦ False) = 0 := by
  simp [prob, expect]

theorem prob_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A] :
    0 ≤ μ.prob A := by
  exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (μ.weight_nonneg ω) (by positivity)

theorem prob_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) [DecidablePred A] :
    μ.prob A ≤ 1 := by
  rw [← μ.weight_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : A ω <;> simp [h, μ.weight_nonneg ω]

/-- An atom cap bounds an event by its cardinality times that cap. -/
theorem prob_le_card_mul (μ : FiniteLaw Ω) (A : Ω → Prop)
    [DecidablePred A] (c : ℚ) (hcap : ∀ ω, μ.weight ω ≤ c) :
    μ.prob A ≤ (Fintype.card {ω : Ω // A ω} : ℚ) * c := by
  classical
  unfold prob expect
  calc
    (∑ ω, μ.weight ω * if A ω then 1 else 0) ≤
        ∑ ω, if A ω then c else 0 := by
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hA : A ω
          · simpa [hA] using hcap ω
          · simp [hA]
    _ = (Fintype.card {ω : Ω // A ω} : ℚ) * c := by
          rw [Finset.sum_ite]
          simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul]
          rw [Fintype.card_subtype]

@[simp] theorem prob_singleton [DecidableEq Ω] (μ : FiniteLaw Ω) (a : Ω) :
    μ.prob (fun ω ↦ ω = a) = μ.weight a := by
  unfold prob expect
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

theorem prob_congr (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (hAB : ∀ ω, A ω ↔ B ω) :
    μ.prob A = μ.prob B := by
  unfold prob expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp_all

/-- The uniform law on a nonempty finite type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight := fun _ ↦ (Fintype.card Ω : ℚ)⁻¹
  weight_nonneg := by intro; positivity
  weight_sum := by
    simp [Fintype.card_ne_zero]

@[simp] theorem uniform_weight (Ω : Type*) [Fintype Ω] [Nonempty Ω] (ω : Ω) :
    (uniform Ω).weight ω = (Fintype.card Ω : ℚ)⁻¹ := rfl

/-- Under the uniform law, probability is exact cardinality divided by the
ambient cardinality. -/
theorem uniform_prob_eq_card (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] :
    (uniform Ω).prob A =
      (Fintype.card {ω : Ω // A ω} : ℚ) / Fintype.card Ω := by
  classical
  change (∑ ω : Ω, (Fintype.card Ω : ℚ)⁻¹ *
      (if A ω then 1 else 0)) = _
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [mul_one, mul_zero, Finset.sum_const_zero]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_subtype]
  field_simp
  ring

end FiniteLaw
end Erdos7
