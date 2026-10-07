/- GID: D5/S3/Arith/Lattices/Klartag/Walk/Chain
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/Chain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

set_option linter.unusedSectionVars false

namespace D5.S3.Arith.Lattices.Klartag.Walk.Chain

open scoped RealInnerProductSpace
open Module
open Submodule
open Finset
open Metric

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

/-- `kSet q W = {A | ∀ i ∈ W, 1 ≤ ⟪A, q i⟫}`.  With `q x = x ⊗ x` this is Klartag's set of
`L`-free matrices (p. 6, eq. 9): `E_A = {x | ⟪A x, x⟫ < 1}` misses every `x` with `q x` a
constraint. -/
def kSet (q : ι → E) (W : Finset ι) : Set E := {A | ∀ i ∈ W, (1 : ℝ) ≤ ⟪A, q i⟫}

/-- If `K_L` is nonempty then no constraint vector vanishes (`⟪A, 0⟫ = 0 < 1`). -/
theorem q_ne_zero_of_nonempty {q : ι → E} {W : Finset ι} {A : E} (hA : A ∈ kSet q W)
    {i : ι} (hi : i ∈ W) : q i ≠ 0 := by
  intro h
  have := hA i hi
  rw [h, inner_zero_right] at this
  linarith

/-- `p` is *the* projection of `u` onto `K`: `p ∈ K` and `K` lies in the half-space through `p`
orthogonal to `u - p`. -/
def IsProjOn (K : Set E) (u p : E) : Prop := p ∈ K ∧ ∀ w ∈ K, ⟪u - p, w - p⟫ ≤ (0 : ℝ)

theorem IsProjOn.mem {K : Set E} {u p : E} (h : IsProjOn K u p) : p ∈ K := h.1

/-- The projection onto a convex set is unique. -/
theorem IsProjOn.eq {K : Set E} {u p p' : E} (h : IsProjOn K u p) (h' : IsProjOn K u p') :
    p = p' := by
  have h1 : ⟪u - p, p' - p⟫ ≤ (0 : ℝ) := h.2 _ h'.1
  have h2 : ⟪u - p', p - p'⟫ ≤ (0 : ℝ) := h'.2 _ h.1
  have hid : ⟪p' - p, p' - p⟫ = ⟪u - p, p' - p⟫ + ⟪u - p', p - p'⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    linarith [real_inner_comm u p, real_inner_comm u p', real_inner_comm p p']
  rw [real_inner_self_eq_norm_sq] at hid
  have hz : ‖p' - p‖ = 0 := by nlinarith [norm_nonneg (p' - p)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 hz)).symm

end Basic

section Free

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

/-- The **free subspace** `F(C) = {B | ∀ i ∈ C, ⟪B, q i⟫ = 0}` (Klartag eq. 13). -/
def freeSub (q : ι → E) (C : Finset ι) : Submodule ℝ E where
  carrier := {B | ∀ i ∈ C, ⟪B, q i⟫ = (0 : ℝ)}
  add_mem' := by
    intro a b ha hb i hi
    rw [inner_add_left, ha i hi, hb i hi, add_zero]
  zero_mem' := by intro i _; rw [inner_zero_left]
  smul_mem' := by
    intro c a ha i hi
    rw [real_inner_smul_left, ha i hi, mul_zero]

@[simp] theorem mem_freeSub {q : ι → E} {C : Finset ι} {B : E} :
    B ∈ freeSub q C ↔ ∀ i ∈ C, ⟪B, q i⟫ = (0 : ℝ) := Iff.rfl

/-- `F(C)` is the orthogonal complement of the span of the active constraints. -/
theorem freeSub_eq_orthogonal (q : ι → E) (C : Finset ι) :
    freeSub q C = (span ℝ (q '' (C : Set ι)))ᗮ := by
  ext B
  rw [mem_freeSub, Submodule.mem_orthogonal]
  constructor
  · intro hB u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; rw [real_inner_comm]; exact hB i hi
    | zero => rw [inner_zero_left]
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  · intro hB i hi
    rw [real_inner_comm]
    exact hB (q i) (Submodule.subset_span ⟨i, hi, rfl⟩)

variable [FiniteDimensional ℝ E]

section Drop
variable [DecidableEq ι]

end Drop

/-- `dim F(C) ≥ dim E - |q(C)|`: Klartag's `N_t ≥ n(n+1)/2 - |∂E_t ∩ L|/2` (p. 16).  Counting
the *image* `q '' C` rather than `C` itself is what supplies the paper's factor `1/2`, since
`q x = x ⊗ x = q (-x)` identifies the antipodal pairs of contact points. -/
theorem finrank_freeSub_ge (q : ι → E) (C : Finset ι) :
    finrank ℝ E - (q '' (C : Set ι)).ncard ≤ finrank ℝ (freeSub q C) := by
  classical
  have himg : q '' (C : Set ι) = ((C.image q : Finset E) : Set E) := by
    rw [Finset.coe_image]
  have hcard : (q '' (C : Set ι)).ncard = (C.image q).card := by
    rw [himg, Set.ncard_coe_finset]
  have hspan : finrank ℝ (span ℝ (q '' (C : Set ι))) ≤ (C.image q).card := by
    rw [himg]; exact finrank_span_finset_le_card (C.image q)
  have hadd : finrank ℝ (span ℝ (q '' (C : Set ι)))
      + finrank ℝ (span ℝ (q '' (C : Set ι)))ᗮ = finrank ℝ E :=
    Submodule.finrank_add_finrank_orthogonal _
  rw [freeSub_eq_orthogonal, hcard]
  omega

/-- The crude form of `finrank_freeSub_ge`, without the antipodal saving. -/
theorem finrank_freeSub_ge_card (q : ι → E) (C : Finset ι) :
    finrank ℝ E - C.card ≤ finrank ℝ (freeSub q C) := by
  have h := finrank_freeSub_ge q C
  have hle : (q '' (C : Set ι)).ncard ≤ C.card := by
    have := Set.ncard_image_le (s := (C : Set ι)) (f := q) C.finite_toSet
    rwa [Set.ncard_coe_finset] at this
  omega

end Free

section Process

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]

/-- The window constraints broken by `A'`. -/
noncomputable def violated (q : ι → E) (W : Finset ι) (A' : E) : Finset ι :=
  W.filter (fun i => ⟪A', q i⟫ < (1 : ℝ))

theorem mem_violated {q : ι → E} {W : Finset ι} {A' : E} {i : ι} :
    i ∈ violated q W A' ↔ i ∈ W ∧ ⟪A', q i⟫ < (1 : ℝ) := by
  simp [violated]

theorem violated_subset (q : ι → E) (W : Finset ι) (A' : E) : violated q W A' ⊆ W :=
  Finset.filter_subset _ _

/-- The **one-sided lift** back into `K_L`: move along the broken constraints only, each by
exactly the amount that makes it tight. -/
noncomputable def lift (q : ι → E) (W : Finset ι) (A' : E) : E :=
  A' + ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) • q i

theorem inner_lift (q : ι → E) (W : Finset ι) (A' : E) (j : ι) :
    ⟪lift q W A', q j⟫ = ⟪A', q j⟫
      + ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  rw [lift, inner_add_left, sum_inner]
  congr 1
  exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _

/-- **The lift lands in `K_L`.**  The only structural input is non-negative correlation of the
constraint vectors, `0 ≤ ⟪q i, q j⟫` — true for `q x = x ⊗ x`, where it is `(x ⬝ᵥ y)² ≥ 0`. -/
theorem lift_mem_kSet {q : ι → E} {W : Finset ι} (A' : E)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) :
    lift q W A' ∈ kSet q W := by
  intro j hj
  have hcoef : ∀ i ∈ violated q W A', 0 ≤ (1 - ⟪A', q i⟫) / ‖q i‖ ^ 2 := by
    intro i hi
    rcases mem_violated.1 hi with ⟨hiW, hilt⟩
    exact div_nonneg (by linarith) (sq_nonneg _)
  rw [inner_lift]
  by_cases hjV : j ∈ violated q W A'
  · have hqj : ‖q j‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hne j hj))
    have hsplit : ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫
        = ((1 - ⟪A', q j⟫) / ‖q j‖ ^ 2) * ⟪q j, q j⟫
          + ∑ i ∈ (violated q W A').erase j, ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ :=
      (Finset.add_sum_erase _ _ hjV).symm
    have hrest : 0 ≤ ∑ i ∈ (violated q W A').erase j,
        ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hi' := Finset.mem_of_mem_erase hi
      exact mul_nonneg (hcoef i hi') (hq i (violated_subset q W A' hi') j hj)
    have hdiag : ((1 - ⟪A', q j⟫) / ‖q j‖ ^ 2) * ⟪q j, q j⟫ = 1 - ⟪A', q j⟫ := by
      rw [real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hqj]
    rw [hsplit, hdiag]
    linarith
  · have h1 : (1 : ℝ) ≤ ⟪A', q j⟫ := by
      by_contra hlt
      exact hjV (mem_violated.2 ⟨hj, not_le.1 hlt⟩)
    have hrest : 0 ≤ ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ :=
      Finset.sum_nonneg fun i hi =>
        mul_nonneg (hcoef i hi) (hq i (violated_subset q W A' hi) j hj)
    linarith

/-- One step of the chain: Gaussian increment inside the free subspace, then the lift, then the
newly broken constraints are adjoined to the active set. -/
noncomputable def stepTo (q : ι → E) (W : Finset ι) (p : E × Finset ι) (x : E) : E × Finset ι :=
  (lift q W (p.1 + (freeSub q p.2).starProjection x),
    p.2 ∪ violated q W (p.1 + (freeSub q p.2).starProjection x))

/-- **The chain** `(A_k, C_k)`, driven by an arbitrary sequence `ξ`.  Klartag's Proposition 2.3. -/
noncomputable def chain (q : ι → E) (W : Finset ι) (A₀ : E) {Ω : Type*} (ξ : ℕ → Ω → E) :
    ℕ → Ω → E × Finset ι
  | 0, _ => (A₀, ∅)
  | k + 1, ω => stepTo q W (chain q W A₀ ξ k ω) (ξ k ω)

variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

@[simp] theorem chain_zero (ω : Ω) : chain q W A₀ ξ 0 ω = (A₀, ∅) := rfl

theorem chain_succ (k : ℕ) (ω : Ω) :
    chain q W A₀ ξ (k + 1) ω = stepTo q W (chain q W A₀ ξ k ω) (ξ k ω) := rfl

/-- **`A_k ∈ K_L` for every `k`** (Klartag Proposition 2.3(C), the `L`-free half). -/
theorem chain_fst_mem_kSet (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ k ω).1 ∈ kSet q W := by
  cases k with
  | zero => exact hA₀
  | succ k => exact lift_mem_kSet _ hq hne

/-- The active set only grows (Klartag Proposition 2.3(D)). -/
theorem chain_snd_subset_succ (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ k ω).2 ⊆ (chain q W A₀ ξ (k + 1) ω).2 := by
  rw [chain_succ]; exact Finset.subset_union_left

theorem chain_snd_mono {k m : ℕ} (h : k ≤ m) (ω : Ω) :
    (chain q W A₀ ξ k ω).2 ⊆ (chain q W A₀ ξ m ω).2 := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hlt | heq
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (chain_snd_subset_succ m ω)
    · rw [heq]

theorem chain_snd_subset_window (k : ℕ) (ω : Ω) : (chain q W A₀ ξ k ω).2 ⊆ W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [chain_succ, stepTo]
    exact Finset.union_subset ih (violated_subset _ _ _)

end Process

section Freezes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]
variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

@[simp] theorem freeSub_empty (q : ι → E) : freeSub q (∅ : Finset ι) = ⊤ := by
  ext B; simp

/-- `N_k = dim F(C_k)`, Klartag's `N_t` (p. 13, eq. 39). -/
noncomputable def freeDim (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    ℕ :=
  finrank ℝ (freeSub q (chain q W A₀ ξ k ω).2)

end Freezes

section NewActive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]
variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

/-- `V_{k+1}`: the constraints newly broken at step `k`. -/
noncomputable def newActive (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    Finset ι :=
  violated q W ((chain q W A₀ ξ k ω).1
    + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω))

theorem chain_snd_succ_eq (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ (k + 1) ω).2 = (chain q W A₀ ξ k ω).2 ∪ newActive q W A₀ ξ k ω := rfl

/-- **A step breaks no already-active constraint.** -/
theorem violated_disjoint {C : Finset ι} {A x : E} (hA : A ∈ kSet q W) :
    Disjoint (violated q W (A + (freeSub q C).starProjection x)) C := by
  rw [Finset.disjoint_left]
  intro i hiV hiC
  obtain ⟨hiW, hilt⟩ := mem_violated.1 hiV
  have hperp : ⟪(freeSub q C).starProjection x, q i⟫ = (0 : ℝ) :=
    (mem_freeSub.1 ((freeSub q C).starProjection_apply_mem x)) i hiC
  rw [inner_add_left, hperp, add_zero] at hilt
  exact absurd (hA i hiW) (not_le.2 hilt)

theorem newActive_disjoint (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    Disjoint (newActive q W A₀ ξ k ω) (chain q W A₀ ξ k ω).2 :=
  violated_disjoint (chain_fst_mem_kSet hA₀ hq hne k ω)

/-- The active set grows by exactly the size of the new block. -/
theorem card_chain_snd_succ (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ (k + 1) ω).2.card
      = (chain q W A₀ ξ k ω).2.card + (newActive q W A₀ ξ k ω).card := by
  rw [chain_snd_succ_eq, Finset.card_union_of_disjoint
    (newActive_disjoint hA₀ hq hne k ω).symm]

/-- **`∑_{k<m} |V_k| = |C_m|`** — the number of terms in the discretisation-error sum. -/
theorem sum_card_newActive (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (m : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range m, (newActive q W A₀ ξ k ω).card = (chain q W A₀ ξ m ω).2.card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, card_chain_snd_succ hA₀ hq hne m ω]

end NewActive

section Measurability

open scoped MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*}

local instance instMeasurableSpaceFinset : MeasurableSpace (Finset ι) := ⊤

local instance instMeasurableSingletonFinset : MeasurableSingletonClass (Finset ι) :=
  ⟨fun _ => trivial⟩

/-- A `Finset`-valued `filter` of measurable predicates is measurable. -/
theorem measurableSet_filter_eq {α : Type*} [MeasurableSpace α] (W s : Finset ι)
    (P : ι → α → Prop) [∀ i, DecidablePred (P i)] (hP : ∀ i, MeasurableSet {a | P i a}) :
    MeasurableSet {a | W.filter (fun i => P i a) = s} := by
  by_cases hs : s ⊆ W
  · have hset : {a | W.filter (fun i => P i a) = s}
        = (⋂ i ∈ (s : Set ι), {a | P i a}) ∩ ⋂ i ∈ ((W \ s : Finset ι) : Set ι), {a | ¬ P i a} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe,
        Finset.mem_sdiff]
      constructor
      · intro hfilt
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · have : i ∈ W.filter (fun i => P i a) := by rw [hfilt]; exact hi
          exact (Finset.mem_filter.1 this).2
        · intro hPi
          have : i ∈ W.filter (fun i => P i a) := Finset.mem_filter.2 ⟨hi.1, hPi⟩
          rw [hfilt] at this
          exact hi.2 this
      · rintro ⟨h1, h2⟩
        ext i
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hiW, hPi⟩
          by_contra hik
          exact h2 i ⟨hiW, hik⟩ hPi
        · intro hi
          exact ⟨hs hi, h1 i hi⟩
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter (Finset.countable_toSet s) fun i _ => hP i)
      (MeasurableSet.biInter (Finset.countable_toSet (W \ s)) fun i _ => (hP i).compl)
  · have hset : {a | W.filter (fun i => P i a) = s} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hfilt
      exact hs (hfilt ▸ Finset.filter_subset _ _)
    rw [hset]
    exact MeasurableSet.empty

variable (q : ι → E) (W : Finset ι)

theorem measurable_violated : Measurable fun A' : E => violated q W A' := by
  classical
  refine measurable_to_countable' fun s => ?_
  have : (fun A' : E => violated q W A') ⁻¹' {s}
      = {A' : E | W.filter (fun i => ⟪A', q i⟫ < (1 : ℝ)) = s} := rfl
  rw [this]
  refine measurableSet_filter_eq W s _ fun i => ?_
  exact measurableSet_lt (by fun_prop) measurable_const

/-- The lift, written as a sum over the whole window: this is the form measurability uses. -/
theorem lift_eq_sum_window (A' : E) :
    lift q W A' = A' + ∑ i ∈ W,
      (if ⟪A', q i⟫ < (1 : ℝ) then (1 - ⟪A', q i⟫) / ‖q i‖ ^ 2 else 0) • q i := by
  rw [lift, violated, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> simp

theorem measurable_lift : Measurable fun A' : E => lift q W A' := by
  simp only [lift_eq_sum_window]
  refine measurable_id.add (Finset.measurable_sum W fun i _ => ?_)
  refine Measurable.smul ?_ measurable_const
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (by fun_prop) measurable_const

theorem measurable_stepTo :
    Measurable fun p : (E × E) × Finset ι => stepTo q W (p.1.1, p.2) p.1.2 := by
  refine measurable_from_prod_countable_left fun C => ?_
  have hA' : Measurable fun p : E × E => p.1 + (freeSub q C).starProjection p.2 :=
    measurable_fst.add (((freeSub q C).starProjection.continuous.measurable).comp measurable_snd)
  exact ((measurable_lift q W).comp hA').prodMk ((measurable_from_top (f := fun s =>
    C ∪ s)).comp ((measurable_violated q W).comp hA'))

variable {q W} {A₀ : E} {ξ : ℕ → Ω → E}

/-- **Adaptedness.**  If `ξ k` is `m (k+1)`-measurable along a monotone family of σ-algebras,
then `(A_k, C_k)` is `m k`-measurable — Klartag Proposition 2.3's "adapted to the filtration". -/
theorem measurable_chain {m : ℕ → MeasurableSpace Ω} (hmono : Monotone m)
    (hξ : ∀ k, Measurable[m (k + 1)] (ξ k)) (k : ℕ) :
    Measurable[m k] fun ω => chain q W A₀ ξ k ω := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have ih' : Measurable[m (k + 1)] fun ω => chain q W A₀ ξ k ω :=
      ih.mono (hmono (Nat.le_succ k)) le_rfl
    have hpair : Measurable[m (k + 1)] fun ω =>
        (((chain q W A₀ ξ k ω).1, ξ k ω), (chain q W A₀ ξ k ω).2) :=
      ((measurable_fst.comp ih').prodMk (hξ k)).prodMk (measurable_snd.comp ih')
    exact (measurable_stepTo q W).comp hpair

variable [MeasurableSpace Ω]

theorem measurable_chain' (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => chain q W A₀ ξ k ω :=
  measurable_chain (m := fun _ => ‹MeasurableSpace Ω›) monotone_const hξ k

/-- `A_k` is measurable. -/
theorem measurable_chain_fst (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => (chain q W A₀ ξ k ω).1 :=
  measurable_fst.comp (measurable_chain' hξ k)

/-- `{ω | i ∈ C_k ω}` is measurable — the form the contact-count expectation
`E |C_N| = ∑_i P(i ∈ C_N)` consumes. -/
theorem measurableSet_mem_active (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (i : ι) :
    MeasurableSet {ω | i ∈ (chain q W A₀ ξ k ω).2} := by
  have h : Measurable fun ω => (chain q W A₀ ξ k ω).2 :=
    measurable_snd.comp (measurable_chain' hξ k)
  have h2 : MeasurableSet ((fun ω => (chain q W A₀ ξ k ω).2) ⁻¹' {s : Finset ι | i ∈ s}) :=
    h trivial
  exact h2

end Measurability

end D5.S3.Arith.Lattices.Klartag.Walk.Chain
