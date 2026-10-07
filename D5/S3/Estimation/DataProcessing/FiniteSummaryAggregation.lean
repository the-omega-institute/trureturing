/- GID: D5/S3/Estimation/DataProcessing/FiniteSummaryAggregation
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/FiniteSummaryAggregation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Combination]
   utility: none
   digest: Finite history fibers aggregate lawful convex rows and conserve incoming summary mass. -/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

open Finset
open scoped BigOperators Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Estimation.DataProcessing.FiniteSummaryAggregation

variable (S : ℕ → Type*) (H : (k : ℕ) → S k → Type*)
  (A : (k : ℕ) → S k → Type*) (X : (k : ℕ) → (s : S k) → A k s → Type*)
  [∀ k, Fintype (S k)] [∀ k s, Fintype (H k s)]
  [∀ k s, Fintype (A k s)]
  [∀ k s i, Fintype (X k s i)]

/-- A layer of the original tree, displayed in its actual summary fibers. -/
abbrev Node (k : ℕ) := Σ s : S k, H k s
/-- An original edge keeps its parent, named legal action and dependent result. -/
abbrev Edge (k : ℕ) := Σ s : S k, Σ h : H k s, Σ i : A k s, X k s i

/-- Public stage, legal names, dependent alphabets and accessible summary update. -/
structure Dynamics (N : ℕ) where
  root : Node S H 0
  action_nonempty : ∀ k, k < N → ∀ s, Nonempty (A k s)
  update : ∀ k (s : S k), (i : A k s) → X k s i → S (k+1)

/-- The one-child special case, without retained auxiliary branching. -/
structure Tree (N : ℕ) extends Dynamics S H A X N where
  extend : ∀ k, k < N → Edge S H A X k ≃ Node S H (k+1)
  public_update : ∀ k (hk : k < N) (e : Edge S H A X k),
    (extend k hk e).1 = update k e.1 e.2.2.1 e.2.2.2

instance {N : ℕ} : Coe (Tree S H A X N) (Dynamics S H A X N) := ⟨Tree.toDynamics⟩

/-- Common arbitrary nonempty convex sets of normalized nonnegative rows. -/
structure RowSets where
  carrier : ∀ k (s : S k) (i : A k s), Set (X k s i → ℝ)
  convex : ∀ k s i, Convex ℝ (carrier k s i)
  nonempty : ∀ k s i, (carrier k s i).Nonempty
  lawful : ∀ k s i q, q ∈ carrier k s i →
    (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1

variable {S H A X}

/-- Source node/selection flows and the actual chosen lawful rows. -/
structure SourceFlow {N : ℕ} (tree : Tree S H A X N) (K : RowSets S A X) where
  mass : ∀ k (s : S k), H k s → ℝ
  select : ∀ k (s : S k), H k s → A k s → ℝ
  row : ∀ k (s : S k), H k s → (i : A k s) → X k s i → ℝ
  mass_nonneg : ∀ k s h, 0 ≤ mass k s h
  select_nonneg : ∀ k s h i, 0 ≤ select k s h i
  row_mem : ∀ k s h i, row k s h i ∈ K.carrier k s i
  root_mass : ∀ s h, mass 0 s h = if (⟨s,h⟩ : Node S H 0) = tree.root then 1 else 0
  select_sum : ∀ k, k < N → ∀ s h, ∑ i, select k s h i = mass k s h
  child_mass : ∀ k (hk : k < N) (s : S k) (h : H k s) (i : A k s) (x : X k s i),
    let n := tree.extend k hk ⟨s,h,i,x⟩
    mass (k+1) n.1 n.2 = select k s h i * row k s h i x

/-- A conserved finite flow, derived from an actual source partition. -/
structure Flow {N : ℕ} (tree : Dynamics S H A X N) (K : RowSets S A X) where
  mass : ∀ k (s : S k), H k s → ℝ
  select : ∀ k (s : S k), H k s → A k s → ℝ
  row : ∀ k (s : S k), H k s → (i : A k s) → X k s i → ℝ
  mass_nonneg : ∀ k s h, 0 ≤ mass k s h
  select_nonneg : ∀ k s h i, 0 ≤ select k s h i
  row_mem : ∀ k s h i, row k s h i ∈ K.carrier k s i
  root_mass : ∀ s h, mass 0 s h = if (⟨s,h⟩ : Node S H 0) = tree.root then 1 else 0
  select_sum : ∀ k, k < N → ∀ s h, ∑ i, select k s h i = mass k s h
  incoming : ∀ k, k < N → ∀ t,
    (∑ h, mass (k+1) t h) = ∑ s, ∑ i, ∑ x,
      if tree.update k s i x = t then (∑ h, select k s h i * row k s h i x) else 0

private theorem fiber_sum {U : Type*} {V : U → Type*}
    [Fintype U] [∀ u, Fintype (V u)] (m : (Σ u, V u) → ℝ) (u : U) :
    (∑ n : Σ u, V u, if n.1 = u then m n else 0) = ∑ v, m ⟨u,v⟩ := by
  classical
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ v : U, if v = u then (∑ w : V v, m ⟨v,w⟩) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = u <;> simp [hv]
    _ = _ := by simp

theorem source_incoming_conservation {N : ℕ} {tree : Tree S H A X N} {K : RowSets S A X} (p : SourceFlow tree K) (k : ℕ) (hk : k < N) (t : S (k+1)) :
    (∑ h, p.mass (k+1) t h) =
      ∑ s, ∑ i, ∑ x, if tree.update k s i x = t then (∑ h, p.select k s h i * p.row k s h i x) else 0 := by
  classical
  calc
    (∑ h, p.mass (k+1) t h) = ∑ n : Node S H (k+1),
        if n.1 = t then p.mass (k+1) n.1 n.2 else 0 :=
      (fiber_sum (fun n => p.mass (k+1) n.1 n.2) t).symm
    _ = ∑ e : Edge S H A X k,
        if (tree.extend k hk e).1 = t then
          p.mass (k+1) (tree.extend k hk e).1 (tree.extend k hk e).2 else 0 :=
      ((tree.extend k hk).sum_comp _).symm
    _ = ∑ s, ∑ h : H k s, ∑ i, ∑ x,
        if tree.update k s i x = t then p.select k s h i * p.row k s h i x else 0 := by
      simp only [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      rw [p.child_mass, tree.public_update]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      by_cases he : tree.update k s i x = t <;> simp [he]

def SourceFlow.toFlow {N : ℕ} {tree : Tree S H A X N} {K : RowSets S A X}
    (p : SourceFlow tree K) : Flow tree.toDynamics K where
  mass := p.mass
  select := p.select
  row := p.row
  mass_nonneg := p.mass_nonneg
  select_nonneg := p.select_nonneg
  row_mem := p.row_mem
  root_mass := p.root_mass
  select_sum := p.select_sum
  incoming := source_incoming_conservation p

instance {N : ℕ} {tree : Tree S H A X N} {K : RowSets S A X} :
    Coe (SourceFlow tree K) (Flow tree.toDynamics K) := ⟨SourceFlow.toFlow⟩

variable {N : ℕ} {tree : Dynamics S H A X N} {K : RowSets S A X}

def nodeMass (p : Flow tree K) (k : ℕ) (s : S k) : ℝ := ∑ h, p.mass k s h
def selectionMass (p : Flow tree K) (k : ℕ) (s : S k) (i : A k s) : ℝ :=
  ∑ h, p.select k s h i
def resultMass (p : Flow tree K) (k : ℕ) (s : S k) (i : A k s) (x : X k s i) : ℝ :=
  ∑ h, p.select k s h i * p.row k s h i x

def scheduler (p : Flow tree K) (k : ℕ) (s : S k) (i : A k s) : ℝ :=
  if nodeMass p k s = 0 then 1 / Fintype.card (A k s)
  else selectionMass p k s i / nodeMass p k s

/-- A null selection uses an actual member of its legal set. -/
def resultRow (p : Flow tree K) (k : ℕ) (s : S k) (i : A k s) : X k s i → ℝ :=
  if selectionMass p k s i = 0 then (K.nonempty k s i).choose
  else Finset.univ.centerMass (fun h => p.select k s h i) (fun h => p.row k s h i)

theorem incoming_conservation (p : Flow tree K) (k : ℕ) (hk : k < N) (t : S (k+1)) :
    nodeMass p (k+1) t =
      ∑ s, ∑ i, ∑ x, if tree.update k s i x = t then resultMass p k s i x else 0 :=
  p.incoming k hk t

private theorem mass_nonneg (p : Flow tree K) (k : ℕ) (s : S k) :
    0 ≤ nodeMass p k s := Finset.sum_nonneg fun h _ => p.mass_nonneg k s h

private theorem selection_nonneg (p : Flow tree K) (k : ℕ) (s : S k) (i : A k s) :
    0 ≤ selectionMass p k s i := Finset.sum_nonneg fun h _ => p.select_nonneg k s h i

private theorem selection_sum (p : Flow tree K) (k : ℕ) (hk : k < N) (s : S k) :
    ∑ i, selectionMass p k s i = nodeMass p k s := by
  unfold selectionMass nodeMass
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun h _ => p.select_sum k hk s h)

private theorem selection_zero (p : Flow tree K) (k : ℕ) (hk : k < N) (s : S k)
    (hm : nodeMass p k s = 0) (i : A k s) : selectionMass p k s i = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => selection_nonneg p k s i)).mp
    ((selection_sum p k hk s).trans hm) i (Finset.mem_univ i)

theorem normalized_rows (p : Flow tree K) (k : ℕ) (hk : k < N) (s : S k) :
    ((∀ i, 0 ≤ scheduler p k s i) ∧ ∑ i, scheduler p k s i = 1) ∧
      ∀ i, resultRow p k s i ∈ K.carrier k s i := by
  classical
  letI := tree.action_nonempty k hk s
  constructor
  · by_cases hm : nodeMass p k s = 0
    · simp only [scheduler, hm, if_true]
      exact ⟨fun i => by positivity, by simp [Fintype.card_ne_zero]⟩
    · simp only [scheduler, hm, if_false]
      exact ⟨fun i => div_nonneg (selection_nonneg p k s i) (mass_nonneg p k s), by
        rw [← Finset.sum_div, selection_sum p k hk s, div_self hm]⟩
  · intro i
    by_cases hf : selectionMass p k s i = 0
    · simpa [resultRow, hf] using (K.nonempty k s i).choose_spec
    · simp only [resultRow, hf, if_false]
      exact (K.convex k s i).centerMass_mem (fun h _ => p.select_nonneg k s h i)
        (lt_of_le_of_ne (selection_nonneg p k s i) (Ne.symm hf))
        (fun h _ => p.row_mem k s h i)

theorem weighted_rows (p : Flow tree K) (k : ℕ) (hk : k < N) (s : S k) :
    (∀ i, nodeMass p k s * scheduler p k s i = selectionMass p k s i) ∧
      ∀ i x, selectionMass p k s i * resultRow p k s i x = resultMass p k s i x := by
  classical
  constructor
  · intro i
    by_cases hm : nodeMass p k s = 0
    · simp [hm, selection_zero p k hk s hm i]
    · simp only [scheduler, hm, if_false]
      field_simp
  · intro i x
    by_cases hf : selectionMass p k s i = 0
    · have hz (h : H k s) : p.select k s h i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun h _ => p.select_nonneg k s h i)).mp
          hf h (Finset.mem_univ h)
      simp [hf, resultMass, hz]
    · simp only [resultRow, hf, if_false, Finset.centerMass, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      change selectionMass p k s i * ((selectionMass p k s i)⁻¹ * resultMass p k s i x) = _
      rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

/-- The summary policy law is generated recursively, independently of the prescribed masses. -/
def policyMass (p : Flow tree K) : (k : ℕ) → S k → ℝ
  | 0, s => if s = tree.root.1 then 1 else 0
  | k+1, t => ∑ s, ∑ i, ∑ x,
      if tree.update k s i x = t then
        policyMass p k s * scheduler p k s i * resultRow p k s i x else 0

theorem recursive_mass (p : Flow tree K) (k : ℕ) (hk : k ≤ N) (s : S k) :
    policyMass p k s = nodeMass p k s := by
  classical
  induction k with
  | zero =>
    change (if s = tree.root.1 then 1 else 0) = ∑ h, p.mass 0 s h
    simp_rw [p.root_mass]
    by_cases hs : s = tree.root.1
    · subst s
      have he (h : H 0 tree.root.1) :
          (⟨tree.root.1,h⟩ : Node S H 0) = tree.root ↔ h = tree.root.2 := by
        exact ⟨fun he => eq_of_heq (Sigma.mk.inj he).2, fun he => by subst h; rfl⟩
      simp only [he, if_true]
      simp
    · have hn (h : H 0 s) : (⟨s,h⟩ : Node S H 0) ≠ tree.root := by
        intro he
        exact hs (congrArg Sigma.fst he)
      simp [hs, hn]
  | succ k ih =>
    rw [policyMass, incoming_conservation p k (by omega)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    rw [ih (by omega), (weighted_rows p k (by omega) t).1 i,
      (weighted_rows p k (by omega) t).2 i x]


/-- Compatible actual fine successors: pre-result records and post-result
records depend on their parent and actual named action/result. -/
abbrev FineEdge (P : ∀ k (s : S k), H k s → A k s → Type*)
    (R : ∀ k (s : S k) (h : H k s) (i : A k s), P k s h i → X k s i → Type*)
    (k : ℕ) := Σ s : S k, Σ h : H k s, Σ i : A k s,
      Σ r : P k s h i, Σ x : X k s i, R k s h i r x

/-- A finite actual archive tree. Empty compatible fibers are allowed. -/
structure ArchiveTree (S : ℕ → Type*) (H : (k : ℕ) → S k → Type*)
    (A : (k : ℕ) → S k → Type*)
    (X : (k : ℕ) → (s : S k) → A k s → Type*)
    [∀ k, Fintype (S k)] [∀ k s, Fintype (H k s)]
    [∀ k s, Fintype (A k s)] [∀ k s i, Fintype (X k s i)]
    (N : ℕ) extends Dynamics S H A X N where
  Pre : ∀ k (s : S k), H k s → A k s → Type
  preFintype : ∀ k s h i, Fintype (Pre k s h i)
  Post : ∀ k (s : S k) (h : H k s) (i : A k s), Pre k s h i → X k s i → Type
  postFintype : ∀ k s h i r x, Fintype (Post k s h i r x)
  extend : ∀ k, k < N → FineEdge (S := S) (H := H) (A := A) (X := X) Pre Post k ≃
    Node S H (k+1)
  public_update : ∀ k (hk : k < N) (e : FineEdge
      (S := S) (H := H) (A := A) (X := X) Pre Post k),
    (extend k hk e).1 = update k e.1 e.2.2.1 e.2.2.2.2.1

attribute [instance] ArchiveTree.preFintype ArchiveTree.postFintype

/-- Raw source masses at the F archive, actual scheduler branches at G,
and the lawful G-conditional result row. The post-result partition is local
at each actual branch/result; no summary incoming balance is assumed. -/
structure ArchiveFlow {N : ℕ} (tree : ArchiveTree S H A X N) (K : RowSets S A X) where
  mass : ∀ k (s : S k), H k s → ℝ
  select : ∀ k (s : S k) (h : H k s) (i : A k s), tree.Pre k s h i → ℝ
  row : ∀ k (s : S k) (h : H k s) (i : A k s), tree.Pre k s h i → X k s i → ℝ
  mass_nonneg : ∀ k s h, 0 ≤ mass k s h
  select_nonneg : ∀ k s h i r, 0 ≤ select k s h i r
  row_mem : ∀ k s h i r, row k s h i r ∈ K.carrier k s i
  root_mass : ∀ s h, mass 0 s h = if (⟨s,h⟩ : Node S H 0) = tree.root then 1 else 0
  select_sum : ∀ k, k < N → ∀ s h,
    (∑ i, ∑ r, select k s h i r) = mass k s h
  partition : ∀ k (hk : k < N) s h i r x,
    (∑ t, mass (k+1) (tree.extend k hk ⟨s,h,i,r,x,t⟩).1
      (tree.extend k hk ⟨s,h,i,r,x,t⟩).2) = select k s h i r * row k s h i r x

variable {atree : ArchiveTree S H A X N}

def preSelection (p : ArchiveFlow atree K) (k : ℕ) (s : S k) (h : H k s) (i : A k s) : ℝ :=
  ∑ r, p.select k s h i r

def preRow (p : ArchiveFlow atree K) (k : ℕ) (s : S k) (h : H k s) (i : A k s) :
    X k s i → ℝ :=
  if preSelection p k s h i = 0 then (K.nonempty k s i).choose
  else Finset.univ.centerMass (p.select k s h i) (p.row k s h i)

private theorem pre_nonneg (p : ArchiveFlow atree K) (k : ℕ) (s : S k) (h : H k s)
    (i : A k s) : 0 ≤ preSelection p k s h i :=
  Finset.sum_nonneg (fun r _ => p.select_nonneg k s h i r)

private theorem pre_lawful (p : ArchiveFlow atree K) (k : ℕ) (s : S k) (h : H k s)
    (i : A k s) : preRow p k s h i ∈ K.carrier k s i := by
  by_cases hf : preSelection p k s h i = 0
  · simpa [preRow, hf] using (K.nonempty k s i).choose_spec
  · simp only [preRow, hf, if_false]
    exact (K.convex k s i).centerMass_mem (fun r _ => p.select_nonneg k s h i r)
      (lt_of_le_of_ne (pre_nonneg p k s h i) (Ne.symm hf))
      (fun r _ => p.row_mem k s h i r)

/-- Selection-weighted finite averaging retains the actual G-branch result mass,
including null and empty branch fibers. -/
theorem pre_weighted (p : ArchiveFlow atree K) (k : ℕ) (s : S k) (h : H k s)
    (i : A k s) (x : X k s i) :
    preSelection p k s h i * preRow p k s h i x =
      ∑ r, p.select k s h i r * p.row k s h i r x := by
  by_cases hf : preSelection p k s h i = 0
  · have hz (r : atree.Pre k s h i) : p.select k s h i r = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => p.select_nonneg k s h i r)).mp
        hf r (Finset.mem_univ r)
    simp [hf, hz]
  · simp only [preRow, hf, if_false, Finset.centerMass, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    change preSelection p k s h i * ((preSelection p k s h i)⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]

/-- Every actual child appears once; summing only compatible post-records,
then actual pre-records, derives the summary incoming equation. -/
theorem archive_incoming_conservation (p : ArchiveFlow atree K) (k : ℕ) (hk : k < N)
    (u : S (k+1)) :
    (∑ h, p.mass (k+1) u h) = ∑ s, ∑ i, ∑ x,
      if atree.update k s i x = u then
        (∑ h, ∑ r, p.select k s h i r * p.row k s h i r x) else 0 := by
  classical
  calc
    _ = ∑ n : Node S H (k+1), if n.1 = u then p.mass (k+1) n.1 n.2 else 0 :=
      (fiber_sum (fun n => p.mass (k+1) n.1 n.2) u).symm
    _ = ∑ e : FineEdge (S := S) (H := H) (A := A) (X := X) atree.Pre atree.Post k,
        if (atree.extend k hk e).1 = u then
          p.mass (k+1) (atree.extend k hk e).1 (atree.extend k hk e).2 else 0 :=
      ((atree.extend k hk).sum_comp _).symm
    _ = ∑ s, ∑ h : H k s, ∑ i, ∑ r : atree.Pre k s h i, ∑ x,
        if atree.update k s i x = u then p.select k s h i r * p.row k s h i r x else 0 := by
      simp only [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [atree.public_update]
      by_cases he : atree.update k s i x = u
      · simp only [he, if_true]
        exact p.partition k hk s h i r x
      · simp [he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [Finset.sum_comm (f := fun r x =>
        if atree.update k s i x = u then p.select k s _ i r * p.row k s _ i r x else 0)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      by_cases he : atree.update k s i x = u <;> simp [he]

/-- Derived input to the same fresh interpreter; original archive nodes are
unchanged, and branch rows are averaged from their actual selection masses. -/
def ArchiveFlow.toFlow (p : ArchiveFlow atree K) : Flow atree.toDynamics K where
  mass := p.mass
  select := preSelection p
  row := preRow p
  mass_nonneg := p.mass_nonneg
  select_nonneg := pre_nonneg p
  row_mem := pre_lawful p
  root_mass := p.root_mass
  select_sum := p.select_sum
  incoming k hk u := by
    simpa only [pre_weighted] using archive_incoming_conservation p k hk u

instance : Coe (ArchiveFlow atree K) (Flow atree.toDynamics K) := ⟨ArchiveFlow.toFlow⟩

#print axioms archive_incoming_conservation
#print axioms pre_weighted

end D5.S3.Estimation.DataProcessing.FiniteSummaryAggregation
