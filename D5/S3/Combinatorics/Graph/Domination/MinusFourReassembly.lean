/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result; premises=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result
   digest: General rooted-component reduction and support replication, applied to the complete connected minus-four family. -/

import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000

namespace D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

open Finset DominatingSetAverage LocalDominatingStemBoundReplication

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordinary dominating subsets, each counted once with its cardinality weight. -/
noncomputable def evaluation (H : SimpleGraph V) (x : ℤ) : ℤ :=
  ∑ S ∈ domSets H, x ^ S.card

private theorem subtype_sum (F : Finset (Finset V)) (x : ℤ) :
    (∑ S : ↥F, x ^ S.val.card) = ∑ S ∈ F, x ^ S.card := by
  classical
  simpa only [Finset.univ_eq_attach] using sum_attach F (fun S => x ^ S.card)

private theorem independent_weights (F : Finset (Finset V)) (x : ℤ) (r : ℕ) :
    (∑ f : Fin r → ↥F, x ^ (∑ i, (f i).val.card)) =
      (∑ S ∈ F, x ^ S.card) ^ r := by
  classical
  simp_rw [← prod_pow_eq_pow_sum]
  rw [← subtype_sum F x]
  exact (Fintype.sum_pow (fun S : ↥F => x ^ S.val.card) r).symm

private theorem hub_weights (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    (∑ S ∈ domSetsAt (replicated H U r) (hub r), x ^ S.card) =
      x * (1 + x) * (∑ S ∈ partialSets H U, x ^ S.card) ^ r := by
  classical
  have he := Fintype.sum_equiv (hubEquiv H U r).symm
    (fun p => x ^ (assemble r true p.1 (fun i => (p.2 i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  rw [subtype_sum] at he
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [assemble_card, pow_add]
  simp only [Bool.false_eq_true, ↓reduceIte, pow_one, pow_zero, mul_one]
  simp_rw [← sum_mul, independent_weights]
  ring

private theorem omitted_weights (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    (∑ S ∈ omittedSets H U r, x ^ S.card) =
      x * (evaluation H x) ^ r := by
  classical
  have he := Fintype.sum_equiv (omittedEquiv H U r).symm
    (fun f => x ^ (assemble r false true (fun i => (f i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  rw [subtype_sum] at he
  rw [← he]
  simp_rw [assemble_card]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, pow_add, pow_one]
  rw [← sum_mul, independent_weights]
  simp only [evaluation, mul_comm]

/-- The two hub cases preserve cardinality weights, including zero copies. -/
private theorem replicated_evaluation (H : SimpleGraph V) (U : Finset V) (r : ℕ) (x : ℤ) :
    evaluation (replicated H U r) x =
      x * (1 + x) * (∑ S ∈ partialSets H U, x ^ S.card) ^ r +
        x * (evaluation H x) ^ r := by
  classical
  rw [← hub_weights, ← omitted_weights]
  exact (sum_filter_add_sum_filter_not (domSets (replicated H U r))
    (fun S => hub r ∈ S) (fun S => x ^ S.card)).symm

private theorem partial_eq_of_leaf (H : SimpleGraph V) (v w : V)
    (hw : Leaf H w) (hvw : H.Adj w v) : partialSets H {v} = domSets H := by
  classical
  apply Subset.antisymm
  · intro S hS
    have hp := (mem_partialSets H {v} S).mp hS
    apply mem_domSets.mpr
    intro a
    by_cases ha : a = v
    · subst a
      have hne : w ≠ v := hvw.ne
      rcases (leaf_dominated_iff hw hvw S).mp (hp w (by simpa using hne)) with h | h
      · exact Or.inr ⟨w, h, hvw.symm⟩
      · exact Or.inl h
    · exact hp a (by simpa using ha)
  · exact domSets_subset_partialSets H {v}

/-- A leaf at the attachment support prevents the hub from creating new partial sets. -/
private theorem support_replication_evaluation (H : SimpleGraph V) (v w : V)
    (hw : Leaf H w) (hvw : H.Adj w v) (r : ℕ) (x : ℤ) :
    evaluation (replicated H {v} r) x = x * (x + 2) * (evaluation H x) ^ r := by
  rw [replicated_evaluation, partial_eq_of_leaf H v w hw hvw]
  unfold evaluation
  ring

/-- Every copied vertex reaches the hub through the specified support. -/
private theorem support_replication_connected (H : SimpleGraph V) (v : V)
    (hH : H.Connected) (r : ℕ) : (replicated H {v} r).Connected := by
  classical
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨hub r, ?_⟩
  intro a
  cases a with
  | inl a =>
    let f : H →g replicated H {v} r := {
      toFun := fun w => Sum.inl (a.1, w)
      map_rel' := fun h => ⟨rfl, h⟩ }
    have hh : (replicated H {v} r).Adj (hub r) (Sum.inl (a.1, v)) :=
      ⟨rfl, mem_singleton_self v⟩
    exact hh.reachable.trans ((hH v a.2).map f)
  | inr a =>
    fin_cases a
    · exact SimpleGraph.Reachable.refl _
    · exact (show (replicated H {v} r).Adj (hub r) (pendant r) from by
        simp [replicated, hub, pendant]).reachable


/-- Data and local graph laws for any finite rooted-component decomposition.
The laws are checker inputs, not claims about the published finite graph. -/
private structure Decomposition where
  n k m : ℕ
  size : Fin m → ℕ
  graph : SimpleGraph (Fin n)
  adjDec : DecidableRel graph.Adj
  labels : (Fin k ⊕ (Σ i : Fin m, Fin (size i))) ≃ Fin n
  root leaf : (i : Fin m) → Fin (size i)
  incidence : Fin m → Finset (Fin k)
  leaf_neighbors : ∀ (i : Fin m) (v : Fin n),
    graph.Adj (labels (.inr ⟨i, leaf i⟩)) v ↔ v = labels (.inr ⟨i, root i⟩)
  root_leaf_edge : ∀ i, graph.Adj (labels (.inr ⟨i, root i⟩)) (labels (.inr ⟨i, leaf i⟩))
  nonroot_neighbors : ∀ (i : Fin m) (v : Fin (size i)), v ≠ root i →
    ∀ w : Fin n, graph.Adj (labels (.inr ⟨i,v⟩)) w →
      ∃ t : Fin (size i), w = labels (.inr ⟨i,t⟩)
  core_neighbors : ∀ (c : Fin k) (v : Fin n),
    graph.Adj (labels (.inl c)) v ↔
      (∃ a : Fin k, v = labels (.inl a) ∧ graph.Adj (labels (.inl c)) (labels (.inl a))) ∨
      ∃ i : Fin m, v = labels (.inr ⟨i,root i⟩) ∧ c ∈ incidence i

private instance (d : Decomposition) : DecidableRel d.graph.Adj := d.adjDec

noncomputable section

namespace Reduction

local notation "branchSize" => d.size
local notation "sourceGraph" => d.graph
local notation "coreLabel" => fun c => d.labels (Sum.inl c)
local notation "branchLabel" => fun i v => d.labels (Sum.inr ⟨i,v⟩)
local notation "labelEquiv" => d.labels
local notation "label_bijective" => d.labels.bijective
local notation "label" => d.labels
local notation "root" => d.root
local notation "leaf" => d.leaf
local notation "rootNeighbors" => d.incidence
local notation "leaf_neighbors" => d.leaf_neighbors
local notation "root_leaf_edge" => d.root_leaf_edge
local notation "nonroot_neighbors" => d.nonroot_neighbors
local notation "core_neighbors" => d.core_neighbors

private def branchGraph (d : Decomposition) (i : Fin d.m) : SimpleGraph (Fin (d.size i)) :=
  d.graph.comap (fun v => d.labels (.inr ⟨i,v⟩))
local notation "branchGraph" => branchGraph d
private instance (d : Decomposition) (i : Fin d.m) : DecidableRel (branchGraph i).Adj :=
  fun _ _ => inferInstanceAs (Decidable (d.graph.Adj _ _))

/-- A computationally transparent form of ordinary internal domination. -/
private def localDominating (d : Decomposition) (i : Fin d.m) (S : Finset (Fin (branchSize i))) : Prop :=
  ∀ v, v ∈ S ∨ ∃ w ∈ S, (branchGraph i).Adj v w


local notation "localDominating" => localDominating d

private instance (d : Decomposition) (i : Fin d.m) (S : Finset (Fin (branchSize i))) : Decidable (localDominating i S) := by
  unfold localDominating
  infer_instance

/-- Root-selected and root-omitted internally dominating configurations. -/
private def message (d : Decomposition) (x : ℤ) (i : Fin d.m) (b : Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin (branchSize i))).powerset,
    if localDominating i S ∧ decide (root i ∈ S) = b then x ^ S.card else 0

/-- The four-cycle is covered by core choices and selected component roots. -/

local notation "message" => message d x

private def coreCovered (d : Decomposition) (Z : Finset (Fin d.k)) (A : Finset (Fin d.m)) : Prop :=
  ∀ c : Fin d.k, c ∈ Z ∨
    (∃ a ∈ Z, sourceGraph.Adj (coreLabel c) (coreLabel a)) ∨
    ∃ i ∈ A, c ∈ rootNeighbors i


local notation "coreCovered" => coreCovered d

private instance (d : Decomposition) (Z : Finset (Fin d.k)) (A : Finset (Fin d.m)) : Decidable (coreCovered Z A) := by
  unfold coreCovered
  infer_instance

/-- The finite core-and-root expression whose exact reassembly bridge is required. -/
private def stateEvaluation (d : Decomposition) (x : ℤ) : ℤ :=
  ∑ Z ∈ (univ : Finset (Fin d.k)).powerset,
    x ^ Z.card *
      ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
        if coreCovered Z A then ∏ i : Fin d.m, message i (decide (i ∈ A)) else 0


local notation "stateEvaluation" => stateEvaluation d x

private def assemble (d : Decomposition) (Z : Finset (Fin d.k)) (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) :
    Finset (Fin d.n) := (Z.disjSum (univ.sigma f)).map labelEquiv.toEmbedding


local notation "assemble" => assemble d

private theorem mem_assemble_core (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) (c : Fin d.k) :
    coreLabel c ∈ assemble Z f ↔ c ∈ Z := by
  rw [assemble, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have he' : label a = label (Sum.inl c) := he
    have hh := label_bijective.1 he'
    subst a
    simpa using ha
  · intro h
    exact ⟨Sum.inl c, by simp [h], rfl⟩


local notation "mem_assemble_core" => mem_assemble_core d

private theorem mem_assemble_branch (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) (i : Fin d.m) (v : Fin (branchSize i)) :
    branchLabel i v ∈ assemble Z f ↔ v ∈ f i := by
  rw [assemble, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have he' : label a = label (Sum.inr ⟨i,v⟩) := he
    have hh := label_bijective.1 he'
    subst a
    simpa using ha
  · intro h
    exact ⟨Sum.inr ⟨i,v⟩, by simp [h], rfl⟩


local notation "mem_assemble_branch" => mem_assemble_branch d

private def coreSlice (d : Decomposition) (S : Finset (Fin d.n)) : Finset (Fin d.k) :=
  univ.filter (fun c => coreLabel c ∈ S)


local notation "coreSlice" => coreSlice d

private def branchSlice (d : Decomposition) (S : Finset (Fin d.n)) (i : Fin d.m) : Finset (Fin (branchSize i)) :=
  univ.filter (fun v => branchLabel i v ∈ S)


local notation "branchSlice" => branchSlice d

private theorem assemble_slices (d : Decomposition) (S : Finset (Fin d.n)) :
    assemble (coreSlice S) (branchSlice S) = S := by
  ext v
  obtain ⟨a, rfl⟩ := labelEquiv.surjective v
  cases a with
  | inl c =>
    change coreLabel c ∈ assemble _ _ ↔ coreLabel c ∈ S
    simpa [coreSlice] using mem_assemble_core (coreSlice S) (branchSlice S) c
  | inr a =>
    change branchLabel a.1 a.2 ∈ assemble _ _ ↔ branchLabel a.1 a.2 ∈ S
    simpa [branchSlice] using mem_assemble_branch (coreSlice S) (branchSlice S) a.1 a.2


local notation "assemble_slices" => assemble_slices d

private theorem coreSlice_assemble (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) : coreSlice (assemble Z f) = Z := by
  ext c
  simp [coreSlice, mem_assemble_core]


local notation "coreSlice_assemble" => coreSlice_assemble d

private theorem branchSlice_assemble (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) (i : Fin d.m) :
    branchSlice (assemble Z f) i = f i := by
  ext v
  simp [branchSlice, mem_assemble_branch]


local notation "branchSlice_assemble" => branchSlice_assemble d

private theorem assemble_card (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) :
    (assemble Z f).card = Z.card + ∑ i, (f i).card := by
  simp [assemble]


local notation "assemble_card" => assemble_card d

private def selectedRoots (d : Decomposition) (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) : Finset (Fin d.m) :=
  univ.filter (fun i => root i ∈ f i)


local notation "selectedRoots" => selectedRoots d

private theorem dominating_assemble_iff (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (branchSize i))) :
    sourceGraph.IsDominating (assemble Z f : Set (Fin d.n)) ↔
      coreCovered Z (selectedRoots f) ∧ ∀ i, localDominating i (f i) := by
  constructor
  · intro h
    constructor
    · intro c
      rcases h (coreLabel c) with hm | ⟨v,hv,ha⟩
      · exact Or.inl ((mem_assemble_core Z f c).mp hm)
      · rcases (core_neighbors c v).mp ha with ⟨a, rfl, hd⟩ | ⟨i, rfl, hi⟩
        · exact Or.inr (Or.inl ⟨a, (mem_assemble_core Z f a).mp hv, hd⟩)
        · exact Or.inr (Or.inr ⟨i, by
            simpa [selectedRoots] using (mem_assemble_branch Z f i (root i)).mp hv, hi⟩)
    · intro i v
      by_cases hr : v = root i
      · subst v
        rcases h (branchLabel i (leaf i)) with hm | ⟨w, hw, ha⟩
        · exact Or.inr ⟨leaf i, (mem_assemble_branch Z f i (leaf i)).mp hm,
            root_leaf_edge i⟩
        · have he := (leaf_neighbors i w).mp ha
          exact Or.inl ((mem_assemble_branch Z f i (root i)).mp (he ▸ hw))
      · rcases h (branchLabel i v) with hm | ⟨w,hw,ha⟩
        · exact Or.inl ((mem_assemble_branch Z f i v).mp hm)
        · obtain ⟨t, rfl⟩ := nonroot_neighbors i v hr w ha
          exact Or.inr ⟨t, (mem_assemble_branch Z f i t).mp hw, ha⟩
  · rintro ⟨hc, hl⟩ v
    obtain ⟨a, rfl⟩ := labelEquiv.surjective v
    cases a with
    | inl c =>
      rcases hc c with hm | ⟨a,hd,ha⟩ | ⟨i,hi,ha⟩
      · exact Or.inl ((mem_assemble_core Z f c).mpr hm)
      · exact Or.inr ⟨coreLabel a, (mem_assemble_core Z f a).mpr hd, ha⟩
      · exact Or.inr ⟨branchLabel i (root i), (mem_assemble_branch Z f i (root i)).mpr
          (by simpa [selectedRoots] using hi), (core_neighbors c _).mpr (Or.inr ⟨i,rfl,ha⟩)⟩
    | inr a =>
      rcases hl a.1 a.2 with hm | ⟨w,hw,ha⟩
      · exact Or.inl ((mem_assemble_branch Z f a.1 a.2).mpr hm)
      · exact Or.inr ⟨branchLabel a.1 w, (mem_assemble_branch Z f a.1 w).mpr hw, ha⟩



local notation "dominating_assemble_iff" => dominating_assemble_iff d

private def choices (d : Decomposition) (i : Fin d.m) (b : Bool) : Finset (Finset (Fin (branchSize i))) :=
  univ.powerset.filter (fun S => localDominating i S ∧ decide (root i ∈ S) = b)


local notation "choices" => choices d

private abbrev Choice (d : Decomposition) (i : Fin d.m) (b : Bool) := ↥(choices i b)


local notation "Choice" => Choice d

private def coreChoices (d : Decomposition) (Z : Finset (Fin d.k)) : Finset (Finset (Fin d.m)) :=
  univ.powerset.filter (coreCovered Z)


local notation "coreChoices" => coreChoices d

private abbrev Valid (d : Decomposition) := Σ Z : Finset (Fin d.k), Σ A : ↥(coreChoices Z),
  ∀ i : Fin d.m, Choice i (decide (i ∈ A.val))


local notation "Valid" => Valid d

private theorem choice_dominating (d : Decomposition) (i : Fin d.m) (b : Bool) (S : Choice i b) :
    localDominating i S.val := (mem_filter.mp S.property).2.1


local notation "choice_dominating" => choice_dominating d

private theorem choice_root (d : Decomposition) (i : Fin d.m) (b : Bool) (S : Choice i b) :
    decide (root i ∈ S.val) = b := (mem_filter.mp S.property).2.2


local notation "choice_root" => choice_root d

private theorem selected_eq (d : Decomposition) {Z : Finset (Fin d.k)} (A : ↥(coreChoices Z))
    (f : ∀ i : Fin d.m, Choice i (decide (i ∈ A.val))) :
    selectedRoots (fun i => (f i).val) = A.val := by
  ext i
  simp only [selectedRoots, mem_filter, mem_univ, true_and]
  exact decide_eq_decide.mp (choice_root i _ (f i))


local notation "selected_eq" => selected_eq d

private def validToDom (d : Decomposition) (p : Valid) : ↥(domSets sourceGraph) := by
  refine ⟨assemble p.1 (fun i => (p.2.2 i).val), mem_domSets.mpr ?_⟩
  apply (dominating_assemble_iff _ _).mpr
  constructor
  · rw [selected_eq p.2.1 p.2.2]
    exact (mem_filter.mp p.2.1.property).2
  · exact fun i => choice_dominating i _ (p.2.2 i)


local notation "validToDom" => validToDom d

private theorem validToDom_injective (d : Decomposition) : Function.Injective validToDom := by
  rintro ⟨Z,A,f⟩ ⟨Z',A',f'⟩ h
  have hs := congrArg Subtype.val h
  change assemble Z (fun i => (f i).val) = assemble Z' (fun i => (f' i).val) at hs
  have hz : Z = Z' := by
    simpa only [coreSlice_assemble] using congrArg coreSlice hs
  subst Z'
  have hf : (fun i => (f i).val) = (fun i => (f' i).val) := by
    funext i
    simpa only [branchSlice_assemble] using congrArg (fun S => branchSlice S i) hs
  have ha : A = A' := by
    apply Subtype.ext
    rw [← selected_eq A f, ← selected_eq A' f', hf]
  subst A'
  have he : f = f' := by
    funext i
    exact Subtype.ext (congrFun hf i)
  subst f'
  rfl


local notation "validToDom_injective" => validToDom_injective d

private theorem validToDom_surjective (d : Decomposition) : Function.Surjective validToDom := by
  intro S
  let Z := coreSlice S.val
  let f := branchSlice S.val
  have hd : coreCovered Z (selectedRoots f) ∧ ∀ i, localDominating i (f i) := by
    apply (dominating_assemble_iff Z f).mp
    dsimp [Z,f]
    rw [assemble_slices]
    exact mem_domSets.mp S.property
  let A : ↥(coreChoices Z) := ⟨selectedRoots f, by simp [coreChoices, hd.1]⟩
  let g : ∀ i, Choice i (decide (i ∈ A.val)) := fun i => ⟨f i, by
    simp [choices, hd.2 i, A, selectedRoots]⟩
  refine ⟨⟨Z,A,g⟩, ?_⟩
  apply Subtype.ext
  exact assemble_slices S.val


local notation "validToDom_surjective" => validToDom_surjective d

private def configEquiv (d : Decomposition) : Valid ≃ ↥(domSets sourceGraph) :=
  Equiv.ofBijective validToDom ⟨validToDom_injective, validToDom_surjective⟩


local notation "configEquiv" => configEquiv d

private theorem choice_sum (d : Decomposition) (x : ℤ) (i : Fin d.m) (b : Bool) :
    (∑ S : Choice i b, x ^ S.val.card) = message i b := by
  classical
  calc
    (∑ S : Choice i b, x ^ S.val.card) =
        ∑ S ∈ choices i b, x ^ S.card := by
      simpa only [Finset.univ_eq_attach] using
        sum_attach (choices i b) (fun S => x ^ S.card)
    _ = message i b := by
      unfold choices message
      rw [sum_filter]


local notation "choice_sum" => choice_sum d x

private theorem choice_product (d : Decomposition) (x : ℤ) (Z : Finset (Fin d.k)) (A : ↥(coreChoices Z)) :
    (∑ f : ∀ i : Fin d.m, Choice i (decide (i ∈ A.val)),
      x ^ (∑ i, (f i).val.card)) =
        ∏ i : Fin d.m, message i (decide (i ∈ A.val)) := by
  classical
  simp_rw [← prod_pow_eq_pow_sum]
  calc
    (∑ f : ∀ i : Fin d.m, Choice i (decide (i ∈ A.val)), ∏ i, x ^ (f i).val.card) =
        ∏ i : Fin d.m, ∑ S : Choice i (decide (i ∈ A.val)), x ^ S.val.card :=
      (Fintype.prod_sum (fun (i : Fin d.m) (S : Choice i (decide (i ∈ A.val))) =>
        x ^ S.val.card)).symm
    _ = _ := by simp_rw [choice_sum]

/-- The exact graph sum is obtained by unique restriction to core and components,
followed by the cardinality-preserving root-state partition. -/

local notation "choice_product" => choice_product d x

private theorem reassembly (d : Decomposition) (x : ℤ) : evaluation sourceGraph x = stateEvaluation := by
  classical
  have hs := Fintype.sum_equiv configEquiv
    (fun p : Valid => x ^ (assemble p.1 (fun i => (p.2.2 i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  have hdom : (∑ S : ↥(domSets sourceGraph), x ^ S.val.card) =
      evaluation sourceGraph x := by
    simpa only [Finset.univ_eq_attach, evaluation] using
      sum_attach (domSets sourceGraph) (fun S => x ^ S.card)
  have hterm (Z : Finset (Fin d.k)) (A : ↥(coreChoices Z)) :
      (∑ f : ∀ i : Fin d.m, Choice i (decide (i ∈ A.val)),
        x ^ (assemble Z (fun i => (f i).val)).card) =
      x ^ Z.card * ∏ i : Fin d.m, message i (decide (i ∈ A.val)) := by
    simp_rw [assemble_card, pow_add]
    rw [← mul_sum, choice_product]
  have hcore (Z : Finset (Fin d.k)) :
      (∑ A : ↥(coreChoices Z), ∏ i : Fin d.m, message i (decide (i ∈ A.val))) =
      ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
        if coreCovered Z A then ∏ i : Fin d.m, message i (decide (i ∈ A)) else 0 := by
    calc
      (∑ A : ↥(coreChoices Z), ∏ i : Fin d.m, message i (decide (i ∈ A.val))) =
          ∑ A ∈ coreChoices Z, ∏ i : Fin d.m, message i (decide (i ∈ A)) := by
        simpa only [Finset.univ_eq_attach] using
          sum_attach (coreChoices Z) (fun A => ∏ i : Fin d.m, message i (decide (i ∈ A)))
      _ = _ := by unfold coreChoices; rw [sum_filter]
  rw [hdom] at hs
  rw [← hs]
  unfold stateEvaluation
  simp only [Fintype.sum_sigma]
  apply sum_congr rfl
  intro Z _
  simp_rw [hterm]
  rw [← mul_sum, hcore]


local notation "reassembly" => reassembly d x


/-- Soundness of arbitrary supplied message values for the same decomposition,
weight, root states and core sum. The actual application must prove both inputs. -/
private theorem zero_of_messages (d : Decomposition) (x : ℤ)
    (table : Fin d.m → Bool → ℤ)
    (hm : ∀ i b, message i b = table i b)
    (hz : (∑ Z ∈ (univ : Finset (Fin d.k)).powerset,
      x ^ Z.card * ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
        if coreCovered Z A then ∏ i : Fin d.m, table i (decide (i ∈ A)) else 0) = 0) :
    evaluation d.graph x = 0 := by
  rw [reassembly]
  unfold stateEvaluation
  simp_rw [hm]
  exact hz

end Reduction

private theorem connected_of_parent {n : ℕ} (H : SimpleGraph (Fin (n+1)))
    (parent : Fin (n+1) → Fin (n+1))
    (parent_edge : ∀ v, v ≠ 0 → H.Adj v (parent v))
    (parent_lower : ∀ v, v ≠ 0 → (parent v).val < v.val) : H.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro v
  have reach : ∀ (t : ℕ) (v : Fin (n+1)), v.val = t → H.Reachable 0 v := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro v hv
      by_cases hzero : v = 0
      · subst v; exact SimpleGraph.Reachable.refl _
      · exact (ih (parent v).val (hv ▸ parent_lower v hzero) (parent v) rfl).trans
          (parent_edge v hzero).symm.reachable
  exact reach v.val v rfl

private theorem evaluation_iso {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (x : ℤ) : evaluation G x = evaluation H x := by
  classical
  unfold evaluation
  rw [← domSets_map e, Finset.sum_map]
  apply sum_congr rfl
  intro S _
  change x ^ S.card = x ^ (S.map e.toEquiv.toEmbedding).card
  rw [card_map]

/-- The complete unbounded-order event follows from the single exact base evaluation.
No base root is assumed elsewhere in this construction. -/
private theorem family_of_root {n : ℕ} (H : SimpleGraph (Fin (n+1)))
    (v w : Fin (n+1)) (hconn : H.Connected) (hleaf : Leaf H w) (hadj : H.Adj w v)
    (x : ℤ) (hbase : evaluation H x = 0) :
    ∀ N : ℕ, ∃ q : ℕ, N < q ∧ ∃ G : SimpleGraph (Fin q),
      G.Connected ∧ ∑ S ∈ domSets G, x ^ S.card = 0 := by
  classical
  intro N
  let r := N + 1
  let R := replicated H {v} r
  let e := Fintype.equivFin (RepVertex r (Fin (n+1)))
  let G := R.map e
  have hn : Fintype.card (RepVertex r (Fin (n+1))) = (n+1) * r + 2 := by
    rw [replicated_card]; simp [Nat.mul_comm]
  refine ⟨Fintype.card (RepVertex r (Fin (n+1))), ?_, G, ?_, ?_⟩
  · rw [hn]; dsimp [r]; omega
  · exact (support_replication_connected H v hconn r).map
      (SimpleGraph.Iso.map e R).toHom e.surjective
  · change evaluation G x = 0
    rw [← evaluation_iso (SimpleGraph.Iso.map e R)]
    change evaluation (replicated H {v} r) x = 0
    rw [support_replication_evaluation H v w hleaf hadj,
      hbase, zero_pow (by dsimp [r]; omega : r ≠ 0), mul_zero]

/-- Factual edge data from Alikhani--Griswold, arXiv:2608.00109v1.
The independently written encoding uses the explicit graph, rather than the branch prose. -/
private def sourceEdges : Finset (Fin 33 × Fin 33) := {
  (0, 1),
  (0, 3),
  (0, 4),
  (0, 12),
  (1, 2),
  (1, 12),
  (1, 18),
  (2, 3),
  (2, 6),
  (2, 8),
  (2, 10),
  (2, 18),
  (2, 21),
  (3, 21),
  (3, 24),
  (4, 5),
  (6, 7),
  (8, 9),
  (10, 11),
  (12, 13),
  (12, 14),
  (12, 15),
  (12, 16),
  (12, 17),
  (18, 19),
  (18, 20),
  (21, 22),
  (21, 23),
  (24, 25),
  (24, 26),
  (26, 27),
  (27, 28),
  (28, 29),
  (28, 31),
  (29, 30),
  (31, 32) }

/-- The actual finite simple undirected source graph on the published labels. -/
private def sourceGraph : SimpleGraph (Fin 33) where
  Adj u v := (u,v) ∈ sourceEdges ∨ (v,u) ∈ sourceEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel sourceGraph.Adj := fun _ _ => inferInstanceAs
  (Decidable (_ ∈ sourceEdges ∨ _ ∈ sourceEdges))

/-- Component sizes after removing the actual four-cycle. -/
private def branchSize : Fin 8 → ℕ := ![2,2,2,2,6,3,3,9]

/-- Each component occupies an interval in the published vertex labels. -/
private def branchStart : Fin 8 → ℕ := ![4,6,8,10,12,18,21,24]

/-- Exact source labels, with no vertices added or discarded. -/
private def branchLabel (i : Fin 8) (v : Fin (branchSize i)) : Fin 33 :=
  ⟨branchStart i + v.val, by have h : ∀ i : Fin 8, branchStart i + branchSize i ≤ 33 := by decide; have := h i; omega⟩

/-- The root is the first vertex of every interval. -/
private def root (i : Fin 8) : Fin (branchSize i) :=
  ⟨0, by fin_cases i <;> decide⟩

/-- Core neighbors of each component root. -/
private def rootNeighbors : Fin 8 → Finset (Fin 4) :=
  ![{0},{2},{2},{2},{0,1},{1,2},{2,3},{3}]

private def parent (v : Fin 33) : Fin 33 :=
  ![0,0,1,0,0,4,2,6,2,8,2,10,0,12,12,12,12,12,1,18,18,2,21,21,3,24,24,26,27,28,29,28,31] v


/-- The complete event: every order threshold is exceeded by a connected graph
whose ordinary domination polynomial vanishes at minus four. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem result : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0 := by
  let labels : (Fin 4 ⊕ (Σ i : Fin 8, Fin (branchSize i))) → Fin 33 := fun a =>
    match a with
    | .inl c => ⟨c.val, by omega⟩
    | .inr v => branchLabel v.1 v.2
  let d : Decomposition := {
    n := 33, k := 4, m := 8, size := branchSize, graph := sourceGraph
    adjDec := instDecidableRelFinOfNatNatAdjSourceGraph
    labels := Equiv.ofBijective labels (by decide)
    root := root
    leaf := fun i => ⟨1, by fin_cases i <;> decide⟩
    incidence := rootNeighbors
    leaf_neighbors := by decide
    root_leaf_edge := by decide
    nonroot_neighbors := by decide
    core_neighbors := by decide }
  let table : Fin 8 → Bool → ℤ := fun i b =>
    if b then ![12,12,12,12,972,-36,-36,-20736] i
    else ![-4,-4,-4,-4,-1024,16,16,5888] i
  have hbase : evaluation sourceGraph (-4) = 0 :=
    Reduction.zero_of_messages d (-4) table (by decide) (by decide)
  apply family_of_root sourceGraph 4 5 ?_ ?_ (by decide) (-4) hbase
  · exact connected_of_parent sourceGraph parent (by decide) (by decide)
  · have hn : ∀ w : Fin 33, sourceGraph.Adj 5 w ↔ w = 4 := by decide
    classical
    exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      ⟨4, (hn 4).mpr rfl, fun w hw => (hn w).mp hw⟩

#print axioms result

end

end D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
