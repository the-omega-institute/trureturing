/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result; instance=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result
   digest: General rooted-component reduction and support replication, applied to the complete connected minus-four family. -/
import D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph
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
structure Decomposition where
  n : ℕ
  k : ℕ
  m : ℕ
  size : Fin m → ℕ
  graph : SimpleGraph (Fin n)
  adjDec : DecidableRel graph.Adj
  labels : (Fin k ⊕ (Σ i : Fin m, Fin (size i))) ≃ Fin n
  root : (i : Fin m) → Fin (size i)
  leaf : (i : Fin m) → Fin (size i)
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

private def coreLabel (d : Decomposition) (c : Fin d.k) : Fin d.n := d.labels (.inl c)
private def branchLabel (d : Decomposition) (i : Fin d.m) (v : Fin (d.size i)) : Fin d.n :=
  d.labels (.inr ⟨i,v⟩)

def branchGraph (d : Decomposition) (i : Fin d.m) : SimpleGraph (Fin (d.size i)) :=
  d.graph.comap (fun v => d.labels (.inr ⟨i,v⟩))
private instance (d : Decomposition) (i : Fin d.m) : DecidableRel ((branchGraph d) i).Adj :=
  fun _ _ => inferInstanceAs (Decidable (d.graph.Adj _ _))

/-- A computationally transparent form of ordinary internal domination. -/
def localDominating (d : Decomposition) (i : Fin d.m) (S : Finset (Fin (d.size i))) : Prop :=
  ∀ v, v ∈ S ∨ ∃ w ∈ S, ((branchGraph d) i).Adj v w

private instance (d : Decomposition) (i : Fin d.m) (S : Finset (Fin (d.size i))) : Decidable ((localDominating d) i S) := by
  unfold localDominating
  infer_instance

/-- Root-selected and root-omitted internally dominating configurations. -/
def message (d : Decomposition) (x : ℤ) (i : Fin d.m) (b : Bool) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin (d.size i))).powerset,
    if (localDominating d) i S ∧ decide (d.root i ∈ S) = b then x ^ S.card else 0

/-- The arbitrary core is covered by core choices and selected component roots. -/
def coreCovered (d : Decomposition) (Z : Finset (Fin d.k)) (A : Finset (Fin d.m)) : Prop :=
  ∀ c : Fin d.k, c ∈ Z ∨
    (∃ a ∈ Z, d.graph.Adj ((coreLabel d) c) ((coreLabel d) a)) ∨
    ∃ i ∈ A, c ∈ d.incidence i

private instance (d : Decomposition) (Z : Finset (Fin d.k)) (A : Finset (Fin d.m)) : Decidable ((coreCovered d) Z A) := by
  unfold coreCovered
  infer_instance

/-- The finite core-and-root expression whose exact reassembly bridge is required. -/
def stateEvaluation (d : Decomposition) (x : ℤ) : ℤ :=
  ∑ Z ∈ (univ : Finset (Fin d.k)).powerset,
    x ^ Z.card *
      ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
        if (coreCovered d) Z A then ∏ i : Fin d.m, (message d x) i (decide (i ∈ A)) else 0

private def assemble (d : Decomposition) (Z : Finset (Fin d.k)) (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) :
    Finset (Fin d.n) := (Z.disjSum (univ.sigma f)).map (d.labels).toEmbedding

private theorem mem_assemble_core (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) (c : Fin d.k) :
    (coreLabel d) c ∈ (assemble d) Z f ↔ c ∈ Z := by
  rw [assemble, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have he' : d.labels a = d.labels (Sum.inl c) := he
    have hh := (d.labels.bijective).1 he'
    subst a
    simpa using ha
  · intro h
    exact ⟨Sum.inl c, by simp [h], rfl⟩

private theorem mem_assemble_branch (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) (i : Fin d.m) (v : Fin (d.size i)) :
    (branchLabel d) i v ∈ (assemble d) Z f ↔ v ∈ f i := by
  rw [assemble, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have he' : d.labels a = d.labels (Sum.inr ⟨i,v⟩) := he
    have hh := (d.labels.bijective).1 he'
    subst a
    simpa using ha
  · intro h
    exact ⟨Sum.inr ⟨i,v⟩, by simp [h], rfl⟩

private def coreSlice (d : Decomposition) (S : Finset (Fin d.n)) : Finset (Fin d.k) :=
  univ.filter (fun c => (coreLabel d) c ∈ S)

private def branchSlice (d : Decomposition) (S : Finset (Fin d.n)) (i : Fin d.m) : Finset (Fin (d.size i)) :=
  univ.filter (fun v => (branchLabel d) i v ∈ S)

private theorem assemble_slices (d : Decomposition) (S : Finset (Fin d.n)) :
    (assemble d) ((coreSlice d) S) ((branchSlice d) S) = S := by
  ext v
  obtain ⟨a, rfl⟩ := (d.labels).surjective v
  cases a with
  | inl c =>
    change (coreLabel d) c ∈ (assemble d) _ _ ↔ (coreLabel d) c ∈ S
    simpa [coreSlice] using (mem_assemble_core d) ((coreSlice d) S) ((branchSlice d) S) c
  | inr a =>
    change (branchLabel d) a.1 a.2 ∈ (assemble d) _ _ ↔ (branchLabel d) a.1 a.2 ∈ S
    simpa [branchSlice] using (mem_assemble_branch d) ((coreSlice d) S) ((branchSlice d) S) a.1 a.2

private theorem coreSlice_assemble (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) : (coreSlice d) ((assemble d) Z f) = Z := by
  ext c
  simp [coreSlice, mem_assemble_core]

private theorem branchSlice_assemble (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) (i : Fin d.m) :
    (branchSlice d) ((assemble d) Z f) i = f i := by
  ext v
  simp [branchSlice, mem_assemble_branch]

private theorem assemble_card (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) :
    ((assemble d) Z f).card = Z.card + ∑ i, (f i).card := by
  simp [assemble]

private def selectedRoots (d : Decomposition) (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) : Finset (Fin d.m) :=
  univ.filter (fun i => d.root i ∈ f i)

private theorem dominating_assemble_iff (d : Decomposition) (Z : Finset (Fin d.k))
    (f : ∀ i : Fin d.m, Finset (Fin (d.size i))) :
    d.graph.IsDominating ((assemble d) Z f : Set (Fin d.n)) ↔
      (coreCovered d) Z ((selectedRoots d) f) ∧ ∀ i, (localDominating d) i (f i) := by
  constructor
  · intro h
    constructor
    · intro c
      rcases h ((coreLabel d) c) with hm | ⟨v,hv,ha⟩
      · exact Or.inl (((mem_assemble_core d) Z f c).mp hm)
      · rcases (d.core_neighbors c v).mp ha with ⟨a, rfl, hd⟩ | ⟨i, rfl, hi⟩
        · exact Or.inr (Or.inl ⟨a, ((mem_assemble_core d) Z f a).mp hv, hd⟩)
        · exact Or.inr (Or.inr ⟨i, by
            simpa [selectedRoots] using ((mem_assemble_branch d) Z f i (d.root i)).mp hv, hi⟩)
    · intro i v
      by_cases hr : v = d.root i
      · subst v
        rcases h ((branchLabel d) i (d.leaf i)) with hm | ⟨w, hw, ha⟩
        · exact Or.inr ⟨d.leaf i, ((mem_assemble_branch d) Z f i (d.leaf i)).mp hm,
            d.root_leaf_edge i⟩
        · have he := (d.leaf_neighbors i w).mp ha
          exact Or.inl (((mem_assemble_branch d) Z f i (d.root i)).mp (by
            change d.labels (Sum.inr ⟨i,d.root i⟩) ∈ (assemble d) Z f
            rw [← he]
            exact hw))
      · rcases h ((branchLabel d) i v) with hm | ⟨w,hw,ha⟩
        · exact Or.inl (((mem_assemble_branch d) Z f i v).mp hm)
        · obtain ⟨t, rfl⟩ := d.nonroot_neighbors i v hr w ha
          exact Or.inr ⟨t, ((mem_assemble_branch d) Z f i t).mp hw, ha⟩
  · rintro ⟨hc, hl⟩ v
    obtain ⟨a, rfl⟩ := (d.labels).surjective v
    cases a with
    | inl c =>
      rcases hc c with hm | ⟨a,hd,ha⟩ | ⟨i,hi,ha⟩
      · exact Or.inl (((mem_assemble_core d) Z f c).mpr hm)
      · exact Or.inr ⟨(coreLabel d) a, ((mem_assemble_core d) Z f a).mpr hd, ha⟩
      · exact Or.inr ⟨(branchLabel d) i (d.root i), ((mem_assemble_branch d) Z f i (d.root i)).mpr
          (by simpa [selectedRoots] using hi), (d.core_neighbors c _).mpr (Or.inr ⟨i,rfl,ha⟩)⟩
    | inr a =>
      rcases hl a.1 a.2 with hm | ⟨w,hw,ha⟩
      · exact Or.inl (((mem_assemble_branch d) Z f a.1 a.2).mpr hm)
      · exact Or.inr ⟨(branchLabel d) a.1 w, ((mem_assemble_branch d) Z f a.1 w).mpr hw, ha⟩

private def choices (d : Decomposition) (i : Fin d.m) (b : Bool) : Finset (Finset (Fin (d.size i))) :=
  univ.powerset.filter (fun S => (localDominating d) i S ∧ decide (d.root i ∈ S) = b)

private abbrev Choice (d : Decomposition) (i : Fin d.m) (b : Bool) := ↥((choices d) i b)

private def coreChoices (d : Decomposition) (Z : Finset (Fin d.k)) : Finset (Finset (Fin d.m)) :=
  univ.powerset.filter ((coreCovered d) Z)

private abbrev Valid (d : Decomposition) := Σ Z : Finset (Fin d.k), Σ A : ↥((coreChoices d) Z),
  ∀ i : Fin d.m, (Choice d) i (decide (i ∈ A.val))

private theorem choice_dominating (d : Decomposition) (i : Fin d.m) (b : Bool) (S : (Choice d) i b) :
    (localDominating d) i S.val := (mem_filter.mp S.property).2.1

private theorem choice_root (d : Decomposition) (i : Fin d.m) (b : Bool) (S : (Choice d) i b) :
    decide (d.root i ∈ S.val) = b := (mem_filter.mp S.property).2.2

private theorem selected_eq (d : Decomposition) {Z : Finset (Fin d.k)} (A : ↥((coreChoices d) Z))
    (f : ∀ i : Fin d.m, (Choice d) i (decide (i ∈ A.val))) :
    (selectedRoots d) (fun i => (f i).val) = A.val := by
  ext i
  simp only [selectedRoots, mem_filter, mem_univ, true_and]
  exact decide_eq_decide.mp ((choice_root d) i _ (f i))

private def validToDom (d : Decomposition) (p : (Valid d)) : ↥(domSets d.graph) := by
  refine ⟨(assemble d) p.1 (fun i => (p.2.2 i).val), mem_domSets.mpr ?_⟩
  apply ((dominating_assemble_iff d) _ _).mpr
  constructor
  · rw [selected_eq d p.2.1 p.2.2]
    exact (mem_filter.mp p.2.1.property).2
  · exact fun i => (choice_dominating d) i _ (p.2.2 i)

private theorem validToDom_injective (d : Decomposition) : Function.Injective (validToDom d) := by
  rintro ⟨Z,A,f⟩ ⟨Z',A',f'⟩ h
  have hs := congrArg Subtype.val h
  change (assemble d) Z (fun i => (f i).val) = (assemble d) Z' (fun i => (f' i).val) at hs
  have hz : Z = Z' := by
    simpa only [coreSlice_assemble] using congrArg (coreSlice d) hs
  subst Z'
  have hf : (fun i => (f i).val) = (fun i => (f' i).val) := by
    funext i
    simpa only [branchSlice_assemble] using congrArg (fun S => (branchSlice d) S i) hs
  have ha : A = A' := by
    apply Subtype.ext
    rw [← selected_eq d A f, ← selected_eq d A' f', hf]
  subst A'
  have he : f = f' := by
    funext i
    exact Subtype.ext (congrFun hf i)
  subst f'
  rfl

private theorem validToDom_surjective (d : Decomposition) : Function.Surjective (validToDom d) := by
  intro S
  let Z := (coreSlice d) S.val
  let f := (branchSlice d) S.val
  have hd : (coreCovered d) Z ((selectedRoots d) f) ∧ ∀ i, (localDominating d) i (f i) := by
    apply ((dominating_assemble_iff d) Z f).mp
    dsimp [Z,f]
    rw [assemble_slices]
    exact mem_domSets.mp S.property
  let A : ↥((coreChoices d) Z) := ⟨(selectedRoots d) f, by simp [coreChoices, hd.1]⟩
  let g : ∀ i, (Choice d) i (decide (i ∈ A.val)) := fun i => ⟨f i, by
    simp [choices, hd.2 i, A, selectedRoots]⟩
  refine ⟨⟨Z,A,g⟩, ?_⟩
  apply Subtype.ext
  exact (assemble_slices d) S.val

private def configEquiv (d : Decomposition) : (Valid d) ≃ ↥(domSets d.graph) :=
  Equiv.ofBijective (validToDom d) ⟨(validToDom_injective d), (validToDom_surjective d)⟩

private theorem choice_sum (d : Decomposition) (x : ℤ) (i : Fin d.m) (b : Bool) :
    (∑ S : (Choice d) i b, x ^ S.val.card) = (message d x) i b := by
  classical
  calc
    (∑ S : (Choice d) i b, x ^ S.val.card) =
        ∑ S ∈ (choices d) i b, x ^ S.card := by
      simpa only [Finset.univ_eq_attach] using
        sum_attach ((choices d) i b) (fun S => x ^ S.card)
    _ = (message d x) i b := by
      unfold choices message
      rw [sum_filter]

private theorem choice_product (d : Decomposition) (x : ℤ) (Z : Finset (Fin d.k)) (A : ↥((coreChoices d) Z)) :
    (∑ f : ∀ i : Fin d.m, (Choice d) i (decide (i ∈ A.val)),
      x ^ (∑ i, (f i).val.card)) =
        ∏ i : Fin d.m, (message d x) i (decide (i ∈ A.val)) := by
  classical
  simp_rw [← prod_pow_eq_pow_sum]
  calc
    (∑ f : ∀ i : Fin d.m, (Choice d) i (decide (i ∈ A.val)), ∏ i, x ^ (f i).val.card) =
        ∏ i : Fin d.m, ∑ S : (Choice d) i (decide (i ∈ A.val)), x ^ S.val.card :=
      (Fintype.prod_sum (fun (i : Fin d.m) (S : (Choice d) i (decide (i ∈ A.val))) =>
        x ^ S.val.card)).symm
    _ = _ := by simp_rw [choice_sum]

/-- The exact graph sum is obtained by unique restriction to core and components,
followed by the cardinality-preserving root-state partition. -/
theorem reassembly (d : Decomposition) (x : ℤ) : evaluation d.graph x = (stateEvaluation d x) := by
  classical
  have hs := Fintype.sum_equiv (configEquiv d)
    (fun p : (Valid d) => x ^ ((assemble d) p.1 (fun i => (p.2.2 i).val)).card)
    (fun S => x ^ S.val.card) (fun _ => rfl)
  have hdom : (∑ S : ↥(domSets d.graph), x ^ S.val.card) =
      evaluation d.graph x := by
    simpa only [Finset.univ_eq_attach, evaluation] using
      sum_attach (domSets d.graph) (fun S => x ^ S.card)
  have hterm (Z : Finset (Fin d.k)) (A : ↥((coreChoices d) Z)) :
      (∑ f : ∀ i : Fin d.m, (Choice d) i (decide (i ∈ A.val)),
        x ^ ((assemble d) Z (fun i => (f i).val)).card) =
      x ^ Z.card * ∏ i : Fin d.m, (message d x) i (decide (i ∈ A.val)) := by
    simp_rw [assemble_card, pow_add]
    rw [← mul_sum, choice_product]
  have hcore (Z : Finset (Fin d.k)) :
      (∑ A : ↥((coreChoices d) Z), ∏ i : Fin d.m, (message d x) i (decide (i ∈ A.val))) =
      ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
        if (coreCovered d) Z A then ∏ i : Fin d.m, (message d x) i (decide (i ∈ A)) else 0 := by
    calc
      (∑ A : ↥((coreChoices d) Z), ∏ i : Fin d.m, (message d x) i (decide (i ∈ A.val))) =
          ∑ A ∈ (coreChoices d) Z, ∏ i : Fin d.m, (message d x) i (decide (i ∈ A)) := by
        simpa only [Finset.univ_eq_attach] using
          sum_attach ((coreChoices d) Z) (fun A => ∏ i : Fin d.m, (message d x) i (decide (i ∈ A)))
      _ = _ := by unfold coreChoices; rw [sum_filter]
  rw [hdom] at hs
  rw [← hs]
  unfold stateEvaluation
  simp only [Fintype.sum_sigma]
  apply sum_congr rfl
  intro Z _
  simp_rw [hterm]
  rw [← mul_sum, hcore]

/-- The covered core sum for arbitrary candidate branch-message values. -/
def tableEvaluation (d : Decomposition) (x : ℤ) (table : Fin d.m → Bool → ℤ) : ℤ :=
  ∑ Z ∈ (univ : Finset (Fin d.k)).powerset,
    x ^ Z.card * ∑ A ∈ (univ : Finset (Fin d.m)).powerset,
      if coreCovered d Z A then ∏ i : Fin d.m, table i (decide (i ∈ A)) else 0

/-- Soundness of arbitrary supplied (message d x) values for the same decomposition,
weight, d.root states and core sum. The actual application must prove both inputs. -/
theorem zero_of_messages (d : Decomposition) (x : ℤ)
    (table : Fin d.m → Bool → ℤ)
    (hm : ∀ i b, (message d x) i b = table i b)
    (hz : tableEvaluation d x table = 0) :
    evaluation d.graph x = 0 := by
  rw [reassembly]
  unfold stateEvaluation
  simp_rw [hm]
  exact hz

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
private theorem family_of_root {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (v w : Fin (n + 1)) (hconn : H.Connected) (hleaf : Leaf H w) (hadj : H.Adj w v)
    (x : ℤ) (hbase : evaluation H x = 0) :
    ∀ N : ℕ, ∃ q : ℕ, N < q ∧ ∃ G : SimpleGraph (Fin q),
      G.Connected ∧ ∑ S ∈ domSets G, x ^ S.card = 0 := by
  classical
  intro N
  let r := N + 1
  let R := replicated H {v} r
  let e := Fintype.equivFin (RepVertex r (Fin (n + 1)))
  let G := R.map e
  have hn : Fintype.card (RepVertex r (Fin (n + 1))) = (n + 1) * r + 2 := by
    rw [replicated_card]; simp [Nat.mul_comm]
  refine ⟨Fintype.card (RepVertex r (Fin (n + 1))), ?_, G, ?_, ?_⟩
  · rw [hn]; dsimp [r]; simp only [Nat.add_mul, Nat.one_mul]; omega
  · exact (support_replication_connected H v hconn r).map
      (SimpleGraph.Iso.map e R).toHom e.surjective
  · change evaluation G x = 0
    rw [← evaluation_iso (SimpleGraph.Iso.map e R)]
    change evaluation (replicated H {v} r) x = 0
    rw [support_replication_evaluation H v w hleaf hadj,
      hbase, zero_pow (by dsimp [r]; omega : r ≠ 0), mul_zero]

/-- Factual edge data from Alikhani--Griswold, arXiv:2608.00109v1.
The independently written encoding uses the explicit graph, rather than the branch prose. -/
private theorem leaf_of_unique {V : Type*} [Fintype V] (H : SimpleGraph V) (w v : V)
    (h : ∀ a, H.Adj w a ↔ a = v) : Leaf H w := by
  classical
  exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨v, (h v).mpr rfl, fun a ha => (h a).mp ha⟩

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
private def sourceBranchSize : Fin 8 → ℕ := ![2,2,2,2,6,3,3,9]

/-- Each component occupies an interval in the published vertex labels. -/
private def sourceBranchStart : Fin 8 → ℕ := ![4,6,8,10,12,18,21,24]

/-- Exact source labels, with no vertices added or discarded. -/
private def sourceBranchLabel (i : Fin 8) (v : Fin (sourceBranchSize i)) : Fin 33 :=
  ⟨sourceBranchStart i + v.val, by
    have h : ∀ i : Fin 8, sourceBranchStart i + sourceBranchSize i ≤ 33 := by decide
    have hi := h i
    omega⟩

/-- The sourceRoot is the first vertex of every interval. -/
private def sourceRoot (i : Fin 8) : Fin (sourceBranchSize i) :=
  ⟨0, by fin_cases i <;> decide⟩

/-- Core neighbors of each component sourceRoot. -/
private def sourceIncidence : Fin 8 → Finset (Fin 4) :=
  ![{0},{2},{2},{2},{0,1},{1,2},{2,3},{3}]

private def parent (v : Fin 33) : Fin 33 :=
  ![0,0,1,0,0,4,2,6,2,8,2,10,0,12,12,12,12,12,1,18,18,2,21,21,3,24,24,26,27,28,29,28,31] v

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The complete event: every order threshold is exceeded by a connected graph
whose ordinary domination polynomial vanishes at minus four. -/
theorem result : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0 := by
  let labels : (Fin 4 ⊕ (Σ i : Fin 8, Fin (sourceBranchSize i))) → Fin 33 := fun a =>
    match a with
    | .inl c => ⟨c.val, by omega⟩
    | .inr v => sourceBranchLabel v.1 v.2
  let d : Decomposition := {
    n := 33, k := 4, m := 8, size := sourceBranchSize, graph := sourceGraph
    adjDec := instDecidableRelFinOfNatNatAdjSourceGraph
    labels := Equiv.ofBijective labels (by decide)
    root := sourceRoot
    leaf := fun i => ⟨1, by fin_cases i <;> decide⟩
    incidence := sourceIncidence
    leaf_neighbors := by decide
    root_leaf_edge := by decide
    nonroot_neighbors := by decide
    core_neighbors := by decide }
  let table : Fin 8 → Bool → ℤ := fun i b =>
    if b then ![12,12,12,12,972,-36,-36,-20736] i
    else ![-4,-4,-4,-4,-1024,16,16,5888] i
  have hbase : evaluation sourceGraph (-4) = 0 :=
    zero_of_messages d (-4) table (by decide) (by decide)
  apply family_of_root sourceGraph 4 5 ?_ ?_ (by decide) (-4) hbase
  · have parent_edge : ∀ v : Fin 33, v ≠ 0 → sourceGraph.Adj v (parent v) := by decide
    have parent_lower : ∀ v : Fin 33, v ≠ 0 → (parent v).val < v.val := by decide
    have hc := D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph.connected_of_predecessor
      (G := sourceGraph) (C := (univ : Finset (Fin 33))) (0 : Fin 33) (mem_univ _) (by
        intro v _ hv
        exact ⟨parent v, mem_univ _, parent_lower v hv, (parent_edge v hv).symm⟩)
    exact (sourceGraph.induceUnivIso.connected_iff).mp
      (Eq.mp (congrArg (fun C : Set (Fin 33) => (sourceGraph.induce C).Connected)
        Finset.coe_univ) hc)
  · exact leaf_of_unique sourceGraph 5 4 (by decide)

#print axioms result

end

end D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
