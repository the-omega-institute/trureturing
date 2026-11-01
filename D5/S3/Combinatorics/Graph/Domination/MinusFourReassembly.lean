/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourReassembly
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result; premises=D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.label_bijective,D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.leaf_neighbors,D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.root_leaf_edge,D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.nonroot_neighbors,D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.core_neighbors
   digest: Restriction and reassembly for the actual source graph. -/

import D5.S3.Combinatorics.Graph.Domination.MinusFourBaseStates
import Mathlib.Data.Finset.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000

namespace D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly

open Finset DominatingSetAverage MinusFourReplication MinusFourFamily MinusFourBaseStates

noncomputable section

private abbrev Coordinate := Fin 4 ⊕ (Σ i : Fin 8, Fin (branchSize i))

private def coreLabel (v : Fin 4) : Fin 33 := ⟨v.val, by omega⟩

private def label : Coordinate → Fin 33
  | Sum.inl v => coreLabel v
  | Sum.inr v => branchLabel v.1 v.2

set_option maxRecDepth 10000 in
private theorem label_bijective : Function.Bijective label := by decide

private def labelEquiv : Coordinate ≃ Fin 33 := Equiv.ofBijective label label_bijective

private def assemble (Z : Finset (Fin 4)) (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) :
    Finset (Fin 33) := (Z.disjSum (univ.sigma f)).map labelEquiv.toEmbedding

private theorem mem_assemble_core (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) (c : Fin 4) :
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

private theorem mem_assemble_branch (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) (i : Fin 8) (v : Fin (branchSize i)) :
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

private def coreSlice (S : Finset (Fin 33)) : Finset (Fin 4) :=
  univ.filter (fun c => coreLabel c ∈ S)

private def branchSlice (S : Finset (Fin 33)) (i : Fin 8) : Finset (Fin (branchSize i)) :=
  univ.filter (fun v => branchLabel i v ∈ S)

private theorem assemble_slices (S : Finset (Fin 33)) :
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

private theorem coreSlice_assemble (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) : coreSlice (assemble Z f) = Z := by
  ext c
  simp [coreSlice, mem_assemble_core]

private theorem branchSlice_assemble (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) (i : Fin 8) :
    branchSlice (assemble Z f) i = f i := by
  ext v
  simp [branchSlice, mem_assemble_branch]

private theorem assemble_card (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) :
    (assemble Z f).card = Z.card + ∑ i, (f i).card := by
  simp [assemble]

private def selectedRoots (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) : Finset (Fin 8) :=
  univ.filter (fun i => root i ∈ f i)

private def leaf (i : Fin 8) : Fin (branchSize i) :=
  ⟨1, by fin_cases i <;> decide⟩

set_option maxRecDepth 10000 in
private theorem leaf_neighbors : ∀ (i : Fin 8) (v : Fin 33),
    sourceGraph.Adj (branchLabel i (leaf i)) v ↔ v = branchLabel i (root i) := by decide

set_option maxRecDepth 10000 in
private theorem root_leaf_edge : ∀ i : Fin 8, (branchGraph i).Adj (root i) (leaf i) := by decide

set_option maxRecDepth 10000 in
private theorem nonroot_neighbors : ∀ (i : Fin 8) (v : Fin (branchSize i)), v ≠ root i →
    ∀ w : Fin 33, sourceGraph.Adj (branchLabel i v) w →
      ∃ t : Fin (branchSize i), w = branchLabel i t := by decide

set_option maxRecDepth 10000 in
private theorem core_neighbors : ∀ (c : Fin 4) (v : Fin 33),
    sourceGraph.Adj (coreLabel c) v ↔
      (∃ d : Fin 4, v = coreLabel d ∧ sourceGraph.Adj (coreLabel c) (coreLabel d)) ∨
      ∃ i : Fin 8, v = branchLabel i (root i) ∧ c ∈ rootNeighbors i := by decide

private theorem dominating_assemble_iff (Z : Finset (Fin 4))
    (f : ∀ i : Fin 8, Finset (Fin (branchSize i))) :
    sourceGraph.IsDominating (assemble Z f : Set (Fin 33)) ↔
      coreCovered Z (selectedRoots f) ∧ ∀ i, localDominating i (f i) := by
  constructor
  · intro h
    constructor
    · intro c
      rcases h (coreLabel c) with hm | ⟨v,hv,ha⟩
      · exact Or.inl ((mem_assemble_core Z f c).mp hm)
      · rcases (core_neighbors c v).mp ha with ⟨d, rfl, hd⟩ | ⟨i, rfl, hi⟩
        · exact Or.inr (Or.inl ⟨d, (mem_assemble_core Z f d).mp hv, hd⟩)
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
      rcases hc c with hm | ⟨d,hd,ha⟩ | ⟨i,hi,ha⟩
      · exact Or.inl ((mem_assemble_core Z f c).mpr hm)
      · exact Or.inr ⟨coreLabel d, (mem_assemble_core Z f d).mpr hd, ha⟩
      · exact Or.inr ⟨branchLabel i (root i), (mem_assemble_branch Z f i (root i)).mpr
          (by simpa [selectedRoots] using hi), (core_neighbors c _).mpr (Or.inr ⟨i,rfl,ha⟩)⟩
    | inr a =>
      rcases hl a.1 a.2 with hm | ⟨w,hw,ha⟩
      · exact Or.inl ((mem_assemble_branch Z f a.1 a.2).mpr hm)
      · exact Or.inr ⟨branchLabel a.1 w, (mem_assemble_branch Z f a.1 w).mpr hw, ha⟩


private def choices (i : Fin 8) (b : Bool) : Finset (Finset (Fin (branchSize i))) :=
  univ.powerset.filter (fun S => localDominating i S ∧ decide (root i ∈ S) = b)

private abbrev Choice (i : Fin 8) (b : Bool) := ↥(choices i b)

private def coreChoices (Z : Finset (Fin 4)) : Finset (Finset (Fin 8)) :=
  univ.powerset.filter (coreCovered Z)

private abbrev Valid := Σ Z : Finset (Fin 4), Σ A : ↥(coreChoices Z),
  ∀ i : Fin 8, Choice i (decide (i ∈ A.val))

private theorem choice_dominating (i : Fin 8) (b : Bool) (S : Choice i b) :
    localDominating i S.val := (mem_filter.mp S.property).2.1

private theorem choice_root (i : Fin 8) (b : Bool) (S : Choice i b) :
    decide (root i ∈ S.val) = b := (mem_filter.mp S.property).2.2

private theorem selected_eq {Z : Finset (Fin 4)} (A : ↥(coreChoices Z))
    (f : ∀ i : Fin 8, Choice i (decide (i ∈ A.val))) :
    selectedRoots (fun i => (f i).val) = A.val := by
  ext i
  simp only [selectedRoots, mem_filter, mem_univ, true_and]
  exact decide_eq_decide.mp (choice_root i _ (f i))

private def validToDom (p : Valid) : ↥(domSets sourceGraph) := by
  refine ⟨assemble p.1 (fun i => (p.2.2 i).val), mem_domSets.mpr ?_⟩
  apply (dominating_assemble_iff _ _).mpr
  constructor
  · rw [selected_eq p.2.1 p.2.2]
    exact (mem_filter.mp p.2.1.property).2
  · exact fun i => choice_dominating i _ (p.2.2 i)

private theorem validToDom_injective : Function.Injective validToDom := by
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

private theorem validToDom_surjective : Function.Surjective validToDom := by
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

private def configEquiv : Valid ≃ ↥(domSets sourceGraph) :=
  Equiv.ofBijective validToDom ⟨validToDom_injective, validToDom_surjective⟩

private theorem choice_sum (i : Fin 8) (b : Bool) :
    (∑ S : Choice i b, (-4 : ℤ) ^ S.val.card) = message i b := by
  classical
  calc
    (∑ S : Choice i b, (-4 : ℤ) ^ S.val.card) =
        ∑ S ∈ choices i b, (-4 : ℤ) ^ S.card := by
      simpa only [Finset.univ_eq_attach] using
        sum_attach (choices i b) (fun S => (-4 : ℤ) ^ S.card)
    _ = message i b := by
      unfold choices message
      rw [sum_filter]

private theorem choice_product (Z : Finset (Fin 4)) (A : ↥(coreChoices Z)) :
    (∑ f : ∀ i : Fin 8, Choice i (decide (i ∈ A.val)),
      (-4 : ℤ) ^ (∑ i, (f i).val.card)) =
        ∏ i : Fin 8, message i (decide (i ∈ A.val)) := by
  classical
  simp_rw [← prod_pow_eq_pow_sum]
  calc
    (∑ f : ∀ i : Fin 8, Choice i (decide (i ∈ A.val)), ∏ i, (-4 : ℤ) ^ (f i).val.card) =
        ∏ i : Fin 8, ∑ S : Choice i (decide (i ∈ A.val)), (-4 : ℤ) ^ S.val.card :=
      (Fintype.prod_sum (fun (i : Fin 8) (S : Choice i (decide (i ∈ A.val))) =>
        (-4 : ℤ) ^ S.val.card)).symm
    _ = _ := by simp_rw [choice_sum]

/-- The exact graph sum is obtained by unique restriction to core and components,
followed by the cardinality-preserving root-state partition. -/
theorem source_reassembly : evaluation sourceGraph (-4) = stateEvaluation := by
  classical
  have hs := Fintype.sum_equiv configEquiv
    (fun p : Valid => (-4 : ℤ) ^ (assemble p.1 (fun i => (p.2.2 i).val)).card)
    (fun S => (-4 : ℤ) ^ S.val.card) (fun _ => rfl)
  have hdom : (∑ S : ↥(domSets sourceGraph), (-4 : ℤ) ^ S.val.card) =
      evaluation sourceGraph (-4) := by
    simpa only [Finset.univ_eq_attach, evaluation] using
      sum_attach (domSets sourceGraph) (fun S => (-4 : ℤ) ^ S.card)
  have hterm (Z : Finset (Fin 4)) (A : ↥(coreChoices Z)) :
      (∑ f : ∀ i : Fin 8, Choice i (decide (i ∈ A.val)),
        (-4 : ℤ) ^ (assemble Z (fun i => (f i).val)).card) =
      (-4 : ℤ) ^ Z.card * ∏ i : Fin 8, message i (decide (i ∈ A.val)) := by
    simp_rw [assemble_card, pow_add]
    rw [← mul_sum, choice_product]
  have hcore (Z : Finset (Fin 4)) :
      (∑ A : ↥(coreChoices Z), ∏ i : Fin 8, message i (decide (i ∈ A.val))) =
      ∑ A ∈ (univ : Finset (Fin 8)).powerset,
        if coreCovered Z A then ∏ i : Fin 8, message i (decide (i ∈ A)) else 0 := by
    calc
      (∑ A : ↥(coreChoices Z), ∏ i : Fin 8, message i (decide (i ∈ A.val))) =
          ∑ A ∈ coreChoices Z, ∏ i : Fin 8, message i (decide (i ∈ A)) := by
        simpa only [Finset.univ_eq_attach] using
          sum_attach (coreChoices Z) (fun A => ∏ i : Fin 8, message i (decide (i ∈ A)))
      _ = _ := by unfold coreChoices; rw [sum_filter]
  rw [hdom] at hs
  rw [← hs]
  unfold stateEvaluation
  simp only [Fintype.sum_sigma]
  apply sum_congr rfl
  intro Z _
  simp_rw [hterm]
  rw [← mul_sum, hcore]

/-- The full connected unbounded-order ordinary-domination event. -/
theorem result : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
    G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0 :=
  result_of_reassembly source_reassembly

end

end D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
