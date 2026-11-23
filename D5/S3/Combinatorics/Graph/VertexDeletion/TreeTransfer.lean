/- GID: D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact hub and balanced optimizers yield four small transfer ratios. -/

import D5.S3.Combinatorics.Graph.VertexDeletion.BalancedCuts

/-! Exact hub and balanced optimizers yield four small transfer ratios. -/

set_option autoImplicit false
set_option linter.style.openClassical false

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section SpineComponents

variable {p t b k : ℕ}

private def hostSpine : Fin (p + t) ↪ Vertex p t b k :=
  ⟨Sum.inl, Sum.inl_injective⟩

def hostHub (hub : Fin b → Fin p) (i : Fin b) : Vertex p t b k :=
  hostSpine ((hub i).castAdd t)

private def survivingSpine (D : Finset (Vertex p t b k)) (i : Fin (p + t))
    (hi : hostSpine i ∉ D) : survivors D :=
  ⟨hostSpine i, hi⟩

private def deletedSpine (D : Finset (Vertex p t b k)) : Finset (Fin (p + t)) :=
  Finset.univ.filter (fun i => hostSpine i ∈ D)

private def spineRunStarts (D : Finset (Vertex p t b k)) : Finset (Fin (p + t)) :=
  Finset.univ.filter (fun i => hostSpine i ∉ D ∧
    ∀ j : Fin (p + t), j.val + 1 = i.val → hostSpine j ∈ D)

private theorem spineRunStarts_card_le (D : Finset (Vertex p t b k)) :
    (spineRunStarts D).card ≤ (deletedSpine D).card + 1 := by
  let f (i : ↥(spineRunStarts D)) : Option ↥(deletedSpine D) :=
    if h : i.val.val = 0 then none
    else
      let j : Fin (p + t) := ⟨i.val.val - 1, by have := i.val.isLt; omega⟩
      some ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp i.property).2).2 j (by dsimp [j]; omega)⟩⟩
  have decode (i : ↥(spineRunStarts D)) :
      (f i).elim 0 (fun j => j.val.val + 1) = i.val.val := by
    dsimp only [f]
    split
    · simp_all
    · change i.val.val - 1 + 1 = i.val.val
      omega
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    rw [← decode i, ← decode j, hij]
  simpa only [Fintype.card_option, Fintype.card_coe] using Fintype.card_le_of_injective f hf

private theorem spine_has_run_start (hub : Fin b → Fin p) (D : Finset (Vertex p t b k))
    (i : Fin (p + t)) (hi : hostSpine i ∉ D) :
    ∃ j : ↥(spineRunStarts D),
      (survivorGraph (host hub) D).Reachable
        (survivingSpine D j.val ((Finset.mem_filter.mp j.property).2).1)
        (survivingSpine D i hi) := by
  revert hi
  induction i using Fin.strong_induction_on with
  | h i ih =>
    intro hi
    let j : Fin (p + t) := ⟨i.val - 1, by have := i.isLt; omega⟩
    by_cases hj : i.val ≠ 0 ∧ hostSpine j ∉ D
    · have hstep : j.val + 1 = i.val := by dsimp [j]; omega
      obtain ⟨a, ha⟩ := ih j (Fin.lt_def.mpr (by omega)) hj.2
      refine ⟨a, ha.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact induce_adj.mpr (pathGraph_adj.mpr (Or.inl hstep))
    · refine ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_⟩⟩,
        SimpleGraph.Reachable.rfl⟩
      intro z hz
      have he : z = j := Fin.ext (by dsimp [j]; omega)
      subst z
      exact Classical.not_not.mp (fun h => hj ⟨by omega, h⟩)

private theorem surviving_leaf_no_adj (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) (a : Fin b × Fin k) (ha : Sum.inr a ∉ D)
    (hd : hostHub hub a.1 ∈ D) (v : survivors D) :
    ¬ (survivorGraph (host hub) D).Adj ⟨Sum.inr a, ha⟩ v := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl i =>
    intro e
    change i = (hub a.1).castAdd t at e
    subst i
    exact hv hd
  | inr i => exact fun e => e

theorem component_eq_iff_of_no_adj {V : Type*} {G : SimpleGraph V} {v : V}
    (h : ∀ w, ¬ G.Adj v w) (w : V) :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ v = w := by
  rw [ConnectedComponent.eq]
  refine ⟨fun reach => ?_, fun e => e ▸ Reachable.rfl⟩
  by_contra hne
  obtain ⟨u, hu⟩ := G.mem_support.mp (mem_support_of_reachable hne reach)
  exact h u hu

private def deletedHubIndices (hub : Fin b → Fin p) (D : Finset (Vertex p t b k)) :
    Finset (Fin b) := Finset.univ.filter (fun i => hostHub hub i ∈ D)

private def detachedLeafIndices (hub : Fin b → Fin p) (D : Finset (Vertex p t b k)) :
    Finset (Fin b × Fin k) :=
  ((deletedHubIndices hub D) ×ˢ (Finset.univ : Finset (Fin k))).filter
    (fun a => Sum.inr a ∉ D)

private theorem detachedLeafIndices_card_le (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) :
    (detachedLeafIndices hub D).card ≤ (deletedHubIndices hub D).card * k := by
  unfold detachedLeafIndices
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le ((deletedHubIndices hub D) ×ˢ (Finset.univ : Finset (Fin k)))
      (fun a : Fin b × Fin k => Sum.inr a ∉ D)

private theorem host_component_count_le (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) :
    Fintype.card (survivorGraph (host hub) D).ConnectedComponent ≤
      (deletedSpine D).card + 1 + (deletedHubIndices hub D).card * k := by
  let G := survivorGraph (host hub) D
  let A := spineRunStarts D
  let L := detachedLeafIndices hub D
  let f : ↥A ⊕ ↥L → G.ConnectedComponent
    | .inl i => G.connectedComponentMk
        (survivingSpine D i.val ((Finset.mem_filter.mp i.property).2).1)
    | .inr a => G.connectedComponentMk ⟨Sum.inr a.val, (Finset.mem_filter.mp a.property).2⟩
  have reaches (i : Fin (p + t)) (hi : hostSpine i ∉ D) :
      ∃ a : ↥A, f (.inl a) = G.connectedComponentMk (survivingSpine D i hi) := by
    obtain ⟨a, ha⟩ := spine_has_run_start hub D i hi
    exact ⟨a, ConnectedComponent.eq.mpr ha⟩
  have hSurj : Function.Surjective f := by
    intro C
    obtain ⟨⟨v, hv⟩, rfl⟩ := C.exists_rep
    cases v with
    | inl i =>
      obtain ⟨a, ha⟩ := reaches i hv
      exact ⟨.inl a, ha⟩
    | inr leaf =>
      by_cases hd : hostHub hub leaf.1 ∈ D
      · have hLeaf : leaf ∈ L := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
            Finset.mem_univ _⟩, hv⟩
        exact ⟨.inr ⟨leaf, hLeaf⟩, rfl⟩
      · obtain ⟨a, ha⟩ := reaches ((hub leaf.1).castAdd t) hd
        refine ⟨.inl a, ha.trans (ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable ?_))⟩
        exact induce_adj.mpr (show (hub leaf.1).castAdd t = (hub leaf.1).castAdd t from rfl)
  calc
    _ ≤ A.card + L.card := by
      simpa only [Fintype.card_sum, Fintype.card_coe] using
        Fintype.card_le_of_surjective f hSurj
    _ ≤ _ := Nat.add_le_add (spineRunStarts_card_le D) (detachedLeafIndices_card_le hub D)

end SpineComponents

section UniformHubDeletion

variable {b k q : ℕ}

private def uniformHubEmbedding (b k q : ℕ) : Fin b ↪ UniformVertex b k q where
  toFun := hostHub (uniformHub b)
  inj' := fun _ _ e => (uniform_hubs_independent b).1
    (Fin.castAdd_injective _ _ (hostSpine.injective e))

private def uniformHubDeletion (b k q : ℕ) : Finset (UniformVertex b k q) :=
  Finset.univ.map (uniformHubEmbedding b k q)

private theorem uniform_hub_deletion_card (b k q : ℕ) :
    (uniformHubDeletion b k q).card = b := by
  simp [uniformHubDeletion]

private def uniformDeletedHubs (D : Finset (UniformVertex b k q)) : ℕ :=
  (deletedHubIndices (uniformHub b) D).card

private def uniformDeletedOtherSpine (D : Finset (UniformVertex b k q)) : ℕ :=
  ((deletedSpine D).filter (fun i =>
    ∀ j : Fin b, i ≠ (uniformHub b j).castAdd (uniformTailLength b k q))).card

private theorem uniform_spine_count (D : Finset (UniformVertex b k q)) :
    (deletedSpine D).card = uniformDeletedHubs D + uniformDeletedOtherSpine D := by
  let e : Fin b ↪ Fin (2 * b + uniformTailLength b k q) :=
    ⟨fun i => (uniformHub b i).castAdd _, fun _ _ he =>
      (uniform_hubs_independent b).1 (Fin.castAdd_injective _ _ he)⟩
  let S := (deletedSpine D).filter (fun i => ∃ j : Fin b, i = e j)
  have hEq : (deletedHubIndices (uniformHub b) D).map e = S := by
    ext i
    simp only [S, deletedHubIndices, deletedSpine, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, j, rfl⟩
    · rintro ⟨hi, j, rfl⟩
      exact ⟨j, hi, rfl⟩
  have hCard : S.card = uniformDeletedHubs D := by
    rw [← hEq, Finset.card_map]
    rfl
  rw [← hCard]
  have h := Finset.card_filter_add_card_filter_not (s := deletedSpine D)
    (fun i => ∃ j : Fin b, i = e j)
  have hOther : (deletedSpine D).filter (fun i => ¬ ∃ j : Fin b, i = e j) =
      (deletedSpine D).filter (fun i =>
        ∀ j : Fin b, i ≠ (uniformHub b j).castAdd (uniformTailLength b k q)) := by
    ext i
    simp only [Finset.mem_filter, not_exists]
    rfl
  rw [hOther] at h
  exact h.symm

private theorem uniform_spine_card_le (D : Finset (UniformVertex b k q)) :
    (deletedSpine D).card ≤ D.card := by
  rw [← Finset.card_map hostSpine]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
  exact (Finset.mem_filter.mp hi).2

private theorem uniform_nc_upper_bound (D : Finset (UniformVertex b k q)) (hD : D.card = b) :
    let h := uniformDeletedHubs D
    let x := uniformDeletedOtherSpine D
    (spineRunStarts D).card ≤ h + x + 1 ∧
    (detachedLeafIndices (uniformHub b) D).card ≤ k * h ∧
    ncDamage (host (uniformHub b)) D ≤ b + k * h := by
  dsimp only
  have hs := uniform_spine_count D
  have hp := spineRunStarts_card_le D
  have hl := detachedLeafIndices_card_le (uniformHub b) D
  have hc := host_component_count_le (uniformHub b) D
  have hBudget := uniform_spine_card_le D
  rw [hD] at hBudget
  change _ ≤ _ + 1 + uniformDeletedHubs D * k at hc
  change _ ≤ uniformDeletedHubs D * k at hl
  rw [Nat.mul_comm (uniformDeletedHubs D) k] at hc hl
  have hNC : ncDamage (host (uniformHub b)) D =
      Fintype.card (survivorGraph (host (uniformHub b)) D).ConnectedComponent - 1 := by
    simp [ncDamage, componentSizes]
  exact ⟨by omega, hl, by omega⟩

private theorem uniform_hubs_recover (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hh : uniformDeletedHubs D = b) : D = uniformHubDeletion b k q := by
  have hUniv : deletedHubIndices (uniformHub b) D = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, Fintype.card_fin, uniformDeletedHubs] using hh.ge
  symm
  apply Finset.eq_of_subset_of_card_le _ (by rw [hD, uniform_hub_deletion_card])
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  have hi : i ∈ deletedHubIndices (uniformHub b) D := hUniv.symm ▸ Finset.mem_univ _
  exact (Finset.mem_filter.mp hi).2

end UniformHubDeletion

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section HubProfile

variable {b k q : ℕ}

local notation "T" => uniformTailLength b k q
local notation "U" => UniformVertex b k q
local notation "H" => (host (uniformHub b) : SimpleGraph U)
local notation "A" => uniformHubDeletion b k q
local notation "HubSurvivorGraph" => survivorGraph H A

private theorem uniform_hub_mem (i : Fin b) : hostHub (t := T) (k := k) (uniformHub b) i ∈ A :=
  Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem uniform_hub_delete_spine_iff (i : Fin (2 * b + T)) :
    hostSpine (b := b) (k := k) i ∈ A ↔ ∃ j : Fin b, i.val = 2 * j.val + 1 := by
  constructor
  · intro h
    obtain ⟨j, _, he⟩ := Finset.mem_map.mp h
    exact ⟨j, (congrArg Fin.val (hostSpine.injective he)).symm⟩
  · rintro ⟨j, hj⟩
    have he : i = (uniformHub b j).castAdd T := Fin.ext hj
    rw [he]
    exact uniform_hub_mem j

private theorem uniform_hub_delete_tail_survives (i : Fin T) :
    tailVertex (p := 2 * b) (b := b) (k := k) i ∉ A := by
  intro hi
  obtain ⟨j, hj⟩ := (uniform_hub_delete_spine_iff _).mp hi
  have hb := j.isLt
  change 2 * b + i.val = 2 * j.val + 1 at hj
  omega

private def uniformHubTail (i : Fin T) : survivors A :=
  survivingTailVertex A i (uniform_hub_delete_tail_survives i)

private def uniformEvenIndex (i : Fin b) : Fin (2 * b + T) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

private def uniformEvenSurvivor (i : Fin b) : survivors A :=
  survivingSpine A (uniformEvenIndex i) (by
    rw [uniform_hub_delete_spine_iff]
    rintro ⟨j, hj⟩
    change 2 * i.val = 2 * j.val + 1 at hj
    omega)

private def uniformLeafSurvivor (a : Fin b × Fin k) : survivors A :=
  ⟨Sum.inr a, by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    change (Sum.inl _ : U) = Sum.inr a at hi
    cases hi⟩

private theorem uniform_even_no_adj (i : Fin b) (v : survivors A) :
    ¬ (HubSurvivorGraph).Adj (uniformEvenSurvivor i) v := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl j =>
    intro e
    change (pathGraph (2 * b + T)).Adj (uniformEvenIndex i) j at e
    apply hv
    apply (uniform_hub_delete_spine_iff j).mpr
    have hi := i.isLt
    rcases pathGraph_adj.mp e with h | h
    · exact ⟨i, h.symm⟩
    · change j.val + 1 = 2 * i.val at h
      exact ⟨⟨i.val - 1, by omega⟩, by dsimp; omega⟩
  | inr a =>
    intro e
    change uniformEvenIndex i = (uniformHub b a.1).castAdd T at e
    have he := congrArg Fin.val e
    change 2 * i.val = 2 * a.1.val + 1 at he
    omega

private theorem uniform_leaf_no_adj (a : Fin b × Fin k) (v : survivors A) :
    ¬ (HubSurvivorGraph).Adj (uniformLeafSurvivor a) v :=
  surviving_leaf_no_adj (uniformHub b) A a (uniformLeafSurvivor a).property
    (uniform_hub_mem a.1) v

private theorem uniform_hub_survivor_cases (v : survivors A) :
    (∃ i : Fin T, uniformHubTail i = v) ∨
      (∃ i : Fin b, uniformEvenSurvivor i = v) ∨
      (∃ a : Fin b × Fin k, uniformLeafSurvivor a = v) := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inr a => exact Or.inr (Or.inr ⟨a, rfl⟩)
  | inl i =>
    have hi := i.isLt
    by_cases h : i.val < 2 * b
    · right
      left
      have he : 2 * (i.val / 2) = i.val := by
        by_contra hodd
        apply hv
        apply (uniform_hub_delete_spine_iff i).mpr
        exact ⟨⟨i.val / 2, by omega⟩, by dsimp; omega⟩
      exact ⟨⟨i.val / 2, by omega⟩, Subtype.ext (congrArg Sum.inl (Fin.ext he))⟩
    · exact Or.inl ⟨⟨i.val - 2 * b, by omega⟩,
        Subtype.ext (congrArg Sum.inl (Fin.ext (by change 2 * b + (i.val - 2 * b) = i.val; omega)))⟩

private theorem uniform_hub_tail_reachable (z i : Fin T) (hz : z.val = 0) :
    (HubSurvivorGraph).Reachable (uniformHubTail z) (uniformHubTail i) :=
  tail_interval_reachable (uniformHub b) A (uniform_hub_delete_tail_survives z)
    (uniform_hub_delete_tail_survives i) (by omega)
    (fun j _ _ => uniform_hub_delete_tail_survives j)

private def uniformIsolated (a : Fin b ⊕ (Fin b × Fin k)) : survivors A :=
  a.elim uniformEvenSurvivor uniformLeafSurvivor

private theorem uniform_isolated_no_adj (a : Fin b ⊕ (Fin b × Fin k)) (v : survivors A) :
    ¬ (HubSurvivorGraph).Adj (uniformIsolated a) v := by
  cases a with
  | inl i => exact uniform_even_no_adj i v
  | inr l => exact uniform_leaf_no_adj l v

private theorem uniform_isolated_injective :
    Function.Injective (uniformIsolated (b := b) (k := k) (q := q)) := by
  intro a c h
  have he := congrArg Subtype.val h
  cases a with
  | inl i =>
    cases c with
    | inl j =>
      have hij : uniformEvenIndex (k := k) (q := q) i = uniformEvenIndex j :=
        Sum.inl_injective he
      have hn := congrArg Fin.val hij
      change 2 * i.val = 2 * j.val at hn
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr j =>
      change (Sum.inl _ : U) = Sum.inr j at he
      cases he
  | inr a =>
    cases c with
    | inl _ =>
      change (Sum.inr a : U) = Sum.inl _ at he
      cases he
    | inr c => exact congrArg Sum.inr (Sum.inr_injective he)

private theorem uniform_isolated_ne_tail (a : Fin b ⊕ (Fin b × Fin k)) (i : Fin T) :
    uniformIsolated a ≠ uniformHubTail i := by
  intro he
  have h := congrArg Subtype.val he
  cases a with
  | inl j =>
    have hi := j.isLt
    have hj := congrArg Fin.val (Sum.inl_injective h)
    change 2 * j.val = 2 * b + i.val at hj
    omega
  | inr j =>
    change (Sum.inr j : U) = Sum.inl _ at h
    cases h

private theorem uniform_hub_tail_pos (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    0 < T := by
  have hP := uniform_prefix_lt_q hb hq
  unfold uniformTailLength
  rw [Nat.add_mul, Nat.one_mul]
  omega

private def uniformHubComponent (z : Fin T) :
    Option (Fin b ⊕ (Fin b × Fin k)) → (HubSurvivorGraph).ConnectedComponent
  | none => (HubSurvivorGraph).connectedComponentMk (uniformHubTail z)
  | some a => (HubSurvivorGraph).connectedComponentMk (uniformIsolated a)

private theorem uniform_hub_component_bijective (z : Fin T) (hz : z.val = 0) :
    Function.Bijective (uniformHubComponent (k := k) z) := by
  constructor
  · intro a a' h
    cases a with
    | none =>
      cases a' with
      | none => rfl
      | some r =>
        have he := (component_eq_iff_of_no_adj (uniform_isolated_no_adj r) _).mp h.symm
        exact (uniform_isolated_ne_tail r z he).elim
    | some r =>
      cases a' with
      | none =>
        have he := (component_eq_iff_of_no_adj (uniform_isolated_no_adj r) _).mp h
        exact (uniform_isolated_ne_tail r z he).elim
      | some r' =>
        exact congrArg some (uniform_isolated_injective
          ((component_eq_iff_of_no_adj (uniform_isolated_no_adj r) _).mp h))
  · intro C
    obtain ⟨v, rfl⟩ := C.exists_rep
    rcases uniform_hub_survivor_cases v with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨none, ConnectedComponent.eq.mpr (uniform_hub_tail_reachable z i hz)⟩
    · exact ⟨some (.inl i), rfl⟩
    · exact ⟨some (.inr a), rfl⟩

private theorem uniform_hub_tail_supp (z : Fin T) (hz : z.val = 0) :
    (uniformHubComponent (k := k) z none).supp.toFinset =
      survivingTailVertices (uniformHub b) A := by
  ext v
  rcases uniform_hub_survivor_cases v with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨a, rfl⟩
  · exact iff_of_true
      (Set.mem_toFinset.mpr ((ConnectedComponent.mem_supp_iff _ _).mpr
        (ConnectedComponent.eq.mpr (uniform_hub_tail_reachable z i hz).symm)))
      (survivingTailVertex_mem (uniformHub b) A i (uniform_hub_delete_tail_survives i))
  · apply iff_of_false
    · intro h
      have he := (ConnectedComponent.mem_supp_iff _ _).mp (Set.mem_toFinset.mp h)
      exact uniform_isolated_ne_tail (.inl i) z
        ((component_eq_iff_of_no_adj (uniform_even_no_adj i) _).mp he)
    · intro h
      have hi := (Finset.mem_filter.mp h).2
      change 2 * b ≤ 2 * i.val at hi
      have := i.isLt
      omega
  · apply iff_of_false
    · intro h
      have he := (ConnectedComponent.mem_supp_iff _ _).mp (Set.mem_toFinset.mp h)
      exact uniform_isolated_ne_tail (.inr a) z
        ((component_eq_iff_of_no_adj (uniform_leaf_no_adj a) _).mp he)
    · intro h
      exact (Nat.not_le_of_gt (uniformHub b a.1).isLt) (Finset.mem_filter.mp h).2

private theorem uniform_hub_tail_size (z : Fin T) (hz : z.val = 0) :
    (uniformHubComponent (k := k) z none).supp.toFinset.card = T := by
  rw [uniform_hub_tail_supp z hz, survivingTailVertices_card]
  have h : deletedTailIndices (uniformHubDeletion b k q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact uniform_hub_delete_tail_survives i (Finset.mem_filter.mp hi).2
  simp [h]

private theorem uniform_isolated_supp (a : Fin b ⊕ (Fin b × Fin k)) :
    ((HubSurvivorGraph).connectedComponentMk (uniformIsolated a)).supp.toFinset =
      {uniformIsolated a} := by
  ext v
  rw [Set.mem_toFinset, ConnectedComponent.mem_supp_iff, Finset.mem_singleton]
  exact ⟨fun h => ((component_eq_iff_of_no_adj (uniform_isolated_no_adj a) v).mp h.symm).symm,
    fun h => congrArg (HubSurvivorGraph).connectedComponentMk h⟩

set_option maxHeartbeats 1000000 in
/-- The component index none denotes the intact tail. The two summands of
some denote the b even prefix vertices and bk pendant vertices respectively. -/
private theorem uniform_hub_deletion_profile (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    ∃ e : Option (Fin b ⊕ (Fin b × Fin k)) ≃ (HubSurvivorGraph).ConnectedComponent,
      (e none).supp.toFinset = survivingTailVertices (uniformHub b) A ∧
      (e none).supp.toFinset.card = T ∧
      (∀ i, (e (some (.inl i))).supp.toFinset = {uniformEvenSurvivor i}) ∧
      (∀ a, (e (some (.inr a))).supp.toFinset = {uniformLeafSurvivor a}) := by
  let z : Fin T := ⟨0, uniform_hub_tail_pos hb hq⟩
  let e := Equiv.ofBijective (uniformHubComponent (k := k) z)
    (uniform_hub_component_bijective z rfl)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (uniformHubComponent (k := k) z none).supp.toFinset =
      survivingTailVertices (uniformHub b) A
    exact uniform_hub_tail_supp (k := k) z rfl
  · change (uniformHubComponent (k := k) z none).supp.toFinset.card = T
    exact uniform_hub_tail_size (k := k) z rfl
  · intro i
    exact uniform_isolated_supp (q := q) (.inl i)
  · intro a
    exact uniform_isolated_supp (q := q) (.inr a)

private theorem uniform_hub_deletion_componentSizes (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    componentSizes H A = T ::ₘ Multiset.replicate (b + b * k) 1 := by
  obtain ⟨e, _, ht, hp, hl⟩ := uniform_hub_deletion_profile (k := k) hb hq
  let c (C : (HubSurvivorGraph).ConnectedComponent) := C.supp.toFinset.card
  let C := e none
  let S := (Finset.univ : Finset (HubSurvivorGraph).ConnectedComponent).erase C
  have hn : C ∉ S := Finset.notMem_erase _ _
  have hc : S.card = b + b * k := by
    have he := Fintype.card_congr e
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin] at he
    change (Finset.univ.erase C).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← he]
    omega
  have hs (D : (HubSurvivorGraph).ConnectedComponent) (hd : D ∈ S.val) : c D = 1 := by
    have hne : D ≠ C := Finset.ne_of_mem_erase (Finset.mem_val.mp hd)
    obtain ⟨a, rfl⟩ := e.surjective D
    cases a with
    | none => exact (hne rfl).elim
    | some a =>
      cases a with
      | inl i =>
        change (e (some (.inl i))).supp.toFinset.card = 1
        rw [hp i, Finset.card_singleton]
      | inr a =>
        change (e (some (.inr a))).supp.toFinset.card = 1
        rw [hl a, Finset.card_singleton]
  have hu : insert C S = Finset.univ := Finset.insert_erase (Finset.mem_univ C)
  change Finset.univ.val.map c = _
  have hMap : S.val.map c = Multiset.replicate (b + b * k) 1 := by
    calc
      _ = S.val.map (fun _ => 1) := Multiset.map_congr rfl hs
      _ = _ := by rw [Multiset.map_const', ← Finset.card_def, hc]
  rw [← hu, Finset.insert_val_of_notMem hn, Multiset.map_cons, show c C = T from ht, hMap]

private theorem uniform_hub_deletion_nc (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    ncDamage H A = b * (k + 1) := by
  rw [ncDamage, uniform_hub_deletion_componentSizes hb hq]
  simp [Nat.mul_succ, Nat.add_comm]

theorem uniform_hub_deletion_unique_nc_optimizer
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset U) (hD : D.card = b) :
    ncDamage H D ≤ ncDamage H A ∧ (ncDamage H D = ncDamage H A ↔ D = A) := by
  have hCount : uniformDeletedHubs D ≤ b := by
    unfold uniformDeletedHubs
    simpa only [Fintype.card_fin] using Finset.card_le_univ (deletedHubIndices (uniformHub b) D)
  have hUpper := (uniform_nc_upper_bound D hD).2.2
  have hScore : ncDamage H A = b + k * b := by
    simpa only [Nat.mul_succ, Nat.mul_comm b k, Nat.add_comm (k * b)] using
      uniform_hub_deletion_nc (k := k) hb hq
  rw [hScore]
  constructor
  · exact hUpper.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k hCount) _)
  · constructor
    · intro he
      apply uniform_hubs_recover D hD
      by_contra hne
      have hs : uniformDeletedHubs D < b := lt_of_le_of_ne hCount hne
      have hstrict := Nat.mul_lt_mul_of_pos_left hs (by omega : 0 < k)
      omega
    · rintro rfl
      exact hScore

end HubProfile

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section Transfer

variable {b k q : ℕ}

local notation "T" => uniformTailLength b k q
local notation "P" => b * (k + 2)
local notation "n" => (b + 1) * q + b
local notation "U" => UniformVertex b k q
local notation "H" => (host (uniformHub b) : SimpleGraph U)
local notation "A" => uniformHubDeletion b k q

theorem uniform_order (hq : 2 * b * (k + 2) ≤ q) :
    Fintype.card U = n := by
  have h := uniform_survivor_card hq A (uniform_hub_deletion_card b k q)
  rw [Finset.card_compl, uniform_hub_deletion_card] at h
  have hn := Finset.card_le_univ A
  rw [uniform_hub_deletion_card] at hn
  omega

private theorem uniform_hub_deletion_pair_and_largest_scores
    (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    pcDamage H A = (n).choose 2 - (T).choose 2 ∧ lccDamage H A = P := by
  have h := uniform_hub_deletion_componentSizes hb hq
  have hTail := uniform_hub_tail_pos hb hq
  constructor
  · simp [pcDamage, h, uniform_order hq, Multiset.map_replicate]
  · have hSup : (T ::ₘ Multiset.replicate (b + b * k) 1).sup = T := by
      apply le_antisymm
      · apply Multiset.sup_le.mpr
        intro v hv
        rcases Multiset.mem_cons.mp hv with rfl | hv
        · exact le_rfl
        · rw [Multiset.eq_of_mem_replicate hv]
          exact hTail
      · exact Multiset.le_sup (Multiset.mem_cons_self _ _)
    rw [lccDamage, h, hSup, uniform_order hq]
    have hP := uniform_prefix_le_q hq
    unfold uniformTailLength
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem uniform_balanced_nc (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 2 * b * (k + 2) ≤ q) : ncDamage H (uniformBalancedDeletion hq) = b := by
  obtain ⟨_, _, hCard, _⟩ := uniform_balanced_deletion_profile hb hk hq
  rw [ncDamage]
  simp [componentSizes, hCard]

theorem damageMaximum_eq_of_dominates {V : Type*} [DecidableEq V] [Fintype V]
    (score : Finset V → ℕ) (b : ℕ) (D : Finset V) (hD : D.card = b)
    (h : ∀ E : Finset V, E.card = b → score E ≤ score D) :
    damageMaximum score b = score D := by
  apply le_antisymm
  · apply Finset.sup_le
    intro E hE
    exact h E (Finset.mem_powersetCard.mp hE).2
  · exact Finset.le_sup (f := score) (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD⟩)

theorem uniform_exact_budget_maxima (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 2 * b * (k + 2) ≤ q) :
    (damageMaximum (ncDamage H) b = ncDamage H A ∧
      damageMaximum (pcDamage H) b = pcDamage H (uniformBalancedDeletion hq) ∧
      damageMaximum (lccDamage H) b = lccDamage H (uniformBalancedDeletion hq)) ∧
    (damageMaximum (ncDamage H) b = b * (k + 1) ∧
      damageMaximum (pcDamage H) b = (n).choose 2 - (b + 1) * q.choose 2 ∧
      damageMaximum (lccDamage H) b = b * (q + 1)) ∧
    (0 < damageMaximum (ncDamage H) b ∧ 0 < damageMaximum (pcDamage H) b ∧
      0 < damageMaximum (lccDamage H) b) := by
  let B := uniformBalancedDeletion hq
  have hB := uniform_balanced_deletion_card hq
  have hNC := damageMaximum_eq_of_dominates (ncDamage H) b A
    (uniform_hub_deletion_card b k q)
    (fun E hE => (uniform_hub_deletion_unique_nc_optimizer hb hk hq E hE).1)
  have hPC := damageMaximum_eq_of_dominates (pcDamage H) b B hB
    (fun E hE => (uniform_balanced_deletion_unique_optimizer hb hk hq E hE).1)
  have hLCC := damageMaximum_eq_of_dominates (lccDamage H) b B hB
    (fun E hE => (uniform_balanced_deletion_unique_optimizer hb hk hq E hE).2.1)
  obtain ⟨hPc, hLcc⟩ := uniform_balanced_deletion_scores hb hk hq
  rw [uniform_order hq] at hPc hLcc
  have hNC' := hNC.trans (uniform_hub_deletion_nc hb hq)
  have hPC' := hPC.trans hPc
  have hLCC' : damageMaximum (lccDamage H) b = b * (q + 1) := by
    rw [hLCC, hLcc, Nat.add_mul, Nat.one_mul, Nat.mul_succ]
    omega
  have hPos := balanced_pair_target_positive (show 2 ≤ b + 1 by omega)
    (uniform_prefix_lt_q hb hq).pos (show (b + 1) * q ≤ n by omega)
  refine ⟨⟨hNC, hPC, hLCC⟩, ⟨hNC', hPC', hLCC'⟩, ?_⟩
  rw [hNC', hPC', hLCC']
  exact ⟨Nat.mul_pos (by omega) (by omega), Nat.sub_pos_of_lt hPos,
    Nat.mul_pos (by omega) (by omega)⟩

noncomputable def damageRatio {V : Type*} [DecidableEq V] [Fintype V]
    (target : Finset V → ℕ) (b : ℕ) (D : Finset V) : ℝ :=
  (target D : ℝ) / (damageMaximum target b : ℝ)

/-- The four ratios hold pointwise for every exact source-optimal deletion. -/
theorem uniform_transfer_identities (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 2 * b * (k + 2) ≤ q)
    (Dn Dp Dl : Finset U) (hn : Dn.card = b) (hp : Dp.card = b) (hl : Dl.card = b)
    (on : ncDamage H Dn = damageMaximum (ncDamage H) b)
    (op : pcDamage H Dp = damageMaximum (pcDamage H) b)
    (ol : lccDamage H Dl = damageMaximum (lccDamage H) b) :
    damageRatio (ncDamage H) b Dp = 1 / ((k : ℝ) + 1) ∧
    damageRatio (ncDamage H) b Dl = 1 / ((k : ℝ) + 1) ∧
    damageRatio (lccDamage H) b Dn = (P : ℕ) / (↑(b * (q + 1)) : ℝ) ∧
    damageRatio (pcDamage H) b Dn =
      (↑((n).choose 2 - (T).choose 2 : ℕ) : ℝ) /
        (↑((n).choose 2 - (b + 1) * q.choose 2 : ℕ) : ℝ) := by
  obtain ⟨⟨hNa, hPa, hLa⟩, ⟨hN, hP, hL⟩, _⟩ := uniform_exact_budget_maxima hb hk hq
  have en := (uniform_hub_deletion_unique_nc_optimizer hb hk hq Dn hn).2.mp (on.trans hNa)
  have ep := (uniform_balanced_deletion_unique_optimizer hb hk hq Dp hp).2.2.mp
    (Or.inl (op.trans hPa))
  have el := (uniform_balanced_deletion_unique_optimizer hb hk hq Dl hl).2.2.mp
    (Or.inr (ol.trans hLa))
  subst Dn
  subst Dp
  subst Dl
  obtain ⟨hanP, hanL⟩ := uniform_hub_deletion_pair_and_largest_scores hb hq
  simp only [damageRatio, hN, hP, hL, hanP, hanL, uniform_balanced_nc hb hk hq]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hk' : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  constructor
  · field_simp [hb', hk']
  · field_simp [hb', hk']
    exact ⟨trivial, trivial, trivial⟩

end Transfer

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section Epsilon

variable {b k q : ℕ}

local notation "T" => uniformTailLength b k q
local notation "P" => b * (k + 2)
local notation "n" => (b + 1) * q + b

theorem uniform_pc_transfer_bound (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    (↑((n).choose 2 - (T).choose 2 : ℕ) : ℝ) /
      (↑((n).choose 2 - (b + 1) * q.choose 2 : ℕ) : ℝ) ≤
        (↑(4 * P : ℕ) : ℝ) / (↑(b * q) : ℝ) := by
  have hq0 := (uniform_prefix_lt_q hb hq).pos
  have hP := uniform_prefix_le_q hq
  have hqt : q ≤ (b + 1) * q := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hSum : T + P = n := Nat.sub_add_cancel (by omega : P ≤ n)
  have hSq : (n) ^ 2 = T ^ 2 + P * (n + T) := by rw [← hSum]; ring
  have hMon := Nat.choose_le_choose 2 (show T ≤ n by omega)
  have hTwiceN := twice_choose_two_add (n)
  have hTwiceT := twice_choose_two_add (T)
  have hMul := Nat.mul_le_mul_left P (show n + T ≤ 2 * n by omega)
  rw [Nat.mul_left_comm _ 2] at hMul
  have hNum : (n).choose 2 - (T).choose 2 ≤ P * n := by omega
  have hChoose := Nat.choose_le_choose 2 (show (b + 1) * q ≤ n by omega)
  have hTwiceBase := twice_choose_two_add ((b + 1) * q)
  have hBal : 2 * ((b + 1) * q.choose 2) + (b + 1) * q = (b + 1) * q ^ 2 := by
    calc
      _ = (b + 1) * (2 * q.choose 2 + q) := by ring
      _ = _ := by rw [twice_choose_two_add]
  have hBaseSq : ((b + 1) * q) ^ 2 = (b + 1) * q ^ 2 + b * ((b + 1) * q ^ 2) := by
    ring
  have hDen : b * ((b + 1) * q ^ 2) ≤ 2 * ((n).choose 2 - (b + 1) * q.choose 2) := by
    omega
  have hDenPos := balanced_pair_target_positive (show 2 ≤ b + 1 by omega) hq0
    (show (b + 1) * q ≤ n by omega)
  have hn : n ≤ 2 * ((b + 1) * q) := by
    have hq1 := Nat.mul_le_mul_left b (show 1 ≤ q by omega)
    rw [Nat.mul_one] at hq1
    rw [Nat.add_mul, Nat.one_mul] at *
    omega
  apply (div_le_div_iff₀ ?_ ?_).mpr
  · exact_mod_cast (show
      ((n).choose 2 - (T).choose 2) * (b * q) ≤
        (4 * P) * ((n).choose 2 - (b + 1) * q.choose 2) by
      calc
        _ ≤ (P * n) * (b * q) := Nat.mul_le_mul_right _ hNum
        _ ≤ (P * (2 * ((b + 1) * q))) * (b * q) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
        _ = (2 * P) * (b * ((b + 1) * q ^ 2)) := by ring
        _ ≤ (2 * P) * (2 * ((n).choose 2 - (b + 1) * q.choose 2)) :=
          Nat.mul_le_mul_left _ hDen
        _ = _ := by ring)
  · exact_mod_cast Nat.sub_pos_of_lt hDenPos
  · exact_mod_cast Nat.mul_pos (show 0 < b by omega) hq0

theorem uniform_lcc_transfer_bound (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    (↑(P : ℕ) : ℝ) / (↑(b * (q + 1)) : ℝ) ≤ (↑(4 * P : ℕ) : ℝ) / (↑(b * q) : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (uniform_prefix_lt_q hb hq).pos
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h : (b : ℝ) * q ≤ 4 * ((b : ℝ) * ((q : ℝ) + 1)) := by
    have hp : 0 ≤ (b : ℝ) * q := by positivity
    nlinarith
  have hp : 0 ≤ (b : ℝ) * ((k : ℝ) + 2) := by positivity
  have hs := mul_le_mul_of_nonneg_left h hp
  linarith only [show (b : ℝ) * ((k : ℝ) + 2) * ((b : ℝ) * q) ≤
    4 * ((b : ℝ) * ((k : ℝ) + 2)) * ((b : ℝ) * ((q : ℝ) + 1)) by
    calc
      _ ≤ (b : ℝ) * ((k : ℝ) + 2) * (4 * ((b : ℝ) * ((q : ℝ) + 1))) := hs
      _ = _ := by ring]

/-- For each exact budget at least two, one host makes all four transfers
strictly smaller than epsilon, for every choice of source-optimal deletions. -/
theorem uniform_simultaneous_epsilon (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ k q : ℕ, 1 ≤ k ∧ 2 * b * (k + 2) ≤ q ∧
      (let H : SimpleGraph (UniformVertex b k q) := host (uniformHub b)
       (0 < damageMaximum (ncDamage H) b ∧ 0 < damageMaximum (pcDamage H) b ∧
          0 < damageMaximum (lccDamage H) b) ∧
       ∀ Dn Dp Dl : Finset (UniformVertex b k q), Dn.card = b → Dp.card = b → Dl.card = b →
         ncDamage H Dn = damageMaximum (ncDamage H) b →
         pcDamage H Dp = damageMaximum (pcDamage H) b →
         lccDamage H Dl = damageMaximum (lccDamage H) b →
         damageRatio (ncDamage H) b Dp < ε ∧ damageRatio (ncDamage H) b Dl < ε ∧
           damageRatio (lccDamage H) b Dn < ε ∧ damageRatio (pcDamage H) b Dn < ε) := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / ε)
  let k := k₀ + 1
  have hk : 1 ≤ k := Nat.succ_pos k₀
  have hkLarge : 1 / ε < (k : ℝ) + 1 := by push_cast [k]; linarith
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt (4 * ((k : ℝ) + 2) / ε)
  let q := q₀ + 2 * b * (k + 2)
  have hq : 2 * b * (k + 2) ≤ q := Nat.le_add_left _ _
  have hqLarge : 4 * ((k : ℝ) + 2) / ε < (q : ℝ) :=
    hq₀.trans_le (by exact_mod_cast (show q₀ ≤ q from Nat.le_add_right _ _))
  have hNC : 1 / ((k : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    exact (div_lt_iff₀ hε).mp hkLarge |>.trans_eq (mul_comm _ _)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (uniform_prefix_lt_q hb hq).pos
  have hCross : (↑(4 * b * (k + 2) : ℕ) : ℝ) / (↑(b * q) : ℝ) < ε := by
    push_cast
    apply (div_lt_iff₀ (by positivity)).mpr
    have ha := mul_lt_mul_of_pos_left ((div_lt_iff₀ hε).mp hqLarge) hb0
    convert ha using 1 <;> ring
  refine ⟨k, q, hk, hq, (uniform_exact_budget_maxima hb hk hq).2.2, ?_⟩
  intro Dn Dp Dl hn hp hl on op ol
  obtain ⟨e₁, e₂, e₃, e₄⟩ := uniform_transfer_identities hb hk hq Dn Dp Dl hn hp hl on op ol
  rw [e₁, e₂, e₃, e₄]
  have hBound : (↑(4 * (b * (k + 2)) : ℕ) : ℝ) / (↑(b * q) : ℝ) < ε := by
    simpa only [Nat.mul_assoc] using hCross
  exact ⟨hNC, hNC, (uniform_lcc_transfer_bound hb hq).trans_lt hBound,
    (uniform_pc_transfer_bound hb hq).trans_lt hBound⟩

end Epsilon

end Ugurlu33528
