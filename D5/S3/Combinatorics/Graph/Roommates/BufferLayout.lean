/- GID: D5/S3/Combinatorics/Graph/Roommates/BufferLayout
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/BufferLayout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Finite clique matchings joined through central vertices give the six-buffer completion. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 32
namespace D5.S3.Combinatorics.Graph.Roommates.BufferLayout

/-- The four boundary sites already reserved for old partners. -/
def occupied (b : Fin 4 → Bool) : Fin 6 → Bool :=
  ![b 0, b 1, false, false, b 2, b 3]

/-- A finite clique can be paired with only its distinguished vertex possibly single. -/
private theorem clique_partner {α : Type} (G : SimpleGraph α) (s : Set α)
    (hs : s.Finite) (c : α) (hc : c ∈ s) (hcl : G.IsClique s) :
    ∃ f : α → α, Function.Involutive f ∧
      (∀ x, x ∉ s → f x = x) ∧
      (∀ x, x ∈ s → f x = x → x = c) ∧
      (∀ x, f x ≠ x → G.Adj x (f x)) := by
  classical
  have he : ∃ u : Set α, u ⊆ s ∧ (∀ x, x ∈ s → x ∉ u → x = c) ∧
      ∃ M : G.Subgraph, M.verts = u ∧ M.IsMatching := by
    by_cases hp : Even s.ncard
    · exact ⟨s, Set.Subset.rfl, by simp, (hcl.even_iff_exists_isMatching hs).mp hp⟩
    · have hp' : Even (s \ {c}).ncard := by
        have hn := Set.ncard_sdiff_singleton_add_one hc hs
        rw [← hn, Nat.even_add_one] at hp
        simpa only [not_not] using hp
      refine ⟨s \ {c}, Set.sdiff_subset, ?_,
        ((hcl.subset Set.sdiff_subset).even_iff_exists_isMatching (hs.sdiff _)).mp hp'⟩
      intro x hx hxu
      simpa only [Set.mem_sdiff, Set.mem_singleton_iff, hx, true_and, not_not] using hxu
  obtain ⟨u, hus, hmissing, M, hverts, hM⟩ := he
  let f : α → α := fun x => if hx : x ∈ M.verts then (hM hx).choose else x
  have ha (x : α) (hx : x ∈ M.verts) : M.Adj x (f x) := by
    simpa only [f, dif_pos hx] using (hM hx).choose_spec.1
  have hi : Function.Involutive f := by
    intro x
    by_cases hx : x ∈ M.verts
    · have hax := ha x hx
      have hfx := hax.snd_mem
      exact hM.eq_of_adj_left (ha (f x) hfx) hax.symm
    · simp only [f, dif_neg hx]
  refine ⟨f, hi, ?_, ?_, ?_⟩
  · intro x hx
    have hn : x ∉ M.verts := by rw [hverts]; exact fun h => hx (hus h)
    exact dif_neg hn
  · intro x hx hfix
    apply hmissing x hx
    intro hxu
    have ha' := ha x (hverts.symm ▸ hxu)
    rw [hfix] at ha'
    exact G.irrefl x (M.adj_sub ha')
  · intro x hx
    have hm : x ∈ M.verts := by
      by_contra hn
      exact hx (dif_neg hn)
    exact M.adj_sub (ha x hm)

/-- Joining two disjoint cliques through their hubs leaves at most one single.
The construction applies to arbitrary finite cliques, without a cardinality bound. -/
private theorem two_clique_partner {α : Type} (G : SimpleGraph α) (s t : Set α)
    (hs : s.Finite) (ht : t.Finite) (hdis : Disjoint s t)
    (c d : α) (hc : c ∈ s) (hd : d ∈ t)
    (hsc : G.IsClique s) (htc : G.IsClique t) (hcd : G.Adj c d) :
    ∃ f : α → α, Function.Involutive f ∧
      (∀ x, x ∉ s ∪ t → f x = x) ∧
      (∀ x, f x ≠ x → G.Adj x (f x)) ∧
      (∀ x, x ∈ s ∪ t → f x = x → x = c ∨ x = d) ∧
      (∀ x y, x ∈ s ∪ t → y ∈ s ∪ t → f x = x → f y = y → x = y) := by
  classical
  obtain ⟨f, hfi, hfo, hfc, hfa⟩ := clique_partner G s hs c hc hsc
  obtain ⟨g, hgi, hgo, hgc, hga⟩ := clique_partner G t ht d hd htc
  have hdst : ∀ x, x ∈ s → x ∉ t := fun x hx hy => Set.disjoint_left.mp hdis hx hy
  have hmemf (x : α) : f x ∈ s ↔ x ∈ s := by
    constructor
    · intro h; by_contra hn; simpa only [hfo x hn] using h
    · intro h; by_contra hn; have := hfo (f x) hn; rw [hfi x] at this; exact hn (this ▸ h)
  have hmemg (x : α) : g x ∈ t ↔ x ∈ t := by
    constructor
    · intro h; by_contra hn; simpa only [hgo x hn] using h
    · intro h; by_contra hn; have := hgo (g x) hn; rw [hgi x] at this; exact hn (this ▸ h)
  let k : α → α := fun x => if x ∈ s then f x else g x
  have hki : Function.Involutive k := by
    intro x
    by_cases hx : x ∈ s
    · simp only [k, if_pos hx, if_pos ((hmemf x).mpr hx), hfi x]
    · have hgx : g x ∉ s := by
        by_cases hxt : x ∈ t
        · exact fun h => hdst _ h ((hmemg x).mpr hxt)
        · simpa only [hgo x hxt] using hx
      simp only [k, if_neg hx, if_neg hgx, hgi x]
  have hko (x : α) (hx : x ∉ s ∪ t) : k x = x := by
    simp only [Set.mem_union, not_or] at hx
    simp only [k, if_neg hx.1, hgo x hx.2]
  have hka (x : α) (hx : k x ≠ x) : G.Adj x (k x) := by
    by_cases hxs : x ∈ s
    · simp only [k, if_pos hxs] at hx ⊢; exact hfa x hx
    · simp only [k, if_neg hxs] at hx ⊢; exact hga x hx
  have hkfix (x : α) (hx : x ∈ s ∪ t) (he : k x = x) : x = c ∨ x = d := by
    by_cases hxs : x ∈ s
    · exact Or.inl (hfc x hxs (by simpa only [k, if_pos hxs] using he))
    · exact Or.inr (hgc x (hx.resolve_left hxs) (by simpa only [k, if_neg hxs] using he))
  have hne : c ≠ d := fun h => hdst c hc (h ▸ hd)
  by_cases hp : k c = c ∧ k d = d
  · let q : α → α := fun x => if x = c then d else if x = d then c else k x
    have hqoff (x : α) (hxc : x ≠ c) (hxd : x ≠ d) : k x ≠ c ∧ k x ≠ d := by
      constructor
      · intro he; have := congrArg k he; rw [hki x, hp.1] at this; exact hxc this
      · intro he; have := congrArg k he; rw [hki x, hp.2] at this; exact hxd this
    have hqi : Function.Involutive q := by
      intro x
      by_cases hxc : x = c
      · subst x; simp only [q, if_pos rfl, if_neg hne.symm]
      by_cases hxd : x = d
      · subst x; simp only [q, if_neg hne.symm, if_pos rfl]
      have hh := hqoff x hxc hxd
      simp only [q, if_neg hxc, if_neg hxd, if_neg hh.1, if_neg hh.2, hki x]
    have hqfix (x : α) (he : q x = x) : x ≠ c ∧ x ≠ d ∧ k x = x := by
      by_cases hxc : x = c
      · subst x; simp only [q, if_pos rfl] at he; exact (hne he.symm).elim
      by_cases hxd : x = d
      · subst x; simp only [q, if_neg hne.symm, if_pos rfl] at he; exact (hne he).elim
      exact ⟨hxc, hxd, by simpa only [q, if_neg hxc, if_neg hxd] using he⟩
    refine ⟨q, hqi, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxc : x ≠ c := fun h => hx (Or.inl (h ▸ hc))
      have hxd : x ≠ d := fun h => hx (Or.inr (h ▸ hd))
      simpa only [q, if_neg hxc, if_neg hxd] using hko x hx
    · intro x hx
      by_cases hxc : x = c
      · subst x; simpa only [q, if_pos rfl] using hcd
      by_cases hxd : x = d
      · subst x; simpa only [q, if_neg hne.symm, if_pos rfl] using hcd.symm
      simp only [q, if_neg hxc, if_neg hxd] at hx ⊢; exact hka x hx
    · intro x hx he
      have hh := hqfix x he
      exact (hkfix x hx hh.2.2).elim (fun h => (hh.1 h).elim) (fun h => (hh.2.1 h).elim)
    · intro x y hx _ he _
      have hh := hqfix x he
      exact (hkfix x hx hh.2.2).elim (fun h => (hh.1 h).elim) (fun h => (hh.2.1 h).elim)
  · refine ⟨k, hki, hko, hka, hkfix, ?_⟩
    intro x y hx hy hfx hfy
    rcases hkfix x hx hfx with rfl | rfl <;> rcases hkfix y hy hfy with rfl | rfl
    · rfl
    · exact (hp ⟨hfx, hfy⟩).elim
    · exact (hp ⟨hfy, hfx⟩).elim
    · rfl

private def bufferGraph : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ i.val ≤ j.val + 2 ∧ j.val ≤ i.val + 2
  symm := by intro i j h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by intro i h; exact h.1 rfl

private def leftFree (b : Fin 4 → Bool) : Set (Fin 6) :=
  {i | i.val ≤ 2 ∧ occupied b i = false}

private def rightFree (b : Fin 4 → Bool) : Set (Fin 6) :=
  {i | 3 ≤ i.val ∧ occupied b i = false}

private theorem free_union (b : Fin 4 → Bool) (i : Fin 6) :
    i ∈ leftFree b ∪ rightFree b ↔ occupied b i = false := by
  change (i.val ≤ 2 ∧ _ ) ∨ (3 ≤ i.val ∧ _) ↔ _
  omega

private theorem layout_exists (b : Fin 4 → Bool) :
    ∃ f : Fin 6 → Fin 6, Function.Involutive f ∧
    (∀ i, occupied b i = true → f i = i) ∧
    (∀ i, f i ≠ i → occupied b (f i) = false) ∧
    (∀ i, (f i).val ≤ i.val + 2 ∧ i.val ≤ (f i).val + 2) ∧
    (∀ i, occupied b i = false → f i = i → i = 2 ∨ i = 3) ∧
    (∀ i j, occupied b i = false → f i = i →
      i ≠ j → i.val ≤ j.val + 2 → j.val ≤ i.val + 2 →
      occupied b j = true ∨ f j ≠ j) := by
  classical
  have hl : (2 : Fin 6) ∈ leftFree b := by simp [leftFree, occupied]
  have hr : (3 : Fin 6) ∈ rightFree b := by simp [rightFree, occupied]
  have hd : Disjoint (leftFree b) (rightFree b) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    have := hi.1; have := hj.1; omega
  have hcl : bufferGraph.IsClique (leftFree b) := by
    intro i hi j hj hij
    exact ⟨hij, by have := hi.1; have := hj.1; omega⟩
  have hcr : bufferGraph.IsClique (rightFree b) := by
    intro i hi j hj hij
    exact ⟨hij, by have := hi.1; have := hj.1; have := i.isLt; have := j.isLt; omega⟩
  obtain ⟨f, hfi, hfo, hfa, hfc, hsingle⟩ := two_clique_partner bufferGraph
    (leftFree b) (rightFree b) (Set.toFinite _) (Set.toFinite _) hd 2 3 hl hr hcl hcr (by decide)
  have hocc (i : Fin 6) (hi : occupied b i = true) : f i = i := by
    apply hfo
    rw [free_union]
    simp only [hi, Bool.true_eq_false, not_false_eq_true]
  refine ⟨f, hfi, hocc, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_contra hn
    have hh : occupied b (f i) = true := by cases h : occupied b (f i) <;> simp_all
    have he := hocc (f i) hh
    rw [hfi i] at he
    exact hi he.symm
  · intro i
    by_cases hi : f i = i
    · rw [hi]; omega
    · exact ⟨(hfa i hi).2.2, (hfa i hi).2.1⟩
  · intro i hi he; exact hfc i ((free_union b i).mpr hi) he
  · intro i j hi he hij _ _
    by_cases hj : occupied b j = true
    · exact Or.inl hj
    · right
      intro hej
      have hj' : occupied b j = false := by cases h : occupied b j <;> simp_all
      exact hij (hsingle i j ((free_union b i).mpr hi) ((free_union b j).mpr hj') he hej)

/-- Pairing chosen from the general two-clique construction. -/
noncomputable def mate (b : Fin 4 → Bool) : Fin 6 → Fin 6 :=
  Classical.choose (layout_exists b)

/-- The six-site specialization of the arbitrary finite-clique construction. -/
theorem buffer_completion (b : Fin 4 → Bool) :
    Function.Involutive (mate b) ∧
    (∀ i, occupied b i = true → mate b i = i) ∧
    (∀ i, mate b i ≠ i → occupied b (mate b i) = false) ∧
    (∀ i, (mate b i).val ≤ i.val + 2 ∧ i.val ≤ (mate b i).val + 2) ∧
    (∀ i, occupied b i = false → mate b i = i → i = 2 ∨ i = 3) ∧
    (∀ i j, occupied b i = false → mate b i = i →
      i ≠ j → i.val ≤ j.val + 2 → j.val ≤ i.val + 2 →
      occupied b j = true ∨ mate b j ≠ j) := Classical.choose_spec (layout_exists b)


open scoped Classical

/-- Boundary sites at which old requests can land. -/
def boundarySite : Fin 4 → Fin 6 := ![0, 1, 4, 5]

noncomputable def flags {α : Type} (request : α → Fin 6) : Fin 4 → Bool :=
  fun j => decide (∃ a, request a = boundarySite j)

theorem occupied_iff {α : Type} (request : α → Fin 6)
    (hcentral : ∀ a, request a ≠ 2 ∧ request a ≠ 3) (i : Fin 6) :
    occupied (flags request) i = true ↔ ∃ a, request a = i := by
  classical
  fin_cases i <;> simp [occupied, flags, boundarySite, hcentral, decide_eq_true_eq,
    show ¬ (∃ a, request a = 2) from fun ⟨a, h⟩ => (hcentral a).1 h,
    show ¬ (∃ a, request a = 3) from fun ⟨a, h⟩ => (hcentral a).2 h]
  all_goals exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩

/-- Every request is fulfilled. Unreserved buffer sites use the local layout. -/
noncomputable def partner {α : Type} (request : α → Fin 6) :
    Sum α (Fin 6) → Sum α (Fin 6)
  | .inl a => .inr (request a)
  | .inr i => if h : ∃ a, request a = i then .inl (Classical.choose h)
      else .inr (mate (flags request) i)

/-- Completion handles an arbitrary injective family of exterior requests.
It produces an actual involution, rather than a list of small examples. -/
theorem complete_requests {α : Type} (request : α → Fin 6)
    (hinj : Function.Injective request)
    (hcentral : ∀ a, request a ≠ 2 ∧ request a ≠ 3) :
    Function.Involutive (partner request) ∧
    (∀ a, partner request (.inl a) = .inr (request a)) ∧
    (∀ i, partner request (.inr i) = .inr i → i = 2 ∨ i = 3) := by
  classical
  have hlocal := buffer_completion (flags request)
  have hocc := occupied_iff request hcentral
  have hmate := hlocal.1
  constructor
  · intro x
    cases x with
    | inl a =>
      have h : ∃ a', request a' = request a := ⟨a, rfl⟩
      have hc : Classical.choose h = a := hinj (Classical.choose_spec h)
      simp only [partner, dif_pos h, hc]
    | inr i =>
      by_cases h : ∃ a, request a = i
      · simp only [partner, dif_pos h]
        rw [Classical.choose_spec h]
      · have ho : occupied (flags request) i = false := by
          cases he : occupied (flags request) i
          · rfl
          · exact (h ((hocc i).mp he)).elim
        have hfree : ¬ ∃ a, request a = mate (flags request) i := by
          intro ⟨a, ha⟩
          have hx := hlocal.2.1 _ ((hocc _).mpr ⟨a, ha⟩)
          have hy := hmate i
          rw [hx] at hy
          exact h ⟨a, ha.trans hy⟩
        simp only [partner, dif_neg h, dif_neg hfree]
        exact congrArg Sum.inr (hmate i)
  · constructor
    · intro a
      rfl
    · intro i hi
      by_cases h : ∃ a, request a = i
      · simp only [partner, dif_pos h] at hi
        cases hi
      · have ho : occupied (flags request) i = false := by
          cases he : occupied (flags request) i
          · rfl
          · exact (h ((hocc i).mp he)).elim
        have he : mate (flags request) i = i := by
          simpa only [partner, dif_neg h, Sum.inr.injEq] using hi
        exact hlocal.2.2.2.2.1 i ho he

#print axioms complete_requests
#print axioms buffer_completion
end D5.S3.Combinatorics.Graph.Roommates.BufferLayout
