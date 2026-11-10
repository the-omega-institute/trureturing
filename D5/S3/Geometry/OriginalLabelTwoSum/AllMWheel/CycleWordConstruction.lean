/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction
   mirror-E: none(waiver:actual-three-block-cycle-word-source-only)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Occurrence and attachment Word constructors. -/

import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance allMWheelCycleWordPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open FiniteProtectedDualWord OriginalLabelTwoSum

/- Elementary private occurrence/erasure arguments are repeated from the
   selected PathWord owner because its helpers are private. No path definition,
   recursion, Symbol, Word, or Contract is redefined here. -/
namespace CycleProof
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem split_append {α : Type*} (xs ys p : List α) (z : α) (s : List α)
    (h : xs ++ ys = p ++ z :: s) :
    (∃ a b, xs = a ++ z :: b ∧ p = a ∧ s = b ++ ys) ∨
    (∃ a b, ys = a ++ z :: b ∧ p = xs ++ a ∧ s = b) := by
  induction xs generalizing p with
  | nil => exact Or.inr ⟨p, s, by simpa using h, rfl, rfl⟩
  | cons x xs ih =>
      cases p with
      | nil =>
          have hh := List.cons.inj h
          exact Or.inl ⟨[], xs, by simp [hh.1], rfl, hh.2.symm⟩
      | cons y p =>
          have hh := List.cons.inj h
          rcases ih p hh.2 with ⟨a, b, hx, hp, hs⟩ | ⟨a, b, hy, hp, hs⟩
          · exact Or.inl ⟨x :: a, b, by simp [hx, hh.1], by simp [hp, hh.1], hs⟩
          · exact Or.inr ⟨a, b, hy, by simp [hp, hh.1], hs⟩

private theorem split_map {α β : Type*} (f : α → β) (xs : List α)
    (p : List β) (z : β) (s : List β) (h : xs.map f = p ++ z :: s) :
    ∃ a x b, xs = a ++ x :: b ∧ p = a.map f ∧ z = f x ∧ s = b.map f := by
  induction p generalizing xs with
  | nil =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hh := List.cons.inj h
          exact ⟨[], x, xs, rfl, rfl, hh.1.symm, hh.2.symm⟩
  | cons y p ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hh := List.cons.inj h
          obtain ⟨a, u, b, hx, hp, hz, hs⟩ := ih xs hh.2
          exact ⟨x :: a, u, b, by simp [hx], by simp [hp, hh.1], hz, hs⟩

private theorem smaller_in_prefix {xs p s : List (Finset V)} {A B : Finset V}
    (ho : xs.Pairwise (fun a b => a.card ≤ b.card))
    (h : xs = p ++ B :: s) (hA : A ∈ xs) (hlt : A.card < B.card) : A ∈ p := by
  rw [h] at hA ho
  rcases List.mem_append.mp hA with hp | ht
  · exact hp
  · rcases List.mem_cons.mp ht with he | ht
    · subst A; omega
    · have hBA := (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).1 A ht
      omega

private theorem pairwise_map_on {α β : Type*} (f : α → β)
    {R : α → α → Prop} {Q : β → β → Prop} {xs : List α}
    (h : xs.Pairwise R)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, R x y → Q (f x) (f y)) :
    (xs.map f).Pairwise Q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hh, ht⟩ := List.pairwise_cons.mp h
      apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hf x (by simp) z (by simp [hz]) (hh z hz)
      · exact ih ht (fun a ha b hb hab => hf a (by simp [ha]) b (by simp [hb]) hab)

private theorem index_faces (xs : List (Symbol V)) (s : Finset V) :
    (∃ i : Fin xs.length, s ∈ (xs.get i).faces) ↔ ∃ q ∈ xs, s ∈ q.faces := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨xs.get i, List.mem_iff_get.mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨q, hq, hs⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    exact ⟨i, by simpa only [hi] using hs⟩

private theorem word_face {W : Finset V} {K : Family V} (d : Word W K)
    {q : Symbol V} (hq : q ∈ d.word) {s : Finset V} (hs : s ∈ q.faces) : s ∈ K := by
  cases q with
  | critical S =>
      have he : s = S := by simpa [FiniteProtectedDualWord.Symbol.faces] using hs
      subst s; exact d.critical_data S hq
  | pair L a =>
      rcases (show s = L ∨ s = insert a L by
        simpa [FiniteProtectedDualWord.Symbol.faces] using hs) with he | he
      · exact he.symm ▸ (d.pair_data L a hq).1
      · exact he.symm ▸ (d.pair_data L a hq).2.1

private theorem insert_injective_on {b : V} {A B : Finset V}
    (hA : b ∉ A) (hB : b ∉ B) (h : insert b A = insert b B) : A = B := by
  have hh := congrArg (fun t : Finset V => t.erase b) h
  simpa only [Finset.erase_insert hA, Finset.erase_insert hB] using hh

private theorem pair_face_erase {a : V} {A S : Finset V} (ha : a ∉ A)
    (hS : S ∈ (Symbol.pair A a).faces) : S.erase a = A := by
  rcases (show S = A ∨ S = insert a A by
    simpa [FiniteProtectedDualWord.Symbol.faces] using hS) with rfl | rfl
  · exact Finset.erase_eq_of_notMem ha
  · exact Finset.erase_insert ha

private theorem first_disjoint {a : V} {A B : Finset V}
    (ha : a ∉ A) (hb : a ∉ B) (hAB : A ≠ B) :
    Disjoint (Symbol.pair A a).faces (Symbol.pair B a).faces := by
  apply Finset.disjoint_left.mpr
  intro S hSA hSB
  exact hAB ((pair_face_erase ha hSA).symm.trans (pair_face_erase hb hSB))

private theorem first_partition (a : V) (xs : List (Finset V))
    (hn : xs.Nodup) (ha : ∀ A ∈ xs, a ∉ A) :
    (xs.map (fun A => Symbol.pair A a)).Pairwise
      (fun q r => Disjoint q.faces r.faces) := by
  induction xs with
  | nil => simp
  | cons A tail ih =>
      obtain ⟨hAn, htail⟩ := List.nodup_cons.mp hn
      apply List.pairwise_cons.mpr
      constructor
      · intro q hq
        obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hq
        exact first_disjoint (ha A (by simp)) (ha B (by simp [hB]))
          (fun he => hAn (he.symm ▸ hB))
      · exact ih htail (fun B hB => ha B (by simp [hB]))

private theorem erase_dependency {a : V} {A T : Finset V}
    (hT : T ⊂ insert a A) (hne : T ≠ A) : T.erase a ⊂ A := by
  have hsub : T.erase a ⊆ A := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact (Finset.mem_insert.mp (hT.subset hx'.2)).resolve_left hx'.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  by_cases hat : a ∈ T
  · have ht : T = insert a A := by rw [← he, Finset.insert_erase hat]
    exact hT.ne ht
  · exact hne ((Finset.erase_eq_of_notMem hat).symm.trans he)

private theorem erase_lift_dependency {b : V} {U T : Finset V}
    (hT : T ⊂ insert b U) (hbT : b ∈ T) : T.erase b ⊂ U := by
  have hs : T.erase b ⊆ U := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact (Finset.mem_insert.mp (hT.subset hx'.2)).resolve_left hx'.1
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
  intro he
  exact hT.ne (by rw [← he, Finset.insert_erase hbT])


/-- Union with a cone whose base already belongs to the earlier family. -/
private def attachFamily (K G : Family V) (b : V) (hGK : G ≤ K) : Family V where
  carrier := {s | s ∈ K ∨ ∃ t ∈ G, insert b t = s}
  lower' := by
    intro s t hts hs
    rcases hs with hs | ⟨u, hu, he⟩
    · exact Or.inl (K.lower hts hs)
    · rw [← he] at hts
      have herase : t.erase b ⊆ u := by
        intro x hx
        exact (Finset.mem_insert.mp (hts (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.mem_erase.mp hx).1
      by_cases hb : b ∈ t
      · exact Or.inr ⟨t.erase b, G.lower herase hu, Finset.insert_erase hb⟩
      · have htu : t ⊆ u := by
          intro x hx
          exact (Finset.mem_insert.mp (hts hx)).resolve_left (fun he => hb (he ▸ hx))
        exact Or.inl (hGK (G.lower htu hu))

private theorem mem_attach (K G : Family V) (b : V) (hGK : G ≤ K) (s : Finset V) :
    s ∈ attachFamily K G b hGK ↔ s ∈ K ∨ ∃ t ∈ G, insert b t = s := Iff.rfl

private theorem facets_mem (F : Finset (Finset V))
    (hl : ∀ s ∈ F, ∀ t, t ⊆ s → t ∈ F) (s : Finset V) :
    s ∈ facets F ↔ s ∈ F := by
  constructor
  · rintro ⟨u, hu, hs⟩
    exact hl u hu s hs
  · exact fun hs => ⟨s, hs, Finset.Subset.refl s⟩

/- A cone paired in increasing base-cardinality. This is consumed by the
   first cycle block, and requires only ordinary finite-family heredity. -/
private def pairedCone (W : Finset V) (F : Finset (Finset V)) (a : V)
    (hl : ∀ s ∈ F, ∀ t, t ⊆ s → t ∈ F)
    (hFW : ∀ s ∈ F, s ⊆ W) (haW : a ∈ W) (ha : ∀ s ∈ F, a ∉ s) :
    Word W (attachFamily (facets F) (facets F) a le_rfl) := by
  let xs := orderedFaces F
  have hxs : ∀ s, s ∈ xs ↔ s ∈ F := mem_orderedFaces F
  have hm := facets_mem F hl
  refine {
    word := xs.map (fun s => Symbol.pair s a)
    supported := ?_
    pair_data := ?_
    critical_data := ?_
    partition := first_partition a xs (orderedFaces_spec F).1
      (fun s hs => ha s ((hxs s).mp hs))
    covers := ?_
    pair_dependency := ?_
    critical_dependency := ?_ }
  · rintro s (hs | ⟨u, hu, rfl⟩)
    · exact hFW s ((hm s).mp hs)
    · exact Finset.insert_subset_iff.mpr ⟨haW, hFW u ((hm u).mp hu)⟩
  · intro L v hp
    obtain ⟨A, hA, he⟩ := List.mem_map.mp hp
    injection he with hL hv
    subst L; subst v
    have hAF := (hxs A).mp hA
    exact ⟨Or.inl ((hm A).mpr hAF),
      Or.inr ⟨A, (hm A).mpr hAF, rfl⟩, ha A hAF⟩
  · intro S hp
    obtain ⟨A, _, he⟩ := List.mem_map.mp hp
    cases he
  · intro s
    rw [index_faces, mem_attach]
    constructor
    · rintro (hs | ⟨A, hA, rfl⟩)
      · exact ⟨Symbol.pair s a, List.mem_map.mpr ⟨s, (hxs s).mpr ((hm s).mp hs), rfl⟩,
          by simp [FiniteProtectedDualWord.Symbol.faces]⟩
      · exact ⟨Symbol.pair A a, List.mem_map.mpr ⟨A, (hxs A).mpr ((hm A).mp hA), rfl⟩,
          by simp [FiniteProtectedDualWord.Symbol.faces]⟩
    · rintro ⟨q, hq, hs⟩
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hq
      have hAK := (hm A).mpr ((hxs A).mp hA)
      rcases (show s = A ∨ s = insert a A by
        simpa [FiniteProtectedDualWord.Symbol.faces] using hs) with rfl | rfl
      · exact Or.inl hAK
      · exact Or.inr ⟨A, hAK, rfl⟩
  · intro p s L v hword T hT hne
    obtain ⟨p₀, A, s₀, hx, hp, he, _⟩ := split_map (fun A => Symbol.pair A a)
      xs p (Symbol.pair L v) s hword
    injection he with hL hv
    subst L; subst v
    have hAF : A ∈ F := (hxs A).mp (by rw [hx]; simp)
    have hRA := erase_dependency hT hne
    have hRxs := (hxs (T.erase a)).mpr (hl A hAF _ hRA.subset)
    have hRp := smaller_in_prefix (orderedFaces_spec F).2.2 hx hRxs
      (Finset.card_lt_card hRA)
    refine ⟨Symbol.pair (T.erase a) a, ?_, ?_⟩
    · rw [hp]
      exact List.mem_map.mpr ⟨T.erase a, hRp, rfl⟩
    · by_cases hat : a ∈ T
      · simp [FiniteProtectedDualWord.Symbol.faces, Finset.insert_erase hat]
      · simp [FiniteProtectedDualWord.Symbol.faces, Finset.erase_eq_of_notMem hat]
  · intro p s S h
    obtain ⟨_, A, _, _, _, he, _⟩ := split_map (fun A => Symbol.pair A a)
      xs p (Symbol.critical S) s h
    cases he

/- Appending a mapped, already proved Word along its actual base inclusion.
   The inclusion G≤K supplies the missing-apex dependencies in earlier blocks.
   This is a private composition lemma, not a second Word authority. -/
private def attachWord {W X : Finset V} {K G : Family V}
    (d : Word W K) (e : Word X G) (b : V) (hbW : b ∈ W)
    (hGK : G ≤ K) (hbK : ∀ s ∈ K, b ∉ s) :
    Word W (attachFamily K G b hGK) := by
  have hlift : ∀ s ∈ G, insert b s ∈ attachFamily K G b hGK :=
    fun s hs => Or.inr ⟨s, hs, rfl⟩
  have hfaceG : ∀ q ∈ e.word, ∀ s ∈ q.faces, s ∈ G :=
    fun q hq s hs => word_face e hq hs
  have havoid : ∀ q ∈ e.word, ∀ s ∈ q.faces, b ∉ s :=
    fun q hq s hs => hbK s (hGK (hfaceG q hq s hs))
  have hcover : ∀ T ∈ K, ∃ q ∈ d.word, T ∈ q.faces := by
    intro T hT
    exact (index_faces d.word T).mp ((d.covers T).mp hT)
  refine {
    word := d.word ++ e.word.map (adjoinSymbol b)
    supported := ?_
    pair_data := ?_
    critical_data := ?_
    partition := ?_
    covers := ?_
    pair_dependency := ?_
    critical_dependency := ?_ }
  · rintro s (hs | ⟨u, hu, rfl⟩)
    · exact d.supported s hs
    · exact Finset.insert_subset_iff.mpr ⟨hbW, d.supported u (hGK hu)⟩
  · intro L v hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hL, hU, hv⟩ := d.pair_data L v hp
      exact ⟨Or.inl hL, Or.inl hU, hv⟩
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
      cases q with
      | critical S => simp [adjoinSymbol] at he
      | pair A u =>
          change Symbol.pair (insert b A) u = Symbol.pair L v at he
          injection he with hL hv
          subst L; subst v
          obtain ⟨hA, hU, hu⟩ := e.pair_data A u hq
          have hbU := hbK _ (hGK hU)
          have hub : u ≠ b := fun h => hbU (by simp [← h])
          exact ⟨hlift A hA,
            by simpa only [Finset.insert_comm] using hlift (insert u A) hU,
            by simp [hub, hu]⟩
  · intro S hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Or.inl (d.critical_data S hp)
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
      cases q with
      | pair A u => simp [adjoinSymbol] at he
      | critical A =>
          change Symbol.critical (insert b A) = Symbol.critical S at he
          injection he with hS
          subst S
          exact hlift A (e.critical_data A hq)
  · apply List.pairwise_append.mpr
    refine ⟨d.partition, ?_, ?_⟩
    · exact pairwise_map_on (adjoinSymbol b) e.partition (by
        intro q hq r hr hqr
        apply Finset.disjoint_left.mpr
        intro T hTq hTr
        obtain ⟨A, hA, hAT⟩ := (mem_adjoinSymbol_faces b q T).mp hTq
        obtain ⟨B, hB, hBT⟩ := (mem_adjoinSymbol_faces b r T).mp hTr
        have he := insert_injective_on (havoid q hq A hA) (havoid r hr B hB)
          (hAT.trans hBT.symm)
        exact Finset.disjoint_left.mp hqr hA (he.symm ▸ hB))
    · intro q hq r hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      apply Finset.disjoint_left.mpr
      intro T hTq hTr
      obtain ⟨A, _, hAT⟩ := (mem_adjoinSymbol_faces b u T).mp hTr
      exact hbK T (word_face d hq hTq) (hAT ▸ Finset.mem_insert_self b A)
  · intro s
    rw [index_faces, mem_attach]
    constructor
    · rintro (hs | ⟨T, hT, rfl⟩)
      · obtain ⟨q, hq, hs⟩ := hcover s hs
        exact ⟨q, List.mem_append.mpr (Or.inl hq), hs⟩
      · obtain ⟨q, hq, hTq⟩ := (index_faces e.word T).mp ((e.covers T).mp hT)
        exact ⟨adjoinSymbol b q,
          List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q, hq, rfl⟩)),
          (mem_adjoinSymbol_faces b q _).mpr ⟨T, hTq, rfl⟩⟩
    · rintro ⟨q, hq, hs⟩
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (word_face d hq hs)
      · change q ∈ e.word.map (adjoinSymbol b) at hq
        obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
        obtain ⟨A, hA, rfl⟩ := (mem_adjoinSymbol_faces b q₀ s).mp hs
        exact Or.inr ⟨A, hfaceG q₀ hq₀ A hA, rfl⟩
  · intro p s L v hword T hT hne
    rcases split_append d.word (e.word.map (adjoinSymbol b)) p (Symbol.pair L v) s hword with
      ⟨p₁, s₁, h₁, hp, _⟩ | ⟨p₂, s₂, h₂, hp, _⟩
    · obtain ⟨q, hq, hTq⟩ := d.pair_dependency p₁ s₁ L v h₁ T hT hne
      exact ⟨q, hp.symm ▸ hq, hTq⟩
    · obtain ⟨p₀, q, s₀, hx, hpp, he, _⟩ := split_map (adjoinSymbol b)
        e.word p₂ (Symbol.pair L v) s₂ h₂
      have hq : q ∈ e.word := by rw [hx]; simp
      cases q with
      | critical S => simp [adjoinSymbol] at he
      | pair A u =>
          change Symbol.pair L v = Symbol.pair (insert b A) u at he
          injection he with hL hv
          subst L; subst v
          have hU := (e.pair_data A u hq).2.1
          have hT' : T ⊂ insert b (insert u A) := by
            simpa only [Finset.insert_comm] using hT
          by_cases hbT : b ∈ T
          · have hRT := erase_lift_dependency hT' hbT
            have hRA : T.erase b ≠ A := by
              intro heA
              apply hne
              rw [← heA, Finset.insert_erase hbT]
            obtain ⟨r, hr, hRr⟩ := e.pair_dependency p₀ s₀ A u hx _ hRT hRA
            refine ⟨adjoinSymbol b r, ?_, ?_⟩
            · rw [hp, hpp]
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))
            · exact (mem_adjoinSymbol_faces b r T).mpr
                ⟨T.erase b, hRr, Finset.insert_erase hbT⟩
          · have hTU : T ⊆ insert u A := by
              intro x hxT
              exact (Finset.mem_insert.mp (hT'.subset hxT)).resolve_left
                (fun he => hbT (he ▸ hxT))
            obtain ⟨r, hr, hTr⟩ := hcover T (hGK (G.lower hTU hU))
            exact ⟨r, by rw [hp]; exact List.mem_append.mpr (Or.inl hr), hTr⟩
  · intro p s S hword T hT
    rcases split_append d.word (e.word.map (adjoinSymbol b)) p (Symbol.critical S) s hword with
      ⟨p₁, s₁, h₁, hp, _⟩ | ⟨p₂, s₂, h₂, hp, _⟩
    · obtain ⟨q, hq, hTq⟩ := d.critical_dependency p₁ s₁ S h₁ T hT
      exact ⟨q, hp.symm ▸ hq, hTq⟩
    · obtain ⟨p₀, q, s₀, hx, hpp, he, _⟩ := split_map (adjoinSymbol b)
        e.word p₂ (Symbol.critical S) s₂ h₂
      have hq : q ∈ e.word := by rw [hx]; simp
      cases q with
      | pair A u => simp [adjoinSymbol] at he
      | critical A =>
          change Symbol.critical S = Symbol.critical (insert b A) at he
          injection he with hS
          subst S
          have hA := e.critical_data A hq
          by_cases hbT : b ∈ T
          · obtain ⟨r, hr, hRr⟩ := e.critical_dependency p₀ s₀ A hx _
              (erase_lift_dependency hT hbT)
            refine ⟨adjoinSymbol b r, ?_, ?_⟩
            · rw [hp, hpp]
              exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r, hr, rfl⟩))
            · exact (mem_adjoinSymbol_faces b r T).mpr
                ⟨T.erase b, hRr, Finset.insert_erase hbT⟩
          · have hTA : T ⊆ A := by
              intro x hxT
              exact (Finset.mem_insert.mp (hT.subset hxT)).resolve_left
                (fun he => hbT (he ▸ hxT))
            obtain ⟨r, hr, hTr⟩ := hcover T (hGK (G.lower hTA hA))
            exact ⟨r, by rw [hp]; exact List.mem_append.mpr (Or.inl hr), hTr⟩

end CycleProof

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
