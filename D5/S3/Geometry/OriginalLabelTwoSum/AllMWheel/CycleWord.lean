/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWord
   generality: G
   digest: The literal three-block cycle list is a P02 Word on every original rim.
   SOURCE_ONLY_UNCOMPILED. No kernel, native or project acceptance receipt.
   The selected AllMWheel/PathWord/P02 authorities are imported unchanged. -/
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


open CycleProof

private theorem interval_independent (m lo n : Nat) (h : lo + n ≤ m + 1)
    (s : Finset (Label m)) :
    s ∈ pathIndependentOn (labelInterval m lo n h) ↔
      (∀ x ∈ s, lo ≤ x.val ∧ x.val < lo + n) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1) := by
  rw [mem_pathIndependentOn]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨fun x hx => (mem_labelInterval m lo n h x).mp
      (List.mem_toFinset.mp (hs hx)), ?_⟩
    intro x hx y hy hxy
    have hxI := (mem_labelInterval m lo n h x).mp (List.mem_toFinset.mp (hs hx))
    have hyI := (mem_labelInterval m lo n h y).mp (List.mem_toFinset.mp (hs hy))
    exact he {x,y} ((labelInterval_edges m lo n h _).mpr
      ⟨x,y,hxI.1,hxy,hyI.2,rfl⟩) (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
  · rintro ⟨hs, he⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact List.mem_toFinset.mpr ((mem_labelInterval m lo n h x).mpr (hs x hx))
    · intro e heI hes
      obtain ⟨x,y,_,hxy,_,rfl⟩ := (labelInterval_edges m lo n h e).mp heI
      exact he x (hes (by simp)) y (hes (by simp)) hxy

/-- Literal cycle independence, retaining the empty face and the wrap edge. -/
theorem mem_cycleIndependentOn (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ cycleIndependentOn m hm ↔ s ⊆ ground m ∧
      ∀ e ∈ cycleEdges m hm, ¬ e ⊆ s := by
  simp [cycleIndependentOn, pathIndependent]

theorem cycleIndependentOn_lower (m : Nat) (hm : 3 ≤ m)
    {s t : Finset (Label m)} (hs : s ∈ cycleIndependentOn m hm) (ht : t ⊆ s) :
    t ∈ cycleIndependentOn m hm := by
  obtain ⟨hW,hE⟩ := (mem_cycleIndependentOn m hm s).mp hs
  exact (mem_cycleIndependentOn m hm t).mpr
    ⟨ht.trans hW, fun e he h => hE e he (h.trans ht)⟩

@[simp] theorem mem_cycleFamily (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ facets (cycleIndependentOn m hm) ↔ s ∈ cycleIndependentOn m hm :=
  facets_mem _ (fun _ hs _ ht => cycleIndependentOn_lower m hm hs ht) s

private theorem cycle_numeric (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ cycleIndependentOn m hm ↔
      (∀ x ∈ s, 1 ≤ x.val) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1) ∧
      (lastLabel m ∉ s ∨ firstLabel m hm ∉ s) := by
  rw [mem_cycleIndependentOn]
  have hground : s ⊆ ground m ↔ ∀ x ∈ s, 1 ≤ x.val := by
    constructor
    · intro h x hx
      have hn : x ≠ 0 := (Finset.mem_erase.mp (h hx)).1
      have hz : x ≠ 0 ↔ x.val ≠ 0 := not_congr Fin.ext_iff
      rw [hz] at hn
      omega
    · intro h x hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
      intro he
      have hp := h x hx
      have he' := congrArg Fin.val he
      change x.val = 0 at he'
      omega
  rw [hground]
  constructor
  · rintro ⟨hW,hE⟩
    refine ⟨hW, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hE {x,y} ((cycleEdges_mem m hm _).mpr (Or.inl
        ⟨x,y,hW x hx,hxy,by have := y.isLt; omega,rfl⟩)) (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
    · by_cases hl : lastLabel m ∈ s
      · exact Or.inr (fun hf => hE _ ((cycleEdges_mem m hm _).mpr (Or.inr rfl))
          (Finset.insert_subset_iff.mpr ⟨hl, Finset.singleton_subset_iff.mpr hf⟩))
      · exact Or.inl hl
  · rintro ⟨hW,hE,hwrap⟩
    refine ⟨hW, ?_⟩
    intro e he hes
    rcases (cycleEdges_mem m hm e).mp he with ⟨x,y,_,hxy,_,rfl⟩ | rfl
    · exact hE x (hes (by simp)) y (hes (by simp)) hxy
    · exact hwrap.elim (fun h => h (hes (by simp))) (fun h => h (hes (by simp)))

private theorem cycle_segments (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    (s ∈ pathIndependentOn (cyclePath m hm) ↔
      (∀ x ∈ s, 3 ≤ x.val ∧ x.val < m) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1)) ∧
    (s ∈ pathIndependentOn (cyclePathTail m hm) ↔
      (∀ x ∈ s, 4 ≤ x.val ∧ x.val < m) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1)) ∧
    (s ∈ pathIndependentOn (cyclePathLast m hm) ↔
      (∀ x ∈ s, 2 ≤ x.val ∧ x.val + 1 < m) ∧
      (∀ x ∈ s, ∀ y ∈ s, y.val ≠ x.val + 1)) := by
  simp only [cyclePath, cyclePathTail, cyclePathLast, interval_independent]
  constructor
  · have hn : 3 + (m - 3) = m := by omega
    rw [hn]
  · constructor
    · by_cases h4 : 4 ≤ m
      · have hn : 4 + (m - 4) = m := by omega
        rw [hn]
      · have he : m = 3 := by omega
        subst m
        constructor
        · rintro ⟨hs,he⟩
          exact ⟨fun x hx => by have := hs x hx; omega,he⟩
        · rintro ⟨hs,he⟩
          exact ⟨fun x hx => by have := hs x hx; omega,he⟩
    · constructor
      · rintro ⟨hs,he⟩
        exact ⟨fun x hx => by have := hs x hx; omega,he⟩
      · rintro ⟨hs,he⟩
        exact ⟨fun x hx => by have := hs x hx; omega,he⟩

/-- Exact four summands representing the three blocks: two faces per first
    pair, followed by the second-label and last-label path families. -/
theorem cycleIndependentOn_decomposition (m : Nat) (hm : 3 ≤ m) :
    cycleIndependentOn m hm =
      ((pathIndependentOn (cyclePath m hm) ∪
        (pathIndependentOn (cyclePath m hm)).image (insert (firstLabel m hm))) ∪
        (pathIndependentOn (cyclePathTail m hm)).image (insert (secondLabel m hm))) ∪
        (pathIndependentOn (cyclePathLast m hm)).image (insert (lastLabel m)) := by
  let a := firstLabel m hm
  let b := secondLabel m hm
  let c := lastLabel m
  have ha : a.val = 1 := rfl
  have hb : b.val = 2 := rfl
  have hc : c.val = m := rfl
  have eqv : ∀ x y : Label m, x = y ↔ x.val = y.val := fun _ _ => Fin.ext_iff
  have hsegment := cycle_segments m hm
  have hfrom : ∀ s,
      (s ∈ pathIndependentOn (cyclePath m hm) ∨
        ∃ t ∈ pathIndependentOn (cyclePath m hm), insert a t = s) ∨
      (∃ t ∈ pathIndependentOn (cyclePathTail m hm), insert b t = s) ∨
      (∃ t ∈ pathIndependentOn (cyclePathLast m hm), insert c t = s) →
      s ∈ cycleIndependentOn m hm := by
    intro s hs
    rcases hs with (hs | ⟨t,ht,rfl⟩) | ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
    · obtain ⟨hbound,hE⟩ := (hsegment s).1.mp hs
      apply (cycle_numeric m hm s).mpr
      refine ⟨fun x hx => by have := hbound x hx; omega,hE,Or.inl ?_⟩
      intro h
      have := hbound c h
      omega
    · obtain ⟨hbound,hE⟩ := (hsegment t).1.mp ht
      apply (cycle_numeric m hm _).mpr
      refine ⟨?_,?_,Or.inl ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · have := hbound x hx; omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx <;>
          rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · have := hbound y hy; omega
        · have := hbound x hx; omega
        · exact hE x hx y hy hxy
      · intro h
        rcases Finset.mem_insert.mp h with he | ht
        · have := (eqv c a).mp he; omega
        · have := hbound c ht; omega
    · obtain ⟨hbound,hE⟩ := (hsegment t).2.1.mp ht
      apply (cycle_numeric m hm _).mpr
      refine ⟨?_,?_,Or.inl ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · have := hbound x hx; omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx <;>
          rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · have := hbound y hy; omega
        · have := hbound x hx; omega
        · exact hE x hx y hy hxy
      · intro h
        rcases Finset.mem_insert.mp h with he | ht
        · have := (eqv c b).mp he; omega
        · have := hbound c ht; omega
    · obtain ⟨hbound,hE⟩ := (hsegment t).2.2.mp ht
      apply (cycle_numeric m hm _).mpr
      refine ⟨?_,?_,Or.inr ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · have := hbound x hx; omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx <;>
          rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · have := hbound y hy; omega
        · have := hbound x hx; omega
        · exact hE x hx y hy hxy
      · intro h
        rcases Finset.mem_insert.mp h with he | ht
        · have := (eqv a c).mp he; omega
        · have := hbound a ht; omega
  ext s
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hs
    obtain ⟨hpos,hE,hwrap⟩ := (cycle_numeric m hm s).mp hs
    have hsub : ∀ z, ∀ x ∈ s.erase z, x ∈ s :=
      fun _ _ hx => Finset.mem_of_mem_erase hx
    have hEerase : ∀ z, ∀ x ∈ s.erase z, ∀ y ∈ s.erase z, y.val ≠ x.val + 1 :=
      fun z x hx y hy => hE x (hsub z x hx) y (hsub z y hy)
    by_cases hcs : c ∈ s
    · right
      refine ⟨s.erase c, (hsegment _).2.2.mpr ⟨?_,hEerase c⟩,Finset.insert_erase hcs⟩
      intro x hx
      have hxs := hsub c x hx
      have hp := hpos x hxs
      have hxne := (Finset.mem_erase.mp hx).1
      have hxv : x.val ≠ m := fun he => hxne ((eqv x c).mpr (he.trans hc.symm))
      have hf : a ∉ s := hwrap.resolve_left (not_not.mpr hcs)
      have hx1 : x.val ≠ 1 := fun he => hf (((eqv x a).mpr (he.trans ha.symm)) ▸ hxs)
      have hn := hE x hxs c hcs
      have hxm := x.isLt
      constructor <;> omega
    · left
      by_cases hbs : b ∈ s
      · right
        refine ⟨s.erase b, (hsegment _).2.1.mpr ⟨?_,hEerase b⟩,Finset.insert_erase hbs⟩
        intro x hx
        have hxs := hsub b x hx
        have hp := hpos x hxs
        have hxne := (Finset.mem_erase.mp hx).1
        have hx2 : x.val ≠ 2 := fun he => hxne ((eqv x b).mpr (he.trans hb.symm))
        have hx3 := hE b hbs x hxs
        have hx1 := hE x hxs b hbs
        have hxm := x.isLt
        have hxc : x.val ≠ m := fun he => hcs (((eqv x c).mpr (he.trans hc.symm)) ▸ hxs)
        constructor <;> omega
      · left
        by_cases has : a ∈ s
        · right
          refine ⟨s.erase a, (hsegment _).1.mpr ⟨?_,hEerase a⟩,Finset.insert_erase has⟩
          intro x hx
          have hxs := hsub a x hx
          have hp := hpos x hxs
          have hxne := (Finset.mem_erase.mp hx).1
          have hx1 : x.val ≠ 1 := fun he => hxne ((eqv x a).mpr (he.trans ha.symm))
          have hx2 : x.val ≠ 2 := fun he => hbs (((eqv x b).mpr (he.trans hb.symm)) ▸ hxs)
          have hxc : x.val ≠ m := fun he => hcs (((eqv x c).mpr (he.trans hc.symm)) ▸ hxs)
          have hxm := x.isLt
          constructor <;> omega
        · left
          apply (hsegment _).1.mpr
          refine ⟨?_,hE⟩
          intro x hx
          have hp := hpos x hx
          have hx1 : x.val ≠ 1 := fun he => has (((eqv x a).mpr (he.trans ha.symm)) ▸ hx)
          have hx2 : x.val ≠ 2 := fun he => hbs (((eqv x b).mpr (he.trans hb.symm)) ▸ hx)
          have hxc : x.val ≠ m := fun he => hcs (((eqv x c).mpr (he.trans hc.symm)) ▸ hx)
          have hxm := x.isLt
          constructor <;> omega
  · intro hs
    apply hfrom s
    rcases hs with ((h | h) | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)


/-- All fields of the sole P02 Word, for the literal selected three blocks.
    No Word/partition/dependency or desired endpoint is an input. -/
def cycleWordData (m : Nat) (hm : 3 ≤ m) :
    Word (ground m) (facets (cycleIndependentOn m hm)) := by
  let F := pathIndependentOn (cyclePath m hm)
  let K := pathFamily (cyclePath m hm)
  let G := pathFamily (cyclePathTail m hm)
  let J := pathFamily (cyclePathLast m hm)
  let a := firstLabel m hm
  let b := secondLabel m hm
  let c := lastLabel m
  have ha : a.val = 1 := rfl
  have hb : b.val = 2 := rfl
  have hc : c.val = m := rfl
  have hsegments := cycle_segments m hm
  have hground : ∀ x : Label m, 1 ≤ x.val → x ∈ ground m := by
    intro x hx
    simp only [ground, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_zero] at this
    omega
  have hFbound : ∀ s ∈ F, ∀ x ∈ s, 3 ≤ x.val ∧ x.val < m :=
    fun s hs => ((hsegments s).1.mp hs).1
  have hGbound : ∀ s ∈ G, ∀ x ∈ s, 4 ≤ x.val ∧ x.val < m :=
    fun s hs => ((hsegments s).2.1.mp ((mem_pathFamily _ _).mp hs)).1
  have haF : ∀ s ∈ F, a ∉ s := by
    intro s hs h
    have := hFbound s hs a h
    omega
  let d0 := pairedCone (ground m) F a
    (fun _ hs _ ht => pathIndependentOn_lower hs ht)
    (fun s hs x hx => hground x (by have := hFbound s hs x hx; omega))
    (hground a (by omega)) haF
  let K0 := attachFamily K K a le_rfl
  have hGK : G ≤ K := by
    intro s hs
    apply (mem_pathFamily _ _).mpr
    obtain ⟨hs,hE⟩ := (hsegments s).2.1.mp ((mem_pathFamily _ _).mp hs)
    exact (hsegments s).1.mpr ⟨fun x hx => by have := hs x hx; omega,hE⟩
  have hG0 : G ≤ K0 := fun _ hs => Or.inl (hGK hs)
  have hb0 : ∀ s ∈ K0, b ∉ s := by
    rintro s (hs | ⟨t,ht,rfl⟩) hbs
    · have := hFbound s ((mem_pathFamily _ _).mp hs) b hbs
      omega
    · rcases Finset.mem_insert.mp hbs with he | hbt
      · have := congrArg Fin.val he; omega
      · have := hFbound t ((mem_pathFamily _ _).mp ht) b hbt; omega
  let d1 := attachWord d0 (cycleTailWordData m hm) b (hground b (by omega)) hG0 hb0
  let K1 := attachFamily K0 G b hG0
  /- This is the last-versus-second incidence. If 2 is retained, the actual
     path edge {2,3} excludes 3, so deleting 2 leaves labels 4,...,m-2.
     If 2 is absent, the entire last-path face is already a first-block base. -/
  have hJ1 : J ≤ K1 := by
    intro s hs
    obtain ⟨hbound,hE⟩ := (hsegments s).2.2.mp ((mem_pathFamily _ _).mp hs)
    by_cases hbs : b ∈ s
    · right
      refine ⟨s.erase b, (mem_pathFamily _ _).mpr ((hsegments _).2.1.mpr ⟨?_,?_⟩),
        Finset.insert_erase hbs⟩
      · intro x hx
        have hxs := Finset.mem_of_mem_erase hx
        have hxb := (Finset.mem_erase.mp hx).1
        have hbnd := hbound x hxs
        have hx2 : x.val ≠ 2 := by
          intro he
          apply hxb
          apply Fin.ext
          omega
        have hx3 := hE b hbs x hxs
        constructor <;> omega
      · intro x hx y hy
        exact hE x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
    · left
      left
      apply (mem_pathFamily _ _).mpr
      apply (hsegments s).1.mpr
      refine ⟨?_,hE⟩
      intro x hx
      have hbnd := hbound x hx
      have hx2 : x.val ≠ 2 := by
        intro he
        apply hbs
        have heq : x = b := Fin.ext (by omega)
        exact heq ▸ hx
      constructor <;> omega
  have hc1 : ∀ s ∈ K1, c ∉ s := by
    rintro s ((hs | ⟨t,ht,rfl⟩) | ⟨t,ht,rfl⟩) hcs
    · have := hFbound s ((mem_pathFamily _ _).mp hs) c hcs
      omega
    · rcases Finset.mem_insert.mp hcs with he | hct
      · have := congrArg Fin.val he; omega
      · have := hFbound t ((mem_pathFamily _ _).mp ht) c hct; omega
    · rcases Finset.mem_insert.mp hcs with he | hct
      · have := congrArg Fin.val he; omega
      · have := hGbound t ht c hct; omega
  let d2 := attachWord d1 (cycleLastWordData m hm) c (hground c (by omega)) hJ1 hc1
  have hfamily : attachFamily K1 J c hJ1 = facets (cycleIndependentOn m hm) := by
    apply SetLike.ext
    intro s
    rw [mem_cycleFamily, cycleIndependentOn_decomposition]
    simp only [Finset.mem_union, Finset.mem_image]
    change ((s ∈ K ∨ ∃ t ∈ K, insert a t = s) ∨
      ∃ t ∈ G, insert b t = s) ∨ (∃ t ∈ J, insert c t = s) ↔ _
    simp only [K,G,J,mem_pathFamily]
    rfl
  have hw : d2.word = cycleWord m hm := by
    dsimp only [d2, d1, d0, attachWord, pairedCone]
    simp only [cycleWord, mapSecond, mapLast, a, b, c, F, List.append_assoc]
  refine {
    word := cycleWord m hm
    supported := ?_
    pair_data := ?_
    critical_data := ?_
    partition := ?_
    covers := ?_
    pair_dependency := ?_
    critical_dependency := ?_ }
  · rw [← hfamily]
    exact d2.supported
  · rw [← hfamily,← hw]
    exact d2.pair_data
  · rw [← hfamily,← hw]
    exact d2.critical_data
  · rw [← hw]
    exact d2.partition
  · rw [← hfamily,← hw]
    exact d2.covers
  · rw [← hw]
    exact d2.pair_dependency
  · rw [← hw]
    exact d2.critical_dependency

/-- The record computes the original public list, rather than a new matching. -/
@[simp] theorem cycleWordData_word (m : Nat) (hm : 3 ≤ m) :
    (cycleWordData m hm).word = cycleWord m hm := rfl

/-- Indexed exact coverage is consumed below at the actual fixed-ground
    complement; it is not a nonempty projection or a membership-only ordering. -/
theorem cycleWord_covers (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ cycleIndependentOn m hm ↔
      ∃ i : Fin (cycleWord m hm).length, s ∈ ((cycleWord m hm).get i).faces := by
  simpa only [cycleWordData_word, mem_cycleFamily] using (cycleWordData m hm).covers s


namespace CycleProof
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem critical_append (xs ys : List (Symbol V)) :
    criticalFaces (xs ++ ys) = criticalFaces xs ∪ criticalFaces ys := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons q xs ih => cases q <;> simp [criticalFaces, ih, Finset.insert_union]

private theorem critical_first (a : V) (xs : List (Finset V)) :
    criticalFaces (xs.map (fun T => Symbol.pair T a)) = ∅ := by
  induction xs with
  | nil => rfl
  | cons T xs ih => simpa only [List.map_cons, criticalFaces] using ih

private theorem critical_adjoin (a : V) (xs : List (Symbol V)) :
    criticalFaces (xs.map (adjoinSymbol a)) = (criticalFaces xs).image (insert a) := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons q xs ih => cases q <;> simp [criticalFaces, adjoinSymbol, ih]
end CycleProof

/-- Raw symbol criticals, before taking any fixed-ground complement. Both
    empty-path criticals are included, in particular at m=3 and m=4. -/
theorem cycleWord_critical_blocks (m : Nat) (hm : 3 ≤ m) :
    criticalFaces (cycleWord m hm) =
      (pathCritical (cyclePathTail m hm)).image (insert (secondLabel m hm)) ∪
      (pathCritical (cyclePathLast m hm)).image (insert (lastLabel m)) := by
  rw [cycleWord_eq]
  simp only [critical_append, critical_first, critical_adjoin,
    Finset.empty_union, pathWord_critical]

/-- Universal numerical identification of the selected second vertex in each
    consecutive triple, with the final two-vertex block included. -/
theorem pathChosen_labelInterval (m lo n : Nat) (h : lo + n ≤ m + 1) (x : Label m) :
    x ∈ FiniteIndependentPathGreedy.pathChosen (labelInterval m lo n h) ↔
      lo + 1 ≤ x.val ∧ x.val < lo + n ∧ x.val % 3 = (lo + 1) % 3 := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
      cases n with
      | zero =>
          simp only [labelInterval, FiniteIndependentPathGreedy.pathChosen,
            Finset.notMem_empty, false_iff]
          rintro ⟨hl, hu, _⟩
          omega
      | succ n =>
          cases n with
          | zero =>
              simp only [labelInterval, FiniteIndependentPathGreedy.pathChosen,
                Finset.notMem_empty, false_iff]
              rintro ⟨hl, hu, _⟩
              omega
          | succ n =>
              cases n with
              | zero =>
                  simp only [labelInterval, FiniteIndependentPathGreedy.pathChosen,
                    Finset.mem_singleton, Fin.ext_iff]
                  omega
              | succ n =>
                  change x ∈ insert (⟨lo + 1, by omega⟩ : Label m)
                    (FiniteIndependentPathGreedy.pathChosen
                      (labelInterval m (lo + 3) n (by omega))) ↔ _
                  rw [Finset.mem_insert, ih n (by omega) (lo + 3) (by omega)]
                  simp only [Fin.ext_iff]
                  omega

private theorem chosen_second (m : Nat) (hm : 3 ≤ m) (hr : m % 3 ≠ 2) :
    insert (secondLabel m hm)
      (FiniteIndependentPathGreedy.pathChosen (cyclePathTail m hm)) =
      labelsCongruent m 2 2 := by
  ext x
  simp only [Finset.mem_insert, cyclePathTail, pathChosen_labelInterval,
    labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
    secondLabel]
  have hx := x.isLt
  dsimp
  omega

private theorem chosen_last_zero (m : Nat) (hm : 3 ≤ m) (hr : m % 3 = 0) :
    insert (lastLabel m)
      (FiniteIndependentPathGreedy.pathChosen (cyclePathLast m hm)) =
      labelsCongruent m 0 3 := by
  ext x
  simp only [Finset.mem_insert, cyclePathLast, pathChosen_labelInterval,
    labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
    lastLabel]
  have hx := x.isLt
  dsimp
  omega

private theorem chosen_last_two (m : Nat) (hm : 3 ≤ m) (hr : m % 3 = 2) :
    insert (lastLabel m)
      (FiniteIndependentPathGreedy.pathChosen (cyclePathLast m hm)) =
      insert (lastLabel m) (labelsCongruent m 0 3) := by
  ext x
  simp only [Finset.mem_insert, cyclePathLast, pathChosen_labelInterval,
    labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff,
    lastLabel]
  have hx := x.isLt
  dsimp
  omega

/-- Exact tail raw criticals. In the short empty-tail cases the singleton
    {empty} is retained; in residue two the collection itself is empty. -/
theorem tailWord_critical_formula (m : Nat) (hm : 3 ≤ m) :
    criticalFaces (tailWord m hm) =
      if m % 3 = 2 then ∅ else {tailCritical m hm} := by
  rw [tailWord_eq, pathWord_critical_formula _ (cyclePathTail_nodup m hm),
    cyclePathTail_length]
  by_cases hr : m % 3 = 2
  · have ht : (m - 4) % 3 = 1 := by omega
    simp only [if_pos hr,if_pos ht]
  · have ht : (m - 4) % 3 ≠ 1 := by omega
    have hchosen : FiniteIndependentPathGreedy.pathChosen (cyclePathTail m hm) =
        labelsCongruent m 2 5 := by
      ext x
      simp only [cyclePathTail,pathChosen_labelInterval,labelsCongruent,
        Finset.mem_filter,Finset.mem_univ,true_and]
      have hx := x.isLt
      omega
    simp only [if_neg ht,if_neg hr,tailCritical,hchosen]

/-- Full labelled RAW critical formulas of the actual three-block word.
    These are independent faces, not their dual cells. -/
theorem cycleWord_critical_formula (m : Nat) (hm : 3 ≤ m) :
    criticalFaces (cycleWord m hm) =
      if m % 3 = 0 then {labelsCongruent m 2 2, labelsCongruent m 0 3}
      else if m % 3 = 1 then {labelsCongruent m 2 2}
      else {insert (lastLabel m) (labelsCongruent m 0 3)} := by
  have ht : pathCritical (cyclePathTail m hm) =
      if (m - 4) % 3 = 1 then ∅ else
        {FiniteIndependentPathGreedy.pathChosen (cyclePathTail m hm)} := by
    simpa only [pathCritical, cyclePathTail_length] using
      pathWord_critical_formula _ (cyclePathTail_nodup m hm)
  have hl : pathCritical (cyclePathLast m hm) =
      if (m - 3) % 3 = 1 then ∅ else
        {FiniteIndependentPathGreedy.pathChosen (cyclePathLast m hm)} := by
    simpa only [pathCritical, cyclePathLast_length] using
      pathWord_critical_formula _ (cyclePathLast_nodup m hm)
  rw [cycleWord_critical_blocks, ht, hl]
  by_cases h0 : m % 3 = 0
  · have ht0 : (m - 4) % 3 ≠ 1 := by omega
    have hl0 : (m - 3) % 3 ≠ 1 := by omega
    simp only [if_pos h0, if_neg ht0, if_neg hl0, Finset.image_singleton,
      chosen_second m hm (by omega), chosen_last_zero m hm h0, Finset.singleton_union]
  · by_cases h1 : m % 3 = 1
    · have ht1 : (m - 4) % 3 ≠ 1 := by omega
      have hl1 : (m - 3) % 3 = 1 := by omega
      simp only [if_neg h0, if_pos h1, if_neg ht1, if_pos hl1,
        Finset.image_singleton, Finset.image_empty, Finset.union_empty,
        chosen_second m hm (by omega)]
    · have h2 : m % 3 = 2 := by omega
      have ht2 : (m - 4) % 3 = 1 := by omega
      have hl2 : (m - 3) % 3 ≠ 1 := by omega
      simp only [if_neg h0, if_neg h1, if_pos ht2, if_neg hl2,
        Finset.image_singleton, Finset.image_empty, Finset.empty_union,
        chosen_last_two m hm h2]

/-- The existing cycleCritical is correctly typed as fixed-ground COMPLEMENTS
    of raw symbol criticals. No untyped raw/dual equality is asserted. -/
theorem cycleCritical_eq_complements (m : Nat) (hm : 3 ≤ m) :
    cycleCritical m hm =
      (criticalFaces (cycleWord m hm)).image (fun s => ground m \ s) := by
  rw [cycleWord_critical_formula]
  unfold cycleCritical
  split_ifs <;> simp

/-- Independent source-level negative control for the former raw {1,3}
    proposal: the actual m=5 critical is {3,5}. -/
theorem cycleWord_five_raw :
    criticalFaces (cycleWord 5 (by omega)) =
      {({(⟨3, by omega⟩ : Label 5), (⟨5, by omega⟩ : Label 5)} : Finset (Label 5))} := by
  have hface : insert (lastLabel 5) (labelsCongruent 5 0 3) =
      ({(⟨3, by omega⟩ : Label 5), (⟨5, by omega⟩ : Label 5)} : Finset (Label 5)) := by
    ext x
    fin_cases x <;> simp [labelsCongruent,lastLabel]
  simpa only [cycleWord_critical_formula, if_neg (by decide : ¬ 5 % 3 = 0),
    if_neg (by decide : ¬ 5 % 3 = 1),hface]

/-- Original-label complementary-row membership, without projecting away the
    empty face or deleting the hub ghost coordinate from the ambient type. -/
theorem wheelRoot_mem_cycleDual (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ wheelRoot m (by omega) ↔
      s ⊆ ground m ∧ ground m \ s ∉ cycleIndependentOn m hm := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨hi.trans Finset.sdiff_subset, ?_⟩
    intro hc
    have hE := ((mem_cycleIndependentOn m hm _).mp hc).2
    apply hE (rimEdge m (by omega) i)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨(rimRows m (by omega)).row_supported i hx, ?_⟩
    intro hxs
    exact (Finset.mem_sdiff.mp (hi hxs)).2 hx
  · rintro ⟨hsW,hn⟩
    have hnot : ¬ ∀ e ∈ cycleEdges m hm, ¬ e ⊆ ground m \ s := by
      intro hE
      exact hn ((mem_cycleIndependentOn m hm _).mpr ⟨Finset.sdiff_subset,hE⟩)
    push_neg at hnot
    obtain ⟨e,he,hsub⟩ := hnot
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
    refine ⟨i,?_⟩
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨hsW hx,?_⟩
    intro hxi
    have hxe : x ∈ e := hi ▸ hxi
    exact (Finset.mem_sdiff.mp (hsub hxe)).2 hx

/-- Actual P02 interface consumer: indexed Word coverage computes the literal
    wheel-root face family, on its unchanged original ground. All hypotheses
    are established above; no Contract, protected set or Sequence is assumed. -/
theorem cycleWord_wheelRoot_identity (m : Nat) (hm : 3 ≤ m) (s : Finset (Label m)) :
    s ∈ wheelRoot m (by omega) ↔ s ⊆ ground m ∧
      ¬ ∃ i : Fin (cycleWord m hm).length,
        ground m \ s ∈ ((cycleWord m hm).get i).faces := by
  rw [wheelRoot_mem_cycleDual, cycleWord_covers]

/-- Same consumer through the sole concrete P02 rawDual interface. -/
theorem cycleWord_rawDual_eq_wheelRoot (m : Nat) (hm : 3 ≤ m) :
    rawDual (ground m) (facets (cycleIndependentOn m hm)) =
      wheelRoot m (by omega) := by
  apply SetLike.ext
  intro s
  change s ∈ FiniteAlexanderDualCollapse.dualTable (ground m)
    ((ground m).powerset.filter (fun t => t ∈ facets (cycleIndependentOn m hm))) ↔ _
  simp only [FiniteAlexanderDualCollapse.dualTable,Finset.mem_filter,
    Finset.mem_powerset,Finset.sdiff_subset,true_and,mem_cycleFamily]
  exact (wheelRoot_mem_cycleDual m hm s).symm

/- Full protected upward H and whole-symbol closure, including all unexecuted
   criticals, remain separate obligations. In particular the m=4 critical {2}
   survives before the final native lower {1,3}, leaving coface {1,3,4}.
   No H=empty, universal maximality, fill or Gamma endpoint is claimed here.
   Both all-residue fillings, standalone B1/Q1, parent compiler, physical/all-
   plane supplier and every kernel/native/Reg/gate/remote-delivery check remain
   outside this uncompiled source construction. -/
end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
