/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestSlotGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prescribed history fibers determine the exact directed slot statistics. -/

import D5.S3.ObserverMemory.Algorithms.FixedForestTargetInventory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph

open FixedForestTargetInventory
attribute [local instance] Classical.propDecidable

variable {P h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP) (R : Prescribed F)

private theorem marked_ne : R.H ≠ R.K ∧ R.H ≠ R.H1 ∧ R.H ≠ R.K1 ∧
    R.K ≠ R.H1 ∧ R.K ≠ R.K1 ∧ R.H1 ≠ R.K1 := by
  have hs := R.marked_distinct
  have h := (List.pairwise_cons.mp hs).1
  have k := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have v := (List.pairwise_cons.mp
    (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).2).1
  exact ⟨h R.K (by simp), h R.H1 (by simp), h R.K1 (by simp),
    k R.H1 (by simp), k R.K1 (by simp), v R.K1 (by simp)⟩

private theorem binary_shared_only {n m : Node} (hn : F.Binary n) (hm : F.Binary m)
    (hs : Shared F R n m) : n = m := by
  rcases hs with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · exact False.elim (binary_not_unary F hm R.K_unary)
  · exact False.elim (binary_not_unary F hn R.K_unary)
  · exact False.elim (binary_not_unary F hn R.H1_unary)
  · exact False.elim (binary_not_unary F hn R.K1_unary)

private theorem prescribed_rows (α : Assignment (e := e) F R) :
    placement F R α R.H = placement F R α R.K ∧
    placement F R α R.H1 = placement F R α R.K1 := by
  constructor
  · rcases R.HK_parents with ⟨hh, hk⟩ | ⟨hh, hk⟩
    all_goals
      simp [placement, hh, hk, nextTarget, R.A_binary, R.B_binary,
        binaryTarget, R.AB_distinct, R.HK_color]
  · have nk : ¬ F.Binary R.K := fun hb => binary_not_unary F hb R.K_unary
    simp [placement, R.first_children.1, R.first_children.2,
      nextTarget, R.H_binary, nk, R.child_color]

theorem shared_rows_distinct (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : placement F R α R.H ≠ placement F R α R.H1 := by
  intro he
  have hs := placement_fibers F R hc α he
  have hd := marked_ne F R
  rcases hs with hh | ⟨hh, hv⟩ | ⟨hh, hv⟩ | ⟨hh, hv⟩ | ⟨hh, hv⟩
  · exact hd.2.1 hh
  · exact hd.2.2.2.1 hv.symm
  · exact hd.1 hh
  · exact hd.2.1 hh
  · exact hd.2.2.1 hh

/-- Each nonroot complete-history node indexes one forest edge. -/
noncomputable def forestEdge (α : Assignment (e := e) F R) (n : Node) :
    Option (Row (e := e) F R × Row (e := e) F R) :=
  (F.parent n).map (fun p => (placement F R α p, placement F R α n))

/-- Equality of actual directed edges preserves forest multiplicity. The only
possible distinct preimages are the H1/K1 histories of the one w→v edge. -/
theorem repeated_edge_only (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) {n m : Node}
    (hn : F.parent n ≠ none) (hm : F.parent m ≠ none)
    (he : forestEdge F R α n = forestEdge F R α m) :
    n = m ∨ (n = R.H1 ∧ m = R.K1) ∨ (n = R.K1 ∧ m = R.H1) := by
  have distinct : placement F R α R.A ≠ placement F R α R.B := by
    intro hh
    exact R.AB_distinct (binary_shared_only F R R.A_binary R.B_binary
      (placement_fibers F R hc α hh))
  cases hp : F.parent n with
  | none => exact False.elim (hn hp)
  | some p =>
    cases hq : F.parent m with
    | none => exact False.elim (hm hq)
    | some q =>
      have pair : (placement F R α p, placement F R α n) =
          (placement F R α q, placement F R α m) := by
        simpa [forestEdge, hp, hq] using he
      have hs := placement_fibers F R hc α (congrArg Prod.snd pair)
      rcases hs with hh | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hh
      · exfalso
        rcases R.HK_parents with ⟨hh, hk⟩ | ⟨hh, hk⟩
        all_goals
          have ep := Option.some.inj (hp.symm.trans hh)
          have eq := Option.some.inj (hq.symm.trans hk)
          subst p; subst q
        · exact distinct (congrArg Prod.fst pair)
        · exact distinct (congrArg Prod.fst pair).symm
      · exfalso
        rcases R.HK_parents with ⟨hh, hk⟩ | ⟨hh, hk⟩
        all_goals
          have ep := Option.some.inj (hp.symm.trans hk)
          have eq := Option.some.inj (hq.symm.trans hh)
          subst p; subst q
        · exact distinct (congrArg Prod.fst pair).symm
        · exact distinct (congrArg Prod.fst pair)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private theorem edge_witness (α : Assignment (e := e) F R) {n : Node}
    {f : Row (e := e) F R × Row (e := e) F R} (hf : forestEdge F R α n = some f) :
    ∃ p, F.parent n = some p ∧ (placement F R α p, placement F R α n) = f := by
  cases hp : F.parent n with
  | none => simp [forestEdge, hp] at hf
  | some p => exact ⟨p, rfl, by simpa [forestEdge, hp] using hf⟩

private theorem prescribed_edge (α : Assignment (e := e) F R) :
    forestEdge F R α R.H1 = some (placement F R α R.H, placement F R α R.H1) ∧
    forestEdge F R α R.K1 = some (placement F R α R.H, placement F R α R.H1) := by
  obtain ⟨hw, hv⟩ := prescribed_rows F R α
  simp [forestEdge, R.first_children.1, R.first_children.2, hw, hv]

noncomputable def edgePreimage (α : Assignment (e := e) F R)
    (f : Row (e := e) F R × Row (e := e) F R) : Finset Node :=
  Finset.univ.filter (fun n => forestEdge F R α n = some f)

private theorem prescribed_edge_preimage (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) :
    edgePreimage F R α (placement F R α R.H, placement F R α R.H1) = {R.H1, R.K1} := by
  obtain ⟨h1, k1⟩ := prescribed_edge F R α
  have distinct := (marked_ne F R).2.2.2.2.2
  ext n
  simp only [edgePreimage, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hn
    obtain ⟨p, hp, _⟩ := edge_witness F R α hn
    have pn : F.parent n ≠ none := by rw [hp]; simp
    have pH : F.parent R.H1 ≠ none := by rw [R.first_children.1]; simp
    have he := repeated_edge_only F R hc α pn pH (hn.trans h1.symm)
    rcases he with he | ⟨he, bad⟩ | ⟨he, _⟩
    · exact Or.inl he
    · exact False.elim (distinct bad)
    · exact Or.inr he
  · rintro (rfl | rfl)
    · exact h1
    · exact k1

private theorem other_edge_preimage (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (f : Row (e := e) F R × Row (e := e) F R)
    (hf : f ≠ (placement F R α R.H, placement F R α R.H1)) :
    (edgePreimage F R α f).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have en := (Finset.mem_filter.mp hn).2
  have em := (Finset.mem_filter.mp hm).2
  obtain ⟨p, hp, _⟩ := edge_witness F R α en
  obtain ⟨q, hq, _⟩ := edge_witness F R α em
  have pn : F.parent n ≠ none := by rw [hp]; simp
  have pm : F.parent m ≠ none := by rw [hq]; simp
  rcases repeated_edge_only F R hc α pn pm (en.trans em.symm) with he | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact he
  · exact False.elim (hf (Option.some.inj (en.symm.trans (prescribed_edge F R α).1)))
  · exact False.elim (hf (Option.some.inj (en.symm.trans (prescribed_edge F R α).2)))

noncomputable def Xi (α : Assignment (e := e) F R) : Nat :=
  ∑ f : Row (e := e) F R × Row (e := e) F R, ((edgePreimage F R α f).card - 1)

/-- The one repeated directed edge has two history preimages, irrespective of
how many initialized inputs traverse it. Every other edge has at most one. -/
theorem repetition_excess (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : Xi F R α = 1 := by
  have hf (f : Row (e := e) F R × Row (e := e) F R) :
      (edgePreimage F R α f).card - 1 =
        if f = (placement F R α R.H, placement F R α R.H1) then 1 else 0 := by
    by_cases he : f = (placement F R α R.H, placement F R α R.H1)
    · rw [if_pos he, he, prescribed_edge_preimage F R hc α]
      have ne := (marked_ne F R).2.2.2.2.2
      simp [ne]
    · rw [if_neg he]
      have := other_edge_preimage F R hc α f he
      omega
  unfold Xi
  simp_rw [hf]
  simp

noncomputable def incoming (α : Assignment (e := e) F R)
    (row : Row (e := e) F R) : Finset (Row (e := e) F R) :=
  Finset.univ.biUnion (fun n => match F.parent n with
    | none => ∅
    | some p => if placement F R α n = row then {placement F R α p} else ∅)

private theorem mem_incoming (α : Assignment (e := e) F R)
    (row a : Row (e := e) F R) : a ∈ incoming F R α row ↔
    ∃ n p, F.parent n = some p ∧ placement F R α n = row ∧ placement F R α p = a := by
  constructor
  · intro ha
    obtain ⟨n, _, ha⟩ := Finset.mem_biUnion.mp ha
    cases hp : F.parent n with
    | none => simp [hp] at ha
    | some p =>
      by_cases he : placement F R α n = row
      · exact ⟨n, p, hp, he, by
          have hh : a = placement F R α p := by simpa [hp, he] using ha
          exact hh.symm⟩
      · simp [hp, he] at ha
  · rintro ⟨n, p, hp, he, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hp, he]⟩

private theorem incoming_shared (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : incoming F R α (placement F R α R.H) =
    {placement F R α R.A, placement F R α R.B} := by
  have dist := marked_ne F R
  have pairs := R.HK_parents
  ext a
  rw [mem_incoming F R α]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, p, hp, hn, ha⟩
    have hs := placement_fibers F R hc α hn
    have nk : n = R.H ∨ n = R.K := by
      rcases hs with he | ⟨he, bad⟩ | ⟨he, _⟩ | ⟨he, bad⟩ | ⟨he, bad⟩
      · exact Or.inl he
      · exact False.elim (dist.1 bad)
      · exact Or.inr he
      · exact False.elim (dist.2.2.1 bad)
      · exact False.elim (dist.2.1 bad)
    rcases nk with rfl | rfl <;> rcases pairs with ⟨hH, hK⟩ | ⟨hH, hK⟩
    all_goals
      first | have ep := Option.some.inj (hp.symm.trans hH)
            | have ep := Option.some.inj (hp.symm.trans hK)
      subst p
    · exact Or.inl ha.symm
    · exact Or.inr ha.symm
    · exact Or.inr ha.symm
    · exact Or.inl ha.symm
  · intro ha
    have hw := (prescribed_rows F R α).1
    rcases pairs with ⟨hH, hK⟩ | ⟨hH, hK⟩ <;> rcases ha with rfl | rfl
    · exact ⟨R.H, R.A, hH, rfl, rfl⟩
    · exact ⟨R.K, R.B, hK, hw.symm, rfl⟩
    · exact ⟨R.K, R.A, hK, hw.symm, rfl⟩
    · exact ⟨R.H, R.B, hH, rfl, rfl⟩

private theorem other_incoming (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (row : Row (e := e) F R)
    (hr : row ≠ placement F R α R.H) : (incoming F R α row).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨n, p, hp, hn, ha⟩ := (mem_incoming F R α row a).mp ha
  obtain ⟨m, q, hq, hm, hb⟩ := (mem_incoming F R α row b).mp hb
  have hs := placement_fibers F R hc α (hn.trans hm.symm)
  obtain ⟨hw, _⟩ := prescribed_rows F R α
  rcases hs with he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · subst m
    have ep := Option.some.inj (hp.symm.trans hq)
    subst q
    exact ha.symm.trans hb
  · exact False.elim (hr hn.symm)
  · exact False.elim (hr (hm.symm))
  · have ep := Option.some.inj (hp.symm.trans R.first_children.1)
    have eq := Option.some.inj (hq.symm.trans R.first_children.2)
    subst p; subst q
    exact ha.symm.trans (hw.trans hb)
  · have ep := Option.some.inj (hp.symm.trans R.first_children.2)
    have eq := Option.some.inj (hq.symm.trans R.first_children.1)
    subst p; subst q
    exact ha.symm.trans (hw.symm.trans hb)

noncomputable def J (α : Assignment (e := e) F R) : Nat :=
  ∑ row : Row (e := e) F R, ((incoming F R α row).card - 1)

/-- Only w has two distinct incoming source rows. Unused rows and root rows
contribute zero, so summing over all nominal digit rows gives the original J. -/
theorem incoming_excess (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) : J F R α = 1 := by
  have ne : placement F R α R.A ≠ placement F R α R.B := by
    intro he
    exact R.AB_distinct (binary_shared_only F R R.A_binary R.B_binary
      (placement_fibers F R hc α he))
  have hf (row : Row (e := e) F R) : (incoming F R α row).card - 1 =
      if row = placement F R α R.H then 1 else 0 := by
    by_cases he : row = placement F R α R.H
    · rw [if_pos he, he, incoming_shared F R hc α]
      simp [ne]
    · rw [if_neg he]
      have := other_incoming F R hc α row he
      omega
  unfold J
  simp_rw [hf]
  simp

noncomputable def binaryMultiplicity (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) : Nat :=
  (Finset.univ.filter (fun n => F.Binary n ∧ nextTarget F R α n = q)).card

noncomputable def sharing (α : Assignment (e := e) F R) : Nat :=
  ∑ q : Target (e := e) F R, (binaryMultiplicity F R α q - 1)

/-- Exactly A/B share a binary target; source histories, rather than visits,
are counted, including the allowed case H=A or H=B. -/
theorem sharing_excess (α : Assignment (e := e) F R) : sharing F R α = 1 := by
  let Q : Target (e := e) F R := .inl ⟨R.A, R.A_binary, R.AB_distinct⟩
  have hf (q : Target (e := e) F R) : binaryMultiplicity F R α q - 1 =
      if q = Q then 1 else 0 := by
    cases q with
    | inl b =>
      have same : Finset.univ.filter (fun n => F.Binary n ∧ nextTarget F R α n = .inl b) =
          if b.val = R.A then {R.A, R.B} else {b.val} := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have pred : (F.Binary n ∧ nextTarget F R α n = .inl b) ↔
            n = b.val ∨ (b.val = R.A ∧ n = R.B) := by
          constructor
          · rintro ⟨hn, ht⟩
            exact (binary_representative F R n hn b).mp (by
              simpa [nextTarget, hn] using ht)
          · rintro (he | ⟨he, hb⟩)
            · subst n
              refine ⟨b.property.1, ?_⟩
              simpa [nextTarget, b.property.1] using
                (binary_representative F R b.val b.property.1 b).mpr (Or.inl rfl)
            · subst n
              refine ⟨R.B_binary, ?_⟩
              simpa [nextTarget, R.B_binary] using
                (binary_representative F R R.B R.B_binary b).mpr (Or.inr ⟨he, rfl⟩)
        rw [pred]
        by_cases he : b.val = R.A <;> simp [he]
      unfold binaryMultiplicity
      rw [same]
      by_cases he : b.val = R.A
      · simp [he, Q, Subtype.ext_iff, R.AB_distinct]
      · simp [he, Q, Subtype.ext_iff]
    | inr t =>
      have same : Finset.univ.filter (fun n => F.Binary n ∧
          nextTarget F R α n = .inr t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hb, ht⟩ := (Finset.mem_filter.mp hn).2
        simp only [nextTarget, dif_pos hb, binaryTarget] at ht
        split_ifs at ht
      simp [binaryMultiplicity, same, Q]
  unfold sharing
  simp_rw [hf]
  simp


/-- Fiber surplus counts histories beyond their first occurrence, not visits. -/
private theorem fiber_surplus {X Y : Type*} [DecidableEq Y]
    (a : Finset X) (f : X → Y) :
    (∑ y ∈ a.image f, ((a.filter (fun x => f x = y)).card - 1)) =
      a.card - (a.image f).card := by
  classical
  rw [Finset.sum_tsub_distrib]
  · rw [← Finset.card_eq_sum_card_image f a]
    simp
  · intro y hy
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hy
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, he⟩⟩

section RawGraph
variable {S : Type*} [DecidableEq S]

noncomputable def rawNonroots : Finset Node :=
  Finset.univ.filter (fun n => F.parent n ≠ none)

noncomputable def rawEdge (row : Node → S) (n : Node) : S × S :=
  (row ((F.parent n).getD n), row n)

noncomputable def rawEdges (row : Node → S) : Finset (S × S) :=
  (rawNonroots F).image (rawEdge F row)

noncomputable def rawRows (row : Node → S) : Finset S :=
  (rawNonroots F).image row

noncomputable def rawJ (row : Node → S) : Nat :=
  ∑ r ∈ rawRows F row, (((rawEdges F row).filter (fun edge => edge.2 = r)).card - 1)

noncomputable def rawXi (row : Node → S) : Nat :=
  ∑ edge ∈ rawEdges F row,
    (((rawNonroots F).filter (fun n => rawEdge F row n = edge)).card - 1)

/-- A change of row carrier maps the exact finite row image. -/
theorem rawRows_map {T : Type*} [DecidableEq T] (row : Node → S) (f : S → T) :
    rawRows F (f ∘ row) = (rawRows F row).image f := by
  simp [rawRows, Finset.image_image]

/-- The same change acts on both endpoints of every original history edge. -/
theorem rawEdges_map {T : Type*} [DecidableEq T] (row : Node → S) (f : S → T) :
    rawEdges F (f ∘ row) =
      (rawEdges F row).image (fun edge => (f edge.1, f edge.2)) := by
  simp only [rawEdges, Finset.image_image, Function.comp_def]
  rfl

/-- Tagged row injection preserves distinct incoming edges and their counts. -/
theorem rawJ_map {T : Type*} [DecidableEq T] (row : Node → S)
    (f : S → T) (hf : Function.Injective f) : rawJ F (f ∘ row) = rawJ F row := by
  have hi : Function.Injective (fun edge : S × S => (f edge.1, f edge.2)) := by
    intro a b he
    exact Prod.ext (hf (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))
  unfold rawJ
  rw [rawRows_map, Finset.sum_image hf.injOn]
  apply Finset.sum_congr rfl
  intro r hr
  rw [rawEdges_map, Finset.filter_image]
  simp only [hf.eq_iff]
  rw [Finset.card_image_of_injective _ hi]

/-- Tagged row injection preserves each complete-history edge fiber. -/
theorem rawXi_map {T : Type*} [DecidableEq T] (row : Node → S)
    (f : S → T) (hf : Function.Injective f) : rawXi F (f ∘ row) = rawXi F row := by
  have hi : Function.Injective (fun edge : S × S => (f edge.1, f edge.2)) := by
    intro a b he
    exact Prod.ext (hf (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))
  unfold rawXi
  rw [rawEdges_map, Finset.sum_image hi.injOn]
  apply Finset.sum_congr rfl
  intro edge he
  have same : (rawNonroots F).filter (fun n => rawEdge F (f ∘ row) n =
      (f edge.1, f edge.2)) =
      (rawNonroots F).filter (fun n => rawEdge F row n = edge) := by
    ext n
    simp [rawEdge, Prod.ext_iff, hf.eq_iff]
  rw [same]

private theorem raw_edge_fiber_placement (α : Assignment (e := e) F R)
    (edge : Row (e := e) F R × Row (e := e) F R) :
    (rawNonroots F).filter (fun n => rawEdge F (placement F R α) n = edge) =
      edgePreimage F R α edge := by
  ext n
  cases hp : F.parent n <;> simp [rawNonroots, rawEdge, edgePreimage, forestEdge, hp]

/-- Canonical edge multiplicity equals the original finite-image statistic. -/
theorem rawXi_placement (α : Assignment (e := e) F R) :
    rawXi F (placement F R α) = Xi F R α := by
  unfold rawXi Xi
  trans ∑ edge ∈ rawEdges F (placement F R α), ((edgePreimage F R α edge).card - 1)
  · apply Finset.sum_congr rfl
    intro edge he
    apply congrArg (fun a : Finset Node => a.card - 1)
    convert raw_edge_fiber_placement F R α edge using 1
    ext n
    simp
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro edge _ he
    have empty : edgePreimage F R α edge = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have en := (Finset.mem_filter.mp hn).2
      obtain ⟨p, hp, pair⟩ := edge_witness F R α en
      apply he
      simp only [rawEdges, Finset.mem_image]
      exact ⟨n, by simp [rawNonroots, hp], by
        simpa [rawEdge, hp] using pair⟩
    simp [empty]

private theorem raw_incoming_placement (α : Assignment (e := e) F R)
    (row : Row (e := e) F R) :
    (rawEdges F (placement F R α)).filter (fun edge => edge.2 = row) =
      (incoming F R α row).image (fun a => (a, row)) := by
  ext edge
  constructor
  · intro he
    have inImage := (Finset.mem_filter.mp he).1
    unfold rawEdges at inImage
    simp only [Finset.mem_image] at inImage
    obtain ⟨n, hn, en⟩ := inImage
    have ne := (Finset.mem_filter.mp hn).2
    cases hp : F.parent n with
    | none => exact False.elim (ne hp)
    | some p =>
      have pair : (placement F R α p, placement F R α n) = edge := by
        simpa [rawEdge, hp] using en
      have target : placement F R α n = row :=
        (congrArg Prod.snd pair).trans (Finset.mem_filter.mp he).2
      exact Finset.mem_image.mpr ⟨placement F R α p,
        (mem_incoming F R α row _).mpr ⟨n, p, hp, target, rfl⟩,
        by rw [← target]; exact pair⟩
  · intro he
    obtain ⟨a, ha, pair⟩ := Finset.mem_image.mp he
    obtain ⟨n, p, hp, target, source⟩ := (mem_incoming F R α row a).mp ha
    apply Finset.mem_filter.mpr
    constructor
    · simp only [rawEdges, Finset.mem_image]
      exact ⟨n, by simp [rawNonroots, hp], by
        simpa [rawEdge, hp, target, source] using pair⟩
    · exact (congrArg Prod.snd pair).symm

/-- Canonical incoming-row counts equal those of the actual finite edge image. -/
theorem rawJ_placement (α : Assignment (e := e) F R) :
    rawJ F (placement F R α) = J F R α := by
  unfold rawJ J
  have counts (row : Row (e := e) F R) :
      ((rawEdges F (placement F R α)).filter (fun edge => edge.2 = row)).card =
        (incoming F R α row).card := by
    rw [raw_incoming_placement, Finset.card_image_of_injective _
      (fun a b he => congrArg Prod.fst he)]
  simp_rw [counts]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro row _ hr
  have empty : incoming F R α row = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨n, p, hp, target, _⟩ := (mem_incoming F R α row a).mp ha
    exact hr (Finset.mem_image.mpr ⟨n, by simp [rawNonroots, hp], target⟩)
  simp [empty]

private theorem raw_rows_image (row : Node → S) :
    (rawEdges F row).image Prod.snd = rawRows F row := by
  simp [rawEdges, rawRows, Finset.image_image, Function.comp_def, rawEdge]

/-- The original indegree and repeated-edge surpluses account exactly for
all nonroot history multiplicity, even when the actual row graph has cycles. -/
theorem raw_history_surplus (row : Node → S) :
    (∑ r ∈ rawRows F row,
      (((rawNonroots F).filter (fun n => row n = r)).card - 1)) =
      rawJ F row + rawXi F row := by
  have hJ := fiber_surplus (rawEdges F row) Prod.snd
  rw [raw_rows_image F row] at hJ
  have hX := fiber_surplus (rawNonroots F) (rawEdge F row)
  have hR := fiber_surplus (rawNonroots F) row
  have edges_le := Finset.card_image_le (s := rawNonroots F) (f := rawEdge F row)
  have rows_le := Finset.card_image_le (s := rawEdges F row) (f := Prod.snd)
  rw [raw_rows_image F row] at rows_le
  change (rawEdges F row).card ≤ (rawNonroots F).card at edges_le
  change rawJ F row = _ at hJ
  change rawXi F row = (rawNonroots F).card - (rawEdges F row).card at hX
  change _ = (rawNonroots F).card - (rawRows F row).card at hR
  calc
    _ = (rawNonroots F).card - (rawRows F row).card := hR
    _ = rawJ F row + rawXi F row := by rw [hJ, hX]; omega

/-- Two prescribed, distinct double rows exhaust J=Xi=1. Any further
collision of nonroot histories is impossible in the original slot graph. -/
theorem raw_fibers_only (row : Node → S)
    (hw : row R.H = row R.K) (hv : row R.H1 = row R.K1)
    (hd : row R.H ≠ row R.H1) (hJ : rawJ F row = 1) (hX : rawXi F row = 1)
    {n m : Node} (hn : F.parent n ≠ none) (hm : F.parent m ≠ none)
    (he : row n = row m) : Shared F R n m := by
  let a := rawNonroots F
  let rows := rawRows F row
  let count := fun r => (a.filter (fun n => row n = r)).card
  have distinct := marked_ne F R
  have marked (p : Node) (hp : p = R.H ∨ p = R.K ∨ p = R.H1 ∨ p = R.K1) : p ∈ a := by
    rcases hp with rfl | rfl | rfl | rfl
    · rcases R.HK_parents with ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp [a, rawNonroots, hp]
    · rcases R.HK_parents with ⟨_, hp⟩ | ⟨_, hp⟩ <;> simp [a, rawNonroots, hp]
    · simp [a, rawNonroots, R.first_children.1]
    · simp [a, rawNonroots, R.first_children.2]
  have wmem : row R.H ∈ rows := Finset.mem_image.mpr ⟨R.H, marked _ (Or.inl rfl), rfl⟩
  have vmem : row R.H1 ∈ rows := Finset.mem_image.mpr
    ⟨R.H1, marked _ (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  have wtwo : 2 ≤ count (row R.H) := by
    have sub : {R.H, R.K} ⊆ a.filter (fun n => row n = row R.H) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_filter.mpr ⟨marked _ (Or.inl rfl), rfl⟩
      · have ep := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_filter.mpr ⟨marked _ (Or.inr (Or.inl rfl)), hw.symm⟩
    simpa [count, distinct.1] using Finset.card_le_card sub
  have vtwo : 2 ≤ count (row R.H1) := by
    have sub : {R.H1, R.K1} ⊆ a.filter (fun n => row n = row R.H1) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_filter.mpr ⟨marked _ (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
      · have ep := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_filter.mpr ⟨marked _ (Or.inr (Or.inr (Or.inr rfl))), hv.symm⟩
    simpa [count, distinct.2.2.2.2.2] using Finset.card_le_card sub
  have total : ∑ r ∈ rows, (count r - 1) = 2 := by
    simpa [rows, count, a, hJ, hX] using raw_history_surplus F row
  have pair_le : count (row R.H) - 1 + (count (row R.H1) - 1) ≤ 2 := by
    have sub : {row R.H, row R.H1} ⊆ rows := by simp [Finset.insert_subset_iff, wmem, vmem]
    have hle := Finset.sum_le_sum_of_subset sub (f := fun r => count r - 1)
    simpa [hd, total] using hle
  have wc : count (row R.H) = 2 := by omega
  have vc : count (row R.H1) = 2 := by omega
  by_cases eq : n = m
  · exact Or.inl eq
  have nmem : n ∈ a := by simp [a, rawNonroots, hn]
  have mmem : m ∈ a := by simp [a, rawNonroots, hm]
  have rmem : row n ∈ rows := Finset.mem_image.mpr ⟨n, nmem, rfl⟩
  have ntwo : 2 ≤ count (row n) := by
    have sub : {n, m} ⊆ a.filter (fun p => row p = row n) := by
      simp [Finset.insert_subset_iff, nmem, mmem, he.symm]
    simpa [count, eq] using Finset.card_le_card sub
  have whereRow : row n = row R.H ∨ row n = row R.H1 := by
    by_contra bad
    have nw : row n ≠ row R.H := fun hh => bad (Or.inl hh)
    have nv : row n ≠ row R.H1 := fun hh => bad (Or.inr hh)
    have sub : {row n, row R.H, row R.H1} ⊆ rows := by
      simp [Finset.insert_subset_iff, wmem, vmem, rmem]
    have hle := Finset.sum_le_sum_of_subset sub (f := fun r => count r - 1)
    simp [nw, nv, hd, total, wc, vc] at hle
    omega
  have membership (p a1 a2 : Node) (hp : p ∈ a) (e1 : row a1 = row p)
      (e2 : row a2 = row p) (h1 : a1 ∈ a) (h2 : a2 ∈ a)
      (ne : a1 ≠ a2) (card : count (row p) = 2) : p = a1 ∨ p = a2 := by
    have sub : {a1, a2} ⊆ a.filter (fun n => row n = row p) := by
      simp [Finset.insert_subset_iff, h1, h2, e1, e2]
    have same : {a1, a2} = a.filter (fun n => row n = row p) :=
      Finset.eq_of_subset_of_card_le sub (by simpa [ne, count] using card.le)
    have mem : p ∈ ({a1, a2} : Finset Node) := by rw [same]; simp [hp]
    simpa using mem
  rcases whereRow with ew | ev
  · have cn : count (row n) = 2 := ew ▸ wc
    have cm : count (row m) = 2 := he ▸ cn
    have nn := membership n R.H R.K nmem ew.symm (hw.symm.trans ew.symm)
      (marked _ (Or.inl rfl)) (marked _ (Or.inr (Or.inl rfl))) distinct.1 cn
    have mm := membership m R.H R.K mmem (ew.symm.trans he) (hw.symm.trans (ew.symm.trans he))
      (marked _ (Or.inl rfl)) (marked _ (Or.inr (Or.inl rfl))) distinct.1 cm
    rcases nn with rfl | rfl <;> rcases mm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inl rfl
  · have cn : count (row n) = 2 := ev ▸ vc
    have cm : count (row m) = 2 := he ▸ cn
    have nn := membership n R.H1 R.K1 nmem ev.symm (hv.symm.trans ev.symm)
      (marked _ (Or.inr (Or.inr (Or.inl rfl))))
      (marked _ (Or.inr (Or.inr (Or.inr rfl)))) distinct.2.2.2.2.2 cn
    have mm := membership m R.H1 R.K1 mmem (ev.symm.trans he) (hv.symm.trans (ev.symm.trans he))
      (marked _ (Or.inr (Or.inr (Or.inl rfl))))
      (marked _ (Or.inr (Or.inr (Or.inr rfl)))) distinct.2.2.2.2.2 cm
    rcases nn with rfl | rfl <;> rcases mm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact Or.inl rfl

end RawGraph

end D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph
