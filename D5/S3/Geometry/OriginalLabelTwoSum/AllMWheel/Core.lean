/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Core
   generality: G
   digest: The separate good-path noncover collapse is constructed on the
           core alone; Gamma is never inverted to infer collapsibility.
   SOURCE_ONLY_UNCOMPILED. -/
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Protected

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open OriginalLabelTwoSum FiniteProtectedDualWord
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

private theorem edge_support (vs : List V) (e : Finset V) (he : e ∈ pathEdges vs) :
    e ⊆ vs.toFinset := by
  induction vs with
  | nil => simp [pathEdges] at he
  | cons a vs ih =>
      cases vs with
      | nil => simp [pathEdges] at he
      | cons b vs =>
          rcases Finset.mem_insert.mp he with rfl | he
          · simp
          · exact (ih he).trans (by simp)

private theorem noncover_mem (vs : List V) (s : Finset V) :
    s ∈ rawDual vs.toFinset (pathFamily vs) ↔ s ⊆ vs.toFinset ∧
      ∃ e ∈ pathEdges vs, Disjoint e s := by
  change s ∈ FiniteAlexanderDualCollapse.dualTable vs.toFinset
    (vs.toFinset.powerset.filter (fun T => T ∈ pathFamily vs)) ↔ _
  simp only [FiniteAlexanderDualCollapse.dualTable, Finset.mem_filter,
    Finset.mem_powerset, Finset.sdiff_subset, true_and, mem_pathFamily, mem_pathIndependentOn]
  constructor
  · rintro ⟨hs, hn⟩
    have hn' : ¬ ∀ e ∈ pathEdges vs, ¬ e ⊆ vs.toFinset \ s := by
      intro h
      exact hn h
    push_neg at hn'
    obtain ⟨e, he, hsub⟩ := hn'
    exact ⟨hs, e, he, Finset.disjoint_left.mpr (fun x hx hxs =>
      (Finset.mem_sdiff.mp (hsub hx)).2 hxs)⟩
  · rintro ⟨hs, e, he, hd⟩
    refine ⟨hs, ?_⟩
    intro hall
    exact hall e he (fun x hx => Finset.mem_sdiff.mpr
      ⟨edge_support vs e he hx, fun hxs => Finset.disjoint_left.mp hd hx hxs⟩)

/- The existing descending rectangle produces the actual first stage. -/
private def delete_cone_link (W : Finset V) (K : Family V) (a b : V)
    (hs : Supported W K) (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b)
    (hcone : ∀ s ∈ K, b ∈ s → insert a s ∈ K) :
    Sequence (project K) (project (restrict (W.erase b) K)) := by
  classical
  let Y := (W.erase a).erase b
  let F := Y.powerset.filter (fun t => insert b t ∈ K)
  have hF : ∀ t, t ∈ F ↔ t ⊆ Y ∧ insert b t ∈ K := by intro t; simp [F]
  have disj : Disjoint ({a,b} : Finset V) Y := by simp [Y, Finset.disjoint_left]
  have hdecomp : ∀ (s : Finset V), b ∈ s →
      s = ({b} ∪ ((s.erase a).erase b)) ∨
        s = insert a ({b} ∪ ((s.erase a).erase b)) := by
    intro s hbs
    by_cases has : a ∈ s
    · right; ext x; by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
    · left; ext x; by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  have hmem : ∀ t ∈ F, {b} ∪ t ∈ K ∧ insert a ({b} ∪ t) ∈ K := by
    intro t ht
    have hk := (hF t).mp ht |>.2
    exact ⟨by simpa using hk, by simpa using hcone _ hk (by simp)⟩
  have hco : ∀ t ∈ F, ∀ s ∈ K, {b} ∪ t ⊆ s →
      ∃ u ∈ F, t ⊆ u ∧ (s = {b} ∪ u ∨ s = insert a ({b} ∪ u)) := by
    intro t ht s hK hts
    have hbS : b ∈ s := hts (by simp)
    let u := (s.erase a).erase b
    refine ⟨u, (hF u).mpr ⟨?_, ?_⟩, ?_, hdecomp s hbS⟩
    · intro x hx
      obtain ⟨hxb, hxa, hxs⟩ := by simpa [u, Finset.mem_erase] using hx
      exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hs s hK hxs⟩⟩
    · apply K.lower _ hK
      exact Finset.insert_subset hbS ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    · intro x hx
      have hxY := (hF t).mp ht |>.1 <| hx
      obtain ⟨hxb, hxa, _⟩ := by simpa [Y, Finset.mem_erase] using hxY
      exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr
        ⟨hxa, hts (Finset.mem_union_right _ hx)⟩⟩
  let S := rectangle {a,b} Y {b} a disj (by simp) (by simp) (by simp [hab]) F K
    (fun t ht => ((hF t).mp ht).1) (by intro t ht; simp) hmem hco
  refine S.cast rfl ?_
  congr 1
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hK, hn⟩
    refine ⟨hK, ?_⟩
    have hbS : b ∉ s := by
      intro hbs
      let u := (s.erase a).erase b
      have hu : u ∈ F := (hF u).mpr ⟨by
        intro x hx
        obtain ⟨hxb, hxa, hxs⟩ := by simpa [u, Finset.mem_erase] using hx
        exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hs s hK hxs⟩⟩,
        K.lower (Finset.insert_subset hbs
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))) hK⟩
      exact hn ({b} ∪ u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        (Finset.union_subset (Finset.singleton_subset_iff.mpr hbs)
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun he => hbS (he ▸ hx), hs s hK hx⟩
  · rintro ⟨hK, hsW⟩
    refine ⟨hK, ?_⟩
    intro t ht hts
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_erase.mp (hsW (hts (by simp)))).1 rfl

private theorem path_link_cone (a b : V) (vs : List V) (hd : (a::b::vs).Nodup)
    (s : Finset V) (hs : s ∈ rawDual (a::b::vs).toFinset (pathFamily (a::b::vs)))
    (hb : b ∈ s) : insert a s ∈ rawDual (a::b::vs).toFinset (pathFamily (a::b::vs)) := by
  obtain ⟨hsW, e, he, heS⟩ := (noncover_mem _ _).mp hs
  apply (noncover_mem _ _).mpr
  refine ⟨Finset.insert_subset (by simp) hsW, e, he, ?_⟩
  have hae : a ∉ e := by
    rcases Finset.mem_insert.mp he with rfl | he
    · exact (Finset.disjoint_left.mp heS (by simp) hb).elim
    · intro hae
      have hmem := List.mem_toFinset.mp (edge_support (b::vs) e he hae)
      exact (List.nodup_cons.mp hd).1 hmem
  exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_insert.mp hxs).elim
    (fun he => hae (he ▸ hx)) (fun hxs => Finset.disjoint_left.mp heS hx hxs))

private theorem join_simplex (a : V) (T : Finset V) :
    rawJoin (delta {a}) (delta T) = delta (insert a T) := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact Finset.union_subset (hu.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop)) (hv.trans (Finset.subset_insert _ _))
  · intro hs
    refine ⟨s ∩ {a}, Finset.inter_subset_right, s.erase a, ?_, ?_⟩
    · intro x hx
      exact (Finset.mem_insert.mp (hs (Finset.mem_erase.mp hx).2)).resolve_left
        (Finset.mem_erase.mp hx).1
    · ext x; by_cases hxa : x = a <;> simp [hxa]

/- Exact post-first-stage family. The two endpoint edges give the two
   single-ghost cones; all remaining uncovered edges are tail edges. -/
private theorem path_delete_formula (a b c : V) (vs : List V)
    (hd : (a::b::c::vs).Nodup) :
    restrict ((a::b::c::vs).toFinset.erase b)
      (rawDual (a::b::c::vs).toFinset (pathFamily (a::b::c::vs))) =
      (delta (insert a vs.toFinset) ⊔ delta (insert c vs.toFinset)) ⊔
        rawJoin (delta {a,c}) (rawDual vs.toFinset (pathFamily vs)) := by
  have ha := (List.nodup_cons.mp hd).1
  have hb := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
  have hc := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
  have hab : a ≠ b := fun h => ha (by simp [h])
  have hac : a ≠ c := fun h => ha (by simp [h])
  have hbc : b ≠ c := fun h => hb (by simp [h])
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hK, hsW⟩
    obtain ⟨_, e, he, hdis⟩ := (noncover_mem _ _).mp hK
    have hbs : b ∉ s := fun h => (Finset.mem_erase.mp (hsW h)).1 rfl
    have hsupport : s ⊆ insert a (insert c vs.toFinset) := by
      intro x hx
      have hx' := (Finset.mem_erase.mp (hsW hx)).2
      simp only [List.toFinset_cons, Finset.mem_insert] at hx'
      rcases hx' with he | he | he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact (hbs (he ▸ hx)).elim
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl he)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr he)))
    by_cases has : a ∉ s
    · exact Or.inl (Or.inr (fun x hx => (Finset.mem_insert.mp (hsupport hx)).resolve_left
        (fun h => has (h ▸ hx))))
    · by_cases hcs : c ∉ s
      · left; left
        intro x hx
        rcases Finset.mem_insert.mp (hsupport hx) with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr ((Finset.mem_insert.mp h).resolve_left
            (fun h => hcs (h ▸ hx))))
      · have has' : a ∈ s := by simpa using has
        have hcs' : c ∈ s := by simpa using hcs
        have het : e ∈ pathEdges vs := by
          have he' : e = {a,b} ∨ e = {b,c} ∨ e ∈ pathEdges (c::vs) := by
            simpa only [pathEdges, Finset.mem_insert] using he
          rcases he' with rfl | rfl | he'
          · exact (Finset.disjoint_left.mp hdis (by simp) has').elim
          · exact (Finset.disjoint_left.mp hdis (by simp) hcs').elim
          · cases vs with
            | nil => simp [pathEdges] at he'
            | cons d vs =>
                rcases Finset.mem_insert.mp he' with rfl | he''
                · exact (Finset.disjoint_left.mp hdis (by simp) hcs').elim
                · exact he''
        right
        refine ⟨s ∩ {a,c}, Finset.inter_subset_right, s ∩ vs.toFinset,
          (noncover_mem vs _).mpr ⟨Finset.inter_subset_right, e, het,
            Finset.disjoint_left.mpr (fun x hx hxs =>
              Finset.disjoint_left.mp hdis hx (Finset.mem_inter.mp hxs).1)⟩, ?_⟩
        ext x
        constructor
        · intro hx
          rcases Finset.mem_insert.mp (hsupport hx) with h | h
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, by simp [h]⟩)
          · rcases Finset.mem_insert.mp h with h | h
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, by simp [h]⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, h⟩)
        · intro hx; exact (Finset.mem_union.mp hx).elim
            (fun h => (Finset.mem_inter.mp h).1) (fun h => (Finset.mem_inter.mp h).1)
  · rintro ((hs | hs) | ⟨u, hu, t, ht, rfl⟩)
    · have hbs : b ∉ s := by
        intro h
        have := hs h
        simp only [Finset.mem_insert, List.mem_toFinset] at this
        exact this.elim (fun h => hab h.symm) (fun h => hb (by simp [h]))
      refine ⟨(noncover_mem _ _).mpr ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), {b,c}, by simp [pathEdges], ?_⟩, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro x hx hxs
        rcases (show x = b ∨ x = c by simpa using hx) with rfl | rfl
        · exact hbs hxs
        · have := hs hxs
          simp only [Finset.mem_insert, List.mem_toFinset] at this
          exact this.elim (fun h => hac h.symm) hc
      · exact Finset.subset_erase.mpr ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), hbs⟩
    · have has : a ∉ s := by
        intro h
        have := hs h
        simp only [Finset.mem_insert, List.mem_toFinset] at this
        exact this.elim hac (fun h => ha (by simp [h]))
      have hbs : b ∉ s := by
        intro h
        have := hs h
        simp only [Finset.mem_insert, List.mem_toFinset] at this
        exact this.elim hbc (fun h => hb (by simp [h]))
      refine ⟨(noncover_mem _ _).mpr ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), {a,b}, by simp [pathEdges], ?_⟩,
        Finset.subset_erase.mpr ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), hbs⟩⟩
      simp [Finset.disjoint_left, has, hbs]
    · obtain ⟨htW, e, he, hdis⟩ := (noncover_mem vs t).mp ht
      have hsW : u ∪ t ⊆ (a::b::c::vs).toFinset :=
        Finset.union_subset (hu.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop)) (htW.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop))
      have hbs : b ∉ u ∪ t := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · have := hu h; simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact this.elim (fun h => hab h.symm) hbc
        · exact hb (by simp [List.mem_toFinset.mp (htW h)])
      refine ⟨(noncover_mem _ _).mpr ⟨hsW, e, ?_, ?_⟩,
        Finset.subset_erase.mpr ⟨hsW, hbs⟩⟩
      · cases vs <;> simp_all [pathEdges]
      · apply Finset.disjoint_left.mpr
        intro x hx hxs
        rcases Finset.mem_union.mp hxs with hxu | hxt
        · have hxl := List.mem_toFinset.mp (edge_support vs e he hx)
          have hxa := hu hxu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxa
          exact hxa.elim (fun h => ha (by simp only [List.mem_cons]; exact Or.inr (Or.inr (h ▸ hxl)))) (fun h => hc (h ▸ hxl))
        · exact Finset.disjoint_left.mp hdis hx hxt

/- The all-length tail Gamma used below is the immutable path Word with
   H=empty ONLY after its no-critical condition has been proved. -/
private def tailGamma (vs : List V) (hd : vs.Nodup) (h2 : 2 ≤ vs.length)
    (h1 : vs.length % 3 = 1) :
    Sequence (project (delta vs.toFinset)) (project (rawDual vs.toFinset (pathFamily vs))) := by
  have hcrit : ∀ q ∈ (pathWordData vs hd).word, ¬ q.isCritical := by
    intro q hq hc
    cases q with
    | pair L v => exact hc
    | critical S =>
        have hs := (criticalFaces_mem _ S).mpr (by simpa only [pathWordData_word] using hq)
        rw [pathWord_critical_formula vs hd, if_pos h1] at hs
        exact Finset.notMem_empty _ hs
  exact (pathWordData vs hd).noCritical_unprotected hcrit (by
    intro L v hp
    have hd' := (pathWordData vs hd).pair_data L v hp
    have hU := (mem_pathIndependentOn vs _).mp ((mem_pathFamily vs _).mp hd'.2.1)
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hU.1, ?_⟩
    intro he
    cases vs with
    | nil => simp at h2
    | cons a vs =>
        cases vs with
        | nil => simp at h2
        | cons b vs =>
            exact hU.2 {a,b} (by simp [pathEdges]) (by rw [he]; simp))

private def coreFinish (a b c : V) (vs : List V) (hd : (a::b::c::vs).Nodup)
    (hne : 0 < vs.length) (hmod : vs.length % 3 = 1) :
    Σ p : {p : V // p ∈ (a::b::c::vs).toFinset},
      Sequence (project ((delta (insert a vs.toFinset) ⊔ delta (insert c vs.toFinset)) ⊔
        rawJoin (delta {a,c}) (rawDual vs.toFinset (pathFamily vs))))
          (project (delta {p.val})) := by
  have ha := (List.nodup_cons.mp hd).1
  have hb := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
  have hct := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
  have hvs := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).2
  have has : a ∉ vs.toFinset := fun h => ha (by simp [List.mem_toFinset.mp h])
  have hcs : c ∉ vs.toFinset := fun h => hct (List.mem_toFinset.mp h)
  by_cases hsingle : vs.length = 1
  · have hex : ∃ d, vs = [d] := by
      cases vs with
      | nil => simp at hsingle
      | cons d vs =>
          have he : vs = [] := List.length_eq_zero_iff.mp (by simpa using hsingle)
          subst vs
          exact ⟨d, rfl⟩
    let d := Classical.choose hex
    have he : vs = [d] := Classical.choose_spec hex
    rw [he]
    have hN : rawDual ([d] : List V).toFinset (pathFamily [d]) = ⊥ := by
      apply SetLike.ext
      intro s
      simp only [noncover_mem, pathEdges, Finset.notMem_empty, exists_prop,
        false_and, exists_false, and_false]
      rfl
    let D : Family V := delta {a,d} ⊔ delta {c,d}
    have hsrc : ((delta (insert a ([d] : List V).toFinset) ⊔
        delta (insert c ([d] : List V).toFinset)) ⊔
        rawJoin (delta {a,c}) (rawDual ([d] : List V).toFinset (pathFamily [d]))) = D := by
      rw [hN, (rawJoin_void (delta {a,c})).2, sup_bot_eq]
      rfl
    have hs : Supported (a::b::c::[d]).toFinset D := by
      intro s h
      rcases h with h | h <;> exact h.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop)
    have hp : ({d} : Finset V) ∈ D := Or.inl (by simp)
    have hcone : ∀ s ∈ D, insert d s ∈ D := by
      intro s h
      rcases h with h | h
      · exact Or.inl (Finset.insert_subset (by simp) h)
      · exact Or.inr (Finset.insert_subset (by simp) h)
    exact ⟨⟨d, by simp⟩, (collapseCone _ D d hs hp hcone).cast
      (congrArg project hsrc).symm rfl⟩
  · have h2 : 2 ≤ vs.length := by omega
    let N := rawDual vs.toFinset (pathFamily vs)
    let C := delta (insert c vs.toFinset) ⊔ rawJoin (delta {a,c}) N
    have hN0 : (∅ : Finset V) ∈ N := by
      apply (noncover_mem vs ∅).mpr
      refine ⟨Finset.empty_subset _, ?_⟩
      cases vs with
      | nil => simp at h2
      | cons d vs =>
          cases vs with
          | nil => simp at h2
          | cons e vs => exact ⟨{d,e}, by simp [pathEdges], by simp⟩
    have hdisj : Disjoint ({a} : Finset V) vs.toFinset := by simpa using has
    have hboundary : ∀ x ⊂ ({a} : Finset V), ∀ t ∈ delta vs.toFinset, x ∪ t ∈ C := by
      intro x hx t ht
      have he : x = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hya : y = a := Finset.mem_singleton.mp (hx.subset hy)
        have hax : a ∈ x := hya ▸ hy
        exact hx.ne (Finset.Subset.antisymm hx.subset (Finset.singleton_subset_iff.mpr hax))
      subst x
      exact Or.inl (by simpa using ht.trans (Finset.subset_insert c vs.toFinset))
    have hbase : ∀ t ⊆ vs.toFinset, {a} ∪ t ∈ C → t ∈ N := by
      intro t ht h
      rcases h with h | ⟨u, hu, v, hv, he⟩
      · have haC : a ∈ insert c vs.toFinset := h (by simp)
        rcases Finset.mem_insert.mp haC with he | he
        · exact (ha (by simp [he])).elim
        · exact (has he).elim
      · apply N.lower _ hv
        intro x hx
        have hxt : x ∈ u ∪ v := by rw [← he]; exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hxt with hxu | hxv
        · have hxac := hu hxu
          rcases (show x = a ∨ x = c by simpa using hxac) with he | he
          · exact (has (he ▸ ht hx)).elim
          · exact (hcs (he ▸ ht hx)).elim
        · exact hxv
    let S := liftFibre (delta vs.toFinset) N C {a} vs.toFinset (Finset.empty_subset _) hN0
      (tailGamma vs hvs h2 hmod) hdisj (fun _ h => h) hboundary hbase
    have hstart : ((delta (insert a vs.toFinset) ⊔ delta (insert c vs.toFinset)) ⊔
        rawJoin (delta {a,c}) N) = C ⊔ rawJoin (delta {a}) (delta vs.toFinset) := by
      rw [join_simplex]
      exact by simp only [C, sup_assoc, sup_comm, sup_left_comm]
    have hend : C ⊔ rawJoin (delta {a}) N = C := by
      apply sup_eq_left.mpr
      rintro s ⟨u, hu, v, hv, rfl⟩
      exact Or.inr ⟨u, (show u ⊆ ({a,c} : Finset V) from
        (show u ⊆ {a} from hu).trans (Finset.singleton_subset_iff.mpr (by simp))),
        v, hv, rfl⟩
    have hC : Supported (a::b::c::vs).toFinset C := by
      intro s h
      rcases h with h | ⟨u, hu, v, hv, rfl⟩
      · exact h.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop)
      · exact Finset.union_subset (hu.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop))
          (((noncover_mem vs v).mp hv).1.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop))
    have hp : ({c} : Finset V) ∈ C := Or.inl (by simp)
    have hcone : ∀ s ∈ C, insert c s ∈ C := by
      intro s h
      rcases h with h | ⟨u, hu, v, hv, rfl⟩
      · exact Or.inl (Finset.insert_subset (by simp) h)
      · exact Or.inr ⟨insert c u, Finset.insert_subset (by simp) hu, v, hv, by simp⟩
    exact ⟨⟨c, by simp⟩,
      (S.cast (congrArg project hstart).symm (congrArg project hend)).append
        (collapseCone _ C c hC hp hcone)⟩

/-- P09's separate collapse of the actual good-length path noncover core.
    The m=4 tail is handled as a cone, never collapsed from UNIT to VOID. -/
def pathGoodCore (vs : List V) (hd : vs.Nodup) (h4 : 4 ≤ vs.length)
    (h1 : vs.length % 3 = 1) :
    Σ p : {p : V // p ∈ vs.toFinset},
      Sequence (project (rawDual vs.toFinset (pathFamily vs))) (project (delta {p.val})) := by
  cases vs with
  | nil => simp at h4
  | cons a vs =>
      cases vs with
      | nil => simp at h4
      | cons b vs =>
          cases vs with
          | nil => simp at h4
          | cons c vs =>
              have hne : 0 < vs.length := by simp only [List.length_cons] at h4; omega
              have hmod : vs.length % 3 = 1 := by simp only [List.length_cons] at h1; omega
              have hs : Supported (a::b::c::vs).toFinset
                  (rawDual (a::b::c::vs).toFinset (pathFamily (a::b::c::vs))) :=
                fun s h => ((noncover_mem _ _).mp h).1
              have hab : a ≠ b := fun h => (List.nodup_cons.mp hd).1 (by simp [h])
              let S := delete_cone_link _ _ a b hs (by simp) (by simp) hab
                (path_link_cone a b (c::vs) hd)
              let T := coreFinish a b c vs hd hne hmod
              exact ⟨T.1, (S.cast rfl (congrArg project (path_delete_formula a b c vs hd))).append T.2⟩

/-- Separate collapse on E_m ALONE to a retained original label. -/
def pathRootCore (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :
    Σ p : {p : Label m // p ∈ ground m},
      Sequence (project (pathRoot m hm)) (project (delta {p.val})) := by
  let k := Classical.choose hg
  have hk := Classical.choose_spec hg
  have h4 : 4 ≤ m := by omega
  have hmod : m % 3 = 1 := by omega
  let S := pathGoodCore (pathRootPath m hm) (pathRootPath_nodup m hm)
    (by simpa only [pathRootPath_length] using h4)
    (by simpa only [pathRootPath_length] using hmod)
  have hp : S.1.val ∈ ground m := by
    simpa only [pathRootPath_vertices] using S.1.property
  have hsrc : rawDual (pathRootPath m hm).toFinset (pathFamily (pathRootPath m hm)) =
      pathRoot m hm := by rw [pathRootPath_vertices, pathRoot_rawDual]
  exact ⟨⟨S.1.val, hp⟩, S.2.cast (congrArg project hsrc) rfl⟩

/-- The right wheel's actual absolute certificate: fill0 runs in Delta(Z)
    while fixing E, then the separate list collapses E alone. -/
def wheelCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :
    Certificate (ground m) (A1 m hm) := by
  let f := fill0 m hm
  let C := pathRootCore m hm hg
  have hEZ : A0 m hm ≤ pathRoot m hm := inf_le_left
  have hN0 : (∅ : Finset (Label m)) ∈ endpoint (A0 m hm) f.critical := Or.inl f.empty_mem
  let S := liftFibre (delta (tailGround m hm)) (endpoint (A0 m hm) f.critical)
    (pathRoot m hm) ∅ (tailGround m hm) (Finset.empty_subset _) hN0 f.main (by simp)
    (fun _ h => h)
    (by intro x hx; exact (Finset.not_ssubset_empty x hx).elim)
    (by intro t ht h; exact Or.inl ⟨by simpa using h, ht⟩)
  have hstart : pathRoot m hm ⊔ rawJoin (delta ∅) (delta (tailGround m hm)) = A1 m hm := by
    rw [(rawJoin_unit _).1]
    rfl
  have hend : pathRoot m hm ⊔ rawJoin (delta ∅) (endpoint (A0 m hm) f.critical) =
      endpoint (pathRoot m hm) f.critical := by
    rw [(rawJoin_unit _).1]
    change pathRoot m hm ⊔ (A0 m hm ⊔ facets f.critical) = pathRoot m hm ⊔ facets f.critical
    rw [← sup_assoc, sup_eq_left.mpr hEZ]
  have hcore : Supported (ground m) (pathRoot m hm) :=
    ((rimRows m (by omega)).without (interfaceRow m hm)).root_supported
  refine {
    supported := ?_
    core := pathRoot m hm
    critical := f.critical
    vertex := C.1.val
    vertex_mem := ?_
    core_supported := hcore
    critical_supported := by intro s hs; exact (f.critical_supported s hs).trans Finset.sdiff_subset
    cells := ?_
    main := S.cast (congrArg project hstart) (congrArg project hend)
    separate := C.2 }
  · intro s hs
    rcases hs with hs | hs
    · exact hcore s hs
    · exact hs.trans Finset.sdiff_subset
  · exact (C.2.monotone ⟨by simp, by simp⟩).2
  · constructor
    · exact f.cells.nonempty
    · intro s hs hE
      exact f.cells.absent s hs ⟨hE, f.critical_supported s hs⟩
    · intro s hs t hts
      exact hEZ (f.cells.boundary s hs t hts)
    · exact f.cells.antichain

private theorem raw_dual_mem (W : Finset V) (K : Family V) (s : Finset V) :
    s ∈ rawDual W K ↔ s ⊆ W ∧ W \ s ∉ K := by
  change s ∈ FiniteAlexanderDualCollapse.dualTable W
    (W.powerset.filter (fun T => T ∈ K)) ↔ _
  simp only [FiniteAlexanderDualCollapse.dualTable, Finset.mem_filter,
    Finset.mem_powerset, Finset.sdiff_subset, true_and]

private theorem two_ghost_dual (a c : V) (T : Finset V) (K : Family V)
    (hac : a ≠ c) (ha : a ∉ T) (hc : c ∉ T) (hK : Supported T K) :
    rawDual (insert a (insert c T)) K =
      (delta (insert a T) ⊔ delta (insert c T)) ⊔
        rawJoin (delta {a,c}) (rawDual T K) := by
  apply SetLike.ext
  intro s
  rw [raw_dual_mem]
  constructor
  · rintro ⟨hsW, hn⟩
    by_cases has : a ∈ s
    · by_cases hcs : c ∈ s
      · right
        have he : insert a (insert c T) \ s = T \ (s ∩ T) := by
          ext x
          constructor
          · intro hmem
            obtain ⟨hx, hxs⟩ := Finset.mem_sdiff.mp hmem
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact (hxs has).elim
            · rcases Finset.mem_insert.mp hx with rfl | hx
              · exact (hxs hcs).elim
              · exact Finset.mem_sdiff.mpr ⟨hx, fun h => hxs (Finset.mem_inter.mp h).1⟩
          · intro hx
            have ht := Finset.mem_sdiff.mp hx
            exact Finset.mem_sdiff.mpr ⟨by simp [ht.1],
              fun hxs => ht.2 (Finset.mem_inter.mpr ⟨hxs, ht.1⟩)⟩
        refine ⟨s ∩ {a,c}, Finset.inter_subset_right, s ∩ T,
          (raw_dual_mem T K _).mpr ⟨Finset.inter_subset_right, by rw [← he]; exact hn⟩, ?_⟩
        ext x
        constructor
        · intro hx
          rcases Finset.mem_insert.mp (hsW hx) with hxa | hx'
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, by simp [hxa]⟩)
          · rcases Finset.mem_insert.mp hx' with hxc | hxt
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, by simp [hxc]⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxt⟩)
        · intro hx
          exact (Finset.mem_union.mp hx).elim (fun h => (Finset.mem_inter.mp h).1)
            (fun h => (Finset.mem_inter.mp h).1)
      · left; left
        intro x hx
        rcases Finset.mem_insert.mp (hsW hx) with hxa | hx'
        · exact Finset.mem_insert.mpr (Or.inl hxa)
        · exact Finset.mem_insert.mpr (Or.inr ((Finset.mem_insert.mp hx').resolve_left
            (fun hxc => hcs (hxc ▸ hx))))
    · left; right
      intro x hx
      exact (Finset.mem_insert.mp (hsW hx)).resolve_left (fun hxa => has (hxa ▸ hx))
  · rintro ((hs | hs) | ⟨u, hu, t, ht, rfl⟩)
    · refine ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), ?_⟩
      intro h
      have hcs : c ∉ s := by
        intro hcs
        exact (Finset.mem_insert.mp (hs hcs)).elim (fun he => hac he.symm) hc
      exact hc (hK _ h (Finset.mem_sdiff.mpr ⟨by simp, hcs⟩))
    · refine ⟨hs.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop), ?_⟩
      intro h
      have has : a ∉ s := by
        intro has
        exact (Finset.mem_insert.mp (hs has)).elim hac ha
      exact ha (hK _ h (Finset.mem_sdiff.mpr ⟨by simp, has⟩))
    · obtain ⟨htT, hn⟩ := (raw_dual_mem T K t).mp ht
      refine ⟨Finset.union_subset (hu.trans (by
          intro x hx
          simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          aesop)) (htT.trans ((Finset.subset_insert c T).trans (Finset.subset_insert a _))), ?_⟩
      intro h
      apply hn
      apply K.lower _ h
      intro x hx
      obtain ⟨hxT, hxnt⟩ := Finset.mem_sdiff.mp hx
      refine Finset.mem_sdiff.mpr ⟨by simp [hxT], ?_⟩
      intro hxs
      rcases Finset.mem_union.mp hxs with hxu | hxt
      · rcases (show x = a ∨ x = c by simpa using hu hxu) with hxa | hxc
        · exact ha (hxa ▸ hxT)
        · exact hc (hxc ▸ hxT)
      · exact hxnt hxt

/-- P08's additional actual collapse of A0 in residue two. This is separate
    from fill0.main; a simplex collapsing onto A0 is not used in reverse. -/
def zeroCore (m : Nat) (hm : 3 ≤ m) (h2 : m % 3 = 2) :
    Σ p : {p : Label m // p ∈ tailGround m hm},
      Sequence (project (A0 m hm)) (project (delta {p.val})) := by
  have h5 : 5 ≤ m := by omega
  let a : Label m := ⟨3, by omega⟩
  let b := firstLabel m hm
  let c := lastLabel m
  let vs := cyclePathTail m hm
  have ha : a ∉ vs := by
    rw [← List.mem_toFinset, cyclePathTail_vertices]
    dsimp [a]
    omega
  have hb : b ∉ c::vs := by
    simp only [List.mem_cons, b, c, firstLabel, lastLabel, Fin.ext_iff, not_or]
    constructor
    · omega
    · intro h
      have hx := (cyclePathTail_vertices m hm b).mp (List.mem_toFinset.mpr h)
      dsimp [b, firstLabel] at hx
      omega
  have hc : c ∉ vs := by
    rw [← List.mem_toFinset, cyclePathTail_vertices]
    dsimp [c, lastLabel]
    omega
  have hd : (a::b::c::vs).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨hb, List.nodup_cons.mpr
      ⟨hc, cyclePathTail_nodup m hm⟩⟩⟩
    simp only [List.mem_cons, not_or]
    exact ⟨by intro h; have he := congrArg Fin.val h; dsimp [a,b,firstLabel] at he; omega,
      by intro h; have he := congrArg Fin.val h; dsimp [a,c,lastLabel] at he; omega, ha⟩
  have hw : tailGround m hm = insert a (insert c vs.toFinset) := by
    ext x
    simp only [tailGround, ground, rim, Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_insert, Finset.mem_singleton,
      cyclePathTail_vertices, Fin.ext_iff, a, c, firstLabel, secondLabel, lastLabel,
      vs, ne_eq, Fin.val_zero, Fin.val_mk]
    have := x.isLt
    omega
  have hK : Supported vs.toFinset (pathFamily vs) := by
    intro s hs
    exact ((mem_pathIndependentOn vs s).mp ((mem_pathFamily vs s).mp hs)).1
  have hformula := two_ghost_dual a c vs.toFinset (pathFamily vs)
    (by intro h; have he := congrArg Fin.val h; dsimp [a,c,lastLabel] at he; omega)
    (by simpa only [List.mem_toFinset] using ha) (by simpa only [List.mem_toFinset] using hc) hK
  have hD : ((delta (insert a vs.toFinset) ⊔ delta (insert c vs.toFinset)) ⊔
      rawJoin (delta {a,c}) (rawDual vs.toFinset (pathFamily vs))) = A0 m hm := by
    rw [← hformula, ← hw]
    exact A0_rawDual m hm
  let S := coreFinish a b c vs hd (by simp only [vs, cyclePathTail_length]; omega)
    (by simp only [vs, cyclePathTail_length]; omega)
  let G := S.2.cast (congrArg project hD) rfl
  have hp : S.1.val ∈ tailGround m hm := by
    have hpoint : ({S.1.val} : Finset (Label m)) ∈ project (delta {S.1.val}) :=
      ⟨by simp, Finset.Subset.refl _⟩
    have hs := (G.monotone hpoint).2
    exact hs.2 (by simp)
  exact ⟨⟨S.1.val, hp⟩, G⟩

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
