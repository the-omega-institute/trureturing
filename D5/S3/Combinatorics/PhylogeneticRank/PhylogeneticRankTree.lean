/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankTree
   mirror-E: none(waiver:weighted-tree-metric)
   anchors: []
   utility: none
   digest: Positive weighted tree distances equal the length of the unique simple path. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank

open SimpleGraph PhylogeneticRankDefs

/-- Loop erasure decreases positive weighted length, so the unique path attains the infimum. -/
theorem tree_dist_eq_path_length (T : MetricTree) {u v : Fin T.m}
    (p : T.graph.Walk u v) (hp : p.IsPath) : T.dist u v = T.walkLength p := by
  classical
  have hn : ∀ {x y : Fin T.m} (w : T.graph.Walk x y), 0 ≤ T.walkLength w := by
    intro x y w
    induction w with
    | nil => exact le_rfl
    | cons h w ih => exact add_nonneg (T.len_pos _ _ h).le ih
  have ha : ∀ {x y z : Fin T.m} (w : T.graph.Walk x y) (q : T.graph.Walk y z),
      T.walkLength (w.append q) = T.walkLength w + T.walkLength q := by
    intro x y z w q
    induction w with
    | nil => simp [MetricTree.walkLength]
    | cons h w ih => simp [MetricTree.walkLength, ih, add_assoc]
  have hd : ∀ {x y z : Fin T.m} (w : T.graph.Walk x y) (h : z ∈ w.support),
      T.walkLength (w.dropUntil z h) ≤ T.walkLength w := by
    intro x y z w h
    have he := ha (w.takeUntil z h) (w.dropUntil z h)
    rw [Walk.take_spec] at he
    linarith [hn (w.takeUntil z h)]
  have hb : ∀ {x y : Fin T.m} (w : T.graph.Walk x y),
      T.walkLength w.bypass ≤ T.walkLength w := by
    intro x y w
    induction w with
    | nil => exact le_rfl
    | @cons x z y h w ih =>
      simp only [Walk.bypass]
      split_ifs with hx
      · exact (hd w.bypass hx).trans
          (ih.trans (le_add_of_nonneg_left (T.len_pos x z h).le))
      · exact add_le_add_right ih _
  have hmin : ∀ w : T.graph.Walk u v, T.walkLength p ≤ T.walkLength w := by
    intro w
    have he := T.isTree.isAcyclic.subsingleton_path u v |>.elim
      (⟨p, hp⟩ : T.graph.Path u v) w.toPath
    have he' : p = w.bypass := congrArg Subtype.val he
    rw [he']
    exact hb w
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact hn w⟩ ⟨p, rfl⟩
  · exact le_csInf ⟨T.walkLength p, p, rfl⟩ (by rintro _ ⟨w, rfl⟩; exact hmin w)

/-- Root paths split at their last common vertex; their remaining branches are disjoint. -/
theorem tree_root_path_fork (T : MetricTree) {a b c : Fin T.m}
    (p : T.graph.Walk a b) (q : T.graph.Walk a c) (hp : p.IsPath) (hq : q.IsPath) :
    ∃ m : Fin T.m, ∃ r : T.graph.Walk a m,
      ∃ p' : T.graph.Walk m b, ∃ q' : T.graph.Walk m c,
        r.IsPath ∧ p'.IsPath ∧ q'.IsPath ∧ p = r.append p' ∧ q = r.append q' ∧
        (∀ x, x ∈ p.support ∧ x ∈ q.support ↔ x ∈ r.support) ∧
        (∀ x, x ∈ p'.support → x ∈ q'.support → x = m) := by
  classical
  induction p generalizing c with
  | nil =>
    refine ⟨_, .nil, .nil, q, .nil, .nil, hq, rfl, rfl, ?_, ?_⟩
    · intro x
      simp only [Walk.support_nil, List.mem_singleton]
      exact ⟨And.left, fun h => ⟨h, h ▸ q.start_mem_support⟩⟩
    · intro x hx _
      simpa using hx
  | @cons a t b h p ih =>
    cases q with
    | nil =>
      refine ⟨_, .nil, Walk.cons h p, .nil, .nil, hp, .nil, rfl, rfl, ?_, ?_⟩
      · intro x
        simp only [Walk.support_nil, List.mem_singleton]
        exact ⟨And.right, fun hx => ⟨hx ▸ (Walk.cons h p).start_mem_support, hx⟩⟩
      · intro x _ hx
        simpa using hx
    | @cons _ t' c h' q =>
      by_cases he : t = t'
      · subst t'
        obtain ⟨m, r, p', q', hr, hp', hq', ep, eq, hinter, hbranch⟩ :=
          ih q hp.of_cons hq.of_cons
        have erp : (Walk.cons h p : T.graph.Walk a b) = (Walk.cons h r).append p' := by
          simp [ep]
        refine ⟨m, Walk.cons h r, p', q', ?_, hp', hq', erp, ?_, ?_, hbranch⟩
        · rw [erp] at hp
          exact hp.of_append_left
        · simp [eq]
        · intro x
          simp only [Walk.support_cons, List.mem_cons]
          have hx := hinter x
          tauto
      · have hcommon : ∀ x, x ∈ (Walk.cons h p).support →
            x ∈ (Walk.cons h' q).support → x = a := by
          intro x hx hy
          by_contra hxa
          have hh := T.isTree.isAcyclic.subsingleton_path a x |>.elim
            (⟨(Walk.cons h p).takeUntil x hx, hp.takeUntil hx⟩ : T.graph.Path a x)
            ⟨(Walk.cons h' q).takeUntil x hy, hq.takeUntil hy⟩
          have hs := congrArg (fun w : T.graph.Path a x => w.val.snd) hh
          rw [Walk.snd_takeUntil hxa, Walk.snd_takeUntil hxa] at hs
          exact he (by simpa using hs)
        refine ⟨a, .nil, Walk.cons h p, Walk.cons h' q, .nil, hp, hq, rfl, rfl, ?_, ?_⟩
        · intro x
          simp only [Walk.support_nil, List.mem_singleton]
          exact ⟨fun hx => hcommon x hx.1 hx.2,
            fun hx => ⟨hx ▸ (Walk.cons h p).start_mem_support,
              hx ▸ (Walk.cons h' q).start_mem_support⟩⟩
        · exact hcommon

/-- The common-prefix heights satisfy the ultrametric inequality, giving four points. -/
theorem tree_four_point (T : MetricTree) (a b c d : Fin T.m) :
    T.dist a b + T.dist c d ≤
      max (T.dist a c + T.dist b d) (T.dist a d + T.dist b c) := by
  classical
  have hn : ∀ {x y : Fin T.m} (w : T.graph.Walk x y), 0 ≤ T.walkLength w := by
    intro x y w
    induction w with
    | nil => exact le_rfl
    | cons h w ih => exact add_nonneg (T.len_pos _ _ h).le ih
  have ha : ∀ {x y z : Fin T.m} (w : T.graph.Walk x y) (q : T.graph.Walk y z),
      T.walkLength (w.append q) = T.walkLength w + T.walkLength q := by
    intro x y z w q
    induction w with
    | nil => simp [MetricTree.walkLength]
    | cons h w ih => simp [MetricTree.walkLength, ih, add_assoc]
  have hr : ∀ {x y : Fin T.m} (w : T.graph.Walk x y),
      T.walkLength w.reverse = T.walkLength w := by
    intro x y w
    induction w with
    | nil => rfl
    | cons h w ih =>
      simp [Walk.reverse_cons, ha, ih, MetricTree.walkLength, T.len_symm, add_comm]
  have hsub : ∀ {x y z : Fin T.m} (r : T.graph.Walk x y) (s : T.graph.Walk x z),
      r.IsPath → s.IsPath → y ∈ s.support → T.walkLength r ≤ T.walkLength s := by
    intro x y z r s hrr hss hy
    have he := T.isTree.isAcyclic.subsingleton_path x y |>.elim
      (⟨r, hrr⟩ : T.graph.Path x y) ⟨s.takeUntil y hy, hss.takeUntil hy⟩
    have he' : r = s.takeUntil y hy := congrArg Subtype.val he
    have hs := ha (s.takeUntil y hy) (s.dropUntil y hy)
    rw [Walk.take_spec] at hs
    rw [he']
    linarith [hn (s.dropUntil y hy)]
  have hnest : ∀ {x y z w : Fin T.m} (r : T.graph.Walk x y) (s : T.graph.Walk x z)
      (p : T.graph.Walk y w) (q : T.graph.Walk z w),
      r.append p = s.append q → r.length ≤ s.length → y ∈ s.support := by
    intro x y z w r s p q he hle
    have hg := congrArg (fun t : T.graph.Walk x w => t.getVert r.length) he
    simp only [Walk.getVert_append', le_refl, if_true, Walk.getVert_length,
      if_pos hle] at hg
    rw [hg]
    exact s.getVert_mem_support _
  have hformula : ∀ {x y z m : Fin T.m} (p : T.graph.Walk x y)
      (q : T.graph.Walk x z) (r : T.graph.Walk x m)
      (p' : T.graph.Walk m y) (q' : T.graph.Walk m z),
      p.IsPath → q.IsPath → r.IsPath → p'.IsPath → q'.IsPath →
      p = r.append p' → q = r.append q' →
      (∀ t, t ∈ p'.support → t ∈ q'.support → t = m) →
      T.dist y z = T.dist x y + T.dist x z - 2 * T.walkLength r := by
    intro x y z m p q r p' q' hp hq hrr hp' hq' ep eq hinter
    have hjoin : (p'.reverse.append q').IsPath := by
      apply Walk.IsPath.mk'
      rw [Walk.support_append, Walk.support_reverse, List.nodup_append']
      refine ⟨(by simpa using hp'.reverse.support_nodup), hq'.support_nodup.tail, ?_⟩
      intro t ht ht'
      have htm : t = m := hinter t (List.mem_reverse.mp ht) (List.mem_of_mem_tail ht')
      subst t
      have hnn := hq'.support_nodup
      rw [← q'.cons_tail_support, List.nodup_cons] at hnn
      exact hnn.1 ht'
    rw [tree_dist_eq_path_length T _ hjoin, ha, hr,
      tree_dist_eq_path_length T p hp, tree_dist_eq_path_length T q hq, ep, eq, ha, ha]
    ring
  obtain ⟨pb, hpb, _⟩ := T.isTree.existsUnique_path a b
  obtain ⟨pc, hpc, _⟩ := T.isTree.existsUnique_path a c
  obtain ⟨pd, hpd, _⟩ := T.isTree.existsUnique_path a d
  obtain ⟨mbc, rbc, sbc, tbc, hrbc, hsbc, htbc, ebc, ecb, ibc, jbc⟩ :=
    tree_root_path_fork T pb pc hpb hpc
  obtain ⟨mbd, rbd, sbd, tbd, hrbd, hsbd, htbd, ebd, edb, ibd, jbd⟩ :=
    tree_root_path_fork T pb pd hpb hpd
  obtain ⟨mcd, rcd, scd, tcd, hrcd, hscd, htcd, ecd, edc, icd, jcd⟩ :=
    tree_root_path_fork T pc pd hpc hpd
  have hmineq : ∀ {x y z w m₁ m₂ m₃ : Fin T.m}
      (p : T.graph.Walk x y) (q : T.graph.Walk x z) (t : T.graph.Walk x w)
      (r₁ : T.graph.Walk x m₁) (r₂ : T.graph.Walk x m₂) (r₃ : T.graph.Walk x m₃)
      (t₂ : T.graph.Walk m₂ w) (t₃ : T.graph.Walk m₃ w),
      r₁.IsPath → r₂.IsPath → r₃.IsPath →
      t = r₂.append t₂ → t = r₃.append t₃ →
      (∀ v, v ∈ p.support ∧ v ∈ q.support ↔ v ∈ r₁.support) →
      (∀ v, v ∈ p.support ∧ v ∈ t.support ↔ v ∈ r₂.support) →
      (∀ v, v ∈ q.support ∧ v ∈ t.support ↔ v ∈ r₃.support) →
      min (T.walkLength r₂) (T.walkLength r₃) ≤ T.walkLength r₁ := by
    intro x y z w m₁ m₂ m₃ p q t r₁ r₂ r₃ t₂ t₃ h₁ h₂ h₃ e₂ e₃ i₁ i₂ i₃
    by_cases hle : r₂.length ≤ r₃.length
    · have hm : m₂ ∈ r₃.support := hnest r₂ r₃ t₂ t₃ (e₂.symm.trans e₃) hle
      have hpq : m₂ ∈ p.support ∧ m₂ ∈ q.support :=
        ⟨((i₂ m₂).mpr r₂.end_mem_support).1, ((i₃ m₂).mpr hm).1⟩
      exact (min_le_left _ _).trans (hsub r₂ r₁ h₂ h₁ ((i₁ m₂).mp hpq))
    · have hm : m₃ ∈ r₂.support :=
        hnest r₃ r₂ t₃ t₂ (e₃.symm.trans e₂) (le_of_not_ge hle)
      have hpq : m₃ ∈ p.support ∧ m₃ ∈ q.support :=
        ⟨((i₂ m₃).mpr hm).1, ((i₃ m₃).mpr r₃.end_mem_support).1⟩
      exact (min_le_right _ _).trans (hsub r₃ r₁ h₃ h₁ ((i₁ m₃).mp hpq))
  have hacd := hmineq pc pd pb rcd rbc rbd sbc sbd hrcd hrbc hrbd ebc ebd icd
    (fun v => by simpa [and_comm] using ibc v)
    (fun v => by simpa [and_comm] using ibd v)
  have dbc := hformula pb pc rbc sbc tbc hpb hpc hrbc hsbc htbc ebc ecb jbc
  have dbd := hformula pb pd rbd sbd tbd hpb hpd hrbd hsbd htbd ebd edb jbd
  have dcd := hformula pc pd rcd scd tcd hpc hpd hrcd hscd htcd ecd edc jcd
  rw [dbc, dbd, dcd]
  by_cases hle : T.walkLength rbd ≤ T.walkLength rbc
  · rw [min_eq_right hle] at hacd
    exact (by linarith : T.dist a b +
      (T.dist a c + T.dist a d - 2 * T.walkLength rcd) ≤
      T.dist a c + (T.dist a b + T.dist a d - 2 * T.walkLength rbd)).trans
        (le_max_left _ _)
  · rw [min_eq_left (le_of_not_ge hle)] at hacd
    exact (by linarith : T.dist a b +
      (T.dist a c + T.dist a d - 2 * T.walkLength rcd) ≤
      T.dist a d + (T.dist a b + T.dist a c - 2 * T.walkLength rbc)).trans
        (le_max_right _ _)

#print axioms tree_dist_eq_path_length
#print axioms tree_root_path_fork
#print axioms tree_four_point

end D5.S3.Combinatorics.PhylogeneticRank
