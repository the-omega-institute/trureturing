/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter
   mirror-E: none(waiver:semi-baxter-equinumerosity)
   anchors: []
   utility: none
   digest: Weak ascent and vincular permutation avoiders have equal counts at every length. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentCounting
import D5.S3.Combinatorics.WeakAscent.WeakAscentPermParents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentSemiBaxter

open WeakAscentDefs WeakAscentGrowth WeakAscentStates WeakAscentChildren WeakAscentInsertion
open WeakAscentCounting WeakAscentSites WeakAscentPermChildren WeakAscentPermParents

def permExtensions (p : List ℕ) (depth : ℕ) : Set (List ℕ) :=
  {q | q ∈ permAvoiders (p.length + depth) ∧ q.filter (fun value => value ≤ p.length) = p}

theorem result : WeakAscentDefs.claim := by
  classical
  have maximum_parent (n : ℕ) (q : List ℕ) (hq : q ∈ permAvoiders (n + 1)) :
      ∃ site, site ≤ n ∧ (q.filter (fun value => value ≤ n)) ∈ permAvoiders n ∧
        q = (q.filter (fun value => value ≤ n)).insertIdx site (n + 1) := by
    have hperm := hq.1
    have hlength : q.length = n + 1 := by simpa using hperm.length_eq
    have hnodup : q.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
    have bound (value : ℕ) (hvalue : value ∈ q) : value ≤ n + 1 := by
      obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
      omega
    have hmaxmem : n + 1 ∈ q :=
      hperm.mem_iff.mpr (List.mem_range'.mpr ⟨n, by omega, by omega⟩)
    let site := q.idxOf (n + 1)
    have hsite : site < q.length := List.idxOf_lt_length_iff.mpr hmaxmem
    have hsitevalue : q[site] = n + 1 := List.getElem_idxOf hsite
    have hsite_option : q.idxOf? (n + 1) = some site := by
      apply List.idxOf?_eq_some_iff.mpr
      refine ⟨hsite, hsitevalue, ?_⟩
      intro earlier hearlier heq
      have hread : q.getD earlier 0 = q.getD site 0 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hsite]
        exact heq.trans hsitevalue.symm
      have hsame := (List.getD_inj (show earlier < q.length by omega) hsite hnodup).mp hread
      omega
    have erase_index : q.erase (n + 1) = q.eraseIdx site := by
      rw [List.erase_eq_eraseIdx, hsite_option]
    have erase_filter : q.erase (n + 1) = q.filter (fun value => value ≤ n) := by
      rw [hnodup.erase_eq_filter]
      apply List.filter_congr
      intro value hvalue
      have hbound := bound value hvalue
      by_cases hle : value ≤ n
      · have hne : value ≠ n + 1 := by omega
        simp [hle, hne]
      · have heq : value = n + 1 := by omega
        simp [heq]
    have reconstruct : (q.filter (fun value => value ≤ n)).insertIdx site (n + 1) = q := by
      rw [← erase_filter, erase_index, ← hsitevalue]
      exact List.insertIdx_eraseIdx_getElem hsite
    have hparentperm : (q.filter (fun value => value ≤ n)).Perm (List.range' 1 n) := by
      rw [← erase_filter]
      have hnot : n + 1 ∉ List.range' 1 n := by
        intro hmem
        obtain ⟨index, hindex, heq⟩ := List.mem_range'.mp hmem
        omega
      have hpermerase := hperm.erase (n + 1)
      rw [List.range'_concat] at hpermerase
      simp only [Nat.one_mul] at hpermerase
      rw [List.erase_append_right _ hnot] at hpermerase
      simpa [Nat.add_comm] using hpermerase
    have hparentlength : (q.filter (fun value => value ≤ n)).length = n := by
      simpa using hparentperm.length_eq
    have hparentmax : ∀ value ∈ q.filter (fun value => value ≤ n), value < n + 1 := by
      intro value hvalue
      have hle := (List.mem_filter.mp hvalue).2
      simp only [decide_eq_true_eq] at hle
      omega
    have hparentavoid : ¬ ContainsV2413 (q.filter (fun value => value ≤ n)) := by
      apply delete_maximum_avoids _ site (n + 1) (by omega) hparentmax
      rw [reconstruct]
      exact hq.2
    exact ⟨site, by omega, ⟨hparentperm, hparentavoid⟩, reconstruct.symm⟩
  
  have full_filter (p : List ℕ) (n : ℕ) (hperm : p.Perm (List.range' 1 n)) :
      p.filter (fun value => value ≤ n) = p := by
    apply List.filter_eq_self.mpr
    intro value hvalue
    obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
    simp only [decide_eq_true_eq]
    omega
  have nested_filter (q : List ℕ) (smaller larger : ℕ) (hbound : smaller ≤ larger) :
      (q.filter (fun value => value ≤ larger)).filter (fun value => value ≤ smaller) =
        q.filter (fun value => value ≤ smaller) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro value _
    by_cases hvalue : value ≤ smaller
    · have hvalue' : value ≤ larger := by omega
      simp [hvalue, hvalue']
    · simp [hvalue]
  have filter_insert (values : List ℕ) (site letter : ℕ) (pred : ℕ → Bool)
      (hletter : pred letter = false) :
      (values.insertIdx site letter).filter pred = values.filter pred := by
    induction site generalizing values with
    | zero => simp [hletter]
    | succ site ih =>
      cases values with
      | nil => simp
      | cons first rest => rw [List.insertIdx_succ_cons]; simp only [List.filter_cons, ih]
  have finite_permutations (n : ℕ) : (permAvoiders n).Finite := by
    apply (List.range' 1 n).permutations.toFinset.finite_toSet.subset
    intro p hp
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr hp.1)
  have finite_extensions (base : List ℕ) (depth : ℕ) : (permExtensions base depth).Finite :=
    (finite_permutations (base.length + depth)).subset fun _ hmember => hmember.1
  let (base : List ℕ) (depth : ℕ) : Fintype (permExtensions base depth) :=
    (finite_extensions base depth).fintype
  have permutation_count (depth : ℕ) (p : List ℕ) (hempty : p ≠ [])
      (hperm : p.Perm (List.range' 1 p.length)) (havoid : ¬ ContainsV2413 p) :
      (permExtensions p depth).ncard = treeCount depth (permLabel p).1 (permLabel p).2 := by
    induction depth generalizing p with
    | zero =>
      have hsingleton : permExtensions p 0 = {p} := by
        ext q
        constructor
        · rintro ⟨hq, hparent⟩
          rw [full_filter q p.length (by simpa using hq.1)] at hparent
          exact hparent
        · intro hq
          have heq : q = p := hq
          subst q
          exact ⟨⟨by simpa using hperm, havoid⟩, full_filter p p.length hperm⟩
      rw [hsingleton, Set.ncard_singleton]
      rfl
    | succ depth ih =>
      let Children := {q : List ℕ // ∃ site, site ∈ activeSites p ∧
        q = p.insertIdx site (p.length + 1)}
      obtain ⟨hheight, hslack, correspondence, hlabels⟩ :=
        permutation_children_rule p hempty hperm havoid
      let : Finite Children := Finite.of_injective correspondence correspondence.injective
      let : Fintype Children := Fintype.ofFinite Children
      have child_valid (child : Children) : child.val ∈ permAvoiders (p.length + 1) := by
        obtain ⟨site, hsite, heq⟩ := child.property
        rw [heq]
        have hsitebound : site ≤ p.length := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp hsite).1
          omega
        refine ⟨?_, (Finset.mem_filter.mp hsite).2⟩
        rw [List.range'_concat]
        simp only [Nat.one_mul, Nat.add_comm 1]
        exact ((List.perm_insertIdx (p.length + 1) p hsitebound).trans
          (hperm.cons (p.length + 1))).trans (by
            simpa only [List.singleton_append] using
              (List.perm_append_comm : ([p.length + 1] ++ List.range' 1 p.length).Perm
                (List.range' 1 p.length ++ [p.length + 1])))
      have child_length (child : Children) : child.val.length = p.length + 1 := by
        simpa using (child_valid child).1.length_eq
      have child_parent (child : Children) :
          child.val.filter (fun value => value ≤ p.length) = p := by
        obtain ⟨site, hsite, heq⟩ := child.property
        rw [heq, filter_insert p site (p.length + 1) (fun value => decide (value ≤ p.length))
          (by simp), full_filter p p.length hperm]
      have first_valid (q : permExtensions p (depth + 1)) :
          q.val.filter (fun value => value ≤ p.length + 1) ∈ permAvoiders (p.length + 1) :=
        restriction_avoids (p.length + (depth + 1)) q.val q.property.1 _ (by omega)
      have first_parent (q : permExtensions p (depth + 1)) :
          (q.val.filter (fun value => value ≤ p.length + 1)).filter
            (fun value => value ≤ p.length) = p := by
        rw [nested_filter q.val p.length (p.length + 1) (by omega)]
        exact q.property.2
      have first_member (q : permExtensions p (depth + 1)) :
          ∃ site, site ∈ activeSites p ∧
            q.val.filter (fun value => value ≤ p.length + 1) =
              p.insertIdx site (p.length + 1) := by
        obtain ⟨site, hsite, hparent, hrecover⟩ := maximum_parent p.length _ (first_valid q)
        rw [first_parent q] at hrecover
        refine ⟨site, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, hrecover⟩
        rw [← hrecover]
        exact (first_valid q).2
      let firstChild (q : permExtensions p (depth + 1)) : Children :=
        ⟨q.val.filter (fun value => value ≤ p.length + 1), first_member q⟩
      let splitExtension : permExtensions p (depth + 1) →
          Σ child : Children, permExtensions child.val depth := fun q =>
        ⟨firstChild q, ⟨q.val, ⟨by
          refine ⟨?_, q.property.1.2⟩
          have hperm_length := child_length (firstChild q)
          rw [hperm_length]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using q.property.1.1,
        by rw [child_length (firstChild q)]⟩⟩⟩
      let joinExtension : (Σ child : Children, permExtensions child.val depth) →
          permExtensions p (depth + 1) := fun extension =>
        ⟨extension.2.val, ⟨by
          refine ⟨?_, extension.2.property.1.2⟩
          have hperm_length := extension.2.property.1.1
          rw [child_length extension.1] at hperm_length
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperm_length,
        by
          have hparent := congrArg (fun values : List ℕ =>
            values.filter (fun value => value ≤ p.length)) extension.2.property.2
          rw [child_length extension.1, nested_filter _ _ _ (by omega),
            child_parent extension.1] at hparent
          exact hparent⟩⟩
      let splitEquiv : permExtensions p (depth + 1) ≃
          (Σ child : Children, permExtensions child.val depth) :=
        ⟨splitExtension, joinExtension, by
          intro q
          apply Subtype.ext
          rfl,
        by
          intro extension
          have hchild : (splitExtension (joinExtension extension)).1 = extension.1 := by
            apply Subtype.ext
            change extension.2.val.filter (fun value => value ≤ p.length + 1) = extension.1.val
            have hfilter := extension.2.property.2
            rwa [child_length extension.1] at hfilter
          apply Sigma.ext hchild
          have hpredicate := congrArg (fun child : Children => fun q : List ℕ =>
            q ∈ permExtensions child.val depth) hchild
          exact (Subtype.heq_iff_coe_heq rfl (heq_of_eq hpredicate)).mpr HEq.rfl⟩
      rw [← Nat.card_coe_set_eq, Nat.card_congr splitEquiv, Nat.card_sigma]
      simp only [Nat.card_coe_set_eq]
      calc
        (∑ child : Children, (permExtensions child.val depth).ncard) =
            ∑ child : Children, treeCount depth (permLabel child.val).1
              (permLabel child.val).2 := by
          apply Finset.sum_congr rfl
          intro child _
          have hvalid := child_valid child
          apply ih child.val
          · have hlength := child_length child
            intro hemptychild
            simp [hemptychild] at hlength
          · simpa only [child_length child] using hvalid.1
          · exact hvalid.2
        _ = ∑ index : Fin (permLabel p).1 ⊕ Fin (permLabel p).2,
            treeCount depth (childLabel (permLabel p).1 (permLabel p).2 index).1
              (childLabel (permLabel p).1 (permLabel p).2 index).2 := by
          apply Fintype.sum_equiv correspondence
          intro child
          rw [hlabels child]
        _ = treeCount (depth + 1) (permLabel p).1 (permLabel p).2 := rfl
  have short_avoid (q : List ℕ) (hlength : q.length ≤ 3) : ¬ ContainsV2413 q := by
    rintro ⟨earlier, top, later, hearlier, hlater, hlast, _⟩
    omega
  have weak_root : IsWeakAscent [0] ∧ ¬ Contains210 [0] := by
    constructor
    · intro index hindex
      have heq : index = 0 := by simpa using hindex
      subst index
      simp
    · rintro ⟨top, bottom, last, htop, hbottom, hlast, _⟩
      simp only [List.length_singleton] at hlast
      omega
  have perm_root : [1] ∈ permAvoiders 1 :=
    ⟨by simp, short_avoid [1] (by simp)⟩
  have weak_root_label : weakLabel [0] = (1, 1) := by
    simp [weakLabel, inversionBottom, wasc]
  have active_root : activeSites [1] = {0, 1} := by
    ext site
    constructor
    · intro hsite
      have hbound := Finset.mem_range.mp (Finset.mem_filter.mp hsite).1
      simp only [List.length_singleton] at hbound
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · intro hsite
      have hbound : site ≤ 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hsite
        omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by simpa using (show site < 2 by omega)), ?_⟩
      apply short_avoid
      simp [List.length_insertIdx, hbound]
  have record_root : recordSites [1] = {0} := by simp [recordSites]
  have perm_root_label : permLabel [1] = (1, 1) := by
    simp [permLabel, active_root, record_root, Finset.filter_insert, Finset.filter_singleton]
  intro n
  cases n with
  | zero =>
    have hweakzero : weakAvoiders 0 = {[]} := by
      ext e
      constructor
      · intro he
        exact List.length_eq_zero_iff.mp he.1
      · intro he
        have heq : e = [] := he
        subst e
        simp [weakAvoiders, IsWeakAscent, Contains210]
    have hpermzero : permAvoiders 0 = {[]} := by
      ext p
      constructor
      · intro hp
        have hlength : p.length = 0 := by simpa using hp.1.length_eq
        exact List.length_eq_zero_iff.mp hlength
      · intro hp
        have heq : p = [] := hp
        subst p
        simp [permAvoiders, ContainsV2413]
    rw [hweakzero, hpermzero]
  | succ n =>
    have hweakroot : weakAvoiders (n + 1) = weakExtensions [0] n := by
      ext e
      constructor
      · intro he
        refine ⟨?_, ?_⟩
        · simpa [Nat.add_comm] using he
        · cases e with
          | nil => have hlength := he.1; simp at hlength
          | cons first rest =>
            have hfirst := he.2.1 0 (by simp)
            have hfirstzero : first ≤ 0 := by simpa using hfirst
            have hzero : first = 0 := by omega
            simp [hzero]
      · rintro ⟨he, _⟩
        simpa [Nat.add_comm] using he
    have hpermroot : permAvoiders (n + 1) = permExtensions [1] n := by
      ext p
      constructor
      · intro hp
        refine ⟨?_, ?_⟩
        · simpa [Nat.add_comm] using hp
        · have hrestrict := restriction_avoids (n + 1) p hp 1 (by omega)
          simpa using hrestrict.1
      · rintro ⟨hp, _⟩
        simpa [Nat.add_comm] using hp
    rw [hweakroot, hpermroot,
      weak_extensions_count n [0] (by simp) weak_root.1 weak_root.2,
      permutation_count n [1] (by simp) (by simp) perm_root.2,
      weak_root_label, perm_root_label]

end D5.S3.Combinatorics.WeakAscent.WeakAscentSemiBaxter
