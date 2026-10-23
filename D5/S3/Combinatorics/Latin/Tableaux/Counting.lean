/- GID: D5/S3/Combinatorics/Latin/Tableaux/Counting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/Tableaux/Counting
   mirror-E: none(waiver:exact-source-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63; premises=D5/S3/Combinatorics/Latin/Tableaux/Counting.base_count_and_invariant
   digest: Exact source tableaux enumeration and the universal fourfold recurrence. -/

import D5.S3.Combinatorics.Latin.Tableaux.MatchingTemplate
import D5.S3.Combinatorics.Latin.Tableaux.Source

/-! Counting for literal Latin tableaux and their availability graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace D5.S3.Combinatorics.Latin.Tableaux.Counting

open MatchingTemplate Source

/-- Literal column disjointness, including columns absent from a shorter row. -/
def ColumnDisjoint (r s : List ℕ) : Prop :=
  ∀ (j x : ℕ), r[j]? = some x → s[j]? ≠ some x

/-- Row permutations with all rows and columns in their fixed order. -/
def RawLatin (lam : List ℕ) (T : List (List ℕ)) : Prop :=
  List.Forall₂ (fun m r => r.Perm (List.range m)) lam T ∧ T.Pairwise ColumnDisjoint

/-- The availability graph for the next row of length m. -/
def available (m : ℕ) (T : List (List ℕ)) : List (Finset ℕ) :=
  (List.range m).map (fun j => (Finset.range m).filter
    (fun x => ∀ r ∈ T, r[j]? ≠ some x))

/-- Full, unreduced row-by-row enumeration. -/
def enumerate : List ℕ → Finset (List (List ℕ))
  | [] => {[]}
  | m :: lam => (enumerate lam).biUnion fun T =>
      (matchings (available m T)).image (· :: T)

private theorem matching_available (m : ℕ) (T : List (List ℕ)) (r : List ℕ) :
    r ∈ matchings (available m T) ↔
      r.Perm (List.range m) ∧ ∀ s ∈ T, ColumnDisjoint r s := by
  rw [mem_matchings]
  have hrel : List.Forall₂ (fun x g => x ∈ g) r (available m T) ↔
      r.length = m ∧ ∀ (j : ℕ) (hj : j < r.length),
        r[j] < m ∧ ∀ s ∈ T, s[j]? ≠ some r[j] := by
    simp only [available, List.forall₂_iff_get, List.length_map, List.getElem_map,
      List.length_range, List.get_eq_getElem, List.getElem_range, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hlen,h⟩
      exact ⟨hlen,fun j hj => h j hj (by omega)⟩
    · rintro ⟨hlen,h⟩
      exact ⟨hlen,fun j hj _ => h j hj⟩
  rw [hrel]
  constructor
  · rintro ⟨⟨hlen,hcol⟩,hnd⟩
    have hsub : r.toFinset ⊆ Finset.range m := by
      intro x hx
      obtain ⟨j,hj,hx⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hx)
      subst x
      exact Finset.mem_range.mpr (hcol j hj).1
    have heq : r.toFinset = Finset.range m := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp [List.toFinset_card_of_nodup hnd,hlen]
    refine ⟨(List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr ?_, ?_⟩
    · intro x
      have he := Finset.ext_iff.mp heq x
      simpa using he
    · intro s hs j x hj
      obtain ⟨hjr,hx⟩ := List.getElem?_eq_some_iff.mp hj
      subst x
      exact (hcol j hjr).2 s hs
  · rintro ⟨hp,hc⟩
    have hlen := hp.length_eq
    simp only [List.length_range] at hlen
    refine ⟨⟨hlen,?_⟩, hp.nodup_iff.mpr List.nodup_range⟩
    intro j hj
    refine ⟨?_,fun s hs => hc s hs j r[j] (by simp [hj])⟩
    exact List.mem_range.mp (hp.mem_iff.mp (List.getElem_mem hj))

/-- The finite enumeration contains exactly the literal compatible row permutations. -/
theorem mem_enumerate (lam : List ℕ) (T : List (List ℕ)) :
    T ∈ enumerate lam ↔ RawLatin lam T := by
  induction lam generalizing T with
  | nil => cases T <;> simp [enumerate,RawLatin]
  | cons m lam ih =>
      cases T with
      | nil => simp [enumerate,RawLatin]
      | cons r T =>
          simp only [enumerate, Finset.mem_biUnion, Finset.mem_image, List.cons.injEq]
          simp only [RawLatin, List.forall₂_cons, List.pairwise_cons]
          constructor
          · rintro ⟨S,hS,p,hp,he,hST⟩
            subst S
            subst p
            have hs := ih T |>.mp hS
            have hr := (matching_available m T r).mp hp
            exact ⟨⟨hr.1,hs.1⟩,hr.2,hs.2⟩
          · rintro ⟨⟨hr,hs⟩,hc,hp⟩
            exact ⟨T,(ih T).mpr ⟨hs,hp⟩,r,(matching_available m T r).mpr ⟨hr,hc⟩,rfl,rfl⟩

/-- The literal zero-based rows of a bounded source filling. -/
def rowsOf {lam : List ℕ} (T : FiniteLatin lam) : List (List ℕ) :=
  List.ofFn (fun i : Fin lam.length => List.ofFn (fun j : Fin lam[i] => (T.1 i j).val))

private theorem rowsOf_valid {lam : List ℕ} (T : FiniteLatin lam) : RawLatin lam (rowsOf T) := by
  refine ⟨?_, ?_⟩
  · rw [List.forall₂_iff_get]
    refine ⟨by simp [rowsOf], ?_⟩
    intro i hi hj
    simp only [rowsOf, List.get_eq_getElem, List.getElem_ofFn]
    have hnd : (List.ofFn (fun j : Fin lam[i] => (T.1 ⟨i,hi⟩ j).val)).Nodup := by
      rw [List.nodup_ofFn]
      intro j j' he
      exact T.2.1 _ (Fin.ext he)
    apply (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr
    intro x
    simp only [List.mem_ofFn, List.mem_range]
    constructor
    · rintro ⟨j,rfl⟩
      exact (T.1 ⟨i,hi⟩ j).isLt
    · intro hx
      obtain ⟨j,hj⟩ := (Finite.injective_iff_bijective.mp (T.2.1 ⟨i,hi⟩)).2 ⟨x,hx⟩
      exact ⟨j,congrArg Fin.val hj⟩
  · rw [rowsOf, List.pairwise_ofFn]
    intro i i' hii j x h1 h2
    obtain ⟨hj,hjval⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hj',hjval'⟩ := List.getElem?_eq_some_iff.mp h2
    simp only [List.length_ofFn] at hj hj'
    have he := T.2.2 i i' ⟨j,hj⟩ ⟨j,hj'⟩ rfl (by
      simpa only [List.getElem_ofFn] using hjval.trans hjval'.symm)
    exact (ne_of_lt hii) he

private theorem rowsOf_injective (lam : List ℕ) :
    Function.Injective (@rowsOf lam) := by
  intro T U he
  apply Subtype.ext
  funext i j
  apply Fin.ext
  have hr := congrArg (fun R => R[i.val]?.bind (fun r => r[j.val]?)) he
  simpa [rowsOf] using hr

private def ofRows {lam : List ℕ} (R : List (List ℕ)) (hR : RawLatin lam R) :
    FiniteLatin lam := by
  have hlen := hR.1.length_eq
  have row (i : Fin lam.length) : (R[i.val]'(by omega)).Perm (List.range lam[i]) := by
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hR.1.get i.isLt (by omega)
  have rowlen (i : Fin lam.length) : (R[i.val]'(by omega)).length = lam[i] := by
    simpa only [List.length_range] using (row i).length_eq
  let f : (i : Fin lam.length) → Fin lam[i] → Fin lam[i] := fun i j =>
    ⟨(R[i.val]'(by omega))[j.val]'(by rw [rowlen]; exact j.isLt), by
      exact List.mem_range.mp ((row i).mem_iff.mp (List.getElem_mem (by rw [rowlen]; exact j.isLt)))⟩
  refine ⟨f,?_,?_⟩
  · intro i j j' he
    apply Fin.ext
    have hnd := (row i).nodup_iff.mpr List.nodup_range
    have hinj := List.nodup_iff_injective_get.mp hnd
    have hv := congrArg Fin.val he
    have hjj := hinj (show (R[i.val]'(by omega)).get ⟨j.val,by rw [rowlen]; exact j.isLt⟩ =
        (R[i.val]'(by omega)).get ⟨j'.val,by rw [rowlen]; exact j'.isLt⟩ from hv)
    exact congrArg (fun t : Fin (R[i.val]'(by omega)).length => t.val) hjj
  · intro i i' j j' he hs
    by_contra hn
    have disj (a b : Fin lam.length) (hab : a < b) :
        ColumnDisjoint (R[a.val]'(by omega)) (R[b.val]'(by omega)) := by
      exact (List.pairwise_iff_get.mp hR.2) ⟨a.val,by omega⟩ ⟨b.val,by omega⟩ hab
    have hj1 : (R[i.val]'(by omega))[j.val]? = some (f i j).val := by
      exact List.getElem?_eq_some_iff.mpr ⟨by rw [rowlen]; exact j.isLt, rfl⟩
    have hj2 : (R[i'.val]'(by omega))[j'.val]? = some (f i' j').val := by
      exact List.getElem?_eq_some_iff.mpr ⟨by rw [rowlen]; exact j'.isLt, rfl⟩
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact disj i i' hlt j.val (f i j).val hj1 (by simpa [he,hs] using hj2)
    · exact disj i' i hlt j'.val (f i' j').val hj2 (by simpa [he,hs] using hj1)

private theorem ofRows_inverse {lam : List ℕ} (R : List (List ℕ)) (hR : RawLatin lam R) :
    rowsOf (ofRows R hR) = R := by
  apply List.ext_getElem
  · simp only [rowsOf, List.length_ofFn]
    exact hR.1.length_eq
  · intro i hi hj
    simp only [rowsOf, List.getElem_ofFn]
    apply List.ext_getElem
    · simpa only [List.length_ofFn, List.get_eq_getElem, List.length_range, Fin.getElem_fin] using
        ((hR.1.get (by simpa [rowsOf] using hi) hj).length_eq.symm)
    · intro j hj hj'
      simp [ofRows]

/-- Reversible finite enumeration of every full source tableau. -/
noncomputable def enumerationEquiv (lam : List ℕ) :
    {T : Filling lam // SourceLatin lam T} ≃ {R // R ∈ enumerate lam} :=
  (sourceEquiv lam).trans (Equiv.ofBijective
    (fun T => (⟨rowsOf T, (mem_enumerate lam _).mpr (rowsOf_valid T)⟩ : {R // R ∈ enumerate lam}))
    ⟨fun T U he => rowsOf_injective lam (congrArg Subtype.val he), by
      rintro ⟨R,hR⟩
      exact ⟨ofRows R ((mem_enumerate lam R).mp hR),
        Subtype.ext (ofRows_inverse R ((mem_enumerate lam R).mp hR))⟩⟩)

/-- The algorithm's finite cardinality is exactly the source's literal full count. -/
theorem source_enumeration (k : ℕ) : Source.LT k = (enumerate (shape k)).card := by
  haveI := source_finite (shape k)
  letI := Fintype.ofFinite {T : Filling (shape k) // SourceLatin (shape k) T}
  rw [Source.LT,Nat.card_eq_fintype_card,Fintype.card_congr (enumerationEquiv (shape k))]
  exact Fintype.card_coe _


private theorem raw_bounds {lam : List ℕ} {T : List (List ℕ)} (h : RawLatin lam T)
    (m : ℕ) (hm : ∀ l ∈ lam, l ≤ m) :
    ∀ r ∈ T, r.length ≤ m ∧ ∀ x ∈ r, x < m := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < lam.length := by have := h.1.length_eq; omega
  have hp := h.1.get hi' hi
  simp only [List.get_eq_getElem] at hp
  have hl := hp.length_eq
  simp only [List.length_range] at hl
  have hb := hm lam[i] (List.getElem_mem hi')
  refine ⟨by omega, ?_⟩
  intro x hx
  have := List.mem_range.mp (hp.mem_iff.mp hx)
  omega

private theorem available_update (m : ℕ) (T : List (List ℕ)) (r : List ℕ)
    (hb : ∀ s ∈ T, s.length ≤ m ∧ ∀ x ∈ s, x < m)
    (hr : r ∈ matchings (available m T)) :
    available (m+1) (r::T) = border (available m T) (Finset.range m) r m := by
  have hp := (matching_available m T r).mp hr
  have hlen : r.length = m := by simpa using hp.1.length_eq
  have hrb (j : ℕ) (hj : j < r.length) : r[j] < m :=
    List.mem_range.mp (hp.1.mem_iff.mp (List.getElem_mem hj))
  have hnone : ∀ s ∈ T, s[m]? = none := by
    intro s hs
    exact List.getElem?_eq_none_iff.mpr (hb s hs).1
  have hfresh : ∀ s ∈ T, ∀ (j : ℕ), s[j]? ≠ some m := by
    intro s hs j he
    have hx := List.mem_of_getElem? he
    have := (hb s hs).2 m hx
    omega
  simp only [border]
  apply List.ext_getElem
  · simp [available,hlen]
  · intro j hj hj'
    have hjb : j < m+1 := by simpa [available] using hj
    by_cases h : j < m
    · rw [List.getElem_append_left (by simp [List.length_zipWith,available,hlen]; omega)]
      simp only [List.getElem_zipWith,available,List.getElem_map,List.getElem_range]
      ext x
      simp only [Finset.mem_filter,Finset.mem_range,List.mem_cons,forall_eq_or_imp,
        Finset.mem_insert,Finset.mem_erase]
      have hjr : r[j]? = some r[j] := List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
      constructor
      · rintro ⟨hx,hxr,hxs⟩
        by_cases hxm : x = m
        · exact Or.inl hxm
        · exact Or.inr ⟨by intro he; subst x; exact hxr hjr,by omega,hxs⟩
      · rintro (rfl | ⟨hne,hx,hxs⟩)
        · refine ⟨by omega, ?_,fun s hs => hfresh s hs j⟩
          intro he
          have hv := Option.some.inj (hjr.symm.trans he)
          have := hrb j (by omega)
          omega
        · refine ⟨by omega, ?_,hxs⟩
          intro he
          exact hne (Option.some.inj (hjr.symm.trans he)).symm
    · have he : j = m := by omega
      subst j
      rw [List.getElem_append_right (by simp [List.length_zipWith,available,hlen])]
      simp only [List.length_zipWith,available,List.length_map,List.length_range,hlen,
        min_self,Nat.sub_self,List.getElem_cons_zero,List.getElem_map,List.getElem_range]
      ext x
      have hn : ∀ a ∈ T, a[m]? ≠ some x := by
        intro a ha
        rw [hnone a ha]
        simp
      simp [Finset.mem_range, List.getElem?_eq_none_iff.mpr (by omega : r.length ≤ m), hn,
        Finset.mem_insert]
      constructor
      · rintro ⟨hx,_⟩
        omega
      · intro hx
        exact ⟨by omega,hn⟩

/-- The source shapes grow by adding their actual new longest row. -/
theorem shape_succ (k : ℕ) (hk : 5 ≤ k) : shape (k+1) = (k+1)::shape k := by
  have he : k+1-3 = (k-3)+1 := by omega
  simp [shape,he,List.range_succ,List.map_append,List.reverse_append]
  omega

private def BaseCertificate (T : List (List ℕ)) : Prop :=
  ∃ (e x y z : Fin 3), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ({x.val,y.val,z.val} : Finset ℕ) = Finset.range 3 ∧
    available 6 T = headGraph e 3 4 5 ++
      ([{x.val},{y.val,z.val},{x.val,y.val,z.val}] : List (Finset ℕ)).map
        (fun g => ({3,4,5} : Finset ℕ) ∪ g)

private instance (T : List (List ℕ)) : Decidable (BaseCertificate T) := by
  unfold BaseCertificate
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The complete base certificate is reduced by the kernel, without a native decision axiom.
private theorem checked_base : (enumerate (shape 5)).card = 144 ∧
    ∀ T ∈ enumerate (shape 5), BaseCertificate T := by
  decide +kernel

/-- The complete source base has 144 tableaux and every one has the transition invariant. -/
theorem base_count_and_invariant : (enumerate (shape 5)).card = 144 ∧
    ∀ T ∈ enumerate (shape 5), Full (available 6 T) (Finset.range 3) 3 4 5 := by
  refine ⟨checked_base.1, ?_⟩
  intro T hT
  obtain ⟨e,x,y,z,hxy,hxz,hyz,hB,hG⟩ := checked_base.2 T hT
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,e,_,?_,hG⟩
  rw [←hB]
  exact Tail.base x.val y.val z.val (fun he => hxy (Fin.ext he)) (fun he => hxz (Fin.ext he)) (fun he => hyz (Fin.ext he))


private theorem shape_bound (k : ℕ) (hk : 5 ≤ k) : ∀ l ∈ shape k, l ≤ k := by
  intro l hl
  simp only [shape,List.mem_append,List.mem_reverse,List.mem_map,List.mem_cons,
    List.not_mem_nil,or_false,or_self] at hl
  rcases hl with ⟨j,hj,rfl⟩ | rfl
  · simp only [List.mem_range] at hj
    omega
  · omega

/-- The availability invariant holds for every full tableau and every source parameter. -/
theorem universal_invariant (k : ℕ) (hk : 5 ≤ k) :
    ∀ T ∈ enumerate (shape k),
      Full (available (k+1) T) (Finset.range (k-2)) (k-2) (k-1) k := by
  induction k, hk using Nat.le_induction with
  | base => exact base_count_and_invariant.2
  | succ k hk ih =>
      intro R hR
      rw [shape_succ k hk,enumerate] at hR
      obtain ⟨T,hT,hR⟩ := Finset.mem_biUnion.mp hR
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hR
      have hb := raw_bounds ((mem_enumerate _ _).mp hT) (k+1)
        (fun l hl => (shape_bound k hk l hl).trans (by omega))
      rw [available_update (k+1) T r hb hr]
      have he : ({k-2,k-1,k} : Finset ℕ) ∪ Finset.range (k-2) = Finset.range (k+1) := by
        ext x
        simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_range]
        omega
      have hu : k+1 ∉ ({k-2,k-1,k} : Finset ℕ) ∪ Finset.range (k-2) := by
        rw [he]
        simp
      have ht := full_transition (ih T hT) r hr (k+1) hu
      rw [he] at ht
      have hb' : insert (k-2) (Finset.range (k-2)) = Finset.range (k+1-2) := by
        ext x
        simp only [Finset.mem_insert,Finset.mem_range]
        omega
      simpa only [hb',show k+1-2=k-1 by omega,show k+1-1=k by omega] using ht

/-- Each full source tableau has exactly four next rows, in the literal enumeration. -/
theorem count_step (k : ℕ) (hk : 5 ≤ k) :
    (enumerate (shape (k+1))).card = (enumerate (shape k)).card * 4 := by
  rw [shape_succ k hk]
  change ((enumerate (shape k)).biUnion fun T =>
    (matchings (available (k+1) T)).image (· :: T)).card = _
  rw [Finset.card_biUnion]
  · apply Finset.sum_const_nat
    intro T hT
    rw [Finset.card_image_of_injective _ (fun r s he => (List.cons.inj he).1)]
    exact full_matchings (universal_invariant k hk T hT)
  · intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro R hR hR'
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hR
    obtain ⟨s,hs,he'⟩ := Finset.mem_image.mp hR'
    exact hne (List.cons.inj (he.trans he'.symm)).2

/-- Conjecture 6.3, with no parameter cutoff, recurrence hypothesis, or quotient. -/
theorem conjecture63 (k : ℕ) (hk : 5 ≤ k) : Source.LT k = 9 * 4^(k-3) := by
  rw [source_enumeration]
  induction k, hk using Nat.le_induction with
  | base => exact base_count_and_invariant.1
  | succ k hk ih =>
      rw [count_step k hk,ih,show k+1-3=(k-3)+1 by omega,pow_succ]
      omega

/-- The entire source claim quantified over all integers at least five. -/
theorem conjecture63_integer (k : ℤ) (hk : 5 ≤ k) :
    Source.LT k.toNat = 9 * 4^(k.toNat-3) := by
  apply conjecture63
  omega

end D5.S3.Combinatorics.Latin.Tableaux.Counting
