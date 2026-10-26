/- GID: D5/S3/Combinatorics/Graph/Walks/SemicompleteHamilton
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/SemicompleteHamilton
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite strongly connected semicomplete directed relations have simple spanning cycles through any specified vertex. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation

/-! Simple spanning directed cycles in finite semicomplete relations. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton

private theorem chain_forward {V : Type*} {P Q : V → Prop} {a : V} {l : List V}
    (h : List.IsChain (fun u v => P u → P v ∧ Q v) (a :: l)) (ha : P a) :
    (∀ v ∈ a :: l, P v) ∧ (∀ v ∈ l, Q v) := by
  induction l generalizing a with
  | nil =>
    constructor
    · intro v hv
      have he : v = a := by simpa using hv
      exact he.symm ▸ ha
    · simp
  | cons b l ih =>
    have hab := h.rel ha
    obtain ⟨hP,hQ⟩ := ih h.tail hab.1
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact hP v hv
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hab.2
      · exact hQ v hv

/-- Genuine generic cyclic insertion, with reciprocal arcs and two-cycles
allowed. When the original cyclic word is a simple directed cycle and x is
outside it, the displayed split gives its strictly longer insertion cycle.
The displayed split is used by outside_uniform_of_no_insertion
and the longest-cycle argument. -/
theorem cyclic_insertion {V : Type*} {D : V → V → Prop} {c x : V} {l : List V}
    (hsemi : ∀ v ∈ c :: l, D v x ∨ D x v)
    (hin : ∃ v ∈ c :: l, D v x)
    (hout : ∃ v ∈ c :: l, D x v) :
    ∃ (p : List V) (u v : V) (s : List V),
      (c :: l) ++ [c] = p ++ u :: v :: s ∧ D u x ∧ D x v := by
  by_contra hn
  let H := fun u v => D u x → D v x ∧ ¬D x v
  have hchain : List.IsChain H ((c :: l) ++ [c]) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u v p s he hux
    have hv' : v ∈ (c :: l) ++ [c] := by rw [he]; simp
    have hv : v ∈ c :: l := by
      rcases List.mem_append.mp hv' with hv | hv
      · exact hv
      · have heq : v = c := by simpa using hv
        simp [heq]
    have hnv : ¬D x v := fun hxv => hn ⟨p,u,v,s,he,hux,hxv⟩
    exact ⟨(hsemi v hv).resolve_right hnv,hnv⟩
  obtain ⟨v,hv,hvx⟩ := hin
  obtain ⟨p,s,he⟩ := List.mem_iff_append.mp hv
  have hsuffix : List.IsChain H (v :: (s ++ [c])) := by
    have hchain' : List.IsChain H (p ++ (v :: (s ++ [c]))) := by
      simpa only [he,List.append_assoc,List.cons_append] using hchain
    exact hchain'.right_of_append
  have hcx : D c x := (chain_forward hsuffix hvx).1 c (by simp)
  have hclosed : List.IsChain H (c :: (l ++ [c])) := by simpa using hchain
  have hall := (chain_forward hclosed hcx).2
  obtain ⟨w,hw,hxw⟩ := hout
  have hw' : w ∈ l ++ [c] := by
    rcases List.mem_cons.mp hw with rfl | hw
    · simp
    · simp [hw]
  exact hall w hw' hxw

/-- The uniform-outside-vertex inference used after longest-cycle maximality.
It consumes cyclic_insertion and retains both absent reverse-arc conditions. -/
theorem outside_uniform_of_no_insertion {V : Type*} {D : V → V → Prop}
    {c x : V} {l : List V}
    (hsemi : ∀ v ∈ c :: l, D v x ∨ D x v)
    (hno : ¬∃ (p : List V) (u v : V) (s : List V),
      (c :: l) ++ [c] = p ++ u :: v :: s ∧ D u x ∧ D x v) :
    (∀ v ∈ c :: l, D v x ∧ ¬D x v) ∨
      (∀ v ∈ c :: l, D x v ∧ ¬D v x) := by
  by_cases hin : ∃ v ∈ c :: l, D v x
  · left
    have hout : ¬∃ v ∈ c :: l, D x v :=
      fun h => hno (cyclic_insertion hsemi hin h)
    intro v hv
    have hnv : ¬D x v := fun h => hout ⟨v,hv,h⟩
    exact ⟨(hsemi v hv).resolve_right hnv,hnv⟩
  · right
    intro v hv
    have hnv : ¬D v x := fun h => hin ⟨v,hv,h⟩
    exact ⟨(hsemi v hv).resolve_left hnv,hnv⟩


/-- Loop erasure along an actual ReflTransGen derivation. The resulting list
keeps both endpoints and all actual directed edges; no transitivity of D is
assumed. This is used to obtain the initial simple directed cycle. -/
private theorem simple_chain_of_reachable {V : Type*} {D : V → V → Prop}
    {a b : V} (h : Relation.ReflTransGen D a b) :
    ∃ w : List V, w.Nodup ∧ List.IsChain D w ∧
      w.head? = some a ∧ w.getLast? = some b := by
  classical
  induction h with
  | refl => exact ⟨[a], by simp, .singleton a, rfl, rfl⟩
  | @tail b c hab hbc ih =>
    obtain ⟨w,hn,hc,hh,hl⟩ := ih
    by_cases hcw : c ∈ w
    · obtain ⟨p,s,he⟩ := List.mem_iff_append.mp hcw
      have hsplit : List.IsChain D (p ++ c :: s) := he ▸ hc
      have hprefix : List.IsChain D (p ++ [c]) :=
        (List.isChain_split.mp hsplit).1
      have hnodup : (p ++ [c]).Nodup := by
        have hn' : (p ++ c :: s).Nodup := he ▸ hn
        have hpre : p ++ [c] <+: p ++ c :: s :=
          ⟨s, by simp [List.append_assoc]⟩
        exact hpre.sublist.nodup hn'
      refine ⟨p ++ [c],hnodup,hprefix,?_,by simp⟩
      cases p with
      | nil => simpa [he] using hh
      | cons d p => simpa [he] using hh
    · have hnodup : (w ++ [c]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hn,by simp,?_⟩
        intro x hx y hy hxy
        have hyc : y = c := by simpa using hy
        subst y
        subst x
        exact hcw hx
      have hchain : List.IsChain D (w ++ [c]) :=
        hc.append (.singleton c) (by
          intro x hx y hy
          have hxb : x = b := by simpa [hl, eq_comm] using hx
          have hyc : y = c := by simpa [eq_comm] using hy
          simpa [hxb,hyc] using hbc)
      refine ⟨w ++ [c],hnodup,hchain,?_,by simp⟩
      simp [List.head?_append,hh]

/-- Replace a displayed edge by a directed path, retaining the two endpoints
of the whole chain. The permutation records every inserted vertex exactly.
Both one-vertex insertion and the receiving-to-sending two-vertex splice use
this same helper. -/
private theorem chain_splice {V : Type*} {D : V → V → Prop}
    {a b u v : V} {l p s k : List V}
    (hc : List.IsChain D (a :: (l ++ [b])))
    (he : a :: (l ++ [b]) = p ++ u :: v :: s)
    (hk : List.IsChain D (u :: (k ++ [v]))) :
    ∃ m : List V, m.Perm (k ++ l) ∧
      List.IsChain D (a :: (m ++ [b])) := by
  induction l generalizing a p with
  | nil =>
    cases p with
    | nil =>
      have hau : a = u := by simpa using congrArg List.head? he
      have hbvs : [b] = v :: s := by
        simpa [hau] using (List.cons.inj he).2
      have hbv : b = v := by simpa using congrArg List.head? hbvs
      subst u
      subst v
      exact ⟨k,by simp,by simpa using hk⟩
    | cons d p =>
      have hlen := congrArg List.length he
      simp only [List.length_cons,List.length_append,List.length_nil] at hlen
      omega
  | cons d l ih =>
    cases p with
    | nil =>
      have hau : a = u := by simpa using congrArg List.head? he
      have hdv : d = v := by
        simpa using congrArg List.head? (List.cons.inj he).2
      subst u
      subst v
      have htail : List.IsChain D (d :: (l ++ [b])) := hc.tail
      have hbridge : List.IsChain D ((a :: k) ++ [d]) := by simpa using hk
      have hjoined := hbridge.append_overlap htail (by simp : [d] ≠ [])
      refine ⟨k ++ d :: l,List.Perm.refl _,?_⟩
      simpa [List.append_assoc] using hjoined
    | cons e p =>
      have he' : d :: (l ++ [b]) = p ++ u :: v :: s :=
        (List.cons.inj he).2
      obtain ⟨m,hm,hmc⟩ := ih hc.tail he'
      refine ⟨d :: m,?_,?_⟩
      · exact (List.Perm.cons d hm).trans
          (List.perm_middle (a := d) (l₁ := k) (l₂ := l)).symm
      · exact List.IsChain.cons_cons hc.rel hmc

/-- An actual edge crosses any predicate that changes along a reachable path.
The two uses below locate a receiving vertex and then a receiving-to-sending
outside edge. -/
private theorem reachable_crossing {V : Type*} {D : V → V → Prop}
    {P : V → Prop} {a b : V} (h : Relation.ReflTransGen D a b) :
    P a → ¬P b → ∃ u v, P u ∧ ¬P v ∧ D u v := by
  classical
  induction h with
  | refl => intro ha hb; exact (hb ha).elim
  | @tail b c hab hbc ih =>
    intro ha hc
    by_cases hb : P b
    · exact ⟨b,c,hb,hc,hbc⟩
    · exact ih ha hb

/-- Rotate a closed chain at a specified occurring vertex. This is literal
list rotation, recorded by a permutation, and preserves the closing edge. -/
private theorem cycle_at {V : Type*} {D : V → V → Prop}
    {c a : V} {l : List V}
    (hc : List.IsChain D ((c :: l) ++ [c])) (ha : a ∈ c :: l) :
    ∃ m : List V, (a :: m).Perm (c :: l) ∧
      List.IsChain D ((a :: m) ++ [a]) := by
  obtain ⟨p,s,he⟩ := List.mem_iff_append.mp ha
  cases p with
  | nil =>
    have hca : c = a := by simpa using congrArg List.head? he
    have hls : l = s := (List.cons.inj he).2
    subst a
    subst s
    exact ⟨l,List.Perm.refl _,hc⟩
  | cons d p =>
    have hcd : c = d := by simpa using congrArg List.head? he
    subst d
    have hls : l = p ++ a :: s := (List.cons.inj he).2
    have hsplit : List.IsChain D ((c :: p) ++ a :: (s ++ [c])) := by
      simpa only [hls,List.append_assoc,List.cons_append] using hc
    have hleft : List.IsChain D ((c :: p) ++ [a]) :=
      (List.isChain_split.mp hsplit).1
    have hright : List.IsChain D (a :: (s ++ [c])) :=
      (List.isChain_split.mp hsplit).2
    have hright' : List.IsChain D ((a :: s) ++ [c]) := by simpa using hright
    have hleft' : List.IsChain D ([c] ++ (p ++ [a])) := by simpa using hleft
    have hjoined := hright'.append_overlap hleft' (by simp : [c] ≠ [])
    refine ⟨s ++ c :: p,?_,?_⟩
    · rw [he]
      simpa only [List.cons_append,List.append_assoc] using
        (List.perm_append_comm (l₁ := a :: s) (l₂ := c :: p))
    · simpa [List.append_assoc] using hjoined

/-- Finite strongly connected semicomplete directed relations have a simple
Hamilton cycle, based at any specified vertex. `hD` says that S is the actual
finite vertex set of D. Loops are immaterial; reciprocal arcs and two-cycles
are allowed. Connectivity is the actual pinned ReflTransGen relation.

Proof: erase loops from one return path, maximize simple cycle length, consume
the original cyclic_insertion/outside_uniform_of_no_insertion, cross the two
outside classes along actual reachable paths, and splice two outside vertices.
-/
theorem finite_semicomplete_hamilton {V : Type*} [DecidableEq V]
    (S : Finset V) (D : V → V → Prop)
    (hD : ∀ {s t}, D s t → s ∈ S ∧ t ∈ S)
    (hsize : 2 ≤ S.card)
    (hsemi : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → D s t ∨ D t s)
    (hstrong : ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen D s t)
    (a : V) (ha : a ∈ S) :
    ∃ l : List V, (a :: l).Nodup ∧ (a :: l).toFinset = S ∧
      2 ≤ (a :: l).length ∧ List.IsChain D ((a :: l) ++ [a]) := by
  classical
  obtain ⟨s,hs,t,ht,hst⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hedge : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ D u v := by
    rcases hsemi s hs t ht hst with h | h
    · exact ⟨s,hs,t,ht,hst,h⟩
    · exact ⟨t,ht,s,hs,hst.symm,h⟩
  obtain ⟨u,hu,v,hv,huv,hDuv⟩ := hedge
  obtain ⟨w,hwn,hwc,hwh,hwl⟩ := simple_chain_of_reachable (hstrong v hv u hu)
  obtain ⟨r,hr⟩ := List.getLast?_eq_some_iff.mp hwl
  subst w
  have hr0 : r ≠ [] := by
    intro he
    exact huv (by simpa [he] using hwh)
  obtain ⟨d,k,hrk⟩ := List.exists_cons_of_ne_nil hr0
  subst r
  have hdv : d = v := by simpa using hwh
  subst d
  have hstartN : (u :: v :: k).Nodup :=
    (List.perm_append_singleton u (v :: k)).nodup_iff.mp hwn
  have hstartC : List.IsChain D ((u :: v :: k) ++ [u]) :=
    List.IsChain.cons_cons hDuv hwc
  have hstartM : ∀ x ∈ u :: v :: k, x ∈ S := by
    intro x hx
    exact hstartC.induction (fun y => y ∈ S) _
      (fun _ _ h _ => (hD h).2) (by simp [hu]) x
      (List.mem_append.mpr (Or.inl hx))
  have bound {c : V} {l : List V} (hn : (c :: l).Nodup)
      (hm : ∀ x ∈ c :: l, x ∈ S) : (c :: l).length ≤ S.card := by
    have hsub : (c :: l).toFinset ⊆ S := by
      intro x hx
      exact hm x (List.mem_toFinset.mp hx)
    have hh := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hn] at hh
  let P : ℕ → Prop := fun n => ∃ c : V, ∃ l : List V,
    (c :: l).Nodup ∧ 2 ≤ (c :: l).length ∧
      (∀ x ∈ c :: l, x ∈ S) ∧ List.IsChain D ((c :: l) ++ [c]) ∧
        (c :: l).length = n
  have hP : P (u :: v :: k).length :=
    ⟨u,v :: k,hstartN,by simp,hstartM,hstartC,rfl⟩
  obtain ⟨c,l,hn,hlen,hm,hc,hN⟩ :=
    Nat.findGreatest_spec (bound hstartN hstartM) hP
  have maximal (d : V) (m : List V) (hdn : (d :: m).Nodup)
      (hdl : 2 ≤ (d :: m).length) (hdm : ∀ x ∈ d :: m, x ∈ S)
      (hdc : List.IsChain D ((d :: m) ++ [d])) :
      (d :: m).length ≤ (c :: l).length := by
    have hle := Nat.le_findGreatest (bound hdn hdm)
      (show P (d :: m).length from ⟨d,m,hdn,hdl,hdm,hdc,rfl⟩)
    rw [← hN] at hle
    exact hle
  have forbid_splice (k : List V) (hk0 : k ≠ []) (hkn : k.Nodup)
      (hkm : ∀ x ∈ k, x ∈ S) (hkout : ∀ x ∈ k, x ∉ c :: l)
      (p : List V) (u v : V) (s : List V)
      (he : (c :: l) ++ [c] = p ++ u :: v :: s)
      (hbridge : List.IsChain D (u :: (k ++ [v]))) : False := by
    obtain ⟨m,hmp,hmc⟩ := chain_splice hc he hbridge
    have hperm : (c :: m).Perm (k ++ c :: l) :=
      (List.Perm.cons c hmp).trans
        (List.perm_middle (a := c) (l₁ := k) (l₂ := l)).symm
    have hkn' : (k ++ c :: l).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hkn,hn,?_⟩
      intro x hx y hy hxy
      exact hkout x hx (hxy.symm ▸ hy)
    have hmn : (c :: m).Nodup := hperm.nodup_iff.mpr hkn'
    have hmm : ∀ x ∈ c :: m, x ∈ S := by
      intro x hx
      rcases List.mem_append.mp (hperm.mem_iff.mp hx) with hk | hl
      · exact hkm x hk
      · exact hm x hl
    have hlength : (c :: m).length = k.length + (c :: l).length := by
      simpa only [List.length_append] using hperm.length_eq
    have hkpos := List.length_pos_iff.mpr hk0
    have hmlen : 2 ≤ (c :: m).length := by omega
    have hle := maximal c m hmn hmlen hmm hmc
    omega
  have no_insertion {x : V} (hx : x ∈ S) (hxout : x ∉ c :: l) :
      ¬∃ (p : List V) (u v : V) (s : List V),
        (c :: l) ++ [c] = p ++ u :: v :: s ∧ D u x ∧ D x v := by
    rintro ⟨p,u,v,s,he,hux,hxv⟩
    exact forbid_splice [x] (by simp) (by simp)
      (by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hx)
      (by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hxout)
      p u v s he (List.IsChain.cons_cons hux (List.isChain_pair.mpr hxv))
  let R : V → Prop := fun x => x ∉ c :: l ∧
    ∀ v ∈ c :: l, D v x ∧ ¬D x v
  let Q : V → Prop := fun x => x ∉ c :: l ∧
    ∀ v ∈ c :: l, D x v ∧ ¬D v x
  have classify {x : V} (hx : x ∈ S) (hxout : x ∉ c :: l) : R x ∨ Q x := by
    have hsemi' : ∀ v ∈ c :: l, D v x ∨ D x v := by
      intro v hv
      apply hsemi v (hm v hv) x hx
      intro he
      exact hxout (he ▸ hv)
    rcases outside_uniform_of_no_insertion hsemi' (no_insertion hx hxout) with h | h
    · exact Or.inl ⟨hxout,h⟩
    · exact Or.inr ⟨hxout,h⟩
  have spans : ∀ x ∈ S, x ∈ c :: l := by
    intro x hx
    by_contra hxout
    have hcS : c ∈ S := hm c (by simp)
    obtain ⟨d,r,hd,hrout,hdr⟩ :=
      reachable_crossing (P := fun v => v ∈ c :: l)
        (hstrong c hcS x hx) (by simp) hxout
    have hrS : r ∈ S := (hD hdr).2
    have hr : R r := by
      rcases classify hrS hrout with hr | hr
      · exact hr
      · exact ((hr.2 d hd).2 hdr).elim
    have hcR : ¬R c := by intro h; exact h.1 (by simp)
    obtain ⟨r',y,hr',hyR,hr'y⟩ :=
      reachable_crossing (hstrong r hrS c hcS) hr hcR
    have hyout : y ∉ c :: l := by
      intro hy
      exact (hr'.2 y hy).2 hr'y
    have hyQ : Q y := (classify (hD hr'y).2 hyout).resolve_left hyR
    have hry : r' ≠ y := by
      intro he
      exact (hr'.2 c (by simp)).2 (he.symm ▸ (hyQ.2 c (by simp)).1)
    cases l with
    | nil => simp at hlen
    | cons e l =>
      have hbridge : List.IsChain D (c :: r' :: y :: [e]) :=
        List.IsChain.cons_cons (hr'.2 c (by simp)).1
          (List.IsChain.cons_cons hr'y (List.isChain_pair.mpr (hyQ.2 e (by simp)).1))
      exact forbid_splice [r',y] (by simp) (by simp [hry])
        (by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact (hD hr'y).1
          · have he : z = y := by simpa using hz
            exact he.symm ▸ (hD hr'y).2)
        (by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hr'.1
          · have he : z = y := by simpa using hz
            exact he.symm ▸ hyQ.1)
        [] c e (l ++ [c]) rfl hbridge
  obtain ⟨m,hrot,hrotC⟩ := cycle_at hc (spans a ha)
  refine ⟨m,hrot.nodup_iff.mpr hn,?_,?_,hrotC⟩
  · ext x
    simp only [List.mem_toFinset]
    exact hrot.mem_iff.trans ⟨fun hx => hm x hx,fun hx => spans x hx⟩
  · have hlen' := hrot.length_eq
    omega

end D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
