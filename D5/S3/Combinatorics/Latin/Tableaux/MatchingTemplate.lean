/- GID: D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/Tableaux/MatchingTemplate
   mirror-E: none(waiver:structural-matching-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact matchings and stability of the ordered Latin-tableaux tail template. -/

import Mathlib.Tactic

/-! MatchingTemplate for literal Latin tableaux and their availability graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Finset

namespace D5.S3.Combinatorics.Latin.Tableaux.MatchingTemplate

private def sections : List (Finset ℕ) → Finset (List ℕ)
  | [] => {[]}
  | g :: gs => g.biUnion fun x => (sections gs).image (x :: ·)

/-- All injective choices of one actual symbol in each ordered column. -/
def matchings (G : List (Finset ℕ)) : Finset (List ℕ) :=
  (sections G).filter List.Nodup

private theorem mem_sections {G : List (Finset ℕ)} {q : List ℕ} :
    q ∈ sections G ↔ List.Forall₂ (fun x g => x ∈ g) q G := by
  induction G generalizing q with
  | nil => cases q <;> simp [sections]
  | cons g gs ih =>
      cases q with
      | nil => simp [sections]
      | cons x q => simp [sections, ih, List.forall₂_cons]

/-- Membership in the finite enumerator is exactly the literal matching condition. -/
theorem mem_matchings {G : List (Finset ℕ)} {q : List ℕ} :
    q ∈ matchings G ↔ List.Forall₂ (fun x g => x ∈ g) q G ∧ q.Nodup := by
  simp [matchings, mem_sections]

/-- Delete a chosen row and border by a new universal symbol and column. -/
def border (G : List (Finset ℕ)) (B : Finset ℕ) (q : List ℕ) (u : ℕ) :
    List (Finset ℕ) :=
  List.zipWith (fun g x => insert u (g.erase x)) G q ++ [insert u B]

/-- The ordered tail template, including its actual fixed symbol set. -/
inductive Tail : List (Finset ℕ) → Finset ℕ → Prop
  | base (x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      Tail [{x}, {y,z}, {x,y,z}] {x,y,z}
  | step (x : ℕ) (G : List (Finset ℕ)) (B : Finset ℕ)
      (fresh : x ∉ B) (tail : Tail G B) :
      Tail ({x} :: G.map (insert x)) (insert x B)

private theorem strip_insert (G : List (Finset ℕ)) (q : List ℕ) (x : ℕ)
    (h : List.Forall₂ (fun a g => a ∈ g) q (G.map (insert x))) (hn : x ∉ q) :
    List.Forall₂ (fun a g => a ∈ g) q G := by
  induction G generalizing q with
  | nil => simpa using h
  | cons g G ih =>
      cases h with
      | cons ha ht =>
          simp only [List.mem_cons, not_or] at hn
          exact .cons ((Finset.mem_insert.mp ha).resolve_left (Ne.symm hn.1)) (ih _ ht hn.2)

private theorem avoids (G : List (Finset ℕ)) (q : List ℕ) (x : ℕ)
    (h : List.Forall₂ (fun a g => a ∈ g) q G) (hx : ∀ g ∈ G, x ∉ g) : x ∉ q := by
  induction h with
  | nil => simp
  | @cons a g q G ha ht ih =>
      simp only [List.mem_cons, not_or]
      exact ⟨(by intro he; subst a; exact hx g (by simp) ha),
        ih (fun g hg => hx g (by simp [hg]))⟩

private theorem matchings_forced (G : List (Finset ℕ)) (x : ℕ)
    (h : ∀ g ∈ G, x ∉ g) :
    matchings ({x} :: G.map (insert x)) = (matchings G).image (x :: ·) := by
  ext q
  cases q with
  | nil => simp [mem_matchings]
  | cons a q =>
      simp only [mem_matchings, List.forall₂_cons, Finset.mem_singleton,
        List.nodup_cons, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨⟨rfl, hf⟩, hn, hnd⟩
        exact ⟨q, ⟨strip_insert G q a hf hn, hnd⟩, rfl, rfl⟩
      · rintro ⟨p, ⟨hp, hnd⟩, rfl, rfl⟩
        refine ⟨⟨rfl, ?_⟩, avoids G p x hp h, hnd⟩
        rw [List.forall₂_map_right_iff]
        exact hp.imp fun _ _ ha => Finset.mem_insert_of_mem ha

theorem tail_subsets {G : List (Finset ℕ)} {B : Finset ℕ}
    (h : Tail G B) : ∀ g ∈ G, g ⊆ B := by
  induction h with
  | base x y z hxy hxz hyz => simp only [List.mem_cons, List.not_mem_nil, or_false]; aesop
  | step x G B hx ht ih =>
      intro g hg
      simp only [List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g, hg, rfl⟩
      · simp
      · exact Finset.insert_subset_insert x (ih g hg)

private theorem base_matchings (x y z : ℕ) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    matchings [{x}, {y,z}, {x,y,z}] = {[x,y,z], [x,z,y]} := by
  simp [matchings, sections, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz,
    Finset.insert_comm, Finset.filter_insert, Finset.filter_singleton, List.nodup_cons]

/-- Every tail template has exactly two full matchings. -/
theorem tail_matchings {G : List (Finset ℕ)} {B : Finset ℕ}
    (h : Tail G B) : (matchings G).card = 2 := by
  induction h with
  | base x y z hxy hxz hyz =>
      rw [base_matchings x y z hxy hxz hyz]
      simp [hyz]
  | step x G B hx ht ih =>
      rw [matchings_forced G x (fun g hg hmem => hx (tail_subsets ht g hg hmem))]
      rw [Finset.card_image_of_injective _ (fun _ _ h => List.cons_injective h)]
      exact ih

private theorem zip_insert_erase (G : List (Finset ℕ)) (q : List ℕ)
    (x u : ℕ) (hx : ∀ g ∈ G, x ∉ g)
    (hq : List.Forall₂ (fun a g => a ∈ g) q G) :
    List.zipWith (fun g a => insert u (g.erase a)) (G.map (insert x)) q =
      (List.zipWith (fun g a => insert x (g.erase a)) G q).map (insert u) := by
  induction hq with
  | nil => rfl
  | @cons a g q G ha ht ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      congr 1
      · have hax : a ≠ x := by intro he; subst a; exact hx g (by simp) ha
        ext s
        simp only [Finset.mem_insert, Finset.mem_erase]
        aesop
      · exact ih (fun g hg => hx g (by simp [hg]))

/-- Every chosen matching preserves the tail template under bordering. -/
theorem tail_transition {G : List (Finset ℕ)} {B : Finset ℕ}
    (h : Tail G B) (q : List ℕ) (hq : q ∈ matchings G)
    (u : ℕ) (hu : u ∉ B) : Tail (border G B q u) (insert u B) := by
  induction h generalizing q u with
  | base x y z hxy hxz hyz =>
      rw [base_matchings x y z hxy hxz hyz] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      have hux : u ≠ x := by aesop
      have huy : u ≠ y := by aesop
      have huz : u ≠ z := by aesop
      rcases hq with rfl | rfl
      · have hb := Tail.step u _ _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; aesop) (Tail.base z x y (Ne.symm hxz) (Ne.symm hyz) hxy)
        convert hb using 1 <;>
          try simp only [border, List.zipWith_cons_cons, List.zipWith_nil_left,
            List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        all_goals
          try simp only [List.cons.injEq, and_true]
          and_intros <;> ext s <;> simp <;> aesop
      · have hb := Tail.step u _ _ (by simpa [Finset.insert_comm] using hu)
          (Tail.base y x z (Ne.symm hxy) hyz hxz)
        convert hb using 1 <;>
          try simp only [border, List.zipWith_cons_cons, List.zipWith_nil_left,
            List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        all_goals
          try simp only [List.cons.injEq, and_true]
          and_intros <;> ext s <;> simp <;> aesop
  | step x G B hx ht ih =>
      rw [matchings_forced G x (fun g hg hmem => hx (tail_subsets ht g hg hmem))] at hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hb := ih p hp x hx
      have hux : u ∉ insert x B := hu
      have hb' := Tail.step u _ _ hux hb
      have heq : border ({x} :: G.map (insert x)) (insert x B) (x :: p) u =
          {u} :: (border G B p x).map (insert u) := by
        unfold border
        simp only [List.zipWith_cons_cons, Finset.erase_singleton,
          Finset.insert_empty, List.cons_append, List.map_append,
          List.map_cons, List.map_nil]
        rw [zip_insert_erase G p x u
          (fun g hg hmem => hx (tail_subsets ht g hg hmem)) (mem_matchings.mp hp).1]
      rw [heq]
      simpa [Finset.insert_comm] using hb'

/-- The three fixed first-column profiles; the index is the distinguished column. -/
def headGraph (e : Fin 3) (a b c : ℕ) : List (Finset ℕ) :=
  if e.val = 0 then [{a,c}, {b,c}, {b,c}]
  else if e.val = 1 then [{b,c}, {a,c}, {b,c}]
  else [{b,c}, {b,c}, {a,c}]

/-- The two literal head rows in a profile. -/
def headRows (e : Fin 3) (a b c : ℕ) : Finset (List ℕ) :=
  if e.val = 0 then {[a,b,c], [a,c,b]}
  else if e.val = 1 then {[b,a,c], [c,a,b]}
  else {[b,c,a], [c,b,a]}

private theorem strip_union3 (G : List (Finset ℕ)) (q : List ℕ) (a b c : ℕ)
    (h : List.Forall₂ (fun x g => x ∈ g) q (G.map (fun g => {a,b,c} ∪ g)))
    (ha : a ∉ q) (hb : b ∉ q) (hc : c ∉ q) :
    List.Forall₂ (fun x g => x ∈ g) q G := by
  induction G generalizing q with
  | nil => simpa using h
  | cons g G ih =>
      cases h with
      | @cons x _ q _ hx ht =>
          simp only [List.mem_cons, not_or] at ha hb hc
          have hxg : x ∈ g := by simpa [Ne.symm ha.1, Ne.symm hb.1, Ne.symm hc.1] using hx
          exact .cons hxg (ih q ht ha.2 hb.2 hc.2)

private theorem full_split (H : List (Finset ℕ)) (B : Finset ℕ)
    (hsub : ∀ g ∈ H, g ⊆ B) (e : Fin 3) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ B) (hb : b ∉ B) (hc : c ∉ B) :
    matchings (headGraph e a b c ++ H.map (fun g => {a,b,c} ∪ g)) =
      ((headRows e a b c).product (matchings H)).image (fun pq => pq.1 ++ pq.2) := by
  have lift (q : List ℕ) (hq : q ∈ matchings H) :
      List.Forall₂ (fun x g => x ∈ g) q (H.map (fun g => {a,b,c} ∪ g)) ∧
      a ∉ q ∧ b ∉ q ∧ c ∉ q ∧ q.Nodup := by
    have hm := (mem_matchings.mp hq).1
    refine ⟨?_, avoids H q a hm (fun g hg hmem => ha (hsub g hg hmem)),
      avoids H q b hm (fun g hg hmem => hb (hsub g hg hmem)),
      avoids H q c hm (fun g hg hmem => hc (hsub g hg hmem)), (mem_matchings.mp hq).2⟩
    rw [List.forall₂_map_right_iff]
    exact hm.imp fun _ _ h => Finset.mem_union_right _ h
  ext q
  constructor
  · intro hq
    have hm := (mem_matchings.mp hq).1
    have hn := (mem_matchings.mp hq).2
    fin_cases e <;> simp [headGraph] at hm
    all_goals
      cases hm with
      | @cons x _ q _ hx ht =>
        cases ht with
        | @cons y _ q _ hy ht =>
          cases ht with
          | @cons z _ q _ hz ht =>
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
            simp only [List.nodup_cons, List.mem_cons, not_or] at hn
            rcases hx with hx | hx <;> subst x <;>
              rcases hy with hy | hy <;> subst y <;>
              rcases hz with hz | hz <;> subst z <;> simp_all only [not_true_eq_false, false_and,
                and_false, not_false_eq_true, and_true, true_and, not_or,
                List.mem_cons, List.nodup_cons, List.not_mem_nil]
            all_goals
              have htail : q ∈ matchings H := mem_matchings.mpr
                ⟨strip_union3 H q a b c (by simpa using ht) (by tauto) (by tauto) (by tauto), by tauto⟩
              apply Finset.mem_image.mpr
              refine ⟨([_,_,_],q), ?_, rfl⟩
              exact Finset.mem_product.mpr ⟨by simp [headRows], htail⟩
  · intro hq
    obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    have hl := lift q hq
    fin_cases e <;> simp [headRows] at hp
    all_goals rcases hp with rfl | rfl
    all_goals
      apply mem_matchings.mpr
      simp only [headGraph]
      simp_all [Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- A source availability graph with its actual low symbols and three high symbols. -/
def Full (G : List (Finset ℕ)) (B : Finset ℕ) (a b c : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∉ B ∧ b ∉ B ∧ c ∉ B ∧
  ∃ (e : Fin 3) (H : List (Finset ℕ)), Tail H B ∧
    G = headGraph e a b c ++ H.map (fun g => {a,b,c} ∪ g)

/-- Every full invariant graph has exactly four distinct matchings. -/
theorem full_matchings {G : List (Finset ℕ)} {B : Finset ℕ} {a b c : ℕ}
    (h : Full G B a b c) : (matchings G).card = 4 := by
  obtain ⟨hab,hac,hbc,ha,hb,hc,e,H,ht,rfl⟩ := h
  rw [full_split H B (tail_subsets ht) e a b c hab hac hbc ha hb hc]
  have hlen (p : List ℕ) (hp : p ∈ headRows e a b c) : p.length = 3 := by
    fin_cases e <;> simp [headRows] at hp <;> rcases hp with rfl | rfl <;> rfl
  have hi : Set.InjOn (fun pq : List ℕ × List ℕ => pq.1 ++ pq.2)
      (↑((headRows e a b c).product (matchings H)) : Set _) := by
    intro p hp q hq he
    have hp' := hlen p.1 (Finset.mem_product.mp hp).1
    have hq' := hlen q.1 (Finset.mem_product.mp hq).1
    have hh := List.append_inj he (hp'.trans hq'.symm)
    exact Prod.ext hh.1 hh.2
  rw [Finset.card_image_iff.mpr hi]
  change (headRows e a b c ×ˢ matchings H).card = 4
  rw [Finset.card_product, tail_matchings ht]
  have hh : (headRows e a b c).card = 2 := by
    fin_cases e <;> simp [headRows, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  rw [hh]

private theorem zip_full_border (H : List (Finset ℕ)) (q : List ℕ)
    (B : Finset ℕ) (a b c u : ℕ) (hsub : ∀ g ∈ H, g ⊆ B)
    (ha : a ∉ B) (hb : b ∉ B) (hc : c ∉ B)
    (hq : List.Forall₂ (fun x g => x ∈ g) q H) :
    List.zipWith (fun g x => insert u (g.erase x)) (H.map (fun g => {a,b,c} ∪ g)) q =
      (List.zipWith (fun g x => insert a (g.erase x)) H q).map (fun g => {b,c,u} ∪ g) := by
  induction hq with
  | nil => rfl
  | @cons x g q H hx ht ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      congr 1
      · have hxa : x ≠ a := by intro he; subst x; exact ha (hsub g (by simp) hx)
        have hxb : x ≠ b := by intro he; subst x; exact hb (hsub g (by simp) hx)
        have hxc : x ≠ c := by intro he; subst x; exact hc (hsub g (by simp) hx)
        ext s
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
        aesop
      · exact ih (fun g hg => hsub g (by simp [hg]))

set_option maxHeartbeats 2000000 in
/-- Every full matching preserves the invariant, including the entire enlarged tail. -/
theorem full_transition {G : List (Finset ℕ)} {B : Finset ℕ} {a b c : ℕ}
    (h : Full G B a b c) (q : List ℕ) (hq : q ∈ matchings G)
    (u : ℕ) (hu : u ∉ {a,b,c} ∪ B) :
    Full (border G ({a,b,c} ∪ B) q u) (insert a B) b c u := by
  obtain ⟨hab,hac,hbc,ha,hb,hc,e,H,ht,rfl⟩ := h
  rw [full_split H B (tail_subsets ht) e a b c hab hac hbc ha hb hc] at hq
  obtain ⟨⟨p,r⟩, hpr, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hp,hr⟩ := Finset.mem_product.mp hpr
  have ht' := tail_transition ht r hr a ha
  have hu' : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ∉ B := by simpa using hu
  refine ⟨hbc, Ne.symm hu'.2.1, Ne.symm hu'.2.2.1, ?_, ?_, ?_, ?_⟩
  · simp [Ne.symm hab,hb]
  · simp [Ne.symm hac,hc]
  · simp [hu'.1,hu'.2.2.2]
  have hz := zip_full_border H r B a b c u (tail_subsets ht) ha hb hc (mem_matchings.mp hr).1
  have hlast : insert u ({a,b,c} ∪ B) = {b,c,u} ∪ insert a B := by ext s; simp; tauto
  let f : Fin 3 := if p[0]? = some c then 0 else if p[1]? = some c then 1 else 2
  refine ⟨f, border H B r a, ht', ?_⟩
  fin_cases e <;> simp [headRows] at hp
  all_goals rcases hp with rfl | rfl
  all_goals
    simp only [border, List.cons_append, List.nil_append]
    simp only [headGraph, f]
    norm_num only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq, hac, hbc, Ne.symm hac, Ne.symm hbc]
    try simp only [ite_false, ite_true]
    norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]
    try simp only [ite_false, ite_true]
    simp only [List.zipWith_cons_cons, List.cons_append, List.map_append,
      List.map_cons, List.map_nil, List.nil_append]
    rw [hz, hlast]
    try simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    and_intros <;> first
    | rfl
    | (ext s; simp; aesop)

end D5.S3.Combinatorics.Latin.Tableaux.MatchingTemplate
