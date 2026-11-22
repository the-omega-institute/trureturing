/- GID: D5/S1/Words/TraceLevi
   generality: G
   mirror-B: D5/B/S1/Words/TraceLevi
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native trace Levi refinement with strictly independent crossing factors. -/

import D5.S1.Words.TraceProjection

/-! # Levi factorization for native traces -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TraceLevi

open D5.S1.Words.TraceProjection

universe u
variable {α : Type u}

private theorem connected_symm (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    {x y : List α} (h : Connected I x y) : Connected I y x := by
  apply (connected_iff_same_projections I hs hi y x).mpr
  intro a b hab
  exact ((connected_iff_same_projections I hs hi x y).mp h a b hab).symm

private theorem connected_append (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    {x x' y y' : List α} (hx : Connected I x x') (hy : Connected I y y') :
    Connected I (x ++ y) (x' ++ y') := by
  classical
  apply (connected_iff_same_projections I hs hi _ _).mpr
  intro a b hab
  have hx' := (connected_iff_same_projections I hs hi _ _).mp hx a b hab
  have hy' := (connected_iff_same_projections I hs hi _ _).mp hy a b hab
  have happ (v w : List α) : pairProjection a b (v ++ w) =
      pairProjection a b v ++ pairProjection a b w := by simp [pairProjection]
  rw [happ, happ, hx', hy']

private theorem mem_of_connected (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    {x y : List α} (h : Connected I x y) {b : α} (hb : b ∈ y) : b ∈ x := by
  classical
  have hp := (connected_iff_same_projections I hs hi _ _).mp h b b (hi b)
  have hm : b ∈ pairProjection b b y := by simp [pairProjection, hb]
  rw [← hp] at hm
  exact (List.mem_filter.mp hm).1

private theorem split_exposed_head (a : α) (z t k l : List α)
    (h : z ++ t = k ++ a :: l) :
    (∃ v, z = k ++ a :: v ∧ l = v ++ t) ∨
      (∃ v, k = z ++ v ∧ t = v ++ a :: l) := by
  rcases List.append_eq_append_iff.mp h with ⟨v, hk, ht⟩ | ⟨v, hz, hl⟩
  · exact Or.inr ⟨v, hk, ht⟩
  · cases v with
    | nil => exact Or.inr ⟨[], by simpa using hz.symm, by simpa using hl.symm⟩
    | cons b v =>
        have he : a = b ∧ l = v ++ t := List.cons.inj hl
        have hab := he.1
        subst b
        exact Or.inl ⟨v, hz, he.2⟩

private theorem commute_blocks (I : α → α → Prop) (q r : List α)
    (hc : ∀ a ∈ q, ∀ b ∈ r, I a b) : Connected I (q ++ r) (r ++ q) := by
  induction q with
  | nil => simpa only [List.nil_append, List.append_nil, Connected] using
      (Relation.ReflTransGen.refl (r := Swap I) (a := r))
  | cons a q ih =>
      have hq := ih (fun b hb c hc' => hc b (by simp [hb]) c hc')
      exact Relation.ReflTransGen.trans (connected_cons I a hq)
        (move_head_right I a r q (hc a (by simp)))

/-- A native trace equality admits one simultaneous four-factor refinement.
The factors crossing between the two cuts are strictly independent letter by letter. -/
theorem connected_append_iff (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (x y z t : List α) :
    Connected I (x ++ y) (z ++ t) ↔
      ∃ p q r s : List α,
        Connected I x (p ++ q) ∧ Connected I y (r ++ s) ∧
        Connected I z (p ++ r) ∧ Connected I t (q ++ s) ∧
        (∀ a ∈ q, ∀ b ∈ r, I a b) := by
  constructor
  · intro h
    induction x generalizing z t with
    | nil =>
        exact ⟨[], [], z, t, .refl, h, .refl, .refl, by simp⟩
    | cons a x ih =>
        obtain ⟨k, l, ht, hk, hres⟩ := head_exposure I hs hi a (x ++ y) (z ++ t)
          ((connected_iff_same_projections I hs hi _ _).mp h)
        have hrest : Connected I (x ++ y) (k ++ l) :=
          (connected_iff_same_projections I hs hi _ _).mpr hres
        rcases split_exposed_head a z t k l ht with ⟨v, hz, hl⟩ | ⟨v, hkv, htv⟩
        · have hr : Connected I (x ++ y) ((k ++ v) ++ t) := by
            simpa only [hl, List.append_assoc] using hrest
          obtain ⟨p, q, r, s, hx, hy, hz', ht', hc⟩ := ih (k ++ v) t hr
          refine ⟨a :: p, q, r, s, connected_cons I a hx, hy, ?_, ht', hc⟩
          rw [hz]
          exact Relation.ReflTransGen.trans
            (connected_symm I hs hi (move_head_right I a k v hk))
            (connected_cons I a hz')
        · have hr : Connected I (x ++ y) (z ++ (v ++ l)) := by
            simpa only [hkv, List.append_assoc] using hrest
          obtain ⟨p, q, r, s, hx, hy, hz', ht', hc⟩ := ih z (v ++ l) hr
          have haz : ∀ b ∈ z, I a b := by
            intro b hb
            exact hk b (by simp [hkv, hb])
          have hapr : ∀ b ∈ p ++ r, I a b := by
            intro b hb
            exact haz b (mem_of_connected I hs hi hz' hb)
          refine ⟨p, a :: q, r, s, ?_, hy, hz', ?_, ?_⟩
          · exact Relation.ReflTransGen.trans (connected_cons I a hx)
              (move_head_right I a p q (fun b hb => hapr b (by simp [hb])))
          · rw [htv]
            exact Relation.ReflTransGen.trans
              (connected_symm I hs hi (move_head_right I a v l
                (fun b hb => hk b (by simp [hkv, hb]))))
              (connected_cons I a ht')
          · intro b hb c hcr
            rcases List.mem_cons.mp hb with rfl | hbq
            · exact hapr c (by simp [hcr])
            · exact hc b hbq c hcr
  · rintro ⟨p, q, r, s, hx, hy, hz, ht, hc⟩
    have hleft := connected_append I hs hi hx hy
    have hmid := connected_append I hs hi
      (connected_append I hs hi (Relation.ReflTransGen.refl (a := p))
        (commute_blocks I q r hc)) (Relation.ReflTransGen.refl (a := s))
    have hright := connected_append I hs hi hz ht
    exact Relation.ReflTransGen.trans hleft (Relation.ReflTransGen.trans
      (by simpa only [Connected, List.append_assoc] using hmid)
      (connected_symm I hs hi hright))

end D5.S1.Words.TraceLevi
