/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tree edges are indexed by the non-root vertices and additive edge differences determine the colors. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.TreeDecomposition
import Mathlib.Data.ZMod.Basic

section

namespace CayleyColors

open SimpleGraph

universe u w
variable {V : Type u} {A : Type w}

abbrev Away (r : V) := {v : V // v ≠ r}

noncomputable def parent (T : CayleyProbe.Tree V) (r : V) (v : Away r) : V :=
  (CayleyProbe.shorterNeighbor T.prop v.prop).exists.choose

theorem parent_spec (T : CayleyProbe.Tree V) (r : V) (v : Away r) :
    T.val.Adj v.val (parent T r v) ∧ T.val.dist r (parent T r v) < T.val.dist r v.val :=
  (CayleyProbe.shorterNeighbor T.prop v.prop).exists.choose_spec

theorem parent_unique (T : CayleyProbe.Tree V) (r : V) (v : Away r) {w : V}
    (hadj : T.val.Adj v.val w) (hlt : T.val.dist r w < T.val.dist r v.val) :
    w = parent T r v :=
  (CayleyProbe.shorterNeighbor T.prop v.prop).unique ⟨hadj, hlt⟩ (parent_spec T r v)

theorem depth_parent (T : CayleyProbe.Tree V) (r : V) (v : Away r) :
    T.val.dist r v.val = T.val.dist r (parent T r v) + 1 := by
  have h := parent_spec T r v
  have hh := T.prop.dist_eq_dist_add_one_of_adj r h.1
  omega

theorem edge_orientation (T : CayleyProbe.Tree V) (r : V) {v w : V}
    (h : T.val.Adj v w) :
    (∃ hv : v ≠ r, parent T r ⟨v, hv⟩ = w) ∨
      (∃ hw : w ≠ r, parent T r ⟨w, hw⟩ = v) := by
  rcases T.prop.dist_eq_dist_add_one_of_adj r h with hd | hd
  · have hv : v ≠ r := by
      intro e
      rw [e, dist_self] at hd
      omega
    exact Or.inl ⟨hv, (parent_unique T r ⟨v, hv⟩ h (by simp [hd])).symm⟩
  · have hw : w ≠ r := by
      intro e
      rw [e, dist_self] at hd
      omega
    exact Or.inr ⟨hw, (parent_unique T r ⟨w, hw⟩ h.symm (by simp [hd])).symm⟩

/-- Each tree edge has exactly one endpoint farther from the root. -/
noncomputable def edgeEquiv (T : CayleyProbe.Tree V) (r : V) : Away r ≃ T.val.edgeSet := by
  let f : Away r → T.val.edgeSet := fun v =>
    ⟨s(v.val, parent T r v), (T.val.mem_edgeSet).mpr (parent_spec T r v).1⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨he, _⟩ | ⟨he, he'⟩
    · exact Subtype.ext he
    · have ha := (parent_spec T r a).2
      have hb := (parent_spec T r b).2
      rw [he'] at ha
      rw [← he] at hb
      exact (lt_asymm ha hb).elim
  · rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ v w =>
      rcases edge_orientation T r ((T.val.mem_edgeSet).mp he) with ⟨hv, hp⟩ | ⟨hw, hp⟩
      · exact ⟨⟨v, hv⟩, Subtype.ext (by change s(v, parent T r ⟨v,hv⟩) = s(v,w); rw [hp])⟩
      · exact ⟨⟨w, hw⟩, Subtype.ext (by
          change s(w, parent T r ⟨w,hw⟩) = s(v,w)
          rw [hp, Sym2.eq_swap])⟩

section AddGroup

variable [AddGroup A]

/-- Reconstruct the colors by following the parent direction towards the root. -/
noncomputable def reconstruct (T : CayleyProbe.Tree V) (r : V) (base : A)
    (diff : Away r → A) (v : V) : A := by
  classical
  exact if hv : v = r then base
    else diff ⟨v, hv⟩ + reconstruct T r base diff (parent T r ⟨v, hv⟩)
termination_by T.val.dist r v
decreasing_by exact (parent_spec T r ⟨v, hv⟩).2

@[simp] theorem reconstruct_root (T : CayleyProbe.Tree V) (r : V) (base : A) (diff : Away r → A) :
    reconstruct T r base diff r = base := by
  rw [reconstruct]
  simp

theorem reconstruct_child (T : CayleyProbe.Tree V) (r : V) (base : A) (diff : Away r → A)
    (v : Away r) :
    reconstruct T r base diff v.val = diff v + reconstruct T r base diff (parent T r v) := by
  rw [reconstruct]
  simp [v.prop]

/-- The root color and all cyclic edge differences are independent uniform coordinates when
the input coloring is uniform. The equivalence itself works over any additive group. -/
noncomputable def colorEquiv (T : CayleyProbe.Tree V) (r : V) :
    (V → A) ≃ A × (Away r → A) where
  toFun c := ⟨c r, fun v => c v.val - c (parent T r v)⟩
  invFun p := reconstruct T r p.1 p.2
  left_inv c := by
    funext v
    change reconstruct T r (c r) (fun v => c v.val - c (parent T r v)) v = c v
    induction n : T.val.dist r v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        exact reconstruct_root .. 
      · have hp := (parent_spec T r ⟨v, hv⟩).2
        change T.val.dist r (parent T r ⟨v, hv⟩) < T.val.dist r v at hp
        rw [n] at hp
        calc
          _ = (c v - c (parent T r ⟨v, hv⟩)) +
              reconstruct T r (c r) (fun v => c v.val - c (parent T r v)) (parent T r ⟨v, hv⟩) :=
            reconstruct_child T r _ _ ⟨v, hv⟩
          _ = _ := by rw [ih _ hp _ rfl, sub_add_cancel]
  right_inv p := by
    apply Prod.ext
    · exact reconstruct_root ..
    · funext v
      change reconstruct T r p.1 p.2 v.val - reconstruct T r p.1 p.2 (parent T r v) = p.2 v
      rw [reconstruct_child, add_sub_cancel_right]

theorem conflict_iff_zero (T : CayleyProbe.Tree V) (r : V) (c : V → A) (v : Away r) :
    c v.val = c (parent T r v) ↔ ((colorEquiv T r) c).2 v = 0 :=
  sub_eq_zero.symm

end AddGroup

/-- Reindex the coloring differences by the actual native tree edges. -/
noncomputable def edgeColorEquiv [AddGroup A] (T : CayleyProbe.Tree V) (r : V) :
    (V → A) ≃ A × (T.val.edgeSet → A) :=
  (colorEquiv T r).trans (Equiv.prodCongr (Equiv.refl A)
    (Equiv.arrowCongr (edgeEquiv T r) (Equiv.refl A)))

theorem zero_pattern_iff [AddGroup A] (T : CayleyProbe.Tree V) (r : V) (c : V → A)
    (v : Away r) :
    ((edgeColorEquiv (A := A) T r) c).2 (edgeEquiv T r v) = 0 ↔ c v.val = c (parent T r v) := by
  simp [edgeColorEquiv, colorEquiv, Equiv.arrowCongr, sub_eq_zero]


end CayleyColors

end

section

namespace CayleyParent

open SimpleGraph
open Function
open scoped Classical

universe u
variable {V : Type u}

def Hits (f : V → V) (x y : V) : Prop :=
  ∃ m : ℕ, (f^[m]) x = y

theorem hits_refl (f : V → V) (x : V) : Hits f x x := ⟨0,rfl⟩

theorem hits_trans {f : V → V} {x y z : V} (hxy : Hits f x y) (hyz : Hits f y z) :
    Hits f x z := by
  obtain ⟨m,hm⟩ := hxy
  obtain ⟨n,hn⟩ := hyz
  exact ⟨n + m, by rw [iterate_add_apply, hm, hn]⟩

theorem hits_step (f : V → V) (x : V) : Hits f x (f x) := ⟨1,rfl⟩

def RootMap (r : V) :=
  {f : V → V // f r = r ∧ ∀ v, Hits f v r}

noncomputable def fromTree (T : CayleyProbe.Tree V) (r : V) : V → V := by
  classical
  exact fun v => if hv : v = r then r else CayleyColors.parent T r ⟨v,hv⟩

@[simp] theorem fromTree_root (T : CayleyProbe.Tree V) (r : V) : fromTree T r r = r := by
  classical
  simp [fromTree]

theorem fromTree_child (T : CayleyProbe.Tree V) (r : V) (v : CayleyColors.Away r) :
    fromTree T r v.val = CayleyColors.parent T r v := by
  classical
  simp [fromTree, v.prop]

theorem fromTree_depth (T : CayleyProbe.Tree V) (r : V) {v : V} (hv : v ≠ r) :
    T.val.dist r v = T.val.dist r (fromTree T r v) + 1 := by
  rw [fromTree_child T r ⟨v,hv⟩]
  exact CayleyColors.depth_parent T r ⟨v,hv⟩

theorem fromTree_hits (T : CayleyProbe.Tree V) (r v : V) :
    Hits (fromTree T r) v r := by
  induction n : T.val.dist r v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v = r
    · exact hv ▸ hits_refl _ _
    · have ht := fromTree_depth T r hv
      exact hits_trans (hits_step _ _) (ih _ (by omega) _ rfl)

noncomputable def depth (r : V) (f : RootMap r) (v : V) : Nat :=
  Nat.find (f.prop.2 v)

theorem depth_hits (r : V) (f : RootMap r) (v : V) :
    (f.val^[depth r f v]) v = r :=
  Nat.find_spec (f.prop.2 v)

theorem depth_min (r : V) (f : RootMap r) (v : V) {d : Nat} (h : (f.val^[d]) v = r) :
    depth r f v ≤ d :=
  Nat.find_min' _ h

theorem depth_zero (r : V) (f : RootMap r) (v : V) :
    depth r f v = 0 ↔ v = r := by
  constructor
  · intro h
    have hd := depth_hits r f v
    rw [h] at hd
    exact hd
  · intro h
    exact Nat.eq_zero_of_le_zero (depth_min r f v (d := 0) h)

theorem depth_step (r : V) (f : RootMap r) {v : V} (hv : v ≠ r) :
    depth r f v = depth r f (f.val v) + 1 := by
  have hpos : 0 < depth r f v := Nat.pos_of_ne_zero ((depth_zero r f v).not.mpr hv)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h₁ : depth r f v ≤ depth r f (f.val v) + 1 := by
    apply depth_min r f
    rw [iterate_succ_apply]
    exact depth_hits r f _
  have h₂ : depth r f (f.val v) ≤ d := by
    apply depth_min r f
    have ht := depth_hits r f v
    rw [hd, Nat.succ_eq_add_one, iterate_succ_apply] at ht
    exact ht
  omega

theorem parent_not_self (r : V) (f : RootMap r) {v : V} (hv : v ≠ r) : f.val v ≠ v := by
  intro h
  have hs := depth_step r f hv
  rw [h] at hs
  omega

def toGraph (r : V) (f : RootMap r) : SimpleGraph V where
  Adj v w := (v ≠ r ∧ f.val v = w) ∨ (w ≠ r ∧ f.val w = v)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun he => parent_not_self r f he.1 he.2)
    (fun he => parent_not_self r f he.1 he.2)⟩

theorem toGraph_spec (r : V) (f : RootMap r) :
    (toGraph r f).IsTree ∧ ∀ v, (toGraph r f).dist r v = depth r f v := by
  apply CayleyProbe.tree_of_depth (depth r f) (depth_zero r f)
  · intro v w h
    rcases h with ⟨hv, hf⟩ | ⟨hw,hf⟩
    · exact Or.inl (hf ▸ depth_step r f hv)
    · exact Or.inr (hf ▸ depth_step r f hw)
  · intro v hv
    have hd := depth_step r f hv
    refine ⟨f.val v, ⟨Or.inl ⟨hv,rfl⟩, by omega⟩, ?_⟩
    intro w hw
    rcases hw.1 with ⟨_, h⟩ | ⟨hw', h⟩
    · exact h.symm
    · obtain ⟨_, hs⟩ := hw
      have ht := depth_step r f hw'
      rw [h] at ht
      omega

def toTree (r : V) (f : RootMap r) : CayleyProbe.Tree V :=
  ⟨toGraph r f, (toGraph_spec r f).1⟩

theorem toTree_parent (r : V) (f : RootMap r) (v : CayleyColors.Away r) :
    CayleyColors.parent (toTree r f) r v = f.val v.val := by
  symm
  apply CayleyColors.parent_unique
  · exact Or.inl ⟨v.prop,rfl⟩
  · change (toGraph r f).dist r _ < (toGraph r f).dist r _
    simp only [(toGraph_spec r f).2]
    have h := depth_step r f v.prop
    omega

noncomputable def rootMapEquiv (r : V) : CayleyProbe.Tree V ≃ RootMap r where
  toFun T := ⟨fromTree T r, fromTree_root T r, fromTree_hits T r⟩
  invFun := toTree r
  left_inv T := by
    apply Subtype.ext
    ext x y
    change ((x ≠ r ∧ fromTree T r x = y) ∨ (y ≠ r ∧ fromTree T r y = x)) ↔ T.val.Adj x y
    constructor
    · rintro (⟨hx, he⟩ | ⟨hy,he⟩)
      · exact he ▸ (fromTree_child T r ⟨x,hx⟩).symm ▸ (CayleyColors.parent_spec T r ⟨x,hx⟩).1
      · exact (he ▸ (fromTree_child T r ⟨y,hy⟩).symm ▸ (CayleyColors.parent_spec T r ⟨y,hy⟩).1).symm
    · intro ha
      rcases CayleyColors.edge_orientation T r ha with ⟨hx,he⟩ | ⟨hy,he⟩
      · exact Or.inl ⟨hx,(fromTree_child T r ⟨x,hx⟩).trans he⟩
      · exact Or.inr ⟨hy,(fromTree_child T r ⟨y,hy⟩).trans he⟩
  right_inv f := by
    apply Subtype.ext
    funext v
    change fromTree (toTree r f) r v = f.val v
    by_cases hv : v = r
    · subst v
      exact (fromTree_root _ _).trans f.prop.1.symm
    · exact (fromTree_child _ _ ⟨v,hv⟩).trans (toTree_parent r f ⟨v,hv⟩)


end CayleyParent

end
