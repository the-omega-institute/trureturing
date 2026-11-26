/- GID: D5/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SharpRegularConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Symbolic vertex-deletion connectivity of every sharp regular block. -/

import D5.S3.Combinatorics.Graph.StarForming.SharpRegular
import D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity

/-! The all-degree structural assertion in SHARP_REGULAR_BIPARTITE_GAP,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The crown, the disjoint high--outside--outside--high ears,
and the two hubs are handled in the actual graph, at arbitrary degree. -/

namespace D5.S3.Combinatorics.Graph.StarForming.SharpRegularConnectivity
open SharpRegular

variable {I : Type} [Fintype I] [DecidableEq I]

private def high (b : Bool) (i : I) : Vertex I := (b,some (false,i))
private def outside (b : Bool) (i : I) : Vertex I := (b,some (true,i))
private def hub (b : Bool) : Vertex I := (b,none)
private abbrev Avoid (next : Equiv.Perm I) (z : Vertex I) :=
  (graph next).induce {v | v ≠ z}

private theorem third (hd : 3 ≤ Fintype.card I) (i j : I) :
    ∃ k : I, k ≠ i ∧ k ≠ j := by
  classical
  have hp : ({i,j} : Finset I).card ≤ 2 := by
    by_cases h : i = j <;> simp [h]
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s:= {i,j}) (t:= Finset.univ) (by simp only [Finset.card_univ]; omega)
  exact ⟨k,by simpa using hk⟩

private theorem high_injective (b : Bool) : Function.Injective (high b : I → Vertex I) := by
  intro i j h
  simpa [high] using h

private theorem high_opposite (b : Bool) (i j : I) : high b i ≠ high (!b) j := by
  cases b <;> simp [high]

private theorem crown_edge (next : Equiv.Perm I) (b : Bool) (i j : I) (h : i ≠ j) :
    (graph next).Adj (high b i) (high (!b) j) := by
  cases b <;> simp [graph,link,high,h,h.symm]

private theorem outside_edge (next : Equiv.Perm I) (b : Bool) (i : I) :
    (graph next).Adj (outside b i) (high (!b) i) := by
  cases b <;> simp [graph,link,high,outside]

private theorem ear_edge (next : Equiv.Perm I) (b : Bool) (i : I)
    (h1 : next i ≠ i) (h2 : next (next i) ≠ i) :
    (graph next).Adj (outside b i) (outside (!b) i) := by
  cases b <;> simp [graph,link,outside,h1.symm,h2.symm]

private theorem hub_edge (next : Equiv.Perm I) (b : Bool) (i : I) :
    (graph next).Adj (hub b) (outside (!b) i) := by
  cases b <;> simp [graph,link,outside,hub]

private theorem step (next : Equiv.Perm I) (z a b : Vertex I)
    (ha : a ≠ z) (hb : b ≠ z) (he : (graph next).Adj a b) :
    (Avoid next z).Reachable ⟨a,ha⟩ ⟨b,hb⟩ :=
  (show (Avoid next z).Adj ⟨a,ha⟩ ⟨b,hb⟩ from he).reachable

private theorem same_high (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (z : Vertex I) (b : Bool) (i j : I) (hi : high b i ≠ z) (hj : high b j ≠ z) :
    (Avoid next z).Reachable ⟨high b i,hi⟩ ⟨high b j,hj⟩ := by
  by_cases hij : i = j
  · subst j
    exact .refl _
  obtain ⟨k,hki,hkj⟩ := third hd i j
  by_cases hk : high (!b) k = z
  · have hi' : high (!b) i ≠ z := fun h => hki (high_injective (!b) (hk.trans h.symm))
    have hj' : high (!b) j ≠ z := fun h => hkj (high_injective (!b) (hk.trans h.symm))
    have hk' : high b k ≠ z := fun h => high_opposite b k k (h.trans hk.symm)
    exact (step next z _ _ hi hj' (crown_edge next b i j hij)).trans
      ((step next z _ _ hk' hj' (crown_edge next b k j hkj)).symm.trans
        ((step next z _ _ hk' hi' (crown_edge next b k i hki)).trans
          (step next z _ _ hj hi' (crown_edge next b j i (Ne.symm hij))).symm))
  · exact (step next z _ _ hi hk (crown_edge next b i k hki.symm)).trans
      (step next z _ _ hj hk (crown_edge next b j k hkj.symm)).symm

private theorem other_high (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (z : Vertex I) (b : Bool) (i j : I) (hi : high b i ≠ z) (hj : high (!b) j ≠ z) :
    (Avoid next z).Reachable ⟨high b i,hi⟩ ⟨high (!b) j,hj⟩ := by
  by_cases hij : i = j
  · subst j
    obtain ⟨a,hai,_⟩ := third hd i i
    obtain ⟨c,hci,hca⟩ := third hd i a
    have hac : high b a ≠ high b c := fun h => hca (high_injective b h).symm
    have hs := FiberConnectivity.surviving_pair (high b a) (high b a)
      (high b c) (high b c) z hac hac hac hac
    rcases hs with ⟨ha,_⟩ | ⟨hc,_⟩
    · exact (same_high next hd z b i a hi ha).trans
        (step next z _ _ ha hj (crown_edge next b a i hai))
    · exact (same_high next hd z b i c hi hc).trans
        (step next z _ _ hc hj (crown_edge next b c i hci))
  · exact step next z _ _ hi hj (crown_edge next b i j hij)

private theorem all_high (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (z : Vertex I) (b c : Bool) (i j : I) (hi : high b i ≠ z) (hj : high c j ≠ z) :
    (Avoid next z).Reachable ⟨high b i,hi⟩ ⟨high c j,hj⟩ := by
  cases b <;> cases c
  · exact same_high next hd z false i j hi hj
  · exact other_high next hd z false i j hi hj
  · exact other_high next hd z true i j hi hj
  · exact same_high next hd z true i j hi hj

private theorem outside_to_high (next : Equiv.Perm I)
    (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i)
    (z : Vertex I) (b : Bool) (i : I) (hv : outside b i ≠ z) :
    ∃ c j, ∃ hj : high c j ≠ z,
      (Avoid next z).Reachable ⟨outside b i,hv⟩ ⟨high c j,hj⟩ := by
  by_cases hh : high (!b) i = z
  · have ho : outside (!b) i ≠ z := by
      intro he
      have := he.trans hh.symm
      simp [high,outside] at this
    have hi : high b i ≠ z := fun he => high_opposite b i i (he.trans hh.symm)
    refine ⟨b,i,hi,?_⟩
    exact (step next z _ _ hv ho (ear_edge next b i (h1 i) (h2 i))).trans
      (step next z _ _ hi ho (by
        simpa using (outside_edge next (!b) i).symm)).symm
  · exact ⟨!b,i,hh,step next z _ _ hv hh (outside_edge next b i)⟩

private theorem hub_to_high (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (z : Vertex I) (b : Bool) (hv : hub b ≠ z) :
    ∃ c j, ∃ hj : high c j ≠ z,
      (Avoid next z).Reachable ⟨hub b,hv⟩ ⟨high c j,hj⟩ := by
  classical
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card I)
  obtain ⟨j,hji,_⟩ := third hd i i
  have hoo : outside (!b) i ≠ outside (!b) j := by
    intro h
    have he : i = j := by simpa [outside] using h
    exact hji he.symm
  have hhh : high b i ≠ high b j := fun h => hji (high_injective b h).symm
  have hoh (a c : I) : outside (!b) a ≠ high b c := by
    cases b <;> simp [outside,high]
  have hs := FiberConnectivity.surviving_pair (outside (!b) i) (high b i)
    (outside (!b) j) (high b j) z hoo (hoh i j) (hoh j i).symm hhh
  rcases hs with ⟨ho,hi⟩ | ⟨ho,hi⟩
  · refine ⟨b,i,hi,?_⟩
    exact (step next z _ _ hv ho (hub_edge next b i)).trans
      (step next z _ _ ho hi (by simpa using outside_edge next (!b) i))
  · refine ⟨b,j,hi,?_⟩
    exact (step next z _ _ hv ho (hub_edge next b j)).trans
      (step next z _ _ ho hi (by simpa using outside_edge next (!b) j))

/-- Each vertex deletion leaves the actual graph connected by crown paths,
surviving ears and hub attachments. The index type is arbitrary and finite. -/
theorem delete_preconnected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) (z : Vertex I) :
    ((graph next).induce {v | v ≠ z}).Preconnected := by
  have hr (v : {v : Vertex I // v ≠ z}) : ∃ b i, ∃ hi : high b i ≠ z,
      (Avoid next z).Reachable v ⟨high b i,hi⟩ := by
    rcases v with ⟨⟨b,x⟩,hv⟩
    cases x with
    | none => exact hub_to_high next hd z b hv
    | some x =>
      rcases x with ⟨c,i⟩
      cases c with
      | false => exact ⟨b,i,hv,.refl _⟩
      | true => exact outside_to_high next h1 h2 z b i hv
  intro v w
  obtain ⟨b,i,hi,hv⟩ := hr v
  obtain ⟨c,j,hj,hw⟩ := hr w
  exact hv.trans ((all_high next hd z b c i j hi hj).trans hw.symm)

/-- The source's ear argument gives actual two-connectivity, with order at
least three, for every such finite index permutation. -/
theorem two_connected (next : Equiv.Perm I) (hd : 3 ≤ Fintype.card I)
    (h1 : ∀ i, next i ≠ i) (h2 : ∀ i, next (next i) ≠ i) :
    (graph next).Connected ∧
      (∀ z : Vertex I, ((graph next).induce {v | v ≠ z}).Connected) ∧
      3 ≤ Fintype.card (Vertex I) := by
  classical
  have hc : 3 ≤ Fintype.card (Vertex I) := by
    simp only [Vertex,Side,Fintype.card_prod,Fintype.card_bool,Fintype.card_option]
    omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card I)
  have full : (graph next).Preconnected := by
    intro a b
    obtain ⟨z,hza,hzb⟩ := third hc a b
    let f : ((graph next).induce {v | v ≠ z}) →g graph next :=
      ⟨fun v => v.val,fun h => h⟩
    exact ((delete_preconnected next hd h1 h2 z) ⟨a,Ne.symm hza⟩
      ⟨b,Ne.symm hzb⟩).map f
  refine ⟨{ preconnected := full, nonempty := ⟨high false i⟩ },?_,hc⟩
  intro z
  have exists_survivor : ∃ v : Vertex I, v ≠ z := by
    by_cases h : high false i = z
    · exact ⟨high true i,fun he => high_opposite false i i (h.trans he.symm)⟩
    · exact ⟨high false i,h⟩
  obtain ⟨v,hv⟩ := exists_survivor
  letI : Nonempty {v : Vertex I // v ≠ z} := ⟨⟨v,hv⟩⟩
  exact { preconnected := delete_preconnected next hd h1 h2 z, nonempty := ⟨⟨v,hv⟩⟩ }

private theorem rotate_two_ne {d : ℕ} (hd : 3 ≤ d) (i : Fin d) :
    finRotate d (finRotate d i) ≠ i := by
  letI : NeZero d := ⟨by omega⟩
  intro he
  have h : i + ((1 : Fin d) + 1) = i + 0 := by
    simpa only [finRotate_apply,add_assoc,add_zero] using he
  have hh := congrArg Fin.val (add_left_cancel h)
  norm_num [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : 1 < d),
    Nat.mod_eq_of_lt (by omega : 2 < d)] at hh

/-- Every source graph G_d, d at least three, is two-connected. The proof
does not enumerate degree values or graph orders. -/
theorem cyclic_two_connected (d : ℕ) (hd : 3 ≤ d) :
    (graph (finRotate d)).Connected ∧
      (∀ z : Vertex (Fin d),
        ((graph (finRotate d)).induce {v | v ≠ z}).Connected) ∧
      3 ≤ Fintype.card (Vertex (Fin d)) := by
  apply two_connected (finRotate d) (by simpa using hd)
  · intro i
    letI : NeZero d := ⟨by omega⟩
    intro he
    have h : i + (1 : Fin d) = i + 0 := by simpa only [finRotate_apply,add_zero] using he
    have hh := congrArg Fin.val (add_left_cancel h)
    norm_num [Fin.val_natCast,Nat.mod_eq_of_lt (by omega : 1 < d)] at hh
  · exact rotate_two_ne hd

end D5.S3.Combinatorics.Graph.StarForming.SharpRegularConnectivity
