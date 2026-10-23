/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Structural classification of the small cubic graphs through their complements. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmall

open Finset

private lemma neighbors_eq_pair {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v = 2)
    {x y z : V} (hy : H.Adj x y) (hz : H.Adj x z) (hyz : y ≠ z) :
    H.neighborFinset x = {y, z} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (H.mem_neighborFinset x _).mpr hy
    · exact (H.mem_neighborFinset x _).mpr hz
  · rw [H.card_neighborFinset_eq_degree, hdeg]
    simp [hyz]

private lemma closed_small_complement {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v = 2)
    (s : Finset V) (hclosed : ∀ x ∈ s, ∀ y, H.Adj x y → y ∈ s)
    (hsmall : (univ \ s).card ≤ 2) : s = univ := by
  by_contra hne
  have hn : (univ \ s).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hs := Finset.sdiff_eq_empty_iff_subset.mp he
    exact hne (Finset.Subset.antisymm (Finset.subset_univ _) hs)
  obtain ⟨z,hz⟩ := hn
  have hzs : z ∉ s := (Finset.mem_sdiff.mp hz).2
  have hsub : H.neighborFinset z ⊆ (univ \ s).erase z := by
    intro y hy
    have ha := (H.mem_neighborFinset z y).mp hy
    have hys : y ∉ s := by
      intro hm
      exact hzs (hclosed y hm z ha.symm)
    simp [hys, ha.ne.symm]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hz] at hc
  rw [H.card_neighborFinset_eq_degree, hdeg] at hc
  omega

private lemma triangle_complement_presentation {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcard : Fintype.card V = 6)
    (hdeg : ∀ v, H.degree v = 2) {a b c : V}
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c) :
    ∃ d e f : V, List.Pairwise (· ≠ ·) [a,b,c,d,e,f] ∧
      univ = ({a,b,c,d,e,f} : Finset V) ∧
      H.neighborFinset a = {b,c} ∧ H.neighborFinset b = {a,c} ∧
      H.neighborFinset c = {a,b} ∧ H.neighborFinset d = {e,f} ∧
      H.neighborFinset e = {d,f} ∧ H.neighborFinset f = {d,e} := by
  have habn := hab.ne
  have hacn := hac.ne
  have hbcn := hbc.ne
  have ha := neighbors_eq_pair H hdeg hab hac hbcn
  have hb := neighbors_eq_pair H hdeg hab.symm hbc hacn
  have hc := neighbors_eq_pair H hdeg hac.symm hbc.symm habn
  have hr : (univ \ ({a,b,c} : Finset V)).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hcard, habn, hacn, hbcn]
  obtain ⟨d,e,f,hde,hdf,hef,hrset⟩ := Finset.card_eq_three.mp hr
  have hd : d ∉ ({a,b,c} : Finset V) := by
    have : d ∈ univ \ ({a,b,c} : Finset V) := by rw [hrset]; simp
    exact (Finset.mem_sdiff.mp this).2
  have he : e ∉ ({a,b,c} : Finset V) := by
    have : e ∈ univ \ ({a,b,c} : Finset V) := by rw [hrset]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hf : f ∉ ({a,b,c} : Finset V) := by
    have : f ∈ univ \ ({a,b,c} : Finset V) := by rw [hrset]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hu : univ = ({a,b,c,d,e,f} : Finset V) := by
    ext x
    have hx : x ∈ univ \ ({a,b,c} : Finset V) ↔ x ∈ ({d,e,f} : Finset V) := by rw [hrset]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢
    tauto
  have hpair : List.Pairwise (· ≠ ·) [a,b,c,d,e,f] := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd he hf
    simp_all [List.pairwise_cons, ne_comm]
  have rest (x y z : V) (hx : x ∈ ({d,e,f} : Finset V))
      (hp : List.Pairwise (· ≠ ·) [x,y,z])
      (hr : ({d,e,f} : Finset V) = {x,y,z}) : H.neighborFinset x = {y,z} := by
    have hxnot : x ∉ ({a,b,c} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hd
      · exact he
      · exact hf
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
    have hsub : H.neighborFinset x ⊆ ({y,z} : Finset V) := by
      intro w hw
      have hadj := (H.mem_neighborFinset x w).mp hw
      have hwrest : w ∈ ({d,e,f} : Finset V) := by
        have hwa : w ≠ a := by
          intro h; subst w
          have := (H.mem_neighborFinset a x).mpr hadj.symm
          rw [ha] at this
          simp_all
        have hwb : w ≠ b := by
          intro h; subst w
          have := (H.mem_neighborFinset b x).mpr hadj.symm
          rw [hb] at this
          simp_all
        have hwc : w ≠ c := by
          intro h; subst w
          have := (H.mem_neighborFinset c x).mpr hadj.symm
          rw [hc] at this
          simp_all
        have := Finset.mem_univ w
        rw [hu] at this
        simp_all
      rw [hr] at hwrest
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwrest ⊢
      rcases hwrest with h | h | h
      · exact False.elim (hadj.ne h.symm)
      · exact Or.inl h
      · exact Or.inr h
    apply Finset.eq_of_subset_of_card_le hsub
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
      List.pairwise_singleton, and_true] at hp
    simp [hp, hdeg]
  refine ⟨d,e,f,hpair,hu,ha,hb,hc,?_,?_,?_⟩
  · exact rest d e f (by simp) (by simp [hde,hdf,hef]) rfl
  · exact rest e d f (by simp) (by simp [hde.symm,hef,hdf]) (by ext; simp; tauto)
  · exact rest f d e (by simp) (by simp [hdf.symm,hef.symm,hde]) (by ext; simp; tauto)

set_option maxHeartbeats 1600000 in
private lemma cycle_complement_presentation {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcard : Fintype.card V = 6)
    (hdeg : ∀ v, H.degree v = 2)
    (htri : ∀ x y z, H.Adj x y → H.Adj x z → ¬ H.Adj y z) :
    ∃ a b c d e f : V, List.Pairwise (· ≠ ·) [a,b,c,d,e,f] ∧
      univ = ({a,b,c,d,e,f} : Finset V) ∧
      H.neighborFinset a = {b,f} ∧ H.neighborFinset b = {a,c} ∧
      H.neighborFinset c = {b,d} ∧ H.neighborFinset d = {c,e} ∧
      H.neighborFinset e = {d,f} ∧ H.neighborFinset f = {e,a} := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := ‹Nonempty V›
  obtain ⟨b,c,hbc,ha⟩ := Finset.card_eq_two.mp (hdeg a)
  have hab : H.Adj a b := (H.mem_neighborFinset a b).mp (by rw [ha]; simp)
  have hac : H.Adj a c := (H.mem_neighborFinset a c).mp (by rw [ha]; simp)
  have hncb : ¬ H.Adj c b := htri a c b hac hab
  have hnbc : ¬ H.Adj b c := htri a b c hab hac
  have hberase : ((H.neighborFinset b).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset b a).mpr hab.symm)]
    simp [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hberase
  have hdm : d ∈ (H.neighborFinset b).erase a := by rw [hd]; simp
  have hda := (Finset.mem_erase.mp hdm).1
  have hbd : H.Adj b d := (H.mem_neighborFinset b d).mp (Finset.mem_erase.mp hdm).2
  have hb := neighbors_eq_pair H hdeg hab.symm hbd hda.symm
  have hcerase : ((H.neighborFinset c).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset c a).mpr hac.symm)]
    simp [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hcerase
  have hem : e ∈ (H.neighborFinset c).erase a := by rw [he]; simp
  have hea := (Finset.mem_erase.mp hem).1
  have hce : H.Adj c e := (H.mem_neighborFinset c e).mp (Finset.mem_erase.mp hem).2
  have hc := neighbors_eq_pair H hdeg hac.symm hce hea.symm
  have hdc : d ≠ c := by intro h; exact hnbc (h ▸ hbd)
  have heb : e ≠ b := by intro h; exact hncb (h ▸ hce)
  have habn := hab.ne
  have hacn := hac.ne
  have hbdn := hbd.ne
  have hcen := hce.ne
  have hfour : ({a,b,c,d} : Finset V).card = 4 :=
    Finset.card_eq_four.mpr ⟨a,b,c,d,habn,hacn,hda.symm,hbc,hbdn,hdc.symm,rfl⟩
  have hde : d ≠ e := by
    intro h
    have hdN := neighbors_eq_pair H hdeg hbd.symm (h ▸ hce.symm) hbc
    have hclosed : ∀ x ∈ ({a,b,c,d} : Finset V), ∀ y, H.Adj x y → y ∈ ({a,b,c,d} : Finset V) := by
      intro x hx y hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        have hm := (H.mem_neighborFinset _ y).mpr hxy
        simp_all
        aesop
    have hall := closed_small_complement H hdeg {a,b,c,d} hclosed (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [hcard, hfour])
    have hcount := congrArg Finset.card hall
    simp [hcard, hfour] at hcount
  have hefresh : e ∉ ({a,b,c,d} : Finset V) := by
    simp [hea,heb,hcen.symm,hde.symm]
  have hfive : ({a,b,c,d,e} : Finset V).card = 5 := by
    rw [show ({a,b,c,d,e} : Finset V) = insert e {a,b,c,d} by ext; simp; tauto]
    rw [Finset.card_insert_of_notMem hefresh, hfour]
  have hnde : ¬ H.Adj d e := by
    intro h
    have hdN := neighbors_eq_pair H hdeg hbd.symm h heb.symm
    have heN := neighbors_eq_pair H hdeg hce.symm h.symm hdc.symm
    have hclosed : ∀ x ∈ ({a,b,c,d,e} : Finset V), ∀ y, H.Adj x y → y ∈ ({a,b,c,d,e} : Finset V) := by
      intro x hx y hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals
        have hm := (H.mem_neighborFinset _ y).mpr hxy
        simp_all
        aesop
    have hall := closed_small_complement H hdeg {a,b,c,d,e} hclosed (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [hcard, hfive])
    have hcount := congrArg Finset.card hall
    simp [hcard, hfive] at hcount
  have hr : (univ \ ({a,b,c,d,e} : Finset V)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hcard, hfive]
  obtain ⟨f,hfset⟩ := Finset.card_eq_one.mp hr
  have hf : f ∉ ({a,b,c,d,e} : Finset V) := by
    have : f ∈ univ \ ({a,b,c,d,e} : Finset V) := by rw [hfset]; simp
    exact (Finset.mem_sdiff.mp this).2
  have hu : univ = ({a,b,c,d,e,f} : Finset V) := by
    ext x
    have hx : x ∈ univ \ ({a,b,c,d,e} : Finset V) ↔ x = f := by rw [hfset]; simp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢
    tauto
  have hpair : List.Pairwise (· ≠ ·) [a,b,c,d,e,f] := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
    simp_all [List.pairwise_cons, ne_comm]
  have hdsub : H.neighborFinset d ⊆ ({b,f} : Finset V) := by
    intro y hy
    have hyadj := (H.mem_neighborFinset d y).mp hy
    have hyn := hyadj.ne.symm
    have hyna : y ≠ a := by
      intro h; subst y
      have := (H.mem_neighborFinset a d).mpr hyadj.symm
      simp_all
    have hync : y ≠ c := by
      intro h; subst y
      have := (H.mem_neighborFinset c d).mpr hyadj.symm
      simp_all
    have hyne : y ≠ e := by intro h; exact hnde (h ▸ hyadj)
    have := Finset.mem_univ y
    rw [hu] at this
    simp_all
  have hdN : H.neighborFinset d = {b,f} :=
    Finset.eq_of_subset_of_card_le hdsub (by simp_all [hdeg, List.pairwise_cons])
  have hdf : H.Adj d f := (H.mem_neighborFinset d f).mp (by rw [hdN]; simp)
  have hesub : H.neighborFinset e ⊆ ({c,f} : Finset V) := by
    intro y hy
    have hyadj := (H.mem_neighborFinset e y).mp hy
    have hyn := hyadj.ne.symm
    have hyna : y ≠ a := by
      intro h; subst y
      have := (H.mem_neighborFinset a e).mpr hyadj.symm
      simp_all
    have hynb : y ≠ b := by
      intro h; subst y
      have := (H.mem_neighborFinset b e).mpr hyadj.symm
      simp_all
    have hynd : y ≠ d := by intro h; exact hnde (h ▸ hyadj.symm)
    have := Finset.mem_univ y
    rw [hu] at this
    simp_all
  have heN : H.neighborFinset e = {c,f} :=
    Finset.eq_of_subset_of_card_le hesub (by simp_all [hdeg, List.pairwise_cons])
  have hef : H.Adj e f := (H.mem_neighborFinset e f).mp (by rw [heN]; simp)
  have hfN := neighbors_eq_pair H hdeg hdf.symm hef.symm hde
  refine ⟨a,b,d,f,e,c,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp_all [List.pairwise_cons, ne_comm]
  · rw [hu]; ext; simp; tauto
  · exact ha
  · exact hb
  · exact hdN
  · exact hfN
  · simpa [Finset.pair_comm] using heN
  · simpa [Finset.pair_comm] using hc

/-- Every six-vertex degree-two graph is two triangles or a six-cycle. -/
theorem two_regular_six_presentation {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcard : Fintype.card V = 6)
    (hdeg : ∀ v, H.degree v = 2) :
    ∃ a b c d e f : V, List.Pairwise (· ≠ ·) [a,b,c,d,e,f] ∧
      univ = ({a,b,c,d,e,f} : Finset V) ∧
      ((H.neighborFinset a = {b,c} ∧ H.neighborFinset b = {a,c} ∧
        H.neighborFinset c = {a,b} ∧ H.neighborFinset d = {e,f} ∧
        H.neighborFinset e = {d,f} ∧ H.neighborFinset f = {d,e}) ∨
       (H.neighborFinset a = {b,f} ∧ H.neighborFinset b = {a,c} ∧
        H.neighborFinset c = {b,d} ∧ H.neighborFinset d = {c,e} ∧
        H.neighborFinset e = {d,f} ∧ H.neighborFinset f = {e,a})) := by
  classical
  by_cases ht : ∃ a b c, H.Adj a b ∧ H.Adj a c ∧ H.Adj b c
  · obtain ⟨a,b,c,hab,hac,hbc⟩ := ht
    obtain ⟨d,e,f,hp,hu,hs⟩ := triangle_complement_presentation H hcard hdeg hab hac hbc
    exact ⟨a,b,c,d,e,f,hp,hu,Or.inl hs⟩
  · obtain ⟨a,b,c,d,e,f,hp,hu,hs⟩ := cycle_complement_presentation H hcard hdeg (by
      intro a b c hab hac hbc
      exact ht ⟨a,b,c,hab,hac,hbc⟩)
    exact ⟨a,b,c,d,e,f,hp,hu,Or.inr hs⟩

/-- A covering listing of six distinct vertices gives a vertex equivalence. -/
theorem six_listing_equiv {V : Type} [Fintype V] [DecidableEq V]
    {a b c d e f : V} (hp : List.Pairwise (· ≠ ·) [a,b,c,d,e,f])
    (hu : univ = ({a,b,c,d,e,f} : Finset V)) :
    ∃ q : Fin 6 ≃ V, q 0 = a ∧ q 1 = b ∧ q 2 = c ∧
      q 3 = d ∧ q 4 = e ∧ q 5 = f := by
  let g : Fin 6 → V := ![a,b,c,d,e,f]
  have hi : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [g, List.pairwise_cons, ne_comm]
  have hs : Function.Surjective g := by
    intro x
    have hx := Finset.mem_univ x
    rw [hu] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  exact ⟨Equiv.ofBijective g ⟨hi,hs⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Four-vertex cubic graphs are complete, without a graph-enumeration certificate. -/
theorem cubic_four_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 4)
    (hdeg : ∀ v, G.degree v = 3) : ∀ x y, G.Adj x y ↔ x ≠ y := by
  intro x y
  constructor
  · exact SimpleGraph.Adj.ne
  · intro hxy
    have hsub : G.neighborFinset x ⊆ univ.erase x := by
      intro z hz
      simp [((G.mem_neighborFinset x z).mp hz).ne.symm]
    have heq : G.neighborFinset x = univ.erase x :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hcard, SimpleGraph.card_neighborFinset_eq_degree, hdeg])
    apply (G.mem_neighborFinset x y).mp
    simp [heq, hxy.symm]

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphSmall
