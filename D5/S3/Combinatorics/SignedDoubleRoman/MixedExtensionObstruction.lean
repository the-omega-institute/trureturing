/- GID: D5/S3/Combinatorics/SignedDoubleRoman/MixedExtensionObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/MixedExtensionObstruction
   mirror-E: none(waiver:single-centre-diamond)
   anchors: []
   utility: none
   digest: A four-clique created by one imposing centre contains the removable diamond. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtension

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One imposing centre can create a colour four-clique only through the six-vertex diamond. -/
theorem single_centre_obstruction (C D : SimpleGraph V) [DecidableRel D.Adj]
    (S R Q K : Finset V) (t : V) (hQ : Q ⊆ R)
    (hsupport : Supported C D S) (hno : C.CliqueFreeOn (S : Set V) 4)
    (hboundary : ∀ q ∈ Q, ∀ w ∈ S \ R, ¬ D.Adj q w)
    (hcentre : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card = 1 →
      (D.neighborFinset r ∩ (S \ R)).card = 2 →
        ∀ a ∈ K, ∀ b ∈ K, a ≠ b → D.Adj r a → D.Adj r b → r = t)
    (hK : K ⊆ S \ R) (hcard : K.card = 4)
    (hclique : (ReducedColour C D R Q (S \ R)).IsClique (K : Set V)) :
    ∃ p q r s u v : V, [p, q, r, s, u, v].Nodup ∧
      ({p, q, r, s, u, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      D.Adj u p ∧ D.Adj u q ∧ D.Adj u v := by
  classical
  let T := S \ R
  let C' := ReducedColour C D R Q T
  have hnot : ¬ C.IsClique (K : Set V) := fun h =>
    hno (hK.trans Finset.sdiff_subset) ((C.isNClique_iff).2 ⟨h, hcard⟩)
  obtain ⟨p, q, hpqsub, hpqold⟩ := (C.not_isClique_iff).mp hnot
  have hp : (p : V) ∈ K := p.property
  have hq : (q : V) ∈ K := q.property
  have hpq : (p : V) ≠ (q : V) := fun h => hpqsub (Subtype.ext h)
  have hpqnew : C'.Adj p q := hclique hp hq hpq
  obtain ⟨_, u, huR, huQ, huP, hup, huq⟩ := hpqnew.2.2.resolve_left hpqold
  have hut : u = t := hcentre u huR huQ huP p hp q hq hpq hup huq
  have hpair : D.neighborFinset u ∩ T = {(p : V), (q : V)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hup, hK hp⟩
      · exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr huq, hK hq⟩
    · rw [huP, Finset.card_pair hpq]
  have hsingle : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → ¬ C.Adj a b →
      ({a, b} : Finset V) = {(p : V), (q : V)} := by
    intro a ha b hb hab hold
    have hadj : C'.Adj a b := hclique ha hb hab
    obtain ⟨_, z, hzR, hzQ, hzP, hza, hzb⟩ := hadj.2.2.resolve_left hold
    have hzu : z = u := (hcentre z hzR hzQ hzP a ha b hb hab hza hzb).trans hut.symm
    subst z
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rw [← hpair]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hza, hK ha⟩
      · exact Finset.mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hzb, hK hb⟩
    · rw [Finset.card_pair hpq, Finset.card_pair hab]
  have hrestcard : (K \ {(p : V), (q : V)}).card = 2 := by
    rw [Finset.card_sdiff_of_subset (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · exact Finset.mem_singleton.mp hx ▸ hq), hcard, Finset.card_pair hpq]
  obtain ⟨r, s, hrs, hrest⟩ := Finset.card_eq_two.mp hrestcard
  have hrrest : r ∈ K \ {(p : V), (q : V)} := hrest ▸ by simp
  have hsrest : s ∈ K \ {(p : V), (q : V)} := hrest ▸ by simp
  obtain ⟨hr, hrpq⟩ := Finset.mem_sdiff.mp hrrest
  obtain ⟨hs, hspq⟩ := Finset.mem_sdiff.mp hsrest
  have hold : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → b ∉ ({(p : V), (q : V)} : Finset V) →
      C.Adj a b := by
    intro a ha b hb hab hbnot
    by_contra h
    have hpair' := hsingle a ha b hb hab h
    exact hbnot (hpair' ▸ by simp)
  have hpr := hold p hp r hr (by aesop) hrpq
  have hps := hold p hp s hs (by aesop) hspq
  have hqr := hold q hq r hr (by aesop) hrpq
  have hqs := hold q hq s hs (by aesop) hspq
  have hrsC := hold r hr s hs hrs hspq
  have huNotQ : u ∉ Q := by
    intro hu
    exact hboundary u hu p (hK hp) hup
  have hnonempty : ((insert u (D.neighborFinset u)) ∩ Q).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨v, hv⟩ := hnonempty
  obtain ⟨hvclosed, hvQ⟩ := Finset.mem_inter.mp hv
  have huv : D.Adj u v := by
    rcases Finset.mem_insert.mp hvclosed with h | h
    · exact (huNotQ (h ▸ hvQ)).elim
    · exact (D.mem_neighborFinset _ _).mp h
  have huK : u ∉ K := fun h => (Finset.mem_sdiff.mp (hK h)).2 huR
  have hvK : v ∉ K := fun h => (Finset.mem_sdiff.mp (hK h)).2 (hQ hvQ)
  have hdist : [p.val, q.val, r, s, u, v].Nodup := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrpq hspq
    have hpu : p.val ≠ u := fun h => huK (h ▸ hp)
    have hqu : q.val ≠ u := fun h => huK (h ▸ hq)
    have hru : r ≠ u := fun h => huK (h ▸ hr)
    have hsu : s ≠ u := fun h => huK (h ▸ hs)
    have hpv : p.val ≠ v := fun h => hvK (h ▸ hp)
    have hqv : q.val ≠ v := fun h => hvK (h ▸ hq)
    have hrv : r ≠ v := fun h => hvK (h ▸ hr)
    have hsv : s ≠ v := fun h => hvK (h ▸ hs)
    have huvne := huv.ne
    simp_all [List.nodup_cons, ne_comm]
  refine ⟨p, q, r, s, u, v, hdist, ?_, hpr, hps, hqr, hqs, hrsC, hup, huq, huv⟩
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hsupport (Or.inr hup)).2
  · exact (hsupport (Or.inr huq)).2
  · exact (hsupport (Or.inl hpr)).2
  · exact (hsupport (Or.inl hps)).2
  · exact (hsupport (Or.inr hup)).1
  · exact (hsupport (Or.inr huv)).2

end D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
