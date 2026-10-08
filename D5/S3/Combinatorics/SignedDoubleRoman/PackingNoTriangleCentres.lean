/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingNoTriangleCentres
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingNoTriangleCentres
   mirror-E: none(waiver:saturated-obstruction-centres)
   anchors: []
   utility: none
   digest: Every centre attached to a saturated residual clique has one core and two clique ends. -/

import D5.S3.Combinatorics.SignedDoubleRoman.CliqueSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleCentres

open Finset MixedDefs CliqueSaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Saturation exhausts a centre's three domination edges and eliminates its colour edges. -/
theorem centre_data (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S R Q T K : Finset V) (hR : R ⊆ S) (hQ : Q ⊆ R)
    (hdegree : DegreeBound C D S) (hdisj : Disjoint T R)
    (hT : T ⊆ S) (hK : K ⊆ T) (hk : K.card = 4)
    (hclique : (ReducedColour C D R Q T).IsClique (K : Set V))
    (hboundary : ∀ c ∈ Q, ∀ p ∈ T, ¬D.Adj c p)
    (r p : V) (hp : p ∈ K) (hrp : D.Adj r p) :
    r ∈ R ∧ r ∉ Q ∧
      (D.neighborFinset r ∩ T).card = 2 ∧ D.neighborFinset r ∩ T ⊆ K ∧
      C.neighborFinset r = ∅ ∧
      (∀ a ∈ D.neighborFinset r ∩ T, ∀ b ∈ D.neighborFinset r ∩ T,
        a ≠ b → ¬C.Adj a b) ∧
      ∃ c ∈ Q, D.neighborFinset r = insert c (D.neighborFinset r ∩ T) := by
  classical
  obtain ⟨hrR, hrQ, q, hq, hpq, hpair, hnotC, _⟩ :=
    saturated_imposing_centres C D R Q T K (fun v hv => hdegree v (hT hv))
      hdisj hK hk hclique p hp r hrp.symm
  have hrnot : r ∉ Q := fun hr => hboundary r hr p (hK hp) hrp
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega :
    0 < ((insert r (D.neighborFinset r)) ∩ Q).card)
  have hcQ := (mem_inter.mp hc).2
  have hrc : D.Adj r c := by
    rcases mem_insert.mp (mem_inter.mp hc).1 with h | h
    · exact False.elim (hrnot (h ▸ hcQ))
    · exact (D.mem_neighborFinset _ _).mp h
  have hcT : c ∉ T := fun hcT => disjoint_left.mp hdisj hcT (hQ hcQ)
  have hcard : (insert c (D.neighborFinset r ∩ T)).card = 3 := by
    rw [hpair, card_insert_of_notMem (by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hcT (h ▸ hK hp), fun h => hcT (h ▸ hK hq)⟩), card_pair hpq]
  have heq : D.neighborFinset r = insert c (D.neighborFinset r ∩ T) := by
    symm
    apply eq_of_subset_of_card_le
    · exact insert_subset ((D.mem_neighborFinset _ _).mpr hrc) inter_subset_left
    · have hd := hdegree r (hR hrR)
      change (C.neighborFinset r).card + (D.neighborFinset r).card ≤ 3 at hd
      omega
  have hC : C.neighborFinset r = ∅ := by
    have hd := hdegree r (hR hrR)
    change (C.neighborFinset r).card + (D.neighborFinset r).card ≤ 3 at hd
    rw [heq, hcard] at hd
    exact card_eq_zero.mp (by omega)
  refine ⟨hrR, hrnot, by rw [hpair, card_pair hpq], ?_, hC, ?_, c, hcQ, heq⟩
  · rw [hpair]
    exact insert_subset hp (singleton_subset_iff.mpr hq)
  · intro a ha b hb hab
    rw [hpair] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact False.elim (hab (ha.trans hb.symm))
    · intro h
      rw [ha, hb] at h
      exact hnotC h
    · intro h
      rw [ha, hb] at h
      exact hnotC h.symm
    · exact False.elim (hab (ha.trans hb.symm))

end D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleCentres
