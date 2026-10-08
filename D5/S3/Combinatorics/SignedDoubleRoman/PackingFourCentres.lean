/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingFourCentres
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingFourCentres
   mirror-E: none(waiver:corrected-four-centre-selection)
   anchors: []
   utility: none
   digest: The meeting-edge obstruction admits the corrected core-vertex four-set selection. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingFourCentres

open MixedDefs Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 800000 in
/-- One selected core, the colour-path centre, and one centre on each side suffice. -/
theorem meeting_edges_selection (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (K A B : Finset V) (u v z p q : V)
    (hK : K.card = 4) (hA : A.card = 2) (hB : B.card = 2)
    (hKA : Disjoint K A) (hKB : Disjoint K B) (hAB : Disjoint A B)
    (hu : u ∉ K ∪ A ∪ B) (hv : v ∉ K ∪ A ∪ B) (huv : u ≠ v)
    (hz : z ∈ K) (hp : p ∈ A) (hq : q ∈ B)
    (hDu : D.neighborFinset u = insert v A)
    (hDv : D.neighborFinset v = insert u B)
    (hDK : ∀ r ∈ K, D.neighborFinset r ⊆ A ∪ B)
    (hDA : ∀ r ∈ A, D.neighborFinset r ⊆ insert u K)
    (hDB : ∀ r ∈ B, D.neighborFinset r ⊆ insert v K)
    (hDz : (D.neighborFinset z).card ≤ 1) (hpz : ¬ D.Adj p z)
    (hCu : C.neighborFinset u = ∅)
    (hCC : ∀ r ∈ A ∪ B, C.neighborFinset r = ∅)
    (hCz : C.neighborFinset z ⊆ K)
    (hclosedR : ∀ r ∈ insert u (insert v (K ∪ A ∪ B)),
      C.neighborFinset r ∪ D.neighborFinset r ⊆ insert u (insert v (K ∪ A ∪ B))) :
    let R := insert u (insert v (K ∪ A ∪ B))
    let Q : Finset V := {u, z, p, q}
    Q ⊆ R ∧ MixedAdmissible C D Q ∧ R.card ≤ 3 * Q.card := by
  classical
  let R := insert u (insert v (K ∪ A ∪ B))
  let Q : Finset V := {u, z, p, q}
  have hKA' := disjoint_left.mp hKA
  have hKB' := disjoint_left.mp hKB
  have hAB' := disjoint_left.mp hAB
  have hune : u ≠ z ∧ u ≠ p ∧ u ≠ q := by
    simp only [mem_union, not_or] at hu
    aesop
  have hvne : v ≠ z ∧ v ≠ p ∧ v ≠ q := by
    simp only [mem_union, not_or] at hv
    aesop
  have hzp : z ≠ p := fun h => hKA' hz (h.symm ▸ hp)
  have hzq : z ≠ q := fun h => hKB' hz (h.symm ▸ hq)
  have hpq : p ≠ q := fun h => hAB' hp (h.symm ▸ hq)
  have hpK : p ∉ K := fun h => hKA' h hp
  have hqK : q ∉ K := fun h => hKB' h hq
  have hzA : z ∉ A := hKA' hz
  have hzB : z ∉ B := hKB' hz
  have hpB : p ∉ B := hAB' hp
  have hqA : q ∉ A := fun h => hAB' h hq
  have huK : u ∉ K := fun h => hu (by simp [h])
  have hvK : v ∉ K := fun h => hv (by simp [h])
  have huA : u ∉ A := fun h => hu (by simp [h])
  have huB : u ∉ B := fun h => hu (by simp [h])
  have hvA : v ∉ A := fun h => hv (by simp [h])
  have hvB : v ∉ B := fun h => hv (by simp [h])
  have hQsub : Q ⊆ R := by
    intro r hr
    simp only [Q, mem_insert, mem_singleton] at hr
    rcases hr with hr | hr | hr | hr <;> subst r <;> simp [R, hz, hp, hq]
  have hCnone : ∀ r ∈ ({u, p, q} : Finset V), ∀ s, ¬ C.Adj r s := by
    intro r hr s hrs
    have hzero : C.neighborFinset r = ∅ := by
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with hr | hr | hr <;> subst r
      · exact hCu
      · exact hCC p (mem_union_left _ hp)
      · exact hCC q (mem_union_right _ hq)
    have hmem := (C.mem_neighborFinset _ _).mpr hrs
    rw [hzero] at hmem
    exact notMem_empty _ hmem
  have hcolour : C.IsIndepSet (Q : Set V) := by
    intro r hr s hs hrs hCs
    by_cases hrz : r = z
    · subst r
      have hsK := hCz ((C.mem_neighborFinset _ _).mpr hCs)
      simp only [Q, mem_coe, mem_insert, mem_singleton] at hs
      rcases hs with hs | hs | hs | hs <;> subst s
      · exact huK hsK
      · exact C.irrefl hCs
      · exact hpK hsK
      · exact hqK hsK
    · have hr' : r ∈ ({u, p, q} : Finset V) := by
        simp only [Q, mem_coe, mem_insert, mem_singleton] at hr
        simp only [mem_insert, mem_singleton]
        tauto
      exact hCnone r hr' s hCs
  have hclosed : ∀ r, ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 := by
    intro r
    by_cases hrR : r ∈ R
    · simp only [R, mem_insert, mem_union] at hrR
      rcases hrR with hr | hr | (hrK | hrA) | hrB
      · subst r
        have hsub : (insert u (D.neighborFinset u)) ∩ Q ⊆ {u, p} := by
          intro s hs
          rw [hDu] at hs
          simp only [mem_inter, mem_insert] at hs
          simp only [Q, mem_insert, mem_singleton] at hs
          simp only [mem_insert, mem_singleton]
          rcases hs.2 with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
        exact (card_le_card hsub).trans card_le_two
      · subst r
        have hsub : (insert v (D.neighborFinset v)) ∩ Q ⊆ {u, q} := by
          intro s hs
          rw [hDv] at hs
          simp only [mem_inter, mem_insert] at hs
          simp only [Q, mem_insert, mem_singleton] at hs
          simp only [mem_insert, mem_singleton]
          rcases hs.2 with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
        exact (card_le_card hsub).trans card_le_two
      · by_cases hrz : r = z
        · subst r
          exact (card_le_card inter_subset_left).trans
            ((card_insert_le z (D.neighborFinset z)).trans (by omega))
        · have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {p, q} := by
            intro s hs
            have hsQ := (mem_inter.mp hs).2
            rcases mem_insert.mp (mem_inter.mp hs).1 with hsr | hsD
            · subst s
              simp only [Q, mem_insert, mem_singleton] at hsQ
              rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst r <;> aesop
            · have hss := hDK r hrK hsD
              simp only [Q, mem_insert, mem_singleton] at hsQ
              simp only [mem_insert, mem_singleton]
              rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
          exact (card_le_card hsub).trans card_le_two
      · have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {u, z} ∨ r = p := by
          by_cases hrp : r = p
          · exact Or.inr hrp
          · left
            intro s hs
            have hsQ := (mem_inter.mp hs).2
            rcases mem_insert.mp (mem_inter.mp hs).1 with hsr | hsD
            · subst s
              simp only [Q, mem_insert, mem_singleton] at hsQ
              rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst r <;> aesop
            · have hss := hDA r hrA hsD
              simp only [Q, mem_insert, mem_singleton] at hsQ
              simp only [mem_insert, mem_singleton]
              rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
        rcases hsub with hsub | hrp
        · exact (card_le_card hsub).trans card_le_two
        · subst r
          have hsub : (insert p (D.neighborFinset p)) ∩ Q ⊆ {p, u} := by
            intro s hs
            have hsQ := (mem_inter.mp hs).2
            rcases mem_insert.mp (mem_inter.mp hs).1 with hsp | hsD
            · subst s
              simp
            · have hss := hDA p hp hsD
              have hsDz := (D.mem_neighborFinset _ _).mp hsD
              simp only [Q, mem_insert, mem_singleton] at hsQ
              simp only [mem_insert, mem_singleton]
              rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
          exact (card_le_card hsub).trans card_le_two
      · have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {q, z} := by
          intro s hs
          have hsQ := (mem_inter.mp hs).2
          rcases mem_insert.mp (mem_inter.mp hs).1 with hsr | hsD
          · subst s
            simp only [Q, mem_insert, mem_singleton] at hsQ
            rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst r <;> aesop
          · have hss := hDB r hrB hsD
            simp only [Q, mem_insert, mem_singleton] at hsQ
            simp only [mem_insert, mem_singleton]
            rcases hsQ with hsQ | hsQ | hsQ | hsQ <;> subst s <;> aesop
        exact (card_le_card hsub).trans card_le_two
    · have hzero : (insert r (D.neighborFinset r)) ∩ Q = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        rcases mem_insert.mp (mem_inter.mp hs).1 with hsr | hsD
        · subst s
          exact hrR (hQsub (mem_inter.mp hs).2)
        · exact hrR (hclosedR s (hQsub (mem_inter.mp hs).2)
            (mem_union_right _ ((D.mem_neighborFinset _ _).mpr
              ((D.mem_neighborFinset _ _).mp hsD).symm)))
      rw [hzero]
      simp
  change Q ⊆ R ∧ MixedAdmissible C D Q ∧ _
  refine ⟨hQsub, ⟨hcolour, hclosed⟩, ?_⟩
  have hQc : Q.card = 4 := by simp [Q, hune, hzp, hzq, hpq]
  have hRc : R.card ≤ 10 := by
    have h1 := card_union_le K A
    have h2 := card_union_le (K ∪ A) B
    have h3 := card_insert_le v (K ∪ A ∪ B)
    have h4 := card_insert_le u (insert v (K ∪ A ∪ B))
    dsimp only [R]
    omega
  change R.card ≤ 3 * Q.card
  omega

/-- When each clique vertex has two attachments, selecting all four centres is admissible. -/
theorem disjoint_edges_selection (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (K A B : Finset V) (u v : V)
    (hK : K.card = 4) (hA : A.card = 2) (hB : B.card = 2)
    (hKA : Disjoint K A) (hKB : Disjoint K B) (hAB : Disjoint A B)
    (hu : u ∉ K ∪ A ∪ B) (hv : v ∉ K ∪ A ∪ B)
    (hDu : D.neighborFinset u = insert v A)
    (hDv : D.neighborFinset v = insert u B)
    (hDK : ∀ r ∈ K, (D.neighborFinset r).card ≤ 2)
    (hDC : ∀ r ∈ A ∪ B, D.neighborFinset r ⊆ insert u (insert v K))
    (hCC : ∀ r ∈ A ∪ B, C.neighborFinset r = ∅)
    (hclosedR : ∀ r ∈ insert u (insert v (K ∪ A ∪ B)),
      C.neighborFinset r ∪ D.neighborFinset r ⊆ insert u (insert v (K ∪ A ∪ B))) :
    let R := insert u (insert v (K ∪ A ∪ B))
    let Q := A ∪ B
    Q ⊆ R ∧ MixedAdmissible C D Q ∧ R.card ≤ 3 * Q.card := by
  classical
  let R := insert u (insert v (K ∪ A ∪ B))
  let Q := A ∪ B
  have hQsub : Q ⊆ R := by
    intro r hr
    simp only [Q, mem_union] at hr
    rcases hr with hr | hr <;> simp [R, hr]
  have huQ : u ∉ Q := fun h => hu (by simp only [Q, mem_union] at h; aesop)
  have hvQ : v ∉ Q := fun h => hv (by simp only [Q, mem_union] at h; aesop)
  have hKQ : Disjoint K Q := disjoint_union_right.mpr ⟨hKA, hKB⟩
  have hcolour : C.IsIndepSet (Q : Set V) := by
    intro r hr s hs hrs hCs
    have hh := (C.mem_neighborFinset _ _).mpr hCs
    rw [hCC r hr] at hh
    exact notMem_empty _ hh
  have hclosed : TwoLimited D Q := by
    intro r
    by_cases hrR : r ∈ R
    · simp only [R, mem_insert, mem_union] at hrR
      rcases hrR with hr | hr | (hrK | hrA) | hrB
      · subst r
        have hsub : (insert u (D.neighborFinset u)) ∩ Q ⊆ A := by
          intro s hs
          rw [hDu] at hs
          have hsQ := (mem_inter.mp hs).2
          rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
          · subst s
            exact (huQ hsQ).elim
          · rcases mem_insert.mp h with h | h
            · subst s
              exact (hvQ hsQ).elim
            · exact h
        exact (card_le_card hsub).trans (by omega)
      · subst r
        have hsub : (insert v (D.neighborFinset v)) ∩ Q ⊆ B := by
          intro s hs
          rw [hDv] at hs
          have hsQ := (mem_inter.mp hs).2
          rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
          · subst s
            exact (hvQ hsQ).elim
          · rcases mem_insert.mp h with h | h
            · subst s
              exact (huQ hsQ).elim
            · exact h
        exact (card_le_card hsub).trans (by omega)
      · have hrQ : r ∉ Q := disjoint_left.mp hKQ hrK
        have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ D.neighborFinset r := by
          intro s hs
          rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
          · subst s
            exact (hrQ (mem_inter.mp hs).2).elim
          · exact h
        exact (card_le_card hsub).trans (hDK r hrK)
      · have hrQ : r ∈ Q := mem_union_left _ hrA
        have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {r} := by
          intro s hs
          rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
          · simpa using h
          · have hss := hDC r hrQ h
            have hsQ := (mem_inter.mp hs).2
            rcases mem_insert.mp hss with hss | hss
            · subst s
              exact (huQ hsQ).elim
            · rcases mem_insert.mp hss with hss | hss
              · subst s
                exact (hvQ hsQ).elim
              · exact (disjoint_left.mp hKQ hss hsQ).elim
        exact (card_le_card hsub).trans (by simp)
      · have hrQ : r ∈ Q := mem_union_right _ hrB
        have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {r} := by
          intro s hs
          rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
          · simpa using h
          · have hss := hDC r hrQ h
            have hsQ := (mem_inter.mp hs).2
            rcases mem_insert.mp hss with hss | hss
            · subst s
              exact (huQ hsQ).elim
            · rcases mem_insert.mp hss with hss | hss
              · subst s
                exact (hvQ hsQ).elim
              · exact (disjoint_left.mp hKQ hss hsQ).elim
        exact (card_le_card hsub).trans (by simp)
    · have hzero : (insert r (D.neighborFinset r)) ∩ Q = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        rcases mem_insert.mp (mem_inter.mp hs).1 with h | h
        · subst s
          exact hrR (hQsub (mem_inter.mp hs).2)
        · exact hrR (hclosedR s (hQsub (mem_inter.mp hs).2)
            (mem_union_right _ ((D.mem_neighborFinset _ _).mpr
              ((D.mem_neighborFinset _ _).mp h).symm)))
      rw [hzero]
      simp
  change Q ⊆ R ∧ MixedAdmissible C D Q ∧ _
  refine ⟨hQsub, ⟨hcolour, hclosed⟩, ?_⟩
  have hQc : Q.card = 4 := by rw [card_union_of_disjoint hAB, hA, hB]
  have hRc : R.card ≤ 10 := by
    have h1 := card_union_le K A
    have h2 := card_union_le (K ∪ A) B
    have h3 := card_insert_le v (K ∪ A ∪ B)
    have h4 := card_insert_le u (insert v (K ∪ A ∪ B))
    dsimp only [R]
    omega
  change R.card ≤ 3 * Q.card
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingFourCentres
