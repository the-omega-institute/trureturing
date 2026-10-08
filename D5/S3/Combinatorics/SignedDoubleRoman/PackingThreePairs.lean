/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingThreePairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingThreePairs
   mirror-E: none(waiver:three-pair-obstruction-reduction)
   anchors: []
   utility: none
   digest: Three saturated missing pairs permit four selections with one remaining constraint. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingSaturation

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingThreePairs

open MixedDefs PackingSaturation Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
/-- Two missing-pair centres on the same side yield the ten-for-four alternative reduction. -/
theorem three_pair_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (K A B : Finset V) (u v a b c d p q : V)
    (hdist : [u, v, a, b, c, d].Nodup)
    (hK : K.card = 4) (hKA : Disjoint K ({u, v, a, b, c, d} : Finset V))
    (hp : p ∈ K) (hq : q ∈ K) (hpq : p ≠ q)
    (hA : A ⊆ K) (hAc : A.card = 2) (hAP : A ≠ {p, q})
    (hB : B ⊆ K) (hBc : B.card = 2) (hBP : B ≠ {p, q})
    (hDu : D.neighborFinset u = {v, a, b})
    (hDa : D.neighborFinset a = {u, p, q})
    (hDb : D.neighborFinset b = insert u A)
    (hDc : D.neighborFinset c = insert v B)
    (hNv : C.neighborFinset v ∪ D.neighborFinset v = {u, c, d})
    (hdv : C.Adj d v ∨ D.Adj d v)
    (hCK : ∀ r ∈ K, C.neighborFinset r ⊆ K)
    (hDK : ∀ r ∈ K, D.neighborFinset r ⊆ {a, b, c})
    (hnopq : ¬ C.Adj p q)
    (hdegree : ∀ r ∈ K ∪ ({u, v, a, b, c, d} : Finset V),
      C.degree r + D.degree r ≤ 3) :
    let R := K ∪ ({u, v, a, b, c, d} : Finset V)
    let Q : Finset V := {p, q, b, v}
    R.card ≤ 10 ∧ Q.card = 4 ∧ Q ⊆ R ∧ C.IsIndepSet (Q : Set V) ∧
      (∀ r ∈ Q, C.neighborFinset r ∪ D.neighborFinset r ⊆ R) ∧
      (∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 ∧
        (((insert r (D.neighborFinset r)) ∩ Q).card = 2 →
          D.neighborFinset r \ R = ∅) ∧ (D.neighborFinset r \ R).card ≤ 2) ∧
      (∀ r ∈ R, (D.neighborFinset r \ R).card = 2 → r = d) := by
  classical
  let U : Finset V := {u, v, a, b, c, d}
  let R := K ∪ U
  let P : Finset V := {p, q}
  let Q : Finset V := {p, q, b, v}
  have hcore : ∀ r ∈ U, r ∉ K := by
    intro r hr hrK
    exact disjoint_left.mp hKA hrK hr
  have hdist' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist'
  have hUnodup : U.card = 6 := by simp_all [U]
  have hKsub : K ⊆ R := subset_union_left
  have hUsub : U ⊆ R := subset_union_right
  have hpU : p ∉ U := disjoint_left.mp hKA hp
  have hqU : q ∉ U := disjoint_left.mp hKA hq
  have hpu : p ≠ u := by intro h; exact hpU (by simp [U, h])
  have hpv : p ≠ v := by intro h; exact hpU (by simp [U, h])
  have hpb : p ≠ b := by intro h; exact hpU (by simp [U, h])
  have hqu : q ≠ u := by intro h; exact hqU (by simp [U, h])
  have hqv : q ≠ v := by intro h; exact hqU (by simp [U, h])
  have hqb : q ≠ b := by intro h; exact hqU (by simp [U, h])
  have hnuv : u ≠ v := by aesop
  have hnua : u ≠ a := by aesop
  have hnub : u ≠ b := by aesop
  have hnuc : u ≠ c := by aesop
  have hnud : u ≠ d := by aesop
  have hnva : v ≠ a := by aesop
  have hnvb : v ≠ b := by aesop
  have hnvc : v ≠ c := by aesop
  have hnvd : v ≠ d := by aesop
  have hnab : a ≠ b := by aesop
  have hnac : a ≠ c := by aesop
  have hnad : a ≠ d := by aesop
  have hnbc : b ≠ c := by aesop
  have hnbd : b ≠ d := by aesop
  have hncd : c ≠ d := by aesop
  have hnpa : p ≠ a := by
    intro h
    exact hpU (by simp [U, h])
  have hnpc : p ≠ c := by
    intro h
    exact hpU (by simp [U, h])
  have hnpd : p ≠ d := by
    intro h
    exact hpU (by simp [U, h])
  have hnqa : q ≠ a := by
    intro h
    exact hqU (by simp [U, h])
  have hnqc : q ≠ c := by
    intro h
    exact hqU (by simp [U, h])
  have hnqd : q ≠ d := by
    intro h
    exact hqU (by simp [U, h])
  have houA : u ∉ A := by
    intro h
    exact hcore u (by simp [U]) (hA h)
  have houB : u ∉ B := by
    intro h
    exact hcore u (by simp [U]) (hB h)
  have hovA : v ∉ A := by
    intro h
    exact hcore v (by simp [U]) (hA h)
  have hovB : v ∉ B := by
    intro h
    exact hcore v (by simp [U]) (hB h)
  have hoaA : a ∉ A := by
    intro h
    exact hcore a (by simp [U]) (hA h)
  have hoaB : a ∉ B := by
    intro h
    exact hcore a (by simp [U]) (hB h)
  have hobA : b ∉ A := by
    intro h
    exact hcore b (by simp [U]) (hA h)
  have hobB : b ∉ B := by
    intro h
    exact hcore b (by simp [U]) (hB h)
  have hocA : c ∉ A := by
    intro h
    exact hcore c (by simp [U]) (hA h)
  have hocB : c ∉ B := by
    intro h
    exact hcore c (by simp [U]) (hB h)
  have hodA : d ∉ A := by
    intro h
    exact hcore d (by simp [U]) (hA h)
  have hodB : d ∉ B := by
    intro h
    exact hcore d (by simp [U]) (hB h)
  have hQsub : Q ⊆ R := by
    intro r hr
    simp only [Q, mem_insert, mem_singleton] at hr
    rcases hr with hr | hr | hr | hr <;> subst r
    · exact hKsub hp
    · exact hKsub hq
    · exact hUsub (by simp [U])
    · exact hUsub (by simp [U])
  have hsmall_inter : ∀ J : Finset V, J.card = 2 → J ≠ P → (J ∩ P).card ≤ 1 := by
    intro J hJ hJP
    have hleft := card_le_card (inter_subset_left (s₁ := J) (s₂ := P))
    have hright := card_le_card (inter_subset_right (s₁ := J) (s₂ := P))
    have hPc : P.card = 2 := card_pair hpq
    by_contra hh
    have hj : J ∩ P = J := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hp' : J ∩ P = P := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hJP (hj.symm.trans hp')
  have hCzero : ∀ r, r = u ∨ r = a ∨ r = b ∨ r = c → C.neighborFinset r = ∅ := by
    intro r hr
    have hDcard : (D.neighborFinset r).card = 3 := by
      rcases hr with hr | hr | hr | hr <;> subst r
      · rw [hDu]; simp_all
      · rw [hDa]; simp [hpu.symm, hqu.symm, hpq]
      · rw [hDb, card_insert_of_notMem (fun h => hcore u (by simp [U]) (hA h)), hAc]
      · rw [hDc, card_insert_of_notMem (fun h => hcore v (by simp [U]) (hB h)), hBc]
    have hrR : r ∈ R := by rcases hr with hr | hr | hr | hr <;> subst r <;> simp [R, U]
    have hh := hdegree r hrR
    change (C.neighborFinset r).card + (D.neighborFinset r).card ≤ 3 at hh
    apply card_eq_zero.mp
    omega
  have hCnone : ∀ r, r = u ∨ r = a ∨ r = b ∨ r = c → ∀ t, ¬ C.Adj r t := by
    intro r hr t hrt
    have hh := (C.mem_neighborFinset _ _).mpr hrt
    rw [hCzero r hr] at hh
    exact notMem_empty _ hh
  have hCvu : ¬ C.Adj v u := by
    intro h
    exact hCnone u (Or.inl rfl) v h.symm
  have hCvc : ¬ C.Adj v c := by
    intro h
    exact hCnone c (Or.inr (Or.inr (Or.inr rfl))) v h.symm
  have hCv : C.neighborFinset v ⊆ {d} := by
    intro r hr
    have hrN := subset_union_left (s₂ := D.neighborFinset v) hr
    rw [hNv] at hrN
    simp only [mem_insert, mem_singleton] at hrN
    rcases hrN with hrN | hrN | hrN <;> subst r
    · exact (hCvu ((C.mem_neighborFinset _ _).mp hr)).elim
    · exact (hCvc ((C.mem_neighborFinset _ _).mp hr)).elim
    · simp
  have hcolour : C.IsIndepSet (Q : Set V) := by
    intro r hr s hs hrs hCs
    simp only [Q, mem_coe, mem_insert, mem_singleton] at hr hs
    rcases hr with hr | hr | hr | hr <;> subst r
    · rcases hs with hs | hs | hs | hs <;> subst s
      · exact C.irrefl hCs
      · exact hnopq hCs
      · exact hcore b (by simp [U]) (hCK p hp ((C.mem_neighborFinset _ _).mpr hCs))
      · exact hcore v (by simp [U]) (hCK p hp ((C.mem_neighborFinset _ _).mpr hCs))
    · rcases hs with hs | hs | hs | hs <;> subst s
      · exact hnopq hCs.symm
      · exact C.irrefl hCs
      · exact hcore b (by simp [U]) (hCK q hq ((C.mem_neighborFinset _ _).mpr hCs))
      · exact hcore v (by simp [U]) (hCK q hq ((C.mem_neighborFinset _ _).mpr hCs))
    · exact hCnone b (Or.inr (Or.inr (Or.inl rfl))) s hCs
    · have hsd : s = d := mem_singleton.mp (hCv ((C.mem_neighborFinset _ _).mpr hCs))
      subst s
      rcases hs with hs | hs | hs | hs <;> subst d <;>
        simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
          hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
          hnva, hnvb, hnvc,
          hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
          hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
          hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
          hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
          hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
          hqb.symm, hpq.symm] at * <;> aesop
  have hNsub : ∀ r, r ∈ K ∨ r = u ∨ r = v ∨ r = a ∨ r = b ∨ r = c →
      C.neighborFinset r ∪ D.neighborFinset r ⊆ R := by
    intro r hr t ht
    rcases hr with hrK | hr | hr | hr | hr | hr
    · rcases mem_union.mp ht with ht | ht
      · exact hKsub (hCK r hrK ht)
      · apply hUsub
        have hh := hDK r hrK ht
        simp only [mem_insert, mem_singleton] at hh
        rcases hh with hh | hh | hh <;> subst t <;> simp [U]
    · subst r
      rw [hCzero u (Or.inl rfl), empty_union, hDu] at ht
      apply hUsub
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t <;> simp [U]
    · subst r
      rw [hNv] at ht
      apply hUsub
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t <;> simp [U]
    · subst r
      rw [hCzero a (Or.inr (Or.inl rfl)), empty_union, hDa] at ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t
      · exact hUsub (by simp [U])
      · exact hKsub hp
      · exact hKsub hq
    · subst r
      rw [hCzero b (Or.inr (Or.inr (Or.inl rfl))), empty_union, hDb] at ht
      rcases mem_insert.mp ht with ht | ht
      · subst t; exact hUsub (by simp [U])
      · exact hKsub (hA ht)
    · subst r
      rw [hCzero c (Or.inr (Or.inr (Or.inr rfl))), empty_union, hDc] at ht
      rcases mem_insert.mp ht with ht | ht
      · subst t; exact hUsub (by simp [U])
      · exact hKsub (hB ht)
  have hsdiff : ∀ r, r ∈ K ∨ r = u ∨ r = v ∨ r = a ∨ r = b ∨ r = c →
      D.neighborFinset r \ R = ∅ := by
    intro r hr
    exact sdiff_eq_empty_iff_subset.mpr (subset_union_right.trans (hNsub r hr))
  have hdsub : (insert d (D.neighborFinset d)) ∩ Q ⊆ {v} := by
      intro t ht
      have htQ := (mem_inter.mp ht).2
      rcases mem_insert.mp (mem_inter.mp ht).1 with ht | htD
      · subst t
        simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
          hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
          hnva, hnvb, hnvc,
          hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
          hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
          hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
          hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
          hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
          hqb.symm, hpq.symm] at * <;> aesop
      · have htD' := (D.mem_neighborFinset _ _).mp htD
        simp only [Q, mem_insert, mem_singleton] at htQ
        rcases htQ with htQ | htQ | htQ | htQ <;> subst t
        · have hh := hDK p hp ((D.mem_neighborFinset _ _).mpr htD'.symm)
          simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
            hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
            hnva, hnvb, hnvc,
            hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
            hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
            hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
            hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
            hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
            hqb.symm, hpq.symm] at * <;> aesop
        · have hh := hDK q hq ((D.mem_neighborFinset _ _).mpr htD'.symm)
          simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
            hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
            hnva, hnvb, hnvc,
            hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
            hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
            hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
            hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
            hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
            hqb.symm, hpq.symm] at * <;> aesop
        · have hh := (D.mem_neighborFinset b d).mpr htD'.symm
          rw [hDb] at hh
          rcases mem_insert.mp hh with hh | hh
          · simp_all
          · exact (hcore d (by simp [U]) (hA hh)).elim
        · simp
  have hbound : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 := by
    intro r hr
    rcases mem_union.mp hr with hrK | hrU
    · have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {r, b} := by
        intro t ht
        rcases mem_insert.mp (mem_inter.mp ht).1 with htr | htD
        · subst t; simp
        · have hh := hDK r hrK htD
          have htQ := (mem_inter.mp ht).2
          simp only [Q, mem_insert, mem_singleton] at htQ
          simp only [mem_insert, mem_singleton] at hh ⊢
          rcases hh with hh | hh | hh <;> subst t <;>
            simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
              hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
              hnva, hnvb, hnvc,
              hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
              hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
              hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
              hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
              hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
              hqb.symm, hpq.symm] at * <;> aesop
      exact (card_le_card hsub).trans card_le_two
    · simp only [U, mem_insert, mem_singleton] at hrU
      rcases hrU with hr | hr | hr | hr | hr | hr <;> subst r
      · have heq : (insert u (D.neighborFinset u)) ∩ Q = {v, b} := by
          rw [hDu]; ext t; simp [Q]; aesop
        rw [heq]; exact card_le_two
      · have heq : (insert v (D.neighborFinset v)) ∩ Q ⊆ {v} := by
          intro t ht
          have htQ := (mem_inter.mp ht).2
          rcases mem_insert.mp (mem_inter.mp ht).1 with ht | ht
          · subst t; simp
          · have hh := subset_union_right (s₁ := C.neighborFinset v) ht
            rw [hNv] at hh
            simp only [Q, mem_insert, mem_singleton] at htQ
            simp only [mem_insert, mem_singleton] at hh ⊢
            rcases htQ with htQ | htQ | htQ | htQ <;> subst t <;>
              simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB,
                hoaA, hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc,
                hnud, hnva, hnvb, hnvc,
                hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
                hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
                hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
                hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
                hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
                hqb.symm, hpq.symm] at * <;> aesop
        exact (card_le_card heq).trans (by simp)
      · have heq : (insert a (D.neighborFinset a)) ∩ Q ⊆ P := by
          rw [hDa]
          intro t ht
          simp only [mem_inter, mem_insert, mem_singleton] at ht
          simp only [Q, mem_insert, mem_singleton] at ht
          simp only [P, mem_insert, mem_singleton]
          rcases ht.2 with htQ | htQ | htQ | htQ <;> subst t <;>
            simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
              hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
              hnva, hnvb, hnvc,
              hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
              hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
              hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
              hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
              hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
              hqb.symm, hpq.symm] at * <;> aesop
        exact (card_le_card heq).trans card_le_two
      · have hsub : (insert b (D.neighborFinset b)) ∩ Q ⊆ insert b (A ∩ P) := by
          rw [hDb]
          intro t ht
          have htQ := (mem_inter.mp ht).2
          rcases mem_insert.mp (mem_inter.mp ht).1 with ht | ht
          · subst t; simp
          · rcases mem_insert.mp ht with ht | ht
            · subst t
              simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB,
                hoaA, hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc,
                hnud, hnva, hnvb, hnvc,
                hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
                hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
                hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
                hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
                hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
                hqb.symm, hpq.symm] at * <;> aesop
            · simp only [Q, mem_insert, mem_singleton] at htQ
              rcases htQ with htQ | htQ | htQ | htQ <;> subst t <;>
                simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB,
                  hoaA, hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc,
                  hnud, hnva, hnvb, hnvc,
                  hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
                  hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
                  hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
                  hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
                  hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
                  hqb.symm, hpq.symm] at * <;> aesop
        have hh := card_le_card hsub
        have hi := card_insert_le b (A ∩ P)
        have hlim := hsmall_inter A hAc hAP
        omega
      · have hsub : (insert c (D.neighborFinset c)) ∩ Q ⊆ insert v (B ∩ P) := by
          rw [hDc]
          intro t ht
          have htQ := (mem_inter.mp ht).2
          rcases mem_insert.mp (mem_inter.mp ht).1 with ht | ht
          · subst t
            simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB, hoaA,
              hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc, hnud,
              hnva, hnvb, hnvc,
              hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
              hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
              hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
              hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
              hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
              hqb.symm, hpq.symm] at * <;> aesop
          · rcases mem_insert.mp ht with ht | ht
            · subst t; simp
            · simp only [Q, mem_insert, mem_singleton] at htQ
              rcases htQ with htQ | htQ | htQ | htQ <;> subst t <;>
                simp only [U, Q, P, mem_insert, mem_singleton, houA, houB, hovA, hovB,
                  hoaA, hoaB, hobA, hobB, hocA, hocB, hodA, hodB,
                  hnuv, hnua, hnub, hnuc,
                  hnud, hnva, hnvb, hnvc,
                  hnvd, hnab, hnac, hnad, hnbc, hnbd, hncd, hnpa, hnpc, hnpd, hnqa, hnqc, hnqd, hpu,
                  hpv, hpb, hqu, hqv, hqb, hpq, hnuv.symm, hnua.symm, hnub.symm, hnuc.symm,
                  hnud.symm, hnva.symm, hnvb.symm, hnvc.symm, hnvd.symm, hnab.symm, hnac.symm,
                  hnad.symm, hnbc.symm, hnbd.symm, hncd.symm, hnpa.symm, hnpc.symm, hnpd.symm,
                  hnqa.symm, hnqc.symm, hnqd.symm, hpu.symm, hpv.symm, hpb.symm, hqu.symm, hqv.symm,
                  hqb.symm, hpq.symm] at * <;> aesop
        have hh := card_le_card hsub
        have hi := card_insert_le v (B ∩ P)
        have hlim := hsmall_inter B hBc hBP
        omega
      · exact (card_le_card hdsub).trans (by simp)
  have hcases : ∀ r ∈ R, r ≠ d →
      r ∈ K ∨ r = u ∨ r = v ∨ r = a ∨ r = b ∨ r = c := by
    intro r hr hrd
    rcases mem_union.mp hr with hrK | hrU
    · exact Or.inl hrK
    · simp only [U, mem_insert, mem_singleton] at hrU
      rcases hrU with hh | hh | hh | hh | hh | hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))
      · exact (hrd hh).elim
  change R.card ≤ 10 ∧ Q.card = 4 ∧ Q ⊆ R ∧ _
  refine ⟨?_, ?_, hQsub, hcolour, ?_, ?_, ?_⟩
  · have hh := card_union_le K U
    change (K ∪ U).card ≤ 10
    omega
  · simp [Q, hpq, hpb, hpv, hqb, hqv, hnvb.symm]
  · intro r hr
    simp only [Q, mem_insert, mem_singleton] at hr
    rcases hr with hr | hr | hr | hr <;> subst r
    · exact hNsub p (Or.inl hp)
    · exact hNsub q (Or.inl hq)
    · exact hNsub b (by simp)
    · exact hNsub v (by simp)
  · intro r hr
    refine ⟨hbound r hr, ?_, ?_⟩
    · intro htwo
      by_cases hrd : r = d
      · subst r
        change ((insert d (D.neighborFinset d)) ∩ Q).card = 2 at htwo
        have hh := card_le_card hdsub
        simp only [card_singleton] at hh
        omega
      · exact hsdiff r (hcases r hr hrd)
    · by_cases hrd : r = d
      · subst r
        exact (card_le_card (sdiff_subset_sdiff subset_union_right (Subset.refl _))).trans
          (surviving_degree_le_two C D d R (hdegree d hr) ⟨v, hUsub (by simp [U]), hdv⟩)
      · have hh : D.neighborFinset r \ R = ∅ := by
          exact hsdiff r (hcases r hr hrd)
        rw [hh]; simp
  · intro r hr htwo
    by_contra hrd
    have hh : D.neighborFinset r \ R = ∅ := by
      exact hsdiff r (hcases r hr hrd)
    rw [hh, card_empty] at htwo
    omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingThreePairs
