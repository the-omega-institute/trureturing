/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingThreeInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingThreeInduction
   mirror-E: none(waiver:three-centre-induction)
   anchors: []
   utility: none
   digest: A three-centre obstruction reduces to a ten-for-four selection with one harmless pair. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingThreePairs
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore
import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtensionObstruction

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingThreeInduction

open Finset MixedDefs PackingThreePairs PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sole remaining centre cannot create a clique in the absence of a colour diamond. -/
theorem three_centre_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S K A B : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4)
    (hnoA : ¬ ∃ p q r s c v : V, [p, q, r, s, c, v].Nodup ∧
      ({p, q, r, s, c, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj c p ∨ D.Adj c p) ∧ (C.Adj c q ∨ D.Adj c q) ∧
      (C.Adj c v ∨ D.Adj c v))
    (u v a b c d p q : V) (hdist : [u, v, a, b, c, d].Nodup)
    (hK : K.card = 4) (hKA : Disjoint K ({u, v, a, b, c, d} : Finset V))
    (hR : K ∪ ({u, v, a, b, c, d} : Finset V) ⊆ S)
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
    (hnopq : ¬ C.Adj p q) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R := K ∪ ({u, v, a, b, c, d} : Finset V)
  let Q : Finset V := {p, q, b, v}
  let T := S \ R
  obtain ⟨hcount, hQcard, hQ, hc, hb, hl, hdonly⟩ := three_pair_reduction C D K A B
    u v a b c d p q hdist hK hKA hp hq hpq hA hAc hAP hB hBc hBP
    hDu hDa hDb hDc hNv hdv hCK hDK hnopq (fun r hr => hdegree r (hR hr))
  have hboundary : ∀ r ∈ Q, ∀ t ∈ T, ¬ C.Adj r t ∧ ¬ D.Adj r t := by
    intro r hr t ht
    have htR := (mem_sdiff.mp ht).2
    constructor
    · exact fun h => htR (hb r hr (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · exact fun h => htR (hb r hr (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  have hP (r : V) : D.neighborFinset r ∩ T = D.neighborFinset r \ R := by
    ext t
    simp only [T, mem_inter, mem_sdiff]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, (hsupport (Or.inr ((D.mem_neighborFinset _ _).mp h.1))).2, h.2⟩
  have hlocal : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card ≤ 2 ∧
      (((insert r (D.neighborFinset r)) ∩ Q).card = 2 →
        D.neighborFinset r ∩ T = ∅) ∧ (D.neighborFinset r ∩ T).card ≤ 2 := by
    intro r hr
    rw [hP]
    exact hl r hr
  have hnone : (ReducedColour C D R Q T).CliqueFreeOn (T : Set V) 4 := by
    intro J hJ
    intro hJnc
    obtain ⟨hJclique, hJcard⟩ := (ReducedColour C D R Q T).isNClique_iff.mp hJnc
    obtain ⟨p, q, r, s, t, w, hdist, hsub, hpr, hps, hqr, hqs, hrs, htp, htq, htw⟩ :=
      single_centre_obstruction C D S R Q J d hQ hsupport hno
        (fun r hr t ht => (hboundary r hr t ht).2)
        (fun r hr _ hrP _ _ _ _ _ _ _ => hdonly r hr (by rwa [← hP]))
        hJ hJcard hJclique
    exact hnoA ⟨p, q, r, s, t, w, hdist, hsub, hpr, hps, hqr, hqs, hrs,
      Or.inr htp, Or.inr htq, Or.inr htw⟩
  apply reduce C D S R Q ih hR hQ ⟨u, by simp [R]⟩ _ hsupport hdegree
    hc hboundary hlocal hnone
  change R.card ≤ 3 * Q.card
  change R.card ≤ 10 at hcount
  change Q.card = 4 at hQcard
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingThreeInduction
