/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingDiamondInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingDiamondInduction
   mirror-E: none(waiver:diamond-induction-reduction)
   anchors: []
   utility: none
   digest: A six-vertex colour diamond reduces the mixed packing induction. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingConfigurationA
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingDiamondInduction

open Finset MixedDefs PackingConfigurationA PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing the saturated diamond adds two selected vertices to an inductive solution. -/
theorem diamond_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4) (p q r s u v : V)
    (hdist : [p, q, r, s, u, v].Nodup)
    (hR : ({p, q, r, s, u, v} : Finset V) ⊆ S)
    (hpr : C.Adj p r) (hps : C.Adj p s) (hqr : C.Adj q r)
    (hqs : C.Adj q s) (hrs : C.Adj r s)
    (hup : C.Adj u p ∨ D.Adj u p) (huq : C.Adj u q ∨ D.Adj u q)
    (huv : C.Adj u v ∨ D.Adj u v) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R : Finset V := {p, q, r, s, u, v}
  let Q : Finset V := {p, q}
  have hdeg : ∀ x ∈ R, C.degree x + D.degree x ≤ 3 :=
    fun x hx => hdegree x (hR hx)
  obtain ⟨hc, hb, hl⟩ := diamond_reduction C D p q r s u v hdist
    hdeg hpr hps hqr hqs hrs hup huq huv
  have hpq : p ≠ q := by
    have hh := (List.nodup_cons.mp hdist).1
    intro hpq
    exact hh (by simp [hpq])
  have hQ : Q ⊆ R := by
    intro x hx
    simp only [Q, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [R]
  have hboundary : ∀ x ∈ Q, ∀ y ∈ S \ R, ¬ C.Adj x y ∧ ¬ D.Adj x y := by
    intro x hx y hy
    have hyR := (mem_sdiff.mp hy).2
    refine ⟨?_, ?_⟩
    · intro h
      exact hyR (hb x hx (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · intro h
      exact hyR (hb x hx (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  have hlocal : ∀ x ∈ R, ((insert x (D.neighborFinset x)) ∩ Q).card +
      (D.neighborFinset x ∩ (S \ R)).card ≤ 2 := by
    intro x hx
    have hh := hl x hx
    change ((insert x (D.neighborFinset x)) ∩ Q).card +
      (D.neighborFinset x \ R).card ≤ 2 at hh
    have hsub : D.neighborFinset x ∩ (S \ R) ⊆ D.neighborFinset x \ R := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (mem_inter.mp hy).2).2⟩
    have hle := card_le_card hsub
    omega
  apply clean_reduce C D S R Q ih hR hQ ⟨p, by simp [R]⟩ _
    hsupport hdegree hc hboundary hlocal hno
  have hRcard : R.card ≤ 6 := by
    exact (card_insert_le _ _).trans (by
      have h1 := card_insert_le q ({r, s, u, v} : Finset V)
      have h2 := card_insert_le r ({s, u, v} : Finset V)
      have h3 := card_insert_le s ({u, v} : Finset V)
      have h4 : ({u, v} : Finset V).card ≤ 2 := card_le_two
      omega)
  simpa only [Q, card_pair hpq] using hRcard

end D5.S3.Combinatorics.SignedDoubleRoman.PackingDiamondInduction
