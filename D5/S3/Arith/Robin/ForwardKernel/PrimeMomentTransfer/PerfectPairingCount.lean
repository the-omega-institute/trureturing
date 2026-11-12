/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Counting and evaluating perfect pairings of finite label sets. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Cardinality and evaluations of finite perfect pairings. -/

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Disjoint two-element edges cover exactly twice their number of labels. -/
theorem pairingSupport_card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartialPairing U P) : (pairingSupport P).card = 2 * P.card := by
  change (P.biUnion fun e => e).card = 2 * P.card
  rw [Finset.card_biUnion hP.2.1]
  rw [Finset.sum_congr rfl hP.1]
  simp [Nat.mul_comm]

/-- A perfect pairing has half as many edges as covered labels. -/
theorem IsPerfectPairing.card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPerfectPairing U P) : U.card = 2 * P.card := by
  rw [← hP.2]
  exact pairingSupport_card hP.1

/-- Rank-one edge weights have the same product on every perfect pairing. -/
theorem finitePairingPolynomial_rankOne (U : Finset α) (c : Finset α → ℝ)
    (x : α → ℝ) (hc : ∀ e, e.card = 2 → c e = ∏ i ∈ e, x i) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * ∏ i ∈ U, x i := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = ∏ i ∈ U, x i := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have h := Finset.prod_biUnion (f := x) hP.1.2.1
    change (∏ i ∈ pairingSupport P, x i) = ∏ e ∈ P, ∏ i ∈ e, x i at h
    rw [hP.2] at h
    exact h.symm
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

/-- Constant edge weights contribute one power per edge of a perfect pairing. -/
theorem finitePairingPolynomial_const (U : Finset α) (c : Finset α → ℝ)
    (κ : ℝ) (hc : ∀ e, e.card = 2 → c e = κ) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * κ ^ (U.card / 2) := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = κ ^ (U.card / 2) := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have hcard : P.card = U.card / 2 := by rw [hP.card]; omega
    simp [hcard]
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

/-- Remove the pair containing a fixed label: its partner and the residual pairing
parametrize perfect pairings without multiplicity. -/
theorem perfectPairingCount_rec (U : Finset α) (a : α) (ha : a ∈ U) :
    ((Finset.univ : Finset (Finset (Finset α))).filter
      (IsPerfectPairing U)).card =
      ∑ b ∈ U.erase a, ((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing ((U.erase a).erase b))).card := by
  have hrem (b : α) : U \ {a, b} = (U.erase a).erase b := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    tauto
  have partner (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      ∃ b, b ∈ U.erase a ∧ {a, b} ∈ P := by
    obtain ⟨e, he, hae⟩ := (mem_pairingSupport a P).mp (by rw [hP.2]; exact ha)
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hP.1.1 e he)
    rcases (show a = x ∨ a = y by simpa using hae) with hax | hay
    · subst x
      refine ⟨y, Finset.mem_erase.mpr ⟨hxy.symm, ?_⟩, he⟩
      exact hP.1.2.2 ((mem_pairingSupport y P).2 ⟨{a, y}, he, by simp⟩)
    · subst y
      refine ⟨x, Finset.mem_erase.mpr ⟨hxy, ?_⟩, ?_⟩
      · exact hP.1.2.2 ((mem_pairingSupport x P).2 ⟨{x, a}, he, by simp⟩)
      · simpa only [Finset.pair_comm] using he
  let pick (P : Finset (Finset α)) (hP : IsPerfectPairing U P) : α :=
    Classical.choose (partner P hP)
  have hpick (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      pick P hP ∈ U.erase a ∧ {a, pick P hP} ∈ P :=
    Classical.choose_spec (partner P hP)
  have hErase (P : Finset (Finset α)) (hP : IsPerfectPairing U P)
      (b : α) (hb : {a, b} ∈ P) :
      IsPerfectPairing ((U.erase a).erase b) (P.erase {a, b}) := by
    have hh := (pairing_remainder hP (Finset.singleton_subset_iff.mpr hb)).2
    simpa only [pairingSupport, Finset.biUnion_singleton, id_eq, hrem b,
      Finset.sdiff_singleton_eq_erase] using hh
  have hInsert (b : α) (hb : b ∈ U.erase a) (Q : Finset (Finset α))
      (hQ : IsPerfectPairing ((U.erase a).erase b) Q) :
      IsPerfectPairing U (insert {a, b} Q) := by
    have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
    have hsub : ({a, b} : Finset α) ⊆ U := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha
      · have hiq : i = b := Finset.mem_singleton.mp hi
        subst i
        exact (Finset.mem_erase.mp hb).2
    have hE : IsPartialPairing U {{a, b}} := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        have heq : e = {a, b} := Finset.mem_singleton.mp he
        subst e
        simp [hab]
      · simp
      · simpa only [pairingSupport, Finset.biUnion_singleton, id_eq] using hsub
    have hQ' : IsPerfectPairing (U \ pairingSupport {{a, b}}) Q := by
      simpa only [pairingSupport, Finset.biUnion_singleton, id_eq, hrem b] using hQ
    simpa only [Finset.singleton_union] using (pairing_join hE hQ').1
  let S := (Finset.univ : Finset (Finset (Finset α))).filter (IsPerfectPairing U)
  let Z := (U.erase a).sigma (fun b =>
    (Finset.univ : Finset (Finset (Finset α))).filter
      (IsPerfectPairing ((U.erase a).erase b)))
  have hmem (P : Finset (Finset α)) (hP : P ∈ S) : IsPerfectPairing U P :=
    (Finset.mem_filter.mp hP).2
  let f (P : Finset (Finset α)) (hP : P ∈ S) :
      Sigma (fun _ : α => Finset (Finset α)) :=
    ⟨pick P (hmem P hP), P.erase {a, pick P (hmem P hP)}⟩
  have hbij : S.card = Z.card := by
    apply Finset.card_bij f
    · intro P hP
      apply Finset.mem_sigma.mpr
      exact ⟨(hpick P (hmem P hP)).1, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hErase P (hmem P hP) _ (hpick P (hmem P hP)).2⟩⟩
    · intro P hP Q hQ heq
      have hb := congrArg Sigma.fst heq
      have hEq := congrArg
        (fun z : Sigma (fun _ : α => Finset (Finset α)) => z.2) heq
      change pick P (hmem P hP) = pick Q (hmem Q hQ) at hb
      change P.erase {a, pick P (hmem P hP)} =
        Q.erase {a, pick Q (hmem Q hQ)} at hEq
      rw [hb] at hEq
      calc
        P = insert {a, pick P (hmem P hP)} (P.erase {a, pick P (hmem P hP)}) :=
          (Finset.insert_erase (hpick P (hmem P hP)).2).symm
        _ = insert {a, pick Q (hmem Q hQ)} (Q.erase {a, pick Q (hmem Q hQ)}) := by
          rw [hb, hEq]
        _ = Q := Finset.insert_erase (hpick Q (hmem Q hQ)).2
    · rintro ⟨b, Q⟩ hz
      obtain ⟨hb, hQ⟩ := Finset.mem_sigma.mp hz
      have hQ' := (Finset.mem_filter.mp hQ).2
      let P := insert {a, b} Q
      have hP : IsPerfectPairing U P := hInsert b hb Q hQ'
      have hPS : P ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩
      refine ⟨P, hPS, ?_⟩
      have hbp : pick P hP = b := by
        have hp := hpick P hP
        have he : {a, pick P hP} = {a, b} := by
          by_contra hn
          exact Finset.disjoint_left.mp
            (hP.1.2.1 hp.2 (by simp [P]) hn) (by simp) (by simp)
        have hm : pick P hP ∈ ({a, b} : Finset α) :=
          he ▸ (by simp : pick P hP ∈ ({a, pick P hP} : Finset α))
        have hh : pick P hP = a ∨ pick P hP = b := by simpa using hm
        exact hh.resolve_left (Finset.mem_erase.mp hp.1).1
      have heQ : ({a, b} : Finset α) ∉ Q := by
        intro he
        have hh := hQ'.1.2.2 ((mem_pairingSupport a Q).2 ⟨{a, b}, he, by simp⟩)
        simp at hh
      change (⟨pick P hP, P.erase {a, pick P hP}⟩ :
        Sigma (fun _ : α => Finset (Finset α))) = ⟨b, Q⟩
      rw [hbp]
      simp [P, heQ]
  change S.card = _
  rw [hbij]
  exact Finset.card_sigma _ _

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
