/- GID: D5/S3/Combinatorics/Graph/URSRelativeCyclePartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/URSRelativeCyclePartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Type]
   utility: none
   digest: Actual reflected incidences bound every invariant partition of moved support. -/

import D5.S3.Combinatorics.Graph.URSComponentParity
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.URSRelativeCyclePartition

open Finset
open D5.S3.Combinatorics.Graph.URSComponentParity

/-- Relative coordinates retain every original row and column. -/
def relative {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
    (r t : Fin (2 * n)) : Equiv.Perm (Fin n) :=
  (ρ t).trans (ρ r).symm

def movedSupport {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
    (r s : Fin (2 * n)) : Finset (Fin n) :=
  univ.filter fun x => relative ρ r s x ≠ x

/-- Invariant partitions include either empty block. All counts use the original indexed array. -/
theorem actual_invariant_moved_support_bound {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
    (hf : ∀ x p, (fibre ρ x p).card = 2)
    (hr : ∀ x y p q, x ≠ y → p ≠ q →
      pairCount ρ x y p q = pairCount ρ x y q p)
    {r s : Fin (2 * n)} (hrs : r ≠ s)
    (U : Finset (Fin n)) (hUD : U ⊆ movedSupport ρ r s)
    (hU : U.image (relative ρ r s) = U) :
    n + (movedSupport ρ r s).card ≤
      U.card ^ 2 + ((movedSupport ρ r s) \ U).card ^ 2 + 1 := by
  classical

  have relative_apply {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (r t : Fin (2 * n)) (x : Fin n) :
      relative ρ r t x = (ρ r).symm ((ρ t) x) := by
    rfl

  have relative_agreement_iff {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (r t : Fin (2 * n)) (x : Fin n) :
      relative ρ r t x = x ↔ ρ t x = ρ r x := by
    constructor
    · intro h
      have := congrArg (ρ r) h
      simpa [relative] using this
    · intro h
      apply (ρ r).injective
      simpa [relative, h]

  have agreement_third_row_not_fixed {n : ℕ}
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
      (x : Fin n) (hs : relative ρ r s x = x) :
      relative ρ r t x ≠ x := by
    intro ht
    have hrsval : ρ s x = ρ r x := (relative_agreement_iff ρ r s x).mp hs
    have hrtval : ρ t x = ρ r x := (relative_agreement_iff ρ r t x).mp ht
    have hrmem : r ∈ fibre ρ x (ρ r x) := by simp [fibre]
    have hsmem : s ∈ fibre ρ x (ρ r x) := by simp [fibre, hrsval]
    have htmem : t ∈ fibre ρ x (ρ r x) := by simp [fibre, hrtval]
    have hsub : insert r (insert s {t}) ⊆ fibre ρ x (ρ r x) := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hrmem
      · exact hsmem
      · exact htmem
    have hthree : 3 ≤ (fibre ρ x (ρ r x)).card := by
      have hc := Finset.card_le_card hsub
      simpa [hrs, hrt, hst] using hc
    have htwo := hf x (ρ r x)
    omega

  have saturated_transport_to_agreement {n : ℕ}
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      (hr : ∀ x y p q, x ≠ y → p ≠ q →
        pairCount ρ x y p q = pairCount ρ x y q p)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
      {u x : Fin n} (hu : relative ρ r s u ≠ u)
      (hx : relative ρ r s x = x) (ht : relative ρ r t u = x) :
      relative ρ r t x = u ∨ relative ρ r t x = relative ρ r s u := by
    classical
    have hsx : ρ s x = ρ r x := (relative_agreement_iff ρ r s x).mp hx
    have hsu : ρ s u ≠ ρ r u := by
      intro h
      exact hu ((relative_agreement_iff ρ r s u).mpr h)
    have hxu : x ≠ u := by
      intro h
      rw [h] at hx
      exact hu hx
    have hpxq : ρ r x ≠ ρ r u := fun h => hxu ((ρ r).injective h)
    have hpxz : ρ r x ≠ ρ s u := by
      rw [← hsx]
      exact fun h => hxu ((ρ s).injective h)
    let A : Finset (Fin (2 * n)) :=
      univ.filter fun j => ρ j x = ρ r u ∧ ρ j u = ρ r x
    let B : Finset (Fin (2 * n)) :=
      univ.filter fun j => ρ j x = ρ s u ∧ ρ j u = ρ r x
    have hApos : 0 < A.card := by
      have hpos : 0 < pairCount ρ x u (ρ r x) (ρ r u) := by
        apply card_pos.mpr
        exact ⟨r, by simp⟩
      rw [hr x u (ρ r x) (ρ r u) hxu hpxq] at hpos
      exact hpos
    have hBpos : 0 < B.card := by
      have hpos : 0 < pairCount ρ x u (ρ r x) (ρ s u) := by
        apply card_pos.mpr
        exact ⟨s, by simp [hsx]⟩
      rw [hr x u (ρ r x) (ρ s u) hxu hpxz] at hpos
      exact hpos
    have hAB : Disjoint A B := by
      apply disjoint_left.mpr
      intro j hjA hjB
      have ha : ρ j x = ρ r u ∧ ρ j u = ρ r x := by simpa [A] using hjA
      have hb : ρ j x = ρ s u ∧ ρ j u = ρ r x := by simpa [B] using hjB
      exact hsu (hb.1.symm.trans ha.1)
    have hsub : A ∪ B ⊆ fibre ρ u (ρ r x) := by
      intro j hj
      rcases mem_union.mp hj with hj | hj
      · have ha : ρ j x = ρ r u ∧ ρ j u = ρ r x := by simpa [A] using hj
        simpa [fibre] using ha.2
      · have hb : ρ j x = ρ s u ∧ ρ j u = ρ r x := by simpa [B] using hj
        simpa [fibre] using hb.2
    have hunion : A ∪ B = fibre ρ u (ρ r x) := by
      apply eq_of_subset_of_card_le hsub
      rw [hf, card_union_of_disjoint hAB]
      omega
    have htu : ρ t u = ρ r x := by
      have h := congrArg (ρ r) ht
      simpa [relative] using h
    have htmem : t ∈ A ∪ B := by
      rw [hunion]
      simp [fibre, htu]
    rcases mem_union.mp htmem with htA | htB
    · left
      have ha : ρ t x = ρ r u ∧ ρ t u = ρ r x := by simpa [A] using htA
      simpa [relative, ha.1]
    · right
      have hb : ρ t x = ρ s u ∧ ρ t u = ρ r x := by simpa [B] using htB
      simp only [relative_apply, hb.1]

  have agreement_internal_transposition {n : ℕ}
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      (hr : ∀ x y p q, x ≠ y → p ≠ q →
        pairCount ρ x y p q = pairCount ρ x y q p)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
      {x y : Fin n} (hx : relative ρ r s x = x)
      (hy : relative ρ r s y = y) (ht : relative ρ r t x = y) :
      relative ρ r t y = x := by
    classical
    have htx := agreement_third_row_not_fixed ρ hf hrs hrt hst x hx
    have hxy : x ≠ y := by intro h; exact htx (ht.trans h.symm)
    have hpq : ρ r x ≠ ρ r y := fun h => hxy ((ρ r).injective h)
    have hsx := (relative_agreement_iff ρ r s x).mp hx
    have hsy := (relative_agreement_iff ρ r s y).mp hy
    let A := (univ : Finset (Fin (2 * n))).filter
      fun j => ρ j x = ρ r x ∧ ρ j y = ρ r y
    let B := (univ : Finset (Fin (2 * n))).filter
      fun j => ρ j x = ρ r y ∧ ρ j y = ρ r x
    have hsubA : A ⊆ fibre ρ x (ρ r x) := by
      intro j hj
      have hj' : ρ j x = ρ r x ∧ ρ j y = ρ r y := by simpa [A] using hj
      simpa [fibre] using hj'.1
    have hsubrs : {r, s} ⊆ A := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · simp [A]
      · simp [A, hsx, hsy]
    have hcA : A.card = 2 := by
      have hu := card_le_card hsubA
      have hl := card_le_card hsubrs
      rw [hf] at hu
      have : ({r, s} : Finset (Fin (2 * n))).card = 2 := by simp [hrs]
      rw [this] at hl
      omega
    have hcB : B.card = 2 := by
      change pairCount ρ x y (ρ r y) (ρ r x) = 2
      rw [← hr x y (ρ r x) (ρ r y) hxy hpq]
      exact hcA
    have hsubB : B ⊆ fibre ρ x (ρ r y) := by
      intro j hj
      have hj' : ρ j x = ρ r y ∧ ρ j y = ρ r x := by simpa [B] using hj
      simpa [fibre] using hj'.1
    have heqB : B = fibre ρ x (ρ r y) :=
      eq_of_subset_of_card_le hsubB (by rw [hf, hcB])
    have htmem : t ∈ B := by
      rw [heqB]
      have h := congrArg (ρ r) ht
      simpa [fibre, relative] using h
    have hty : ρ t y = ρ r x := (show ρ t x = ρ r y ∧ ρ t y = ρ r x from
      by simpa [B] using htmem).2
    simp [relative, hty]

  have actual_contracted_permutation {n : ℕ}
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      (hr : ∀ x y p q, x ≠ y → p ≠ q →
        pairCount ρ x y p q = pairCount ρ x y q p)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
      ∃ h : Equiv.Perm {u : Fin n // relative ρ r s u ≠ u},
        (∀ u : {u : Fin n // relative ρ r s u ≠ u}, (h u).val = if relative ρ r s (relative ρ r t u) ≠ relative ρ r t u
          then relative ρ r t u else relative ρ r t (relative ρ r t u)) ∧
        (∀ u : {u : Fin n // relative ρ r s u ≠ u}, relative ρ r s (relative ρ r t u) = relative ρ r t u →
          (h u).val = u.val ∨ (h u).val = relative ρ r s u) := by
    classical
    let σ := relative ρ r s
    let τ := relative ρ r t
    have hreturn : ∀ u, σ u ≠ u → σ (τ u) = τ u → σ (τ (τ u)) ≠ τ (τ u) := by
      intro u hu htu htt
      have hi := agreement_internal_transposition ρ hf hr hrs hrt hst htu htt rfl
      have heq : τ (τ u) = u := τ.injective hi
      exact hu (by simpa [heq] using htt)
    let f : {u : Fin n // σ u ≠ u} → {u : Fin n // σ u ≠ u} := fun u =>
      if hd : σ (τ u) ≠ τ u then ⟨τ u, hd⟩
      else ⟨τ (τ u), hreturn u u.property (not_ne_iff.mp hd)⟩
    have hfval : ∀ u, (f u).val = if σ (τ u) ≠ τ u then τ u else τ (τ u) := by
      intro u
      dsimp [f]
      split <;> rfl
    have hinj : Function.Injective f := by
      intro u v heq
      have he := congrArg Subtype.val heq
      rw [hfval, hfval] at he
      by_cases hu : σ (τ u) ≠ τ u <;> by_cases hv : σ (τ v) ≠ τ v
      · simp only [if_pos hu, if_pos hv] at he
        exact Subtype.ext (τ.injective he)
      · simp only [if_pos hu, if_neg hv] at he
        have heuv : u.val = τ v := τ.injective he
        exact False.elim (u.property (by simpa [← heuv] using not_ne_iff.mp hv))
      · simp only [if_neg hu, if_pos hv] at he
        have hevu : τ u = v.val := τ.injective he
        exact False.elim (v.property (by simpa [hevu] using not_ne_iff.mp hu))
      · simp only [if_neg hu, if_neg hv] at he
        exact Subtype.ext (τ.injective (τ.injective he))
    let h : Equiv.Perm {u : Fin n // σ u ≠ u} :=
      Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj)
    refine ⟨h, hfval, ?_⟩
    intro u hu
    change (f u).val = u.val ∨ (f u).val = σ u
    rw [hfval, if_neg (not_ne_iff.mpr hu)]
    exact saturated_transport_to_agreement ρ hf hr hrs hrt hst u.property hu rfl

  have actual_moved_count_odd {n : ℕ} (hn : Odd n)
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      (hr : ∀ x y p q, x ≠ y → p ≠ q →
        pairCount ρ x y p q = pairCount ρ x y q p)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
      Odd ((movedSupport ρ r s).filter
        fun u => relative ρ r t u ∈ movedSupport ρ r s).card := by
    classical
    let σ := relative ρ r s
    let τ := relative ρ r t
    let S : Finset (Fin n) := univ.filter fun x => σ x = x
    let D : Finset (Fin n) := univ.filter fun x => σ x ≠ x
    let A := S.filter fun x => τ x ∈ S
    let B := S.filter fun x => τ x ∉ S
    let C := D.filter fun x => τ x ∈ S
    let K := D.filter fun x => τ x ∉ S
    have hA : ∀ x, x ∈ A ↔ σ x = x ∧ σ (τ x) = τ x := by
      intro x; simp [A, S]
    have hint : ∀ x, x ∈ A → τ (τ x) = x := by
      intro x hx
      exact agreement_internal_transposition ρ hf hr hrs hrt hst
        ((hA x).mp hx).1 ((hA x).mp hx).2 rfl
    let f : Function.End {x // x ∈ A} := fun x => ⟨τ x, (hA (τ x)).mpr
      ⟨((hA x).mp x.property).2, by simpa [hint x x.property] using ((hA x).mp x.property).1⟩⟩
    have hpow : f ^ (2 ^ 1) = 1 := by
      change (fun x => f (f x)) = id
      funext x
      apply Subtype.ext
      change τ (τ x.val) = x.val
      exact hint x x.property
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfix : Fintype.card (Function.fixedPoints f) = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun x => ?_⟩
      have heq : τ x.val.val = x.val.val := congrArg Subtype.val x.property
      exact agreement_third_row_not_fixed ρ hf hrs hrt hst x.val.val
        ((hA x.val.val).mp x.val.property).1 heq
    have hAeven : A.card % 2 = 0 := by
      have hm := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hpow
      simpa [Nat.ModEq, hfix, Fintype.card_coe] using hm
    have hAB : A.card + B.card = S.card := card_filter_add_card_filter_not _
    have hKC : K.card + C.card = D.card := by
      have h := card_filter_add_card_filter_not (s := D) (fun x => τ x ∈ S)
      simpa [K, C, add_comm] using h
    have hSD : S.card + D.card = n := by
      simpa [S, D] using card_filter_add_card_filter_not
        (s := (univ : Finset (Fin n))) (fun x => σ x = x)
    let F := (univ : Finset (Fin n)).filter fun x => τ x ∈ S
    have hF : F.card = S.card := card_equiv τ (by intro x; simp [F])
    have hFAC : F.card = A.card + C.card := by
      have hp := card_filter_add_card_filter_not (s := F) (fun x => σ x = x)
      have hpA : F.filter (fun x => σ x = x) = A := by ext x; simp [F, A, S]; tauto
      have hpC : F.filter (fun x => ¬σ x = x) = C := by ext x; simp [F, C, D]; tauto
      rw [hpA, hpC] at hp
      omega
    have hnmod := Nat.odd_iff.mp hn
    have hKodd : Odd K.card := by
      rw [Nat.odd_iff]
      omega
    simpa [K, D, S, movedSupport, σ] using hKodd

  have actual_block_count_odd {n : ℕ} (hn : Odd n)
      (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
      (hf : ∀ x p, (fibre ρ x p).card = 2)
      (hr : ∀ x y p q, x ≠ y → p ≠ q →
        pairCount ρ x y p q = pairCount ρ x y q p)
      {r s t : Fin (2 * n)} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
      (U : Finset (Fin n)) (hUD : U ⊆ movedSupport ρ r s)
      (hUσ : ∀ x, relative ρ r s x ∈ U ↔ x ∈ U) :
      Odd ((U.filter fun x => relative ρ r t x ∈ U).card +
        (((movedSupport ρ r s) \ U).filter
          fun x => relative ρ r t x ∈ (movedSupport ρ r s) \ U).card) := by
    classical
    let σ := relative ρ r s
    let τ := relative ρ r t
    let D := movedSupport ρ r s
    let V := D \ U
    have hD : ∀ x, x ∈ D ↔ σ x ≠ x := by intro x; simp [D, movedSupport, σ]
    have hVD : V ⊆ D := sdiff_subset
    have hUV : ∀ x, x ∈ U → x ∉ V := by intro x hx; simp [V, hx]
    have hVσ : ∀ x, x ∈ V → σ x ∈ V := by
      intro x hx
      have hxD := (mem_sdiff.mp hx).1
      have hxU := (mem_sdiff.mp hx).2
      apply mem_sdiff.mpr
      refine ⟨(hD (σ x)).mpr (fun he => (hD x).mp hxD (σ.injective he)), ?_⟩
      exact fun he => hxU ((hUσ x).mp he)
    obtain ⟨h, hval, hkeep⟩ := actual_contracted_permutation ρ hf hr hrs hrt hst
    let f : Fin n → Fin n := fun x => if σ (τ x) ≠ τ x then τ x else τ (τ x)
    have hval' : ∀ x : {x : Fin n // σ x ≠ x}, (h x).val = f x := hval
    have hfD : ∀ x ∈ D, f x ∈ D := by
      intro x hx
      rw [← hval' ⟨x, (hD x).mp hx⟩]
      exact (hD _).mpr (h ⟨x, (hD x).mp hx⟩).property
    have hfinj : ∀ x ∈ D, ∀ y ∈ D, f x = f y → x = y := by
      intro x hx y hy he
      have hh : h ⟨x, (hD x).mp hx⟩ = h ⟨y, (hD y).mp hy⟩ :=
        Subtype.ext (by simpa only [hval'] using he)
      exact congrArg Subtype.val (h.injective hh)
    have hcontract : ∀ x ∈ D, τ x ∉ D → f x = x ∨ f x = σ x := by
      intro x hx ht
      have hfix : σ (τ x) = τ x := not_ne_iff.mp (by simpa [hD] using ht)
      simpa only [hval'] using hkeep ⟨x, (hD x).mp hx⟩ hfix
    have hdirect : ∀ x, τ x ∈ D → f x = τ x := by
      intro x hx; simp [f, (hD (τ x)).mp hx]
    let F := D.filter fun x => f x ∈ U
    let WU := U.filter fun x => f x ∈ U
    let XUV := U.filter fun x => f x ∉ U
    let XVU := V.filter fun x => f x ∈ U
    have hFcard : F.card = U.card := by
      apply card_bij (fun x _ => f x)
      · intro x hx; exact (mem_filter.mp hx).2
      · intro x hx y hy he
        exact hfinj x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 he
      · intro y hy
        let yD : {x : Fin n // σ x ≠ x} := ⟨y, (hD y).mp (hUD hy)⟩
        let x := h.symm yD
        have he : f x.val = y := by
          rw [← hval']
          exact congrArg Subtype.val (h.apply_symm_apply yD)
        exact ⟨x.val, mem_filter.mpr ⟨(hD _).mpr x.property, by simpa [he] using hy⟩, he⟩
    have hWU : WU.card + XUV.card = U.card := card_filter_add_card_filter_not _
    have hFsplit : WU.card + XVU.card = F.card := by
      have hp := card_filter_add_card_filter_not (s := F) (fun x => x ∈ U)
      have he1 : F.filter (fun x => x ∈ U) = WU := by
        ext x
        have hxD : x ∈ U → x ∈ D := fun hx => hUD hx
        simp only [F, WU, mem_filter]
        tauto
      have he2 : F.filter (fun x => x ∉ U) = XVU := by
        ext x; simp [F, XVU, V]; tauto
      rwa [he1, he2] at hp
    let UV := U.filter fun x => τ x ∈ V
    let VU := V.filter fun x => τ x ∈ U
    have heUV : XUV = UV := by
      ext x
      by_cases hx : x ∈ U
      · by_cases ht : τ x ∈ D
        · simp [XUV, UV, hx, hdirect x ht, V, ht]
        · have hfx : f x ∈ U := by
            rcases hcontract x (hUD hx) ht with he | he
            · simpa [he] using hx
            · rw [he]; exact (hUσ x).mpr hx
          simp [XUV, UV, hx, hfx, V, ht]
      · simp [XUV, UV, hx]
    have heVU : XVU = VU := by
      ext x
      by_cases hx : x ∈ V
      · by_cases ht : τ x ∈ D
        · simp [XVU, VU, hx, hdirect x ht]
        · have hfx : f x ∈ V := by
            rcases hcontract x (hVD hx) ht with he | he
            · simpa [he] using hx
            · rw [he]; exact hVσ x hx
          have hfnot : f x ∉ U := fun hu => hUV _ hu hfx
          have htnot : τ x ∉ U := fun hu => ht (hUD hu)
          simp [XVU, VU, hx, hfnot, htnot]
      · simp [XVU, VU, hx]
    have hcross : UV.card = VU.card := by
      rw [heUV] at hWU
      rw [heVU] at hFsplit
      omega
    let AU := U.filter fun x => τ x ∈ U
    let AV := V.filter fun x => τ x ∈ V
    let KU := U.filter fun x => τ x ∈ D
    let KV := V.filter fun x => τ x ∈ D
    let K := D.filter fun x => τ x ∈ D
    have hKU : AU.card + UV.card = KU.card := by
      have hp := card_filter_add_card_filter_not (s := KU) (fun x => τ x ∈ U)
      have he1 : KU.filter (fun x => τ x ∈ U) = AU := by
        ext x
        have hxD : τ x ∈ U → τ x ∈ D := fun hx => hUD hx
        simp only [KU, AU, mem_filter]; tauto
      have he2 : KU.filter (fun x => τ x ∉ U) = UV := by
        ext x; simp [KU, UV, V]; tauto
      rwa [he1, he2] at hp
    have hKV : VU.card + AV.card = KV.card := by
      have hp := card_filter_add_card_filter_not (s := KV) (fun x => τ x ∈ U)
      have he1 : KV.filter (fun x => τ x ∈ U) = VU := by
        ext x
        have hxD : τ x ∈ U → τ x ∈ D := fun hx => hUD hx
        simp only [KV, VU, mem_filter]; tauto
      have he2 : KV.filter (fun x => τ x ∉ U) = AV := by
        ext x; simp [KV, AV, V]; tauto
      rwa [he1, he2] at hp
    have hK : KU.card + KV.card = K.card := by
      have hp := card_filter_add_card_filter_not (s := K) (fun x => x ∈ U)
      have he1 : K.filter (fun x => x ∈ U) = KU := by
        ext x
        have hxD : x ∈ U → x ∈ D := fun hx => hUD hx
        simp only [K, KU, mem_filter]; tauto
      have he2 : K.filter (fun x => x ∉ U) = KV := by
        ext x; simp [K, KV, V]; tauto
      rwa [he1, he2] at hp
    have hkodd : Odd K.card := actual_moved_count_odd hn ρ hf hr hrs hrt hst
    have hwodd : Odd (AU.card + AV.card) := by
      rw [Nat.odd_iff] at hkodd ⊢
      omega
    exact hwodd

  let σ := relative ρ r s
  let D := movedSupport ρ r s
  let V := D \ U
  have hUσ : ∀ x, σ x ∈ U ↔ x ∈ U := by
    intro x
    constructor
    · intro hx
      rw [← hU] at hx
      obtain ⟨y, hy, he⟩ := mem_image.mp hx
      exact σ.injective he ▸ hy
    · intro hx
      rw [← hU]
      exact mem_image_of_mem σ hx
  have hVσ : ∀ x, x ∈ V → σ x ∈ V := by
    intro x hx
    have hxD : σ x ≠ x := by simpa [D, movedSupport, σ] using (mem_sdiff.mp hx).1
    apply mem_sdiff.mpr
    refine ⟨?_, fun hu => (mem_sdiff.mp hx).2 ((hUσ x).mp hu)⟩
    change σ x ∈ movedSupport ρ r s
    simp only [movedSupport, mem_filter, mem_univ, true_and]
    exact fun he => hxD (σ.injective he)
  have hpartition : U.card + V.card = D.card := by
    have hp := card_sdiff_add_card_eq_card hUD
    change V.card + U.card = D.card at hp
    omega
  have htotal : ∀ W : Finset (Fin n),
      (∑ t : Fin (2 * n), (W.filter fun x => relative ρ r t x ∈ W).card)
        = 2 * W.card ^ 2 := by
    intro W
    have hfrel : ∀ x p, ((univ : Finset (Fin (2 * n))).filter
        fun t => relative ρ r t x = p).card = 2 := by
      intro x p
      have he : ((univ : Finset (Fin (2 * n))).filter
          fun t => relative ρ r t x = p) = fibre ρ x (ρ r p) := by
        ext t
        simp only [mem_filter, mem_univ, true_and, fibre]
        constructor
        · intro h
          have h' := congrArg (ρ r) h
          simpa [relative] using h'
        · intro h
          simp [relative, h]
      rw [he]
      exact hf x (ρ r p)
    have hcol : ∀ x, ((univ : Finset (Fin (2 * n))).filter
        fun t => relative ρ r t x ∈ W).card = 2 * W.card := by
      intro x
      have hp := sum_card_fiberwise_eq_card_filter
        (univ : Finset (Fin (2 * n))) W (fun t => relative ρ r t x)
      rw [sum_congr rfl (fun p _ => hfrel x p)] at hp
      simpa [Nat.mul_comm] using hp.symm
    calc
      _ = ∑ t : Fin (2 * n), ∑ x ∈ W, if relative ρ r t x ∈ W then 1 else 0 := by
        apply sum_congr rfl
        intro t _
        rw [card_eq_sum_ones, sum_filter]
      _ = ∑ x ∈ W, ∑ t : Fin (2 * n), if relative ρ r t x ∈ W then 1 else 0 :=
        sum_comm
      _ = ∑ x ∈ W, 2 * W.card := by
        apply sum_congr rfl
        intro x _
        rw [← sum_filter, ← card_eq_sum_ones]
        exact hcol x
      _ = 2 * W.card ^ 2 := by simp [Nat.pow_two]; ring
  let B : Fin (2 * n) → ℕ := fun t =>
    (U.filter fun x => relative ρ r t x ∈ U).card +
    (V.filter fun x => relative ρ r t x ∈ V).card
  have hsum : (∑ t : Fin (2 * n), B t) = 2 * (U.card ^ 2 + V.card ^ 2) := by
    simp only [B, sum_add_distrib]
    rw [htotal, htotal]
    ring
  have hrB : B r = D.card := by
    have he : ∀ W : Finset (Fin n), (W.filter fun x => relative ρ r r x ∈ W) = W := by
      intro W; ext x; simp [relative]
    dsimp [B]
    rw [he, he]
    exact hpartition
  have hsB : B s = D.card := by
    have heU : (U.filter fun x => relative ρ r s x ∈ U) = U := by
      ext x
      simp only [mem_filter, and_iff_left_iff_imp]
      exact (hUσ x).mpr
    have heV : (V.filter fun x => relative ρ r s x ∈ V) = V := by
      ext x
      simp only [mem_filter, and_iff_left_iff_imp]
      exact hVσ x
    dsimp [B]
    rw [heU, heV]
    exact hpartition
  let T : Finset (Fin (2 * n)) := univ \ {r, s}
  have hTcard : T.card + 2 = 2 * n := by
    have hp := card_sdiff_add_card_eq_card (s := ({r, s} : Finset (Fin (2 * n))))
      (subset_univ _)
    simpa [T, hrs] using hp
  have hlow : T.card ≤ ∑ t ∈ T, B t := by
    calc
      T.card = ∑ _t ∈ T, 1 := by simp
      _ ≤ ∑ t ∈ T, B t := by
        apply sum_le_sum
        intro t ht
        have htr : r ≠ t := by
          have hm := (mem_sdiff.mp ht).2
          intro he; apply hm; simp [← he]
        have hts : s ≠ t := by
          have hm := (mem_sdiff.mp ht).2
          intro he; apply hm; simp [← he]
        have ho : Odd (B t) := actual_block_count_odd hn ρ hf hr hrs htr hts U hUD hUσ
        have hm := Nat.odd_iff.mp ho
        omega
  have hsep : (∑ t ∈ T, B t) + (B r + B s) = ∑ t : Fin (2 * n), B t := by
    have hp := sum_sdiff (f := B) (show ({r, s} : Finset (Fin (2 * n))) ⊆ univ from subset_univ _)
    simpa [T, hrs] using hp
  rw [hrB, hsB, hsum] at hsep
  change n + D.card ≤ U.card ^ 2 + V.card ^ 2 + 1
  omega

end D5.S3.Combinatorics.Graph.URSRelativeCyclePartition
