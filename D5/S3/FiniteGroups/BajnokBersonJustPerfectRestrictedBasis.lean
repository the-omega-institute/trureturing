/- GID: D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bajnok--Berson--Just Question 6 is proved for finite abelian groups. -/

/- proof_shape: IsPerfectRestrictedBasis: definition; escape_witness: none; admission_basis: open-problem-resolution (#19526; Proved)
   proof_shape: claim: definition; escape_witness: none; basis: module admission_basis above
   proof_shape: even_card_of_ninvolution: bind-only; escape_witness: none; consumer: result; basis: module admission_basis above
   proof_shape: card_le_of_subset_ne: bind-only; escape_witness: none; consumer: result; basis: module admission_basis above
   proof_shape: toggle_ne: bind-only; escape_witness: none; consumer: result; basis: module admission_basis above
   proof_shape: toggle_involutive: bind-only; escape_witness: none; consumer: result; basis: module admission_basis above
   proof_shape: result: content; escape_witness: result (coset-fiber toggle parity and bijection); basis: module admission_basis above
   Direct frozen dependencies (even_card_of_ninvolution and result):
   GID D5/S3/PrimeForms/Crossing/GlideCrossingParity.glide_crossing_count_even;
   statement_id sha256:fe94679447dd7dce2f59e682f3c19feada6dc543da3167847ed3a9ba247e8f57.
   Direct frozen dependencies (all other declarations): none.
   Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/19735.
   The claim keeps the preregistered subset expression; the proof uses the Mathlib finite sum directly.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import D5.S3.PrimeForms.Crossing.GlideCrossingParity

namespace D5.S3.FiniteGroups.BajnokBersonJustPerfectRestrictedBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

def IsPerfectRestrictedBasis {G : Type*} [AddCommGroup G] [DecidableEq G] (s : ℕ) (A : Finset G) : Prop :=
  ∀ g : G, ∃! T : Finset G, T ⊆ A ∧ T.card ≤ s ∧ ∑ x ∈ T, x = g

def claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (s : ℕ) (A : Finset G),
    1 ≤ s → A.card = s + 1 → IsPerfectRestrictedBasis s A → IsAddCyclic G

private lemma even_card_of_ninvolution {α : Type*} [Fintype α]
    (f : α → α) (hinv : ∀ x, f (f x) = x) (hfixed : ∀ x, f x ≠ x) :
    Even (Fintype.card α) := by
  exact D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even f hinv hfixed

private lemma card_le_of_subset_ne {G : Type*} [DecidableEq G] {s : ℕ}
    {T A : Finset G} (hsub : T ⊆ A) (hne : T ≠ A) (hA : A.card = s + 1) : T.card ≤ s := by
  exact Nat.le_of_lt_succ (by
    simpa only [Nat.succ_eq_add_one, hA] using
      (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)))

private lemma toggle_ne {G : Type*} [DecidableEq G] (a : G) (T : Finset G) :
    (if a ∈ T then T.erase a else insert a T) ≠ T := by
  by_cases h : a ∈ T
  · simpa only [if_pos h] using (Finset.erase_ne_self.mpr h)
  · simpa only [if_neg h] using (Finset.insert_ne_self.mpr h)

private lemma toggle_involutive {G : Type*} [DecidableEq G] (a : G) (T : Finset G) :
    (if a ∈ (if a ∈ T then T.erase a else insert a T) then
        (if a ∈ T then T.erase a else insert a T).erase a
      else insert a (if a ∈ T then T.erase a else insert a T)) = T := by
  by_cases h : a ∈ T
  · simpa only [if_pos h, Finset.notMem_erase, if_false] using Finset.insert_erase h
  · simpa only [if_neg h, Finset.mem_insert_self, if_true] using Finset.erase_insert h

 theorem result : claim := by
  classical
  intro G _ _ _ s A hs hA hbasis
  have hApos : 0 < A.card := Nat.lt_of_sub_eq_succ hA
  have hAne : A.Nonempty := Finset.card_pos.mp hApos
  let D := {T : Finset G // T ⊆ A ∧ T.card ≤ s}
  let fD : D → G := fun T => (∑ x ∈ T.1, x)
  have hfD_bij : Function.Bijective fD := by
    constructor
    · intro T U heq
      apply Subtype.ext
      have hu := (hbasis ((∑ x ∈ T.1, x))).unique
        ⟨T.property.1, T.property.2, rfl⟩
        ⟨U.property.1, U.property.2, heq.symm⟩
      exact hu
    · intro g
      obtain ⟨T, hT, hTu⟩ := hbasis g
      exact ⟨⟨T, hT.1, hT.2.1⟩, hT.2.2⟩
  let eDG : D ≃ G := Equiv.ofBijective fD hfD_bij
  have eDQ : D ≃ {T : Finset G // T ∈ A.powerset.erase A} :=
    Equiv.subtypeEquiv (Equiv.refl (Finset G)) (by
      intro T
      constructor
      · intro hT
        have hTA : T ∈ A.powerset := Finset.mem_powerset.mpr hT.1
        have hne : T ≠ A := by
          intro heq
          subst T
          omega
        exact Finset.mem_erase.mpr ⟨hne, hTA⟩
      · intro hT
        have hTA := (Finset.mem_erase.mp hT).2
        have hne := (Finset.mem_erase.mp hT).1
        have hsub : T ⊆ A := Finset.mem_powerset.mp hTA
        exact ⟨hsub, card_le_of_subset_ne hsub hne hA⟩)
  have hcardG : Fintype.card G = 2 ^ A.card - 1 := by
    calc
      Fintype.card G = Fintype.card D := (Fintype.card_congr eDG).symm
      _ = Fintype.card {T : Finset G // T ∈ A.powerset.erase A} := Fintype.card_congr eDQ
      _ = (A.powerset.erase A).card := by exact Fintype.card_coe _
      _ = A.powerset.card - 1 := by rw [Finset.card_erase_of_mem (by simp)]
      _ = 2 ^ A.card - 1 := by rw [Finset.card_powerset]
  have hpowEven : Even (2 ^ A.card) := even_two.pow_of_ne_zero (Nat.ne_of_gt hApos)
  have hpow_le : 1 ≤ 2 ^ A.card := Nat.one_le_two_pow
  have hoddG : Odd (Nat.card G) := by
    rw [Nat.card_eq_fintype_card, hcardG]
    exact Nat.Even.sub_odd hpow_le hpowEven odd_one
  obtain ⟨a, ha⟩ := hAne
  let H : AddSubgroup G := AddSubgroup.zmultiples a
  have hoddH : Odd (Nat.card H) := hoddG.of_dvd_nat (AddSubgroup.card_addSubgroup_dvd_card H)
  have hgen : H = ⊤ := by
    by_contra hHtop
    have hb_exists : ∃ b : G, b ∉ H := SetLike.exists_notMem_of_ne_top H hHtop
    obtain ⟨b, hb⟩ := hb_exists
    have contradiction_of : ∀ (c : G), (∑ x ∈ A, x) - c ∉ H → False := by
      intro c hfull
      let α := {T : Finset G // T ⊆ A ∧ (∑ x ∈ T, x) - c ∈ H}
      let t : Finset G → Finset G := fun T => if a ∈ T then T.erase a else insert a T
      have ht_subset : ∀ T : Finset G, T ⊆ A → t T ⊆ A := by
        intro T hT
        by_cases hm : a ∈ T
        · simpa [t, hm] using (Finset.erase_subset _ _).trans hT
        · simpa [t, hm] using Finset.insert_subset_iff.mpr ⟨ha, hT⟩
      have ht_inv : ∀ T : Finset G, t (t T) = T := by
        intro T
        dsimp [t]
        exact toggle_involutive a T
      have ht_ne : ∀ T : Finset G, t T ≠ T := by
        intro T
        exact toggle_ne a T
      have haH : a ∈ H := AddSubgroup.mem_zmultiples a
      have ht_sum : ∀ T : Finset G,
          (∑ x ∈ (t T), x) = if a ∈ T then (∑ x ∈ T, x) - a else (∑ x ∈ T, x) + a := by
        intro T
        by_cases hm : a ∈ T
        · have he := Finset.sum_erase_add T (fun x : G => x) hm
          dsimp [t]
          simp only [hm, if_true]
          rw [← he]
          abel
        · simpa [t, hm, add_comm]
      have ht_coset : ∀ T : Finset G, T ⊆ A → (∑ x ∈ T, x) - c ∈ H →
          (∑ x ∈ (t T), x) - c ∈ H := by
        intro T hT hTC
        by_cases hm : a ∈ T
        · have heq : (∑ x ∈ (t T), x) - c = ((∑ x ∈ T, x) - c) - a := by
            rw [ht_sum T]
            simp only [hm, if_true]
            exact sub_right_comm _ _ _
          rw [heq]
          exact H.sub_mem hTC haH
        · have heq : (∑ x ∈ (t T), x) - c = ((∑ x ∈ T, x) - c) + a := by
            rw [ht_sum T]
            simp only [hm, if_false]
            exact add_sub_right_comm _ _ _
          rw [heq]
          exact H.add_mem hTC haH
      let toggle : α → α := fun T =>
        ⟨t T.1, ht_subset T.1 T.property.1, ht_coset T.1 T.property.1 T.property.2⟩
      have htoggle_inv : ∀ T : α, toggle (toggle T) = T := by
        intro T
        apply Subtype.ext
        exact ht_inv T.1
      have htoggle_ne : ∀ T : α, toggle T ≠ T := by
        intro T hEq
        apply toggle_ne a T.1
        exact congrArg Subtype.val hEq
      have heven : Even (Fintype.card α) := even_card_of_ninvolution toggle htoggle_inv htoggle_ne
      have hTcard : ∀ T : α, T.1.card ≤ s := by
        intro T
        have hne : T.1 ≠ A := by
          intro heq
          apply hfull
          simpa [heq] using T.property.2
        exact card_le_of_subset_ne T.property.1 hne hA
      let fα : α → H := fun T => ⟨(∑ x ∈ T.1, x) - c, T.property.2⟩
      have hfα_bij : Function.Bijective fα := by
        constructor
        · intro T U heq
          apply Subtype.ext
          have heq' : (∑ x ∈ T.1, x) - c = (∑ x ∈ U.1, x) - c := congrArg Subtype.val heq
          have hsum : (∑ x ∈ T.1, x) = (∑ x ∈ U.1, x) := by
            have := congrArg (fun z : G => z + c) heq'
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
          exact (hbasis ((∑ x ∈ T.1, x))).unique
            ⟨T.property.1, hTcard T, rfl⟩
            ⟨U.property.1, hTcard U, hsum.symm⟩
        · intro h
          let g : G := c + (h : G)
          obtain ⟨T, hT, hTu⟩ := hbasis g
          have hne : T ≠ A := by
            intro heq
            apply hfull
            have hsumA : (∑ x ∈ A, x) = g := by simpa [heq] using hT.2.2
            rw [hsumA]
            simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.property
          have hcard : T.card ≤ s := card_le_of_subset_ne hT.1 hne hA
          have hTC : (∑ x ∈ T, x) - c ∈ H := by
            change (∑ x ∈ T, x) - c ∈ H
            rw [hT.2.2]
            simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.property
          refine ⟨⟨T, hT.1, hTC⟩, ?_⟩
          apply Subtype.ext
          change (∑ x ∈ T, x) - c = (h : G)
          have hsum : (∑ x ∈ T, x) = g := by simpa only [] using hT.2.2
          rw [hsum]
          simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.property
      let eαH : α ≃ H := Equiv.ofBijective fα hfα_bij
      have hcardα : Fintype.card α = Nat.card H := by
        calc
          Fintype.card α = Fintype.card H := Fintype.card_congr eαH
          _ = Nat.card H := (Nat.card_eq_fintype_card).symm
      have hevenH : Even (Nat.card H) := by simpa [hcardα] using heven
      exact (Nat.not_even_iff_odd.mpr hoddH) hevenH
    by_cases hsumA : (∑ x ∈ A, x) ∈ H
    · have hfull : (∑ x ∈ A, x) - b ∉ H := by
        intro hdiff
        apply hb
        have hsub := H.sub_mem hsumA hdiff
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
      exact False.elim (contradiction_of b hfull)
    · have hfull : (∑ x ∈ A, x) - 0 ∉ H := by simpa using hsumA
      exact False.elim (contradiction_of 0 hfull)
  exact isAddCyclic_iff_exists_zmultiples_eq_top.mpr ⟨a, hgen⟩


end D5.S3.FiniteGroups.BajnokBersonJustPerfectRestrictedBasis
