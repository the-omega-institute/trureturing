/- GID: D5/S3/FiniteGroups/HeadleyTwoGroupNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyTwoGroupNormalization
   mirror-E: none(waiver:two-primary-presentation)
   anchors: []
   utility: none
   digest: Two-primary coordinate presentations with the noncyclicity invariant discharged. -/

import D5.S3.FiniteGroups.HeadleyCoordinateKernel
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.DirectSum.Basic

/-! Normalize abstract finite abelian two-groups without assuming positive exponents. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyTwoGroupNormalization
open HeadleyCoordinateKernel Function

private theorem two_positive_of_noncyclic {r : ℕ} (e : Fin r → ℕ)
    (hn : ¬ IsAddCyclic (Coordinates e)) :
    ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j := by
  classical
  by_contra hbad
  by_cases hex : ∃ i, 0 < e i
  · obtain ⟨i, hi⟩ := hex
    have hz (k : Fin r) (hki : k ≠ i) : e k = 0 := by
      by_contra hk
      exact hbad ⟨i, k, hki.symm, hi, Nat.pos_of_ne_zero hk⟩
    have hinj : Injective (Pi.evalAddMonoidHom (fun k => ZMod (2 ^ e k)) i) := by
      intro x y hxy
      funext k
      by_cases hki : k = i
      · subst k
        exact hxy
      · haveI : Subsingleton (ZMod (2 ^ e k)) := by
          rw [hz k hki, pow_zero]
          infer_instance
        exact Subsingleton.elim _ _
    exact hn (isAddCyclic_of_injective _ hinj)
  · have hz (k : Fin r) : e k = 0 := by
      by_contra hk
      exact hex ⟨k, Nat.pos_of_ne_zero hk⟩
    letI : Subsingleton (Coordinates e) := ⟨fun x y => by
      funext k
      haveI : Subsingleton (ZMod (2 ^ e k)) := by rw [hz k, pow_zero]; infer_instance
      exact Subsingleton.elim _ _⟩
    exact hn inferInstance

/-- Every finite abelian two-group has a two-primary coordinate presentation; noncyclicity
forces two distinct positive factors. No positivity is imposed on the other factors. -/
theorem coordinate_presentation (G : Type*) [AddCommGroup G] [Finite G]
    (hG : IsPGroup 2 (Multiplicative G)) (hn : ¬ IsAddCyclic G) :
    ∃ (r : ℕ) (e : Fin r → ℕ),
      Nonempty (G ≃+ Coordinates e) ∧ ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j := by
  classical
  obtain ⟨n, hncard⟩ := IsPGroup.iff_card.mp hG
  change Nat.card G = 2 ^ n at hncard
  obtain ⟨ι, fι, p, hp, e, ⟨E⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  let P := E.trans (DirectSum.addEquivProd _)
  have hc : (∏ i, p i ^ e i) = 2 ^ n := by
    calc
      (∏ i, p i ^ e i) = Nat.card (∀ i, ZMod (p i ^ e i)) := by
        simp [Nat.card_pi]
      _ = Nat.card G := (Nat.card_congr P.toEquiv).symm
      _ = 2 ^ n := hncard
  have hm (i : ι) : p i ^ e i = 2 ^ e i := by
    by_cases he : e i = 0
    · simp [he]
    · have hd : p i ∣ 2 ^ n := by
        rw [← hc]
        exact (dvd_pow_self (p i) he).trans
          (Finset.dvd_prod_of_mem (fun i => p i ^ e i) (Finset.mem_univ i))
      rw [Nat.prime_eq_prime_of_dvd_pow (hp i) Nat.prime_two hd]
  let T := P.trans (AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (hm i)).toAddEquiv)
  let f := (Fintype.equivFin ι).symm
  let U := T.trans ((RingEquiv.piCongrLeft (fun i => ZMod (2 ^ e i)) f).toAddEquiv).symm
  refine ⟨Fintype.card ι, fun i => e (f i), ⟨U⟩, ?_⟩
  apply two_positive_of_noncyclic
  intro hcyc
  letI := hcyc
  exact hn (isAddCyclic_of_surjective U.symm.toAddMonoidHom U.symm.surjective)

end D5.S3.FiniteGroups.HeadleyTwoGroupNormalization
