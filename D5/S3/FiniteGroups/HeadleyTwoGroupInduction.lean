/- GID: D5/S3/FiniteGroups/HeadleyTwoGroupInduction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyTwoGroupInduction
   mirror-E: none(waiver:two-primary-induction)
   anchors: []
   utility: none
   digest: R-cycles for every finite noncyclic additive abelian two-group. -/

import D5.S3.FiniteGroups.HeadleyCoordinateCases
import D5.S3.FiniteGroups.HeadleyTwoGroupNormalization
import D5.S3.FiniteGroups.HeadleyOddProduct
import D5.S3.FiniteGroups.HeadleyRankTwoLift

/-! Strict induction on the full exponent sum, with all elementary and order-eight leaves. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyTwoGroupInduction
open HeadleyCoordinateKernel HeadleyDoubledCoordinates HeadleyCoordinateCases
open HeadleyElementaryCycles HeadleyTwoGroupNormalization HeadleyExtension

private theorem coordinate_r_cycle {r : ℕ} (e : Fin r → ℕ)
    (htwo : ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j) : Nonempty (RCycle (Coordinates e)) := by
  classical
  suffices h : ∀ s : ℕ, ∀ (r : ℕ) (e : Fin r → ℕ), (∑ k, e k) = s →
      (∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j) → Nonempty (RCycle (Coordinates e)) by
    exact h (∑ k, e k) r e rfl htwo
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro r e hsum htwo
    by_cases hthin : ∃ i j, i ≠ j ∧ e i = 1 ∧ 0 < e j ∧
        ∀ k, k ≠ i → k ≠ j → e k = 0
    · obtain ⟨i,j,hij,hi,hj,hz⟩ := hthin
      let E : Coordinates e ≃+ ZMod 2 × ZMod (2 ^ e j) :=
        (twoCoordinatesEquiv e i j hij.symm hz).trans
          (AddEquiv.prodCongr (ZMod.ringEquivCongr (by simp [hi])).toAddEquiv
            (AddEquiv.refl _))
      by_cases hj1 : e j = 1
      · let T : Coordinates e ≃+ ZMod 2 × ZMod 2 := E.trans (AddEquiv.prodCongr (AddEquiv.refl _)
          (ZMod.ringEquivCongr (by simp [hj1])).toAddEquiv)
        exact ⟨transportCycle T.symm e4RStar.toRCycle⟩
      by_cases hj2 : e j = 2
      · let T : Coordinates e ≃+ ZMod 2 × ZMod 4 := E.trans (AddEquiv.prodCongr (AddEquiv.refl _)
          (ZMod.ringEquivCongr (by simp [hj2])).toAddEquiv)
        exact ⟨transportCycle T.symm c2c4Cycle⟩
      · have hj3 : 3 ≤ e j := by omega
        exact ⟨transportCycle E.symm (HeadleyRankTwoLift.powerTwoRStar (e j) hj3).toRCycle⟩
    · by_cases hel : ∀ k, 0 < e k → e k = 1
      · exact ⟨elementaryCoordinates e hel htwo⟩
      obtain ⟨i,j,hij,hi,hj,htwo'⟩ := recursive_pair e htwo hel hthin
      have hdec := lower_sum_add_two e i j hij hi hj
      have hlt : (∑ k, lower e i j k) < s := by omega
      obtain ⟨rsmall⟩ := ih (∑ k, lower e i j k) hlt r (lower e i j) rfl htwo'
      let N := (quotientHom e i j hij.symm hi hj).ker
      letI : Fintype N := Fintype.ofFinite N
      letI : Fintype (Coordinates e ⧸ N) := Fintype.ofFinite _
      let rN : RCycle N := transportCycle (kernelEquiv e i j hij.symm hi hj).symm rsmall
      let rQ : RStar (Coordinates e ⧸ N) :=
        HeadleyOddProduct.transportRStar (quotientEquiv e i j hij.symm hi hj) e4RStar
      exact nonsplit_extension_r_cycle N rN rQ

/-- Every finite noncyclic additive abelian two-group has an actual R-cycle. Both
C2 cubed and C2 times C4 are included as R-only leaves of the induction. -/
theorem finite_noncyclic_two_group_r_cycle (G : Type*) [AddCommGroup G] [Finite G]
    (hG : IsPGroup 2 (Multiplicative G)) (hn : ¬ IsAddCyclic G) :
    Nonempty (RCycle G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨r,e,⟨E⟩,htwo⟩ := coordinate_presentation G hG hn
  obtain ⟨R⟩ := coordinate_r_cycle e htwo
  exact ⟨transportCycle E.symm R⟩

end D5.S3.FiniteGroups.HeadleyTwoGroupInduction
