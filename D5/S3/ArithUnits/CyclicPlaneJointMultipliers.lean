/- GID: D5/S3/ArithUnits/CyclicPlaneJointMultipliers
   generality: I
   mirror-B: D5/B/S3/ArithUnits/CyclicPlaneJointMultipliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint multiplier-two and multiplier-three invariance forces the four trivial subsets modulo 157. -/

import D5.S3.ArithUnits.CyclicPlaneThreeMultiplierObstruction

/-! Joint multiplier-two and multiplier-three orbit classification modulo 157. -/

namespace D5.S3.ArithUnits.CyclicPlaneJointMultipliers

open D5.S3.ArithUnits.CyclicPlaneTwelveMultiplierObstruction
open D5.S3.ArithUnits.CyclicPlaneThreeMultiplierObstruction

private def twoUnit157 : (ZMod 157)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num)

private def threeUnit157 : (ZMod 157)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

private theorem orderOf_twoUnit157 : orderOf twoUnit157 = 52 := by
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  calc
    orderOf twoUnit157 = orderOf ((twoUnit157 : (ZMod 157)ˣ) : ZMod 157) :=
      (orderOf_injective (Units.coeHom (ZMod 157)) Units.val_injective
        twoUnit157).symm
    _ = orderOf (2 : ZMod 157) := by simp [twoUnit157]
    _ = 52 := orderOf_two_zmod157

private theorem orderOf_threeUnit157 : orderOf threeUnit157 = 78 := by
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  calc
    orderOf threeUnit157 = orderOf ((threeUnit157 : (ZMod 157)ˣ) : ZMod 157) :=
      (orderOf_injective (Units.coeHom (ZMod 157)) Units.val_injective
        threeUnit157).symm
    _ = orderOf (3 : ZMod 157) := by simp [threeUnit157]
    _ = 78 := orderOf_three_zmod157

/-- The two cyclic orbit periods combine to the full nonzero period `156`. -/
theorem joint_nonzero_card_dvd (S : Finset (ZMod 157))
    (hinv₂ : S.image (fun x => 2 * x) = S)
    (hinv₃ : S.image (fun x => 3 * x) = S) :
    156 ∣ (S.erase 0).card := by
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  have hinv₂' : S.image (fun x => (twoUnit157 : ZMod 157) * x) = S := by
    simpa [twoUnit157] using hinv₂
  have hinv₃' : S.image (fun x => (threeUnit157 : ZMod 157) * x) = S := by
    simpa [threeUnit157] using hinv₃
  have h₂ := orderOf_dvd_card_erase_zero_of_image_mul_eq twoUnit157 S hinv₂'
  have h₃ := orderOf_dvd_card_erase_zero_of_image_mul_eq threeUnit157 S hinv₃'
  rw [orderOf_twoUnit157] at h₂
  rw [orderOf_threeUnit157] at h₃
  have hL := Nat.lcm_dvd h₂ h₃
  norm_num at hL ⊢
  exact hL

/-- Joint invariance leaves only residues zero and one modulo the full nonzero period. -/
theorem joint_invariant_cardinality_residue (S : Finset (ZMod 157))
    (hinv₂ : S.image (fun x => 2 * x) = S)
    (hinv₃ : S.image (fun x => 3 * x) = S) :
    S.card % 156 ∈ ({0, 1} : Set Nat) := by
  have hd := joint_nonzero_card_dvd S hinv₂ hinv₃
  by_cases hzero : (0 : ZMod 157) ∈ S
  · have hcard := Finset.card_erase_add_one hzero
    obtain ⟨k, hk⟩ := hd
    rw [← hcard, hk]
    simp [Nat.add_mod]
  · rw [Finset.erase_eq_of_notMem hzero] at hd
    simp [Nat.mod_eq_zero_of_dvd hd]

/-- A set invariant under both multipliers is empty, `{0}`, the nonzero field,
or the whole field. This is the orbit classification for the subgroup generated
by `2` and `3`, whose order is `lcm 52 78 = 156`. -/
theorem joint_invariant_classification (S : Finset (ZMod 157))
    (hinv₂ : S.image (fun x => 2 * x) = S)
    (hinv₃ : S.image (fun x => 3 * x) = S) :
    S = ∅ ∨ S = {0} ∨ S = Finset.univ.erase 0 ∨ S = Finset.univ := by
  have hd := joint_nonzero_card_dvd S hinv₂ hinv₃
  have hle : S.card ≤ 157 := by
    simpa using (Finset.card_le_univ S)
  by_cases hzero : (0 : ZMod 157) ∈ S
  · have hcard := Finset.card_erase_add_one hzero
    obtain ⟨k, hk⟩ := hd
    have hmod : S.card % 156 = 1 := by
      rw [← hcard, hk]
      simp [Nat.add_mod]
    have hcases : S.card = 1 ∨ S.card = 157 := by omega
    rcases hcases with hone | hfull
    · right
      left
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
      have ha0 : a = 0 := by
        have h0a : (0 : ZMod 157) = a := by simpa [ha] using hzero
        simpa [Finset.mem_singleton] using h0a.symm
      simpa [ha0] using ha
    · right
      right
      right
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simp [hfull])
  · obtain ⟨k, hk⟩ := hd
    rw [Finset.erase_eq_of_notMem hzero] at hk
    have hmod : S.card % 156 = 0 := by
      rw [hk]
      exact Nat.mod_eq_zero_of_dvd (by simpa using hd)
    have hcases : S.card = 0 ∨ S.card = 156 := by omega
    rcases hcases with hempty | hnonzero
    · left
      exact Finset.card_eq_zero.mp hempty
    · right
      right
      left
      apply Finset.eq_of_subset_of_card_le
        (fun x hx => by
          rw [Finset.mem_erase]
          exact ⟨fun hx0 => hzero (hx0 ▸ hx), Finset.mem_univ _⟩)
      simp [hnonzero]

#print axioms joint_nonzero_card_dvd
#print axioms joint_invariant_cardinality_residue
#print axioms joint_invariant_classification

end D5.S3.ArithUnits.CyclicPlaneJointMultipliers
