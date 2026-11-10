/- GID: D5/S3/ArithUnits/CyclicPlaneThreeMultiplierObstruction
   generality: I
   mirror-B: D5/B/S3/ArithUnits/CyclicPlaneThreeMultiplierObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The second multiplier-three orbit obstruction modulo 157. -/

import D5.S3.ArithUnits.CyclicPlaneTwelveMultiplierObstruction

namespace D5.S3.ArithUnits.CyclicPlaneThreeMultiplierObstruction

open D5.S3.ArithUnits.CyclicPlaneTwelveMultiplierObstruction

/-- The multiplicative order of three in the prime residue field `ZMod 157` is 78. -/
theorem orderOf_three_zmod157 : orderOf (3 : ZMod 157) = 78 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 157))
    (n := 78) (by norm_num) ?_ ?_
  · decide
  · intro q hq hq78
    have hqne : q ≠ 1 := hq.ne_one
    have hqle : q ≤ 78 := Nat.le_of_dvd (by norm_num) hq78
    interval_cases q
    all_goals norm_num at hqne
    all_goals norm_num at hq78
    all_goals decide

private def threeUnit157 : (ZMod 157)ˣ :=
  ZMod.unitOfCoprime 3 (by norm_num)

/-- A finite set invariant under multiplication by three has one possible fixed
point, zero; every nonzero point lies in a free orbit of length 78. -/
theorem card_of_invariant_under_mul_three (S : Finset (ZMod 157))
    (hinv : S.image (fun x => 3 * x) = S) :
    S.card % 78 ∈ ({0, 1} : Set Nat) := by
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  have hu : orderOf threeUnit157 = 78 := by
    calc
      orderOf threeUnit157 =
          orderOf ((threeUnit157 : (ZMod 157)ˣ) : ZMod 157) :=
        (orderOf_injective (Units.coeHom (ZMod 157)) Units.val_injective
          threeUnit157).symm
      _ = orderOf (3 : ZMod 157) := by simp [threeUnit157]
      _ = 78 := orderOf_three_zmod157
  have hinv' : S.image (fun x => (threeUnit157 : ZMod 157) * x) = S := by
    simpa [threeUnit157] using hinv
  have hd := orderOf_dvd_card_erase_zero_of_image_mul_eq threeUnit157 S hinv'
  rw [hu] at hd
  by_cases hzero : (0 : ZMod 157) ∈ S
  · have hcard := Finset.card_erase_add_one hzero
    obtain ⟨k, hk⟩ := hd
    rw [← hcard, hk]
    simp [Nat.add_mod]
  · rw [Finset.erase_eq_of_notMem hzero] at hd
    simp [Nat.mod_eq_zero_of_dvd hd]

/-- No thirteen-element subset of `ZMod 157` can be carried to a translate
of itself by the multiplier three. The proof is the orbit obstruction, after
conjugating the affine relation to a fixed-point invariant relation. -/
theorem multiplier_three_obstruction (D : Finset (ZMod 157))
    (hcard : D.card = 13) (g : ZMod 157) :
    D.image (fun x => 3 * x) ≠ D.image (fun x => x + g) := by
  intro hrel
  letI : DecidableEq (ZMod 157) := Classical.decEq _
  rw [Subsingleton.elim (ZMod.decidableEq 157) (Classical.decEq (ZMod 157))] at hrel
  let center : ZMod 157 := 79 * g
  have hfixed : (3 : ZMod 157) * center = center + g := by
    dsimp [center]
    calc
      (3 : ZMod 157) * (79 * g) = ((3 : ZMod 157) * 79) * g := by ring
      _ = (237 : ZMod 157) * g := by rfl
      _ = (80 : ZMod 157) * g := by
        rw [show (237 : ZMod 157) = 80 by
          change ((237 : ℕ) : ZMod 157) = ((80 : ℕ) : ZMod 157)
          rw [ZMod.natCast_eq_natCast_iff]
          decide]
      _ = 79 * g + g := by ring
  let S := D.image (fun x => x - center)
  have hinv : S.image (fun x => 3 * x) = S := by
    exact affine_multiplier_conjugacy D 3 g center hfixed hrel
  have hSCard : S.card = 13 := by
    rw [show S = D.image (fun x => x - center) by rfl,
      Finset.card_image_of_injective]
    · exact hcard
    · intro x y hxy
      simpa using congrArg (fun z => z + center) hxy
  have hinvDefault :
      @Finset.image (ZMod 157) (ZMod 157) (ZMod.decidableEq 157)
          (fun x => 3 * x) S = S := by
    rw [Subsingleton.elim (ZMod.decidableEq 157) (Classical.decEq (ZMod 157))]
    exact hinv
  have hmod := card_of_invariant_under_mul_three S hinvDefault
  rw [hSCard] at hmod
  norm_num at hmod

#print axioms orderOf_three_zmod157
#print axioms card_of_invariant_under_mul_three
#print axioms multiplier_three_obstruction

end D5.S3.ArithUnits.CyclicPlaneThreeMultiplierObstruction
