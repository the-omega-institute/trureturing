/- GID: D5/S3/Combinatorics/Circle/FourNegativeSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegativeSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Physical positive flux excludes four negative LARGE labels at an original minimum. -/
module
public import D5.S3.Combinatorics.Circle.BinaryRunSource
public import D5.S3.Combinatorics.Circle.FirstNegativeShiftExchange

/-! Positive supply is counted on physical labels, including repeated values and zero.
The original arbitrary signed-prefix minimum has at least five negative LARGE labels.
The remaining branches of Circle C3.1 are open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.FourNegativeSource
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open TwoOppositeLargeExchange ThreeLargePacketExchange BinaryRunSource
open scoped BigOperators

/-- A finite centered-doubling permutation balances the LARGE sign crossings.
Its positive SMALL mass is exactly the excess of positive LARGE mass over the
positive arrivals from negative LARGE labels. No orbit or value injectivity is assumed. -/
theorem permutation_doubleStep_positive_flux
    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Equiv.Perm α) (f : α → ℤ) (q : ℤ)
    (hq : 0 < q)
    (hbound : ∀ i, -(2 * q - 1) ≤ f i ∧ f i ≤ 2 * q - 1)
    (hstep : ∀ i, f (ρ i) = doubleStep (4 * q - 1) (f i)) :
    let SP := Finset.univ.filter (fun i => 0 < f i ∧ f i < q)
    let PL := Finset.univ.filter (fun i => q ≤ f i)
    let NL := Finset.univ.filter (fun i => f i ≤ -q)
    PL.card = NL.card ∧
      (∑ i ∈ SP, f i) + (∑ i ∈ NL, f (ρ i)) = ∑ i ∈ PL, f i := by
  classical
  dsimp only
  let SP := Finset.univ.filter (fun i => 0 < f i ∧ f i < q)
  let PL := Finset.univ.filter (fun i => q ≤ f i)
  let NL := Finset.univ.filter (fun i => f i ≤ -q)
  let Pos := Finset.univ.filter (fun i => 0 < f i)
  have hpos (i : α) : 0 < f (ρ i) ↔ (0 < f i ∧ f i < q) ∨ f i ≤ -q := by
    rw [hstep]
    have hb := hbound i
    unfold doubleStep
    split_ifs <;> omega
  have hsmall (i : α) (hi : i ∈ SP) : f (ρ i) = 2 * f i := by
    have hi' : 0 < f i ∧ f i < q := (Finset.mem_filter.mp hi).2
    rw [hstep, doubleStep, if_neg (by omega), if_neg (by omega)]
  have hd1 : Disjoint SP PL := by
    simp only [Finset.disjoint_left, SP, PL, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hd2 : Disjoint SP NL := by
    simp only [Finset.disjoint_left, SP, NL, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hp1 : Pos = SP ∪ PL := by
    ext i
    simp only [Pos, SP, PL, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hp2 : Pos = (SP ∪ NL).image ρ := by
    ext i
    constructor
    · intro hi
      refine Finset.mem_image.mpr ⟨ρ.symm i, ?_, ρ.apply_symm_apply i⟩
      have hh : 0 < f (ρ (ρ.symm i)) := by simpa [Pos] using hi
      simpa only [SP, NL, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] using (hpos (ρ.symm i)).mp hh
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hh : (0 < f j ∧ f j < q) ∨ f j ≤ -q := by
        simpa only [SP, NL, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and] using hj
      simpa only [Pos, Finset.mem_filter, Finset.mem_univ, true_and] using (hpos j).mpr hh
  have hc1 : Pos.card = SP.card + PL.card := by rw [hp1, Finset.card_union_of_disjoint hd1]
  have hc2 : Pos.card = SP.card + NL.card := by
    rw [hp2, Finset.card_image_of_injective _ ρ.injective, Finset.card_union_of_disjoint hd2]
  have hs1 : (∑ i ∈ Pos, f i) = (∑ i ∈ SP, f i) + ∑ i ∈ PL, f i := by
    rw [hp1, Finset.sum_union hd1]
  have hs2 : (∑ i ∈ Pos, f i) = 2 * (∑ i ∈ SP, f i) + ∑ i ∈ NL, f (ρ i) := by
    rw [hp2, Finset.sum_image (fun _ _ _ _ h => ρ.injective h), Finset.sum_union hd2]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hsmall
  exact ⟨by omega, by omega⟩

end D5.S3.Combinatorics.Circle.FourNegativeSource
