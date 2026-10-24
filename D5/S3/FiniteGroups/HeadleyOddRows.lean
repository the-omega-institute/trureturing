/- GID: D5/S3/FiniteGroups/HeadleyOddRows
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyOddRows
   mirror-E: none(waiver:pure-mathematical-odd-product)
   anchors: []
   utility: none
   digest: The Gordon predecessor is a complete row cycle with carry-derived orthomorphisms. -/

import D5.S3.FiniteGroups.GordonFullSet
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! Original Gordon mixed-radix suppliers, with a complete predecessor orbit.
Rank is only a set coordinate: no cyclic additive encoding is assumed. -/

namespace D5.S3.FiniteGroups.HeadleyOddRows

open Gordon

private theorem residue_rank (ds : List OddRadix) (x : Box ds) :
    residue ds (rank ds x) = x := by
  apply (rankEquiv ds).injective
  apply Fin.ext
  change rank ds (residue ds (rank ds x)) = rank ds x
  rw [rank_residue]
  exact Nat.mod_eq_of_lt (rankEquiv ds x).isLt

private theorem residue_volume (ds : List OddRadix) : residue ds (volume ds) = 0 := by
  rw [← residue_zero ds]
  exact (residue_eq_iff ds _ _).2 (by simp [Nat.ModEq])

private theorem pred_next (ds : List OddRadix) (x : Box ds) :
    pred ds (residue ds (rank ds x + 1)) = x := by
  rw [pred_residue ds _ (by omega), Nat.add_sub_cancel, residue_rank]

/-- Predecessor with the explicit positive-residue successor as inverse. -/
def predecessor (ds : List OddRadix) : Equiv.Perm (Box ds) where
  toFun := pred ds
  invFun x := residue ds (rank ds x + 1)
  right_inv := pred_next ds
  left_inv x := by
    have hi : Function.Injective (pred ds) :=
      Finite.injective_iff_surjective.mpr (fun y => ⟨_, pred_next ds y⟩)
    exact hi (pred_next ds (pred ds x))

/-- All bounded ranks, the positive wrap at zero, and closure in one formula. -/
theorem predecessor_orbit (ds : List OddRadix) (i : ℕ) (hi : i ≤ volume ds) :
    (predecessor ds ^ i) 0 = residue ds (volume ds - i) := by
  induction i with
  | zero => simpa using (residue_volume ds).symm
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    change pred ds (residue ds (volume ds - i)) = _
    rw [pred_residue ds _ (by omega)]
    congr 1

/-- Every row belongs to the same predecessor cycle, including a singleton box. -/
theorem predecessor_cycle (ds : List OddRadix) :
    (predecessor ds).IsCycleOn Set.univ := by
  have hz (x : Box ds) : (predecessor ds).SameCycle x 0 := by
    have h : ∀ n : ℕ, (predecessor ds ^ n) (residue ds n) = 0 := by
      intro n
      induction n with
      | zero => simp [residue_zero]
      | succ n ih =>
        rw [pow_succ, Equiv.Perm.mul_apply]
        change (predecessor ds ^ n) (pred ds (residue ds (n + 1))) = 0
        rw [pred_residue ds _ (by omega), Nat.add_sub_cancel]
        exact ih
    refine ⟨(rank ds x : ℤ), ?_⟩
    rw [zpow_natCast]
    simpa only [residue_rank] using h (rank ds x)
  exact ⟨(predecessor ds).bijective.bijOn_univ, fun x _ y _ => (hz x).trans (hz y).symm⟩

/-- Odd-coordinate doubling, with its inverse supplied by the original injectivity proof. -/
noncomputable def doubling (ds : List OddRadix) : Equiv.Perm (Box ds) :=
  Equiv.ofBijective (fun x => x + x)
    ⟨box_two_injective ds, Finite.surjective_of_injective (box_two_injective ds)⟩

/-- The original reversible carry, not a new copy of its proof. -/
noncomputable def carries (ds : List OddRadix) : Equiv.Perm (Box ds) :=
  Equiv.ofBijective (carry ds)
    ⟨carry_injective ds, Finite.surjective_of_injective (carry_injective ds)⟩

/-- The ordinary involutory row lift. -/
def rowZero (ds : List OddRadix) : Equiv.Perm (Box ds) := Equiv.neg _

/-- The unique distinguished ordinary row lift. -/
def rowOne (ds : List OddRadix) : Equiv.Perm (Box ds) :=
  (Equiv.neg _).trans (predecessor ds)

/-- Actual differences of the involutory lift. -/
noncomputable def deltaZero (ds : List OddRadix) : Equiv.Perm (Box ds) :=
  (doubling ds).trans (Equiv.neg _)

/-- Actual differences of the distinguished lift, expressed through Gordon carry. -/
noncomputable def deltaOne (ds : List OddRadix) : Equiv.Perm (Box ds) :=
  (Equiv.neg _).trans ((carries ds).trans
    ((Equiv.neg _).trans (Equiv.addRight (-ones ds))))

theorem delta_zero_spec (ds : List OddRadix) (h : Box ds) :
    deltaZero ds h = rowZero ds h - h := by
  change -(h + h) = -h - h
  abel

theorem delta_one_spec (ds : List OddRadix) (h : Box ds) :
    deltaOne ds h = rowOne ds h - h := by
  change -carry ds (-h) + -ones ds = pred ds (-h) - h
  dsimp [carry]
  abel

/-- Traversal order matters: the two row maps compose to predecessor. -/
theorem row_return (ds : List OddRadix) (h : Box ds) :
    rowOne ds (rowZero ds h) = predecessor ds h := by
  change pred ds (- -h) = pred ds h
  rw [neg_neg]

/-- Unconditional original trichotomy supplies every odd group, without a total premise.
This consumed helper is normalization of the original decomposition, not a new structure theorem. -/
theorem odd_box {H : Type*} [AddCommGroup H] [Fintype H]
    (hH : Odd (Nat.card H)) : ∃ ds : List OddRadix, Nonempty (H ≃+ Box ds) := by
  have ho : Odd (Fintype.card H) := by simpa [Nat.card_eq_fintype_card] using hH
  obtain ⟨cs, ⟨e⟩⟩ := finite_abelian_presentation H
  rcases case_transport e (chain_classification cs) with ⟨_, ds, he⟩ | ⟨a, ha, ds, ⟨f⟩⟩ | ⟨he, _⟩
  · exact ⟨ds, he⟩
  · exact ((Nat.not_even_iff_odd.mpr ho) (card_even_of_power_box a ha ds f)).elim
  · exact ((Nat.not_even_iff_odd.mpr ho) he).elim

end D5.S3.FiniteGroups.HeadleyOddRows
