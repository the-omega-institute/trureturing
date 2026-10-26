/- GID: D5/S3/Combinatorics/Geometry/MiuraRunCompositions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraRunCompositions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual positive run-length vectors have the exact binomial cardinality. -/

module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic

/-! The positive length vectors used in frozen-run expansion fibers. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraRunCompositions

open scoped BigOperators

/-- Each indexed run has a positive integer length and the total is fixed. -/
def PositiveLengths (N r : ℕ) :=
  {f : Fin r → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = N}

/-- Remove one compulsory cell from every indexed run. -/
def removeOnesEquiv (N r : ℕ) (hle : r ≤ N) :
    PositiveLengths N r ≃ {f : Fin r → ℕ // ∑ i, f i = N - r} where
  toFun x := ⟨fun i => x.val i - 1, by
    have hsum : (∑ i, (x.val i - 1)) + r = N := by
      calc
        (∑ i, (x.val i - 1)) + r = ∑ i, (x.val i - 1 + 1) := by
          simp [Finset.sum_add_distrib]
        _ = ∑ i, x.val i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Nat.sub_add_cancel (x.property.1 i)
        _ = N := x.property.2
    exact Nat.add_right_cancel (hsum.trans (Nat.sub_add_cancel hle).symm)⟩
  invFun x := ⟨fun i => x.val i + 1, by
    refine ⟨fun i => Nat.zero_lt_succ _, ?_⟩
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, x.property]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Nat.sub_add_cancel (x.property.1 i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel _ _

/-- Positive run lengths are counted as actual indexed vectors. -/
theorem positive_lengths_card (N r : ℕ) (hr : 1 ≤ r) (hle : r ≤ N) :
    Nat.card (PositiveLengths N r) = (N - 1).choose (r - 1) := by
  classical
  let e := (removeOnesEquiv N r hle).trans (Sym.equivNatSumOfFintype (Fin r) (N - r)).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose,
    Fintype.card_fin]
  have htop : r + (N - r) - 1 = N - 1 := by omega
  rw [htop]
  exact Nat.choose_symm_of_eq_add (by omega)

end D5.S3.Combinatorics.Geometry.MiuraRunCompositions
