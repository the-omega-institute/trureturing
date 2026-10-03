/- GID: D5/S1/Words/Patterns/Separable/RecordWeights
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordWeights
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strict records on actual permutations and their signed minimum-cut fibers. -/

import D5.S1.Words.Patterns.Separable.ActualCardinality
import Mathlib.Algebra.BigOperators.Fin

/-!
Records are strict position records on actual permutations. The carrier of
separable permutations is the literal 2413/3142-avoiding subtype. A direct
cut has all prefix values below all suffix values; a skew cut has the opposite
inequality. The record weights below include all natural lengths and indices.
-/

namespace D5.S1.Words.Patterns.Separable.RecordWeights

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ActualCardinality
open scoped BigOperators

def IsRightMaximum {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j, i < j → π j < π i

noncomputable def rmax {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (IsRightMaximum π)).card

/-- A direct sum retains only suffix right maxima when its suffix is nonempty;
a skew sum retains the right maxima in both factors, including empty factors. -/
theorem rmax_block_sum {m k : ℕ} (α : Equiv.Perm (Fin m))
    (β : Equiv.Perm (Fin k)) :
    rmax (blockSum false α β) = (if k = 0 then rmax α else rmax β) ∧
    rmax (blockSum true α β) = rmax α + rmax β := by
  classical
  have leftval (sign : Bool) (i : Fin m) :
      (blockSum sign α β (Fin.castAdd k i)).val =
        (if sign then k else 0) + (α i).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
  have rightval (sign : Bool) (i : Fin k) :
      (blockSum sign α β (Fin.natAdd m i)).val =
        (if sign then 0 else m) + (β i).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
  have suffix (sign : Bool) (i : Fin k) :
      IsRightMaximum (blockSum sign α β) (Fin.natAdd m i) ↔
        IsRightMaximum β i := by
    constructor
    · intro h j hj
      have comparison := h (Fin.natAdd m j) (by simpa using hj)
      simpa only [Fin.lt_def, rightval, Nat.add_lt_add_iff_left] using comparison
    · intro h j hj
      by_cases left : j.val < m
      · simp only [Fin.lt_def, Fin.val_natAdd] at hj
        omega
      · let last : Fin k := ⟨j.val - m, by omega⟩
        have eq : j = Fin.natAdd m last := Fin.ext (by simp [last]; omega)
        rw [eq] at hj ⊢
        have comparison := h last (by simpa using hj)
        simpa only [Fin.lt_def, rightval, Nat.add_lt_add_iff_left] using comparison
  have prefixLaw (sign : Bool) (allowed : sign = true ∨ k = 0) (i : Fin m) :
      IsRightMaximum (blockSum sign α β) (Fin.castAdd k i) ↔
        IsRightMaximum α i := by
    constructor
    · intro h j hj
      have comparison := h (Fin.castAdd k j) (by
        simpa only [Fin.lt_def, Fin.val_castAdd] using hj)
      simpa only [Fin.lt_def, leftval,
        Nat.add_lt_add_iff_left] using comparison
    · intro h j hj
      by_cases left : j.val < m
      · let first : Fin m := ⟨j.val, left⟩
        have eq : j = Fin.castAdd k first := Fin.ext rfl
        rw [eq] at hj ⊢
        have comparison := h first (by
          simpa only [Fin.lt_def, Fin.val_castAdd] using hj)
        simpa only [Fin.lt_def, leftval,
          Nat.add_lt_add_iff_left] using comparison
      · let last : Fin k := ⟨j.val - m, by omega⟩
        have eq : j = Fin.natAdd m last := Fin.ext (by simp [last]; omega)
        rw [eq]
        cases sign with
        | false =>
          have empty : k = 0 := allowed.resolve_left Bool.false_ne_true
          have bound := last.isLt
          omega
        | true =>
          simp only [Fin.lt_def, rightval, leftval, ↓reduceIte, Nat.zero_add]
          exact lt_of_lt_of_le (β last).isLt (Nat.le_add_right _ _)
  have directPrefix (hk : 0 < k) (i : Fin m) :
      ¬IsRightMaximum (blockSum false α β) (Fin.castAdd k i) := by
    intro h
    have comparison := h (Fin.natAdd m ⟨0, hk⟩) (by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega)
    simp only [Fin.lt_def, rightval, leftval, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add] at comparison
    have bound := (α i).isLt
    omega
  have count {n : ℕ} (π : Equiv.Perm (Fin n)) :
      rmax π = ∑ i : Fin n, if IsRightMaximum π i then 1 else 0 := by
    simp only [rmax, Finset.card_eq_sum_ones, Finset.sum_filter]
  constructor
  · by_cases hk : k = 0
    · subst k
      rw [if_pos rfl, count, Fin.sum_univ_add, count]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      simp only [prefixLaw false (Or.inr rfl)]
    · rw [if_neg hk, count, Fin.sum_univ_add, count]
      simp only [directPrefix (Nat.pos_of_ne_zero hk), ↓reduceIte,
        Finset.sum_const_zero, zero_add, suffix]
  · rw [count, Fin.sum_univ_add, count, count]
    simp only [prefixLaw true (Or.inl rfl), suffix]

/-- Actual proper-cut record fibers, for every length and record index. Direct
cuts carry only the suffix weight; skew cuts convolve the two strict counts. -/
theorem proper_cut_record_convolution (sign : Bool) (n k : ℕ) :
    Nat.card {π : ProperSigned sign n // rmax π.val.val = k} =
      ∑ cut ∈ Finset.Ioo 0 n,
        if sign then
          ∑ b ∈ Finset.range (k + 1),
            Nat.card {α : Indecomposable sign cut // rmax α.val.val = b} *
              Nat.card {β : Avoider (n - cut) // rmax β.val = k - b}
        else
          Nat.card (Indecomposable sign cut) *
            Nat.card {β : Avoider (n - cut) // rmax β.val = k} := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, enumeration, _⟩ := actual_schroder_cardinality
  obtain ⟨e, reconstruction⟩ := enumeration sign n
  let Factors (cut : ↥(Finset.Ioo 0 n)) :=
    Indecomposable sign cut.val × Avoider (n - cut.val)
  let weight (cut : ↥(Finset.Ioo 0 n)) (factors : Factors cut) :=
    if sign then rmax factors.1.val.val + rmax factors.2.val else rmax factors.2.val
  have transported {a b : ℕ} (h : a = b) (π : Equiv.Perm (Fin a)) :
      rmax (h ▸ π : Equiv.Perm (Fin b)) = rmax π := by
    cases h
    rfl
  have exactWeight (π : ProperSigned sign n) :
      rmax π.val.val = weight (e π).1 (e π).2 := by
    have cutPositive := (Finset.mem_Ioo.mp (e π).1.property).1
    have cutBelow := (Finset.mem_Ioo.mp (e π).1.property).2
    have law := rmax_block_sum (e π).2.1.val.val (e π).2.2.val
    have preserved := congrArg rmax (reconstruction π).2
    rw [transported] at preserved
    rw [← preserved]
    cases sign with
    | false =>
      dsimp [weight]
      exact law.1.trans (if_neg (by omega))
    | true => exact law.2
  let restricted : {π : ProperSigned sign n // rmax π.val.val = k} ≃
      {item : Σ cut, Factors cut // weight item.1 item.2 = k} :=
    Equiv.subtypeEquiv e (fun π => by rw [exactWeight])
  let split : {item : Σ cut, Factors cut // weight item.1 item.2 = k} ≃
      Σ cut, {factors : Factors cut // weight cut factors = k} :=
    { toFun := fun item => ⟨item.val.1, item.val.2, item.property⟩
      invFun := fun item => ⟨⟨item.1, item.2.val⟩, item.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have counts (cut : ↥(Finset.Ioo 0 n)) :
      Nat.card {factors : Factors cut // weight cut factors = k} =
        if sign then
          ∑ b ∈ Finset.range (k + 1),
            Nat.card {α : Indecomposable sign cut.val // rmax α.val.val = b} *
              Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b}
        else
          Nat.card (Indecomposable sign cut.val) *
            Nat.card {β : Avoider (n - cut.val) // rmax β.val = k} := by
    cases sign with
    | false =>
      let suffixOnly : {factors : Factors cut // weight cut factors = k} ≃
          Indecomposable false cut.val ×
            {β : Avoider (n - cut.val) // rmax β.val = k} :=
        { toFun := fun item => ⟨item.val.1, item.val.2, item.property⟩
          invFun := fun item => ⟨⟨item.1, item.2.val⟩, item.2.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        (Nat.card_congr suffixOnly).trans (Nat.card_prod _ _)
    | true =>
      let additive : {factors : Factors cut // weight cut factors = k} ≃
          Σ b : ↥(Finset.range (k + 1)),
            {α : Indecomposable true cut.val // rmax α.val.val = b.val} ×
              {β : Avoider (n - cut.val) // rmax β.val = k - b.val} :=
        { toFun := fun item =>
            ⟨⟨rmax item.val.1.val.val, Finset.mem_range.mpr (by
                have sum := item.property
                dsimp [weight] at sum
                omega)⟩,
              ⟨item.val.1, rfl⟩, ⟨item.val.2, by
                change rmax item.val.2.val = k - rmax item.val.1.val.val
                have sum := item.property
                dsimp [weight] at sum
                omega⟩⟩
          invFun := fun item => ⟨⟨item.2.1.val, item.2.2.val⟩, by
            dsimp [weight]
            rw [item.2.1.property, item.2.2.property]
            have bound := Finset.mem_range.mp item.1.property
            omega⟩
          left_inv := fun _ => rfl
          right_inv := by
            rintro ⟨⟨b, hb⟩, ⟨α, hα⟩, ⟨β, hβ⟩⟩
            dsimp at hα
            cases hα
            rfl }
      rw [Nat.card_congr additive, Nat.card_sigma]
      simp only [↓reduceIte, Nat.card_prod]
      exact Finset.sum_coe_sort (Finset.range (k + 1))
        (fun b => Nat.card {α : Indecomposable true cut.val // rmax α.val.val = b} *
          Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b})
  calc
    _ = Nat.card (Σ cut, {factors : Factors cut // weight cut factors = k}) :=
      Nat.card_congr (restricted.trans split)
    _ = ∑ cut : ↥(Finset.Ioo 0 n),
        Nat.card {factors : Factors cut // weight cut factors = k} := Nat.card_sigma
    _ = ∑ cut : ↥(Finset.Ioo 0 n),
        if sign then
          ∑ b ∈ Finset.range (k + 1),
            Nat.card {α : Indecomposable sign cut.val // rmax α.val.val = b} *
              Nat.card {β : Avoider (n - cut.val) // rmax β.val = k - b}
        else
          Nat.card (Indecomposable sign cut.val) *
            Nat.card {β : Avoider (n - cut.val) // rmax β.val = k} := by
      apply Finset.sum_congr rfl
      intro cut _
      exact counts cut
    _ = _ := Finset.sum_coe_sort (Finset.Ioo 0 n)
      (fun cut => if sign then
        ∑ b ∈ Finset.range (k + 1),
          Nat.card {α : Indecomposable sign cut // rmax α.val.val = b} *
            Nat.card {β : Avoider (n - cut) // rmax β.val = k - b}
        else Nat.card (Indecomposable sign cut) *
          Nat.card {β : Avoider (n - cut) // rmax β.val = k})

#print axioms rmax_block_sum
#print axioms proper_cut_record_convolution

end D5.S1.Words.Patterns.Separable.RecordWeights
