/- GID: D5/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every nonidentity free-group element survives in a finite prime-group quotient. -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; full terms: docs/reports/licenses/TauCeti-LICENSE.txt.
Authors of the adapted source: The Tau Ceti contributors.
Adapted from TauCeti revision d91980bdc255e6e50506be147ad9bcb88eb9fcc0,
GroupTheory/FreeGroup/{Syllables,ResiduallyP}.lean and NumberTheory/Binomial/PadicVal.lean.
The target is the existing Uplus subgroup with its upper-entry chart; its cardinality
supplies the period. The normalized word and first-row argument follow the attributed source.
-/
module

public import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangularCard
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FreeGroupPrimeQuotientSeparation

open FreeGroup Matrix NikolovSegal.SLnNormalizer NikolovSegal.SLnSylow

universe u
variable {X : Type u}

section Syllables

/-- The product `x₁ ^ e₁ ⋯ x_k ^ e_k` of a list of syllables. -/
private def syllableProd (s : List (X × ℤ)) : FreeGroup X :=
  (s.map fun a ↦ of a.1 ^ a.2).prod

/-- The empty syllable list represents the identity. -/
@[simp]
private theorem syllableProd_nil : syllableProd ([] : List (X × ℤ)) = 1 := by
  simp [syllableProd]

/-- The product of a nonempty syllable list factors at its head. -/
@[simp]
private theorem syllableProd_cons (a : X × ℤ) (s : List (X × ℤ)) :
    syllableProd (a :: s) = of a.1 ^ a.2 * syllableProd s := by
  simp [syllableProd]

/-- A syllable list is normal when its exponents are nonzero and consecutive generators are
distinct. -/
private def IsSyllableNormal (s : List (X × ℤ)) : Prop :=
  (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1

/-- A syllable list is normal iff its exponents are nonzero and consecutive generators are
distinct. -/
private theorem isSyllableNormal_iff {s : List (X × ℤ)} :
    IsSyllableNormal s ↔ (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1 :=
  Iff.rfl

/-- Left-multiplying the product of a normal syllable list by a generator power gives the
product of another normal syllable list. -/
private theorem exists_isSyllableNormal_zpow_mul (x : X) (e : ℤ) (s : List (X × ℤ))
    (hs : IsSyllableNormal s) :
    ∃ t, IsSyllableNormal t ∧ syllableProd t = of x ^ e * syllableProd s := by
  obtain ⟨hs0, hsc⟩ := hs
  rcases eq_or_ne e 0 with rfl | he
  · exact ⟨s, ⟨hs0, hsc⟩, by simp⟩
  match s, hs0, hsc with
  | [], _, _ => exact ⟨[(x, e)], ⟨by simpa, .singleton _⟩, by simp⟩
  | (y, f) :: s', hs0, hsc =>
    by_cases hyx : y = x
    · subst hyx
      have hs' : IsSyllableNormal s' := ⟨fun a ha ↦ hs0 a (.tail _ ha), hsc.tail⟩
      by_cases hf : e + f = 0
      · exact ⟨s', hs', by simp [← mul_assoc, ← zpow_add, hf]⟩
      · refine ⟨(y, e + f) :: s', ⟨by simpa [hf] using hs'.1, ?_⟩, by simp [mul_assoc, zpow_add]⟩
        exact List.isChain_cons.2 ⟨(List.isChain_cons.1 hsc).1, hsc.tail⟩
    · exact ⟨(x, e) :: (y, f) :: s', ⟨by simpa [he] using hs0, .cons_cons (Ne.symm hyx) hsc⟩,
        by simp⟩

/-- Every element of a free group is the product of a normal syllable list. -/
private theorem exists_isSyllableNormal (w : FreeGroup X) :
    ∃ s, IsSyllableNormal s ∧ syllableProd s = w := by
  suffices h : ∀ s, IsSyllableNormal s →
      ∃ t, IsSyllableNormal t ∧ syllableProd t = w * syllableProd s by
    simpa using h [] ⟨by simp, .nil⟩
  induction w with
  | one => exact fun s hs ↦ ⟨s, hs, (one_mul _).symm⟩
  | of x => simpa using exists_isSyllableNormal_zpow_mul x 1
  | inv_of x _ => simpa using exists_isSyllableNormal_zpow_mul x (-1)
  | mul u v hu hv =>
    intro s hs
    obtain ⟨t, ht, htv⟩ := hv s hs
    obtain ⟨r, hr, hru⟩ := hu t ht
    exact ⟨r, hr, by rw [hru, htv, mul_assoc]⟩

end Syllables

section Binomial

variable {p : ℕ} [Fact p.Prime]

/-- If `K` exceeds `v_p(e)` for nonzero `e`, then for every natural number `n` congruent to
`e` modulo `p ^ K`, the binomial coefficient `n.choose (p ^ v_p(e))` is nonzero modulo `p`. -/
private theorem natCast_choose_pow_padicValInt_ne_zero_of_modEq {e : ℤ} (he : e ≠ 0) {K : ℕ}
    (hK : padicValInt p e < K) {n : ℕ} (hn : (n : ℤ) ≡ e [ZMOD (p : ℤ) ^ K]) :
    ((n.choose (p ^ padicValInt p e) : ℕ) : ZMod p) ≠ 0 := by
  set v := padicValInt p e
  have hdvd (k : ℕ) (hk : k ≤ K) : p ^ k ∣ n ↔ (p : ℤ) ^ k ∣ e := by
    exact_mod_cast (hn.of_dvd (pow_dvd_pow _ hk)).dvd_iff
  obtain ⟨m, rfl⟩ := (hdvd v hK.le).2 (padicValInt_dvd e)
  have hpm : ¬ p ∣ m := fun h ↦ by
    have := (hdvd (v + 1) hK).1 (pow_succ p v ▸ mul_dvd_mul_left _ h)
    rw [padicValInt_dvd_iff] at this
    omega
  have := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := v) (a := m) (b := 1)
  rw [mul_one, Nat.choose_one_right] at this
  rwa [(ZMod.natCast_eq_natCast_iff _ _ _).2 this, Ne, ZMod.natCast_eq_zero_iff]

end Binomial

section Matrices

variable {p : ℕ} (ℓ : ℕ → Option X) (D : ℕ)

/-- All positions in the interval `(a, b]` are spelled with the letter `x`. -/
private def Spelled (x : X) (a b : ℕ) : Prop :=
  ∀ s ∈ Finset.Ioc a b, ℓ s = some x

private instance [DecidableEq X] (x : X) (a b : ℕ) : Decidable (Spelled ℓ x a b) := by
  unfold Spelled; infer_instance

private theorem spelled_iff {x : X} {a b : ℕ} :
    Spelled ℓ x a b ↔ ∀ s, a < s → s ≤ b → ℓ s = some x := by
  simp [Spelled]

private theorem spelled_succ_iff {x : X} {a c : ℕ} (hac : a ≤ c) :
    Spelled ℓ x a (c + 1) ↔ Spelled ℓ x a c ∧ ℓ (c + 1) = some x := by
  simp only [spelled_iff]
  refine ⟨fun h ↦ ⟨fun s h₁ h₂ ↦ h s h₁ (by omega), h _ (by omega) le_rfl⟩, fun h s h₁ h₂ ↦ ?_⟩
  rcases Nat.lt_or_ge s (c + 1) with hs | hs
  · exact h.1 s h₁ (by omega)
  -- Normalize the final position of the interval to its successor index.
  · rw [show s = c + 1 by omega]
    exact h.2

variable [DecidableEq X]

/-- The shift matrix of the letter `x`: it has an entry `1` at `(s - 1, s)` for each position
`s` spelled with `x`, and is zero elsewhere. -/
private def shift (x : X) : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p) :=
  Matrix.of fun a b ↦ if (b : ℕ) = a + 1 ∧ ℓ b = some x then 1 else 0

private theorem shift_pow_apply (x : X) (j : ℕ) (a b : Fin (D + 1)) :
    (shift (p := p) ℓ D x ^ j) a b =
      if (b : ℕ) = a + j ∧ Spelled ℓ x a b then 1 else 0 := by
  induction j generalizing b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, (spelled_iff ℓ).2 fun s h₁ h₂ ↦ absurd h₂ (by omega)⟩]
    · rw [ite_eq_right hab, ite_eq_right fun h ↦ hab (Fin.ext (by omega))]
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hb : (b : ℕ) = a + j + 1
    · rw [Fintype.sum_eq_single (⟨a + j, by omega⟩ : Fin (D + 1))]
      · have key := spelled_succ_iff ℓ (x := x) (le_add_right (le_refl (a : ℕ)) : (a : ℕ) ≤ a + j)
        rw [ih]
        simp only [shift, Matrix.of_apply, hb, ← add_assoc]
        by_cases h₁ : Spelled ℓ x a (a + j) <;> by_cases h₂ : ℓ (a + j + 1) = some x <;>
          simp [h₁, h₂, key]
      · intro c hc
        have hc' : (c : ℕ) ≠ a + j := fun h ↦ hc (Fin.ext h)
        rw [ih, ite_eq_right fun h ↦ hc' h.1, zero_mul]
    · rw [ite_eq_right fun h ↦ hb (by omega)]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      by_cases hc : (c : ℕ) = a + j
      · have : ¬ ((b : ℕ) = c + 1 ∧ ℓ b = some x) := fun h ↦ hb (by omega)
        simp [shift, this]
      · rw [ih, ite_eq_right fun h ↦ hc h.1, zero_mul]

private theorem one_add_shift_pow_apply (x : X) (n : ℕ) (a b : Fin (D + 1)) :
    ((1 + shift (p := p) ℓ D x) ^ n) a b =
      if (a : ℕ) ≤ b ∧ Spelled ℓ x a b then (n.choose (b - a) : ZMod p) else 0 := by
  rw [add_comm (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)), (Commute.one_right _).add_pow,
    Matrix.sum_apply]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, shift_pow_apply, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ((b : ℕ) - a)]
    · rw [ite_eq_left ⟨by omega, h.2⟩]
    · intro j _ hj
      rw [ite_eq_right fun h' ↦ hj (by omega)]
    · intro hj
      rw [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, ite_self]
  · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h' ↦ h ⟨by omega, h'.2⟩

variable [hp : Fact p.Prime]

local notation "U" => Uplus (D + 1) (ZMod p)
local notation "q" => ((D + 1) * ((D + 1) - 1) / 2)
local notation "K" => (q + (D + 1))

private instance : Finite U :=
  Finite.of_equiv (UpperEntry (D + 1) → ZMod p)
    (upperCoordinatesEquiv (D + 1) (ZMod p)).symm

private theorem group_card : Nat.card U = p ^ q := by
  simpa only [ZMod.card] using (card_Uplus (F := ZMod p) (D + 1))

private theorem period (g : U) : g ^ (p ^ K) = 1 := by
  have hcard : g ^ (p ^ q) = 1 := by
    rw [← group_card (p := p) D]
    exact pow_card_eq_one'
  rw [pow_add, pow_mul, hcard, one_pow]

private noncomputable def generator (x : X) : U :=
  upperChart (fun a => shift (p := p) ℓ D x ⟨a.2.val, a.2.isLt.trans a.1.isLt⟩ a.1)

private def projection : U →* Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p) :=
  SpecialLinearGroup.coeMonoidHom.comp (Uplus (D + 1) (ZMod p)).subtype

private theorem generator_val (x : X) :
    projection (p := p) D (generator (p := p) ℓ D x) = 1 + shift ℓ D x := by
  classical
  change upperMatrix (fun a =>
    shift (p := p) ℓ D x ⟨a.2.val, a.2.isLt.trans a.1.isLt⟩ a.1) = _
  ext r c
  rcases lt_trichotomy r.val c.val with hrc | he | hcr
  · have hne : r ≠ c := fun h => (ne_of_lt hrc) (congrArg Fin.val h)
    simp [upperMatrix, hrc, Matrix.add_apply, Matrix.one_apply, hne]
  · have heq : r = c := Fin.ext he
    subst c
    have hstep : ¬ (r : ℕ) = r + 1 := by omega
    simp [upperMatrix, shift, hstep]
  · have hrc : ¬ r.val < c.val := by omega
    have hne : r ≠ c := fun h => (ne_of_gt hcr) (congrArg Fin.val h)
    have hstep : ¬ ((c : ℕ) = r + 1 ∧ ℓ c = some x) := by
      intro h
      omega
    simp [upperMatrix, hrc, shift, hstep, Matrix.one_apply, hne]

private noncomputable def rep : FreeGroup X →* U :=
  FreeGroup.lift (generator (p := p) ℓ D)

private theorem coe_rep_of_zpow (x : X) (e : ℤ) :
    projection (p := p) D (rep (p := p) ℓ D (FreeGroup.of x ^ e)) =
      (1 + shift ℓ D x) ^ (e % (p ^ K : ℕ)).toNat := by
  have hperiod := period (p := p) D (generator (p := p) ℓ D x)
  have hnonneg : 0 ≤ e % (p ^ K : ℕ) :=
    Int.emod_nonneg _ (Nat.cast_ne_zero.mpr (pow_pos hp.out.pos _).ne')
  rw [rep, map_zpow, FreeGroup.lift_apply_of, zpow_eq_zpow_emod' e hperiod,
    ← Int.toNat_of_nonneg hnonneg, zpow_natCast, map_pow, generator_val]
  simp only [Int.toNat_natCast]

end Matrices

section Tracking

variable (p : ℕ)

/-- The length `p ^ v_p(e)` given to a syllable with exponent `e`. -/
private noncomputable def weight (e : ℤ) : ℕ :=
  p ^ padicValInt p e

/-- The letters spelling `x₁ ^ t₁ ⋯ x_k ^ t_k` in positions `1, 2, …`, where `tᵢ` is the weight
of the `i`-th syllable. -/
private noncomputable def letters : List (X × ℤ) → ℕ → Option X
  | [], _ => none
  | a :: s, j => if j ≤ weight p a.2 then some a.1 else letters s (j - weight p a.2)

/-- The total weight of a syllable list. -/
private noncomputable def totalWeight (s : List (X × ℤ)) : ℕ :=
  (s.map fun a ↦ weight p a.2).sum

variable {p} (ℓ : ℕ → Option X) (D : ℕ)

/-- The positions `L + 1, …, D` spell the syllable list `s` with the weights. -/
private def Spells : ℕ → List (X × ℤ) → Prop
  | L, [] => L = D
  | L, a :: s => Spelled ℓ a.1 L (L + weight p a.2) ∧ Spells (L + weight p a.2) s

private theorem Spells.le {L : ℕ} {s : List (X × ℤ)} (h : Spells (p := p) ℓ D L s) : L ≤ D := by
  induction s generalizing L with
  | nil => exact le_of_eq h
  | cons a s ih => exact (Nat.le_add_right _ _).trans (ih h.2)

private theorem spells_letters (s : List (X × ℤ)) (L : ℕ)
    (hℓ : ∀ j, 0 < j → ℓ (L + j) = letters p s j) (hD : L + totalWeight p s = D) :
    Spells (p := p) ℓ D L s := by
  induction s generalizing L with
  | nil =>
    simp only [Spells]
    simpa [totalWeight] using hD
  | cons a s ih =>
    refine ⟨(spelled_iff ℓ).2 fun j h₁ h₂ ↦ ?_, ih _ (fun j hj ↦ ?_) ?_⟩
    -- Normalize `j` to its offset from the start of this syllable's run.
    · rw [show j = L + (j - L) by omega, hℓ _ (by omega), letters, ite_eq_left (by omega)]
    · rw [add_assoc, hℓ _ (by omega), letters, ite_eq_right (by omega), Nat.add_sub_cancel_left]
    · simp only [totalWeight, List.map_cons, List.sum_cons] at hD ⊢
      omega

/-- The first row of `R` is supported in the columns `≤ L` and is nonzero in column `L`. -/
private def RowInv (R : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) (L : ℕ) : Prop :=
  (∀ b : Fin (D + 1), R 0 b ≠ 0 → (b : ℕ) ≤ L) ∧ ∀ b : Fin (D + 1), (b : ℕ) = L → R 0 b ≠ 0

variable [hp : Fact p.Prime]

/-- One syllable step: multiplying by a matrix supported on runs of `x`, whose entry across the
run `(L, L + t]` is nonzero, moves the first-row invariant from `L` to `L + t`, provided the run
is maximal. -/
private theorem RowInv.mul {R M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)} {L t : ℕ} {x : X}
    (hR : RowInv D R L) (hLt : L + t ≤ D) (hprev : L = 0 ∨ ℓ L ≠ some x)
    (hnext : L + t = D ∨ ℓ (L + t + 1) ≠ some x)
    (hM : ∀ a b : Fin (D + 1), M a b ≠ 0 → Spelled ℓ x a b)
    (hMv : ∀ a b : Fin (D + 1), (a : ℕ) = L → (b : ℕ) = L + t → M a b ≠ 0) :
    RowInv D (R * M) (L + t) := by
  constructor
  · intro b hb
    rw [Matrix.mul_apply] at hb
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    have h₁ := hR.1 a (left_ne_zero_of_mul ha)
    have h₂ := (spelled_iff ℓ).1 (hM a b (right_ne_zero_of_mul ha))
    by_contra hlt
    rcases hnext with h | h
    · exact hlt (by omega)
    · exact h (h₂ _ (by omega) (by omega))
  · intro b hb
    rw [Matrix.mul_apply, Fintype.sum_eq_single (⟨L, by omega⟩ : Fin (D + 1))]
    · exact mul_ne_zero (hR.2 _ rfl) (hMv _ _ rfl hb)
    · intro a ha
      by_contra hne
      have haL := hR.1 a (left_ne_zero_of_mul hne)
      have haL' : (a : ℕ) < L := lt_of_le_of_ne haL fun h ↦ ha (Fin.ext h)
      have h₂ := (spelled_iff ℓ).1 (hM a b (right_ne_zero_of_mul hne))
      rcases hprev with h | h
      · omega
      · exact h (h₂ _ haL' (by omega))

private theorem one_le_weight (e : ℤ) : 1 ≤ weight p e :=
  Nat.one_le_pow _ _ hp.out.pos

variable [DecidableEq X]

/-- The first-row invariant is carried through the image of a normal syllable list spelled by
the positions after `L`. -/
private theorem RowInv.mul_rep (s : List (X × ℤ)) (hs : IsSyllableNormal s) (L : ℕ)
    (hL : Spells (p := p) ℓ D L s) (R : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))
    (hR : RowInv D R L) (hprev : ∀ a ∈ s.head?, L = 0 ∨ ℓ L ≠ some a.1) :
    RowInv D (R * projection (p := p) D (rep (p := p) ℓ D (syllableProd s))) D := by
  induction s generalizing L R with
  | nil =>
    obtain rfl : L = D := hL
    simpa using hR
  | cons a s ih =>
    obtain ⟨x, e⟩ := a
    obtain ⟨hs0, hsc⟩ := isSyllableNormal_iff.1 hs
    obtain ⟨hrun, hL'⟩ := hL
    have hLt : L + weight p e ≤ D := hL'.le
    have hrunx : ℓ (L + weight p e) = some x :=
      (spelled_iff ℓ).1 hrun _ (by have := one_le_weight (p := p) e; omega) le_rfl
    rw [syllableProd_cons, map_mul, map_mul, ← mul_assoc]
    -- Apply the one-syllable step to `x ^ e`, then continue with the remaining syllables.
    refine ih (isSyllableNormal_iff.2 ⟨fun a ha ↦ hs0 a (List.mem_cons_of_mem _ ha), hsc.tail⟩)
      _ hL' _ (RowInv.mul ℓ D hR hLt (hprev (x, e) rfl) ?_ ?_ ?_) ?_
    -- The run of `x` ends at `L + weight p e`: the next syllable has a different letter.
    · cases s with
      | nil => exact Or.inl hL'
      | cons c s =>
        right
        rw [(spelled_iff ℓ).1 hL'.1 _ (by omega)
          (by have := one_le_weight (p := p) c.2; omega)]
        exact fun h ↦ (List.isChain_cons_cons.mp hsc).1 (Option.some_injective _ h).symm
    -- The image of `x ^ e` is supported on runs of `x`.
    · intro a b hab
      rw [coe_rep_of_zpow, one_add_shift_pow_apply] at hab
      by_contra h
      exact hab (ite_eq_right fun h' ↦ h h'.2)
    -- Its entry across the run is a binomial coefficient that is nonzero modulo `p`.
    · intro a b ha hb
      dsimp only at hb ⊢
      -- Normalize the matrix index difference to the weight of this syllable.
      rw [coe_rep_of_zpow, one_add_shift_pow_apply, ite_eq_left ⟨by omega, by rwa [ha, hb]⟩,
        show (b : ℕ) - a = p ^ padicValInt p e by rw [ha, hb]; simp [weight]]
      refine natCast_choose_pow_padicValInt_ne_zero_of_modEq (e := e)
        (K := (D + 1) * ((D + 1) - 1) / 2 + (D + 1))
        (hs0 _ List.mem_cons_self) ?_ ?_
      · have := Nat.lt_pow_self hp.out.one_lt (n := padicValInt p e)
        have : weight p e ≤ D := by omega
        simp only [weight] at this
        omega
      · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by simp [hp.out.ne_zero]))]
        exact_mod_cast Int.mod_modEq _ _
    -- Position `L + weight p e` is spelled `x`, which differs from the next syllable's letter.
    · intro c hc
      right
      rw [hrunx]
      cases s with
      | nil => simp at hc
      | cons d s =>
        obtain rfl : d = c := by simpa using hc
        exact fun h ↦ (List.isChain_cons_cons.mp hsc).1 (Option.some_injective _ h)

end Tracking

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every nonidentity element of an arbitrary free group is excluded by a normal subgroup
of finite index whose quotient is a p-group, for every prime p. -/
theorem exists_normal_is_p_group_quotient_not_mem {w : FreeGroup X} (hw : w ≠ 1) :
    ∃ (N : Subgroup (FreeGroup X)) (_ : N.Normal),
      N.FiniteIndex ∧ IsPGroup p (FreeGroup X ⧸ N) ∧ w ∉ N := by
  classical
  obtain ⟨s, hs, rfl⟩ := exists_isSyllableNormal w
  have hs₀ : s ≠ [] := by
    rintro rfl
    exact hw (by simp)
  let D := totalWeight p s
  let ρ := rep (p := p) (letters p s) D
  letI : Finite ρ.range := inferInstance
  refine ⟨ρ.ker, inferInstance, Subgroup.finiteIndex_ker ρ,
    (IsPGroup.of_card (group_card (p := p) D)).of_injective
      (QuotientGroup.kerLift ρ) (QuotientGroup.kerLift_injective ρ), fun hmem ↦ ?_⟩
  have hD : 0 < D := by
    obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs₀
    have := one_le_weight (p := p) a.2
    simp only [D, totalWeight, List.map_cons, List.sum_cons]
    omega
  have hR : RowInv D (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) 0 := by
    refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
    · by_contra h
      exact hb (Matrix.one_apply_ne fun h' ↦ h (by rw [← h']; rfl))
    · rw [show b = 0 from Fin.ext hb, Matrix.one_apply_eq]
      exact one_ne_zero
  have hterminal := (RowInv.mul_rep (letters p s) D s hs 0
    (spells_letters _ _ s 0 (fun j _ ↦ by rw [zero_add]) (zero_add _)) 1 hR
    (fun _ _ ↦ Or.inl rfl)).2 ⟨D, by omega⟩ rfl
  have hrep : rep (p := p) (letters p s) D (syllableProd s) = 1 :=
    MonoidHom.mem_ker.mp hmem
  rw [hrep, map_one, one_mul] at hterminal
  exact hterminal (Matrix.one_apply_ne fun h ↦ by
    simp [Fin.ext_iff] at h
    omega)

end FreeGroupPrimeQuotientSeparation
