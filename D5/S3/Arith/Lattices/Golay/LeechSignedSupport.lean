/- GID: D5/S3/Arith/Lattices/Golay/LeechSignedSupport
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/LeechSignedSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed coordinate supports and parity reconstruction. -/

import D5.S3.Arith.Lattices.Golay.IntegerLeech
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

/-! # Signed finite coordinate supports -/

open scoped BigOperators
noncomputable section
namespace D5.S3.Arith.Lattices.Golay.LeechSignedSupport
open GolayEncoder IntegerLeech
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

abbrev I := Fin 24

def liftBit (c : F2) : ℤ := c.val

def sign (c : F2) : ℤ := 1 - 2 * liftBit c

private theorem bit_cases (c : F2) : c = 0 ∨ c = 1 := by
  have hc := ZMod.val_lt c
  have h : c.val = 0 ∨ c.val = 1 := by omega
  rcases h with h | h
  · left; apply ZMod.val_injective 2; simpa using h
  · right; apply ZMod.val_injective 2; change c.val = 1; exact h

@[simp] theorem liftBit_zero : liftBit 0 = 0 := by decide +kernel
@[simp] theorem liftBit_one : liftBit 1 = 1 := by decide +kernel
@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

@[simp] theorem liftBit_cast (c : F2) : (liftBit c : F2) = c := by
  simp [liftBit]

@[simp] theorem sign_sq (c : F2) : sign c ^ 2 = 1 := by
  rcases bit_cases c with rfl | rfl <;> norm_num

@[simp] theorem sign_ne_zero (c : F2) : sign c ≠ 0 := by
  have := sign_sq c
  intro h; rw [h] at this; norm_num at this

@[simp] theorem sign_mod_two (c : F2) : sign c % 2 = 1 := by
  rcases bit_cases c with rfl | rfl <;> norm_num

@[simp] theorem sign_cast (c : F2) : (sign c : F2) = 1 := by
  rcases bit_cases c with rfl | rfl <;> decide +kernel

theorem sign_injective : Function.Injective sign := by
  intro c d h
  rcases bit_cases c with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl <;> simp_all

theorem sign_values (c : F2) : sign c = 1 ∨ sign c = -1 := by
  rcases bit_cases c with rfl | rfl <;> simp

def nzSupport (x : IntVector) : Finset I := Finset.univ.filter (fun i => x i ≠ 0)

def wordSupport (c : Word) : Finset I := Finset.univ.filter (fun i => c i ≠ 0)

@[simp] theorem mem_nzSupport (x : IntVector) (i : I) : i ∈ nzSupport x ↔ x i ≠ 0 := by
  simp [nzSupport]

@[simp] theorem mem_wordSupport (c : Word) (i : I) : i ∈ wordSupport c ↔ c i ≠ 0 := by
  simp [wordSupport]

@[simp] theorem wordSupport_card (c : Word) : (wordSupport c).card = weight c := by
  rw [Finset.card_eq_sum_ones]
  simp only [wordSupport, Finset.sum_filter, weight]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = 0 <;> simp [h]

/-- Sum a dependent function on a finite support without choosing an ordering. -/
theorem sum_on {A : Type*} [AddCommMonoid A] (S : Finset I) (f : S → A) :
    (∑ i : I, if h : i ∈ S then f ⟨i, h⟩ else 0) = ∑ j : S, f j := by
  calc
    _ = ∑ i ∈ S, if h : i ∈ S then f ⟨i, h⟩ else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [hi]
    _ = ∑ j : S, if h : j.val ∈ S then f ⟨j.val, h⟩ else 0 :=
      Finset.sum_subtype S (fun _ => Iff.rfl) _
    _ = _ := by apply Finset.sum_congr rfl; intro j _; simp [j.property]

/-- Literal coordinates; the signs are indexed by the support itself. -/
def signed (k : ℤ) (S : Finset I) (σ : S → F2) : IntVector :=
  fun i => if h : i ∈ S then k * sign (σ ⟨i, h⟩) else 0

@[simp] theorem signed_at (k : ℤ) (S : Finset I) (σ : S → F2) (i : S) :
    signed k S σ i.val = k * sign (σ i) := by simp [signed, i.property]

@[simp] theorem signed_off (k : ℤ) (S : Finset I) (σ : S → F2) {i : I}
    (hi : i ∉ S) : signed k S σ i = 0 := by simp [signed, hi]

theorem signed_sum (k : ℤ) (S : Finset I) (σ : S → F2) :
    (∑ i, signed k S σ i) =
      k * ((S.card : ℤ) - 2 * ∑ j : S, liftBit (σ j)) := by
  rw [show (∑ i, signed k S σ i) = ∑ j : S, k * sign (σ j) from by
    simpa only [signed] using (sum_on S (fun j => k * sign (σ j)))]
  calc
    (∑ j : S, k * sign (σ j)) = ∑ j : S, (k - (2 * k) * liftBit (σ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold sign
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

theorem signed_squareSum (k : ℤ) (S : Finset I) (σ : S → F2) :
    squareSum (signed k S σ) = k ^ 2 * S.card := by
  unfold squareSum
  calc
    _ = ∑ i : I, if i ∈ S then k ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ∈ S <;> simp [signed, h, mul_pow]
    _ = _ := by
      rw [Finset.sum_ite_mem_eq]
      simp [mul_comm]

theorem signed_support {k : ℤ} (hk : k ≠ 0) (S : Finset I) (σ : S → F2) :
    nzSupport (signed k S σ) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [nzSupport, signed, h, hk]

theorem signed_injective {k : ℤ} (hk : k ≠ 0) (S : Finset I) :
    Function.Injective (signed k S) := by
  intro σ τ h
  funext i
  apply sign_injective
  have he := congrFun h i.val
  rw [signed_at, signed_at] at he
  exact (mul_left_cancel₀ hk) he

/-- Recover the unique sign at each support coordinate. -/
theorem exists_signed {k : ℤ} (S : Finset I) (x : IntVector)
    (hon : ∀ i ∈ S, x i = k ∨ x i = -k)
    (hoff : ∀ i ∉ S, x i = 0) : ∃ σ : S → F2, signed k S σ = x := by
  let σ : S → F2 := fun i => if x i.val = k then 0 else 1
  refine ⟨σ, ?_⟩
  funext i
  by_cases hi : i ∈ S
  · rcases hon i hi with h | h
    · simp [signed, hi, σ, h]
    · by_cases hk : k = 0
      · simp [signed, hi, σ, h, hk]
      · have hn : -k ≠ k := by omega
        simp [signed, hi, σ, h, hn]
  · rw [signed_off k S σ hi, hoff i hi]

/-- The residue of the half of an even signed octad is its actual support word. -/
theorem signed_two_red (c : Word) (σ : wordSupport c → F2) :
    red (fun i => signed 2 (wordSupport c) σ i / 2) = c := by
  ext i
  change ((signed 2 (wordSupport c) σ i / 2 : ℤ) : F2) = c i
  by_cases hi : c i = 0
  · simp [signed, hi]
  · have hc : c i = 1 := (bit_cases (c i)).resolve_left hi
    have hiS : i ∈ wordSupport c := by simp [hi]
    have hx : signed 2 (wordSupport c) σ i = 2 * sign (σ ⟨i, hiS⟩) :=
      signed_at 2 (wordSupport c) σ ⟨i, hiS⟩
    have hd : 2 * sign (σ ⟨i, hiS⟩) / 2 = sign (σ ⟨i, hiS⟩) := by omega
    rw [hx, hd, sign_cast, hc]

/-- Even sign parity, expressed in the two-element field. -/
abbrev EvenSigns (S : Finset I) := {σ : S → F2 // ∑ i, σ i = 0}

/-- Delete one support coordinate; the omitted bit is forced by the parity equation.
This proves the count of even subsets without choosing an ordering of the octad. -/
def evenSignsEquiv (S : Finset I) (p : S) :
    EvenSigns S ≃ ({i : S // i ≠ p} → F2) where
  toFun σ i := σ.val i.val
  invFun τ := ⟨fun i => if h : i = p then -(∑ j, τ j) else τ ⟨i, h⟩, by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ p]
    simp only [dite_eq_left rfl]
    have hrest :
        (∑ x : {i : S // i ≠ p},
          if h : x.val = p then -(∑ j, τ j) else τ ⟨x.val, h⟩) = ∑ j, τ j := by
      apply Finset.sum_congr rfl
      intro x _
      rw [dite_eq_right x.property]
    rw [hrest]
    exact neg_add_cancel _⟩
  left_inv σ := by
    apply Subtype.ext
    funext i
    by_cases hi : i = p
    · subst i
      have hs := σ.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ p] at hs
      simp only [dite_eq_left rfl]
      calc
        -(∑ j : {i : S // i ≠ p}, σ.val j.val) =
            σ.val p - (σ.val p + ∑ j : {i : S // i ≠ p}, σ.val j.val) := by ring
        _ = σ.val p := by rw [hs]; simp
    · simp [hi]
  right_inv τ := by funext i; simp [i.property]

theorem evenSigns_card (S : Finset I) (hS : S.card = 8) :
    Fintype.card (EvenSigns S) = 128 := by
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hn
  rw [Fintype.card_congr (evenSignsEquiv S ⟨p, hp⟩), Fintype.card_fun]
  have hc : Fintype.card {i : S // i ≠ ⟨p, hp⟩} = 7 := by
    rw [Fintype.card_subtype_compl (fun i : S => i = ⟨p, hp⟩)]
    simp [hS]
  rw [hc]
  norm_num [ZMod.card]

theorem evenSigns_sum_div_two (S : Finset I) (σ : EvenSigns S) :
    2 ∣ ∑ i : S, liftBit (σ.val i) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  simpa using σ.property

theorem evenSigns_of_sum_div_two (S : Finset I) (σ : S → F2)
    (h : 2 ∣ ∑ i : S, liftBit (σ i)) : ∑ i, σ i = 0 := by
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simpa using hc

end D5.S3.Arith.Lattices.Golay.LeechSignedSupport
