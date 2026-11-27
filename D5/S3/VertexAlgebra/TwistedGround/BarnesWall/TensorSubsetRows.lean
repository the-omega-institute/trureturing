/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorSubsetRows
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scaled tensor rows identify the integral tail and ambient Pauli action. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliQuotientMaps

/-! Pauli row operations on the scaled subset basis of the Barnes–Wall
tensor lattice. -/

open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorSubsetRows

open TailPauliPairing (Word flip parity parity_flip)

variable {ι : Type} [LinearOrder ι]

def included (u v : Word ι) : Prop := ∀ r, v r = true → u r = true

open Classical in
noncomputable def subsetRow (u v : Word ι) : ℚ := if included u v then 1 else 0

private theorem included_split (u v : Word ι) (r : ι) :
    included u v ↔ (∀ t, t ≠ r → v t = true → u t = true) ∧
      (v r = true → u r = true) := by
  constructor
  · intro h
    exact ⟨fun t _ => h t, h r⟩
  · rintro ⟨h, hr⟩ t ht
    by_cases he : t = r
    · subst t
      exact hr ht
    · exact h t he ht

/-- Swapping the ambient coordinates in one tensor slot gives the integer
row replacement in KRR Appendix A.2 before the row scalings. -/
theorem subsetRow_X (u v : Word ι) (r : ι) :
    subsetRow u (flip v r) =
      if u r then subsetRow u v else subsetRow (flip u r) v - subsetRow u v := by
  classical
  simp only [subsetRow, included_split (r := r)]
  have hv : (∀ t, t ≠ r → flip v r t = true → u t = true) ↔
      (∀ t, t ≠ r → v t = true → u t = true) := by
    apply forall_congr'
    intro t
    by_cases ht : t = r <;> simp [TailPauliPairing.flip, ht]
  have hu : (∀ t, t ≠ r → v t = true → flip u r t = true) ↔
      (∀ t, t ≠ r → v t = true → u t = true) := by
    apply forall_congr'
    intro t
    by_cases ht : t = r <;> simp [TailPauliPairing.flip, ht]
  rw [hv, hu]
  by_cases h : ∀ t, t ≠ r → v t = true → u t = true <;>
    cases hur : u r <;> cases hvr : v r <;>
    norm_num [h, TailPauliPairing.flip, hur, hvr]

/-- The ambient diagonal sign gives the second integer row replacement
before the row scalings. -/
theorem subsetRow_Z (u v : Word ι) (r : ι) :
    (if v r then (-1 : ℚ) else 1) * subsetRow u v =
      if u r then 2 * subsetRow (flip u r) v - subsetRow u v else subsetRow u v := by
  classical
  simp only [subsetRow, included_split (r := r)]
  have hu : (∀ t, t ≠ r → v t = true → flip u r t = true) ↔
      (∀ t, t ≠ r → v t = true → u t = true) := by
    apply forall_congr'
    intro t
    by_cases ht : t = r <;> simp [TailPauliPairing.flip, ht]
  rw [hu]
  by_cases h : ∀ t, t ≠ r → v t = true → u t = true <;>
    cases hur : u r <;> cases hvr : v r <;>
    norm_num [h, TailPauliPairing.flip, hur, hvr]
  all_goals split <;> norm_num [*]

variable [Fintype ι]

def falseCount (u : Word ι) : ℕ := (Finset.univ.filter fun r => u r = false).card

open LatticeTwistedGroundRealization.SignQuotient (F₂)

omit [LinearOrder ι] in
/-- With an even number of tail slots, zero-coordinate parity and
one-coordinate parity agree. -/
theorem falseCount_mod_two_eq_zero_iff (u : Word ι)
    (heven : (Fintype.card ι : F₂) = 0) :
    falseCount u % 2 = 0 ↔ parity u = 0 := by
  have hcard : (falseCount u : F₂) = ∑ r, if u r = false then 1 else 0 := by
    rw [falseCount, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    split <;> simp [*]
  have hsum : (falseCount u : F₂) + parity u = (Fintype.card ι : F₂) := by
    rw [hcard, parity, ← Finset.sum_add_distrib]
    have hs : ∀ r : ι, (if u r = false then (1 : F₂) else 0) +
        (if u r then (1 : F₂) else 0) = 1 := by
      intro r
      cases u r <;> simp
    simp [hs]
  rw [heven] at hsum
  rw [← CharTwo.add_eq_zero.mp hsum, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

private theorem falseCount_flip_false (u : Word ι) (r : ι) (hu : u r = false) :
    falseCount (flip u r) + 1 = falseCount u := by
  let s := Finset.univ.filter fun t => u t = false
  have hr : r ∈ s := by simp [s, hu]
  have hset : (Finset.univ.filter fun t => flip u r t = false) = s.erase r := by
    ext t
    by_cases ht : t = r <;> simp [s, TailPauliPairing.flip, ht, hu]
  unfold falseCount
  rw [hset]
  simpa [s] using Finset.card_erase_add_one hr

private theorem falseCount_flip_true (u : Word ι) (r : ι) (hu : u r = true) :
    falseCount (flip u r) = falseCount u + 1 := by
  let s := Finset.univ.filter fun t => u t = false
  have hr : r ∉ s := by simp [s, hu]
  have hset : (Finset.univ.filter fun t => flip u r t = false) = insert r s := by
    ext t
    by_cases ht : t = r <;> simp [s, TailPauliPairing.flip, ht, hu]
  unfold falseCount
  rw [hset]
  exact Finset.card_insert_of_notMem hr

/-- The common normalization of the Barnes–Wall basis is independent of
the word. Its word-dependent multiplier is the indicated power of two. -/
def rowScale (u : Word ι) : ℚ := 2 ^ ((falseCount u + 1) / 2)

noncomputable def scaledRow (u v : Word ι) : ℚ := rowScale u * subsetRow u v

private theorem scale_flip_X (u : Word ι) (r : ι) (hu : u r = false) :
    rowScale u = (if falseCount u % 2 = 0 then 1 else 2) * rowScale (flip u r) := by
  have h := falseCount_flip_false u r hu
  unfold rowScale
  split
  · rename_i he
    have e : (falseCount u + 1) / 2 = (falseCount (flip u r) + 1) / 2 := by omega
    rw [e, one_mul]
  · rename_i ho
    have e : (falseCount u + 1) / 2 = (falseCount (flip u r) + 1) / 2 + 1 := by omega
    rw [e, pow_succ, mul_comm]

private theorem scale_flip_Z (u : Word ι) (r : ι) (hu : u r = true) :
    2 * rowScale u = (if falseCount u % 2 = 0 then 1 else 2) * rowScale (flip u r) := by
  have h := falseCount_flip_true u r hu
  unfold rowScale
  split
  · rename_i he
    have e : (falseCount (flip u r) + 1) / 2 = (falseCount u + 1) / 2 + 1 := by omega
    rw [e, pow_succ, one_mul, mul_comm]
  · rename_i ho
    have e : (falseCount (flip u r) + 1) / 2 = (falseCount u + 1) / 2 := by omega
    rw [e]

/-- Swapping the ambient coordinate gives the actual scaled integer
row replacement for a Pauli X. -/
theorem scaledRow_X (u v : Word ι) (r : ι) :
    scaledRow u (flip v r) = if u r then scaledRow u v else
      (if falseCount u % 2 = 0 then 1 else 2) * scaledRow (flip u r) v - scaledRow u v := by
  unfold scaledRow
  rw [subsetRow_X]
  cases hu : u r
  · simp only [Bool.false_eq_true, ite_false, mul_sub]
    rw [← mul_assoc, ← scale_flip_X u r hu]
  · simp

/-- The ambient Pauli Z sign gives the second scaled integer row replacement. -/
theorem scaledRow_Z (u v : Word ι) (r : ι) :
    (if v r then (-1 : ℚ) else 1) * scaledRow u v = if u r then
      (if falseCount u % 2 = 0 then 1 else 2) * scaledRow (flip u r) v - scaledRow u v
      else scaledRow u v := by
  unfold scaledRow
  rw [mul_left_comm, subsetRow_Z]
  cases hu : u r
  · simp
  · simp only [ite_true, mul_sub]
    rw [← mul_assoc, mul_comm (rowScale u) 2, scale_flip_Z u r hu, mul_assoc]

open TailPauliQuotientMaps (Coeff slot slotDev_apply toggle wordAction signedWord selections select)

/-- Synthesis in the scaled subset basis, with the overall scale omitted. -/
noncomputable def synthesize (a : Coeff ι) (v : Word ι) : ℚ :=
  ∑ u, (a u : ℚ) * scaledRow u v

omit [LinearOrder ι] in
private theorem falseCount_lt_of_included {u v : Word ι} (h : included u v) (hne : u ≠ v) :
    falseCount u < falseCount v := by
  unfold falseCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    cases hv : v t
    · rfl
    · exact Bool.false_ne_true (ht.symm.trans (h t hv)) |>.elim
  · intro he
    apply hne
    funext t
    have hh := Finset.ext_iff.mp he t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    cases hu : u t <;> cases hv : v t <;> simp_all

/-- The scaled subset rows give faithful coordinates on the integer
span of the tensor basis. -/
theorem synthesize_injective : Function.Injective (synthesize (ι := ι)) := by
  intro a b hab
  have hmain (n : ℕ) : ∀ u : Word ι, falseCount u = n → a u = b u := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hu
      let F (v : Word ι) : ℚ := ((a v : ℚ) - (b v : ℚ)) * scaledRow v u
      have hs : ∑ v, F v = 0 := by
        simp only [F, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (congrFun hab u)
      rw [Finset.sum_eq_single u] at hs
      · have huu : included u u := fun _ h => h
        have hscale : rowScale u ≠ 0 := pow_ne_zero _ (by norm_num)
        have hdiff : (a u : ℚ) - (b u : ℚ) = 0 := by
          simp only [F, scaledRow, subsetRow, huu, ite_true, mul_one] at hs
          exact (mul_eq_zero.mp hs).resolve_right hscale
        exact_mod_cast sub_eq_zero.mp hdiff
      · intro v _ hv
        by_cases hvu : included v u
        · have hlt := falseCount_lt_of_included hvu hv
          rw [hu] at hlt
          simp [F, ih _ hlt _ rfl]
        · simp [F, scaledRow, subsetRow, hvu]
      · exact fun h => (h (Finset.mem_univ u)).elim
  exact funext fun u => hmain (falseCount u) u rfl

/-- The integral tail generator acts through synthesis as the literal
ambient Pauli generator. -/
theorem synthesize_slot (heven : (Fintype.card ι : F₂) = 0)
    (a : Coeff ι) (r : ι) (isZ : Bool) (v : Word ι) :
    synthesize (slot 0 r isZ a) v =
      if isZ then (if v r then (-1 : ℚ) else 1) * synthesize a v
      else synthesize a (flip v r) := by
  let diag (u : Word ι) : ℚ := if u r = isZ then -1 else 1
  let off (u : Word ι) : ℚ := if u r = isZ then if parity u = 0 then 1 else 2 else 0
  let E : Word ι ≃ Word ι :=
    ⟨fun u => TailPauliPairing.flip u r, fun u => TailPauliPairing.flip u r,
      fun u => TailPauliQuotientMaps.flip_flip u r, fun u => TailPauliQuotientMaps.flip_flip u r⟩
  have hpar (u : Word ι) : parity (flip u r) = 0 ↔ parity u ≠ 0 := by
    rw [parity_flip, toggle]
  have hcoord (u : Word ι) :
      (slot 0 r isZ a u : ℚ) = diag u * (a u : ℚ) + off (flip u r) * (a (flip u r) : ℚ) := by
    change ((a u + TailPauliQuotientMaps.slotDev 0 r isZ a u : ℤ) : ℚ) = _
    rw [slotDev_apply]
    by_cases hd : u r = isZ <;> by_cases hf : flip u r r = isZ <;>
      by_cases hp : parity u = 0 <;>
      simp [hd, hf, hp, diag, off, hpar, Int.cast_add, Int.cast_mul] <;> ring
  have hrow (u : Word ι) :
      (if isZ then (if v r then (-1 : ℚ) else 1) * scaledRow u v
        else scaledRow u (flip v r)) =
        diag u * scaledRow u v + off u * scaledRow (flip u r) v := by
    have he := falseCount_mod_two_eq_zero_iff u heven
    cases isZ
    · simp only [Bool.false_eq_true, ite_false, scaledRow_X]
      cases hu : u r <;> simp [diag, off, hu, he, sub_eq_add_neg, add_comm]
    · simp only [ite_true, scaledRow_Z]
      cases hu : u r <;> simp [diag, off, hu, he, sub_eq_add_neg, add_comm]
  have hreindex : (∑ u, (off (TailPauliPairing.flip u r) *
      (a (TailPauliPairing.flip u r) : ℚ)) * scaledRow u v) =
      ∑ u, (off u * (a u : ℚ)) * scaledRow (TailPauliPairing.flip u r) v := by
    simpa [E, TailPauliQuotientMaps.flip_flip] using E.sum_comp
      (fun u => (off u * (a u : ℚ)) * scaledRow (TailPauliPairing.flip u r) v)
  calc
    synthesize (slot 0 r isZ a) v =
        (∑ u, (diag u * (a u : ℚ)) * scaledRow u v) +
          ∑ u, (off (TailPauliPairing.flip u r) * (a (TailPauliPairing.flip u r) : ℚ)) *
            scaledRow u v := by
      simp only [synthesize, hcoord, add_mul, Finset.sum_add_distrib]
    _ = ∑ u, (a u : ℚ) * (diag u * scaledRow u v + off u * scaledRow (flip u r) v) := by
      rw [hreindex, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by
      simp_rw [← hrow]
      cases isZ <;> simp [synthesize, Finset.mul_sum, mul_left_comm]

/-- The action on ambient coordinates, in the same row-action order as
the list of Pauli factors. -/
def ambientWord : List (ι × Bool) → (Word ι → ℚ) → (Word ι → ℚ)
  | [], f => f
  | (r, isZ) :: word, f =>
      ambientWord word fun v => if isZ then (if v r then -1 else 1) * f v else f (flip v r)

private theorem synthesize_word (heven : (Fintype.card ι : F₂) = 0)
    (word : List (ι × Bool)) (a : Coeff ι) :
    synthesize (wordAction 0 word a) = ambientWord word (synthesize a) := by
  induction word generalizing a with
  | nil => rfl
  | cons factor word ih =>
    obtain ⟨r, isZ⟩ := factor
    change synthesize (wordAction 0 word (slot 0 r isZ a)) = _
    rw [ih, funext (synthesize_slot heven a r isZ)]
    rfl

/-- Integral coefficients transport the actual signed Pauli action on
the rational ambient space. -/
theorem synthesize_signedWord (heven : (Fintype.card ι : F₂) = 0)
    (negative : Bool) (word : List (ι × Bool)) (a : Coeff ι) :
    synthesize (signedWord negative 0 word a) =
      if negative then -ambientWord word (synthesize a) else ambientWord word (synthesize a) := by
  cases negative
  · exact synthesize_word heven word a
  · have hneg (b : Coeff ι) : synthesize (-b) = -synthesize b := by
      funext v
      simp [synthesize, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    change synthesize (-wordAction 0 word a) = -ambientWord word (synthesize a)
    rw [hneg, synthesize_word heven]

private def bit (b : Bool) : F₂ := if b then 1 else 0

private theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

private theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> simp [bit, CharTwo.add_self_eq_zero]

private def translate (x : ι → F₂) (v : Word ι) : Word ι :=
  fun i => decide (bit (v i) + x i = 1)

omit [LinearOrder ι] [Fintype ι] in
private theorem bit_translate (x : ι → F₂) (v : Word ι) (i : ι) :
    bit (translate x v i) = bit (v i) + x i := by
  have h : ∀ q : F₂, bit (decide (q = 1)) = q := by decide +kernel
  exact h _

omit [Fintype ι] in
private theorem translate_flip (x : ι → F₂) (v : Word ι) (r : ι) :
    flip (translate x v) r = translate (select r false false + x) v := by
  funext i
  apply bit_injective
  rw [bit_translate]
  by_cases hi : i = r
  · subst i
    simp [TailPauliPairing.flip, bit_not, bit_translate, select, add_comm, add_left_comm, add_assoc]
  · simp [TailPauliPairing.flip, bit_translate, select, hi]

omit [LinearOrder ι] [Fintype ι] in
private theorem translate_twice (x : ι → F₂) (v : Word ι) :
    translate x (translate x v) = v := by
  funext i
  apply bit_injective
  rw [bit_translate, bit_translate, add_assoc, CharTwo.add_self_eq_zero, add_zero]

def rationalSign (e : F₂) : ℚ := if e = 0 then 1 else -1

private theorem rationalSign_add : ∀ a b : F₂,
    rationalSign (a + b) = rationalSign a * rationalSign b := by
  decide +kernel

private theorem ambientWord_normal (word : List (ι × Bool)) :
    ∃ e : F₂, ∀ (f : Word ι → ℚ) (v : Word ι),
      ambientWord word f v =
        rationalSign (e + ∑ r, selections true word r * bit (v r)) *
          f (translate (selections false word) v) := by
  induction word with
  | nil =>
    refine ⟨0, fun f v => ?_⟩
    have hv : translate (0 : ι → F₂) v = v := by
      funext i
      apply bit_injective
      simp [bit_translate]
    simp [ambientWord, selections, hv, rationalSign]
  | cons factor tail ih =>
    obtain ⟨r, isZ⟩ := factor
    obtain ⟨e, he⟩ := ih
    let x := selections false tail
    let z := selections true tail
    cases isZ
    · refine ⟨e, fun f v => ?_⟩
      rw [ambientWord, he]
      simp [selections, select, translate_flip]
    · refine ⟨e + x r, fun f v => ?_⟩
      rw [ambientWord, he]
      have hs : (if translate x v r then (-1 : ℚ) else 1) =
          rationalSign (bit (translate x v r)) := by
        cases translate x v r <;> simp [rationalSign, bit]
      change rationalSign (e + ∑ i, z i * bit (v i)) *
        ((if translate x v r then -1 else 1) * f (translate x v)) = _
      rw [hs, ← mul_assoc, ← rationalSign_add, bit_translate]
      have hz : ∑ i, select r true true i * bit (v i) = bit (v r) := by
        simp [select, ite_mul]
      have hx : select r true false = (0 : ι → F₂) := by
        funext i
        simp [select]
      simp only [selections, hx, zero_add]
      change rationalSign ((e + ∑ i, z i * bit (v i)) + (bit (v r) + x r)) *
        f (translate x v) =
          rationalSign (e + x r + ∑ i, (select r true true i + z i) * bit (v i)) *
            f (translate x v)
      simp only [add_mul, Finset.sum_add_distrib, hz]
      congr 2
      abel

/-- Squaring any ambient Pauli word reads the parity of the number
of slots with both one X and one Z selection. -/
theorem ambientWord_square (word : List (ι × Bool)) (f : Word ι → ℚ) (v : Word ι) :
    ambientWord word (ambientWord word f) v =
      rationalSign (∑ r, selections false word r * selections true word r) * f v := by
  obtain ⟨e, h⟩ := ambientWord_normal word
  let x := selections false word
  let z := selections true word
  rw [h _ v, h f (translate x v), translate_twice, ← mul_assoc, ← rationalSign_add]
  have ha : (e + ∑ i, z i * bit (v i)) +
      (e + ∑ i, z i * bit (translate x v i)) = ∑ i, x i * z i := by
    simp only [bit_translate, mul_add, Finset.sum_add_distrib, mul_comm (z _) (x _)]
    rw [show (e + ∑ i, z i * bit (v i)) +
      (e + ((∑ i, z i * bit (v i)) + ∑ i, x i * z i)) =
      (e + e) + ((∑ i, z i * bit (v i)) + ∑ i, z i * bit (v i)) + ∑ i, x i * z i by abel]
    simp [CharTwo.add_self_eq_zero]
  rw [show (e + ∑ i, z i * bit (v i)) +
      (e + ∑ i, z i * bit (translate x v i)) = _ from ha]

private theorem falseCount_cons {n : ℕ} (head : Bool) (u : Word (Fin n)) :
    falseCount (Fin.cons head u) = (if head then 0 else 1) + falseCount u := by
  simp only [falseCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  cases head <;> simp

private theorem included_cons {n : ℕ} (a b : Bool) (u v : Word (Fin n)) :
    included (Fin.cons a u) (Fin.cons b v) ↔ (b = true → a = true) ∧ included u v := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun r => by simpa using h r.succ⟩
  · rintro ⟨hhead, htail⟩ r
    refine Fin.cases ?_ (fun i => ?_) r
    · simpa using hhead
    · simpa using htail i

private theorem rowScale_cons {n : ℕ} (heven : (n : F₂) = 0)
    (head : Bool) (u : Word (Fin n)) :
    rowScale (Fin.cons head u) =
      (if head then 1 else if parity u = 0 then 2 else 1) * rowScale u := by
  have he : (Fintype.card (Fin n) : F₂) = 0 := by simpa using heven
  have hp := falseCount_mod_two_eq_zero_iff u he
  unfold rowScale
  rw [falseCount_cons]
  simp only [← hp]
  cases head
  · simp only [Bool.false_eq_true, ite_false]
    split
    · rename_i h
      rw [show (1 + falseCount u + 1) / 2 = (falseCount u + 1) / 2 + 1 by omega]
      rw [pow_succ, mul_comm]
    · rename_i h
      rw [show (1 + falseCount u + 1) / 2 = (falseCount u + 1) / 2 by omega, one_mul]
  · simp

private theorem scaledRow_cons {n : ℕ} (heven : (n : F₂) = 0)
    (a b : Bool) (u v : Word (Fin n)) :
    scaledRow (Fin.cons a u) (Fin.cons b v) =
      if b = true ∧ a = false then 0
      else (if a then 1 else if parity u = 0 then 2 else 1) * scaledRow u v := by
  classical
  unfold scaledRow
  rw [rowScale_cons heven]
  simp only [subsetRow, included_cons]
  cases a <;> cases b <;> simp

/-- The coefficient vector in the two blocks of the full subset basis. -/
def coefficientBlocks {n : ℕ} (a b : Coeff (Fin n)) : Coeff (Fin (n + 1)) :=
  fun u => if u 0 then b (Fin.tail u) else a (Fin.tail u)

/-- Splitting the literal Barnes–Wall tensor basis at its first bit
identifies the ambient pair as `(a+b,b)`, with the first block of
lattice coefficients embedded at the prescribed parity-dependent scale. -/
theorem synthesize_blocks {n : ℕ} (heven : (n : F₂) = 0)
    (a b : Coeff (Fin n)) (head : Bool) (v : Word (Fin n)) :
    synthesize (coefficientBlocks a b) (Fin.cons head v) =
      if head then synthesize b v else synthesize (TailPauliQuotientMaps.embed 0 a + b) v := by
  let E := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
  unfold synthesize
  rw [← E.sum_comp (fun u => (coefficientBlocks a b u : ℚ) * scaledRow u (Fin.cons head v)),
    Fintype.sum_prod_type]
  simp only [E, Fin.consEquiv, Equiv.coe_fn_mk, coefficientBlocks, Fin.cons_zero, Fin.tail_cons,
    scaledRow_cons heven, Fintype.sum_bool]
  cases head
  · simp only [Bool.false_eq_true, false_and, ite_false, ite_true, one_mul, Pi.add_apply,
      Int.cast_add, add_mul, Finset.sum_add_distrib]
    conv_lhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    by_cases hp : parity u = 0
    · simp [TailPauliQuotientMaps.embed, hp, Int.cast_mul]
      ring
    · simp [TailPauliQuotientMaps.embed, hp, Int.cast_mul]
  · simp

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorSubsetRows
