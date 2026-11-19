/- GID: D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks
   mirror-E: none(waiver:symbolic-CAR-certificate)
   anchors: []
   utility: none
   digest: Clifford conjugations and the exact block reduction of the three-mode channel. -/

import D5.S3.Quantum.Fermionic.BravyiThreeModeDeterminantOrder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The physical three-mode CAR blocks in chiral coordinates

The generators and weights are those of sections 1 and 2 of
`three-mode-bravyi-entropy-certificate.py`. We use coordinates
`(+1,+2,+3,+4,-1,-2,-3,-4)` and ordinary matrix trace. The entries of the
Clifford words lie in the Gaussian integers. Their row permutations give
small finite coefficient checks, with all amplitudes and weights kept symbolic.
-/

namespace D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks

open scoped Matrix BigOperators ComplexConjugate
open BravyiThreeModeDeterminantOrder

abbrev SpinMatrix := Matrix (Fin 8) (Fin 8) ℂ

private abbrev G := GaussianInt
private abbrev Rows := Fin 8 → Fin 8 × G

private def gi : G := ⟨0, 1⟩

private def partner : Fin 6 → Fin 4 → Fin 4 :=
  ![![1, 0, 3, 2], ![1, 0, 3, 2], ![2, 3, 0, 1],
    ![2, 3, 0, 1], ![3, 2, 1, 0], ![3, 2, 1, 0]]

private def upperPhase : Fin 6 → Fin 4 → G :=
  ![![1, -1, 1, -1], ![gi, -gi, -gi, gi], ![1, -1, -1, 1],
    ![gi, gi, -gi, -gi], ![1, 1, -1, -1], ![gi, -gi, gi, -gi]]

private def positive (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
private def negative (i : Fin 4) : Fin 8 := ⟨4 + i.val, by omega⟩
private def coordinate (i : Fin 8) : Fin 4 := ⟨i.val % 4, by omega⟩

private def paritySign (i : Fin 8) : G := if i.val < 4 then 1 else -1

private def generatorRows (j : Fin 6) : Rows := fun i =>
  let a := coordinate i
  if i.val < 4 then (negative (partner j a), upperPhase j a)
  else (positive (partner j a), -star (upperPhase j a))

private def parityRows : Rows := fun i => (i, paritySign i)
private def identityRows : Rows := fun i => (i, 1)

private def mulRows (r s : Rows) : Rows := fun i =>
  ((s (r i).1).1, (r i).2 * (s (r i).1).2)

noncomputable section

private def asMatrix (r : Rows) : SpinMatrix :=
  fun i j => if j = (r i).1 then GaussianInt.toComplex (r i).2 else 0

private theorem asMatrix_identity : asMatrix identityRows = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [asMatrix, identityRows]
  · simp [asMatrix, identityRows, h, Ne.symm h]

private theorem asMatrix_mul (r s : Rows) :
    asMatrix r * asMatrix s = asMatrix (mulRows r s) := by
  ext i j
  simp only [Matrix.mul_apply, asMatrix, mulRows, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, map_mul]
  split <;> simp_all

/-- The skew upper-right block of the Hermitian flip operator. -/
def B (j : Fin 6) : Matrix (Fin 4) (Fin 4) ℂ := fun a b =>
  if b = partner j a then GaussianInt.toComplex (upperPhase j a) else 0

/-- The flip operator with chiral blocks `[0,B; Bᴴ,0]`. -/
def U (j : Fin 6) : SpinMatrix := asMatrix (generatorRows j)

/-- The chirality operator, with value +1 on the first four coordinates. -/
def parity : SpinMatrix := asMatrix parityRows

private theorem upperPhase_skew (j : Fin 6) (a : Fin 4) :
    upperPhase j (partner j a) = -upperPhase j a := by
  revert a
  fin_cases j <;> decide

private theorem partner_involutive (j : Fin 6) (a : Fin 4) :
    partner j (partner j a) = a := by
  revert a
  fin_cases j <;> decide

theorem B_skew (j : Fin 6) : (B j)ᵀ = -B j := by
  ext a b
  change (if a = partner j b then GaussianInt.toComplex (upperPhase j b) else 0) = -B j a b
  by_cases h : b = partner j a
  · subst b
    simp [B, partner_involutive, upperPhase_skew]
  · have h' : a ≠ partner j b := by
      intro h'
      apply h
      simpa only [partner_involutive] using (congrArg (partner j) h').symm
    simp [B, h, h']

private theorem coordinate_positive (a : Fin 4) : coordinate (positive a) = a := by
  apply Fin.ext
  change a.val % 4 = a.val
  exact Nat.mod_eq_of_lt a.isLt

private theorem coordinate_negative (a : Fin 4) : coordinate (negative a) = a := by
  apply Fin.ext
  change (4 + a.val) % 4 = a.val
  omega

private theorem negative_injective : Function.Injective negative := by
  intro a b h
  simpa only [coordinate_negative] using congrArg coordinate h

private theorem positive_injective : Function.Injective positive := by
  intro a b h
  simpa only [coordinate_positive] using congrArg coordinate h

/-- Chiral matrix entries, with the lower-left block given by the adjoint. -/
theorem U_chiral_entries (j : Fin 6) (a b : Fin 4) :
    U j (positive a) (positive b) = 0 ∧
    U j (negative a) (negative b) = 0 ∧
    U j (positive a) (negative b) = B j a b ∧
    U j (negative a) (positive b) = (B j)ᴴ a b := by
  have hp : (positive a).val < 4 := a.isLt
  have hn : ¬ (negative a).val < 4 := by change ¬ 4 + a.val < 4; omega
  have hpne (x y : Fin 4) : positive x ≠ negative y := by
    intro h
    have h' : x.val = 4 + y.val := congrArg Fin.val h
    omega
  have hpartner : a = partner j b ↔ b = partner j a := by
    constructor <;> intro h
    · simpa only [partner_involutive] using (congrArg (partner j) h).symm
    · simpa only [partner_involutive] using (congrArg (partner j) h).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [U, asMatrix, generatorRows, hp, coordinate_positive, hpne]
  · simp [U, asMatrix, generatorRows, hn, coordinate_negative,
      fun x y => (hpne x y).symm]
  · simp [U, asMatrix, generatorRows, hp, coordinate_positive, negative_injective.eq_iff, B]
  · by_cases h : b = partner j a
    · subst b
      simp [U, asMatrix, generatorRows, hn, coordinate_negative, B, partner_involutive,
        upperPhase_skew, Matrix.conjTranspose_apply]
    · have h' := mt hpartner.mp h
      simp [U, asMatrix, generatorRows, hn, coordinate_negative, positive_injective.eq_iff,
        B, h, h', Matrix.conjTranspose_apply]

private theorem asMatrix_hermitian (r : Rows)
    (hback : ∀ a, (r (r a).1).1 = a)
    (hstar : ∀ a, (r (r a).1).2 = star (r a).2) :
    (asMatrix r)ᴴ = asMatrix r := by
  ext i k
  by_cases h : k = (r i).1
  · subst k
    simp [asMatrix, Matrix.conjTranspose_apply, hback, hstar, GaussianInt.toComplex_star]
  · have h' : i ≠ (r k).1 := by
      intro he
      apply h
      rw [he, hback]
    simp [asMatrix, Matrix.conjTranspose_apply, h, h']

private theorem paritySign_star (i : Fin 8) : star (paritySign i) = paritySign i := by
  by_cases h : i.val < 4 <;> simp [paritySign, h]

private theorem parity_hermitian : parityᴴ = parity :=
  asMatrix_hermitian parityRows (fun _ => rfl) (fun i => (paritySign_star i).symm)

private theorem generatorRows_involution (j : Fin 6) (i : Fin 8) :
    mulRows (generatorRows j) (generatorRows j) i = identityRows i := by
  revert i
  fin_cases j <;> decide

private theorem generatorRows_hermitian (j : Fin 6) (i : Fin 8) :
    (generatorRows j ((generatorRows j i).1)).2 = star (generatorRows j i).2 := by
  revert i
  fin_cases j <;> decide

theorem U_square (j : Fin 6) : U j * U j = 1 := by
  rw [U, asMatrix_mul, ← asMatrix_identity]
  exact congrArg asMatrix (funext (generatorRows_involution j))

theorem U_hermitian (j : Fin 6) : (U j)ᴴ = U j :=
  asMatrix_hermitian (generatorRows j)
    (fun a => congrArg Prod.fst (generatorRows_involution j a))
    (generatorRows_hermitian j)

private def majoranaRows (j : Fin 6) : Rows :=
  fun i => ((generatorRows j i).1, -gi * (paritySign i * (generatorRows j i).2))

/-- The physical Majoranas `γ_j = -i P U_j`. -/
def majorana (j : Fin 6) : SpinMatrix := asMatrix (majoranaRows j)

private theorem gi_complex : GaussianInt.toComplex gi = Complex.I := by
  simp [gi, GaussianInt.toComplex_def']

theorem majorana_eq (j : Fin 6) : majorana j = (-Complex.I) • (parity * U j) := by
  rw [parity, U, asMatrix_mul]
  ext i k
  by_cases h : k = (generatorRows j i).1 <;>
    simp [majorana, asMatrix, mulRows, majoranaRows, parityRows, h, gi_complex,
      Matrix.smul_apply, smul_eq_mul]

private theorem majoranaRows_square (j : Fin 6) (i : Fin 8) :
    mulRows (majoranaRows j) (majoranaRows j) i = identityRows i := by
  revert i
  fin_cases j <;> decide

private theorem majoranaRows_star (j : Fin 6) (i : Fin 8) :
    (majoranaRows j (majoranaRows j i).1).2 = star (majoranaRows j i).2 := by
  revert i
  fin_cases j <;> decide

theorem majorana_square (j : Fin 6) : majorana j * majorana j = 1 := by
  rw [majorana, asMatrix_mul, ← asMatrix_identity]
  exact congrArg asMatrix (funext (majoranaRows_square j))

theorem majorana_hermitian (j : Fin 6) : (majorana j)ᴴ = majorana j :=
  asMatrix_hermitian (majoranaRows j)
    (fun a => congrArg Prod.fst (majoranaRows_square j a))
    (majoranaRows_star j)

private def flipSign (j k : Fin 6) : G := if j = k then -1 else 1

private theorem flip_rows (j k : Fin 6) (i : Fin 8) :
    mulRows (mulRows (generatorRows j) (majoranaRows k)) (generatorRows j) i =
      ((majoranaRows k i).1, flipSign j k * (majoranaRows k i).2) := by
  revert k i
  fin_cases j <;> decide

/-- Each physical flip changes the sign of exactly one Majorana. -/
theorem U_flip (j k : Fin 6) :
    U j * majorana k * (U j)ᴴ =
      (if j = k then (-1 : ℂ) else 1) • majorana k := by
  rw [U_hermitian]
  simp only [U, majorana, asMatrix_mul]
  ext i b
  by_cases h : b = (majoranaRows k i).1 <;> by_cases hj : j = k <;>
    simp [asMatrix, flip_rows, flipSign, Matrix.smul_apply, smul_eq_mul, h, hj]

private theorem majorana_anticomm_rows (j k : Fin 6) (i : Fin 8) :
    j ≠ k →
    mulRows (majoranaRows j) (majoranaRows k) i =
      ((mulRows (majoranaRows k) (majoranaRows j) i).1,
        -(mulRows (majoranaRows k) (majoranaRows j) i).2) := by
  revert k i
  fin_cases j <;> decide

theorem majorana_anticomm (j k : Fin 6) (h : j ≠ k) :
    majorana j * majorana k = -(majorana k * majorana j) := by
  simp only [majorana, asMatrix_mul]
  ext i b
  by_cases hb : b = (mulRows (majoranaRows k) (majoranaRows j) i).1 <;>
    simp [asMatrix, majorana_anticomm_rows j k i h, hb]

/-- Bit `j` selects `U_j`. Words multiply in increasing generator order. -/
def indices (mask : Fin 64) : List (Fin 6) :=
  (List.finRange 6).filter (fun j => mask.val.testBit j.val)

/-- Degree of the Clifford word of a subset of the six generators. -/
def degree (mask : Fin 64) : Fin 7 :=
  ⟨(indices mask).length, Nat.lt_succ_of_le
    ((List.length_filter_le _ _).trans (by simp))⟩

private def rowsOf : List (Fin 6) → Rows
  | [] => identityRows
  | j :: js => mulRows (generatorRows j) (rowsOf js)

private def wordRows (mask : Fin 64) : Rows := rowsOf (indices mask)

/-- The ordered Clifford word of a subset. -/
def word (mask : Fin 64) : SpinMatrix := asMatrix (wordRows mask)

private theorem rowsOf_eq_prod (js : List (Fin 6)) :
    asMatrix (rowsOf js) = (js.map U).prod := by
  induction js with
  | nil => exact asMatrix_identity
  | cons j js ih =>
    simp only [rowsOf, List.map_cons, List.prod_cons, ← ih, U, asMatrix_mul]

theorem word_eq_prod (mask : Fin 64) : word mask = ((indices mask).map U).prod :=
  rowsOf_eq_prod (indices mask)

/-- Conjugation by the given Clifford word. -/
def conjugateWord (mask : Fin 64) (L : SpinMatrix) : SpinMatrix :=
  word mask * L * (word mask)ᴴ

private def rowPhase (r : Rows) (i j : Fin 8) : G := (r i).2 * star (r j).2

private theorem asMatrix_conjugate_apply (r : Rows) (L : SpinMatrix) (i j : Fin 8) :
    (asMatrix r * L * (asMatrix r)ᴴ) i j =
      GaussianInt.toComplex (rowPhase r i j) * L (r i).1 (r j).1 := by
  have hleft (k : Fin 8) :
      (asMatrix r * L) i k = GaussianInt.toComplex (r i).2 * L (r i).1 k := by
    simp only [Matrix.mul_apply, asMatrix, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hright (k : Fin 8) :
      (asMatrix r)ᴴ k j =
        if k = (r j).1 then GaussianInt.toComplex (star (r j).2) else 0 := by
    by_cases h : k = (r j).1 <;>
      simp [Matrix.conjTranspose_apply, asMatrix, h]
  rw [Matrix.mul_apply]
  simp only [hleft, hright, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, rowPhase, map_mul]
  ring

private theorem conjugateWord_apply (mask : Fin 64) (L : SpinMatrix) (i j : Fin 8) :
    conjugateWord mask L i j =
      GaussianInt.toComplex (rowPhase (wordRows mask) i j) *
        L (wordRows mask i).1 (wordRows mask j).1 :=
  asMatrix_conjugate_apply _ _ _ _

private theorem prod_U_unitary (js : List (Fin 6)) :
    let W := (js.map U).prod
    W * Wᴴ = 1 ∧ Wᴴ * W = 1 := by
  induction js with
  | nil => simp
  | cons j js ih =>
    let W := (js.map U).prod
    change W * Wᴴ = 1 ∧ Wᴴ * W = 1 at ih
    simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, U_hermitian]
    change (U j * W) * (Wᴴ * U j) = 1 ∧ (Wᴴ * U j) * (U j * W) = 1
    constructor
    · calc
        _ = U j * (W * Wᴴ) * U j := by simp only [mul_assoc]
        _ = 1 := by rw [ih.1, mul_one, U_square]
    · calc
        _ = Wᴴ * (U j * U j) * W := by simp only [mul_assoc]
        _ = 1 := by rw [U_square, mul_one, ih.2]

/-- Every word in the 64-term channel is unitary. -/
theorem word_unitary (m : Fin 64) :
    word m * (word m)ᴴ = 1 ∧ (word m)ᴴ * word m = 1 := by
  rw [word_eq_prod]
  exact prod_U_unitary (indices m)

private theorem prod_U_flip (js : List (Fin 6)) (k : Fin 6) :
    let W := (js.map U).prod
    W * majorana k * Wᴴ = ((js.map fun j => if j = k then (-1 : ℂ) else 1).prod) • majorana k := by
  induction js with
  | nil => simp
  | cons j js ih =>
    let W := (js.map U).prod
    let s : ℂ := (js.map fun l => if l = k then (-1 : ℂ) else 1).prod
    change W * majorana k * Wᴴ = s • majorana k at ih
    simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul]
    calc
      _ = U j * (W * majorana k * Wᴴ) * (U j)ᴴ := by simp only [W, mul_assoc]
      _ = _ := by rw [ih, mul_smul_comm, smul_mul_assoc, U_flip, smul_smul, mul_comm]

private theorem prod_index_sign (m : Fin 64) (k : Fin 6) :
    ((indices m).map fun j => if j = k then (-1 : ℤ) else 1).prod =
      if m.val.testBit k.val then -1 else 1 := by
  revert m
  fin_cases k <;> decide +kernel

/-- Every subset word flips precisely its selected Majoranas. -/
theorem conjugateWord_majorana (m : Fin 64) (k : Fin 6) :
    conjugateWord m (majorana k) =
      (if m.val.testBit k.val then (-1 : ℂ) else 1) • majorana k := by
  rw [conjugateWord, word_eq_prod, prod_U_flip]
  apply congrArg (fun a : ℂ => a • majorana k)
  have h := congrArg (Int.castRingHom ℂ) (prod_index_sign m k)
  cases hb : m.val.testBit k.val <;>
    simpa only [hb, Bool.false_eq_true, ite_false, ite_true, map_list_prod, List.map_map,
      Function.comp_def, apply_ite, map_neg, map_one] using h

/-- Conjugation by any of the 64 words acts multiplicatively on Majorana
products, with the sign given by the product of the selected flips. -/
theorem conjugateWord_majorana_prod (m : Fin 64) (js : List (Fin 6)) :
    conjugateWord m (js.map majorana).prod =
      (js.map fun k => if m.val.testBit k.val then (-1 : ℂ) else 1).prod •
        (js.map majorana).prod := by
  have hmul (L M : SpinMatrix) :
      conjugateWord m (L * M) = conjugateWord m L * conjugateWord m M := by
    unfold conjugateWord
    calc
      _ = word m * L * ((word m)ᴴ * word m) * M * (word m)ᴴ := by
        rw [(word_unitary m).2, mul_one]
        simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  induction js with
  | nil => simp [conjugateWord, (word_unitary m).1]
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, hmul, conjugateWord_majorana, ih,
      List.map_cons, List.prod_cons, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A sum of the word conjugations selected by a Boolean predicate. -/
def selectedTwirl (take : Fin 64 → Bool) (L : SpinMatrix) : SpinMatrix :=
  ∑ m : Fin 64, if take m then conjugateWord m L else 0

/-- The degree-`k` part of the unweighted word twirl. -/
def degreeTwirl (k : Fin 7) (L : SpinMatrix) : SpinMatrix :=
  selectedTwirl (fun m => decide (degree m = k)) L

private theorem selectedTwirl_apply (take : Fin 64 → Bool) (L : SpinMatrix) (i j : Fin 8) :
    selectedTwirl take L i j =
      ∑ m : Fin 64, if take m then conjugateWord m L i j else 0 := by
  rw [selectedTwirl, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : take m <;> simp [h]

private theorem degreeTwirl_apply (k : Fin 7) (L : SpinMatrix) (i j : Fin 8) :
    degreeTwirl k L i j =
      ∑ m : Fin 64, if degree m = k then conjugateWord m L i j else 0 := by
  simp [degreeTwirl, selectedTwirl_apply]

/-- Probability of each individual degree-`k` conjugation. -/
def weight (lam : ℝ) (k : Fin 7) : ℝ :=
  ((1 + lam) / 2) ^ (6 - k.val) * ((1 - lam) / 2) ^ k.val

/-- The physical channel written as its 64 weighted conjugations. -/
def channel (lam : ℝ) (L : SpinMatrix) : SpinMatrix :=
  ∑ m : Fin 64, (weight lam (degree m) : ℂ) • conjugateWord m L

private theorem sum_by_degree (w : Fin 7 → ℂ) (L : SpinMatrix) (i j : Fin 8) :
    (∑ k : Fin 7, w k * degreeTwirl k L i j) =
      ∑ m : Fin 64, w (degree m) * conjugateWord m L i j := by
  simp_rw [degreeTwirl_apply, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem channel_by_degree (lam : ℝ) (L : SpinMatrix) :
    channel lam L = ∑ k : Fin 7, (weight lam k : ℂ) • degreeTwirl k L := by
  ext i j
  simpa only [channel, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    (sum_by_degree (fun k => (weight lam k : ℂ)) L i j).symm

private def complementMask (m : Fin 64) : Fin 64 := ⟨63 - m.val, by omega⟩

private theorem complement_involutive (m : Fin 64) : complementMask (complementMask m) = m := by
  apply Fin.ext
  change 63 - (63 - m.val) = m.val
  omega

private def maskComplement : Fin 64 ≃ Fin 64 where
  toFun := complementMask
  invFun := complementMask
  left_inv := complement_involutive
  right_inv := complement_involutive

private def complementPhase (m : Fin 64) : G :=
  (wordRows (complementMask m) 0).2 * star (wordRows m 0).2

private theorem complement_data (i : Fin 8) :
    ∀ m : Fin 64, wordRows (complementMask m) i =
      ((wordRows m i).1, complementPhase m * (paritySign i * (wordRows m i).2)) := by
  fin_cases i <;> decide

private theorem complement_phase_unit (m : Fin 64) :
    complementPhase m * star (complementPhase m) = 1 :=
  (by decide : ∀ m : Fin 64, complementPhase m * star (complementPhase m) = 1) m

private theorem complement_degree (m : Fin 64) :
    (degree (complementMask m)).val + (degree m).val = 6 :=
  (by decide : ∀ m : Fin 64, (degree (complementMask m)).val + (degree m).val = 6) m

private theorem complement_eq_rev (m : Fin 64) :
    degree (complementMask m) = (degree m).rev := by
  apply Fin.ext
  have h := complement_degree m
  simp only [Fin.val_rev]
  omega

private theorem complement_conjugate (m : Fin 64) (L : SpinMatrix) (i j : Fin 8) :
    conjugateWord (complementMask m) L i j =
      GaussianInt.toComplex (paritySign i) * GaussianInt.toComplex (paritySign j) *
        conjugateWord m L i j := by
  simp only [conjugateWord_apply, rowPhase, complement_data i m, complement_data j m,
    star_mul, paritySign_star]
  have h :
      (complementPhase m * (paritySign i * (wordRows m i).2)) *
          ((star ((wordRows m j).2) * paritySign j) * star (complementPhase m)) =
        (paritySign i * paritySign j) * ((wordRows m i).2 * star ((wordRows m j).2)) := by
    calc
      _ = (complementPhase m * star (complementPhase m)) *
          ((paritySign i * paritySign j) * ((wordRows m i).2 * star ((wordRows m j).2))) := by
        ring
      _ = _ := by rw [complement_phase_unit, one_mul]
  rw [h]
  simp only [map_mul, mul_assoc]

private theorem degreeTwirl_rev_apply (k : Fin 7) (L : SpinMatrix) (i j : Fin 8) :
    degreeTwirl k.rev L i j =
      GaussianInt.toComplex (paritySign i) * GaussianInt.toComplex (paritySign j) *
        degreeTwirl k L i j := by
  rw [degreeTwirl_apply, degreeTwirl_apply, ← maskComplement.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change (if degree (complementMask m) = k.rev then
      conjugateWord (complementMask m) L i j else 0) = _
  rw [complement_eq_rev]
  by_cases h : degree m = k
  · simp [h, complement_conjugate]
  · have h' : (degree m).rev ≠ k.rev := fun he => h (Fin.rev_injective he)
    simp [h, h']

/-- Complementary degrees are conjugate by chirality for every input. -/
theorem degreeTwirl_complement (k : Fin 7) (L : SpinMatrix) :
    degreeTwirl k.rev L = parity * degreeTwirl k L * parity := by
  ext i j
  rw [degreeTwirl_rev_apply]
  have h := asMatrix_conjugate_apply parityRows (degreeTwirl k L) i j
  rw [show (asMatrix parityRows)ᴴ = asMatrix parityRows from parity_hermitian] at h
  simpa only [parity, parityRows, rowPhase, paritySign_star, map_mul] using h.symm

/- A coefficient vector gives a linear form in (c²,p²,q²,cp,cq,pq). -/
private abbrev Coeff := Fin 6 → ℤ

private def variableCoeff (r : Fin 6) : Coeff := fun s => if s = r then 1 else 0

private def evalCoeff (v : Fin 6 → ℂ) (f : Coeff) : ℂ :=
  ∑ r, (f r : ℂ) * v r

@[simp] private theorem eval_zero (v : Fin 6 → ℂ) : evalCoeff v 0 = 0 := by
  simp [evalCoeff]

@[simp] private theorem eval_variable (v : Fin 6 → ℂ) (r : Fin 6) :
    evalCoeff v (variableCoeff r) = v r := by
  simp [evalCoeff, variableCoeff, apply_ite, ite_mul, Finset.sum_ite_eq']

@[simp] private theorem eval_add (v : Fin 6 → ℂ) (f g : Coeff) :
    evalCoeff v (f + g) = evalCoeff v f + evalCoeff v g := by
  simp [evalCoeff, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private def scaleCoeff (a : ℤ) (f : Coeff) : Coeff := a • f

@[simp] private theorem eval_scale (v : Fin 6 → ℂ) (a : ℤ) (f : Coeff) :
    evalCoeff v (scaleCoeff a f) = (a : ℂ) * evalCoeff v f := by
  simp [scaleCoeff, evalCoeff, Pi.smul_apply, Finset.mul_sum, mul_assoc]

private def lowCoeffs (k : Fin 3) : Matrix (Fin 8) (Fin 8) Coeff :=
  let x := variableCoeff 0
  let y := variableCoeff 1
  let z := variableCoeff 2
  let u := variableCoeff 3
  let v := variableCoeff 4
  let w := variableCoeff 5
  if k = 0 then
    !![x, 0, 0, 0, u, v, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0;
       u, 0, 0, 0, y, w, 0, 0;
       v, 0, 0, 0, w, z, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0]
  else if k = 1 then
    !![scaleCoeff 2 z, scaleCoeff (-2) w, 0, 0, 0, 0, 0, 0;
       scaleCoeff (-2) w, scaleCoeff 2 y, 0, 0, 0, 0, 0, 0;
       0, 0, scaleCoeff 2 (y + z), 0, 0, 0, 0, scaleCoeff (-2) v;
       0, 0, 0, scaleCoeff 2 (y + z), 0, 0, scaleCoeff 2 v, 0;
       0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, scaleCoeff 2 x, 0, 0;
       0, 0, 0, scaleCoeff 2 v, 0, 0, scaleCoeff 2 x, 0;
       0, 0, scaleCoeff (-2) v, 0, 0, 0, 0, scaleCoeff 2 x]
  else
    !![scaleCoeff 3 x, 0, 0, 0, scaleCoeff (-3) u, v, 0, 0;
       0, scaleCoeff 4 x, 0, 0, scaleCoeff (-4) v, 0, 0, 0;
       0, 0, scaleCoeff 4 x, 0, 0, 0, 0, 0;
       0, 0, 0, scaleCoeff 4 x, 0, 0, 0, 0;
       scaleCoeff (-3) u, scaleCoeff (-4) v, 0, 0, scaleCoeff 3 y + scaleCoeff 4 z,
         scaleCoeff (-1) w, 0, 0;
       v, 0, 0, 0, scaleCoeff (-1) w, scaleCoeff 4 y + scaleCoeff 3 z, 0, 0;
       0, 0, 0, 0, 0, 0, scaleCoeff 4 (y + z), 0;
       0, 0, 0, 0, 0, 0, 0, scaleCoeff 4 (y + z)]

/-- Real pure-spinor amplitudes in the original chiral order. -/
def spinor (c p q : ℝ) : Fin 8 → ℝ := ![c, 0, 0, 0, p, q, 0, 0]

/-- The physical rank-one outer product with ordinary trace. -/
def normalInput (c p q : ℝ) : SpinMatrix :=
  fun i j => (spinor c p q i : ℂ) * star (spinor c p q j : ℂ)

theorem trace_normalInput (c p q : ℝ) :
    (normalInput c p q).trace = ((c ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ) := by
  norm_num [Matrix.trace, Matrix.diag, normalInput, spinor, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Complex.star_def, pow_two]

private def amplitudeProducts (c p q : ℝ) : Fin 6 → ℂ :=
  ![((c ^ 2 : ℝ) : ℂ), ((p ^ 2 : ℝ) : ℂ), ((q ^ 2 : ℝ) : ℂ),
    ((c * p : ℝ) : ℂ), ((c * q : ℝ) : ℂ), ((p * q : ℝ) : ℂ)]

private theorem normalInput_apply (c p q : ℝ) (i j : Fin 8) :
    normalInput c p q i j = evalCoeff (amplitudeProducts c p q) (lowCoeffs 0 i j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [normalInput, spinor, lowCoeffs, amplitudeProducts, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Complex.star_def, pow_two]
  all_goals ring

/-- Include the degrees 0, 1, and 2 among the seven possible degrees. -/
def degreeIndex (k : Fin 3) : Fin 7 := ⟨k.val, by omega⟩

/-- Degree-zero, one, and two formulas. Amplitudes need no normalization here. -/
def lowBlock (k : Fin 3) (c p q : ℝ) : SpinMatrix :=
  fun i j => evalCoeff (amplitudeProducts c p q) (lowCoeffs k i j)

private def constantCoeff (i j : Fin 8) : Coeff :=
  if i = j then scaleCoeff 8 (variableCoeff 0 + variableCoeff 1 + variableCoeff 2) else 0

-- The coefficient computation visits each selected mask once for a fixed entry and variable.
private def sumCoeff (take : Fin 64 → Bool) (i j : Fin 8) (r : Fin 6) : G :=
  (List.ofFn (fun m : Fin 64 =>
    if take m then
      rowPhase (wordRows m) i j * (lowCoeffs 0 (wordRows m i).1 (wordRows m j).1 r : G)
    else 0)).sum

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Reduce 64 masks for each of the 3 × 8 × 8 × 6 coefficient comparisons.
private theorem low_coeff_check (k : Fin 3) (i j : Fin 8) :
    ∀ r : Fin 6, sumCoeff (fun m => decide (degree m = degreeIndex k)) i j r =
      (lowCoeffs k i j r : G) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Reduce 64 masks for each of the 8 × 8 × 6 completeness coefficients.
private theorem total_coeff_check (i j : Fin 8) :
    ∀ r : Fin 6, sumCoeff (fun _ => true) i j r = (constantCoeff i j r : G) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem selectedTwirl_normal_apply (take : Fin 64 → Bool) (c p q : ℝ) (i j : Fin 8) :
    selectedTwirl take (normalInput c p q) i j =
      ∑ r : Fin 6, GaussianInt.toComplex (sumCoeff take i j r) * amplitudeProducts c p q r := by
  have hterm (m : Fin 64) :
      (if take m then conjugateWord m (normalInput c p q) i j else 0) =
        ∑ r : Fin 6, GaussianInt.toComplex (if take m then rowPhase (wordRows m) i j *
          (lowCoeffs 0 (wordRows m i).1 (wordRows m j).1 r : G) else 0) *
          amplitudeProducts c p q r := by
    by_cases h : take m
    · simp only [h, ite_true, conjugateWord_apply, normalInput_apply, evalCoeff, map_mul,
        map_intCast, Finset.mul_sum, mul_assoc]
    · simp [h]
  simp_rw [selectedTwirl_apply, hterm]
  rw [Finset.sum_comm]
  simp only [sumCoeff, List.sum_ofFn, map_sum, Finset.sum_mul]

/-- The actual degree-zero, one, and two word sums equal the displayed formulas. -/
theorem degreeTwirl_low (k : Fin 3) (c p q : ℝ) :
    degreeTwirl (degreeIndex k) (normalInput c p q) = lowBlock k c p q := by
  ext i j
  simp only [degreeTwirl, selectedTwirl_normal_apply, low_coeff_check, lowBlock, evalCoeff,
    map_intCast]

/-- Completeness of the 64-word sum on the real rank-one normal form. -/
theorem normal_unweighted_twirl (c p q : ℝ) :
    selectedTwirl (fun _ => true) (normalInput c p q) =
      (8 * ((c ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ)) • (1 : SpinMatrix) := by
  ext i j
  rw [selectedTwirl_normal_apply]
  simp only [total_coeff_check, map_intCast]
  change evalCoeff (amplitudeProducts c p q) (constantCoeff i j) = _
  by_cases h : i = j <;>
    norm_num [constantCoeff, h, Matrix.smul_apply, Matrix.one_apply, amplitudeProducts,
      smul_eq_mul]

private theorem weight_zero (k : Fin 7) : (weight 0 k : ℂ) = 1 / 64 := by
  fin_cases k <;> norm_num [weight]

/-- At zero attenuation the channel gives the completely mixed state. -/
theorem channel_normal_zero (c p q : ℝ) (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    channel 0 (normalInput c p q) = (1 / 8 : ℂ) • (1 : SpinMatrix) := by
  calc
    _ = (1 / 64 : ℂ) • selectedTwirl (fun _ => true) (normalInput c p q) := by
      simp only [channel, selectedTwirl, ite_true, weight_zero, Finset.smul_sum]
    _ = _ := by
      rw [normal_unweighted_twirl, hn, Complex.ofReal_one, smul_smul]
      norm_num

private theorem degree_zero_iff (m : Fin 64) : degree m = 0 ↔ m = 0 :=
  (by decide +kernel : ∀ m : Fin 64, degree m = 0 ↔ m = 0) m

private theorem weight_one (k : Fin 7) : (weight 1 k : ℂ) = if k = 0 then 1 else 0 := by
  fin_cases k <;> norm_num [weight]

/-- At unit attenuation the channel is the identity on every matrix. -/
theorem channel_one (L : SpinMatrix) : channel 1 L = L := by
  have hword : word 0 = 1 := by
    change asMatrix identityRows = 1
    exact asMatrix_identity
  simp only [channel, weight_one, degree_zero_iff, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, conjugateWord, hword,
    Matrix.conjTranspose_one, one_mul, mul_one]

private theorem channel_apply_paired (lam c p q : ℝ) (i j : Fin 8) :
    let w : Fin 7 → ℂ := fun k => (weight lam k : ℂ)
    let s := GaussianInt.toComplex (paritySign i) * GaussianInt.toComplex (paritySign j)
    channel lam (normalInput c p q) i j =
      w 3 * ((8 * ((c ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ)) • (1 : SpinMatrix)) i j
        + ((w 0 - w 3) + s * (w 6 - w 3)) * lowBlock 0 c p q i j
        + ((w 1 - w 3) + s * (w 5 - w 3)) * lowBlock 1 c p q i j
        + ((w 2 - w 3) + s * (w 4 - w 3)) * lowBlock 2 c p q i j := by
  let L := normalInput c p q
  let s := GaussianInt.toComplex (paritySign i) * GaussianInt.toComplex (paritySign j)
  have h4 := degreeTwirl_rev_apply 2 L i j
  have h5 := degreeTwirl_rev_apply 1 L i j
  have h6 := degreeTwirl_rev_apply 0 L i j
  change degreeTwirl 4 L i j = s * degreeTwirl 2 L i j at h4
  change degreeTwirl 5 L i j = s * degreeTwirl 1 L i j at h5
  change degreeTwirl 6 L i j = s * degreeTwirl 0 L i j at h6
  have htotal : (∑ k : Fin 7, degreeTwirl k L i j) =
      ((8 * ((c ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ)) • (1 : SpinMatrix)) i j := by
    calc
      _ = ∑ m : Fin 64, conjugateWord m L i j := by
        simpa only [one_mul] using sum_by_degree (fun _ => 1) L i j
      _ = selectedTwirl (fun _ => true) L i j := by simp [selectedTwirl_apply]
      _ = _ := congrArg (fun A : SpinMatrix => A i j) (normal_unweighted_twirl c p q)
  have h0 := congrArg (fun A : SpinMatrix => A i j) (degreeTwirl_low 0 c p q)
  have h1 := congrArg (fun A : SpinMatrix => A i j) (degreeTwirl_low 1 c p q)
  have h2 := congrArg (fun A : SpinMatrix => A i j) (degreeTwirl_low 2 c p q)
  change degreeTwirl 0 L i j = lowBlock 0 c p q i j at h0
  change degreeTwirl 1 L i j = lowBlock 1 c p q i j at h1
  change degreeTwirl 2 L i j = lowBlock 2 c p q i j at h2
  dsimp only
  rw [channel_by_degree]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  -- Expand seven scalar terms and eliminate the common degree-three contribution.
  simp only [Fin.sum_univ_seven] at htotal ⊢
  rw [h4, h5, h6, h0, h1, h2] at htotal ⊢
  simp only [Matrix.smul_apply, smul_eq_mul] at htotal
  dsimp only [s] at htotal ⊢
  linear_combination (weight lam 3 : ℂ) * htotal

private def basisOrder : Fin 8 → Fin 8 := ![0, 1, 4, 5, 2, 7, 3, 6]
private def inverseOrder : Fin 8 → Fin 8 := ![0, 1, 4, 6, 2, 3, 7, 5]

/-- Change to the order (+1,+2,-1,-2,+3,-4,+4,-3). -/
def blockPermutation : Equiv.Perm (Fin 8) where
  toFun := basisOrder
  invFun := inverseOrder
  left_inv := by decide
  right_inv := by decide

private def blockSign (i : Fin 8) : G := if i = 5 then -1 else 1

private def blockRows : Rows := fun i => (blockPermutation i, blockSign i)

/-- The new coordinates in the old basis, with -4 rephased by -1. -/
def signedBasis : SpinMatrix := asMatrix blockRows

theorem signedBasis_isUnitary : signedBasis * signedBasisᴴ = 1 := by
  ext i j
  have h := asMatrix_conjugate_apply blockRows (1 : SpinMatrix) i j
  simp only [mul_one] at h
  change (signedBasis * signedBasisᴴ) i j = _ at h
  rw [h]
  by_cases hij : i = j
  · subst j
    by_cases hs : i = 5 <;> simp [blockRows, blockSign, hs, rowPhase]
  · simp [blockRows, rowPhase, Matrix.one_apply, hij]

/-- Entrywise action of the signed basis change. -/
def signedReorder (L : SpinMatrix) : SpinMatrix := fun i j =>
  GaussianInt.toComplex (blockSign i) * GaussianInt.toComplex (blockSign j) *
    L (blockPermutation i) (blockPermutation j)

theorem signedReorder_eq (L : SpinMatrix) : signedReorder L = signedBasis * L * signedBasisᴴ := by
  ext i j
  have hs (a : Fin 8) : star (blockSign a) = blockSign a := by
    by_cases h : a = 5 <;> simp [blockSign, h]
  simp only [signedReorder, signedBasis, asMatrix_conjugate_apply, blockRows, rowPhase,
    hs, map_mul]

private def blockIndex (i : Fin 8) : Fin 4 ⊕ (Fin 2 ⊕ Fin 2) :=
  if h : i.val < 4 then .inl ⟨i.val, h⟩
  else if h' : i.val < 6 then .inr (.inl ⟨i.val - 4, by omega⟩)
  else .inr (.inr ⟨i.val - 6, by omega⟩)

/-- Direct sum of a 4-by-4 block and two copies of a 2-by-2 block. -/
def determinantBlocks (M : Matrix (Fin 4) (Fin 4) ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  (Matrix.fromBlocks M 0 0 (Matrix.fromBlocks N 0 0 N)).submatrix blockIndex blockIndex

/-- The characteristic polynomial records both copies of the complementary block. -/
theorem determinantBlocks_charpoly (M : Matrix (Fin 4) (Fin 4) ℝ)
    (N : Matrix (Fin 2) (Fin 2) ℝ) :
    (determinantBlocks M N).charpoly = M.charpoly * (N.charpoly * N.charpoly) := by
  let e : Fin 4 ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin 8 :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  have he : blockIndex = e.symm := by
    funext i
    fin_cases i <;> rfl
  unfold determinantBlocks
  rw [he, ← Matrix.reindex_apply, Matrix.charpoly_reindex]
  simp only [Matrix.charpoly_fromBlocks_zero₁₂]

private theorem chiral_entries (lam c p q : ℝ) :
    chiral lam c p q =
      let t := lam ^ 2
      let kp := (1 - t ^ 2) * (1 - t * (2 * c ^ 2 - 1)) / 8
      let km := (1 - t ^ 2) * (1 + t * (2 * c ^ 2 - 1)) / 8
      let a := t * (1 + t) / 2
      let b := t * (1 - t) / 2
      let v := lam ^ 3 * c * p
      let w := lam * ((1 + t) ^ 2 / 4) * c * q
      let f := -lam * ((1 - t) ^ 2 / 4) * c * q
      !![kp + a * c ^ 2 - b * p ^ 2, -b * p * q, v, w;
         -b * p * q, kp - b * q ^ 2, f, 0;
         v, f, km + a * p ^ 2 - b * c ^ 2, a * p * q;
         w, 0, a * p * q, km + a * q ^ 2] := by
  rfl

private theorem complement_entries (lam c q : ℝ) :
    complement lam c q =
      let t := lam ^ 2
      let kp := (1 - t ^ 2) * (1 - t * (2 * c ^ 2 - 1)) / 8
      let km := (1 - t ^ 2) * (1 + t * (2 * c ^ 2 - 1)) / 8
      let v := lam * (1 - t ^ 2) * c * q / 4
      !![kp, v; v, km] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The 64-word physical channel on a normalized real pure spinor gives
exactly the determinant module's chiral block and two copies of its
complementary block. The identity holds for all real attenuation parameters. -/
theorem channel_normal_blocks (lam c p q : ℝ) (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    signedBasis * channel lam (normalInput c p q) * signedBasisᴴ =
      (determinantBlocks (chiral lam c p q) (complement lam c q)).map Complex.ofReal := by
  rw [← signedReorder_eq, chiral_entries, complement_entries]
  have hqReal : q ^ 2 = 1 - c ^ 2 - p ^ 2 := by linarith only [hn]
  have hqComplex : (q : ℂ) ^ 2 = 1 - (c : ℂ) ^ 2 - (p : ℂ) ^ 2 := by
    exact_mod_cast hqReal
  ext i j
  simp only [signedReorder, channel_apply_paired, hn, Complex.ofReal_one]
  fin_cases i <;> fin_cases j <;>
    norm_num [blockPermutation, basisOrder, blockSign, paritySign, weight, lowBlock, lowCoeffs,
      amplitudeProducts, determinantBlocks, blockIndex, Matrix.submatrix_apply,
      Matrix.fromBlocks, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ, GaussianInt.toComplex_neg,
      GaussianInt.toComplex_one, smul_eq_mul]
  all_goals
    push_cast
    simp (config := { failIfUnchanged := false }) only [hqComplex]
    ring

end

end D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
