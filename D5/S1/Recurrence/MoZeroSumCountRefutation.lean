/- GID: D5/S1/Recurrence/MoZeroSumCountRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/MoZeroSumCountRefutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff, mathlib/module/Mathlib.LinearAlgebra.Matrix.Vec]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/MoZeroSumCountRefutation.claim; result=D5/S1/Recurrence/MoZeroSumCountRefutation.result; claim=D5/S1/Recurrence/MoZeroSumCountRefutation.claim
   digest: Exact finite-digit prefix counts and bounded binary carry matrices. -/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Exact source counts and their finite bounded-carry representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S1.Recurrence.MoZeroSumCountRefutation

open scoped BigOperators Matrix Kronecker
open Polynomial Finset

/-- Index zero is the source's first positive index. -/
def sequence (n : ℕ) : ℤ :=
  if n % 2 = 0 then 4 ^ (n / 2 + 1) else 2 ^ (n / 2 + 1)

/-- The polynomial of the proposed minimal integer recurrence. -/
def characteristic : ℤ[X] := (X ^ 2 - C 4) * (X ^ 2 - C 2)

/-- Polynomial annihilation uses every original sequence index. -/
def Annihilates (a : ℕ → ℤ) (p : ℤ[X]) : Prop :=
  ∀ n, ∑ j ∈ p.support, p.coeff j * a (n + j) = 0

/-- Minimality among monic constant-integer-coefficient recurrences. -/
def MinimalCharacteristic (a : ℕ → ℤ) (p : ℤ[X]) : Prop :=
  p.Monic ∧ Annihilates a p ∧
    ∀ q : ℤ[X], q.Monic → Annihilates a q → p.natDegree ≤ q.natDegree

/-- Each member is an ordered assignment to the original prefix coordinates. -/
def zeroAssignments (a : ℕ → ℤ) (D : Finset ℤ) (n : ℕ) :=
  {d : Fin n → ↥D // ∑ i, (d i : ℤ) * a i = 0}

private instance (a : ℕ → ℤ) (D : Finset ℤ) (n : ℕ) :
    Fintype (zeroAssignments a D n) := by
  classical
  unfold zeroAssignments
  infer_instance

/-- This includes the empty-tuple convention only at length zero. -/
def sourceCount (a : ℕ → ℤ) (D : Finset ℤ) (n : ℕ) : ℕ :=
  Fintype.card (zeroAssignments a D n)

/-- Complex coefficients and an arbitrary initial cutoff retain the general
constant-coefficient convention; the source sequence starts at length one. -/
def CountRecurrence (s : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ c : Fin k → ℂ, ∃ N : ℕ, ∀ n ≥ N,
    (s (n + k + 1) : ℂ) = ∑ i : Fin k, c i * (s (n + i + 1) : ℂ)

/-- All three complex-root clauses of the displayed characterization. -/
def RootConditions (p : ℤ[X]) : Prop :=
  (∀ z : ℂ, (p.map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ ≠ 1) ∧
  (∀ z : ℂ, (p.map (Int.castRingHom ℂ)).IsRoot z → 1 < ‖z‖ →
    (p.map (Int.castRingHom ℂ)).rootMultiplicity z = 1) ∧
  (∀ z w : ℂ, (p.map (Int.castRingHom ℂ)).IsRoot z →
    (p.map (Int.castRingHom ℂ)).IsRoot w → 1 < ‖z‖ → 1 < ‖w‖ →
    ∃ k : ℕ, 0 < k ∧ (z / w) ^ k = 1)

/-- The entire MathOverflow 516232 revision-two iff, with no monotonicity,
alphabet bound, recurrence-order bound, or restriction to the candidate. -/
def claim : Prop :=
  ∀ (a : ℕ → ℤ) (p : ℤ[X]), (∀ n, 0 < a n) → MinimalCharacteristic a p →
    ((∀ D : Finset ℤ, CountRecurrence (sourceCount a D)) ↔ RootConditions p)

private abbrev Carry (M : ℕ) := ↥(Finset.Icc (-2 * (M : ℤ)) (2 * M))

private def zeroCarry (M : ℕ) : Carry M := ⟨0, by simp⟩

private def Assignments (D : Type) : List ℕ → Type
  | [] => PUnit
  | m :: ms => (Fin m → D) × Assignments D ms

private instance assignmentsFintype (D : Type) [Fintype D] :
    (ms : List ℕ) → Fintype (Assignments D ms)
  | [] => inferInstanceAs (Fintype PUnit)
  | m :: ms => @instFintypeProd (Fin m → D) (Assignments D ms)
      inferInstance (assignmentsFintype D ms)

private def digitSum {D : Type} (digit : D → ℤ) {m : ℕ} (d : Fin m → D) : ℤ :=
  ∑ i, digit (d i)

private def binaryValue {D : Type} (digit : D → ℤ) :
    (ms : List ℕ) → Assignments D ms → ℤ
  | [], _ => 0
  | _ :: ms, x => digitSum digit x.1 + 2 * binaryValue digit ms x.2

private def carryCount {D : Type} [Fintype D] (digit : D → ℤ)
    (ms : List ℕ) (c : ℤ) : ℕ :=
  Fintype.card {x : Assignments D ms // c + binaryValue digit ms x = 0}

private def transition {D : Type} [Fintype D] (digit : D → ℤ) (M m : ℕ) :
    Matrix (Carry M) (Carry M) ℕ :=
  fun c c' => Fintype.card {d : Fin m → D // (c : ℤ) + digitSum digit d = 2 * (c' : ℤ)}

private theorem digitSum_bounds {D : Type} (digit : D → ℤ) (M m : ℕ)
    (hd : ∀ d, -(M : ℤ) ≤ digit d ∧ digit d ≤ M) (hm : m ≤ 2)
    (d : Fin m → D) :
    -2 * (M : ℤ) ≤ digitSum digit d ∧ digitSum digit d ≤ 2 * M := by
  have hl := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (f := fun _ => -(M : ℤ)) (g := fun i => digit (d i)) (fun i _ => (hd (d i)).1)
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (f := fun i => digit (d i)) (g := fun _ => (M : ℤ)) (fun i _ => (hd (d i)).2)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hl hu
  have hm' : (m : ℤ) ≤ 2 := by exact_mod_cast hm
  have hM : (0 : ℤ) ≤ M := by positivity
  constructor <;> dsimp [digitSum] at * <;> nlinarith

private def splitZero {D : Type} [Fintype D] (digit : D → ℤ) (M m : ℕ)
    (hd : ∀ d, -(M : ℤ) ≤ digit d ∧ digit d ≤ M) (hm : m ≤ 2)
    (ms : List ℕ) (c : Carry M) :
    {x : Assignments D (m :: ms) // (c : ℤ) + binaryValue digit (m :: ms) x = 0} ≃
      Σ c' : Carry M,
        {d : Fin m → D // (c : ℤ) + digitSum digit d = 2 * (c' : ℤ)} ×
        {x : Assignments D ms // (c' : ℤ) + binaryValue digit ms x = 0} where
  toFun x := by
    let v := binaryValue digit ms x.val.2
    have hx : (c : ℤ) + digitSum digit x.val.1 + 2 * v = 0 := by
      simpa [binaryValue, v, add_assoc] using x.property
    have hc := Finset.mem_Icc.mp c.property
    have hb := digitSum_bounds digit M m hd hm x.val.1
    let c' : Carry M := ⟨-v, Finset.mem_Icc.mpr (by constructor <;> omega)⟩
    exact ⟨c', ⟨x.val.1, by dsimp [c']; omega⟩,
      ⟨x.val.2, by dsimp [c', v]; omega⟩⟩
  invFun x := ⟨(x.2.1.val, x.2.2.val), by
    have h₁ := x.2.1.property
    have h₂ := x.2.2.property
    dsimp only [binaryValue]
    omega⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨c', d, x⟩
    have hc : -(binaryValue digit ms x.val) = (c' : ℤ) := by
      have := x.property
      omega
    rcases c' with ⟨c', hc'⟩
    rcases d with ⟨d, hd'⟩
    rcases x with ⟨x, hx'⟩
    dsimp only at hc
    subst c'
    rfl

private theorem carryCount_cons {D : Type} [Fintype D] (digit : D → ℤ) (M m : ℕ)
    (hd : ∀ d, -(M : ℤ) ≤ digit d ∧ digit d ≤ M) (hm : m ≤ 2)
    (ms : List ℕ) (c : Carry M) :
    carryCount digit (m :: ms) c =
      ∑ c' : Carry M, transition digit M m c c' * carryCount digit ms c' := by
  classical
  unfold carryCount transition
  rw [Fintype.card_congr (splitZero digit M m hd hm ms c), Fintype.card_sigma]
  simp only [Fintype.card_prod]

private def transferProduct {D : Type} [Fintype D] (digit : D → ℤ) (M : ℕ) :
    List ℕ → Matrix (Carry M) (Carry M) ℕ
  | [] => 1
  | m :: ms => transition digit M m * transferProduct digit M ms

private theorem carryCount_matrix {D : Type} [Fintype D] (digit : D → ℤ) (M : ℕ)
    (hd : ∀ d, -(M : ℤ) ≤ digit d ∧ digit d ≤ M)
    (ms : List ℕ) (hms : ∀ m ∈ ms, m ≤ 2) (c : Carry M) :
    carryCount digit ms c = transferProduct digit M ms c (zeroCarry M) := by
  classical
  induction ms generalizing c with
  | nil =>
    change Fintype.card {x : PUnit // (c : ℤ) + 0 = 0} =
      (1 : Matrix (Carry M) (Carry M) ℕ) c (zeroCarry M)
    simp only [add_zero]
    by_cases hc : (c : ℤ) = 0
    · simp [Matrix.one_apply, zeroCarry, Subtype.ext_iff, hc]
    · simp [Matrix.one_apply, zeroCarry, Subtype.ext_iff, hc]
  | cons m ms ih =>
    rw [carryCount_cons digit M m hd (hms m (by simp)) ms c]
    simp_rw [ih (fun k hk => hms k (by simp [hk]))]
    rfl

private def blocks : (L : ℕ) → (Fin L → ℕ) → List ℕ
  | 0, _ => []
  | L + 1, m => m 0 :: blocks L (fun j => m j.succ)

private def blockEquiv (D : Type) : (L : ℕ) → (m : Fin L → ℕ) →
    Assignments D (blocks L m) ≃ (∀ j : Fin L, Fin (m j) → D)
  | 0, _ =>
    { toFun := fun _ j => Fin.elim0 j
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun _ => by ext j; exact Fin.elim0 j }
  | L + 1, m =>
    (Equiv.prodCongr (Equiv.refl _) (blockEquiv D L (fun j => m j.succ))).trans
      (Fin.consEquiv (fun j : Fin (L+1) => Fin (m j) → D))

private theorem binaryValue_blocks {D : Type} (digit : D → ℤ) (L : ℕ)
    (m : Fin L → ℕ) (x : Assignments D (blocks L m)) :
    binaryValue digit (blocks L m) x =
      ∑ j : Fin L, digitSum digit (blockEquiv D L m x j) * (2 : ℤ) ^ j.val := by
  induction L with
  | zero => simp [blocks, binaryValue]
  | succ L ih =>
    change digitSum digit x.1 + 2 * binaryValue digit _ x.2 = _
    rw [Fin.sum_univ_succ, ih]
    change digitSum digit x.1 + 2 * (∑ j : Fin L,
      digitSum digit (blockEquiv D L (fun j => m j.succ) x.2 j) * 2 ^ j.val) =
      digitSum digit x.1 * 2 ^ 0 + ∑ j : Fin L,
        digitSum digit (blockEquiv D L (fun j => m j.succ) x.2 j) * 2 ^ (j.val+1)
    simp only [pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem blocks_bound (L : ℕ) (m : Fin L → ℕ) (hm : ∀ j, m j ≤ 2) :
    ∀ k ∈ blocks L m, k ≤ 2 := by
  induction L with
  | zero => simp [blocks]
  | succ L ih =>
    intro k hk
    simp only [blocks, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hm 0
    · exact ih (fun j => m j.succ) (fun j => hm j.succ) k hk

private def groupingEquiv {n L : ℕ} (D : Type) (m : Fin L → ℕ)
    (e : (Σ j : Fin L, Fin (m j)) ≃ Fin n) :
    (Fin n → D) ≃ (∀ j : Fin L, Fin (m j) → D) where
  toFun d j k := d (e ⟨j,k⟩)
  invFun d i := d (e.symm i).1 (e.symm i).2
  left_inv d := by ext i; simp
  right_inv d := by
    ext j k
    exact congrArg (fun z => d z.1 z.2) (e.symm_apply_apply ⟨j,k⟩)

private theorem grouped_source_count (n L : ℕ) (a : ℕ → ℤ) (D : Finset ℤ)
    (m : Fin L → ℕ) (e : (Σ j : Fin L, Fin (m j)) ≃ Fin n)
    (hw : ∀ j k, a (e ⟨j, k⟩) = 2 * (2 : ℤ) ^ j.val) :
    sourceCount a D n = carryCount (fun d : ↥D => (d : ℤ)) (blocks L m) 0 := by
  classical
  let E := (groupingEquiv (↥D) m e).trans (blockEquiv (↥D) L m).symm
  have hv (d : Fin n → ↥D) :
      (∑ i : Fin n, (d i : ℤ) * a i) =
        2 * binaryValue (fun d : ↥D => (d : ℤ)) (blocks L m) (E d) := by
    rw [binaryValue_blocks]
    have hs := e.sum_comp (fun i : Fin n => (d i : ℤ) * a i)
    rw [← hs, Fintype.sum_sigma]
    simp only [hw, E, Equiv.trans_apply, Equiv.apply_symm_apply,
      groupingEquiv, digitSum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (d (e ⟨j,k⟩) : ℤ) * (2 * 2 ^ j.val) =
      2 * ((d (e ⟨j,k⟩) : ℤ) * 2 ^ j.val)
    ring
  unfold sourceCount carryCount zeroAssignments
  apply Fintype.card_congr
  exact E.subtypeEquiv (fun d => by rw [hv d]; omega)

private def exponent {n : ℕ} (i : Fin n) : Fin (n + n % 2) :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val / 2, by
    have := i.isLt
    have hi : i.val % 2 < 2 := Nat.mod_lt _ (by decide)
    have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
    split_ifs <;> omega⟩

private def multiplicity (n : ℕ) (j : Fin (n + n % 2)) : ℕ :=
  Fintype.card {i : Fin n // exponent i = j}

private def coordinateEquiv (n : ℕ) :
    (Σ j : Fin (n + n % 2), Fin (multiplicity n j)) ≃ Fin n :=
  (Equiv.sigmaCongrRight (fun j =>
    (Fintype.equivFin {i : Fin n // exponent i = j}).symm)).trans
      (Equiv.sigmaFiberEquiv exponent)

private theorem multiplicity_bound (n : ℕ) (j : Fin (n + n % 2)) :
    multiplicity n j ≤ 2 := by
  let parity : {i : Fin n // exponent i = j} → Fin 2 :=
    fun i => ⟨i.val.val % 2, Nat.mod_lt _ (by decide)⟩
  have hinj : Function.Injective parity := by
    intro i k hik
    have hp : i.val.val % 2 = k.val.val % 2 := congrArg Fin.val hik
    have he : (exponent i.val).val = (exponent k.val).val :=
      congrArg Fin.val (i.property.trans k.property.symm)
    change (if i.val.val % 2 = 0 then i.val.val + 1 else i.val.val / 2) =
      (if k.val.val % 2 = 0 then k.val.val + 1 else k.val.val / 2) at he
    apply Subtype.ext
    apply Fin.ext
    split_ifs at he <;> omega
  simpa [multiplicity] using Fintype.card_le_of_injective parity hinj

private def multiplicityFormula (n j : ℕ) : ℕ :=
  (if j % 2 = 1 then 1 else 0) + (if j < n / 2 then 1 else 0)

private theorem multiplicity_formula (n : ℕ) (j : Fin (n + n % 2)) :
    multiplicity n j = multiplicityFormula n j.val := by
  classical
  let s := (Finset.range n).filter
    (fun i => (if i % 2 = 0 then i + 1 else i / 2) = j.val)
  let E : {i : Fin n // exponent i = j} ≃ ↥s :=
    { toFun := fun i => ⟨i.val.val, by
        have hi := congrArg Fin.val i.property
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.val.isLt, hi⟩⟩
      invFun := fun i =>
        ⟨⟨i.val, Finset.mem_range.mp (Finset.mem_filter.mp i.property).1⟩,
          Fin.ext (Finset.mem_filter.mp i.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hj : j.val ≤ n := by have := j.isLt; omega
  have hs : s = (if j.val % 2 = 1 then {j.val-1} else ∅) ∪
      (if j.val < n / 2 then {2*j.val+1} else ∅) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    split_ifs <;> simp_all <;> omega
  change Fintype.card {i : Fin n // exponent i = j} = _
  rw [Fintype.card_congr E, Fintype.card_coe, hs]
  have hne : j.val-1 ≠ 2*j.val+1 := by omega
  unfold multiplicityFormula
  split_ifs <;> simp [hne]

private def multiplicityWord (n : ℕ) : List ℕ :=
  (List.range (n + n % 2)).map (multiplicityFormula n)

private theorem blocks_eq_word (n : ℕ) :
    blocks (n + n % 2) (multiplicity n) = multiplicityWord n := by
  have h (L : ℕ) (m : Fin L → ℕ) :
      blocks L m = List.ofFn m := by
    induction L with
    | zero => rfl
    | succ L ih => simp only [blocks, List.ofFn_succ, ih]
  rw [h]
  apply List.ext_getElem
  · simp [multiplicityWord]
  · intro i hi hi'
    simp only [List.getElem_ofFn, multiplicityWord, List.getElem_map,
      List.getElem_range]
    exact multiplicity_formula n ⟨i, by simpa using hi⟩

private theorem multiplicityWord_step (n : ℕ) :
    multiplicityWord (n+4) = [1,2] ++ multiplicityWord n ++ [0,1] := by
  have hlen : n + 4 + (n+4)%2 = n + n%2 + 4 := by omega
  apply List.ext_getElem
  · simp [multiplicityWord, hlen]
  · intro i hi hi'
    simp only [multiplicityWord, List.length_map, List.length_range] at hi hi'
    simp only [multiplicityWord, List.getElem_map, List.getElem_range]
    by_cases hi₂ : i < 2
    · interval_cases i <;> simp [multiplicityFormula] <;> split_ifs <;> omega
    · have hi₂' : 2 ≤ i := by omega
      by_cases him : i - 2 < n + n%2
      · rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_right (by simp; omega)]
        simp only [List.length_cons, List.length_nil, List.getElem_map, List.getElem_range]
        unfold multiplicityFormula
        split_ifs <;> omega
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_map, List.length_range]
        have htail : i = 2 + (n+n%2) ∨ i = 2 + (n+n%2) + 1 := by omega
        have ht := Nat.mod_lt n (by decide : 0 < 2)
        rcases htail with rfl | rfl <;>
          simp [multiplicityFormula]
        all_goals (try split_ifs) <;> omega

private theorem transferProduct_append {D : Type} [Fintype D]
    (digit : D → ℤ) (M : ℕ) (xs ys : List ℕ) :
    transferProduct digit M (xs ++ ys) =
      transferProduct digit M xs * transferProduct digit M ys := by
  induction xs with
  | nil => simp [transferProduct]
  | cons x xs ih => simp [transferProduct, ih, Matrix.mul_assoc]

private def countMatrix (D : Finset ℤ) (n : ℕ) :
    Matrix (Carry (D.sup Int.natAbs)) (Carry (D.sup Int.natAbs)) ℕ :=
  transferProduct (fun d : ↥D => (d : ℤ)) (D.sup Int.natAbs) (multiplicityWord n)

private def lowerMatrix (D : Finset ℤ) :=
  transition (fun d : ↥D => (d : ℤ)) (D.sup Int.natAbs) 1 *
    transition (fun d : ↥D => (d : ℤ)) (D.sup Int.natAbs) 2

private def upperMatrix (D : Finset ℤ) :=
  transition (fun d : ↥D => (d : ℤ)) (D.sup Int.natAbs) 0 *
    transition (fun d : ↥D => (d : ℤ)) (D.sup Int.natAbs) 1

private theorem countMatrix_step (D : Finset ℤ) (n : ℕ) :
    countMatrix D (n+4) = lowerMatrix D * countMatrix D n * upperMatrix D := by
  simp only [countMatrix, multiplicityWord_step, transferProduct_append,
    transferProduct, lowerMatrix, upperMatrix, Matrix.mul_one, Matrix.mul_assoc]

private theorem sequence_weight {n : ℕ} (i : Fin n) :
    sequence i = 2 * (2 : ℤ) ^ (exponent i).val := by
  change (if i.val % 2 = 0 then (4 : ℤ) ^ (i.val / 2 + 1)
    else 2 ^ (i.val / 2 + 1)) =
    2 * 2 ^ (if i.val % 2 = 0 then i.val + 1 else i.val / 2)
  split_ifs with hi
  · rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul,
      show 2 * (i.val / 2 + 1) = (i.val + 1) + 1 by omega, pow_succ]
    ring
  · rw [pow_succ]
    ring

private abbrev digitBound (D : Finset ℤ) : ℕ := D.sup Int.natAbs

private theorem digitBound_spec (D : Finset ℤ) (d : ↥D) :
    -(digitBound D : ℤ) ≤ (d : ℤ) ∧ (d : ℤ) ≤ digitBound D := by
  have h : Int.natAbs (d : ℤ) ≤ digitBound D :=
    Finset.le_sup (f := Int.natAbs) d.property
  have h' : |(d : ℤ)| ≤ (digitBound D : ℤ) := by
    have h'' : (Int.natAbs (d : ℤ) : ℤ) ≤ (digitBound D : ℤ) := by exact_mod_cast h
    simpa only [Int.natCast_natAbs] using h''
  exact abs_le.mp h'

private theorem original_count_matrix (D : Finset ℤ) (n : ℕ) :
    sourceCount sequence D n =
      transferProduct (fun d : ↥D => (d : ℤ)) (digitBound D)
        (blocks (n + n % 2) (multiplicity n))
        (zeroCarry (digitBound D)) (zeroCarry (digitBound D)) := by
  rw [grouped_source_count n (n + n % 2) sequence D (multiplicity n) (coordinateEquiv n)
    (by
      intro j k
      have h := sequence_weight (coordinateEquiv n ⟨j,k⟩)
      have he : exponent (coordinateEquiv n ⟨j,k⟩) = j := by
        exact ((Fintype.equivFin {i : Fin n // exponent i = j}).symm k).property
      simpa [he] using h)]
  exact carryCount_matrix _ (digitBound D) (digitBound_spec D) _
    (blocks_bound _ _ (multiplicity_bound n)) (zeroCarry (digitBound D))

private abbrev PairCarry (D : Finset ℤ) := Carry (digitBound D) × Carry (digitBound D)

private def integralCountMatrix (D : Finset ℤ) (n : ℕ) :
    Matrix (Carry (digitBound D)) (Carry (digitBound D)) ℤ :=
  (Nat.castRingHom ℤ).mapMatrix (countMatrix D n)

private def synchronizedMatrix (D : Finset ℤ) : Matrix (PairCarry D) (PairCarry D) ℤ :=
  ((Nat.castRingHom ℤ).mapMatrix (upperMatrix D))ᵀ ⊗ₖ
    ((Nat.castRingHom ℤ).mapMatrix (lowerMatrix D))

private def countVector (D : Finset ℤ) (n : ℕ) : PairCarry D → ℤ :=
  Matrix.vec (integralCountMatrix D n)

private theorem countVector_step (D : Finset ℤ) (n : ℕ) :
    synchronizedMatrix D *ᵥ countVector D n = countVector D (n+4) := by
  rw [synchronizedMatrix, countVector, Matrix.kronecker_mulVec_vec]
  simp only [Matrix.transpose_transpose, countVector, integralCountMatrix,
    countMatrix_step]
  rw [(Nat.castRingHom ℤ).mapMatrix.map_mul, (Nat.castRingHom ℤ).mapMatrix.map_mul]

private abbrev StateIndex (D : Finset ℤ) := Fin 4 × PairCarry D

private def state (D : Finset ℤ) (n : ℕ) : StateIndex D → ℤ :=
  fun i => countVector D (n + i.1.val) i.2

private def stateMatrix (D : Finset ℤ) : Matrix (StateIndex D) (StateIndex D) ℤ :=
  fun i j => if i.1.val < 3 then
    (if j.1.val = i.1.val + 1 then if i.2 = j.2 then 1 else 0 else 0)
    else (if j.1.val = 0 then synchronizedMatrix D i.2 j.2 else 0)

private theorem state_step (D : Finset ℤ) (n : ℕ) :
    stateMatrix D *ᵥ state D n = state D (n+1) := by
  classical
  ext ⟨r,i⟩
  fin_cases r
  all_goals simp [stateMatrix, state, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Nat.add_assoc]
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_prod_type] using
    congrFun (countVector_step D n) i

private theorem state_power (D : Finset ℤ) (n k : ℕ) :
    stateMatrix D ^ k *ᵥ state D n = state D (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, state_step]
    simp only [Nat.add_assoc]

private def stateZero (D : Finset ℤ) : StateIndex D :=
  (0, zeroCarry (digitBound D), zeroCarry (digitBound D))

private theorem sourceCount_state (D : Finset ℤ) (n : ℕ) :
    state D n (stateZero D) = (sourceCount sequence D n : ℤ) := by
  rw [original_count_matrix, blocks_eq_word]
  rfl

private theorem integer_count_recurrence (D : Finset ℤ) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : Fin k → ℤ, ∀ n : ℕ,
      (sourceCount sequence D (n+k) : ℤ) =
        ∑ i : Fin k, c i * (sourceCount sequence D (n+i) : ℤ) := by
  classical
  let W := stateMatrix D
  let k := Fintype.card (StateIndex D)
  have hk : 0 < k := by
    letI : Nonempty (StateIndex D) := ⟨stateZero D⟩
    exact Fintype.card_pos
  refine ⟨k, hk, fun i => -W.charpoly.coeff i.val, ?_⟩
  intro n
  have hlead : W.charpoly.coeff k = 1 := by
    simpa [k, Matrix.charpoly_natDegree_eq_dim] using W.charpoly_monic.coeff_natDegree
  have hCH : (∑ i ∈ Finset.range k, W.charpoly.coeff i • W ^ i) + W ^ k = 0 := by
    have h := Matrix.aeval_self_charpoly W
    rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim,
      show Fintype.card (StateIndex D) = k from rfl, Finset.sum_range_succ, hlead] at h
    simpa only [one_smul] using h
  have h := congrArg (fun M => (M *ᵥ state D n) (stateZero D)) hCH
  simp only [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.zero_mulVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, show W = stateMatrix D from rfl, state_power, sourceCount_state,
    Pi.zero_apply] at h
  change _ = ∑ i : Fin k, -(W.charpoly.coeff i.val) * (sourceCount sequence D (n+i) : ℤ)
  rw [Fin.sum_univ_eq_sum_range (fun i => -W.charpoly.coeff i *
    (sourceCount sequence D (n+i) : ℤ)) k]
  simp only [neg_mul, Finset.sum_neg_distrib]
  change _ = -(∑ i ∈ Finset.range k, W.charpoly.coeff i * (sourceCount sequence D (n+i) : ℤ))
  linarith

private theorem all_digit_count_recurrences (D : Finset ℤ) :
    CountRecurrence (sourceCount sequence D) := by
  obtain ⟨k, hk, c, hc⟩ := integer_count_recurrence D
  refine ⟨k, hk, fun i => (c i : ℂ), 0, ?_⟩
  intro n _
  have h := hc (n+1)
  have h' := congrArg (Int.castRingHom ℂ) h
  simpa [map_sum, map_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'

private theorem sequence_positive (n : ℕ) : 0 < sequence n := by
  unfold sequence
  split_ifs <;> positivity

private theorem sequence_recurrence (n : ℕ) :
    sequence (n + 4) = 6 * sequence (n + 2) - 8 * sequence n := by
  have hmod : (n + 4) % 2 = n % 2 := by omega
  have hmod' : (n + 2) % 2 = n % 2 := by omega
  have hdiv : (n + 4) / 2 + 1 = n / 2 + 1 + 2 := by omega
  have hdiv' : (n + 2) / 2 + 1 = n / 2 + 1 + 1 := by omega
  simp only [sequence, hmod, hmod', hdiv, hdiv']
  split_ifs <;> simp only [pow_add, pow_one, pow_two] <;> ring

private theorem characteristic_expanded :
    characteristic = X ^ 4 - C 6 * X ^ 2 + C 8 := by
  unfold characteristic
  norm_num only [map_ofNat]
  ring

private theorem characteristic_monic : characteristic.Monic :=
  (monic_X_pow_sub_C (4 : ℤ) (by decide : (2 : ℕ) ≠ 0)).mul
    (monic_X_pow_sub_C (2 : ℤ) (by decide : (2 : ℕ) ≠ 0))

private theorem characteristic_degree : characteristic.natDegree = 4 := by
  rw [characteristic, natDegree_mul
    (monic_X_pow_sub_C (4 : ℤ) (by decide : (2 : ℕ) ≠ 0)).ne_zero
    (monic_X_pow_sub_C (2 : ℤ) (by decide : (2 : ℕ) ≠ 0)).ne_zero]
  rw [natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]

private theorem characteristic_annihilates : Annihilates sequence characteristic := by
  intro n
  change characteristic.sum (fun j c => c * sequence (n + j)) = 0
  rw [characteristic.sum_over_range' (f := fun j c => c * sequence (n+j))
    (fun _ => zero_mul _) 5
    (by rw [characteristic_degree]; omega)]
  simp [sum_range_succ, characteristic_expanded, sequence_recurrence]
  ring

private theorem characteristic_minimal : MinimalCharacteristic sequence characteristic := by
  refine ⟨characteristic_monic, characteristic_annihilates, ?_⟩
  intro q hq ha
  rw [characteristic_degree]
  by_contra hlt
  have hdeg : q.natDegree < 4 := by omega
  have heq (n : ℕ) :
      q.coeff 0 * sequence n + q.coeff 1 * sequence (n+1) +
        q.coeff 2 * sequence (n+2) + q.coeff 3 * sequence (n+3) = 0 := by
    have h := ha n
    change q.sum (fun j c => c * sequence (n+j)) = 0 at h
    rw [q.sum_over_range' (f := fun j c => c * sequence (n+j))
      (fun _ => zero_mul _) 4 hdeg] at h
    simpa [sum_range_succ, add_assoc] using h
  have h₀ := heq 0
  have h₁ := heq 1
  have h₂ := heq 2
  have h₃ := heq 3
  norm_num [sequence] at h₀ h₁ h₂ h₃
  have hc₀ : q.coeff 0 = 0 := by omega
  have hc₁ : q.coeff 1 = 0 := by omega
  have hc₂ : q.coeff 2 = 0 := by omega
  have hc₃ : q.coeff 3 = 0 := by omega
  have hz : q = 0 := by
    ext j
    by_cases hj : j < 4
    · interval_cases j <;> simp_all
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]
  exact hq.ne_zero hz

private theorem characteristic_root_obstruction : ¬ RootConditions characteristic := by
  have hp : characteristic.map (Int.castRingHom ℂ) =
      (X ^ 2 - C (4 : ℂ)) * (X ^ 2 - C (2 : ℂ)) := by
    simp only [characteristic, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Int.cast_ofNat]
    norm_num
  have hs₀ : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs₂ : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs₁ : 1 < Real.sqrt 2 := by nlinarith
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs₂
  have hr₂ : (characteristic.map (Int.castRingHom ℂ)).IsRoot 2 := by
    rw [hp]
    norm_num [Polynomial.IsRoot]
  have hrs : (characteristic.map (Int.castRingHom ℂ)).IsRoot (Real.sqrt 2 : ℂ) := by
    rw [hp]
    simp [Polynomial.IsRoot, hs]
  have hn₂ : 1 < ‖(2 : ℂ)‖ := by norm_num
  have hns : ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs₀]
  have hratio : 1 < ‖(2 : ℂ) / (Real.sqrt 2 : ℂ)‖ := by
    rw [norm_div, hns]
    norm_num
    exact hs₁
  intro h
  obtain ⟨k, hk, he⟩ := h.2.2 2 (Real.sqrt 2) hr₂ hrs hn₂ (by rw [hns]; exact hs₁)
  have hpow : 1 < ‖(2 : ℂ) / (Real.sqrt 2 : ℂ)‖ ^ k := one_lt_pow₀ hratio (by omega)
  have he' := congrArg norm he
  rw [norm_pow, norm_one] at he'
  linarith

/-- The entire displayed characterization fails for the alternating sequence;
the original prefix counts satisfy integer recurrences for every finite D. -/
theorem result : ¬ claim := by
  intro h
  exact characteristic_root_obstruction
    ((h sequence characteristic sequence_positive characteristic_minimal).mp
      all_digit_count_recurrences)

#check claim
#check result
#print axioms claim
#print axioms carryCount_matrix
#print axioms characteristic_minimal
#print axioms original_count_matrix
#print axioms characteristic_root_obstruction
#print axioms all_digit_count_recurrences
#print axioms result

end D5.S1.Recurrence.MoZeroSumCountRefutation
