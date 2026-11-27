/- GID: D5/S3/Quantum/Codes/BinaryEARankOneBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEARankOneBridge
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Quantum/Codes/BinaryEARankOneBridge.claim; result=D5/S3/Quantum/Codes/BinaryEARankOneBridge.result; claim=D5/S3/Quantum/Codes/BinaryEARankOneBridge.claim
   digest: Binary rank-one support of eight through ten sites cannot meet the three-zero bound. -/

import D5.S3.Quantum.Codes.BinaryEARankOneCore
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! Systematic generators for the binary rank-one obstruction. -/

namespace D5.S3.Quantum.Codes.BinaryEARankOneBridge

open scoped BigOperators

private abbrev F := ZMod 2

private def tail {m : ℕ} (A : Fin 4 → Fin m → F) (h : Fin 4 → F) (j : Fin m) : F :=
  ∑ i, h i * A i j

private theorem tail_single {m : ℕ} (A : Fin 4 → Fin m → F) (i : Fin 4) (a : F) (j : Fin m) :
    tail A (Pi.single i a) j = a * A i j := by
  classical
  simp [tail, Pi.single_apply, ite_mul]

private theorem tail_add {m : ℕ} (A : Fin 4 → Fin m → F) (h k : Fin 4 → F) (j : Fin m) :
    tail A (h + k) j = tail A h j + tail A k j := by
  simp [tail, add_mul, Finset.sum_add_distrib]

private def zeros {ι : Type*} [Fintype ι] (x z : ι → F) : Finset ι :=
  Finset.univ.filter (fun i => x i = 0 ∧ z i = 0)

private theorem card_zeros_ge {ι : Type*} [Fintype ι] {x z : ι → F} (sites : Finset ι)
    (h : ∀ i ∈ sites, x i = 0 ∧ z i = 0) :
    sites.card ≤ (zeros x z).card :=
  Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i hi⟩)

private def Distance {m : ℕ} (A R : Fin 4 → Fin m → F) (X : (Fin 4 → F) → Fin m → F) : Prop :=
  ∀ q : Fin 4 → F, q ≠ 0 → ∀ h : Fin 4 → F,
    (zeros (Sum.elim h (X q + tail A h)) (Sum.elim q (tail R q))).card ≤ 3

private theorem bit_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  have h : ∀ x : F, x = 0 ∨ x = 1 := by decide
  exact h a

private theorem single_exchange {m : ℕ} {A R : Fin 4 → Fin m → F}
    {X : (Fin 4 → F) → Fin m → F} (distance : Distance A R X)
    (i : Fin 4) (j : Fin m) (ha : A i j = 1) : R i j = 1 := by
  classical
  rcases bit_eq_zero_or_one (R i j) with hr | hr
  · let q : Fin 4 → F := Pi.single i 1
    let h : Fin 4 → F := Pi.single i (X q j)
    have hq : q ≠ 0 := by
      intro he
      simpa [q] using congrFun he i
    let sites : Finset (Fin 4 ⊕ Fin m) :=
      (Finset.univ.erase i).disjSum {j}
    have hcard : sites.card = 4 := by simp [sites, Finset.card_erase_of_mem]
    have hz := card_zeros_ge (x := Sum.elim h (X q + tail A h)) (z := Sum.elim q (tail R q))
      sites (by
        rintro (k | l) hk
        · have hki : k ≠ i := (Finset.mem_erase.mp (Finset.inl_mem_disjSum.mp hk)).1
          simp [q, h, Pi.single_eq_of_ne hki]
        · have hl : l = j := Finset.mem_singleton.mp (Finset.inr_mem_disjSum.mp hk)
          subst l
          simp [h, q, tail_single, ha, hr, CharTwo.add_self_eq_zero])
    have hd := distance q hq h
    omega
  · exact hr

private theorem double_exchange {m : ℕ} {A R : Fin 4 → Fin m → F}
    {X : (Fin 4 → F) → Fin m → F} (distance : Distance A R X)
    {i k : Fin 4} {l j : Fin m} (hik : i ≠ k)
    (hil : A i l = 1) (hkl : A k l = 1) (hij : A i j = 0) (hkj : A k j = 1) :
    R i j = 0 := by
  classical
  rcases bit_eq_zero_or_one (R i j) with hr | hr
  · exact hr
  have hjl : j ≠ l := by
    intro he
    subst l
    rw [hil] at hij
    exact one_ne_zero hij
  have hril := single_exchange distance i l hil
  have hrkl := single_exchange distance k l hkl
  have hrkj := single_exchange distance k j hkj
  let q : Fin 4 → F := Pi.single i 1 + Pi.single k 1
  let h : Fin 4 → F := Pi.single i (X q l + X q j) + Pi.single k (X q j)
  have hq : q ≠ 0 := by
    intro he
    simpa [q, Pi.single_eq_of_ne hik] using congrFun he i
  let sites : Finset (Fin 4 ⊕ Fin m) := ((Finset.univ.erase i).erase k).disjSum {j, l}
  have hcard : sites.card = 4 := by
    have hk : k ∈ Finset.univ.erase i := by simp [Ne.symm hik]
    simp [sites, Finset.card_erase_of_mem hk, Finset.card_erase_of_mem, hjl]
  have hz := card_zeros_ge (x := Sum.elim h (X q + tail A h)) (z := Sum.elim q (tail R q))
    sites (by
      rintro (p | p) hp
      · have hp' := Finset.mem_erase.mp (Finset.inl_mem_disjSum.mp hp)
        have hpi := (Finset.mem_erase.mp hp'.2).1
        simp [q, h, Pi.single_eq_of_ne hp'.1, Pi.single_eq_of_ne hpi]
      · rcases Finset.mem_insert.mp (Finset.inr_mem_disjSum.mp hp) with he | he
        · subst p
          simp [q, h, tail_add, tail_single, hij, hkj, hr, hrkj, CharTwo.add_self_eq_zero]
        · have he' : p = l := Finset.mem_singleton.mp he
          subst p
          simp [q, h, tail_add, tail_single, hil, hkl, hril, hrkl,
            add_assoc, CharTwo.add_self_eq_zero])
  have hd := distance q hq h
  omega

/-- Single and double exchanges force the radical tail to have identity Gram matrix. -/
private theorem gram_entries {m : ℕ} {A R : Fin 4 → Fin m → F}
    {X : (Fin 4 → F) → Fin m → F} (distance : Distance A R X)
    (pairing : ∀ k i, (∑ j, A k j * R i j) = if k = i then 1 else 0) :
    ∀ k i, (∑ j, A k j * A i j) = if k = i then 1 else 0 := by
  classical
  intro k i
  have compare : (∀ j, A k j = 1 → A i j = R i j) →
      (∑ j, A k j * A i j) = if k = i then 1 else 0 := by
    intro h
    rw [← pairing k i]
    apply Finset.sum_congr rfl
    intro j _
    rcases bit_eq_zero_or_one (A k j) with hz | ho
    · simp [hz]
    · rw [h j ho]
  by_cases he : k = i
  · subst k
    exact compare (fun j ho => ho.trans (single_exchange distance i j ho).symm)
  by_cases overlap : ∃ l, A i l = 1 ∧ A k l = 1
  · obtain ⟨l, hil, hkl⟩ := overlap
    apply compare
    intro j hkj
    rcases bit_eq_zero_or_one (A i j) with hij | hij
    · exact hij.trans (double_exchange distance (Ne.symm he) hil hkl hij hkj).symm
    · exact hij.trans (single_exchange distance i j hij).symm
  · rw [ite_eq_right_iff.mpr (fun h => (he h).elim)]
    apply Finset.sum_eq_zero
    intro j _
    rcases bit_eq_zero_or_one (A k j) with hz | ho
    · simp [hz]
    · rcases bit_eq_zero_or_one (A i j) with hz | hi
      · simp [hz]
      · exact (overlap ⟨j, hi, ho⟩).elim

private def bit (x : F) : Bool := decide (x = 1)

private theorem bit_injective : Function.Injective bit := by
  have h : ∀ x y : F, bit x = bit y → x = y := by decide
  exact h

private theorem bit_zero (x : F) : bit x = false ↔ x = 0 := by
  have h : ∀ x : F, bit x = false ↔ x = 0 := by decide
  exact h x

private theorem bit_add (x y : F) : bit (x + y) = (bit x ^^ bit y) := by
  have h : ∀ x y : F, bit (x + y) = (bit x ^^ bit y) := by decide
  exact h x y

private theorem bit_mul (x y : F) : bit (x * y) = (bit x && bit y) := by
  have h : ∀ x y : F, bit (x * y) = (bit x && bit y) := by decide
  exact h x y

private def pack : {n : ℕ} → (Fin n → F) → BitVec n
  | 0, _ => 0
  | _ + 1, v => (pack (v ∘ Fin.succ)).concat (bit (v 0))

private theorem pack_get {n : ℕ} (v : Fin n → F) (i : Fin n) :
    (pack v).toNat.testBit i = bit (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero ..
    · exact (BitVec.getLsbD_concat_succ ..).trans (ih _ j)

private theorem pack_injective {n : ℕ} : Function.Injective (@pack n) := by
  intro v w h
  funext i
  apply bit_injective
  simpa only [pack_get] using congrArg (fun b : BitVec n => b.toNat.testBit i) h

private theorem pack_add {n : ℕ} (v w : Fin n → F) : pack (v + w) = pack v ^^^ pack w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (pack (v + w)).toNat.testBit i = (pack v ^^^ pack w).toNat.testBit i
  rw [BitVec.toNat_xor, Nat.testBit_xor]
  simpa only [pack_get (i := ⟨i, hi⟩), Pi.add_apply] using bit_add (v ⟨i, hi⟩) (w ⟨i, hi⟩)

private theorem pack_zero (n : ℕ) : pack (0 : Fin n → F) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (pack (0 : Fin n → F)).toNat.testBit i = (0 : Nat).testBit i
  rw [Nat.zero_testBit]
  exact pack_get (0 : Fin n → F) ⟨i, hi⟩

private def unpack {n : ℕ} (v : BitVec n) (i : Fin n) : F :=
  if v.toNat.testBit i then 1 else 0

private theorem pack_unpack {n : ℕ} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (pack (unpack v)).getLsbD i = bit (unpack v ⟨i, hi⟩) from pack_get _ ⟨i, hi⟩]
  change bit (if v.getLsbD i then 1 else 0) = _
  cases v.getLsbD i <;> rfl

private theorem unpack_pack {n : ℕ} (v : Fin n → F) : unpack (pack v) = v :=
  pack_injective (pack_unpack _)

private theorem unpack_xor {n : ℕ} (v w : BitVec n) :
    unpack (v ^^^ w) = unpack v + unpack w := by
  apply pack_injective
  rw [pack_unpack, pack_add, pack_unpack, pack_unpack]

private theorem pack_single (i : Fin 4) :
    (pack (Pi.single i 1 : Fin 4 → F)).toNat = (1 : ℕ) <<< i.val := by
  classical
  let v : Fin 4 → F := Pi.single i 1
  change (pack v).toNat = (1 : ℕ) <<< i.val
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hk : k < 4
  · have ht : (pack v).toNat.testBit k = bit (v ⟨k, hk⟩) := pack_get v ⟨k, hk⟩
    rw [ht]
    by_cases he : i.val = k
    · have he' : (⟨k, hk⟩ : Fin 4) = i := Fin.ext he.symm
      simp [he, he', v, bit]
    · have he' : (⟨k, hk⟩ : Fin 4) ≠ i := fun h => he (congrArg Fin.val h).symm
      simp [he, v, Pi.single_eq_of_ne he', bit]
  · have hz : (pack v).getLsbD k = false := BitVec.getLsbD_of_ge _ k (by omega)
    exact hz.trans (decide_eq_false (show i.val ≠ k by omega)).symm

open BinaryEARankOneCore (columnSum gram radicalWord zeroCount)

private def columns {m : ℕ} (A : Fin 4 → Fin m → F) : List ℕ :=
  List.ofFn (fun j => (pack (fun i => A i j)).toNat)

private theorem columnSum_eq {m : ℕ} (A : Fin 4 → Fin m → F) (z : Fin m → F) :
    columnSum (columns A) (pack z).toNat = (pack (fun i => ∑ j, A i j * z j)).toNat := by
  induction m with
  | zero =>
    have h : (fun i => ∑ j : Fin 0, A i j * z j) = 0 := by funext i; simp
    rw [h, pack_zero]
    rfl
  | succ m ih =>
    let A' : Fin 4 → Fin m → F := fun i j => A i j.succ
    have hshift : (pack z).toNat >>> 1 = (pack (z ∘ Fin.succ)).toNat := by
      rw [pack, BitVec.toNat_concat, Nat.shiftRight_eq_div_pow]
      have hb := (bit (z 0)).toNat_lt
      omega
    have hbit : (pack z).toNat.testBit 0 = bit (z 0) := pack_get z (0 : Fin (m + 1))
    rw [columns, List.ofFn_succ, columnSum, hbit, hshift]
    change _ ^^^ columnSum (columns A') (pack (z ∘ Fin.succ)).toNat = _
    rw [ih A' (z ∘ Fin.succ)]
    simp only [Fin.sum_univ_succ]
    rw [show (fun i => A i 0 * z 0 + ∑ j : Fin m, A i j.succ * z j.succ) =
         (fun i => A i 0 * z 0) + (fun i => ∑ j, A' i j * (z ∘ Fin.succ) j) from rfl]
    rw [pack_add, BitVec.toNat_xor]
    rcases bit_eq_zero_or_one (z 0) with h | h
    · simp [h, bit, pack_zero, show (fun i : Fin 4 => (0 : F)) = 0 from rfl]
    · simp [h, bit]

private def gramIndex : Fin 10 → Fin 4 × Fin 4 :=
  ![(0, 0), (1, 1), (2, 2), (3, 3), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

private def gramColumn (v : Fin 4 → F) (p : Fin 10) : F :=
  v (gramIndex p).1 * v (gramIndex p).2

private theorem gram_one (v : Fin 4 → F) :
    gram [(pack v).toNat] = (pack (gramColumn v)).toNat := by
  have h : ∀ w : Fin 16,
      gram [w.val] = (pack (gramColumn (unpack (BitVec.ofFin w)))).toNat := by decide +kernel
  have hv := h (pack v).toFin
  change gram [(pack v).toNat] = (pack (gramColumn (unpack (pack v)))).toNat at hv
  simpa only [unpack_pack] using hv

private theorem gram_pack {m : ℕ} (A : Fin 4 → Fin m → F) :
    gram (columns A) = (pack (fun p => ∑ j, gramColumn (fun i => A i j) p)).toNat := by
  induction m with
  | zero =>
    have h : (fun p : Fin 10 => ∑ j : Fin 0, gramColumn (fun i => A i j) p) = 0 := by funext p; simp
    rw [h, pack_zero]
    rfl
  | succ m ih =>
    rw [columns, List.ofFn_succ]
    have hcons (a : ℕ) (as : List ℕ) : gram (a :: as) = gram [a] ^^^ gram as := by
      simp [gram]
    rw [hcons, gram_one]
    change _ ^^^ gram (columns (fun i j => A i j.succ)) = _
    rw [ih]
    simp only [Fin.sum_univ_succ]
    rw [← BitVec.toNat_xor, ← pack_add]
    rfl

private theorem gram_eq_15 {m : ℕ} (A : Fin 4 → Fin m → F)
    (h : ∀ k i, (∑ j, A k j * A i j) = if k = i then 1 else 0) :
    gram (columns A) = 15 := by
  classical
  rw [gram_pack]
  have he : (fun p => ∑ j, gramColumn (fun i => A i j) p) =
      (fun p => if (gramIndex p).1 = (gramIndex p).2 then (1 : F) else 0) := by
    funext p
    exact h _ _
  rw [he]
  have h15 : (pack (fun p => if (gramIndex p).1 = (gramIndex p).2 then (1 : F) else 0)).toNat =
      15 := by decide +kernel
  exact h15

private def dotMask (h a : ℕ) : Bool :=
  ((h.testBit 0 && a.testBit 0) != (h.testBit 1 && a.testBit 1)) !=
    ((h.testBit 2 && a.testBit 2) != (h.testBit 3 && a.testBit 3))

private theorem dotMask_eq (v w : Fin 4 → F) :
    dotMask (pack v).toNat (pack w).toNat = bit (∑ i, v i * w i) := by
  have h : ∀ a b : Fin 16, dotMask a.val b.val =
      bit (∑ i, unpack (BitVec.ofFin (w := 4) a) i * unpack (BitVec.ofFin (w := 4) b) i) := by decide +kernel
  have hv := h (pack v).toFin (pack w).toFin
  change dotMask (pack v).toNat (pack w).toNat =
    bit (∑ i, unpack (pack v) i * unpack (pack w) i) at hv
  simpa only [unpack_pack] using hv

private theorem radicalWord_eq {m : ℕ} (A : Fin 4 → Fin m → F) (h : Fin 4 → F) :
    radicalWord (columns A) (pack h).toNat = (pack h).toNat + 16 * (pack (tail A h)).toNat := by
  let a := (pack h).toNat
  have ha : a < 16 := (pack h).isLt
  have hcons (b : ℕ) (bs : List ℕ) :
      radicalWord (b :: bs) a = a + 16 * ((dotMask a b).toNat + 2 * (radicalWord bs a / 16)) := by
    have hdiv (v : ℕ) : (a + 16 * v) / 16 = v := by omega
    unfold radicalWord
    rw [hdiv]
    rfl
  induction m with
  | zero => rfl
  | succ m ih =>
    let A' : Fin 4 → Fin m → F := fun i j => A i j.succ
    rw [columns, List.ofFn_succ, hcons]
    change a + 16 * ((dotMask a (pack (fun i => A i 0)).toNat).toNat +
      2 * (radicalWord (columns A') a / 16)) = _
    have ht : (pack (tail A h)).toNat =
        (pack (tail A' h)).toNat * 2 + (bit (tail A h 0)).toNat :=
      BitVec.toNat_concat ..
    rw [ih, dotMask_eq, ht]
    have hdiv : (a + 16 * (pack (tail A' h)).toNat) / 16 = (pack (tail A' h)).toNat := by omega
    change a + 16 * ((bit (tail A h 0)).toNat + 2 * ((a + 16 * (pack (tail A' h)).toNat) / 16)) =
      a + 16 * ((pack (tail A' h)).toNat * 2 + (bit (tail A h 0)).toNat)
    rw [hdiv, Nat.mul_comm 2, Nat.add_comm (bit (tail A h 0)).toNat]

private theorem packed_testBit {m : ℕ} (h : Fin 4 → F) (t : Fin m → F)
    (i : Fin 4 ⊕ Fin m) :
    ((pack h).toNat + 16 * (pack t).toNat).testBit (finSumFinEquiv i : Fin (4 + m)).val =
      bit (Sum.elim h t i) := by
  rw [Nat.add_comm, show 16 = 2 ^ 4 by rfl,
    Nat.testBit_two_pow_mul_add (pack t).toNat (pack h).isLt]
  cases i with
  | inl i =>
    change (if i.val < 4 then (pack h).toNat.testBit i.val
      else (pack t).toNat.testBit (i.val - 4)) = bit (h i)
    rw [if_pos i.isLt, pack_get]
  | inr i =>
    change (if 4 + i.val < 4 then (pack h).toNat.testBit (4 + i.val)
      else (pack t).toNat.testBit (4 + i.val - 4)) = bit (t i)
    rw [if_neg (by omega), show 4 + i.val - 4 = i.val by omega, pack_get]

private theorem zeroCount_eq {m : ℕ} (A R : Fin 4 → Fin m → F)
    (x : Fin m → F) (q h : Fin 4 → F) :
    zeroCount (m + 4) (pack q).toNat (pack (tail R q)).toNat (pack x).toNat
        (radicalWord (columns A) (pack h).toNat) =
      (zeros (Sum.elim h (x + tail A h)) (Sum.elim q (tail R q))).card := by
  classical
  let u := Sum.elim h (x + tail A h)
  let v := Sum.elim q (tail R q)
  let e := (finSumFinEquiv : Fin 4 ⊕ Fin m ≃ Fin (4 + m))
  let a := (16 * (pack x).toNat) ^^^ radicalWord (columns A) (pack h).toNat
  let b := (pack q).toNat + 16 * (pack (tail R q)).toNat
  have he (i : Fin 4 ⊕ Fin m) : (a ||| b).testBit (e i).val = false ↔
      u i = 0 ∧ v i = 0 := by
    dsimp only [a, b]
    rw [Nat.testBit_or, Nat.testBit_xor, radicalWord_eq, packed_testBit, packed_testBit]
    change ((16 * (pack x).toNat).testBit (e i).val ^^ bit (Sum.elim h (tail A h) i) ||
      bit (v i)) = false ↔ _
    have hx := packed_testBit (0 : Fin 4 → F) x i
    rw [pack_zero] at hx
    change (0 + 16 * (pack x).toNat).testBit (e i).val = bit (Sum.elim 0 x i) at hx
    rw [zero_add] at hx
    rw [hx, ← bit_add, Bool.or_eq_false_iff, bit_zero, bit_zero]
    cases i <;> simp [u]
  let p : ℕ → Prop := fun i => (a ||| b).testBit i = false
  have : DecidablePred p := fun _ => inferInstanceAs (Decidable (_ = false))
  let f := e.toEmbedding.trans Fin.valEmbedding
  have hm : (zeros u v).map f = (List.range (4 + m)).toFinset.filter p := by
    ext i
    simp only [Finset.mem_map, zeros, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(e j).isLt, (he j).mpr hj⟩
    · rintro ⟨hi, hp⟩
      refine ⟨e.symm ⟨i, hi⟩, (he _).mp ?_, ?_⟩
      · simpa [p] using hp
      · change (e (e.symm ⟨i, hi⟩)).val = i
        rw [e.apply_symm_apply]
  have hc := congrArg Finset.card hm
  rw [Finset.card_map, List.nodup_range.card_eq_countP] at hc
  rw [Nat.add_comm m 4]
  change (List.range (4 + m)).countP (fun i => !(a ||| b).testBit i) = (zeros u v).card
  rw [hc]
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [p]

private theorem zero_card_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x z : κ → F) :
    (zeros (x ∘ e) (z ∘ e)).card = (zeros x z).card := by
  classical
  rw [← Finset.card_map e.toEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, zeros, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply, Function.comp_apply]
  exact ⟨fun ⟨j, hj, he⟩ => he ▸ hj, fun hi =>
    ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi, e.apply_symm_apply i⟩⟩

private def restrictCoordinates {ι κ : Type*} (e : κ → ι) : (ι → F) →ₗ[F] (κ → F) :=
  LinearMap.pi (fun i => LinearMap.proj (e i))

private theorem systematic_core {m : ℕ} (A R : Fin 4 → Fin m → F)
    (X : (Fin 4 → F) →ₗ[F] (Fin m → F))
    (nonzero : ∀ j, (fun i => A i j) ≠ 0)
    (pairing : ∀ k i, (∑ j, A k j * R i j) = if k = i then 1 else 0)
    (distance : Distance A R X) : Nonempty (BinaryEARankOneCore.Core m) := by
  classical
  let f := fun j => (pack (fun i => A i j)).toNat
  let σ := Tuple.sort f
  let A' : Fin 4 → Fin m → F := fun i j => A i (σ j)
  let R' : Fin 4 → Fin m → F := fun i j => R i (σ j)
  let X' := (restrictCoordinates σ).comp X
  have pairing' (k i : Fin 4) : (∑ j, A' k j * R' i j) = if k = i then 1 else 0 := by
    exact (Equiv.sum_comp σ (fun j => A k j * R i j)).trans (pairing k i)
  have distance' : Distance A' R' X' := by
    intro q hq h
    let e := Equiv.sumCongr (Equiv.refl (Fin 4)) σ
    have hx : Sum.elim h (X' q + tail A' h) = (Sum.elim h (X q + tail A h)) ∘ e := by
      funext i
      cases i <;> rfl
    have hz : Sum.elim q (tail R' q) = (Sum.elim q (tail R q)) ∘ e := by
      funext i
      cases i <;> rfl
    change (zeros (Sum.elim h (X' q + tail A' h)) (Sum.elim q (tail R' q))).card ≤ 3
    rw [hx, hz, zero_card_equiv]
    exact distance q hq h
  refine ⟨{
    columns := columns A'
    length_eq := List.length_ofFn
    sorted := ?_
    column_bounds := ?_
    self_orthogonal := gram_eq_15 A' (gram_entries distance' pairing')
    zTail := fun q => pack (tail R' (unpack q))
    xTail := fun q => pack (X' (unpack q))
    z_xor := ?_
    x_xor := ?_
    syndrome := ?_
    distance := ?_ }⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    exact Tuple.monotone_sort f hij.le
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    let v : Fin 4 → F := fun i => A' i j
    refine ⟨Nat.pos_of_ne_zero ?_, (pack v).isLt⟩
    intro hz
    apply nonzero (σ j)
    apply pack_injective
    rw [pack_zero]
    exact BitVec.eq_of_toNat_eq hz
  · intro q r
    rw [unpack_xor, ← pack_add]
    congr 1
    funext j
    exact tail_add _ _ _ _
  · intro q r
    rw [unpack_xor, map_add, pack_add]
  · intro i
    have hq : ((1 : BitVec 4) <<< i.val) = pack (Pi.single i 1 : Fin 4 → F) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, pack_single]
      apply Nat.mod_eq_of_lt
      change (1 : ℕ) <<< i.val < 2 ^ 4
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by decide) i.isLt
    rw [hq, unpack_pack, columnSum_eq, ← pack_single i]
    congr 2
    funext k
    simpa [tail_single, Pi.single_apply, eq_comm] using pairing' k i
  · intro q hq h
    have hq' : unpack q ≠ 0 := by
      intro hz
      exact hq (by rw [← pack_unpack q, hz, pack_zero])
    have he := zeroCount_eq A' R' (X' (unpack q)) (unpack q) (unpack h)
    rw [pack_unpack, pack_unpack] at he
    exact he.trans_le (distance' (unpack q) hq' (unpack h))

end D5.S3.Quantum.Codes.BinaryEARankOneBridge
