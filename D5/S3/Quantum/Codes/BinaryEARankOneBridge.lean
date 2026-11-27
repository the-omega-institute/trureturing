/- GID: D5/S3/Quantum/Codes/BinaryEARankOneBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEARankOneBridge
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Quantum/Codes/BinaryEARankOneBridge.claim; result=D5/S3/Quantum/Codes/BinaryEARankOneBridge.result; claim=D5/S3/Quantum/Codes/BinaryEARankOneBridge.claim
   digest: Binary rank-one support of eight through ten sites cannot meet the three-zero bound. -/

import D5.S3.Quantum.Codes.BinaryEARankOneCore
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! Systematic generators for the binary rank-one obstruction. [Helper escape audits](https://github.com/the-omega-institute/trureturing/issues/34915). -/

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
      bit (∑ i, unpack (BitVec.ofFin (w := 4) a) i * unpack (BitVec.ofFin (w := 4) b) i) := by
    decide +kernel
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
    rw [ite_eq_left i.isLt, pack_get]
  | inr i =>
    change (if 4 + i.val < 4 then (pack h).toNat.testBit (4 + i.val)
      else (pack t).toNat.testBit (4 + i.val - 4)) = bit (t i)
    rw [ite_eq_right (show ¬ 4 + i.val < 4 by omega),
      show 4 + i.val - 4 = i.val by omega, pack_get]

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

private abbrev Ambient (s : ℕ) := (Fin s → F) × (Fin s → F)

open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (spForm)

/-- Project to the two binary coordinates at a site. -/
def site {s : ℕ} (i : Fin s) : Ambient s →ₗ[F] F × F :=
  ((LinearMap.proj i).comp (LinearMap.fst F _ _)).prod
    ((LinearMap.proj i).comp (LinearMap.snd F _ _))

/-- Existence of an original dimension-eight code and dimension-four radical,
with rank-one site images on a support of eight through ten sites. -/
def claim : Prop :=
  ∃ (s : ℕ) (U H : Submodule F (Ambient s)),
    8 ≤ s ∧ s ≤ 10 ∧ H ≤ U ∧ Module.finrank F U = 8 ∧ Module.finrank F H = 4 ∧
    U ≤ (spForm s).orthogonal H ∧
    (∀ i, Module.finrank F (H.map (site i)) = 1) ∧
    (∀ u ∈ U, u ∉ H → (zeros u.1 u.2).card ≤ 3)

private def axes (a : F × F) : (F × F) →ₗ[F] F × F :=
  if a.1 = 0 then (LinearMap.snd F F F).prod (LinearMap.fst F F F)
  else (LinearMap.fst F F F).prod (LinearMap.snd F F F + a.2 • LinearMap.fst F F F)

private theorem axes_apply (a v : F × F) :
    axes a v = if a.1 = 0 then (v.2, v.1) else (v.1, v.2 + a.2 * v.1) := by
  by_cases ha : a.1 = 0 <;> simp [axes, ha, smul_eq_mul]

private theorem axes_self (a : F × F) (ha : a ≠ 0) : axes a a = (1, 0) := by
  rcases bit_eq_zero_or_one a.1 with hx | hx
  · have hz : a.2 = 1 := by
      rcases bit_eq_zero_or_one a.2 with hz | hz
      · exact (ha (Prod.ext hx hz)).elim
      · exact hz
    simp [axes_apply, hx, hz]
  · simp [axes_apply, hx, CharTwo.add_self_eq_zero]

private theorem axes_zero_iff (a v : F × F) :
    ((axes a v).1 = 0 ∧ (axes a v).2 = 0) ↔ v.1 = 0 ∧ v.2 = 0 := by
  by_cases ha : a.1 = 0
  · simp [axes_apply, ha, and_comm]
  · simp only [axes_apply, ite_eq_right ha]
    constructor
    · rintro ⟨hx, hz⟩
      exact ⟨hx, by simpa [hx] using hz⟩
    · rintro ⟨hx, hz⟩
      simp [hx, hz]

private theorem axes_pair (a u v : F × F) :
    (axes a u).1 * (axes a v).2 + (axes a u).2 * (axes a v).1 =
      u.1 * v.2 + u.2 * v.1 := by
  by_cases ha : a.1 = 0
  · simp [axes_apply, ha, mul_comm, add_comm]
  · simp only [axes_apply, ite_eq_right ha]
    calc
      _ = (u.1 * v.2 + u.2 * v.1) + (a.2 * u.1 * v.1 + a.2 * u.1 * v.1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem exists_axes {s : ℕ} (H : Submodule F (Ambient s))
    (rank : ∀ i, Module.finrank F (H.map (site i)) = 1) :
    ∃ X Z : Ambient s →ₗ[F] (Fin s → F),
      (∀ u i, X u i = 0 ∧ Z u i = 0 ↔ u.1 i = 0 ∧ u.2 i = 0) ∧
      (∀ u v, (∑ i : Fin s, (X u i * Z v i + Z u i * X v i)) = spForm s u v) ∧
      (∀ h : H, Z h = 0) ∧ (∀ i, ∃ h : H, X h i = 1) := by
  classical
  have haxis (i : Fin s) : ∃ a : H.map (site i), a ≠ 0 ∧
      ∀ w : H.map (site i), ∃ c : F, c • a = w := finrank_eq_one_iff'.mp (rank i)
  choose a ha hspan using haxis
  let T (i : Fin s) : Ambient s →ₗ[F] (F × F) := (axes (a i)).comp (site i)
  let X : Ambient s →ₗ[F] (Fin s → F) :=
    LinearMap.pi (fun i => (LinearMap.fst F F F).comp (T i))
  let Z : Ambient s →ₗ[F] (Fin s → F) :=
    LinearMap.pi (fun i => (LinearMap.snd F F F).comp (T i))
  have ha' (i : Fin s) : (a i : F × F) ≠ 0 :=
    fun h => ha i (Subtype.ext h)
  refine ⟨X, Z, ?_, ?_, ?_, ?_⟩
  · intro u i
    exact axes_zero_iff (a i) (site i u)
  · intro u v
    change (∑ i : Fin s, (X u i * Z v i + Z u i * X v i)) =
      ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)
    exact Finset.sum_congr rfl (fun i _ => axes_pair (a i) (site i u) (site i v))
  · intro h
    funext i
    let w : H.map (site i) := ⟨site i h, Submodule.mem_map.mpr ⟨h, h.property, rfl⟩⟩
    obtain ⟨c, hc⟩ := hspan i w
    have he : c • (a i : F × F) = site i h := congrArg Subtype.val hc
    change (axes (a i) (site i h)).2 = 0
    rw [← he, map_smul, axes_self _ (ha' i)]
    simp
  · intro i
    obtain ⟨h, hh, hsite⟩ := Submodule.mem_map.mp (a i).property
    refine ⟨⟨h, hh⟩, ?_⟩
    change (axes (a i) (site i h)).1 = 1
    rw [hsite, axes_self _ (ha' i)]

private theorem exists_head {s : ℕ} {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (X : V →ₗ[F] (Fin s → F)) (inj : Function.Injective X)
    (rank : Module.finrank F V = 4) :
    ∃ e : Fin 4 ⊕ Fin (s - 4) ≃ Fin s,
      Function.Bijective ((restrictCoordinates (e ∘ Sum.inl)).comp X) := by
  classical
  let family (i : Fin s) : Module.Dual F V := (LinearMap.proj i).comp X
  have hspan : Submodule.span F (Set.range family) = ⊤ := by
    apply top_unique
    intro d _
    obtain ⟨f, rfl⟩ := LinearMap.dualMap_surjective_of_injective inj d
    let b := (Pi.basisFun F (Fin s)).dualBasis
    have hb (i) : X.dualMap (b i) = family i := by
      ext v
      exact (Module.Basis.dualBasis_apply _ i (X v)).trans (Pi.basisFun_repr F (Fin s) (X v) i)
    rw [← b.sum_repr f, map_sum]
    exact Submodule.sum_mem _ (fun i _ => by
      rw [map_smul, hb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  obtain ⟨t, a, ha, hsel, hli⟩ := exists_linearIndependent' (K := F) family
  let _ : Fintype t := Fintype.ofInjective a ha
  let basis := Module.Basis.mk hli (by rw [hsel, hspan])
  have ht : Fintype.card t = 4 := by
    rw [← Module.finrank_eq_card_basis basis, Subspace.dual_finrank_eq, rank]
  let r := (Fintype.equivFinOfCardEq ht).symm
  let lhs := r.trans (Equiv.ofInjective a ha)
  let sum := Equiv.Set.sumCompl (Set.range a)
  have hleft := Fintype.card_congr lhs
  have hsum := Fintype.card_congr sum
  rw [Fintype.card_sum, ← hleft, Fintype.card_fin, Fintype.card_fin] at hsum
  have hright : Fintype.card (↑((Set.range a)ᶜ) : Type) = s - 4 := by omega
  let e := (lhs.sumCongr (Fintype.equivFinOfCardEq hright).symm).trans sum
  let head := (restrictCoordinates (e ∘ Sum.inl)).comp X
  have he (i : Fin 4) : e (.inl i) = a (r i) := rfl
  have hi : Function.Injective head := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hkill : Set.range (family ∘ a) ⊆ LinearMap.ker (Module.Dual.eval F V v) := by
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := r.surjective j
      have h := congrFun hv i
      change X v (e (.inl i)) = 0 at h
      rw [he] at h
      exact h
    have hle := Submodule.span_le.mpr hkill
    rw [hsel, hspan] at hle
    apply (Module.evalEquiv F V).injective
    ext d
    rw [map_zero]
    exact hle (Submodule.mem_top : d ∈ (⊤ : Submodule F (Module.Dual F V)))
  have hr : Module.finrank F V = Module.finrank F (Fin 4 → F) := by
    rw [rank]
    simp
  exact ⟨e, hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp hi⟩

private theorem expand_tail {m : ℕ} (f : (Fin 4 → F) →ₗ[F] (Fin m → F)) (q : Fin 4 → F) :
    f q = tail (fun i => f (Pi.single i 1)) q := by
  classical
  let b := Pi.basisFun F (Fin 4)
  have he : (∑ i, q i • Pi.single i (1 : F)) = q := by
    simpa [b, Pi.basisFun_repr, Pi.basisFun_apply] using b.sum_repr q
  funext j
  calc
    f q j = f (∑ i, q i • Pi.single i (1 : F)) j := by rw [he]
    _ = tail (fun i => f (Pi.single i 1)) q j := by
      simp [tail, map_sum, map_smul, Finset.sum_apply, smul_eq_mul]

/-- The rank-one hypotheses are inconsistent on any support of at most ten sites. -/
theorem no_rank_one_of_card_le_ten {s : ℕ} (U H : Submodule F (Ambient s))
    (shi : s ≤ 10) (hHU : H ≤ U) (rankU : Module.finrank F U = 8)
    (rankH : Module.finrank F H = 4) (orthogonal : U ≤ (spForm s).orthogonal H)
    (rankSite : ∀ i, Module.finrank F (H.map (site i)) = 1)
    (distance : ∀ u ∈ U, u ∉ H → (zeros u.1 u.2).card ≤ 3) : False := by
  classical
  obtain ⟨X, Z, siteZero, axesPair, radicalZ, radicalSite⟩ := exists_axes H rankSite
  let XH := X.comp H.subtype
  have injectiveXH : Function.Injective XH := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro h hx
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · exact ((siteZero h i).mp ⟨congrFun hx i, congrFun (radicalZ h) i⟩).1
    · exact ((siteZero h i).mp ⟨congrFun hx i, congrFun (radicalZ h) i⟩).2
  obtain ⟨e, headBijective⟩ := exists_head XH injectiveXH rankH
  let head := restrictCoordinates (e ∘ Sum.inl)
  let rest := restrictCoordinates (e ∘ Sum.inr)
  let radicalHead := LinearEquiv.ofBijective (head.comp XH) headBijective
  let Hgen := radicalHead.symm.toLinearMap
  let inc := Submodule.inclusion hHU
  let XU := (head.comp X).comp U.subtype
  let ZU := (head.comp Z).comp U.subtype
  have headH (h : Fin 4 → F) : head (X (Hgen h)) = h := radicalHead.apply_symm_apply h
  have normalizedDistance (u : U) (hu : (u : Ambient s) ∉ H) :
      (zeros (X u) (Z u)).card ≤ 3 := by
    have h : zeros (X u) (Z u) = zeros u.val.1 u.val.2 := by
      ext i
      simpa only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] using siteZero u i
    rw [h]
    exact distance u.val u.property hu
  -- Any vector with zero Z on the head can be shifted by the radical to
  -- have zero X there as well. Thus the kernel of the Z-head map is H.
  have kerZU : LinearMap.ker ZU = LinearMap.range inc := by
    ext u
    constructor
    · intro hzu
      by_cases hu : u.val ∈ H
      · exact ⟨⟨u.val, hu⟩, rfl⟩
      exfalso
      let h := Hgen (XU u)
      let w := u - inc h
      have hw : w.val ∉ H := by
        intro hwh
        have he := H.add_mem hwh h.property
        change (u.val - h.val) + h.val ∈ H at he
        rw [sub_add_cancel] at he
        exact hu he
      have hxw : XU w = 0 := by
        rw [show XU w = XU u - head (X h) from map_sub XU u (inc h), headH, sub_self]
      have hzw : ZU w = 0 := by
        have hzu' : ZU u = 0 := hzu
        rw [show ZU w = ZU u - head (Z h) from map_sub ZU u (inc h),
          radicalZ h, map_zero, sub_zero, hzu']
      let sites := Finset.univ.map (Function.Embedding.inl.trans e.toEmbedding)
      have hcard : sites.card = 4 := by simp [sites]
      have hle := card_zeros_ge (x := X w) (z := Z w) sites (by
        intro i hi
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
        exact ⟨congrFun hxw j, congrFun hzw j⟩)
      have hd := normalizedDistance w hw
      omega
    · rintro ⟨h, rfl⟩
      change head (Z h) = 0
      rw [radicalZ h, map_zero]
  have rankKer : Module.finrank F (LinearMap.ker ZU) = 4 := by
    rw [kerZU, LinearMap.finrank_range_of_inj (Submodule.inclusion_injective hHU), rankH]
  have rankRange : Module.finrank F (LinearMap.range ZU) = 4 := by
    have h := ZU.finrank_range_add_finrank_ker
    omega
  obtain ⟨lift, hlift⟩ := ZU.exists_rightInverse_of_surjective
    (Submodule.eq_top_of_finrank_eq (by simpa using rankRange))
  -- Subtract the unique radical word with the same X-head. This is a
  -- linear choice of representatives of U/H with X-head zero.
  let L := lift - inc.comp (Hgen.comp (XU.comp lift))
  have headLX (q : Fin 4 → F) : head (X (L q)) = 0 := by
    change XU (lift q - inc (Hgen (XU (lift q)))) = 0
    rw [map_sub, show XU (inc (Hgen (XU (lift q)))) = _ from headH _, sub_self]
  have headLZ (q : Fin 4 → F) : head (Z (L q)) = q := by
    change ZU (lift q - inc (Hgen (XU (lift q)))) = q
    rw [map_sub]
    change ZU (lift q) - head (Z (Hgen (XU (lift q)))) = q
    rw [radicalZ, map_zero, sub_zero]
    exact LinearMap.congr_fun hlift q
  let radicalTail := (rest.comp XH).comp Hgen
  let logicalTail := (rest.comp Z).comp (U.subtype.comp L)
  have headPairing (a q : Fin 4 → F) :
      (∑ j, a j * q j) + (∑ j, radicalTail a j * logicalTail q j) = 0 := by
    let h := Hgen a
    let u := L q
    have hp := (LinearMap.BilinForm.mem_orthogonal_iff.mp (orthogonal u.property)) h h.property
    have hp' := (axesPair h u).trans hp
    rw [radicalZ h] at hp'
    simp only [Pi.zero_apply, zero_mul, add_zero] at hp'
    have hs := (Equiv.sum_comp e (fun j => X h j * Z u j)).trans hp'
    rw [Fintype.sum_sum_type] at hs
    change (∑ j : Fin 4, head (X h) j * head (Z u) j) +
      (∑ j : Fin (s - 4), radicalTail a j * logicalTail q j) = 0 at hs
    rwa [headH, headLZ] at hs
  have injectiveTail : Function.Injective logicalTail := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro q hq
    funext i
    have hs := headPairing (Pi.single i 1) q
    rw [hq] at hs
    simpa [Pi.single_apply] using hs
  have width := LinearMap.finrank_le_finrank_of_injective injectiveTail
  have tailWidth : 4 ≤ s - 4 := by simpa using width
  let Xtail := (rest.comp X).comp (U.subtype.comp L)
  let A := fun i => radicalTail (Pi.single i 1)
  let R := fun i => logicalTail (Pi.single i 1)
  have ha (h : Fin 4 → F) : radicalTail h = tail A h := expand_tail _ _
  have hr (q : Fin 4 → F) : logicalTail q = tail R q := expand_tail _ _
  have nonzero (j : Fin (s - 4)) : (fun i => A i j) ≠ 0 := by
    intro hz
    obtain ⟨h, hh⟩ := radicalSite (e (.inr j))
    have he : radicalTail (radicalHead h) j = 1 := by
      change X (radicalHead.symm (radicalHead h)) (e (.inr j)) = 1
      simpa only [radicalHead.symm_apply_apply] using hh
    rw [ha] at he
    have hzero (i : Fin 4) : A i j = 0 := congrFun hz i
    simp [tail, hzero] at he
  have pairing (k i : Fin 4) : (∑ j, A k j * R i j) = if k = i then 1 else 0 := by
    have hs := headPairing (Pi.single k 1) (Pi.single i 1)
    change (∑ j : Fin 4, Pi.single k (1 : F) j * Pi.single i (1 : F) j) +
      (∑ j, A k j * R i j) = 0 at hs
    let d : F := if k = i then 1 else 0
    have hd : (∑ j : Fin 4, Pi.single k (1 : F) j * Pi.single i (1 : F) j) = d := by
      simp [d, Pi.single_apply, eq_comm]
    rw [hd] at hs
    calc
      (∑ j, A k j * R i j) = d + (d + ∑ j, A k j * R i j) := by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      _ = d := by rw [hs, add_zero]
  have systematicDistance : Distance A R Xtail := by
    intro q hq h
    let u := L q + inc (Hgen h)
    have hx : X u = X (L q) + X (Hgen h) := map_add X _ _
    have hz : Z u = Z (L q) := by
      change Z ((L q : Ambient s) + (Hgen h : Ambient s)) = Z (L q)
      rw [map_add, radicalZ, add_zero]
    have hu : u.val ∉ H := by
      intro hu
      have he : Z u = 0 := radicalZ ⟨u.val, hu⟩
      rw [hz] at he
      apply hq
      rw [← headLZ q, he, map_zero]
    have hx' : X u ∘ e = Sum.elim h (Xtail q + tail A h) := by
      funext j
      cases j with
      | inl i =>
        change head (X u) i = h i
        rw [hx, map_add, headLX, headH, zero_add]
      | inr i =>
        change rest (X u) i = (Xtail q + tail A h) i
        rw [hx, map_add]
        change (Xtail q + radicalTail h) i = _
        rw [ha]
    have hz' : Z u ∘ e = Sum.elim q (tail R q) := by
      funext j
      cases j with
      | inl i =>
        change head (Z u) i = q i
        rw [hz, headLZ]
      | inr i =>
        change rest (Z u) i = tail R q i
        rw [hz]
        exact congrFun (hr q) i
    rw [← hx', ← hz', zero_card_equiv]
    exact normalizedDistance u hu
  exact BinaryEARankOneCore.result
    ⟨s - 4, tailWidth, by omega, systematic_core A R Xtail nonzero pairing systematicDistance⟩

/-- On eight through ten sites, the original rank-one hypotheses are inconsistent. -/
theorem result : ¬ claim := by
  rintro ⟨s, U, H, _, shi, hHU, rankU, rankH, orthogonal, rankSite, distance⟩
  exact no_rank_one_of_card_le_ten U H shi hHU rankU rankH orthogonal rankSite distance

end D5.S3.Quantum.Codes.BinaryEARankOneBridge
