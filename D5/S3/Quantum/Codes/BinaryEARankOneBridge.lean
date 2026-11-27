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
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Sum

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

end D5.S3.Quantum.Codes.BinaryEARankOneBridge
