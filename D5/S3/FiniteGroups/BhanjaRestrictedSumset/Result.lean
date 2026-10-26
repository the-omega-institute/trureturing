/- GID: D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BhanjaRestrictedSumset/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.claim; result=D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result; claim=D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.claim
   digest: Odd two-value sums equal A; ordinary sums cover elementary 2-groups above half size. -/

/-
admission_basis: open-problem-resolution (#22373; Refuted).
Direct frozen D5 dependencies: none (pinned Mathlib imports only).
Per declaration: name | proof_shape | escape_witness | consumers.
  hSumset | bind-only (definition) | none | elementary_two_group_gap, elementary_two_group_minima, largeIterated, minSize
  restrictedSumset | bind-only (definition) | none | elementary_two_group_gap, elementary_two_group_minima, memR, minRestrictedSize, restrictedOdd
  memR | bind-only | none | restrictedOdd
  doubleZero | bind-only | none | oddSmul, pairSum
  oddSmul | bind-only | none | restrictedOdd
  pairSum | bind-only | none | restrictedOdd
  restrictedOdd | bind-only | none | elementary_two_group_gap
  largeDouble | bind-only | none | largeIterated
  largeIterated | bind-only | none | elementary_two_group_gap
  elementary_two_group_gap | bind-only | none | elementary_two_group_minima
  minSize | bind-only (definition) | none | claim, elementary_two_group_minima, result
  minRestrictedSize | bind-only (definition) | none | claim, elementary_two_group_minima, result
  claim | bind-only (definition) | none | result
  uniformMinimum | bind-only | none | elementary_two_group_minima
  elementary_two_group_minima | bind-only | none | result
  result | bind-only | none | settling result
Finset.card_eq_one / Finset.card_eq_two extract singleton or pair images;
parity in exponent two gives the restricted identity, while large-set coverage
and Finset.card_nsmul_mono give the ordinary identity.
CLAUDE.md §3.2 permits this bind-only resolution of an external named open problem.
-/

import Mathlib.Tactic
noncomputable section
open scoped Pointwise
open Finset
namespace D5.S3.FiniteGroups.BhanjaRestrictedSumset.Result

def hSumset {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h : ℕ) (A : Finset G) : Finset G := h • A

def restrictedSumset {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h r : ℕ) (A : Finset G) : Finset G :=
  ((Fintype.piFinset fun _ : Fin h => A).filter
    fun f => (univ.image f).card ≤ r).image fun f => ∑ i, f i

private lemma memR {G : Type*} [AddCommGroup G] [DecidableEq G]
    (h r : ℕ) (A : Finset G) (x : G) :
    x ∈ restrictedSumset h r A ↔ ∃ f : Fin h → G,
      (∀ i, f i ∈ A) ∧ (univ.image f).card ≤ r ∧ ∑ i, f i = x := by
  simp only [restrictedSumset, mem_image, mem_filter, Fintype.mem_piFinset]
  aesop

private lemma doubleZero (m : ℕ) (a : Fin m → ZMod 2) : 2 • a = 0 := by
  exact ZModModule.char_nsmul_eq_zero 2 a

private lemma oddSmul (m h : ℕ) (hodd : Odd h) (a : Fin m → ZMod 2) : h • a = a := by
  rw [nsmul_eq_mod_nsmul h (doubleZero m a), Nat.odd_iff.mp hodd, one_nsmul]

private lemma pairSum (m h : ℕ) (hodd : Odd h) (f : Fin h → (Fin m → ZMod 2))
    (a b : Fin m → ZMod 2) (hf : ∀ i, f i = a ∨ f i = b) :
    (∑ i, f i) = a ∨ (∑ i, f i) = b := by
  classical
  let u := (univ.filter fun i => f i = a).card
  let v := (univ.filter fun i => f i ≠ a).card
  have huv : u + v = h := by
    simpa [u, v] using card_filter_add_card_filter_not (s := univ) (fun i => f i = a)
  have hs : (∑ i, f i) = u • a + v • b := by
    calc
      _ = ∑ i, if f i = a then a else b := by
        apply sum_congr rfl
        intro i hi
        rcases hf i with he | he <;> simp [he]
      _ = _ := by rw [sum_ite]; simp [u, v]
  have hp := Nat.odd_iff.mp hodd
  have hcases : (u % 2 = 1 ∧ v % 2 = 0) ∨ (u % 2 = 0 ∧ v % 2 = 1) := by omega
  rw [hs, nsmul_eq_mod_nsmul u (doubleZero m a), nsmul_eq_mod_nsmul v (doubleZero m b)]
  rcases hcases with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [hu, hv]

private lemma restrictedOdd (m h : ℕ) (hodd : Odd h)
    (A : Finset (Fin m → ZMod 2)) : restrictedSumset h 2 A = A := by
  classical
  have hh : 0 < h := hodd.pos
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, hc, rfl⟩ := (memR h 2 A x).mp hx
    let S := univ.image f
    have hS : S.Nonempty := ⟨f ⟨0, hh⟩, mem_image_of_mem _ (mem_univ _)⟩
    have hSc : S.card = 1 ∨ S.card = 2 := by
      change S.card ≤ 2 at hc
      have := hS.card_pos
      omega
    rcases hSc with hSc | hSc
    · obtain ⟨a, ha⟩ := card_eq_one.mp hSc
      have hfa : ∀ i, f i = a := by
        intro i
        have : f i ∈ S := mem_image_of_mem _ (mem_univ _)
        simpa [ha] using this
      simp only [hfa, sum_const, card_univ, Fintype.card_fin]
      rw [oddSmul m h hodd]
      simpa [hfa] using hf ⟨0, hh⟩
    · obtain ⟨a, b, hab, hSab⟩ := card_eq_two.mp hSc
      have hfa : ∀ i, f i = a ∨ f i = b := by
        intro i
        have : f i ∈ S := mem_image_of_mem _ (mem_univ _)
        simpa [hSab] using this
      have ha : a ∈ A := by
        have : a ∈ S := by simp [hSab]
        obtain ⟨i, hi, rfl⟩ := mem_image.mp this
        exact hf i
      have hb : b ∈ A := by
        have : b ∈ S := by simp [hSab]
        obtain ⟨i, hi, rfl⟩ := mem_image.mp this
        exact hf i
      rcases pairSum m h hodd f a b hfa with hs | hs <;> simpa [hs] using (by assumption : _ ∈ A)
  · intro hx
    apply (memR h 2 A x).mpr
    refine ⟨fun _ => x, fun _ => hx, ?_, ?_⟩
    · calc
        _ ≤ ({x} : Finset (Fin m → ZMod 2)).card := card_le_card (by
          intro y hy
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
          simp)
        _ ≤ 2 := by simp
    · simpa using oddSmul m h hodd x

private lemma largeDouble {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (hc : Fintype.card G < 2 * A.card) : A + A = univ := by
  classical
  apply eq_univ_iff_forall.mpr
  intro g
  let B := A.image fun a => g - a
  have hBc : B.card = A.card := card_image_of_injective _ (fun a b hab => sub_right_injective hab)
  obtain ⟨x, hx⟩ := inter_nonempty_of_card_lt_card_add_card
    (subset_univ A) (subset_univ B) (by simp only [card_univ, hBc]; omega)
  obtain ⟨a, ha, he⟩ := mem_image.mp (mem_inter.mp hx).2
  apply mem_add.mpr
  exact ⟨x, (mem_inter.mp hx).1, a, ha, by rw [← he]; abel⟩

private lemma largeIterated {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (h : ℕ) (hh : 2 ≤ h) (A : Finset G) (hc : Fintype.card G < 2 * A.card) :
    hSumset h A = univ := by
  classical
  unfold hSumset
  apply Finset.eq_univ_of_card
  apply le_antisymm (Finset.card_le_univ _)
  calc
    Fintype.card G = (2 • A).card := by rw [two_nsmul, largeDouble A hc, card_univ]
    _ ≤ (h • A).card := Finset.card_nsmul_mono (by decide : 2 ≠ 0) hh

theorem elementary_two_group_gap (m : ℕ) (hm : 2 ≤ m) (h : ℕ)
    (hodd : Odd h) (h3 : 3 ≤ h) (A : Finset (Fin m → ZMod 2))
    (hk1 : 2^(m-1) < A.card) (_hk2 : A.card < 2^m) :
    restrictedSumset h 2 A = A ∧ hSumset h A = univ := by
  refine ⟨restrictedOdd m h hodd A, largeIterated h (by omega) A ?_⟩
  have hp : 2^m = 2 * 2^(m-1) := by
    calc
      2^m = 2^((m - 1) + 1) := congrArg (fun n => 2^n) (by omega)
      _ = 2 * 2^(m - 1) := by rw [pow_succ]; omega
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  omega

def minSize (G : Type*) [AddCommGroup G] [DecidableEq G] (k h : ℕ) : ℕ :=
  sInf {n | ∃ A : Finset G, A.card = k ∧ (hSumset h A).card = n}

def minRestrictedSize (G : Type*) [AddCommGroup G] [DecidableEq G] (k h r : ℕ) : ℕ :=
  sInf {n | ∃ A : Finset G, A.card = k ∧ (restrictedSumset h r A).card = n}

def claim : Prop := ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (h k r : ℕ),
  1 ≤ h → 2 ≤ r → (∃ A : Finset G, A.card = k) →
    minRestrictedSize G k h r = minSize G k h

private lemma uniformMinimum {G : Type*} [DecidableEq G] (k v : ℕ)
    (F : Finset G → Finset G) (hex : ∃ A : Finset G, A.card = k)
    (hF : ∀ A : Finset G, A.card = k → (F A).card = v) :
    sInf {n | ∃ A : Finset G, A.card = k ∧ (F A).card = n} = v := by
  have he : {n | ∃ A : Finset G, A.card = k ∧ (F A).card = n} = {v} := by
    ext n
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact hF A hA
    · intro hn
      have : n = v := hn
      obtain ⟨A, hA⟩ := hex
      exact ⟨A, hA, (hF A hA).trans this.symm⟩
  rw [he, csInf_singleton]

theorem elementary_two_group_minima (m : ℕ) (hm : 2 ≤ m) (h : ℕ)
    (hodd : Odd h) (h3 : 3 ≤ h) (k : ℕ)
    (hk1 : 2^(m-1) < k) (hk2 : k < 2^m) :
    minRestrictedSize (Fin m → ZMod 2) k h 2 = k ∧
      minSize (Fin m → ZMod 2) k h = 2^m := by
  classical
  have hex : ∃ A : Finset (Fin m → ZMod 2), A.card = k := by
    obtain ⟨A, hA, hc⟩ := exists_subset_card_eq (s := (univ : Finset (Fin m → ZMod 2)))
      (show k ≤ univ.card by simpa using hk2.le)
    exact ⟨A, hc⟩
  constructor
  · apply uniformMinimum k k (restrictedSumset h 2) hex
    intro A hA
    rw [(elementary_two_group_gap m hm h hodd h3 A (by omega) (by omega)).1, hA]
  · apply uniformMinimum k (2^m) (hSumset h) hex
    intro A hA
    rw [(elementary_two_group_gap m hm h hodd h3 A (by omega) (by omega)).2]
    simp

theorem result : ¬ claim := by
  intro hc
  have he := elementary_two_group_minima 2 (by omega) 3 (by decide) (by omega)
    3 (by norm_num) (by norm_num)
  have hex : ∃ A : Finset (Fin 2 → ZMod 2), A.card = 3 := by
    obtain ⟨A, hA, hc⟩ := exists_subset_card_eq (s := (univ : Finset (Fin 2 → ZMod 2)))
      (show 3 ≤ univ.card by decide)
    exact ⟨A, hc⟩
  have hh := hc (Fin 2 → ZMod 2) 3 3 2 (by omega) (by omega) hex
  rw [he.1, he.2] at hh
  norm_num at hh
end D5.S3.FiniteGroups.BhanjaRestrictedSumset.Result
