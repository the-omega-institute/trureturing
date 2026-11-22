/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Characterize coordinatewise bounds on odd-multiplier seed counts by a marked binary support. -/

import D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
import D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization
import D5.S3.Combinatorics.Transportation.OrderedMarginAllocation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedSupport

open Finset
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds (EvenSubset OddSubset)
open D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
open D5.S3.ConceptDynamics.Attribution.ParityColouredTableRealization

noncomputable section

private theorem exists_nat_transport {P Q : Type*} [Fintype P] [Fintype Q]
    (supply : P → ℕ) (demand : Q → ℕ) (balance : (∑ p, supply p) = ∑ q, demand q) :
    ∃ t : P → Q → ℕ, (∀ p, ∑ q, t p q = supply p) ∧ (∀ q, ∑ p, t p q = demand q) := by
  classical
  let rows := (univ : Finset P).toList
  let columns := (univ : Finset Q).toList
  let s := D5.S3.Combinatorics.Transportation.OrderedMarginAllocation.orderedAllocation
    rows columns supply demand
  have tabs := D5.S3.Combinatorics.Transportation.OrderedMarginAllocation.ordered_allocation_complete
    rows columns (by simp [rows]) (by simp [columns]) supply demand balance
  exact ⟨fun p q => s.2.2 (p, q), fun p => (tabs.1 p).2, fun q => (tabs.2.1 q).2⟩

/-- Recover a table with specified odd cells and optional mandatory mass in one cell. -/
private theorem parity_support_completion {P Q : Type*} [Fintype P] [Fintype Q]
    (base : P → Q → ℕ) (row : P → ℕ) (col : Q → ℕ)
    (balance : (∑ p, row p) = ∑ q, col q) :
    (∃ m : P → Q → ℕ, (∀ p, ∑ q, m p q = row p) ∧ (∀ q, ∑ p, m p q = col q) ∧
      ∀ p q, base p q ≤ m p q ∧ m p q % 2 = base p q % 2) ↔
    (∀ p, (∑ q, base p q) ≤ row p ∧ (∑ q, base p q) % 2 = row p % 2) ∧
    (∀ q, (∑ p, base p q) ≤ col q ∧ (∑ p, base p q) % 2 = col q % 2) := by
  constructor
  · rintro ⟨m, rows, cols, cells⟩
    have parity (p : P) (q : Q) : base p q ≡ m p q [MOD 2] := (cells p q).2.symm
    exact ⟨fun p => ⟨(sum_le_sum (fun q _ => (cells p q).1)).trans_eq (rows p), by
      have h := Nat.ModEq.sum (s := (univ : Finset Q)) fun q _ => parity p q
      rwa [rows] at h⟩, fun q => ⟨(sum_le_sum (fun p _ => (cells p q).1)).trans_eq (cols q), by
      have h := Nat.ModEq.sum (s := (univ : Finset P)) fun p _ => parity p q
      rwa [cols] at h⟩⟩
  · rintro ⟨rp, cp⟩
    let u (p : P) := (row p - ∑ q, base p q) / 2
    let v (q : Q) := (col q - ∑ p, base p q) / 2
    have row_eq (p : P) : (∑ q, base p q) + 2 * u p = row p := by
      obtain ⟨bound, parity⟩ := rp p
      dsimp only [u]
      omega
    have col_eq (q : Q) : (∑ p, base p q) + 2 * v q = col q := by
      obtain ⟨bound, parity⟩ := cp q
      dsimp only [v]
      omega
    have row_sum : (∑ p, ∑ q, base p q) + 2 * (∑ p, u p) = ∑ p, row p := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl (fun p _ => row_eq p)
    have col_sum : (∑ p, ∑ q, base p q) + 2 * (∑ q, v q) = ∑ q, col q := by
      rw [sum_comm (s := (univ : Finset P)), mul_sum, ← sum_add_distrib]
      exact sum_congr rfl (fun q _ => col_eq q)
    obtain ⟨t, htrow, htcol⟩ := exists_nat_transport u v (by omega)
    refine ⟨fun p q => base p q + 2 * t p q, ?_, ?_, ?_⟩
    · intro p
      rw [sum_add_distrib, ← mul_sum, htrow]
      exact row_eq p
    · intro q
      rw [sum_add_distrib, ← mul_sum, htcol]
      exact col_eq q
    · intro p q
      change base p q ≤ base p q + 2 * t p q ∧
        (base p q + 2 * t p q) % 2 = base p q % 2
      omega


private theorem colour_with_one_odd_column {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq Q]
    (m : P → Q → ℕ) (special : P) (marked : Q) {k : ℕ}
    (odd : k % 2 = 1) (rows : ∀ p, ∑ q, m p q = k)
    (present : 0 < m special marked) :
    ∃ b : P → Q → Fin 2 → ℕ,
      (∀ p c, ∑ q, b p q c = k) ∧
      (∀ p q, b p q 0 + b p q 1 = 2 * m p q) ∧
      (∀ p q c, p ≠ special → b p q c = m p q) ∧
      (∀ q c, b special q c % 2 = if q = marked then 1 else 0) := by
  classical
  let flag (q : Q) : ℕ := if q = marked then 1 else 0
  have flagSum : ∑ q, flag q = 1 := by simp [flag]
  have available (q : Q) : flag q ≤ m special q := by
    by_cases h : q = marked
    · simpa [flag, h] using (Nat.succ_le_of_lt present)
    · simp [flag, h]
  let rest (q : Q) := m special q - flag q
  have addRest (q : Q) : flag q + rest q = m special q := by
    have h := available q
    dsimp [rest]
    omega
  have totalRest : (∑ q, rest q) = k - 1 := by
    have sum_eq : (∑ q, flag q) + ∑ q, rest q = k := by
      rw [← sum_add_distrib]
      simp_rw [addRest, rows]
    omega
  let half := (k - 1) / 2
  have twiceHalf : 2 * half = k - 1 := by dsimp [half]; omega
  have residualBalance : (∑ _c : Fin 2, half) = ∑ q, rest q := by
    rw [totalRest, ← twiceHalf]
    simp
  obtain ⟨transport, supply, demand⟩ := exists_nat_transport
    (fun _ : Fin 2 => half) rest residualBalance
  let b (p : P) (q : Q) (c : Fin 2) :=
    if p = special then flag q + 2 * transport c q else m p q
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro p c
    by_cases h : p = special
    · simp only [b, h, ite_true]
      rw [sum_add_distrib, ← mul_sum, flagSum, supply c, twiceHalf]
      omega
    · simpa only [b, ite_eq_right h] using rows p
  · intro p q
    by_cases h : p = special
    · subst p
      simp only [b, eq_self, ite_true]
      have sum_at := demand q
      rw [Fin.sum_univ_two] at sum_at
      have source := addRest q
      omega
    · simp only [b, ite_eq_right h, two_mul]
  · intro p q c h
    simp only [b, ite_eq_right h]
  · intro q c
    simp only [b, eq_self, ite_true]
    by_cases h : q = marked <;> simp [flag, h, Nat.add_mod]

private theorem realize_from_base {n k : ℕ}
    (base : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ)
    (full : ParityClass (n + 2) 0) (hfull : full.val = 1)
    (marked : ParityClass (n + 2) 1) (present : 0 < base full marked)
    (odd : k % 2 = 1)
    (rp : ∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1)
    (cp : ∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) :
    ∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧
      ∀ i, z i = 4 * ∑ p, ∑ q,
        if p.val i = 1 ∧ q.val i = 1 then
          if p = full then if q = marked then 1 else 0 else base p q % 2
        else 0 := by
  classical
  have balance : (∑ _p : ParityClass (n + 2) 0, k) =
      ∑ _q : ParityClass (n + 2) 1, k := by
    simp only [sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card, parityCard]
  obtain ⟨m, rows, cols, cells⟩ :=
    (parity_support_completion base (fun _ => k) (fun _ => k) balance).mpr
      ⟨fun p => ⟨(rp p).1, (rp p).2.trans odd.symm⟩,
       fun q => ⟨(cp q).1, (cp q).2.trans odd.symm⟩⟩
  obtain ⟨b, brow, localCol, ordinary, flags⟩ :=
    colour_with_one_odd_column m full marked odd rows (present.trans_le (cells full marked).1)
  let z (i : Fin (n + 2)) := 2 * (∑ p, ∑ q, ∑ c : Fin 2,
    if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0)
  have fibre : RealizesFibreCounts n k (colouredPairWeight b) z := by
    apply realize_coloured_table b brow
    · intro q
      simp_rw [localCol, ← mul_sum, cols]
    · intro p q h
      have neq : p ≠ full := fun e => h (congrArg Subtype.val e |>.trans hfull)
      rw [ordinary p q 0 neq, ordinary p q 1 neq]
  obtain ⟨S, ftype, act, f, card, equivariant, margins, fixed, _⟩ := fibre
  refine ⟨z, ⟨S, ftype, act, f, card, equivariant, margins, fixed⟩, ?_⟩
  have parity (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      b p q 0 % 2 + b p q 1 % 2 =
        2 * (if p = full then if q = marked then 1 else 0 else base p q % 2) := by
    by_cases h : p = full
    · subst p
      simp only [flags, eq_self, ite_true, two_mul]
    · simp only [ite_eq_right h, ordinary p q 0 h, ordinary p q 1 h, (cells p q).2, two_mul]
  intro i
  have cells (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :
      (∑ c : Fin 2, if p.val i = 1 ∧ q.val i = 1 then b p q c % 2 else 0) =
        2 * (if p.val i = 1 ∧ q.val i = 1 then
          if p = full then if q = marked then 1 else 0 else base p q % 2
        else 0) := by
    by_cases h : p.val i = 1 ∧ q.val i = 1
    · simpa only [ite_eq_left h, Fin.sum_univ_two] using parity p q
    · simp only [ite_eq_right h, sum_const_zero, Nat.mul_zero]
  dsimp only [z]
  simp_rw [cells, ← mul_sum, ← Nat.mul_assoc]

/-- Count the coordinate's ordinary odd cells and the marked column of the full row. -/
def supportCount {d : ℕ} (base : EvenSubset d → OddSubset d → ℕ)
    (full : EvenSubset d) (marked : OddSubset d) (i : Fin d) : ℕ :=
  4 * ∑ p, ∑ q, if i ∈ p.val ∩ q.val then
    if p = full then if q = marked then 1 else 0 else base p q % 2 else 0

private theorem support_below_seed_counts (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (z : Fin (n + 2) → ℕ) (realized : RealizableSeedCounts n k z) :
    ∃ (base : EvenSubset (n + 2) → OddSubset (n + 2) → ℕ) (marked : OddSubset (n + 2)),
      (∀ p, ∑ q, base p q = k) ∧ (∀ q, ∑ p, base p q = k) ∧
      0 < base ⟨univ, by simpa using even⟩ marked ∧
      ∀ i, supportCount base ⟨univ, by simpa using even⟩ marked i ≤ z i := by
  obtain ⟨m, row, col, ordinary, bound⟩ := extract_coloured_subsets n k even z realized
  let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
  let mass (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) := (m p q 0 + m p q 1) / 2
  let flags (q : OddSubset (n + 2)) := m full q 0 % 2
  have othersEven (q : OddSubset (n + 2)) : (∑ p ∈ univ.erase full, (m p q 0 + m p q 1)) % 2 = 0 := by
    have h : (∑ p ∈ univ.erase full, (m p q 0 + m p q 1)) ≡
        (∑ _p ∈ univ.erase full, (0 : ℕ)) [MOD 2] := by
      apply Nat.ModEq.sum
      intro p hp
      have notFull : p.val ≠ univ := fun eq => (mem_erase.mp hp).1 (Subtype.ext eq)
      have eq := ordinary p q notFull
      change (m p q 0 + m p q 1) % 2 = 0
      omega
    simpa [Nat.ModEq] using h
  have sameParity (q : OddSubset (n + 2)) : m full q 0 % 2 = m full q 1 % 2 := by
    have hs := col q
    rw [← sum_erase_add _ _ (mem_univ full)] at hs
    have other := othersEven q
    omega
  have twoMass (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) :
      2 * mass p q = m p q 0 + m p q 1 := by
    by_cases eq : p.val = univ
    · have hp : p = full := Subtype.ext eq
      subst p
      dsimp [mass]
      have := sameParity q
      omega
    · have := ordinary p q eq
      dsimp [mass]
      omega
  have rows (p : EvenSubset (n + 2)) : ∑ q, mass p q = k := by
    have twice : 2 * (∑ q, mass p q) = 2 * k := by
      rw [mul_sum]
      simp_rw [twoMass, sum_add_distrib, row]
      omega
    omega
  have cols (q : OddSubset (n + 2)) : ∑ p, mass p q = k := by
    have twice : 2 * (∑ p, mass p q) = 2 * k := by
      rw [mul_sum]
      simp_rw [twoMass, col]
    omega
  have someFlag : ∃ q, 0 < flags q := by
    by_contra! absent
    have allEven : (∑ q, m full q 0) ≡ ∑ _q : OddSubset (n + 2), (0 : ℕ) [MOD 2] := by
      apply Nat.ModEq.sum
      intro q _
      have h := absent q
      change flags q = 0
      omega
    rw [row] at allEven
    simp [Nat.ModEq, odd] at allEven
  have flagFits (q : OddSubset (n + 2)) : flags q ≤ mass full q := by
    have a := Nat.mod_le (m full q 0) 2
    have b := Nat.mod_le (m full q 1) 2
    have eq := sameParity q
    have ht := twoMass full q
    dsimp [flags]
    omega
  obtain ⟨q, pos⟩ := someFlag
  have present : 1 ≤ mass full q := (Nat.succ_le_of_lt pos).trans (flagFits q)
  refine ⟨mass, q, rows, cols, present, ?_⟩
  intro i
  have one (c : OddSubset (n + 2)) :
      (if c = q then 1 else 0 : ℕ) ≤ flags c := by
    split
    · subst c
      omega
    · exact Nat.zero_le _
  let use (p : EvenSubset (n + 2)) (c : OddSubset (n + 2)) : ℕ :=
    if p = full then if c = q then 1 else 0 else mass p c % 2
  have cellEstimate (p : EvenSubset (n + 2)) (c : OddSubset (n + 2)) :
      2 * use p c ≤ m p c 0 % 2 + m p c 1 % 2 := by
    by_cases eq : p = full
    · subst p
      have same := sameParity c
      have h := one c
      simp only [use, eq_self, ite_true]
      dsimp only [flags] at h
      omega
    · have same := ordinary p c (fun h => eq (Subtype.ext h))
      have count : mass p c = m p c 0 := by
        have := twoMass p c
        omega
      rw [show use p c = mass p c % 2 by simp only [use, ite_eq_right eq], count, ← same, two_mul]
  have each (p : EvenSubset (n + 2)) (c : OddSubset (n + 2)) :
      2 * (if i ∈ p.val ∩ c.val then use p c else 0) ≤
        ∑ d : Fin 2, if i ∈ p.val ∩ c.val then m p c d % 2 else 0 := by
    by_cases h : i ∈ p.val ∩ c.val
    · simpa only [ite_eq_left h, Fin.sum_univ_two] using cellEstimate p c
    · simp [h]
  have sumBound := sum_le_sum (fun p (_ : p ∈ univ) =>
    sum_le_sum (fun c (_ : c ∈ univ) => each p c))
  simp_rw [← mul_sum] at sumBound
  unfold supportCount
  rw [show 4 = 2 * 2 by decide, Nat.mul_assoc]
  exact (Nat.mul_le_mul_left 2 sumBound).trans (bound i)

private def left (d : ℕ) : EvenSubset d ≃ ParityClass d 0 := parityClassEquiv d 0 (by decide)
private def right (d : ℕ) : OddSubset d ≃ ParityClass d 1 := parityClassEquiv d 1 (by decide)

private theorem left_bit {d : ℕ} (p : EvenSubset d) (i : Fin d) :
    (left d p).val i = 1 ↔ i ∈ p.val := by
  change indicator p.val i = 1 ↔ _
  by_cases h : i ∈ p.val <;> simp [indicator, h]

private theorem right_bit {d : ℕ} (q : OddSubset d) (i : Fin d) :
    (right d q).val i = 1 ↔ i ∈ q.val := by
  change indicator q.val i = 1 ↔ _
  by_cases h : i ∈ q.val <;> simp [indicator, h]

private theorem realize_base_subset (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (base : EvenSubset (n + 2) → OddSubset (n + 2) → ℕ) (marked : OddSubset (n + 2))
    (hp : 0 < base ⟨univ, by simpa using even⟩ marked)
    (rp : ∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1)
    (cp : ∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) :
    ∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧
      ∀ i, z i = supportCount base ⟨univ, by simpa using even⟩ marked i := by
  classical
  let pFull : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
  let m (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) :=
    base ((left (n + 2)).symm p) ((right (n + 2)).symm q)
  have full : (left (n + 2) pFull).val = 1 := by
    funext i
    apply (left_bit pFull i).mpr
    simp [pFull]
  have someMass : 0 < m (left (n + 2) pFull) (right (n + 2) marked) := by
    simpa only [m, Equiv.symm_apply_apply] using hp
  have rows (p : ParityClass (n + 2) 0) : (∑ q, m p q) ≤ k ∧ (∑ q, m p q) % 2 = 1 := by
    rw [← (right (n + 2)).sum_comp]
    simpa only [m, Equiv.symm_apply_apply] using rp ((left (n + 2)).symm p)
  have cols (q : ParityClass (n + 2) 1) : (∑ p, m p q) ≤ k ∧ (∑ p, m p q) % 2 = 1 := by
    rw [← (left (n + 2)).sum_comp]
    simpa only [m, Equiv.symm_apply_apply] using cp ((right (n + 2)).symm q)
  obtain ⟨z, feasible, count⟩ :=
    realize_from_base m (left (n + 2) pFull) full (right (n + 2) marked) someMass odd rows cols
  refine ⟨z, feasible, fun i => (count i).trans ?_⟩
  unfold supportCount
  congr 1
  rw [← (left (n + 2)).sum_comp]
  simp_rw [← (right (n + 2)).sum_comp]
  simp only [left_bit, right_bit, ← mem_inter, Equiv.apply_eq_iff_eq, m, Equiv.symm_apply_apply, pFull]

private theorem seed_counts_at_most_iff (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1) (budget : Fin (n + 2) → ℕ) :
    (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧ (∀ i, z i ≤ budget i)) ↔
    ∃ (base : EvenSubset (n + 2) → OddSubset (n + 2) → ℕ) (marked : OddSubset (n + 2)),
      (∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1) ∧
      (∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) ∧
      0 < base ⟨univ, by simpa using even⟩ marked ∧
      ∀ i, supportCount base ⟨univ, by simpa using even⟩ marked i ≤ budget i := by
  constructor
  · rintro ⟨z, realized, bound⟩
    obtain ⟨base, marked, rows, cols, positive, estimate⟩ :=
      support_below_seed_counts n k even odd z realized
    exact ⟨base, marked, fun p => by rw [rows p]; exact ⟨le_rfl, odd⟩,
      fun q => by rw [cols q]; exact ⟨le_rfl, odd⟩,
      positive, fun i => (estimate i).trans (bound i)⟩
  · rintro ⟨base, marked, rows, cols, positive, bound⟩
    obtain ⟨z, realized, score⟩ := realize_base_subset n k even odd base marked positive rows cols
    exact ⟨z, realized, fun i => (score i).le.trans (bound i)⟩

def minimalBase {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) (p : EvenSubset d) (q : OddSubset d) : ℕ :=
  (e p q).toNat + if p = full ∧ q = marked ∧ e p q = false then 2 else 0

private theorem minimalBase_parity {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) (p : EvenSubset d) (q : OddSubset d) :
    minimalBase e full marked p q % 2 = (e p q).toNat := by
  unfold minimalBase
  split <;> cases e p q <;> decide

private theorem minimalBase_present {d : ℕ} (e : EvenSubset d → OddSubset d → Bool)
    (full : EvenSubset d) (marked : OddSubset d) :
    0 < minimalBase e full marked full marked := by
  unfold minimalBase
  cases e full marked <;> simp

/-- Existence of an odd-margined binary support within the coordinate budgets. -/
def markedSupportWithin (n k : ℕ) (budget : Fin (n + 2) → ℕ) : Prop :=
    ∃ (even : (n + 2) % 2 = 0) (e : EvenSubset (n + 2) → OddSubset (n + 2) → Bool) (marked : OddSubset (n + 2)),
      let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
      let base := minimalBase e full marked
      (∀ p, (∑ q, base p q) ≤ k ∧ (∑ q, base p q) % 2 = 1) ∧
      (∀ q, (∑ p, base p q) ≤ k ∧ (∑ p, base p q) % 2 = 1) ∧
      ∀ i, supportCount base full marked i ≤ budget i

/-- A binary support and one marked column characterize simultaneous coordinate budgets. -/
theorem binary_support_iff (n k : ℕ) (even : (n + 2) % 2 = 0) (odd : k % 2 = 1)
    (budget : Fin (n + 2) → ℕ) :
    (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧ (∀ i, z i ≤ budget i)) ↔
    markedSupportWithin n k budget := by
  unfold markedSupportWithin
  rw [seed_counts_at_most_iff n k even odd]
  let full : EvenSubset (n + 2) := ⟨univ, by simpa using even⟩
  constructor
  · rintro ⟨base, marked, rows, cols, positive, bound⟩
    let e (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) := decide (base p q % 2 = 1)
    have epar (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) :
        (e p q).toNat = base p q % 2 := by
      by_cases h : base p q % 2 = 1
      · simp [e, h]
      · have h0 : base p q % 2 = 0 := by omega
        simp [e, h0]
    let smaller := minimalBase e full marked
    have par (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) :
        smaller p q % 2 = base p q % 2 := by
      rw [minimalBase_parity, epar]
    have no_larger (p : EvenSubset (n + 2)) (q : OddSubset (n + 2)) :
        smaller p q ≤ base p q := by
      dsimp only [smaller, minimalBase]
      rw [epar]
      split
      · rename_i special
        obtain ⟨hp, hq, h⟩ := special
        subst p
        subst q
        have bit := epar full marked
        rw [h] at bit
        change 0 = base full marked % 2 at bit
        change 0 < base full marked at positive
        omega
      · omega
    have sameCost (i : Fin (n + 2)) :
        supportCount smaller full marked i = supportCount base full marked i := by
      unfold supportCount
      simp_rw [par]
    refine ⟨even, e, marked, ?_, ?_, ?_⟩
    · intro p
      have r := Nat.ModEq.sum (s := univ) fun q _ => (par p q : smaller p q ≡ base p q [MOD 2])
      exact ⟨(sum_le_sum (fun q _ => no_larger p q)).trans (rows p).1, (show (∑ q, smaller p q) % 2 = (∑ q, base p q) % 2 from r).trans (rows p).2⟩
    · intro q
      have c := Nat.ModEq.sum (s := univ) fun p _ => (par p q : smaller p q ≡ base p q [MOD 2])
      exact ⟨(sum_le_sum (fun p _ => no_larger p q)).trans (cols q).1, (show (∑ p, smaller p q) % 2 = (∑ p, base p q) % 2 from c).trans (cols q).2⟩
    · intro i
      change supportCount smaller full marked i ≤ budget i
      rw [sameCost]
      exact bound i
  · rintro ⟨_, e, marked, rows, cols, bound⟩
    exact ⟨minimalBase e full marked, marked, rows, cols, minimalBase_present e full marked, bound⟩

end
end D5.S3.ConceptDynamics.Attribution.ParitySeedSupport
