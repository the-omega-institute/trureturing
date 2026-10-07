/- GID: D5/S1/Words/Patterns/Separable/RecordTransport
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordTransport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fin.Rev]
   utility: none
   digest: Actual four-record transports and all rising comparisons through record three. -/

import D5.S1.Words.Patterns.Separable.RecordPeak
import Mathlib.Data.Fin.Rev

namespace D5.S1.Words.Patterns.Separable.RecordTransport

open D5.S1.Words.Patterns.Separable.RecordPeak
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ActualCardinality
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open D5.S1.Words.Patterns.Separable.ProperCut (pattern2413 pattern3142)

def IsLeftMaximum {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j, j < i → π j < π i

def IsLeftMinimum {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j, j < i → π i < π j

def IsRightMinimum {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j, i < j → π i < π j

noncomputable def lmax {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (IsLeftMaximum π)).card

noncomputable def lmin {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (IsLeftMinimum π)).card

noncomputable def rmin {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (IsRightMinimum π)).card

/-- Positive length is part of the irreducible class. -/
noncomputable def irreducibleCount (n : ℕ) (stat : Equiv.Perm (Fin n) → ℕ)
    (k : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card {π : Indecomposable false n // stat π.val.val = k}

noncomputable def reducibleCount (n : ℕ) (stat : Equiv.Perm (Fin n) → ℕ)
    (k : ℕ) : ℕ :=
  Nat.card {π : ProperSigned false n // stat π.val.val = k}

/-- Actual symmetry of the four record fibers, including the singleton
correction, and the complete rising side at every length at least four. -/
theorem actual_four_record_transports_and_rising :
    (∀ n k,
      irreducibleCount n lmin k = irreducibleCount n rmax k ∧
      reducibleCount n lmax k + (if n = 1 ∧ k = 1 then 1 else 0) =
        irreducibleCount n rmax k ∧
      reducibleCount n rmin k + (if n = 1 ∧ k = 1 then 1 else 0) =
        irreducibleCount n rmax k) ∧
    (∀ n, 0 < n →
      irreducibleCount n rmax 0 = 0 ∧ irreducibleCount n lmin 0 = 0 ∧
      reducibleCount n lmax 0 = 0 ∧ reducibleCount n rmin 0 = 0) ∧
    (∀ n, 2 ≤ n →
      irreducibleCount n rmax 1 = 0 ∧ irreducibleCount n lmin 1 = 0 ∧
      reducibleCount n lmax 1 = 0 ∧ reducibleCount n rmin 1 = 0) ∧
    (∀ n, 4 ≤ n → ∀ k, k < 3 →
      irreducibleCount n rmax k ≤ irreducibleCount n rmax (k + 1) ∧
      irreducibleCount n lmin k ≤ irreducibleCount n lmin (k + 1) ∧
      reducibleCount n lmax k ≤ reducibleCount n lmax (k + 1) ∧
      reducibleCount n rmin k ≤ reducibleCount n rmin (k + 1)) := by
  classical
  have complementPatterns :
      (∀ i, (pattern2413 i).rev = pattern3142 i) ∧
      (∀ i, (pattern3142 i).rev = pattern2413 i) := by decide
  have reversePatterns :
      (∀ i, pattern2413 i.rev = pattern3142 i) ∧
      (∀ i, pattern3142 i.rev = pattern2413 i) := by decide
  let complement {n : ℕ} (π : Avoider n) : Avoider n :=
    ⟨π.val.trans Fin.revPerm, by
      constructor
      · rintro ⟨embedding, order⟩
        apply π.property.2
        refine ⟨embedding, fun i j => ?_⟩
        rw [← complementPatterns.1 i, ← complementPatterns.1 j, Fin.rev_lt_rev]
        simpa only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using order j i
      · rintro ⟨embedding, order⟩
        apply π.property.1
        refine ⟨embedding, fun i j => ?_⟩
        rw [← complementPatterns.2 i, ← complementPatterns.2 j, Fin.rev_lt_rev]
        simpa only [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using order j i⟩
  let reverse {n : ℕ} (π : Avoider n) : Avoider n :=
    ⟨Fin.revPerm.trans π.val, by
      constructor
      · rintro ⟨embedding, order⟩
        apply π.property.2
        let reversed : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono
          (fun i => (embedding i.rev).rev)
          (fun _ _ h => Fin.rev_strictAnti (embedding.strictMono (Fin.rev_strictAnti h)))
        refine ⟨reversed, fun i j => ?_⟩
        change pattern3142 i < pattern3142 j ↔
          π.val (embedding i.rev).rev < π.val (embedding j.rev).rev
        simpa only [Equiv.trans_apply, Fin.revPerm_apply, reversePatterns.1]
          using order i.rev j.rev
      · rintro ⟨embedding, order⟩
        apply π.property.1
        let reversed : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono
          (fun i => (embedding i.rev).rev)
          (fun _ _ h => Fin.rev_strictAnti (embedding.strictMono (Fin.rev_strictAnti h)))
        refine ⟨reversed, fun i j => ?_⟩
        change pattern2413 i < pattern2413 j ↔
          π.val (embedding i.rev).rev < π.val (embedding j.rev).rev
        simpa only [Equiv.trans_apply, Fin.revPerm_apply, reversePatterns.2]
          using order i.rev j.rev⟩
  have complementInvolution {n : ℕ} : Function.Involutive (@complement n) := by
    intro π
    apply Subtype.ext
    ext i
    simp [complement, Equiv.trans_apply]
  have reverseInvolution {n : ℕ} : Function.Involutive (@reverse n) := by
    intro π
    apply Subtype.ext
    ext i
    simp [reverse, Equiv.trans_apply]
  have commuting {n : ℕ} (π : Avoider n) :
      complement (reverse π) = reverse (complement π) := by
    apply Subtype.ext
    ext i
    rfl
  let both {n : ℕ} (π : Avoider n) := complement (reverse π)
  have bothInvolution {n : ℕ} : Function.Involutive (@both n) := by
    intro π
    change complement (reverse (complement (reverse π))) = π
    rw [← commuting, complementInvolution, reverseInvolution]
  have complementProper {n : ℕ} (sign : Bool) (π : Avoider n) :
      HasProperCut (!sign) (complement π).val ↔ HasProperCut sign π.val := by
    unfold HasProperCut
    cases sign <;> simp [Cut, complement, Equiv.trans_apply, Fin.rev_lt_rev]
  have reverseCut {n : ℕ} (sign : Bool) (π : Avoider n) (cut : ℕ) (hc : cut ≤ n) :
      Cut (!sign) (reverse π).val cut ↔ Cut sign π.val (n - cut) := by
    constructor <;> intro h i j hi hj
    · have h' := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
          (by simp only [Fin.val_rev]; omega)
      cases sign <;> simpa [reverse, Equiv.trans_apply] using h'
    · have h' := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
          (by simp only [Fin.val_rev]; omega)
      cases sign <;> simpa [reverse, Equiv.trans_apply] using h'
  have reverseProper {n : ℕ} (sign : Bool) (π : Avoider n) :
      HasProperCut (!sign) (reverse π).val ↔ HasProperCut sign π.val := by
    constructor
    · rintro ⟨c, hp, hb, h⟩
      exact ⟨n-c, by omega, by omega, (reverseCut sign π c (by omega)).mp h⟩
    · rintro ⟨c, hp, hb, h⟩
      refine ⟨n-c, by omega, by omega, (reverseCut sign π (n-c) (by omega)).mpr ?_⟩
      convert h using 1
      omega
  have bothProper {n : ℕ} (sign : Bool) (π : Avoider n) :
      HasProperCut sign (both π).val ↔ HasProperCut sign π.val := by
    calc
      HasProperCut sign (both π).val ↔ HasProperCut (!sign) (reverse π).val := by
        simpa only [both, Bool.not_not] using complementProper (!sign) (reverse π)
      _ ↔ HasProperCut sign π.val := reverseProper sign π
  have complementRecord {n : ℕ} (π : Avoider n) : rmin (complement π).val = rmax π.val := by
    unfold rmin rmax
    congr 1
    apply Finset.filter_congr
    intro i _
    simp [IsRightMinimum, IsRightMaximum, complement, Equiv.trans_apply, Fin.rev_lt_rev]
  have reverseRecord {n : ℕ} (π : Avoider n) : lmax (reverse π).val = rmax π.val := by
    apply (Finset.card_equiv Fin.revPerm ?_).symm
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply]
    constructor
    · intro h j hj
      have h' := h j.rev (Fin.lt_rev_iff.mp hj)
      simpa only [reverse, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev] using h'
    · intro h j hj
      have h' := h j.rev (by simpa only [Fin.rev_lt_rev, Fin.rev_rev] using hj)
      simpa only [reverse, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev] using h'
  have bothRecord {n : ℕ} (π : Avoider n) : lmin (both π).val = rmax π.val := by
    have eq : lmin (complement (reverse π)).val = lmax (reverse π).val := by
      unfold lmin lmax
      congr 1
      apply Finset.filter_congr
      intro i _
      simp [IsLeftMinimum, IsLeftMaximum, complement, Equiv.trans_apply, Fin.rev_lt_rev]
    exact eq.trans (reverseRecord π)
  have properTiny (n : ℕ) (stat : Equiv.Perm (Fin n) → ℕ) (k : ℕ) (hn : n ≤ 1) :
      reducibleCount n stat k = 0 := by
    have : IsEmpty {π : ProperSigned false n // stat π.val.val = k} :=
      ⟨fun π => by obtain ⟨c, hp, hb, _⟩ := π.val.property; omega⟩
    exact Nat.card_of_isEmpty
  have singletonRecords (π : Equiv.Perm (Fin 1)) :
      rmax π = 1 ∧ lmin π = 1 ∧ lmax π = 1 ∧ rmin π = 1 := by
    have noComparison : ∀ i j : Fin 1, ¬i < j := by
      intro i j
      simp only [Fin.lt_def]
      omega
    have hr : ∀ i, IsRightMaximum π i := fun i j h => (noComparison i j h).elim
    have hl : ∀ i, IsLeftMinimum π i := fun i j h => (noComparison j i h).elim
    have hm : ∀ i, IsLeftMaximum π i := fun i j h => (noComparison j i h).elim
    have hn : ∀ i, IsRightMinimum π i := fun i j h => (noComparison i j h).elim
    simp [rmax, lmin, lmax, rmin, hr, hl, hm, hn]
  obtain ⟨_, _, _, _, _, _, _, tinyCounts, _, _⟩ := actual_schroder_cardinality
  have singleCount (stat : Equiv.Perm (Fin 1) → ℕ) (hs : ∀ π, stat π = 1) (k : ℕ) :
      irreducibleCount 1 stat k = if k = 1 then 1 else 0 := by
    simp only [irreducibleCount, Nat.one_ne_zero, if_false]
    by_cases hk : k = 1
    · subst k
      rw [if_pos rfl]
      exact (Nat.card_congr (Equiv.subtypeUnivEquiv
        (fun π : Indecomposable false 1 => hs π.val.val))).trans (tinyCounts false).2
    · rw [if_neg hk]
      have : IsEmpty {π : Indecomposable false 1 // stat π.val.val = k} :=
        ⟨fun π => hk (π.property.symm.trans (hs π.val.val.val))⟩
      exact Nat.card_of_isEmpty
  have transports (n k : ℕ) :
      irreducibleCount n lmin k = irreducibleCount n rmax k ∧
      reducibleCount n lmax k + (if n = 1 ∧ k = 1 then 1 else 0) =
        irreducibleCount n rmax k ∧
      reducibleCount n rmin k + (if n = 1 ∧ k = 1 then 1 else 0) =
        irreducibleCount n rmax k := by
    by_cases hz : n = 0
    · subst n
      simp [irreducibleCount, properTiny 0 lmax k (by omega),
        properTiny 0 rmin k (by omega)]
    by_cases ho : n = 1
    · subst n
      simp [singleCount rmax (fun π => (singletonRecords π).1) k,
        singleCount lmin (fun π => (singletonRecords π).2.1) k,
        properTiny 1 lmax k (by omega), properTiny 1 rmin k (by omega)]
    have hn : 2 ≤ n := by omega
    have same : irreducibleCount n rmax k = irreducibleCount n lmin k := by
      let e : Avoider n ≃ Avoider n := ⟨both, both, bothInvolution, bothInvolution⟩
      let ec : Indecomposable false n ≃ Indecomposable false n :=
        Equiv.subtypeEquiv e (fun π => (bothProper false π).not.symm)
      simp only [irreducibleCount, if_neg hz]
      apply Nat.card_congr (Equiv.subtypeEquiv ec ?_)
      intro π
      change rmax π.val.val = k ↔ lmin (both π.val).val = k
      rw [bothRecord]
    have exchanged (e : Avoider n ≃ Avoider n)
        (hc : ∀ π, HasProperCut true (e π).val ↔ HasProperCut false π.val)
        (stat : Equiv.Perm (Fin n) → ℕ) (hr : ∀ π, stat (e π).val = rmax π.val) :
        irreducibleCount n rmax k = reducibleCount n stat k := by
      obtain ⟨_, _, _, _, _, _, _, _, signLaw⟩ :=
        endpoint_history_count_kernel (EndpointHistory.stop none n)
      let ec : Indecomposable false n ≃ Indecomposable true n :=
        Equiv.subtypeEquiv e (fun π => (hc π).not.symm)
      let ep : Indecomposable true n ≃ ProperSigned false n :=
        Equiv.subtypeEquivRight (fun π => signLaw false hn π)
      simp only [irreducibleCount, if_neg hz, reducibleCount]
      apply Nat.card_congr (Equiv.subtypeEquiv (ec.trans ep) ?_)
      intro π
      change rmax π.val.val = k ↔ stat (e π.val).val = k
      rw [hr]
    refine ⟨same.symm, ?_, ?_⟩
    · simp only [ho, false_and, if_false, add_zero]
      exact (exchanged ⟨reverse, reverse, reverseInvolution, reverseInvolution⟩
        (reverseProper false) lmax reverseRecord).symm
    · simp only [ho, false_and, if_false, add_zero]
      exact (exchanged ⟨complement, complement, complementInvolution, complementInvolution⟩
        (complementProper false) rmin complementRecord).symm
  have positiveRecord (n : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin n)) : 1 ≤ rmax π := by
    apply Nat.succ_le_iff.mpr
    apply Finset.card_pos.mpr
    refine ⟨⟨n-1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro j hj
    have bound := j.isLt
    simp only [Fin.lt_def] at hj
    omega
  have twoRecords (n : ℕ) (hn : 2 ≤ n) (π : Indecomposable false n) :
      2 ≤ rmax π.val.val := by
    have hp := positiveRecord n (by omega) π.val.val
    by_contra htwo
    have hone : rmax π.val.val = 1 := by omega
    let last : Fin n := ⟨n-1, by omega⟩
    let top : Fin n := π.val.val.symm last
    have ht : π.val.val top = last := π.val.val.apply_symm_apply last
    have lastRecord : IsRightMaximum π.val.val last := by
      intro j hj
      have bound := j.isLt
      simp only [Fin.lt_def] at hj
      dsimp [last] at hj
      omega
    have topRecord : IsRightMaximum π.val.val top := by
      intro j hj
      rw [ht]
      have hne : π.val.val j ≠ last := by
        intro he
        have eq := π.val.val.injective (he.trans ht.symm)
        exact (ne_of_gt hj) eq
      have bound := (π.val.val j).isLt
      have hval : (π.val.val j).val ≠ n-1 := fun he => hne (Fin.ext he)
      change (π.val.val j).val < n-1
      omega
    have eq : top = last := (Finset.card_le_one.mp hone.le)
      top (Finset.mem_filter.mpr ⟨Finset.mem_univ _, topRecord⟩)
      last (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lastRecord⟩)
    have hlast : π.val.val last = last := eq ▸ ht
    apply π.property
    refine ⟨n-1, by omega, by omega, ?_⟩
    intro i j hi hj
    have jeq : j = last := Fin.ext (by have := j.isLt; dsimp [last]; omega)
    subst j
    change π.val.val i < π.val.val last
    rw [hlast]
    have hne : π.val.val i ≠ last := by
      intro he
      have ieq := π.val.val.injective (he.trans hlast.symm)
      have := congrArg Fin.val ieq
      dsimp [last] at this
      omega
    have bound := (π.val.val i).isLt
    have hval : (π.val.val i).val ≠ n-1 := fun he => hne (Fin.ext he)
    change (π.val.val i).val < n-1
    omega
  have zeroRecords (n : ℕ) (hn : 0 < n) : irreducibleCount n rmax 0 = 0 := by
    simp only [irreducibleCount, if_neg (by omega : n ≠ 0)]
    have : IsEmpty {π : Indecomposable false n // rmax π.val.val = 0} :=
      ⟨fun π => by have := positiveRecord n hn π.val.val.val; omega⟩
    exact Nat.card_of_isEmpty
  have oneRecord (n : ℕ) (hn : 2 ≤ n) : irreducibleCount n rmax 1 = 0 := by
    simp only [irreducibleCount, if_neg (by omega : n ≠ 0)]
    have : IsEmpty {π : Indecomposable false n // rmax π.val.val = 1} :=
      ⟨fun π => by have := twoRecords n hn π.val; omega⟩
    exact Nat.card_of_isEmpty
  refine ⟨transports, ?_, ?_, ?_⟩
  · intro n hn
    have h := transports n 0
    simp only [show ¬(n = 1 ∧ (0 : ℕ) = 1) by omega, if_false, add_zero] at h
    rw [h.1, h.2.1, h.2.2, zeroRecords n hn]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro n hn
    have h := transports n 1
    simp only [show n ≠ 1 by omega, false_and, if_false, add_zero] at h
    rw [h.1, h.2.1, h.2.2, oneRecord n hn]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro n hn k hk
    have h := transports n k
    have hs := transports n (k+1)
    simp only [show n ≠ 1 by omega, false_and, if_false, add_zero] at h hs
    rw [h.1, h.2.1, h.2.2, hs.1, hs.2.1, hs.2.2]
    have rising : irreducibleCount n rmax k ≤ irreducibleCount n rmax (k+1) := by
      interval_cases k
      · rw [zeroRecords n (by omega)]
        exact Nat.zero_le _
      · rw [oneRecord n (by omega)]
        exact Nat.zero_le _
      · simp only [irreducibleCount, if_neg (by omega : n ≠ 0)]
        exact actual_record_rising n hn
    exact ⟨rising, rising, rising, rising⟩

end D5.S1.Words.Patterns.Separable.RecordTransport
