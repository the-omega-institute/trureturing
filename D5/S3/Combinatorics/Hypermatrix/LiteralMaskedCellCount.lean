/- GID: D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Acyclic coefficient-one elimination counts both literal masked faces. -/

import D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

namespace D5.S3.Combinatorics.Hypermatrix.LiteralMaskedCellCount

open D5.S1.Digit.Carry.ListInversions
open D5.S3.Combinatorics.Permutation.CoupledRepairedWeight
open D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction

def LiteralSolutions {F : Type*} [Field F] {k : ℕ}
    (lam mu : Fin k → ℕ) (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :=
  {z : CellVariables sigma pi → F //
    (∀ r j, k+1-lam j ≤ r.val →
      (∑ b : Fin k, cellA sigma pi z r b.castSucc * cellB sigma pi z b j) = 0) ∧
    (∀ r j, k+1-mu j ≤ r.val →
      (∑ b : Fin k, cellA sigma pi z r b.succ * cellB sigma pi z b j) = 0)}

set_option maxHeartbeats 3000000 in
theorem literal_cell_count_original_masks (F : Type*) [Field F] [Fintype F]
    (k : ℕ) (hk : 1 ≤ k) (lam mu : Fin k → ℕ)
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hml : ∀ j, mu j ≤ lam j)
    (hlbound : ∀ j, lam j ≤ k - j.val)
    (hmbound : ∀ j, mu j < k - j.val) : by
  classical
  exact ∀ (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)),
      Nat.card (LiteralSolutions (F := F) lam mu sigma pi) =
        if Eligible (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi then
          Fintype.card F ^ (E (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi).toNat
        else 0 := by
  classical
  let rx (a b : ℕ) := 2 * (k + 1) * b + a
  let ry (p a : ℕ) := 2 * (k + 1) * p + (k + 1) + (k - 1 - a)
  have frontEndpointRank (a p j : ℕ) (ha : a < k + 1) :
      rx a p < ry p j := by
    dsimp [rx, ry]
    omega
  have frontMiddleRank (p a b : ℕ) (hab : a < b) (hb : b < k) :
      ry p b < ry p a := by
    dsimp [ry]
    omega
  have backXRank (a b p r : ℕ) (ha : a < k + 1) (hb : b ≤ p) :
      rx a b < rx r (p + 1) := by
    have hm := Nat.mul_le_mul_left (2 * (k + 1)) hb
    dsimp [rx]
    nlinarith
  have backYRank (p a r : ℕ) :
      ry p a < rx r (p + 1) := by
    have hsub : k - 1 - a ≤ k := Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)
    dsimp [rx, ry]
    nlinarith
  have frontXMiddleRank (a b p j : ℕ) (ha : a < k + 1) (hb : b < p) :
      rx a b < ry p j := by
    have hm := Nat.mul_le_mul_left (2 * (k + 1)) (Nat.succ_le_of_lt hb)
    dsimp [rx, ry]
    nlinarith
  have frontElimination (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (i j : Fin k) (hji : j < i) (hpi : pi i < pi j)
      (z : CellVariables sigma pi → F) :
      ∃! t : F,
        (∑ b : Fin k,
          cellA sigma pi (Function.update z (.inr ⟨(j,i),hji,hpi⟩) t)
            (sigma (pi i).castSucc) b.castSucc *
          cellB sigma pi (Function.update z (.inr ⟨(j,i),hji,hpi⟩) t) b j) = 0 := by
    let y : CellVariables sigma pi := .inr ⟨(j,i),hji,hpi⟩
    have hA (t : F) : cellA sigma pi (Function.update z y t) = cellA sigma pi z := by
      ext r b
      simp [cellA, y, Function.update]
    have hB (t : F) (b : Fin k) (hb : b ≠ pi i) :
        cellB sigma pi (Function.update z y t) b j = cellB sigma pi z b j := by
      have hi : pi.symm b ≠ i := fun he => hb (by simpa using congrArg pi he)
      simp only [cellB]
      split_ifs <;> simp_all [y, Function.update]
    let remainder := ∑ b ∈ Finset.univ.erase (pi i),
      cellA sigma pi z (sigma (pi i).castSucc) b.castSucc * cellB sigma pi z b j
    have entry (t : F) :
        (∑ b : Fin k, cellA sigma pi (Function.update z y t)
          (sigma (pi i).castSucc) b.castSucc *
          cellB sigma pi (Function.update z y t) b j) = t + remainder := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (pi i))]
      have hp : cellA sigma pi (Function.update z y t)
          (sigma (pi i).castSucc) (pi i).castSucc *
          cellB sigma pi (Function.update z y t) (pi i) j = t := by
        simp [cellA, cellB, y, Function.update, ne_of_lt hji, hji, hpi]
      rw [hp]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [hA, hB t b (Finset.ne_of_mem_erase hb)]
    refine ⟨-remainder, ?_, ?_⟩
    · change (∑ b : Fin k, cellA sigma pi (Function.update z y (-remainder))
          (sigma (pi i).castSucc) b.castSucc *
          cellB sigma pi (Function.update z y (-remainder)) b j) = 0
      rw [entry]
      simp
    · intro t ht
      change (∑ b : Fin k, cellA sigma pi (Function.update z y t)
          (sigma (pi i).castSucc) b.castSucc *
          cellB sigma pi (Function.update z y t) b j) = 0 at ht
      rw [entry] at ht
      exact eq_neg_of_add_eq_zero_left ht
  have backElimination (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (a : Fin (k+1)) (j : Fin k) (hap : a < (pi j).succ)
      (hrow : sigma (pi j).succ < sigma a) (z : CellVariables sigma pi → F) :
      ∃! t : F,
        (∑ b : Fin k,
          cellA sigma pi (Function.update z (.inl ⟨(a,(pi j).succ),hap,hrow⟩) t)
            (sigma a) b.succ *
          cellB sigma pi (Function.update z (.inl ⟨(a,(pi j).succ),hap,hrow⟩) t) b j) = 0 := by
    let x : CellVariables sigma pi := .inl ⟨(a,(pi j).succ),hap,hrow⟩
    have hB (t : F) : cellB sigma pi (Function.update z x t) = cellB sigma pi z := by
      ext r b
      simp [cellB, x, Function.update]
    have hA (t : F) (b : Fin k) (hb : b ≠ pi j) :
        cellA sigma pi (Function.update z x t) (sigma a) b.succ =
          cellA sigma pi z (sigma a) b.succ := by
      have hi : b.succ ≠ (pi j).succ := fun he => hb (Fin.succ_inj.mp he)
      simp only [cellA, Equiv.symm_apply_apply]
      split_ifs <;> simp_all [x, Function.update]
    let remainder := ∑ b ∈ Finset.univ.erase (pi j),
      cellA sigma pi z (sigma a) b.succ * cellB sigma pi z b j
    have entry (t : F) :
        (∑ b : Fin k, cellA sigma pi (Function.update z x t)
          (sigma a) b.succ * cellB sigma pi (Function.update z x t) b j) =
            t + remainder := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (pi j))]
      have hp : cellA sigma pi (Function.update z x t) (sigma a) (pi j).succ *
          cellB sigma pi (Function.update z x t) (pi j) j = t := by
        simp [cellA, cellB, x, Function.update, ne_of_lt hap, hap, hrow]
      rw [hp]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [hB, hA t b (Finset.ne_of_mem_erase hb)]
    refine ⟨-remainder, ?_, ?_⟩
    · change (∑ b : Fin k, cellA sigma pi (Function.update z x (-remainder))
          (sigma a) b.succ * cellB sigma pi (Function.update z x (-remainder)) b j) = 0
      rw [entry]
      simp
    · intro t ht
      change (∑ b : Fin k, cellA sigma pi (Function.update z x t)
          (sigma a) b.succ * cellB sigma pi (Function.update z x t) b j) = 0 at ht
      rw [entry] at ht
      exact eq_neg_of_add_eq_zero_left ht
  have frontForbiddenElimination (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k))
      (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi)
      (r : Fin (k+1)) (j : Fin k) (hr : k+1-lam j ≤ r.val) :
      (∀ z : CellVariables sigma pi → F,
        (∑ b : Fin k, cellA sigma pi z r b.castSucc * cellB sigma pi z b j) = 0) ∨
      ∃ (i : Fin k) (hji : j < i) (hpi : pi i < pi j),
        r = sigma (pi i).castSucc ∧
        ∀ z : CellVariables sigma pi → F, ∃! t : F,
          (∑ b : Fin k,
            cellA sigma pi (Function.update z (.inr ⟨(j,i),hji,hpi⟩) t) r b.castSucc *
            cellB sigma pi (Function.update z (.inr ⟨(j,i),hji,hpi⟩) t) b j) = 0 := by
    let a := sigma.symm r
    have hne : a ≠ (pi j).castSucc := by
      intro he
      have hp := (hel j).1
      change (sigma (pi j).castSucc).val < k+1-lam j at hp
      have hre : r = sigma (pi j).castSucc := by rw [← he]; exact (sigma.apply_symm_apply r).symm
      rw [hre] at hr
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      let af : Fin k := ⟨a.val, by have hh : a.val < (pi j).val := hlt; exact hh.trans (pi j).isLt⟩
      let i := pi.symm af
      have hcast : (pi i).castSucc = a := by simp [i, af]
      have hre : r = sigma (pi i).castSucc := by rw [hcast]; exact (sigma.apply_symm_apply r).symm
      have hji : j < i := by
        by_contra hn
        have hm := hlam (le_of_not_gt hn)
        have he := (hel i).1
        change (sigma (pi i).castSucc).val < k+1-lam i at he
        rw [← hre] at he
        omega
      have hpi : pi i < pi j := by
        change (pi i).val < (pi j).val
        simpa [i, af] using (show a.val < (pi j).val from hlt)
      exact ⟨i, hji, hpi, hre, fun z => by rw [hre]; exact frontElimination sigma pi i j hji hpi z⟩
    · left
      intro z
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : b ≤ pi j
      · have hab : b.castSucc < a := (show b.castSucc ≤ (pi j).castSucc from hb).trans_lt hgt
        have hane : a ≠ b.castSucc := ne_of_gt hab
        have hanot : ¬a < b.castSucc := not_lt_of_ge hab.le
        have har : sigma.symm r = a := rfl
        simp [cellA, har, hane, hanot]
      · have hpb : pi j < b := lt_of_not_ge hb
        have hjne : j ≠ pi.symm b := fun he => (ne_of_lt hpb) (by simpa using congrArg pi he)
        simp [cellB, hjne, not_lt_of_ge hpb.le]
  have backForbiddenElimination (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k))
      (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi)
      (r : Fin (k+1)) (j : Fin k) (hr : k+1-mu j ≤ r.val) :
      (∀ z : CellVariables sigma pi → F,
        (∑ b : Fin k, cellA sigma pi z r b.succ * cellB sigma pi z b j) = 0) ∨
      ∃ (a : Fin (k+1)) (hap : a < (pi j).succ)
        (hrow : sigma (pi j).succ < sigma a), r = sigma a ∧
        ∀ z : CellVariables sigma pi → F, ∃! t : F,
          (∑ b : Fin k,
            cellA sigma pi (Function.update z (.inl ⟨(a,(pi j).succ),hap,hrow⟩) t) r b.succ *
            cellB sigma pi (Function.update z (.inl ⟨(a,(pi j).succ),hap,hrow⟩) t) b j) = 0 := by
    let a := sigma.symm r
    have hre : r = sigma a := (sigma.apply_symm_apply r).symm
    have hrow : sigma (pi j).succ < sigma a := by
      have hp := (hel j).2
      change (sigma (pi j).succ).val < k+1-mu j at hp
      rw [hre] at hr
      change (sigma (pi j).succ).val < (sigma a).val
      omega
    have hne : a ≠ (pi j).succ := fun he => (ne_of_lt hrow) (congrArg sigma he).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr ⟨a, hlt, hrow, hre, fun z => by rw [hre]; exact backElimination sigma pi a j hlt hrow z⟩
    · left
      intro z
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : b ≤ pi j
      · have hab : b.succ < a := (show b.succ ≤ (pi j).succ from by change b.val+1 ≤ (pi j).val+1; exact Nat.add_le_add_right hb 1).trans_lt hgt
        have hane : a ≠ b.succ := ne_of_gt hab
        have hanot : ¬a < b.succ := not_lt_of_ge hab.le
        have har : sigma.symm r = a := rfl
        simp [cellA, har, hane, hanot]
      · have hpb : pi j < b := lt_of_not_ge hb
        have hjne : j ≠ pi.symm b := fun he => (ne_of_lt hpb) (by simpa using congrArg pi he)
        simp [cellB, hjne, not_lt_of_ge hpb.le]
  have literalPivots (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) (j : Fin k) :
      (∑ b : Fin k, cellA sigma pi z (sigma (pi j).castSucc) b.castSucc *
        cellB sigma pi z b j) = 1 ∧
      (∑ b : Fin k, cellA sigma pi z (sigma (pi j).succ) b.succ *
        cellB sigma pi z b j) = 1 := by
    have rightZero (b : Fin k) (hb : pi j < b) : cellB sigma pi z b j = 0 := by
      have hn : j ≠ pi.symm b := fun h => (ne_of_lt hb) (by simpa using congrArg pi h)
      have hnb : ¬pi (pi.symm b) < pi j := by simpa using not_lt_of_ge hb.le
      simp [cellB, hn, not_lt_of_ge hb.le]
    constructor
    · rw [Finset.sum_eq_single (pi j)]
      · simp [cellA, cellB]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with hlt | hgt
        · have hne : (pi j).castSucc ≠ b.castSucc := by
            exact fun he => hb (Fin.castSucc_inj.mp he).symm
          have hnot : ¬(pi j).castSucc < b.castSucc := by simpa using not_lt_of_ge hlt.le
          simp [cellA, hne, hnot]
        · rw [rightZero b hgt, mul_zero]
      · simp
    · rw [Finset.sum_eq_single (pi j)]
      · simp [cellA, cellB]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with hlt | hgt
        · have hne : (pi j).succ ≠ b.succ := fun he => hb (Fin.succ_inj.mp he).symm
          have hnot : ¬(pi j).succ < b.succ := by simpa using not_lt_of_ge hlt.le
          simp [cellA, hne, hnot]
        · rw [rightZero b hgt, mul_zero]
      · simp
  have literalEligible (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : (LiteralSolutions (F := F) lam mu sigma pi)) :
      D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi := by
    intro j
    constructor
    · by_contra hn
      have hz := z.property.1 (sigma (pi j).castSucc) j (le_of_not_gt hn)
      rw [(literalPivots sigma pi z.val j).1] at hz
      exact one_ne_zero hz
    · by_contra hn
      have hz := z.property.2 (sigma (pi j).succ) j (le_of_not_gt hn)
      rw [(literalPivots sigma pi z.val j).2] at hz
      exact one_ne_zero hz
  have literalIneligibleCount (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (h : ¬D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi) :
      Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) = 0 := by
    letI : IsEmpty ((LiteralSolutions (F := F) lam mu sigma pi)) := ⟨fun z => h (literalEligible sigma pi z)⟩
    exact Nat.card_of_isEmpty
  let variableRank (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) : CellVariables sigma pi → ℕ :=
    Sum.elim (fun ab => rx ab.val.1.val ab.val.2.val)
      (fun ij => ry (pi ij.val.1).val (pi ij.val.2).val)
  have frontDependency (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) (i j : Fin k) (hji : j < i) (hpi : pi i < pi j)
      (z w : CellVariables sigma pi → F)
      (hw : ∀ v, variableRank sigma pi v ≤
        variableRank sigma pi (.inr ⟨(j,i),hji,hpi⟩) → z v = w v) :
      (∑ b : Fin k, cellA sigma pi z (sigma (pi i).castSucc) b.castSucc *
        cellB sigma pi z b j) =
      (∑ b : Fin k, cellA sigma pi w (sigma (pi i).castSucc) b.castSucc *
        cellB sigma pi w b j) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbp : b ≤ pi j
    · by_cases hab : pi i ≤ b
      · have hA : cellA sigma pi z (sigma (pi i).castSucc) b.castSucc =
            cellA sigma pi w (sigma (pi i).castSucc) b.castSucc := by
          simp only [cellA, Equiv.symm_apply_apply]
          split_ifs with he hh
          · rfl
          · apply hw
            change rx (pi i).val b.val ≤ ry (pi j).val (pi i).val
            have hm := Nat.mul_le_mul_left (2 * (k+1)) hbp
            have hi := (pi i).isLt
            dsimp [rx, ry]
            nlinarith
          · rfl
        have hB : cellB sigma pi z b j = cellB sigma pi w b j := by
          simp only [cellB]
          split_ifs with he hh
          · rfl
          · apply hw
            change ry (pi j).val (pi (pi.symm b)).val ≤ ry (pi j).val (pi i).val
            rw [pi.apply_symm_apply]
            by_cases hb : pi i = b
            · rw [hb]
            · exact (frontMiddleRank (pi j).val (pi i).val b.val
                (show (pi i).val < b.val from
                  lt_of_le_of_ne hab (fun he => hb (Fin.ext he))) b.isLt).le
          · rfl
        rw [hA, hB]
      · have hlt : b < pi i := lt_of_not_ge hab
        have hn : (pi i).castSucc ≠ b.castSucc := fun he =>
          (ne_of_gt hlt) (Fin.castSucc_inj.mp he)
        have hnot : ¬(pi i).castSucc < b.castSucc := not_lt_of_ge hlt.le
        simp [cellA, hn, hnot]
    · have hlt : pi j < b := lt_of_not_ge hbp
      have hn : j ≠ pi.symm b := fun he =>
        (ne_of_lt hlt) (by simpa using congrArg pi he)
      simp [cellB, hn, not_lt_of_ge hlt.le]
  have backDependency (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) (a : Fin (k+1)) (j : Fin k)
      (hap : a < (pi j).succ) (hrow : sigma (pi j).succ < sigma a)
      (z w : CellVariables sigma pi → F)
      (hw : ∀ v, variableRank sigma pi v ≤
        variableRank sigma pi (.inl ⟨(a,(pi j).succ),hap,hrow⟩) → z v = w v) :
      (∑ b : Fin k, cellA sigma pi z (sigma a) b.succ * cellB sigma pi z b j) =
      (∑ b : Fin k, cellA sigma pi w (sigma a) b.succ * cellB sigma pi w b j) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbp : b ≤ pi j
    · have hA : cellA sigma pi z (sigma a) b.succ =
          cellA sigma pi w (sigma a) b.succ := by
        simp only [cellA, Equiv.symm_apply_apply]
        split_ifs with he hh
        · rfl
        · apply hw
          change rx a.val (b.val+1) ≤ rx a.val ((pi j).val+1)
          have hm := Nat.mul_le_mul_left (2 * (k+1)) hbp
          dsimp [rx]
          nlinarith
        · rfl
      have hB : cellB sigma pi z b j = cellB sigma pi w b j := by
        simp only [cellB]
        split_ifs with he hh
        · rfl
        · apply hw
          change ry (pi j).val (pi (pi.symm b)).val ≤ rx a.val ((pi j).val+1)
          exact (backYRank (pi j).val (pi (pi.symm b)).val a.val).le
        · rfl
      rw [hA, hB]
    · have hlt : pi j < b := lt_of_not_ge hbp
      have hn : j ≠ pi.symm b := fun he =>
        (ne_of_lt hlt) (by simpa using congrArg pi he)
      simp [cellB, hn, not_lt_of_ge hlt.le]
  have laterUpdateAgrees (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) (z : CellVariables sigma pi → F)
      (pivot v : CellVariables sigma pi) (t : F)
      (hv : variableRank sigma pi pivot < variableRank sigma pi v) :
      ∀ u, variableRank sigma pi u ≤ variableRank sigma pi pivot →
        z u = Function.update z v t u := by
    intro u hu
    have hne : u ≠ v := by
      intro he
      rw [he] at hu
      omega
    simp [Function.update_of_ne hne]
  have frontLaterPreserved (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) (i j : Fin k) (hji : j < i) (hpi : pi i < pi j)
      (z : CellVariables sigma pi → F) (v : CellVariables sigma pi) (t : F)
      (hv : variableRank sigma pi (.inr ⟨(j,i),hji,hpi⟩) < variableRank sigma pi v) :
      (∑ b : Fin k, cellA sigma pi z (sigma (pi i).castSucc) b.castSucc * cellB sigma pi z b j) =
      (∑ b : Fin k, cellA sigma pi (Function.update z v t)
        (sigma (pi i).castSucc) b.castSucc * cellB sigma pi (Function.update z v t) b j) :=
    frontDependency sigma pi i j hji hpi z (Function.update z v t)
      (laterUpdateAgrees sigma pi z _ v t hv)
  have backLaterPreserved (sigma : Equiv.Perm (Fin (k+1)))
      (pi : Equiv.Perm (Fin k)) (a : Fin (k+1)) (j : Fin k)
      (hap : a < (pi j).succ) (hrow : sigma (pi j).succ < sigma a)
      (z : CellVariables sigma pi → F) (v : CellVariables sigma pi) (t : F)
      (hv : variableRank sigma pi (.inl ⟨(a,(pi j).succ),hap,hrow⟩) < variableRank sigma pi v) :
      (∑ b : Fin k, cellA sigma pi z (sigma a) b.succ * cellB sigma pi z b j) =
      (∑ b : Fin k, cellA sigma pi (Function.update z v t) (sigma a) b.succ *
        cellB sigma pi (Function.update z v t) b j) :=
    backDependency sigma pi a j hap hrow z (Function.update z v t)
      (laterUpdateAgrees sigma pi z _ v t hv)
  have variableRankInjective (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      Function.Injective (variableRank sigma pi) := by
    have enc (b a d c : ℕ) (ha : a < 2*(k+1)) (hc : c < 2*(k+1))
        (he : 2*(k+1)*b+a = 2*(k+1)*d+c) : b=d ∧ a=c := by
      have hd := congrArg (fun x : ℕ => x / (2*(k+1))) he
      have hm := congrArg (fun x : ℕ => x % (2*(k+1))) he
      simp only [Nat.mul_add_div (by omega : 0 < 2*(k+1)), Nat.div_eq_of_lt ha,
        Nat.div_eq_of_lt hc, Nat.add_zero] at hd
      simp only [Nat.mul_add_mod,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hc] at hm
      exact ⟨hd,hm⟩
    intro u v he
    cases u with
    | inl ab =>
      cases v with
      | inl cd =>
        have hh := enc ab.val.2.val ab.val.1.val cd.val.2.val cd.val.1.val
          (by have h := ab.val.1.isLt; omega) (by have h := cd.val.1.isLt; omega) he
        congr 1
        apply Subtype.ext
        exact Prod.ext (Fin.ext hh.2) (Fin.ext hh.1)
      | inr ij =>
        have hh := enc ab.val.2.val ab.val.1.val (pi ij.val.1).val
          ((k+1)+(k-1-(pi ij.val.2).val))
          (by have h := ab.val.1.isLt; omega) (by omega)
          (by simpa only [variableRank,rx,ry,Sum.elim_inl,Sum.elim_inr,Nat.add_assoc] using he)
        have h := ab.val.1.isLt
        omega
    | inr ij =>
      cases v with
      | inl ab =>
        have hh := enc ab.val.2.val ab.val.1.val (pi ij.val.1).val
          ((k+1)+(k-1-(pi ij.val.2).val))
          (by have h := ab.val.1.isLt; omega) (by omega)
          (by simpa only [variableRank,rx,ry,Sum.elim_inl,Sum.elim_inr,Nat.add_assoc] using he.symm)
        have h := ab.val.1.isLt
        omega
      | inr lm =>
        have hh := enc (pi ij.val.1).val ((k+1)+(k-1-(pi ij.val.2).val))
          (pi lm.val.1).val ((k+1)+(k-1-(pi lm.val.2).val)) (by omega) (by omega)
          (by simpa only [variableRank,rx,ry,Sum.elim_inl,Sum.elim_inr,Nat.add_assoc] using he)
        have h1 : ij.val.1 = lm.val.1 := pi.injective (Fin.ext hh.1)
        have h2 : ij.val.2 = lm.val.2 := by
          apply pi.injective
          apply Fin.ext
          have hi := (pi ij.val.2).isLt
          have hl := (pi lm.val.2).isLt
          omega
        congr 1
        apply Subtype.ext
        exact Prod.ext h1 h2
  have acyclicCompletionEquiv (V : Type) [DecidableEq V] (rank : V → ℕ)
      (active : V → Prop) (equation : V → (V → F) → Prop)
      (roots : ∀ v, active v → ∀ z, ∃! t : F, equation v (Function.update z v t))
      (stable : ∀ v z w, (∀ u, rank u < rank v → z u = w u) →
        ∀ t, equation v (Function.update z v t) ↔ equation v (Function.update w v t)) :
      {z : V → F // ∀ v, active v → equation v z} ≃ ({v : V // ¬active v} → F) := by
    let restriction : {z : V → F // ∀ v, active v → equation v z} →
        ({v : V // ¬active v} → F) := fun z v => z.val v.val
    have uniqueness (z w : {z : V → F // ∀ v, active v → equation v z})
        (hfree : restriction z = restriction w) : z = w := by
      apply Subtype.ext
      funext v
      induction v using (measure rank).wf.induction with
      | h v ih =>
        by_cases hv : active v
        · obtain ⟨t, ht, hu⟩ := roots v hv z.val
          have hz : equation v (Function.update z.val v (z.val v)) := by
            simpa using z.property v hv
          have hw : equation v (Function.update z.val v (w.val v)) := by
            apply (stable v z.val w.val (fun u h => ih u h) (w.val v)).mpr
            simpa using w.property v hv
          exact (hu _ hz).trans (hu _ hw).symm
        · exact congrFun hfree ⟨v,hv⟩
    have existence (free : {v : V // ¬active v} → F) :
        ∃ z : {z : V → F // ∀ v, active v → equation v z}, restriction z = free := by
      let step (v : V) (rec : ∀ u, rank u < rank v → F) : F :=
        if hv : active v then
          Classical.choose (roots v hv (fun u => if h : rank u < rank v then rec u h else 0))
        else free ⟨v,hv⟩
      let fill : V → F := (measure rank).wf.fix step
      have fill_eq (v : V) : fill v = step v (fun u _ => fill u) := by
        exact (measure rank).wf.fix_eq step v
      have satisfies (v : V) (hv : active v) : equation v fill := by
        let earlier : V → F := fun u => if rank u < rank v then fill u else 0
        have chosen : fill v = Classical.choose (roots v hv earlier) := by
          rw [fill_eq]
          simp only [step, dif_pos hv]
        have hroot : equation v (Function.update earlier v (fill v)) := by
          rw [chosen]
          exact (Classical.choose_spec (roots v hv earlier)).1
        have hsame : ∀ u, rank u < rank v → earlier u = fill u := by
          intro u hu
          simp [earlier,hu]
        have hh := (stable v earlier fill hsame (fill v)).mp hroot
        simpa using hh
      refine ⟨⟨fill,satisfies⟩, ?_⟩
      funext v
      change fill v.val = free v
      rw [fill_eq]
      simp only [step,dif_neg v.property]
    exact Equiv.ofBijective restriction ⟨uniqueness,existence⟩
  let backColumn (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (ab : XVariables sigma) : Fin k :=
    pi.symm ⟨ab.val.2.val-1, by
      have h := ab.property.1
      have h2 := ab.val.2.isLt
      omega⟩
  have backColumnSucc (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (ab : XVariables sigma) : (pi (backColumn sigma pi ab)).succ = ab.val.2 := by
    apply Fin.ext
    simp only [backColumn,pi.apply_symm_apply,Fin.val_succ]
    have h := ab.property.1
    omega
  let activeCoordinate (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      CellVariables sigma pi → Prop :=
    Sum.elim (fun ab => k+1-mu (backColumn sigma pi ab) ≤ (sigma ab.val.1).val)
      (fun ij => k+1-lam ij.val.1 ≤ (sigma (pi ij.val.2).castSucc).val)
  let coordinateEquation (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      CellVariables sigma pi → (CellVariables sigma pi → F) → Prop :=
    Sum.elim
      (fun ab z => (∑ b : Fin k, cellA sigma pi z (sigma ab.val.1) b.succ *
        cellB sigma pi z b (backColumn sigma pi ab)) = 0)
      (fun ij z => (∑ b : Fin k, cellA sigma pi z (sigma (pi ij.val.2).castSucc) b.castSucc *
        cellB sigma pi z b ij.val.1) = 0)
  have coordinateRoots (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (v : CellVariables sigma pi) (hv : activeCoordinate sigma pi v)
      (z : CellVariables sigma pi → F) :
      ∃! t : F, coordinateEquation sigma pi v (Function.update z v t) := by
    cases v with
    | inl ab =>
      let j := backColumn sigma pi ab
      have hc : (pi j).succ = ab.val.2 := backColumnSucc sigma pi ab
      have hap : ab.val.1 < (pi j).succ := hc.symm ▸ ab.property.1
      have hrow : sigma (pi j).succ < sigma ab.val.1 := hc.symm ▸ ab.property.2
      have hp : (Sum.inl ⟨(ab.val.1,(pi j).succ),hap,hrow⟩ : CellVariables sigma pi) = .inl ab := by
        congr 1
        apply Subtype.ext
        simp [hc]
      simpa only [coordinateEquation,Sum.elim_inl,hp] using
        backElimination sigma pi ab.val.1 j hap hrow z
    | inr ij =>
      exact frontElimination sigma pi ij.val.2 ij.val.1 ij.property.1 ij.property.2 z
  have coordinateStable (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (v : CellVariables sigma pi) (z w : CellVariables sigma pi → F)
      (hw : ∀ u, variableRank sigma pi u < variableRank sigma pi v → z u = w u)
      (t : F) :
      coordinateEquation sigma pi v (Function.update z v t) ↔
        coordinateEquation sigma pi v (Function.update w v t) := by
    have hagree : ∀ u, variableRank sigma pi u ≤ variableRank sigma pi v →
        Function.update z v t u = Function.update w v t u := by
      intro u hu
      by_cases he : u = v
      · subst u
        simp
      · rw [Function.update_of_ne he,Function.update_of_ne he]
        apply hw
        apply lt_of_le_of_ne hu
        intro heq
        exact he (variableRankInjective sigma pi heq)
    cases v with
    | inl ab =>
      let j := backColumn sigma pi ab
      have hc : (pi j).succ = ab.val.2 := backColumnSucc sigma pi ab
      have hap : ab.val.1 < (pi j).succ := hc.symm ▸ ab.property.1
      have hrow : sigma (pi j).succ < sigma ab.val.1 := hc.symm ▸ ab.property.2
      have hp : (Sum.inl ⟨(ab.val.1,(pi j).succ),hap,hrow⟩ : CellVariables sigma pi) = .inl ab := by
        congr 1
        apply Subtype.ext
        simp [hc]
      have he := backDependency sigma pi ab.val.1 j hap hrow
        (Function.update z (.inl ab) t) (Function.update w (.inl ab) t)
        (by simpa only [hp] using hagree)
      exact congrArg (fun x : F => x = 0) he |>.to_iff
    | inr ij =>
      have he := frontDependency sigma pi ij.val.2 ij.val.1 ij.property.1 ij.property.2
        (Function.update z (.inr ij) t) (Function.update w (.inr ij) t) hagree
      exact congrArg (fun x : F => x = 0) he |>.to_iff
  have activeEquationsIff (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi)
      (z : CellVariables sigma pi → F) :
      (∀ v, activeCoordinate sigma pi v → coordinateEquation sigma pi v z) ↔
      (∀ r j, k+1-lam j ≤ r.val →
        (∑ b : Fin k, cellA sigma pi z r b.castSucc * cellB sigma pi z b j) = 0) ∧
      (∀ r j, k+1-mu j ≤ r.val →
        (∑ b : Fin k, cellA sigma pi z r b.succ * cellB sigma pi z b j) = 0) := by
    constructor
    · intro hz
      constructor
      · intro r j hr
        rcases frontForbiddenElimination sigma pi hel r j hr with hzero | ⟨i,hji,hpi,hre,_⟩
        · exact hzero z
        · have he := hz (.inr ⟨(j,i),hji,hpi⟩) (by
            change k+1-lam j ≤ (sigma (pi i).castSucc).val
            simpa only [hre] using hr)
          simpa only [coordinateEquation,Sum.elim_inr,← hre] using he
      · intro r j hr
        rcases backForbiddenElimination sigma pi hel r j hr with hzero | ⟨a,hap,hrow,hre,_⟩
        · exact hzero z
        · let ab : XVariables sigma := ⟨(a,(pi j).succ),hap,hrow⟩
          have hj : backColumn sigma pi ab = j := by
            apply pi.injective
            apply Fin.succ_injective
            exact backColumnSucc sigma pi ab
          have he := hz (.inl ab) (by
            change k+1-mu (backColumn sigma pi ab) ≤ (sigma a).val
            simpa only [hj,hre] using hr)
          change (∑ b : Fin k, cellA sigma pi z (sigma a) b.succ *
            cellB sigma pi z b (backColumn sigma pi ab)) = 0 at he
          simpa only [hj,← hre] using he
    · intro hz v hv
      cases v with
      | inl ab => exact hz.2 (sigma ab.val.1) (backColumn sigma pi ab) hv
      | inr ij => exact hz.1 (sigma (pi ij.val.2).castSucc) ij.val.1 hv
  let literalFreeEquiv (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi) :
      (LiteralSolutions (F := F) lam mu sigma pi) ≃ ({v : CellVariables sigma pi // ¬activeCoordinate sigma pi v} → F) :=
    (Equiv.subtypeEquivRight (fun z => (activeEquationsIff sigma pi hel z).symm)).trans
      (acyclicCompletionEquiv (CellVariables sigma pi) (variableRank sigma pi)
        (activeCoordinate sigma pi) (coordinateEquation sigma pi)
        (coordinateRoots sigma pi) (coordinateStable sigma pi))
  have literalFreeCount (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (hel : D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi) :
      Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) = Fintype.card F ^
        Nat.card {v : CellVariables sigma pi // ¬activeCoordinate sigma pi v} := by
    rw [Nat.card_congr (literalFreeEquiv sigma pi hel),Nat.card_fun,Nat.card_eq_fintype_card]
  have literalCellCount (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) =
        if D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi
        then Fintype.card F ^
          (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
            (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi).toNat
        else 0 := by
    split_ifs with hel
    · rw [literalFreeCount sigma pi hel]
      congr 1
      have actual_coordinate_exponent {k : ℕ} (f g : Fin k → ℕ)
          (hf : Monotone f) (hg : Monotone g) (hfg : ∀ j, f j ≤ g j)
          (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
          (hel : Eligible f g sigma pi) :
          let bc (ab : XVariables sigma) : Fin k := pi.symm ⟨ab.val.2.val-1, by
            have h := ab.property.1
            have h2 := ab.val.2.isLt
            omega⟩
          let active : CellVariables sigma pi → Prop :=
            Sum.elim (fun ab => g (bc ab) ≤ (sigma ab.val.1).val)
              (fun ij => f ij.val.1 ≤ (sigma (pi ij.val.2).castSucc).val)
          Nat.card {v : CellVariables sigma pi // ¬active v} = (E f g sigma pi).toNat ∧
            0 ≤ E f g sigma pi := by
        classical
        dsimp only
        have inversion_pair_count {n : ℕ} (f : Fin n → ℕ) :
            inv (List.ofFn f) = ∑ a : Fin n, ∑ b : Fin n, if a < b ∧ f b < f a then 1 else 0 := by
          have countFn {m : ℕ} (w : Fin m → ℕ) (p : ℕ → Bool) :
              (List.ofFn w).countP p = ∑ i : Fin m, if p (w i) then 1 else 0 := by
            induction m with
            | zero => simp
            | succ m ih =>
              simp only [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
              omega
          induction n with
          | zero => simp [inv]
          | succ n ih =>
            rw [List.ofFn_succ, inv, ih, countFn]
            simp only [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, false_and,
              ite_false, Fin.succ_pos, true_and, Nat.add_zero, Nat.zero_add, decide_eq_true_eq]
            omega
        let Prefix {K : Nat} (σ : Equiv.Perm (Fin (K+1))) (r : Fin K) (T : Nat) : Finset (Fin (K+1)) :=
          Finset.univ.filter (fun u => u.val < r.val ∧ T ≤ (σ u).val)
        have pairCount {n : ℕ} (S : Equiv.Perm (Fin n)) :
            Nat.card {ab : Fin n × Fin n // ab.1 < ab.2 ∧ S ab.2 < S ab.1} = I S := by
          rw [I, inversion_pair_count]
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          exact Fintype.sum_prod_type _
        let bc (ab : XVariables sigma) : Fin k := pi.symm ⟨ab.val.2.val-1, by
          have h := ab.property.1
          have h2 := ab.val.2.isLt
          omega⟩
        have bcSucc (ab : XVariables sigma) : (pi (bc ab)).succ = ab.val.2 := by
          apply Fin.ext
          simp only [bc, pi.apply_symm_apply, Fin.val_succ]
          have h := ab.property.1
          omega
        let activeX (ab : XVariables sigma) := g (bc ab) ≤ (sigma ab.val.1).val
        let activeY (ij : YVariables pi) := f ij.val.1 ≤ (sigma (pi ij.val.2).castSucc).val
        let active : CellVariables sigma pi → Prop := Sum.elim activeX activeY
        have xCount : Nat.card {ab : XVariables sigma // activeX ab} =
            (ForbiddenCount f g sigma pi).2 := by
          let target := Σ j : Fin k, {a : Fin (k+1) // a ∈ Prefix sigma (pi j) (g j)}
          let toTarget : {ab : XVariables sigma // activeX ab} → target := fun ab =>
            ⟨bc ab.val, ab.val.val.1, by
              simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and]
              have hlt := ab.val.property.1
              have hs := congrArg Fin.val (bcSucc ab.val)
              have hf0 := (hel (bc ab.val)).1
              have hfg0 := hfg (bc ab.val)
              have ha := ab.property
              change g (bc ab.val) ≤ (sigma ab.val.val.1).val at ha
              constructor
              · by_contra hn
                have he : ab.val.val.1 = (pi (bc ab.val)).castSucc := by
                  apply Fin.ext
                  simp only [Fin.val_castSucc]
                  change ab.val.val.1.val < ab.val.val.2.val at hlt
                  simp only [Fin.val_succ] at hs
                  omega
                rw [he] at ha
                omega
              · exact ha⟩
          have hinj : Function.Injective toTarget := by
            intro a b he
            have hj : bc a.val = bc b.val := congrArg Sigma.fst he
            have ha : a.val.val.1 = b.val.val.1 := by
              exact congrArg (fun z : target => z.2.val) he
            apply Subtype.ext
            apply Subtype.ext
            apply Prod.ext ha
            rw [← bcSucc a.val, ← bcSucc b.val, hj]
          have hsurj : Function.Surjective toTarget := by
            rintro ⟨j,a,ha⟩
            simp only [Prefix, Finset.mem_filter, Finset.mem_univ, true_and] at ha
            have hap : a < (pi j).succ := by
              change a.val < (pi j).val+1
              omega
            have hrow : sigma (pi j).succ < sigma a := (hel j).2.trans_le ha.2
            let ab : XVariables sigma := ⟨(a,(pi j).succ),hap,hrow⟩
            have hj : bc ab = j := by
              apply pi.injective
              apply Fin.succ_injective
              exact bcSucc ab
            refine ⟨⟨ab, ?_⟩, ?_⟩
            · change g (bc ab) ≤ (sigma a).val
              simpa only [hj] using ha.2
            · dsimp only [toTarget]
              apply Sigma.ext hj
              apply (Subtype.heq_iff_coe_eq (by intro u; dsimp only; rw [hj])).mpr
              rfl
          rw [Nat.card_congr (Equiv.ofBijective toTarget ⟨hinj,hsurj⟩)]
          change Nat.card target = _
          simp only [target, Nat.card_eq_fintype_card, Fintype.card_sigma,
            Fintype.card_coe]
          change (∑ j, (Prefix sigma (pi j) (g j)).card) = ∑ j, (Back g sigma pi j).card
          apply Finset.sum_congr rfl
          intro j _
          exact (prefix_counts f g sigma pi hf hg hfg hel j).2.symm
        have yCount : Nat.card {ij : YVariables pi // activeY ij} =
            (ForbiddenCount f g sigma pi).1 := by
          let target := Σ j : Fin k, {i : Fin k // i ∈ Front f sigma pi j}
          let toTarget : {ij : YVariables pi // activeY ij} → target := fun ij =>
            ⟨ij.val.val.1, ij.val.val.2, by
              simp only [Front, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨ij.val.property.1, (hel ij.val.val.1).1.trans_le ij.property,
                ij.val.property.2, ij.property⟩⟩
          have hinj : Function.Injective toTarget := by
            intro a b he
            apply Subtype.ext
            apply Subtype.ext
            exact Prod.ext (congrArg Sigma.fst he) (congrArg (fun z : target => z.2.val) he)
          have hsurj : Function.Surjective toTarget := by
            rintro ⟨j,i,hi⟩
            simp only [Front, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact ⟨⟨⟨(j,i),hi.1,hi.2.2.1⟩,hi.2.2.2⟩,rfl⟩
          rw [Nat.card_congr (Equiv.ofBijective toTarget ⟨hinj,hsurj⟩)]
          simp only [target, Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_coe]
          rfl
        have activeCount : Nat.card {v : CellVariables sigma pi // active v} =
            (ForbiddenCount f g sigma pi).1 + (ForbiddenCount f g sigma pi).2 := by
          let e : {v : CellVariables sigma pi // active v} ≃
              {ab : XVariables sigma // activeX ab} ⊕ {ij : YVariables pi // activeY ij} :=
            { toFun := fun v => match v with
                | ⟨.inl ab,h⟩ => .inl ⟨ab,h⟩
                | ⟨.inr ij,h⟩ => .inr ⟨ij,h⟩
              invFun := fun v => match v with
                | .inl ⟨ab,h⟩ => ⟨.inl ab,h⟩
                | .inr ⟨ij,h⟩ => ⟨.inr ij,h⟩
              left_inv := by rintro ⟨v,h⟩; cases v <;> rfl
              right_inv := by intro v; cases v <;> rfl }
          rw [Nat.card_congr e, Nat.card_sum, xCount, yCount, Nat.add_comm]
        have totalCount : Nat.card (CellVariables sigma pi) = I sigma + I pi := by
          rw [Nat.card_sum, pairCount sigma, pairCount pi]
        have hle : Nat.card {v : CellVariables sigma pi // active v} ≤
            Nat.card (CellVariables sigma pi) := by
          simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le active
        have freeCount : Nat.card {v : CellVariables sigma pi // ¬active v} =
            Nat.card (CellVariables sigma pi) - Nat.card {v : CellVariables sigma pi // active v} := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
        rw [activeCount, totalCount] at freeCount hle
        have hE : E f g sigma pi =
            ((I sigma + I pi - ((ForbiddenCount f g sigma pi).1 +
              (ForbiddenCount f g sigma pi).2) : ℕ) : ℤ) := by
          unfold E
          omega
        constructor
        · change Nat.card {v : CellVariables sigma pi // ¬active v} = _
          rw [freeCount, hE, Int.toNat_natCast]
        · rw [hE]
          exact Int.natCast_nonneg _

      simpa only [activeCoordinate, backColumn] using
        (actual_coordinate_exponent (fun j => k+1-lam j) (fun j => k+1-mu j)
          (by intro a b hab; dsimp only; have h := hlam hab; omega)
          (by intro a b hab; dsimp only; have h := hmu hab; omega)
          (by intro j; have h := hml j; omega) sigma pi hel).1
    · exact literalIneligibleCount sigma pi hel
  exact literalCellCount


end D5.S3.Combinatorics.Hypermatrix.LiteralMaskedCellCount
