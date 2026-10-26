/- GID: D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCanonicalColumns
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed deletions in one actual axis have compatible overlapping choices. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreNormal

/-! Exact column deletion identities, including overlaps within one frozen run. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreContract MiuraCoreCellExpand
  MiuraCoreJoint MiuraCoreNormal MiuraSlabIncidence

variable {m n : ℕ}

private theorem contract_le (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (p : Cell m (n - 1))
    (hp : p.2.val ≤ j.val) :
    contractAt h hm j hj p = h (p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩) := by
  by_cases he : p.2.val < j.val
  · exact contractAt_left h hm j hj p he
  · have heq : p.2.val = j.val := by omega
    rw [contractAt_right h hm j hj p he]
    have hs := frozenSlope_eq_right h hh hm j hj p.1
    have e1 : (⟨p.2.val + 1, by have := p.2.isLt; omega⟩ : Fin n) =
        ⟨j.val + 1, hj.2.1⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    have e2 : (⟨p.2.val, by have := p.2.isLt; omega⟩ : Fin n) = j := Fin.ext heq
    rw [e1, e2]
    omega

private theorem contract_ge (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) (p : Cell m (n - 1))
    (hp : j.val - 1 ≤ p.2.val) :
    contractAt h hm j hj p =
      h (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩) - frozenSlope h hm j hj := by
  by_cases he : p.2.val < j.val
  · rw [contractAt_left h hm j hj p he]
    have hs := frozenSlope_eq h hh hm j hj p.1
    have e1 : (⟨p.2.val + 1, by have := p.2.isLt; omega⟩ : Fin n) = j :=
      Fin.ext (by have := hj.1; simp only [Fin.val_mk]; omega)
    have e2 : (⟨p.2.val, by have := p.2.isLt; omega⟩ : Fin n) =
        ⟨j.val - 1, by have := hj.1; have := j.isLt; omega⟩ :=
      Fin.ext (by have := hj.1; simp only [Fin.val_mk]; omega)
    rw [e1, e2]
    omega
  · exact contractAt_right h hm j hj p he

/-- Every other frozen column survives deletion, with its actual shifted index. -/
theorem frozen_after_left_deletion (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k) (hjk : j.val < k.val) :
    frozenColumn (contractAt h hm j hj) ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  have hj0 := hj.1
  have hk0 := hk.1
  have hk1 := hk.2.1
  refine ⟨by simp only [Fin.val_mk]; omega, by simp only [Fin.val_mk]; omega, ?_⟩
  intro i
  rw [contract_ge h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_ge h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_ge h hh hm j hj _ (by simp only [Fin.val_mk]; omega)]
  simp only [show k.val - 1 - 1 + 1 = k.val - 1 by omega,
    show k.val - 1 + 1 + 1 = k.val + 1 by omega,
    show k.val - 1 + 1 = k.val by omega]
  have hs := hk.2.2 i
  change _ = 2 * (h (i, k) - _)
  linarith

/-- A frozen column to the left keeps its original index. -/
theorem frozen_after_right_deletion (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k) (hkj : k.val < j.val) :
    frozenColumn (contractAt h hm j hj) ⟨k.val, by have := hj.2.1; omega⟩ := by
  have hk0 := hk.1
  have hk1 := hk.2.1
  refine ⟨hk0, by simp only [Fin.val_mk]; have := hj.2.1; omega, ?_⟩
  intro i
  rw [contract_le h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_le h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_le h hh hm j hj _ (by simp only [Fin.val_mk]; omega)]
  exact hk.2.2 i

private theorem slope_after_left (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k) (hjk : j.val < k.val) :
    frozenSlope (contractAt h hm j hj) hm ⟨k.val - 1, by have := k.isLt; omega⟩
      (frozen_after_left_deletion h hh hm j k hj hk hjk) = frozenSlope h hm k hk := by
  have hj0 := hj.1
  unfold frozenSlope
  rw [contract_ge h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_ge h hh hm j hj _ (by simp only [Fin.val_mk]; omega)]
  simp only [show k.val - 1 + 1 = k.val by omega,
    show k.val - 1 - 1 + 1 = k.val - 1 by omega]
  change (h (_, k) - _) - (h (_, _) - _) = _
  ring

private theorem slope_after_right (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k) (hkj : k.val < j.val) :
    frozenSlope (contractAt h hm j hj) hm ⟨k.val, by have := hj.2.1; omega⟩
      (frozen_after_right_deletion h hh hm j k hj hk hkj) = frozenSlope h hm k hk := by
  unfold frozenSlope
  rw [contract_le h hh hm j hj _ (by simp only [Fin.val_mk]; omega),
      contract_le h hh hm j hj _ (by simp only [Fin.val_mk]; omega)]

/-- Overlapping choices within a frozen run produce the same complete array. -/
theorem adjacent_deletions_equal (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k)
    (hjk : j.val + 1 = k.val) :
    contractAt h hm j hj = contractAt h hm k hk := by
  have hj0 := hj.1
  have hk0 := hk.1
  have hs : frozenSlope h hm j hj = frozenSlope h hm k hk := by
    have he := frozenSlope_eq_right h hh hm j hj ⟨0, hm⟩
    unfold frozenSlope at *
    have ek : (⟨j.val + 1, hj.2.1⟩ : Fin n) = k := Fin.ext hjk
    have ej : (⟨k.val - 1, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    rw [ek] at he
    rw [ej]
    omega
  funext p
  by_cases hp : p.2.val ≤ j.val
  · rw [contract_le h hh hm j hj p hp, contract_le h hh hm k hk p (by omega)]
  · rw [contract_ge h hh hm j hj p (by omega),
        contract_ge h hh hm k hk p (by omega), hs]

/-- Distinct signed deletions commute with their genuine shifted indices. -/
theorem separated_deletions_commute (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j k : Fin n) (hj : frozenColumn h j) (hk : frozenColumn h k) (hjk : j.val < k.val) :
    contractAt (contractAt h hm j hj) hm ⟨k.val - 1, by have := k.isLt; omega⟩
        (frozen_after_left_deletion h hh hm j k hj hk hjk) =
      contractAt (contractAt h hm k hk) hm ⟨j.val, by have := hk.2.1; omega⟩
        (frozen_after_right_deletion h hh hm k j hk hj hjk) := by
  have hj0 := hj.1
  have hk0 := hk.1
  funext p
  conv_lhs => rw [contractAt]
  conv_rhs => rw [contractAt]
  rw [slope_after_left h hh hm j k hj hk hjk,
      slope_after_right h hh hm k j hk hj hjk]
  simp only [contractAt]
  split_ifs <;> (try simp_all only [Fin.val_mk]) <;> try omega
  all_goals try { congr 2 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega }
  all_goals try ring

end D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
