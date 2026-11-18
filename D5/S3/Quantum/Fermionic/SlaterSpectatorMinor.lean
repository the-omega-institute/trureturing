/- GID: D5/S3/Quantum/Fermionic/SlaterSpectatorMinor
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterSpectatorMinor
   mirror-E: none(waiver:ordered-coordinate-cofactor)
   anchors: []
   utility: none
   digest: Ordered Slater minors with an appended coordinate orbital. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin

/-! # Ordered Slater minors with an appended orbital -/

namespace D5.S3.Quantum.Fermionic.SlaterSpectatorMinor

open Matrix Finset
open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- Append the coordinate column at the prescribed site. -/
def appendOrbital {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι) :
    Matrix ι (Fin (k + 1)) ℂ :=
  fun s => Fin.snoc (V s) (if s = p then 1 else 0)

private theorem minor_without_spectator {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι)
    (S : Finset ι) (hS : S.card = k + 1) (hp : p ∉ S) :
    ((appendOrbital V p).submatrix (S.orderEmbOfFin hS) id).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last k)
  intro i
  have hne : S.orderEmbOfFin hS i ≠ p := fun he =>
    hp (he ▸ S.orderEmbOfFin_mem hS i)
  simp [Matrix.submatrix_apply, appendOrbital, hne]

private theorem ordered_erase {k : ℕ} (S : Finset ι) (hS : S.card = k + 1)
    (j : Fin (k + 1)) {p : ι} (hj : S.orderEmbOfFin hS j = p)
    (hp : p ∈ S) :
    (fun i : Fin k => S.orderEmbOfFin hS (j.succAbove i)) =
      (S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    apply Finset.mem_erase.mpr
    refine ⟨fun he => ?_, S.orderEmbOfFin_mem hS _⟩
    apply Fin.succAbove_ne j i
    exact (S.orderEmbOfFin hS).injective (he.trans hj.symm)
  · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove j)

private theorem tail_card_of_rank {k : ℕ} (S : Finset ι) (hS : S.card = k + 1)
    (j : Fin (k + 1)) {p : ι} (hj : S.orderEmbOfFin hS j = p) :
    (S.filter (p < ·)).card = k - (j : ℕ) := by
  have he : (Finset.Ioi j).map (S.orderEmbOfFin hS).toEmbedding = S.filter (p < ·) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem hS i,
        hj ▸ (S.orderEmbOfFin hS).strictMono (Finset.mem_Ioi.mp hi)⟩
    · intro hz
      obtain ⟨hs, hlt⟩ := Finset.mem_filter.mp hz
      let i := (S.orderIsoOfFin hS).symm ⟨z, hs⟩
      have hi : S.orderEmbOfFin hS i = z :=
        congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨z, hs⟩)
      refine Finset.mem_map.mpr ⟨i, Finset.mem_Ioi.mpr ?_, hi⟩
      apply (S.orderEmbOfFin hS).strictMono.lt_iff_lt.mp
      simpa only [hj, hi] using hlt
  rw [← he, Finset.card_map, Fin.card_Ioi]
  omega

private theorem minor_with_spectator {k : ℕ} (V : Matrix ι (Fin k) ℂ) (p : ι)
    (S : Finset ι) (hS : S.card = k + 1) (hp : p ∈ S) :
    ((appendOrbital V p).submatrix (S.orderEmbOfFin hS) id).det =
      (-1 : ℂ) ^ (S.filter (p < ·)).card *
        (V.submatrix ((S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp)) id).det := by
  classical
  let j := (S.orderIsoOfFin hS).symm ⟨p, hp⟩
  have hj : S.orderEmbOfFin hS j = p :=
    congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨p, hp⟩)
  let A := (appendOrbital V p).submatrix (S.orderEmbOfFin hS) id
  have hcol (i : Fin (k + 1)) : A i (Fin.last k) = if i = j then 1 else 0 := by
    change (appendOrbital V p) (S.orderEmbOfFin hS i) (Fin.last k) = _
    simp [appendOrbital, ← hj, (S.orderEmbOfFin hS).injective.eq_iff]
  have hminor : A.submatrix j.succAbove (Fin.last k).succAbove =
      V.submatrix ((S.erase p).orderEmbOfFin (by rw [Finset.card_erase_of_mem hp, hS]; simp)) id := by
    ext i l : 1
    have he := congrFun (ordered_erase S hS j hj hp) i
    simp only [A, Matrix.submatrix_apply, id_eq, Fin.succAbove_last, appendOrbital, Fin.snoc_castSucc]
    rw [he]
  change A.det = _
  rw [Matrix.det_succ_column A (Fin.last k)]
  simp_rw [hcol]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, mul_one, hminor, tail_card_of_rank S hS j hj]
    have he : (j : ℕ) + (Fin.last k : ℕ) = (k - (j : ℕ)) + 2 * (j : ℕ) := by
      simp only [Fin.val_last]
      have hjk := j.isLt
      omega
    rw [he, pow_add]
    simp [pow_mul]
  · intro i _ hne
    simp [hne]
  · simp

/-- The increasingly ordered occupied minor, with zero amplitude outside
the particle-number sector. -/
noncomputable def occupiedMinor {k : ℕ} (V : Matrix ι (Fin k) ℂ) (S : Finset ι) : ℂ :=
  if h : S.card = k then (V.submatrix (S.orderEmbOfFin h) id).det else 0

/-- The added coordinate must be occupied. Its cofactor sign is determined by the
number of occupied sites that follow it in the ambient site order. -/
theorem occupiedMinor_append {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (p : ι) (S : Finset ι) :
    occupiedMinor (appendOrbital V p) S =
      if p ∈ S then (-1 : ℂ) ^ (S.filter (p < ·)).card * occupiedMinor V (S.erase p) else 0 := by
  classical
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp]
    by_cases hS : S.card = k + 1
    · have hErase : (S.erase p).card = k := by
        rw [Finset.card_erase_of_mem hp, hS]
        omega
      simp only [occupiedMinor, dite_eq_left hS, dite_eq_left hErase]
      exact minor_with_spectator V p S hS hp
    · have hErase : (S.erase p).card ≠ k := by
        rw [Finset.card_erase_of_mem hp]
        have hpos := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      simp [occupiedMinor, hS, hErase]
  · rw [ite_eq_right hp]
    by_cases hS : S.card = k + 1
    · simpa [occupiedMinor, hS] using minor_without_spectator V p S hS hp
    · simp [occupiedMinor, hS]

end D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
