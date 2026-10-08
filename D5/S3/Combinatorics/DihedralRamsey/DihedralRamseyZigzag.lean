/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyZigzag
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyZigzag
   mirror-E: none(waiver:finite-cyclic-order)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Cyclically increasing selections give dihedral graph embeddings. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyDefs
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs

/-- Rotate a sequence increasing from a cyclic cut into the ambient increasing order. -/
theorem cyclic_selection {k n : ℕ} (f : Fin (k + 1) → Fin n)
    (hc : StrictMono fun i => ((f i) - (f 0)).val) :
    ∃ (s : ℕ) (ψ : Fin (k + 1) → Fin n), StrictMono ψ ∧
      ∀ i, f i = ψ (dihedralPerm s false i) := by
  classical
  have hdist (x y : Fin n) : (y - x).val =
      if x.val ≤ y.val then y.val - x.val else n + y.val - x.val := by
    split_ifs with hxy
    · exact Fin.sub_val_of_le hxy
    · exact Fin.coe_sub_iff_lt.mpr (by omega)
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ f (by simp)
  have ht' : ∀ i, (f t).val ≤ (f i).val := fun i => ht i (by simp)
  have hordered : ∀ i j : Fin (k + 1), i < j →
      (f 0).val ≤ (f i).val → (f 0).val ≤ (f j).val → (f i).val < (f j).val := by
    intro i j hij hi hj
    have hh := hc hij
    simp only [hdist, if_pos hi, if_pos hj] at hh
    omega
  have hwrapped : ∀ i j : Fin (k + 1), i < j →
      (f i).val < (f 0).val → (f j).val < (f 0).val → (f i).val < (f j).val := by
    intro i j hij hi hj
    have hh := hc hij
    simp only [hdist, if_neg (by omega : ¬ (f 0).val ≤ (f i).val),
      if_neg (by omega : ¬ (f 0).val ≤ (f j).val)] at hh
    omega
  have hno_back : ∀ i j : Fin (k + 1), i < j →
      (f i).val < (f 0).val → (f j).val < (f 0).val := by
    intro i j hij hi
    have hh := hc hij
    have hn := (f j).isLt
    have hn' := (f i).isLt
    simp only [hdist] at hh
    split_ifs at hh <;> omega
  have hbefore : ∀ i : Fin (k + 1), i < t → (f 0).val ≤ (f i).val := by
    intro i hi
    by_contra hn
    have hti := ht' i
    by_cases ht0 : (f t).val < (f 0).val
    · have hh := hwrapped i t hi (by omega) ht0
      omega
    · omega
  have hafter : ∀ i : Fin (k + 1), t ≤ i →
      t ≠ 0 → (f i).val < (f 0).val := by
    intro i hi ht0
    have hti := ht' 0
    have hft : (f t).val < (f 0).val := by
      have hne : f t ≠ f 0 := by
        intro he
        apply ht0
        apply hc.injective
        change ((f t) - (f 0)).val = ((f 0) - (f 0)).val
        rw [he]
      have hne' : (f t).val ≠ (f 0).val := fun h => hne (Fin.ext h)
      omega
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hft
    · exact hno_back t i hlt hft
  have hmod (x : ℕ) (hx : k + 1 ≤ x) (hx' : x < 2 * (k + 1)) :
      x % (k + 1) = x - (k + 1) := by
    rw [Nat.mod_eq_sub_mod hx, Nat.mod_eq_of_lt (by omega)]
  let ψ : Fin (k + 1) → Fin n := fun i =>
    f ⟨(i.val + t.val) % (k + 1), Nat.mod_lt _ (by omega)⟩
  have hψ : StrictMono ψ := by
    intro i j hij
    have hin := i.isLt
    have hjn := j.isLt
    have htn := t.isLt
    have hmodi := Nat.mod_add_div (i.val + t.val) (k + 1)
    have hmodj := Nat.mod_add_div (j.val + t.val) (k + 1)
    by_cases hit : i.val + t.val < k + 1
    · by_cases hjt : j.val + t.val < k + 1
      · have hie : (i.val + t.val) % (k + 1) = i.val + t.val :=
          Nat.mod_eq_of_lt hit
        have hje : (j.val + t.val) % (k + 1) = j.val + t.val :=
          Nat.mod_eq_of_lt hjt
        have hp : (⟨(i.val + t.val) % (k + 1), Nat.mod_lt _ (by omega)⟩ :
            Fin (k + 1)) < ⟨(j.val + t.val) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
          simp only [Fin.lt_def, hie, hje]
          exact Nat.add_lt_add_right hij t.val
        change (f _).val < (f _).val
        by_cases ht0 : t = 0
        · apply hordered _ _ hp
          · simpa [ht0] using ht' _
          · simpa [ht0] using ht' _
        · apply hwrapped _ _ hp
          · apply hafter _ (by simp only [Fin.le_def, hie]; omega) ht0
          · apply hafter _ (by simp only [Fin.le_def, hje]; omega) ht0
      · have hje : (j.val + t.val) % (k + 1) = j.val + t.val - (k + 1) :=
          hmod _ (by omega) (by omega)
        have ht0 : t ≠ 0 := by intro h; subst t; simp at hjt
        have ha := hafter
          ⟨(i.val + t.val) % (k + 1), Nat.mod_lt _ (by omega)⟩
          (by simp only [Fin.le_def, Nat.mod_eq_of_lt hit]; omega) ht0
        have hb := hbefore
          ⟨(j.val + t.val) % (k + 1), Nat.mod_lt _ (by omega)⟩
          (by simp only [Fin.lt_def, hje]; omega)
        change (f _).val < (f _).val
        omega
    · have hjt : ¬ j.val + t.val < k + 1 := by omega
      have hie : (i.val + t.val) % (k + 1) = i.val + t.val - (k + 1) := hmod _ (by omega) (by omega)
      have hje : (j.val + t.val) % (k + 1) = j.val + t.val - (k + 1) := hmod _ (by omega) (by omega)
      apply hordered
      · simp only [Fin.lt_def, hie, hje]
        omega
      · apply hbefore _
        simp only [Fin.lt_def, hie]
        omega
      · apply hbefore _
        simp only [Fin.lt_def, hje]
        omega
  refine ⟨k + 1 - t.val, ψ, hψ, ?_⟩
  intro i
  congr 1
  apply Fin.ext
  dsimp [ψ, dihedralPerm]
  rw [Nat.mod_add_mod]
  have he : i.val + (k + 1 - t.val) + t.val = i.val + (k + 1) := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

end D5.S3.Combinatorics.DihedralRamsey
