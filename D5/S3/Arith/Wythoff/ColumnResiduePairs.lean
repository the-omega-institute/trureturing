/- GID: D5/S3/Arith/Wythoff/ColumnResiduePairs
   generality: I
   mirror-B: D5/B/S3/Arith/Wythoff/ColumnResiduePairs
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: The first two Wythoff columns attain all residue pairs modulo every positive integer. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Wythoff.ColumnResiduePairs

/-- The Wythoff array, with rows and columns numbered from one. Column zero
is the lower Wythoff sequence; columns one and two have Morrison's floor
definitions, and all later columns follow the Fibonacci recurrence. -/
noncomputable def W (n : ℕ) : ℕ → ℤ
  | 0 => ⌊(n : ℝ) * Real.goldenRatio⌋
  | 1 => ⌊(⌊(n : ℝ) * Real.goldenRatio⌋ : ℝ) * Real.goldenRatio⌋
  | 2 => ⌊(⌊(n : ℝ) * Real.goldenRatio⌋ : ℝ) * Real.goldenRatio ^ 2⌋
  | k + 3 => W n (k + 2) + W n (k + 1)

/-- Every pair occurs in the first two columns, and their residue image has
exactly `m²` elements. The modulus-one case is included. -/
theorem result (m : ℕ) (hm : 1 ≤ m) :
    ((Set.Ici 1).image (fun n : ℕ => ((W n 1 : ZMod m), (W n 2 : ZMod m)))).ncard =
      m ^ 2 ∧
    ∀ a b : ZMod m, ∃ n : ℕ, 1 ≤ n ∧ (W n 1 : ZMod m) = a ∧
      (W n 2 : ZMod m) = b := by
  classical
  have : NeZero m := ⟨by omega⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have : Fact (0 < (m : ℝ)) := ⟨hmR⟩
  have closed (n : ℕ) (hn : 1 ≤ n) :
      W n 1 = ⌊(n : ℝ) * Real.goldenRatio⌋ + n - 1 ∧
      W n 2 = 2 * ⌊(n : ℝ) * Real.goldenRatio⌋ + n - 1 := by
    let A : ℤ := ⌊(n : ℝ) * Real.goldenRatio⌋
    have hle : (A : ℝ) ≤ (n : ℝ) * Real.goldenRatio := Int.floor_le _
    have hlt : (A : ℝ) < (n : ℝ) * Real.goldenRatio :=
      lt_of_le_of_ne hle
        ((Real.goldenRatio_irrational.natCast_mul (by omega : n ≠ 0)).ne_int A).symm
    have hnext : (n : ℝ) * Real.goldenRatio < (A : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hphi := Real.goldenRatio_sq
    have hphi1 := Real.one_lt_goldenRatio
    have hphi2 := Real.goldenRatio_lt_two
    have heq : (A : ℝ) * Real.goldenRatio =
        (A : ℝ) + n - ((n : ℝ) * Real.goldenRatio - A) * (Real.goldenRatio - 1) := by
      nlinarith
    have hfloor : ⌊(A : ℝ) * Real.goldenRatio⌋ = A + n - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hphi1),
        mul_pos (sub_pos.mpr hnext) (sub_pos.mpr hphi1)]
    constructor
    · exact hfloor
    · change ⌊(A : ℝ) * Real.goldenRatio ^ 2⌋ = _
      rw [hphi, mul_add, mul_one, Int.floor_add_intCast, hfloor]
      dsimp [A]
      ring
  have hit : ∀ a b : ZMod m, ∃ n : ℕ, 1 ≤ n ∧ (W n 1 : ZMod m) = a ∧
      (W n 2 : ZMod m) = b := by
    intro a b
    let r : ℕ := (2 * a - b).val
    let s : ℕ := (b - a).val
    let c : ℕ := r + 1
    let α : AddCircle (m : ℝ) := ((m : ℝ) * Real.goldenRatio : ℝ)
    have hdZ : DenseRange (fun k : ℤ => k • α) := by
      apply AddCircle.denseRange_zsmul_coe_iff.mpr
      simpa [mul_div_cancel_left₀ _ hmR.ne'] using Real.goldenRatio_irrational
    have hdN : DenseRange (fun k : ℕ => k • α) :=
      denseRange_zsmul_iff_nsmul.mp hdZ
    let x : AddCircle (m : ℝ) := ((c : ℝ) * Real.goldenRatio : ℝ)
    have hd : DenseRange (fun k : ℕ => k • α + x) :=
      (Homeomorph.addRight x).surjective.denseRange.comp hdN
        (Homeomorph.addRight x).continuous
    have ho : IsOpen (((↑) : ℝ → AddCircle (m : ℝ)) '' Set.Ioo (s : ℝ) (s + 1)) :=
      QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    have hne : (((↑) : ℝ → AddCircle (m : ℝ)) '' Set.Ioo (s : ℝ) (s + 1)).Nonempty :=
      (Set.nonempty_Ioo.mpr (by linarith)).image _
    obtain ⟨k, y, hy, hky⟩ := hd.exists_mem_open ho hne
    let n : ℕ := c + m * k
    have hn : 1 ≤ n := by dsimp [n, c]; omega
    have hcoe : (((n : ℝ) * Real.goldenRatio - y : ℝ) : AddCircle (m : ℝ)) = 0 := by
      rw [AddCircle.coe_sub]
      have he : (((n : ℝ) * Real.goldenRatio : ℝ) : AddCircle (m : ℝ)) = k • α + x := by
        dsimp [n, α, x]
        push_cast
        rw [show ((c : ℝ) + (m : ℝ) * k) * Real.goldenRatio =
          (k : ℝ) * ((m : ℝ) * Real.goldenRatio) + (c : ℝ) * Real.goldenRatio by ring]
        rw [AddCircle.coe_add, ← nsmul_eq_mul, AddCircle.coe_nsmul]
      rw [he, hky, sub_self]
    obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff (m : ℝ)).mp hcoe
    have hfloor : ⌊(n : ℝ) * Real.goldenRatio⌋ = (s : ℤ) + q * m := by
      apply Int.floor_eq_iff.mpr
      push_cast
      simp only [zsmul_eq_mul] at hq
      constructor <;> linarith [hy.1, hy.2]
    have hres : (⌊(n : ℝ) * Real.goldenRatio⌋ : ZMod m) = b - a := by
      rw [hfloor]
      simp [s]
    have hnres : (n : ZMod m) = 2 * a - b + 1 := by
      simp [n, c, r]
    obtain ⟨h1, h2⟩ := closed n hn
    refine ⟨n, hn, ?_, ?_⟩
    · rw [h1]
      push_cast
      rw [hres, hnres]
      ring
    · rw [h2]
      push_cast
      rw [hres, hnres]
      ring
  refine ⟨?_, hit⟩
  have hall : (Set.Ici 1).image
      (fun n : ℕ => ((W n 1 : ZMod m), (W n 2 : ZMod m))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ⟨a, b⟩
    obtain ⟨n, hn, ha, hb⟩ := hit a b
    exact ⟨n, hn, Prod.ext ha hb⟩
  rw [hall, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod,
    ZMod.card, pow_two]

end D5.S3.Arith.Wythoff.ColumnResiduePairs
