import D5.S0.Certificates.BoxCover.CheckedRationalBoxCover
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumPermutation
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumRationalCorner
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumThermalInterpolation

/-! Closed rational bisection certificates for the low-spectrum Wu cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover

open _root_.Matrix
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicCornerInterpolation (boxCorner)
open WuCubicLowSpectrumPermutation (exists_sorted_normalizedDeficit)
open WuCubicLowSpectrumRationalCorner (cornerCheck cornerCheck_sound lowerCoeffRat upperCoeffRat)
open WuCubicLowSpectrumThermalInterpolation (normalizedDeficit_box_floor)
open private region leftBox rightBox split_retains from
  D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

/-- The coordinates are `(r, m, n, q)`, with the fourth spectral level fixed at one. -/
abbrev Box := Fin 4 → ℚ × ℚ

abbrev InBox (box : Box) (x : Fin 4 → ℝ) : Prop := x ∈ region box

private def corner (box : Box) (ε : Fin 4 → Bool) (i : Fin 4) : ℚ :=
  if ε i then (box i).2 else (box i).1

private def levels (y : Fin 4 → ℚ) (i : Fin 3) : ℚ := y i.succ

private def sortingPerm (f : Fin 3 → ℚ) : Equiv.Perm (Fin 3) :=
  if f 0 ≤ f 1 then
    if f 1 ≤ f 2 then Equiv.refl _
    else if f 0 ≤ f 2 then Equiv.swap 1 2
    else (Equiv.swap 1 2).trans (Equiv.swap 0 2)
  else
    if f 0 ≤ f 2 then Equiv.swap 0 1
    else if f 1 ≤ f 2 then (Equiv.swap 0 1).trans (Equiv.swap 0 2)
    else Equiv.swap 0 2

private theorem sortingPerm_monotone (f : Fin 3 → ℚ) : Monotone (f ∘ sortingPerm f) := by
  let z := f ∘ sortingPerm f
  suffices h : z 0 ≤ z 1 ∧ z 1 ≤ z 2 by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  dsimp only [z, Function.comp_apply, sortingPerm]
  split_ifs with h01 h12 h02 h02 h12
  · exact ⟨h01, h12⟩
  · exact ⟨h02, le_of_not_ge h12⟩
  · exact ⟨le_of_not_ge h02, h01⟩
  · exact ⟨le_of_not_ge h01, h02⟩
  · exact ⟨h12, le_of_not_ge h02⟩
  · exact ⟨le_of_not_ge h12, le_of_not_ge h01⟩

private def sortedLevels (y : Fin 4 → ℚ) : Fin 3 → ℚ := levels y ∘ sortingPerm (levels y)

private def interpolationLoss (box : Box) : ℚ :=
  let width := fun i => (box i).2 - (box i).1
  10 * (width 0)^2 + 3 * (∑ i : Fin 3, (width i.succ)^2)

/-- The two mixture weights and two endpoint charges for a sorted corner. -/
structure CornerWitness where
  L : ℚ
  R : ℚ
  μ₀ : ℚ
  μ₂ : ℚ

/-- The witness is indexed by a corner mask, where `true` selects the upper endpoint.
Every sorted corner must pay the requested floor plus the interpolation loss. -/
def checkCell (box : Box) (floor : ℚ) (witness : (Fin 4 → Bool) → CornerWitness) : Bool :=
  decide (1 ≤ (box 0).1 ∧ (box 0).2 ≤ 6 / 5 ∧
    (∀ i : Fin 3, 0 ≤ (box i.succ).1 ∧ (box i.succ).2 ≤ 1) ∧
    ∀ ε, let y := corner box ε
         let z := sortedLevels y
         let w := witness ε
         cornerCheck (y 0) (z 0) (z 1) (z 2) w.L w.R w.μ₀ w.μ₂
           (floor + interpolationLoss box) = true)

private theorem sortedLevels_cast (y : Fin 4 → ℚ) :
    (fun i => (sortedLevels y i : ℝ)) =
      (fun i => (levels y i : ℝ)) ∘ Tuple.sort (fun i => (levels y i : ℝ)) := by
  apply (Tuple.comp_sort_eq_comp_iff_monotone
    (f := fun i => (levels y i : ℝ)) (σ := sortingPerm (levels y))).mpr
  intro i j hij
  exact Rat.cast_le.mpr (sortingPerm_monotone (levels y) hij)

theorem checkCell_sound (U : unitary Mat) {box : Box} {floor : ℚ}
    {witness : (Fin 4 → Bool) → CornerWitness} (h : checkCell box floor witness = true)
    {x : Fin 4 → ℝ} (hx : InBox box x) :
    (floor : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) := by
  unfold checkCell at h
  obtain ⟨hrlo, hrhi, hlevels, hcorners⟩ := of_decide_eq_true h
  have hrlo' : (1 : ℝ) ≤ (box 0).1 := by exact_mod_cast hrlo
  have hrhi' : ((box 0).2 : ℝ) ≤ 6 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le.mpr hrhi :
      ((box 0).2 : ℝ) ≤ ((6 / 5 : ℚ) : ℝ))
  have hloLevel (i : Fin 3) : (0 : ℝ) ≤ (box i.succ).1 := by exact_mod_cast (hlevels i).1
  have hhiLevel (i : Fin 3) : ((box i.succ).2 : ℝ) ≤ 1 := by exact_mod_cast (hlevels i).2
  let axis : Sum Unit (Fin 3) → Fin 4 := Sum.elim (fun _ => 0) Fin.succ
  let lo := fun i => ((box (axis i)).1 : ℝ)
  let hi := fun i => ((box (axis i)).2 : ℝ)
  refine normalizedDeficit_box_floor U (lo := lo) (hi := hi) (x := x ∘ axis)
    hrlo' hrhi' hloLevel hhiLevel (fun i => hx (axis i)) ?_
  intro ε
  let mask : Fin 4 → Bool := fun i => Fin.cases (ε (.inl ())) (fun j => ε (.inr j)) i
  let y := corner box mask
  have hy (i : Sum Unit (Fin 3)) : boxCorner lo hi ε i = (y (axis i) : ℝ) := by
    suffices hmask : mask (axis i) = ε i by
      cases he : ε i <;> simp [boxCorner, lo, hi, y, corner, hmask, he]
    rcases i with ⟨⟨⟩⟩ | i <;> rfl
  have hr : 1 ≤ (y 0 : ℝ) := by
    have hspan := (hx 0).1.trans (hx 0).2
    cases hm : mask 0 <;> simp [y, corner, hm, hrlo', hrlo'.trans hspan]
  have hbounds (i : Fin 3) : (levels y i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    have hspan := (hx i.succ).1.trans (hx i.succ).2
    cases hm : mask i.succ <;> simp [levels, y, corner, hm, hloLevel i, hhiLevel i,
      (hloLevel i).trans hspan, hspan.trans (hhiLevel i)]
  obtain ⟨σ, _, _, _, _, _, _, hperm⟩ := exists_sorted_normalizedDeficit U _ hbounds
  have hc := cornerCheck_sound (WuCubicLowSpectrumPermutation.permuteColumns U σ) (hcorners mask)
  change ((floor + interpolationLoss box : ℚ) : ℝ) <
    normalizedDeficit (y 0) _ (sortedLevels y 0) (sortedLevels y 1) (sortedLevels y 2) at hc
  have hcast (i : Fin 3) := congrFun (sortedLevels_cast y) i
  rw [hcast 0, hcast 1, hcast 2, hperm _ hr] at hc
  simp only [hy]
  simpa only [interpolationLoss, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_sum, Rat.cast_ofNat, levels, axis, Sum.elim_inl, Sum.elim_inr, lo, hi, add_assoc]
    using hc.le

/-- A strict coordinate gap separates the closed box from `m ≤ n ≤ q`. -/
def checkPrune (box : Box) : Bool :=
  decide ((box 2).2 < (box 1).1 ∨ (box 3).2 < (box 2).1 ∨ (box 3).2 < (box 1).1)

private theorem checkPrune_sound {box : Box} (h : checkPrune box = true)
    {x : Fin 4 → ℝ} (hx : InBox box x) (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) : False := by
  unfold checkPrune at h
  rcases of_decide_eq_true h with h | h | h
  · exact not_lt_of_ge ((hx 1).1.trans (hmn.trans (hx 2).2)) (Rat.cast_lt.mpr h)
  · exact not_lt_of_ge ((hx 2).1.trans (hnq.trans (hx 3).2)) (Rat.cast_lt.mpr h)
  · exact not_lt_of_ge ((hx 1).1.trans ((hmn.trans hnq).trans (hx 3).2)) (Rat.cast_lt.mpr h)

inductive Tree where
  | leaf (witness : (Fin 4 → Bool) → CornerWitness)
  | prune
  | split (axis : Fin 4) (left right : Tree)

private def midpoint (box : Box) (axis : Fin 4) : ℚ := ((box axis).1 + (box axis).2) / 2

/-- Both children are checked on closed half-boxes defined by the exact rational midpoint. -/
def Tree.check (floor : ℚ) : Tree → Box → Bool
  | .leaf witness, box => checkCell box floor witness
  | .prune, box => checkPrune box
  | .split axis left right, box =>
      let cut := midpoint box axis
      left.check floor (leftBox box axis cut) && right.check floor (rightBox box axis cut)

theorem Tree.check_sound (U : unitary Mat) (tree : Tree) {box : Box} {floor : ℚ}
    (h : tree.check floor box = true) {x : Fin 4 → ℝ} (hx : InBox box x)
    (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) :
    (floor : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) := by
  induction tree generalizing box with
  | leaf witness => exact checkCell_sound U h hx
  | prune => exact (checkPrune_sound h hx hmn hnq).elim
  | split axis left right ihLeft ihRight =>
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      rcases split_retains box axis (midpoint box axis) hx with hxLeft | hxRight
      · exact ihLeft hl hxLeft
      · exact ihRight hr hxRight

/-- The starting box for the ordered low-spectrum domain. -/
def root : Box := ![(1, 6 / 5), (0, 63 / 100), (0, 1), (0, 1)]

theorem Tree.root_sound (U : unitary Mat) (tree : Tree) {floor : ℚ}
    (h : tree.check floor root = true) {r m n q : ℝ}
    (hr : r ∈ Set.Icc (1 : ℝ) (6 / 5)) (hm : m ∈ Set.Icc (0 : ℝ) (63 / 100))
    (hmn : m ≤ n) (hnq : n ≤ q) (hq : q ≤ 1) :
    (floor : ℝ) ≤ normalizedDeficit r U m n q := by
  refine tree.check_sound U h (x := ![r, m, n, q]) (fun i => ?_) hmn hnq
  have hn : n ∈ Set.Icc (0 : ℝ) 1 := ⟨hm.1.trans hmn, hnq.trans hq⟩
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hn.1.trans hnq, hq⟩
  fin_cases i <;> norm_num [root, InBox, region] <;> assumption

/-- A test box whose lower `n` half is strictly separated and whose upper half
has corners on both sides of `m = n`. -/
def firstBox : Box := ![(1, 101 / 100), (49 / 100, 1 / 2), (47 / 100, 1 / 2),
  (69 / 100, 7 / 10)]

def firstTree : Tree :=
  .split 2 .prune (.leaf fun ε =>
    let y := corner (rightBox firstBox 2 (midpoint firstBox 2)) ε
    let z := sortedLevels y
    ⟨lowerCoeffRat (y 0) (z 0) (z 1) (z 2) / 2,
      upperCoeffRat (y 0) (z 1) (z 2) / 2, 0, 0⟩)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem firstTree_accepted : firstTree.check (1 / 20) firstBox = true := by
  simp only [firstTree, Tree.check, Bool.and_eq_true_iff]
  refine ⟨by decide +kernel, ?_⟩
  unfold checkCell
  apply decide_eq_true
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · intro ε
    have he : ε = ![ε 0, ε 1, ε 2, ε 3] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    generalize ε 0 = a, ε 1 = b, ε 2 = c, ε 3 = d
    cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

theorem firstTree_sound (U : unitary Mat) {x : Fin 4 → ℝ} (hx : InBox firstBox x)
    (hmn : x 1 ≤ x 2) (hnq : x 2 ≤ x 3) :
    (1 / 20 : ℝ) ≤ normalizedDeficit (x 0) U (x 1) (x 2) (x 3) := by
  simpa using firstTree.check_sound U firstTree_accepted hx hmn hnq

#print axioms checkCell_sound
#print axioms Tree.root_sound
#print axioms firstTree_accepted
#print axioms firstTree_sound

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
