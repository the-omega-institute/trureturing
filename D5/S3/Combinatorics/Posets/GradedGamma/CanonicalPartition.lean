/- GID: D5/S3/Combinatorics/Posets/GradedGamma/CanonicalPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/CanonicalPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Grade]
   utility: none
   digest: Rank-parity relabelling translates every bounded graded-poset partition. -/

import D5.S3.Combinatorics.Posets.PPartitions.Series
import Mathlib.Order.Grade
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Minimal
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

def parityLabel {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (ω : α → ℕ) (x : α) : ℕ :=
  if grade ℕ x % 2 = 0 then ω x else Fintype.card α + ω x

private theorem parityLabel_injective {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (ω : α → ℕ) (hω : Function.Injective ω)
    (hbound : ∀ x, ω x < Fintype.card α) :
    Function.Injective (parityLabel ω) := by
  intro x y heq
  by_cases hx : grade ℕ x % 2 = 0 <;>
    by_cases hy : grade ℕ y % 2 = 0
  · exact hω (by simpa [parityLabel, hx, hy] using heq)
  · simp only [parityLabel, if_pos hx, if_neg hy] at heq
    have := hbound x
    omega
  · simp only [parityLabel, if_neg hx, if_pos hy] at heq
    have := hbound y
    omega
  · exact hω (by simpa [parityLabel, hx, hy] using heq)

private theorem parityLabel_covBy_descends {α : Type*} [Fintype α]
    [PartialOrder α] [GradeOrder ℕ α] (ω : α → ℕ)
    (hbound : ∀ x, ω x < Fintype.card α)
    {x y : α} (hxy : x ⋖ y) :
    (parityLabel ω y < parityLabel ω x) ↔ grade ℕ x % 2 = 1 := by
  have hg : grade ℕ y = grade ℕ x + 1 :=
    (Nat.covBy_iff_add_one_eq.mp (hxy.grade ℕ)).symm
  have hx : grade ℕ x % 2 = 0 ∨ grade ℕ x % 2 = 1 := by omega
  rcases hx with hx | hx
  · have hy : grade ℕ y % 2 ≠ 0 := by omega
    simp only [parityLabel, if_pos hx, if_neg hy]
    constructor
    · intro h
      have hb := hbound x
      omega
    · intro h
      omega
  · have hnx : grade ℕ x % 2 ≠ 0 := by omega
    have hy : grade ℕ y % 2 = 0 := by omega
    simp only [parityLabel, if_neg hnx, if_pos hy]
    constructor
    · intro _
      exact hx
    · intro _
      have hb := hbound y
      omega

private def parityShift {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (a : ℕ) (x : α) : ℕ :=
  a - 1 - grade ℕ x / 2

private def toParityPartition {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (a q : ℕ) (ha : 0 < a)
    (hgrade : ∀ x : α, grade ℕ x ≤ 2 * a - 1)
    (ω : α → ℕ) (hω : StrictMono ω)
    (hbound : ∀ x, ω x < Fintype.card α)
    (p : PPartition ω (q + 1)) :
    PPartition (parityLabel ω) (q + a) := by
  refine ⟨fun x => ⟨(p.1 x).val + parityShift a x, by
    have hp := (p.1 x).isLt
    have hg := hgrade x
    dsimp [parityShift]
    omega⟩, ?_, ?_⟩
  · intro x y hxy
    apply Fin.mk_le_mk.mpr
    have hp := p.2.1 hxy
    have hg := grade_mono (𝕆 := ℕ) hxy
    dsimp [parityShift]
    have hbx := hgrade x
    have hby := hgrade y
    omega
  · intro x y hxy hlabel
    apply Fin.mk_lt_mk.mpr
    have hp := p.2.1 hxy.le
    have hg := grade_strictMono (𝕆 := ℕ) hxy
    have hnat := hω hxy
    have hbx := hgrade x
    have hby := hgrade y
    have hodd : grade ℕ x % 2 = 1 ∧ grade ℕ y % 2 = 0 := by
      have hx : grade ℕ x % 2 = 0 ∨ grade ℕ x % 2 = 1 := by omega
      have hy : grade ℕ y % 2 = 0 ∨ grade ℕ y % 2 = 1 := by omega
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · have : ω y < ω x := by simpa [parityLabel, hx, hy] using hlabel
        omega
      · have hb := hbound x
        simp only [parityLabel, if_pos hx, if_neg (by omega : grade ℕ y % 2 ≠ 0)] at hlabel
        omega
      · exact ⟨hx, hy⟩
      · have : ω y < ω x := by simpa [parityLabel, hx, hy] using hlabel
        omega
    dsimp [parityShift]
    omega

private theorem parityPartition_lower {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (a bound : ℕ)
    (hmax : ∀ x : α, IsMax x → grade ℕ x = 2 * a - 1)
    (ω : α → ℕ)
    (hbound : ∀ x, ω x < Fintype.card α)
    (s : PPartition (parityLabel ω) bound) :
    ∀ x : α, parityShift a x ≤ (s.1 x).val := by
  intro x
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    by_cases hmaxx : IsMax x
    · have hg := hmax x hmaxx
      dsimp [parityShift]
      omega
    · obtain ⟨y, hcov⟩ := exists_covBy_of_wellFoundedLT hmaxx
      have hy := ih y hcov.lt
      have hle := s.2.1 hcov.le
      have hg : grade ℕ y = grade ℕ x + 1 :=
        (Nat.covBy_iff_add_one_eq.mp (hcov.grade ℕ)).symm
      by_cases hx : grade ℕ x % 2 = 0
      · dsimp [parityShift] at hy ⊢
        omega
      · have hxodd : grade ℕ x % 2 = 1 := by omega
        have hlabel := (parityLabel_covBy_descends ω hbound hcov).2 hxodd
        have hstrict := s.2.2 hcov.lt hlabel
        dsimp [parityShift] at hy ⊢
        omega

private def fromParityPartition {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (a q : ℕ) (ha : 0 < a)
    (hgrade : ∀ x : α, grade ℕ x ≤ 2 * a - 1)
    (hmin : ∀ x : α, IsMin x → grade ℕ x = 0)
    (hmax : ∀ x : α, IsMax x → grade ℕ x = 2 * a - 1)
    (ω : α → ℕ) (hω : StrictMono ω)
    (hbound : ∀ x, ω x < Fintype.card α)
    (s : PPartition (parityLabel ω) (q + a)) :
    PPartition ω (q + 1) := by
  have lower := parityPartition_lower a (q + a) hmax ω hbound s
  have anti : Antitone (fun x : α => (s.1 x).val - parityShift a x) := by
    classical
    letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
    rw [antitone_iff_forall_covBy]
    intro x y hcov
    have hle := s.2.1 hcov.le
    have hxlower := lower x
    have hylower := lower y
    have hg : grade ℕ y = grade ℕ x + 1 :=
      (Nat.covBy_iff_add_one_eq.mp (hcov.grade ℕ)).symm
    by_cases hx : grade ℕ x % 2 = 0
    · dsimp [parityShift] at hxlower hylower ⊢
      omega
    · have hxodd : grade ℕ x % 2 = 1 := by omega
      have hlabel := (parityLabel_covBy_descends ω hbound hcov).2 hxodd
      have hstrict := s.2.2 hcov.lt hlabel
      dsimp [parityShift] at hxlower hylower ⊢
      omega
  refine ⟨fun x => ⟨(s.1 x).val - parityShift a x, ?_⟩, ?_, ?_⟩
  · obtain ⟨y, hyx, hymin⟩ :=
      exists_minimal_le_of_wellFoundedLT (fun _ : α => True) x trivial
    have hym : IsMin y := by simpa [IsMin] using hymin
    have hg := hmin y hym
    have hs := anti hyx
    have hb := (s.1 y).isLt
    dsimp [parityShift] at hs ⊢
    omega
  · intro x y hxy
    exact Fin.mk_le_mk.mpr (anti hxy)
  · intro x y hxy hlabel
    exact False.elim ((not_lt_of_ge (hω hxy).le) hlabel)

def parityPartitionEquiv {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] (a q : ℕ) (ha : 0 < a)
    (hgrade : ∀ x : α, grade ℕ x ≤ 2 * a - 1)
    (hmin : ∀ x : α, IsMin x → grade ℕ x = 0)
    (hmax : ∀ x : α, IsMax x → grade ℕ x = 2 * a - 1)
    (ω : α → ℕ) (hω : StrictMono ω)
    (hbound : ∀ x, ω x < Fintype.card α) :
    PPartition ω (q + 1) ≃ PPartition (parityLabel ω) (q + a) where
  toFun := toParityPartition a q ha hgrade ω hω hbound
  invFun := fromParityPartition a q ha hgrade hmin hmax ω hω hbound
  left_inv := by
    intro p
    apply Subtype.ext
    funext x
    apply Fin.ext
    change ((p.1 x).val + parityShift a x) - parityShift a x = (p.1 x).val
    omega
  right_inv := by
    intro s
    apply Subtype.ext
    funext x
    apply Fin.ext
    change ((s.1 x).val - parityShift a x) + parityShift a x = (s.1 x).val
    have hbound := parityPartition_lower a (q + a) hmax ω hbound s x
    omega

/-- Natural and rank-parity labels have descent enumerators differing by the
number of forced strict steps on a maximal graded chain. -/
theorem parity_W_shift {α : Type*} [Fintype α] [PartialOrder α]
    [GradeOrder ℕ α] [Nonempty α]
    (a : ℕ) (ha : 0 < a)
    (hgrade : ∀ x : α, grade ℕ x ≤ 2 * a - 1)
    (hmin : ∀ x : α, IsMin x → grade ℕ x = 0)
    (hmax : ∀ x : α, IsMax x → grade ℕ x = 2 * a - 1)
    (ω : α → ℕ) (hω : StrictMono ω) (hinj : Function.Injective ω)
    (hbound : ∀ x, ω x < Fintype.card α) :
    WPolynomial (parityLabel ω) =
      Polynomial.X ^ (a - 1) * WPolynomial ω := by
  classical
  let r := a - 1
  let U := (PowerSeries.invOneSubPow ℤ (Fintype.card α + 1)).val
  have hcanon : Function.Injective (parityLabel ω) :=
    parityLabel_injective ω hinj hbound
  have hcount (q : ℕ) :
      Fintype.card (PPartition ω (q + 1)) =
        Fintype.card (PPartition (parityLabel ω) (q + r + 1)) := by
    have he := parityPartitionEquiv a q ha hgrade hmin hmax ω hω hbound
    have hb : q + r + 1 = q + a := by dsimp [r]; omega
    rw [hb]
    exact Fintype.card_congr he
  have hzero (q : ℕ) (hq : q < r) :
      Fintype.card (PPartition (parityLabel ω) (q + 1)) = 0 := by
    have hempty : IsEmpty (PPartition (parityLabel ω) (q + 1)) := by
      refine ⟨fun s => ?_⟩
      obtain ⟨x, _, hxm⟩ :=
        exists_minimal_le_of_wellFoundedLT (fun _ : α => True)
          (Classical.choice inferInstance) trivial
      have hx : IsMin x := by simpa [IsMin] using hxm
      have hs := parityPartition_lower a (q + 1) hmax ω hbound s x
      have hg := hmin x hx
      have hb := (s.1 x).isLt
      dsimp [parityShift] at hs
      omega
    simp
  have hseries :
      PowerSeries.X ^ r *
          ((WPolynomial ω : PowerSeries ℤ) * U) =
        (WPolynomial (parityLabel ω) : PowerSeries ℤ) * U := by
    have hn := pPartition_series ω hinj
    have hc := pPartition_series (parityLabel ω) hcanon
    change PowerSeries.mk (fun q =>
      (Fintype.card (PPartition ω (q + 1)) : ℤ)) =
      (WPolynomial ω : PowerSeries ℤ) * U at hn
    change PowerSeries.mk (fun q =>
      (Fintype.card (PPartition (parityLabel ω) (q + 1)) : ℤ)) =
      (WPolynomial (parityLabel ω) : PowerSeries ℤ) * U at hc
    rw [← hn, ← hc]
    ext q
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hq : r ≤ q
    · rw [if_pos hq]
      simp only [PowerSeries.coeff_mk]
      have hh := hcount (q - r)
      have hqr : q - r + r = q := Nat.sub_add_cancel hq
      simpa [hqr, Nat.add_assoc] using congrArg (fun k : ℕ => (k : ℤ)) hh
    · rw [if_neg hq]
      simp only [PowerSeries.coeff_mk]
      rw [hzero q (by omega)]
      norm_num
  have hW : PowerSeries.X ^ r * (WPolynomial ω : PowerSeries ℤ) =
      (WPolynomial (parityLabel ω) : PowerSeries ℤ) := by
    have hi : U * (PowerSeries.invOneSubPow ℤ (Fintype.card α + 1)).inv = 1 :=
      (PowerSeries.invOneSubPow ℤ (Fintype.card α + 1)).val_inv
    have h := congrArg (fun p : PowerSeries ℤ =>
      p * (PowerSeries.invOneSubPow ℤ (Fintype.card α + 1)).inv) hseries
    simpa only [mul_assoc, hi, mul_one] using h
  have hcast :
      ((Polynomial.X ^ r * WPolynomial ω : Polynomial ℤ) : PowerSeries ℤ) =
        PowerSeries.X ^ r * (WPolynomial ω : PowerSeries ℤ) := by
    simp
  apply Polynomial.ext
  intro k
  have hk := congrArg (PowerSeries.coeff k) hW
  rw [← hcast] at hk
  simpa only [Polynomial.coeff_coe] using hk.symm

end
end D5.S3.Combinatorics.Posets.GradedGamma
