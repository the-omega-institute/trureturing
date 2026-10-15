/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteGenuinePeriods
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteGenuinePeriods
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine return-time gcd periods and cyclic labels of actual finite closed classes. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Data.ZMod.Basic

open Finset Matrix
open scoped BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods
noncomputable section
universe u
variable {S : Type u} [Fintype S] [DecidableEq S]

/-- Positive return lengths of the actual matrix, excluding time zero. -/
def returns (A : Matrix S S ℝ) (x : S) : Set ℕ :=
  {n | 0 < n ∧ 0 < (A ^ n) x x}

/-- The gcd of all actual positive return lengths at a state. -/
def period (A : Matrix S S ℝ) (x : S) : ℕ := Nat.setGcd (returns A x)

private theorem positive_add {A : Matrix S S ℝ} (hA : ∀ x y, 0 ≤ A x y)
    {a b : ℕ} {x y z : S} (ha : 0 < (A ^ a) x y) (hb : 0 < (A ^ b) y z) :
    0 < (A ^ (a + b)) x z := by
  rw [pow_add, Matrix.mul_apply]
  exact (sum_pos_iff_of_nonneg (fun k _ => mul_nonneg
    (Matrix.pow_apply_nonneg hA a x k) (Matrix.pow_apply_nonneg hA b k z))).mpr
      ⟨y, mem_univ _, mul_pos ha hb⟩

private theorem period_dvd {A : Matrix S S ℝ} {x : S} {n : ℕ}
    (hn : 0 < (A ^ n) x x) : period A x ∣ n := by
  by_cases h : n = 0
  · simp [h]
  · exact Nat.setGcd_dvd_of_mem ⟨Nat.pos_of_ne_zero h, hn⟩

private theorem period_positive {A : Matrix S S ℝ} (hA : Matrix.IsIrreducible A)
    (x : S) : 0 < period A x := by
  obtain ⟨n, hn, hp⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA x x
  apply Nat.pos_of_ne_zero
  intro he
  have hd := Nat.setGcd_dvd_of_mem (s := returns A x) ⟨hn, hp⟩
  change period A x ∣ n at hd
  rw [he] at hd
  exact (Nat.ne_of_gt hn) (zero_dvd_iff.mp hd)

private theorem period_transport {A : Matrix S S ℝ} (hA : Matrix.IsIrreducible A)
    (x y : S) : period A x ∣ period A y := by
  apply Nat.dvd_setGcd_iff.mpr
  intro n hn
  obtain ⟨a, ha, haxy⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA x y
  obtain ⟨b, hb, hbyx⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA y x
  have hd := period_dvd (positive_add hA.nonneg haxy hbyx)
  have he := period_dvd (positive_add hA.nonneg
    (positive_add hA.nonneg haxy hn.2) hbyx)
  have hf : period A x ∣ (a + b) + n := by
    convert he using 1
    omega
  exact (Nat.dvd_add_right hd).mp hf

private theorem period_independent {A : Matrix S S ℝ} (hA : Matrix.IsIrreducible A)
    (x y : S) : period A x = period A y :=
  Nat.dvd_antisymm (period_transport hA x y) (period_transport hA y x)

/-- Labels use residues of actual positive paths from the chosen base state. -/
def label (A : Matrix S S ℝ) (hA : Matrix.IsIrreducible A) (a x : S) :
    ZMod (period A a) :=
  ((Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA a x).choose

private theorem label_base {A : Matrix S S ℝ} (hA : Matrix.IsIrreducible A) (a : S) :
    label A hA a a = 0 := by
  unfold label
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact period_dvd ((Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA a a).choose_spec.2

private theorem label_path {A : Matrix S S ℝ} (hA : Matrix.IsIrreducible A)
    (a x y : S) (n : ℕ) (hn : 0 < (A ^ n) x y) :
    label A hA a x + (n : ZMod (period A a)) = label A hA a y := by
  let ix := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA a x
  let iy := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA a y
  obtain ⟨b, hb, hby⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA y a
  have hd := period_dvd (positive_add hA.nonneg
    (positive_add hA.nonneg ix.choose_spec.2 hn) hby)
  have he := period_dvd (positive_add hA.nonneg iy.choose_spec.2 hby)
  have hdz := (ZMod.natCast_eq_zero_iff (ix.choose + n + b) (period A a)).mpr hd
  have hez := (ZMod.natCast_eq_zero_iff (iy.choose + b) (period A a)).mpr he
  simp only [Nat.cast_add] at hdz hez
  change (ix.choose : ZMod (period A a)) + n = iy.choose
  linear_combination hdz - hez

private theorem label_surjective {A : Matrix S S ℝ}
    (hA : A ∈ rowStochastic ℝ S) (hi : Matrix.IsIrreducible A) (a : S) :
    Function.Surjective (label A hi a) := by
  let : NeZero (period A a) := ⟨ne_of_gt (period_positive hi a)⟩
  intro j
  have hs := (rowStochastic ℝ S).pow_mem hA j.val
  obtain ⟨y, _, hy⟩ := (sum_pos_iff_of_nonneg (fun y _ => hs.1 a y)).mp
    (by rw [sum_row_of_mem_rowStochastic hs a]; norm_num)
  refine ⟨y, ?_⟩
  have he := label_path hi a a y j.val hy
  simpa [label_base hi a, ZMod.natCast_zmod_val] using he.symm

private theorem period_card {A : Matrix S S ℝ}
    (hA : A ∈ rowStochastic ℝ S) (hi : Matrix.IsIrreducible A) (a : S) :
    period A a ≤ Fintype.card S := by
  let : NeZero (period A a) := ⟨ne_of_gt (period_positive hi a)⟩
  simpa only [ZMod.card] using Fintype.card_le_of_surjective
    (label A hi a) (label_surjective hA hi a)

private theorem closure_returns {A : Matrix S S ℝ} (hA : ∀ x y, 0 ≤ A x y)
    (x : S) {n : ℕ} (hn : n ∈ AddSubmonoid.closure (returns A x)) :
    0 < (A ^ n) x x := by
  exact AddSubmonoid.closure_induction (fun n hn => hn.2)
    (by simp) (fun m n _ _ hm hn => positive_add hA hm hn) hn

private theorem eventual_positive {A : Matrix S S ℝ} (hi : Matrix.IsIrreducible A)
    (a x y : S) : ∃ N : ℕ, ∀ n ≥ N,
      label A hi a x + (n : ZMod (period A a)) = label A hi a y →
      0 < (A ^ n) x y := by
  obtain ⟨b, hb, hby⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hi.nonneg).mp hi x y
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (returns A y)
  refine ⟨N + b, fun n hn he => ?_⟩
  have hbn : b ≤ n := by omega
  have hp := label_path hi a x y b hby
  have hz : (n : ZMod (period A a)) = b := by
    exact add_left_cancel (he.trans hp.symm)
  have hdiv : period A a ∣ n - b := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hbn, hz, sub_self]
  have hdivy : period A y ∣ n - b := by rwa [← period_independent hi a y]
  have hr := closure_returns hi.nonneg y (hN (n - b) (by omega) hdivy)
  have hpos := positive_add hi.nonneg hby hr
  simpa only [Nat.add_sub_of_le hbn] using hpos

/-- The period/label interface refers only to the original actual class restriction. -/
structure ClassPeriods {X : Type u} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (C : FiniteClosedClasses.ClosedClass P) where
  base : C.val
  positive : 0 < period (FiniteClosedClasses.restriction P C.val) base
  independent : ∀ x : C.val,
    period (FiniteClosedClasses.restriction P C.val) x =
      period (FiniteClosedClasses.restriction P C.val) base
  bound : period (FiniteClosedClasses.restriction P C.val) base ≤ Fintype.card C.val
  phase : C.val → ZMod (period (FiniteClosedClasses.restriction P C.val) base)
  onto : Function.Surjective phase
  advance : ∀ x y : C.val, 0 < P x.val y.val → phase x + 1 = phase y
  path_residue : ∀ (n : ℕ) (x y : C.val), 0 < (P ^ n) x.val y.val →
    phase x + (n : ZMod (period (FiniteClosedClasses.restriction P C.val) base)) = phase y
  eventual : ∀ x y : C.val, ∃ N : ℕ, ∀ n ≥ N,
    phase x + (n : ZMod (period (FiniteClosedClasses.restriction P C.val) base)) = phase y →
    0 < (P ^ n) x.val y.val

/-- Every actual closed class has its genuine positive return-time gcd period and onto cyclic labels. -/
theorem actual_periods {X : Type u} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (C : FiniteClosedClasses.ClosedClass P) : Nonempty (ClassPeriods P C) := by
  classical
  have hS := FiniteClosedClasses.actual_structure P hP
  obtain ⟨a, ha⟩ := hS.class_nonempty C
  let b : C.val := ⟨a, ha⟩
  let A := FiniteClosedClasses.restriction P C.val
  have hi : Matrix.IsIrreducible A := hS.class_irreducible C
  have hs : A ∈ rowStochastic ℝ C.val := hS.class_stochastic C
  refine ⟨{
    base := b
    positive := period_positive hi b
    independent := fun x => period_independent hi x b
    bound := period_card hs hi b
    phase := label A hi b
    onto := label_surjective hs hi b
    advance := ?_
    path_residue := ?_
    eventual := ?_ }⟩
  · intro x y hp
    change 0 < A x y at hp
    simpa using label_path hi b x y 1 (by simpa only [pow_one] using hp)
  · intro n x y hp
    exact label_path hi b x y n ((hS.class_powers C n x y).symm ▸ hp)
  · intro x y
    obtain ⟨N, hN⟩ := eventual_positive hi b x y
    exact ⟨N, fun n hn he => (hS.class_powers C n x y) ▸ hN n hn he⟩

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods
