/- GID: D5/S3/HilbertOperators/OrderThreeOrientationBound
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/OrderThreeOrientationBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The squared commutator norms of an odd orthogonal map against commuting rotations of order dividing three have sum at least three when their commutant preserves orientation. -/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith

/-! # Orientation bound for commuting order-three orthogonal operators -/

@[expose] public section

open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.HilbertOperators.OrderThreeOrientationBound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "End" => H →L[ℝ] H

/-- The operator norm of the commutator with each member of a family. -/
def commutatorNorm {ι : Type*} (T : ι → End) (A : End) : ι → ℝ :=
  fun j => ‖A * T j - T j * A‖

private def conjugate (T A : End) : End := T * A * T ^ 2

private def average (T A : End) : End :=
  (1 / 3 : ℝ) • (A + conjugate T A + conjugate T (conjugate T A))

private def segment (T A : End) (s : ℝ) : End :=
  (1 - 2 * s / 3) • A + (s / 3) • conjugate T A +
    (s / 3) • conjugate T (conjugate T A)

private theorem conjugate_sub (T A B : End) :
    conjugate T (A - B) = conjugate T A - conjugate T B := by
  simp only [conjugate, mul_sub, sub_mul]

private theorem conjugate_norm (T : End) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hcube : T ^ 3 = 1) (A : End) :
    ‖conjugate T A‖ = ‖A‖ := by
  have hpoint (x : H) : ‖conjugate T A x‖ = ‖A ((T ^ 2) x)‖ := hT _
  have hsq (x : H) : ‖(T ^ 2) x‖ = ‖x‖ := by
    change ‖T (T x)‖ = ‖x‖
    rw [hT, hT]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [hpoint, ← hsq x]
    exact A.le_opNorm _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hx : (T ^ 2) (T x) = x := by
      change (T ^ 2 * T) x = x
      rw [← pow_succ, hcube]
      rfl
    simpa only [hpoint, hx, hT] using (conjugate T A).le_opNorm (T x)

private theorem conjugate_cube (T : End) (hcube : T ^ 3 = 1) (A : End) :
    conjugate T (conjugate T (conjugate T A)) = A := by
  calc
    _ = T ^ 3 * A * (T ^ 3) ^ 2 := by unfold conjugate; noncomm_ring
    _ = A := by simp [hcube]

private theorem defect_eq_commutator (T A : End) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hcube : T ^ 3 = 1) :
    ‖conjugate T A - A‖ = ‖A * T - T * A‖ := by
  have hright : (T * A - A * T) * T ^ 2 = conjugate T A - A := by
    rw [sub_mul]
    unfold conjugate
    rw [mul_assoc A, ← pow_succ', hcube, mul_one]
  have hsq (x : H) : ‖(T ^ 2) x‖ = ‖x‖ := by
    change ‖T (T x)‖ = ‖x‖
    rw [hT, hT]
  rw [← hright, norm_sub_rev (A * T) (T * A)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖(T * A - A * T) ((T ^ 2) x)‖ ≤ _
    rw [← hsq x]
    exact (T * A - A * T).le_opNorm _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hx : (T ^ 2) (T x) = x := by
      change (T ^ 2 * T) x = x
      rw [← pow_succ, hcube]
      rfl
    have h := ((T * A - A * T) * T ^ 2).le_opNorm (T x)
    change ‖(T * A - A * T) ((T ^ 2) (T x))‖ ≤ _ at h
    rwa [hx, hT] at h

private theorem conjugate_commutes {T P : End} (h : Commute T P) (A : End) :
    conjugate T (conjugate P A) = conjugate P (conjugate T A) := by
  unfold conjugate
  calc
    _ = (T * P) * A * (P ^ 2 * T ^ 2) := by simp only [mul_assoc]
    _ = (P * T) * A * (T ^ 2 * P ^ 2) := by rw [h.eq, (h.symm.pow_pow 2 2).eq]
    _ = _ := by simp only [mul_assoc]

private theorem conjugate_average {T P : End} (h : Commute T P) (A : End) :
    conjugate T (average P A) = average P (conjugate T A) := by
  simp only [average, conjugate, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  change (1 / 3 : ℝ) •
      (conjugate T A + conjugate T (conjugate P A) +
        conjugate T (conjugate P (conjugate P A))) = _
  rw [conjugate_commutes h A, conjugate_commutes h (conjugate P A),
    conjugate_commutes h A]
  rfl

private theorem average_fixed (T : End) (hcube : T ^ 3 = 1) (A : End) :
    conjugate T (average T A) = average T A := by
  have h : conjugate T (average T A) = (1 / 3 : ℝ) •
      (conjugate T A + conjugate T (conjugate T A) +
        conjugate T (conjugate T (conjugate T A))) := by
    simp only [average, conjugate, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  rw [h, conjugate_cube T hcube, average]
  congr 1
  abel

private theorem commute_of_fixed {T A : End} (hcube : T ^ 3 = 1)
    (h : conjugate T A = A) : Commute A T := by
  have heq := congrArg (fun B : End => B * T) h
  change (T * A * T ^ 2) * T = A * T at heq
  rw [mul_assoc (T * A), ← pow_succ, hcube, mul_one] at heq
  exact heq.symm

private theorem average_sub (T A B : End) :
    average T (A - B) = average T A - average T B := by
  simp only [average, conjugate_sub, ← smul_sub]
  congr 1
  abel

private theorem average_norm_le (T : End) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hcube : T ^ 3 = 1) (A : End) : ‖average T A‖ ≤ ‖A‖ := by
  have h₁ := norm_add_le (A + conjugate T A) (conjugate T (conjugate T A))
  have h₂ := norm_add_le A (conjugate T A)
  rw [conjugate_norm T hT hcube, conjugate_norm T hT hcube] at h₁
  rw [conjugate_norm T hT hcube] at h₂
  rw [average, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 3 : ℝ))]
  linarith

private theorem variance (x y z : H) (a b c : ℝ) (h : a + b + c = 1) :
    ‖a • x + b • y + c • z‖ ^ 2 =
      a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 + c * ‖z‖ ^ 2 -
        (a * b * ‖x - y‖ ^ 2 + a * c * ‖x - z‖ ^ 2 + b * c * ‖y - z‖ ^ 2) := by
  have hc : c = 1 - a - b := by linarith
  subst c
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
  ring

private theorem segment_lower (T A : End) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hcube : T ^ 3 = 1) {b e : ℝ} (he : 0 ≤ e)
    (hA : ∀ x, b * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hdefect : ‖conjugate T A - A‖ ≤ e)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) (x : H) :
    (b - e ^ 2 / 3) * ‖x‖ ^ 2 ≤ ‖segment T A s x‖ ^ 2 := by
  let B := conjugate T A
  let C := conjugate T B
  let p := 1 - 2 * s / 3
  let q := s / 3
  have hp : 0 ≤ p := by dsimp [p]; linarith [hs.2]
  have hq : 0 ≤ q := by dsimp [q]; linarith [hs.1]
  have hsum : p + q + q = 1 := by dsimp [p, q]; ring
  have hmass : p * q + p * q + q * q ≤ 1 / 3 := by
    dsimp [p, q]
    nlinarith [sq_nonneg (s - 1)]
  have lift_lower (D : End) (hD : ∀ y, b * ‖y‖ ^ 2 ≤ ‖D y‖ ^ 2) (y : H) :
      b * ‖y‖ ^ 2 ≤ ‖conjugate T D y‖ ^ 2 := by
    have hy : ‖(T ^ 2) y‖ = ‖y‖ := by
      change ‖T (T y)‖ = ‖y‖
      rw [hT, hT]
    change b * ‖y‖ ^ 2 ≤ ‖T (D ((T ^ 2) y))‖ ^ 2
    rw [hT, ← hy]
    exact hD _
  have hB : ∀ y, b * ‖y‖ ^ 2 ≤ ‖B y‖ ^ 2 := lift_lower A hA
  have hC : ∀ y, b * ‖y‖ ^ 2 ≤ ‖C y‖ ^ 2 := lift_lower B hB
  have hCB : ‖C - B‖ ≤ e := by
    change ‖conjugate T B - conjugate T A‖ ≤ e
    rwa [← conjugate_sub, conjugate_norm T hT hcube]
  have hAC : ‖A - C‖ ≤ e := by
    change ‖A - C‖ ≤ e
    calc
      _ = ‖conjugate T C - conjugate T B‖ := by
        rw [show conjugate T C = A from conjugate_cube T hcube A]
        rfl
      _ = ‖C - B‖ := by rw [← conjugate_sub, conjugate_norm T hT hcube]
      _ ≤ e := hCB
  have pair_bound (D F : End) (hDF : ‖D - F‖ ≤ e) :
      ‖D x - F x‖ ^ 2 ≤ e ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg he (norm_nonneg _))).2
    exact ((D - F).le_opNorm x).trans (mul_le_mul_of_nonneg_right hDF (norm_nonneg _))
  have hab := pair_bound A B (by rwa [norm_sub_rev])
  have hac := pair_bound A C hAC
  have hbc := pair_bound B C (by rwa [norm_sub_rev])
  have havg := add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hA x) hp)
    (mul_le_mul_of_nonneg_left (hB x) hq)) (mul_le_mul_of_nonneg_left (hC x) hq)
  have hvar := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hab (mul_nonneg hp hq))
      (mul_le_mul_of_nonneg_left hac (mul_nonneg hp hq)))
    (mul_le_mul_of_nonneg_left hbc (mul_nonneg hq hq))
  have htotal := mul_le_mul_of_nonneg_right hmass (mul_nonneg (sq_nonneg e) (sq_nonneg ‖x‖))
  change _ ≤ ‖p • A x + q • B x + q • C x‖ ^ 2
  rw [variance _ _ _ _ _ _ hsum]
  rw [← add_mul, ← add_mul, hsum, one_mul] at havg
  rw [← add_mul, ← add_mul] at hvar
  linarith

private theorem segment_one (T A : End) : segment T A 1 = average T A := by
  unfold segment average
  rw [smul_add, smul_add]
  congr 2 <;> norm_num

private theorem average_det_neg [FiniteDimensional ℝ H] (T A : End)
    (hT : ∀ x, ‖T x‖ = ‖x‖) (hcube : T ^ 3 = 1)
    {b e : ℝ} (he : 0 ≤ e) (hpos : 0 < b - e ^ 2 / 3)
    (hA : ∀ x, b * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) (hdet : A.det < 0)
    (hdefect : ‖conjugate T A - A‖ ≤ e) : (average T A).det < 0 := by
  let f : ℝ → ℝ := fun s => (segment T A s).det
  have hcont : Continuous f := by
    apply ContinuousLinearMap.continuous_det.comp
    unfold segment
    fun_prop
  have hzero : f 0 = A.det := by simp [f, segment]
  have hone : f 1 = (average T A).det := congrArg ContinuousLinearMap.det (segment_one T A)
  by_contra! hnonneg
  have hmem : 0 ∈ Set.Icc (f 0) (f 1) :=
    ⟨hzero ▸ le_of_lt hdet, hone ▸ hnonneg⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hmem
  have hker : LinearMap.ker (segment T A s).toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.2
    intro x hx
    by_contra hne
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
    have hh := segment_lower T A hT hcube he hA hdefect hs x
    change segment T A s x = 0 at hx
    rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
    exact (not_lt_of_ge hh) (mul_pos hpos (pow_pos hxpos _))
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hfs) hker

/-- If the common real commutant contains no map of negative determinant,
every negative-determinant orthogonal map has squared commutator sum at least three. -/
theorem sum_sq_commutatorNorm_ge_three
    {ι : Type*} [FiniteDimensional ℝ H] (S : Finset ι) (T : ι → End) (U : End)
    (hT : ∀ j ∈ S, ∀ x, ‖T j x‖ = ‖x‖)
    (hcube : ∀ j ∈ S, T j ^ 3 = 1)
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute (T i) (T j))
    (hU : ∀ x, ‖U x‖ = ‖x‖) (hneg : U.det < 0)
    (horient : ∀ A : End, (∀ j ∈ S, Commute A (T j)) → 0 ≤ A.det) :
    3 ≤ ∑ j ∈ S, commutatorNorm T U j ^ 2 := by
  classical
  let e := commutatorNorm T U
  by_contra! hsmall
  have hsmall' : ∑ j ∈ S, e j ^ 2 < 3 := hsmall
  have hstep (F : Finset ι) (hF : F ⊆ S) :
      ∃ A : End, A.det < 0 ∧
        (∀ x, (1 - (∑ j ∈ F, e j ^ 2) / 3) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) ∧
        (∀ j ∈ F, conjugate (T j) A = A) ∧
        (∀ j ∈ S, ‖conjugate (T j) A - A‖ ≤ e j) := by
    induction F using Finset.induction_on with
    | empty =>
      refine ⟨U, hneg, ?_, by simp, ?_⟩
      · intro x
        simp [hU]
      · intro j hj
        exact le_of_eq (defect_eq_commutator (T j) U (hT j hj) (hcube j hj))
    | insert i F hi ih =>
      have hiS : i ∈ S := hF (Finset.mem_insert_self i F)
      have hFS : F ⊆ S := fun _ hj => hF (Finset.mem_insert_of_mem hj)
      obtain ⟨A, hAneg, hAlower, hAfixed, hAdefect⟩ := ih hFS
      have hsum : ∑ j ∈ insert i F, e j ^ 2 = e i ^ 2 + ∑ j ∈ F, e j ^ 2 :=
        Finset.sum_insert hi
      have hbound := (Finset.sum_le_sum_of_subset_of_nonneg hF
        (fun j _ _ => sq_nonneg (e j))).trans_lt hsmall'
      rw [hsum] at hbound
      have hpos : 0 < 1 - (∑ j ∈ F, e j ^ 2) / 3 - e i ^ 2 / 3 := by linarith
      have he : 0 ≤ e i := norm_nonneg _
      refine ⟨average (T i) A,
        average_det_neg (T i) A (hT i hiS) (hcube i hiS) he hpos hAlower hAneg
          (hAdefect i hiS), ?_, ?_, ?_⟩
      · intro x
        rw [hsum, add_div, sub_add_eq_sub_sub, add_comm (e i ^ 2 / 3),
          ← sub_add_eq_sub_sub, ← segment_one]
        rw [sub_add_eq_sub_sub]
        exact segment_lower (T i) A (hT i hiS) (hcube i hiS) he hAlower
          (hAdefect i hiS) (by norm_num) x
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact average_fixed _ (hcube i hiS) _
        · rw [conjugate_average (hcomm j (hFS hj) i hiS), hAfixed j hj]
      · intro j hj
        rw [conjugate_average (hcomm j hj i hiS), ← average_sub]
        exact (average_norm_le (T i) (hT i hiS) (hcube i hiS) _).trans (hAdefect j hj)
  obtain ⟨A, hAneg, _, hAfixed, _⟩ := hstep S (fun _ hj => hj)
  exact (not_lt_of_ge (horient A (fun j hj => commute_of_fixed (hcube j hj) (hAfixed j hj)))) hAneg

end D5.S3.HilbertOperators.OrderThreeOrientationBound
