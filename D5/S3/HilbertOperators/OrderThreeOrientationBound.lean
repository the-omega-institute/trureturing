/- GID: D5/S3/HilbertOperators/OrderThreeOrientationBound
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/OrderThreeOrientationBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Squared commutator lower bound for an odd orthogonal map and order-three rotations. -/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
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
    calc
      _ = ‖conjugate T C - conjugate T B‖ := by
        rw [show conjugate T C = A from conjugate_cube T hcube A]
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
  congr 2
  norm_num

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
        rw [hsum, add_comm (e i ^ 2), add_div, sub_add_eq_sub_sub, ← segment_one]
        exact segment_lower (T i) A (hT i hiS) (hcube i hiS) he hAlower
          (hAdefect i hiS) (by norm_num) x
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact average_fixed _ (hcube j hiS) _
        · rw [conjugate_average (hcomm j (hFS hj) i hiS), hAfixed j hj]
      · intro j hj
        rw [conjugate_average (hcomm j hj i hiS), ← average_sub]
        exact (average_norm_le (T i) (hT i hiS) (hcube i hiS) _).trans (hAdefect j hj)
  obtain ⟨A, hAneg, _, hAfixed, _⟩ := hstep S (fun _ hj => hj)
  exact (not_lt_of_ge (horient A (fun j hj => commute_of_fixed (hcube j hj) (hAfixed j hj)))) hAneg

section CharacterPlanes

attribute [local instance] InnerProductSpace.complexToReal

variable {ι κ : Type*} [Fintype κ]

local notation "Planes" => EuclideanSpace ℂ κ

/-- Multiplication by the specified complex character value on each real plane. -/
def characterPlane (w : κ → ℂ) : Planes →L[ℝ] Planes :=
  ({
    toFun := fun x => WithLp.toLp 2 (fun k => w k * x k)
    map_add' := fun x y => by ext k; exact mul_add (w k) (x k) (y k)
    map_smul' := fun r x => by
      ext k
      change w k * (r • x k) = r • (w k * x k)
      rw [Complex.real_smul, Complex.real_smul]
      ring
  } : Planes →ₗ[ℝ] Planes).toContinuousLinearMap

private theorem characterPlane_apply (w : κ → ℂ) (x : Planes) (k : κ) :
    characterPlane w x k = w k * x k := rfl

private theorem characterPlane_det_nonneg (S : Finset ι) (w : ι → κ → ℂ)
    (hsep : ∀ i k, ∃ j ∈ S, w j i ≠ starRingEnd ℂ (w j k))
    (A : Planes →L[ℝ] Planes)
    (hA : ∀ j ∈ S, Commute A (characterPlane (w j))) : 0 ≤ A.det := by
  classical
  let J : Planes →ₗ[ℝ] Planes :=
    (Complex.I • (LinearMap.id : Planes →ₗ[ℂ] Planes)).restrictScalars ℝ
  let F := A.toLinearMap * J - J * A.toLinearMap
  have hF (x : Planes) : F x = A (Complex.I • x) - Complex.I • A x := rfl
  have hI (x : Planes) : Complex.I • Complex.I • x = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hanti (x : Planes) : F (Complex.I • x) = -(Complex.I • F x) := by
    rw [hF, hF, hI, map_neg, smul_sub, hI]
    abel
  have hscalar (a : ℂ) (x : Planes) : F (a • x) = starRingEnd ℂ a • F x := by
    have hconj : starRingEnd ℂ a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hconj, sub_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    nth_rw 1 [← Complex.re_add_im a]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul,
      hanti, smul_neg, sub_eq_add_neg]
  have hFcomm (j : ι) (hj : j ∈ S) (x : Planes) :
      F (characterPlane (w j) x) = characterPlane (w j) (F x) := by
    have hAx (y : Planes) : A (characterPlane (w j) y) = characterPlane (w j) (A y) :=
      congrArg (fun B : Planes →L[ℝ] Planes => B y) (hA j hj).eq
    have hJ (y : Planes) : Complex.I • characterPlane (w j) y =
        characterPlane (w j) (Complex.I • y) := by
      ext i
      simp only [characterPlane_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hF, hF, hJ, hAx, hAx, hJ, map_sub]
  let b := (EuclideanSpace.basisFun κ ℂ).toBasis
  have hBasis (k : κ) : F (b k) = 0 := by
    ext i
    obtain ⟨j, hj, hji⟩ := hsep i k
    have hdiag : characterPlane (w j) (b k) = w j k • b k := by
      ext l
      simp only [characterPlane_apply, PiLp.smul_apply, smul_eq_mul]
      change w j l * (EuclideanSpace.basisFun κ ℂ k) l =
        w j k * (EuclideanSpace.basisFun κ ℂ k) l
      rw [EuclideanSpace.basisFun_apply]
      by_cases hl : l = k
      · subst l
        rfl
      · simp [EuclideanSpace.single, hl]
    have heq := hFcomm j hj (b k)
    rw [hdiag, hscalar] at heq
    have hi : starRingEnd ℂ (w j k) * F (b k) i = w j i * F (b k) i :=
      by simpa only [characterPlane_apply, PiLp.smul_apply, smul_eq_mul] using
        congrArg (fun y : Planes => y i) heq
    have hz : (w j i - starRingEnd ℂ (w j k)) * F (b k) i = 0 := by
      rw [sub_mul, hi, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hji)
  have hzero (x : Planes) : F x = 0 := by
    rw [← b.sum_repr x, map_sum]
    simp [hscalar, hBasis]
  let B : Planes →ₗ[ℂ] Planes :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun a x => by
        have hAI : A (Complex.I • x) = Complex.I • A x := by
          simpa only [hF, sub_eq_zero] using hzero x
        change A (a • x) = a • A x
        rw [← Complex.re_add_im a, add_smul, add_smul, mul_smul, mul_smul,
          Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, Complex.coe_smul,
          map_add, map_smul, map_smul, hAI] }
  have hB : B.restrictScalars ℝ = A.toLinearMap := by ext x; rfl
  change 0 ≤ A.toLinearMap.det
  rw [← hB, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  exact sq_nonneg _

private theorem exists_sqrt_card_le {S : Finset ι} {e : ι → ℝ}
    (he : ∀ j ∈ S, 0 ≤ e j) (h : 3 ≤ ∑ j ∈ S, e j ^ 2) :
    ∃ j ∈ S, Real.sqrt (3 / (S.card : ℝ)) ≤ e j := by
  classical
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at h
    norm_num at h
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  by_contra! hn
  have hj (j : ι) (hj : j ∈ S) : e j ^ 2 < 3 / (S.card : ℝ) := by
    have hs := hn j hj
    rw [Real.lt_sqrt (he j hj)] at hs
    exact hs
  have hlt := Finset.sum_lt_sum_of_nonempty hS hj
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hc)] at hlt
  linarith

/-- The character planes give the orientation obstruction whenever no character
is the conjugate of another in the chosen list of plane labels. -/
theorem characterPlane_commutator_bounds
    (S : Finset ι) (w : ι → κ → ℂ) (U : Planes →L[ℝ] Planes)
    (hcube : ∀ j ∈ S, ∀ k, w j k ^ 3 = 1)
    (hsep : ∀ i k, ∃ j ∈ S, w j i ≠ starRingEnd ℂ (w j k))
    (hU : ∀ x, ‖U x‖ = ‖x‖) (hneg : U.det < 0) :
    (3 ≤ ∑ j ∈ S, commutatorNorm (fun j => characterPlane (w j)) U j ^ 2) ∧
      ∃ j ∈ S, Real.sqrt (3 / (S.card : ℝ)) ≤
        commutatorNorm (fun j => characterPlane (w j)) U j := by
  have hnorm (j : ι) (hj : j ∈ S) (x : Planes) :
      ‖characterPlane (w j) x‖ = ‖x‖ := by
    have hw (k : κ) : ‖w j k‖ = 1 := by
      have h := congrArg norm (hcube j hj k)
      rw [norm_pow, norm_one] at h
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 3 ≠ 0)).mp
        (h.trans (one_pow 3).symm)
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro k _
    rw [characterPlane_apply, norm_mul, hw, one_mul]
  have hpow (j : ι) (hj : j ∈ S) : characterPlane (w j) ^ 3 = 1 := by
    ext x k
    change characterPlane (w j) (characterPlane (w j) (characterPlane (w j) x)) k = x k
    simp only [characterPlane_apply]
    calc
      _ = w j k ^ 3 * x k := by ring
      _ = _ := by rw [hcube j hj k, one_mul]
  have hcomm (i j : ι) : Commute (characterPlane (w i)) (characterPlane (w j)) := by
    change characterPlane (w i) * characterPlane (w j) =
      characterPlane (w j) * characterPlane (w i)
    ext x k
    change characterPlane (w i) (characterPlane (w j) x) k =
      characterPlane (w j) (characterPlane (w i) x) k
    simp only [characterPlane_apply]
    ring
  have hsum := sum_sq_commutatorNorm_ge_three S (fun j => characterPlane (w j)) U
    hnorm hpow (fun i _ j _ => hcomm i j) hU hneg (characterPlane_det_nonneg S w hsep)
  exact ⟨hsum, exists_sqrt_card_le (fun _ _ => norm_nonneg _) hsum⟩

end CharacterPlanes

end D5.S3.HilbertOperators.OrderThreeOrientationBound
