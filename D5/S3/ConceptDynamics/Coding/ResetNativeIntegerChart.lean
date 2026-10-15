/- GID: D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNativeIntegerChart
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Original native square arithmetic and bounded generation by actual forward shifts. -/
import D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
import D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.Nat.Periodic
import D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open Polynomial
open scoped BigOperators
open ResetNumberedHistories
open ResetSignIntegerCyclic
open ResetNativeIntegralDefect
open InertGroupBlockConjugacy
  (VertexModule DimensionGroup transition stationaryTransition groupAction leftTranslation induced)

local instance originalNativeIntModule (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

/-- The original native integer group, with its canonical integer-module instance. -/
abbrev Native (q : ℕ) := DimensionGroup (resetMatrix q)

/-- Original stage maps, with no change in the orientation of stationary time. -/
def nativeStage (q n : ℕ) (v : VertexModule Sign q) : Native q :=
  Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
    (stationaryTransition (transition (resetMatrix q))) n v

private theorem finite_time (q : ℕ) (hq : 0 < q) (v : VertexModule Sign q) :
    D5.S1.Recurrence.FiniteCompanionCyclicModule.time resetLabel q hq v =
      transition (resetMatrix q) v := by
  cases q with
  | zero => omega
  | succ n =>
    exact (congrArg (fun f : VertexModule Sign (n + 1) →+ VertexModule Sign (n + 1) => f v)
      (ResetSquareIntegralDefect.time_eq n)).symm

private abbrev finiteChart (q : ℕ) (hq : 0 < q) : QP q ≃ₗ[ℤ] VertexModule Sign q :=
  ((D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclicEquiv resetLabel q hq).toAddEquiv.trans
    (Module.AEval'.of
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.time resetLabel q hq)).symm.toAddEquiv).toIntLinearEquiv

/-- The actual integral chart: literal ring inverse, cyclic chart, and original stage zero. -/
def nativeIntEquiv (q : ℕ) (hq : 0 < q) : QF q ≃ₗ[ℤ] Native q :=
  (ringEquiv q).symm.toAddEquiv.toIntLinearEquiv |>.trans
    ((finiteChart q hq).trans (resetNativeEquiv q hq).symm)

private theorem native_read (q : ℕ) (hq : 0 < q) (b : QF q) :
    resetNativeEquiv q hq (nativeIntEquiv q hq b) =
      finiteChart q hq ((ringEquiv q).symm b) :=
  (resetNativeEquiv q hq).apply_symm_apply _

private theorem ring_X (q : ℕ) (b : QF q) :
    (ringEquiv q).symm (fp q X * b) = pp q X * (ringEquiv q).symm b := by
  rw [map_mul]
  congr 1
  exact (ringEquiv q).injective (by
    rw [RingEquiv.apply_symm_apply]
    exact (literal_presentation q).2.2.2.2.1.symm)

private theorem finite_X (q : ℕ) (hq : 0 < q) (b : QP q) :
    finiteChart q hq (pp q X * b) = transition (resetMatrix q) (finiteChart q hq b) := by
  change (Module.AEval'.of _).symm
    (D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclicEquiv resetLabel q hq
      ((X : R[X]) • b)) = _
  rw [map_smul, Module.AEval'.of_symm_X_smul, finite_time]
  rfl

private theorem native_X (q : ℕ) (hq : 0 < q) (b : QF q) :
    nativeIntEquiv q hq (fp q X * b) = resetTheta q (nativeIntEquiv q hq b) := by
  apply (resetNativeEquiv q hq).injective
  rw [native_read, resetNativeEquiv_theta, native_read, ring_X, finite_X]

private theorem native_symm_X (q : ℕ) (hq : 0 < q) (x : Native q) :
    (nativeIntEquiv q hq).symm (resetTheta q x) = (X : ℤ[X]) • (nativeIntEquiv q hq).symm x := by
  apply (nativeIntEquiv q hq).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((native_X q hq ((nativeIntEquiv q hq).symm x)).trans
    (congrArg (resetTheta q) ((nativeIntEquiv q hq).apply_symm_apply x))).symm

/-- Polynomial-linearity is promoted only after actual forward-time intertwining. -/
def nativePolynomialEquiv (q : ℕ) (hq : 0 < q) :
    QF q ≃ₗ[ℤ[X]] Module.AEval' (resetTheta q) :=
  (LinearEquiv.ofAEval (resetTheta q) (nativeIntEquiv q hq).symm (native_symm_X q hq)).symm

private theorem polynomial_chart (q : ℕ) (hq : 0 < q) (b : QF q) :
    nativePolynomialEquiv q hq b = Module.AEval'.of (resetTheta q) (nativeIntEquiv q hq b) := rfl

private theorem native_polynomial (q : ℕ) (hq : 0 < q) (p : ℤ[X]) (b : QF q) :
    nativeIntEquiv q hq (fp q p * b) =
      (aeval (resetTheta q) p) (nativeIntEquiv q hq b) := by
  have h := (nativePolynomialEquiv q hq).map_smul p b
  change nativePolynomialEquiv q hq (fp q p * b) = p • nativePolynomialEquiv q hq b at h
  rw [polynomial_chart, polynomial_chart] at h
  exact congrArg (Module.AEval'.of (resetTheta q)).symm h

private theorem native_one (q : ℕ) (hq : 0 < q) :
    nativeIntEquiv q hq 1 = nativeStage q 0
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.e0 q hq) := by
  change (resetNativeEquiv q hq).symm
    ((Module.AEval'.of _).symm
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclicEquiv resetLabel q hq
        ((ringEquiv q).symm 1))) = _
  rw [map_one, (D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclic_presentation resetLabel q hq).2.2,
    LinearEquiv.symm_apply_apply]
  rfl

private theorem native_coordinates (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q) :
    (nativeIntEquiv q hq).symm (nativeStage q n v) =
      ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
          ((resetInverse q hq ^ n) v))) := by
  change ringEquiv q
    ((D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclicEquiv resetLabel q hq).symm
      (Module.AEval'.of _ (resetNativeEquiv q hq (nativeStage q n v)))) = _
  rw [show resetNativeEquiv q hq (nativeStage q n v) = (resetInverse q hq ^ n) v from
    resetNativeEquiv_stage q hq n v,
    (D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclic_presentation resetLabel q hq).2.1]
  rfl

private theorem native_coefficient (q : ℕ) (hq : 0 < q) (x : Native q) :
    resetNativeEquiv q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
      leftTranslation (Multiplicative.ofAdd true) (resetNativeEquiv q hq x) := by
  let v := resetNativeEquiv q hq x
  have hx : (resetNativeEquiv q hq).symm v = x :=
    (resetNativeEquiv q hq).symm_apply_apply x
  rw [← hx]
  change resetNativeEquiv q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true)
    (nativeStage q 0 v)) = leftTranslation (Multiplicative.ofAdd true)
      (resetNativeEquiv q hq (nativeStage q 0 v))
  have hs : groupAction (resetMatrix q) (Multiplicative.ofAdd true) (nativeStage q 0 v) =
      nativeStage q 0 (leftTranslation (Multiplicative.ofAdd true) v) := by
    dsimp only [groupAction, induced, nativeStage]
    exact Module.DirectLimit.map_apply_of (R := ℤ) (ι := ℕ)
      (G := fun _ : ℕ => VertexModule Sign q) (G' := fun _ : ℕ => VertexModule Sign q)
      (f := stationaryTransition (transition (resetMatrix q)))
      (f' := stationaryTransition (transition (resetMatrix q))) _ _ v
  rw [hs]
  simp only [nativeStage, resetNativeEquiv_stage, pow_zero, Module.End.one_apply]

private theorem literal_translation (q : ℕ) (v : VertexModule Sign q) :
    leftTranslation (Multiplicative.ofAdd true) v = fun i => v i * resetLabel := by
  funext i
  exact mul_comm resetLabel (v i)

private theorem finite_coefficient (q : ℕ) (hq : 0 < q) (b : QP q) :
    finiteChart q hq (pp q (C resetLabel) * b) =
      leftTranslation (Multiplicative.ofAdd true) (finiteChart q hq b) := by
  change (Module.AEval'.of _).symm
    (D5.S1.Recurrence.FiniteCompanionCyclicModule.cyclicEquiv resetLabel q hq
      ((C resetLabel : R[X]) • b)) = _
  rw [map_smul, Module.AEval.C_smul, literal_translation]
  funext i
  exact mul_comm resetLabel _

private theorem native_label (q : ℕ) (hq : 0 < q) :
    groupAction (resetMatrix q) (Multiplicative.ofAdd true) = aeval (resetTheta q) (W q) := by
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := (nativeIntEquiv q hq).surjective x
  rw [← native_polynomial]
  apply (resetNativeEquiv q hq).injective
  rw [native_coefficient, native_read, native_read, map_mul]
  have hu : (ringEquiv q).symm (fp q (W q)) = pp q (C resetLabel) := by
    apply (ringEquiv q).injective
    rw [RingEquiv.apply_symm_apply]
    exact (literal_presentation q).2.2.2.2.2.1.symm
  rw [hu, finite_coefficient]

/-- Complete original native presentation. The coefficient identity is justified by
stage-zero naturality, and stage n retains the original inverse-time reading. -/
theorem native_presentation (q : ℕ) (hq : 0 < q) :
    nativeIntEquiv q hq 1 = nativeStage q 0
      (D5.S1.Recurrence.FiniteCompanionCyclicModule.e0 q hq) ∧
    (∀ b : QF q, nativeIntEquiv q hq (fp q X * b) = resetTheta q (nativeIntEquiv q hq b)) ∧
    (∀ p : ℤ[X], ∀ b : QF q, nativeIntEquiv q hq (fp q p * b) =
      (aeval (resetTheta q) p) (nativeIntEquiv q hq b)) ∧
    (∀ z : ℤ, ∀ b : QF q, nativeIntEquiv q hq (z • b) = z • nativeIntEquiv q hq b) ∧
    (∀ b : QF q, nativePolynomialEquiv q hq b =
      Module.AEval'.of (resetTheta q) (nativeIntEquiv q hq b)) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q,
      (nativeIntEquiv q hq).symm (nativeStage q n v) = ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
          ((resetInverse q hq ^ n) v)))) ∧
    (∀ x : Native q, resetNativeEquiv q hq
      (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
        leftTranslation (Multiplicative.ofAdd true) (resetNativeEquiv q hq x)) ∧
    groupAction (resetMatrix q) (Multiplicative.ofAdd true) = aeval (resetTheta q) (W q) :=
  ⟨native_one q hq, native_X q hq, native_polynomial q hq,
    fun z b => (nativeIntEquiv q hq).map_smul z b, polynomial_chart q hq,
    native_coordinates q hq, native_coefficient q hq, native_label q hq⟩

/-- The square-time relation, in the original integral polynomial ring. -/
def H : ℤ[X] := X ^ 2 + 1

private abbrev HI : Ideal ℤ[X] := Ideal.span {H}
private abbrev Period := ℤ[X] ⧸ HI
private def hp : ℤ[X] →+* Period := Ideal.Quotient.mk _

private theorem hp_square : hp X ^ 2 = -1 := by
  have h : hp H = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [H, map_add, map_pow, map_one, add_eq_zero_iff_eq_neg] using h

private theorem hp_four : hp X ^ 4 = 1 := by
  calc
    hp X ^ 4 = (hp X ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hp_square]; ring

private theorem sum_four : hp (S 4) = 0 := by
  simp only [S, map_sum, map_pow]
  norm_num [Finset.sum_range_succ, hp_square, pow_succ]
  linear_combination (hp X + 1) * hp_square

private theorem sum_period (q : ℕ) : hp (S (q + 4)) = hp (S q) := by
  simp only [S, Finset.sum_range_add, map_add, map_sum, pow_add, map_mul, map_pow]
  rw [← Finset.mul_sum]
  have h : (∑ i ∈ Finset.range 4, hp X ^ i) = 0 := by
    simpa only [S, map_sum, map_pow] using sum_four
  rw [h, mul_zero, add_zero]

private theorem sum_reduce (q : ℕ) : hp (S q) = hp (S (q % 4)) :=
  (Function.Periodic.map_mod_nat (f := fun n => hp (S n)) sum_period q).symm

private theorem pow_reduce (q : ℕ) : hp (X ^ q) = hp X ^ (q % 4) := by
  rw [map_pow]
  exact pow_eq_pow_mod q hp_four

/-- Literal residues of the integral relation modulo square time. -/
def residueF (r : ℕ) : ℤ[X] :=
  if r = 0 then 1 else if r = 1 then -2 else if r = 2 then 1 - 2 * X else 0

private theorem relation_reduce (q : ℕ) : hp (F q) = hp (residueF (q % 4)) := by
  have htwo : hp (2 : ℤ[X]) = 2 := map_ofNat hp 2
  have hc : hp X ^ 3 = -hp X := by
    calc
      hp X ^ 3 = hp X ^ 2 * hp X := by ring
      _ = -hp X := by rw [hp_square]; ring
  have hr : q % 4 < 4 := Nat.mod_lt q (by decide)
  have hx : hp (X ^ (2 * q)) = (hp X ^ (q % 4)) ^ 2 := by
    rw [show 2 * q = q * 2 by omega, pow_mul, map_pow, pow_reduce]
  change hp (X ^ (2 * q)) - hp (S q) ^ 2 = _
  rw [hx, sum_reduce q]
  interval_cases h : q % 4 <;>
    norm_num [residueF, S, Finset.sum_range_succ, map_sum, map_pow,
      map_mul, hp_square, hc, htwo] <;> linear_combination hp_square

/-- The actual joint ideal before any ring structure is transported to the native group. -/
def joint (q : ℕ) : Ideal ℤ[X] := Ideal.span {F q} ⊔ HI
abbrev SquareRing (q : ℕ) := ℤ[X] ⧸ joint q
def squarePolynomial (q : ℕ) : ℤ[X] →+* SquareRing q := Ideal.Quotient.mk _

private theorem joint_reduce (q : ℕ) :
    joint q = Ideal.span {residueF (q % 4)} ⊔ HI := by
  have hd : F q - residueF (q % 4) ∈ HI := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change hp (F q - residueF (q % 4)) = 0
    rw [map_sub, relation_reduce, sub_self]
  apply le_antisymm
  · apply sup_le
    · apply Ideal.span_le.mpr
      intro p hp'
      rcases Set.mem_singleton_iff.mp hp' with rfl
      have hb : residueF (q % 4) ∈ Ideal.span {residueF (q % 4)} ⊔ HI :=
        (show Ideal.span {residueF (q % 4)} ≤ Ideal.span {residueF (q % 4)} ⊔ HI from le_sup_left)
          (Ideal.subset_span (by simp))
      have hd' := (show HI ≤ Ideal.span {residueF (q % 4)} ⊔ HI from le_sup_right) hd
      simpa using (Ideal.add_mem _ hd' hb)
    · exact le_sup_right
  · apply sup_le
    · apply Ideal.span_le.mpr
      intro p hp'
      rcases Set.mem_singleton_iff.mp hp' with rfl
      have hf : F q ∈ joint q :=
        (show Ideal.span {F q} ≤ joint q from le_sup_left) (Ideal.subset_span (by simp))
      have hd' : F q - residueF (q % 4) ∈ joint q := (show HI ≤ joint q from le_sup_right) hd
      simpa using (Ideal.sub_mem _ hf hd')
    · exact le_sup_right

private theorem five_ideal :
    Ideal.span {(1 - 2 * X : ℤ[X])} ⊔ HI = Ideal.span {C 5, X - C 3} := by
  let J : Ideal ℤ[X] := Ideal.span {C 5, X - C 3}
  let I : Ideal ℤ[X] := Ideal.span {(1 - 2 * X : ℤ[X])} ⊔ HI
  have hF : (1 - 2 * X : ℤ[X]) ∈ I :=
    (show Ideal.span {(1 - 2 * X : ℤ[X])} ≤ I from le_sup_left) (Ideal.subset_span (by simp))
  have hH : H ∈ I := (show HI ≤ I from le_sup_right) (Ideal.subset_span (by simp))
  have h5 : (C 5 : ℤ[X]) ∈ I := by
    have he : (C 5 : ℤ[X]) = 4 * H + (2 * X + 1) * (1 - 2 * X) := by simp [H]; ring
    rw [he]
    exact I.add_mem (I.mul_mem_left _ hH) (I.mul_mem_left _ hF)
  have hX : (X - C 3 : ℤ[X]) ∈ I := by
    have he : (X - C 3 : ℤ[X]) = -3 * (1 - 2 * X) - C 5 * X := by norm_num; ring
    rw [he]
    exact I.sub_mem (I.mul_mem_left _ hF) (I.mul_mem_right _ h5)
  have j5 : (C 5 : ℤ[X]) ∈ J := Ideal.subset_span (by simp)
  have jX : (X - C 3 : ℤ[X]) ∈ J := Ideal.subset_span (by simp)
  apply le_antisymm
  · apply sup_le
    · apply Ideal.span_le.mpr
      intro p hp'
      rcases Set.mem_singleton_iff.mp hp' with rfl
      have he : (1 - 2 * X : ℤ[X]) = -2 * (X - C 3) - C 5 := by norm_num; ring
      rw [he]
      exact J.sub_mem (J.mul_mem_left _ jX) j5
    · apply Ideal.span_le.mpr
      intro p hp'
      rcases Set.mem_singleton_iff.mp hp' with rfl
      have he : H = (X - C 3) * (X + C 3) + 2 * C 5 := by simp [H]; ring
      rw [he]
      exact J.add_mem (J.mul_mem_right _ jX) (J.mul_mem_left _ j5)
  · apply Ideal.span_le.mpr
    intro p hp'
    rcases hp' with rfl | hp'
    · exact h5
    · exact Set.mem_singleton_iff.mp hp' ▸ hX

private theorem joint_zero (q : ℕ) (h : q % 4 = 0) : joint q = ⊤ := by
  rw [joint_reduce, h]
  simp [residueF, Ideal.span_singleton_one]

private theorem joint_one (q : ℕ) (h : q % 4 = 1) :
    joint q = Ideal.span {(2 : ℤ[X])} ⊔ HI := by
  rw [joint_reduce, h]
  simp only [residueF, if_false, if_true, show (1 : ℕ) ≠ 0 by decide]
  rw [Ideal.span_singleton_neg]

private theorem joint_two (q : ℕ) (h : q % 4 = 2) :
    joint q = Ideal.span {C 5, X - C 3} := by
  rw [joint_reduce, h]
  simpa [residueF] using five_ideal

private theorem joint_three (q : ℕ) (h : q % 4 = 3) : joint q = HI := by
  rw [joint_reduce, h]
  simp [residueF]

/-- The original integer endomorphism id+Theta². -/
def nativeSquare (q : ℕ) : Module.End ℤ (Native q) := LinearMap.id + resetTheta q ^ 2

/-- The canonical polynomial projection composed with the actual native chart inverse. -/
def bProjection (q : ℕ) : QF q →+* SquareRing q :=
  (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {F q}) HI).toRingHom.comp
    (Ideal.Quotient.mk (HI.map (Ideal.Quotient.mk (Ideal.span {F q}))))

def squareProjection (q : ℕ) (hq : 0 < q) : Native q →ₗ[ℤ] SquareRing q :=
  (bProjection q).toAddMonoidHom.toIntLinearMap.comp
    (nativeIntEquiv q hq).symm.toLinearMap

private theorem squareProjection_chart (q : ℕ) (hq : 0 < q) (p : ℤ[X]) :
    squareProjection q hq (nativeIntEquiv q hq (fp q p)) = squarePolynomial q p := by
  change DoubleQuot.quotLeftToQuotSup (Ideal.span {F q}) HI
    ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq (fp q p))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem native_square_chart (q : ℕ) (hq : 0 < q) (b : QF q) :
    nativeSquare q (nativeIntEquiv q hq b) = nativeIntEquiv q hq (fp q H * b) := by
  have hx := (native_presentation q hq).2.1
  simp only [nativeSquare, LinearMap.add_apply, LinearMap.id_apply, Module.End.pow_apply,
    pow_two, Module.End.mul_apply]
  rw [← hx, ← hx]
  rw [H, map_add, map_pow, map_one, add_mul, one_mul, pow_two, mul_assoc, map_add]
  abel

private theorem projection_kernel (q : ℕ) (hq : 0 < q) (x : Native q) :
    squareProjection q hq x = 0 ↔ ∃ y : Native q, nativeSquare q y = x := by
  have hm : HI.map (Ideal.Quotient.mk (Ideal.span {F q})) = Ideal.span {fp q H} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hk := DoubleQuot.ker_quotLeftToQuotSup (Ideal.span {F q}) HI
  rw [hm] at hk
  change DoubleQuot.quotLeftToQuotSup (Ideal.span {F q}) HI ((nativeIntEquiv q hq).symm x) = 0 ↔ _
  rw [← RingHom.mem_ker, hk, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨nativeIntEquiv q hq b, ?_⟩
    rw [native_square_chart, mul_comm, hb, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨(nativeIntEquiv q hq).symm y, ?_⟩
    apply (nativeIntEquiv q hq).injective
    rw [LinearEquiv.apply_symm_apply, mul_comm, ← native_square_chart,
      LinearEquiv.apply_symm_apply]

private theorem projection_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (squareProjection q hq) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨nativeIntEquiv q hq (fp q p), squareProjection_chart q hq p⟩

private theorem kernel_eq_range (q : ℕ) (hq : 0 < q) :
    LinearMap.ker (squareProjection q hq) = LinearMap.range (nativeSquare q) := by
  ext x
  exact projection_kernel q hq x

/-- An equivalence of the actual native additive quotient, with its original projection. -/
def nativeSquareEquiv (q : ℕ) (hq : 0 < q) :
    (Native q ⧸ LinearMap.range (nativeSquare q)) ≃ₗ[ℤ] SquareRing q :=
  (Submodule.quotEquivOfEq _ _ (kernel_eq_range q hq).symm).trans
    (LinearMap.quotKerEquivOfSurjective (squareProjection q hq) (projection_surjective q hq))

private abbrev TwoIdeal : Ideal ℤ[X] := Ideal.span {(2 : ℤ[X])} ⊔ HI
private abbrev TwoRing := ℤ[X] ⧸ TwoIdeal
private def tp : ℤ[X] →+* TwoRing := Ideal.Quotient.mk _
abbrev BinaryRing := MonoidAlgebra (ZMod 2) Sign
def binaryTime : BinaryRing := MonoidAlgebra.single oddTau 1

private theorem two_zero : (2 : TwoRing) = 0 := by
  change tp 2 = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_left (Ideal.subset_span (by simp)))

private theorem two_square : tp X * tp X = 1 := by
  have h : tp H = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have h2 := two_zero
  simp only [H, map_add, map_pow, map_one] at h
  rw [pow_two] at h
  linear_combination h - h2

private def binarySign : Sign →* TwoRing where
  toFun h := if h = 1 then 1 else tp X
  map_one' := by simp
  map_mul' h k := by
    rcases ResetFiniteIntegralDefect.sign_cases h with rfl | rfl <;>
      rcases ResetFiniteIntegralDefect.sign_cases k with rfl | rfl
    · simp
    · simp
    · simp
    · simpa [show oddTau * oddTau = (1 : Sign) by decide,
        show oddTau ≠ (1 : Sign) by decide] using two_square.symm

private def binaryCoeff : ZMod 2 →+* TwoRing :=
  (Ideal.Quotient.lift (Ideal.span {(2 : ℤ)}) (Int.castRingHom TwoRing) (by
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    simp only [map_mul, map_ofNat, two_zero, mul_zero])).comp
      (Int.quotientSpanNatEquivZMod 2).symm.toRingHom

private theorem binaryCoeff_int (z : ℤ) : binaryCoeff (z : ZMod 2) = (z : TwoRing) :=
  map_intCast binaryCoeff z

private def binaryBackward : BinaryRing →+* TwoRing :=
  MonoidAlgebra.liftNCRingHom binaryCoeff binarySign (fun _ _ => Commute.all _ _)

private theorem binary_tau_square : binaryTime * binaryTime = 1 := by
  simp [binaryTime, MonoidAlgebra.single_mul_single,
    show oddTau * oddTau = (1 : Sign) by decide, MonoidAlgebra.one_def]

private def binaryEval : ℤ[X] →+* BinaryRing :=
  Polynomial.eval₂RingHom (Int.castRingHom BinaryRing) binaryTime

private theorem binary_two_zero : (2 : BinaryRing) = 0 := by
  rw [MonoidAlgebra.ofNat_def, show (2 : ZMod 2) = 0 by decide, MonoidAlgebra.single_zero]

private def binaryForward : TwoRing →+* BinaryRing :=
  Ideal.Quotient.lift TwoIdeal binaryEval (by
    have h2 : binaryEval 2 = 0 := by rw [map_ofNat]; exact binary_two_zero
    have hh : binaryEval H = 0 := by
      rw [H, map_add, map_pow, map_one]
      have hx : binaryEval X = binaryTime := by simp [binaryEval]
      rw [hx]
      rw [pow_two, binary_tau_square]
      simpa only [one_add_one_eq_two] using binary_two_zero
    have hk : TwoIdeal ≤ RingHom.ker binaryEval := sup_le
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h2))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hh))
    exact hk)

private theorem binary_forward_backward :
    binaryForward.comp binaryBackward = RingHom.id BinaryRing := by
  apply MonoidAlgebra.ringHom_ext
  · intro a
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
    change binaryForward (binaryBackward (MonoidAlgebra.single 1 (z : ZMod 2))) = _
    rw [binaryBackward, MonoidAlgebra.liftNCRingHom_single, map_one, mul_one, binaryCoeff_int]
    change binaryForward (z : TwoRing) = MonoidAlgebra.single 1 (z : ZMod 2)
    rw [map_intCast]
    exact (map_intCast (MonoidAlgebra.singleOneRingHom : ZMod 2 →+* BinaryRing) z).symm
  · intro h
    rcases ResetFiniteIntegralDefect.sign_cases h with rfl | rfl
    · simp [← MonoidAlgebra.one_def]
    · change binaryForward (binaryBackward binaryTime) = binaryTime
      simp [binaryBackward, binaryTime, binarySign,
        show oddTau ≠ (1 : Sign) by decide, binaryForward, tp, binaryEval]

private theorem binary_backward_forward :
    binaryBackward.comp binaryForward = RingHom.id TwoRing := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro z
    have hz : C z = (z : ℤ[X]) := map_intCast (C : ℤ →+* ℤ[X]) z
    simp only [RingHom.comp_apply, hz, map_intCast]
  · change binaryBackward (binaryForward (tp X)) = tp X
    simp [binaryForward, tp, binaryEval, binaryTime, binaryBackward, binarySign,
      show oddTau ≠ (1 : Sign) by decide]

private def binaryEquiv : TwoRing ≃+* BinaryRing :=
  RingEquiv.ofRingHom binaryForward binaryBackward binary_forward_backward binary_backward_forward

private def gaussianEval : ℤ[X] →+* GaussianInt :=
  Polynomial.eval₂RingHom (Int.castRingHom GaussianInt) Zsqrtd.sqrtd

private def gaussianForward : Period →+* GaussianInt :=
  Ideal.Quotient.lift HI gaussianEval (by
    intro p hp'
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp'
    rw [map_mul]
    have h : gaussianEval H = 0 := by
      simp [H, gaussianEval, pow_two, Zsqrtd.dmuld]
    rw [h, mul_zero])

private def gaussianBackward : GaussianInt →+* Period :=
  Zsqrtd.lift ⟨hp X, by simpa only [pow_two, Int.cast_neg, Int.cast_one] using hp_square⟩

private theorem gaussian_forward_backward :
    gaussianForward.comp gaussianBackward = RingHom.id GaussianInt := by
  apply Zsqrtd.hom_ext
  simp [gaussianBackward, gaussianForward, hp, gaussianEval, Zsqrtd.sqrtd]

private theorem gaussian_backward_forward :
    gaussianBackward.comp gaussianForward = RingHom.id Period := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro z
    have hz : C z = (z : ℤ[X]) := map_intCast (C : ℤ →+* ℤ[X]) z
    simp only [RingHom.comp_apply, hz, map_intCast]
  · change gaussianBackward (gaussianForward (hp X)) = hp X
    simp [gaussianBackward, gaussianForward, hp, gaussianEval, Zsqrtd.sqrtd]

private def gaussianEquiv : Period ≃+* GaussianInt :=
  RingEquiv.ofRingHom gaussianForward gaussianBackward
    gaussian_forward_backward gaussian_backward_forward

/-- The zero ring chart in residue zero, with its actual inverse. -/
def zeroChart (q : ℕ) (h : q % 4 = 0) : SquareRing q ≃+* ZMod 1 :=
  (Ideal.quotEquivOfEq (joint_zero q h)).trans
    (by letI : Unique (ℤ[X] ⧸ (⊤ : Ideal ℤ[X])) :=
          ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
        exact RingEquiv.ofUnique)

/-- The literal F₂[Sign] chart; time is the nonidentity basis element. -/
def binaryChart (q : ℕ) (h : q % 4 = 1) : SquareRing q ≃+* BinaryRing :=
  (Ideal.quotEquivOfEq (joint_one q h)).trans binaryEquiv

/-- The integral five-chart, oriented by X=3. -/
def fiveChart (q : ℕ) (h : q % 4 = 2) : SquareRing q ≃+* ZMod 5 :=
  (Ideal.quotEquivOfEq (joint_two q h)).trans
    ((Polynomial.quotientSpanCXSubCAlgEquiv (5 : ℤ) 3).toRingEquiv.trans
      (Int.quotientSpanNatEquivZMod 5))

/-- The Gaussian chart with X=i, rather than its conjugate. -/
def gaussianChart (q : ℕ) (h : q % 4 = 3) : SquareRing q ≃+* GaussianInt :=
  (Ideal.quotEquivOfEq (joint_three q h)).trans gaussianEquiv

/-- The four literal arithmetic rings in residue order. -/
abbrev Target : ℕ → Type
  | 0 => ZMod 1
  | 1 => BinaryRing
  | 2 => ZMod 5
  | _ + 3 => GaussianInt

instance targetCommRing : (r : ℕ) → CommRing (Target r)
  | 0 => inferInstanceAs (CommRing (ZMod 1))
  | 1 => inferInstanceAs (CommRing BinaryRing)
  | 2 => inferInstanceAs (CommRing (ZMod 5))
  | _ + 3 => inferInstanceAs (CommRing GaussianInt)

/-- The distinguished forward-time element in each arithmetic ring. -/
def targetTime : (r : ℕ) → Target r
  | 0 => 1
  | 1 => binaryTime
  | 2 => 3
  | _ + 3 => Zsqrtd.sqrtd

/-- The literal coefficient involution in each arithmetic ring. -/
def targetLabel : (r : ℕ) → Target r
  | 0 => 1
  | 1 => binaryTime
  | 2 => 1
  | _ + 3 => -1

private def chartAt (q : ℕ) : (r : ℕ) → q % 4 = r → SquareRing q ≃+* Target r
  | 0, h => zeroChart q h
  | 1, h => binaryChart q h
  | 2, h => fiveChart q h
  | _ + 3, h => gaussianChart q (by omega)

/-- Actual inverse ring maps, with the orientation fixed by original forward time. -/
def arithmeticChart (q : ℕ) : SquareRing q ≃+* Target (q % 4) := chartAt q (q % 4) rfl

private theorem chartAt_X (q : ℕ) : (r : ℕ) → (h : q % 4 = r) →
    chartAt q r h (squarePolynomial q X) = targetTime r
  | 0, _ => Subsingleton.elim _ _
  | 1, h => by
    simp [chartAt, targetTime, binaryChart, binaryEquiv, binaryForward, squarePolynomial, binaryEval]
  | 2, h => by
    have hx : squarePolynomial q (X - C 3) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [joint_two q h]
      exact Ideal.subset_span (by simp)
    have hx' : squarePolynomial q X = 3 := by
      simpa only [map_sub, C_ofNat, map_ofNat, sub_eq_zero] using hx
    change fiveChart q h (squarePolynomial q X) = 3
    rw [hx', map_ofNat]
  | _ + 3, _ => by
    simp [chartAt, targetTime, gaussianChart, gaussianEquiv, gaussianForward, squarePolynomial,
      gaussianEval]

private theorem arithmetic_X (q : ℕ) :
    arithmeticChart q (squarePolynomial q X) = targetTime (q % 4) := chartAt_X q _ rfl

private theorem chart_polynomial {A : Type*} [CommRing A] (q : ℕ)
    (c : SquareRing q ≃+* A) (t : A) (hx : c (squarePolynomial q X) = t) (p : ℤ[X]) :
    c (squarePolynomial q p) = p.eval₂ (Int.castRingHom A) t := by
  have hh : c.toRingHom.comp (squarePolynomial q) = Polynomial.eval₂RingHom (Int.castRingHom A) t := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : C z = (z : ℤ[X]) := C_eq_intCast z
      simp only [RingHom.comp_apply, hz, map_intCast]
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X]
      exact hx
  exact RingHom.congr_fun hh p

private theorem arithmetic_polynomial (q : ℕ) (p : ℤ[X]) :
    arithmeticChart q (squarePolynomial q p) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4)) :=
  chart_polynomial q (arithmeticChart q) _ (arithmetic_X q) p

private def residueW (r : ℕ) : ℤ[X] :=
  if r = 0 then 1 - X else if r = 1 then 2 + X else if r = 2 then 2 * X else -1

private theorem label_reduce (q : ℕ) : hp (W q) = hp (residueW (q % 4)) := by
  have hc : hp X ^ 3 = -hp X := by
    calc
      hp X ^ 3 = hp X ^ 2 * hp X := by ring
      _ = -hp X := by rw [hp_square]; ring
  have htwo : hp (2 : ℤ[X]) = 2 := map_ofNat hp 2
  change hp (S q) - hp (X - 1) * hp (X ^ q) = _
  rw [sum_reduce, pow_reduce]
  have hr : q % 4 < 4 := Nat.mod_lt q (by decide)
  interval_cases h : q % 4 <;>
    norm_num [residueW, S, Finset.sum_range_succ, map_sum, map_pow, map_mul,
      hp_square, hc, htwo]
  all_goals ring_nf
  all_goals try rw [hp_square]
  all_goals ring

private theorem chartAt_label (q r : ℕ) (h : q % 4 = r) :
    chartAt q r h (squarePolynomial q (residueW r)) = targetLabel r := by
  rw [chart_polynomial q (chartAt q r h) _ (chartAt_X q r h)]
  rcases r with _ | _ | _ | r
  · exact Subsingleton.elim _ _
  · change (2 + X : ℤ[X]).eval₂ (Int.castRingHom BinaryRing) binaryTime = binaryTime
    rw [eval₂_add, eval₂_X]
    have h2 : (2 : ℤ[X]).eval₂ (Int.castRingHom BinaryRing) binaryTime = 2 :=
      map_ofNat (Polynomial.eval₂RingHom (Int.castRingHom BinaryRing) binaryTime) 2
    rw [h2, binary_two_zero, zero_add]
  · change (2 * X : ℤ[X]).eval₂ (Int.castRingHom (ZMod 5)) 3 = 1
    rw [eval₂_mul, eval₂_X]
    have h2 : (2 : ℤ[X]).eval₂ (Int.castRingHom (ZMod 5)) 3 = 2 :=
      map_ofNat (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 5)) 3) 2
    rw [h2]
    decide
  · have h0 : r + 3 ≠ 0 := by omega
    have h1 : r + 3 ≠ 1 := by omega
    have h2 : r + 3 ≠ 2 := by omega
    simp [residueW, h0, h1, h2, targetLabel]

private theorem arithmetic_label (q : ℕ) :
    arithmeticChart q (squarePolynomial q (W q)) = targetLabel (q % 4) := by
  have hd : W q - residueW (q % 4) ∈ HI := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change hp (W q - residueW (q % 4)) = 0
    rw [map_sub, label_reduce, sub_self]
  have hw : squarePolynomial q (W q) = squarePolynomial q (residueW (q % 4)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hd)
  rw [hw]
  exact chartAt_label q _ rfl

/-- The oriented arithmetic readout on the original integer dimension group. -/
def eta (q : ℕ) (hq : 0 < q) : Native q →ₗ[ℤ] Target (q % 4) :=
  (arithmeticChart q).toAddEquiv.toIntLinearEquiv.toLinearMap.comp (squareProjection q hq)

private theorem eta_chart (q : ℕ) (hq : 0 < q) (b : QF q) :
    eta q hq (nativeIntEquiv q hq b) = arithmeticChart q (bProjection q b) := by
  change arithmeticChart q (bProjection q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq b))) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem eta_polynomial (q : ℕ) (hq : 0 < q) (p : ℤ[X]) (x : Native q) :
    eta q hq ((aeval (resetTheta q) p) x) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4)) * eta q hq x := by
  obtain ⟨b, rfl⟩ := (nativeIntEquiv q hq).surjective x
  rw [← (native_presentation q hq).2.2.1, eta_chart, eta_chart, map_mul, map_mul]
  have h : bProjection q (fp q p) = squarePolynomial q p := rfl
  rw [h, arithmetic_polynomial]

/-- The original distinguished stage-zero vector. -/
def generator (q : ℕ) (hq : 0 < q) : Native q :=
  nativeStage q 0 (D5.S1.Recurrence.FiniteCompanionCyclicModule.e0 q hq)

private theorem eta_one (q : ℕ) (hq : 0 < q) : eta q hq (generator q hq) = 1 := by
  rw [generator, ← (native_presentation q hq).1, eta_chart, map_one, map_one]

private theorem eta_time (q : ℕ) (hq : 0 < q) (x : Native q) :
    eta q hq (resetTheta q x) = targetTime (q % 4) * eta q hq x := by
  simpa only [aeval_X, eval₂_X] using eta_polynomial q hq X x

private theorem eta_label (q : ℕ) (hq : 0 < q) (x : Native q) :
    eta q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
      targetLabel (q % 4) * eta q hq x := by
  rw [(native_presentation q hq).2.2.2.2.2.2.2]
  rw [eta_polynomial, ← arithmetic_polynomial, arithmetic_label]

private theorem eta_kernel (q : ℕ) (hq : 0 < q) (x : Native q) :
    eta q hq x = 0 ↔ ∃ y : Native q, nativeSquare q y = x := by
  change arithmeticChart q (squareProjection q hq x) = 0 ↔ _
  rw [← (arithmeticChart q).map_zero, (arithmeticChart q).injective.eq_iff, projection_kernel]

private theorem eta_surjective (q : ℕ) (hq : 0 < q) : Function.Surjective (eta q hq) :=
  (arithmeticChart q).surjective.comp (projection_surjective q hq)

abbrev NativeSquare (q : ℕ) := Native q ⧸ LinearMap.range (nativeSquare q)

/-- Only the proved quotient equivalence transports a ring to the original additive quotient. -/
abbrev nativeSquareRing (q : ℕ) (hq : 0 < q) : CommRing (NativeSquare q) :=
  (nativeSquareEquiv q hq).toEquiv.commRing

/-- The transported ring chart; its additive operations agree with the original quotient. -/
def nativeArithmeticEquiv (q : ℕ) (hq : 0 < q) :
    letI := nativeSquareRing q hq
    NativeSquare q ≃+* Target (q % 4) := by
  letI := nativeSquareRing q hq
  exact (nativeSquareEquiv q hq).toEquiv.ringEquiv.trans (arithmeticChart q)

private theorem nativeArithmetic_mk (q : ℕ) (hq : 0 < q) (x : Native q) :
    nativeArithmeticEquiv q hq ((LinearMap.range (nativeSquare q)).mkQ x) = eta q hq x := by
  change arithmeticChart q (nativeSquareEquiv q hq (Submodule.Quotient.mk x)) = _
  rfl

private theorem eta_stage (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q) :
    eta q hq (nativeStage q n v) = arithmeticChart q (bProjection q
      (ringEquiv q (pp q (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial
        resetLabel q ((resetInverse q hq ^ n) v))))) := by
  change arithmeticChart q (bProjection q ((nativeIntEquiv q hq).symm (nativeStage q n v))) = _
  rw [(native_presentation q hq).2.2.2.2.2.1]

private theorem nativeArithmetic_add (q : ℕ) (hq : 0 < q) (x y : NativeSquare q) :
    nativeArithmeticEquiv q hq (x + y) = nativeArithmeticEquiv q hq x + nativeArithmeticEquiv q hq y := by
  change arithmeticChart q (nativeSquareEquiv q hq (x + y)) =
    arithmeticChart q (nativeSquareEquiv q hq x) + arithmeticChart q (nativeSquareEquiv q hq y)
  rw [map_add, map_add]

/-- The forward-shift exponent bound in each arithmetic target. -/
def targetBound : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ + 2 => 4

/-- The distinguished time unit, with its literal integral inverse. -/
def targetTimeUnit : (r : ℕ) → (Target r)ˣ
  | 0 => 1
  | 1 => ⟨binaryTime, binaryTime, binary_tau_square, binary_tau_square⟩
  | 2 => ⟨3, 2, by decide, by decide⟩
  | _ + 3 => ⟨Zsqrtd.sqrtd, -Zsqrtd.sqrtd,
      by simp [Zsqrtd.dmuld], by simp [Zsqrtd.dmuld]⟩

theorem targetTimeUnit_val (r : ℕ) :
    (targetTimeUnit r : Target r) = targetTime r := by
  rcases r with _ | _ | _ | r <;> rfl

private theorem binary_expand (a : BinaryRing) :
    a = MonoidAlgebra.single 1 (a.coeff 1) + MonoidAlgebra.single oddTau (a.coeff oddTau) := by
  ext h
  rcases ResetFiniteIntegralDefect.sign_cases h with rfl | rfl <;>
    simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
      show oddTau ≠ (1 : Sign) by decide]

private def binaryAug : BinaryRing →+* ZMod 2 :=
  MonoidAlgebra.liftNCRingHom (RingHom.id _) (1 : Sign →* ZMod 2)
    (fun _ _ => Commute.all _ _)

private theorem binary_unit (u : BinaryRingˣ) :
    (u : BinaryRing) = 1 ∨ (u : BinaryRing) = binaryTime := by
  have hu : IsUnit (binaryAug (u : BinaryRing)) := u.isUnit.map binaryAug
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have ha : binaryAug (u : BinaryRing) = 1 := by
    rcases hc (binaryAug (u : BinaryRing)) with h | h
    · exact (hu.ne_zero h).elim
    · exact h
  have hs : (u : BinaryRing).coeff 1 + (u : BinaryRing).coeff oddTau = 1 := by
    rw [binary_expand (u : BinaryRing)] at ha
    simpa [binaryAug] using ha
  rcases hc ((u : BinaryRing).coeff 1) with h0 | h0
  · rcases hc ((u : BinaryRing).coeff oddTau) with ht | ht
    · have h : (0 : ZMod 2) + 0 = 1 := by simpa only [h0, ht] using hs
      exact ((by decide : (0 : ZMod 2) + 0 ≠ 1) h).elim
    · right
      exact (binary_expand (u : BinaryRing)).trans (by simp [h0, ht, binaryTime])
  · rcases hc ((u : BinaryRing).coeff oddTau) with ht | ht
    · left
      exact (binary_expand (u : BinaryRing)).trans (by simp [h0, ht, MonoidAlgebra.one_def])
    · have h : (1 : ZMod 2) + 1 = 1 := by simpa only [h0, ht] using hs
      exact ((by decide : (1 : ZMod 2) + 1 ≠ 1) h).elim

private theorem gaussian_unit (u : GaussianIntˣ) :
    (u : GaussianInt) = 1 ∨ (u : GaussianInt) = Zsqrtd.sqrtd ∨
      (u : GaussianInt) = -1 ∨ (u : GaussianInt) = -Zsqrtd.sqrtd := by
  have hn : (u : GaussianInt).re ^ 2 + (u : GaussianInt).im ^ 2 = 1 := by
    have h := (Zsqrtd.norm_eq_one_iff' (d := -1) (by decide) (u : GaussianInt)).mpr u.isUnit
    simpa [Zsqrtd.norm, pow_two] using h
  have hr : -1 ≤ (u : GaussianInt).re ∧ (u : GaussianInt).re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).im]
  have hi : -1 ≤ (u : GaussianInt).im ∧ (u : GaussianInt).im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re]
  generalize hre : (u : GaussianInt).re = a at hn hr
  generalize him : (u : GaussianInt).im = b at hn hi
  rcases hr with ⟨ha0, ha1⟩
  rcases hi with ⟨hb0, hb1⟩
  interval_cases a <;> interval_cases b <;> norm_num at hn
  all_goals solve
    | (left; ext <;> simp_all [Zsqrtd.sqrtd])
    | (right; left; ext <;> simp_all [Zsqrtd.sqrtd])
    | (right; right; left; ext <;> simp_all [Zsqrtd.sqrtd])
    | (right; right; right; ext <;> simp_all [Zsqrtd.sqrtd])

private theorem five_unit_power (u : (ZMod 5)ˣ) :
    ∃ n : Fin 4, (3 : ZMod 5) ^ n.val = (u : ZMod 5) := by
  letI : Fact (1 < (5 : ℕ)) := ⟨by decide⟩
  have h : ∀ c : ZMod 5, c ≠ 0 → ∃ n : Fin 4, (3 : ZMod 5) ^ n.val = c := by decide
  exact h u u.isUnit.ne_zero

private theorem target_unit_power : (r : ℕ) → (u : (Target r)ˣ) →
    ∃ n : ℕ, n < targetBound r ∧ targetTime r ^ n = (u : Target r)
  | 0, _ => ⟨0, by decide, Subsingleton.elim _ _⟩
  | 1, u => by
    rcases binary_unit u with h | h
    · exact ⟨0, by norm_num [targetBound], by simpa [targetTime] using h.symm⟩
    · exact ⟨1, by norm_num [targetBound], by simpa [targetTime] using h.symm⟩
  | 2, u => by
    obtain ⟨n, hn⟩ := five_unit_power u
    exact ⟨n.val, n.isLt, hn⟩
  | _ + 3, u => by
    rcases gaussian_unit u with h | h | h | h
    · exact ⟨0, by norm_num [targetBound], by simpa [targetTime] using h.symm⟩
    · exact ⟨1, by norm_num [targetBound], by simpa [targetTime] using h.symm⟩
    · refine ⟨2, by norm_num [targetBound], ?_⟩
      simpa [targetTime, pow_two, Zsqrtd.dmuld] using h.symm
    · refine ⟨3, by norm_num [targetBound], ?_⟩
      simpa [targetTime, pow_succ, Zsqrtd.dmuld] using h.symm

private theorem native_shift_power (q : ℕ) (hq : 0 < q) (n : ℕ) (x : Native q) :
    eta q hq (ResetFullStandardBeamRepresentation.rho q hq
      (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q) ^ n) x) =
      targetTime (q % 4) ^ n * eta q hq x := by
  rw [map_pow, LinearEquiv.pow_apply]
  have hx : ⇑(ResetFullStandardBeamRepresentation.rho q hq
      (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q))) =
      ⇑(resetTheta q) :=
    funext (fun z => LinearMap.congr_fun
      (ResetFullStandardBeamRepresentation.rho_unitShift q hq) z)
  rw [hx, ← Module.End.pow_apply]
  simpa only [map_pow, aeval_X, eval₂_pow, eval₂_X] using eta_polynomial q hq (X ^ n) x

private theorem native_unit_generation (q : ℕ) (hq : 0 < q) (u : (Target (q % 4))ˣ) :
    ∃ n : ℕ, n < targetBound (q % 4) ∧
      targetTimeUnit (q % 4) ^ n = u ∧
      eta q hq (ResetFullStandardBeamRepresentation.rho q hq
        (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q) ^ n)
        (generator q hq)) = (u : Target (q % 4)) := by
  obtain ⟨n, hn, hu⟩ := target_unit_power (q % 4) u
  refine ⟨n, hn, ?_, by rw [native_shift_power, eta_one, mul_one, hu]⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, targetTimeUnit_val] using hu

/-- The original native square quotient, its four inverse integral ring charts, and
the canonical projection with literal time, coefficient and inverse-stage laws,
and bounded generation by actual numbered-history forward shifts. -/
theorem native_square_arithmetic (q : ℕ) (hq : 0 < q) :
    (∀ b : QF q, nativeSquare q (nativeIntEquiv q hq b) = nativeIntEquiv q hq (fp q H * b)) ∧
    (∀ x : Native q, eta q hq x = 0 ↔ ∃ y : Native q, nativeSquare q y = x) ∧
    Function.Surjective (eta q hq) ∧
    (∀ x : Native q, nativeArithmeticEquiv q hq ((LinearMap.range (nativeSquare q)).mkQ x) = eta q hq x) ∧
    (∀ x y : NativeSquare q, nativeArithmeticEquiv q hq (x + y) =
      nativeArithmeticEquiv q hq x + nativeArithmeticEquiv q hq y) ∧
    eta q hq (generator q hq) = 1 ∧
    (∀ p : ℤ[X], ∀ x : Native q, eta q hq ((aeval (resetTheta q) p) x) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4)) * eta q hq x) ∧
    (∀ x : Native q, eta q hq (resetTheta q x) = targetTime (q % 4) * eta q hq x) ∧
    (∀ x : Native q, eta q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) =
      targetLabel (q % 4) * eta q hq x) ∧
    (∀ n : ℕ, ∀ v : VertexModule Sign q, eta q hq (nativeStage q n v) =
      arithmeticChart q (bProjection q (ringEquiv q (pp q
        (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial
          resetLabel q ((resetInverse q hq ^ n) v)))))) ∧
    (∀ p : ℤ[X], arithmeticChart q (squarePolynomial q p) =
      p.eval₂ (Int.castRingHom (Target (q % 4))) (targetTime (q % 4))) ∧
    joint q = Ideal.span {residueF (q % 4)} ⊔ HI ∧
    (∀ u : (Target (q % 4))ˣ, ∃ n : ℕ, n < targetBound (q % 4) ∧
      targetTimeUnit (q % 4) ^ n = u ∧
      eta q hq (ResetFullStandardBeamRepresentation.rho q hq
        (StandardBeamHomeomorphisms.unitShift (ResetStandardBeamGeometry.ResetGraph q) ^ n)
        (generator q hq)) = (u : Target (q % 4))) :=
  ⟨native_square_chart q hq, eta_kernel q hq, eta_surjective q hq,
    nativeArithmetic_mk q hq, nativeArithmetic_add q hq, eta_one q hq,
    eta_polynomial q hq, eta_time q hq, eta_label q hq, eta_stage q hq,
    arithmetic_polynomial q, joint_reduce q, native_unit_generation q hq⟩

end D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
