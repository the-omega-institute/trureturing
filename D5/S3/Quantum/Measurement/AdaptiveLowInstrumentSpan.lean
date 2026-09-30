/- GID: D5/S3/Quantum/Measurement/AdaptiveLowInstrumentSpan
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/AdaptiveLowInstrumentSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adaptive low-instrument events span the least forward-unitary invariant algebra. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
  NonUnitalContinuousFunctionalCalculus

namespace D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

variable {a j : Type*} [Fintype a] [DecidableEq a]
  [Fintype j] [DecidableEq j]

/-- A finite low instrument retains its outcome and sums its hidden Kraus index. -/
structure LowInstrument (a : Type*) [Fintype a] [DecidableEq a] where
  outcomes : ℕ
  multiplicity : ℕ
  kraus : Fin outcomes → Fin multiplicity → CStarMatrix a a ℂ
  complete : ∑ y, ∑ r, star (kraus y r) * kraus y r = 1

/-- An event marks the accepted leaves of a finite adaptive protocol. -/
inductive Event (a : Type*) [Fintype a] [DecidableEq a] where
  | stop : Bool → Event a
  | tick : Event a → Event a
  | observe : (instrument : LowInstrument a) →
      (Fin instrument.outcomes → Event a) → Event a

/-- The joint low action is the literal tensor product with the high identity. -/
def tensorLow (h : Type*) [Fintype h] [DecidableEq h] :
    CStarMatrix a a ℂ →⋆ₐ[ℂ] CStarMatrix (a × h) (a × h) ℂ := by
  let f : Matrix a a ℂ →⋆ₐ[ℂ] Matrix (a × h) (a × h) ℂ :=
    { toFun K := Matrix.kronecker K (1 : Matrix h h ℂ)
      map_zero' := Matrix.zero_kronecker _
      map_one' := Matrix.one_kronecker_one
      map_add' K L := Matrix.add_kronecker K L _
      map_mul' K L := by
        simpa only [one_mul, Matrix.kronecker] using Matrix.mul_kronecker_mul K L
          (1 : Matrix h h ℂ) (1 : Matrix h h ℂ)
      commutes' z := by
        ext ⟨b, u⟩ ⟨c, v⟩
        by_cases hbc : b = c <;> by_cases huv : u = v <;>
          simp [Algebra.algebraMap_eq_smul_one, Matrix.kronecker,
            Matrix.kroneckerMap, Matrix.one_apply, Prod.mk.injEq, hbc, huv]
      map_star' K := by simp [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_kronecker] }
  exact CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (f.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

/-- The Heisenberg recursion uses one forward gate and the actual low branches. -/
def effect (low : CStarMatrix a a ℂ →⋆ₐ[ℂ] CStarMatrix j j ℂ)
    (W : CStarMatrix j j ℂ) : Event a → CStarMatrix j j ℂ
  | .stop accepted => if accepted then 1 else 0
  | .tick next => star W * effect low W next * W
  | .observe I next => ∑ y, ∑ r,
      star (low (I.kraus y r)) * effect low W (next y) * low (I.kraus y r)

/-- The Schrödinger recursion sums exactly the accepted branch substates. -/
def eventState (low : CStarMatrix a a ℂ →⋆ₐ[ℂ] CStarMatrix j j ℂ)
    (W : CStarMatrix j j ℂ) : Event a → CStarMatrix j j ℂ → CStarMatrix j j ℂ
  | .stop accepted, rho => if accepted then rho else 0
  | .tick next, rho => eventState low W next (W * rho * star W)
  | .observe I next, rho => ∑ y, ∑ r,
      eventState low W (next y)
        (low (I.kraus y r) * rho * star (low (I.kraus y r)))

/-- The complex span is defined from actual event effects. -/
def effectSpan (low : CStarMatrix a a ℂ →⋆ₐ[ℂ] CStarMatrix j j ℂ)
    (W : CStarMatrix j j ℂ) : Submodule ℂ (CStarMatrix j j ℂ) :=
  Submodule.span ℂ (Set.range (effect low W))

/-- Actual effects form the least invariant star algebra. Inverse conjugation is
a consequence of finite-dimensional injectivity, not an allowed event action. -/
theorem actual_adaptive_span
    {h : Type*} [Fintype h] [DecidableEq h] [Nonempty a] [Nonempty h]
    (W : CStarMatrix (a × h) (a × h) ℂ)
    (hW : star W * W = 1 ∧ W * star W = 1) :
    (∀ e rho, Matrix.trace (eventState (tensorLow h) W e rho) =
      Matrix.trace (effect (tensorLow h) W e * rho)) ∧
    (∀ e, 0 ≤ effect (tensorLow h) W e ∧ effect (tensorLow h) W e ≤ 1) ∧
    ∃ D : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
      D.toSubalgebra.toSubmodule = effectSpan (tensorLow h) W ∧
      (∀ K, tensorLow h K ∈ D) ∧
      (∀ X, X ∈ D ↔ star W * X * W ∈ D) ∧
      (∀ R : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
        (∀ K, tensorLow h K ∈ R) →
        (∀ X ∈ R, star W * X * W ∈ R) → D ≤ R) := by
  let low := tensorLow (a := a) h
  classical
  have : FiniteDimensional ℂ (CStarMatrix (a × h) (a × h) ℂ) :=
    (CStarMatrix.ofMatrixStarAlgEquiv
      (n := a × h) (A := ℂ)).toAlgEquiv.toLinearEquiv.finiteDimensional
  let S := effectSpan low W
  have generator (e : Event a) : effect low W e ∈ S :=
    Submodule.subset_span ⟨e, rfl⟩
  have oneS : (1 : CStarMatrix (a × h) (a × h) ℂ) ∈ S := generator (.stop true)
  have bounds : ∀ e : Event a, 0 ≤ effect low W e ∧ effect low W e ≤ 1 := by
    intro e
    induction e with
    | stop accepted => cases accepted <;> simp [effect]
    | tick next ih =>
        refine ⟨star_left_conjugate_nonneg ih.1 W, ?_⟩
        simpa only [effect, mul_one, hW.1] using star_left_conjugate_le_conjugate ih.2 W
    | observe I next ih =>
        have hcomp : ∑ y, ∑ r, star (low (I.kraus y r)) * low (I.kraus y r) = 1 := by
          simpa only [map_sum, map_mul, map_star, map_one] using congrArg low I.complete
        refine ⟨Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun r _ =>
          star_left_conjugate_nonneg (ih y).1 _)), ?_⟩
        rw [effect, ← hcomp]
        exact Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun r _ => by
          simpa only [mul_one] using
            star_left_conjugate_le_conjugate (ih y).2 (low (I.kraus y r))))
  have duality : ∀ (e : Event a) (rho : CStarMatrix (a × h) (a × h) ℂ),
      Matrix.trace (eventState low W e rho) = Matrix.trace (effect low W e * rho) := by
    let m := (CStarMatrix.ofMatrixStarAlgEquiv (n := a × h) (A := ℂ)).symm.toAlgEquiv
    let tr : CStarMatrix (a × h) (a × h) ℂ →ₗ[ℂ] ℂ :=
      (Matrix.traceLinearMap (a × h) ℂ ℂ).comp m.toLinearMap
    have cyclic (X Y Z : CStarMatrix (a × h) (a × h) ℂ) : tr (X * Y * Z) = tr (Z * X * Y) := by
      change Matrix.trace (m (X * Y * Z)) = Matrix.trace (m (Z * X * Y))
      simp only [map_mul]
      exact Matrix.trace_mul_cycle (m X) (m Y) (m Z)
    change ∀ e rho, tr (eventState low W e rho) = tr (effect low W e * rho)
    intro e
    induction e with
    | stop accepted => intro rho; cases accepted <;> simp [eventState, effect]
    | tick next ih =>
        intro rho
        rw [eventState, ih, effect]
        simpa only [mul_assoc] using cyclic (effect low W next * W) rho (star W)
    | observe I next ih =>
        intro rho
        simp only [eventState, effect, Finset.sum_mul, map_sum]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro r _
        rw [ih]
        simpa only [mul_assoc] using cyclic
          (effect low W (next y) * low (I.kraus y r)) rho (star (low (I.kraus y r)))
  have starS : ∀ X ∈ S, star X ∈ S := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨e, rfl⟩ := hX
        rw [(bounds e).1.isSelfAdjoint.star_eq]
        exact generator e
    | zero => simpa using S.zero_mem
    | add X Y _ _ hX hY => simpa using S.add_mem hX hY
    | smul z X _ hX => simpa using S.smul_mem (star z) hX
  have filterS (K : CStarMatrix a a ℂ) :
      ∀ X ∈ S, star (low K) * X * low K ∈ S := by
    let : NonUnitalContinuousFunctionalCalculus ℂ (CStarMatrix a a ℂ) IsStarNormal :=
      (IsStarNormal.instNonUnitalContinuousFunctionalCalculus
        (A := CStarMatrix a a ℂ)).toNonUnitalContinuousFunctionalCalculus
    let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix a a ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    let : NonnegSpectrumClass ℝ (CStarMatrix a a ℂ) :=
      CStarAlgebra.instNonnegSpectrumClass'
    let eps : ℂ := ((‖K‖ + 1)⁻¹ : ℝ)
    have hepspos : 0 < (‖K‖ + 1)⁻¹ := inv_pos.mpr (by positivity)
    have heps : eps ≠ 0 := by
      dsimp [eps]
      exact_mod_cast (ne_of_gt hepspos)
    let Z := eps • K
    have hnorm : ‖Z‖ ≤ 1 := by
      rw [show ‖Z‖ = (‖K‖ + 1)⁻¹ * ‖K‖ by
        simp only [Z, norm_smul, eps, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hepspos]]
      rw [inv_mul_le_iff₀ (by positivity : 0 < ‖K‖ + 1)]
      linarith
    have hdefect : 0 ≤ (1 : CStarMatrix a a ℂ) - star Z * Z := by
      apply sub_nonneg.mpr
      apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star Z * Z)
        (star_mul_self_nonneg Z)).mp
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg Z]
    let F := CFC.sqrt ((1 : CStarMatrix a a ℂ) - star Z * Z)
    have hF : star F * F = (1 : CStarMatrix a a ℂ) - star Z * Z := by
      dsimp [F]
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,
        CFC.sqrt_mul_sqrt_self _ hdefect]
    let I : LowInstrument a :=
      { outcomes := 2
        multiplicity := 1
        kraus := fun y _ => if y = 0 then Z else F
        complete := by
          simp only [Fin.sum_univ_two, Fin.sum_univ_one]
          change star Z * Z + star F * F = 1
          rw [hF]
          abel }
    have hgen (e : Event a) : star (low K) * effect low W e * low K ∈ S := by
      have h := generator (.observe I (fun y => if y = 0 then e else .stop false))
      have heffect : effect low W (.observe I (fun y => if y = 0 then e else .stop false)) =
          (star eps * eps) • (star (low K) * effect low W e * low K) := by
        simp [effect, I, Z, map_smul, star_smul, smul_smul, Fin.sum_univ_two, mul_comm]
      rw [heffect] at h
      have hc : star eps * eps ≠ 0 := mul_ne_zero (star_ne_zero.mpr heps) heps
      have h' := S.smul_mem (star eps * eps)⁻¹ h
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h'
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX => obtain ⟨e, rfl⟩ := hX; exact hgen e
    | zero => simpa using S.zero_mem
    | add X Y _ _ hX hY => simpa [mul_add, add_mul] using S.add_mem hX hY
    | smul z X _ hX =>
        simpa only [mul_smul_comm, smul_mul_assoc] using S.smul_mem z hX
  have crossS (A B : CStarMatrix a a ℂ) (X : CStarMatrix (a × h) (a × h) ℂ) (hX : X ∈ S) :
      star (low A) * X * low B ∈ S := by
    have h1 := filterS (A + B) X hX
    have h2 := filterS (A - B) X hX
    have h3 := filterS (A + Complex.I • B) X hX
    have h4 := filterS (A - Complex.I • B) X hX
    have hp : star (low A) * X * low B = (1 / 4 : ℂ) •
        ((star (low (A + B)) * X * low (A + B) -
          star (low (A - B)) * X * low (A - B)) +
          (-Complex.I) • (star (low (A + Complex.I • B)) * X *
            low (A + Complex.I • B) -
          star (low (A - Complex.I • B)) * X * low (A - Complex.I • B))) := by
      simp only [map_add, map_sub, map_smul, star_add, star_sub, star_smul,
        mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
        smul_add, smul_sub, smul_smul, Complex.star_def, Complex.conj_I,
        neg_mul, mul_neg, Complex.I_mul_I, neg_neg]
      module
    rw [hp]
    exact S.smul_mem _ (S.add_mem (S.sub_mem h1 h2)
      (S.smul_mem _ (S.sub_mem h3 h4)))
  have leftS (K : CStarMatrix a a ℂ) (X : CStarMatrix (a × h) (a × h) ℂ) (hX : X ∈ S) :
      low K * X ∈ S := by
    simpa only [map_star, star_star, map_one, mul_one] using crossS (star K) 1 X hX
  have rightS (K : CStarMatrix a a ℂ) (X : CStarMatrix (a × h) (a × h) ℂ) (hX : X ∈ S) :
      X * low K ∈ S := by
    simpa only [map_one, star_one, one_mul] using crossS 1 K X hX
  let alpha : CStarMatrix (a × h) (a × h) ℂ →ₗ[ℂ] CStarMatrix (a × h) (a × h) ℂ :=
    { toFun := fun X => star W * X * W
      map_add' := by intro X Y; simp [mul_add, add_mul]
      map_smul' := by intro z X; simp }
  have alphaS : ∀ X ∈ S, alpha X ∈ S := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX => obtain ⟨e, rfl⟩ := hX; exact generator (.tick e)
    | zero => simpa using S.zero_mem
    | add X Y _ _ hX hY => simpa using S.add_mem hX hY
    | smul z X _ hX => simpa using S.smul_mem z hX
  have undo (X : CStarMatrix (a × h) (a × h) ℂ) : W * alpha X * star W = X := by
    dsimp [alpha]
    simp only [mul_assoc, ← mul_assoc W (star W), hW.2, one_mul, mul_one]
  have alphaInjective : Function.Injective alpha := by
    intro X Y h
    simpa only [undo] using congrArg (fun Z => W * Z * star W) h
  have alphaSurjective : Function.Surjective (alpha.restrict alphaS) :=
    LinearMap.surjective_of_injective (fun X Y h => Subtype.ext
      (alphaInjective (congrArg Subtype.val h)))
  have preimageS (X : CStarMatrix (a × h) (a × h) ℂ) (hX : X ∈ S) :
      ∃ Y ∈ S, alpha Y = X := by
    obtain ⟨Y, hY⟩ := alphaSurjective ⟨X, hX⟩
    exact ⟨Y.1, Y.2, congrArg Subtype.val hY⟩
  have alphaMul (X Y : CStarMatrix (a × h) (a × h) ℂ) : alpha (X * Y) = alpha X * alpha Y := by
    dsimp [alpha]
    simp only [mul_assoc, ← mul_assoc W (star W), hW.2, one_mul]
  let D : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ) :=
    { carrier := {X | (∀ Y ∈ S, X * Y ∈ S) ∧ (∀ Y ∈ S, Y * X ∈ S)}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro X Y hX hY
        exact ⟨fun Z hZ => by simpa [add_mul] using S.add_mem (hX.1 Z hZ) (hY.1 Z hZ),
          fun Z hZ => by simpa [mul_add] using S.add_mem (hX.2 Z hZ) (hY.2 Z hZ)⟩
      mul_mem' := by
        intro X Y hX hY
        exact ⟨fun Z hZ => by simpa [mul_assoc] using hX.1 (Y * Z) (hY.1 Z hZ),
          fun Z hZ => by simpa [mul_assoc] using hY.2 (Z * X) (hX.2 Z hZ)⟩
      algebraMap_mem' := by
        intro z
        exact ⟨fun X hX => by simpa [Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc] using S.smul_mem z hX,
          fun X hX => by simpa [Algebra.algebraMap_eq_smul_one,
          mul_smul_comm] using S.smul_mem z hX⟩
      star_mem' := by
        intro X hX
        exact ⟨fun Y hY => by simpa using starS (star Y * X) (hX.2 (star Y) (starS Y hY)),
          fun Y hY => by simpa using starS (X * star Y) (hX.1 (star Y) (starS Y hY))⟩ }
  have lowD (K : CStarMatrix a a ℂ) : low K ∈ D := ⟨leftS K, rightS K⟩
  have alphaD : ∀ X ∈ D, alpha X ∈ D := by
    intro X hX
    constructor <;> intro Y hY <;> obtain ⟨Z, hZ, rfl⟩ := preimageS Y hY
    · rw [← alphaMul]; exact alphaS _ (hX.1 Z hZ)
    · rw [← alphaMul]; exact alphaS _ (hX.2 Z hZ)
  have eventIn (R : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ))
      (hLow : ∀ K, low K ∈ R) (hAlpha : ∀ X ∈ R, alpha X ∈ R) : S ≤ R.toSubalgebra.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro X ⟨e, rfl⟩
    induction e with
    | stop accepted => cases accepted <;> simp [effect]
    | tick next ih => exact hAlpha _ ih
    | observe I next ih =>
        exact R.sum_mem (fun y _ => R.sum_mem (fun r _ =>
          R.mul_mem (R.mul_mem (R.star_mem' (hLow _)) (ih y)) (hLow _)))
  have DS : D.toSubalgebra.toSubmodule = S := by
    apply le_antisymm
    · intro X hX
      simpa using hX.1 1 oneS
    · exact eventIn D lowD alphaD
  have alphaIff (X : CStarMatrix (a × h) (a × h) ℂ) : X ∈ D ↔ alpha X ∈ D := by
    constructor
    · exact alphaD X
    · intro hX
      have hx : alpha X ∈ S := by rw [← DS]; exact hX
      obtain ⟨Y, hY, hYX⟩ := preimageS _ hx
      have hEq : Y = X := alphaInjective hYX
      rw [hEq, ← DS] at hY
      exact hY
  exact ⟨duality, bounds, D, DS, lowD, alphaIff,
    fun R hLow hAlpha => by
      rw [show D ≤ R ↔ D.toSubalgebra.toSubmodule ≤ R.toSubalgebra.toSubmodule by rfl, DS]
      exact eventIn R hLow hAlpha⟩

#print axioms actual_adaptive_span

end D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
