/- GID: D5/S3/Quantum/Dynamics/ControlledObservableCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ControlledObservableCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative control words determine the sharp Hermitian observable and summary spaces. -/

import D5.S3.Quantum.Dynamics.HamiltonianEffectCompletionGenerator
import D5.S3.Quantum.Dynamics.ConservationAutonomySeparation
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace Filter
open scoped Topology

namespace D5.S3.Quantum.Dynamics.ControlledObservableCompletion

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.HamiltonianEffectCompletionGenerator
open D5.S3.Quantum.Dynamics.ConservationAutonomySeparation
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

variable {m : Nat}

section Dynamics

open scoped Matrix.Norms.L2Operator

local instance (priority := 2000) : Ring ℂ := Complex.instRing

local instance (priority := 2000) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.instL2OpNormedAddCommGroup
local instance (priority := 2000) : NormedSpace ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.instL2OpNormedSpace
local instance (priority := 2000) : NormedRing (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.instL2OpNormedRing
local instance (priority := 2000) : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.instL2OpNormedAlgebra
local instance (priority := 2000) : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

private def comm (H : HermitianSpace m) : HermitianSpace m →ₗ[ℝ] HermitianSpace m where
  toFun A := ⟨Complex.I • (H.1 * A.1 - A.1 * H.1), by
    have hH := H.2
    have hA := A.2
    change star H.1 = H.1 at hH
    change star A.1 = A.1 at hA
    change star (Complex.I • (H.1 * A.1 - A.1 * H.1)) =
      Complex.I • (H.1 * A.1 - A.1 * H.1)
    simp only [star_smul, star_sub, star_mul, hH, hA, Complex.star_def,
      Complex.conj_I, neg_smul]
    module⟩
  map_add' A B := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul, smul_add, sub_eq_add_neg]
    abel
  map_smul' r A := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Submodule.coe_smul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, smul_smul]
    module

def generator (H : HermitianSpace m) :
    Module.End ℝ (Matrix (Fin m) (Fin m) ℂ) where
  toFun A := Complex.I • (H.1 * A - A * H.1)
  map_add' A B := by
    simp [Matrix.mul_add, Matrix.add_mul, smul_add, sub_eq_add_neg]
    abel
  map_smul' r A := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul,
      smul_sub, smul_smul]
    module

def wordReadout {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m)
    (word : List (α × {t : ℝ // 0 ≤ t})) (b : β) :
    Matrix (Fin m) (Fin m) ℂ :=
  word.foldr (fun seg O => hamiltonianEffectOrbit (H seg.1).1 O seg.2.1) (E b).1

def actualSpan {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m) :
    Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) :=
  Submodule.span ℝ ({1} ∪ {O | ∃ word b, O = wordReadout H E word b})

private theorem orbit_invariant {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m) (a : α)
    (x : Matrix (Fin m) (Fin m) ℂ) (hx : x ∈ actualSpan H E) :
    generator (H a) x ∈ actualSpan H E := by
  let I : Matrix (Fin m) (Fin m) ℂ := 1
  letI : DecidableEq (Fin m) := Classical.decEq _
  have hI : I = (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    simp [I, Matrix.one_apply]
  let U := actualSpan H E
  have hF : ∀ (a : α) (t : ℝ), 0 ≤ t → ∀ x ∈ U,
      hamiltonianEffectOrbit (H a).1 x t ∈ U := by
    intro a t ht x hx
    refine Submodule.span_induction
      (p := fun x _ => hamiltonianEffectOrbit (H a).1 x t ∈ U)
      ?_ ?_ ?_ ?_ hx
    · intro x hxgen
      rcases hxgen with hId | hOrbit
      · subst x
        change hamiltonianEffectOrbit (H a).1 I t ∈ U
        have hH := (H a).2
        change star (H a).1 = (H a).1 at hH
        have hFixed : hamiltonianEffectOrbit (H a).1 I t = I := by
          rw [hI]
          simpa only [hamiltonianEffectOrbit] using
            (conservation_and_autonomy_are_distinct (H a).1 1 hH (by simp)).1
              (by simp) t
        apply Submodule.subset_span
        left
        exact hFixed
      · rcases hOrbit with ⟨word, b, rfl⟩
        apply Submodule.subset_span
        right
        exact ⟨(a, ⟨t, ht⟩) :: word, b, by
          simp only [wordReadout, List.foldr_cons]⟩
    · simpa [hamiltonianEffectOrbit] using U.zero_mem
    · intro x y _ _ hx hy
      simpa [hamiltonianEffectOrbit, Matrix.mul_add, Matrix.add_mul] using U.add_mem hx hy
    · intro r x _ hx
      simpa [hamiltonianEffectOrbit, Matrix.mul_smul, Matrix.smul_mul] using U.smul_mem r hx
  have hClosed : IsClosed (U : Set (Matrix (Fin m) (Fin m) ℂ)) :=
    U.closed_of_finiteDimensional
  have hderiv : HasDerivAt (hamiltonianEffectOrbit (H a).1 x)
      (generator (H a) x) 0 := by
    simpa [generator, hamiltonianEffectOrbit, hamiltonianPropagator] using
      hasDerivAt_hamiltonianEffectOrbit (H a).1 x 0
  apply hClosed.mem_of_tendsto hderiv.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hzero : hamiltonianEffectOrbit (H a).1 x 0 = x := by
    simp [hamiltonianEffectOrbit, hamiltonianPropagator]
  simp only [zero_add, hzero]
  exact U.smul_mem t⁻¹
    (U.sub_mem (hF a t ht.le x hx) hx)

private theorem flow_preserves (H : HermitianSpace m)
    (W : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hD : ∀ x ∈ W, generator H x ∈ W)
    (x : Matrix (Fin m) (Fin m) ℂ) (hx : x ∈ W) (t : ℝ) :
    hamiltonianEffectOrbit H.1 x t ∈ W := by
  let KCL : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toContinuousLinearMap (generator H)
  let comparisonFlow : ℝ → Matrix (Fin m) (Fin m) ℂ :=
    fun s => exp (s • KCL) x
  have hComparisonDeriv : ∀ s,
      HasDerivAt comparisonFlow (KCL (comparisonFlow s)) s := by
    intro s
    have hExp := hasDerivAt_exp_smul_const' KCL s
    have hApplied := (ContinuousLinearMap.apply ℝ _ x).hasFDerivAt.comp_hasDerivAt s hExp
    change HasDerivAt (fun u : ℝ => exp (u • KCL) x)
      ((KCL * exp (s • KCL)) x) s at hApplied
    simpa [comparisonFlow, mul_apply] using hApplied
  have hActualDeriv : ∀ s,
      HasDerivAt (hamiltonianEffectOrbit H.1 x)
        (KCL (hamiltonianEffectOrbit H.1 x s)) s := by
    intro s
    simpa [KCL, generator] using
      hasDerivAt_hamiltonianEffectOrbit H.1 x s
  have hLipschitz : ∀ _s : ℝ,
      LipschitzOnWith ‖KCL‖₊ (fun x => KCL x)
        (Set.univ : Set (Matrix (Fin m) (Fin m) ℂ)) := by
    intro s
    exact KCL.lipschitz.lipschitzOnWith
  have hInitial : hamiltonianEffectOrbit H.1 x 0 = comparisonFlow 0 := by
    simp [comparisonFlow, hamiltonianEffectOrbit, hamiltonianPropagator]
  have hEqual : hamiltonianEffectOrbit H.1 x = comparisonFlow := by
    apply ODE_solution_unique_univ (K := ‖KCL‖₊)
      (v := fun _ y => KCL y) (s := fun _ => Set.univ)
      (t₀ := 0)
    · exact hLipschitz
    · intro s
      exact ⟨hActualDeriv s, Set.mem_univ _⟩
    · intro s
      exact ⟨hComparisonDeriv s, Set.mem_univ _⟩
    · exact hInitial
  have hScaledInvariant : ∀ y ∈ W, (t • KCL) y ∈ W := by
    intro y hy
    simpa [KCL] using W.smul_mem t (hD y hy)
  have hPower : ∀ n : ℕ, ((t • KCL) ^ n) x ∈ W := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa [pow_succ'] using hScaledInvariant _ ih
  have hSeries : HasSum
      (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • (t • KCL) ^ n)
      (exp (t • KCL)) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) (t • KCL)
  have hApplied := (ContinuousLinearMap.apply ℝ _ x).hasSum hSeries
  have hComparisonMem : comparisonFlow t ∈ W := by
    change (ContinuousLinearMap.apply ℝ _ x (exp (t • KCL))) ∈ W
    rw [← hApplied.tsum_eq]
    apply tsum_mem W.closed_of_finiteDimensional
    intro n
    exact W.smul_mem _ (hPower n)
  rw [congrFun hEqual t]
  exact hComparisonMem

def initial {β : Type*} (E : β → HermitianSpace m) :
    Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) :=
  Submodule.span ℝ ({1} ∪ Set.range (fun b => (E b).1))

def levels {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m) :
    ℕ → Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)
  | 0 => initial E
  | n + 1 => levels H E n ⊔ ⨆ a, (levels H E n).map (generator (H a))

private theorem controlled_completion {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m) :
    ∃ k, k ≤ m ^ 2 - Module.finrank ℝ (initial E) ∧
      (∀ n, levels H E n ≤ HermitianSpace m) ∧
      (∀ j, k ≤ j → levels H E j = levels H E k) ∧
      actualSpan H E = levels H E k ∧
      (∀ Z : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ),
        (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Z →
        (∀ b, (E b).1 ∈ Z) →
        (∀ a x, x ∈ Z → generator (H a) x ∈ Z) →
        actualSpan H E ≤ Z) := by
  have hOrbitLe (Z : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
      (hI : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Z)
      (hE : ∀ b, (E b).1 ∈ Z)
      (hD : ∀ a x, x ∈ Z → generator (H a) x ∈ Z) : actualSpan H E ≤ Z := by
    change Submodule.span ℝ ({1} ∪ {O | ∃ word b, O = wordReadout H E word b}) ≤ Z
    refine Submodule.span_le.mpr ?_
    rintro O (hId | ⟨word, b, rfl⟩)
    · subst O
      exact hI
    · induction word with
      | nil => simpa [wordReadout] using hE b
      | cons seg tail ih =>
        change hamiltonianEffectOrbit (H seg.1).1 (wordReadout H E tail b)
          seg.2.1 ∈ Z
        exact flow_preserves (H seg.1) Z (hD seg.1) _ ih seg.2.1
  have hInitialLe : initial E ≤ actualSpan H E := by
    rw [initial, actualSpan]
    refine Submodule.span_le.mpr ?_
    rintro O (hId | ⟨b, rfl⟩)
    · exact Submodule.subset_span (Or.inl hId)
    · apply Submodule.subset_span
      right
      exact ⟨[], b, by simp [wordReadout]⟩
  have hLevelsLe : ∀ n, levels H E n ≤ actualSpan H E := by
    intro n
    induction n with
    | zero => exact hInitialLe
    | succ n ih =>
      change levels H E n ⊔ ⨆ a, (levels H E n).map (generator (H a)) ≤
        actualSpan H E
      refine sup_le ih (iSup_le fun a => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact orbit_invariant H E a x (ih hx)
  have hStep (n : ℕ) : levels H E n ≤ levels H E (n + 1) := by
    change levels H E n ≤ levels H E n ⊔
      ⨆ a, (levels H E n).map (generator (H a))
    exact le_sup_left
  have hMonotone : Monotone (levels H E) := monotone_nat_of_le_succ hStep
  have hGeneratorHermitian (a : α) (x : Matrix (Fin m) (Fin m) ℂ)
      (hx : x ∈ HermitianSpace m) :
      generator (H a) x ∈ HermitianSpace m := by
    let X : HermitianSpace m := ⟨x, hx⟩
    have h := (comm (H a) X).2
    simpa [X, comm, generator] using h
  have hHermitian : ∀ n, levels H E n ≤ HermitianSpace m := by
    intro n
    induction n with
    | zero =>
      change initial E ≤ HermitianSpace m
      rw [initial]
      refine Submodule.span_le.mpr ?_
      rintro x (hx | ⟨b, rfl⟩)
      · subst x
        change star (1 : Matrix (Fin m) (Fin m) ℂ) = 1
        simp
      · exact (E b).2
    | succ n ih =>
      change levels H E n ⊔ ⨆ a, (levels H E n).map (generator (H a)) ≤
        HermitianSpace m
      refine sup_le ih (iSup_le fun a => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hGeneratorHermitian a x (ih hx)
  have hBound (n : ℕ) : Module.finrank ℝ (levels H E n) ≤ m ^ 2 := by
    calc
      Module.finrank ℝ (levels H E n)
          ≤ Module.finrank ℝ (HermitianSpace m) :=
            Submodule.finrank_mono (hHermitian n)
      _ = m ^ 2 := hermitian_space_finrank m
  have hFinrankMonotone : Monotone (fun n => Module.finrank ℝ (levels H E n)) :=
    monotone_nat_of_le_succ (fun n => Submodule.finrank_mono (hStep n))
  obtain ⟨k, hk, hEqRank⟩ := bounded_monotone_has_equal_step
    (fun n => Module.finrank ℝ (levels H E n)) (m ^ 2)
    hFinrankMonotone hBound
  have hEq : levels H E k = levels H E (k + 1) :=
    Submodule.eq_of_le_of_finrank_eq (hStep k) hEqRank
  have hStableD : ∀ a x, x ∈ levels H E k →
      generator (H a) x ∈ levels H E k := by
    intro a x hx
    have hMap : (levels H E k).map (generator (H a)) ≤ levels H E (k + 1) := by
      change (levels H E k).map (generator (H a)) ≤
        levels H E k ⊔ ⨆ a, (levels H E k).map (generator (H a))
      exact le_sup_of_le_right (le_iSup (fun a =>
        (levels H E k).map (generator (H a))) a)
    have hMem := hMap (show generator (H a) x ∈
      (levels H E k).map (generator (H a)) from ⟨x, hx, rfl⟩)
    rw [← hEq] at hMem
    exact hMem
  have hInitialK : initial E ≤ levels H E k := by
    simpa only [levels] using hMonotone (Nat.zero_le k)
  have hIK : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ levels H E k :=
    hInitialK (Submodule.subset_span (Or.inl rfl))
  have hEK (b : β) : (E b).1 ∈ levels H E k :=
    hInitialK (Submodule.subset_span (Or.inr ⟨b, rfl⟩))
  have hOrbitEq : actualSpan H E = levels H E k :=
    le_antisymm (hOrbitLe _ hIK hEK hStableD) (hLevelsLe k)
  have hStay : ∀ n, levels H E (k + n) = levels H E k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        levels H E (k + (n + 1)) =
            levels H E (k + n) ⊔
              ⨆ a, (levels H E (k + n)).map (generator (H a)) := by
                rw [Nat.add_succ]
                rfl
        _ = levels H E k ⊔
              ⨆ a, (levels H E k).map (generator (H a)) := by rw [ih]
        _ = levels H E k := by simpa only [levels] using hEq.symm
  refine ⟨k, hk, hHermitian, ?_, hOrbitEq, hOrbitLe⟩
  intro j hkj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
  exact hStay n

end Dynamics

open scoped ComplexOrder ComplexStarModule InnerProductSpace MatrixOrder

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
local instance matrixRealInnerProductSpace : InnerProductSpace ℝ (Matrix (Fin m) (Fin m) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin m) (Fin m) ℂ)

def densityHermitian (rho : DensityState (Fin m)) : HermitianSpace m :=
  ⟨densityMatrix rho, by
    change (densityMatrix rho).IsHermitian
    exact congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq⟩

def observedHermitian {α β : Type*} (H : α → HermitianSpace m)
    (E : β → HermitianSpace m) : Submodule ℝ (HermitianSpace m) :=
  (actualSpan H E).comap (HermitianSpace m).subtype

private theorem physical_summary_attainment [NeZero m]
    (W : Submodule ℝ (HermitianSpace m))
    (hI : identityHermitian m ∈ W) :
    ∃ r : ℕ, r = Module.finrank ℝ W - 1 ∧
      ∃ coordinates : HermitianSpace m →ₗ[ℝ] (Fin r → ℝ),
        (∀ rho sigma : DensityState (Fin m),
          coordinates (densityHermitian rho) = coordinates (densityHermitian sigma) →
          ∀ O ∈ W,
            inner ℝ (densityHermitian rho - densityHermitian sigma) O = 0) ∧
        Module.finrank ℝ
          (LinearMap.range (coordinates.comp (traceZeroHermitian m).subtype)) = r ∧
        ∃ observables : Fin r → W,
          ∀ A i, coordinates A i =
            (Matrix.trace (A.1 * (observables i).1.1)).re := by
  let Z := traceZeroHermitian m
  let K := scalarHermitian m
  let C := Kᗮ ⊓ W
  have hK_le_W : K ≤ W := by
    change ℝ ∙ identityHermitian m ≤ W
    exact Submodule.span_le.mpr (by simpa using hI)
  have hC_le_Z : C ≤ Z := by
    dsimp [Z]
    rw [traceZeroHermitian_eq_orthogonal m]
    exact inf_le_left
  have hDim : Module.finrank ℝ C = Module.finrank ℝ W - 1 := by
    have hRank := Submodule.finrank_add_inf_finrank_orthogonal hK_le_W
    have hRankK : Module.finrank ℝ K = 1 :=
      finrank_span_singleton (identityHermitian_ne_zero m)
    rw [hRankK] at hRank
    change 1 + Module.finrank ℝ C = Module.finrank ℝ W at hRank
    omega
  let P : HermitianSpace m →ₗ[ℝ] C :=
    C.projectionOnto Cᗮ C.isCompl_orthogonal
  let basis : OrthonormalBasis (Fin (Module.finrank ℝ C)) ℝ C :=
    stdOrthonormalBasis ℝ C
  let equiv : C ≃ₗ[ℝ] (Fin (Module.finrank ℝ C) → ℝ) :=
    basis.toBasis.equivFun
  let coordinates : HermitianSpace m →ₗ[ℝ]
      (Fin (Module.finrank ℝ C) → ℝ) := equiv.toLinearMap.comp P
  have hPSurj : Function.Surjective (P.comp Z.subtype) := by
    intro c
    refine ⟨⟨c.1, hC_le_Z c.2⟩, ?_⟩
    exact Submodule.projectionOnto_apply_left C.isCompl_orthogonal c
  have hCoordinateSurj : Function.Surjective (coordinates.comp Z.subtype) := by
    exact equiv.surjective.comp hPSurj
  have hCoordinateRank : Module.finrank ℝ
      (LinearMap.range (coordinates.comp Z.subtype)) = Module.finrank ℝ C := by
    rw [LinearMap.range_eq_top.mpr hCoordinateSurj, finrank_top]
    exact equiv.finrank_eq.symm
  have hSufficient : ∀ rho sigma : DensityState (Fin m),
      coordinates (densityHermitian rho) = coordinates (densityHermitian sigma) →
      ∀ O ∈ W, inner ℝ (densityHermitian rho - densityHermitian sigma) O = 0 := by
    intro rho sigma hCoord O hO
    have hP : P (densityHermitian rho) = P (densityHermitian sigma) := by
      exact equiv.injective hCoord
    let D := densityHermitian rho - densityHermitian sigma
    have hPD : P D = 0 := by
      dsimp [D]
      rw [map_sub, hP, sub_self]
    have hD_Z : D ∈ Z := by
      change Matrix.trace D.1 = 0
      have hrho : Matrix.trace (densityMatrix rho) = 1 := rho.2.2
      have hsigma : Matrix.trace (densityMatrix sigma) = 1 := sigma.2.2
      simpa [D, densityHermitian, Matrix.trace_sub, hrho, hsigma]
    have hD_K : D ∈ Kᗮ := by
      rw [← traceZeroHermitian_eq_orthogonal m]
      exact hD_Z
    have hD_C : D ∈ Cᗮ := by
      exact (Submodule.projectionOnto_apply_eq_zero_iff C.isCompl_orthogonal).mp hPD
    have hDecomp : K ⊔ C = W :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hK_le_W
    rw [← hDecomp] at hO
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hO
    rw [Submodule.mem_orthogonal'] at hD_K hD_C
    have hu0 : inner ℝ D u = 0 := hD_K u hu
    have hv0 : inner ℝ D v = 0 := hD_C v hv
    change inner ℝ D (u + v) = 0
    simp [inner_add_right, hu0, hv0]
  let observables : Fin (Module.finrank ℝ C) → W :=
    fun i => ⟨(basis i).1, (basis i).2.2⟩
  have hExpect (A : HermitianSpace m) (i : Fin (Module.finrank ℝ C)) :
      coordinates A i =
        (Matrix.trace (A.1 * (observables i).1.1)).re := by
    have hInner : coordinates A i = inner ℝ A (observables i).1 := by
      change basis.toBasis.repr (P A) i = inner ℝ A (basis i).1
      rw [basis.coe_toBasis_repr_apply, basis.repr_apply_apply]
      change inner ℝ (basis i) (C.orthogonalProjectionOnto A) = _
      rw [C.inner_orthogonalProjectionOnto_eq_of_mem_left]
      exact real_inner_comm A (basis i).1
    rw [hInner]
    letI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
    change (inner ℂ A.1 (observables i).1.1).re = _
    rw [matrix_inner_eq_trace_mul_of_hermitian A.1 (observables i).1.1 A.2]
  exact ⟨Module.finrank ℝ C, hDim, coordinates, hSufficient,
    hCoordinateRank, observables, hExpect⟩

theorem controlled_observable_completion {α β Y : Type*}
    [AddCommGroup Y] [Module ℝ Y]
    (H : α → HermitianSpace m) (E : β → HermitianSpace m)
    (summary : HermitianSpace m →ₗ[ℝ] Y) :
    let W0 := (initial E).comap (HermitianSpace m).subtype
    let W := observedHermitian H E
    (∀ a : α, ∀ t : ℝ,
      star (hamiltonianPropagator (H a).1 t) =
        hamiltonianPropagator (H a).1 (-t)) ∧
    (∃ k, k ≤ m ^ 2 - Module.finrank ℝ W0 ∧
      (∀ n, levels H E n ≤ HermitianSpace m) ∧
      (∀ j, k ≤ j → levels H E j = levels H E k) ∧
      W = (levels H E k).comap (HermitianSpace m).subtype ∧
      (∀ Z : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ),
        (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Z →
        (∀ b, (E b).1 ∈ Z) →
        (∀ a x, x ∈ Z → generator (H a) x ∈ Z) →
        actualSpan H E ≤ Z)) ∧
    (∀ rho sigma : DensityState (Fin m),
      (∀ word b,
        Matrix.trace (densityMatrix rho * wordReadout H E word b) =
          Matrix.trace (densityMatrix sigma * wordReadout H E word b)) ↔
        ∀ O ∈ W,
          Matrix.trace ((densityMatrix rho - densityMatrix sigma) * O.1) = 0) ∧
    ((∀ rho sigma : DensityState (Fin m),
        summary (densityHermitian rho) = summary (densityHermitian sigma) →
        ∀ word b,
          Matrix.trace (densityMatrix rho * wordReadout H E word b) =
            Matrix.trace (densityMatrix sigma * wordReadout H E word b)) →
      Module.finrank ℝ W - 1 ≤ Module.finrank ℝ
        (LinearMap.range (summary.comp (traceZeroHermitian m).subtype))) ∧
    (∃ r : ℕ, r = Module.finrank ℝ W - 1 ∧
      ∃ coordinates : HermitianSpace m →ₗ[ℝ] (Fin r → ℝ),
        (∀ rho sigma : DensityState (Fin m),
          coordinates (densityHermitian rho) =
              coordinates (densityHermitian sigma) →
          ∀ word b,
            Matrix.trace (densityMatrix rho * wordReadout H E word b) =
              Matrix.trace (densityMatrix sigma * wordReadout H E word b)) ∧
        Module.finrank ℝ
          (LinearMap.range
            (coordinates.comp (traceZeroHermitian m).subtype)) = r ∧
        ∃ observables : Fin r → W,
          ∀ A i, coordinates A i =
            (Matrix.trace (A.1 * (observables i).1.1)).re) := by
  dsimp only
  let W0 := (initial E).comap (HermitianSpace m).subtype
  let W := observedHermitian H E
  have hAdjoint (a : α) (t : ℝ) :
      star (hamiltonianPropagator (H a).1 t) =
        hamiltonianPropagator (H a).1 (-t) := by
    have hH := (H a).2
    change star (H a).1 = (H a).1 at hH
    simp [hamiltonianPropagator, hamiltonianGenerator,
      star_exp, star_smul, hH]
  obtain ⟨k, hk, hHermitian, hStable, hOrbit, hLeast⟩ :=
    controlled_completion H E
  have hCompletion : ∃ k, k ≤ m ^ 2 - Module.finrank ℝ W0 ∧
      (∀ n, levels H E n ≤ HermitianSpace m) ∧
      (∀ j, k ≤ j → levels H E j = levels H E k) ∧
      W = (levels H E k).comap (HermitianSpace m).subtype ∧
      (∀ Z : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ),
        (1 : Matrix (Fin m) (Fin m) ℂ) ∈ Z →
        (∀ b, (E b).1 ∈ Z) →
        (∀ a x, x ∈ Z → generator (H a) x ∈ Z) →
        actualSpan H E ≤ Z) := by
    have hInitial : initial E ≤ HermitianSpace m :=
      hHermitian 0
    have hMap : W0.map (HermitianSpace m).subtype = initial E := by
      change ((initial E).comap (HermitianSpace m).subtype).map
        (HermitianSpace m).subtype = initial E
      rw [Submodule.map_comap_subtype]
      exact inf_of_le_right hInitial
    have hDim : Module.finrank ℝ W0 = Module.finrank ℝ (initial E) := by
      calc
        Module.finrank ℝ W0 =
            Module.finrank ℝ (W0.map (HermitianSpace m).subtype) :=
          (Submodule.finrank_map_subtype_eq (HermitianSpace m) W0).symm
        _ = Module.finrank ℝ (initial E) := by rw [hMap]
    refine ⟨k, ?_, hHermitian, hStable, ?_, hLeast⟩
    · change k ≤ m ^ 2 - Module.finrank ℝ W0
      rw [hDim]
      exact hk
    · change (actualSpan H E).comap (HermitianSpace m).subtype =
        (levels H E k).comap (HermitianSpace m).subtype
      rw [hOrbit]
  have hOrbitHermitian : actualSpan H E ≤ HermitianSpace m := by
    rw [hOrbit]
    exact hHermitian k
  have hExperiment (rho sigma : DensityState (Fin m)) :
      (∀ word b,
        Matrix.trace (densityMatrix rho * wordReadout H E word b) =
          Matrix.trace (densityMatrix sigma * wordReadout H E word b)) ↔
        ∀ O ∈ actualSpan H E,
          Matrix.trace ((densityMatrix rho - densityMatrix sigma) * O) = 0 := by
    have hTraceRho : Matrix.trace (densityMatrix rho) = 1 := rho.2.2
    have hTraceSigma : Matrix.trace (densityMatrix sigma) = 1 := sigma.2.2
    constructor
    · intro hword O hO
      change O ∈ Submodule.span ℝ
        ({1} ∪ {O | ∃ word b, O = wordReadout H E word b}) at hO
      induction hO using Submodule.span_induction with
      | mem O hO =>
        rcases hO with hId | ⟨word, b, rfl⟩
        · subst O
          simp [sub_mul, Matrix.trace_sub, hTraceRho, hTraceSigma]
        · have h := hword word b
          simpa only [sub_mul, Matrix.trace_sub, sub_eq_zero] using h
      | zero => simp
      | add X Y _ _ hX hY =>
        simpa [Matrix.mul_add, Matrix.trace_add] using congrArg₂ (· + ·) hX hY
      | smul r X _ hX =>
        simpa [Matrix.mul_smul, Matrix.trace_smul] using
          congrArg (fun z : ℂ => (r : ℂ) • z) hX
    · intro h word b
      have hO : wordReadout H E word b ∈ actualSpan H E := by
        apply Submodule.subset_span
        exact Or.inr ⟨word, b, rfl⟩
      have hzero := h _ hO
      simpa only [sub_mul, Matrix.trace_sub, sub_eq_zero] using hzero
  have hPhysical (rho sigma : DensityState (Fin m)) :
      (∀ word b,
        Matrix.trace (densityMatrix rho * wordReadout H E word b) =
          Matrix.trace (densityMatrix sigma * wordReadout H E word b)) ↔
        ∀ O ∈ W,
          Matrix.trace ((densityMatrix rho - densityMatrix sigma) * O.1) = 0 := by
    rw [hExperiment rho sigma]
    constructor
    · intro h O hO
      exact h O.1 hO
    · intro h O hO
      exact h ⟨O, hOrbitHermitian hO⟩ hO
  have hTracePair (hm : m ≠ 0) (A O : HermitianSpace m) :
      Matrix.trace (A.1 * O.1) = 0 ↔ inner ℝ A O = 0 := by
    letI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    classical
    have hRe : inner ℝ A O = (Matrix.trace (A.1 * O.1)).re := by
      change (inner ℂ A.1 O.1).re = _
      rw [matrix_inner_eq_trace_mul_of_hermitian A.1 O.1 A.2]
    have hIm : (Matrix.trace (A.1 * O.1)).im = 0 :=
      trace_hermitian_product_real A.1 O.1 A.2 O.2
    constructor
    · intro h
      rw [hRe, h]
      rfl
    · intro h
      apply Complex.ext
      · exact hRe.symm.trans h
      · exact hIm
  refine ⟨hAdjoint, hCompletion, hPhysical, ?_, ?_⟩
  · intro hSufficient
    by_cases hm : m = 0
    · subst m
      have hHermitianZero : Module.finrank ℝ (HermitianSpace 0) = 0 := by
        simpa using hermitian_space_finrank 0
      haveI : Subsingleton (HermitianSpace 0) :=
        (Module.finrank_zero_iff).mp hHermitianZero
      have hWZero : Module.finrank ℝ W = 0 := by
        exact Module.finrank_zero_of_subsingleton
      change Module.finrank ℝ W - 1 ≤
        Module.finrank ℝ
          (LinearMap.range (summary.comp (traceZeroHermitian 0).subtype))
      rw [hWZero]
      simp
    · letI : NeZero m := ⟨hm⟩
      have hI : identityHermitian m ∈ W := by
        change (identityHermitian m).1 ∈ actualSpan H E
        apply Submodule.subset_span
        exact Or.inl rfl
      let Z := traceZeroHermitian m
      let K := scalarHermitian m
      let C := Kᗮ ⊓ W
      have hK_le_W : K ≤ W := by
        change ℝ ∙ identityHermitian m ≤ W
        exact Submodule.span_le.mpr (by simpa using hI)
      have hC_le_Z : C ≤ Z := by
        dsimp [Z]
        rw [traceZeroHermitian_eq_orthogonal m]
        exact inf_le_left
      have hDim : Module.finrank ℝ C = Module.finrank ℝ W - 1 := by
        have hRank := Submodule.finrank_add_inf_finrank_orthogonal hK_le_W
        have hRankK : Module.finrank ℝ K = 1 :=
          finrank_span_singleton (identityHermitian_ne_zero m)
        rw [hRankK] at hRank
        change 1 + Module.finrank ℝ C = Module.finrank ℝ W at hRank
        omega
      let P : HermitianSpace m →ₗ[ℝ] C :=
        C.projectionOnto Cᗮ C.isCompl_orthogonal
      let PZ : Z →ₗ[ℝ] C := P.comp Z.subtype
      let SZ : Z →ₗ[ℝ] Y := summary.comp Z.subtype
      have hPSurj : Function.Surjective PZ := by
        intro c
        refine ⟨⟨c.1, hC_le_Z c.2⟩, ?_⟩
        exact Submodule.projectionOnto_apply_left C.isCompl_orthogonal c
      have hKer : SZ.ker ≤ PZ.ker := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        change summary x.1 = 0 at hx
        apply (Submodule.projectionOnto_apply_eq_zero_iff C.isCompl_orthogonal).mpr
        rw [Submodule.mem_orthogonal']
        intro c hc
        obtain ⟨eps, heps, plus, minus, hmatrices⟩ :=
          traceless_density_perturbations m x
        have hDifference : densityHermitian plus - densityHermitian minus =
            (2 * eps) • x.1 := by
          apply Subtype.ext
          exact hmatrices
        have hSummaryEq : summary (densityHermitian plus) =
            summary (densityHermitian minus) := by
          apply sub_eq_zero.mp
          calc
            summary (densityHermitian plus) - summary (densityHermitian minus) =
                summary (densityHermitian plus - densityHermitian minus) :=
                  (map_sub summary _ _).symm
            _ = 0 := by rw [hDifference, map_smul, hx, smul_zero]
        have hcW : c ∈ W := (show C ≤ W from inf_le_right) hc
        have hTrace := (hPhysical plus minus).mp
          (hSufficient plus minus hSummaryEq) c hcW
        have hPair := (hTracePair hm
          (densityHermitian plus - densityHermitian minus) c).mp hTrace
        rw [hDifference] at hPair
        simp only [real_inner_smul_left] at hPair
        have hNonzero : (2 * eps : ℝ) ≠ 0 :=
          mul_ne_zero (by norm_num) heps.ne'
        exact (smul_eq_zero.mp hPair).resolve_left hNonzero
      have hKerDim := Submodule.finrank_mono hKer
      have hPDim := PZ.finrank_range_add_finrank_ker
      have hSDim := SZ.finrank_range_add_finrank_ker
      have hPRange : LinearMap.range PZ = ⊤ := LinearMap.range_eq_top.mpr hPSurj
      rw [hPRange, finrank_top] at hPDim
      rw [← hDim]
      change Module.finrank ℝ C ≤ Module.finrank ℝ (LinearMap.range SZ)
      omega
  · by_cases hm : m = 0
    · subst m
      have hHermitianZero : Module.finrank ℝ (HermitianSpace 0) = 0 := by
        simpa using hermitian_space_finrank 0
      haveI : Subsingleton (HermitianSpace 0) :=
        (Module.finrank_zero_iff).mp hHermitianZero
      have hWZero : Module.finrank ℝ W = 0 := by
        exact Module.finrank_zero_of_subsingleton
      have hNoStates : IsEmpty (DensityState (Fin 0)) := ⟨by
        intro rho
        have hTrace : Matrix.trace (densityMatrix rho) = 1 := rho.2.2
        rw [Matrix.trace_fin_zero] at hTrace
        norm_num at hTrace⟩
      refine ⟨0, ?_, 0, ?_, ?_, ?_⟩
      · change 0 = Module.finrank ℝ W - 1
        omega
      · intro rho
        exact isEmptyElim rho
      · simp
      · exact ⟨fun i => Fin.elim0 i, by intro A i; exact Fin.elim0 i⟩
    · letI : NeZero m := ⟨hm⟩
      have hI : identityHermitian m ∈ W := by
        change (identityHermitian m).1 ∈ actualSpan H E
        apply Submodule.subset_span
        exact Or.inl rfl
      obtain ⟨r, hr, coordinates, hInnerSufficient, hRank,
        observables, hExpect⟩ :=
        physical_summary_attainment W hI
      refine ⟨r, hr, coordinates, ?_, hRank, observables, hExpect⟩
      intro rho sigma hCoordinates
      apply (hPhysical rho sigma).mpr
      intro O hO
      apply (hTracePair hm
        (densityHermitian rho - densityHermitian sigma) O).mpr
      exact hInnerSufficient rho sigma hCoordinates O hO

#print axioms controlled_observable_completion

end D5.S3.Quantum.Dynamics.ControlledObservableCompletion
