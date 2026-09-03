/- GID: D5/S3/Observer/BlockStructure/CommonSpectrumMasterFeasibility
   generality: I
   mirror-B: D5/B/S3/Observer/BlockStructure/CommonSpectrumMasterFeasibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify finite common-spectrum feasibility with one positive Toeplitz moment system. -/

import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * D5 name and body-shape searches found no exact common-spectrum master
     feasibility theorem and no existing real coordinate decoder for a finite
     Hermitian Toeplitz sequence. RationalToeplitzCollapse supplies the earlier
     rational-feature congruence, not the constrained moment equivalence here.
   * LiCurvatureCriterion owns circleMoment, toeplitzMatrix, Hermitian circle
     moments, and their positive semidefiniteness. TruncatedCircleMomentBridge
     owns the finite-order representing-measure converse used below.
   * Pinned Mathlib supplies LinearEquiv.ofFinrankEq and the real finrank of
     Complex, but no packaged common-spectrum feasibility theorem or truncated
     Toeplitz moment representation. Installed non-Mathlib Lake packages have
     no matching declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexConjugate ComplexOrder MatrixOrder
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge

namespace D5.S3.Observer.BlockStructure.CommonSpectrumMasterFeasibility

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- A fixed real coordinate system for the center and positive half of a
Hermitian moment window. -/
noncomputable def momentCoordinateEquiv (N : Nat) :
    (Fin (2 * (N + 1) - 1) -> Real) ≃ₗ[Real]
      Real × (Fin N -> Complex) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi, Module.finrank_prod, Module.finrank_self,
      Module.finrank_pi_fintype, Complex.finrank_real_complex]
    simp
    omega)

/-- Decode `2 * (N + 1) - 1` real coordinates into a Hermitian moment
sequence supported on the source window. -/
noncomputable def hermitianMomentCoordinates (N : Nat)
    (x : Fin (2 * (N + 1) - 1) -> Real) : Int -> Complex
  | .ofNat 0 => ((momentCoordinateEquiv N x).1 : Complex)
  | .ofNat (n + 1) =>
      if h : n < N then (momentCoordinateEquiv N x).2 ⟨n, h⟩ else 0
  | .negSucc n =>
      if h : n < N then star ((momentCoordinateEquiv N x).2 ⟨n, h⟩) else 0

/-- Decode `N + 1` real coordinates into a real even moment sequence supported
on the source window. -/
def realEvenMomentCoordinates (N : Nat)
    (x : Fin (N + 1) -> Real) : Int -> Complex
  | .ofNat n => if h : n <= N then (x ⟨n, by omega⟩ : Complex) else 0
  | .negSucc n => if h : n < N then (x ⟨n + 1, by omega⟩ : Complex) else 0

private theorem hermitian_moment_coordinates_hermitian
    (N : Nat) (x : Fin (2 * (N + 1) - 1) -> Real) (k : Int) :
    hermitianMomentCoordinates N x (-k) =
      star (hermitianMomentCoordinates N x k) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp [hermitianMomentCoordinates]
      | succ n =>
          change hermitianMomentCoordinates N x (Int.negSucc n) = _
          by_cases h : n < N <;> simp [hermitianMomentCoordinates, h]
  | negSucc n =>
      change hermitianMomentCoordinates N x (Int.ofNat (n + 1)) = _
      by_cases h : n < N <;> simp [hermitianMomentCoordinates, h]

private theorem real_even_moment_coordinates_hermitian
    (N : Nat) (x : Fin (N + 1) -> Real) (k : Int) :
    realEvenMomentCoordinates N x (-k) =
      star (realEvenMomentCoordinates N x k) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp [realEvenMomentCoordinates]
      | succ n =>
          change realEvenMomentCoordinates N x (Int.negSucc n) = _
          by_cases h : n < N <;>
            simp [realEvenMomentCoordinates, h, RCLike.star_def]
  | negSucc n =>
      change realEvenMomentCoordinates N x (Int.ofNat (n + 1)) = _
      by_cases h : n < N <;>
        simp [realEvenMomentCoordinates, h, RCLike.star_def]

private theorem real_even_moment_coordinates_even
    (N : Nat) (x : Fin (N + 1) -> Real) (k : Int) :
    realEvenMomentCoordinates N x (-k) = realEvenMomentCoordinates N x k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp [realEvenMomentCoordinates]
      | succ n =>
          change realEvenMomentCoordinates N x (Int.negSucc n) = _
          simp [realEvenMomentCoordinates]
  | negSucc n =>
      change realEvenMomentCoordinates N x (Int.ofNat (n + 1)) = _
      simp [realEvenMomentCoordinates]

private theorem hermitian_moment_coordinates_existsUnique
    (N : Nat) (r : Int -> Complex)
    (hermitian : forall k, k.natAbs <= N -> r (-k) = star (r k)) :
    ∃! x : Fin (2 * (N + 1) - 1) -> Real,
      forall k : Int, k.natAbs <= N ->
        hermitianMomentCoordinates N x k = r k := by
  let data : Real × (Fin N -> Complex) :=
    ((r 0).re, fun i => r ((i : Nat) + 1))
  let x := (momentCoordinateEquiv N).symm data
  have representation : forall k : Int, k.natAbs <= N ->
      hermitianMomentCoordinates N x k = r k := by
    intro k hbound
    have coordinateIdentity : momentCoordinateEquiv N x = data := by
      exact (momentCoordinateEquiv N).apply_symm_apply data
    have zeroReal : ((r 0).re : Complex) = r 0 := by
      apply Complex.ext
      · simp
      · have h := congrArg Complex.im (hermitian 0 (by omega))
        simp only [neg_zero] at h
        change (r 0).im = -(r 0).im at h
        simp only [Complex.ofReal_im]
        linarith
    cases k with
    | ofNat n =>
        cases n with
        | zero =>
            simpa [hermitianMomentCoordinates, hbound, x, coordinateIdentity, data]
              using zeroReal
        | succ n =>
            change n + 1 <= N at hbound
            rw [hermitianMomentCoordinates, dif_pos (by omega), coordinateIdentity]
            simp [data]
    | negSucc n =>
        have hpositive := hermitian ((n + 1 : Nat) : Int) (by omega)
        change n + 1 <= N at hbound
        rw [hermitianMomentCoordinates, dif_pos (by omega), coordinateIdentity]
        simpa [data, Int.negSucc_eq] using hpositive.symm
  refine ⟨x, representation, ?_⟩
  intro x' representation'
  apply (momentCoordinateEquiv N).injective
  apply Prod.ext
  · have hx := representation 0 (by omega)
    have hx' := representation' 0 (by omega)
    simpa [hermitianMomentCoordinates] using
      congrArg Complex.re (hx'.trans hx.symm)
  · funext i
    have hx := representation (((i : Nat) + 1 : Nat) : Int) (by omega)
    have hx' := representation' (((i : Nat) + 1 : Nat) : Int) (by omega)
    simpa [hermitianMomentCoordinates] using hx'.trans hx.symm

private theorem real_even_moment_coordinates_existsUnique
    (N : Nat) (r : Int -> Complex)
    (hermitian : forall k, k.natAbs <= N -> r (-k) = star (r k))
    (even : forall k, k.natAbs <= N -> r (-k) = r k) :
    ∃! x : Fin (N + 1) -> Real,
      forall k : Int, k.natAbs <= N ->
        realEvenMomentCoordinates N x k = r k := by
  let x : Fin (N + 1) -> Real := fun i => (r (i : Nat)).re
  have realValue (k : Int) (hbound : k.natAbs <= N) :
      ((r k).re : Complex) = r k := by
    apply Complex.ext
    · simp
    · have hfixed : r k = star (r k) :=
        (even k hbound).symm.trans (hermitian k hbound)
      have him := congrArg Complex.im hfixed
      change (r k).im = -(r k).im at him
      simp only [Complex.ofReal_im]
      linarith
  have representation : forall k : Int, k.natAbs <= N ->
      realEvenMomentCoordinates N x k = r k := by
    intro k hbound
    cases k with
    | ofNat n =>
        have hn : n <= N := by simpa using hbound
        simpa [realEvenMomentCoordinates, x, hn] using
          realValue (n : Int) hbound
    | negSucc n =>
        have hboundNat : n + 1 <= N := by simpa using hbound
        have hn : n < N := by omega
        have hpositive : r (Int.negSucc n) = r ((n + 1 : Nat) : Int) := by
          have h := even (Int.negSucc n) hbound
          simpa [Int.negSucc_eq] using h.symm
        rw [realEvenMomentCoordinates, dif_pos hn]
        change (((r ((n + 1 : Nat) : Int)).re : Real) : Complex) =
          r (Int.negSucc n)
        rw [show (r ((n + 1 : Nat) : Int)).re = (r (Int.negSucc n)).re by
          exact congrArg Complex.re hpositive.symm]
        exact realValue (Int.negSucc n) hbound
  refine ⟨x, representation, ?_⟩
  intro x' representation'
  funext i
  have hx := representation ((i : Nat) : Int) (by omega)
  have hx' := representation' ((i : Nat) : Int) (by omega)
  simpa [realEvenMomentCoordinates, show (i : Nat) <= N by omega] using
    congrArg Complex.re (hx'.trans hx.symm)

private theorem circle_moment_hermitian_window
    (mu : FiniteMeasure Circle) (N : Nat) (k : Int)
    (hbound : k.natAbs <= N) :
    circleMoment (mu : Measure Circle) (-k) =
      star (circleMoment (mu : Measure Circle) k) := by
  have hHermitian := circle_moment_toeplitz_isHermitian (mu : Measure Circle) N
  cases k with
  | ofNat n =>
      let j : Fin (N + 1) := ⟨n, by simpa using hbound⟩
      have h := hHermitian.apply (0 : Fin (N + 1)) j
      simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm
  | negSucc n =>
      let j : Fin (N + 1) := ⟨n + 1, by simpa using hbound⟩
      have h := hHermitian.apply j (0 : Fin (N + 1))
      simpa [toeplitzMatrix, j, Int.negSucc_eq] using h.symm

private theorem circle_moment_map_inv (mu : FiniteMeasure Circle) (k : Int) :
    circleMoment ((mu.map Inv.inv : FiniteMeasure Circle) : Measure Circle) k =
      circleMoment (mu : Measure Circle) (-k) := by
  simp only [circleMoment, FiniteMeasure.toMeasure_map]
  have integrandContinuous : Continuous fun z : Circle =>
      (z : Complex) ^ (-k) := by
    exact continuous_subtype_val.zpow₀ (-k) fun z =>
      Or.inl (Circle.coe_ne_zero z)
  rw [integral_map measurable_inv.aemeasurable
    integrandContinuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [show ((↑(z⁻¹) : Complex)) = (z : Complex)⁻¹ by exact Circle.coe_inv z]
  rw [_root_.inv_zpow']

private theorem finite_measure_map_inv_inv (mu : FiniteMeasure Circle) :
    (mu.map Inv.inv).map Inv.inv = mu := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map]
  rw [Measure.map_map measurable_inv measurable_inv]
  simp

private theorem symmetrized_measure_inv_invariant (sigma : FiniteMeasure Circle) :
    let mu : FiniteMeasure Circle :=
      (2 : NNReal)⁻¹ • (sigma + sigma.map Inv.inv)
    mu.map Inv.inv = mu := by
  dsimp only
  rw [FiniteMeasure.map_smul, FiniteMeasure.map_add measurable_inv,
    finite_measure_map_inv_inv]
  ac_rfl

private theorem toeplitz_matrix_eq_of_window
    (N : Nat) (r q : Int -> Complex)
    (equal : forall k : Int, k.natAbs <= N -> r k = q k) :
    toeplitzMatrix r N = toeplitzMatrix q N := by
  ext j k
  apply equal
  have hj := j.isLt
  have hk := k.isLt
  simp only [Nat.lt_add_one_iff] at hj hk
  omega

/-- Finite common positive-spectrum feasibility is equivalent to one positive
Hermitian Toeplitz moment system satisfying every supplied linear observation.
The general window has exactly `2 * (N + 1) - 1` real coordinates; imposing
the even real symmetry reduces it to `N + 1`. -/
theorem common_spectrum_master_feasibility
    (N : Nat) (S O : Type*) [AddCommMonoid O] [Module Real O]
    (observation : S ->
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex →ₗ[Real] O)
    (admissible : S -> Set O) :
    ((∃ mu : FiniteMeasure Circle,
        ∀ s, observation s
          (toeplitzMatrix (circleMoment (mu : Measure Circle)) N) ∈ admissible s) ↔
      ∃ y : Int -> Complex,
        Matrix.PosSemidef (toeplitzMatrix y N) ∧
        (∀ k, k.natAbs <= N -> y (-k) = star (y k)) ∧
        (∀ s, observation s (toeplitzMatrix y N) ∈ admissible s) ∧
        ∃! x : Fin (2 * (N + 1) - 1) -> Real,
          ∀ k, k.natAbs <= N -> hermitianMomentCoordinates N x k = y k) ∧
    ((∃ mu : FiniteMeasure Circle,
        mu.map Inv.inv = mu ∧
        ∀ s, observation s
          (toeplitzMatrix (circleMoment (mu : Measure Circle)) N) ∈ admissible s) ↔
      ∃ y : Int -> Complex,
        Matrix.PosSemidef (toeplitzMatrix y N) ∧
        (∀ k, k.natAbs <= N -> y (-k) = star (y k)) ∧
        (∀ k, k.natAbs <= N -> y (-k) = y k) ∧
        (∀ s, observation s (toeplitzMatrix y N) ∈ admissible s) ∧
        ∃! x : Fin (N + 1) -> Real,
          ∀ k, k.natAbs <= N -> realEvenMomentCoordinates N x k = y k) := by
  constructor
  · constructor
    · rintro ⟨mu, constraints⟩
      let y := circleMoment (mu : Measure Circle)
      refine ⟨y, circle_moment_toeplitz_posSemidef (mu : Measure Circle) N,
        ?_, constraints, ?_⟩
      · exact fun k hbound => circle_moment_hermitian_window mu N k hbound
      · apply hermitian_moment_coordinates_existsUnique
        exact fun k hbound => by
          simpa [y] using circle_moment_hermitian_window mu N k hbound
    · rintro ⟨y, positive, hermitian, constraints, _coordinates⟩
      let r : Int -> Complex := fun k => if k.natAbs <= N then y k else 0
      have rHermitian (k : Int) : r (-k) = star (r k) := by
        by_cases hbound : k.natAbs <= N
        · simp [r, hbound, hermitian k hbound]
        · simp [r, hbound]
      have rMatrix : toeplitzMatrix r N = toeplitzMatrix y N := by
        apply toeplitz_matrix_eq_of_window
        intro k hbound
        simp [r, hbound]
      have rPositive : Matrix.PosSemidef (toeplitzMatrix r N) := by
        rwa [rMatrix]
      obtain ⟨mu, moments⟩ :=
        truncated_circle_moment_of_posSemidef N r rHermitian rPositive
      have recovered (k : Int) (hbound : k.natAbs <= N) :
          circleMoment (mu : Measure Circle) k = y k := by
        simpa only [circleMoment, r, if_pos hbound] using moments k hbound
      refine ⟨mu, ?_⟩
      intro s
      rw [toeplitz_matrix_eq_of_window N _ y]
      · exact constraints s
      · exact recovered
  · constructor
    · rintro ⟨mu, invariant, constraints⟩
      let y := circleMoment (mu : Measure Circle)
      have even (k : Int) : y (-k) = y k := by
        dsimp only [y]
        rw [← circle_moment_map_inv mu k, invariant]
      refine ⟨y, circle_moment_toeplitz_posSemidef (mu : Measure Circle) N,
        ?_, fun k _ => even k, constraints, ?_⟩
      · exact fun k hbound => circle_moment_hermitian_window mu N k hbound
      · apply real_even_moment_coordinates_existsUnique
        · exact fun k hbound => circle_moment_hermitian_window mu N k hbound
        · exact fun k _ => even k
    · rintro ⟨y, positive, hermitian, even, constraints, _coordinates⟩
      let r : Int -> Complex := fun k => if k.natAbs <= N then y k else 0
      have rHermitian (k : Int) : r (-k) = star (r k) := by
        by_cases hbound : k.natAbs <= N
        · simp [r, hbound, hermitian k hbound]
        · simp [r, hbound]
      have rMatrix : toeplitzMatrix r N = toeplitzMatrix y N := by
        apply toeplitz_matrix_eq_of_window
        intro k hbound
        simp [r, hbound]
      have rPositive : Matrix.PosSemidef (toeplitzMatrix r N) := by
        rwa [rMatrix]
      obtain ⟨sigma, moments⟩ :=
        truncated_circle_moment_of_posSemidef N r rHermitian rPositive
      have recovered (k : Int) (hbound : k.natAbs <= N) :
          circleMoment (sigma : Measure Circle) k = y k := by
        simpa only [circleMoment, r, if_pos hbound] using moments k hbound
      let mu : FiniteMeasure Circle :=
        (2 : NNReal)⁻¹ • (sigma + sigma.map Inv.inv)
      have symmetricRecovered (k : Int) (hbound : k.natAbs <= N) :
          circleMoment (mu : Measure Circle) k = y k := by
        have integrablePower (nu : FiniteMeasure Circle) :
            Integrable (fun z : Circle => (z : Complex) ^ (-k))
              (nu : Measure Circle) := by
          have continuousPower : Continuous fun z : Circle =>
              (z : Complex) ^ (-k) := by
            exact continuous_subtype_val.zpow₀ (-k) fun z =>
              Or.inl (Circle.coe_ne_zero z)
          simpa using continuousPower.continuousOn.integrableOn_compact
            (μ := (nu : Measure Circle)) isCompact_univ
        simp only [mu, circleMoment, FiniteMeasure.toMeasure_smul,
          FiniteMeasure.toMeasure_add]
        rw [integral_smul_nnreal_measure]
        rw [integral_add_measure (integrablePower sigma)
          (integrablePower (sigma.map Inv.inv))]
        change (((2 : NNReal)⁻¹ : Real) : Complex) *
          (circleMoment (sigma : Measure Circle) k +
            circleMoment ((sigma.map Inv.inv : FiniteMeasure Circle) : Measure Circle) k) =
          y k
        rw [circle_moment_map_inv, recovered k hbound,
          recovered (-k) (by simpa using hbound), even k hbound]
        norm_num
        ring
      refine ⟨mu, symmetrized_measure_inv_invariant sigma, ?_⟩
      · intro s
        rw [toeplitz_matrix_eq_of_window N _ y]
        · exact constraints s
        · exact symmetricRecovered

#print axioms momentCoordinateEquiv
#print axioms hermitianMomentCoordinates
#print axioms realEvenMomentCoordinates
#print axioms common_spectrum_master_feasibility

end D5.S3.Observer.BlockStructure.CommonSpectrumMasterFeasibility
