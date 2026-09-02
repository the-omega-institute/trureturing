/- GID: D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir
   generality: I
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ordered prime holonomy loses its linear phase but retains squared winding at second order. -/

import D5.S3.Observer.AgencyHolonomy.GoldenScalarDihedralBlindness
import D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
import D5.S3.Quantum.FiniteDimensional
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 searches found the exact owners `goldenPrimeHolonomy` and
     `fourierPhase`, which are imported and used on their existing carriers.
     No frozen theorem states the local trace Casimir together with the
     weighted observer-log consequence and first-order cancellation.
   * Pinned Mathlib supplies infinite dihedral normal forms, matrix trace,
     trigonometric iterated derivatives, and differentiation of a summable
     series. No assembled holonomy-Casimir theorem was found.
   * Searches of every installed non-Mathlib Lean package found no theorem
     about a dihedral holonomy trace or a squared-winding observer series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.OrderedPrimeHolonomyCasimir

open D5.S3.Observer.AgencyHolonomy.GoldenCharacterQuotient
open D5.S3.Observer.AgencyHolonomy.GoldenScalarDihedralBlindness
open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators Matrix

noncomputable section

universe u

/-- The source weight is the product of `p^(-s)` along the ordered prime word. -/
def orderedPrimeWordWeight (s : Real) (word : List UnramifiedPrime) : Real :=
  (word.map fun p => ((p.1 : Real) ^ (-s))).prod

/-- The two diagonal phase channels of an integral rotation. -/
def rotationObserverMatrix (theta : Real) (k : Int) : Matrix (Fin 2) (Fin 2) Complex :=
  !![fourierPhase (-(k : Real)) theta, 0;
     0, fourierPhase (k : Real) theta]

private theorem rotationObserverMatrix_add (theta : Real) (k l : Int) :
    rotationObserverMatrix theta (k + l) =
      rotationObserverMatrix theta k * rotationObserverMatrix theta l := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotationObserverMatrix, Matrix.mul_apply]
    convert
      (fourier_phase_character_laws
        (-(k : Real)) (-(l : Real)) theta 0).2.2.1 using 1
    all_goals ring_nf
  · simp [rotationObserverMatrix, Matrix.mul_apply]
  · simp [rotationObserverMatrix, Matrix.mul_apply]
  · simp [rotationObserverMatrix, Matrix.mul_apply]
    simpa only [Int.cast_add] using
      (fourier_phase_character_laws
        (k : Real) (l : Real) theta 0).2.2.1

private theorem rotationObserverMatrix_reflection (theta : Real) (k : Int) :
    rotationObserverMatrix theta k * qubitX =
      qubitX * rotationObserverMatrix theta (-k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationObserverMatrix, qubitX, Matrix.mul_apply]

private theorem reflection_rotationObserverMatrix (theta : Real) (k : Int) :
    qubitX * rotationObserverMatrix theta k =
      rotationObserverMatrix theta (-k) * qubitX := by
  rw [rotationObserverMatrix_reflection]
  simp

private theorem qubitX_mul_self : qubitX * qubitX = 1 := by
  simpa only [pow_two] using qubit_weyl_star.2.2.2.1

/-- The source's two-dimensional representation of infinite-dihedral
holonomy, with rotations diagonal and reflections exchanging the channels. -/
def dihedralObserverRepresentation (theta : Real) :
    DihedralGroup 0 →* Matrix (Fin 2) (Fin 2) Complex where
  toFun g :=
    match g with
    | DihedralGroup.r k =>
        rotationObserverMatrix theta (ZMod.cast k : Int)
    | DihedralGroup.sr k =>
        qubitX *
          rotationObserverMatrix theta (ZMod.cast k : Int)
  map_one' := by
    rw [DihedralGroup.one_def]
    change rotationObserverMatrix theta 0 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotationObserverMatrix, fourierPhase]
  map_mul' g h := by
    rcases g with k | k <;> rcases h with l | l
    · simp only [DihedralGroup.r_mul_r, ZMod.cast_add']
      exact rotationObserverMatrix_add theta _ _
    · simp only [DihedralGroup.r_mul_sr, ZMod.cast_sub']
      rw [← Matrix.mul_assoc, rotationObserverMatrix_reflection,
        Matrix.mul_assoc, ← rotationObserverMatrix_add]
      congr 2
      ring
    · simp only [DihedralGroup.sr_mul_r, ZMod.cast_add']
      rw [Matrix.mul_assoc, ← rotationObserverMatrix_add]
    · simp only [DihedralGroup.sr_mul_sr, ZMod.cast_sub']
      symm
      calc
        (qubitX * rotationObserverMatrix theta (ZMod.cast k : Int)) *
              (qubitX * rotationObserverMatrix theta (ZMod.cast l : Int)) =
            qubitX *
              (rotationObserverMatrix theta (ZMod.cast k : Int) *
                qubitX) *
              rotationObserverMatrix theta (ZMod.cast l : Int) := by
          simp only [Matrix.mul_assoc]
        _ = qubitX *
              (qubitX *
                rotationObserverMatrix theta (-(ZMod.cast k : Int))) *
              rotationObserverMatrix theta (ZMod.cast l : Int) := by
          rw [rotationObserverMatrix_reflection]
        _ = rotationObserverMatrix theta (-(ZMod.cast k : Int)) *
              rotationObserverMatrix theta (ZMod.cast l : Int) := by
          rw [← Matrix.mul_assoc, qubitX_mul_self, one_mul]
        _ = rotationObserverMatrix theta
              (-(ZMod.cast k : Int) + ZMod.cast l) := by
          rw [← rotationObserverMatrix_add]
        _ = rotationObserverMatrix theta
              (ZMod.cast l - ZMod.cast k) := by
          congr 1
          ring

private theorem rotationObserverMatrix_trace (theta : Real) (k : Int) :
    (Matrix.trace (rotationObserverMatrix theta k)).re =
      2 * Real.cos ((k : Real) * theta) := by
  simp [Matrix.trace, rotationObserverMatrix, fourierPhase,
    Complex.exp_re, Complex.mul_re, Complex.mul_im, Real.cos_neg]
  ring_nf

private theorem rotationObserverMatrix_first_derivative_at_zero (k : Int) :
    iteratedDeriv 1
        (fun theta : Real => (Matrix.trace (rotationObserverMatrix theta k)).re) 0 = 0 := by
  have htrace :
      (fun theta : Real => (Matrix.trace (rotationObserverMatrix theta k)).re) =
        fun theta : Real => 2 * Real.cos ((k : Real) * theta) := by
    funext theta
    exact rotationObserverMatrix_trace theta k
  rw [htrace, iteratedDeriv_const_mul_field]
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (n := 1) Real.contDiff_cos (k : Real)) 0
  rw [hcomp]
  simp

private theorem rotationObserverMatrix_second_derivative_at_zero (k : Int) :
    -iteratedDeriv 2
        (fun theta : Real => (Matrix.trace (rotationObserverMatrix theta k)).re) 0 =
      2 * (k : Real) ^ 2 := by
  have htrace :
      (fun theta : Real => (Matrix.trace (rotationObserverMatrix theta k)).re) =
        fun theta : Real => 2 * Real.cos ((k : Real) * theta) := by
    funext theta
    exact rotationObserverMatrix_trace theta k
  rw [htrace, iteratedDeriv_const_mul_field]
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (n := 2) Real.contDiff_cos (k : Real)) 0
  rw [hcomp]
  norm_num [show (2 : Nat) = 2 * 1 by norm_num,
    Real.iteratedDeriv_even_cos]

/-- The coefficient of a repeated orbit in the source observer log. -/
def observerOrbitAmplitude
    {ι : Type u} (word : ι -> List UnramifiedPrime) (s : Real)
    (x : ι × Nat) : Real :=
  orderedPrimeWordWeight s (word x.1) ^ (x.2 + 1) / (x.2 + 1 : Real)

/-- The winding of the positive repeat indexed by `x`. -/
def repeatedOrbitWinding
    {ι : Type u} (winding : ι -> ZMod 0) (x : ι × Nat) : Real :=
  (x.2 + 1 : Real) * ((ZMod.cast (winding x.1) : Int) : Real)

/-- The source observer log: sum over primitive histories and every positive
repeat, evaluated through the actual prime-word holonomy representation. -/
def orderedPrimeObserverLog
    {ι : Type u} [Countable ι]
    (word : ι -> List UnramifiedPrime) (s theta : Real) : Real :=
  ∑' x : ι × Nat,
    observerOrbitAmplitude word s x *
      (Matrix.trace
        (dihedralObserverRepresentation theta
          ((goldenPrimeHolonomy (word x.1)) ^ (x.2 + 1)))).re

private theorem observer_holonomy_trace
    {ι : Type u} (word : ι -> List UnramifiedPrime) (winding : ι -> ZMod 0)
    (orientation : ∀ i,
      goldenPrimeHolonomy (word i) =
        DihedralGroup.r (winding i))
    (i : ι) (m : Nat) (theta : Real) :
    (Matrix.trace
      (dihedralObserverRepresentation theta
        ((goldenPrimeHolonomy (word i)) ^ m))).re =
      2 * Real.cos
        ((m : Real) * ((ZMod.cast (winding i) : Int) : Real) * theta) := by
  have hpower :
      (goldenPrimeHolonomy (word i)) ^ m =
        DihedralGroup.r (winding i * (m : ZMod 0)) := by
    rw [orientation i, DihedralGroup.r_pow]
  rw [hpower]
  change
    (Matrix.trace
      (rotationObserverMatrix theta
        (ZMod.cast (winding i * (m : ZMod 0)) : Int))).re = _
  rw [ZMod.cast_mul', ZMod.cast_natCast']
  rw [rotationObserverMatrix_trace]
  congr 2
  push_cast
  ring

private theorem orderedPrimeWordWeight_pos
    (s : Real) (word : List UnramifiedPrime) :
    0 < orderedPrimeWordWeight s word := by
  induction word with
  | nil => simp [orderedPrimeWordWeight]
  | cons p tail ih =>
      rw [orderedPrimeWordWeight, List.map_cons, List.prod_cons]
      exact mul_pos
        (Real.rpow_pos_of_pos (by exact_mod_cast p.property.1.pos) _)
        (by simpa [orderedPrimeWordWeight] using ih)

/-- In the absolute-convergence region, the actual two-channel holonomy trace
has zero linear response and its negative second response is precisely the
positive weighted sum of all repeated squared windings. -/
theorem ordered_prime_holonomy_casimir
    {ι : Type u} [Countable ι]
    (word : ι -> List UnramifiedPrime) (winding : ι -> ZMod 0) (s : Real)
    (orientation : ∀ i,
      goldenPrimeHolonomy (word i) = DihedralGroup.r (winding i))
    (summableWeight : Summable fun x : ι × Nat =>
      |observerOrbitAmplitude word s x|)
    (summableLinearMoment : Summable fun x : ι × Nat =>
      |observerOrbitAmplitude word s x| *
        (2 * |repeatedOrbitWinding winding x|))
    (summableSquareMoment : Summable fun x : ι × Nat =>
      |observerOrbitAmplitude word s x| *
        (2 * repeatedOrbitWinding winding x ^ 2)) :
    (∀ (i : ι) (m : Nat),
      -iteratedDeriv 2
          (fun theta : Real =>
            (Matrix.trace
              (dihedralObserverRepresentation theta
                ((goldenPrimeHolonomy (word i)) ^ m))).re) 0 =
        2 * (m : Real) ^ 2 *
          ((ZMod.cast (winding i) : Int) : Real) ^ 2) ∧
    iteratedDeriv 1 (orderedPrimeObserverLog word s) 0 = 0 ∧
    -iteratedDeriv 2 (orderedPrimeObserverLog word s) 0 =
      ∑' x : ι × Nat,
        observerOrbitAmplitude word s x *
          (2 * repeatedOrbitWinding winding x ^ 2) ∧
    (∀ x : ι × Nat,
      0 ≤ observerOrbitAmplitude word s x *
        (2 * repeatedOrbitWinding winding x ^ 2)) := by
  let amplitude : ι × Nat -> Real := observerOrbitAmplitude word s
  let frequency : ι × Nat -> Real := repeatedOrbitWinding winding
  let orbitTerm : ι × Nat -> Real -> Real := fun x theta =>
    amplitude x * (2 * Real.cos (frequency x * theta))
  let firstTerm : ι × Nat -> Real -> Real := fun x theta =>
    -2 * amplitude x * frequency x * Real.sin (frequency x * theta)
  let secondTerm : ι × Nat -> Real -> Real := fun x theta =>
    -2 * amplitude x * frequency x ^ 2 * Real.cos (frequency x * theta)

  have localCasimir : ∀ (i : ι) (m : Nat),
      -iteratedDeriv 2
          (fun theta : Real =>
            (Matrix.trace
              (dihedralObserverRepresentation theta
                ((goldenPrimeHolonomy (word i)) ^ m))).re) 0 =
        2 * (m : Real) ^ 2 *
          ((ZMod.cast (winding i) : Int) : Real) ^ 2 := by
    intro i m
    have htrace :
        (fun theta : Real =>
          (Matrix.trace
            (dihedralObserverRepresentation theta
              ((goldenPrimeHolonomy (word i)) ^ m))).re) =
          fun theta : Real =>
            2 * Real.cos
              (((m : Real) * ((ZMod.cast (winding i) : Int) : Real)) * theta) := by
      funext theta
      rw [observer_holonomy_trace word winding orientation]
    rw [htrace, iteratedDeriv_const_mul_field]
    have hcomp := congrFun
      (iteratedDeriv_comp_const_mul (n := 2) Real.contDiff_cos
        ((m : Real) * ((ZMod.cast (winding i) : Int) : Real))) 0
    rw [hcomp]
    norm_num [show (2 : Nat) = 2 * 1 by norm_num,
      Real.iteratedDeriv_even_cos]
    ring

  have observerLogAsSeries :
      orderedPrimeObserverLog word s = fun theta => ∑' x, orbitTerm x theta := by
    funext theta
    rw [orderedPrimeObserverLog]
    apply tsum_congr
    intro x
    rw [observer_holonomy_trace word winding orientation]
    change amplitude x *
        (2 * Real.cos
          (((x.2 + 1 : Nat) : Real) *
            ((ZMod.cast (winding x.1) : Int) : Real) * theta)) =
      orbitTerm x theta
    simp only [orbitTerm, frequency, repeatedOrbitWinding]
    congr 3
    rw [Nat.cast_add, Nat.cast_one]

  have orbitTermDerivative : ∀ x theta,
      HasDerivAt (orbitTerm x) (firstTerm x theta) theta := by
    intro x theta
    simpa only [orbitTerm, firstTerm, Function.comp_apply, mul_neg, neg_mul,
      one_mul, mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_cos (frequency x * theta)).comp theta
        ((hasDerivAt_id theta).const_mul (frequency x))).const_mul
          (2 * amplitude x))

  have firstTermDerivative : ∀ x theta,
      HasDerivAt (firstTerm x) (secondTerm x theta) theta := by
    intro x theta
    simpa only [firstTerm, secondTerm, Function.comp_apply, mul_neg, neg_mul,
      one_mul, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_sin (frequency x * theta)).comp theta
        ((hasDerivAt_id theta).const_mul (frequency x))).const_mul
          (-2 * amplitude x * frequency x))

  have orbitTermDerivativeBound : ∀ x theta,
      ‖firstTerm x theta‖ ≤
        |amplitude x| * (2 * |frequency x|) := by
    intro x theta
    dsimp only [firstTerm]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    have hsin := Real.abs_sin_le_one (frequency x * theta)
    calc
      2 * |amplitude x| * |frequency x| *
            |Real.sin (frequency x * theta)| ≤
          (2 * |amplitude x| * |frequency x|) * 1 :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = |amplitude x| * (2 * |frequency x|) := by ring

  have firstTermDerivativeBound : ∀ x theta,
      ‖secondTerm x theta‖ ≤
        |amplitude x| * (2 * frequency x ^ 2) := by
    intro x theta
    dsimp only [secondTerm]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), sq_abs]
    have hcos := Real.abs_cos_le_one (frequency x * theta)
    calc
      2 * |amplitude x| * frequency x ^ 2 *
            |Real.cos (frequency x * theta)| ≤
          (2 * |amplitude x| * frequency x ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = |amplitude x| * (2 * frequency x ^ 2) := by ring

  have orbitTermSummableAtZero : Summable fun x => orbitTerm x 0 := by
    have hamplitude : Summable amplitude := by
      apply Summable.of_norm
      simpa only [Real.norm_eq_abs, amplitude] using summableWeight
    simpa only [orbitTerm, mul_zero, Real.cos_zero, mul_one] using
      hamplitude.mul_right 2

  have firstTermSummableAtZero : Summable fun x => firstTerm x 0 := by
    simp only [firstTerm, mul_zero, Real.sin_zero, mul_zero]
    exact summable_zero

  have firstSeriesDerivative : ∀ theta,
      HasDerivAt (fun z => ∑' x, orbitTerm x z)
        (∑' x, firstTerm x theta) theta := by
    intro theta
    exact hasDerivAt_tsum summableLinearMoment orbitTermDerivative
      orbitTermDerivativeBound orbitTermSummableAtZero theta

  have secondSeriesDerivative : ∀ theta,
      HasDerivAt (fun z => ∑' x, firstTerm x z)
        (∑' x, secondTerm x theta) theta := by
    intro theta
    exact hasDerivAt_tsum summableSquareMoment firstTermDerivative
      firstTermDerivativeBound firstTermSummableAtZero theta

  have observerLogDerivative :
      deriv (orderedPrimeObserverLog word s) =
        fun theta => ∑' x, firstTerm x theta := by
    funext theta
    rw [observerLogAsSeries]
    exact (firstSeriesDerivative theta).deriv

  have linearCancellation :
      iteratedDeriv 1 (orderedPrimeObserverLog word s) 0 = 0 := by
    rw [iteratedDeriv_one, observerLogDerivative]
    simp [firstTerm]

  have squareReadout :
      -iteratedDeriv 2 (orderedPrimeObserverLog word s) 0 =
        ∑' x, amplitude x * (2 * frequency x ^ 2) := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, observerLogDerivative,
      (secondSeriesDerivative 0).deriv]
    rw [← tsum_neg]
    apply tsum_congr
    intro x
    simp only [secondTerm, mul_zero, Real.cos_zero, mul_one]
    ring

  have positiveReadout : ∀ x : ι × Nat,
      0 ≤ amplitude x * (2 * frequency x ^ 2) := by
    intro x
    have hweight : 0 < orderedPrimeWordWeight s (word x.1) :=
      orderedPrimeWordWeight_pos s (word x.1)
    have hamplitude : 0 < amplitude x := by
      dsimp only [amplitude, observerOrbitAmplitude]
      positivity
    positivity

  refine ⟨localCasimir, linearCancellation, ?_, ?_⟩
  · simpa only [amplitude, frequency] using squareReadout
  · simpa only [amplitude, frequency] using positiveReadout

/-- The convergence hypotheses are jointly satisfiable on the empty orbit
carrier; this is a kernel-checked consistency witness, not a coverage clause. -/
example (s : Real) :
    let word : Empty -> List UnramifiedPrime := Empty.elim
    let winding : Empty -> ZMod 0 := Empty.elim
    (Summable fun x : Empty × Nat =>
      |observerOrbitAmplitude word s x|) ∧
    (Summable fun x : Empty × Nat =>
      |observerOrbitAmplitude word s x| *
        (2 * |repeatedOrbitWinding winding x|)) ∧
    (Summable fun x : Empty × Nat =>
      |observerOrbitAmplitude word s x| *
        (2 * repeatedOrbitWinding winding x ^ 2)) := by
  simp

#print axioms orderedPrimeWordWeight
#print axioms rotationObserverMatrix
#print axioms dihedralObserverRepresentation
#print axioms observerOrbitAmplitude
#print axioms repeatedOrbitWinding
#print axioms orderedPrimeObserverLog
#print axioms ordered_prime_holonomy_casimir

end

end D5.S3.Observer.AgencyHolonomy.OrderedPrimeHolonomyCasimir
