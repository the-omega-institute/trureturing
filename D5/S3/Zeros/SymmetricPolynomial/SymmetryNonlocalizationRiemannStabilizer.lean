/- GID: D5/S3/Zeros/SymmetricPolynomial/SymmetryNonlocalizationRiemannStabilizer
   generality: I
   mirror-B: D5/B/S3/Zeros/SymmetricPolynomial/SymmetryNonlocalizationRiemannStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full quartic symmetry does not localize zeros, while RH is mirror fixedness. -/

import D5.S3.Zeros.SymmetricPolynomial.FullSymmetryNonlocalization

/-!
# Symmetry nonlocalization and Riemann stabilizers

The source leaves `gamma` free. The frozen predecessor proves its explicit
quartic result when `gamma` is nonzero because it additionally records a
four-element cardinality statement. Here the zero-height factorization handles
the collapsed two-point set, so the source's exact zero-set and off-line
conclusions hold under only its stated assumption `delta != 0`.

Library-search audit trail (2026-09-05):

* D5 statement and body-shape searches found the frozen quartic predecessor,
  the mirror fixed-locus theorem, and one-way RH location results, but no owner
  combining the source's all-height quartic statement with its RH equivalence.
* Pinned Mathlib defines `RiemannHypothesis` with the exact zero, trivial-zero,
  and pole premises used below. It has no theorem identifying those points with
  conjugate-reflection fixed points.
* Searches over the other installed Lean packages found no matching quartic or
  RH mirror-fixed declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.SymmetricPolynomial.SymmetryNonlocalizationRiemannStabilizer

open Complex
open D5.S3.Weil.Convention
open D5.S3.Weil.ReflectionLedger
open D5.S3.Zeros.SymmetricPolynomial.FullSymmetryNonlocalization
open scoped ComplexConjugate

noncomputable section

/-- At zero height the source quartic is the square of its two distinct
horizontal linear factors. This is the new edge needed to remove the frozen
predecessor's extra `gamma != 0` premise. -/
private theorem offCriticalQuartic_zero_height_factorization
    (delta : Real) (s : Complex) :
    offCriticalQuartic delta 0 s =
      (((s - (1 / 2 : Complex) - delta) *
        (s - (1 / 2 : Complex) + delta)) ^ 2) := by
  unfold offCriticalQuartic
  dsimp
  ring

private theorem offCriticalQuartic_zero_height_zero_iff
    (delta : Real) (s : Complex) :
    offCriticalQuartic delta 0 s = 0 <-> s ∈ sourceZeros delta 0 := by
  rw [offCriticalQuartic_zero_height_factorization]
  simp only [sq_eq_zero_iff, mul_eq_zero]
  suffices
      (s - (1 / 2 : Complex) - delta = 0 ∨
        s - (1 / 2 : Complex) + delta = 0) <->
      (s = (1 / 2 : Complex) + delta ∨
        s = (1 / 2 : Complex) - delta) by
    simpa [sourceZeros, rootPP, rootPM, rootMP, rootMM] using this
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

private theorem offCriticalQuartic_zero_displacement_factorization
    (gamma : Real) (s : Complex) :
    offCriticalQuartic 0 gamma s =
      (((s - (1 / 2 : Complex) - I * gamma) *
        (s - (1 / 2 : Complex) + I * gamma)) ^ 2) := by
  unfold offCriticalQuartic
  dsimp
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_four]
  ring

private theorem offCriticalQuartic_zero_displacement_zero_iff
    (gamma : Real) (s : Complex) :
    offCriticalQuartic 0 gamma s = 0 <-> s ∈ sourceZeros 0 gamma := by
  rw [offCriticalQuartic_zero_displacement_factorization]
  simp only [sq_eq_zero_iff, mul_eq_zero]
  suffices
      (s - (1 / 2 : Complex) - I * gamma = 0 ∨
        s - (1 / 2 : Complex) + I * gamma = 0) <->
      (s = (1 / 2 : Complex) + I * gamma ∨
        s = (1 / 2 : Complex) - I * gamma) by
    simpa [sourceZeros, rootPP, rootPM, rootMP, rootMM] using this
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

private theorem riemann_hypothesis_iff_mirror_fixed :
    RiemannHypothesis <->
      forall rho : Complex,
        riemannZeta rho = 0 ->
        (¬ exists n : Nat, rho = -2 * (n + 1)) ->
        rho ≠ 1 ->
        mirror rho = rho := by
  constructor
  · intro hRH rho hZero hNontrivial hOne
    have hLine : rho.re = (1 : Real) / 2 :=
      hRH rho hZero hNontrivial hOne
    apply Complex.ext
    · norm_num [mirror, reflection, hLine]
    · simp [mirror, reflection]
  · intro hFixed rho hZero hNontrivial hOne
    have hLine := mirror_fixed_re_eq rho
      (hFixed rho hZero hNontrivial hOne)
    simpa [criticalAbscissa] using hLine

/-- Theorem 21.1: the source quartic has both functional symmetries and exactly
the displayed zero set at every real height. If `delta` is nonzero, every zero
is off the critical line, giving a same-witness counterexample to localization.
For the classical zeta function, RH is instead exactly the assertion that every
Mathlib-nontrivial zero is fixed by conjugate reflection. -/
theorem full_symmetry_nonlocalization_and_rh_stabilizer
    (delta gamma : Real) :
    (exists F : Complex -> Complex,
      F = offCriticalQuartic delta gamma /\
      Differentiable Complex F /\
      HasFullZetaSymmetry F /\
      (forall s, F s = 0 <-> s ∈ sourceZeros delta gamma) /\
      (delta ≠ 0 ->
        (forall s, F s = 0 -> s.re ≠ criticalAbscissa) /\
        (¬ FixedLineLocalization F) /\
        ¬ (forall G : Complex -> Complex,
          Differentiable Complex G -> HasFullZetaSymmetry G ->
            FixedLineLocalization G))) /\
    (RiemannHypothesis <->
      forall rho : Complex,
        riemannZeta rho = 0 ->
        (¬ exists n : Nat, rho = -2 * (n + 1)) ->
        rho ≠ 1 ->
        mirror rho = rho) := by
  have hEntire : Differentiable Complex (offCriticalQuartic delta gamma) := by
    unfold offCriticalQuartic
    fun_prop
  have hSymmetry : HasFullZetaSymmetry (offCriticalQuartic delta gamma) := by
    constructor
    · intro s
      simp only [offCriticalQuartic, reflection]
      ring
    · intro s
      simp only [offCriticalQuartic, map_mul, map_add, map_sub, map_pow,
        map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
  have hZeros : forall s,
      offCriticalQuartic delta gamma s = 0 <->
        s ∈ sourceZeros delta gamma := by
    intro s
    by_cases hdelta : delta = 0
    · subst delta
      exact offCriticalQuartic_zero_displacement_zero_iff gamma s
    · by_cases hgamma : gamma = 0
      · subst gamma
        exact offCriticalQuartic_zero_height_zero_iff delta s
      · have hFrozen :=
          full_symmetry_not_fixed_line_localization delta gamma hdelta hgamma
        rcases hFrozen.1 with ⟨F, hF, _, _, hFrozenZeros, _, _⟩
        simpa [hF] using hFrozenZeros s
  refine ⟨?_, riemann_hypothesis_iff_mirror_fixed⟩
  refine ⟨offCriticalQuartic delta gamma, rfl, hEntire, hSymmetry, hZeros, ?_⟩
  intro hdelta
  have hOff : forall s,
      offCriticalQuartic delta gamma s = 0 ->
        s.re ≠ criticalAbscissa := by
    intro s hs hLine
    have hMember := (hZeros s).1 hs
    simp only [sourceZeros, Finset.mem_insert, Finset.mem_singleton] at hMember
    rcases hMember with h | h | h | h <;> subst s <;>
      simp [rootPP, rootPM, rootMP, rootMM, criticalAbscissa] at hLine <;>
      apply hdelta <;> linarith
  have hRoot : offCriticalQuartic delta gamma (rootPP delta gamma) = 0 :=
    (hZeros (rootPP delta gamma)).2 (by simp [sourceZeros])
  have hNotLocalized :
      ¬ FixedLineLocalization (offCriticalQuartic delta gamma) := by
    intro hLocalized
    exact hOff (rootPP delta gamma) hRoot
      (hLocalized (rootPP delta gamma) hRoot)
  refine ⟨hOff, hNotLocalized, ?_⟩
  intro hUniversal
  exact hNotLocalized
    (hUniversal (offCriticalQuartic delta gamma) hEntire hSymmetry)

-- The new factorization is used at the parameter value omitted by the predecessor.
example (delta : Real) (s : Complex) :
    offCriticalQuartic delta 0 s =
      (((s - (1 / 2 : Complex) - delta) *
        (s - (1 / 2 : Complex) + delta)) ^ 2) :=
  offCriticalQuartic_zero_height_factorization delta s

-- The source's nonzero transverse displacement is essential for off-line zeros.
example (gamma : Real) :
    ¬ exists F : Complex -> Complex,
      F = offCriticalQuartic 0 gamma /\
      (forall s, F s = 0 <-> s ∈ sourceZeros 0 gamma) /\
      forall s, F s = 0 -> s.re ≠ criticalAbscissa := by
  rintro ⟨F, rfl, hZeros, hOff⟩
  have hRoot : offCriticalQuartic 0 gamma (rootPP 0 gamma) = 0 :=
    (hZeros (rootPP 0 gamma)).2 (by simp [sourceZeros])
  exact hOff (rootPP 0 gamma) hRoot
    (by simp [rootPP, criticalAbscissa])

-- The boxed RH clause is a public projection of the primary theorem.
example :
    RiemannHypothesis <->
      forall rho : Complex,
        riemannZeta rho = 0 ->
        (¬ exists n : Nat, rho = -2 * (n + 1)) ->
        rho ≠ 1 ->
        mirror rho = rho :=
  (full_symmetry_nonlocalization_and_rh_stabilizer 0 0).2

#print axioms full_symmetry_nonlocalization_and_rh_stabilizer

end


end D5.S3.Zeros.SymmetricPolynomial.SymmetryNonlocalizationRiemannStabilizer
