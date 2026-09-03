/- GID: D5/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization
   generality: I
   mirror-B: D5/B/S3/Zeros/SymmetricPolynomial/FullSymmetryNonlocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An explicit entire quartic has full zeta symmetry and four off-line zeros. -/

import D5.S3.Weil.ReflectionLedger
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * The repository owners `ReflectionLedger.reflection` and
     `Convention.criticalAbscissa` are reused for the source's maps and fixed line.
   * Related `ZeroSymmetryAction` and `ConvolutionSquareOffLineOrbits` results assume
     supplied zero data; neither constructs this explicit quartic counterexample.
   * Pinned Mathlib supplies complex conjugation, `Complex.I_sq`, zero-product
     reduction, differentiability rules, and finite-set operations. Loogle found
     generic polynomial root APIs but no theorem for this source-specific quartic.
-/

namespace D5.S3.Zeros.SymmetricPolynomial.FullSymmetryNonlocalization

open Complex
open D5.S3.Weil.Convention
open D5.S3.Weil.ReflectionLedger
open scoped ComplexConjugate

noncomputable section

/-- Source lines 247-254: the explicit quartic, written with `z = s - 1/2`. -/
def offCriticalQuartic (delta gamma : ℝ) (s : ℂ) : ℂ :=
  let z := s - (1 / 2 : ℂ)
  ((z - delta) ^ 2 + gamma ^ 2) * ((z + delta) ^ 2 + gamma ^ 2)

/-- Source lines 256-260: the root `1/2 + delta + i gamma`. -/
def rootPP (delta gamma : ℝ) : ℂ :=
  (1 / 2 : ℂ) + delta + I * gamma

/-- Source lines 256-260: the root `1/2 + delta - i gamma`. -/
def rootPM (delta gamma : ℝ) : ℂ :=
  (1 / 2 : ℂ) + delta - I * gamma

/-- Source lines 256-260: the root `1/2 - delta + i gamma`. -/
def rootMP (delta gamma : ℝ) : ℂ :=
  (1 / 2 : ℂ) - delta + I * gamma

/-- Source lines 256-260: the root `1/2 - delta - i gamma`. -/
def rootMM (delta gamma : ℝ) : ℂ :=
  (1 / 2 : ℂ) - delta - I * gamma

/-- Source lines 256-260: the four-point zero set named immediately above Theorem 2.1. -/
def sourceZeros (delta gamma : ℝ) : Finset ℂ :=
  {rootPP delta gamma, rootPM delta gamma, rootMP delta gamma, rootMM delta gamma}

/-- Source lines 160-184 and 262-272: the two displayed symmetries generating
the full Klein-four `G_zeta` symmetry. -/
def HasFullZetaSymmetry (F : ℂ → ℂ) : Prop :=
  (∀ s, F (reflection s) = F s) ∧
    ∀ s, F (conj s) = conj (F s)

/-- Source lines 274-284: all zeros lie on the fixed critical line. -/
def FixedLineLocalization (F : ℂ → ℂ) : Prop :=
  ∀ s, F s = 0 → s.re = criticalAbscissa

private theorem offCriticalQuartic_factorization (delta gamma : ℝ) (s : ℂ) :
    offCriticalQuartic delta gamma s =
      (s - rootPP delta gamma) * (s - rootPM delta gamma) *
        ((s - rootMP delta gamma) * (s - rootMM delta gamma)) := by
  unfold offCriticalQuartic rootPP rootPM rootMP rootMM
  dsimp
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_four]
  ring

private theorem offCriticalQuartic_zero_iff (delta gamma : ℝ) (s : ℂ) :
    offCriticalQuartic delta gamma s = 0 ↔ s ∈ sourceZeros delta gamma := by
  rw [offCriticalQuartic_factorization]
  simp only [sourceZeros, Finset.mem_insert, Finset.mem_singleton, mul_eq_zero, sub_eq_zero]
  tauto

private theorem sourceZeros_card (delta gamma : ℝ)
    (hdelta : delta ≠ 0) (hgamma : gamma ≠ 0) :
    (sourceZeros delta gamma).card = 4 := by
  let a := rootPP delta gamma
  let b := rootPM delta gamma
  let c := rootMP delta gamma
  let d := rootMM delta gamma
  have hab : a ≠ b := by
    intro h
    have him := congrArg Complex.im h
    simp [a, b, rootPP, rootPM] at him
    apply hgamma
    linarith
  have hac : a ≠ c := by
    intro h
    have hre := congrArg Complex.re h
    simp [a, c, rootPP, rootMP] at hre
    apply hdelta
    linarith
  have had : a ≠ d := by
    intro h
    have hre := congrArg Complex.re h
    simp [a, d, rootPP, rootMM] at hre
    apply hdelta
    linarith
  have hbc : b ≠ c := by
    intro h
    have hre := congrArg Complex.re h
    simp [b, c, rootPM, rootMP] at hre
    apply hdelta
    linarith
  have hbd : b ≠ d := by
    intro h
    have hre := congrArg Complex.re h
    simp [b, d, rootPM, rootMM] at hre
    apply hdelta
    linarith
  have hcd : c ≠ d := by
    intro h
    have him := congrArg Complex.im h
    simp [c, d, rootMP, rootMM] at him
    apply hgamma
    linarith
  have ha : a ∉ ({b, c, d} : Finset ℂ) := by
    simp [hab, hac, had]
  have hb : b ∉ ({c, d} : Finset ℂ) := by
    simp [hbc, hbd]
  have hc : c ∉ ({d} : Finset ℂ) := by
    simpa using hcd
  change ({a, b, c, d} : Finset ℂ).card = 4
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
    Finset.card_insert_of_notMem hc]
  rfl

private theorem offCriticalQuartic_entire (delta gamma : ℝ) :
    Differentiable ℂ (offCriticalQuartic delta gamma) := by
  unfold offCriticalQuartic
  fun_prop

private theorem offCriticalQuartic_full_symmetry (delta gamma : ℝ) :
    HasFullZetaSymmetry (offCriticalQuartic delta gamma) := by
  constructor
  · intro s
    simp only [offCriticalQuartic, reflection]
    ring
  · intro s
    simp only [offCriticalQuartic, map_mul, map_add, map_sub, map_pow,
      map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

private theorem offCriticalQuartic_zeros_off_line (delta gamma : ℝ)
    (hdelta : delta ≠ 0) :
    ∀ s, offCriticalQuartic delta gamma s = 0 → s.re ≠ criticalAbscissa := by
  intro s hs
  rw [offCriticalQuartic_zero_iff] at hs
  simp only [sourceZeros, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    intro hline <;>
    simp [rootPP, rootPM, rootMP, rootMM, criticalAbscissa] at hline <;>
    apply hdelta <;>
    linarith

/-- Theorem 2.1 (source lines 274-288): the source quartic is an entire function
with both generators of full `G_zeta` symmetry, exactly four stated zeros, and
every zero off the critical line. Consequently full symmetry does not imply
fixed-line localization, even among entire functions. -/
theorem full_symmetry_not_fixed_line_localization
    (delta gamma : ℝ) (hdelta : delta ≠ 0) (hgamma : gamma ≠ 0) :
    (∃ F : ℂ → ℂ,
      F = offCriticalQuartic delta gamma ∧
      Differentiable ℂ F ∧
      HasFullZetaSymmetry F ∧
      (∀ s, F s = 0 ↔ s ∈ sourceZeros delta gamma) ∧
      (sourceZeros delta gamma).card = 4 ∧
      ∀ s, F s = 0 → s.re ≠ criticalAbscissa) ∧
    ¬ (∀ F : ℂ → ℂ,
      Differentiable ℂ F → HasFullZetaSymmetry F → FixedLineLocalization F) := by
  have hEntire := offCriticalQuartic_entire delta gamma
  have hSymmetry := offCriticalQuartic_full_symmetry delta gamma
  have hZeros := offCriticalQuartic_zero_iff delta gamma
  have hCard := sourceZeros_card delta gamma hdelta hgamma
  have hOff := offCriticalQuartic_zeros_off_line delta gamma hdelta
  constructor
  · exact ⟨offCriticalQuartic delta gamma, rfl, hEntire, hSymmetry, hZeros, hCard, hOff⟩
  · intro hImplication
    have hLocalized := hImplication (offCriticalQuartic delta gamma) hEntire hSymmetry
    have hRoot : offCriticalQuartic delta gamma (rootPP delta gamma) = 0 :=
      (hZeros (rootPP delta gamma)).2 (by simp [sourceZeros])
    exact hOff (rootPP delta gamma) hRoot
      (hLocalized (rootPP delta gamma) hRoot)

#print axioms full_symmetry_not_fixed_line_localization

-- Reverse probe for CAS-A1: every witness obligation is projected from the public theorem.
example (delta gamma : ℝ) (hdelta : delta ≠ 0) (hgamma : gamma ≠ 0) :
    ∃ F : ℂ → ℂ,
      F = offCriticalQuartic delta gamma ∧
      Differentiable ℂ F ∧
      HasFullZetaSymmetry F ∧
      (∀ s, F s = 0 ↔ s ∈ sourceZeros delta gamma) ∧
      (sourceZeros delta gamma).card = 4 ∧
      ∀ s, F s = 0 → s.re ≠ criticalAbscissa :=
  (full_symmetry_not_fixed_line_localization delta gamma hdelta hgamma).1

-- Reverse probe for CAS-A2: the public theorem exposes the boxed non-implication.
example (delta gamma : ℝ) (hdelta : delta ≠ 0) (hgamma : gamma ≠ 0) :
    ¬ (∀ F : ℂ → ℂ,
      Differentiable ℂ F → HasFullZetaSymmetry F → FixedLineLocalization F) :=
  (full_symmetry_not_fixed_line_localization delta gamma hdelta hgamma).2

-- Trivialization probe for CAS-A1: delta = 0 forces a displayed zero onto the fixed line.
example (gamma : ℝ) :
    ¬ ∃ F : ℂ → ℂ,
      F = offCriticalQuartic 0 gamma ∧
      (∀ s, F s = 0 ↔ s ∈ sourceZeros 0 gamma) ∧
      ∀ s, F s = 0 → s.re ≠ criticalAbscissa := by
  rintro ⟨F, rfl, hZeros, hOff⟩
  have hRoot : offCriticalQuartic 0 gamma (rootPP 0 gamma) = 0 :=
    (hZeros (rootPP 0 gamma)).2 (by simp [sourceZeros])
  exact hOff (rootPP 0 gamma) hRoot (by simp [rootPP, criticalAbscissa])

-- Trivialization probe for CAS-A1: gamma = 0 collapses the four-point source zero set.
example (delta : ℝ) : (sourceZeros delta 0).card ≠ 4 := by
  have hset : sourceZeros delta 0 = {rootPP delta 0, rootMP delta 0} := by
    ext s
    simp [sourceZeros, rootPP, rootPM, rootMP, rootMM]
  rw [hset]
  exact ne_of_lt (lt_of_le_of_lt Finset.card_le_two (by omega))

end

end D5.S3.Zeros.SymmetricPolynomial.FullSymmetryNonlocalization
