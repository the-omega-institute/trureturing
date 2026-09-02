/- GID: D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance
   generality: G
   mirror-B: D5/B/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero constant rescaling preserves a projective toroidal jet fingerprint. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-09-02):
   * Exact searches for `ProjectiveJetFingerprint`,
     `projectiveToroidalJet`, and
     `projective_toroidal_jet_scale_invariance` missed in both D5 and pinned
     Mathlib.
   * Shape searches for lower derivative vanishing plus a nonzero anchor and
     equality of normalized derivative ratios found no covering D5 or Mathlib
     declaration. Mathlib's
     `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` instead characterizes
     an analytic vanishing order; it does not state rescaling invariance.
   * `ToroidalJetDepth` concerns a future producer of the anchor order and is
     deliberately not imported: this module receives that order through its
     lower-vanishing and anchor-nonzero hypotheses.
   * Pinned Mathlib supplies the exact constituents
     `iteratedDeriv_const_mul_field` and `mul_ne_zero`, both used directly in
     the named hypothesis-transfer lemma. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Analytic.Toroidal.ProjectiveJetScaleInvariance

/-- The anchor order and the normalized derivative tail of a jet. -/
structure ProjectiveJetFingerprint (K : Type u) (r : Nat) where
  order : Nat
  tail : Fin r → K

/-- The order-`m` projective jet at `s`, normalized by its nonzero anchor. -/
def projectiveToroidalJet
    (period : ℂ → ℂ) (s : ℂ) (m r : Nat)
    (_earlierVanish : ∀ j < m, iteratedDeriv j period s = 0)
    (_anchorNonzero : iteratedDeriv m period s ≠ 0) :
    ProjectiveJetFingerprint ℂ r where
  order := m
  tail := fun k ↦
    iteratedDeriv (m + k.1 + 1) period s / iteratedDeriv m period s

/-- Nonzero constant rescaling preserves the supplied anchor-order
hypotheses. -/
lemma projective_toroidal_jet_const_mul_hypotheses
    (period : ℂ → ℂ) (s c : ℂ) (m : Nat)
    (hc : c ≠ 0)
    (earlierVanish : ∀ j < m, iteratedDeriv j period s = 0)
    (anchorNonzero : iteratedDeriv m period s ≠ 0) :
    (∀ j < m,
        iteratedDeriv j (fun z ↦ c * period z) s = 0) ∧
      iteratedDeriv m (fun z ↦ c * period z) s ≠ 0 := by
  constructor
  · intro j hj
    rw [iteratedDeriv_const_mul_field, earlierVanish j hj, mul_zero]
  · rw [iteratedDeriv_const_mul_field]
    exact mul_ne_zero hc anchorNonzero

/-- A nonzero constant rescaling leaves the projective toroidal jet
fingerprint unchanged at the same supplied anchor order. -/
theorem projective_toroidal_jet_scale_invariance
    (period : ℂ → ℂ) (s c : ℂ) (m r : Nat)
    (hc : c ≠ 0)
    (earlierVanish : ∀ j < m, iteratedDeriv j period s = 0)
    (anchorNonzero : iteratedDeriv m period s ≠ 0) :
    projectiveToroidalJet period s m r earlierVanish anchorNonzero =
      projectiveToroidalJet (fun z ↦ c * period z) s m r
        (projective_toroidal_jet_const_mul_hypotheses
          period s c m hc earlierVanish anchorNonzero).1
        (projective_toroidal_jet_const_mul_hypotheses
          period s c m hc earlierVanish anchorNonzero).2 := by
  change ProjectiveJetFingerprint.mk m _ = ProjectiveJetFingerprint.mk m _
  apply congrArg (ProjectiveJetFingerprint.mk m)
  funext k
  simp only [iteratedDeriv_const_mul_field]
  field_simp

-- The fingerprint carrier is inhabited for every finite tail length.
example (r : Nat) : Nonempty (ProjectiveJetFingerprint ℂ r) :=
  ⟨⟨0, fun _ ↦ 0⟩⟩

-- Constant one at order zero witnesses simultaneous satisfiability.
example :
    ∃ (period : ℂ → ℂ) (s c : ℂ) (m : Nat),
      c ≠ 0 ∧
        (∀ j < m, iteratedDeriv j period s = 0) ∧
        iteratedDeriv m period s ≠ 0 := by
  refine ⟨fun _ ↦ 1, 0, 1, 0, one_ne_zero, ?_, ?_⟩
  · intro j hj
    exact (Nat.not_lt_zero j hj).elim
  · simp

#print axioms projective_toroidal_jet_const_mul_hypotheses
#print axioms projective_toroidal_jet_scale_invariance

end D5.S3.Analytic.Toroidal.ProjectiveJetScaleInvariance
