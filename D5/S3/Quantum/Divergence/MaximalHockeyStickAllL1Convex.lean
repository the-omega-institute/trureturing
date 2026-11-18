/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual all-L1 maximal convex equality on the common interior. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
import D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder ENNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

variable {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}

/-- The actual infimum over every s-finite source in the arbitrary universe u,
with positive complex-linear trace-preserving preparation on its entire L1 space. -/
def allL1Value (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  sInf (allL1Costs.{u} hf A B)

/-- Exact source atomization identifies the actual all-L1 infimum with the
finite maximal value for the same generator and closed-perspective convention. -/
theorem allL1Value_eq_maximalValue (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : allL1Value.{u} hf A B = maximalValue hf A B := by
  exact source_class_infimum_eq hf A B

/-- Common-interior commutation suffices for every real convex generator as an
equality of extended actual all-L1 and PSD-overlap hockey values. -/
theorem commute_implies_integrated_eq (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : let S := A + B
      let C := MaximalHockeyStickSupport.normalize S A
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) :
    allL1Value.{u} hf A B = hockeyValue hf A B := by
  rw [allL1Value_eq_maximalValue]
  exact MaximalHockeyStickConvex.commute_implies_integrated_eq hf A B hA hB hc

/-- For actual full-support curvature and a real finite actual all-L1 infimum,
equality holds exactly when the original common-interior compressions commute.
No optimizer, trace normalization or nonsingularity is assumed. -/
theorem integrated_eq_iff_commute (hf : ConvexOn ℝ (Ioi 0) f)
    [(curvature hf).IsOpenPosMeasure]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : allL1Value.{u} hf A B = (c : EReal)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (allL1Value.{u} hf A B = hockeyValue hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  dsimp only
  constructor
  · intro he
    rw [allL1Value_eq_maximalValue] at hc he
    exact (MaximalHockeyStickConvex.integrated_eq_iff_commute hf A B hA hB c hc).1 he
  · exact commute_implies_integrated_eq hf A B hA hB

/-- The original sigma-finite maximal f-value, with the actual closed-perspective
cost and arbitrary independent source universe. -/
def originalL1Value (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  sInf (sigmaFiniteL1Costs.{u} hf A B)

/-- Original maximal hockey-stick f-value: the actual sigma-finite operational
negative infimum on (0,1] and positive infimum on (1,infinity), integrated against
the actual curvature. The full atom at one is in the negative branch. -/
def originalHockeyValue (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  (affineMass f A B : EReal) +
    (∫⁻ (t : Positive), ENNReal.ofReal
      (if (t : ℝ) ≤ 1 then operationalL1NegativeHockey.{u} A B t
        else operationalL1Hockey.{u} A B t) ∂curvature hf : ℝ≥0∞)

/-- The same actual operational curvature value over all s-finite L1 sources. -/
def sFiniteHockeyValue (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  (affineMass f A B : EReal) +
    (∫⁻ (t : Positive), ENNReal.ofReal
      (if (t : ℝ) ≤ 1 then sFiniteOperationalNegativeHockey.{u} A B t
        else sFiniteOperationalHockey.{u} A B t) ∂curvature hf : ℝ≥0∞)

/-- Finite counting sources sandwich the original sigma-finite class inside the
s-finite class, identifying the original maximal value without changing its cost. -/
theorem originalL1Value_eq_allL1Value (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : originalL1Value.{u} hf A B = allL1Value.{u} hf A B := by
  rw [originalL1Value, sigma_finite_source_infimum_eq,
    allL1Value_eq_maximalValue]
  rfl

/-- The actual original and s-finite L1 hockey infima, rather than an assumed
hinge perspective identity, identify the exact integrated PSD hockey value. -/
theorem hockeyValue_eq_original_operational (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B = originalHockeyValue.{u} hf A B ∧
      hockeyValue hf A B = sFiniteHockeyValue.{u} hf A B := by
  have hp (t : Positive) := operationalL1_hockey_eq.{u} A B hA hB t t.2
  have hσ (t : Positive) : maximalKernel A B t =
      (if (t : ℝ) ≤ 1 then operationalL1NegativeHockey.{u} A B t
        else operationalL1Hockey.{u} A B t) := by
    rw [(hp t).1, (hp t).2.1]
    rfl
  have hs (t : Positive) : maximalKernel A B t =
      (if (t : ℝ) ≤ 1 then sFiniteOperationalNegativeHockey.{u} A B t
        else sFiniteOperationalHockey.{u} A B t) := by
    rw [(hp t).2.2.1, (hp t).2.2.2]
    rfl
  constructor
  · unfold hockeyValue originalHockeyValue
    simp_rw [hσ]
  · unfold hockeyValue sFiniteHockeyValue
    simp_rw [hs]

/-- Common-interior commutation gives the actual all-L1 operational equality
for every convex generator, retaining infinite endpoints and extended values. -/
theorem commute_implies_allL1_operational_eq (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : let S := A + B
      let C := MaximalHockeyStickSupport.normalize S A
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) :
    allL1Value.{u} hf A B = originalHockeyValue.{u} hf A B ∧
      allL1Value.{u} hf A B = sFiniteHockeyValue.{u} hf A B := by
  have he := commute_implies_integrated_eq.{u} hf A B hA hB hc
  exact ⟨he.trans (hockeyValue_eq_original_operational hf A B hA hB).1,
    he.trans (hockeyValue_eq_original_operational hf A B hA hB).2⟩

/-- The all-L1 classifier now consumes the original operational infima. Necessity
requires actual full-support curvature and a real finite maximal value. -/
theorem allL1_operational_eq_iff_commute (hf : ConvexOn ℝ (Ioi 0) f)
    [(curvature hf).IsOpenPosMeasure]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : allL1Value.{u} hf A B = (c : EReal)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    ((allL1Value.{u} hf A B = originalHockeyValue.{u} hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) ∧
    ((allL1Value.{u} hf A B = sFiniteHockeyValue.{u} hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) := by
  rw [← (hockeyValue_eq_original_operational hf A B hA hB).1,
    ← (hockeyValue_eq_original_operational hf A B hA hB).2]
  exact ⟨integrated_eq_iff_commute hf A B hA hB c hc,
    integrated_eq_iff_commute hf A B hA hB c hc⟩

/-- The original HMT sigma-finite formulation, with both sides referring to
its actual original source class. Sufficiency has no finiteness assumption. -/
theorem commute_implies_original_eq (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : let S := A + B
      let C := MaximalHockeyStickSupport.normalize S A
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) :
    originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B := by
  rw [originalL1Value_eq_allL1Value]
  exact (commute_implies_allL1_operational_eq hf A B hA hB hc).1

/-- Exact original-source equality classification for arbitrary finite PSD
outputs, including empty, singular and zero pairs and arbitrary trace masses. -/
theorem original_eq_iff_commute (hf : ConvexOn ℝ (Ioi 0) f)
    [(curvature hf).IsOpenPosMeasure]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  rw [originalL1Value_eq_allL1Value] at hc ⊢
  exact (allL1_operational_eq_iff_commute hf A B hA hB c hc).1

#print axioms hockeyValue_eq_original_operational
#print axioms original_eq_iff_commute
#print axioms commute_implies_original_eq
#print axioms allL1Value_eq_maximalValue
#print axioms commute_implies_integrated_eq
#print axioms integrated_eq_iff_commute

end D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
