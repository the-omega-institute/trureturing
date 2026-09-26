/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalRealReadoutRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalRealReadoutRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Function-valued CUT readouts retain the real mechanical prefix and completion laws. -/

import D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
import D5.S1.Words.Mechanical.MechanicalReadoutRegularity
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
import D5.S3.ConceptDynamics.InformationEscape.MechanicalReadoutSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

open Set Filter MeasureTheory
open scoped Topology
open D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

abbrev PrefixOutput := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ
abbrev CompletionOutput := (ℝ → ℝ → ℝ → ℝ) × (ℝ → ℝ → ℝ → ℕ → ℝ)

/-- The complete weighted finite readout, with weights, slope, phase, and horizon retained. -/
def actualPrefix (weights : ℕ → ℝ) (alpha x : ℝ) (n : ℕ) : ℝ :=
  MechanicalReadoutSources.actualPrefix weights alpha x n

/-- The completed readout and every geometric finite prefix share one observation. -/
def completedReadout (r alpha x : ℝ) : ℝ :=
  MechanicalReadoutSources.completedReadout r alpha x

def finitePrefixReadout (r alpha x : ℝ) (n : ℕ) : ℝ :=
  MechanicalReadoutSources.finitePrefixReadout r alpha x n

def actualCompletion : CompletionOutput :=
  MechanicalReadoutSources.actualCompletion

def localOrderClaim (P : PrefixOutput) : Prop :=
  ∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 →
    ∀ (weights : ℕ → ℝ) (m : ℕ),
      (∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
        ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius → ∀ x ∈ Ico (0 : ℝ) 1,
          P weights alpha x (m + 1) ≤ P weights (alpha + delta) x (m + 1)) ↔
        0 ≤ weights m ∧ ∀ k < m, weights (k + 1) ≤ weights k

def isometricClaim (o : CompletionOutput) : Prop :=
  ∀ (r alpha beta : ℝ), 0 ≤ r → r < 1 →
    alpha ∈ Ico (0 : ℝ) 1 → beta ∈ Ico (0 : ℝ) 1 →
    IntegrableOn (o.1 r alpha) (Ico (0 : ℝ) 1) ∧
    IntegrableOn (o.1 r beta) (Ico (0 : ℝ) 1) ∧
    (∀ x : ℝ, ∀ n : ℕ,
      0 ≤ o.1 r alpha x - o.2 r alpha x n ∧
      o.1 r alpha x - o.2 r alpha x n ≤ r ^ n) ∧
    (∀ n : ℕ, (∫ x : ℝ in Ico (0 : ℝ) 1,
      |o.2 r beta x n - o.2 r alpha x n|) =
        (1 - r ^ n) * |beta - alpha|) ∧
    ((∫ x : ℝ in Ico (0 : ℝ) 1,
      |o.1 r beta x - o.1 r alpha x|) = |beta - alpha|) ∧
    (beta ≤ alpha → ∀ n : ℕ, (∫ x : ℝ in Ico (0 : ℝ) 1,
      |o.1 r alpha x - o.2 r beta x n|) =
        alpha - beta * (1 - r ^ n))

def uniformBoundClaim (o : CompletionOutput) : Prop :=
  ∀ (r alpha x : ℝ), 0 ≤ r → r < 1 → alpha ∈ Ico (0 : ℝ) 1 →
    |o.1 r alpha x - alpha| ≤ 1 - r ∧
    (∀ (target : ℝ) (n : ℕ),
      |o.2 r alpha x n - target| ≤ r ^ n + (1 - r) + |alpha - target|) ∧
    (1 - r) * (Int.fract x - 1) ≤ o.1 r alpha x - alpha ∧
      o.1 r alpha x - alpha ≤ (1 - r) * Int.fract x

def regularityClaim (o : CompletionOutput) : Prop :=
  ∀ (r alpha x : ℝ), 0 < r → r < 1 → alpha ∈ Ioo (0 : ℝ) 1 →
    ((∀ eps : ℝ, 0 < eps → ∃ radius : ℝ, 0 < radius ∧
      ∀ beta : ℝ, |beta - alpha| < radius →
        |o.1 r beta x - o.1 r alpha x| < eps) ↔
      ∀ k : ℕ, 0 < k → ∀ z : ℤ, x + (k : ℝ) * alpha ≠ (z : ℝ)) ∧
    (∀ k : ℕ, 0 < k → ∀ z : ℤ, x + (k : ℝ) * alpha = (z : ℝ) →
      ∀ beta : ℝ, beta ∈ Ico (0 : ℝ) alpha →
        (1 - r) ^ 2 * r ^ (k - 1) ≤
          o.1 r alpha x - o.1 r beta x)

private def unitArena := Arena.ofFintype Unit

def localOrderArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq PrefixOutput := Classical.decEq _
    exact { toArena := unitArena
            signature := mechanicalReadoutSignature PrefixOutput
            Law := fun realization => localOrderClaim (realization.readout () ()) }
  Domain := ℝ

def isometricArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq CompletionOutput := Classical.decEq _
    exact { toArena := unitArena
            signature := mechanicalReadoutSignature CompletionOutput
            Law := fun realization => isometricClaim (realization.readout () ()) }
  Domain := ℝ

def uniformBoundArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq CompletionOutput := Classical.decEq _
    exact { toArena := unitArena
            signature := mechanicalReadoutSignature CompletionOutput
            Law := fun realization => uniformBoundClaim (realization.readout () ()) }
  Domain := ℝ

def regularityArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq CompletionOutput := Classical.decEq _
    exact { toArena := unitArena
            signature := mechanicalReadoutSignature CompletionOutput
            Law := fun realization => regularityClaim (realization.readout () ()) }
  Domain := ℝ

def localOrderRealization :=
  @mechanicalReadoutRealization PrefixOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.actualPrefix)

def completionRealization :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.actualCompletion)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
