/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single CUT slot retains complete mechanical readout functions for dyadic boundary laws. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

open D5.S1.Words.Mechanical
open LeanInformationAudit

/-- One CUT slot carries an entire parameterized observation function. -/
def mechanicalReadoutSignature (Y : Type) [dY : DecidableEq Y] :
    PrimitiveSignature Unit where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => dY
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def mechanicalReadoutRealization {Y : Type} [dY : DecidableEq Y]
    (f : Unit → Y) : PrimitiveRealization (mechanicalReadoutSignature Y) where
  readout := fun _ state => f state
  anchor := Fin.elim0

abbrev LowerOutput := ℝ → ℕ → ℝ × Bool
abbrev UpperOutput := ℝ → ℝ → ℕ → ℕ → Bool
abbrev StableOutput := ℝ → ℝ → ℕ → ℤ × Bool

/-- The lower slope and its actual boundary bit, independent of the target theorem. -/
def lowerReadout (alpha : ℝ) (p : ℕ) : ℝ × Bool :=
  let beta := (⌊((2 ^ p : ℕ) : ℝ) * alpha⌋ : ℝ) / ((2 ^ p : ℕ) : ℝ)
  (beta, lowerMechanicalWord beta (1 - alpha) 0)

/-- The actual bit at an upper dyadic slope. -/
def upperReadout (alpha x : ℝ) (p j : ℕ) : Bool :=
  lowerMechanicalWord
    ((⌈((2 ^ p : ℕ) : ℝ) * alpha⌉ : ℝ) / ((2 ^ p : ℕ) : ℝ)) x j

/-- Both observations governed by a local slope radius. -/
def stableReadout (beta x : ℝ) (k : ℕ) : ℤ × Bool :=
  (⌊x + (k : ℝ) * beta⌋, lowerMechanicalWord beta x k)

private def unitArena := Arena.ofFintype Unit

def lowerArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq LowerOutput := Classical.decEq _
    exact {
      toArena := unitArena
      signature := mechanicalReadoutSignature LowerOutput
      Law := fun r => ∀ (alpha : ℝ), Irrational alpha → 0 < alpha → alpha < 1 →
        ∀ p : ℕ,
          0 ≤ (r.readout () () alpha p).1 ∧
          0 < alpha - (r.readout () () alpha p).1 ∧
          alpha - (r.readout () () alpha p).1 <
            (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
          lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
          (r.readout () () alpha p).2 = false }
  Domain := ℝ

def upperArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq UpperOutput := Classical.decEq _
    exact {
      toArena := unitArena
      signature := mechanicalReadoutSignature UpperOutput
      Law := fun r => ∀ (alpha x : ℝ) (n : ℕ),
        ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ j < n,
          r.readout () () alpha x p j = lowerMechanicalWord alpha x j }
  Domain := ℝ

def stableArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq StableOutput := Classical.decEq _
    exact {
      toArena := unitArena
      signature := mechanicalReadoutSignature StableOutput
      Law := fun r => ∀ (alpha x : ℝ) (n : ℕ),
        (∀ k : ℕ, 0 < k → k ≤ n → ∀ z : ℤ,
          x + (k : ℝ) * alpha ≠ (z : ℝ)) →
        ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
          (∀ k ≤ n,
            (r.readout () () beta x k).1 = (r.readout () () alpha x k).1) ∧
          (∀ j < n,
            (r.readout () () beta x j).2 = (r.readout () () alpha x j).2) }
  Domain := ℝ

def lowerRealization :=
  @mechanicalReadoutRealization LowerOutput (Classical.decEq _)
    (fun _ : Unit => lowerReadout)

def upperRealization :=
  @mechanicalReadoutRealization UpperOutput (Classical.decEq _)
    (fun _ : Unit => upperReadout)

def stableRealization :=
  @mechanicalReadoutRealization StableOutput (Classical.decEq _)
    (fun _ : Unit => stableReadout)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
