/- GID: D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete finite-history source law and its family interventions. -/

import D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open MeasureTheory Finset
open scoped BigOperators ENNReal
noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open DependentFamily
universe u v

abbrev Readout {J : Type*} {Z : ℕ → Type*} (N : ℕ) :=
  (J × History Z N) → History Z N

def readoutSigma {J : Type*} {Z : ℕ → Type*} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    {N t : ℕ} (ρ : Readout (J := J) (Z := Z) N) (ht : t ≤ N) :
    MeasurableSpace (J × History Z N) :=
  MeasurableSpace.comap (fun ω => readPrefix ht (ρ ω)) inferInstance

def Law {J : Type*} {Z : ℕ → Type*} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    (N : ℕ)
    (ρ : Readout (J := J) (Z := Z) N)
    (ν : J → ℝ) (hν : (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1)
    (K : (n : ℕ) → J → History Z n → Z n → ℝ)
    (hK : ∀ n < N, (∀ j h z, 0 ≤ K n j h z) ∧ ∀ j h, ∑ z, K n j h z = 1) : Prop :=
  IsProbabilityMeasure (historyLaw ν K N) ∧
    (∀ t (ht : t ≤ N) (f : J → History Z t → ℝ),
      (∫ ω, f ω.1 (readPrefix ht (ρ ω)) ∂historyLaw ν K N) =
        ∑ j, ∑ h, ν j * likelihood K t j h * f j h) ∧
    (∀ t (ht : t < N) (f : History Z (t+1) → ℝ),
      (historyLaw ν K N)[(fun ω => f (readPrefix (Nat.succ_le_of_lt ht) (ρ ω))) |
          readoutSigma ρ (Nat.le_of_lt ht)] =ᵐ[historyLaw ν K N]
      fun ω => ∑ z, historyMass ν K (t+1)
          (Fin.snoc (readPrefix (Nat.le_of_lt ht) (ρ ω)) z) /
          historyMass ν K t (readPrefix (Nat.le_of_lt ht) (ρ ω)) *
          f (Fin.snoc (readPrefix (Nat.le_of_lt ht) (ρ ω)) z))

def identityReadout {J : Type*} {Z : ℕ → Type*} {N : ℕ} : Readout (J := J) (Z := Z) N :=
  fun ω => ω.2

abbrev Family := ∀ (J : Type u) (Z : ℕ → Type v) (N : ℕ), Readout (J := J) (Z := Z) N

def identityFamily : Family.{u,v} := fun _ _ _ ω => ω.2

def FullLaw (ρ : Family.{u,v}) : Prop :=
  ∀ {J : Type u} {Z : ℕ → Type v} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    (ν : J → ℝ) (hν : (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1)
    (K : (n : ℕ) → J → History Z n → Z n → ℝ) (N : ℕ)
    (hK : ∀ n < N, (∀ j h z, 0 ≤ K n j h z) ∧ ∀ j h, ∑ z, K n j h z = 1),
    Law N (ρ J Z N) ν hν K hK

abbrev Fiber := (J : Type u) × (Z : (ℕ → Type v)) × ℕ
abbrev FiberReadout (x : Fiber.{u,v}) := Readout (J := x.1) (Z := x.2.1) x.2.2
abbrev TargetJ := ULift.{u} Unit
abbrev TargetZ (_ : ℕ) := ULift.{v} Bool

def targetFiber : Fiber.{u,v} := ⟨TargetJ, TargetZ, 1⟩
def trueTargetReadout : FiberReadout targetFiber.{u,v} := fun _ _ => ⟨true⟩

def badFiber : (x : Fiber.{u,v}) → FiberReadout x := by
  classical
  exact Function.update (fun x ω => ω.2) targetFiber trueTargetReadout

def badFamily : Family.{u,v} := fun J Z N => badFiber ⟨J, Z, N⟩

def targetNu : TargetJ.{u} → ℝ := fun _ => 1

def targetK : (n : ℕ) → TargetJ.{u} → History TargetZ.{v} n → TargetZ.{v} n → ℝ :=
  fun _ _ _ z => if z.down = false then 1 else 0

def targetF : TargetJ.{u} → History TargetZ.{v} 1 → ℝ :=
  fun _ h => if (h 0).down = true then 1 else 0


def signature : Signature where
  Params := Fiber.{u,v}
  State := fun x => x.1 × History x.2.1 x.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ x => History x.2.1 x.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : DependentFamily.Arena where
  signature := signature.{u,v}
  Law r := FullLaw (fun J Z N => r.readout () ⟨J, Z, N⟩)

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ w => w.2) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ x => badFiber x) (fun e => nomatch e)

end D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
