/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite joint operations admit common fresh tables on the actual source product. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalObserverNormalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalHistoryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization
open OriginalObserverNormalization ActualRenewalPrefixLaw

variable {C : Type*}

instance actionFinite [Finite C] (e : C → Option Bool) : Finite (Action e) := by
  let encode : Action e → C × Option Bool := fun a => match a with
    | .read c => (c.val, none)
    | .emit c d _ => (c, some d)
  apply Finite.of_injective encode
  intro a b h
  cases a <;> cases b <;> simp_all [encode]

instance actionMeasurableSpace (e : C → Option Bool) : MeasurableSpace (Action e) := ⊤
instance actionMeasurableSingletonClass (e : C → Option Bool) :
    MeasurableSingletonClass (Action e) := ⟨fun _ => trivial⟩

/-- Original stochastic primitives are specified before any innovation tape.
    The pair retains the correlation of the update and ensuing action choice.
    Both configuration values belong to the complete original carrier. -/
structure Observer (C : Type*) where
  emission : C → Option Bool
  label : Bool → C
  label_emission : ∀ d, emission (label d) = some d
  initialize : PMF (C × Action emission)
  operation : C → Bool → PMF (C × Action emission)

namespace Observer
variable (O : Observer C)

abbrev Outcome := C × Action O.emission
abbrev Innovation := C × Bool → O.Outcome

/-- This random table is fresh at each paid read. Only its selected entry is
    evaluated; it is not part of the retained configuration. -/
def machine : Machine C O.Outcome O.Innovation where
  emission := O.emission
  label := O.label
  label_emission := O.label_emission
  prepare := Prod.fst
  initialAction := fun _ seed => seed.2
  update := fun c b r => (r (c,b)).1
  afterRead := fun c b r _ => (r (c,b)).2

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

def seedLaw : Measure O.Outcome := O.initialize.toMeasure
def innovationLaw : Measure O.Innovation :=
  Measure.pi fun p : C × Bool => (O.operation p.1 p.2).toMeasure

instance : IsProbabilityMeasure O.seedLaw := by unfold seedLaw; infer_instance
instance : IsProbabilityMeasure O.innovationLaw := by unfold innovationLaw; infer_instance

private theorem table_entry (c : C) (b : Bool) :
    O.innovationLaw.map (fun r => r (c,b)) = (O.operation c b).toMeasure :=
  (measurePreserving_eval (fun p : C × Bool => (O.operation p.1 p.2).toMeasure) (c,b)).map_eq

end Observer

section Product
variable {I S R : Type*} [MeasurableSpace I] [MeasurableSpace S] [MeasurableSpace R]
    (κ : Measure I) (ρ : Measure R) [IsProbabilityMeasure κ] [IsProbabilityMeasure ρ]

private theorem finite_coordinates (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => fun j : Fin n => z j.val) = Measure.pi (fun _ : Fin n => ρ) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

private theorem separated_blocks (l r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map
      (fun z => (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) =
      (Measure.pi fun _ : Fin l => ρ).prod (Measure.pi fun _ : Fin r => ρ) := by
  apply (Measure.prod_eq fun D B hD hB => ?_).symm
  rw [Measure.map_apply (by fun_prop) (hD.prod hB)]
  have he : (fun z : ℕ → R =>
      (fun j : Fin l => z j.val, fun j : Fin r => z (l + j.val))) ⁻¹' (D ×ˢ B) =
      (fun z => fun j : Fin l => z j.val) ⁻¹' D ∩
        FreshServiceRestart.shift l ⁻¹'
          ((fun z : ℕ → R => fun j : Fin r => z j.val) ⁻¹' B) := by
    ext z
    simp [FreshServiceRestart.shift, Nat.add_comm]
  rw [he, FreshServiceRestart.prefix_suffix_independent ρ l D hD _
    (hB.preimage (by fun_prop)),
    ← Measure.map_apply (by fun_prop) hD, finite_coordinates,
    ← Measure.map_apply (by fun_prop) hB, finite_coordinates]

end Product
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalJointRealization
