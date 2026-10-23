/- GID: D5/S3/Quantum/Entanglement/ElegantJointMeasurementInflation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ElegantJointMeasurementInflation
   mirror-E: none(waiver:exact-inflation-certificate-consumer)
   anchors: []
   utility: none
   digest: Exact upstream inflation marginal identities for actual continuous triangle responses. -/
import D5.S3.Quantum.Entanglement.TriangleInflationSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation
open D5.S3.Quantum.Entanglement.TriangleInflationSoundness
open D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation
open scoped BigOperators

abbrev Copy := Fin 4
abbrev Node := Fin 20

-- Exact upstream order, with sources alpha(BC), beta(CA), gamma(AB).
def spec : InflationSpec Copy Node where
  party := ![0,1,2,1,2,0,2,2,0,1,0,1,0,1,0,1,0,1,0,1]
  firstCopy := ![0,0,0,0,1,1,0,1,0,1,1,1,0,2,1,2,0,3,1,3]
  secondCopy := ![0,0,0,1,0,0,1,1,1,0,1,1,2,0,2,1,3,0,3,1]

def triangle : Finset Node := {0,1,2}
def triangleRemainder : Finset Node := {10,14,18,11,15,19,7}
def singleton : Finset Node := {0}
def singletonRemainder : Finset Node := {9,11,13,15,17,19,6,7}

private theorem triangle_nodes_disjoint : Disjoint triangle triangleRemainder := by decide
private theorem singleton_nodes_disjoint : Disjoint singleton singletonRemainder := by decide
private theorem triangle_sources_disjoint :
    Disjoint (sourceSupport spec triangle) (sourceSupport spec triangleRemainder) := by decide
private theorem singleton_sources_disjoint :
    Disjoint (sourceSupport spec singleton) (sourceSupport spec singletonRemainder) := by decide

-- A renaming may choose different injections separately for alpha, beta and gamma.
def renamed (ρ : Party → Copy → Copy) : InflationSpec Copy Node where
  party := spec.party
  firstCopy v := ρ (spec.party v + 1) (spec.firstCopy v)
  secondCopy v := ρ (spec.party v + 2) (spec.secondCopy v)

def sourceRename (ρ : Party → Copy → Copy) (i : Source Copy) : Source Copy := (i.1, ρ i.1 i.2)

private theorem sourceRename_injective (ρ : Party → Copy → Copy)
    (hρ : ∀ party, Function.Injective (ρ party)) : Function.Injective (sourceRename ρ) := by
  intro i j h
  have hp := congrArg Prod.fst h
  obtain ⟨i, x⟩ := i
  obtain ⟨j, y⟩ := j
  dsimp [sourceRename] at hp
  subst j
  have hx := hρ i (congrArg Prod.snd h)
  exact congrArg (fun z => (i,z)) hx

private theorem renamed_support (ρ : Party → Copy → Copy) (J : Finset Node) :
    sourceSupport (renamed ρ) J = (sourceSupport spec J).image (sourceRename ρ) := by
  unfold sourceSupport
  rw [Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro v _
  simp [renamed, InflationSpec.firstSource, InflationSpec.secondSource, sourceRename]

private theorem renamed_triangle_sources_disjoint (ρ : Party → Copy → Copy)
    (hρ : ∀ party, Function.Injective (ρ party)) :
    Disjoint (sourceSupport (renamed ρ) triangle)
      (sourceSupport (renamed ρ) triangleRemainder) := by
  rw [renamed_support, renamed_support, Finset.disjoint_image (sourceRename_injective ρ hρ)]
  exact triangle_sources_disjoint

private theorem renamed_singleton_sources_disjoint (ρ : Party → Copy → Copy)
    (hρ : ∀ party, Function.Injective (ρ party)) :
    Disjoint (sourceSupport (renamed ρ) singleton)
      (sourceSupport (renamed ρ) singletonRemainder) := by
  rw [renamed_support, renamed_support, Finset.disjoint_image (sourceRename_injective ρ hρ)]
  exact singleton_sources_disjoint

theorem triangle_identity_renamed (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (ρ : Party → Copy → Copy) (hρ : ∀ party, Function.Injective (ρ party))
    (o : Node → Outcome) :
    marginalMass (renamed ρ) R (triangle ∪ triangleRemainder) o =
      p (o 0) (o 1) (o 2) * marginalMass (renamed ρ) R triangleRemainder o := by
  rw [marginalMass_disjoint_source_factorization _ _ _ _ _ triangle_nodes_disjoint
    (renamed_triangle_sources_disjoint ρ hρ)]
  have htri := marginalMass_triangle (renamed ρ) R p hp (0 : Node) 1 2
    (ρ 0 0) (ρ 1 0) (ρ 2 0) o
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  rw [show triangle = ({0,1,2} : Finset Node) from rfl, htri]

theorem singleton_identity_renamed (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (ρ : Party → Copy → Copy) (hρ : ∀ party, Function.Injective (ρ party))
    (o : Node → Outcome) :
    marginalMass (renamed ρ) R (singleton ∪ singletonRemainder) o =
      (∑ b : Outcome, ∑ c : Outcome, p (o 0) b c) *
        marginalMass (renamed ρ) R singletonRemainder o := by
  rw [marginalMass_disjoint_source_factorization _ _ _ _ _ singleton_nodes_disjoint
    (renamed_singleton_sources_disjoint ρ hρ)]
  have hsingle := marginalMass_singleton_A (renamed ρ) R p hp (0 : Node) 1 2
    (ρ 0 0) (ρ 1 0) (ρ 2 0) o
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  rw [show singleton = ({0} : Finset Node) from rfl, hsingle]

example (R : ResponseModel) (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (o : Node → Outcome) :
    marginalMass spec R (triangle ∪ triangleRemainder) o =
      p (o 0) (o 1) (o 2) * marginalMass spec R triangleRemainder o := by
  simpa [renamed] using triangle_identity_renamed R p hp (fun _ => id) (fun _ => fun _ _ h => h) o

example (R : ResponseModel) (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (o : Node → Outcome) :
    marginalMass spec R (singleton ∪ singletonRemainder) o =
      (∑ b : Outcome, ∑ c : Outcome, p (o 0) b c) *
        marginalMass spec R singletonRemainder o := by
  simpa [renamed] using singleton_identity_renamed R p hp (fun _ => id) (fun _ => fun _ _ h => h) o

#print axioms triangle_identity_renamed
#print axioms singleton_identity_renamed
end D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation
