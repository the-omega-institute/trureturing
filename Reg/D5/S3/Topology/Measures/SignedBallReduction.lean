import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.SignedBallReduction

/-! # Exact source laws for the signed-ball reduction

These source bridges retain the original universes and every hypothesis.
The variation, sensitivity and compiler source-selection obligations for
four-slot registrations are unfinished; these laws are not registrations.
-/

noncomputable section

namespace Reg.D5.S3.Topology.Measures.SignedBallReduction

open Set Filter Function MeasureTheory
open scoped _root_.Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.Measures.NormPreservingLifts
open _root_.D5.S3.Topology.Measures.SignedBallReduction

universe u

structure Space where
  K : Type u
  top : TopologicalSpace K
  compact : @CompactSpace K top
  hausdorff : @T2Space K top
  measurable : MeasurableSpace K
  borel : @BorelSpace K top measurable

attribute [instance] Space.top Space.compact Space.hausdorff Space.measurable Space.borel

@[reducible] def massSignature : DependentFamily.Signature where
  Params := Space.{u}
  State := fun P => SignedMeasure P.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def massActual : DependentFamily.Realization massSignature.{u} :=
  DependentFamily.realize massSignature
    (fun _ _ s => s.totalVariation.real univ) (fun a => nomatch a)

@[reducible] def normalizationArena : DependentFamily.Arena where
  signature := massSignature.{u}
  Law R := ∀ (P : Space.{u})
    (h : StoneCech ℕ → WeakDual ℝ C(P.K, ℝ)),
    Continuous h → Function.Injective h →
    (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) →
    ∃ (b : ℕ → SignedMeasure P.K) (E : ℕ → Set P.K)
      (f : Ultrafilter ℕ → WeakDual ℝ C(P.K, ℝ)),
      (∀ n, (b n).totalVariation.Regular) ∧
      (∀ n, R.readout () P (b n) = 1) ∧
      (∀ n, MeasurableSet (E n)) ∧ Pairwise (Disjoint on E) ∧
      (∀ n, (b n).totalVariation (E n)ᶜ = 0) ∧
      Continuous f ∧ Function.Injective f ∧
      (∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (b n))) ∧
      ∀ p, ‖WeakDual.toStrongDual (f p)‖ ≤ 1

abbrev normalizationScope := type_of% (@exists_normalized_disjoint_embedding.{u})

theorem normalizationBridge :
    normalizationScope.{u} ↔ normalizationArena.{u}.Law massActual.{u} := by
  constructor
  · intro h P
    exact h
  · intro h K top compact hausdorff measurable borel
    exact h ⟨K, top, compact, hausdorff, measurable, borel⟩

theorem normalizationPositive : normalizationArena.{u}.Law massActual.{u} :=
  normalizationBridge.mp (@exists_normalized_disjoint_embedding.{u})

@[reducible] def injectionSignature : DependentFamily.Signature where
  Params := Space.{u}
  State := fun P => StoneCech ℕ → WeakDual ℝ C(P.K, ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def injectionActual : DependentFamily.Realization injectionSignature.{u} :=
  DependentFamily.realize injectionSignature
    (fun _ _ h => Function.Injective h) (fun a => nomatch a)

@[reducible] def collisionArena : DependentFamily.Arena where
  signature := injectionSignature.{u}
  Law R := ∀ (P : Space.{u}) [ZeroDimensionalSpace P.K],
    SignedClopenCollision (K := P.K) →
    ∀ h : StoneCech ℕ → WeakDual ℝ C(P.K, ℝ), Continuous h →
      (∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) → ¬ R.readout () P h

abbrev collisionScope := type_of% (@not_injective_signed_ball_of_collision.{u})

theorem collisionBridge : collisionScope.{u} ↔ collisionArena.{u}.Law injectionActual.{u} := by
  constructor
  · intro h P hd
    exact h
  · intro h K top compact hausdorff measurable borel hd
    exact h ⟨K, top, compact, hausdorff, measurable, borel⟩

theorem collisionPositive : collisionArena.{u}.Law injectionActual.{u} :=
  collisionBridge.mp (@not_injective_signed_ball_of_collision.{u})

end Reg.D5.S3.Topology.Measures.SignedBallReduction
