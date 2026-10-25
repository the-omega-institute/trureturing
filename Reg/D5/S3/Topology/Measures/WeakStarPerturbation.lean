import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.WeakStarPerturbation

/-! # Exact source laws for full-domain perturbation

The norm and neighborhood readouts keep arbitrary normed spaces and all
original domain universes. Four-slot variation, sensitivity and compiler
source selection remain unfinished; source laws are not registrations.
-/

noncomputable section

namespace Reg.D5.S3.Topology.Measures.WeakStarPerturbation

open Set Filter Function
open scoped _root_.Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.Measures.WeakStarPerturbation

universe u v w

structure Space where
  X : Type u
  normed : NormedAddCommGroup X
  scalar : letI := normed; NormedSpace ℝ X

attribute [instance] Space.normed Space.scalar

@[reducible] def normSignature : DependentFamily.Signature where
  Params := Space.{u}
  State := fun P => StrongDual ℝ P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def normActual : DependentFamily.Realization normSignature.{u} :=
  DependentFamily.realize normSignature (fun _ _ F => ‖F‖) (fun a => nomatch a)

@[reducible] def denseArena : DependentFamily.Arena where
  signature := normSignature.{u}
  Law R := ∀ (P : Space.{u}) {A : Type v} {T : Type w} [TopologicalSpace T]
    (i : A → T), DenseRange i →
    ∀ f g : T → WeakDual ℝ P.X, Continuous f → Continuous g →
    ∀ ε : ℝ, (∀ a, ‖WeakDual.toStrongDual (f (i a) - g (i a))‖ ≤ ε) →
    ∀ p, R.readout () P (WeakDual.toStrongDual (f p - g p)) ≤ ε

abbrev denseScope := type_of% (@norm_sub_le_of_denseRange.{u, v, w})

theorem denseBridge : denseScope.{u, v, w} ↔ denseArena.{u, v, w}.Law normActual.{u} := by
  constructor
  · intro h P
    exact h
  · intro h X normed scalar
    exact h ⟨X, normed, scalar⟩

@[reducible] def injectionArena : DependentFamily.Arena where
  signature := normSignature.{u}
  Law R := ∀ (P : Space.{u}) {A : Type v} {T : Type w} [TopologicalSpace T]
    (i : A → T), DenseRange i →
    ∀ f g : T → WeakDual ℝ P.X, Continuous f → Continuous g →
    ∀ c ε : ℝ,
      (∀ p q, p ≠ q → c ≤ R.readout () P (WeakDual.toStrongDual (f p - f q))) →
      2 * ε < c →
      (∀ a, ‖WeakDual.toStrongDual (f (i a) - g (i a))‖ ≤ ε) → Injective g

abbrev injectionScope := type_of% (@injective_of_approximation.{u, v, w})

theorem injectionBridge :
    injectionScope.{u, v, w} ↔ injectionArena.{u, v, w}.Law normActual.{u} := by
  constructor
  · intro h P
    exact h
  · intro h X normed scalar
    exact h ⟨X, normed, scalar⟩

@[reducible] def extensionArena : DependentFamily.Arena where
  signature := normSignature.{u}
  Law R := ∀ (P : Space.{u}) (a : ℕ → StrongDual ℝ P.X) (B : ℝ),
    (∀ n, ‖a n‖ ≤ B) →
    ∃ f : Ultrafilter ℕ → WeakDual ℝ P.X, Continuous f ∧
      (∀ n, f (pure n) = StrongDual.toWeakDual (a n)) ∧
      ∀ p, R.readout () P (WeakDual.toStrongDual (f p)) ≤ B

abbrev extensionScope := type_of% (@exists_bounded_extension.{u})

theorem extensionBridge : extensionScope.{u} ↔ extensionArena.{u}.Law normActual.{u} := by
  constructor
  · intro h P
    exact h
  · intro h X normed scalar
    exact h ⟨X, normed, scalar⟩

@[reducible] def neighborhoodSignature : DependentFamily.Signature where
  Params := Space.{v}
  State := fun P => P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => Filter P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def neighborhoodActual : DependentFamily.Realization neighborhoodSignature.{v} :=
  DependentFamily.realize neighborhoodSignature (fun _ _ x => 𝓝 x) (fun a => nomatch a)

@[reducible] def normalizationArena : DependentFamily.Arena where
  signature := neighborhoodSignature.{v}
  Law R := ∀ (P : Space.{v}) (a : ℕ → P.X) (B r : ℝ),
    (∀ n, ‖a n‖ ≤ B) → 0 < r →
    Tendsto (fun n => ‖a n‖) atTop (𝓝 r) →
    Tendsto (fun n => ‖a n‖⁻¹ • a n - r⁻¹ • a n) atTop (R.readout () P 0)

abbrev normalizationScope := type_of% (@normalize_sub_tendsto_zero.{v})

theorem normalizationBridge :
    normalizationScope.{v} ↔ normalizationArena.{v}.Law neighborhoodActual.{v} := by
  constructor
  · intro h P
    exact h
  · intro h E normed scalar
    exact h ⟨E, normed, scalar⟩

end Reg.D5.S3.Topology.Measures.WeakStarPerturbation
