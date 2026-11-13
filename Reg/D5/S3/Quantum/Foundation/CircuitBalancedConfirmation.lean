import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source-family reconstruction for the original cone, unit and comparison.
Whole-family variation, sensitivity, observational dependence and source-coordinate
selection remain unsupplied. No complete four-slot registration is asserted. -/

noncomputable section
universe u
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  A : Type u
  [add : NormedAddCommGroup A]
  [space : NormedSpace ℝ A]
  [finite : FiniteDimensional ℝ A]
  cone : PointedCone ℝ A
  unit : A →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.A × P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => comparison P.cone P.unit x.1 x.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    let T := fun p x => O.readout () P (p, x)
    IsClosed (C : Set P.A) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.A) = ⊤ →
    (∀ p : pure C u, balanced (pure C u) (fun q => T q p)) →
    ∃ e : pure C u → (P.A →ₗ[ℝ] ℝ),
      (∀ p : pure C u, confirms C u p (e p)) ∧
      (∀ p q : pure C u, e p q = T q p) ∧
      (∀ p q : pure C u, T p q = T q p) ∧
      (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, e p x ≤ f x) ∧
      (∀ (p : pure C u) x, x ∈ C → T p x = e p x) ∧
      (∀ (p : pure C u) (n : ℕ) (q : Fin n → pure C u) (w : Fin n → ℝ),
        (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
        T p (∑ i, w i • (q i : P.A)) = ∑ i, w i * T (q i) p)

abbrev sourceScope : Prop := type_of% (@circuit_balance_least_confirmation.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.A P.add P.space P.finite P.cone P.unit
  · intro h A add space finite C u
    exact h (@Inputs.mk A add space finite C u)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@circuit_balance_least_confirmation.{u})

abbrev equivalenceArena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    let T := fun p x => O.readout () P (p, x)
    IsClosed (C : Set P.A) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.A) = ⊤ →
    ((∀ (p : pure C u) (n : ℕ) (q : Fin n → pure C u) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      T p (∑ i, w i • (q i : P.A)) = ∑ i, w i * T (q i) p) ↔
      ∀ p : pure C u, balanced (pure C u) (fun q => T q p)) ∧
    ((∀ p : pure C u, balanced (pure C u) (fun q => T q p)) ↔
      (∀ p q : pure C u, T p q = T q p) ∧
      (∀ p : pure C u, balanced (pure C u) (fun q => T q p))) ∧
    ((∀ p : pure C u, balanced (pure C u) (fun q => T q p)) ↔
      ∃ e : pure C u → (P.A →ₗ[ℝ] ℝ),
        (∀ p : pure C u, confirms C u p (e p)) ∧
        (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, e p x ≤ f x) ∧
        (∀ p q : pure C u, e p q = e q p))

abbrev equivalenceSourceScope : Prop := type_of% (@full_mixture_iff_circuit_balance.{u})

theorem equivalence_source_bridge :
    equivalenceSourceScope.{u} ↔ equivalenceArena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.A P.add P.space P.finite P.cone P.unit
  · intro h A add space finite C u
    exact h (@Inputs.mk A add space finite C u)

theorem equivalence_actual_positive : equivalenceArena.{u}.Law actual.{u} :=
  equivalence_source_bridge.mp (@full_mixture_iff_circuit_balance.{u})

namespace Normalization

/-- The normalization theorem does not require a finite dimensional carrier. -/
structure Inputs where
  A : Type u
  [add : NormedAddCommGroup A]
  [space : NormedSpace ℝ A]
  cone : PointedCone ℝ A
  unit : A →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P x => (P.unit x)⁻¹ • x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ P : Inputs.{u},
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    ∀ x : P.A, x ∈ P.cone → x ≠ 0 →
      O.readout () P x ∈ base P.cone P.unit

abbrev sourceScope : Prop := type_of% (@normalized_mem.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P hu x hx hne
    exact @h P.A P.add P.space P.cone P.unit hu x hx hne
  · intro h A add space C u hu x hx hne
    exact h (@Inputs.mk A add space C u) hu x hx hne

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@normalized_mem.{u})

end Normalization

/-- Exact original telescopes of the exposed convex-geometric owners. These
checks do not supply four-slot variation or source-coordinate evidence. -/
abbrev compactSourceScope : Prop := type_of% (@base_compact.{u})
abbrev nonnegativeSourceScope : Prop := type_of% (@nonneg_on_cone.{u})
abbrev boundSourceScope : Prop := type_of% (@cone_bound.{u})

theorem compact_source_exact : compactSourceScope.{u} := @base_compact.{u}
theorem nonnegative_source_exact : nonnegativeSourceScope.{u} := @nonneg_on_cone.{u}
theorem bound_source_exact : boundSourceScope.{u} := @cone_bound.{u}

end Reg.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
