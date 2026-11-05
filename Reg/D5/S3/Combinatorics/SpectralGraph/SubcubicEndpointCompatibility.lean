import D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Whole-source audit of the actual first-departure norm observation. -/

noncomputable section

namespace Reg.D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility

open _root_.D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates
open _root_.D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix SimpleGraph

universe u
abbrev Parameters := Σ V : Type u, Σ _ : Fintype V, Σ _ : DecidableEq V,
  Σ _ : Matrix V V ℚ, Σ _ : V, ℚ × ℚ

namespace Parameters
abbrev V (p : Parameters.{u}) := p.1
abbrev finite (p : Parameters.{u}) : Fintype p.V := p.2.1
abbrev equality (p : Parameters.{u}) : DecidableEq p.V := p.2.2.1
abbrev M (p : Parameters.{u}) : Matrix p.V p.V ℚ := p.2.2.2.1
abbrev o (p : Parameters.{u}) : p.V := p.2.2.2.2.1
abbrev a (p : Parameters.{u}) : ℚ := p.2.2.2.2.2.1
abbrev c (p : Parameters.{u}) : ℚ := p.2.2.2.2.2.2
end Parameters

attribute [instance] Parameters.finite Parameters.equality

private abbrev pack {V : Type u} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℚ) (o : V) (a c : ℚ) : Parameters.{u} :=
  ⟨V, inferInstance, inferInstance, M, o, a, c⟩

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p j => chainNorm p.M p.o p.a p.c j) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) (hdeg : ∀ x, G.degree x ≤ 3)
    (o : V) (a c : ℚ) (hc : 0 < c),
    ∃ r : ℕ, ∃ hr : 0 < r, r ≤ Fintype.card V ∧
      (∀ j < r, O.readout () (pack (uniformMatrix G a c) o a c) j = 1) ∧
      O.readout () (pack (uniformMatrix G a c) o a c) r ≠ 1 ∧
      (O.readout () (pack (uniformMatrix G a c) o a c) r = 0 ↔ EndpointPath G o) ∧
      (O.readout () (pack (uniformMatrix G a c) o a c) r = 0 ∨
        O.readout () (pack (uniformMatrix G a c) o a c) r = 2 ∨
        O.readout () (pack (uniformMatrix G a c) o a c) r = 3) ∧
      (Compatible (uniformMatrix G a c) o ↔ EndpointPath G o) ∧
      (¬ EndpointPath G o → ∀ (n : ℕ)
        (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ), PositiveJacobi J →
          ¬ MatchesThrough (uniformMatrix G a c) o J (2 * r)) ∧
      (EndpointPath G o → r = Fintype.card V ∧
        (∃ e : G ≃g pathGraph r, e o = ⟨0, hr⟩ ∧
          (uniformMatrix G a c).reindex e.toEquiv e.toEquiv = pathMatrix r a c ∧
          (Pi.single o (1 : ℚ)) ∘ e.toEquiv.symm = Pi.single ⟨0, hr⟩ 1 ∧
          (∀ v : V → ℚ, pathMatrix r a c *ᵥ (v ∘ e.toEquiv.symm) =
            (uniformMatrix G a c *ᵥ v) ∘ e.toEquiv.symm) ∧
          ∀ k, ((uniformMatrix G a c) ^ k) o o =
            ((pathMatrix r a c) ^ k) ⟨0, hr⟩ ⟨0, hr⟩) ∧
        ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ),
          PositiveJacobi J → MatchesThrough (uniformMatrix G a c) o J (2 * r) →
            n + 1 = r ∧ J = pathMatrix (n + 1) a c)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  have ht : (⊥ : SimpleGraph V).IsTree :=
    ⟨connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩, isAcyclic_bot⟩
  obtain ⟨r, hr, _, _, hn, _⟩ := h ht (by intro x; simp) (ULift.up ()) 0 1 (by norm_num)
  exact hn rfl

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let p : Parameters.{u} := pack
    (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℚ) (ULift.up ()) 0 1
  refine ⟨p, 0, 1, ?_⟩
  change chainNorm (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℚ)
    (ULift.up ()) 0 1 0 ≠ chainNorm 0 (ULift.up ()) 0 1 1
  norm_num [actual, realize, p, pack, chainNorm, chainVector, polynomialVector,
    chainPolynomial, affinePolynomial, dotProduct, Matrix.col_apply, Matrix.one_apply]

def family : Registration arena.{u} (type_of% (@complete78_3.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete78_3.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@complete78_3.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility.complete78_3.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility
