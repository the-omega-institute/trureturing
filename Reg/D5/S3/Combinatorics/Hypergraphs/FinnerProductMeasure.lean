import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
open scoped ENNReal BigOperators

namespace Reg.D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
universe u

abbrev productSignature : Signature where
  Params := Σ n : ℕ, Σ E : Fin n → Type u, (i : Fin n) → E i → ℝ≥0∞
  State p := ∀ i, p.2.1 i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def productActual : Realization productSignature.{u} :=
  realize productSignature (fun _ p x => ∏ i, p.2.2 i (x i)) (fun e => nomatch e)

def productRejected : Realization productSignature.{u} :=
  realize productSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := productSignature.{u}
  Law R := ∀ {n : ℕ} {E : Fin n → Type u} {mE : ∀ i, MeasurableSpace (E i)}
    (μ : (i : Fin n) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞), (∀ i, Measurable (f i)) →
      (∫⁻ x, R.readout () ⟨n, E, f⟩ x ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i

theorem product_source_bridge : (type_of% @lintegral_fin_prod.{u}) ↔
    productArena.{u}.Law productActual := Iff.rfl

private theorem productRejectedLaw : ¬ productArena.{u}.Law productRejected := by
  intro law
  have H := law (n := 0) (E := fun _ => ULift.{u} Unit)
    (fun _ => Measure.dirac ⟨()⟩) (fun _ _ => 1) (fun _ => measurable_const)
  simpa [productRejected, realize] using H

private theorem productDependence : ObservationalDependence productSignature.{u} productActual := by
  classical
  intro role
  let E (_ : Fin 1) := ULift.{u} Bool
  let f : (i : Fin 1) → E i → ℝ≥0∞ := fun _ x => if x.down then 1 else 0
  refine ⟨⟨1, E, f⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  norm_num [productActual, realize, f, Fin.prod_univ_succ]

def productFamily : Registration productArena.{u} (type_of% @lintegral_fin_prod.{u}) where
  actual := productActual
  bridge := product_source_bridge
  variation := ⟨@lintegral_fin_prod.{u}, productRejected, productRejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨productRejected, ?_, rfl, productRejectedLaw⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := productDependence

def productRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lintegral_fin_prod.{u}) (Realization productSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.lintegral_fin_prod.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.productFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productArena.{u}⟩
  objectArena := .source ⟨productArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena.{u} ⟨productFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize productSignature.{u} (fun _ p x => ∏ i, p.2.2 i (x i))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
