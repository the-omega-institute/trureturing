import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The whole original spectral-form statement with its actual ambient norm observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (G)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (Pi C)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping (G0)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
  (D K Sigma energy lift mean_Pi free_root_least_energy)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
  (boundaryOperator actual_positive_spectral_exhaustion)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter
open scoped Topology

abbrev signature : Signature where
  Params := Unit
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => ‖F‖ ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
    (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
    Monotone (fun i => (mu i)⁻¹) ∧
    Tendsto (fun i => (mu i)⁻¹) atTop atTop ∧
    (∀ i, ((b i).val,(mu i)⁻¹ • (b i).val) ∈ boundaryOperator.graph) ∧
    (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
    (∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) ∧
    (∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) ∧
    (∀ F : D,
      HasSum (fun i => (b.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i)
        (energy F.val)) ∧
    (∀ (lam : ℝ) (F : D),
      (∀ i, (mu i)⁻¹ < lam → b.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0) →
      lam * R.readout () () (Pi F.val) ≤ energy F.val)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨b,k,mu,_,_,_,_,_,_,_,_,_,_,hsupport⟩
  let f : D := ⟨0,D.zero_mem⟩
  have hz : ‖lift f‖^2 ≤ 0 := by
    simpa using ((free_root_least_energy f).2.2.2.2.1 0 0
      (by change (0 : G) = _; simp)).2
  have he : energy f.val = 0 := by
    rw [(free_root_least_energy f).2.2.2.1]
    exact le_antisymm hz (sq_nonneg _)
  have h := hsupport 1 f (by intro i hi; change b.repr 0 i = 0; simp)
  change 1 * 1 ≤ energy f.val at h
  rw [he] at h
  norm_num at h

def familyRegistration : Registration arena (type_of% actual_spectral_form_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_spectral_form_energy,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    obtain ⟨b,k,mu,h⟩ := actual_positive_spectral_exhaustion
    refine ⟨(),(0 : G),(b 0).val,?_⟩
    change ‖(0 : G)‖ ^ 2 ≠ ‖(b 0).val‖ ^ 2
    have hn : ‖(b 0).val‖ = 1 := b.orthonormal.1 0
    rw [hn]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_spectral_form_energy)
    (type_of% (realize signature (fun _ _ F => ‖F‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm.unit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ F => ‖F‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg","body","arg","body","arg","body",
        "arg","arg","arg","arg","arg","arg","arg","arg","arg","arg",
        "body","body","body","fn","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","arg","arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm
