import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The original real polar statement with the actual total resolvent observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (G)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (Pi C mean centered_suffix_residual Pi_const)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping (G0)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (D K Sigma mean_Pi)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
  (boundaryOperator boundaryResolvent actual_compact_resolvent actual_self_adjoint_realization)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => boundaryResolvent F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := 
    ∃ (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
      (W : K ≃ₗᵢ[ℝ] G0) (S T R : K →L[ℝ] K),
      (∀ i, 0 < mu i) ∧
      (∀ x : K, ∀ i, b.repr (W x) i = k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (S x) i = Real.sqrt (mu i) * k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (T x) i = mu i * k.repr x i) ∧
      (∀ x : K, ∀ i, k.repr (R x) i = (1 + mu i)⁻¹ * k.repr x i) ∧
      (∀ x : K, (T x).val = Sigma x.val) ∧
      (∀ x : K, S (S x) = T x) ∧
      (∀ x : K, (W (S x)).val = C x.val) ∧
      (∀ u : G0, C.adjoint u.val = (S (W.symm u)).val) ∧
      (Function.Injective S ∧ Function.Injective T) ∧
      (∀ u : G0, u.val ∈ D ↔ ∃ x : K, W (S x) = u) ∧
      (∀ u : G0, u.val ∈ boundaryOperator.domain ↔ ∃ x : K, W (T x) = u) ∧
      (∀ u h : G, (u,h) ∈ boundaryOperator.graph ↔
        ∃ x : K, h = (W x).val ∧ Pi u = (W (T x)).val) ∧
      (∀ x : K, R x + T (R x) = x ∧ R (x + T x) = x) ∧
      (∀ F : G, obs.readout () () F = constG (mean F) +
        (W (T (R (W.symm ⟨Pi F,mean_Pi F⟩)))).val)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : G)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨b,k,mu,W,S,T,R,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hres⟩
  have h := hres (constG 1)
  change (0 : G) = _ at h
  have hcenter (u : G0) : mean u.val = 0 := u.property
  have hm := congrArg mean h
  simp only [map_zero,map_add,centered_suffix_residual.2.1,hcenter] at hm
  norm_num at hm

def familyRegistration : Registration arena (type_of% actual_polar_domains_resolvent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_polar_domains_resolvent,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : G),constG 1,?_⟩
    have hg : (constG 1,0) ∈ boundaryOperator.graph :=
      (actual_self_adjoint_realization.2.2.2.2.2.2.2 (constG 1)).mpr ⟨1,rfl⟩
    have hr := (actual_compact_resolvent.2.1 (constG 1) 0).mp hg
    simp only [add_zero] at hr
    change boundaryResolvent 0 ≠ boundaryResolvent (constG 1)
    rw [map_zero,hr]
    intro hz
    have hm := congrArg mean hz
    simp only [map_zero,centered_suffix_residual.2.1] at hm
    norm_num at hm

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_polar_domains_resolvent)
    (type_of% (realize signature (fun _ _ F => boundaryResolvent F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ F => boundaryResolvent F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg","body","arg","body","arg","body","arg","body","arg","body","arg","body","arg","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
