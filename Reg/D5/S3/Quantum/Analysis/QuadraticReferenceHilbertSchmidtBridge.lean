import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace ENNReal
open HilbertSchmidt
open _root_.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : Empty → Unit → ℝ := fun a => nomatch a

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => Real.sqrt x) emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) emptyAnchor

def theoremLaw (R : Realization signature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (e : HilbertBasis w ℂ H) (ρ σ : H →L[ℂ] H)
    (hρtc : IsTraceClass ρ) (hσtc : IsTraceClass σ)
    (hρpos : 0 ≤ ρ) (hσpos : 0 ≤ σ)
    (s : w → ℝ) (hs : ∀ i, 0 < s i)
    (hσe : ∀ i, σ (e i) = (s i : ℂ) • e i)
    (hQ : quadraticMoment e s ρ ≠ ⊤),
    ∃ A : H →L[ℂ] H,
      IsHilbertSchmidt A ∧
      (∀ i, A (e i) = (((R.readout ⟨()⟩ () (s i))⁻¹ : ℝ) : ℂ) • ρ (e i)) ∧
      (∑' i : w, ‖A (e i)‖ ^ 2) = (quadraticMoment e s ρ).toReal ∧
      A * CFC.sqrt σ = ρ ∧
      Dense ((invSqrt σ).domain : Set H) ∧
      (∀ x : (invSqrt σ).domain, A (x : H) = ρ (invSqrt σ x)) ∧
      (∀ B : H →L[ℂ] H, IsSelfAdjoint B →
        ‖rightTrace ρ B hρtc‖ ^ 2 ≤
          (quadraticMoment e s ρ).toReal * (rightTrace σ (B ^ 2) hσtc).re)

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ w e ρ σ hρtc hσtc hρpos hσpos s hs hσe hQ
  exact quadratic_reference_hilbertSchmidt_bridge e ρ σ hρtc hσtc hρpos hσpos s hs hσe hQ

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, e, _⟩ := exists_hilbertBasis ℂ K
  letI : Finite w := e.orthonormal.linearIndependent.finite
  letI : Fintype w := Fintype.ofFinite w
  have htc : IsTraceClass (1 : K →L[ℂ] K) := isTraceClass_of_finiteDimensional _
  have hQ : quadraticMoment e (fun _ => 1) (1 : K →L[ℂ] K) ≠ ⊤ := by
    unfold quadraticMoment
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top
  obtain ⟨A, _, hcol, _, hprod, _⟩ := h (H := K) (w := w) e 1 1 htc htc (by positivity)
    (by positivity) (fun _ => 1) (fun _ => by norm_num)
    (fun _ => by simp) hQ
  have hzero (i : w) : A (e i) = 0 := by
    simpa only [rejected, realize, inv_zero, Complex.ofReal_zero, zero_smul] using hcol i
  have hAzero : A = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hs := A.hasSum (e.hasSum_repr x)
    simp only [map_smul, hzero, smul_zero] at hs
    simpa only [ContinuousLinearMap.zero_apply] using hs.unique hasSum_zero
  have hz : (1 : K →L[ℂ] K) = 0 := hprod.symm.trans (by simp [hAzero])
  exact one_ne_zero hz

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ x => Real.sqrt x) emptyAnchor
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

-- The law retains the complete original theorem telescope and every conclusion;
-- only the real square-root operand in the column identity is observed.
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge.quadratic_reference_hilbertSchmidt_bridge.{u})
    (type_of% (realize signature.{u} (fun _ _ x => Real.sqrt x) emptyAnchor))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge.sqrtUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x => Real.sqrt x) emptyAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "body", "arg", "fn",
        "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge
