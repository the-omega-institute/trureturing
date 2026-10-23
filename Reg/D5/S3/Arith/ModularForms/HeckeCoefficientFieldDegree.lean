import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree
import Reg.Support.SingleDependentReadout

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.ModularForms
open LeanInformationAudit UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open scoped BigOperators Matrix

noncomputable section

namespace Reg.D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ n m => n ≤ m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m s : ℕ) (_hm : 1 ≤ m) (_hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ))
    (_hnorm : (qExpansion 1 f).coeff 1 = 1)
    (eigenvalues : {p : ℕ // p.Prime} → ℂ)
    (_heig : ∀ p : {p : ℕ // p.Prime},
      letI : Fact p.val.Prime := ⟨p.property⟩
      primeHecke p.val (12 * m + s : ℕ) f = eigenvalues p • f),
    let K := IntermediateField.adjoin ℚ
      (Set.range (fun j : Fin m => (qExpansion 1 f).coeff (j.val + 1)))
    FiniteDimensional ℚ K ∧ R.readout () () (Module.finrank ℚ K) m

private theorem actual_law : arena.Law actual :=
  normalized_primeHecke_coefficient_field_degree

/-- The one-dimensional actual Miller space gives a normalized form that is an
eigenform for every actual prime Hecke operator, without assuming a toy operator. -/
private theorem inhabited_input :
    ∃ (f : CuspForm 𝒮ℒ (12 * 1 + 0 : ℕ))
      (eigenvalues : {p : ℕ // p.Prime} → ℂ),
      (qExpansion 1 f).coeff 1 = 1 ∧
      ∀ p : {p : ℕ // p.Prime},
        letI : Fact p.val.Prime := ⟨p.property⟩
        primeHecke p.val (12 * 1 + 0 : ℕ) f = eigenvalues p • f := by
  let hm : 1 ≤ (1 : ℕ) := le_rfl
  let hs : MillerResidualWeight 0 := by left; rfl
  let E := millerCoefficientEquiv 1 0 hm hs
  let f := E.symm (fun _ : Fin 1 => (1 : ℂ))
  let eigenvalues : {p : ℕ // p.Prime} → ℂ := fun p =>
    (integerMillerHeckeMatrix p.val 1 0 0 0 : ℂ)
  have hE : E f = fun _ : Fin 1 => (1 : ℂ) := E.apply_symm_apply _
  refine ⟨f, eigenvalues, ?_, ?_⟩
  · have h := congrFun hE 0
    change millerCoefficientEquiv 1 0 hm hs f 0 = 1 at h
    rw [millerCoefficientEquiv_apply] at h
    exact h
  · intro p
    let : Fact p.val.Prime := ⟨p.property⟩
    apply E.injective
    rw [map_smul]
    have h := millerHecke_conjugacy p.val 1 0 hm hs f
    change E (primeHecke p.val (12 * 1 + 0 : ℕ) f) =
      (integerMillerHeckeMatrix p.val 1 0).map (Int.castRingHom ℂ) *ᵥ E f at h
    rw [h, hE]
    ext j
    fin_cases j
    simp [Matrix.mulVec, dotProduct, eigenvalues]

private theorem rejected_law : ¬ arena.Law rejected := by
  obtain ⟨f, eigenvalues, hnorm, heig⟩ := inhabited_input
  intro h
  exact (h 1 0 le_rfl (by left; rfl) f hnorm eigenvalues heig).2

def family : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hbad : (1 : ℕ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.ModularForms.normalized_primeHecke_coefficient_field_degree)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree.unit
  realizationName := `Reg.D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n m => n ≤ m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.ModularForms.HeckeCoefficientFieldDegree
end
