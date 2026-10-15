import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
set_option maxHeartbeats 800000
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
noncomputable section

namespace integral_gluing
abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ[X]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    (∀ z : QF q, fromCompatible q (toCompatible q z) = z) ∧
    (∀ z : Compatible q, toCompatible q (fromCompatible q z) = z) ∧
    (∀ p : ℤ[X], (gluing q (fp q (r.readout () q p))).val =
      (AdjoinRoot.mk (f q) p, AdjoinRoot.mk (g q) p)) ∧
    (∀ z : Compatible q, (gluing q).symm z =
      fp q (a0 q z.val.1 - X * f q * half (a0 q z.val.1 - b0 q z.val.2))) ∧
    (∀ z : Compatible q, (a0 q z.val.1).degree < q ∧ (b0 q z.val.2).degree < q) ∧
    (∀ z : Compatible q, half (a0 q z.val.1 - b0 q z.val.2) =
      ∑ i ∈ Finset.range q, monomial i ((a0 q z.val.1 - b0 q z.val.2).coeff i / 2))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2 (by decide)).2.2.1 (C 1)
  have hz := congrArg (fun z : Plus 2 × Minus 2 => golden z.1) he
  change ((golden.toRingHom.comp (plus 2)).comp (fp 2)) 0 =
    (golden.toRingHom.comp (AdjoinRoot.mk (f 2))) (C 1) at hz
  simp only [Polynomial.C_1, map_zero, map_one] at hz
  have ha := congrArg _root_.D5.S0.Carrier.GoldenInt.a hz
  change (0 : ℤ) = 1 at ha
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q),
    (∀ z : QF q, fromCompatible q (toCompatible q z) = z) ∧
    (∀ z : Compatible q, toCompatible q (fromCompatible q z) = z) ∧
    (∀ p : ℤ[X], (gluing q (fp q p)).val =
      (AdjoinRoot.mk (f q) p, AdjoinRoot.mk (g q) p)) ∧
    (∀ z : Compatible q, (gluing q).symm z =
      fp q (a0 q z.val.1 - X * f q * half (a0 q z.val.1 - b0 q z.val.2))) ∧
    (∀ z : Compatible q, (a0 q z.val.1).degree < q ∧ (b0 q z.val.2).degree < q) ∧
    (∀ z : Compatible q, half (a0 q z.val.1 - b0 q z.val.2) =
      ∑ i ∈ Finset.range q, monomial i ((a0 q z.val.1 - b0 q z.val.2).coeff i / 2))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.integral_gluing, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def integral_gluing_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.integral_gluing)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.integral_gluing_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.integral_gluing.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end integral_gluing

namespace gluing_generators
abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ),
    (gluing q (fp q X)).val =
      (AdjoinRoot.root (f q), AdjoinRoot.root (g q)) ∧
    (gluing q (fp q (W q))).val = (1, -1) ∧
    (∀ z : ℤ, (gluing q (fp q (C (r.readout () q z)))).val = ((z : Plus q), (z : Minus q))) ∧
    (∀ p : ℤ[X], commonQuotientEquiv q (Ideal.Quotient.mk _ p) = commonPolynomial q p) ∧
    reduce (g q) = ∑ k ∈ Finset.range (q + 1), (X : (ZMod 2)[X]) ^ k
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2).2.2.1 1
  have hz : (0 : Plus 2) = 1 := by
    simpa [bad, realize] using congrArg Prod.fst he
  have hg := congrArg golden hz
  have ha := congrArg _root_.D5.S0.Carrier.GoldenInt.a hg
  norm_num at ha
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def evidence : Registration arena (∀ (q : ℕ),
    (gluing q (fp q X)).val =
      (AdjoinRoot.root (f q), AdjoinRoot.root (g q)) ∧
    (gluing q (fp q (W q))).val = (1, -1) ∧
    (∀ z : ℤ, (gluing q (fp q (C z))).val = ((z : Plus q), (z : Minus q))) ∧
    (∀ p : ℤ[X], commonQuotientEquiv q (Ideal.Quotient.mk _ p) = commonPolynomial q p) ∧
    reduce (g q) = ∑ k ∈ Finset.range (q + 1), (X : (ZMod 2)[X]) ^ k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.gluing_generators, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def gluing_generators_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.gluing_generators)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.gluing_generators_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.gluing_generators.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end gluing_generators

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_evenAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := ℕ
  State p := Compatible p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ q z => a0 q z.val.1 - b0 q z.val.2) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (z : Compatible q),
    ∀ i : ℕ, (2 : ℤ) ∣ (r.readout () q z).coeff i
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h 1 0 0
  norm_num [bad, realize, Polynomial.coeff_one] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, toCompatible 1 (fp 1 X), ?_⟩
  intro h
  change a0 1 0 - b0 1 0 =
    a0 1 (AdjoinRoot.mk (f 1) X) - b0 1 (AdjoinRoot.mk (g 1) X) at h
  have hf : a0 1 (AdjoinRoot.mk (f 1) X) = C 1 := by
    change X %ₘ f 1 = C 1
    have he : f 1 = X - C 1 := by norm_num [f, S]
    rw [he, Polynomial.modByMonic_X_sub_C_eq_C_eval]
    simp
  have hg : b0 1 (AdjoinRoot.mk (g 1) X) = C (-1) := by
    change X %ₘ g 1 = C (-1)
    have he : g 1 = X - C (-1) := by norm_num [g, S]
    rw [he, Polynomial.modByMonic_X_sub_C_eq_C_eval]
    simp
  rw [hf,hg] at h
  have he := congrArg (fun p : ℤ[X] => p.coeff 0) h
  norm_num at he
def evidence : Registration arena (∀ (q : ℕ) (z : Compatible q),
    ∀ i : ℕ, (2 : ℤ) ∣ (a0 q z.val.1 - b0 q z.val.2).coeff i) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_even, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_even) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_evenAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_evenAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => a0 q z.val.1 - b0 q z.val.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.compatible_evenAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_idealsAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ q => f q) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ),
    (Ideal.span {r.readout () () q} : Ideal ℤ[X]) ⊔ Ideal.span {g q} = Ideal.span {2, g q} ∧
    (Ideal.span {r.readout () () q} : Ideal ℤ[X]) ⊓ Ideal.span {g q} = Ideal.span {F q}
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he : (⊥ : Ideal ℤ[X]) = ⊤ := by simpa [bad, realize, F, S] using (h 0).2
  exact bot_ne_top he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrArg (fun p : ℤ[X] => p.coeff 1) h
  norm_num [actual, realize, f, S, Finset.sum_range_succ, Polynomial.coeff_one] at he
def evidence : Registration arena (∀ (q : ℕ),
    (Ideal.span {f q} : Ideal ℤ[X]) ⊔ Ideal.span {g q} = Ideal.span {2, g q} ∧
    (Ideal.span {f q} : Ideal ℤ[X]) ⊓ Ideal.span {g q} = Ideal.span {F q}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_ideals, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_ideals) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_idealsAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_idealsAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => f q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.sign_idealsAudit
