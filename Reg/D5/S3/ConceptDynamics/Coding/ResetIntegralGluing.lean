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

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

private def commonOneEval : Common 1 →+* ZMod 2 :=
  AdjoinRoot.lift (RingHom.id (ZMod 2)) 1 (by norm_num [reduce, g, S])

private theorem commonOne_zero_ne_one : (0 : Common 1) ≠ 1 := by
  intro h
  have he : (0 : ZMod 2) = 1 := by simpa using congrArg commonOneEval h
  exact zero_ne_one he

private theorem product_zero_ne_one : (0 : Plus 1 × Minus 1) ≠ 1 := by
  intro h
  apply commonOne_zero_ne_one
  have he : rplus 1 (0 : Plus 1) = rplus 1 (1 : Plus 1) :=
    congrArg (fun d : Plus 1 × Minus 1 => rplus 1 d.1) h
  simpa only [map_zero, map_one] using he

namespace component_residue_kernels
abbrev signature : Signature where
  Params := ℕ
  State q := Plus q ⊕ Minus q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Common q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ q z => Sum.elim (rplus q) (rminus q) z) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    (∀ a : Plus q, r.readout () q (Sum.inl a) = 0 ↔ ∃ a' : Plus q, a = 2 * a') ∧
    (∀ b : Minus q, r.readout () q (Sum.inr b) = 0 ↔ ∃ b' : Minus q, b = 2 * b')
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := ((h 1 (by decide)).1 0).mpr ⟨0, by simp⟩
  change (1 : Common 1) = 0 at he
  exact commonOne_zero_ne_one he.symm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, Sum.inl 0, Sum.inl 1, ?_⟩
  change rplus 1 0 ≠ rplus 1 1
  simpa only [map_zero, map_one] using commonOne_zero_ne_one
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q),
    (∀ a : Plus q, rplus q a = 0 ↔ ∃ a' : Plus q, a = 2 * a') ∧
    (∀ b : Minus q, rminus q b = 0 ↔ ∃ b' : Minus q, b = 2 * b')) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.component_residue_kernels, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.component_residue_kernels)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.component_residue_kernels.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.component_residue_kernels.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => Sum.elim (rplus q) (rminus q) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end component_residue_kernels

namespace w_eigenlattices
abbrev signature : Signature where
  Params := ℕ
  State q := Compatible q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Plus q × Minus q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ z => z.val) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (z : Compatible q),
    (z ∈ eigenLattice q 1 ↔ ∃ a : Plus q, r.readout () q z = (2 * a, 0)) ∧
    (z ∈ eigenLattice q (-1) ↔ ∃ b : Minus q, r.readout () q z = (0, 2 * b))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨a, ha⟩ := (h 1 (by decide) 0).1.mp (zero_mem _)
  have he : (1 : Minus 1) = 0 := congrArg Prod.snd ha
  apply commonOne_zero_ne_one
  simpa only [map_one, map_zero] using (congrArg (rminus 1) he).symm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (0 : Plus 1 × Minus 1) ≠ 1
  exact product_zero_ne_one
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q) (z : Compatible q),
    (z ∈ eigenLattice q 1 ↔ ∃ a : Plus q, z.val = (2 * a, 0)) ∧
    (z ∈ eigenLattice q (-1) ↔ ∃ b : Minus q, z.val = (0, 2 * b))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.w_eigenlattices, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.w_eigenlattices)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.w_eigenlattices.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.w_eigenlattices.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end w_eigenlattices

namespace eigenlattice_sum_even_product
abbrev signature : Signature where
  Params := ℕ
  State q := Compatible q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Plus q × Minus q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ z => z.val) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (z : Compatible q),
    z ∈ eigenLattice q 1 ⊔ eigenLattice q (-1) ↔
      ∃ a : Plus q, ∃ b : Minus q, r.readout () q z = (2 * a, 2 * b)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨a, b, hab⟩ := (h 1 (by decide) 0).mp (zero_mem _)
  have he : rplus 1 (1 : Plus 1) = rplus 1 (2 * a) :=
    congrArg (fun d : Plus 1 × Minus 1 => rplus 1 d.1) hab
  have hz := ((component_residue_kernels 1 (by decide)).1 (2 * a)).mpr ⟨a, rfl⟩
  apply commonOne_zero_ne_one
  simpa only [map_one, hz] using he.symm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change (0 : Plus 1 × Minus 1) ≠ 1
  exact product_zero_ne_one
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q) (z : Compatible q),
    z ∈ eigenLattice q 1 ⊔ eigenLattice q (-1) ↔
      ∃ a : Plus q, ∃ b : Minus q, z.val = (2 * a, 2 * b)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.eigenlattice_sum_even_product, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.eigenlattice_sum_even_product)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.eigenlattice_sum_even_product.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.eigenlattice_sum_even_product.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end eigenlattice_sum_even_product

namespace pullback_conductor_even_product
abbrev signature : Signature where
  Params := ℕ
  State q := Plus q × Minus q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Plus q × Minus q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ d => d) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (d : Plus q × Minus q),
    (∀ t : Plus q × Minus q, r.readout () q d * t ∈ (rplus q).pullback (rminus q)) ↔
      ∃ e : Plus q × Minus q, d = 2 * e
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨e, he⟩ := (h 1 (by decide) 1).mp (by
    intro t
    change rplus 1 ((0 : Plus 1 × Minus 1) * t).1 =
      rminus 1 ((0 : Plus 1 × Minus 1) * t).2
    simp)
  have hh : rplus 1 (1 : Plus 1) = rplus 1 (2 * e.1) :=
    congrArg (fun d : Plus 1 × Minus 1 => rplus 1 d.1) he
  have hz := ((component_residue_kernels 1 (by decide)).1 (2 * e.1)).mpr ⟨e.1, rfl⟩
  apply commonOne_zero_ne_one
  simpa only [map_one, hz] using hh.symm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, 0, 1, product_zero_ne_one⟩
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q) (d : Plus q × Minus q),
    (∀ t : Plus q × Minus q, d * t ∈ (rplus q).pullback (rminus q)) ↔
      ∃ e : Plus q × Minus q, d = 2 * e) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.pullback_conductor_even_product, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.pullback_conductor_even_product)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.pullback_conductor_even_product.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.pullback_conductor_even_product.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end pullback_conductor_even_product

namespace common_residue_surjective
abbrev signature : Signature where
  Params := ℕ
  State q := Compatible q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Common q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ q z => commonResidue q z) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ q : ℕ, Function.Surjective (r.readout () q)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨z, hz⟩ := h 1 (1 : Common 1)
  change (0 : Common 1) = 1 at hz
  exact commonOne_zero_ne_one hz
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change commonResidue 1 0 ≠ commonResidue 1 1
  simpa only [map_zero, map_one] using commonOne_zero_ne_one
def evidence : Registration arena (∀ q : ℕ, Function.Surjective (commonResidue q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.common_residue_surjective, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.common_residue_surjective)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_surjective.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_surjective.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => commonResidue q z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end common_residue_surjective

namespace common_residue_kernel
abbrev signature : Signature where
  Params := ℕ
  State q := Compatible q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Common q
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ q z => commonResidue q z) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (z : Compatible q),
    r.readout () q z = 0 ↔ z ∈ eigenLattice q 1 ⊔ eigenLattice q (-1)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 1 (by decide) 0).mpr (zero_mem _)
  change (1 : Common 1) = 0 at he
  exact commonOne_zero_ne_one he.symm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change commonResidue 1 0 ≠ commonResidue 1 1
  simpa only [map_zero, map_one] using commonOne_zero_ne_one
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q),
    (commonResidue q).toAddMonoidHom.ker = eigenLattice q 1 ⊔ eigenLattice q (-1)) where
  actual := actual
  bridge := by
    constructor
    · intro h q hq z
      change z ∈ (commonResidue q).toAddMonoidHom.ker ↔ _
      rw [h q hq]
    · intro h q hq
      ext z
      exact h q hq z
  variation := ⟨by
    intro q hq z
    change z ∈ (commonResidue q).toAddMonoidHom.ker ↔ _
    rw [common_residue_kernel q hq], bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.common_residue_kernel)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_kernel.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_kernel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => commonResidue q z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end common_residue_kernel

namespace common_residue_cardinality
abbrev signature : Signature where
  Params := ℕ
  State q := Type
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ T => Nat.card T) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    r.readout () q (Common q) = 2 ^ q ∧
    r.readout () q
      (Compatible q ⧸ (eigenLattice q 1 ⊔ eigenLattice q (-1))) = 2 ^ q
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 1 (by decide)).1
  norm_num [bad, realize] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, Empty, Unit, by simp [actual, realize]⟩
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q),
    Nat.card (Common q) = 2 ^ q ∧
    Nat.card (Compatible q ⧸ (eigenLattice q 1 ⊔ eigenLattice q (-1))) = 2 ^ q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.common_residue_cardinality, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.common_residue_cardinality)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_cardinality.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.common_residue_cardinality.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => Nat.card T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end common_residue_cardinality

namespace exact_common_time_order
abbrev signature : Signature where
  Params := ℕ
  State q := (Common q)ˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ u => orderOf u) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := r.readout () 1 (commonTimeUnit 1) = 1 ∧
    ∀ q : ℕ, 2 ≤ q → r.readout () q (commonTimeUnit q) = q + 1
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h.1
  norm_num [bad, realize] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, commonTimeUnit 2, ?_⟩
  change orderOf (1 : (Common 2)ˣ) ≠ orderOf (commonTimeUnit 2)
  rw [orderOf_one, exact_common_time_order.2 2 (by decide)]
  decide
def evidence : Registration arena (orderOf (commonTimeUnit 1) = 1 ∧
    ∀ q : ℕ, 2 ≤ q → orderOf (commonTimeUnit q) = q + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.exact_common_time_order, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.exact_common_time_order)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.exact_common_time_order.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit.exact_common_time_order.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => orderOf u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end exact_common_time_order

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing.uniformAudit
