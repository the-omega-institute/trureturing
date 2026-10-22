import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.InterlaceFan.Cyclotomic
import Reg.D5.S3.Arith.InterlaceFan.Fourier
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.InterlaceFan.Cyclotomic
open _root_.D5.S3.Arith.InterlaceFan.Defs
open _root_.D5.S3.Arith.InterlaceFan.Cyclotomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Arith.InterlaceFan.Fourier
open Finset
noncomputable section

private lemma dependence : ObservationalDependence valueSignature valueActual := by
  intro i
  refine ⟨⟨2, fun _ => 1⟩, 0, 1, ?_⟩
  norm_num [valueActual, realize, I, Fin.sum_univ_succ]

abbrev cosineArena : Arena where
  signature := valueSignature
  Law R := ∀ (n j : ℕ) (x : Fin (n / 2) → ℝ),
    R.readout () ⟨n, x⟩ j = -(1 / 2 : ℝ) * evalCos n j x

private lemma cosineRejected : ¬ cosineArena.Law valueOne := by
  intro h
  have he := h 2 0 (fun _ => 0)
  norm_num [valueOne, realize, evalCos] at he

abbrev propagationSignature : Signature where
  Params := Σ n : ℕ, Fin (n / 2) → ℝ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def propagationActual : Realization propagationSignature :=
  realize propagationSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e)

def propagationBadLeft : Realization propagationSignature :=
  realize propagationSignature (fun r p j => if r then I p.1 j p.2 else 0)
    (fun e => nomatch e)

def propagationBadRight : Realization propagationSignature :=
  realize propagationSignature (fun r p j => if r then 0 else I p.1 j p.2)
    (fun e => nomatch e)

abbrev propagationArena : Arena where
  signature := propagationSignature
  Law R := ∀ (n d : ℕ), 0 < n → d ∣ n →
    ∀ (x : Fin (n / 2) → ℝ), IsRationalPt x → ∀ (c : ℚ) (s t : ℕ),
    s ∈ orderClass n d → t ∈ orderClass n d →
    R.readout false ⟨n, x⟩ s = (c : ℝ) → R.readout true ⟨n, x⟩ t = (c : ℝ)

private lemma propagationBadLeftRejected : ¬ propagationArena.Law propagationBadLeft := by
  intro h
  have he := h 2 1 (by omega) (one_dvd _) (fun _ => 1)
    (fun k => ⟨1, by norm_num⟩) 0 0 0
    (by norm_num [orderClass, certIdx]) (by norm_num [orderClass, certIdx])
    (by norm_num [propagationBadLeft, realize])
  norm_num [propagationBadLeft, realize, I, Fin.sum_univ_succ] at he

private lemma propagationBadRightRejected : ¬ propagationArena.Law propagationBadRight := by
  intro h
  have he := h 2 1 (by omega) (one_dvd _) (fun _ => 1)
    (fun k => ⟨1, by norm_num⟩) (-1) 0 0
    (by norm_num [orderClass, certIdx]) (by norm_num [orderClass, certIdx])
    (by norm_num [propagationBadRight, realize, I, Fin.sum_univ_succ])
  norm_num [propagationBadRight, realize] at he

private lemma propagationDependence :
    ObservationalDependence propagationSignature propagationActual := by
  intro i
  refine ⟨⟨2, fun _ => 1⟩, 0, 1, ?_⟩
  norm_num [propagationActual, realize, I, Fin.sum_univ_succ]

abbrev witnessArena : Arena where
  signature := valueSignature
  Law R := ∀ (n d : ℕ), 2 ≤ n → d ∣ n →
    ∃ x : Fin (n / 2) → ℝ, IsRationalPt x ∧ ∀ j ∈ certIdx n,
      R.readout () ⟨n, x⟩ j = -(1 / 2 : ℝ) *
        ((n : ℝ) * (if j ∈ orderClass n d then 1 else 0) - Nat.totient d)

private lemma witnessRejected : ¬ witnessArena.Law valueZero := by
  intro h
  obtain ⟨x, hx, hv⟩ := h 2 1 (by omega) (one_dvd _)
  have he := hv 0 (by norm_num [certIdx])
  norm_num [valueZero, realize, orderClass, certIdx] at he

abbrev polynomialSignature : Signature where
  Params := Σ n : ℕ, Fin (n / 2) → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def polynomialActual : Realization polynomialSignature :=
  realize polynomialSignature (fun _ p j =>
    ((sigmaPoly p.1 p.2).map Complex.ofRealHom).eval (zeta p.1 ^ j)) (fun e => nomatch e)

def polynomialOne : Realization polynomialSignature :=
  realize polynomialSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev polynomialArena : Arena where
  signature := polynomialSignature
  Law R := ∀ (n j : ℕ) (x : Fin (n / 2) → ℝ),
    R.readout () ⟨n, x⟩ j = (evalCos n j x : ℂ)

private lemma polynomialRejected : ¬ polynomialArena.Law polynomialOne := by
  intro h
  have he := h 2 0 (fun _ => 0)
  norm_num [polynomialOne, realize, evalCos] at he

private lemma polynomialDependence :
    ObservationalDependence polynomialSignature polynomialActual := by
  intro i
  refine ⟨⟨2, fun _ => 1⟩, 0, 1, ?_⟩
  simp only [polynomialActual, realize, I_eq_eval_poly]
  norm_num [evalCos, Fin.sum_univ_succ]

def cosineSource : Registration cosineArena (type_of% @I_eq_eval) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨I_eq_eval, valueOne, cosineRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨valueOne, ?_, rfl, cosineRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def cosineAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@I_eq_eval) (Realization valueSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.cosineUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.cosineSource
  realizationSource := none
  generated := false
  arena := .source ⟨cosineArena⟩
  objectArena := .source ⟨cosineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cosineArena ⟨cosineSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Cyclotomic
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def polynomialSource : Registration polynomialArena (type_of% @I_eq_eval_poly) where
  actual := polynomialActual
  bridge := Iff.rfl
  variation := ⟨I_eq_eval_poly, polynomialOne, polynomialRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨polynomialOne, ?_, rfl, polynomialRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := polynomialDependence

def polynomialAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@I_eq_eval_poly) (Realization polynomialSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.polynomialUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.polynomialSource
  realizationSource := none
  generated := false
  arena := .source ⟨polynomialArena⟩
  objectArena := .source ⟨polynomialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source polynomialArena ⟨polynomialSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize polynomialSignature (fun _ p j => ((sigmaPoly p.1 p.2).map Complex.ofRealHom).eval (zeta p.1 ^ j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Cyclotomic
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def propagationSource : Registration propagationArena (type_of% @rational_const_on_orderClass) where
  actual := propagationActual
  bridge := Iff.rfl
  variation := ⟨rational_const_on_orderClass, propagationBadRight, propagationBadRightRejected⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨propagationBadLeft, ?_, rfl, propagationBadLeftRejected⟩
        intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · refine ⟨propagationBadRight, ?_, rfl, propagationBadRightRejected⟩
        intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := propagationDependence

def propagationAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rational_const_on_orderClass) (Realization propagationSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.propagationUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.propagationSource
  realizationSource := none
  generated := false
  arena := .source ⟨propagationArena⟩
  objectArena := .source ⟨propagationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source propagationArena ⟨propagationSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize propagationSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Cyclotomic
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def witnessSource : Registration witnessArena (type_of% @rational_witness) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨rational_witness, valueZero, witnessRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨valueZero, ?_, rfl, witnessRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def witnessAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rational_witness) (Realization valueSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.witnessUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Cyclotomic.witnessSource
  realizationSource := none
  generated := false
  arena := .source ⟨witnessArena⟩
  objectArena := .source ⟨witnessArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source witnessArena ⟨witnessSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Cyclotomic
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.InterlaceFan.Cyclotomic
