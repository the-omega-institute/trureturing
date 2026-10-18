import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.RationalKummer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Mordell.RationalKummer

open _root_.D5.S3.Factorization.Mordell.RationalKummer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev ellipticSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := WeierstrassCurve ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def ellipticActual : Realization ellipticSignature :=
  realize ellipticSignature (fun _ _ D => curve D) (fun e => nomatch e)

def ellipticRejected : Realization ellipticSignature :=
  realize ellipticSignature (fun _ _ _ => curve 0) (fun e => nomatch e)

abbrev ellipticArena : Arena where
  signature := ellipticSignature
  Law R := ∀ D : ℚ, D ≠ 0 → (R.readout () () D).IsElliptic

private theorem singularZero : ¬ (curve 0).IsElliptic := by
  intro h
  have hd := h.isUnit
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hd

private theorem rejectedLaw : ¬ ellipticArena.Law ellipticRejected := by
  intro h
  exact singularZero (h 1 (by norm_num))

def ellipticRegistration : Registration ellipticArena
    (∀ (D : ℚ), D ≠ 0 → (curve D).IsElliptic) where
  actual := ellipticActual
  bridge := Iff.rfl
  variation := ⟨curve_is_elliptic, ellipticRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨ellipticRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    intro heq
    have h := congrArg WeierstrassCurve.a₂ heq
    norm_num [ellipticActual, realize, curve] at h

noncomputable def curve_is_elliptic_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.curve_is_elliptic)
      (type_of% (realize ellipticSignature (fun _ _ D => curve D) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.curve_is_elliptic.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.ellipticRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨ellipticArena⟩,
  objectArena := .source ⟨ellipticArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source ellipticArena ⟨ellipticRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize ellipticSignature (fun _ _ D => curve D) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}

#print axioms ellipticRegistration
#print axioms curve_is_elliptic_registration



private theorem ordinaryValues (hP : (curve 4).Nonsingular (-15) 75) :
    descentRep 4 0 (WeierstrassCurve.Affine.Point.some (-15) 75 hP) = -15 ∧
    descentRep 4 1 (WeierstrassCurve.Affine.Point.some (-15) 75 hP) = 5 ∧
    descentRep 4 2 (WeierstrassCurve.Affine.Point.some (-15) 75 hP) = -75 := by
  have r0 : root (4 : ℚ) 0 = 0 := rfl
  have r1 : root (4 : ℚ) 1 = -20 := by change (-5 : ℚ) * 4 = -20; norm_num
  have r2 : root (4 : ℚ) 2 = 60 := by change (15 : ℚ) * 4 = 60; norm_num
  simp only [descentRep, r0, r1, r2]
  norm_num

abbrev descentRep_product_squareSignature : Signature where
  Params := ℚ
  State D := (curve D).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def descentRep_product_squareActual : Realization descentRep_product_squareSignature :=
  realize descentRep_product_squareSignature (fun _ D P => descentRep D 0 P * descentRep D 1 P * descentRep D 2 P) (fun e => nomatch e)

def descentRep_product_squareRejected : Realization descentRep_product_squareSignature :=
  realize descentRep_product_squareSignature (fun _ D _ => -1) (fun e => nomatch e)

abbrev descentRep_product_squareArena : Arena where
  signature := descentRep_product_squareSignature
  Law R := ∀ (D : ℚ), D ≠ 0 → ∀ P : (curve D).Point, IsSquare (R.readout () D P)

private theorem descentRep_product_squarePositive : descentRep_product_squareArena.Law descentRep_product_squareActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_product_square

private theorem descentRep_product_squareNegative : ¬ descentRep_product_squareArena.Law descentRep_product_squareRejected := by
  intro h
  obtain ⟨r, hr⟩ := h 1 (by norm_num) 0
  change (-1 : ℚ) = r * r at hr
  nlinarith [sq_nonneg r]

private theorem descentRep_product_squareDependence :
    ObservationalDependence descentRep_product_squareSignature descentRep_product_squareActual := by
  intro i
  have hP : (curve 4).Nonsingular (-15) 75 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve]
  obtain ⟨h0,h1,h2⟩ := ordinaryValues hP
  refine ⟨4, 0, WeierstrassCurve.Affine.Point.some (-15) 75 hP, ?_⟩
  dsimp only [descentRep_product_squareActual, realize]
  rw [h0,h1,h2]
  norm_num [← WeierstrassCurve.Affine.Point.zero_def, descentRep]

def descentRep_product_squareRegistration : Registration descentRep_product_squareArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_product_square)) where
  actual := descentRep_product_squareActual
  bridge := Iff.rfl
  variation := ⟨descentRep_product_squarePositive, descentRep_product_squareRejected, descentRep_product_squareNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨descentRep_product_squareRejected, ?_, rfl, descentRep_product_squareNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := descentRep_product_squareDependence

noncomputable def descentRep_product_square_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_product_square)
      (type_of% (realize descentRep_product_squareSignature (fun _ D P => descentRep D 0 P * descentRep D 1 P * descentRep D 2 P) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.descentRep_product_square.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.descentRep_product_squareRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨descentRep_product_squareArena⟩,
  objectArena := .source ⟨descentRep_product_squareArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source descentRep_product_squareArena ⟨descentRep_product_squareRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize descentRep_product_squareSignature (fun _ D P => descentRep D 0 P * descentRep D 1 P * descentRep D 2 P) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev descentRep_add_squareSignature : Signature where
  Params := Σ D : ℚ, Σ _ : Fin 3, (curve D).Point
  State p := (curve p.1).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def descentRep_add_squareActual : Realization descentRep_add_squareSignature :=
  realize descentRep_add_squareSignature (fun _ p Q => descentRep p.1 p.2.1 p.2.2 * descentRep p.1 p.2.1 Q * descentRep p.1 p.2.1 (p.2.2+Q)) (fun e => nomatch e)

def descentRep_add_squareRejected : Realization descentRep_add_squareSignature :=
  realize descentRep_add_squareSignature (fun _ p _ => -1) (fun e => nomatch e)

abbrev descentRep_add_squareArena : Arena where
  signature := descentRep_add_squareSignature
  Law R := ∀ (D : ℚ), D ≠ 0 → ∀ (i : Fin 3) (P Q : (curve D).Point), IsSquare (R.readout () ⟨D,i,P⟩ Q)

private theorem descentRep_add_squarePositive : descentRep_add_squareArena.Law descentRep_add_squareActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_add_square

private theorem descentRep_add_squareNegative : ¬ descentRep_add_squareArena.Law descentRep_add_squareRejected := by
  intro h
  obtain ⟨r, hr⟩ := h 1 (by norm_num) 0 0 0
  change (-1 : ℚ) = r * r at hr
  nlinarith [sq_nonneg r]

private theorem descentRep_add_squareDependence :
    ObservationalDependence descentRep_add_squareSignature descentRep_add_squareActual := by
  intro i
  have hP : (curve 4).Nonsingular (-15) 75 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve]
  have h0 := (ordinaryValues hP).1
  refine ⟨⟨4, 0, 0⟩, 0, WeierstrassCurve.Affine.Point.some (-15) 75 hP, ?_⟩
  dsimp only [descentRep_add_squareActual, realize]
  rw [zero_add,zero_add,h0]
  norm_num [← WeierstrassCurve.Affine.Point.zero_def, descentRep]

def descentRep_add_squareRegistration : Registration descentRep_add_squareArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_add_square)) where
  actual := descentRep_add_squareActual
  bridge := Iff.rfl
  variation := ⟨descentRep_add_squarePositive, descentRep_add_squareRejected, descentRep_add_squareNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨descentRep_add_squareRejected, ?_, rfl, descentRep_add_squareNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := descentRep_add_squareDependence

noncomputable def descentRep_add_square_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.descentRep_add_square)
      (type_of% (realize descentRep_add_squareSignature (fun _ p Q => descentRep p.1 p.2.1 p.2.2 * descentRep p.1 p.2.1 Q * descentRep p.1 p.2.1 (p.2.2+Q)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.descentRep_add_square.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.descentRep_add_squareRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨descentRep_add_squareArena⟩,
  objectArena := .source ⟨descentRep_add_squareArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source descentRep_add_squareArena ⟨descentRep_add_squareRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize descentRep_add_squareSignature (fun _ p Q => descentRep p.1 p.2.1 p.2.2 * descentRep p.1 p.2.1 Q * descentRep p.1 p.2.1 (p.2.2+Q)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[0, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev explicit_halfSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def explicit_halfActual : Realization explicit_halfSignature :=
  realize explicit_halfSignature (fun _ _ c => c ^ 2) (fun e => nomatch e)

def explicit_halfRejected : Realization explicit_halfSignature :=
  realize explicit_halfSignature (fun _ _ _ => 4) (fun e => nomatch e)

abbrev explicit_halfArena : Arena where
  signature := explicit_halfSignature
  Law R := ∀ (D x y a b c : ℚ), D ≠ 0 → a ^ 2 = x → b ^ 2 = x + 5 * D →
      R.readout () () c = x - 15 * D → a * b * c = -y →
      ∀ hP : (curve D).Nonsingular x y,
      ∃ hQ : (curve D).Nonsingular (x+a*b+a*c+b*c) (-((a+b)*(a+c)*(b+c))),
        (WeierstrassCurve.Affine.Point.some _ _ hQ : (curve D).Point) +
          WeierstrassCurve.Affine.Point.some _ _ hQ = WeierstrassCurve.Affine.Point.some x y hP

private theorem explicit_halfPositive : explicit_halfArena.Law explicit_halfActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.explicit_half

private theorem explicit_halfNegative : ¬ explicit_halfArena.Law explicit_halfRejected := by
  intro h
  have hP : (curve (-1/5)).Nonsingular 1 0 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve]
  obtain ⟨hQ, hEq⟩ := h (-1/5) 1 0 1 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [explicit_halfRejected, realize]) (by norm_num) hP
  have hz : (WeierstrassCurve.Affine.Point.some _ _ hQ : (curve (-1/5)).Point) +
      WeierstrassCurve.Affine.Point.some _ _ hQ = 0 := by
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    norm_num [WeierstrassCurve.Affine.negY, curve]
  rw [hz] at hEq
  exact (WeierstrassCurve.Affine.Point.some_ne_zero hP) hEq.symm

private theorem explicit_halfDependence : ObservationalDependence explicit_halfSignature explicit_halfActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℚ)^2 ≠ 1^2
  norm_num

def explicit_halfRegistration : Registration explicit_halfArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.explicit_half)) where
  actual := explicit_halfActual
  bridge := Iff.rfl
  variation := ⟨explicit_halfPositive, explicit_halfRejected, explicit_halfNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨explicit_halfRejected, ?_, rfl, explicit_halfNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := explicit_halfDependence

noncomputable def explicit_half_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.explicit_half)
      (type_of% (realize explicit_halfSignature (fun _ _ c => c ^ 2) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.explicit_half.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.explicit_halfRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨explicit_halfArena⟩,
  objectArena := .source ⟨explicit_halfArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source explicit_halfArena ⟨explicit_halfRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize explicit_halfSignature (fun _ _ c => c ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev block_translationSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def block_translationActual : Realization block_translationSignature :=
  realize block_translationSignature (fun _ _ L => L ^ 2 + 4) (fun e => nomatch e)

def block_translationRejected : Realization block_translationSignature :=
  realize block_translationSignature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev block_translationArena : Arena where
  signature := block_translationSignature
  Law R := ∀ (D C L F : ℚ), C ≠ 0 → L ^ 2 + 3 = D * C ^ 2 →
      R.readout () () L = 5 * F ^ 2 →
      ∃ (hR : (curve D).Nonsingular (5*D*(L^2+3)) (25*D^2*L*C*F))
        (hT : (curve D).Nonsingular 0 0)
        (hS : (curve D).Nonsingular (-15/C^2) (75*L*F/C^3)),
        WeierstrassCurve.Affine.Point.some _ _ hR +
          WeierstrassCurve.Affine.Point.some _ _ hT = WeierstrassCurve.Affine.Point.some _ _ hS

private theorem block_translationPositive : block_translationArena.Law block_translationActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.block_translation

private theorem block_translationNegative : ¬ block_translationArena.Law block_translationRejected := by
  intro h
  obtain ⟨hR, _, _, _⟩ := h 7 1 2 1 (by norm_num) (by norm_num)
    (by norm_num [block_translationRejected, realize])
  have he := hR.1
  norm_num [WeierstrassCurve.Affine.equation_iff, curve] at he

private theorem block_translationDependence : ObservationalDependence block_translationSignature block_translationActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℚ)^2+4 ≠ 1^2+4
  norm_num

def block_translationRegistration : Registration block_translationArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.block_translation)) where
  actual := block_translationActual
  bridge := Iff.rfl
  variation := ⟨block_translationPositive, block_translationRejected, block_translationNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨block_translationRejected, ?_, rfl, block_translationNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := block_translationDependence

noncomputable def block_translation_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.block_translation)
      (type_of% (realize block_translationSignature (fun _ _ L => L ^ 2 + 4) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.block_translation.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.block_translationRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨block_translationArena⟩,
  objectArena := .source ⟨block_translationArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source block_translationArena ⟨block_translationRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize block_translationSignature (fun _ _ L => L ^ 2 + 4) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev affine_double_iffSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def affine_double_iffActual : Realization affine_double_iffSignature :=
  realize affine_double_iffSignature (fun _ _ x => x) (fun e => nomatch e)

def affine_double_iffRejected : Realization affine_double_iffSignature :=
  realize affine_double_iffSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev affine_double_iffArena : Arena where
  signature := affine_double_iffSignature
  Law R := ∀ (D x y : ℚ), D ≠ 0 → ∀ hP : (curve D).Nonsingular x y,
      (∃ Q : (curve D).Point, Q+Q = WeierstrassCurve.Affine.Point.some x y hP) ↔
      IsSquare (R.readout () () x) ∧ IsSquare (x+5*D) ∧ IsSquare (x-15*D)

private theorem affine_double_iffPositive : affine_double_iffArena.Law affine_double_iffActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff

private theorem affine_double_iffNegative : ¬ affine_double_iffArena.Law affine_double_iffRejected := by
  intro h
  have hP : (curve (-1/5)).Nonsingular 1 0 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve]
  have hd := (_root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff
    (-1/5) 1 0 (by norm_num) hP).mpr
      ⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩, ⟨2, by norm_num⟩⟩
  obtain ⟨r, hr⟩ := ((h (-1/5) 1 0 (by norm_num) hP).mp hd).1
  change (-1 : ℚ) = r * r at hr
  nlinarith [sq_nonneg r]

private theorem affine_double_iffDependence : ObservationalDependence affine_double_iffSignature affine_double_iffActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [affine_double_iffActual, realize]⟩

def affine_double_iffRegistration : Registration affine_double_iffArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff)) where
  actual := affine_double_iffActual
  bridge := Iff.rfl
  variation := ⟨affine_double_iffPositive, affine_double_iffRejected, affine_double_iffNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨affine_double_iffRejected, ?_, rfl, affine_double_iffNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := affine_double_iffDependence

noncomputable def affine_double_iff_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff)
      (type_of% (realize affine_double_iffSignature (fun _ _ x => x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iffRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨affine_double_iffArena⟩,
  objectArena := .source ⟨affine_double_iffArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source affine_double_iffArena ⟨affine_double_iffRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize affine_double_iffSignature (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev kummer_zero_iff_doubleSignature : Signature where
  Params := ℚ
  State D := (curve D).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := (curve D).Point
  Anchor := Empty
  finiteAnchor := inferInstance

def kummer_zero_iff_doubleActual : Realization kummer_zero_iff_doubleSignature :=
  realize kummer_zero_iff_doubleSignature (fun _ D P => P) (fun e => nomatch e)

def kummer_zero_iff_doubleRejected : Realization kummer_zero_iff_doubleSignature :=
  realize kummer_zero_iff_doubleSignature (fun _ D _ => 0) (fun e => nomatch e)

abbrev kummer_zero_iff_doubleArena : Arena where
  signature := kummer_zero_iff_doubleSignature
  Law R := ∀ (D : ℚ) (hD : D ≠ 0) (P : (curve D).Point),
      kummer D hD P = 0 ↔ ∃ Q : (curve D).Point, Q+Q = R.readout () D P

private theorem kummer_zero_iff_doublePositive : kummer_zero_iff_doubleArena.Law kummer_zero_iff_doubleActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double

private theorem kummer_zero_iff_doubleNegative : ¬ kummer_zero_iff_doubleArena.Law kummer_zero_iff_doubleRejected := by
  intro h
  have hP : (curve 1).Nonsingular (-5) 0 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff, curve]
  let P : (curve 1).Point := WeierstrassCurve.Affine.Point.some (-5) 0 hP
  have hk : kummer 1 (by norm_num) P = 0 := (h 1 (by norm_num) P).mpr ⟨0, zero_add 0⟩
  obtain ⟨Q,hQ⟩ := (_root_.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double 1 (by norm_num) P).mp hk
  have hs := (_root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff 1 (-5) 0 (by norm_num) hP).mp ⟨Q,hQ⟩
  obtain ⟨r,hr⟩ := hs.1
  nlinarith [sq_nonneg r]

private theorem kummer_zero_iff_doubleDependence : ObservationalDependence kummer_zero_iff_doubleSignature kummer_zero_iff_doubleActual := by
  intro i
  have hP : (curve 1).Nonsingular 0 0 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_zero, curve]
  exact ⟨1, WeierstrassCurve.Affine.Point.some 0 0 hP, 0,
    WeierstrassCurve.Affine.Point.some_ne_zero hP⟩

def kummer_zero_iff_doubleRegistration : Registration kummer_zero_iff_doubleArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double)) where
  actual := kummer_zero_iff_doubleActual
  bridge := Iff.rfl
  variation := ⟨kummer_zero_iff_doublePositive, kummer_zero_iff_doubleRejected, kummer_zero_iff_doubleNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨kummer_zero_iff_doubleRejected, ?_, rfl, kummer_zero_iff_doubleNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := kummer_zero_iff_doubleDependence

noncomputable def kummer_zero_iff_double_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double)
      (type_of% (realize kummer_zero_iff_doubleSignature (fun _ D P => P) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_doubleRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨kummer_zero_iff_doubleArena⟩,
  objectArena := .source ⟨kummer_zero_iff_doubleArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source kummer_zero_iff_doubleArena ⟨kummer_zero_iff_doubleRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize kummer_zero_iff_doubleSignature (fun _ D P => P) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg", "arg", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}


abbrev block_kummer_imagesSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def block_kummer_imagesActual : Realization block_kummer_imagesSignature :=
  realize block_kummer_imagesSignature (fun _ _ n => 2*n+1) (fun e => nomatch e)

def block_kummer_imagesRejected : Realization block_kummer_imagesSignature :=
  realize block_kummer_imagesSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev block_kummer_imagesArena : Arena where
  signature := block_kummer_imagesSignature
  Law R := ∀ (D C L F : ℚ) (hD : D ≠ 0) (hC : C ≠ 0) (hL : L ≠ 0) (hF : F ≠ 0)
      (hblock : L^2+3=D*C^2) (hfib : L^2+4=5*F^2)
      (hR : (curve D).Nonsingular (5*D*(L^2+3)) (25*D^2*L*C*F))
      (hS : (curve D).Nonsingular (-15/C^2) (75*L*F/C^3)),
      kummer D hD (WeierstrassCurve.Affine.Point.some _ _ hR) =
        (classOf 5 (by norm_num), classOf D hD) ∧
      kummer D hD (WeierstrassCurve.Affine.Point.some _ _ hS) =
        (classOf (-15) (by norm_num), classOf 5 (by norm_num)) ∧
      ∀ n : ℤ, kummer D hD ((R.readout () () n) • (WeierstrassCurve.Affine.Point.some _ _ hS)) =
        (classOf (-15) (by norm_num), classOf 5 (by norm_num))

private theorem block_kummer_imagesPositive : block_kummer_imagesArena.Law block_kummer_imagesActual := by
  exact _root_.D5.S3.Factorization.Mordell.RationalKummer.block_kummer_images

private theorem block_kummer_imagesNegative : ¬ block_kummer_imagesArena.Law block_kummer_imagesRejected := by
  intro h
  obtain ⟨hR,hT,hS,htrans⟩ := _root_.D5.S3.Factorization.Mordell.RationalKummer.block_translation
    4 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  have H := h 4 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hR hS
  have hzero : kummer 4 (by norm_num) (WeierstrassCurve.Affine.Point.some _ _ hS) = 0 := by
    rw [H.2.1, ← H.2.2 0]
    simp [block_kummer_imagesRejected, realize]
  obtain ⟨Q,hQ⟩ := (_root_.D5.S3.Factorization.Mordell.RationalKummer.kummer_zero_iff_double 4 (by norm_num) _).mp hzero
  have hs := (_root_.D5.S3.Factorization.Mordell.RationalKummer.affine_double_iff
    4 (-15/1^2) (75*1*1/1^3) (by norm_num) hS).mp ⟨Q,hQ⟩
  obtain ⟨r,hr⟩ := hs.1
  norm_num at hr
  nlinarith [sq_nonneg r]

private theorem block_kummer_imagesDependence : ObservationalDependence block_kummer_imagesSignature block_kummer_imagesActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (2*(0:ℤ)+1) ≠ 2*1+1
  norm_num

def block_kummer_imagesRegistration : Registration block_kummer_imagesArena
    (type_of% (@_root_.D5.S3.Factorization.Mordell.RationalKummer.block_kummer_images)) where
  actual := block_kummer_imagesActual
  bridge := Iff.rfl
  variation := ⟨block_kummer_imagesPositive, block_kummer_imagesRejected, block_kummer_imagesNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨block_kummer_imagesRejected, ?_, rfl, block_kummer_imagesNegative⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := block_kummer_imagesDependence

noncomputable def block_kummer_images_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Factorization.Mordell.RationalKummer.block_kummer_images)
      (type_of% (realize block_kummer_imagesSignature (fun _ _ n => 2*n+1) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.RationalKummer.block_kummer_images.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.RationalKummer.block_kummer_imagesRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨block_kummer_imagesArena⟩,
  objectArena := .source ⟨block_kummer_imagesArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source block_kummer_imagesArena ⟨block_kummer_imagesRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize block_kummer_imagesSignature (fun _ _ n => 2*n+1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.RationalKummer, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "arg", "fn", "arg"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]
}

end Reg.D5.S3.Factorization.Mordell.RationalKummer
