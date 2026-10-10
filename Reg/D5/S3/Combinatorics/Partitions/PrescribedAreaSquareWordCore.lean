import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
open _root_.D5.S3.Combinatorics.Partitions.PaddedWordPartition
open _root_.D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
open _root_.D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore

abbrev rowSignature : Signature where
  Params := ℕ
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature :=
  realize.{0,0,0,0,0} rowSignature (fun _ n w => rows (literalPowerWord n w)) (fun e => nomatch e)

def rowRejected : Realization rowSignature :=
  realize.{0,0,0,0,0} rowSignature (fun _ _ _ => []) (fun e => nomatch e)

def rowArena : Arena where
  signature := rowSignature
  Law r := ∀ (n : ℕ) (w : List Bool), r.readout () n w =
    (rows w).flatMap (fun x => List.replicate n (n*x))

private theorem rowBad : ¬ rowArena.Law rowRejected := by
  intro h
  have hb := h 1 [true,false]
  norm_num [rowRejected, realize, rows] at hb
  cases hb

def rowRegistration : Registration rowArena (type_of% @rows_literalPowerWord) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨rows_literalPowerWord, rowRejected, rowBad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨rowRejected, ?_, rfl, rowBad⟩
      intro j hj
      change Unit at j
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence rowSignature rowActual
    intro i
    refine ⟨1, [], [true,false], ?_⟩
    norm_num [rowActual, realize, literalPowerWord, rows]
    intro he
    cases he

abbrev geometrySignature : Signature where
  Params := ℕ
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Five
  Anchor := Empty
  finiteAnchor := inferInstance

def geometryActual : Realization geometrySignature :=
  realize.{0,0,0,0,0} geometrySignature (fun _ n w => G (literalPowerWord n w)) (fun e => nomatch e)

def geometryRejected : Realization geometrySignature :=
  realize.{0,0,0,0,0} geometrySignature (fun _ _ _ => zeroFive) (fun e => nomatch e)

def geometryArena : Arena where
  signature := geometrySignature
  Law r := ∀ (n : ℕ) (w : List Bool), r.readout () n w =
    ⟨n*(G w).u,n*(G w).v,(n : ℝ)^2*(G w).d,
      (n : ℝ)^3*(G w).e,(n : ℝ)^3*(G w).f⟩

private theorem geometryBad : ¬ geometryArena.Law geometryRejected := by
  intro h
  have hb := congrArg Five.u (h 1 [true])
  norm_num [geometryRejected, realize, zeroFive, all_word_direct] at hb

def geometryRegistration : Registration geometryArena (type_of% @G_literalPowerWord) where
  actual := geometryActual
  bridge := Iff.rfl
  variation := ⟨G_literalPowerWord, geometryRejected, geometryBad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨geometryRejected, ?_, rfl, geometryBad⟩
      intro j hj
      change Unit at j
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence geometrySignature geometryActual
    intro i
    refine ⟨1, [], [true], ?_⟩
    intro he
    have hu := congrArg Five.u he
    norm_num [geometryActual, realize, literalPowerWord, all_word_direct] at hu

abbrev coreSignature : Signature where
  Params := ℕ
  State J := CoreIndex J
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Five
  Anchor := Empty
  finiteAnchor := inferInstance

def coreActual : Realization coreSignature :=
  realize.{0,0,0,0,0} coreSignature (fun _ J x => G (V J x)) (fun e => nomatch e)

def coreRejected : Realization coreSignature :=
  realize.{0,0,0,0,0} coreSignature (fun _ _ _ => zeroFive) (fun e => nomatch e)

def squareArena : Arena where
  signature := coreSignature
  Law r := ∀ (J h t : ℕ)
    (_hh : 0 < h) (_ha : 8 * coreSide J ≤ h)
    (_ht0 : h ^ 2 ≤ 8 * t) (_ht1 : 8 * t ≤ 7 * h ^ 2) ,
    (∀ x : CoreIndex J,
      r.readout () J x =
        ⟨coreSide J, coreSide J, 0,
          -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val,
          -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val⟩ ∧
      (V J x).count true = coreSide J ∧ (V J x).count false = coreSide J ∧
      scatteredTrueFalseCount (V J x) = (coreSide J) ^ 2 / 2) ∧
    (0 < h-coreSide J ∧ Even (coreSide J) ∧
      coreSide J * h ≤ t + (coreSide J) ^ 2 / 2 ∧
      suffixArea J h t + coreSide J * h = t + (coreSide J) ^ 2 / 2 ∧
      suffixArea J h t ≤ (h-coreSide J) ^ 2) ∧
    (∀ x : CoreIndex J,
      W J h t x ∈ wordFiber h h t ∧
      (W J h t x).count true = h ∧ (W J h t x).count false = h ∧
      scatteredTrueFalseCount (W J h t x) = t ∧
      (rows (W J h t x)).length = h ∧ (rows (W J h t x)).SortedGE ∧
      (∀ r ∈ rows (W J h t x), r ≤ h) ∧ (rows (W J h t x)).sum = t ∧
      rows (W J h t x) =
        (rows (fixedZ (h-coreSide J) (suffixArea J h t))).map
          (fun r => r + coreSide J) ++ rows (V J x) ∧
      G (W J h t x) =
        ⟨h, h, 2 * (t : ℝ)-(h : ℝ) ^ 2,
          -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val+
            (G (fixedZ (h-coreSide J) (suffixArea J h t))).e+
            3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d,
          -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val+
            (G (fixedZ (h-coreSide J) (suffixArea J h t))).f+
            3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d⟩) ∧
    Function.Injective (W J h t) ∧
    Function.Injective (fun x : CoreIndex J => ((G (W J h t x)).e, (G (W J h t x)).f)) ∧
    Function.Injective (fun x : CoreIndex J =>
      (squareRows (rows (W J h t x)), oddRows (rows (W J h t x)))) ∧
    (Set.range (W J h t)).ncard = (q J) ^ 6 ∧
    (Set.range (fun x : CoreIndex J => ((G (W J h t x)).e, (G (W J h t x)).f))).ncard =
      (q J) ^ 6 ∧
    (Set.range (fun x : CoreIndex J =>
      (squareRows (rows (W J h t x)), oddRows (rows (W J h t x))))).ncard = (q J) ^ 6 ∧
    (q J) ^ 6 ≤ capacity h h t

private theorem squareBad : ¬ squareArena.Law coreRejected := by
  intro h
  have hb := ((h 1 560 156800 (by norm_num)
    (by norm_num [coreSide,_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]) (by norm_num) (by norm_num)).1
      (⟨⟨0,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩,⟨0,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩⟩ : CoreIndex 1)).1
  have hu := congrArg Five.u hb
  norm_num [coreRejected,realize,zeroFive,coreSide,_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q] at hu

def squareRegistration : Registration squareArena (type_of% @square_family) where
  actual := coreActual
  bridge := Iff.rfl
  variation := ⟨square_family, coreRejected, squareBad⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      refine ⟨coreRejected, ?_, rfl, squareBad⟩
      intro j hj
      change Unit at j
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    change ObservationalDependence coreSignature coreActual
    intro i
    let x : CoreIndex 1 := ⟨⟨0,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩,⟨0,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩⟩
    let y : CoreIndex 1 := ⟨⟨1,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩,⟨0,by norm_num [_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]⟩⟩
    refine ⟨1, x, y, ?_⟩
    intro he
    have hx := ((square_family 1 560 156800 (by norm_num)
      (by norm_num [coreSide,_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]) (by norm_num) (by norm_num)).1 x).1
    have hy := ((square_family 1 560 156800 (by norm_num)
      (by norm_num [coreSide,_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.q]) (by norm_num) (by norm_num)).1 y).1
    change G (V 1 x) = G (V 1 y) at he
    have hb := congrArg Five.e he
    rw [hx,hy] at hb
    norm_num [x,y] at hb
    linarith

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.rows_literalPowerWord)
      (type_of% (realize.{0,0,0,0,0} rowSignature (fun _ n w => rows (literalPowerWord n w)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.rows_literalPowerWord.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.rowRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rowArena⟩,
  objectArena := .source ⟨rowArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rowArena ⟨rowRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} rowSignature (fun _ n w => rows (literalPowerWord n w)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_2 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.G_literalPowerWord)
      (type_of% (realize.{0,0,0,0,0} geometrySignature (fun _ n w => G (literalPowerWord n w)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.G_literalPowerWord.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.geometryRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨geometryArena⟩,
  objectArena := .source ⟨geometryArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source geometryArena ⟨geometryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} geometrySignature (fun _ n w => G (literalPowerWord n w)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_3 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.square_family)
      (type_of% (realize.{0,0,0,0,0} coreSignature (fun _ J x => G (V J x)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.square_family.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore.squareRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨squareArena⟩,
  objectArena := .source ⟨squareArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source squareArena ⟨squareRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} coreSignature (fun _ J x => G (V J x)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms rowRegistration
#print axioms geometryRegistration
#print axioms squareRegistration

end Reg.D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
