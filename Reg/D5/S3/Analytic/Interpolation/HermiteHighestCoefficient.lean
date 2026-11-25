import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

/-!
Source-bound registrations for the inverse, its sharp scalar constant, and the
matrix estimate. At coalesced nodes the zero readout violates each of the
corresponding laws, while the actual readouts distinguish different states.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient

open _root_.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
open _root_.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
open _root_.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open LeanInformationAudit Set
open scoped ContDiff Matrix.Norms.L2Operator

local notation "Nodes" => Fin 3 → ℝ
local notation "Data" => Fin 2 → ℝ
local notation "Mat₂" => Matrix (Fin 2) (Fin 2) ℝ
local notation "Blocks₂" => Fin 2 → Mat₂

private def nodes : Nodes := fun _ => 1

private theorem nodes_pos : ∀ i, 0 < nodes i := fun _ => zero_lt_one

private theorem nodes_le : ∀ i, nodes i ≤ 1 := fun _ => le_rfl

private theorem nodes_mem : ∀ i, nodes i ∈ Icc (1 / 2 : ℝ) 1 :=
  fun _ => ⟨by norm_num [nodes], le_rfl⟩

private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num

private def zeroReadout {P X Y : Type} [Zero Y] :
    Realization (signature P (fun _ => X) (fun _ => Y)) :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

abbrev scalarSignature : Signature := signature Nodes (fun _ => Data) (fun _ => Data)

def scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ a v => weightedNewtonTail 3 a v) (fun e => nomatch e)

private theorem scalarDependence : ObservationalDependence scalarSignature scalarActual := by
  intro i
  refine ⟨nodes, 0, 1, ?_⟩
  change weightedNewtonTail 3 nodes (0 : Data) ≠ weightedNewtonTail 3 nodes (1 : Data)
  intro he
  have h := (weightedNewtonTail_two_inverse nodes nodes_pos).1.injective he
  have h0 := congrFun h 0
  norm_num at h0

def inverseArena : Arena where
  signature := scalarSignature
  Law R := ∀ (a : Nodes), (∀ i, 0 < a i) →
    let sample := fun v => R.readout () a v
    Function.LeftInverse (inverseTwo a) sample ∧ Function.RightInverse (inverseTwo a) sample

private theorem inverseRejected : ¬ inverseArena.Law zeroReadout := by
  intro h
  have h0 : inverseTwo nodes 0 = (0 : Data) := (h nodes nodes_pos).1 0
  have h1 : inverseTwo nodes 0 = (1 : Data) := (h nodes nodes_pos).1 1
  have he := congrFun (h0.symm.trans h1) 0
  norm_num at he

def inverseFamily : Registration inverseArena (type_of% (@weightedNewtonTail_two_inverse)) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨weightedNewtonTail_two_inverse, zeroReadout, inverseRejected⟩
  sensitivity := sensitivity inverseArena.Law scalarActual zeroReadout inverseRejected
  dependence := scalarDependence

def worstCaseArena : Arena where
  signature := scalarSignature
  Law R := ∀ (a : Nodes), (∀ i, 0 < a i) → ∀ (ε : ℝ), 0 ≤ ε →
    IsGreatest {r : ℝ | ∃ v : Data, ‖R.readout () a v‖ ≤ ε ∧ r = |v 1|}
      (ε * highestRowSum a)

private theorem worstCaseRejected : ¬ worstCaseArena.Law zeroReadout := by
  intro h
  have h1 := (h nodes nodes_pos 0 le_rfl).2 (show (1 : ℝ) ∈
      {r : ℝ | ∃ v : Data, ‖(0 : Data)‖ ≤ 0 ∧ r = |v 1|} from
        ⟨1, by simp, by norm_num⟩)
  norm_num at h1

def worstCaseFamily : Registration worstCaseArena (type_of% (@highestCoefficient_worst_case)) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨highestCoefficient_worst_case, zeroReadout, worstCaseRejected⟩
  sensitivity := sensitivity worstCaseArena.Law scalarActual zeroReadout worstCaseRejected
  dependence := scalarDependence

abbrev rowSignature : Signature := signature Unit (fun _ => Nodes) (fun _ => ℝ)

def rowActual : Realization rowSignature :=
  realize rowSignature (fun _ _ a => highestRowSum a) (fun e => nomatch e)

def rowArena : Arena where
  signature := rowSignature
  Law R := ∀ (a : Nodes), (∀ i, 0 < a i) → (∀ i, a i ≤ 1) →
    let row := R.readout () () a
    1 ≤ row ∧ (row = 1 ↔ ∀ i, a i = 1)

private theorem rowRejected : ¬ rowArena.Law zeroReadout := by
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (h nodes nodes_pos nodes_le).1

private theorem rowDependence : ObservationalDependence rowSignature rowActual := by
  intro i
  let b : Nodes := fun _ => 1 / 2
  refine ⟨(), nodes, b, ?_⟩
  change highestRowSum nodes ≠ highestRowSum b
  intro he
  have hnodes := (highestRowSum_optimal nodes nodes_pos nodes_le).2.mpr (fun _ => rfl)
  have hb := (highestRowSum_optimal b (fun _ => by norm_num [b])
    (fun _ => by norm_num [b])).2.mp (he.symm.trans hnodes) 0
  norm_num [b] at hb

def rowFamily : Registration rowArena (type_of% (@highestRowSum_optimal)) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨highestRowSum_optimal, zeroReadout, rowRejected⟩
  sensitivity := sensitivity rowArena.Law rowActual zeroReadout rowRejected
  dependence := rowDependence

abbrev MatrixParams := Σ _lo : ℝ, Σ _hi : ℝ, Nodes
abbrev matrixSignature : Signature :=
  signature MatrixParams (fun _ => ℝ → Mat₂) (fun _ => Blocks₂)

def matrixActual : Realization matrixSignature :=
  realize matrixSignature (fun _ p F => matrixHermiteTail p.1 p.2.1 p.2.2 F)
    (fun e => nomatch e)

def errorArena : Arena where
  signature := matrixSignature
  Law R := ∀ {lo hi : ℝ}, lo < hi → ∀ {a : Nodes},
    (∀ i, a i ∈ Icc lo hi) → (∀ i, 0 < a i) →
    ∀ (v : Blocks₂) (K : Mat₂) (F E : ℝ → Mat₂),
      EqOn F (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1 + E x) (Icc lo hi) →
      (∀ i j, ContDiffOn ℝ 2 (fun x => E x i j) (Icc lo hi)) → ∀ (B : Data),
      (∀ k x, x ∈ Icc lo hi →
        let D : Mat₂ := fun i j =>
          iteratedDerivWithin (k.val + 1) (fun t => E t i j) (Icc lo hi) x
        ‖D‖ ≤ B k) → ∀ (d : Blocks₂) (ε : ℝ), ‖d - R.readout () ⟨lo, hi, a⟩ F‖ ≤ ε →
        ‖recoverHighest a d - v 1‖ ≤
          ε * highestRowSum a + (|highestWeight0 a| * B 0 + |highestWeight1 a| * (B 1 / 2))

def attainmentArena : Arena where
  signature := matrixSignature
  Law R := ∀ {lo hi : ℝ}, lo < hi → ∀ {a : Nodes},
    (∀ i, a i ∈ Icc lo hi) → (∀ i, 0 < a i) → ∀ (K : Mat₂) (ε : ℝ), 0 ≤ ε →
    let sample := fun F => R.readout () ⟨lo, hi, a⟩ F
    ∃ P : Mat₂, P.rank = 1 ∧ ‖P‖ = 1 ∧
      ∃ v : Blocks₂,
        (let Y := sample (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1)
         Y = (fun k => (![-ε, ε] : Data) k • P) ∧ ‖(0 : Blocks₂) - Y‖ = ε) ∧
        v 1 = (ε * highestRowSum a) • P ∧
        ‖recoverHighest a (0 : Blocks₂) - v 1‖ = ε * highestRowSum a

private theorem matrixDependence : ObservationalDependence matrixSignature matrixActual := by
  intro i
  obtain ⟨P₀, _, _, v₀, ⟨_, h₀⟩, _, _⟩ :=
    matrixHermiteTail_highest_attained half_lt_one nodes_mem nodes_pos 0 0 le_rfl
  obtain ⟨P₁, _, _, v₁, ⟨_, h₁⟩, _, _⟩ :=
    matrixHermiteTail_highest_attained half_lt_one nodes_mem nodes_pos 0 1 zero_le_one
  refine ⟨⟨1 / 2, 1, nodes⟩, (fun x => 0 + x ^ 3 • v₀ 0 + x ^ 4 • v₀ 1),
    (fun x => 0 + x ^ 3 • v₁ 0 + x ^ 4 • v₁ 1), ?_⟩
  intro he
  change matrixHermiteTail (1 / 2) 1 nodes (fun x => 0 + x ^ 3 • v₀ 0 + x ^ 4 • v₀ 1) =
    matrixHermiteTail (1 / 2) 1 nodes (fun x => 0 + x ^ 3 • v₁ 0 + x ^ 4 • v₁ 1) at he
  have hnorm := congrArg (fun Y : Blocks₂ => ‖(0 : Blocks₂) - Y‖) he
  exact zero_ne_one (h₀.symm.trans (hnorm.trans h₁))

private theorem errorRejected : ¬ errorArena.Law zeroReadout := by
  intro h
  obtain ⟨P, _, _, v, _, _, hv⟩ :=
    matrixHermiteTail_highest_attained half_lt_one nodes_mem nodes_pos 0 1 zero_le_one
  let F (x : ℝ) : Mat₂ := 0 + x ^ 3 • v 0 + x ^ 4 • v 1
  have hE : ∀ i j : Fin 2, ContDiffOn ℝ 2 (fun _ : ℝ => (0 : Mat₂) i j)
      (Icc (1 / 2 : ℝ) 1) := fun _ _ => contDiffOn_const
  have hB : ∀ (k : Fin 2) (x : ℝ), x ∈ Icc (1 / 2 : ℝ) 1 →
      let D : Mat₂ := fun i j =>
        iteratedDerivWithin (k.val + 1) (fun _ : ℝ => (0 : Mat₂) i j) (Icc (1 / 2 : ℝ) 1) x
      ‖D‖ ≤ (0 : Data) k := by
    intro k x hx
    have hD : (fun i j => iteratedDerivWithin (k.val + 1)
        (fun _ : ℝ => (0 : Mat₂) i j) (Icc (1 / 2 : ℝ) 1) x) = (0 : Mat₂) := by
      funext i j
      simp [iteratedDerivWithin_const]
    change ‖(Matrix.of fun i j => iteratedDerivWithin (k.val + 1)
        (fun _ : ℝ => (0 : Mat₂) i j) (Icc (1 / 2 : ℝ) 1) x)‖ ≤ (0 : Data) k
    have he : (Matrix.of fun i j => iteratedDerivWithin (k.val + 1)
        (fun _ : ℝ => (0 : Mat₂) i j) (Icc (1 / 2 : ℝ) 1) x) = 0 := hD
    rw [he, norm_zero, Pi.zero_apply]
  let R : Realization matrixSignature := zeroReadout
  have hz : ‖(0 : Blocks₂) - R.readout () ⟨1 / 2, 1, nodes⟩ F‖ ≤ 0 := by
    change ‖(0 : Blocks₂) - 0‖ ≤ 0
    simp
  have he := h half_lt_one nodes_mem nodes_pos v 0 F (fun _ => 0)
    (fun x _ => (add_zero (F x)).symm) hE 0 hB 0 0 hz
  rw [hv] at he
  have hl := (highestRowSum_optimal nodes nodes_pos nodes_le).1
  simp only [Pi.zero_apply, zero_mul, zero_div, mul_zero, add_zero, one_mul] at he
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (hl.trans he)

private theorem attainmentRejected : ¬ attainmentArena.Law zeroReadout := by
  intro h
  obtain ⟨P, _, _, v, ⟨_, he⟩, _, _⟩ :=
    h half_lt_one nodes_mem nodes_pos 0 1 zero_le_one
  change ‖(0 : Blocks₂) - 0‖ = 1 at he
  norm_num at he

def errorFamily : Registration errorArena (type_of% (@matrixHermiteTail_highest_error)) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@matrixHermiteTail_highest_error, zeroReadout, errorRejected⟩
  sensitivity := sensitivity errorArena.Law matrixActual zeroReadout errorRejected
  dependence := matrixDependence

def attainmentFamily :
    Registration attainmentArena (type_of% (@matrixHermiteTail_highest_attained)) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@matrixHermiteTail_highest_attained, zeroReadout, attainmentRejected⟩
  sensitivity := sensitivity attainmentArena.Law matrixActual zeroReadout attainmentRejected
  dependence := matrixDependence

def inverseRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weightedNewtonTail_two_inverse) (Realization scalarSignature) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.weightedNewtonTail_two_inverse.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.inverseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena⟩
  objectArena := .source ⟨inverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverseFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a v => weightedNewtonTail 3 a v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "value", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def worstCaseRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@highestCoefficient_worst_case) (Realization scalarSignature) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.highestCoefficient_worst_case.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.worstCaseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨worstCaseArena⟩
  objectArena := .source ⟨worstCaseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source worstCaseArena ⟨worstCaseFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ a v => weightedNewtonTail 3 a v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body",
        "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rowRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@highestRowSum_optimal) (Realization rowSignature) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.highestRowSum_optimal.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.rowFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena⟩
  objectArena := .source ⟨rowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena ⟨rowFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize rowSignature (fun _ _ a => highestRowSum a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def errorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@matrixHermiteTail_highest_error) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.matrixHermiteTail_highest_error.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.errorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨errorArena⟩
  objectArena := .source ⟨errorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source errorArena ⟨errorFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p F => matrixHermiteTail p.1 p.2.1 p.2.2 F)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def attainmentRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@matrixHermiteTail_highest_attained) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.matrixHermiteTail_highest_attained.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient.attainmentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨attainmentArena⟩
  objectArena := .source ⟨attainmentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source attainmentArena ⟨attainmentFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p F => matrixHermiteTail p.1 p.2.1 p.2.2 F)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value", "body"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
