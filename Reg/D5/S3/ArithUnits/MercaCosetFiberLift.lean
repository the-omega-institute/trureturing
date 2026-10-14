import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithUnits.MercaCosetFiberLift
import Reg.Support.DependentFamily

open _root_.D5.S3.ArithUnits.MercaCosetFiberLift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ArithUnits.MercaCosetFiberLift

@[reducible] def signature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℕ
  State p := Finset (ZMod (p.1 * p.2))ˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => moment (p.1 * p.2) S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p S => moment (p.1 * p.2) S + 1) (fun e => nomatch e)

/-- Every source clause is retained; only the left side of the uncentered equality varies. -/
@[reducible] def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (N ell : ℕ) (hN : 1 < N) (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N)
    (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ),
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
    letI : NeZero (N * ell) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)) hell.ne_zero⟩
    let pi := reduceUnits N ell
    let H : Subgroup (ZMod (N * ell))ˣ := K.comap pi
    let e : (ZMod N)ˣ := ZMod.unitOfCoprime ell hcop
    let C := cosetFinset K c
    let C' := cosetFinset K (e⁻¹ * c)
    let L := liftedFinset N ell C
    Nat.card H = Nat.card K * (ell - 1) ∧
    L.card = Nat.card K * (ell - 1) ∧
    (∃ d : (ZMod (N * ell))ˣ,
      pi d = c ∧ L = cosetFinset H d) ∧
    R.readout () ⟨N, ell⟩ L =
      (ell : ℚ) * moment N C +
        (N : ℚ) * (Nat.card K : ℚ) * (ell : ℚ) * ((ell : ℚ) - 1) / 2 -
        (ell : ℚ) * moment N C' ∧
    deviation (N * ell) H L =
      (ell : ℚ) * (deviation N K C - deviation N K C') ∧
    deviation (N * ell) H L =
      (ell : ℚ) * (moment N C - moment N C')

theorem actual_law : arena.Law actual := by
  exact result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 3 2 (by norm_num) (by decide) (by decide) ⊥ 1).2.2.2.1
  have ha := (result 3 2 (by norm_num) (by decide) (by decide) ⊥ 1).2.2.2.1
  change moment 6 (liftedFinset 3 2 (cosetFinset ⊥ 1)) + 1 = _ at hb
  change moment 6 (liftedFinset 3 2 (cosetFinset ⊥ 1)) = _ at ha
  linarith

private lemma bottom_coset {n : ℕ} [NeZero n] (c : (ZMod n)ˣ) :
    cosetFinset ⊥ c = {c} := by
  classical
  ext u
  simp [cosetFinset, inv_mul_eq_one, eq_comm]

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let e : (ZMod 3)ˣ := ZMod.unitOfCoprime 2 (by decide)
  let X := liftedFinset 3 2 (cosetFinset ⊥ (1 : (ZMod 3)ˣ))
  let Y := liftedFinset 3 2 (cosetFinset ⊥ e)
  refine ⟨⟨3, 2⟩, X, Y, ?_⟩
  change moment 6 X ≠ moment 6 Y
  have hX := (result 3 2 (by norm_num) (by decide) (by decide) ⊥ 1).2.2.2.1
  have hY := (result 3 2 (by norm_num) (by decide) (by decide) ⊥ e).2.2.2.1
  have hee : e * e = 1 := by
    apply Units.ext
    change (2 : ZMod 3) * 2 = 1
    decide
  have he : e⁻¹ = e := by
    exact inv_eq_of_mul_eq_one_left hee
  have hmOne : moment 3 (cosetFinset ⊥ (1 : (ZMod 3)ˣ)) = 1 := by
    rw [bottom_coset]
    simp only [moment, Finset.sum_singleton]
    rfl
  have hmE : moment 3 (cosetFinset ⊥ e) = 2 := by
    rw [bottom_coset]
    simp only [moment, Finset.sum_singleton]
    rfl
  have hX' : moment 6 X = 1 := by
    change moment 6 X =
      2 * moment 3 (cosetFinset ⊥ 1) +
        3 * (Nat.card (⊥ : Subgroup (ZMod 3)ˣ) : ℚ) * 2 * (2 - 1) / 2 -
        2 * moment 3 (cosetFinset ⊥ (e⁻¹ * 1)) at hX
    rw [he, mul_one, hmOne, hmE] at hX
    norm_num at hX
    exact hX
  have hY' : moment 6 Y = 5 := by
    change moment 6 Y =
      2 * moment 3 (cosetFinset ⊥ e) +
        3 * (Nat.card (⊥ : Subgroup (ZMod 3)ˣ) : ℚ) * 2 * (2 - 1) / 2 -
        2 * moment 3 (cosetFinset ⊥ (e⁻¹ * e)) at hY
    rw [he, hee, hmOne, hmE] at hY
    norm_num at hY
    exact hY
  rw [hX', hY']
  norm_num

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@result)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S3.ArithUnits.MercaCosetFiberLift.result.__information_unit,
  realizationName := `Reg.D5.S3.ArithUnits.MercaCosetFiberLift.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p S => moment (p.1 * p.2) S)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ArithUnits.MercaCosetFiberLift,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0,
      stateOperand := some #["arg"],
      functionOperand := false,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.ArithUnits.MercaCosetFiberLift
