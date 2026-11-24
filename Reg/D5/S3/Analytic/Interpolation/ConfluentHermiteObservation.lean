import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-!
The state is the observed function and the dependent parameters specify the
measurement interval and its nodes. The law keeps the full decomposition,
smoothness and derivative budget. The zero intervention fails even at a
fully coalesced first-order observation with an exact noiseless polynomial.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation

open _root_.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped ContDiff Matrix.Norms.L2Operator

abbrev ObservationParams := Σ m : ℕ, ℝ × ℝ × (Fin (m + 1) → ℝ)

abbrev observationSignature (Y : Type) : Signature.{0, 0, 0, 0, 0} where
  Params := ObservationParams
  State _ := ℝ → Y
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → Y
  Anchor := Empty
  finiteAnchor := inferInstance

private def zeroReadout (Y : Type) [Zero Y] : Realization (observationSignature Y) :=
  realize (observationSignature Y) (fun _ _ _ => 0) (fun e => nomatch e)

private theorem zeroReadout_sensitivity {Y : Type} [Zero Y]
    (A : Arena) (hA : A.signature = observationSignature Y)
    (actual : Realization A.signature)
    (hbad : ¬ A.Law (hA.symm ▸ zeroReadout Y)) : Sensitivity A actual := by
  cases A with
  | mk sig law =>
      change sig = observationSignature Y at hA
      subst sig
      constructor
      · intro i
        refine ⟨zeroReadout Y, ?_, ?_, hbad⟩
        · intro j hj
          exact False.elim (hj (Subsingleton.elim j i))
        · funext e
          exact nomatch e
      · intro e
        exact nomatch e

private def doubleNode : Fin 2 → ℝ := fun _ => 1

private theorem doubleNode_mem : ∀ i, doubleNode i ∈ Icc (1 / 2 : ℝ) 1 := by
  intro i
  exact ⟨by norm_num [doubleNode], le_rfl⟩

private theorem half_pos : 0 < (1 / 2 : ℝ) := by norm_num
private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num

def scalarActual : Realization (observationSignature ℝ) :=
  realize (observationSignature ℝ) (fun _ p F => hermiteTail p.2.1 p.2.2.1 p.2.2.2 F)
    (fun e => nomatch e)

def scalarArena : Arena where
  signature := observationSignature ℝ
  Law R := ∀ {m r : ℕ}, 0 < m → 0 < r →
    ∀ {lo hi : ℝ}, 0 < lo → lo < hi →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Icc lo hi) →
      ∀ (v : Fin m → ℝ) (K : ℝ) (F E : ℝ → ℝ) (B : Fin m → ℝ),
        EqOn F (fun x => K + x ^ r * (Polynomial.ofFn m v).eval x + E x) (Icc lo hi) →
        ContDiffOn ℝ m E (Icc lo hi) →
        (∀ j x, x ∈ Icc lo hi → ‖iteratedDerivWithin (j.val + 1) E (Icc lo hi) x‖ ≤ B j) →
        δ * ‖v‖ ≤ ‖R.readout () ⟨m, lo, hi, a⟩ F‖ + ‖fun j => B j / ((j.val + 1).factorial : ℝ)‖

private def scalarWitness (t : ℝ) : ℝ → ℝ :=
  fun x => x ^ 3 * (Polynomial.ofFn 1 (fun _ : Fin 1 => t)).eval x

private theorem scalarWitness_bound (R : Realization (observationSignature ℝ))
    (hLaw : scalarArena.Law R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      δ * ‖t‖ ≤ ‖R.readout () ⟨1, 1 / 2, 1, doubleNode⟩ (scalarWitness t)‖ := by
  obtain ⟨δ, hpos, hbound⟩ := @hLaw 1 3 (by decide) (by decide) (1 / 2) 1 half_pos half_lt_one
  refine ⟨δ, hpos, fun t => ?_⟩
  have h := hbound doubleNode doubleNode_mem (fun _ => t) 0 (scalarWitness t) (fun _ => 0) (fun _ => 0)
    (by intro x hx; simp [scalarWitness]) contDiffOn_const (by
      intro k x hx; simp [iteratedDerivWithin_const_zero])
  have hbudget : (fun k : Fin 1 => (0 : ℝ) / ((k.val + 1).factorial : ℝ)) = 0 := by
    funext k
    exact zero_div _
  simpa only [hbudget, norm_zero, add_zero, pi_norm_const] using h

private theorem scalarRejected : ¬ scalarArena.Law (zeroReadout ℝ) := by
  intro hLaw
  obtain ⟨δ, hδ, hw⟩ := scalarWitness_bound _ hLaw
  exact (not_le_of_gt hδ) (by simpa [zeroReadout, realize] using hw 1)

private theorem scalarDependence :
    ObservationalDependence (observationSignature ℝ) scalarActual := by
  intro role
  cases role
  let p : ObservationParams := ⟨1, 1 / 2, 1, doubleNode⟩
  let z := ‖scalarActual.readout () p 0‖
  obtain ⟨δ, hδ, hw⟩ := scalarWitness_bound scalarActual @hermiteTail_noisy_recovery
  let t := (z + 1) / δ
  have hz : 0 ≤ z := norm_nonneg _
  have ht : 0 ≤ t := div_nonneg (add_nonneg hz zero_le_one) hδ.le
  refine ⟨p, 0, scalarWitness t, fun heq => ?_⟩
  have h : δ * ‖t‖ ≤ z := by
    change δ * ‖t‖ ≤ ‖scalarActual.readout () p 0‖
    rw [heq]
    exact hw t
  rw [Real.norm_of_nonneg ht, show δ * t = z + 1 by
    dsimp only [t]; rw [mul_comm, div_mul_cancel₀ _ hδ.ne']] at h
  exact (not_le_of_gt (lt_add_of_pos_right z zero_lt_one)) h

def scalarFamily : Registration scalarArena (type_of% (@hermiteTail_noisy_recovery)) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@hermiteTail_noisy_recovery, zeroReadout ℝ, scalarRejected⟩
  sensitivity := zeroReadout_sensitivity scalarArena rfl scalarActual scalarRejected
  dependence := scalarDependence

noncomputable def scalarRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@hermiteTail_noisy_recovery) (type_of% scalarActual) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation.hermiteTail_noisy_recovery.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation.scalarFamily
  realizationSource := none
  generated := false
  arena := .source ⟨scalarArena⟩
  objectArena := .source ⟨scalarArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scalarArena ⟨scalarFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (observationSignature ℝ)
    (fun _ p F => hermiteTail p.2.1 p.2.2.1 p.2.2.2 F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
    definition := none
    -- Parameters m, lo, hi, a; the observed function F is binder 13.
    coordinates := #[0, 4, 5, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def matrixActual : Realization (observationSignature (Matrix (Fin 2) (Fin 2) ℝ)) :=
  realize (observationSignature (Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ p F => matrixHermiteTail p.2.1 p.2.2.1 p.2.2.2 F) (fun e => nomatch e)

def matrixArena : Arena where
  signature := observationSignature (Matrix (Fin 2) (Fin 2) ℝ)
  Law R := ∀ {m r : ℕ}, 0 < m → 0 < r →
    ∀ {lo hi : ℝ}, 0 < lo → lo < hi →
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Icc lo hi) →
      ∀ (v : Fin m → Matrix (Fin 2) (Fin 2) ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ)
        (F E : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : Fin m → ℝ),
        EqOn F (fun x i j =>
          K i j + x ^ r * (Polynomial.ofFn m (fun k => v k i j)).eval x + E x i j)
          (Icc lo hi) →
        (∀ i j, ContDiffOn ℝ m (fun x => E x i j) (Icc lo hi)) →
        (∀ k x, x ∈ Icc lo hi →
          let D : Matrix (Fin 2) (Fin 2) ℝ :=
            fun i j => iteratedDerivWithin (k.val + 1) (fun t => E t i j) (Icc lo hi) x
          ‖D‖ ≤ B k) →
        ‖v‖ ≤ C * (‖R.readout () ⟨m, lo, hi, a⟩ F‖ +
          ‖fun k => B k / ((k.val + 1).factorial : ℝ)‖)

private def matrixWitness (t : ℝ) : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun x i j => x ^ 3 * (Polynomial.ofFn 1
    (fun _ : Fin 1 => (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j)).eval x

private theorem matrixWitness_bound (R : Realization (observationSignature (Matrix (Fin 2) (Fin 2) ℝ)))
    (hLaw : matrixArena.Law R) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖t‖ ≤ C * ‖R.readout () ⟨1, 1 / 2, 1, doubleNode⟩ (matrixWitness t)‖ := by
  obtain ⟨C, hpos, hbound⟩ := @hLaw 1 3 (by decide) (by decide) (1 / 2) 1 half_pos half_lt_one
  refine ⟨C, hpos, fun t => ?_⟩
  have h := hbound doubleNode doubleNode_mem (fun _ => t • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    0 (matrixWitness t) (fun _ => 0) (fun _ => 0) (by intro x hx; ext i j; simp [matrixWitness])
    (fun _ _ => contDiffOn_const) (by
      intro k x hx
      let D : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
        iteratedDerivWithin (k.val + 1)
          (fun _ : ℝ => (0 : Matrix (Fin 2) (Fin 2) ℝ) i j) (Icc (1 / 2) 1) x
      have hzero : D = 0 := by
        funext i j
        simp [D]
      have hD : ‖D‖ ≤ (0 : ℝ) := by rw [hzero, norm_zero]
      exact hD)
  have hbudget : (fun k : Fin 1 => (0 : ℝ) / ((k.val + 1).factorial : ℝ)) = 0 := by
    funext k
    exact zero_div _
  simpa only [hbudget, norm_zero, add_zero, pi_norm_const, norm_smul, norm_one, mul_one] using h

private theorem matrixRejected : ¬ matrixArena.Law (zeroReadout (Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro hLaw
  obtain ⟨C, hC, hw⟩ := matrixWitness_bound _ hLaw
  exact (not_le_of_gt zero_lt_one) (by simpa [zeroReadout, realize] using hw 1)

private theorem matrixDependence :
    ObservationalDependence (observationSignature (Matrix (Fin 2) (Fin 2) ℝ)) matrixActual := by
  intro role
  cases role
  let p : ObservationParams := ⟨1, 1 / 2, 1, doubleNode⟩
  let z := ‖matrixActual.readout () p 0‖
  obtain ⟨C, hC, hw⟩ := matrixWitness_bound matrixActual @matrixHermiteTail_noisy_recovery
  let t := C * z + 1
  have ht : 0 ≤ t := add_nonneg (mul_nonneg hC.le (norm_nonneg _)) zero_le_one
  refine ⟨p, 0, matrixWitness t, fun heq => ?_⟩
  have h : ‖t‖ ≤ C * z := by
    change ‖t‖ ≤ C * ‖matrixActual.readout () p 0‖
    rw [heq]
    exact hw t
  rw [Real.norm_of_nonneg ht] at h
  exact (not_le_of_gt (lt_add_of_pos_right (C * z) zero_lt_one)) h

def matrixFamily : Registration matrixArena (type_of% (@matrixHermiteTail_noisy_recovery)) where
  actual := matrixActual
  bridge := Iff.rfl
  variation :=
    ⟨@matrixHermiteTail_noisy_recovery, zeroReadout (Matrix (Fin 2) (Fin 2) ℝ), matrixRejected⟩
  sensitivity := zeroReadout_sensitivity matrixArena rfl matrixActual matrixRejected
  dependence := matrixDependence

noncomputable def matrixRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@matrixHermiteTail_noisy_recovery) (type_of% matrixActual) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation.matrixHermiteTail_noisy_recovery.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation.matrixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨matrixArena⟩
  objectArena := .source ⟨matrixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source matrixArena ⟨matrixFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize (observationSignature (Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ p F => matrixHermiteTail p.2.1 p.2.2.1 p.2.2.2 F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
    definition := none
    -- Parameters m, lo, hi, a; the observed function F is binder 13.
    coordinates := #[0, 4, 5, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
