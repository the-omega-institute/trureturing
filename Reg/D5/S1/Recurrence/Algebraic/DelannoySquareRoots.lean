import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.DelannoySquareRoots
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots

open _root_.D5.S1.Recurrence.Algebraic.DelannoySquareRoots
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := List Step
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => (endpoint p).1 + (endpoint p).2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The entire source law is retained. The observation is the endpoint coordinate sum
in the path-enumeration equivalence, with its original row and path variables. -/
def arena : Arena where
  signature := signature
  Law R :=
    (∀ (n : ℕ) (p : List Step), p ∈ paths n ↔ R.readout () n p = n) ∧
    squareDenominator * squareSeries = 1 - PowerSeries.X ∧
    (∀ n : ℕ, (ordinaryRow n).eval₂ (Int.castRingHom ℝ) (1 - Real.sqrt 2) ≠ 0) ∧
    ∀ (u v y : ℂ), u ≠ 0 → v ≠ 0 → u + v + u * v = 1 → y * u * v = 1 →
      ∀ n : ℕ, y * (v - u) * (-1) ^ n *
        (squareRow n).eval₂ (Int.castRingHom ℂ) (-y) =
        (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-u) / u ^ (n + 1) -
          (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-v) / v ^ (n + 1)

def family : Registration arena (type_of% source_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_correspondence, rejected, by
    intro h
    have h0 := (h.1 0 []).mp (by simp [paths])
    norm_num [rejected, realize] at h0⟩
  sensitivity := by
    have bad : ¬ arena.Law rejected := by
      intro h
      have h0 := (h.1 0 []).mp (by simp [paths])
      norm_num [rejected, realize] at h0
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(0 : ℕ), ([] : List Step), [Step.east], ?_⟩
    change (0 : ℕ) ≠ 1
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    source_correspondence (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.DelannoySquareRoots.source_correspondence
    "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.DelannoySquareRoots
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev circleSignature : Signature where
  Params := ℕ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def circleActual : Realization circleSignature :=
  realize circleSignature (fun _ n w => (squareRow n).eval₂ (Int.castRingHom ℂ) w)
    (fun e => nomatch e)

def circleRejected : Realization circleSignature :=
  realize circleSignature (fun _ _ _ => 1) (fun e => nomatch e)

def circleArena : Arena where
  signature := circleSignature
  Law R := ∀ n : ℕ,
    ∃ z : Fin n → ℝ, Function.Injective z ∧
      (∀ i, 0 < z i ∧ z i ≠ Real.sqrt 2 - 1) ∧
      (∀ w : ℂ, (ordinaryRow n).eval₂ (Int.castRingHom ℂ) (-w) =
        (-1) ^ n * ∏ i, (w - (z i : ℂ))) ∧
      ∃ y : Fin ((Finset.univ.filter fun i : Fin n => Real.sqrt 2 - 1 < z i).card) → ℝ,
        Function.Injective y ∧ ∀ i,
          3 - 2 * Real.sqrt 2 < y i ∧ y i < 3 + 2 * Real.sqrt 2 ∧
          R.readout () n (-(y i : ℂ)) = 0

def circleFamily : Registration circleArena (type_of% upper_circle_roots) where
  actual := circleActual
  bridge := Iff.rfl
  variation := ⟨upper_circle_roots, circleRejected, by
    intro h
    obtain ⟨z, _, _, hf, y, _, hy⟩ := h 1
    have hz : z 0 = 1 := by
      have he := hf 0
      have hr : ordinaryRow 1 = 1 + Polynomial.X := by
        simp [ordinaryRow, paths, endpoint, add_comm]
      rw [hr] at he
      norm_num [Fin.prod_univ_one] at he
      exact_mod_cast he.symm
    have hs : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hc : (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i).card = 1 := by
      have he : (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i) =
          Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        fin_cases i
        change Real.sqrt 2 - 1 < z 0
        rw [hz]
        linarith
      rw [he]
      simp
    have hi : 0 < (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i).card := by
      rw [hc]
      decide
    exact one_ne_zero (hy ⟨0, hi⟩).2.2
  ⟩
  sensitivity := by
    have bad : ¬ circleArena.Law circleRejected := by
      intro h
      obtain ⟨z, _, _, hf, y, _, hy⟩ := h 1
      have hz : z 0 = 1 := by
        have he := hf 0
        have hr : ordinaryRow 1 = 1 + Polynomial.X := by
          simp [ordinaryRow, paths, endpoint, add_comm]
        rw [hr] at he
        norm_num [Fin.prod_univ_one] at he
        exact_mod_cast he.symm
      have hs : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      have hc : (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i).card = 1 := by
        have he : (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i) =
            Finset.univ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          fin_cases i
          change Real.sqrt 2 - 1 < z 0
          rw [hz]
          linarith
        rw [he]
        simp
      have hi : 0 < (Finset.univ.filter fun i : Fin 1 => Real.sqrt 2 - 1 < z i).card := by
        rw [hc]
        decide
      exact one_ne_zero (hy ⟨0, hi⟩).2.2
    constructor
    · intro i
      refine ⟨circleRejected, ?_, rfl, bad⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : ℂ), (1 : ℂ), ?_⟩
    have h00 : delannoy 0 0 = 1 := by simp [delannoy, paths, Finset.filter_insert, Finset.filter_singleton, endpoint]
    have h10 : delannoy 1 0 = 1 := by simp [delannoy, paths, Finset.filter_insert, Finset.filter_singleton, endpoint]
    have h11 : delannoy 1 1 = 1 := by simp [delannoy, paths, Finset.filter_insert, Finset.filter_singleton, endpoint]
    have hr : squareRow 1 = 2 + Polynomial.X := by
      norm_num [squareRow, squareEntry, h00, h10, h11,
        Finset.sum_range_succ, Finset.sum_Icc_succ_top]
    change (squareRow 1).eval₂ (Int.castRingHom ℂ) 0 ≠
      (squareRow 1).eval₂ (Int.castRingHom ℂ) 1
    rw [hr]
    norm_num

def circleRegistration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    upper_circle_roots (Realization circleSignature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.DelannoySquareRoots.upper_circle_roots "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots.circleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨circleArena⟩
  objectArena := .source ⟨circleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source circleArena ⟨circleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize circleSignature circleActual.readout circleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.DelannoySquareRoots
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg",
        "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.DelannoySquareRoots
