import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
open Module

namespace Reg.D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ), 2 ≤ a → 2 ≤ b →
    (∀ (ξ : Fin 3 → ℂ) (k : Fin (a + b + 2)) (r : ℕ),
      finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)) ≤
        finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r))) ∧
    (∃ P : MvPolynomial (Fin 3) ℂ, MvPolynomial.eval ![0, 0, 1] P = 1 ∧
      ∀ ξ : Fin 3 → ℂ, MvPolynomial.eval ξ P ≠ 0 →
        ∀ k : Fin (a + b + 2),
          (∀ r : ℕ,
            R.readout () () (finrank ℂ (LinearMap.range (sectorT a b k ξ ^ r)))
              (finrank ℂ (LinearMap.range (sectorF a b k 2 ^ r)))) ∧
          IsNilpotent (sectorT a b k ξ) ∧ IsNilpotent (sectorF a b k 2) ∧
          (∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ+)
            (bt : Basis (Σ i, Fin (s i)) ℂ (sector a b k)),
            ∀ (m : ℕ) (i : ι) (j : Fin (s i)),
              (sectorT a b k ξ ^ m) (bt ⟨i, j⟩) =
                if h : j.val + m < s i then bt ⟨i, ⟨j.val + m, h⟩⟩ else 0) ∧
          (∃ (ι' : Type) (_ : Fintype ι') (s' : ι' → ℕ+)
            (bf : Basis (Σ i, Fin (s' i)) ℂ (sector a b k)),
            ∀ (m : ℕ) (i : ι') (j : Fin (s' i)),
              (sectorF a b k 2 ^ m) (bf ⟨i, j⟩) =
                if h : j.val + m < s' i then bf ⟨i, ⟨j.val + m, h⟩⟩ else 0) ∧
          (∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (s : ι → ℕ+) (s' : ι' → ℕ+)
            (bt : Basis (Σ i, Fin (s i)) ℂ (sector a b k))
            (bf : Basis (Σ i, Fin (s' i)) ℂ (sector a b k)),
            (∀ (m : ℕ) (i : ι) (j : Fin (s i)),
              (sectorT a b k ξ ^ m) (bt ⟨i, j⟩) =
                if h : j.val + m < s i then bt ⟨i, ⟨j.val + m, h⟩⟩ else 0) →
            (∀ (m : ℕ) (i : ι') (j : Fin (s' i)),
              (sectorF a b k 2 ^ m) (bf ⟨i, j⟩) =
                if h : j.val + m < s' i then bf ⟨i, ⟨j.val + m, h⟩⟩ else 0) →
            ∀ j : ℕ,
              (Finset.univ.filter (fun i => (s i : ℕ) = j)).card =
                (Finset.univ.filter (fun i => (s' i : ℕ) = j)).card))

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨P, hP, h⟩ := (law 2 2 (by decide) (by decide)).2
  exact (h ![0, 0, 1] (by rw [hP]; exact one_ne_zero) 0).1 0

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have h := congrFun eq 0
  change (0 = 0) = (1 = (0 : ℕ)) at h
  exact Nat.one_ne_zero (h.mp rfl)

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
    definition := some {
      owner := `D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
      name := `D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "arg",
        "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.SpinChains.EclecticTwoWallUniversality
