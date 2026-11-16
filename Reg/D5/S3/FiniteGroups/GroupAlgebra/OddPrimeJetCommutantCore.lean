import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
import Reg.Support.OddPrimeJetAudit
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

/-! Faithful full-telescope audit mirrors of the original-action commutant endpoints. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant
open _root_.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
open Polynomial Module

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
universe uK
noncomputable section

abbrev signature : Signature where
  Params := Σ d : Reg.Support.OddPrimeJetAudit.Data.{uK},
    letI := d.prime; letI := d.field; letI := d.algebra
    d.K →ₗ[ZMod d.p] d.K
  State z := let d := z.1; letI := d.prime; letI := d.field; letI := d.algebra
    Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ z X =>
    let d := z.1
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    commutesOriginal (p := d.p) (K := d.K) z.2 X) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (X : Polynomial.degreeLT K p →ₗ[ZMod p] Polynomial.degreeLT K p),
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} :=
      { p := p, prime := pp, odd := po, K := K, field := kk, algebra := ka }
    r.readout () ⟨d, q⟩ X ↔
      commutesJet (p := p) (K := K) q X

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (2 < 3) := ⟨by decide⟩
  let K := Reg.Support.OddPrimeJetAudit.testK.{uK}
  letI : Field K := inferInstance
  letI : Algebra (ZMod 3) K := inferInstance
  let q : K →ₗ[ZMod 3] K := 0
  let X : Polynomial.degreeLT K 3 →ₗ[ZMod 3] Polynomial.degreeLT K 3 := 0
  have hh := h (p := 3) (K := K) q X
  have hj : commutesJet (p := 3) (K := K) q X := by
    intro a v
    simp [commutesJet, q, X]
  exact (by simpa [rejected, realize, hj] using hh : False)

def family : Registration arena.{uK}
    (type_of% (@actual_commutant_iff_jet.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_commutant_iff_jet.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    let q : d.K →ₗ[ZMod d.p] d.K := 0
    let X0 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p := 0
    let X1 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p :=
      ((constantLinear (p := d.p) (K := d.K)).restrictScalars (ZMod d.p)).comp
        ((coefficientZero (p := d.p) (K := d.K)).restrictScalars (ZMod d.p))
    refine ⟨⟨d, q⟩, X0, X1, ?_⟩
    change commutesOriginal (p := d.p) (K := d.K) q X0 ≠
      commutesOriginal (p := d.p) (K := d.K) q X1
    have hzero : commutesOriginal (p := d.p) (K := d.K) q X0 := by
      intro g v
      simp [q, X0]
    have hone : ¬ commutesOriginal (p := d.p) (K := d.K) q X1 := by
      intro h
      have hj := (actual_commutant_iff_jet (p := d.p) (K := d.K) q X1).mp h
      have hp : d.p = 3 := rfl
      have h1 : 1 < d.p := by rw [hp]; decide
      have hpne : d.p ≠ 1 := by rw [hp]; decide
      let v1 : d.K[X]_d.p := dividedMonomial (p := d.p) 1 h1 1
      have hv := hj 1 v1
      have hd := dividedMonomial_succ (p := d.p) (K := d.K) 0 h1 1
      have hc : coefficientZero v1 = 0 := by
        dsimp [v1]
        change ((dividedMonomial (p := d.p) (K := d.K) 1 h1 (1 : d.K) :
          Polynomial.degreeLT d.K d.p) : Polynomial d.K).coeff 0 = 0
        simp [dividedMonomial, hpne]
      have hD : derivativeEnd (p := d.p) (K := d.K) v1 =
          constantLinear (p := d.p) (K := d.K) 1 := by
        dsimp [v1]
        rw [hd, dividedMonomial_zero]
      have hxv : X1 v1 = 0 := by simp [X1, hc]
      have hxd : X1 (derivativeEnd (p := d.p) (K := d.K) v1) =
          constantLinear (p := d.p) (K := d.K) 1 := by
        rw [hD]
        simp [X1, coefficientZero, constantLinear]
      rw [show jetOperator q 1 v1 = derivativeEnd (p := d.p) (K := d.K) v1 by
        simp [jetOperator, q], hxd, hxv] at hv
      have h10 : (1 : d.K) ≠ 0 := one_ne_zero
      exact h10 (by
        simpa [constantLinear] using congrArg (fun w : Polynomial.degreeLT d.K d.p =>
          (w : Polynomial d.K).coeff 0) hv)
    exact fun heq => hone (by rw [← heq]; exact hzero)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_commutant_iff_jet.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.actual_commutant_iff_jet.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family.{uK}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace generated_bridge

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (hq1 : q 1 = 0)
    (X : Polynomial.degreeLT K p →ₗ[ZMod p] Polynomial.degreeLT K p),
    r.readout () ⟨⟨p, pp, po, K, kk, ka⟩, q⟩ X ↔
      ((∀ v, X (derivativeEnd v) = derivativeEnd (X v)) ∧
        (∀ (a : K) (v), X (a • derivativeEnd v) = a • derivativeEnd (X v)))

def rejected : Realization signature.{uK} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
  letI := d.prime
  letI := d.odd
  letI := d.field
  letI := d.algebra
  let q : d.K →ₗ[ZMod d.p] d.K := 0
  let X : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p := 0
  have hh := hbad (p := d.p) q rfl X
  have hr : (∀ v, X (derivativeEnd v) = derivativeEnd (X v)) ∧
      (∀ (a : d.K) (v), X (a • derivativeEnd v) = a • derivativeEnd (X v)) := by
    simp [q, X]
  simpa [rejected, realize] using hh.mpr hr

def family : Registration arena.{uK} (type_of% (@actual_commutant_generated_bridge.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_commutant_generated_bridge.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    let q : d.K →ₗ[ZMod d.p] d.K := 0
    let X0 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p := 0
    let X1 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p :=
      ((constantLinear (p := d.p) (K := d.K)).restrictScalars (ZMod d.p)).comp
        ((coefficientZero (p := d.p) (K := d.K)).restrictScalars (ZMod d.p))
    refine ⟨⟨d, q⟩, X0, X1, ?_⟩
    change commutesOriginal (p := d.p) (K := d.K) q X0 ≠
      commutesOriginal (p := d.p) (K := d.K) q X1
    have hzero : commutesOriginal (p := d.p) (K := d.K) q X0 := by
      intro g v
      simp [q, X0]
    have hone : ¬ commutesOriginal (p := d.p) (K := d.K) q X1 := by
      intro h
      have hj := (actual_commutant_iff_jet (p := d.p) (K := d.K) q X1).mp h
      have hp : d.p = 3 := rfl
      have h1 : 1 < d.p := by rw [hp]; decide
      have hpne : d.p ≠ 1 := by rw [hp]; decide
      let v1 : d.K[X]_d.p := dividedMonomial (p := d.p) 1 h1 1
      have hv := hj 1 v1
      have hd := dividedMonomial_succ (p := d.p) (K := d.K) 0 h1 1
      have hc : coefficientZero v1 = 0 := by
        dsimp [v1]
        change ((dividedMonomial (p := d.p) (K := d.K) 1 h1 (1 : d.K) :
          Polynomial.degreeLT d.K d.p) : Polynomial d.K).coeff 0 = 0
        simp [dividedMonomial, hpne]
      have hD : derivativeEnd (p := d.p) (K := d.K) v1 =
          constantLinear (p := d.p) (K := d.K) 1 := by
        dsimp [v1]
        rw [hd, dividedMonomial_zero]
      have hxv : X1 v1 = 0 := by simp [X1, hc]
      have hxd : X1 (derivativeEnd (p := d.p) (K := d.K) v1) =
          constantLinear (p := d.p) (K := d.K) 1 := by
        rw [hD]
        simp [X1, coefficientZero, constantLinear]
      rw [show jetOperator q 1 v1 = derivativeEnd (p := d.p) (K := d.K) v1 by
        simp [jetOperator, q], hxd, hxv] at hv
      have h10 : (1 : d.K) ≠ 0 := one_ne_zero
      exact h10 (by
        simpa [constantLinear] using congrArg (fun w : Polynomial.degreeLT d.K d.p =>
          (w : Polynomial d.K).coeff 0) hv)
    exact fun heq => hone (by rw [← heq]; exact hzero)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_commutant_generated_bridge.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.actual_commutant_generated_bridge.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore.generated_bridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end generated_bridge

namespace normal_form

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (q : K →ₗ[ZMod p] K) (hq1 : q 1 = 0)
    (X : Polynomial.degreeLT K p →ₗ[ZMod p] Polynomial.degreeLT K p),
    r.readout () ⟨⟨p, pp, po, K, kk, ka⟩, q⟩ X ↔
      ∃ c : Fin p → K, ∃ T : K →ₗ[ZMod p] K, c 0 = 0 ∧
        X = toeplitzDegree c T

def rejected : Realization signature.{uK} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
  intro hbad
  let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
  letI := d.prime
  letI := d.odd
  letI := d.field
  letI := d.algebra
  let q : d.K →ₗ[ZMod d.p] d.K := 0
  let X : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p := 0
  have hh := hbad (p := d.p) q rfl X
  have hr : ∃ c : Fin d.p → d.K, ∃ T : d.K →ₗ[ZMod d.p] d.K, c 0 = 0 ∧
      X = toeplitzDegree c T := by
    refine ⟨0, 0, by simp, ?_⟩
    simp [X, toeplitzDegree, scalarMap, topMap]
  simpa [rejected, realize] using hh.mpr hr

def family : Registration arena.{uK} (type_of% (@actual_commutant_normal_form.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_commutant_normal_form.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := generated_bridge.family.dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_commutant_normal_form.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.actual_commutant_normal_form.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore.normal_form.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end normal_form

namespace injective

abbrev signature : Signature where
  Params := Σ d : Reg.Support.OddPrimeJetAudit.Data.{uK},
    letI := d.prime; letI := d.field; letI := d.algebra
    d.K →ₗ[ZMod d.p] d.K
  State z := Fin z.1.p → z.1.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ z := let d := z.1; letI := d.prime; letI := d.field; letI := d.algebra
    Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ z c =>
    let d := z.1
    letI := d.prime; letI := d.odd; letI := d.field; letI := d.algebra
    toeplitzDegree (p := d.p) c z.2) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ z _ =>
    let d := z.1; letI := d.prime; letI := d.field; letI := d.algebra
    (0 : Polynomial.degreeLT d.K d.p →ₗ[ZMod d.p] Polynomial.degreeLT d.K d.p))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (c d : Fin p → K) (hc : c 0 = 0) (hd : d 0 = 0)
    (T U : K →ₗ[ZMod p] K)
    (h : r.readout () ⟨⟨p, pp, po, K, kk, ka⟩, T⟩ c = toeplitzDegree d U),
    c = d ∧ T = U

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
    intro hbad
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra

    let c : Fin d.p → d.K := 0
    let T : d.K →ₗ[ZMod d.p] d.K := LinearMap.id
    let U : d.K →ₗ[ZMod d.p] d.K := 0
    have hc : c 0 = 0 := rfl
    have hh := hbad (p := d.p) (K := d.K) c c hc hc T U (by
      simp [rejected, realize, c, U, toeplitzDegree, scalarMap, topMap])
    have he := congrArg (fun A : d.K →ₗ[ZMod d.p] d.K => A 1) hh.2
    have h10 : (1 : d.K) ≠ 0 := one_ne_zero
    exact h10 (by simpa [T, U] using he)

def family : Registration arena.{uK} (type_of% (@toeplitzDegree_injective.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@toeplitzDegree_injective.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra
    have hnonzero : constantLinear (p := d.p) (K := d.K) 1 ≠
        (0 : Polynomial.degreeLT d.K d.p) := by
      intro h
      have hh := congrArg (fun v : Polynomial.degreeLT d.K d.p =>
        (v : Polynomial d.K).coeff 0) h
      simpa [constantLinear] using hh
    letI : Nontrivial (Polynomial.degreeLT d.K d.p) := ⟨⟨constantLinear 1, 0, hnonzero⟩⟩

    let T : d.K →ₗ[ZMod d.p] d.K := 0
    let z : Fin d.p → d.K := 0
    let o : Fin d.p → d.K := 1
    refine ⟨⟨d, T⟩, z, o, ?_⟩
    have hz : toeplitzDegree (p := d.p) z T = 0 := by
      simp [z, T, toeplitzDegree, scalarMap, topMap]
    have hu : IsUnit (toeplitzDegree (p := d.p) o T) :=
      (toeplitzDegree_isUnit_iff o T).mpr (by simp [o])
    intro heq
    exact hu.ne_zero (heq.symm.trans hz)

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@toeplitzDegree_injective.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.toeplitzDegree_injective.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore.injective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end injective

namespace isUnit

abbrev signature : Signature where
  Params := Reg.Support.OddPrimeJetAudit.Data.{uK}
  State d := Fin d.p → d.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := d.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uK} :=
  realize signature (fun _ d c => letI := d.prime; letI := d.odd
    c (leadingIndex (p := d.p))) (fun e => nomatch e)

def rejected : Realization signature.{uK} :=
  realize signature (fun _ d _ => letI := d.field; (0 : d.K)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{uK}
  Law r := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type uK} [kk : Field K] [ka : Algebra (ZMod p) K]
    (c : Fin p → K) (T : K →ₗ[ZMod p] K),
    IsUnit (toeplitzDegree (p := p) c T) ↔
      r.readout () ⟨p, pp, po, K, kk, ka⟩ c ≠ 0

private theorem rejected_law : ¬ arena.{uK}.Law rejected := by
    intro hbad
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra

    let c : Fin d.p → d.K := 1
    let T : d.K →ₗ[ZMod d.p] d.K := 0
    have hu : IsUnit (toeplitzDegree (p := d.p) c T) :=
      (toeplitzDegree_isUnit_iff c T).mpr (by simp [c])
    have hh := (hbad (p := d.p) (K := d.K) c T).mp hu
    exact hh rfl

def family : Registration arena.{uK} (type_of% (@toeplitzDegree_isUnit_iff.{uK})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@toeplitzDegree_isUnit_iff.{uK}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    let d : Reg.Support.OddPrimeJetAudit.Data.{uK} := Reg.Support.OddPrimeJetAudit.testData
    letI := d.prime
    letI := d.odd
    letI := d.field
    letI := d.algebra

    refine ⟨d, 0, 1, ?_⟩
    exact zero_ne_one

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@toeplitzDegree_isUnit_iff.{uK}) (Realization signature.{uK}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutant.toeplitzDegree_isUnit_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore.isUnit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{uK}⟩
  objectArena := .source ⟨arena.{uK}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{uK} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end isUnit

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetCommutantCore
