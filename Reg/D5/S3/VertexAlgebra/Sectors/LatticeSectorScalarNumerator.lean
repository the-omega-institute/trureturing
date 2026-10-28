import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator

/-! Source-bound coefficient, support and finite-polynomial observations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.VertexAlgebra
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open _root_.D5.S3.VertexAlgebra.LatticeSectorScalarNumerator
open _root_.D5.S3.VertexAlgebra.LatticeSectorChannelTransport
open _root_.D5.S3.VertexAlgebra.SupportedChannelSeries
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open scoped VertexOperator BigOperators

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator

private def D0 : LatticeData :=
  ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
private theorem inverse_left : (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) * gramComplex D0 = 1 := by
  ext i
  exact Fin.elim0 i
private theorem inverse_right :
    gramComplex D0 * (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) = 1 := by
  ext i
  exact Fin.elim0 i

private theorem vacuum_mode (D : LatticeData) (n : ℤ) (t : Oscillator D) :
    canonical D 0 0 1 n t = if n = -1 then t else 0 := by
  change action D 0 1 n t = _
  rw [action_vacuum]
  split_ifs <;> rfl

namespace IntegerBound
abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad : (1 : ℤ) ≤ 0 := Eq.mp (congrFun h 0) (le_refl 0)
  omega
end IntegerBound

namespace Coefficient
abbrev arena : Arena where
  signature := IntegerBound.signature
  Law a := ∀ (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_hJG : J * gramComplex D = 1) (_hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (m n : ℤ) (T : Exponent D)
    (_ : (canonical D α (β + γ) u m (canonical D β γ v n w)).coeff T ≠ 0),
    a.readout () ()
      (chargeEnergy D α + chargeEnergy D β + chargeEnergy D γ - m - n - 2)
      (chargeEnergy D (α + (β + γ)) + oscillatorEnergy T)

private theorem bad : ¬ arena.Law IntegerBound.rejected := by
  intro h
  apply h D0 0 inverse_left inverse_right 0 0 0 1 1 1 (-1) (-1) 0
  change (canonical D0 0 0 1 (-1) (canonical D0 0 0 1 (-1) 1)).coeff 0 ≠ 0
  rw [vacuum_mode, ite_eq_left rfl, vacuum_mode, ite_eq_left rfl]
  simp

def family : Registration arena (type_of% (@actual_product_coefficient_energy_le)) where
  actual := IntegerBound.actual
  bridge := Iff.rfl
  variation := ⟨actual_product_coefficient_energy_le, IntegerBound.rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨IntegerBound.rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := IntegerBound.dependence
end Coefficient

namespace Support
abbrev arena : Arena where
  signature := IntegerBound.signature
  Law a := ∀ (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_hJG : J * gramComplex D = 1) (_hGJ : gramComplex D * J = 1)
    (α β γ : Charge D) (u v w : Oscillator D) (N A B : ℕ)
    (P : MvPowerSeries (Fin 2) (Oscillator D))
    (_common : ∀ a b : ℤ,
      clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b)
    (p : Oscillator D) (d : Fin 2 →₀ ℕ)
    (_hne : MvPowerSeries.coeff d (mapSeries (readout D p) P) ≠ 0),
    a.readout () () (d.degree : ℤ) (degreeBound D α β γ A B N p)

private theorem common_one (a b : ℤ) :
    clear 0 (product D0 0 0 0 1 1 1) a b =
      extend (1 : MvPowerSeries (Fin 2) (Oscillator D0)) a b := by
  classical
  have hz (x y : ℕ) : powerIndex x y = 0 ↔ x = 0 ∧ y = 0 := by
    constructor
    · intro h
      have hx := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
      have hy := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
      simpa [powerIndex] using And.intro hx hy
    · rintro ⟨rfl, rfl⟩
      simp [powerIndex]
  simp only [clear, Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, one_smul, Nat.cast_zero,
    sub_zero, add_zero]
  change canonical D0 0 0 1 (-a - 1) (canonical D0 0 0 1 (-b - 1) 1) = _
  rw [vacuum_mode, vacuum_mode]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    by_cases hab : 0 ≤ a ∧ 0 ≤ b <;>
    simp [extend, MvPowerSeries.coeff_one, hz, Int.toNat_eq_zero, ha, hb, hab] <;>
    omega

private theorem bad : ¬ arena.Law IntegerBound.rejected := by
  intro h
  apply h D0 0 inverse_left inverse_right 0 0 0 1 1 1 0 0 0 1
    (by intro a b; simpa using common_one a b) 1 0
  change FactorialFockMetric.inner (1 : Oscillator D0) 1 ≠ 0
  have hmon : (1 : Oscillator D0) = MvPolynomial.monomial 0 1 := by simp
  rw [hmon, FactorialFockMetric.inner_monomial_left]
  simp [FactorialFockMetric.weight]

def family : Registration arena (type_of% (@scalar_numerator_support)) where
  actual := IntegerBound.actual
  bridge := Iff.rfl
  variation := ⟨scalar_numerator_support, IntegerBound.rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨IntegerBound.rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := IntegerBound.dependence
end Support

namespace Numerator
abbrev signature : Signature where
  Params := Unit
  State _ := MvPowerSeries (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := MvPowerSeries (Fin 2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have bad : (1 : MvPowerSeries (Fin 2) ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero bad

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_hJG : J * gramComplex D = 1) (_hGJ : gramComplex D * J = 1)
    (α β : Charge D) (u : Sector D α) (v : Sector D β) ,
    ∃ N : ℕ,
      delta^[N] (FieldNormalProductLocality.commutator
        (LatticeAllStateField.Y D (inclusion D α u))
        (LatticeAllStateField.Y D (inclusion D β v))) = 0 ∧
      (∀ n : ℤ, (N : ℤ) ≤ n → canonical D α β u n v = 0) ∧
      ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
        ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
        (∀ n : ℤ, (A : ℤ) ≤ n → canonical D α γ u n w = 0) ∧
        (∀ n : ℤ, (B : ℤ) ≤ n → canonical D β γ v n w = 0) ∧
        (∀ a b : ℤ,
          clear N (product D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clear N (reverseProduct D α β γ u v w) (a - A) (b - B) = extend P a b ∧
          clearIterate N A B (iterate D α β γ u v w) a b = extend (collision P) a b) ∧
        ∀ p : Oscillator D, ∃! R : MvPolynomial (Fin 2) ℂ,
          a.readout () ()
            (R : MvPowerSeries (Fin 2) ℂ) (mapSeries (readout D p) P) ∧
          R.totalDegree ≤ (degreeBound D α β γ A B N p).toNat ∧
          (degreeBound D α β γ A B N p < 0 →
            mapSeries (readout D p) P = 0 ∧ R = 0) ∧
          ∀ a b : ℤ,
            clear N (fun x y => readout D p (product D α β γ u v w x y))
                (a - A) (b - B) = extend (R : MvPowerSeries (Fin 2) ℂ) a b ∧
            clear N (fun x y => readout D p (reverseProduct D α β γ u v w x y))
                (a - A) (b - B) = extend (R : MvPowerSeries (Fin 2) ℂ) a b ∧
            clearIterate N A B (fun x y => readout D p (iterate D α β γ u v w x y))
                a b = extend (collision (R : MvPowerSeries (Fin 2) ℂ)) a b

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, _hN, _huv, rest⟩ := h D0 0 inverse_left inverse_right 0 0 0 0
  obtain ⟨A, B, P, _hA, _hB, _common, tests⟩ := rest 0 0
  obtain ⟨R, hR, _unique⟩ := tests 0
  exact hR.1

def family : Registration arena (type_of% (@ordinary_actual_finite_scalar_numerator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_actual_finite_scalar_numerator, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence
end Numerator

def coefficientAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_product_coefficient_energy_le)
    (Realization IntegerBound.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.coefficientUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.Coefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨Coefficient.arena⟩
  objectArena := .source ⟨Coefficient.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Coefficient.arena ⟨Coefficient.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize IntegerBound.signature
    IntegerBound.actual.readout IntegerBound.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def supportAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@scalar_numerator_support) (Realization IntegerBound.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.supportUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨Support.arena⟩
  objectArena := .source ⟨Support.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Support.arena ⟨Support.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize IntegerBound.signature
    IntegerBound.actual.readout IntegerBound.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def numeratorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_actual_finite_scalar_numerator)
    (Realization Numerator.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.numeratorUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.Numerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨Numerator.arena⟩
  objectArena := .source ⟨Numerator.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Numerator.arena ⟨Numerator.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Numerator.signature Numerator.actual.readout Numerator.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "body",
        "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open UniformGradedLocalCorrelator (word coefficientDistribution clearingPolynomial totalExponent labelledPairs polynomialAction)
open UngradedLocalWordSeries

namespace WordEnergy
abbrev arena : Arena where
  signature := IntegerBound.signature
  Law a := ∀ (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (_hJG : J * gramComplex D = 1) (_hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D)
    (δ : Charge D) (w : Sector D δ) (l : List (Fin n)) (e : Fin n → ℤ)
    (ρ : Charge D) (T : Exponent D)
    (_hne : carrierCoeffEquiv D
      (word (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))) l e
        (inclusion D δ w)) (ρ, T) ≠ 0),
    a.readout () ()
      (chargeEnergy D δ + (l.map (fun i => chargeEnergy D (c i) + e i)).sum)
      (chargeEnergy D ρ + oscillatorEnergy T)

private theorem bad : ¬ arena.Law IntegerBound.rejected := by
  intro h
  apply h D0 0 inverse_left inverse_right 0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) 0 1 [] (fun i => Fin.elim0 i) 0 0
  change (1 : Oscillator D0).coeff 0 ≠ 0
  simp

def family : Registration arena (type_of% (@actual_word_coefficient_energy_le)) where
  actual := IntegerBound.actual
  bridge := Iff.rfl
  variation := ⟨actual_word_coefficient_energy_le, IntegerBound.rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨IntegerBound.rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := IntegerBound.dependence
end WordEnergy

namespace WordSupport
abbrev arena : Arena where
  signature := IntegerBound.signature
  Law obs := ∀ (D : LatticeData)
    (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D)
    (δ : Charge D) (w : Sector D δ) (k : ℕ) (a : Fin n → ℕ)
    (P : MvPowerSeries (Fin n) (Carrier D))
    (common : ∀ e : Fin n → ℤ,
      polynomialAction (clearingPolynomial n k)
        (coefficientDistribution
          (fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i)))
          (inclusion D δ w) 1 (List.ofFn (fun i : Fin n => i)))
        (fun i => e i - (a i : ℤ)) = signedExtend P e)
    (p : Oscillator D) (d : Fin n →₀ ℕ)
    (hne : ((readout D p).comp (projection D ((∑ i, c i) + δ))) (P d) ≠ 0),
    obs.readout () () (d.degree : ℤ) (wordDegreeBound D c δ k a p)

private theorem bad : ¬ arena.Law IntegerBound.rejected := by
  intro h
  let P : MvPowerSeries (Fin 0) (Carrier D0) := fun _ => inclusion D0 0 1
  have common : ∀ e : Fin 0 → ℤ,
      polynomialAction (clearingPolynomial 0 0)
        (coefficientDistribution
          (fun i : Fin 0 => LatticeAllStateField.Y D0 (inclusion D0 (Fin.elim0 i) (Fin.elim0 i)))
          (inclusion D0 0 1) 1 (List.ofFn (fun i : Fin 0 => i)))
        (fun i => e i - ((fun i : Fin 0 => Fin.elim0 i) i : ℕ)) = signedExtend P e := by
    intro e
    have positive : ∀ i : Fin 0, 0 ≤ e i := fun i => Fin.elim0 i
    simp [clearingPolynomial, labelledPairs, coefficientDistribution, word,
      signedExtend, positive, P]
  apply h D0 0 inverse_left inverse_right 0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) 0 1 0 (fun i => Fin.elim0 i) P common 1 0
  change FactorialFockMetric.inner (1 : Oscillator D0) 1 ≠ 0
  have hmon : (1 : Oscillator D0) = MvPolynomial.monomial 0 1 := by simp
  rw [hmon, FactorialFockMetric.inner_monomial_left]
  simp [FactorialFockMetric.weight]

def family : Registration arena (type_of% (@actual_word_scalar_numerator_support)) where
  actual := IntegerBound.actual
  bridge := Iff.rfl
  variation := ⟨actual_word_scalar_numerator_support, IntegerBound.rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨IntegerBound.rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := IntegerBound.dependence
end WordSupport

namespace WordNumerator
abbrev signature : Signature where
  Params := ℕ
  State n := MvPowerSeries (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output n _ := MvPowerSeries (Fin n) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have bad : (1 : MvPowerSeries (Fin 0) ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero bad

abbrev arena : Arena where
  signature := signature
  Law obs := ∀
    (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D),
    let A := fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))
    let order := List.ofFn (fun i : Fin n => i)
    ∃ k : ℕ,
      (∀ i j : Fin n, i < j → (deltaEnd ^ k) (commutator (A i) (A j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin n → ℕ,
        ∃ P : MvPowerSeries (Fin n) (Carrier D),
        (∀ (i : Fin n) (m : ℤ), (a i : ℤ) ≤ m → (A i [[m]]) (inclusion D δ w) = 0) ∧
        (∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
          polynomialAction (clearingPolynomial n k)
            (coefficientDistribution A (inclusion D δ w) 1 other)
            (fun i => e i - (a i : ℤ)) = signedExtend P e) ∧
        ∀ p : Oscillator D,
          let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
          let S : MvPowerSeries (Fin n) ℂ := fun d => φ (P d)
          (∀ d, S d ≠ 0 → (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p) ∧
          ∃! R : MvPolynomial (Fin n) ℂ,
            obs.readout n () (R : MvPowerSeries (Fin n) ℂ) S ∧
            R.totalDegree ≤ (wordDegreeBound D c δ k a p).toNat ∧
            (wordDegreeBound D c δ k a p < 0 → S = 0 ∧ R = 0) ∧
            ∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
              polynomialAction (clearingPolynomial n k)
                (fun b => φ (coefficientDistribution A (inclusion D δ w) 1 other b))
                (fun i => e i - (a i : ℤ)) = signedExtend (R : MvPowerSeries (Fin n) ℂ) e

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, _hk, rest⟩ := h D0 0 inverse_left inverse_right 0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨a, P, _truncation, _common, tests⟩ := rest 0 0
  obtain ⟨_support, R, hR, _unique⟩ := tests 0
  exact hR.1

def family : Registration arena (type_of% (@ordinary_actual_word_finite_scalar_numerator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_actual_word_finite_scalar_numerator, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence
end WordNumerator

def wordEnergyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_word_coefficient_energy_le) (Realization IntegerBound.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordEnergyUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨WordEnergy.arena⟩
  objectArena := .source ⟨WordEnergy.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WordEnergy.arena ⟨WordEnergy.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize IntegerBound.signature IntegerBound.actual.readout IntegerBound.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def wordSupportAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_word_scalar_numerator_support) (Realization IntegerBound.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordSupportUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨WordSupport.arena⟩
  objectArena := .source ⟨WordSupport.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WordSupport.arena ⟨WordSupport.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize IntegerBound.signature IntegerBound.actual.readout IntegerBound.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def wordNumeratorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_actual_word_finite_scalar_numerator) (Realization WordNumerator.signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordNumeratorUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator.WordNumerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨WordNumerator.arena⟩
  objectArena := .source ⟨WordNumerator.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WordNumerator.arena ⟨WordNumerator.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WordNumerator.signature WordNumerator.actual.readout WordNumerator.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
