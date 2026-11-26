import D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
open _root_.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
noncomputable section

namespace FullResult
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℤ × ℕ × ℕ)
    (fun _ => PowerSeries (Polynomial ℚ)) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ p f => (coeff p.2.1 f).coeff p.2.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1/2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (n j : ℕ), ∃ z : ℤ,
    R.readout () (m,n,j) (exponentialSum m) = (z : ℚ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z,hz⟩ := h 0 0 0
  change (1/2 : ℚ) = (z : ℚ) at hz
  have hd := congrArg Rat.den hz
  norm_num at hd

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0,0,0), 0, 1, ?_⟩
    change (coeff 0 (0 : PowerSeries (Polynomial ℚ))).coeff 0 ≠
      (coeff 0 (1 : PowerSeries (Polynomial ℚ))).coeff 0
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.FullResult.unit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.FullResult.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
      name := `D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.claim
      path := #[] }
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FullResult

namespace PolynomialGhost
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Polynomial ℤ) (fun _ => Polynomial ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (p s t : ℕ), p.Prime →
    (p : Polynomial ℤ)^(s+1) ∣ R.readout () ()
      (ghost m (p*(p^s*t))-Polynomial.expand ℤ p (ghost m (p^s*t)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 2 0 0 (by norm_num)
  have hc := (Polynomial.C_dvd_iff_dvd_coeff (2 : ℤ) (1 : Polynomial ℤ)).mp
    (by simpa [rejected, realize] using hb) 0
  norm_num at hc

def family : Registration arena (type_of% @ghost_prime_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghost_prime_power, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Polynomial ℤ) ≠ 1
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    ghost_prime_power (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.PolynomialGhost.unit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.PolynomialGhost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialGhost

namespace Support
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun _ => PowerSeries (Polynomial ℚ)) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ p f => (coeff p.1 f).coeff p.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (n j : ℕ), n<j → R.readout () (n,j) (exponentialSum m) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 1 (by omega)
  change (1 : ℚ) = 0 at hb
  norm_num at hb

def family : Registration arena (type_of% @exponential_coefficient_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exponential_coefficient_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0,0), 0, 1, ?_⟩
    change (coeff 0 (0 : PowerSeries (Polynomial ℚ))).coeff 0 ≠
      (coeff 0 (1 : PowerSeries (Polynomial ℚ))).coeff 0
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    exponential_coefficient_support (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.Support.unit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Extraction
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun _ => PowerSeries ℚ) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ N f => coeff N f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ N f => coeff N f+1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (n j : ℕ), j≤n →
    R.readout () ((n+1)*n+j) (kronecker (n+1) (exponentialSum m)) =
      (coeff n (exponentialSum m)).coeff j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 0 (by omega)
  have he := kronecker_extract 0 0 0 (by omega)
  change coeff 0 (kronecker 1 (exponentialSum 0)) + 1 =
    (coeff 0 (exponentialSum 0)).coeff 0 at hb
  change coeff 0 (kronecker 1 (exponentialSum 0)) =
    (coeff 0 (exponentialSum 0)).coeff 0 at he
  linarith

def family : Registration arena (type_of% @kronecker_extract) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kronecker_extract, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change coeff 0 (0 : PowerSeries ℚ) ≠ coeff 0 (1 : PowerSeries ℚ)
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    kronecker_extract (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.Extraction.unit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality.Extraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extraction

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA155201BivariateIntegrality
