import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for rational row sums and their nonsquare obstruction. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum

namespace Rationality
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℚ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ c q => c = (q : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {R : ℕ} (S : Matrix (Fin R) (Fin R) ℚ), S.IsSymm →
    ∀ (p : Fin R → ℝ) (c : ℝ), c ≠ 0 →
    S.map ((↑) : ℚ → ℝ) *ᵥ p = c • (1 : Fin R → ℝ) →
    (∑ i, p i) = 1 → ∃ q : ℚ, T.readout () () c q
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq⟩ := h (R := 1) 1 Matrix.isSymm_one (fun _ => 1) 1 one_ne_zero
    (by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]) (by simp)
  exact hq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h10 : (1 : ℝ) = 0 := by
    have hh := congrFun he (0 : ℚ)
    simpa only [actual, realize, Rat.cast_zero] using
      hh.mp (by simp [actual, realize])
  exact one_ne_zero h10
def family : Registration arena (type_of% (@rational_row_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_row_sum, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_row_sum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum.rational_row_sum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum.Rationality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c q => c = (q : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Rationality

namespace Nonsquare
abbrev Vec (R : ℕ) := Fin R → ℝ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Vec (fun R => Vec R → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {R : ℕ} (S : Matrix (Fin R) (Fin R) ℚ), S.IsSymm →
    ∀ {k : ℕ}, ¬ IsSquare k → ∀ (p : Vec R), (∑ i, p i) = 1 →
      T.readout () R (S.map ((↑) : ℚ → ℝ) *ᵥ p)
        ((1 / Real.sqrt k) • (1 : Vec R))
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact h (R := 1) 0 Matrix.isSymm_zero (k := 2) Nat.prime_two.not_isSquare (fun _ => 1) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  have hn : (1 : Vec 1) ≠ 0 := by
    intro hz
    have h := congrFun hz 0
    norm_num at h
  exact (hh.mpr hn) rfl
def family : Registration arena (type_of% (@nonsquare_row_sum_ne)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonsquare_row_sum_ne, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonsquare_row_sum_ne) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum.nonsquare_row_sum_ne.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum.Nonsquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Nonsquare

end Reg.D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
