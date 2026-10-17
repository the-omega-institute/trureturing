import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import Reg.Support.DependentFamily

/-! Source-bound audits of incomplete equiangular measurements and their product estimate. -/

namespace Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
open _root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
universe u_1

private def oneKet : Ket (Fin 1) := ⟨fun _ => 1, by simp⟩

private theorem proj_oneKet : proj oneKet = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  rw [proj_eq_outer]
  simp [oneKet, Matrix.vecMulVec]

private theorem scaledPure_one : ScaledPure (1 : Op 1) :=
  ⟨1, oneKet, by norm_num, by simp [proj_oneKet]⟩

private theorem scaledPure_zero : ScaledPure (0 : Op 1) :=
  ⟨0, oneKet, by norm_num, by simp⟩

private def oneKetProd : Ket (Fin 1 × Fin 1) := ⟨fun _ => 1, by simp⟩

private theorem schmidt_one : SchmidtNumberLE (proj oneKetProd) 1 := by
  refine ⟨1, fun _ => 1, fun _ => oneKetProd, by simp, by simp, ?_, by simp⟩
  intro k
  exact le_trans (Matrix.rank_le_card_width _) (by simp)

private def twoEAM : EAM 1 2 := by
  refine ⟨fun _ => oneKet, by norm_num, ?_, ?_⟩
  · simp [proj_oneKet, two_smul]
  · intro a b hab
    norm_num [oneKet, dotProduct]


namespace KetDot

abbrev signature : Signature where
  Params := Type u_1
  State p := p → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ _ v => star v) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [Fintype ι] (u : Ket ι),
    R.readout () ι u.vec ⬝ᵥ u.vec = 1

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let u : Ket (ULift.{u_1} Unit) := ⟨fun _ => 1, by simp⟩
  have he := h u
  change (∑ x, (0 : ℂ) * u.vec x) = 1 at he
  simp only [zero_mul, Finset.sum_const_zero] at he
  exact zero_ne_one he

def source_registration : Registration arena.{u_1} (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ket_dot_self.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_1}.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ket_dot_self.{u_1}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u_1} Unit, 0, 1, ?_⟩
    intro h
    have he := congrFun h ⟨()⟩
    change star (0 : ℂ) = star (1 : ℂ) at he
    exact zero_ne_one (by simpa only [star_zero, star_one] using he)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ket_dot_self.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.KetDot.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.KetDot.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ _ v => star v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end KetDot

namespace Outer

abbrev signature : Signature where
  Params := Type u_1
  State p := p → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ _ v => star v) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature.{u_1} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (u : Ket ι),
    proj u = vecMulVec u.vec (R.readout () ι u.vec)

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let u : Ket (ULift.{u_1} Unit) := ⟨fun _ => 1, by simp⟩
  have he := congrArg (fun M => M ⟨()⟩ ⟨()⟩) (h u)
  simp only [rejected, realize, proj_eq_outer, Matrix.vecMulVec, u] at he
  have he' : (1 : ℂ) * star (1 : ℂ) = 1 * 0 := he
  simp only [star_one, mul_one, mul_zero, one_ne_zero] at he'

def source_registration : Registration arena.{u_1} (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_eq_outer.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_1}.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_eq_outer.{u_1}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u_1} Unit, 0, 1, ?_⟩
    intro h
    have he := congrFun h ⟨()⟩
    change star (0 : ℂ) = star (1 : ℂ) at he
    exact zero_ne_one (by simpa only [star_zero, star_one] using he)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_eq_outer.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Outer.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Outer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ _ v => star v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Outer

namespace Hermitian

abbrev signature : Signature where
  Params := ℕ
  State _ := Star ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Op d → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d conjugation => @Matrix.IsHermitian ℂ (Fin d) conjugation) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {A : Op d} (_hA : ScaledPure A), R.readout () d (inferInstance : Star ℂ) A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h scaledPure_zero

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@scaledPure_hermitian), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let X : Op 1 := fun _ _ => Complex.I
    have hnot : ¬ X.IsHermitian := by
      intro h
      have he := congrArg (fun M : Op 1 => M 0 0) h.eq
      change star Complex.I = Complex.I at he
      have him := congrArg Complex.im he
      norm_num [Complex.star_def] at him
    have hyes : @Matrix.IsHermitian ℂ (Fin 1) ⟨id⟩ X := rfl
    refine ⟨1, (inferInstance : Star ℂ), ⟨id⟩, ?_⟩
    intro h
    have he := congrFun h X
    change X.IsHermitian = @Matrix.IsHermitian ℂ (Fin 1) ⟨id⟩ X at he
    exact hnot (Eq.mpr he hyes)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_hermitian) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Hermitian.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Hermitian.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d conjugation => @Matrix.IsHermitian ℂ (Fin d) conjugation) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Hermitian

namespace Sandwich

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {A : Op d} (_hA : ScaledPure A) (M : Op d),
    A * M * A = R.readout () d (M * A) • A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun M : Op 1 => M 0 0) (h scaledPure_one 0)
  norm_num [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_sandwich) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_sandwich), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.scaledPure_sandwich) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Sandwich.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Sandwich.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Sandwich

namespace Overlap

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (u v : Ket (Fin d)),
    R.readout () d (proj u * proj v) = (‖star u.vec ⬝ᵥ v.vec‖ ^ 2 : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h oneKet oneKet
  norm_num [rejected, realize, oneKet, dotProduct, Ket.apply] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_overlap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_overlap), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.proj_overlap) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Overlap.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Overlap.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Overlap

namespace SchmidtBound

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p β => p.2 + β * (p.1 : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d r : ℕ} {κ : Type u_1} [Fintype κ]
    (ρ : BipartiteOp d) (A B : κ → Op d) (α β : ℝ)
    (_hA : ∀ a, ScaledPure (A a)) (_hB : ∀ b, ScaledPure (B b))
    (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hMA : MomentBound A α β)
    (_hMB : MomentBound B α β) (_hρ : SchmidtNumberLE ρ r),
    traceNorm (correlation ρ A B) ≤ R.readout () ⟨r, α⟩ β

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let κ := ULift.{u_1} Empty
  let A : κ → Op 1 := fun k => nomatch k.down
  have hM : MomentBound A 0 0 := by intro H hH; simp [moment, A, κ]
  have he := h (proj oneKetProd) A A 0 0 (fun a => nomatch a.down)
    (fun a => nomatch a.down) le_rfl le_rfl hM hM schmidt_one
  have hn := traceNorm_nonneg (correlation (proj oneKetProd) A A)
  change traceNorm (correlation (proj oneKetProd) A A) ≤ -1 at he
  linarith

def source_registration : Registration arena.{u_1} (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.{u_1}.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment.{u_1}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment.{u_1}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.SchmidtBound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.SchmidtBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p β => p.2 + β * (p.1 : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[1, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SchmidtBound

namespace ProductTraceNorm

/-- The square-root Hilbert--Schmidt coordinate in the product estimate. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {κ : Type u_1} [Fintype κ] (R S : Matrix κ κ ℂ),
    traceNorm (R * S) ≤ r.readout () ()
      (_root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq R) *
      Real.sqrt
        (_root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq S)

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let κ := ULift.{u_1} Unit
  have he := h (1 : Matrix κ κ ℂ) 1
  have hn := traceNorm_nonneg (1 : Matrix κ κ ℂ)
  have hs : _root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq
      (1 : Matrix κ κ ℂ) = 1 := by
    simp [_root_.D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq]
  change _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
    ((1 : Matrix κ κ ℂ) * 1) ≤ -1 * Real.sqrt _ at he
  rw [Matrix.one_mul, hs, Real.sqrt_one, mul_one] at he
  linarith

def source_registration : Registration arena.{u_1}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨traceNorm_mul_le_hsSq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Real.sqrt 0 ≠ Real.sqrt 1
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq.{u_1})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ProductTraceNorm.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.ProductTraceNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ProductTraceNorm

namespace Bound

abbrev signature : Signature where
  Params := ℕ
  State p := Matrix (Fin p) (Fin p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d n r : ℕ), 1 ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : EAM d n) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      R.readout () n (Pn ρ A B) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + (r : ℝ) * ((n : ℝ) - (d : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 2 1 le_rfl le_rfl le_rfl twoEAM twoEAM (proj oneKetProd) schmidt_one
  norm_num [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.result), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    simp [actual, realize, D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Bound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.Bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
    definition := some { owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM, name := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.claim, path := #[] }
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Bound

end
end Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
