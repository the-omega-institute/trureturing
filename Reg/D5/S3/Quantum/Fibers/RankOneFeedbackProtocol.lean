import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix ComplexOrder
namespace Reg.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open _root_.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

structure Parameters where
  index : Type u
  finite : Fintype index
  decidable : DecidableEq index
  U : NNReal → Matrix index index ℂ
  zero : letI := finite; letI := decidable; U 0 = 1
  add : letI := finite; letI := decidable; ∀ t v, U (t + v) = U v * U t
  unitary : letI := finite; letI := decidable; ∀ t, (U t)ᴴ * U t = 1

abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Parameters.{u}
  State p := Matrix p.index p.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (P : Protocol p.index) → Record P → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.decidable
    exact fun P h => ludersLaw (unitaryMenu p.U p.zero p.add p.unitary) P X h)
  (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,u,0} where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    ∀ X Y : Matrix p.index p.index ℂ, X.PosSemidef → Y.PosSemidef →
      Matrix.trace X = Matrix.trace Y →
      sSup (Set.range (fun P : Protocol p.index =>
        totalVariation (R.readout () p X P) (R.readout () p Y P))) =
      sSup (Set.range (fun t : NNReal =>
        totalVariation (fun s => ((p.U t * X * (p.U t)ᴴ) s s).re)
          (fun s => ((p.U t * Y * (p.U t)ᴴ) s s).re)))

private theorem bridge : (type_of% (@actual_protocol_tv_supremum.{u})) ↔ (arena.{u}).Law (actual.{u}) := by
  constructor
  · intro h p
    letI := p.finite
    letI := p.decidable
    exact h p.U p.zero p.add p.unitary
  · intro h n finite decidable U hzero hadd hunitary X Y hX hY htrace
    exact h ⟨n,finite,decidable,U,hzero,hadd,hunitary⟩ X Y hX hY htrace

private theorem rejected_law : ¬ arena.Law (rejected.{u}) := by
  intro h
  let n := ULift.{u} (Fin 2)
  let a : n := ⟨0⟩
  let b : n := ⟨1⟩
  have hab : a ≠ b := by decide
  let p : Parameters := ⟨n, inferInstance, inferInstance, fun _ => 1,
    rfl, by intros; simp, by intros; simp⟩
  let X : Matrix n n ℂ := Matrix.single a a 1
  let Y : Matrix n n ℂ := Matrix.single b b 1
  have positive (s : n) : (Matrix.single s s (1 : ℂ)).PosSemidef := by
    have he : Matrix.single s s (1 : ℂ) = Matrix.diagonal (Pi.single s 1) := by
      ext i j
      by_cases hi : i = s <;> by_cases hj : j = s <;>
        simp [hi, hj, Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply] <;> aesop
    rw [he, Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases hi : i = s <;> simp [Pi.single_apply, hi]
  have hX : X.PosSemidef := positive a
  have hY : Y.PosSemidef := positive b
  have ht : Matrix.trace X = Matrix.trace Y := by simp [X,Y]
  have he := h p X Y hX hY ht
  letI : Nonempty (Protocol n) := ⟨.stop⟩
  simp only [arena, rejected, realize, totalVariation, p, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one, Pi.zero_apply, sub_self, abs_zero,
    Finset.sum_const_zero, mul_zero, Set.range_const, csSup_singleton] at he
  rw [← Equiv.ulift.symm.sum_comp (fun x : n => |(X x x).re - (Y x x).re|)] at he
  have h01 : (ULift.up (0 : Fin 2) : n) ≠ ULift.up (1 : Fin 2) := hab
  have h10 := Ne.symm h01
  norm_num [Fin.sum_univ_two, X, Y, Matrix.single_apply, a, b, h01, h10] at he

def family : Registration (arena.{u}) (type_of% (@actual_protocol_tv_supremum.{u})) where
  actual := actual
  bridge := bridge.{u}
  variation := ⟨bridge.{u}.mp (@actual_protocol_tv_supremum.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let n := ULift.{u} (Fin 1)
    let p : Parameters := ⟨n, inferInstance, inferInstance, fun _ => 1,
      rfl, by intros; simp, by intros; simp⟩
    refine ⟨p, 0, 1, ?_⟩
    intro h
    have he := congrArg (fun f => f .stop PUnit.unit) h
    change (Matrix.trace (0 : Matrix n n ℂ)).re = (Matrix.trace (1 : Matrix n n ℂ)).re at he
    norm_num [n] at he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.actual_protocol_tv_supremum.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p X => by
      letI := p.finite
      letI := p.decidable
      exact fun P h => ludersLaw (unitaryMenu p.U p.zero p.add p.unitary) P X h)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
