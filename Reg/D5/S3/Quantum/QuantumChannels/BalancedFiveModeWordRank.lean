import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank
import Reg.Support.DependentFamily

open D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
open D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n k => decide (k = min (n + 1) 4)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Ring E] [Algebra ℂ E] [Module.Finite ℂ E]
    (f : ConfigMatrix →ₐ[ℂ] E) (hf : Function.Injective f)
    (a b c z w : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1)
    (hb : b ≠ 0) (hca : c ≠ 0) (ha : a ≠ 1) (hz : z ≠ 0) (hw : w ≠ 0) (n : ℕ),
    R.readout () n (finrank ℂ
      (wordSpace (z • f (reflection0 a b)) (w • f (reflection1 c)) n)) = true

private theorem actual_law : arena.{u}.Law actual := by
  intro E instR instA instF f hf a b c z w hn hc hb hca ha hz hw n
  simpa [actual, realize] using framed_balanced_word_rank f hf a b c z w
    hn hc hb hca ha hz hw n

private theorem source_bridge : (type_of% (@framed_balanced_word_rank.{u})) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h E instR instA instF f hf a b c z w hn hc hb hca ha hz hw n
    simpa [actual, realize] using h f hf a b c z w hn hc hb hca ha hz hw n
  · intro h E instR instA instF f hf a b c z w hn hc hb hca ha hz hw n
    simpa [actual, realize] using h f hf a b c z w hn hc hb hca ha hz hw n

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let f : ConfigMatrix →ₐ[ℂ] ULift.{u} ConfigMatrix :=
    (ULift.algEquiv (R := ℂ) (A := ConfigMatrix)).symm.toAlgHom
  have hc : (2 : ℂ) * (((1 / Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 1 := by
    norm_cast
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hh := h f (ULift.algEquiv (R := ℂ) (A := ConfigMatrix)).symm.injective
    0 1 (((1 / Real.sqrt 2 : ℝ) : ℂ)) 1 1 (by norm_num) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  simpa [rejected, realize] using hh

def familyRegistration : Registration arena.{u}
    (type_of% (@framed_balanced_word_rank.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    simp [actual, realize]

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@framed_balanced_word_rank.{u}) (type_of% actual) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank.framed_balanced_word_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n k => decide (k = min (n + 1) 4)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank
    definition := none
    coordinates := #[18]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#check source_bridge
#print axioms familyRegistration
#print axioms registration_1

end Reg.D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank
