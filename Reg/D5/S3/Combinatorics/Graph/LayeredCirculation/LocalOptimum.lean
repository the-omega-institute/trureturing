import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
open Maths
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
noncomputable section

abbrev testSignature : Signature where
  Params := ℕ
  State n := ZMod n → Fin 5 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The source conjunction is preserved; both appearances of the optimum are
observations of the same real output. -/
def sourceProperty (n : ℕ) (hn : 5 ≤ n) (f : ZMod n → Fin 5 → ℝ) (value : ℝ) : Prop :=
  letI : NeZero n := ⟨by omega⟩
  IsGreatest {v : ℝ | ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p=v} value ∧
  IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} ∧
  {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}.Nonempty ∧
  (∀ p : ZMod n → Fin 5 → ℝ,
    (IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ=1) ∧ IsCirculation p)) ∧
  (∀ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p → HasPositiveCycleDecomposition p) ∧
  (∀ p : ZMod n → Fin 5 → ℝ, (∀ i σ, 0 ≤ p i σ) → IsCirculation p → p ≠ 0 →
    HasPositiveCycleErasure p) ∧
  (∀ m : ℕ, 1 ≤ m →
    IsGreatest {v : ℝ | ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧ wordScore f u=v}
      (traceValue (monodromy f ^ m))) ∧
  ∀ (m : ℕ), 1 ≤ m → ∀ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a),
    w.length=m*n → IsLocalLaw (walkLaw w) ∧
    localScore f (walkLaw w)=Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w/m ∧
    localScore f (walkLaw w) ≤ value

abbrev SourceStatement : Prop := ∀ (n : ℕ) (hn : 5 ≤ n) (f : ZMod n → Fin 5 → ℝ),
  sourceProperty n hn f (shortCycleOptimum f)

def actual : Realization testSignature :=
  realize testSignature (fun _ _ f => shortCycleOptimum f) (fun e => nomatch e)

def rejected : Realization testSignature :=
  realize testSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena where
  signature := testSignature
  Law r := ∀ n (hn : 5 ≤ n) f, sourceProperty n hn f (r.readout () n f)

private theorem sourceProof : SourceStatement := whole_theorem18_1

private theorem constant_optimum (n : ℕ) (hn : 5 ≤ n) (c : ℝ) :
    shortCycleOptimum (fun (_ : ZMod n) (_ : Fin 5) => c) = (n : ℝ)*c := by
  letI : NeZero n := ⟨by omega⟩
  have H := (sourceProof n hn (fun _ _ => c)).1
  obtain ⟨p,hp,hvalue⟩ := H.1
  have hs : localScore (fun _ _ => c) p=(n:ℝ)*c := by
    unfold localScore
    simp_rw [← Finset.mul_sum,hp.2.1]
    simp [nsmul_eq_mul,mul_comm]
  exact hvalue.symm.trans hs

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let f : ZMod 5 → Fin 5 → ℝ := fun _ _ => 1
  letI : NeZero 5 := inferInstance
  have H := (h 5 (by omega) f).1
  have A := (sourceProof 5 (by omega) f).1
  obtain ⟨p,hp,hvalue⟩ := A.1
  have hs : localScore f p=5 := by
    rw [hvalue]
    simpa only [f,Nat.cast_ofNat,mul_one] using constant_optimum 5 (by omega) 1
  have hb := H.2 ⟨p,hp,hs⟩
  norm_num [rejected,realize] at hb

theorem actual_dependence : ObservationalDependence testSignature actual := by
  intro ⟨⟩
  refine ⟨5,(fun _ _ => 0),(fun _ _ => 1),?_⟩
  change shortCycleOptimum (fun (_ : ZMod 5) (_ : Fin 5) => 0) ≠
    shortCycleOptimum (fun (_ : ZMod 5) (_ : Fin 5) => 1)
  rw [constant_optimum 5 (by omega) 0,constant_optimum 5 (by omega) 1]
  norm_num

def sourceRegistration : Registration sourceArena SourceStatement where
  actual := actual
  bridge := by
    constructor
    · intro h n hn f
      exact h n hn f
    · intro h n hn f
      exact h n hn f
  variation := ⟨(fun n hn f => sourceProof n hn f),rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@whole_theorem18_1) (type_of% actual) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize testSignature (fun _ _ f => shortCycleOptimum f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","body","arg","arg","arg","arg","arg","arg","arg","body","body","body","body","body","arg","arg","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
