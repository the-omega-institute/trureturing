import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HereditaryFlip.Median

/-! Source-family observations for native metric median reconstruction and flagness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Median

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
open _root_.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
open _root_.D5.S3.Combinatorics.Graph.HereditaryFlip.Median
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev FamilyData := Σ V : Type u, DecidableEq V × Set (Finset V)
abbrev Vertex (p : FamilyData.{u}) := {S : Finset p.1 // S ∈ p.2.2}
abbrev ReconstructionParams := Σ p : FamilyData.{u}, Vertex p × Vertex p × Vertex p

abbrev reconstructionSignature : Signature where
  Params := ReconstructionParams.{u}
  State p := Vertex p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.1.1
  Anchor := Empty
  finiteAnchor := inferInstance

def reconstructionActual : Realization reconstructionSignature.{u} :=
  realize reconstructionSignature (fun _ p C => letI : DecidableEq p.1.1 := p.1.2.1;
    majority p.2.1.val p.2.2.1.val C.val) (fun e => nomatch e)

def reconstructionRejected : Realization reconstructionSignature.{u} :=
  realize reconstructionSignature (fun _ _ C => C.val) (fun e => nomatch e)

abbrev reconstructionArena : Arena where
  signature := reconstructionSignature.{u}
  Law R := ∀ p : ReconstructionParams.{u}, IsLowerSet p.1.2.2 →
    ∀ C : Vertex p.1, letI : DecidableEq p.1.1 := p.1.2.1;
      IsMedian (flipGraph p.1.2.2) p.2.1 p.2.2.1 C p.2.2.2 ↔
        p.2.2.2.val = R.readout () p C

def base : FamilyData.{u} := ⟨ULift.{u} Bool, Classical.decEq _, Set.univ⟩
def zero : Vertex base.{u} := ⟨∅, Set.mem_univ _⟩
def one : Vertex base.{u} := ⟨{ULift.up false}, Set.mem_univ _⟩

private theorem reconstructionBad : ¬ reconstructionArena.{u}.Law reconstructionRejected := by
  intro h
  have hm := (@is_median_iff base.1 base.2.1 base.2.2 isLowerSet_univ
    zero zero one zero).mpr (by simp [zero, one, majority])
  have hh := (h ⟨base, zero, zero, zero⟩ isLowerSet_univ one).mp hm
  have hc := congrArg Finset.card hh
  change (0 : ℕ) = 1 at hc
  exact Nat.zero_ne_one hc

def reconstructionFamily :
    Registration reconstructionArena.{u} (type_of% (@is_median_iff.{u})) where
  actual := reconstructionActual
  bridge := by
    constructor
    · intro h p hf C
      exact @h p.1.1 p.1.2.1 p.1.2.2 hf p.2.1 p.2.2.1 C p.2.2.2
    · intro h V inst K hf A B C M
      exact h ⟨⟨V, inst, K⟩, A, B, M⟩ hf C
  variation := ⟨fun p hf C => @is_median_iff p.1.1 p.1.2.1 p.1.2.2 hf
    p.2.1 p.2.2.1 C p.2.2.2, reconstructionRejected, reconstructionBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨reconstructionRejected, ?_, rfl, reconstructionBad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨base, one, zero, zero⟩, zero, one, ?_⟩
    change majority one.val zero.val zero.val ≠ majority one.val zero.val one.val
    simp [zero, one, majority]

abbrev CarrierData := Σ V : Type u, DecidableEq V

abbrev flagSignature : Signature where
  Params := CarrierData.{u}
  State p := Set (Finset p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def flagActual : Realization flagSignature.{u} :=
  realize flagSignature (fun _ _ K => Flag K) (fun e => nomatch e)

def flagRejected : Realization flagSignature.{u} :=
  realize flagSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev flagArena : Arena where
  signature := flagSignature.{u}
  Law R := ∀ (p : CarrierData.{u}) (K : Set (Finset p.1)), IsLowerSet K →
    letI : DecidableEq p.1 := p.2;
      IsMedianGraph (flipGraph K) ↔ ∅ ∈ K ∧ R.readout () p K

private theorem flagBad : ¬ flagArena.{u}.Law flagRejected := by
  intro h
  have hc := (@median_graph_iff_flag base.1 base.2.1 base.2.2 isLowerSet_univ).mpr
    ⟨Set.mem_univ _, fun _ _ => trivial⟩
  exact ((h ⟨base.1, base.2.1⟩ base.2.2 isLowerSet_univ).mp hc).2

private theorem triangle_not_flag :
    ¬ Flag {S : Finset (ULift.{u} (Fin 3)) | S.card ≤ 2} := by
  intro h
  have ht := h {⟨0⟩, ⟨1⟩, ⟨2⟩} (fun _ _ hc => hc)
  have hc : ({⟨0⟩, ⟨1⟩, ⟨2⟩} : Finset (ULift.{u} (Fin 3))).card = 3 := by decide
  change _ ≤ 2 at ht
  omega

def flagFamily : Registration flagArena.{u} (type_of% (@median_graph_iff_flag.{u})) where
  actual := flagActual
  bridge := by
    constructor
    · intro h p K hf
      exact @h p.1 p.2 K hf
    · intro h V inst K hf
      exact h ⟨V, inst⟩ K hf
  variation := ⟨fun p K hf => @median_graph_iff_flag p.1 p.2 K hf, flagRejected, flagBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨flagRejected, ?_, rfl, flagBad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 3), Classical.decEq _⟩, Set.univ, {S | S.card ≤ 2}, ?_⟩
    intro heq
    have ht : Flag (Set.univ : Set (Finset (ULift.{u} (Fin 3)))) := fun _ _ => trivial
    exact triangle_not_flag (Eq.mp heq ht)

noncomputable def reconstructionRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, u, 0, 0}
      (@is_median_iff.{u}) (Realization reconstructionSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Median.is_median_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Median.reconstructionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨reconstructionArena⟩
  objectArena := .source ⟨reconstructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reconstructionArena ⟨reconstructionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize reconstructionSignature
    (fun _ p C => letI : DecidableEq p.1.1 := p.1.2.1;
      majority p.2.1.val p.2.2.1.val C.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Median
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def flagRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@median_graph_iff_flag.{u}) (Realization flagSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Median.median_graph_iff_flag.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Median.flagFamily
  realizationSource := none
  generated := false
  arena := .source ⟨flagArena⟩
  objectArena := .source ⟨flagArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source flagArena ⟨flagFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize flagSignature (fun _ _ K => Flag K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Median
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Median
