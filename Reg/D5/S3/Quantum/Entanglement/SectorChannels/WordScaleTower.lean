import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower
import Reg.Support.DependentFamily

/-! Actual-matrix dependent-family audit proof; §3.9 boundary: #25304. -/

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower
open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower
universe u

/-- The state and readout are the actual output matrices, with no truth flag. -/
abbrev signature : Signature where
  Params := Type u
  State := fun A => CStarMatrix A A ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ A => Matrix A A ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => fun _ _ => 1) (fun e => nomatch e)

/-- The entire source telescope is retained. Readouts replace only its actual
matrix conversion occurrences, leaving all physical channel predicates intact. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} [Fintype Sector] [DecidableEq Sector] (b : Sector → ℕ),
    (∀ (n j : ℕ) (h : j ≤ n),
      TensorRealization (localChannel b h) (localChannel b h) (jointChannel b h)) ∧
    (∀ (n j h : ℕ) (hjn : j ≤ n) (hhj : h ≤ j),
      (localChannel b hhj).comp (localChannel b hjn) = localChannel b (hhj.trans hjn)) ∧
    (∀ (n j h : ℕ) (hjn : j ≤ n) (hhj : h ≤ j),
      (jointChannel b hhj).comp (jointChannel b hjn) = jointChannel b (hhj.trans hjn)) ∧
    (∀ (n j : ℕ) (h : j ≤ n) (x z : Level b n) (c : ℂ),
      R.readout () (Level b j)
        ((localChannel b h).toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single x z c))) =
      if tail b h x = tail b h z then Matrix.single (keep b h x) (keep b h z) c else 0) ∧
    (∀ (n : ℕ) (X : Matrix (Level b n) (Level b n) ℂ),
      R.readout () (Level b n)
        ((localChannel b (le_refl n)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X) ∧
    (∀ (n : ℕ) (X : Matrix (Level b n × Level b n) (Level b n × Level b n) ℂ),
      R.readout () (Level b n × Level b n)
        ((jointChannel b (le_refl n)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X)

theorem actual_law : arena.{u}.Law actual := by
  intro Sector _ _ b
  exact result b

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let b : ULift.{u} Unit → ℕ := fun _ => 2
  let x : Level b 0 := ⟨⟨()⟩, ⟨0, by decide⟩⟩
  have hz := (h b).2.2.2.2.1 0 0
  have he := congrFun (congrFun hz x) x
  simpa [rejected, realize] using he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, CStarMatrix.ofMatrix (fun _ _ => 0),
    CStarMatrix.ofMatrix (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (⟨()⟩ : ULift.{u} Unit)) ⟨()⟩
  exact zero_ne_one he

theorem source_bridge :
    (type_of% (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower.result.{u})) ↔
      arena.{u}.Law actual := Iff.rfl

def registration : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower.result.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

/- The actual-matrix dependent-family proof above is a compiled audit attempt.
The Contract payload was rejected by discovery with rigid_universes, and its
sourceSelection was unfinished. Registration is not declared_validated.
The precise §3.9 delivery boundary is recorded in
https://github.com/the-omega-institute/trureturing/issues/25304 . -/

#print axioms actual_law
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.SectorChannels.WordScaleTower
