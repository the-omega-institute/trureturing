import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
import Mathlib.Algebra.Module.ULift
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap

open _root_.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => decide (2 ≤ t)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- The complete vector-system statement with the lower bound on the output size observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [AddCommGroup V] [Module ℝ V]
    (C : PreInnerProductSpace.Core ℝ V) {d t : ℕ}
    (_ht : R.readout () () t = true) (_hd : 2 * t < d) (h : V)
    (u v : Vertex d → Output d t → V) (δ : ℝ) (_hδ0 : 0 ≤ δ) (_hδ1 : δ ≤ 1)
    (_hh : C.inner h h = n d t) (_hu : ∀ σ A, C.inner h (u σ A) = 1)
    (_hv : ∀ τ B, C.inner h (v τ B) = 1)
    (_qu : ∀ σ A, C.inner (u σ A) (u σ A) ≤ 1)
    (_qv : ∀ τ B, C.inner (v τ B) (v τ B) ≤ 1)
    (_qsum : ∀ σ A A', A ≠ A' → C.inner (u σ A + u σ A') (u σ A + u σ A') ≤ 2)
    (_win : ∀ σ τ A B, Wins σ τ A B → C.inner (u σ A) (v τ B) = 1 - δ),
    kappa d t ≤ δ

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let C : PreInnerProductSpace.Core ℝ (ULift.{u} ℝ) := {
    inner := fun x y => x.down * y.down
    conj_inner_symm := by intro x y; simp [mul_comm]
    re_inner_nonneg := by intro x; exact mul_self_nonneg x.down
    add_left := by intro x y z; exact add_mul x.down y.down z.down
    smul_left := by intro x y r; change (r * x.down) * y.down = r * (x.down * y.down); ring }
  have unique : ∀ A : Output 1 0, A.val = ∅ := by
    intro A
    exact Finset.card_eq_zero.mp A.property
  have bad := law C (d := 1) (t := 0) rfl (by decide)
    (ULift.up 1) (fun _ _ => ULift.up 1) (fun _ _ => ULift.up 1) 0
    (by norm_num) (by norm_num)
    (by change (1 : ℝ) * 1 = n 1 0; norm_num [n])
    (by intros; change (1 : ℝ) * 1 = 1; norm_num)
    (by intros; change (1 : ℝ) * 1 = 1; norm_num)
    (by intros; change (1 : ℝ) * 1 ≤ 1; norm_num)
    (by intros; change (1 : ℝ) * 1 ≤ 1; norm_num)
    (by
      intro σ A A' different
      exact (different (Subtype.ext ((unique A).trans (unique A').symm))).elim)
    (by intros; change (1 : ℝ) * 1 = 1 - 0; norm_num)
  norm_num [kappa, n] at bad

def evidence : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap.vector_system_gap.{u})) where
  actual := actual
  bridge := by
    constructor
    · intro source V _ _ C d t ht hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win
      exact source C (of_decide_eq_true ht) hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win
    · intro law V _ _ C d t ht hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win
      exact law C (decide_eq_true ht) hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win
  variation := ⟨by
    intro V _ _ C d t ht hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win
    exact vector_system_gap C (of_decide_eq_true ht) hd h u v δ hδ0 hδ1 hh hu hv qu qv qsum win,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 2, by change false ≠ true; decide⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap.vector_system_gap.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap.vector_system_gap
    "Reg.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap/\
    Reg.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
