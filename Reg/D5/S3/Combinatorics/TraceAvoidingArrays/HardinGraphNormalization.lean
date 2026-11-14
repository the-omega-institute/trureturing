import D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open LeanInformationAudit
noncomputable section

namespace Scanner
abbrev Input := Σ n : ℕ, Fin (n + 1) → Fin 6
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal x.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n (f : Fin (n + 1) → Fin 6),
    R.readout () () ⟨n, f⟩ ↔ Ordered (beta ∘ f) ∧
      ∀ i, First (beta ∘ f) i → (f i).val = (beta (f i)).val

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal (fun _ : Fin 1 => (0 : Fin 6)) := by
    simp [_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal, _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good,
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed]
  exact ((h 0 (fun _ => 0)).mpr ((_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.normal_iff _).mp hn))

def family : Registration arena (type_of% @_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.normal_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro n f; exact _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.normal_iff f, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ⟨0, fun _ => 0⟩, ⟨0, fun _ => 1⟩, ?_⟩
    change _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal (fun _ : Fin 1 => (0 : Fin 6)) ≠ _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal (fun _ : Fin 1 => (1 : Fin 6))
    simp [_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Normal, _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good,
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed]
end Scanner

namespace Fibers
abbrev Input := Σ n : ℕ, Σ G : SimpleGraph (Fin (n + 1)),
  {p : G.Coloring (Fin 3) // Ordered (p : Fin (n + 1) → Fin 3)}
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Nat.card (GraphFiber x.2.1 x.2.2.val)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => Nat.card (GraphFiber x.2.1 x.2.2.val) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n (G : SimpleGraph (Fin (n + 1))) (p : G.Coloring (Fin 3))
    (hp : Ordered (p : Fin (n + 1) → Fin 3)),
    R.readout () () ⟨n, G, p, hp⟩ =
      2 ^ (n + 1 - Fintype.card (Set.range (p : Fin (n + 1) → Fin 3)))
def constant (n : ℕ) : (⊥ : SimpleGraph (Fin (n + 1))).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun _ => 0) (by simp)
private theorem constant_ordered (n : ℕ) : Ordered (constant n : Fin (n + 1) → Fin 3) := by
  simp [Ordered, constant, SimpleGraph.Coloring.mk]
private theorem constant_count (n : ℕ) :
    Nat.card (GraphFiber ⊥ (constant n)) = 2 ^ n := by
  have h := result ⊥ (constant n) (constant_ordered n)
  simpa [constant, SimpleGraph.Coloring.mk] using h
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 ⊥ (constant 0) (constant_ordered 0)
  have ha := result ⊥ (constant 0) (constant_ordered 0)
  change Nat.card (GraphFiber ⊥ (constant 0)) + 1 = _ at hb
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro n G p hp; exact result G p hp, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ⟨0, ⊥, constant 0, constant_ordered 0⟩,
      ⟨1, ⊥, constant 1, constant_ordered 1⟩, ?_⟩
    change Nat.card (GraphFiber ⊥ (constant 0)) ≠ Nat.card (GraphFiber ⊥ (constant 1))
    rw [constant_count, constant_count]
    decide
end Fibers

/-- Typed family evidence; exact raw source selection remains unspecified. -/
def scannerAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.normal_iff) (Realization Scanner.signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.scannerUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Scanner.family
  realizationSource := none
  generated := false
  arena := .source ⟨Scanner.arena⟩
  objectArena := .source ⟨Scanner.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Scanner.arena ⟨Scanner.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some Scanner.actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- Typed family evidence; exact raw source selection remains unspecified. -/
def fibersAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization Fibers.signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.fibersUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Fibers.family
  realizationSource := none
  generated := false
  arena := .source ⟨Fibers.arena⟩
  objectArena := .source ⟨Fibers.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Fibers.arena ⟨Fibers.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some Fibers.actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scannerAudit
#print axioms fibersAudit
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
