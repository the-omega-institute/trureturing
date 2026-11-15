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
namespace Connected
abbrev Input := Σ n : ℕ, SimpleGraph (Fin (n+1))
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => ℕ × ℕ × ℕ × ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ x =>
    (Nat.card (x.2.Coloring (Fin 1)), Nat.card (x.2.Coloring (Fin 2)),
      Nat.card (Legal x.2), Nat.card (x.2.Coloring (Fin 3)))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1,0,0,0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n (G : SimpleGraph (Fin (n+1))), G.Preconnected → G.Colorable 2 →
    (∃ u v, G.Adj u v) →
    (R.readout () () ⟨n,G⟩).1 = 0 ∧ (R.readout () () ⟨n,G⟩).2.1 = 2 ∧
      48 * (R.readout () () ⟨n,G⟩).2.2.1 =
        2^(n+1) * ((R.readout () () ⟨n,G⟩).2.2.2 + 6)
private theorem top_two_colorable : (⊤ : SimpleGraph (Fin 2)).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk id (by intro a b hab; exact hab)⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 ⊤ SimpleGraph.preconnected_top top_two_colorable
    ⟨0,1,by decide⟩).1
  change (1 : ℕ) = 0 at hh
  omega
private theorem one_empty : Nat.card ((⊥ : SimpleGraph (Fin 1)).Coloring (Fin 1)) = 1 := by
  let e : (⊥ : SimpleGraph (Fin 1)).Coloring (Fin 1) ≃ (Fin 1 → Fin 1) :=
    { toFun := fun p => p
      invFun := fun f => SimpleGraph.Coloring.mk f (by simp)
      left_inv := fun p => DFunLike.ext _ _ (fun _ => rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  simp
private theorem one_top : Nat.card ((⊤ : SimpleGraph (Fin 2)).Coloring (Fin 1)) = 0 :=
  (connected_count ⊤ SimpleGraph.preconnected_top top_two_colorable ⟨0,1,by decide⟩).1

def family : Registration arena (type_of% @connected_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro n G hG hc he; exact connected_count G hG hc he, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),⟨0,⊥⟩,⟨1,⊤⟩,?_⟩
    intro he
    have h := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.1) he
    change Nat.card ((⊥ : SimpleGraph (Fin 1)).Coloring (Fin 1)) =
      Nat.card ((⊤ : SimpleGraph (Fin 2)).Coloring (Fin 1)) at h
    rw [one_empty,one_top] at h
    omega

/-- Exact family evidence; the four raw count occurrences have no claimed source selection. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@connected_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Connected.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Connected.family
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
end Connected

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization
