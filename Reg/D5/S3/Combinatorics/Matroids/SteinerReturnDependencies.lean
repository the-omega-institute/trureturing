import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
import Mathlib.Algebra.Module.ULift

/-! # Source registration for compatible Steiner circuit returns -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerReturnDependencies

open Function LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)

universe i u v

noncomputable section

abbrev sig :=
  signature (Sigma fun _ : Type u => Type v) (fun P => P.1 × P.2) (fun P => P.1 × P.2)

def actual : Realization sig.{u,v} :=
  realize sig (fun _ _ x => x) (fun a => nomatch a)

def rejected : Realization sig.{u, v} := by
  classical
  exact realize sig (fun _ P x =>
    (x.1, if h : ∃ a : P.2, a ≠ x.2 then Classical.choose h else x.2)) (fun a => nomatch a)

def law (R : Realization sig.{u,v}) : Prop :=
  ∀ {I : Type i} {L : Type u} {A : Type v} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q rep : I → L) (G : I → SimpleGraph L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_edges : ∀ i u v, (G i).Adj u v ↔ p i * u = v ∨ q i * u = v)
    (target : I → A),
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      (∀ x : L × A, (e, 0) * x = R.readout () ⟨L, A⟩ x) ∧
      (∀ x y : L × A, x * y = y * x) ∧
      (∀ x y : L × A, x * (x * y) = y) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      ∀ i x, (G i).Reachable (rep i) x → ∀ a : A,
        (fun y : L × A => (p i, 0) * ((q i, 0) * y))^[
          minimalPeriod (fun y => p i * (q i * y)) x] (x, a) = (x, a + target i)) ↔
      ∀ c : I →₀ ZMod 2,
        Finsupp.linearCombination (ZMod 2) (fun i => returnRow e (p i) (q i) (rep i)) c = 0 →
        Finsupp.linearCombination (ZMod 2) target c = 0

abbrev arena : Arena := ⟨sig, law.{i,u,v}⟩

private theorem rejected_law : ¬ law.{i,u,v} rejected := by
  classical
  intro h
  let I := PEmpty.{i+1}
  let L := PUnit.{u+1}
  let A := ULift.{v} (ZMod 2)
  let e : L := PUnit.unit
  letI : Mul L := ⟨fun x _ => x⟩
  let pivots : I → L := fun i => nomatch i
  let G : I → SimpleGraph L := fun i => nomatch i
  let target : I → A := fun i => nomatch i
  have unit (x : L) : e * x = x := Subsingleton.elim _ _
  have comm (x y : L) : x * y = y * x := Subsingleton.elim _ _
  have invol (x y : L) : x * (x * y) = y := Subsingleton.elim _ _
  have centre : Set.center L = {e} := by
    ext x
    have hx : x = e := Subsingleton.elim _ _
    subst x
    simp only [Set.mem_singleton_iff, iff_true]
    exact ⟨comm e, fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  have edges (i : I) (x y : L) : (G i).Adj x y ↔
      pivots i * x = y ∨ pivots i * x = y := nomatch i
  have compat (c : I →₀ ZMod 2) : Finsupp.linearCombination (ZMod 2) target c = 0 := by
    have empty : c = 0 := Finsupp.ext fun i => nomatch i
    rw [empty, map_zero]
  obtain ⟨labels, id, _⟩ :=
    (h (A := A) e pivots pivots pivots G unit comm invol centre edges target).mpr
      (fun c _ => compat c)
  have observed := congrArg Prod.snd (id (e, 0))
  have others : ∃ a : A, a ≠ 0 := by
    refine ⟨ULift.up 1, ?_⟩
    intro eq
    exact (show (1 : ZMod 2) ≠ 0 by decide) (congrArg ULift.down eq)
  letI := extensionMul e labels
  have zeroShift : ((e, (0 : A)) * (e, 0)).2 = 0 := by
    change 0 + 0 + _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.factor
      e labels e e = 0
    simp [_root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.factor]
  have changed : (rejected.readout () ⟨L, A⟩ (e, 0)).2 ≠ (0 : A) := by
    simp only [rejected, realize, dif_pos others]
    exact Classical.choose_spec others
  exact changed (observed.symm.trans zeroShift)

private theorem dependence : ObservationalDependence sig.{u,v} actual := by
  intro r
  refine ⟨⟨PUnit.{u+1}, ULift.{v} Bool⟩, (PUnit.unit, ULift.up false),
    (PUnit.unit, ULift.up true), ?_⟩
  intro eq
  exact Bool.noConfusion (congrArg (fun x => x.2.down) eq)

def source : Registration arena.{i,u,v} (type_of% (@realizesExactlyCompatibleReturns.{i,u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realizesExactlyCompatibleReturns, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@realizesExactlyCompatibleReturns.{i,u,v}) (Realization sig.{u,v}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerReturnDependencies.realizesExactlyCompatibleReturns.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerReturnDependencies.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "fn", "arg", "body", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
