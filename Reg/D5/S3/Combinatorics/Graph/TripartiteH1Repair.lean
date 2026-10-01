import D5.S3.Combinatorics.Graph.TripartiteH1Repair
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair
open _root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev AParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ A : Type u, Σ B : Type v, Type w
abbrev ASig : Signature where
  Params := AParams.{u, v, w}
  State p := Potential p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.1 p.2.1 p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def aActual : Realization ASig.{u, v, w} :=
  realize ASig.{u, v, w} (fun _ _ g => d0 g) (fun e => nomatch e)
def aRejected : Realization ASig.{u, v, w} :=
  realize ASig.{u, v, w} (fun _ _ _ => 0) (fun e => nomatch e)

def aArena : Arena where
  signature := ASig.{u, v, w}
  Law r := ∀ {A : Type u} {B : Type v} {C : Type w} [Nonempty A] [Nonempty B] [Nonempty C]
    (f : Edge A B C),
    (∀ a b c, d1 f a b c = 0) ↔
      ∃ g : Potential A B C, r.readout () ⟨A, ⟨B, C⟩⟩ g = f

theorem aRejectedLaw : ¬ aArena.{u, v, w}.Law aRejected.{u, v, w} := by
  intro h
  let A := ULift.{u} Unit
  let B := ULift.{v} Unit
  let C := ULift.{w} Unit
  let f : Edge A B C := (fun _ _ => 1, fun _ _ => 1, fun _ _ => 0)
  have hz : ∀ a b c, d1 f a b c = 0 := by
    intro a b c
    simp [f, d1, CharTwo.add_self_eq_zero]
  obtain ⟨g, hg⟩ := (h f).mp hz
  have hv := congrArg (fun e : Edge A B C => e.1 (ULift.up ()) (ULift.up ())) hg
  simpa [aRejected, realize, f] using hv

theorem aDependence : ObservationalDependence ASig.{u, v, w} aActual.{u, v, w} := by
  intro i
  let A := ULift.{u} Unit
  let B := ULift.{v} Unit
  let C := ULift.{w} Unit
  let p : AParams := ⟨A, ⟨B, C⟩⟩
  let g0 : Potential A B C := (fun _ => 0, fun _ => 0, fun _ => 0)
  let g1 : Potential A B C := (fun _ => 1, fun _ => 0, fun _ => 0)
  refine ⟨p, g0, g1, ?_⟩
  intro h
  have hv := congrArg (fun e : Edge A B C => e.1 (ULift.up ()) (ULift.up ())) h
  simpa [aActual, realize, p, g0, g1, d0] using hv

def aRegistration : Registration aArena.{u, v, w} (aArena.{u, v, w}.Law aActual.{u, v, w}) where
  actual := aActual
  bridge := Iff.rfl
  variation := ⟨ker_d1_eq_im_d0, aRejected, aRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨aRejected, ?_, rfl, aRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := aDependence

register_information_theorem _root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0 in aArena
  readout via (realize ASig.{u, v, w} (fun _ _ g => d0 g) (fun e => nomatch e))
  realizes aRegistration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "fn", "arg", "fn"]
      functionOperand := true }]
  })
  escape continues (open)

abbrev BSig : Signature where
  Params := Unit
  State _ := BitEdge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def bActual : Realization BSig :=
  realize BSig (fun _ _ f => weight f) (fun e => nomatch e)
def bRejected : Realization BSig :=
  realize BSig (fun _ _ _ => 0) (fun e => nomatch e)

def bArena : Arena where
  signature := BSig
  Law r :=
    (∀ (f : BitEdge) (x : Cube),
      (∀ a b c, d1 f a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) →
      let w := cubePath x (antipode x)
      (∀ g : BitPotential, 3 ≤ weight (f + d0 g)) ∧
      (∃ g : BitPotential, f + d0 g = w) ∧
      (∀ a b, w.1 a b ≠ 0 ↔ a = !x.1 ∧ b = !x.2.1) ∧
      (∀ a c, w.2.1 a c ≠ 0 ↔ a = !x.1 ∧ c = x.2.2) ∧
      (∀ b c, w.2.2 b c ≠ 0 ↔ b = x.2.1 ∧ c = x.2.2) ∧
      (∀ a b c, d1 w a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) ∧
      weight w = 3 ∧ defects w = 2) ∧
    (∀ a b, witness.1 a b ≠ 0 ↔ a = false ∧ b = true) ∧
    (∀ a c, witness.2.1 a c ≠ 0 ↔ a = false ∧ c = false) ∧
    (∀ b c, witness.2.2 b c ≠ 0 ↔ b = false ∧ c = false) ∧
    (∀ a b c, d1 witness a b c ≠ 0 ↔
      (a, b, c) = (false, true, true) ∨
      (a, b, c) = (true, false, false)) ∧
    weight witness = 3 ∧ defects witness = 2 ∧
    (∀ g : BitPotential, 3 ≤ r.readout () () (witness + d0 g))

theorem bRejectedLaw : ¬ bArena.Law bRejected := by
  intro h
  have hf := h.2.2.2.2.2.2.2 (0 : BitPotential)
  simpa [bRejected, realize] using hf

theorem bDependence : ObservationalDependence BSig bActual := by
  intro i
  refine ⟨(), 0, witness, ?_⟩
  intro h
  have hw := congrArg id h
  simpa [bActual, realize, weight, witness] using hw

def bRegistration : Registration bArena (bArena.Law bActual) where
  actual := bActual
  bridge := Iff.rfl
  variation := ⟨sharp_three_edge_witness, bRejected, bRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bRejected, ?_, rfl, bRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := bDependence

register_information_theorem _root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness in bArena
  readout via (realize BSig (fun _ _ f => weight f) (fun e => nomatch e))
  realizes bRegistration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair
    coordinates := #[]
    readouts := #[{path := #["arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg"], stateOperand := some #["arg"]}]
  })
  escape continues (open)

abbrev CSig : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def cActual : Realization CSig := realize CSig (fun _ _ n => 3 * n) (fun e => nomatch e)
def cRejected : Realization CSig := realize CSig (fun _ _ _ => 0) (fun e => nomatch e)

def cArena : Arena where
  signature := CSig
  Law r := ∀ p q : Nat,
    (∀ f : BitEdge, ∃ g : BitPotential,
      q * weight (f + d0 g) ≤ p * defects f) ↔
      r.readout () () q ≤ 2 * p

theorem cRejectedLaw : ¬ cArena.Law cRejected := by
  intro h
  have hp := (h 0 1).mpr (by simp [cRejected, realize])
  have bad := (universal_repair 0 1).mp hp
  norm_num at bad

theorem cDependence : ObservationalDependence CSig cActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [cActual, realize]

def cRegistration : Registration cArena (cArena.Law cActual) where
  actual := cActual
  bridge := Iff.rfl
  variation := ⟨universal_repair, cRejected, cRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cRejected, ?_, rfl, cRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := cDependence

register_information_theorem _root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair in cArena
  readout via (realize CSig (fun _ _ n => 3 * n) (fun e => nomatch e))
  realizes cRegistration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair
    coordinates := #[]
    readouts := #[{path := #["body", "body", "arg", "fn", "arg"], stateOperand := some #["arg"]}]
  })
  escape continues (open)

#print axioms aRegistration
#print axioms bRegistration
#print axioms cRegistration
end Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair
