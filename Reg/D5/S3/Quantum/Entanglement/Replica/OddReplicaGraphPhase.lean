import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
import Reg.D5.S3.Fourier.CharacterOrbitField

/-! A dependent readout of the literal contraction in the independent-coordinate identity. -/

namespace Reg.D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open _root_.D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open LeanInformationAudit Matrix
open scoped BigOperators
noncomputable section
universe u

structure Parameter where
  n : ℕ
  q : ℕ
  N : ℕ
  col : Fin N → Fin q
  nz : NeZero n

attribute [instance] Parameter.nz

abbrev signature : Signature where
  Params := Parameter
  State a := (Fin a.N → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun (_ : Unit) (a : Parameter) ψ => Z a.n a.q a.col ψ) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun (_ : Unit) (_ : Parameter) _ => (0 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ} (n : ℕ) [nz : NeZero n]
    (hn : 3 ≤ n) (ho : Odd n) (hq : 2 ≤ q)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hform : ψ = c • (tensorOp U *ᵥ graphAmp A))
    (hnorm : (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1),
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin (q - 1) → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    letI : Fintype O := Fintype.ofFinite O
    ∀ sec : O → G, (∀ a, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec a) = a) →
      let K := fun a : O => IntermediateField.adjoin (ZMod 2)
        (Set.range (fun i : Fin (q - 1) => ζ ^ (sec a i).val))
      letI : ∀ a : O, Fintype (K a) := fun a => Fintype.ofFinite (K a)
      letI : Fintype ((a : O) → Fin N → K a) := Fintype.ofFinite _
      ∃ e : (G → Fin N → ZMod 2) ≃ ((a : O) → Fin N → K a),
        (∀ x a u, (e x a u : F) =
          fourier ζ hζ.pow_eq_one (fun r => algebraMap (ZMod 2) F (x r u)) (sec a)) ∧
        R.readout () ⟨n, q, N, col, nz⟩ ψ = ((2 : ℂ) ^ (N * n ^ (q - 1)))⁻¹ *
          ∑ Y : (a : O) → Fin N → K a, complexSign (∑ a : O,
            Algebra.trace (ZMod 2) (K a)
              (orbitPhase ζ hζ.pow_eq_one A (displacement n col) (e.symm Y) (sec a)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  obtain ⟨ζ,hζ⟩ := Reg.D5.S3.Fourier.CharacterOrbitField.finite_root.{u}
  let F := ULift.{u} (GaloisField 2 2)
  let A : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0
  let U : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ := Fin.elim0
  have hU : ∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ := fun u => Fin.elim0 u
  have hform : (fun _ : Fin 0 → Fin 2 => (1 : ℂ)) =
      (1 : ℂ) • (tensorOp U *ᵥ graphAmp A) := by
    funext x
    simp [Matrix.mulVec, dotProduct, tensorOp, graphAmp, normalExponent, U]
  have hn : (∑ x : Fin 0 → Fin 2, ‖(1 : ℂ)‖ ^ 2) = 1 := by simp
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let G := Fin 1 → ZMod 3
  let p : Equiv.Perm G := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 3)).mulLeft)
  let O := Quotient (Equiv.Perm.SameCycle.setoid p)
  let sec : O → G := Quotient.out
  obtain ⟨e,_,hz⟩ := h (N := 0) (q := 2) 3 (by omega) (by decide) (by omega) F ζ hζ A
    Fin.elim0 (fun _ => 1) U 1 hU hform hn sec (fun a => Quotient.out_eq' a)
  have hpzero (a : O) (y : G → Fin 0 → ZMod 2) :
      orbitPhase ζ hζ.pow_eq_one A (displacement 3 (Fin.elim0 : Fin 0 → Fin 2)) y
        (sec a) = 0 := by
    apply Subtype.ext
    simp [orbitPhase, phaseComponent]
  have hh : (0 : ℂ) = 1 := by
    simpa [rejected, realize, hpzero, complexSign] using hz
  exact zero_ne_one hh

def registration : Registration arena.{u}
    (type_of% (@actual_graph_replica_independent_sum.{u})) := by
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@actual_graph_replica_independent_sum.{u}, rejected, rejected_law⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro e
        exact nomatch e
    dependence := ?_ }
  intro role
  let a : Parameter := ⟨3, 2, 0, Fin.elim0, inferInstance⟩
  refine ⟨a, (fun _ => 0), (fun _ => 1), ?_⟩
  change Z 3 2 Fin.elim0 (fun _ : Fin 0 → Fin 2 => 0) ≠
    Z 3 2 Fin.elim0 (fun _ : Fin 0 → Fin 2 => 1)
  simp [Z]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_graph_replica_independent_sum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase.actual_graph_replica_independent_sum.information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (a : Parameter) ψ => Z a.n a.q a.col ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
    definition := none
    coordinates := #[0, 1, 2, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.Replica.OddReplicaGraphPhase
