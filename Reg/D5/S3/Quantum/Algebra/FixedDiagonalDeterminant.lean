import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
import Mathlib.Algebra.Field.ULift

/-! Complete source reconstruction from the fixed coefficient matrix readout. -/

set_option autoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant

namespace Reg.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
universe u v

structure Parameters where
  k : Type u
  I : Type v
  [field : Field k]
  [finite : Fintype I]
  [decidable : DecidableEq I]
  [nontrivial : Nontrivial I]

attribute [instance] Parameters.field Parameters.finite Parameters.decidable Parameters.nontrivial

abbrev signature : Signature where
  Params := Parameters.{u, v}
  State p := Matrix p.I p.I p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.I p.I p.k
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} := realize signature
  (fun _ _ N => N) (fun e => nomatch e)

def conclusion (p : Parameters.{u, v}) (N observed : Matrix p.I p.I p.k) : Prop :=
  (∀ i j, Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) →
    Irreducible (rowMatrix observed).det

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ (p : Parameters.{u, v}) (N : signature.State p), conclusion p N (R.readout () p N)

theorem full_telescope_bridge :
    (type_of% (@row_determinant_irreducible.{u, v})) ↔ arena.{u, v}.Law actual := by
  constructor
  · intro h p N hN
    exact @h p.k p.I p.field p.finite p.decidable p.nontrivial N hN
  · intro h k I fieldInst finiteInst decidableInst nontrivialInst N hN
    let p : Parameters := {
      k := k
      I := I
      field := fieldInst
      finite := finiteInst
      decidable := decidableInst
      nontrivial := nontrivialInst }
    exact h p N hN

def rejected : Realization signature.{u, v} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

private def probe : Parameters.{u, v} where
  k := ULift.{u} ℚ
  I := ULift.{v} (Fin 2)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro law
  have h := law probe (fun _ _ => 1)
    (fun _ _ => Relation.ReflTransGen.single one_ne_zero)
  change Irreducible (rowMatrix (0 : Matrix probe.I probe.I probe.k)).det at h
  simpa [rowMatrix] using h

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  refine ⟨probe, 0, 1, ?_⟩
  change (0 : Matrix probe.I probe.I probe.k) ≠ 1
  exact zero_ne_one

def source_registration : Registration arena.{u, v}
    (type_of% (@row_determinant_irreducible.{u, v})) where
  actual := actual
  bridge := full_telescope_bridge
  variation := ⟨full_telescope_bridge.mp (@row_determinant_irreducible.{u, v}),
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def diagonalConclusion (p : Parameters.{u, v}) (N observed : Matrix p.I p.I p.k) : Prop :=
  (∀ i j, Relation.ReflTransGen (fun a b => N a b ≠ 0) i j) →
    Irreducible (diagonalMatrix observed).det

abbrev diagonalArena : Arena where
  signature := signature.{u, v}
  Law R := ∀ (p : Parameters.{u, v}) (N : signature.State p),
    diagonalConclusion p N (R.readout () p N)

theorem diagonal_full_telescope_bridge :
    (type_of% (@diagonal_determinant_irreducible.{u, v})) ↔
      diagonalArena.{u, v}.Law actual := by
  constructor
  · intro h p N hN
    exact @h p.k p.I p.field p.finite p.decidable p.nontrivial N hN
  · intro h k I fieldInst finiteInst decidableInst nontrivialInst N hN
    let p : Parameters := {
      k := k
      I := I
      field := fieldInst
      finite := finiteInst
      decidable := decidableInst
      nontrivial := nontrivialInst }
    exact h p N hN

theorem diagonal_rejected_law : ¬ diagonalArena.{u, v}.Law rejected := by
  intro law
  have h := law probe (fun _ _ => 1)
    (fun _ _ => Relation.ReflTransGen.single one_ne_zero)
  change Irreducible (diagonalMatrix (0 : Matrix probe.I probe.I probe.k)).det at h
  have hp : (∏ i : probe.I, MvPolynomial.X i : MvPolynomial probe.I probe.k) =
      MvPolynomial.X (ULift.up (0 : Fin 2)) * MvPolynomial.X (ULift.up (1 : Fin 2)) := by
    calc
      _ = ∏ j : Fin 2, (MvPolynomial.X (ULift.up j) : MvPolynomial probe.I probe.k) :=
        Fintype.prod_equiv (Equiv.ulift : probe.I ≃ Fin 2) _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fin.prod_univ_two]
        rfl
  have hd : (diagonalMatrix (0 : Matrix probe.I probe.I probe.k)).det =
      MvPolynomial.X (ULift.up (0 : Fin 2)) * MvPolynomial.X (ULift.up (1 : Fin 2)) := by
    simpa [diagonalMatrix, Matrix.det_diagonal] using hp
  have hn (i : probe.I) : ¬ IsUnit (MvPolynomial.X i : MvPolynomial probe.I probe.k) := by
    intro hu
    have hh := hu.map (MvPolynomial.eval (fun _ => (0 : probe.k)))
    simpa using hh
  rcases h.isUnit_or_isUnit hd with hi | hj
  · exact hn _ hi
  · exact hn _ hj

def diagonal_source_registration : Registration diagonalArena.{u, v}
    (type_of% (@diagonal_determinant_irreducible.{u, v})) where
  actual := actual
  bridge := diagonal_full_telescope_bridge
  variation := ⟨diagonal_full_telescope_bridge.mp (@diagonal_determinant_irreducible.{u, v}),
    rejected, diagonal_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, diagonal_rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

universe w

structure ReciprocalParameters where
  k : Type u
  I : Type v
  A : Type w
  [field : Field k]
  [finite : Fintype I]
  [decidable : DecidableEq I]
  [ring : CommRing A]
  f : k →+* A
  x : I → Aˣ

attribute [instance] ReciprocalParameters.field ReciprocalParameters.finite
  ReciprocalParameters.decidable ReciprocalParameters.ring

abbrev reciprocalSignature : Signature where
  Params := ReciprocalParameters.{u, v, w}
  State p := Matrix p.I p.I p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.I p.I p.k
  Anchor := Empty
  finiteAnchor := inferInstance

def reciprocalActual : Realization reciprocalSignature.{u, v, w} := realize reciprocalSignature
  (fun _ _ N => N) (fun e => nomatch e)

def reciprocalConclusion (p : ReciprocalParameters.{u, v, w})
    (N observed : Matrix p.I p.I p.k) : Prop :=
  MvPolynomial.eval₂Hom p.f (fun i => (p.x i : p.A)) (rowMatrix observed).det =
    (∏ i, (p.x i : p.A)) *
      MvPolynomial.eval₂Hom p.f (fun i => ((p.x i)⁻¹ : p.Aˣ)) (diagonalMatrix N).det

abbrev reciprocalArena : Arena where
  signature := reciprocalSignature.{u, v, w}
  Law R := ∀ (p : ReciprocalParameters.{u, v, w}) (N : reciprocalSignature.State p),
    reciprocalConclusion p N (R.readout () p N)

theorem reciprocal_full_telescope_bridge :
    (type_of% (@reciprocal_determinant.{u, v, w})) ↔
      reciprocalArena.{u, v, w}.Law reciprocalActual := by
  constructor
  · intro h p N
    exact @h p.k p.I p.field p.finite p.decidable p.A p.ring p.f p.x N
  · intro h k I fieldInst finiteInst decidableInst A ringInst f x N
    let p : ReciprocalParameters := {
      k := k
      I := I
      A := A
      field := fieldInst
      finite := finiteInst
      decidable := decidableInst
      ring := ringInst
      f := f
      x := x }
    exact h p N

end Reg.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant
