import D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient

noncomputable section

abbrev signature : Signature where
  Params := Σ _d : ℕ, Σ _k : ℤ, ℤ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => AddSubgroup (ℤ × ℤ × ℤ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p c => triangularLattice c p.1 p.2.1 p.2.2)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : ℕ) (k v : ℤ)
    (hc : 0 < c) (hd : 0 < d) (hv : v = 1 ∨ v = -1),
    Nonempty (((ℤ × ℤ × ℤ) ⧸ R.readout () ⟨d, k, v⟩ c) ≃+
      ZMod c × ZMod d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hex := h 2 1 0 1 (by omega) (by omega) (Or.inl rfl)
  change Nonempty (((ℤ × ℤ × ℤ) ⧸
    (⊤ : AddSubgroup (ℤ × ℤ × ℤ))) ≃+ ZMod 2 × ZMod 1) at hex
  obtain ⟨e⟩ := hex
  haveI : Subsingleton
      ((ℤ × ℤ × ℤ) ⧸ (⊤ : AddSubgroup (ℤ × ℤ × ℤ))) :=
    QuotientAddGroup.subsingleton_quotient_top
  have heq : (0 : ZMod 2 × ZMod 1) = (1, 0) := by
    apply e.symm.injective
    exact Subsingleton.elim _ _
  have hne : (0 : ZMod 2 × ZMod 1) ≠ (1, 0) := by decide
  exact hne heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨triangular_lattice_quotient, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 0, 1⟩, 1, 2, ?_⟩
    change triangularLattice 1 1 0 1 ≠ triangularLattice 2 1 0 1
    intro heq
    have hm : ((0, 1, 0) : ℤ × ℤ × ℤ) ∈ triangularLattice 1 1 0 1 := by
      refine ⟨0, 1, 0, ?_⟩
      ext <;> norm_num
    rw [heq] at hm
    obtain ⟨a, b, t, ht⟩ := hm
    have hmiddle := congrArg (fun x : ℤ × ℤ × ℤ => x.2.1) ht
    norm_num at hmiddle
    omega

register_information_theorem triangular_lattice_quotient in arena
  readout via (realize signature
    (fun _ p c => triangularLattice c p.1 p.2.1 p.2.2)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := Array.replicate 7 "body" ++
        #["arg", "fn", "fn", "fn", "arg", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "fn", "fn", "arg"] }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``triangular_lattice_quotient)
    | throwError "cubic coordinate quotient registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "cubic coordinate quotient registration is unresolved: {diagnostic}"
  | .undeclared => throwError "cubic coordinate quotient registration is undeclared"

end
end Reg.D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient
