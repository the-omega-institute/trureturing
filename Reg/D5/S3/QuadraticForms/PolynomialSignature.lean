import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.PolynomialSignature
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ActualSignature
open _root_.D5.S3.QuadraticForms.PolynomialSignature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.PolynomialSignature

noncomputable section
universe u

def signature_family : Signature where
  Params := Σ σ : Type u, Σ n : ℕ, Mat (Poly σ) n
  State := fun p => p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature_family.{u} := realize signature_family
  (fun _ p x => signature (Matrix.toQuadraticForm'
    (fun i j => MvPolynomial.eval x (p.2.2 i j)))) (fun e => nomatch e)

def rejected : Realization signature_family.{u} := realize signature_family
  (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature_family.{u}
  Law R := ∀ {σ : Type u} (n : ℕ) (A : Mat (Poly σ) n) (z : ℤ) (x : σ → ℝ)
    (_hs : ∀ i j, MvPolynomial.eval x (A i j) = MvPolynomial.eval x (A j i)),
    holds x (compile n A z) ↔ R.readout () ⟨σ, n, A⟩ x = z

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨compile_iff_signature, rejected, ?_⟩
    intro h
    have hh := (h 0 (0 : Mat (Poly (ULift.{u} Unit)) 0) 0 (fun _ => 0)
      (by simp)).mp (by simp [compile, truth, holds])
    change (1 : ℤ) = 0 at hh
    exact one_ne_zero hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hh := (h 0 (0 : Mat (Poly (ULift.{u} Unit)) 0) 0 (fun _ => 0)
          (by simp)).mp (by simp [compile, truth, holds])
        change (1 : ℤ) = 0 at hh
        exact one_ne_zero hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let A : Mat (Poly (ULift.{u} Unit)) 1 := fun _ _ => MvPolynomial.X ⟨()⟩
    refine ⟨⟨ULift.{u} Unit, 1, A⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change signature (Matrix.toQuadraticForm'
      (fun r s => MvPolynomial.eval (fun _ => (0 : ℝ)) (A r s))) ≠
      signature (Matrix.toQuadraticForm'
        (fun r s => MvPolynomial.eval (fun _ => (1 : ℝ)) (A r s)))
    simp only [A, MvPolynomial.eval_X]
    have hz : signature (Matrix.toQuadraticForm' (fun _ _ : Fin 1 => (0 : ℝ))) = 0 :=
      (realizes_iff_signature 1 _ (by simp) 0).mp (by
        exact Or.inl ⟨by simp, rfl⟩)
    have ho : signature (Matrix.toQuadraticForm' (fun _ _ : Fin 1 => (1 : ℝ))) = 1 :=
      (realizes_iff_signature 1 _ (by simp) 1).mp (by
        refine Or.inr (Or.inl ⟨0, Or.inl ⟨by norm_num, ?_⟩⟩)
        norm_num [Realizes])
    rw [hz, ho]
    norm_num

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature_family.{u_1}
    (fun _ p x => signature.{0} (Matrix.toQuadraticForm'.{0, 0}
      (fun i j => MvPolynomial.eval.{0, u_1} x (p.2.2 i j)))) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "QuadraticForms") "PolynomialSignature") "compile_iff_signature") "Reg.D5.S3.QuadraticForms.PolynomialSignature/Reg.D5.S3.QuadraticForms.PolynomialSignature.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature_family.{u_1}
    (fun _ p x => signature.{0} (Matrix.toQuadraticForm'.{0, 0}
      (fun i j => MvPolynomial.eval.{0, u_1} x (p.2.2 i j)))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.QuadraticForms.PolynomialSignature, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.QuadraticForms.PolynomialSignature, declaration := `D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalArenaFact, `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.sourceBridgeFact, `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.observationFact0, `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.anchorEnumeration }


end
end Reg.D5.S3.QuadraticForms.PolynomialSignature


noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.QuadraticForms.PolynomialSignature.arena.{u_1}
noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S3.QuadraticForms.PolynomialSignature.arena.{u_1}
noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0} (Reg.D5.S3.QuadraticForms.PolynomialSignature.arena.) (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).actual

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"compile_iff_signature\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.QuadraticForms.PolynomialSignature, declaration := `D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.observation0.{u_1} : {σ : Type u_1} →
  (n : Nat) →
    (A : D5.S3.QuadraticForms.ActualSignature.Mat.{u_1} (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n) →
      (z : Int) →
        (x : σ → Real) →
          (hs :
              ∀ (i j : Fin n),
                @Eq.{1} Real
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
                    (@RingHom.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
                      (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                        (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat
                          (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
                      (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
                    (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring)
                    (fun (x : @MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) => Real)
                    (@RingHom.instFunLike.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
                      (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                        (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat
                          (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
                      (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
                    (@MvPolynomial.eval.{0, u_1} Real σ Real.instCommSemiring x) (A i j))
                  (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
                    (@RingHom.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
                      (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                        (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat
                          (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
                      (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
                    (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring)
                    (fun (x : @MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) => Real)
                    (@RingHom.instFunLike.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
                      (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                        (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                        (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                        (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat
                          (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
                      (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
                    (@MvPolynomial.eval.{0, u_1} Real σ Real.instCommSemiring x) (A j i))) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, 0, 0}
              Reg.D5.S3.QuadraticForms.PolynomialSignature.signature_family.{u_1} PUnit.unit.{1}
              (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
                (fun (σ : Type u_1) =>
                  @Sigma.{0, u_1} Nat fun (n : Nat) =>
                    D5.S3.QuadraticForms.ActualSignature.Mat.{u_1}
                      (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n)
                σ
                (@Sigma.mk.{0, u_1} Nat
                  (fun (n : Nat) =>
                    D5.S3.QuadraticForms.ActualSignature.Mat.{u_1}
                      (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n)
                  n A)) :=
  fun {σ : Type u_1} (n : Nat)
    (A : D5.S3.QuadraticForms.ActualSignature.Mat.{u_1} (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n)
    (z : Int) (x : σ → Real)
    (hs :
      ∀ (i j : Fin n),
        @Eq.{1} Real
          (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
            (@RingHom.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
              (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
            (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring)
            (fun (x : @MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) => Real)
            (@RingHom.instFunLike.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
              (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
            (@MvPolynomial.eval.{0, u_1} Real σ Real.instCommSemiring x) (A i j))
          (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
            (@RingHom.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
              (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
            (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring)
            (fun (x : @MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) => Real)
            (@RingHom.instFunLike.{u_1, 0} (@MvPolynomial.{u_1, 0} σ Real Real.instCommSemiring) Real
              (@AddMonoidAlgebra.nonAssocSemiring.{0, u_1} Real
                (@Finsupp.{u_1, 0} σ Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                (@Finsupp.instAddZeroClass.{u_1, 0} σ Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid)))
              (@Semiring.toNonAssocSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)))
            (@MvPolynomial.eval.{0, u_1} Real σ Real.instCommSemiring x) (A j i))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S3.QuadraticForms.PolynomialSignature.signature_family.{u_1}
    Reg.D5.S3.QuadraticForms.PolynomialSignature.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
      (fun (σ : Type u_1) =>
        @Sigma.{0, u_1} Nat fun (n : Nat) =>
          D5.S3.QuadraticForms.ActualSignature.Mat.{u_1} (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n)
      σ
      (@Sigma.mk.{0, u_1} Nat
        (fun (n : Nat) =>
          D5.S3.QuadraticForms.ActualSignature.Mat.{u_1} (D5.S3.QuadraticForms.PolynomialSignature.Poly.{u_1} σ) n)
        n A))
    x

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"compile_iff_signature\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.QuadraticForms.PolynomialSignature, declaration := `D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"compile_iff_signature\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.QuadraticForms.PolynomialSignature, declaration := `D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).actual (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).variation.2.choose (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).variation.1 (Reg.D5.S3.QuadraticForms.PolynomialSignature.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"PolynomialSignature\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.QuadraticForms.PolynomialSignature, declaration := `Reg.D5.S3.QuadraticForms.PolynomialSignature.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
