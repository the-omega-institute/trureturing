import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

open _root_.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ → Ambient
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ roots J => Module.finrank Base (tower roots J))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (roots : ℕ → Ambient)
    (hroots : ∀ j, 1 ≤ j →
      roots j ^ 3 = algebraMap Base Ambient (block j)) (J : ℕ),
    R.readout () roots J = 3 ^ J

private def witnessRoots (j : ℕ) : Ambient :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Base Ambient (block j)) (by decide : 0 < 3))

private theorem witnessRoots_spec (j : ℕ) :
    witnessRoots j ^ 3 = algebraMap Base Ambient (block j) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Base Ambient (block j)) (by decide : 0 < 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h witnessRoots (fun j _ => witnessRoots_spec j) 0
  norm_num [rejected, realize] at hzero

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro roots hroots J
    exact golden_cubic_block_kummer_tower_degree roots hroots J
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨witnessRoots, 0, 1, ?_⟩
    change Module.finrank Base (tower witnessRoots 0) ≠
      Module.finrank Base (tower witnessRoots 1)
    rw [golden_cubic_block_kummer_tower_degree witnessRoots
      (fun j _ => witnessRoots_spec j) 0,
      golden_cubic_block_kummer_tower_degree witnessRoots
        (fun j _ => witnessRoots_spec j) 1]
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ roots J => Module.finrank.{0, 0} Base (tower roots J))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Galois") "GoldenCubicBlockKummerTower") "golden_cubic_block_kummer_tower_degree") "Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower/Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ roots J => Module.finrank.{0, 0} Base (tower roots J))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.observationFact0, `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.anchorEnumeration }


#print axioms registration


end
end Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower


noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.arena
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.arena
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.arena) (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).actual

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"golden_cubic_block_kummer_tower_degree\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).bridge

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.observation0 : (roots : Nat → D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient) →
  (hroots :
      ∀ (j : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
          @Eq.{1} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
            (@HPow.hPow.{0, 0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient Nat
              D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
              (@instHPow.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient Nat
                (@NPow.toPow.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@Monoid.toNPow.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                    (@Semiring.toMonoid.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                      (@DivisionSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                        (@Semifield.toDivisionSemiring.{0}
                          D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                          (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                            (@AlgebraicClosure.instField.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                              (@CyclotomicField.instField.{0}
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat Rat.instField)))))))))
              (roots j) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DFunLike.coe.{1, 1, 1}
              (@RingHom.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CommSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField)))))
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@CommSemiring.toSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@CommRing.toCommSemiring.{0}
                      (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))
                      (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
              (fun (x : D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base) =>
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient)
              (@RingHom.instFunLike.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CommSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField)))))
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@CommSemiring.toSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@CommRing.toCommSemiring.{0}
                      (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))
                      (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              (@Algebra.algebraMap.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                      Rat.instField)))
                (@CommSemiring.toSemiring.{0}
                  (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                      Rat.instField))
                  (@CommRing.toCommSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))))
                (@AlgebraicClosure.instAlgebra.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                    Rat.instField)
                  D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField)))
                  (@Algebra.id.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              (@Nat.cast.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                (@AddMonoidWithOne.toNatCast.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Ring.toAddGroupWithOne.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@DivisionRing.toRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@Field.toDivisionRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                          (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            Rat Rat.instField))))))
                (D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.block j)))) →
    (J : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.signature PUnit.unit.{1} roots :=
  fun (roots : Nat → D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient)
    (hroots :
      ∀ (j : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
          @Eq.{1} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
            (@HPow.hPow.{0, 0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient Nat
              D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
              (@instHPow.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient Nat
                (@NPow.toPow.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@Monoid.toNPow.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                    (@Semiring.toMonoid.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                      (@DivisionSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                        (@Semifield.toDivisionSemiring.{0}
                          D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                          (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                            (@AlgebraicClosure.instField.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                              (@CyclotomicField.instField.{0}
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat Rat.instField)))))))))
              (roots j) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DFunLike.coe.{1, 1, 1}
              (@RingHom.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CommSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField)))))
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@CommSemiring.toSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@CommRing.toCommSemiring.{0}
                      (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))
                      (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
              (fun (x : D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base) =>
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient)
              (@RingHom.instFunLike.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CommSemiring.toSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField)))))
                (@Semiring.toNonAssocSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                  (@CommSemiring.toSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@CommRing.toCommSemiring.{0}
                      (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))
                      (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              (@Algebra.algebraMap.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Ambient
                (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                      Rat.instField)))
                (@CommSemiring.toSemiring.{0}
                  (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                      Rat.instField))
                  (@CommRing.toCommSemiring.{0}
                    (@AlgebraicClosure.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))
                    (@AlgebraicClosure.instCommRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField))))
                (@AlgebraicClosure.instAlgebra.{0, 0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                    Rat.instField)
                  D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                        Rat.instField)))
                  (@Algebra.id.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Semifield.toCommSemiring.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@Field.toSemifield.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Rat Rat.instField))))))
              (@Nat.cast.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                (@AddMonoidWithOne.toNatCast.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                    (@Ring.toAddGroupWithOne.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                      (@DivisionRing.toRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                        (@Field.toDivisionRing.{0} D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.Base
                          (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            Rat Rat.instField))))))
                (D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.block j))))
    (J : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.signature
    Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.actual PUnit.unit.{1} roots J

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"golden_cubic_block_kummer_tower_degree\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree, part := .type, path := [.body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"golden_cubic_block_kummer_tower_degree\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).actual (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).variation.2.choose (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).variation.1 (Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicBlockKummerTower\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
