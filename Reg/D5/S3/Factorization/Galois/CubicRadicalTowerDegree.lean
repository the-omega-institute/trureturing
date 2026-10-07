import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Galois.CubicRadicalTowerDegree
import Reg.Support.DependentFamily
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.Galois.CubicRadicalTowerDegree
open LeanInformationAudit
open scoped WithZero

namespace Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 3 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

-- Only the source's degree target is observed. Every field, finite index family,
-- root equation, valuation matrix, and unit hypothesis stays in the law.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K L : Type} [Field K] [Field L] [Algebra K L]
    {ι : Type} [Fintype ι]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (rad : ι → K) (root : ι → L)
    (hroot : ∀ i, root i ^ 3 = algebraMap K L (rad i))
    (hrad : ∀ i, rad i ≠ 0)
    (ν : ι → Valuation K (WithZero (Multiplicative ℤ)))
    (hdiag : ∀ i, ¬ (3 : ℤ) ∣ WithZero.log (ν i (rad i)))
    (hoff : ∀ i j, i ≠ j → ν i (rad j) = 1)
    (u : K) (hu0 : u ≠ 0) (hunoncube : ¬ ∃ c : K, c ^ 3 = u)
    (huval : ∀ i, WithZero.log (ν i u) = 0),
    Module.finrank K (IntermediateField.adjoin K (Set.range root)) =
        R.readout () () (Fintype.card ι) ∧
      ∀ x : IntermediateField.adjoin K (Set.range root),
        x ^ 3 ≠ algebraMap K (IntermediateField.adjoin K (Set.range root)) u

private theorem cyclotomic_unit_noncube :
    let K := CyclotomicField 3 ℚ
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ K :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    ¬ ∃ x : K, x ^ 3 = IsCyclotomicExtension.zeta 3 ℚ K := by
  dsimp only
  let K := CyclotomicField 3 ℚ
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  rintro ⟨x, hx⟩
  have hnot : x ^ 3 ≠ 1 := by
    rw [hx]
    exact hζ.ne_one (by decide)
  have h9 : x ^ 9 = 1 := by
    calc
      x ^ 9 = (x ^ 3) ^ 3 := by ring
      _ = ζ ^ 3 := by rw [hx]
      _ = 1 := hζ.pow_eq_one
  have horder : orderOf x = 9 := by
    have h := orderOf_eq_prime_pow (p := 3) (n := 1)
      (by simpa only [pow_one] using hnot)
      (by simpa only [show (3 : ℕ) ^ (1 + 1) = 9 by decide] using h9)
    norm_num at h
    exact h
  have hroot9 : IsPrimitiveRoot x 9 := IsPrimitiveRoot.iff_orderOf.mpr horder
  have hdiv : 9 ∣ 2 * 3 := hroot9.dvd_of_isCyclotomicExtension 3 (by decide)
  norm_num at hdiv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K := CyclotomicField 3 ℚ
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hp := hζ.pow_eq_one
    rw [hz] at hp
    norm_num at hp
  have hnc : ¬ ∃ x : K, x ^ 3 = ζ := cyclotomic_unit_noncube
  have hdegree := (h (K := K) (L := K) (ι := Empty)
    ζ hζ (fun i => nomatch i) (fun i => nomatch i)
    (by intro i; exact nomatch i)
    (by intro i; exact nomatch i)
    (fun i => nomatch i)
    (by intro i; exact nomatch i)
    (by intro i; exact nomatch i)
    ζ hζ0 hnc (by intro i; exact nomatch i)).1
  have hrange : Set.range (fun i : Empty => (nomatch i : K)) = ∅ := by
    ext x
    simp
  rw [hrange, IntermediateField.adjoin_empty] at hdegree
  simpa [rejected, realize] using hdegree

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro K L _ _ _ ι _ ζ hζ rad root hroot hrad ν hdiag hoff u hu0 hunoncube huval
    exact finite_valuation_degree_and_unit_noncube
      ζ hζ rad root hroot hrad ν hdiag hoff u hu0 hunoncube huval
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (3 : ℕ) ^ 0 ≠ 3 ^ 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 3 ^ n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Galois") "CubicRadicalTowerDegree") "finite_valuation_degree_and_unit_noncube") "Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree/Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 3 ^ n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.observationFact0, `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree


noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.arena
noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.arena
noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.arena) (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).actual

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"finite_valuation_degree_and_unit_noncube\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).bridge

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.observation0 : {K L : Type} →
  [inst : Field.{0} K] →
    [inst_1 : Field.{0} L] →
      [inst_2 :
          @Algebra.{0, 0} K L (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))
            (@DivisionSemiring.toSemiring.{0} L
              (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))] →
        {ι : Type} →
          [Fintype.{0} ι] →
            (ζ : K) →
              (hζ :
                  @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K inst)) ζ
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                (rad : ι → K) →
                  (root : ι → L) →
                    (hroot :
                        ∀ (i : ι),
                          @Eq.{1} L
                            (@HPow.hPow.{0, 0, 0} L Nat L
                              (@instHPow.{0, 0} L Nat
                                (@NPow.toPow.{0} L
                                  (@Monoid.toNPow.{0} L
                                    (@Semiring.toMonoid.{0} L
                                      (@DivisionSemiring.toSemiring.{0} L
                                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))))
                              (root i) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@DFunLike.coe.{1, 1, 1}
                              (@RingHom.{0, 0} K L
                                (@Semiring.toNonAssocSemiring.{0} K
                                  (@CommSemiring.toSemiring.{0} K
                                    (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))))
                                (@Semiring.toNonAssocSemiring.{0} L
                                  (@DivisionSemiring.toSemiring.{0} L
                                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))
                              K (fun (x : K) => L)
                              (@RingHom.instFunLike.{0, 0} K L
                                (@Semiring.toNonAssocSemiring.{0} K
                                  (@CommSemiring.toSemiring.{0} K
                                    (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))))
                                (@Semiring.toNonAssocSemiring.{0} L
                                  (@DivisionSemiring.toSemiring.{0} L
                                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))
                              (@Algebra.algebraMap.{0, 0} K L
                                (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))
                                (@DivisionSemiring.toSemiring.{0} L
                                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))
                                inst_2)
                              (rad i))) →
                      (hrad :
                          ∀ (i : ι),
                            @Ne.{1} K (rad i)
                              (@OfNat.ofNat.{0} K (nat_lit 0)
                                (@Zero.toOfNat0.{0} K
                                  (@MulZeroClass.toZero.{0} K
                                    (@instMulZeroClassOfSemiring.{0} K
                                      (@DivisionSemiring.toSemiring.{0} K
                                        (@Semifield.toDivisionSemiring.{0} K (@Field.toSemifield.{0} K inst)))))))) →
                        (ν :
                            ι →
                              @Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                                  (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                  (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                  (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                    (@PartialOrder.toPreorder.{0} Int
                                      (@SemilatticeInf.toPartialOrder.{0} Int
                                        (@Lattice.toSemilatticeInf.{0} Int
                                          (@DistribLattice.toLattice.{0} Int
                                            (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                                    (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                                      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                          Int
                                          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                                              Int.instConditionallyCompleteLinearOrder))))
                                      Int.instIsStrictOrderedRing)))
                                (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))) →
                          (hdiag :
                              ∀ (i : ι),
                                Not
                                  (@Dvd.dvd.{0} Int Int.instDvd
                                    (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
                                    (@WithZero.log.{0} Int Int.instAddMonoid
                                      (@DFunLike.coe.{1, 1, 1}
                                        (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                          (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                                            (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                            (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                            (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                              (@PartialOrder.toPreorder.{0} Int
                                                (@SemilatticeInf.toPartialOrder.{0} Int
                                                  (@Lattice.toSemilatticeInf.{0} Int
                                                    (@DistribLattice.toLattice.{0} Int
                                                      (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                                              (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                                                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                    Int
                                                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                      Int
                                                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                        Int Int.instConditionallyCompleteLinearOrder))))
                                                Int.instIsStrictOrderedRing)))
                                          (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
                                        K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
                                        (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                          (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                                          (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                                            (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                            (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                            (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                              (@PartialOrder.toPreorder.{0} Int
                                                (@SemilatticeInf.toPartialOrder.{0} Int
                                                  (@Lattice.toSemilatticeInf.{0} Int
                                                    (@DistribLattice.toLattice.{0} Int
                                                      (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                                              (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                                                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                    Int
                                                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                      Int
                                                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                        Int Int.instConditionallyCompleteLinearOrder))))
                                                Int.instIsStrictOrderedRing))))
                                        (ν i) (rad i))))) →
                            (hoff :
                                ∀ (i j : ι),
                                  @Ne.{1} ι i j →
                                    @Eq.{1} (WithZero.{0} (Multiplicative.{0} Int))
                                      (@DFunLike.coe.{1, 1, 1}
                                        (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                          (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                                            (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                            (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                            (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                              (@PartialOrder.toPreorder.{0} Int
                                                (@SemilatticeInf.toPartialOrder.{0} Int
                                                  (@Lattice.toSemilatticeInf.{0} Int
                                                    (@DistribLattice.toLattice.{0} Int
                                                      (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                                              (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                                                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                    Int
                                                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                      Int
                                                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                        Int Int.instConditionallyCompleteLinearOrder))))
                                                Int.instIsStrictOrderedRing)))
                                          (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
                                        K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
                                        (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                          (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                                          (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                                            (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                            (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                            (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                              (@PartialOrder.toPreorder.{0} Int
                                                (@SemilatticeInf.toPartialOrder.{0} Int
                                                  (@Lattice.toSemilatticeInf.{0} Int
                                                    (@DistribLattice.toLattice.{0} Int
                                                      (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                                              (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                                                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                    Int
                                                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                      Int
                                                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                        Int Int.instConditionallyCompleteLinearOrder))))
                                                Int.instIsStrictOrderedRing))))
                                        (ν i) (rad j))
                                      (@OfNat.ofNat.{0} (WithZero.{0} (Multiplicative.{0} Int)) (nat_lit 1)
                                        (@One.toOfNat1.{0} (WithZero.{0} (Multiplicative.{0} Int))
                                          (@WithZero.one.{0} (Multiplicative.{0} Int)
                                            (@instOneMultiplicativeOfZero.{0} Int
                                              (@MulZeroClass.toZero.{0} Int
                                                (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))))))) →
                              (u : K) →
                                (hu0 :
                                    @Ne.{1} K u
                                      (@OfNat.ofNat.{0} K (nat_lit 0)
                                        (@Zero.toOfNat0.{0} K
                                          (@MulZeroClass.toZero.{0} K
                                            (@instMulZeroClassOfSemiring.{0} K
                                              (@DivisionSemiring.toSemiring.{0} K
                                                (@Semifield.toDivisionSemiring.{0} K
                                                  (@Field.toSemifield.{0} K inst)))))))) →
                                  (hunoncube :
                                      Not
                                        (@Exists.{1} K fun (c : K) =>
                                          @Eq.{1} K
                                            (@HPow.hPow.{0, 0, 0} K Nat K
                                              (@instHPow.{0, 0} K Nat
                                                (@NPow.toPow.{0} K
                                                  (@Monoid.toNPow.{0} K
                                                    (@Semiring.toMonoid.{0} K
                                                      (@DivisionSemiring.toSemiring.{0} K
                                                        (@Semifield.toDivisionSemiring.{0} K
                                                          (@Field.toSemifield.{0} K inst)))))))
                                              c (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            u)) →
                                    (huval :
                                        ∀ (i : ι),
                                          @Eq.{1} Int
                                            (@WithZero.log.{0} Int Int.instAddMonoid
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                                  (@WithZero.instLinearOrderedCommMonoidWithZero.{0}
                                                    (Multiplicative.{0} Int)
                                                    (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                                    (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                                    (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                                      (@PartialOrder.toPreorder.{0} Int
                                                        (@SemilatticeInf.toPartialOrder.{0} Int
                                                          (@Lattice.toSemilatticeInf.{0} Int
                                                            (@DistribLattice.toLattice.{0} Int
                                                              (@instDistribLatticeOfLinearOrder.{0} Int
                                                                Int.instLinearOrder)))))
                                                      (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int
                                                        Int.instSemiring
                                                        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                            Int
                                                            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                              Int
                                                              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                                Int Int.instConditionallyCompleteLinearOrder))))
                                                        Int.instIsStrictOrderedRing)))
                                                  (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
                                                K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
                                                (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                                                  (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                                                  (@WithZero.instLinearOrderedCommMonoidWithZero.{0}
                                                    (Multiplicative.{0} Int)
                                                    (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                                                    (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                                                    (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                                                      (@PartialOrder.toPreorder.{0} Int
                                                        (@SemilatticeInf.toPartialOrder.{0} Int
                                                          (@Lattice.toSemilatticeInf.{0} Int
                                                            (@DistribLattice.toLattice.{0} Int
                                                              (@instDistribLatticeOfLinearOrder.{0} Int
                                                                Int.instLinearOrder)))))
                                                      (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int
                                                        Int.instSemiring
                                                        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                                                          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                            Int
                                                            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                              Int
                                                              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                                Int Int.instConditionallyCompleteLinearOrder))))
                                                        Int.instIsStrictOrderedRing))))
                                                (ν i) u))
                                            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
                                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0,
                                          0, 0}
                                        Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.signature PUnit.unit.{1}
                                        PUnit.unit.{1} :=
  fun {K L : Type} [Field.{0} K] [Field.{0} L]
    [@Algebra.{0, 0} K L (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))
        (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))]
    {ι : Type} [inst_3 : Fintype.{0} ι] (ζ : K)
    (hζ :
      @IsPrimitiveRoot.{0} K (@CommRing.toCommMonoid.{0} K (@Field.toCommRing.{0} K inst)) ζ
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (rad : ι → K) (root : ι → L)
    (hroot :
      ∀ (i : ι),
        @Eq.{1} L
          (@HPow.hPow.{0, 0, 0} L Nat L
            (@instHPow.{0, 0} L Nat
              (@NPow.toPow.{0} L
                (@Monoid.toNPow.{0} L
                  (@Semiring.toMonoid.{0} L
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))))
            (root i) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@DFunLike.coe.{1, 1, 1}
            (@RingHom.{0, 0} K L
              (@Semiring.toNonAssocSemiring.{0} K
                (@CommSemiring.toSemiring.{0} K (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))))
              (@Semiring.toNonAssocSemiring.{0} L
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))
            K (fun (x : K) => L)
            (@RingHom.instFunLike.{0, 0} K L
              (@Semiring.toNonAssocSemiring.{0} K
                (@CommSemiring.toSemiring.{0} K (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))))
              (@Semiring.toNonAssocSemiring.{0} L
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))))
            (@Algebra.algebraMap.{0, 0} K L (@Semifield.toCommSemiring.{0} K (@Field.toSemifield.{0} K inst))
              (@DivisionSemiring.toSemiring.{0} L
                (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst_1)))
              inst_2)
            (rad i)))
    (hrad :
      ∀ (i : ι),
        @Ne.{1} K (rad i)
          (@OfNat.ofNat.{0} K (nat_lit 0)
            (@Zero.toOfNat0.{0} K
              (@MulZeroClass.toZero.{0} K
                (@instMulZeroClassOfSemiring.{0} K
                  (@DivisionSemiring.toSemiring.{0} K
                    (@Semifield.toDivisionSemiring.{0} K (@Field.toSemifield.{0} K inst))))))))
    (ν :
      ι →
        @Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
          (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
            (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
            (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
            (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
              (@PartialOrder.toPreorder.{0} Int
                (@SemilatticeInf.toPartialOrder.{0} Int
                  (@Lattice.toSemilatticeInf.{0} Int
                    (@DistribLattice.toLattice.{0} Int
                      (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
              (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                        Int.instConditionallyCompleteLinearOrder))))
                Int.instIsStrictOrderedRing)))
          (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
    (hdiag :
      ∀ (i : ι),
        Not
          (@Dvd.dvd.{0} Int Int.instDvd (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
            (@WithZero.log.{0} Int Int.instAddMonoid
              (@DFunLike.coe.{1, 1, 1}
                (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                  (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                    (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                    (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                    (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                      (@PartialOrder.toPreorder.{0} Int
                        (@SemilatticeInf.toPartialOrder.{0} Int
                          (@Lattice.toSemilatticeInf.{0} Int
                            (@DistribLattice.toLattice.{0} Int
                              (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                      (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                                Int.instConditionallyCompleteLinearOrder))))
                        Int.instIsStrictOrderedRing)))
                  (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
                K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
                (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                  (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                  (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                    (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                    (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                    (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                      (@PartialOrder.toPreorder.{0} Int
                        (@SemilatticeInf.toPartialOrder.{0} Int
                          (@Lattice.toSemilatticeInf.{0} Int
                            (@DistribLattice.toLattice.{0} Int
                              (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                      (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                                Int.instConditionallyCompleteLinearOrder))))
                        Int.instIsStrictOrderedRing))))
                (ν i) (rad i)))))
    (hoff :
      ∀ (i j : ι),
        @Ne.{1} ι i j →
          @Eq.{1} (WithZero.{0} (Multiplicative.{0} Int))
            (@DFunLike.coe.{1, 1, 1}
              (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                  (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                  (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                  (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                    (@PartialOrder.toPreorder.{0} Int
                      (@SemilatticeInf.toPartialOrder.{0} Int
                        (@Lattice.toSemilatticeInf.{0} Int
                          (@DistribLattice.toLattice.{0} Int
                            (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                    (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                              Int.instConditionallyCompleteLinearOrder))))
                      Int.instIsStrictOrderedRing)))
                (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
              K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
              (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                  (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                  (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                  (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                    (@PartialOrder.toPreorder.{0} Int
                      (@SemilatticeInf.toPartialOrder.{0} Int
                        (@Lattice.toSemilatticeInf.{0} Int
                          (@DistribLattice.toLattice.{0} Int
                            (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                    (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                              Int.instConditionallyCompleteLinearOrder))))
                      Int.instIsStrictOrderedRing))))
              (ν i) (rad j))
            (@OfNat.ofNat.{0} (WithZero.{0} (Multiplicative.{0} Int)) (nat_lit 1)
              (@One.toOfNat1.{0} (WithZero.{0} (Multiplicative.{0} Int))
                (@WithZero.one.{0} (Multiplicative.{0} Int)
                  (@instOneMultiplicativeOfZero.{0} Int
                    (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))))
    (u : K)
    (hu0 :
      @Ne.{1} K u
        (@OfNat.ofNat.{0} K (nat_lit 0)
          (@Zero.toOfNat0.{0} K
            (@MulZeroClass.toZero.{0} K
              (@instMulZeroClassOfSemiring.{0} K
                (@DivisionSemiring.toSemiring.{0} K
                  (@Semifield.toDivisionSemiring.{0} K (@Field.toSemifield.{0} K inst))))))))
    (hunoncube :
      Not
        (@Exists.{1} K fun (c : K) =>
          @Eq.{1} K
            (@HPow.hPow.{0, 0, 0} K Nat K
              (@instHPow.{0, 0} K Nat
                (@NPow.toPow.{0} K
                  (@Monoid.toNPow.{0} K
                    (@Semiring.toMonoid.{0} K
                      (@DivisionSemiring.toSemiring.{0} K
                        (@Semifield.toDivisionSemiring.{0} K (@Field.toSemifield.{0} K inst)))))))
              c (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            u))
    (huval :
      ∀ (i : ι),
        @Eq.{1} Int
          (@WithZero.log.{0} Int Int.instAddMonoid
            (@DFunLike.coe.{1, 1, 1}
              (@Valuation.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                  (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                  (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                  (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                    (@PartialOrder.toPreorder.{0} Int
                      (@SemilatticeInf.toPartialOrder.{0} Int
                        (@Lattice.toSemilatticeInf.{0} Int
                          (@DistribLattice.toLattice.{0} Int
                            (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                    (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                              Int.instConditionallyCompleteLinearOrder))))
                      Int.instIsStrictOrderedRing)))
                (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst)))
              K (fun (x : K) => WithZero.{0} (Multiplicative.{0} Int))
              (@Valuation.instFunLike.{0, 0} K (WithZero.{0} (Multiplicative.{0} Int))
                (@DivisionRing.toRing.{0} K (@Field.toDivisionRing.{0} K inst))
                (@WithZero.instLinearOrderedCommMonoidWithZero.{0} (Multiplicative.{0} Int)
                  (@Multiplicative.commMonoid.{0} Int Int.instAddCommMonoid)
                  (@Multiplicative.linearOrder.{0} Int Int.instLinearOrder)
                  (@Multiplicative.isOrderedCancelMonoid.{0} Int Int.instAddCommMonoid
                    (@PartialOrder.toPreorder.{0} Int
                      (@SemilatticeInf.toPartialOrder.{0} Int
                        (@Lattice.toSemilatticeInf.{0} Int
                          (@DistribLattice.toLattice.{0} Int
                            (@instDistribLatticeOfLinearOrder.{0} Int Int.instLinearOrder)))))
                    (@IsStrictOrderedRing.toIsOrderedCancelAddMonoid.{0} Int Int.instSemiring
                      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                            (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                              Int.instConditionallyCompleteLinearOrder))))
                      Int.instIsStrictOrderedRing))))
              (ν i) u))
          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.signature
    Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.actual PUnit.unit.{1} PUnit.unit.{1}
    (@Fintype.card.{0} ι inst_3)

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"finite_valuation_degree_and_unit_noncube\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"finite_valuation_degree_and_unit_noncube\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).actual (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).variation.2.choose (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).variation.1 (Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"CubicRadicalTowerDegree\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree, declaration := `Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
