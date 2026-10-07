import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.PureCubicIntegralLattices
import Reg.Support.DependentFamily
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.Arith.Lattices.PureCubicIntegralLattices
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Module

namespace Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices
universe u

noncomputable section

abbrev signature : Signature where
  Params := ℤ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k),
    IsIntegral ℤ pb.gen ∧
    IsIntegral ℤ (pb.gen ^ 2 / (n : K)) ∧
    IsIntegral ℤ
      ((1 + (c : K) * pb.gen +
        (v : K) * (pb.gen ^ 2 / (n : K))) / 3) ∧
    ∃ b1 b2 : Basis (Fin 3) ℚ K,
      (b1 : Fin 3 → K) = ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)] ∧
      (b2 : Fin 3 → K) =
        ![(1 : K), pb.gen,
          (1 + (c : K) * pb.gen +
            (v : K) * (pb.gen ^ 2 / (n : K))) / 3] ∧
      Algebra.discr ℚ b1 = -27 * ((m * n : ℤ) : ℚ) ^ 2 ∧
      Algebra.discr ℚ b2 = R.readout () m n

theorem ten_irreducible :
    Irreducible ((X : Polynomial ℚ) ^ 3 - C 10) := by
  have hnocubeInt (z : ℤ) : z ^ 3 ≠ 10 := by
    intro hz
    have hz7 : (z : ZMod 7) ^ 3 = (10 : ZMod 7) := by
      simpa only [Int.cast_pow, Int.cast_ofNat] using
        congrArg (fun x : ℤ => (x : ZMod 7)) hz
    have hnone (w : ZMod 7) : w ^ 3 ≠ (10 : ZMod 7) := by
      fin_cases w <;> decide
    exact hnone (z : ZMod 7) hz7
  have hnocubeRat (r : ℚ) : r ^ 3 ≠ 10 := by
    intro hr
    have hInt : IsIntegral ℤ r := by
      apply IsIntegral.of_pow (n := 3) (by norm_num)
      rw [hr]
      exact isIntegral_algebraMap
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hInt
    apply hnocubeInt z
    rw [← hz] at hr
    apply (Int.cast_injective (α := ℚ))
    simpa only [algebraMap_int_eq, eq_intCast,
      Int.cast_pow, Int.cast_ofNat] using hr
  exact X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 3) hnocubeRat

noncomputable def tenPowerBasis
    [Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 10))] :
    PowerBasis ℚ (AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 10)) :=
  AdjoinRoot.powerBasis (monic_X_pow_sub_C 10 (by norm_num : 3 ≠ 0)).ne_zero

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  letI : Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 10)) := ⟨ten_irreducible⟩
  let K0 := AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 10)
  let K := ULift.{u} K0
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let pb : PowerBasis ℚ K :=
    tenPowerBasis.map (ULift.algEquiv (R := ℚ)).symm
  have h3 : pb.dim = 3 := by
    change (tenPowerBasis).dim = 3
    simp [tenPowerBasis]
  have hroot0 : (tenPowerBasis).gen ^ 3 = (10 : K0) := by
    simpa [tenPowerBasis, K0] using root_X_pow_sub_C_pow 3 (10 : ℚ)
  have hroot : pb.gen ^ 3 = (((10 : ℤ) * 1 ^ 2 : ℤ) : K) := by
    apply (ULift.algEquiv (R := ℚ)).injective
    change (tenPowerBasis.gen : K0) ^ 3 = 10
    exact hroot0
  have hcubic : (1 : ℤ) ^ 3 * 10 * 1 ^ 2 = 1 + 9 * 1 := by norm_num
  have hcv : (1 : ℤ) ^ 2 * 1 = 1 + 3 * 0 := by norm_num
  have hv : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hm : (10 : ℤ) ≠ 0 := by norm_num
  have hn : (1 : ℤ) ≠ 0 := by norm_num
  intro h
  obtain ⟨_, _, _, b1, b2, _, hvec, _, hdisc⟩ :=
    h (K := K) (pb := pb) (h3 := h3) 10 1 1 1 0 1 hm hn hv hroot hcubic hcv
  obtain ⟨_, _, _, b1', b2', _, hvec', _, hdisc'⟩ :=
    integral_cubic_lattices (K := K) pb h3 10 1 1 1 0 1 hm hn hv
      hroot hcubic hcv
  have heq : (b2 : Fin 3 → K) = (b2' : Fin 3 → K) := hvec.trans hvec'.symm
  have hdisceq : Algebra.discr ℚ b2 = Algebra.discr ℚ b2' :=
    congrArg (Algebra.discr ℚ) heq
  rw [hdisc, hdisc'] at hdisceq
  norm_num [rejected, realize] at hdisceq

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by exact integral_cubic_lattices,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      change Unit at j
      cases j
      exact (h rfl).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    intro i
    change Unit at i
    cases i
    dsimp [arena, signature] at *
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Lattices") "PureCubicIntegralLattices") "integral_cubic_lattices") "Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices/Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ m n => -3 * ((m * n : ℤ) : ℚ) ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices, definition := none, coordinates := #[6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.observationFact0, `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.anchorEnumeration }


#print axioms registration


end
end Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices


noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.arena.{u_1}
noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.arena.{u_1}
noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.arena.) (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"integral_cubic_lattices\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.observation0.{u_1} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    [@CharZero.{u_1} K
          (@AddGroupWithOne.toAddMonoidWithOne.{u_1} K
            (@Ring.toAddGroupWithOne.{u_1} K (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))))] →
      [inst_2 :
          @Algebra.{0, u_1} Rat K Rat.commSemiring
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))] →
        (pb :
            @PowerBasis.{0, u_1} Rat K Rat.commRing (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))
              inst_2) →
          (h3 :
              @Eq.{1} Nat
                (@PowerBasis.dim.{0, u_1} Rat K Rat.commRing
                  (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst)) inst_2 pb)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
            (m n c a k v : Int) →
              (hm : @Ne.{1} Int m (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
                (hn : @Ne.{1} Int n (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
                  (hv :
                      Or (@Eq.{1} Int v (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Eq.{1} Int v
                          (@Neg.neg.{0} Int Int.instNegInt
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
                    (hroot :
                        @Eq.{u_1 + 1} K
                          (@HPow.hPow.{u_1, 0, u_1} K Nat K
                            (@instHPow.{u_1, 0} K Nat
                              (@NPow.toPow.{u_1} K
                                (@Monoid.toNPow.{u_1} K
                                  (@Semiring.toMonoid.{u_1} K
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))))
                            (@PowerBasis.gen.{0, u_1} Rat K Rat.commRing
                              (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst)) inst_2 pb)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@Int.cast.{u_1} K
                            (@AddGroupWithOne.toIntCast.{u_1} K
                              (@Ring.toAddGroupWithOne.{u_1} K
                                (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))))
                            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m
                              (@HPow.hPow.{0, 0, 0} Int Nat Int
                                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                n (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                      (hcubic :
                          @Eq.{1} Int
                            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                (@HPow.hPow.{0, 0, 0} Int Nat Int
                                  (@instHPow.{0, 0} Int Nat
                                    (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                  c (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                m)
                              (@HPow.hPow.{0, 0, 0} Int Nat Int
                                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                n (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                (@OfNat.ofNat.{0} Int (nat_lit 9) (@instOfNat (nat_lit 9))) a))) →
                        (hcv :
                            @Eq.{1} Int
                              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                (@HPow.hPow.{0, 0, 0} Int Nat Int
                                  (@instHPow.{0, 0} Int Nat
                                    (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                  c (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                n)
                              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) v
                                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))) k))) →
                          (b1 b2 :
                              @Module.Basis.{0, 0, u_1}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat K Rat.semiring
                                (@Semiring.toAddCommMonoid.{u_1} K
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
                                (@Algebra.toModule.{0, u_1} Rat K Rat.commSemiring
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  inst_2)) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.signature PUnit.unit.{1} m :=
  fun {K : Type u_1} [Field.{u_1} K]
    [@CharZero.{u_1} K
        (@AddGroupWithOne.toAddMonoidWithOne.{u_1} K
          (@Ring.toAddGroupWithOne.{u_1} K (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))))]
    [@Algebra.{0, u_1} Rat K Rat.commSemiring
        (@DivisionSemiring.toSemiring.{u_1} K
          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))]
    (pb :
      @PowerBasis.{0, u_1} Rat K Rat.commRing (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))
        inst_2)
    (h3 :
      @Eq.{1} Nat
        (@PowerBasis.dim.{0, u_1} Rat K Rat.commRing (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))
          inst_2 pb)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (m n c a k v : Int) (hm : @Ne.{1} Int m (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (hn : @Ne.{1} Int n (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
    (hv :
      Or (@Eq.{1} Int v (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Eq.{1} Int v (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
    (hroot :
      @Eq.{u_1 + 1} K
        (@HPow.hPow.{u_1, 0, u_1} K Nat K
          (@instHPow.{u_1, 0} K Nat
            (@NPow.toPow.{u_1} K
              (@Monoid.toNPow.{u_1} K
                (@Semiring.toMonoid.{u_1} K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))))
          (@PowerBasis.gen.{0, u_1} Rat K Rat.commRing
            (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst)) inst_2 pb)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Int.cast.{u_1} K
          (@AddGroupWithOne.toIntCast.{u_1} K
            (@Ring.toAddGroupWithOne.{u_1} K (@DivisionRing.toRing.{u_1} K (@Field.toDivisionRing.{u_1} K inst))))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (hcubic :
      @Eq.{1} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) c
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            m)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 9) (@instOfNat (nat_lit 9))) a)))
    (hcv :
      @Eq.{1} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) c
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          n)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) v
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))) k)))
    (b1 b2 :
      @Module.Basis.{0, 0, u_1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Rat K Rat.semiring
        (@Semiring.toAddCommMonoid.{u_1} K
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))
        (@Algebra.toModule.{0, u_1} Rat K Rat.commSemiring
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          inst_2)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.signature
    Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.actual PUnit.unit.{1} m n

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"integral_cubic_lattices\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"integral_cubic_lattices\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `D5.S3.Arith.Lattices.PureCubicIntegralLattices.integral_cubic_lattices, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).actual (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).variation.2.choose (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).variation.1 (Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Lattices\",\"PureCubicIntegralLattices\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices, declaration := `Reg.D5.S3.Arith.Lattices.PureCubicIntegralLattices.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
