import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.FinitePhaseMixture
import Reg.Support.DependentFamily

open scoped BigOperators ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture

noncomputable section

def signature : Signature where
  Params := ℕ
  State := fun d => Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ d => Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ H => H) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ (d : ℕ) _ => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d) (H : Matrix (Fin d) (Fin d) ℂ)
    (_hH : H.IsHermitian) (_hdiag : ∀ i, H i i = 1)
    (_hmass : (∑ i, ∑ j, if i < j then ‖H i j‖ else 0) ≤ 1),
    ∃ n : ℕ, 0 < n ∧ ∃ (p : Fin n → ℝ) (z : Fin n → Fin d → ℂ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      (∀ a i, ‖z a i‖ = 1) ∧
      ∀ i j, R.readout () d H i j = ∑ a, (p a : ℂ) * z a i * conj (z a j)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨_root_.D5.S3.Quantum.Matrix.FinitePhaseMixture.result, rejected, ?_⟩
    intro h
    obtain ⟨n, _, p, z, _, hp, hz, he⟩ := h 1 (by omega) 1
      (Matrix.isHermitian_one) (by simp) (by simp)
    have he0 := he 0 0
    change (0 : ℂ) = ∑ a, (p a : ℂ) * z a 0 * conj (z a 0) at he0
    simp only [mul_assoc, Complex.mul_conj', hz, one_pow, Complex.ofReal_one, mul_one] at he0
    have hpC : (∑ a, (p a : ℂ)) = 1 := by exact_mod_cast hp
    exact zero_ne_one (he0.trans hpC)
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        obtain ⟨n, _, p, z, _, hp, hz, he⟩ := h 1 (by omega) 1
          (Matrix.isHermitian_one) (by simp) (by simp)
        have he0 := he 0 0
        change (0 : ℂ) = ∑ a, (p a : ℂ) * z a 0 * conj (z a 0) at he0
        simp only [mul_assoc, Complex.mul_conj', hz, one_pow, Complex.ofReal_one, mul_one] at he0
        have hpC : (∑ a, (p a : ℂ)) = 1 := by exact_mod_cast hp
        exact zero_ne_one (he0.trans hpC)
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : Matrix (Fin 1) (Fin 1) ℂ),
      (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [actual, realize] at hh

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Matrix.FinitePhaseMixture.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => H) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Matrix") "FinitePhaseMixture") "result") "Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture/Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ H => H) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "fn"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `D5.S3.Quantum.Matrix.FinitePhaseMixture.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.observationFact0, `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.anchorEnumeration }


end
end Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture


noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.arena
noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.arena
noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.arena) (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).actual

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `D5.S3.Quantum.Matrix.FinitePhaseMixture.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.observation0 : (d : Nat) →
  (_hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d) →
    (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
      (hH :
          @Matrix.IsHermitian.{0, 0} Complex (Fin d)
            (@InvolutiveStar.toStar.{0} Complex
              (@StarAddMonoid.toInvolutiveStar.{0} Complex
                (@AddCommMonoid.toAddMonoid.{0} Complex
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                (@StarRing.toStarAddMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                  Complex.instStarRing)))
            H) →
        (hdiag :
            ∀ (i : Fin d),
              @Eq.{1} Complex (H i i)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
          (hmass :
              @LE.le.{0} Real Real.instLE
                (@Finset.sum.{0, 0} (Fin d) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin d) (Fin.fintype d))
                  fun (i : Fin d) =>
                  @Finset.sum.{0, 0} (Fin d) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin d) (Fin.fintype d))
                    fun (j : Fin d) =>
                    @ite.{1} Real (@LT.lt.{0} (Fin d) (@instLTFin d) i j) (@Fin.decLt d i j)
                      (@Norm.norm.{0} Complex Complex.instNorm (H i j))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (n : Nat) →
              (p : Fin n → Real) →
                (z : Fin n → Fin d → Complex) →
                  (i j : Fin d) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.signature PUnit.unit.{1} d :=
  fun (d : Nat) (_hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
    (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hH :
      @Matrix.IsHermitian.{0, 0} Complex (Fin d)
        (@InvolutiveStar.toStar.{0} Complex
          (@StarAddMonoid.toInvolutiveStar.{0} Complex
            (@AddCommMonoid.toAddMonoid.{0} Complex
              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
            (@StarRing.toStarAddMonoid.{0} Complex
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
              Complex.instStarRing)))
        H)
    (hdiag :
      ∀ (i : Fin d),
        @Eq.{1} Complex (H i i) (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (hmass :
      @LE.le.{0} Real Real.instLE
        (@Finset.sum.{0, 0} (Fin d) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin d) (Fin.fintype d))
          fun (i : Fin d) =>
          @Finset.sum.{0, 0} (Fin d) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin d) (Fin.fintype d))
            fun (j : Fin d) =>
            @ite.{1} Real (@LT.lt.{0} (Fin d) (@instLTFin d) i j) (@Fin.decLt d i j)
              (@Norm.norm.{0} Complex Complex.instNorm (H i j))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (n : Nat) (p : Fin n → Real) (z : Fin n → Fin d → Complex) (i j : Fin d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.signature Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.actual
    PUnit.unit.{1} d H

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `D5.S3.Quantum.Matrix.FinitePhaseMixture.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .argument, .argument, .body, .argument, .body, .argument, .argument, .argument, .body, .body, .function, .argument, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `D5.S3.Quantum.Matrix.FinitePhaseMixture.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).actual (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).variation.2.choose (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).variation.1 (Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Matrix\",\"FinitePhaseMixture\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture, declaration := `Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
