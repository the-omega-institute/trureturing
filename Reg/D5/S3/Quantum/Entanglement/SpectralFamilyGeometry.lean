import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
open _root_.D5.S3.TotalVariation.Hellinger
open _root_.D5.S3.TotalVariation.Bhattacharyya
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 - x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {Sector : Type u} {Coord : Type v}
    [Fintype Sector] [Fintype Coord] [Nonempty Sector]
    (spectrum : Sector → Coord → ℝ)
    (_hnonneg : ∀ s j, 0 ≤ spectrum s j)
    (_hnormal : ∀ s, ∑ j, spectrum s j = 1),
    (∀ p ∈ stdSimplex ℝ Sector,
      spectralPairVariance spectrum p =
        2 * R.readout () () (spectralGramEnergy spectrum p)) ∧
    ∃ p ∈ stdSimplex ℝ Sector, ∃ s t : Sector,
      (∀ r ∈ stdSimplex ℝ Sector,
        spectralPairVariance spectrum r ≤ spectralPairVariance spectrum p) ∧
      (∀ a b : Sector, spectralGap spectrum a b ≤ spectralGap spectrum s t) ∧
      spectralGap spectrum s t / 2 ≤ spectralPairVariance spectrum p ∧
      spectralPairVariance spectrum p ≤ spectralGap spectrum s t ∧
      (spectralPairVariance spectrum p = 0 ↔
        ∀ a b : Sector, spectrum a = spectrum b) ∧
      (∀ a : Sector,
        spectralGramEnergy spectrum p ≤
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t) ∧
        (0 < p a → spectralGramEnergy spectrum p =
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t))) ∧
      (∀ r ∈ stdSimplex ℝ Sector,
        (∀ w ∈ stdSimplex ℝ Sector,
          spectralGramEnergy spectrum r ≤ spectralGramEnergy spectrum w) ↔
        ∀ a : Sector,
          spectralGramEnergy spectrum r ≤
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t) ∧
          (0 < r a → spectralGramEnergy spectrum r =
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t)))

theorem actual_law : arena.{u, v}.Law actual := by
  intro Sector Coord _ _ _ spectrum hnonneg hnormal
  exact finite_spectral_family_geometry spectrum hnonneg hnormal

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let spectrum : ULift.{u} Unit → ULift.{v} Unit → ℝ := fun _ _ => 1
  let p : ULift.{u} Unit → ℝ := Pi.single ⟨()⟩ 1
  have hp : p ∈ stdSimplex ℝ (ULift.{u} Unit) :=
    single_mem_stdSimplex ℝ (⟨()⟩ : ULift.{u} Unit)
  have hnonneg : ∀ s j, 0 ≤ spectrum s j := by simp [spectrum]
  have hnormal : ∀ s : ULift.{u} Unit, ∑ j : ULift.{v} Unit, spectrum s j = 1 := by
    simp [spectrum]
  have heq := (h spectrum hnonneg hnormal).1 p hp
  have hzero : spectralPairVariance spectrum p = 0 := by
    simp [spectralPairVariance, spectrum, hellinger_sq_self]
  have hbad : rejected.readout () () (spectralGramEnergy spectrum p) = 1 := rfl
  rw [hzero, hbad] at heq
  norm_num at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry.{u_1, u_2}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 - x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "SpectralFamilyGeometry") "finite_spectral_family_geometry") "Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry/Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 - x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry


noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.arena.) (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"finite_spectral_family_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.observation0.{u_1, u_2} : {Sector : Type u_1} →
  {Coord : Type u_2} →
    [inst : Fintype.{u_1} Sector] →
      [inst_1 : Fintype.{u_2} Coord] →
        [Nonempty.{u_1 + 1} Sector] →
          (spectrum : Sector → Coord → Real) →
            (hnonneg :
                ∀ (s : Sector) (j : Coord),
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (spectrum s j)) →
              (hnormal :
                  ∀ (s : Sector),
                    @Eq.{1} Real
                      (@Finset.sum.{u_2, 0} Coord Real Real.instAddCommMonoid (@Finset.univ.{u_2} Coord inst_1)
                        fun (j : Coord) => spectrum s j)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                (p : Sector → Real) →
                  @Membership.mem.{u_1, u_1} (Sector → Real) (Set.{u_1} (Sector → Real))
                      (@Set.instMembership.{u_1} (Sector → Real))
                      (@stdSimplex.{u_1, 0} Real Sector Real.semiring Real.partialOrder inst) p →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {Sector : Type u_1} {Coord : Type u_2} [inst : Fintype.{u_1} Sector] [inst_1 : Fintype.{u_2} Coord]
    [Nonempty.{u_1 + 1} Sector] (spectrum : Sector → Coord → Real)
    (hnonneg :
      ∀ (s : Sector) (j : Coord),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (spectrum s j))
    (hnormal :
      ∀ (s : Sector),
        @Eq.{1} Real
          (@Finset.sum.{u_2, 0} Coord Real Real.instAddCommMonoid (@Finset.univ.{u_2} Coord inst_1) fun (j : Coord) =>
            spectrum s j)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (p : Sector → Real)
    (a :
      @Membership.mem.{u_1, u_1} (Sector → Real) (Set.{u_1} (Sector → Real)) (@Set.instMembership.{u_1} (Sector → Real))
        (@stdSimplex.{u_1, 0} Real Sector Real.semiring Real.partialOrder inst) p) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.signature
    Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.actual PUnit.unit.{1} PUnit.unit.{1}
    (@D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.spectralGramEnergy.{u_1, u_2} Sector Coord inst inst_1 spectrum
      p)

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"finite_spectral_family_geometry\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"finite_spectral_family_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"SpectralFamilyGeometry\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, declaration := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
