import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
import Mathlib.Probability.HasLawExists
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Use the original source's additive norm dictionary. The ring-derived route
available after the audit imports is definitionally equal but has different raw operands. -/
local instance : SeminormedAddCommGroup ℝ :=
  Real.normedAddCommGroup.toSeminormedAddCommGroup

abbrev signature : Signature where
  Params := Σ Ω : Type, Σ _ : ℕ → ℕ → Ω → ℝ, Σ _ : ℕ → ℕ → ℝ, Σ _ : ℕ, ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω) ^ 2 - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original telescope and conclusion, with the same weighted summand
replaced in both the existential MemLp witnesses and their actual L² sums. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → ℝ) (v : ℝ≥0),
    (∀ n j, HasLaw (G n j) (gaussianReal 0 1) P) →
    (∀ n, iIndepFun (G n) P) →
    (∀ n, Summable (fun j => (a n j) ^ 2)) →
    Tendsto (fun n => ⨆ j, |a n j|) atTop (𝓝 0) →
    Tendsto (fun n => ∑' j, (a n j) ^ 2) atTop (𝓝 ((v : ℝ) / 2)) →
    ∃ (hmem : ∀ n j, MemLp (fun ω => (r.readout () ⟨Ω, G, a, n, j⟩ ω : ℝ)) 2 P)
      (Q : ℕ → Lp ℝ 2 P),
      (∀ n, HasSum (fun j => (hmem n j).toLp
        (fun ω => (r.readout () ⟨Ω, G, a, n, j⟩ ω : ℝ))) (Q n)) ∧
      TendstoInDistribution (fun n => ⇑(Q n)) atTop (id : ℝ → ℝ)
        (fun _ => P) (gaussianReal 0 v)

/-- A genuine probability space with independent standard Gaussians satisfies every
original premise at a = 0 and v = 0. Constant-one interventions cannot be summed in L². -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Ω, mΩ, P, X, _, hX, hind, hP⟩ := exists_iid ℕ (gaussianReal 0 1)
  let := mΩ
  let := hP
  obtain ⟨hmem, Q, hsum, _⟩ := h Ω P (fun _ => X) (fun _ _ => 0) 0
    (fun _ j => hX j) (fun _ => hind)
    (by simp) (by simp) (by simp)
  have hs : Summable (fun _ : ℕ => Lp.const 2 P (1 : ℝ)) := (hsum 0).summable
  have hz : Lp.const 2 P (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  have hn := congrArg norm hz
  simp [Lp.norm_const] at hn

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ℝ, (fun _ _ ω => ω), (fun _ _ => 1), 0, 0⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    exact (by norm_num : (1 : ℝ) * (0 ^ 2 - 1) ≠ 1 * (1 ^ 2 - 1))

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω) ^ 2 - 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CountableGaussianQuadraticLimit") "result") "Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit/Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω) ^ 2 - 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, definition := none, coordinates := #[0, 4, 5, 12, 13], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn", "arg", "body"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{1, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
      Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
      Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.actual)
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration)

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{1, 0, 0, 0, 0}
  Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.arena
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.actual)
  Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration)

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.observation0 : (Ω : Type) →
  [inst : MeasurableSpace.{0} Ω] →
    (P : @MeasureTheory.Measure.{0} Ω inst) →
      [@MeasureTheory.IsProbabilityMeasure.{0} Ω inst P] →
        (G : Nat → Nat → Ω → Real) →
          (a : Nat → Nat → Real) →
            (v : NNReal) →
              (hG :
                  ∀ (n j : Nat),
                    @ProbabilityTheory.HasLaw.{0, 0} Ω Real inst Real.measurableSpace (G n j)
                      (ProbabilityTheory.gaussianReal
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
                      P) →
                (hind :
                    ∀ (n : Nat),
                      @ProbabilityTheory.iIndepFun.{0, 0, 0} Ω Nat inst (fun (x : Nat) => Real)
                        (fun (x : Nat) => Real.measurableSpace) (G n) P) →
                  (ha :
                      ∀ (n : Nat),
                        @Summable.{0, 0} Real Nat Real.instAddCommMonoid
                          (@UniformSpace.toTopologicalSpace.{0} Real
                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                          (fun (j : Nat) =>
                            @HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (a n j) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (SummationFilter.unconditional.{0} Nat)) →
                    (hM :
                        @Filter.Tendsto.{0, 0} Nat Real
                          (fun (n : Nat) =>
                            @iSup.{0, 1} Real Nat Real.instSupSet fun (j : Nat) =>
                              @abs.{0} Real Real.lattice Real.instAddGroup (a n j))
                          (@Filter.atTop.{0} Nat Nat.instPreorder)
                          (@nhds.{0} Real
                            (@UniformSpace.toTopologicalSpace.{0} Real
                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                      (hS :
                          @Filter.Tendsto.{0, 0} Nat Real
                            (fun (n : Nat) =>
                              @tsum.{0, 0} Real Nat Real.instAddCommMonoid
                                (@UniformSpace.toTopologicalSpace.{0} Real
                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                (fun (j : Nat) =>
                                  @HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    (a n j) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (SummationFilter.unconditional.{0} Nat))
                            (@Filter.atTop.{0} Nat Nat.instPreorder)
                            (@nhds.{0} Real
                              (@UniformSpace.toTopologicalSpace.{0} Real
                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (NNReal.toReal v)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))) →
                        (n j : Nat) →
                          (ω : Ω) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                              Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.signature PUnit.unit.{1}
                              (@Sigma.mk.{1, 0} Type
                                (fun (Ω : Type) =>
                                  @Sigma.{0, 0} (Nat → Nat → Ω → Real) fun (x : Nat → Nat → Ω → Real) =>
                                    @Sigma.{0, 0} (Nat → Nat → Real) fun (x : Nat → Nat → Real) =>
                                      @Sigma.{0, 0} Nat fun (x : Nat) => Nat)
                                Ω
                                (@Sigma.mk.{0, 0} (Nat → Nat → Ω → Real)
                                  (fun (x : Nat → Nat → Ω → Real) =>
                                    @Sigma.{0, 0} (Nat → Nat → Real) fun (x : Nat → Nat → Real) =>
                                      @Sigma.{0, 0} Nat fun (x : Nat) => Nat)
                                  G
                                  (@Sigma.mk.{0, 0} (Nat → Nat → Real)
                                    (fun (x : Nat → Nat → Real) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) a
                                    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) n j)))) :=
  fun (Ω : Type) [MeasurableSpace.{0} Ω] (P : @MeasureTheory.Measure.{0} Ω inst)
    [@MeasureTheory.IsProbabilityMeasure.{0} Ω inst P] (G : Nat → Nat → Ω → Real) (a : Nat → Nat → Real) (v : NNReal)
    (hG :
      ∀ (n j : Nat),
        @ProbabilityTheory.HasLaw.{0, 0} Ω Real inst Real.measurableSpace (G n j)
          (ProbabilityTheory.gaussianReal (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} NNReal (nat_lit 1) (@One.toOfNat1.{0} NNReal NNReal.instOne)))
          P)
    (hind :
      ∀ (n : Nat),
        @ProbabilityTheory.iIndepFun.{0, 0, 0} Ω Nat inst (fun (x : Nat) => Real)
          (fun (x : Nat) => Real.measurableSpace) (G n) P)
    (ha :
      ∀ (n : Nat),
        @Summable.{0, 0} Real Nat Real.instAddCommMonoid
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (fun (j : Nat) =>
            @HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (a n j)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (SummationFilter.unconditional.{0} Nat))
    (hM :
      @Filter.Tendsto.{0, 0} Nat Real
        (fun (n : Nat) =>
          @iSup.{0, 1} Real Nat Real.instSupSet fun (j : Nat) => @abs.{0} Real Real.lattice Real.instAddGroup (a n j))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
    (hS :
      @Filter.Tendsto.{0, 0} Nat Real
        (fun (n : Nat) =>
          @tsum.{0, 0} Real Nat Real.instAddCommMonoid
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (j : Nat) =>
              @HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (a n j)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (SummationFilter.unconditional.{0} Nat))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (NNReal.toReal v)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
    (n j : Nat) (ω : Ω) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.signature
    Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.actual PUnit.unit.{1}
    (@Sigma.mk.{1, 0} Type
      (fun (Ω : Type) =>
        @Sigma.{0, 0} (Nat → Nat → Ω → Real) fun (x : Nat → Nat → Ω → Real) =>
          @Sigma.{0, 0} (Nat → Nat → Real) fun (x : Nat → Nat → Real) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat)
      Ω
      (@Sigma.mk.{0, 0} (Nat → Nat → Ω → Real)
        (fun (x : Nat → Nat → Ω → Real) =>
          @Sigma.{0, 0} (Nat → Nat → Real) fun (x : Nat → Nat → Real) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat)
        G
        (@Sigma.mk.{0, 0} (Nat → Nat → Real) (fun (x : Nat → Nat → Real) => @Sigma.{0, 0} Nat fun (x : Nat) => Nat) a
          (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) n j))))
    ω

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"function\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .function, .function, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration).actual (Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CountableGaussianQuadraticLimit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit, declaration := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
