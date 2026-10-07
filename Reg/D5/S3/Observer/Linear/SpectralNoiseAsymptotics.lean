import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.SpectralNoiseAsymptotics
import Reg.Support.DependentFamily
import Mathlib.Tactic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology BigOperators
noncomputable section
namespace Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics
abbrev Parameters := Σ (_ : ℝ), Σ (_ : ℝ), ℝ
abbrev signature : Signature where
  Params := Parameters
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def emptyAnchor : ∀ (_ : Empty) p,signature.State p := fun e => nomatch e
def actual : Realization signature := realize signature
  (fun _ p x => Real.log (1+x/(p.1*p.2.2^p.2.1))) emptyAnchor
def modified : Realization signature := realize signature (fun _ p _ => p.2.2⁻¹) emptyAnchor
def theoremLaw (family:Realization signature) : Prop := ∀ (n:ℕ) (q:Fin (n+1) → ℕ) (hq:∀ i,q i≤q (Fin.last n))
  (lam:ℝ → Fin (n+1) → ℝ) (c C β:ℝ) (hc:0<c) (hC:0<C) (hβ:0<β)
  (hbounds:∀ᶠ T:ℝ in 𝓝[>] 0,∀ i,c*T^(q i)≤lam T i ∧ lam T i≤C*T^(q i)) ,
 (∀ α:ℝ,
    (fun T:ℝ=>(1/2:ℝ)*(∑ i:Fin (n+1),family.readout () ⟨β,α,T⟩ (lam T i))-
      (1/2:ℝ)*(∑ i:Fin (n+1),max (α-(q i:ℝ)) 0)*Real.log (1/T))
      =O[𝓝[>] 0] (fun _:ℝ=>(1:ℝ))) ∧
  (∀ eps:ℝ → ℝ,(∀ T:ℝ,0<T → 0<eps T) →
    (Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),eps T/(β*eps T+lam T i))
      (𝓝[>] 0) (𝓝 0) ↔ eps =o[𝓝[>] 0] (fun T:ℝ=>T^(q (Fin.last n))))) ∧
  (∀ α:ℝ,(∀ i,α≠(q i:ℝ)) →
    Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),T^α/(β*T^α+lam T i))
      (𝓝[>] 0) (𝓝 ((1/2:ℝ)*∑ i:Fin (n+1),if α<(q i:ℝ) then β⁻¹ else 0)))
def arena : Arena where
  signature := signature
  Law := theoremLaw

theorem actual_law : arena.Law actual := by
  intro n q hq lam c C β hc hC hβ hbounds
  exact _root_.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics
    n q hq lam c C β hc hC hβ hbounds

theorem modified_law : ¬ arena.Law modified := by
  intro h
  have hb:∀ᶠ T:ℝ in 𝓝[>] 0,∀ i:Fin 1,(1:ℝ)*T^(0:ℕ)≤1 ∧ 1≤2*T^(0:ℕ):=
    Filter.Eventually.of_forall (by intro T i;norm_num)
  have hh:=h 0 (fun _=>0) (fun _=>le_rfl) (fun _ _=>1) 1 2 1
    zero_lt_one (by norm_num) zero_lt_one hb
  have hi:(fun T:ℝ=>(1/2:ℝ)*T⁻¹)=O[𝓝[>] 0] (fun _:ℝ=>(1:ℝ)):=by
    simpa [theoremLaw,modified,realize,Fin.sum_univ_one] using hh.1 0
  obtain ⟨K,hK⟩:=hi.bound
  have hTsmall:∀ᶠ T:ℝ in 𝓝[>] 0,T<(2*(|K|+1))⁻¹:=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (inv_pos.mpr (by positivity)))
  have hpos : ∀ᶠ T : ℝ in 𝓝[>] 0, 0 < T := self_mem_nhdsWithin
  obtain ⟨T,hT,hs,hb⟩ := (hpos.and (hTsmall.and hK)).exists
  have hinv : 2*(|K|+1) < T⁻¹ := lt_inv_of_lt_inv₀ hT hs
  have habs : |(1/2:ℝ)*T⁻¹| ≤ K := by
    simpa only [Real.norm_eq_abs,norm_one,mul_one] using hb
  have hb' : (1/2:ℝ)*T⁻¹ ≤ K := (le_abs_self _).trans habs
  linarith [le_abs_self K]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1,0,1⟩,1,2,?_⟩
  have hlog:Real.log 2<Real.log 3:=Real.log_lt_log (by norm_num) (by norm_num)
  norm_num [actual,realize]
  exact hlog.ne

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,modified,modified_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨modified,?_,rfl,modified_law⟩
      intro other hne
      exact (hne (by cases role;cases other;rfl)).elim
    · intro e;exact nomatch e
  dependence := dependence_proof


noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p x => Real.log (1+x/(p.1*p.2.2^p.2.1))) emptyAnchor)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Linear") "SpectralNoiseAsymptotics") "spectral_noise_asymptotics") "Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics/Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p x => Real.log (1+x/(p.1*p.2.2^p.2.1))) emptyAnchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics, definition := none, coordinates := #[6, 11, 12], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.observationFact0, `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.anchorEnumeration }

end Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics


noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
      Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.actual)
    Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration)

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"spectral_noise_asymptotics\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.arena Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.actual)
  Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration)

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.observation0 : (n : Nat) →
  (q :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Nat) →
    (hq :
        ∀
          (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
          @LE.le.{0} Nat instLENat (q i) (q (Fin.last n))) →
      (lam :
          Real →
            Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real) →
        (c C β : Real) →
          (hc :
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                c) →
            (hC :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  C) →
              (hβ :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β) →
                (hbounds :
                    @Filter.Eventually.{0} Real
                      (fun (T : Real) =>
                        ∀
                          (i :
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
                          And
                            (@LE.le.{0} Real Real.instLE
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  T (q i)))
                              (lam T i))
                            (@LE.le.{0} Real Real.instLE (lam T i)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  T (q i)))))
                      (@nhdsWithin.{0} Real
                        (@UniformSpace.toTopologicalSpace.{0} Real
                          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@Set.Ioi.{0} Real Real.instPreorder
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) →
                  (α T : Real) →
                    (i :
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.signature PUnit.unit.{1}
                        (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) β
                          (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) α T)) :=
  fun (n : Nat)
    (q :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Nat)
    (hq :
      ∀
        (i :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
        @LE.le.{0} Nat instLENat (q i) (q (Fin.last n)))
    (lam :
      Real →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real)
    (c C β : Real)
    (hc : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
    (hC : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
    (hβ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β)
    (hbounds :
      @Filter.Eventually.{0} Real
        (fun (T : Real) =>
          ∀
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
            And
              (@LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) T
                    (q i)))
                (lam T i))
              (@LE.le.{0} Real Real.instLE (lam T i)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) T
                    (q i)))))
        (@nhdsWithin.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@Set.Ioi.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
    (α T : Real)
    (i :
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.signature
    Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) β
      (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) α T))
    (lam T i)

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"spectral_noise_asymptotics\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .function, .argument, .body, .function, .argument, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"spectral_noise_asymptotics\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `D5.S3.Observer.Linear.SpectralNoiseAsymptotics.spectral_noise_asymptotics, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration).actual (Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration).variation.2.choose (Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration).variation.1 (Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Linear\",\"SpectralNoiseAsymptotics\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics, declaration := `Reg.D5.S3.Observer.Linear.SpectralNoiseAsymptotics.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
