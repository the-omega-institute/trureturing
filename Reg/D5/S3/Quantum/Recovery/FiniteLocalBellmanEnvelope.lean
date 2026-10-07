import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope

abbrev signature : Signature where
  Params := ℝ
  State _ := State
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ r z => VInfinity r z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def originalStatement : Prop := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1 / 2 < r ^ 2) (hhi : r ^ 2 < 2),
    (IsCompact (K_s r)) ∧
    (∀ n, Admissible r (V r n)) ∧
    (∀ n z, V r n z ≤ V r (n+1) z) ∧
    (∀ n actor z,
      (∃ s : Split 5 (active actor z),
        fiveValue actor (V r n) z =
          ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ∧
      (∀ m (s : Split m (active actor z)),
        (∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor (V r n) z)) ∧
    (∀ n z,
      (∃ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z)) ∧
    (∀ z, VInfinity r z = treeValue r z ∧
      0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ u : State → ℝ, SeparatelyConcave u →
      (∀ z, terminal r z ≤ u z) → ∀ z, VInfinity r z ≤ u z) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r)

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1 / 2 < r ^ 2) (hhi : r ^ 2 < 2),
    (IsCompact (K_s r)) ∧
    (∀ n, Admissible r (V r n)) ∧
    (∀ n z, V r n z ≤ V r (n+1) z) ∧
    (∀ n actor z,
      (∃ s : Split 5 (active actor z),
        fiveValue actor (V r n) z =
          ∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ∧
      (∀ m (s : Split m (active actor z)),
        (∑ i, s.w i * V r n (place actor (s.x i) (passive actor z))) ≤
          fiveValue actor (V r n) z)) ∧
    (∀ n z,
      (∃ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n ∧ T.reward (terminal r) = V r n z) ∧
      (∀ T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z, T.depth ≤ n → T.reward (terminal r) ≤ V r n z)) ∧
    (∀ z, R.readout () r z = treeValue r z ∧
      0 ≤ VInfinity r z ∧ VInfinity r z ≤ h r) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ u : State → ℝ, SeparatelyConcave u →
      (∀ z, terminal r z ≤ u z) → ∀ z, VInfinity r z ≤ u z) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r)

theorem actual_law : arena.Law actual := source_bellman_finite_tree_identity

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let zero : Ball := ⟨0,by simp⟩
  have hb := bad 1 (by norm_num) (by norm_num) (by norm_num)
  have ha := source_bellman_finite_tree_identity 1 (by norm_num) (by norm_num) (by norm_num)
  have he := (hb.2.2.2.2.2.1 (zero,zero)).1
  have hg := (ha.2.2.2.2.2.1 (zero,zero)).2.1
  have hv := (ha.2.2.2.2.2.1 (zero,zero)).1
  change -1 = treeValue 1 (zero,zero) at he
  rw [← hv] at he
  linarith

def registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨⟨a,b⟩,hab⟩ := (all_r_flat_geometry 1 (by norm_num) (by norm_num) (by norm_num)).2.2.2.1
    let x : Ball := ⟨a,by simpa only [Metric.mem_closedBall,dist_zero_right,hab.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    let y : Ball := ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right,hab.2.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    have ha := source_bellman_finite_tree_identity 1 (by norm_num) (by norm_num) (by norm_num)
    have hflat := ha.2.2.2.2.2.2.2.2.2.1 (x,y) hab
    have hdiag := ha.2.2.2.2.2.2.2.2.2.2.1 x hab.1
    refine ⟨(1 : ℝ),(x,y),(x,x),?_⟩
    change VInfinity 1 (x,y) ≠ VInfinity 1 (x,x)
    rw [hflat.1,hdiag.1]
    unfold h kappa
    positivity

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ r z => VInfinity r z) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "FiniteLocalBellmanEnvelope") "source_bellman_finite_tree_identity") "Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope/Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ r z => VInfinity r z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena
    Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.originalStatement
    Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"source_bellman_finite_tree_identity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.arena
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.originalStatement
  Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.observation0 : (r : Real) →
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
    (hlo :
        @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      (hhi :
          @LT.lt.{0} Real Real.instLT
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        (z : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.signature Unit.unit r :=
  fun (r : Real)
    (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (hlo :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhi :
      @LT.lt.{0} Real Real.instLT
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (z : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.signature
    Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.actual Unit.unit r z

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"source_bellman_finite_tree_identity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity, part := .type, path := [.body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .function, .argument, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"source_bellman_finite_tree_identity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration).actual (Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration).variation.2.choose (Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration).variation.1 (Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
