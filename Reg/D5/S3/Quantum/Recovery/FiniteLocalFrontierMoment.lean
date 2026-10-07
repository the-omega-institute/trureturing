import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
abbrev BT := D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree

abbrev signature : Signature where
  Params := (z : State) × BT z
  State p := p.2.Leaves → Bool
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ p m => failureDefect p.2 m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) (z : State) (T : BT z)
    (mark : T.Leaves → Bool)
    (accepted : ∀ l, mark l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r),
    (0 ≤ failureDefect T mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark)) ∧
    4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
    U r-H r^3/(49152*kappa r) < U r ∧
    H r^3/(196608*kappa r) ≤ psi r origin

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) (z : State) (T : BT z)
    (mark : T.Leaves → Bool)
    (accepted : ∀ l, mark l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r),
    (0 ≤ R.readout () ⟨z,T⟩ mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark)) ∧
    4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
    U r-H r^3/(49152*kappa r) < U r ∧
    H r^3/(196608*kappa r) ≤ psi r origin

theorem actual_law : arena.Law actual := same_tree_stopped_moment_certificate

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let zero : Ball := ⟨0,by simp⟩
  let z : State := (zero,zero)
  let T : BT z := .stop z
  have acc : ∀ l : T.Leaves, (fun _ => false) l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s 1 := by simp
  have hn := (bad 1 (by norm_num) (by norm_num) (by norm_num) z T (fun _ => false) acc).1.1
  change 0 ≤ (-1 : ℝ) at hn
  linarith

def registration : Registration arena sourceStatement where
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
    let zero : Ball := ⟨0,by simp⟩
    let z : State := (zero,zero)
    let T : BT z := .stop z
    refine ⟨⟨z,T⟩,(fun _ => false),(fun _ => true),?_⟩
    change failureDefect T (fun _ => false) ≠ failureDefect T (fun _ => true)
    norm_num [failureDefect,T,D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.expect,D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint,d,defect,z,zero]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.same_tree_stopped_moment_certificate) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p m => failureDefect p.2 m) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "FiniteLocalBellmanEnvelope") "same_tree_stopped_moment_certificate") "Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment/Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p m => failureDefect p.2 m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, definition := none, coordinates := #[4, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.same_tree_stopped_moment_certificate, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena
    Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.sourceStatement
    Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"same_tree_stopped_moment_certificate\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.same_tree_stopped_moment_certificate, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.arena
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.sourceStatement
  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.observation0 : (r : Real) →
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
          (T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z) →
            (mark : @D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.Leaves z T → Bool) →
              (accepted :
                  ∀ (l : @D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.Leaves z T),
                    @Eq.{1} Bool (mark l) Bool.true →
                      @Membership.mem.{0, 0}
                        (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                          D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                        (Set.{0}
                          (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                            D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                        (@Set.instMembership.{0}
                          (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                            D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                        (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r)
                        (@Prod.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                          D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                          (@Subtype.val.{1} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                            (fun (x : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch) =>
                              @Membership.mem.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                (Set.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                                (@Set.instMembership.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball x)
                            (@Prod.fst.{0, 0}
                              (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                              (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                              (@D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint z T l)))
                          (@Subtype.val.{1} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                            (fun (x : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch) =>
                              @Membership.mem.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                (Set.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                                (@Set.instMembership.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball x)
                            (@Prod.snd.{0, 0}
                              (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                              (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                                D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                              (@D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint z T l))))) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.signature Unit.unit
                  (@Sigma.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State
                    (fun (z : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State) =>
                      Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.BT z)
                    z T) :=
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
    (z : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State)
    (T : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree z)
    (mark : @D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.Leaves z T → Bool)
    (accepted :
      ∀ (l : @D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.Leaves z T),
        @Eq.{1} Bool (mark l) Bool.true →
          @Membership.mem.{0, 0}
            (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
              D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
            (Set.{0}
              (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
            (@Set.instMembership.{0}
              (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
            (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r)
            (@Prod.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
              D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
              (@Subtype.val.{1} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                (fun (x : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch) =>
                  @Membership.mem.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    (Set.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                    (@Set.instMembership.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball x)
                (@Prod.fst.{0, 0}
                  (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                  (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                  (@D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint z T l)))
              (@Subtype.val.{1} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                (fun (x : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch) =>
                  @Membership.mem.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    (Set.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                    (@Set.instMembership.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball x)
                (@Prod.snd.{0, 0}
                  (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                  (@Set.Elem.{0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Ball)
                  (@D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint z T l))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.signature
    Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.actual Unit.unit
    (@Sigma.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State
      (fun (z : D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State) =>
        Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.BT z)
      z T)
    mark

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"same_tree_stopped_moment_certificate\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.same_tree_stopped_moment_certificate, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalBellmanEnvelope\",\"same_tree_stopped_moment_certificate\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.same_tree_stopped_moment_certificate, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration).actual (Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration).variation.2.choose (Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration).variation.1 (Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalFrontierMoment\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
