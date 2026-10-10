import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness

open _root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- Reader soundness. The parameters are the build system, the reader snapshot and
the lookup schedule; the observed state is the module and the readout is the reader
build artifact. -/
abbrev soundnessSignature : Signature where
  Params := Σ (B : BuildSystem.{u}), Σ (_ : Snapshot B.Node B.Src), B.Node → List (Op B.Node B.Src)
  State p := p.1.Node
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Art
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace only the reader build application. The writers, the collision
hypothesis and the writer-only hypothesis remain in the law. -/
def soundnessArena : Arena where
  signature := soundnessSignature.{u}
  Law r := ∀ (B : BuildSystem.{u}) (writers : Set (Snapshot B.Node B.Src))
    (T : Snapshot B.Node B.Src) (_ : NoCollision B (insert T writers))
    (schedule : B.Node → List (Op B.Node B.Src))
    (_ : ∀ (n : B.Node) (W : Snapshot B.Node B.Src) (m : B.Node),
      Op.store W m ∈ schedule n → W ∈ writers)
    (n : B.Node), r.readout () ⟨B, T, schedule⟩ n = build B T n

noncomputable def soundnessActual : Realization soundnessSignature.{u} :=
  realize soundnessSignature (fun _ p n => cachedBuild p.1 (fun n => run p.1 (p.2.2 n)) p.2.1 n)
    (fun e => nomatch e)

/-- Compile a source against the singleton of its own empty-input artifact. -/
def extraInput (B : BuildSystem.{u}) (s : B.Src) : B.Art := B.compile s {B.compile s ∅}

def soundnessRejected : Realization soundnessSignature.{u} :=
  realize soundnessSignature (fun _ p n => extraInput p.1 (p.2.1.src n)) (fun e => nomatch e)

open Classical in
/-- A compiler that separates the empty dependency set from every nonempty one. -/
noncomputable def emptinessCompile : ULift.{u} ℕ → Set (ULift.{u} ℕ) → ULift.{u} ℕ :=
  fun _ A => if A = ∅ then ⟨0⟩ else ⟨1⟩

/-- One module with no dependencies. -/
def single : Snapshot PUnit.{u + 1} (ULift.{u} ℕ) :=
  { src := fun _ => ⟨0⟩, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

noncomputable def singleSystem : BuildSystem.{u} :=
  ⟨PUnit, ULift ℕ, ULift ℕ, ULift ℕ, ULift ℕ, emptinessCompile, fun _ _ => ⟨0⟩, fun a => a⟩

theorem single_noCollision (writers : Set (Snapshot PUnit.{u + 1} (ULift.{u} ℕ)))
    (only : ∀ W ∈ writers, W = single) : NoCollision singleSystem (insert single writers) := by
  intro X hX Y hY m n _
  have hx : X = single := by
    rcases Set.mem_insert_iff.mp hX with h | h
    · exact h
    · exact only X h
  have hy : Y = single := by
    rcases Set.mem_insert_iff.mp hY with h | h
    · exact h
    · exact only Y h
  subst hx hy
  exact ⟨rfl, rfl⟩

theorem single_build : build singleSystem.{u} single PUnit.unit = ⟨0⟩ := by
  rw [build.eq_1 singleSystem single PUnit.unit]
  simp [singleSystem, emptinessCompile, single]
  exact fun x => Finset.notMem_empty x

theorem soundness_rejected_law : ¬ soundnessArena.{u}.Law soundnessRejected := by
  intro h
  have hl := h singleSystem ∅ single
    (single_noCollision ∅ (fun _ hW => absurd hW (Set.notMem_empty _)))
    (fun _ => []) (fun _ _ _ hm => absurd hm List.not_mem_nil) PUnit.unit
  rw [single_build] at hl
  change emptinessCompile (single.src PUnit.unit) {emptinessCompile (single.src PUnit.unit) ∅} =
    (⟨0⟩ : ULift.{u} ℕ) at hl
  simp [emptinessCompile] at hl

/-- Two dependency-free modules compiled to their own Boolean source. -/
def pair : Snapshot (ULift.{u} Bool) (ULift.{u} Bool) :=
  { src := fun b => b, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

def pairSystem : BuildSystem.{u} :=
  ⟨ULift Bool, ULift Bool, ULift ℕ, ULift ℕ, ULift Bool,
    fun s _ => ⟨if s.down then 1 else 0⟩, fun s _ => s, fun a => a⟩

noncomputable def soundnessRegistration : Registration soundnessArena.{u} (soundnessArena.Law soundnessActual) where
  actual := soundnessActual
  bridge := Iff.rfl
  variation := ⟨by
      intro B writers T noCollision schedule writerOnly n
      exact cachedBuild_eq_build B writers T noCollision schedule writerOnly n,
    soundnessRejected, soundness_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨soundnessRejected, ?_, rfl, soundness_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨pairSystem, pair, fun _ => []⟩, ⟨true⟩, ⟨false⟩, ?_⟩
    change cachedBuild pairSystem (fun n => run pairSystem ([] : List (Op _ _))) pair ⟨true⟩ ≠
      cachedBuild pairSystem (fun n => run pairSystem ([] : List (Op _ _))) pair ⟨false⟩
    rw [cachedBuild.eq_1 pairSystem _ pair ⟨true⟩, cachedBuild.eq_1 pairSystem _ pair ⟨false⟩]
    simp [run, pairSystem, pair]

/-- Restoration. Replace only the reader build application; the writers, both
hypotheses, the writer snapshot, unaffectedness and the stored entry remain in the
law. -/
def restoreArena : Arena where
  signature := soundnessSignature.{u}
  Law r := ∀ (B : BuildSystem.{u}) (writers : Set (Snapshot B.Node B.Src))
    (T : Snapshot B.Node B.Src) (_ : NoCollision B (insert T writers))
    (schedule : B.Node → List (Op B.Node B.Src))
    (_ : ∀ (n : B.Node) (W : Snapshot B.Node B.Src) (m : B.Node),
      Op.store W m ∈ schedule n → W ∈ writers)
    (S : Snapshot B.Node B.Src) (n : B.Node) (_ : Unaffected S T n) (a : B.Art)
    (_ : run B (schedule n) (traceKey B S n) = some a),
    r.readout () ⟨B, T, schedule⟩ n = a

theorem single_unaffected : Unaffected single.{u} single PUnit.unit :=
  Unaffected.intro _ rfl rfl fun _ h => absurd h (Finset.notMem_empty _)

theorem restore_rejected_law : ¬ restoreArena.{u}.Law soundnessRejected := by
  intro h
  have hl := h singleSystem {single} single
    (single_noCollision {single} (fun _ hW => hW))
    (fun _ => [Op.store single PUnit.unit])
    (fun _ W _ hm => by
      rw [List.mem_singleton] at hm
      cases hm
      exact Set.mem_singleton _)
    single PUnit.unit single_unaffected (build singleSystem single PUnit.unit) (by
      classical
      simp only [run, List.foldl_cons, List.foldl_nil, Op.apply, Function.update_self])
  rw [single_build] at hl
  change emptinessCompile (single.src PUnit.unit) {emptinessCompile (single.src PUnit.unit) ∅} =
    (⟨0⟩ : ULift.{u} ℕ) at hl
  simp [emptinessCompile] at hl

noncomputable def restoreRegistration : Registration restoreArena.{u}
    (restoreArena.Law soundnessActual) where
  actual := soundnessActual
  bridge := Iff.rfl
  variation := ⟨by
      intro B writers T noCollision schedule writerOnly S n unaffected a present
      exact cachedBuild_restores_unaffected B writers T noCollision schedule writerOnly S n
        unaffected a present,
    soundnessRejected, restore_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨soundnessRejected, ?_, rfl, restore_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := soundnessRegistration.dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.cachedBuild_eq_build.{u})
    (type_of% (realize.{u + 1, u, 0, u, 0} soundnessSignature.{u}
    (fun (_ : Unit) (p : soundnessSignature.{u}.Params) (n : soundnessSignature.{u}.State p) =>
      cachedBuild p.1 (fun n => run p.1 (p.2.2 n)) p.2.1 n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.anonymous) "D5") "S3") "ConceptDynamics") "Governance") "TraceKeyedArtifactCacheSoundness") "cachedBuild_eq_build") "Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness/Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.soundnessArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.soundnessRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(soundnessArena.{u})⟩,
  objectArena := .source ⟨(soundnessArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (soundnessArena.{u}) ⟨(soundnessRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} soundnessSignature.{u}
    (fun (_ : Unit) (p : soundnessSignature.{u}.Params) (n : soundnessSignature.{u}.State p) =>
      cachedBuild p.1 (fun n => run p.1 (p.2.2 n)) p.2.1 n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness, definition := none, coordinates := #[0, 2, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.cachedBuild_restores_unaffected.{u})
    (type_of% (realize.{u + 1, u, 0, u, 0} soundnessSignature.{u}
    (fun (_ : Unit) (p : soundnessSignature.{u}.Params) (n : soundnessSignature.{u}.State p) =>
      cachedBuild p.1 (fun n => run p.1 (p.2.2 n)) p.2.1 n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.anonymous) "D5") "S3") "ConceptDynamics") "Governance") "TraceKeyedArtifactCacheSoundness") "cachedBuild_restores_unaffected") "Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness/Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.restoreArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.restoreRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(restoreArena.{u})⟩,
  objectArena := .source ⟨(restoreArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (restoreArena.{u}) ⟨(restoreRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} soundnessSignature.{u}
    (fun (_ : Unit) (p : soundnessSignature.{u}.Params) (n : soundnessSignature.{u}.State p) =>
      cachedBuild p.1 (fun n => run p.1 (p.2.2 n)) p.2.1 n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness, definition := none, coordinates := #[0, 2, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms soundnessRegistration
#print axioms restoreRegistration

end Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
