import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness

open _root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x y

/-- The carriers, decision dictionaries, compiler, key and digest functions, the
reader snapshot and the lookup schedule. The writers and both hypotheses stay in
the law. -/
structure Params : Type (max (u + 1) (v + 1) (w + 1) (x + 1) (y + 1)) where
  Node : Type u
  Src : Type v
  Art : Type w
  Dig : Type x
  Key : Type y
  instArt : DecidableEq Art
  instDig : DecidableEq Dig
  compile : Src → Finset Art → Art
  hash : Src → Finset Dig → Key
  digest : Art → Dig
  instKey : DecidableEq Key
  T : Snapshot Node Src
  schedule : Node → List (Op Node Src)

/-- Reader soundness: the observed state is the module; the readout is the reader
build artifact. -/
abbrev soundnessSignature : Signature where
  Params := Params.{u,v,w,x,y}
  State p := p.Node
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Art
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace only the reader build application. The writers, the collision
hypothesis and the writer-only hypothesis remain in the law. -/
def soundnessArena : Arena where
  signature := soundnessSignature.{u,v,w,x,y}
  Law r := ∀ {Node : Type u} {Src : Type v} {Art : Type w} {Dig : Type x} {Key : Type y}
    [instArt : DecidableEq Art] [instDig : DecidableEq Dig]
    (compile : Src → Finset Art → Art) (hash : Src → Finset Dig → Key) (digest : Art → Dig)
    [instKey : DecidableEq Key] (writers : Set (Snapshot Node Src)) (T : Snapshot Node Src)
    (_ : NoCollision compile hash digest (insert T writers))
    (schedule : Node → List (Op Node Src))
    (_ : ∀ (n : Node) (W : Snapshot Node Src) (m : Node), Op.store W m ∈ schedule n → W ∈ writers)
    (n : Node),
    r.readout () ⟨Node, Src, Art, Dig, Key, instArt, instDig, compile, hash, digest, instKey,
      T, schedule⟩ n = build compile T n

def soundnessActual : Realization soundnessSignature.{u,v,w,x,y} :=
  realize soundnessSignature (fun _ p n => @cachedBuild p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
    p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
      p.digest p.instKey (p.schedule n)) p.T n) (fun e => nomatch e)

/-- Compile a source against the singleton of its own empty-input artifact. -/
def extraInput {Src : Type v} {Art : Type w} (compile : Src → Finset Art → Art) (s : Src) : Art :=
  compile s {compile s ∅}

/-- Compile against one extra artifact: it changes the artifact count. -/
def soundnessRejected : Realization soundnessSignature.{u,v,w,x,y} :=
  realize soundnessSignature (fun _ p n =>
    extraInput p.compile (p.T.src n)) (fun e => nomatch e)

/-- One module without dependencies, compiled to its dependency count. -/
def single : Snapshot PUnit.{u + 1} (ULift.{v} ℕ) :=
  { src := fun _ => ⟨0⟩, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

def countCompile : ULift.{v} ℕ → Finset (ULift.{w} ℕ) → ULift.{w} ℕ :=
  fun _ A => ⟨A.card⟩

theorem single_noCollision (hash : ULift.{v} ℕ → Finset (ULift.{x} ℕ) → ULift.{y} ℕ)
    (digest : ULift.{w} ℕ → ULift.{x} ℕ) :
    NoCollision countCompile hash digest (insert single.{u,v} ∅) := by
  intro X hX Y hY m n _
  rw [Set.mem_insert_iff] at hX hY
  rcases hX with rfl | hX
  · rcases hY with rfl | hY
    · exact ⟨rfl, rfl⟩
    · exact absurd hY (Set.notMem_empty _)
  · exact absurd hX (Set.notMem_empty _)

theorem single_build :
    build countCompile.{v,w} single.{u,v} PUnit.unit = (⟨0⟩ : ULift.{w} ℕ) := by
  rw [build]
  rfl

theorem soundness_rejected_law : ¬ soundnessArena.{u,v,w,x,y}.Law soundnessRejected := by
  intro h
  have hl := h (Node := PUnit.{u + 1}) (Src := ULift.{v} ℕ) (Art := ULift.{w} ℕ)
    (Dig := ULift.{x} ℕ) (Key := ULift.{y} ℕ) countCompile (fun _ _ => ⟨0⟩)
    (fun a => ⟨a.down⟩) ∅ single (single_noCollision _ _) (fun _ => [])
    (fun _ _ _ hm => absurd hm (List.not_mem_nil)) PUnit.unit
  rw [single_build] at hl
  change (⟨({(⟨0⟩ : ULift.{w} ℕ)} : Finset (ULift.{w} ℕ)).card⟩ : ULift.{w} ℕ) = ⟨0⟩ at hl
  simp at hl

/-- Two dependency-free modules compiled to their own Boolean source. -/
def pair : Snapshot (ULift.{u} Bool) (ULift.{v} Bool) :=
  { src := fun b => ⟨b.down⟩, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

def bitCompile : ULift.{v} Bool → Finset (ULift.{w} ℕ) → ULift.{w} ℕ :=
  fun s _ => ⟨if s.down then 1 else 0⟩

def soundnessRegistration : Registration soundnessArena.{u,v,w,x,y}
    (soundnessArena.Law soundnessActual) where
  actual := soundnessActual
  bridge := Iff.rfl
  variation := ⟨by
      intro Node Src Art Dig Key _ _ compile hash digest _ writers T noCollision schedule
        writerOnly n
      exact cachedBuild_eq_build compile hash digest writers T noCollision schedule writerOnly n,
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
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, ULift.{w} ℕ, ULift.{x} ℕ, ULift.{y} ℕ,
      inferInstance, inferInstance, bitCompile, fun _ _ => ⟨0⟩, fun a => ⟨a.down⟩,
      inferInstance, pair, fun _ => []⟩, ⟨true⟩, ⟨false⟩, ?_⟩
    change cachedBuild bitCompile (fun _ _ => (⟨0⟩ : ULift.{y} ℕ))
        (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ))
        (fun n => run bitCompile (fun _ _ => (⟨0⟩ : ULift.{y} ℕ))
          (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ)) ([] : List (Op _ _)))
        pair ⟨true⟩ ≠
      cachedBuild bitCompile (fun _ _ => (⟨0⟩ : ULift.{y} ℕ))
        (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ))
        (fun n => run bitCompile (fun _ _ => (⟨0⟩ : ULift.{y} ℕ))
          (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ)) ([] : List (Op _ _)))
        pair ⟨false⟩
    rw [cachedBuild, cachedBuild]
    simp [run, pair, bitCompile]

/-- Restoration: the observed state is the module; the readout is the proposition
that the reader restores it. -/
abbrev restoreSignature : Signature where
  Params := Params.{u,v,w,x,y}
  State p := p.Node
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace only the restoration proposition. The writers, both hypotheses, the
writer snapshot, unaffectedness and the present entry remain in the law. -/
def restoreArena : Arena where
  signature := restoreSignature.{u,v,w,x,y}
  Law r := ∀ {Node : Type u} {Src : Type v} {Art : Type w} {Dig : Type x} {Key : Type y}
    [instArt : DecidableEq Art] [instDig : DecidableEq Dig]
    (compile : Src → Finset Art → Art) (hash : Src → Finset Dig → Key) (digest : Art → Dig)
    [instKey : DecidableEq Key] (writers : Set (Snapshot Node Src)) (T : Snapshot Node Src)
    (_ : NoCollision compile hash digest (insert T writers))
    (schedule : Node → List (Op Node Src))
    (_ : ∀ (n : Node) (W : Snapshot Node Src) (m : Node), Op.store W m ∈ schedule n → W ∈ writers)
    (S : Snapshot Node Src) (n : Node) (_ : Unaffected S T n)
    (_ : ∃ a, run compile hash digest (schedule n) (traceKey compile hash digest S n) = some a),
    r.readout () ⟨Node, Src, Art, Dig, Key, instArt, instDig, compile, hash, digest, instKey,
      T, schedule⟩ n

def restoreActual : Realization restoreSignature.{u,v,w,x,y} :=
  realize restoreSignature (fun _ p n => @Restores p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
    p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
      p.digest p.instKey (p.schedule n)) p.T n) (fun e => nomatch e)

def restoreRejected : Realization restoreSignature.{u,v,w,x,y} :=
  realize restoreSignature (fun _ _ _ => False) (fun e => nomatch e)

theorem single_unaffected : Unaffected single.{u,v} single PUnit.unit :=
  Unaffected.intro _ rfl rfl fun _ h => absurd h (Finset.notMem_empty _)

theorem restore_rejected_law : ¬ restoreArena.{u,v,w,x,y}.Law restoreRejected := by
  intro h
  exact h (Node := PUnit.{u + 1}) (Src := ULift.{v} ℕ) (Art := ULift.{w} ℕ)
    (Dig := ULift.{x} ℕ) (Key := ULift.{y} ℕ) countCompile (fun _ _ => ⟨0⟩)
    (fun a => ⟨a.down⟩) {single} single (by
      rw [Set.insert_eq_of_mem (Set.mem_singleton _)]
      intro X hX Y hY m n _
      rw [Set.mem_singleton_iff] at hX hY
      subst hX hY
      exact ⟨rfl, rfl⟩)
    (fun _ => [Op.store single PUnit.unit])
    (fun _ W _ hm => by
      rw [List.mem_singleton] at hm
      cases hm
      exact Set.mem_singleton _)
    single PUnit.unit single_unaffected
    ⟨_, by
      simp only [run, List.foldl_cons, List.foldl_nil, Op.apply, Function.update_self]
      rfl⟩

def restoreRegistration : Registration restoreArena.{u,v,w,x,y}
    (restoreArena.Law restoreActual) where
  actual := restoreActual
  bridge := Iff.rfl
  variation := ⟨by
      intro Node Src Art Dig Key _ _ compile hash digest _ writers T noCollision schedule
        writerOnly S n unaffected present
      exact cachedBuild_restores_unaffected compile hash digest writers T noCollision schedule
        writerOnly S n unaffected present,
    restoreRejected, restore_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨restoreRejected, ?_, rfl, restore_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, ULift.{w} ℕ, ULift.{x} ℕ, ULift.{y} Bool,
      inferInstance, inferInstance, bitCompile, fun s _ => ⟨s.down⟩, fun a => ⟨a.down⟩,
      inferInstance, pair, fun _ => [Op.store pair ⟨true⟩]⟩, ⟨true⟩, ⟨false⟩, ?_⟩
    intro h
    have restored : Restores bitCompile (fun s (_ : Finset (ULift.{x} ℕ)) => (⟨s.down⟩ : ULift.{y} Bool))
        (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ))
        (fun _ => run bitCompile (fun s (_ : Finset (ULift.{x} ℕ)) => (⟨s.down⟩ : ULift.{y} Bool))
          (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ)) [Op.store pair ⟨true⟩])
        pair ⟨true⟩ :=
      ⟨_, by
        simp only [run, List.foldl_cons, List.foldl_nil, Op.apply]
        rw [show (⟨(pair.{u,v}.src ⟨true⟩).down⟩ : ULift.{y} Bool) = traceKey bitCompile
            (fun s (_ : Finset (ULift.{x} ℕ)) => (⟨s.down⟩ : ULift.{y} Bool))
            (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ)) pair ⟨true⟩ from rfl]
        exact Function.update_self _ _ _⟩
    have notRestored : ¬ Restores bitCompile.{v,w} (fun (s : ULift.{v} Bool) (_ : Finset (ULift.{x} ℕ)) => (⟨s.down⟩ : ULift.{y} Bool))
        (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ))
        (fun (_ : ULift.{u} Bool) => run bitCompile.{v,w} (fun (s : ULift.{v} Bool) (_ : Finset (ULift.{x} ℕ)) => (⟨s.down⟩ : ULift.{y} Bool))
          (fun a : ULift.{w} ℕ => (⟨a.down⟩ : ULift.{x} ℕ)) [Op.store pair.{u,v} (⟨true⟩ : ULift.{u} Bool)])
        pair.{u,v} (⟨false⟩ : ULift.{u} Bool) := by
      rintro ⟨a, ha⟩
      simp [run, Op.apply, traceKey, pair] at ha
    exact notRestored (cast h restored)


noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.cachedBuild_eq_build.{u,v,w,x,y})
    (type_of% (realize.{max (u + 1) (v + 1) (w + 1) (x + 1) (y + 1), u, 0, w, 0} soundnessSignature.{u,v,w,x,y}
    (fun (_ : Unit) (p : soundnessSignature.{u,v,w,x,y}.Params)
      (n : soundnessSignature.{u,v,w,x,y}.State p) =>
      @cachedBuild p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
        p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile
          p.hash p.digest p.instKey (p.schedule n)) p.T n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.anonymous) "D5") "S3") "ConceptDynamics") "Governance") "TraceKeyedArtifactCacheSoundness") "cachedBuild_eq_build") "Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness/Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.soundnessArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.soundnessRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(soundnessArena.{u,v,w,x,y})⟩,
  objectArena := .source ⟨(soundnessArena.{u,v,w,x,y})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (soundnessArena.{u,v,w,x,y}) ⟨(soundnessRegistration.{u,v,w,x,y})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1) (w + 1) (x + 1) (y + 1), u, 0, w, 0} soundnessSignature.{u,v,w,x,y}
    (fun (_ : Unit) (p : soundnessSignature.{u,v,w,x,y}.Params)
      (n : soundnessSignature.{u,v,w,x,y}.State p) =>
      @cachedBuild p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
        p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile
          p.hash p.digest p.instKey (p.schedule n)) p.T n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness, definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.cachedBuild_restores_unaffected.{u,v,w,x,y})
    (type_of% (realize.{max (u + 1) (v + 1) (w + 1) (x + 1) (y + 1), u, 0, 0, 0} restoreSignature.{u,v,w,x,y}
    (fun (_ : Unit) (p : restoreSignature.{u,v,w,x,y}.Params)
      (n : restoreSignature.{u,v,w,x,y}.State p) =>
      @Restores p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
        p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile
          p.hash p.digest p.instKey (p.schedule n)) p.T n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.anonymous) "D5") "S3") "ConceptDynamics") "Governance") "TraceKeyedArtifactCacheSoundness") "cachedBuild_restores_unaffected") "Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness/Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.restoreArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness.restoreRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(restoreArena.{u,v,w,x,y})⟩,
  objectArena := .source ⟨(restoreArena.{u,v,w,x,y})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (restoreArena.{u,v,w,x,y}) ⟨(restoreRegistration.{u,v,w,x,y})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u + 1) (v + 1) (w + 1) (x + 1) (y + 1), u, 0, 0, 0} restoreSignature.{u,v,w,x,y}
    (fun (_ : Unit) (p : restoreSignature.{u,v,w,x,y}.Params)
      (n : restoreSignature.{u,v,w,x,y}.State p) =>
      @Restores p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile p.hash
        p.digest (fun n => @run p.Node p.Src p.Art p.Dig p.Key p.instArt p.instDig p.compile
          p.hash p.digest p.instKey (p.schedule n)) p.T n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness, definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body"], stateBinder := 17, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms soundnessRegistration
#print axioms restoreRegistration

end Reg.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
