/- GID: D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: Writer-filled trace-keyed caches yield from-scratch builds and hit unaffected modules. -/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Image
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness

universe u v

/-- A build system: modules, sources, artifacts, digests and keys, with a compiler
from a source and a set of dependency artifacts, a key function from a source and
a set of digests, and an artifact digest. -/
structure BuildSystem where
  Node : Type u
  Src : Type u
  Art : Type u
  Dig : Type u
  Key : Type u
  compile : Src → Set Art → Art
  hash : Src → Set Dig → Key
  digest : Art → Dig

/-- A build snapshot. Every module has a source input and the finite set of
modules whose artifacts its build reads; a natural-number rank strictly
decreases along every such dependency, so the dependency graph is acyclic. -/
structure Snapshot (Node : Type u) (Src : Type v) where
  src : Node → Src
  deps : Node → Finset Node
  rank : Node → ℕ
  rank_lt : ∀ n, ∀ d ∈ deps n, rank d < rank n

/-- A cache operation: store the from-scratch artifact of module `m` of a writer
snapshot `W` under its key, or delete every entry. -/
inductive Op (Node : Type u) (Src : Type v) where
  | store (W : Snapshot Node Src) (m : Node)
  | clean

variable (B : BuildSystem.{u})

/-- From-scratch build: the artifact of `n` is its source compiled against the
artifacts of its dependencies. -/
def build (S : Snapshot B.Node B.Src) (n : B.Node) : B.Art :=
  B.compile (S.src n) (Set.range fun d : {d // d ∈ S.deps n} => build S d.1)
termination_by S.rank n
decreasing_by exact S.rank_lt n d.1 d.2

private theorem range_attach_eq {α β : Type*} (s : Finset α) (f : α → β) :
    (Set.range fun d : {d // d ∈ s} => f d.1) = f '' ↑s := by
  ext b
  simp

private theorem build_eq (S : Snapshot B.Node B.Src) (n : B.Node) :
    build B S n = B.compile (S.src n) (build B S '' ↑(S.deps n)) := by
  rw [build, range_attach_eq]

/-- The cache key of `n`: its source together with the content digests of its
dependencies' artifacts. -/
def traceKey (S : Snapshot B.Node B.Src) (n : B.Node) : B.Key :=
  B.hash (S.src n) (B.digest '' (build B S '' ↑(S.deps n)))

/-- No collision among the build inputs realized by the snapshots in `𝒮`: equal
keys come from equal sources and equal sets of dependency artifacts. -/
def NoCollision (𝒮 : Set (Snapshot B.Node B.Src)) : Prop :=
  ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, ∀ m n, traceKey B X m = traceKey B Y n →
    X.src m = Y.src n ∧ build B X '' ↑(X.deps m) = build B Y '' ↑(Y.deps n)

open Classical in
/-- Apply one cache operation to a cache state. -/
noncomputable def Op.apply : Op B.Node B.Src → (B.Key → Option B.Art) → B.Key → Option B.Art
  | .store W m, c => Function.update c (traceKey B W m) (some (build B W m))
  | .clean, _ => fun _ => none

/-- The cache state after a sequence of operations applied to the empty cache. -/
noncomputable def run (ops : List (Op B.Node B.Src)) : B.Key → Option B.Art :=
  ops.foldl (fun c o => o.apply B c) fun _ => none

/-- Every entry of the cache is the from-scratch artifact of some module of some
writer snapshot, stored under that module's key. -/
def Sound (writers : Set (Snapshot B.Node B.Src)) (c : B.Key → Option B.Art) : Prop :=
  ∀ k a, c k = some a → ∃ W ∈ writers, ∃ m, traceKey B W m = k ∧ build B W m = a

/-- The reader build of snapshot `T`. The reader computes the key of `n` from its
own dependency artifacts and looks it up in the cache state `look n`; on a hit it
restores the stored artifact, otherwise it compiles `n`. -/
def cachedBuild (look : B.Node → B.Key → Option B.Art) (T : Snapshot B.Node B.Src)
    (n : B.Node) : B.Art :=
  match look n (B.hash (T.src n)
      (B.digest '' Set.range fun d : {d // d ∈ T.deps n} => cachedBuild look T d.1)) with
  | some a => a
  | none => B.compile (T.src n) (Set.range fun d : {d // d ∈ T.deps n} => cachedBuild look T d.1)
termination_by T.rank n
decreasing_by all_goals exact T.rank_lt n d.1 d.2

private theorem cachedBuild_eq (look : B.Node → B.Key → Option B.Art)
    (T : Snapshot B.Node B.Src) (n : B.Node) :
    cachedBuild B look T n =
      match look n (B.hash (T.src n) (B.digest '' (cachedBuild B look T '' ↑(T.deps n)))) with
      | some a => a
      | none => B.compile (T.src n) (cachedBuild B look T '' ↑(T.deps n)) := by
  rw [cachedBuild, range_attach_eq]

/-- `n` is unaffected between a writer snapshot `S` and a reader snapshot `T`: it
has the same source and dependency set in both, and every dependency is
unaffected. -/
inductive Unaffected {Node : Type u} {Src : Type v} (S T : Snapshot Node Src) : Node → Prop where
  | intro (n : Node) : S.src n = T.src n → S.deps n = T.deps n →
      (∀ d ∈ T.deps n, Unaffected S T d) → Unaffected S T n

private theorem build_eq_of_keys
    {𝒮 : Set (Snapshot B.Node B.Src)} (noCollision : NoCollision B 𝒮)
    {X Y : Snapshot B.Node B.Src} (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) {m n : B.Node}
    (keys : traceKey B X m = traceKey B Y n) : build B X m = build B Y n := by
  obtain ⟨sources, artifacts⟩ := noCollision X hX Y hY m n keys
  rw [build_eq, build_eq, sources, artifacts]

private theorem run_sound (writers : Set (Snapshot B.Node B.Src))
    (ops : List (Op B.Node B.Src)) (writerOnly : ∀ W m, Op.store W m ∈ ops → W ∈ writers) :
    Sound B writers (run B ops) := by
  unfold run
  suffices step : ∀ (rest : List (Op B.Node B.Src)) (c : B.Key → Option B.Art),
      (∀ W m, Op.store W m ∈ rest → W ∈ writers) → Sound B writers c →
      Sound B writers (rest.foldl (fun c o => o.apply B c) c) by
    apply step ops _ writerOnly
    intro k a h
    exact absurd h (by simp)
  intro rest
  induction rest with
  | nil => intro c _ sound; exact sound
  | cons o rest ih =>
    intro c onlyWriters sound
    rw [List.foldl_cons]
    apply ih
    · intro W m mem
      exact onlyWriters W m (List.mem_cons_of_mem o mem)
    · cases o with
      | store W m =>
        intro k a entry
        classical
        by_cases same : k = traceKey B W m
        · subst same
          simp only [Op.apply, Function.update_self, Option.some.injEq] at entry
          exact ⟨W, onlyWriters W m List.mem_cons_self, m, rfl, entry⟩
        · simp only [Op.apply] at entry
          rw [Function.update_of_ne same] at entry
          exact sound k a entry
      | clean =>
        intro k a entry
        simp [Op.apply] at entry

private theorem cachedBuild_eq_build_of_sound
    (writers : Set (Snapshot B.Node B.Src)) (T : Snapshot B.Node B.Src)
    (noCollision : NoCollision B (insert T writers))
    (look : B.Node → B.Key → Option B.Art)
    (sound : ∀ n, Sound B writers (look n)) (n : B.Node) :
    cachedBuild B look T n = build B T n := by
  induction hr : T.rank n using Nat.strong_induction_on generalizing n with
  | _ r ih =>
    have depsEq : cachedBuild B look T '' ↑(T.deps n) = build B T '' ↑(T.deps n) := by
      apply Set.image_congr
      intro d hd
      exact ih (T.rank d) (hr ▸ T.rank_lt n d hd) d rfl
    rw [cachedBuild_eq, depsEq]
    have keyEq : B.hash (T.src n) (B.digest '' (build B T '' ↑(T.deps n))) =
        traceKey B T n := rfl
    rw [keyEq]
    cases hit : look n (traceKey B T n) with
    | none => exact (build_eq B T n).symm
    | some a =>
      obtain ⟨W, hW, m, keys, built⟩ := sound n _ a hit
      rw [← built]
      exact build_eq_of_keys B noCollision
        (Set.mem_insert_of_mem T hW) (Set.mem_insert T writers) keys

/-- Reader soundness under arbitrary interleaving. Let every cache state the
reader consults be reached from the empty cache by stores of writer snapshots and
cleans, in any order and possibly different for each module. If no two build
inputs realized by the writers and the reader share a key, the reader build of
every module equals its from-scratch build. -/
theorem cachedBuild_eq_build
    (writers : Set (Snapshot B.Node B.Src)) (T : Snapshot B.Node B.Src)
    (noCollision : NoCollision B (insert T writers))
    (schedule : B.Node → List (Op B.Node B.Src))
    (writerOnly : ∀ n W m, Op.store W m ∈ schedule n → W ∈ writers) (n : B.Node) :
    cachedBuild B (fun n => run B (schedule n)) T n = build B T n :=
  cachedBuild_eq_build_of_sound B writers T noCollision _
    (fun n => run_sound B writers (schedule n) (writerOnly n)) n

private theorem build_eq_of_unaffected {S T : Snapshot B.Node B.Src} {n : B.Node}
    (unaffected : Unaffected S T n) : build B S n = build B T n := by
  induction unaffected with
  | intro n sources deps _ ih =>
    rw [build_eq, build_eq, sources, deps]
    congr 1
    exact Set.image_congr fun d hd => ih d hd

/-- Unaffected modules are restored, not compiled. Under the hypotheses of
`cachedBuild_eq_build`, if `n` is unaffected between a snapshot `S` and the reader
snapshot `T`, and the cache state consulted for `n` holds an artifact `a` under the
key of `n` in `S`, then the reader's artifact for `n` is that stored `a`. -/
theorem cachedBuild_restores_unaffected
    (writers : Set (Snapshot B.Node B.Src)) (T : Snapshot B.Node B.Src)
    (noCollision : NoCollision B (insert T writers))
    (schedule : B.Node → List (Op B.Node B.Src))
    (writerOnly : ∀ n W m, Op.store W m ∈ schedule n → W ∈ writers)
    (S : Snapshot B.Node B.Src) (n : B.Node) (unaffected : Unaffected S T n) (a : B.Art)
    (present : run B (schedule n) (traceKey B S n) = some a) :
    cachedBuild B (fun n => run B (schedule n)) T n = a := by
  cases unaffected with
  | intro _ sources deps depsUnaffected =>
    have depsEq : cachedBuild B (fun n => run B (schedule n)) T '' ↑(T.deps n) =
        build B S '' ↑(S.deps n) := by
      rw [deps]
      apply Set.image_congr
      intro d hd
      rw [cachedBuild_eq_build B writers T noCollision schedule writerOnly d]
      exact (build_eq_of_unaffected B (depsUnaffected d hd)).symm
    rw [cachedBuild_eq, depsEq, ← sources]
    change (match run B (schedule n) (traceKey B S n) with
      | some a => a
      | none => B.compile (S.src n) (build B S '' ↑(S.deps n))) = a
    rw [present]

/-- One module with no dependencies. -/
example : Snapshot Unit ℕ :=
  { src := fun _ => 0, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

/-- Pairing keys and identity digests realize `NoCollision` for every set of
snapshots. -/
example (compile : ℕ → Set ℕ → ℕ) (𝒮 : Set (Snapshot ℕ ℕ)) :
    NoCollision ⟨ℕ, ℕ, ℕ, ℕ, ℕ × Set ℕ, compile, fun s ds => (s, ds), fun a => a⟩
      𝒮 := by
  intro X _ Y _ m n keys
  simp only [traceKey, Prod.mk.injEq, Set.image_id'] at keys
  exact keys

#print axioms cachedBuild_eq_build
#print axioms cachedBuild_restores_unaffected

end D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
