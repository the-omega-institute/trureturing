/- GID: D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: Writer-filled trace-keyed caches yield from-scratch builds and hit unaffected modules. -/
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness

universe u v w x y

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

variable {Node : Type u} {Src : Type v} {Art : Type w} {Dig : Type x} {Key : Type y}
variable [DecidableEq Art] [DecidableEq Dig]
variable (compile : Src → Finset Art → Art) (hash : Src → Finset Dig → Key)
variable (digest : Art → Dig)

/-- From-scratch build: the artifact of `n` is its source compiled against the
artifacts of its dependencies. -/
def build (S : Snapshot Node Src) (n : Node) : Art :=
  compile (S.src n) ((S.deps n).attach.image fun d => build S d.1)
termination_by S.rank n
decreasing_by exact S.rank_lt n d.1 d.2

omit [DecidableEq Dig] in
private theorem image_attach_eq {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) :
    (s.attach.image fun d => f d.1) = s.image f := by
  ext b
  simp

omit [DecidableEq Dig] in
private theorem build_eq (S : Snapshot Node Src) (n : Node) :
    build compile S n = compile (S.src n) ((S.deps n).image (build compile S)) := by
  rw [build, image_attach_eq]

/-- The cache key of `n`: its source together with the content digests of its
dependencies' artifacts. -/
def traceKey (S : Snapshot Node Src) (n : Node) : Key :=
  hash (S.src n) (((S.deps n).image (build compile S)).image digest)

/-- No collision among the build inputs realized by the snapshots in `𝒮`: equal
keys come from equal sources and equal sets of dependency artifacts. -/
def NoCollision (𝒮 : Set (Snapshot Node Src)) : Prop :=
  ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, ∀ m n,
    traceKey compile hash digest X m = traceKey compile hash digest Y n →
      X.src m = Y.src n ∧
        (X.deps m).image (build compile X) = (Y.deps n).image (build compile Y)

/-- Apply one cache operation to a cache state. -/
def Op.apply [DecidableEq Key] : Op Node Src → (Key → Option Art) → Key → Option Art
  | .store W m, c =>
      Function.update c (traceKey compile hash digest W m) (some (build compile W m))
  | .clean, _ => fun _ => none

/-- The cache state after a sequence of operations applied to the empty cache. -/
def run [DecidableEq Key] (ops : List (Op Node Src)) : Key → Option Art :=
  ops.foldl (fun c o => o.apply compile hash digest c) fun _ => none

/-- Every entry of the cache is the from-scratch artifact of some module of some
writer snapshot, stored under that module's key. -/
def Sound (writers : Set (Snapshot Node Src)) (c : Key → Option Art) : Prop :=
  ∀ k a, c k = some a → ∃ W ∈ writers, ∃ m,
    traceKey compile hash digest W m = k ∧ build compile W m = a

/-- The reader build of snapshot `T`. The reader computes the key of `n` from its
own dependency artifacts and looks it up in the cache state `look n`; on a hit it
restores the stored artifact, otherwise it compiles `n`. -/
def cachedBuild (look : Node → Key → Option Art) (T : Snapshot Node Src) (n : Node) : Art :=
  match look n (hash (T.src n)
      (((T.deps n).attach.image fun d => cachedBuild look T d.1).image digest)) with
  | some a => a
  | none => compile (T.src n) ((T.deps n).attach.image fun d => cachedBuild look T d.1)
termination_by T.rank n
decreasing_by all_goals exact T.rank_lt n d.1 d.2

private theorem cachedBuild_eq (look : Node → Key → Option Art) (T : Snapshot Node Src)
    (n : Node) :
    cachedBuild compile hash digest look T n =
      match look n (hash (T.src n)
          (((T.deps n).image (cachedBuild compile hash digest look T)).image digest)) with
      | some a => a
      | none => compile (T.src n) ((T.deps n).image (cachedBuild compile hash digest look T)) := by
  rw [cachedBuild, image_attach_eq]

/-- The reader restores `n`: the key it computes for `n` from its own dependency
artifacts is present in the cache state it consults. -/
def Restores (look : Node → Key → Option Art) (T : Snapshot Node Src) (n : Node) : Prop :=
  ∃ a, look n (hash (T.src n)
    (((T.deps n).image (cachedBuild compile hash digest look T)).image digest)) = some a

/-- `n` is unaffected between a writer snapshot `S` and a reader snapshot `T`: it
has the same source and dependency set in both, and every dependency is
unaffected. -/
inductive Unaffected (S T : Snapshot Node Src) : Node → Prop where
  | intro (n : Node) : S.src n = T.src n → S.deps n = T.deps n →
      (∀ d ∈ T.deps n, Unaffected S T d) → Unaffected S T n

private theorem build_eq_of_keys
    {𝒮 : Set (Snapshot Node Src)} (noCollision : NoCollision compile hash digest 𝒮)
    {X Y : Snapshot Node Src} (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) {m n : Node}
    (keys : traceKey compile hash digest X m = traceKey compile hash digest Y n) :
    build compile X m = build compile Y n := by
  obtain ⟨sources, artifacts⟩ := noCollision X hX Y hY m n keys
  rw [build_eq, build_eq, sources, artifacts]

private theorem run_sound [DecidableEq Key] (writers : Set (Snapshot Node Src))
    (ops : List (Op Node Src))
    (writerOnly : ∀ W m, Op.store W m ∈ ops → W ∈ writers) :
    Sound compile hash digest writers (run compile hash digest ops) := by
  unfold run
  suffices step : ∀ (rest : List (Op Node Src)) (c : Key → Option Art),
      (∀ W m, Op.store W m ∈ rest → W ∈ writers) →
      Sound compile hash digest writers c →
      Sound compile hash digest writers
        (rest.foldl (fun c o => o.apply compile hash digest c) c) by
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
        by_cases same : k = traceKey compile hash digest W m
        · subst same
          simp only [Op.apply, Function.update_self, Option.some.injEq] at entry
          exact ⟨W, onlyWriters W m List.mem_cons_self, m, rfl, entry⟩
        · rw [Op.apply, Function.update_of_ne same] at entry
          exact sound k a entry
      | clean =>
        intro k a entry
        simp [Op.apply] at entry

private theorem cachedBuild_eq_build_of_sound
    (writers : Set (Snapshot Node Src)) (T : Snapshot Node Src)
    (noCollision : NoCollision compile hash digest (insert T writers))
    (look : Node → Key → Option Art)
    (sound : ∀ n, Sound compile hash digest writers (look n)) (n : Node) :
    cachedBuild compile hash digest look T n = build compile T n := by
  induction hr : T.rank n using Nat.strong_induction_on generalizing n with
  | _ r ih =>
    have depsEq : (T.deps n).image (cachedBuild compile hash digest look T) =
        (T.deps n).image (build compile T) := by
      apply Finset.image_congr
      intro d hd
      exact ih (T.rank d) (hr ▸ T.rank_lt n d hd) d rfl
    rw [cachedBuild_eq, depsEq]
    have keyEq : hash (T.src n) (((T.deps n).image (build compile T)).image digest) =
        traceKey compile hash digest T n := rfl
    rw [keyEq]
    cases hit : look n (traceKey compile hash digest T n) with
    | none => exact (build_eq compile T n).symm
    | some a =>
      obtain ⟨W, hW, m, keys, built⟩ := sound n _ a hit
      rw [← built]
      exact build_eq_of_keys compile hash digest noCollision
        (Set.mem_insert_of_mem T hW) (Set.mem_insert T writers) keys

/-- Reader soundness under arbitrary interleaving. Let every cache state the
reader consults be reached from the empty cache by stores of writer snapshots and
cleans, in any order and possibly different for each module. If no two build
inputs realized by the writers and the reader share a key, the reader build of
every module equals its from-scratch build. -/
theorem cachedBuild_eq_build [DecidableEq Key]
    (writers : Set (Snapshot Node Src)) (T : Snapshot Node Src)
    (noCollision : NoCollision compile hash digest (insert T writers))
    (schedule : Node → List (Op Node Src))
    (writerOnly : ∀ n W m, Op.store W m ∈ schedule n → W ∈ writers) (n : Node) :
    cachedBuild compile hash digest (fun n => run compile hash digest (schedule n)) T n =
      build compile T n :=
  cachedBuild_eq_build_of_sound compile hash digest writers T noCollision _
    (fun n => run_sound compile hash digest writers (schedule n) (writerOnly n)) n

omit [DecidableEq Dig] in
private theorem build_eq_of_unaffected {S T : Snapshot Node Src} {n : Node}
    (unaffected : Unaffected S T n) : build compile S n = build compile T n := by
  induction unaffected with
  | intro n sources deps _ ih =>
    rw [build_eq, build_eq, sources, deps]
    congr 1
    exact Finset.image_congr fun d hd => ih d hd

/-- Unaffected modules are restored, not compiled. Under the hypotheses of
`cachedBuild_eq_build`, if `n` is unaffected between a snapshot `S` and the reader
snapshot `T`, and the cache state consulted for `n` holds an entry under the key
of `n` in `S`, then the reader restores `n` from the cache. -/
theorem cachedBuild_restores_unaffected [DecidableEq Key]
    (writers : Set (Snapshot Node Src)) (T : Snapshot Node Src)
    (noCollision : NoCollision compile hash digest (insert T writers))
    (schedule : Node → List (Op Node Src))
    (writerOnly : ∀ n W m, Op.store W m ∈ schedule n → W ∈ writers)
    (S : Snapshot Node Src) (n : Node) (unaffected : Unaffected S T n)
    (present : ∃ a, run compile hash digest (schedule n) (traceKey compile hash digest S n) =
      some a) :
    Restores compile hash digest (fun n => run compile hash digest (schedule n)) T n := by
  obtain ⟨a, entry⟩ := present
  refine ⟨a, ?_⟩
  cases unaffected with
  | intro _ sources deps depsUnaffected =>
    have depsEq : (T.deps n).image
        (cachedBuild compile hash digest (fun n => run compile hash digest (schedule n)) T) =
        (S.deps n).image (build compile S) := by
      rw [deps]
      apply Finset.image_congr
      intro d hd
      rw [cachedBuild_eq_build compile hash digest writers T noCollision schedule writerOnly d]
      exact (build_eq_of_unaffected compile (depsUnaffected d hd)).symm
    rw [depsEq, ← sources]
    exact entry

/-- The empty snapshot shape: one module with no dependencies. -/
example : Snapshot Unit ℕ :=
  { src := fun _ => 0, deps := fun _ => ∅, rank := fun _ => 0,
    rank_lt := fun _ _ h => absurd h (Finset.notMem_empty _) }

/-- Pairing keys and identity digests realize `NoCollision` for every set of
snapshots. -/
example (𝒮 : Set (Snapshot ℕ ℕ)) (compile : ℕ → Finset ℕ → ℕ) :
    NoCollision compile (fun s ds => (s, ds)) (fun a : ℕ => a) 𝒮 := by
  intro X _ Y _ m n keys
  simp only [traceKey, Prod.mk.injEq, Finset.image_id'] at keys
  exact keys

#print axioms cachedBuild_eq_build
#print axioms cachedBuild_restores_unaffected

end D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
