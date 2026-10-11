/- GID: D5/S3/ConceptDynamics/Governance/LayeredLocalCacheSoundness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/LayeredLocalCacheSoundness
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: Persistent cache layers preserve builds and admit an exact readiness probe. -/
import D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness

open _root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness

universe u

/-- K1: a common snapshot family supplies the collision boundary for all sessions. -/
structure Model where
  B : BuildSystem.{u}
  snapshots : Set (Snapshot B.Node B.Src)
  noCollision : NoCollision B snapshots

variable (B : BuildSystem.{u})

/-- K1: each module has at most one persistent key/artifact record. -/
abbrev Local := B.Node → Option (B.Key × B.Art)

/-- K1/K2: read the dependency artifacts currently present in the local layer. -/
def inputs (S : Snapshot B.Node B.Src) (L : Local B) (n : B.Node) : Set B.Art :=
  {a | ∃ d ∈ S.deps n, ∃ k, L d = some (k, a)}

/-- K1/K3: a matching record is reusable; a stale record is a miss. -/
noncomputable def localHit (L : Local B) (n : B.Node) (k : B.Key) : Option B.Art := by
  classical
  exact (L n).bind fun r => if r.1 = k then some r.2 else none

/-- K1/K3: local lookup precedes shared lookup. Neither branch compiles. -/
noncomputable def lookup (c : B.Key → Option B.Art) (L : Local B)
    (n : B.Node) (k : B.Key) : Option B.Art :=
  match localHit B L n k with
  | some a => some a
  | none => c k

/-- K1/K2: update only the visited module. -/
noncomputable def put (L : Local B) (n : B.Node) (k : B.Key) (a : B.Art) : Local B := by
  classical
  exact Function.update L n (some (k, a))

/-- K2: each event records the module, computed key, and both actual lookup outcomes. -/
structure Event where
  node : B.Node
  key : B.Key
  localRead : Option B.Art
  sharedRead : Option B.Art
  compiled : Bool
  reads : Set B.Node

/-- K1/K2: an execution returns a persistent layer and an ordered access trace. -/
structure Result where
  layer : Local B
  events : List (Event B)

/-- K1/K2: compilation is confined to the miss branch. -/
def artifact (S : Snapshot B.Node B.Src) (L : Local B) (n : B.Node) :
    Option B.Art → B.Art
  | some a => a
  | none => B.compile (S.src n) (inputs B S L n)

/-- K1/K2: the ordinary executor computes keys from dependency records, reuses the
first hit, and compiles only on a double miss. Shared histories may differ per node. -/
noncomputable def execute (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (L : Local B) : List B.Node → Result B
  | [] => ⟨L, []⟩
  | n :: ns =>
      let A := inputs B S L n
      let k := B.hash (S.src n) (B.digest '' A)
      let l := localHit B L n k
      let c := if l.isSome then none else shared n k
      let hit := lookup B (shared n) L n k
      let a := artifact B S L n hit
      let tail := execute S shared (put B L n k a) ns
      ⟨tail.layer, ⟨n, k, l, c, hit.isNone, insert n ↑(S.deps n)⟩ :: tail.events⟩

/-- K3: the probe returns the first double miss, or a layer restored entirely by
hits. Its definition contains no compiler and no from-scratch build. -/
noncomputable def probe (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (L : Local B) :
    List B.Node → Except B.Node (Local B)
  | [] => .ok L
  | n :: ns =>
      let k := B.hash (S.src n) (B.digest '' inputs B S L n)
      match lookup B (shared n) L n k with
      | none => .error n
      | some a => probe S shared (put B L n k a) ns

/-- K2: the least dependency-closed set containing the requested roots. -/
inductive Demand (S : Snapshot B.Node B.Src) (roots : Finset B.Node) : B.Node → Prop
  | root {n} : n ∈ roots → Demand S roots n
  | dep {n d} : Demand S roots n → d ∈ S.deps n → Demand S roots d

/-- K1/K2: dependencies precede their users in the finite execution plan. -/
def Ordered (S : Snapshot B.Node B.Src) : Set B.Node → List B.Node → Prop
  | _, [] => True
  | done, n :: ns => (∀ d ∈ S.deps n, d ∈ done) ∧ Ordered S (insert n done) ns

/-- K1/K2: a plan visits each module in the requested dependency closure once. -/
structure Plan (S : Snapshot B.Node B.Src) where
  roots : Finset B.Node
  nodes : List B.Node
  nodup : nodes.Nodup
  ordered : Ordered B S ∅ nodes
  exactDemand : ∀ n, n ∈ nodes ↔ Demand B S roots n

open Classical in
/-- K1/K2: the finite transitive dependency support of one root. -/
noncomputable def support (S : Snapshot B.Node B.Src) (n : B.Node) : Finset B.Node :=
  insert n ((S.deps n).attach.biUnion fun d => support S d.1)
termination_by S.rank n
decreasing_by exact S.rank_lt n d.1 d.2

private theorem support_closed (S : Snapshot B.Node B.Src) (n : B.Node) :
    n ∈ support B S n ∧
    ∀ m ∈ support B S n, ∀ d ∈ S.deps m, d ∈ support B S n := by
  classical
  induction h : S.rank n using Nat.strong_induction_on generalizing n with
  | _ r ih =>
    have child := fun d hd => ih (S.rank d) (h ▸ S.rank_lt n d hd) d rfl
    constructor
    · rw [support]; exact Finset.mem_insert_self _ _
    · intro m hm d hd
      rw [support] at hm ⊢
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨⟨d,hd⟩,Finset.mem_attach _ _,(child d hd).1⟩)
      · obtain ⟨j,hj,hm⟩ := Finset.mem_biUnion.mp hm
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨j,hj,(child j.1 j.2).2 m hm d hd⟩)

private theorem support_least (S : Snapshot B.Node B.Src) (Q : Set B.Node)
    (closed : ∀ n ∈ Q, ∀ d ∈ S.deps n, d ∈ Q) (n : B.Node) (hn : n ∈ Q) :
    ∀ m ∈ support B S n, m ∈ Q := by
  classical
  induction h : S.rank n using Nat.strong_induction_on generalizing n with
  | _ r ih =>
    intro m hm
    rw [support] at hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hn
    · obtain ⟨d,_,hm⟩ := Finset.mem_biUnion.mp hm
      exact ih (S.rank d.1) (h ▸ S.rank_lt n d.1 d.2) d.1
        (closed n hn d.1 d.2) rfl m hm

private theorem ordered_enumeration (S : Snapshot B.Node B.Src) (Q : Finset B.Node)
    (done : Set B.Node)
    (closed : ∀ n ∈ Q, ∀ d ∈ S.deps n, d ∈ done ∨ d ∈ Q) :
    ∃ xs : List B.Node, xs.Nodup ∧ (∀ n, n ∈ xs ↔ n ∈ Q) ∧ Ordered B S done xs := by
  classical
  induction Q using Finset.strongInductionOn generalizing done with
  | _ Q ih =>
    by_cases hQ : Q.Nonempty
    · obtain ⟨n,hn,minimal⟩ := Finset.exists_min_image Q S.rank hQ
      have pre : ∀ d ∈ S.deps n, d ∈ done := by
        intro d hd
        rcases closed n hn d hd with h | h
        · exact h
        · exact False.elim ((Nat.not_lt_of_ge (minimal d h)) (S.rank_lt n d hd))
      have remain : ∀ m ∈ Q.erase n, ∀ d ∈ S.deps m,
          d ∈ insert n done ∨ d ∈ Q.erase n := by
        intro m hm d hd
        rcases closed m (Finset.mem_of_mem_erase hm) d hd with h | h
        · exact Or.inl (Set.mem_insert_of_mem n h)
        · by_cases e : d = n
          · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl e))
          · exact Or.inr (Finset.mem_erase.mpr ⟨e,h⟩)
      obtain ⟨xs,hxs,mem,order⟩ := ih (Q.erase n) (Finset.erase_ssubset hn)
        (insert n done) remain
      refine ⟨n :: xs, ?_, ?_, ⟨pre,order⟩⟩
      · exact List.nodup_cons.mpr ⟨fun h => Finset.notMem_erase n Q ((mem n).mp h),hxs⟩
      · intro m
        simp only [List.mem_cons, mem, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_,h⟩)
          · exact hn
          · exact h
        · intro h
          by_cases e : m = n
          · exact Or.inl e
          · exact Or.inr ⟨e,h⟩
    · have empty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
      subst Q
      exact ⟨[],by simp,by simp,trivial⟩

private theorem plan_exists (S : Snapshot B.Node B.Src) (roots : Finset B.Node) :
    ∃ p : Plan B S, p.roots = roots := by
  classical
  let Q := roots.biUnion (support B S)
  have mem : ∀ n, n ∈ Q ↔ Demand B S roots n := by
    intro n
    constructor
    · intro hn
      obtain ⟨r,hr,hn⟩ := Finset.mem_biUnion.mp hn
      exact support_least B S {n | Demand B S roots n}
        (fun _ h _ hd => Demand.dep h hd) r (Demand.root hr) n hn
    · intro hn
      induction hn with
      | root hr => exact Finset.mem_biUnion.mpr ⟨_,hr,(support_closed B S _).1⟩
      | dep _ hd ih =>
        obtain ⟨r,hr,hm⟩ := Finset.mem_biUnion.mp ih
        exact Finset.mem_biUnion.mpr ⟨r,hr,(support_closed B S r).2 _ hm _ hd⟩
  obtain ⟨xs,nd,hxs,order⟩ := ordered_enumeration B S Q ∅ (by
    intro n hn d hd
    exact Or.inr ((mem d).mpr (Demand.dep ((mem n).mp hn) hd)))
  exact ⟨⟨roots,xs,nd,order,fun n => (hxs n).trans (mem n)⟩,rfl⟩

/-- K1/K2: every finite root request has a certified finite dependency plan. -/
noncomputable def planFor (S : Snapshot B.Node B.Src) (roots : Finset B.Node) : Plan B S :=
  Classical.choose (plan_exists B S roots)

variable (M : Model.{u})

/-- K1: every local record has honest snapshot provenance. -/
def Provenance (L : Local M.B) : Prop :=
  ∀ n k a, L n = some (k, a) → ∃ W ∈ M.snapshots, ∃ m,
    traceKey M.B W m = k ∧ build M.B W m = a

open Classical in
/-- K1: session histories allow snapshot changes, execution, deletion, clearing,
and donor copies; a donor must itself have a reachable history. -/
inductive Reachable : Local M.B → Prop
  | empty : Reachable (fun _ => none)
  | switch {L} : Reachable L → (T : Snapshot M.B.Node M.B.Src) →
      T ∈ M.snapshots → Reachable L
  | execute {L} (S : Snapshot M.B.Node M.B.Src) (hS : S ∈ M.snapshots)
      (p : Plan M.B S) (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
      (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots) :
      Reachable L → Reachable (execute M.B S (fun n => run M.B (schedule n)) L p.nodes).layer
  | delete {L} : Reachable L → (n : M.B.Node) →
      Reachable (fun m => if m = n then none else L m)
  | clear {L} : Reachable L → Reachable (fun _ => none)
  | copy {L donor} : Reachable L → Reachable donor → Reachable donor

private theorem shared_correct (S : Snapshot M.B.Node M.B.Src) (hS : S ∈ M.snapshots)
    (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (n : M.B.Node) (a : M.B.Art) (ha : run M.B (schedule n) (traceKey M.B S n) = some a) :
    a = build M.B S n := by
  have nc : NoCollision M.B (insert S M.snapshots) := by
    simpa [Set.insert_eq_of_mem hS] using M.noCollision
  have all := cachedBuild_eq_build M.B M.snapshots S nc schedule writers
  have eqn := all n
  rw [cachedBuild.eq_1] at eqn
  have he : (Set.range fun d : {d // d ∈ S.deps n} =>
      cachedBuild M.B (fun m => run M.B (schedule m)) S d.1) =
      build M.B S '' (↑(S.deps n) : Set M.B.Node) := by
    ext x
    simp only [all]
    simp
  rw [he] at eqn
  change run M.B (schedule n)
    (M.B.hash (S.src n) (M.B.digest '' (build M.B S '' ↑(S.deps n)))) = some a at ha
  rw [ha] at eqn
  exact eqn

private theorem hit_correct (S : Snapshot M.B.Node M.B.Src) (hS : S ∈ M.snapshots)
    (L : Local M.B) (hL : Provenance M L)
    (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (n : M.B.Node) (a : M.B.Art)
    (ha : lookup M.B (run M.B (schedule n)) L n (traceKey M.B S n) = some a) :
    a = build M.B S n := by
  unfold lookup at ha
  cases hl : localHit M.B L n (traceKey M.B S n) with
  | none => exact shared_correct M S hS schedule writers n a (by simpa [hl] using ha)
  | some v =>
    have hv : v = a := by simpa [hl] using ha
    subst v
    unfold localHit at hl
    cases rec : L n with
    | none => simp [rec] at hl
    | some r =>
      rcases r with ⟨k,b⟩
      simp only [rec, Option.bind_some] at hl
      split_ifs at hl with hk
      · have hb : b = a := Option.some.inj hl
        subst b
        obtain ⟨W,hW,m,key,art⟩ := hL n k a rec
        obtain ⟨src,deps⟩ := M.noCollision W hW S hS m n (key.trans hk)
        rw [← art, build.eq_1 M.B W m, build.eq_1 M.B S n, src]
        congr 1
        have ranges (X : Snapshot M.B.Node M.B.Src) (x : M.B.Node) :
            (Set.range fun d : {d // d ∈ X.deps x} => build M.B X d.1) =
            build M.B X '' (↑(X.deps x) : Set M.B.Node) := by ext a; simp
        simpa only [ranges] using deps

private theorem put_provenance (L : Local M.B) (hL : Provenance M L)
    (S : Snapshot M.B.Node M.B.Src) (hS : S ∈ M.snapshots) (n : M.B.Node) :
    Provenance M (put M.B L n (traceKey M.B S n) (build M.B S n)) := by
  classical
  intro m k a hm
  by_cases h : m = n
  · subst m
    simp only [put, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hm
    exact ⟨S,hS,n,hm.1,hm.2⟩
  · rw [put, Function.update_of_ne h] at hm
    exact hL m k a hm

/-- Correct entries for a processed prefix, independently of stale unvisited entries. -/
def CorrectOn (S : Snapshot B.Node B.Src) (L : Local B) (done : Set B.Node) : Prop :=
  ∀ n ∈ done, L n = some (traceKey B S n, build B S n)

private theorem input_correct (S : Snapshot B.Node B.Src) (L : Local B)
    (done : Set B.Node) (hc : CorrectOn B S L done) (n : B.Node)
    (hd : ∀ d ∈ S.deps n, d ∈ done) :
    inputs B S L n = build B S '' (↑(S.deps n) : Set B.Node) := by
  ext a
  constructor
  · rintro ⟨d,hd',k,hk⟩
    rw [hc d (hd d hd')] at hk
    exact ⟨d,hd',(Prod.mk.inj (Option.some.inj hk)).2⟩
  · rintro ⟨d,hd',rfl⟩
    exact ⟨d,hd',traceKey B S d,hc d (hd d hd')⟩

private theorem put_correct (S : Snapshot B.Node B.Src) (L : Local B)
    (done : Set B.Node) (hc : CorrectOn B S L done) (n : B.Node) :
    CorrectOn B S (put B L n (traceKey B S n) (build B S n)) (insert n done) := by
  classical
  intro m hm
  by_cases h : m = n
  · subst m; simp [put]
  · rw [put, Function.update_of_ne h]
    exact hc m ((Set.mem_insert_iff.mp hm).resolve_left h)

private theorem execute_sound (S : Snapshot M.B.Node M.B.Src) (hS : S ∈ M.snapshots)
    (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (xs : List M.B.Node) (done : Set M.B.Node) (L : Local M.B)
    (hL : Provenance M L) (hc : CorrectOn M.B S L done)
    (ho : Ordered M.B S done xs) :
    Provenance M (execute M.B S (fun n => run M.B (schedule n)) L xs).layer ∧
    CorrectOn M.B S (execute M.B S (fun n => run M.B (schedule n)) L xs).layer
      (done ∪ {n | n ∈ xs}) ∧
    (∀ e ∈ (execute M.B S (fun n => run M.B (schedule n)) L xs).events,
      e.key = traceKey M.B S e.node ∧
      (e.compiled = true ↔ e.localRead = none ∧ e.sharedRead = none)) := by
  induction xs generalizing done L with
  | nil =>
    refine ⟨hL, ?_, ?_⟩
    · simpa [execute, CorrectOn] using hc
    · simp [execute]
  | cons n ns ih =>
    have inp := input_correct M.B S L done hc n ho.1
    have hash : M.B.hash (S.src n) (M.B.digest '' inputs M.B S L n) =
        traceKey M.B S n := by rw [inp]; rfl
    have comp : M.B.compile (S.src n) (inputs M.B S L n) = build M.B S n := by
      rw [inp, build.eq_1 M.B S n]
      congr 1
      ext a; simp
    have hit : artifact M.B S L n
        (lookup M.B (run M.B (schedule n)) L n (traceKey M.B S n)) = build M.B S n := by
      cases h : lookup M.B (run M.B (schedule n)) L n (traceKey M.B S n) with
      | none => simpa [h, artifact] using comp
      | some a => simpa [h, artifact] using hit_correct M S hS L hL schedule writers n a h
    have tail := ih (insert n done) (put M.B L n (traceKey M.B S n) (build M.B S n))
      (put_provenance M L hL S hS n) (put_correct M.B S L done hc n) ho.2
    rw [execute]
    dsimp only
    rw [hash, hit]
    refine ⟨tail.1, ?_, ?_⟩
    · convert tail.2.1 using 1
      ext m; simp [or_assoc, or_left_comm]
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨rfl, ?_⟩
        dsimp
        unfold lookup
        cases hl : localHit M.B L n (traceKey M.B S n) <;>
          cases hs : run M.B (schedule n) (traceKey M.B S n) <;> simp
      · exact tail.2.2 e he

private theorem reachable_provenance {L : Local M.B} (h : Reachable M L) : Provenance M L := by
  induction h with
  | empty => intro n k a h; contradiction
  | switch h T hT ih => exact ih
  | execute S hS p schedule writers h ih =>
    exact (execute_sound M S hS schedule writers p.nodes ∅ _ ih
      (by intro n hn; contradiction) p.ordered).1
  | delete h n ih =>
    intro m k a hm
    dsimp only at hm
    split_ifs at hm with he
    exact ih m k a hm
  | clear h ih => intro n k a hm; contradiction
  | copy h hd ih ihd => exact ihd

private theorem execute_frame (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (xs : List B.Node) (L : Local B) :
    ((execute B S shared L xs).events.map Event.node = xs) ∧
    (∀ n, n ∉ xs → (execute B S shared L xs).layer n = L n) := by
  classical
  induction xs generalizing L with
  | nil => simp [execute]
  | cons m ms ih =>
    rw [execute]
    dsimp only
    constructor
    · simp only [List.map_cons, (ih _).1]
    · intro n hn
      rw [(ih _).2 n (fun h => hn (List.mem_cons_of_mem m h)), put,
        Function.update_of_ne (fun h => hn (List.mem_cons.mpr (Or.inl h)))]

private theorem execute_reads (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (xs : List B.Node) (hn : xs.Nodup)
    (L : Local B) : ∀ e ∈ (execute B S shared L xs).events,
    e.reads = insert e.node (↑(S.deps e.node) : Set B.Node) ∧
    e.localRead = localHit B L e.node e.key ∧
    e.sharedRead = (if e.localRead.isSome then none else shared e.node e.key) := by
  classical
  induction xs generalizing L with
  | nil => simp [execute]
  | cons n ns ih =>
    rw [execute]
    dsimp only
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl,rfl,rfl⟩
    · have htail := ih (List.nodup_cons.mp hn).2 _ e he
      have mem : e.node ∈ ns := by
        rw [← (execute_frame B S shared ns _).1]
        exact List.mem_map.mpr ⟨e,he,rfl⟩
      have ne : e.node ≠ n := by
        intro eq
        exact (List.nodup_cons.mp hn).1 (eq ▸ mem)
      refine ⟨htail.1, ?_, htail.2.2⟩
      simpa only [localHit, put, Function.update_of_ne ne] using htail.2.1

private theorem execute_locality (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (Q : Set B.Node)
    (closed : ∀ n ∈ Q, ∀ d ∈ S.deps n, d ∈ Q)
    (xs : List B.Node) (within : ∀ n ∈ xs, n ∈ Q)
    (L₁ L₂ : Local B) (agree : ∀ n ∈ Q, L₁ n = L₂ n) :
    (execute B S shared L₁ xs).events = (execute B S shared L₂ xs).events ∧
    (∀ n ∈ Q, (execute B S shared L₁ xs).layer n =
      (execute B S shared L₂ xs).layer n) := by
  classical
  induction xs generalizing L₁ L₂ with
  | nil => exact ⟨rfl, agree⟩
  | cons n ns ih =>
    have hn : n ∈ Q := within n List.mem_cons_self
    have inp : inputs B S L₁ n = inputs B S L₂ n := by
      ext a
      simp only [inputs, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨d, hd, k, hk⟩
        exact ⟨d, hd, k, (agree d (closed n hn d hd)) ▸ hk⟩
      · rintro ⟨d, hd, k, hk⟩
        exact ⟨d, hd, k, (agree d (closed n hn d hd)).symm ▸ hk⟩
    have hit : ∀ k, localHit B L₁ n k = localHit B L₂ n k := by
      intro k
      simp only [localHit, agree n hn]
    have look : ∀ k, lookup B (shared n) L₁ n k = lookup B (shared n) L₂ n k := by
      intro k
      simp only [lookup, hit]
    have art : ∀ h, artifact B S L₁ n h = artifact B S L₂ n h := by
      intro h
      cases h <;> simp only [artifact, inp]
    have updated : ∀ k a, ∀ m ∈ Q,
        put B L₁ n k a m = put B L₂ n k a m := by
      intro k a m hm
      by_cases e : m = n
      · subst m; simp only [put, Function.update_self]
      · simp only [put, Function.update_of_ne e, agree m hm]
    have tail := ih (fun m hm => within m (List.mem_cons_of_mem n hm))
      (put B L₁ n (B.hash (S.src n) (B.digest '' inputs B S L₂ n))
        (artifact B S L₂ n (lookup B (shared n) L₂ n
          (B.hash (S.src n) (B.digest '' inputs B S L₂ n)))))
      (put B L₂ n (B.hash (S.src n) (B.digest '' inputs B S L₂ n))
        (artifact B S L₂ n (lookup B (shared n) L₂ n
          (B.hash (S.src n) (B.digest '' inputs B S L₂ n)))))
      (updated _ _)
    rw [execute, execute]
    dsimp only
    simp only [inp, hit, look, art]
    exact ⟨congrArg (List.cons _) tail.1, tail.2⟩

private theorem probe_spec (S : Snapshot B.Node B.Src)
    (shared : B.Node → B.Key → Option B.Art) (xs : List B.Node) (L : Local B) :
    ((∃ L', probe B S shared L xs = .ok L') ↔
      ∀ e ∈ (execute B S shared L xs).events, e.compiled = false) ∧
    (∀ n, probe B S shared L xs = .error n →
      ∃ e ∈ (execute B S shared L xs).events, e.node = n ∧ e.compiled = true) := by
  induction xs generalizing L with
  | nil => simp [probe, execute]
  | cons m ms ih =>
    rw [probe, execute]
    dsimp only
    cases h : lookup B (shared m) L m
        (B.hash (S.src m) (B.digest '' inputs B S L m)) with
    | none =>
      simp only [Option.isNone_none, artifact]
      constructor
      · simp
      · intro n hn
        have he : m = n := Except.error.inj hn
        exact ⟨_,List.mem_cons_self,he,rfl⟩
    | some a =>
      simp only [Option.isNone_some, artifact]
      constructor
      · simpa using (ih (put B L m _ a)).1
      · intro n hn
        obtain ⟨e,he,hen,hec⟩ := (ih (put B L m _ a)).2 n hn
        exact ⟨e,List.mem_cons_of_mem _ he,hen,hec⟩

/-- K1--K3: correctness, persistent reachability, exact access and compile events,
semantic independence from local records outside demand, and a noncompiling probe
with a concrete double-miss diagnostic. -/
structure Guarantees (S : Snapshot M.B.Node M.B.Src)
    (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (L : Local M.B) (p : Plan M.B S) (r : Result M.B) : Prop where
  roots : ∀ n ∈ p.roots, r.layer n = some (traceKey M.B S n, build M.B S n)
  reusable : Reachable M r.layer
  visits : r.events.map Event.node = p.nodes
  outside : ∀ n, ¬ Demand M.B S p.roots n → r.layer n = L n
  reads : ∀ n, (∃ e ∈ r.events, n ∈ e.reads) ↔ Demand M.B S p.roots n
  locality : ∀ (L₁ L₂ : Local M.B),
    (∀ n, Demand M.B S p.roots n → L₁ n = L₂ n) →
    (execute M.B S (fun n => run M.B (schedule n)) L₁ p.nodes).events =
      (execute M.B S (fun n => run M.B (schedule n)) L₂ p.nodes).events ∧
    (∀ n, Demand M.B S p.roots n →
      (execute M.B S (fun n => run M.B (schedule n)) L₁ p.nodes).layer n =
        (execute M.B S (fun n => run M.B (schedule n)) L₂ p.nodes).layer n) ∧
    (∀ n, ¬ Demand M.B S p.roots n →
      (execute M.B S (fun n => run M.B (schedule n)) L₁ p.nodes).layer n = L₁ n ∧
      (execute M.B S (fun n => run M.B (schedule n)) L₂ p.nodes).layer n = L₂ n)
  workload : ∀ n, (∃ e ∈ r.events, e.node = n ∧ e.compiled = true) ↔
    Demand M.B S p.roots n ∧ localHit M.B L n (traceKey M.B S n) = none ∧
      run M.B (schedule n) (traceKey M.B S n) = none
  ready : (∃ L', probe M.B S (fun n => run M.B (schedule n)) L p.nodes = .ok L') ↔
    ∀ e ∈ r.events, e.compiled = false
  needs : ∀ n, probe M.B S (fun n => run M.B (schedule n)) L p.nodes = .error n →
    Demand M.B S p.roots n ∧ localHit M.B L n (traceKey M.B S n) = none ∧
      run M.B (schedule n) (traceKey M.B S n) = none

/-- A reachable persistent layer can be reused by every valid demand plan. The
trace records exactly its demand and compiles exactly at double misses; probing
from the same state is ready exactly when that trace contains no compilation. -/
private theorem plan_contract (M : Model.{u}) (S : Snapshot M.B.Node M.B.Src)
    (hS : S ∈ M.snapshots) (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (L : Local M.B) (hL : Reachable M L) (p : Plan M.B S) :
    Guarantees M S schedule L p (execute M.B S (fun n => run M.B (schedule n)) L p.nodes) := by
  have hs := execute_sound M S hS schedule writers p.nodes ∅ L
    (reachable_provenance M hL) (by intro n hn; contradiction) p.ordered
  have hf := execute_frame M.B S (fun n => run M.B (schedule n)) p.nodes L
  have hr := execute_reads M.B S (fun n => run M.B (schedule n)) p.nodes p.nodup L
  have hp := probe_spec M.B S (fun n => run M.B (schedule n)) p.nodes L
  have event_mem : ∀ e ∈ (execute M.B S (fun n => run M.B (schedule n)) L p.nodes).events,
      Demand M.B S p.roots e.node := by
    intro e he
    apply (p.exactDemand e.node).mp
    rw [← hf.1]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have work : ∀ n, (∃ e ∈ (execute M.B S (fun n => run M.B (schedule n)) L p.nodes).events,
      e.node = n ∧ e.compiled = true) ↔
      Demand M.B S p.roots n ∧ localHit M.B L n (traceKey M.B S n) = none ∧
        run M.B (schedule n) (traceKey M.B S n) = none := by
    intro n
    constructor
    · rintro ⟨e,he,rfl,hc⟩
      have se := hs.2.2 e he
      have re := hr e he
      obtain ⟨hl,hc'⟩ := se.2.mp hc
      refine ⟨event_mem e he, ?_, ?_⟩
      · simpa [re.2.1,se.1] using hl
      · simpa [re.2.2,hl,se.1] using hc'
    · rintro ⟨hn,hl,hc⟩
      have mem : n ∈
          (execute M.B S (fun n => run M.B (schedule n)) L p.nodes).events.map Event.node := by
        rw [hf.1]; exact (p.exactDemand n).mpr hn
      obtain ⟨e,he,hen⟩ := List.mem_map.mp mem
      have se := hs.2.2 e he
      have re := hr e he
      refine ⟨e,he,hen,se.2.mpr ?_⟩
      have hl' : e.localRead = none := by simpa [re.2.1,se.1,hen] using hl
      exact ⟨hl',by simpa [re.2.2,hl',se.1,hen] using hc⟩
  refine ⟨?_, Reachable.execute S hS p schedule writers hL, hf.1, ?_, ?_, ?_, work, hp.1, ?_⟩
  · intro n hn
    exact hs.2.1 n (Or.inr ((p.exactDemand n).mpr (Demand.root hn)))
  · intro n hn
    exact hf.2 n (fun h => hn ((p.exactDemand n).mp h))
  · intro n
    constructor
    · rintro ⟨e,he,hn⟩
      rw [(hr e he).1] at hn
      rcases Set.mem_insert_iff.mp hn with rfl | hn
      · exact event_mem e he
      · exact Demand.dep (event_mem e he) hn
    · intro hn
      have mem : n ∈
          (execute M.B S (fun n => run M.B (schedule n)) L p.nodes).events.map Event.node := by
        rw [hf.1]; exact (p.exactDemand n).mpr hn
      obtain ⟨e,he,hen⟩ := List.mem_map.mp mem
      exact ⟨e,he,by rw [(hr e he).1,hen]; exact Set.mem_insert _ _⟩
  · intro L₁ L₂ agree
    have same := execute_locality M.B S (fun n => run M.B (schedule n))
      {n | Demand M.B S p.roots n} (fun _ hn _ hd => Demand.dep hn hd)
      p.nodes (fun n hn => (p.exactDemand n).mp hn) L₁ L₂ agree
    refine ⟨same.1, same.2, ?_⟩
    intro n hn
    have outside : n ∉ p.nodes := fun h => hn ((p.exactDemand n).mp h)
    exact ⟨(execute_frame M.B S _ p.nodes L₁).2 n outside,
      (execute_frame M.B S _ p.nodes L₂).2 n outside⟩
  · intro n hn
    exact (work n).mp (hp.2 n hn)

/-- Every finite root request admits a dependency plan, and ordinary execution
from any reachable local layer satisfies correctness, locality and readiness.
For this plan, any two local layers agreeing on demand have identical event
traces and final records on demand, and each preserves its own outside records. -/
theorem layered_cache_contract (M : Model.{u}) (S : Snapshot M.B.Node M.B.Src)
    (hS : S ∈ M.snapshots) (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (writers : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (L : Local M.B) (hL : Reachable M L) (roots : Finset M.B.Node) :
    (planFor M.B S roots).roots = roots ∧
    Guarantees M S schedule L (planFor M.B S roots)
      (execute M.B S (fun n => run M.B (schedule n)) L (planFor M.B S roots).nodes) := by
  exact ⟨Classical.choose_spec (plan_exists M.B S roots),
    plan_contract M S hS schedule writers L hL (planFor M.B S roots)⟩

#print axioms layered_cache_contract

end D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness
