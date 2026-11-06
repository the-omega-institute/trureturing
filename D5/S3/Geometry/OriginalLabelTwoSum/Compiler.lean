/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Compiler
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Compiler
   mirror-E: none(waiver:original-label-two-sum-compiler)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The original Gamma/two-filling compiler constructs a computed parent certificate with separate main and core sequences. -/
import D5.S3.Geometry.OriginalLabelTwoSum.CompilerStages
import D5.S3.Geometry.OriginalLabelTwoSum.Cone

/-! UNCOMPILED. This is the ORIGINAL compiler, not matching-staircase. It is an
algebraic original-label parent constructor. A general actual graph edge-2-sum
binding is still a separate missing obligation. No Cout, parent collapse,
critical equality, collar collapse or sphere equivalence is an input. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
open scoped unitInterval ContinuousMap
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteConeCollapse FiniteSimplicialJoin
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact original permission: Gamma, or no vertical pair in EITHER actual
child list together with a core vertex different from the interface. -/
def CompilerPermission {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K) : Prop :=
  Nonempty (Sequence (project (delta Y)) (project E)) ∨
    ((∀ P ∈ c.main.pairs, P.apex ≠ e) ∧
     (∀ P ∈ c.separate.pairs, P.apex ≠ e) ∧ c.vertex ≠ e)

private theorem parent_support (X Y Z : Finset V) (e : V) (E C : Family V)
    (hZ : Z ⊆ Y) (hE : Supported Y E) :
    Supported (X ∪ Y) (parentOf X Y Z e E C) := by
  rintro s ((⟨a,ha,b,hb,rfl⟩ | ⟨a,ha,b,hb,rfl⟩) | ⟨a,ha,b,hb,rfl⟩)
  · exact Finset.union_subset_union ha.2 (hb.trans hZ)
  · exact Finset.union_subset_union ha.1 hb
  · exact Finset.union_subset_union ha (hE b hb)

private theorem core_empty {W : Finset V} {K : Family V} (c : Certificate W K) :
    (∅ : Finset V) ∈ c.core := c.core.lower (Finset.empty_subset _) c.vertex_mem

private theorem source_empty {W : Finset V} {K : Family V} (c : Certificate W K) :
    (∅ : Finset V) ∈ K := by
  have hp : ({c.vertex} : Finset V) ∈ project (endpoint c.core c.critical) :=
    ⟨by simp,Or.inl c.vertex_mem⟩
  exact K.lower (Finset.empty_subset _) (c.main.monotone hp).2

private theorem endpoint_empty {W : Finset V} {K : Family V} (c : Certificate W K) :
    (∅ : Finset V) ∈ endpoint c.core c.critical := Or.inl (core_empty c)

private theorem singleton_parent_other (X Y Z : Finset V) (e p : V) (E : Family V)
    (heX : e ∉ X) (hpX : p ∈ X) (hpe : p ≠ e) :
    parentOf X Y Z e E (delta {p}) =
      rawJoin (delta {p}) (delta Z) ⊔ rawJoin (delta X) E := by
  have hd : restrict X (delta {p}) = delta {p} := by
    apply inf_eq_left.mpr
    intro s hs
    exact hs.trans (Finset.singleton_subset_iff.mpr hpX)
  have hl : rawLink X e (delta {p}) = ⊥ := by
    apply SetLike.ext
    intro s
    constructor
    · intro h
      have he : e = p := Finset.mem_singleton.mp (h.2 (Finset.mem_insert_self e s))
      exact False.elim (hpe he.symm)
    · intro h; exact False.elim h
  simp only [parentOf,phi,hd,hl,rawJoin_void,bot_sup_eq,sup_bot_eq]

private theorem singleton_parent_interface (X Y Z : Finset V) (e : V) (E : Family V)
    (heX : e ∉ X) (hZ : Z ⊆ Y) :
    parentOf X Y Z e E (delta {e}) = delta Y ⊔ rawJoin (delta X) E := by
  have hd : restrict X (delta {e}) = delta ∅ := by
    apply SetLike.ext
    intro s
    change (s ⊆ {e} ∧ s ⊆ X) ↔ s ⊆ ∅
    constructor
    · rintro ⟨he,hx⟩ v hv
      have hve : v = e := by simpa using he hv
      exact False.elim (heX (hve ▸ hx hv))
    · intro hs; exact ⟨hs.trans (Finset.empty_subset _),hs.trans (Finset.empty_subset _)⟩
  have hl : rawLink X e (delta {e}) = delta ∅ := by
    apply SetLike.ext
    intro s
    change (s ⊆ X ∧ insert e s ⊆ {e}) ↔ s ⊆ ∅
    constructor
    · rintro ⟨hx,he⟩ v hv
      have hve : v = e := by simpa using he (Finset.mem_insert_of_mem hv)
      exact False.elim (heX (hve ▸ hx hv))
    · intro hs
      exact ⟨hs.trans (Finset.empty_subset _),Finset.insert_subset_iff.mpr
        ⟨by simp,hs.trans (Finset.empty_subset _)⟩⟩
  have hZY : delta Z ≤ delta Y := fun _ hs => hs.trans hZ
  simp only [parentOf,phi,hd,hl,(rawJoin_unit (delta Z)).1,
    (rawJoin_unit (delta Y)).1,sup_eq_right.mpr hZY]

/-- The terminal core schedule returns an ORIGINAL parent vertex. The e=p case
consumes genuine Gamma and the nonempty original R. It also covers X=empty. -/
def finishCore {X Y Z R : Finset V} {e p : V} {E : Family V}
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hE : Supported Y E)
    (hE0 : (∅ : Finset V) ∈ E) (hp : p ∈ insert e X)
    (permission : p = e → Nonempty (Sequence (project (delta Y)) (project E))) :
    Σ q : {q : V // q ∈ X ∪ Y},
      Sequence (project (parentOf X Y Z e E (delta {p})))
        (project (delta {q.1})) := by
  classical
  by_cases hpe : p = e
  · subst p
    let T := terminalAtInterface X Y R E hXY hR hRne hE hE0
      (Classical.choice (permission rfl))
    exact ⟨T.1,T.2.cast
      (congrArg project (singleton_parent_interface X Y Z e E heX hZ)).symm rfl⟩
  · have hpX : p ∈ X := (Finset.mem_insert.mp hp).resolve_left hpe
    let B := rawJoin (delta {p}) (delta Z) ⊔ rawJoin (delta X) E
    have hpB : ({p} : Finset V) ∈ B :=
      Or.inl ⟨{p},(show ({p} : Finset V) ⊆ {p} from le_rfl),∅,Finset.empty_subset _,by simp⟩
    have hcone : ∀ s ∈ B, insert p s ∈ B := by
      rintro s (⟨a,ha,b,hb,rfl⟩ | ⟨a,ha,b,hb,rfl⟩)
      · exact Or.inl ⟨insert p a,Finset.insert_subset_iff.mpr ⟨by simp,ha⟩,
          b,hb,by simp⟩
      · exact Or.inr ⟨insert p a,Finset.insert_subset_iff.mpr ⟨hpX,ha⟩,
          b,hb,by simp⟩
    have hB : Supported (X ∪ Y) B := by
      dsimp only [B]
      rw [← singleton_parent_other X Y Z e p E heX hpX hpe]
      exact parent_support X Y Z e E _ hZ hE
    exact ⟨⟨p,Finset.mem_union_left _ hpX⟩,
      (collapseCone (X ∪ Y) B p hB hpB hcone).cast
        (congrArg project (singleton_parent_other X Y Z e p E heX hpX hpe)).symm rfl⟩

/-- Full original parent constructor on literal original grounds. Main uses the
child main and P0/P1. Separate starts on Cout ALONE, uses Q0/Q1, the child core
list, and the computed terminal cone/Gamma list. Cout and critical faces are
filled from their explicit constructions, rather than supplied as hypotheses. -/
def compileParent {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    Certificate (X ∪ Y) (parentOf X Y Z e E K) := by
  have hE0 : (∅ : Finset V) ∈ E := f0.empty_mem.1
  have hz : Z ⊆ Y := by rw [hZ]; exact Finset.sdiff_subset
  have mainPermission : Nonempty (Sequence (project (delta Y)) (project E)) ∨
      ∀ P ∈ c.main.pairs, P.apex ≠ e :=
    permission.elim Or.inl (fun h => Or.inr h.1)
  have corePermission : Nonempty (Sequence (project (delta Y)) (project E)) ∨
      ∀ P ∈ c.separate.pairs, P.apex ≠ e :=
    permission.elim Or.inl (fun h => Or.inr h.2.1)
  have sourceSupport : Supported (insert e X) (nativeAug (project K)) := by
    rw [reconstruct_nonvoid K (source_empty c)]
    exact c.supported
  let M0 := replaySequence X Y Z e E hXY hz heX hE hE0 c.main
    sourceSupport mainPermission
  let M := (M0.cast
    (by rw [reconstruct_nonvoid K (source_empty c)])
    (by rw [reconstruct_nonvoid _ (endpoint_empty c)])).append
      (parentFillingStage c f0 f1 heX hXY hz hE)
  have coreSupport : Supported (insert e X) (nativeAug (project c.core)) := by
    rw [reconstruct_nonvoid c.core (core_empty c)]
    exact c.core_supported
  let Q := replaySequence X Y Z e E hXY hz heX hE hE0 c.separate
    coreSupport corePermission
  let Q' := Q.cast (by rw [reconstruct_nonvoid c.core (core_empty c)])
    (by rw [reconstruct_nonvoid (delta {c.vertex}) (Finset.empty_subset _)])
  have hp : c.vertex ∈ insert e X := c.core_supported _ c.vertex_mem (by simp)
  have terminalPermission : c.vertex = e →
      Nonempty (Sequence (project (delta Y)) (project E)) := by
    intro he
    exact permission.elim id (fun h => False.elim (h.2.2 he))
  let F := finishCore heX hXY hz hR hRne hE hE0 hp terminalPermission
  let Qall := ((parentCollarStage c f0 f1 heX hXY hz hE).append Q').append F.2
  have hcritical : ∀ s ∈ parentCritical e c.critical f0.critical f1.critical,
      s ⊆ X ∪ Y := by
    intro s hs
    have hn := (parentCellData c f0 f1 heX hXY hz hE).nonempty s hs
    have hsEnd : s ∈ project (endpoint
        (parentCore X Y Z e E c.core c.critical f0.collar f1.collar)
        (parentCritical e c.critical f0.critical f1.critical)) :=
      ⟨hn,Or.inr ⟨s,hs,le_rfl⟩⟩
    exact parent_support X Y Z e E K hz hE s (M.monotone hsEnd).2
  refine {
    supported := parent_support X Y Z e E K hz hE
    core := parentCore X Y Z e E c.core c.critical f0.collar f1.collar
    critical := parentCritical e c.critical f0.critical f1.critical
    vertex := F.1.1
    vertex_mem := ?_
    core_supported := ?_
    critical_supported := hcritical
    cells := parentCellData c f0 f1 heX hXY hz hE
    main := M
    separate := Qall }
  · exact (Qall.monotone ⟨by simp,by simp⟩).2
  · intro s hs
    by_cases hn : s.Nonempty
    · exact parent_support X Y Z e E K hz hE s
        (M.monotone ⟨hn,Or.inl hs⟩).2
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      exact Finset.empty_subset _

/-- The exact computed critical family is exposed by reduction of the actual
constructor. This equation is consumed by the wheel one-step consequences. -/
theorem compileParent_critical {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).critical =
      parentCritical e c.critical f0.critical f1.critical := rfl

/-- Whole-endpoint coordinate fixedness uses the real native homotopy; no
parallel simulated realization or homotopy is introduced. -/
theorem compiler_main_fixed {W : Finset V} {K : Family V} (c : Certificate W K)
    (t : unitInterval) (x : Space (project K))
    (hx : x.val ∈ realization (project (endpoint c.core c.critical))) (v : V) :
    (c.main.collapseHomotopy (t,x)).val v = x.val v := by
  exact congrArg (fun z : Space (project K) => z.val v)
    (c.main.collapseHomotopy_fixed t x hx)



open Classical in
/-- The descending cone is an actual rectangle on the original ground. -/
theorem collapseCone_orderedPairs (W : Finset V) (K : Family V) (p : V)
    (hs : Supported W K) (hp : ({p} : Finset V) ∈ K)
    (hcone : ∀ s ∈ K, insert p s ∈ K) :
    orderedPairs (collapseCone W K p hs hp hcone) =
      (fibres ((W.erase p).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ K))).map
        (fun t => (t, insert p t)) := by
  classical
  unfold orderedPairs orderedPair
  simp only [collapseCone, Sequence.pairs_cast,
    rectangle_order, Finset.empty_union]

private theorem terminalGamma_orderedPairs (X Y : Finset V) (E : Family V)
    (hXY : Disjoint X Y) (hE : Supported Y E)
    (h0 : (∅ : Finset V) ∈ E)
    (G : Sequence (project (delta Y)) (project E)) :
    orderedPairs (terminalGamma X Y E hXY hE h0 G) = orderedPairs G := by
  unfold orderedPairs orderedPair
  simp only [terminalGamma, Sequence.pairs_cast,
    liftFibre_pairs, Finset.empty_union]

/-- The actual original terminal vertex, specified independently of any
certificate: preserve p away from e, otherwise use the same finite choice as
terminalAtInterface. -/
def finishVertex (X R : Finset V) (e p : V) (hRne : R.Nonempty) : V :=
  if p = e then
    if hX : X.Nonempty then hX.choose else hRne.choose
  else p

/-- The entire terminal face list on the full original ground. Gamma is used
only when e=p and X is nonempty; the X-empty case is the original Y-simplex. -/
def finishFacePairs (X Y Z R : Finset V) (e p : V) (E : Family V)
    (hRne : R.Nonempty) (gamma : List (Finset V × Finset V)) :
    List (Finset V × Finset V) := by
  classical
  exact if p = e then
    if hX : X.Nonempty then
      gamma ++ (fibres (((X ∪ Y).erase hX.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ∈ rawJoin (delta X) E))).map
          (fun t => (t, insert hX.choose t))
    else
      (fibres ((Y.erase hRne.choose).powerset.filter
        (fun s => s.Nonempty ∧ s ⊆ Y))).map
          (fun t => (t, insert hRne.choose t))
  else
    (fibres (((X ∪ Y).erase p).powerset.filter
      (fun s => s.Nonempty ∧ s ∈
        rawJoin (delta {p}) (delta Z) ⊔ rawJoin (delta X) E))).map
          (fun t => (t, insert p t))

/-- The terminal block selected by `finishCore`, with both the e=p Gamma
    branch and the original-vertex cone branch made explicit. -/
def finishPairSchedule (X Y Z R : Finset V) (e p : V) (E : Family V)
    (hXY : Disjoint X Y) (hR : R ⊆ Y) (hRne : R.Nonempty)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    (permission : p = e → Nonempty (Sequence (project (delta Y)) (project E))) :
    List (Finset V × Finset V) := by
  classical
  by_cases hpe : p = e
  · let G := Classical.choice (permission hpe)
    by_cases hX : X.Nonempty
    · let q := hX.choose
      let B := rawJoin (delta X) E
      exact G.pairs.map (fun Q => (Q.lower,Q.upper)) ++
        (fibres (((X ∪ Y).erase q).powerset.filter
          (fun s => s.Nonempty ∧ s ∈ B))).map
          (fun t => (t, insert q t))
    · let q := hRne.choose
      exact (fibres ((Y.erase q).powerset.filter
        (fun s => s.Nonempty ∧ s ⊆ Y))).map
        (fun t => (t, insert q t))
  · let B := rawJoin (delta {p}) (delta Z) ⊔ rawJoin (delta X) E
    exact (fibres (((X ∪ Y).erase p).powerset.filter
      (fun s => s.Nonempty ∧ s ∈ B))).map
      (fun t => (t, insert p t))

/-- Proof irrelevance identifies the chosen right Gamma from any existing
Nonempty permission with the same choice in rightGammaPairs. No equality with
a particular supplied witness is asserted. -/
theorem finishPairSchedule_faces (X Y Z R : Finset V) (e p : V) (E : Family V)
    (hXY : Disjoint X Y) (hR : R ⊆ Y) (hRne : R.Nonempty)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    (permission : p = e → Nonempty (Sequence (project (delta Y)) (project E))) :
    finishPairSchedule X Y Z R e p E hXY hR hRne hE hE0 permission =
      finishFacePairs X Y Z R e p E hRne (rightGammaPairs Y E) := by
  classical
  by_cases hpe : p = e
  · have hg := permission hpe
    by_cases hX : X.Nonempty
    · simp only [finishPairSchedule, finishFacePairs, dif_pos hpe,
        if_pos hpe, dif_pos hX, rightGammaPairs, dif_pos hg, orderedPairs]
      unfold orderedPair
      rfl
    · simp only [finishPairSchedule, finishFacePairs, dif_pos hpe,
        if_pos hpe, dif_neg hX]
  · simp only [finishPairSchedule, finishFacePairs, dif_neg hpe, if_neg hpe]

/-- Exact list extraction for the private terminal constructor in the same
    owner.  The proof follows its two tests and uses only the actual cone and
    Gamma/fibre schedules. -/
theorem finishCore_orderedPairs {X Y Z R : Finset V} {e p : V} {E : Family V}
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hE : Supported Y E)
    (hE0 : (∅ : Finset V) ∈ E) (hp : p ∈ insert e X)
    (permission : p = e → Nonempty (Sequence (project (delta Y)) (project E))) :
    orderedPairs (finishCore heX hXY hZ hR hRne hE hE0 hp permission).2 =
      finishPairSchedule X Y Z R e p E hXY hR hRne hE hE0 permission := by
  classical
  by_cases hpe : p = e
  · subst p
    unfold finishCore
    erw [dif_pos (rfl : e = e)]
    dsimp only
    erw [orderedPairs_cast]
    by_cases hX : X.Nonempty
    · simp only [terminalAtInterface, dif_pos hX, orderedPairs_append,
        terminalGamma_orderedPairs, collapseCone_orderedPairs,
        finishPairSchedule, dif_pos (rfl : e = e)]
      unfold orderedPairs orderedPair
      rfl
    · simp only [terminalAtInterface, dif_neg hX, orderedPairs_cast,
        collapseCone_orderedPairs, finishPairSchedule, dif_pos (rfl : e = e)]
  · unfold finishCore
    erw [dif_neg hpe]
    simp [finishPairSchedule, hpe, orderedPairs_cast, collapseCone_orderedPairs]

private theorem finishCore_vertex {X Y Z R : Finset V} {e p : V} {E : Family V}
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hE : Supported Y E)
    (hE0 : (∅ : Finset V) ∈ E) (hp : p ∈ insert e X)
    (permission : p = e → Nonempty (Sequence (project (delta Y)) (project E))) :
    (finishCore heX hXY hZ hR hRne hE hE0 hp permission).1.1 =
      finishVertex X R e p hRne := by
  classical
  by_cases hpe : p = e
  · subst p
    by_cases hX : X.Nonempty
    · simp [finishCore, terminalAtInterface, finishVertex, hX]
    · simp [finishCore, terminalAtInterface, finishVertex, hX]
  · simp [finishCore, finishVertex, hpe]

/-- Computed parent vertex is consumed by the independent row seed recursion. -/
theorem compileParent_vertex
    {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).vertex =
      finishVertex X R e c.vertex hRne := by
  unfold compileParent
  exact finishCore_vertex _ _ _ _ _ _ _ _ _

/-- Full main list: child-main replay, then the ordered filling blocks. -/
theorem compileParent_main_orderedPairs
    {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    orderedPairs (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).main =
      c.main.pairs.flatMap (fun P =>
        replayFacePairs Y Z e E (orderedPair P) (rightGammaPairs Y E)) ++
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).main.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) := by
  classical
  unfold compileParent
  simp only [orderedPairs_append, orderedPairs_cast]
  rw [replaySequence_orderedPairs, parentFillingStage_orderedPairs]

/-- Full separate/core list: collars on `Cout` alone, child-core replay, then
    the original-vertex cone/Gamma terminal block, including e=p and X=∅. -/
theorem compileParent_separate_orderedPairs
    {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    orderedPairs (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).separate =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).separate.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) ++
      c.separate.pairs.flatMap (fun P =>
        replayFacePairs Y Z e E (orderedPair P) (rightGammaPairs Y E)) ++
      finishPairSchedule X Y Z R e c.vertex E hXY hR hRne hE f0.empty_mem.1
        (fun h => permission.elim (fun hg => hg)
          (fun hn => False.elim (hn.2.2 h))) := by
  classical
  unfold compileParent
  simp only [orderedPairs_append, orderedPairs_cast]
  rw [parentCollarStage_orderedPairs, replaySequence_orderedPairs,
    finishCore_orderedPairs] <;> simp only [List.append_assoc]

/-- Public endpoint consumed by row-history code.  The two equalities are kept
    together so neither the main nor the separate recursion can be dropped. -/
def ParentExpansion
    {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) : Prop :=
  orderedPairs (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).main =
      c.main.pairs.flatMap (fun P => replayFacePairs Y Z e E (orderedPair P) (rightGammaPairs Y E)) ++
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).main.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) ∧
  orderedPairs (compileParent c f0 f1 heX heY hXY hR hRne hZ hE permission).separate =
      (fibres c.critical).flatMap (fun q =>
        (selectFilling e f0 f1 q).separate.pairs.map
          (fun P => (criticalPart e q ∪ P.lower,
            criticalPart e q ∪ P.upper))) ++
      c.separate.pairs.flatMap (fun P => replayFacePairs Y Z e E (orderedPair P) (rightGammaPairs Y E)) ++
      finishPairSchedule X Y Z R e c.vertex E hXY hR hRne hE f0.empty_mem.1
        (fun h => permission.elim (fun hg => hg)
          (fun hn => False.elim (hn.2.2 h)))

 theorem compileParent_consumed_expansion
    {X Y Z R : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (heY : e ∉ Y) (hXY : Disjoint X Y)
    (hR : R ⊆ Y) (hRne : R.Nonempty) (hZ : Z = Y \ R)
    (hE : Supported Y E)
    (permission : CompilerPermission (Y := Y) (Z := Z) (E := E) c) :
    ParentExpansion c f0 f1 heX heY hXY hR hRne hZ hE permission := by
  exact ⟨compileParent_main_orderedPairs c f0 f1 heX heY hXY hR hRne hZ hE permission,
    compileParent_separate_orderedPairs c f0 f1 heX heY hXY hR hRne hZ hE permission⟩


end D5.S3.Geometry.OriginalLabelTwoSum
