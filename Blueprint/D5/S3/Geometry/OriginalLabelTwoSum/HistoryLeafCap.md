# HistoryLeafCap

## Abstract

Tagged singleton caps and leaf strips construct actual native main and separate core lists on unchanged labelled grounds.

Output distinguishes literal VOID and UNIT from the existing Certificate containing actual native Sequence values. padCertificate lifts the smaller factor main, proves critical absence/full boundaries/antichains, and independently lifts its C-only list, deletes the point layer by emitPair, then executes collapseCone on the base. The singleton cap handles empty old ground. oneLeafStrip is the actual dominated b-layer list and uses the smaller DELETION factor; twoLeafStrip uses the smaller LINK factor. Empty-U branches are actual isolated points or an edge. prependOutput retains raw empty membership so projection cannot confuse VOID with UNIT. widening a ground adds ghosts, never faces. These local constructors legitimately consume smaller outputs; no universal history theorem with desired supplier fields is claimed. HistoryPaths, HistorySeed, HistoryIsolated and HistoryAttachment consume these constructors.

The constructions retain the lexical parameters and hypotheses of the paired Lean module.

The existing actual cap, padding, one-leaf DELETION and two-leaf LINK constructors are preserved. CriticalState extracts the actual tag and actual strong critical family without assigning an empty ordinary critical to UNIT. The new readback lemmas prove what these constructors emit; they are consumed in the path induction. Both lists still have their original native domains and order.

**Definition 1.1 (Output).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.Output`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.Output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

inductive Output (W : Finset V) (K : Family V) : Type _

  | void (eq_void : K = ⊥)

  | unit (eq_unit : K = delta ∅)

  | strong (certificate : Certificate W K)

**Definition 1.2 (changeOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def changeOutput {W : Finset V} {K L : Family V}

    (o : Output W K) (h : K = L) : Output W L := by

  subst L

  exact o

**Definition 1.3 (coneCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.coneCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.coneCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def coneCertificate (W : Finset V) (K : Family V) (p : V)

    (hs : Supported W K) (hp : ({p} : Finset V) ∈ K)

    (hc : ∀ s ∈ K, insert p s ∈ K) : Certificate W K where

  supported := hs

  core := K

  critical := ∅

  vertex := p

  vertex_mem := hp

  core_supported := hs

  critical_supported := by simp

  cells := ⟨by simp, by simp, by simp, by simp⟩

  main := (Sequence.refl (project K)).cast rfl (by

    congr 1

    apply SetLike.ext

    intro s

    simp [endpoint, facets])

  separate := collapseCone W K p hs hp hc

**Definition 1.4 (padCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def padCertificate (W U d : Finset V) (B M : Family V)

    (c : Certificate U M) (x : V) (hd : d.Nonempty) (hdu : Disjoint d U)

    (hW : d ∪ U ⊆ W) (hB : Supported W B) (hx : ({x} : Finset V) ∈ B)

    (hcone : ∀ s ∈ B, insert x s ∈ B)

    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)

    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :

    Certificate W (B ⊔ rawJoin (delta d) M) := by

  classical

  let C := B ⊔ rawJoin (delta d) c.core

  let Q := c.critical.image (fun q => d ∪ q)

  have hpU : c.vertex ∈ U := c.core_supported {c.vertex} c.vertex_mem (by simp)

  have hpD : c.vertex ∉ d := fun h => Finset.disjoint_left.mp hdu h hpU

  have hC0 : (∅ : Finset V) ∈ c.core := c.core.lower (Finset.empty_subset _) c.vertex_mem

  have hM0 : (∅ : Finset V) ∈ M := by

    have hm : {c.vertex} ∈ M := (c.main.monotone ⟨by simp, Or.inl c.vertex_mem⟩).2

    exact M.lower (Finset.empty_subset _) hm

  have hN0 : (∅ : Finset V) ∈ endpoint c.core c.critical := Or.inl hC0

  have supportJoin : ∀ {N : Family V}, Supported U N →

      Supported W (B ⊔ rawJoin (delta d) N) := by

    intro N hN s hs

    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩

    · exact hB s hs

    · exact (Finset.union_subset_union ha (hN t ht)).trans hW

  have noBase : ∀ (N : Family V) t, t ⊆ U → d ∪ t ∈ B → t ∈ N := by

    intro N t _ ht

    exact False.elim (hmissing _ ht Finset.subset_union_left)

  let P := liftFibre M (endpoint c.core c.critical) B d U hM0 hN0 c.main hdu

    c.supported (fun z hz t ht => hboundary z hz t (c.supported t ht))

    (noBase (endpoint c.core c.critical))

  have hEnd : B ⊔ rawJoin (delta d) (endpoint c.core c.critical) = endpoint C Q := by

    apply SetLike.ext

    intro s

    constructor

    · rintro (hs | ⟨a, ha, t, ht, rfl⟩)

      · exact Or.inl (Or.inl hs)

      · rcases ht with ht | ⟨q, hq, htq⟩

        · exact Or.inl (Or.inr ⟨a, ha, t, ht, rfl⟩)

        · exact Or.inr ⟨d ∪ q, Finset.mem_image.mpr ⟨q, hq, rfl⟩,

            Finset.union_subset_union ha htq⟩

    · rintro ((hs | ⟨a, ha, t, ht, rfl⟩) | ⟨q, hq, hs⟩)

      · exact Or.inl hs

      · exact Or.inr ⟨a, ha, t, Or.inl ht, rfl⟩

      · change q ∈ c.critical.image (fun q => d ∪ q) at hq

        obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

        clear hq

        have hq := hqSource

        refine Or.inr ⟨s ∩ d, Finset.inter_subset_right, s ∩ q,

          Or.inr ⟨q, hq, Finset.inter_subset_right⟩, ?_⟩

        exact split_union hs

  have hCells : CriticalData C Q := by

    constructor

    · intro q hq

      change q ∈ c.critical.image (fun q => d ∪ q) at hq

      obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

      clear hq

      have hq := hqSource

      exact hd.mono Finset.subset_union_left

    · intro q hq hC

      change q ∈ c.critical.image (fun q => d ∪ q) at hq

      obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

      clear hq

      have hq := hqSource

      rcases hC with hBq | ⟨a, ha, t, ht, he⟩

      · exact hmissing _ hBq Finset.subset_union_left

      · have hqt : q ⊆ t := subset_right_of_disjoint hdu ha

          (c.critical_supported q hq) (by rw [← he]; exact Finset.subset_union_right)

        exact c.cells.absent q hq (c.core.lower hqt ht)

    · intro q hq s hs

      change q ∈ c.critical.image (fun q => d ∪ q) at hq

      obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

      clear hq

      have hq := hqSource

      have hqU := c.critical_supported q hq

      have hsDU := hs.subset.trans (Finset.union_subset_union le_rfl hqU)

      have hsplit := split_union hsDU

      by_cases hdS : d ⊆ s

      · right

        have htq : s ∩ U ⊆ q := subset_right_of_disjoint hdu le_rfl

          Finset.inter_subset_right (Finset.inter_subset_left.trans hs.subset)

        have hproper : s ∩ U ⊂ q := by

          apply Finset.ssubset_iff_subset_ne.mpr

          refine ⟨htq, ?_⟩

          intro he

          have hqs : q ⊆ s := by rw [← he]; exact Finset.inter_subset_left

          exact hs.ne (Finset.Subset.antisymm hs.subset (Finset.union_subset hdS hqs))

        exact ⟨s ∩ d, Finset.inter_subset_right, s ∩ U,

          c.cells.boundary q hq _ hproper, hsplit⟩

      · left

        have hproper : s ∩ d ⊂ d := by

          apply Finset.ssubset_iff_subset_ne.mpr

          refine ⟨Finset.inter_subset_right, ?_⟩

          intro he

          apply hdS

          rw [← he]

          exact Finset.inter_subset_left

        rw [hsplit]

        exact hboundary (s ∩ d) hproper (s ∩ U) Finset.inter_subset_right

    · intro q hq t ht hqt

      change q ∈ c.critical.image (fun q => d ∪ q) at hq

      obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

      clear hq

      have hq := hqSource

      change t ∈ c.critical.image (fun q => d ∪ q) at ht

      obtain ⟨t, htSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp ht

      clear ht

      have ht := htSource

      exact congrArg (fun s => d ∪ s) (c.cells.antichain q hq t ht

        (union_cancel_right hdu (c.critical_supported q hq) hqt))

  let T := liftFibre c.core (delta {c.vertex}) B d U hC0 (by simp) c.separate hdu

    c.core_supported (fun z hz t ht => hboundary z hz t (c.core_supported t ht))

    (noBase (delta {c.vertex}))

  let H := B ⊔ rawJoin (delta d) (delta {c.vertex})

  have hUpper : insert c.vertex d ∈ H := by

    right

    refine ⟨d, ?_, {c.vertex}, ?_, ?_⟩

    · change d ⊆ d

      exact le_rfl

    · change ({c.vertex} : Finset V) ⊆ {c.vertex}

      exact le_rfl

    · ext v

      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]

      tauto

  have hFree : ∀ s ∈ H, d ⊆ s → s = d ∨ s = insert c.vertex d := by

    intro s hs hds

    rcases hs with hs | ⟨a, ha, t, ht, rfl⟩

    · exact False.elim (hmissing s hs hds)

    · apply interval_pair hds

      intro v hv

      rcases Finset.mem_union.mp hv with hva | hvt

      · exact Finset.mem_insert_of_mem (ha hva)

      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (ht hvt)))

  let R := emitPair H d c.vertex hd hpD hUpper hFree

  have hRetained : R.retained = project B := by

    dsimp only [R]

    rw [emitPair_retained]

    congr 1

    apply SetLike.ext

    intro s

    constructor

    · rintro ⟨hs, hn⟩

      have hnot : ¬ d ⊆ s := fun h => hn d (by simp) h

      rcases hs with hs | ⟨a, ha, t, ht, rfl⟩

      · exact hs

      · have hproper : a ⊂ d := Finset.ssubset_iff_subset_ne.mpr ⟨ha, by

          intro he

          apply hnot

          rw [he]

          exact Finset.subset_union_left⟩

        exact hboundary a hproper t (ht.trans (Finset.singleton_subset_iff.mpr hpU))

    · intro hs

      refine ⟨Or.inl hs, ?_⟩

      intro a ha h

      have he : a = d := Finset.mem_singleton.mp ha

      subst a

      exact hmissing s hs h

  let Rseq : Sequence (project H) (project B) :=

    Sequence.step R ((Sequence.refl (project B)).cast hRetained.symm rfl)

  refine {

    supported := supportJoin c.supported

    core := C

    critical := Q

    vertex := x

    vertex_mem := Or.inl hx

    core_supported := supportJoin c.core_supported

    critical_supported := ?_

    cells := hCells

    main := P.cast rfl (congrArg project hEnd)

    separate := T.append (Rseq.append (collapseCone W B x hB hx hcone)) }

  intro q hq

  change q ∈ c.critical.image (fun q => d ∪ q) at hq

  obtain ⟨q, hqSource, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq

  clear hq

  have hq := hqSource

  exact (Finset.union_subset_union le_rfl (c.critical_supported q hq)).trans hW

**Definition 1.5 (paddedOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def paddedOutput (W U d : Finset V) (B M : Family V)

    (o : Output U M) (x : V) (hd : d.Nonempty) (hdu : Disjoint d U)

    (hW : d ∪ U ⊆ W) (hB : Supported W B) (hx : ({x} : Finset V) ∈ B)

    (hcone : ∀ s ∈ B, insert x s ∈ B)

    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)

    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :

    Output W (B ⊔ rawJoin (delta d) M) := by

  classical

  cases o with

  | void h =>

      subst M

      exact changeOutput (.strong (coneCertificate W B x hB hx hcone)) (by

        rw [(rawJoin_void (delta d)).2, sup_bot_eq])

  | unit h =>

      subst M

      have hj : rawJoin (delta d) (delta ∅) = delta d := (rawJoin_unit _).2

      let c : Certificate W (B ⊔ delta d) := {

        supported := by

          intro s hs

          exact hs.elim (hB s) (fun h => h.trans (Finset.subset_union_left.trans hW))

        core := B

        critical := {d}

        vertex := x

        vertex_mem := hx

        core_supported := hB

        critical_supported := by

          intro s hs

          have he := Finset.mem_singleton.mp hs

          subst s

          exact Finset.subset_union_left.trans hW

        cells := {

          nonempty := by intro s hs; have he := Finset.mem_singleton.mp hs

                         subst s; exact hd

          absent := by intro s hs h; have he := Finset.mem_singleton.mp hs

                       subst s; exact hmissing d h le_rfl

          boundary := by intro s hs t ht; have he := Finset.mem_singleton.mp hs

                         subst s; simpa using hboundary t ht ∅ (Finset.empty_subset U)

          antichain := by intro s hs t ht _; exact

            (Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm }

        main := (Sequence.refl (project (B ⊔ delta d))).cast rfl (by

          congr 1; apply SetLike.ext; intro s; simp [endpoint, facets])

        separate := collapseCone W B x hB hx hcone }

      exact changeOutput (.strong c) (by rw [hj])

  | strong c => exact .strong (padCertificate W U d B M c x hd hdu hW hB hx

      hcone hmissing hboundary)

**Definition 1.6 (capOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.capOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.capOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def capOutput (U : Finset V) (a : V) (M : Family V) (ha : a ∉ U)

    (hs : Supported U M) (o : Output U M) :

    Output (insert a U) (delta U ⊔ rawJoin (delta {a}) M) := by

  classical

  by_cases hU : U.Nonempty

  · let x := hU.choose

    have hx : x ∈ U := hU.choose_spec

    exact paddedOutput (insert a U) U {a} (delta U) M o x (by simp)

      (by simpa using ha) (by simp) (fun _ h => h.trans (Finset.subset_insert _ _))

      (Finset.singleton_subset_iff.mpr hx)

      (fun s h => Finset.insert_subset hx h)

      (fun s h hsub => ha (h (hsub (by simp)))) (by

        intro z hz t ht

        have hz0 : z = ∅ := by

          apply Finset.eq_empty_iff_forall_notMem.mpr

          intro v hv

          have hva := Finset.mem_singleton.mp (hz.subset hv)

          exact hz.ne (Finset.Subset.antisymm hz.subset

            (Finset.singleton_subset_iff.mpr (hva ▸ hv)))

        simpa [hz0] using ht)

  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU

    subst U

    by_cases h0 : (∅ : Finset V) ∈ M

    · have hM : M = delta ∅ := by

        apply SetLike.ext; intro s

        exact ⟨hs s, fun h => M.lower h h0⟩

      have he : delta ∅ ⊔ rawJoin (delta {a}) M = delta {a} := by

        rw [hM, (rawJoin_unit _).2]

        exact sup_eq_right.mpr (fun s h => h.trans (Finset.empty_subset _))

      exact changeOutput (.strong (coneCertificate {a} (delta {a}) a (fun _ h => h)

        (by change ({a} : Finset V) ⊆ {a}; exact le_rfl) (fun s h => Finset.insert_subset (by simp) h))) he.symm

    · have hM : M = ⊥ := by

        apply SetLike.ext; intro s

        constructor

        · intro h; exact False.elim (h0 (M.lower (Finset.empty_subset _) h))

        · intro h; exact False.elim h

      exact .unit (by rw [hM, (rawJoin_void _).2, sup_bot_eq])

**Definition 1.7 (singletonOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.singletonOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.singletonOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def singletonOutput (r : Rows V) (a : V) (ha : a ∈ r.ground)

    (c : r.chords) (hc : r.row c = {a})

    (o : Output (avoiding r a).ground (avoiding r a).root) :

    Output r.ground r.root := by

  have out := capOutput (r.ground.erase a) a (avoiding r a).root (by simp)

    (avoiding r a).root_supported o

  have hg : insert a (r.ground.erase a) = r.ground := Finset.insert_erase ha

  rw [hg] at out

  exact changeOutput out (singleton_cap r a ha c hc).symm

**Definition 1.8 (prependOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def prependOutput (W : Finset V) (K L : Family V)

    (hs : Supported W K) (h0 : (∅ : Finset V) ∈ K ↔ ∅ ∈ L)

    (S : Sequence (project K) (project L)) (o : Output W L) : Output W K := by

  cases o with

  | void h =>

      subst L

      have he := sequence_empty_target S (by intro s h; exact h.2)

      exact .void (raw_ext h0 he)

  | unit h =>

      subst L

      have he := sequence_empty_target S (by

        rintro s ⟨hn, hs⟩

        have he : s = ∅ := Finset.subset_empty.mp hs

        exact Finset.not_nonempty_empty (he ▸ hn))

      exact .unit (raw_ext h0 he)

  | strong c =>

      exact .strong {

        supported := hs

        core := c.core

        critical := c.critical

        vertex := c.vertex

        vertex_mem := c.vertex_mem

        core_supported := c.core_supported

        critical_supported := c.critical_supported

        cells := c.cells

        main := S.append c.main

        separate := c.separate }

**Definition 1.9 (widenOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def widenOutput {W W' : Finset V} {K : Family V}

    (h : W ⊆ W') (o : Output W K) : Output W' K := by

  cases o with

  | void he => exact .void he

  | unit he => exact .unit he

  | strong c => exact .strong {

      supported := fun s hs => (c.supported s hs).trans h

      core := c.core

      critical := c.critical

      vertex := c.vertex

      vertex_mem := c.vertex_mem

      core_supported := fun s hs => (c.core_supported s hs).trans h

      critical_supported := fun s hs => (c.critical_supported s hs).trans h

      cells := c.cells

      main := c.main

      separate := c.separate }

**Definition 1.10 (oneLeafFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def oneLeafFamily (U : Finset V) (a : V) (K : Family V) : Family V :=

  delta U ⊔ rawJoin (delta {a}) K

**Definition 1.11 (oneLeafStrip).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafStrip`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def oneLeafStrip (U : Finset V) (a b : V) (K : Family V)

    (ha : a ∉ insert b U) (hb : b ∉ U) (hs : Supported (insert b U) K) :

    Sequence (project (oneLeafFamily U a K))

      (project (oneLeafFamily U a (restrict U K))) := by

  have hab : a ≠ b := fun he => ha (Finset.mem_insert.mpr (Or.inl he))

  have hExt : FiniteVertexDominationCollapse.Extends (project (oneLeafFamily U a K)) a b := by

    rintro s ⟨hn, h | ⟨x, hx, t, ht, rfl⟩⟩ hbs

    · exact False.elim (hb (h hbs))

    · exact ⟨Finset.insert_nonempty _ _, Or.inr

        ⟨insert a x, Finset.insert_subset (by simp) hx, t, ht, by simp⟩⟩

  exact (FiniteVertexDominationCollapse.sequence _ a b hab hExt).cast rfl

    (oneLeaf_delete U a b K ha hb hs)

**Definition 1.12 (oneLeafOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def oneLeafOutput (U : Finset V) (a b : V) (K : Family V)

    (ha : a ∉ insert b U) (hb : b ∉ U) (hs : Supported (insert b U) K)

    (o : Output U (restrict U K)) :

    Output (insert a (insert b U)) (oneLeafFamily U a K) := by

  have cap := capOutput U a (restrict U K) (fun h => ha (Finset.mem_insert_of_mem h))

    (fun _ h => h.2) o

  have cap' : Output (insert a (insert b U))

      (oneLeafFamily U a (restrict U K)) := widenOutput (by

    intro v hv

    rcases Finset.mem_insert.mp hv with rfl | hv

    · simp

    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)) cap

  exact prependOutput _ _ _ (oneLeaf_supported U a b K hs)

    ⟨fun _ => Or.inl (Finset.empty_subset _), fun _ => Or.inl (Finset.empty_subset _)⟩

    (oneLeafStrip U a b K ha hb hs) cap'

**Definition 1.13 (twoLeafFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def twoLeafFamily (U : Finset V) (a b c : V) (K : Family V) : Family V :=

  (delta (insert c U) ⊔ delta (insert a U)) ⊔ rawJoin (delta {a,b}) K

**Definition 1.14 (twoLeafEnd).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafEnd`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def twoLeafEnd (U : Finset V) (a c : V) (M : Family V) : Family V :=

  (delta (insert a U) ⊔ delta (insert c U)) ⊔ rawJoin (delta {a,c}) M

**Definition 1.15 (twoLeafStrip).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafStrip`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafStrip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def twoLeafStrip (U : Finset V) (a b c : V) (K : Family V)

    (ha : a ∉ insert b (insert c U)) (hb : b ∉ insert c U)

    (hc : c ∉ U) (hs : Supported (insert c U) K) :

    Sequence (project (twoLeafFamily U a b c K))

      (project (twoLeafEnd U a c (rawLink U c K))) := by

  have hab : a ≠ b := fun h => ha (Finset.mem_insert.mpr (Or.inl h))

  have hExt : FiniteVertexDominationCollapse.Extends

      (project (twoLeafFamily U a b c K)) a b := by

    rintro s ⟨hn, (h | h) | ⟨x, hx, t, ht, rfl⟩⟩ hbs

    · exact False.elim (hb (h hbs))

    · have hbU : b ∉ U := fun h => hb (Finset.mem_insert_of_mem h)

      exact False.elim ((Finset.mem_insert.mp (h hbs)).elim

        (fun h => hab h.symm) hbU)

    · exact ⟨Finset.insert_nonempty _ _, Or.inr

        ⟨insert a x, Finset.insert_subset (by simp) hx, t, ht, by simp⟩⟩

  exact (FiniteVertexDominationCollapse.sequence _ a b hab hExt).cast rfl

    (twoLeaf_delete U a b c K ha hb hc hs)

**Definition 1.16 (twoLeafOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

The following are literal source declarations, not elaborated metadata. Literal common source context: noncomputable section; open Set Finset; namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; open OriginalLabelTwoSum HistoryCorners; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V]. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. 

Exact public SOURCE declaration and body:

def twoLeafOutput (U : Finset V) (a b c : V) (K : Family V)

    (ha : a ∉ insert b (insert c U)) (hb : b ∉ insert c U)

    (hc : c ∉ U) (hs : Supported (insert c U) K)

    (o : Output U (rawLink U c K)) :

    Output (insert a (insert b (insert c U))) (twoLeafFamily U a b c K) := by

  let out := twoLeafEndOutput U a b c (rawLink U c K) ha hc (fun _ h => h.1) o

  exact prependOutput _ _ _ (twoLeaf_supported U a b c K hs)

    ⟨fun _ => Or.inl (Or.inl (Finset.empty_subset _)),

      fun _ => Or.inl (Or.inl (Finset.empty_subset _))⟩

    (twoLeafStrip U a b c K ha hb hc hs) out

**Definition 1.17 (CriticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.CriticalState`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.CriticalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

inductive CriticalState (V : Type*) : Type _

  | void

  | unit

  | strong (tops : Finset (Finset V))

**Definition 1.18 (Output.criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.criticalState`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.criticalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

def Output.criticalState {W : Finset V} {K : Family V} : Output W K → CriticalState V

  | .void _ => .void

  | .unit _ => .unit

  | .strong c => .strong c.critical

**Theorem 1.19 (changeOutput_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

@[simp] theorem changeOutput_criticalState {W : Finset V} {K L : Family V}

    (o : Output W K) (h : K = L) :

    (changeOutput o h).criticalState = o.criticalState := by

  subst L

  rfl

**Definition 1.20 (padCriticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCriticalState`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCriticalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

def padCriticalState (d : Finset V) : CriticalState V → CriticalState V

  | .void => .strong ∅

  | .unit => .strong {d}

  | .strong D => .strong (D.image (fun q => d ∪ q))

**Theorem 1.21 (widenOutput_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

@[simp] theorem widenOutput_criticalState {W W' : Finset V} {K : Family V}

    (h : W ⊆ W') (o : Output W K) :

    (widenOutput h o).criticalState = o.criticalState := by

  cases o <;> rfl

**Theorem 1.22 (prependOutput_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

@[simp] theorem prependOutput_criticalState (W : Finset V) (K L : Family V)

    (hs : Supported W K) (h0 : (∅ : Finset V) ∈ K ↔ ∅ ∈ L)

    (S : Sequence (project K) (project L)) (o : Output W L) :

    (prependOutput W K L hs h0 S o).criticalState = o.criticalState := by

  cases o with

  | void h => subst L; rfl

  | unit h => subst L; rfl

  | strong c => rfl

**Theorem 1.23 (paddedOutput_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

theorem paddedOutput_criticalState (W U d : Finset V) (B M : Family V)

    (o : Output U M) (x : V) (hd : d.Nonempty) (hdu : Disjoint d U)

    (hW : d ∪ U ⊆ W) (hB : Supported W B) (hx : ({x} : Finset V) ∈ B)

    (hcone : ∀ s ∈ B, insert x s ∈ B)

    (hmissing : ∀ s ∈ B, ¬ d ⊆ s)

    (hboundary : ∀ z ⊂ d, ∀ t ⊆ U, z ∪ t ∈ B) :

    (paddedOutput W U d B M o x hd hdu hW hB hx hcone hmissing hboundary).criticalState =

      padCriticalState d o.criticalState := by

  cases o with

  | void h =>

      subst M

      unfold paddedOutput

      rw [changeOutput_criticalState]

      rfl

  | unit h =>

      subst M

      unfold paddedOutput

      rw [changeOutput_criticalState]

      rfl

  | strong c => rfl

**Theorem 1.24 (twoLeafOutput_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

theorem twoLeafOutput_criticalState (U : Finset V) (a b c : V) (K : Family V)

    (ha : a ∉ insert b (insert c U)) (hb : b ∉ insert c U)

    (hc : c ∉ U) (hs : Supported (insert c U) K)

    (o : Output U (rawLink U c K)) (hU : U.Nonempty) :

    (twoLeafOutput U a b c K ha hb hc hs o).criticalState =

      padCriticalState {a,c} o.criticalState := by

  simp only [twoLeafOutput, prependOutput_criticalState]

  simp only [twoLeafEndOutput, dif_pos hU, if_pos hU, paddedOutput_criticalState]

**Theorem 1.25 (twoLeafOutput_empty_criticalState).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_empty_criticalState`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_empty_criticalState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners, D5.S3.Geometry.OriginalLabelTwoSum.Cone, D5.S3.Geometry.FiniteVertexDominationCollapse. Exact public declaration and proof/source body:

theorem twoLeafOutput_empty_criticalState (a b c : V) (K : Family V)

    (ha : a ∉ insert b (insert c ∅)) (hb : b ∉ insert c ∅)

    (hc : c ∉ (∅ : Finset V)) (hs : Supported (insert c ∅) K)

    (o : Output ∅ (rawLink ∅ c K)) :

    (twoLeafOutput ∅ a b c K ha hb hc hs o).criticalState =

      .strong (if (∅ : Finset V) ∈ rawLink ∅ c K then ∅ else {{c}}) := by

  classical

  simp only [twoLeafOutput, prependOutput_criticalState]

  by_cases h0 : (∅ : Finset V) ∈ rawLink ∅ c K

  · simp [twoLeafEndOutput, h0, changeCertificate, coneCertificate,

      Output.criticalState]

  · simp [twoLeafEndOutput, h0, changeOutput_criticalState, widenOutput_criticalState,

      capOutput, Finset.singleton_nonempty, paddedOutput_criticalState, padCriticalState]

    rfl

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.CriticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.Output`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.capOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.changeOutput_criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.coneCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.oneLeafStrip`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.padCriticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.paddedOutput_criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.prependOutput_criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.singletonOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafEnd`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafOutput_empty_criticalState`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.twoLeafStrip`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap.widenOutput_criticalState`
- Dependency: [D5/S3/Geometry/FiniteVertexDominationCollapse](../FiniteVertexDominationCollapse.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Cone](Cone.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners](HistoryCorners.md)
