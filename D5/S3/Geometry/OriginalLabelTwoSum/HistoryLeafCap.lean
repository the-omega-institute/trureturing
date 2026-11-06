/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap
   mirror-E: none(waiver:physical-history-leaf-cap)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Tagged singleton caps and leaf strips construct actual native main and separate core lists on unchanged labelled grounds. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
import D5.S3.Geometry.OriginalLabelTwoSum.Cone
import D5.S3.Geometry.FiniteVertexDominationCollapse

/-! SOURCE_ONLY_UNCOMPILED. D4 and the common padding argument of D6 are
implemented using the selected native Sequence, liftFibre, emitPair and cone
owners. A factor certificate is a legitimate local induction input here; no
universal history theorem with desired corner suppliers as hypotheses is
asserted. This file does not finish D8--D14.

Both lists are actual native sequences. The `separate` sequence starts at the
computed core, with every critical TOP absent; it never starts at the main
endpoint. The declared outer ground W may contain additional ghost labels.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
open OriginalLabelTwoSum HistoryCorners
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two degenerate tags carry literal augmented-family identities and no
fictional coordinate point. The strong branch uses the existing native type. -/
inductive Output (W : Finset V) (K : Family V) : Type _
  | void (eq_void : K = ⊥)
  | unit (eq_unit : K = delta ∅)
  | strong (certificate : Certificate W K)

/-- Data extracted from an output, without conflating either tag with an
ordinary critical face. In particular UNIT does not have an empty critical. -/
inductive CriticalState (V : Type*) : Type _
  | void
  | unit
  | strong (tops : Finset (Finset V))

/-- The actual tag and critical family of the constructed output. -/
def Output.criticalState {W : Finset V} {K : Family V} : Output W K → CriticalState V
  | .void _ => .void
  | .unit _ => .unit
  | .strong c => .strong c.critical

/-- Equality transport keeps every list and coordinate unchanged. -/
def changeOutput {W : Finset V} {K L : Family V}
    (o : Output W K) (h : K = L) : Output W L := by
  subst L
  exact o

@[simp] theorem changeOutput_criticalState {W : Finset V} {K L : Family V}
    (o : Output W K) (h : K = L) :
    (changeOutput o h).criticalState = o.criticalState := by
  subst L
  rfl

private def changeCertificate {W : Finset V} {K L : Family V}
    (c : Certificate W K) (h : K = L) : Certificate W L where
  supported := h ▸ c.supported
  core := c.core
  critical := c.critical
  vertex := c.vertex
  vertex_mem := c.vertex_mem
  core_supported := c.core_supported
  critical_supported := c.critical_supported
  cells := c.cells
  main := c.main.cast (congrArg project h) rfl
  separate := c.separate

/-- The main list is empty; the independent C-only list is the actual cone
list. These face hypotheses construct a certificate without a collapse input. -/
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

private theorem subset_right_of_disjoint {d U x t q : Finset V}
    (hd : Disjoint d U) (hx : x ⊆ d) (hq : q ⊆ U) (h : q ⊆ x ∪ t) : q ⊆ t := by
  intro v hv
  rcases Finset.mem_union.mp (h hv) with hxi | hti
  · exact False.elim (Finset.disjoint_left.mp hd (hx hxi) (hq hv))
  · exact hti

private theorem split_union {d U s : Finset V} (hs : s ⊆ d ∪ U) :
    s = (s ∩ d) ∪ (s ∩ U) := by
  ext v
  simp only [Finset.mem_union, Finset.mem_inter]
  exact ⟨fun hv => (Finset.mem_union.mp (hs hv)).elim
    (fun h => Or.inl ⟨hv, h⟩) (fun h => Or.inr ⟨hv, h⟩), by tauto⟩

private theorem union_cancel_right {d U q t : Finset V} (hd : Disjoint d U)
    (hq : q ⊆ U) (h : d ∪ q ⊆ d ∪ t) : q ⊆ t :=
  subset_right_of_disjoint hd le_rfl hq (Finset.subset_union_right.trans h)

private theorem interval_pair {d s : Finset V} {p : V}
    (hl : d ⊆ s) (hu : s ⊆ insert p d) : s = d ∨ s = insert p d := by
  by_cases hp : p ∈ s
  · exact Or.inr (Finset.Subset.antisymm hu (Finset.insert_subset hp hl))
  · left
    apply Finset.Subset.antisymm _ hl
    intro v hv
    exact (Finset.mem_insert.mp (hu hv)).resolve_left (fun he => hp (he ▸ hv))

/-- The common padding constructor. B contains the entire pad boundary over
U, contains no complete pad, and is a genuine cone. These are face conditions,
not desired collapse fields. The factor c supplies the smaller problem's two
actual sequences. W can strictly contain d union U, retaining strip ghosts. -/
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
        obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
        refine Or.inr ⟨s ∩ d, Finset.inter_subset_right, s ∩ q,
          Or.inr ⟨q, hq, Finset.inter_subset_right⟩, ?_⟩
        exact split_union hs
  have hCells : CriticalData C Q := by
    constructor
    · intro q hq
      change q ∈ c.critical.image (fun q => d ∪ q) at hq
      obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
      exact hd.mono Finset.subset_union_left
    · intro q hq hC
      change q ∈ c.critical.image (fun q => d ∪ q) at hq
      obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
      rcases hC with hBq | ⟨a, ha, t, ht, he⟩
      · exact hmissing _ hBq Finset.subset_union_left
      · have hqt : q ⊆ t := subset_right_of_disjoint hdu ha
          (c.critical_supported q hq) (by rw [← he]; exact Finset.subset_union_right)
        exact c.cells.absent q hq (c.core.lower hqt ht)
    · intro q hq s hs
      change q ∈ c.critical.image (fun q => d ∪ q) at hq
      obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
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
      obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
      change t ∈ c.critical.image (fun q => d ∪ q) at ht
      obtain ⟨t, ht, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp ht
      exact congrArg (fun s => d ∪ s) (c.cells.antichain q hq t ht
        (union_cancel_right hdu (c.critical_supported q hq) hqt))
  let T := liftFibre c.core (delta {c.vertex}) B d U hC0 (by simp) c.separate hdu
    c.core_supported (fun z hz t ht => hboundary z hz t (c.core_supported t ht))
    (noBase (delta {c.vertex}))
  let H := B ⊔ rawJoin (delta d) (delta {c.vertex})
  have hUpper : insert c.vertex d ∈ H := Or.inr
    ⟨d, (by change d ⊆ d; exact le_rfl), {c.vertex}, (by change ({c.vertex} : Finset V) ⊆ {c.vertex}; exact le_rfl), by ext v; simp only [Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton]; tauto⟩
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
    rw [R, emitPair_retained]
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
  obtain ⟨q, hq, rfl⟩ := (Finset.mem_image (f := fun q : Finset V => d ∪ q) (s := c.critical)).mp hq
  exact (Finset.union_subset_union le_rfl (c.critical_supported q hq)).trans hW

/-- All three factor tags in the common padding construction. This function
does not pretend that UNIT has a point or that VOID has an empty face. -/
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

/-- Singleton cap, D4, including U empty. On nonempty U the main list is the
prefixed factor main; the C-only list is prefixed core, point-layer pair, cone.
For UNIT the cap vertex is critical; for VOID it contributes no layer. -/
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

/-- The D7 singleton row is consumed on its actual surviving original-index
family. Only the smaller avoiding family is an induction input. -/
def singletonOutput (r : Rows V) (a : V) (ha : a ∈ r.ground)
    (c : r.chords) (hc : r.row c = {a})
    (o : Output (avoiding r a).ground (avoiding r a).root) :
    Output r.ground r.root := by
  have out := capOutput (r.ground.erase a) a (avoiding r a).root (by simp)
    (avoiding r a).root_supported o
  have hg : insert a (r.ground.erase a) = r.ground := Finset.insert_erase ha
  rw [hg] at out
  exact changeOutput out (singleton_cap r a ha c hc).symm

private theorem sequence_empty_target {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hL : ∀ s, s ∈ L → False) : K = L := by
  induction S with
  | refl => rfl
  | step P T ih =>
      have hp : ({P.apex} : Finset V) ∈ P.retained := by
        refine ⟨(P.ambient.isRelLowerSet_faces P.upper_mem).2 (by simp)
          (Finset.singleton_nonempty _), ?_⟩
        intro h
        obtain ⟨v, hv⟩ := P.lower_nonempty
        have he : v = P.apex := Finset.mem_singleton.mp (h hv)
        exact P.apex_notMem (he ▸ hv)
      rw [ih hL] at hp
      exact False.elim (hL _ hp)

/-- Appending an already constructed output after an actual strip. For tags,
raw empty-face preservation is required explicitly: projecting alone would
incorrectly identify VOID and UNIT. -/
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

/-- A declared ghost is retained on the outer ground, without adding a face. -/
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

/-- Exact family for the rows ab together with arbitrary rows on U+b.
The complementary simplex of ab is delta U; the old rows are extended by a.
The input K is the old ROW ROOT, never a collapsed replacement of it. -/
def oneLeafFamily (U : Finset V) (a : V) (K : Family V) : Family V :=
  delta U ⊔ rawJoin (delta {a}) K

private theorem oneLeaf_supported (U : Finset V) (a b : V) (K : Family V)
    (hs : Supported (insert b U) K) :
    Supported (insert a (insert b U)) (oneLeafFamily U a K) := by
  rintro s (hsU | ⟨x, hx, t, ht, rfl⟩)
  · exact hsU.trans ((Finset.subset_insert b U).trans (Finset.subset_insert a _))
  · exact Finset.union_subset (hx.trans (by intro v hv; simp_all only [Finset.mem_insert, Finset.mem_singleton]; tauto)) ((hs t ht).trans (by intro v hv; simp_all only [Finset.mem_insert]; tauto))

private theorem oneLeaf_delete (U : Finset V) (a b : V) (K : Family V)
    (ha : a ∉ insert b U) (hb : b ∉ U) (hs : Supported (insert b U) K) :
    deletion (project (oneLeafFamily U a K)) b =
      project (oneLeafFamily U a (restrict U K)) := by
  ext s
  change ((s.Nonempty ∧ (s ⊆ U ∨ s ∈ rawJoin (delta {a}) K)) ∧ b ∉ s) ↔
    s.Nonempty ∧ (s ⊆ U ∨ s ∈ rawJoin (delta {a}) (restrict U K))
  constructor
  · rintro ⟨⟨hn, h | ⟨x, hx, t, ht, rfl⟩⟩, hbs⟩
    · exact ⟨hn, Or.inl h⟩
    · refine ⟨hn, Or.inr ⟨x, hx, t, ⟨ht, ?_⟩, rfl⟩⟩
      intro v hv
      exact (Finset.mem_insert.mp (hs t ht hv)).resolve_left (fun he =>
        hbs (Finset.mem_union_right _ (he ▸ hv)))
  · rintro ⟨hn, h | ⟨x, hx, t, ⟨ht, htU⟩, rfl⟩⟩
    · exact ⟨⟨hn, Or.inl h⟩, fun hbs => hb (h hbs)⟩
    · refine ⟨⟨hn, Or.inr ⟨x, hx, t, ht, rfl⟩⟩, ?_⟩
      intro hbs
      rcases Finset.mem_union.mp hbs with hbx | hbt
      · have he : b = a := Finset.mem_singleton.mp (hx hbx)
        exact ha (Finset.mem_insert.mpr (Or.inl he.symm))
      · exact hb (htU hbt)

/-- D5's actual b-layer strip, obtained from the selected general dominated
vertex theorem. Its ordinary lowers all contain b; its list is descending in
cardinality, and every CURRENT coface is certified by native Sequence. -/
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

/-- Complete D5 local output. Only the smaller deletion factor is an induction
input. The source strip is followed by the cap main; its core list stays
separate, and b remains on the declared outer ground as a ghost. -/
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

/-- Literal complementary-row family for rows ab,bc and old rows on U+c. -/
def twoLeafFamily (U : Finset V) (a b c : V) (K : Family V) : Family V :=
  (delta (insert c U) ⊔ delta (insert a U)) ⊔ rawJoin (delta {a,b}) K

/-- The exact post-strip family; b stays a ghost in the caller's ground. -/
def twoLeafEnd (U : Finset V) (a c : V) (M : Family V) : Family V :=
  (delta (insert a U) ⊔ delta (insert c U)) ⊔ rawJoin (delta {a,c}) M

private theorem twoLeaf_supported (U : Finset V) (a b c : V) (K : Family V)
    (hs : Supported (insert c U) K) :
    Supported (insert a (insert b (insert c U))) (twoLeafFamily U a b c K) := by
  rintro s ((hs | hs) | ⟨x, hx, t, ht, rfl⟩)
  · exact hs.trans ((Finset.subset_insert b _).trans (Finset.subset_insert a _))
  · exact hs.trans (Finset.insert_subset_insert a
      ((Finset.subset_insert c U).trans (Finset.subset_insert b _)))
  · exact Finset.union_subset (hx.trans (by intro v hv; simp_all only [Finset.mem_insert, Finset.mem_singleton]; tauto)) ((hs t ht).trans (by intro v hv; simp_all only [Finset.mem_insert]; tauto))

private theorem twoLeaf_delete (U : Finset V) (a b c : V) (K : Family V)
    (ha : a ∉ insert b (insert c U)) (hb : b ∉ insert c U)
    (hc : c ∉ U) (hs : Supported (insert c U) K) :
    deletion (project (twoLeafFamily U a b c K)) b =
      project (twoLeafEnd U a c (rawLink U c K)) := by
  have hab : a ≠ b := fun h => ha (Finset.mem_insert.mpr (Or.inl h))
  have hac : a ≠ c := fun h => ha (by simp [h])
  have haU : a ∉ U := fun h => ha (by simp [h])
  have hbU : b ∉ U := fun h => hb (Finset.mem_insert_of_mem h)
  have hbc : b ≠ c := fun h => hb (Finset.mem_insert.mpr (Or.inl h))
  ext s
  constructor
  · rintro ⟨⟨hn, (h | h) | ⟨x, hx, t, ht, he⟩⟩, hbs⟩
    · exact ⟨hn, Or.inl (Or.inr h)⟩
    · exact ⟨hn, Or.inl (Or.inl h)⟩
    · by_cases has : a ∈ s
      · by_cases hcs : c ∈ s
        · have htC : c ∈ t := by
            have hct : c ∈ x ∪ t := he ▸ hcs
            rcases Finset.mem_union.mp hct with hcx | hct
            · have h : c = a ∨ c = b := by simpa using hx hcx
              exact False.elim (h.elim (fun h => hac h.symm) (fun h => hbc h.symm))
            · exact hct
          have hxA : x = {a} := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hvab : v = a ∨ v = b := by simpa using hx hv
              rcases hvab with rfl | rfl
              · simp
              · exact False.elim (hbs (he.symm ▸ Finset.mem_union_left t hv))
            · apply Finset.singleton_subset_iff.mpr
              have hat : a ∈ x ∪ t := he ▸ has
              exact (Finset.mem_union.mp hat).resolve_right (fun hat =>
                ha (Finset.mem_insert_of_mem (hs t ht hat)))
          have htU : t.erase c ⊆ U := by
            intro v hv
            obtain ⟨hvc, hvt⟩ := Finset.mem_erase.mp hv
            exact (Finset.mem_insert.mp (hs t ht hvt)).resolve_left hvc
          refine ⟨hn, Or.inr ⟨{a,c}, (by change ({a,c} : Finset V) ⊆ {a,c}; exact le_rfl), t.erase c,
            ⟨htU, (Finset.insert_erase htC).symm ▸ ht⟩, ?_⟩⟩
          rw [he, hxA]
          ext v
          by_cases hv : v = c <;> simp_all only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_erase]
          <;> tauto
        · refine ⟨hn, Or.inl (Or.inl ?_)⟩
          intro v hv
          have hvt : v ∈ x ∪ t := he ▸ hv
          rcases Finset.mem_union.mp hvt with hvx | hvt
          · have h : v = a ∨ v = b := by simpa using hx hvx
            exact h.elim (fun h => Finset.mem_insert.mpr (Or.inl h))
              (fun h => False.elim (hbs (h ▸ hv)))
          · exact Finset.mem_insert.mpr (Or.inr
              ((Finset.mem_insert.mp (hs t ht hvt)).resolve_left (fun h => hcs (h ▸ hv))))
      · refine ⟨hn, Or.inl (Or.inr ?_)⟩
        intro v hv
        have hvt : v ∈ x ∪ t := he ▸ hv
        rcases Finset.mem_union.mp hvt with hvx | hvt
        · have h : v = a ∨ v = b := by simpa using hx hvx
          exact False.elim (h.elim (fun h => has (h ▸ hv)) (fun h => hbs (h ▸ hv)))
        · exact hs t ht hvt
  · rintro ⟨hn, (h | h) | ⟨x, hx, t, ⟨htU, htK⟩, he⟩⟩
    · exact ⟨⟨hn, Or.inl (Or.inr h)⟩, fun hbs =>
        (Finset.mem_insert.mp (h hbs)).elim (fun h => hab h.symm) hbU⟩
    · exact ⟨⟨hn, Or.inl (Or.inl h)⟩, fun hbs => hb (h hbs)⟩
    · have hbig : insert a (insert c t) ∈ twoLeafFamily U a b c K :=
        Or.inr ⟨{a}, by simp, insert c t, htK, by simp [Finset.insert_comm]⟩
      have hsub : s ⊆ insert a (insert c t) := by
        rw [he]
        exact Finset.union_subset (hx.trans (by intro v hv; simp_all only [Finset.mem_insert, Finset.mem_singleton]; tauto)) (by simp)
      refine ⟨⟨hn, (twoLeafFamily U a b c K).lower hsub hbig⟩, ?_⟩
      intro hbs
      have h : b = a ∨ b = c ∨ b ∈ t := by simpa using hsub hbs
      exact h.elim (fun h => hab h.symm) (fun h => h.elim hbc (fun h => hbU (htU h)))

/-- D6 strip: actual domination list, including the f=empty pair whenever
K contains empty. The lower contains b and hence is an ordinary nonempty face. -/
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

private def twoLeafEndOutput (U : Finset V) (a b c : V) (M : Family V)
    (ha : a ∉ insert b (insert c U)) (hc : c ∉ U)
    (hs : Supported U M) (o : Output U M) :
    Output (insert a (insert b (insert c U))) (twoLeafEnd U a c M) := by
  classical
  let W := insert a (insert b (insert c U))
  let B : Family V := delta (insert a U) ⊔ delta (insert c U)
  have hac : a ≠ c := fun h => ha (by simp [h])
  have haU : a ∉ U := fun h => ha (by simp [h])
  by_cases hU : U.Nonempty
  · let x := hU.choose
    have hx : x ∈ U := hU.choose_spec
    have hd : Disjoint ({a,c} : Finset V) U := by
      apply Finset.disjoint_left.mpr
      intro v hv hU
      have h : v = a ∨ v = c := by simpa using hv
      exact h.elim (fun h => haU (h ▸ hU)) (fun h => hc (h ▸ hU))
    have hB : Supported W B := by
      intro s h
      exact h.elim (fun h => h.trans (Finset.insert_subset_insert a
        ((Finset.subset_insert c U).trans (Finset.subset_insert b _))))
        (fun h => h.trans ((Finset.subset_insert b _).trans (Finset.subset_insert a _)))
    have hmissing : ∀ s ∈ B, ¬ ({a,c} : Finset V) ⊆ s := by
      intro s h hsub
      rcases h with h | h
      · have hcs := h (hsub (by simp : c ∈ ({a,c} : Finset V)))
        exact (Finset.mem_insert.mp hcs).elim (fun h => hac h.symm) hc
      · have has := h (hsub (by simp : a ∈ ({a,c} : Finset V)))
        exact (Finset.mem_insert.mp has).elim hac haU
    have hbound : ∀ z ⊂ ({a,c} : Finset V), ∀ t ⊆ U, z ∪ t ∈ B := by
      intro z hz t ht
      by_cases haz : a ∈ z
      · left
        have hcz : c ∉ z := by
          intro hcz
          exact hz.ne (Finset.Subset.antisymm hz.subset (by intro v hv; have hv' : v = a ∨ v = c := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hv; exact hv'.elim (fun h => h ▸ haz) (fun h => h ▸ hcz)))
        apply Finset.union_subset _ (ht.trans (Finset.subset_insert _ _))
        intro v hv
        have h : v = a ∨ v = c := by simpa using hz.subset hv
        exact h.elim (fun h => Finset.mem_insert.mpr (Or.inl h))
          (fun h => False.elim (hcz (h ▸ hv)))
      · right
        apply Finset.union_subset _ (ht.trans (Finset.subset_insert _ _))
        intro v hv
        have h : v = a ∨ v = c := by simpa using hz.subset hv
        exact h.elim (fun h => False.elim (haz (h ▸ hv)))
          (fun h => Finset.mem_insert.mpr (Or.inl h))
    exact paddedOutput W U {a,c} B M o x (by simp) hd (by simp [W]) hB
      (Or.inl (by simpa using Finset.mem_insert_of_mem hx)) (by
        intro s h
        exact h.elim (fun h => Or.inl (Finset.insert_subset (by simp [hx]) h))
          (fun h => Or.inr (Finset.insert_subset (by simp [hx]) h))) hmissing hbound
  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    by_cases h0 : (∅ : Finset V) ∈ M
    · have hM : M = delta ∅ := by
        apply SetLike.ext; intro s
        exact ⟨hs s, fun h => M.lower h h0⟩
      have he : twoLeafEnd ∅ a c M = delta {a,c} := by
        rw [twoLeafEnd, hM, (rawJoin_unit _).2]
        apply sup_eq_right.mpr
        intro s h
        exact h.elim (fun h => h.trans (by intro v hv; simp_all))
          (fun h => h.trans (by intro v hv; simp_all))
      exact .strong (changeCertificate (coneCertificate W (delta {a,c}) a
        (fun _ h => h.trans (by simp [W])) (by simp)
        (fun s h => Finset.insert_subset (by simp) h)) he.symm)
    · have hM : M = ⊥ := by
        apply SetLike.ext; intro s
        exact ⟨fun h => False.elim (h0 (M.lower (Finset.empty_subset _) h)),
          fun h => False.elim h⟩
      let small := capOutput {a} c (delta ∅) (by simpa using hac.symm)
        (fun s h => h.trans (Finset.empty_subset _)) (.unit rfl)
      have he : delta {a} ⊔ rawJoin (delta {c}) (delta ∅) = twoLeafEnd ∅ a c M := by
        rw [(rawJoin_unit _).2, twoLeafEnd, hM, (rawJoin_void _).2, sup_bot_eq]
        rfl
      exact changeOutput (widenOutput (by intro v hv; simp_all [W]) small) he

/-- Complete D6 local output from the smaller LINK factor. In particular the
required factor is rawLink U c K, not a deletion. The empty-U alternatives are
two actual isolated points or an actual edge; neither is mislabeled UNIT. -/
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

/-- The critical transform computed by padding. The two exceptional tags
remain distinct inputs; the resulting ordinary tops are never supplied. -/
def padCriticalState (d : Finset V) : CriticalState V → CriticalState V
  | .void => .strong ∅
  | .unit => .strong {d}
  | .strong D => .strong (D.image (fun q => d ∪ q))

@[simp] theorem widenOutput_criticalState {W W' : Finset V} {K : Family V}
    (h : W ⊆ W') (o : Output W K) :
    (widenOutput h o).criticalState = o.criticalState := by
  cases o <;> rfl

@[simp] theorem prependOutput_criticalState (W : Finset V) (K L : Family V)
    (hs : Supported W K) (h0 : (∅ : Finset V) ∈ K ↔ ∅ ∈ L)
    (S : Sequence (project K) (project L)) (o : Output W L) :
    (prependOutput W K L hs h0 S o).criticalState = o.criticalState := by
  cases o with
  | void h => subst L; rfl
  | unit h => subst L; rfl
  | strong c => rfl

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
      simp only [paddedOutput, changeOutput_criticalState, Output.criticalState,
        padCriticalState, coneCertificate]
  | unit h =>
      subst M
      simp only [paddedOutput, changeOutput_criticalState, Output.criticalState,
        padCriticalState]
  | strong c => rfl

/-- Read back the actual D6 construction on nonempty smaller ground. -/
theorem twoLeafOutput_criticalState (U : Finset V) (a b c : V) (K : Family V)
    (ha : a ∉ insert b (insert c U)) (hb : b ∉ insert c U)
    (hc : c ∉ U) (hs : Supported (insert c U) K)
    (o : Output U (rawLink U c K)) (hU : U.Nonempty) :
    (twoLeafOutput U a b c K ha hb hc hs o).criticalState =
      padCriticalState {a,c} o.criticalState := by
  simp only [twoLeafOutput, prependOutput_criticalState]
  simp only [twoLeafEndOutput, dif_pos hU, if_pos hU, paddedOutput_criticalState]

/-- The zero-ground D6 branch is determined by actual empty-face membership.
It returns two isolated points or an edge, with critical c or no critical. -/
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
  · simp [twoLeafEndOutput, h0, capOutput, Finset.singleton_nonempty,
      paddedOutput_criticalState, padCriticalState, Output.criticalState]

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
