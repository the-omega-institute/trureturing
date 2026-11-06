/-
  SOURCE ATTEMPT — UNCOMPILED.

  Released ordinary finite incidence certificate for the restricted
  bipartite-distance-hereditary (pendant/twin-pruning) class.  This file is
  deliberately an implementation owner: its input certificate contains only
  incidence/pruning hypotheses.  The collapse sequence, retained frames,
  critical face, core and all coordinate maps are constructed below.

  No kernel, axiom, Scribe, Reg, admission, gate, repository or publication
  result is claimed by this source-only artifact.
-/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import D5.S3.Geometry.FiniteVertexDominationCollapse
import D5.S3.Geometry.FiniteAlexanderDualCollapse

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteIncidenceRootCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse
open FiniteVertexDominationCollapse
open FiniteAlexanderDualCollapse
open FiniteComponentClosure (vertexComplex)

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Literal incidence presentations and their original ground -/

structure State (ρ : I → J → Prop) where
  active : Finset I
  rows : Finset J

def rowNeighborhood (ρ : I → J → Prop) (q : State ρ) (b : J) : Finset I := by
  classical
  exact q.active.filter (fun x => ρ x b)

@[simp] theorem mem_rowNeighborhood (ρ : I → J → Prop) (q : State ρ)
    (x : I) (b : J) :
    x ∈ rowNeighborhood ρ q b ↔ x ∈ q.active ∧ ρ x b := by
  classical
  simp [rowNeighborhood]

private theorem mem_rowComplement (ρ : I → J → Prop) (q : State ρ)
    (x : I) (b : J) :
    x ∈ q.active \ rowNeighborhood ρ q b ↔ x ∈ q.active ∧ ¬ ρ x b := by
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxA, hxN⟩
    exact ⟨hxA, fun hρ => hxN ((mem_rowNeighborhood ρ q x b).mpr ⟨hxA, hρ⟩)⟩
  · rintro ⟨hxA, hxρ⟩
    exact Finset.mem_sdiff.mpr ⟨hxA, fun hxN => hxρ
      ((mem_rowNeighborhood ρ q x b).mp hxN).2⟩

def incidenceSimplex (lambda : Finset I) : PreAbstractSimplicialComplex I :=
  FiniteAlexanderDualCollapse.simplex lambda

/-- The literal root K on the ORIGINAL type `I`.  `q.active` is a local
    ground; a label outside it remains a genuine ghost of this face family. -/
def rootK (ρ : I → J → Prop) (q : State ρ) : PreAbstractSimplicialComplex I where
  faces := {s | s.Nonempty ∧ ∃ b ∈ q.rows, s ⊆ q.active \ rowNeighborhood ρ q b}
  isRelLowerSet_faces := by
    rintro s ⟨hs, b, hb, hsb⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, b, hb, fun x hx => hsb (hts hx)⟩

@[simp] theorem mem_rootK (ρ : I → J → Prop) (q : State ρ) (s : Finset I) :
    s ∈ rootK ρ q ↔
      s.Nonempty ∧ ∃ b ∈ q.rows, s ⊆ q.active \ rowNeighborhood ρ q b := Iff.rfl

def incidenceDual (ρ : I → J → Prop) (q : State ρ) :
    PreAbstractSimplicialComplex I where
  faces := {s | s.Nonempty ∧ s ⊂ q.active ∧ ∀ b ∈ q.rows,
    ¬ rowNeighborhood ρ q b ⊆ s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hproper, hrows⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    refine ⟨ht, Finset.ssubset_iff_subset_ne.mpr ⟨hts.trans hproper.subset, ?_⟩, ?_⟩
    · intro he
      exact hproper.not_ge (he ▸ hts)
    intro b hb hsub
    exact hrows b hb (hsub.trans hts)

theorem rootK_dual (ρ : I → J → Prop) (q : State ρ) :
    FiniteAlexanderDualCollapse.dual q.active (rootK ρ q) = incidenceDual ρ q := by
  classical
  have havoid : ∀ {s : Finset I},
      s ⊂ q.active →
      (∀ b ∈ q.rows, ¬ rowNeighborhood ρ q b ⊆ s) →
        ¬ AugmentedFace (rootK ρ q) (q.active \ s) := by
    intro s hproper hrows haug
    rcases haug with he | ⟨hne, b, hb, hsub⟩
    · have hact : q.active ⊆ s := by
        intro x hx
        by_contra hxs
        exact (Finset.notMem_empty x (by simpa [he] using
          (Finset.mem_sdiff.mpr ⟨hx, hxs⟩)))
      exact hproper.ne (Finset.Subset.antisymm hproper.subset hact)
    · apply hrows b hb
      intro x hx
      by_contra hxs
      have hxA : x ∈ q.active :=
        ((mem_rowNeighborhood ρ q x b).mp hx).1
      have hxcomp : x ∈ q.active \ s := Finset.mem_sdiff.mpr ⟨hxA, hxs⟩
      exact (Finset.mem_sdiff.mp (hsub hxcomp)).2 hx
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, hsA, hnot⟩
    refine ⟨hs, ?_, ?_⟩
    · exact Finset.ssubset_iff_subset_ne.mpr ⟨hsA, by
        intro he
        exact hnot (Or.inl (by simpa [he]))
      ⟩
    · intro b hb hsub
      apply hnot
      by_cases hempty : q.active \ s = ∅
      · exact Or.inl hempty
      · right
        refine ⟨Finset.nonempty_iff_ne_empty.mpr hempty, b, hb, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, by
          intro hxs
          exact (Finset.mem_sdiff.mp hx).2 (hsub hxs)⟩
  · rintro ⟨hs, hproper, hrows⟩
    exact ⟨hs, hproper.subset, havoid hproper hrows⟩

/- The dual proof is a fixed-ground bridge; it does not alter any active label
   or reintroduce an augmented empty face as an ordinary realization point. -/

def eraseRow (ρ : I → J → Prop) (q : State ρ) (c : J) : State ρ :=
  { q with rows := q.rows.erase c }

def eraseColumn (ρ : I → J → Prop) (q : State ρ) (y : I) : State ρ :=
  { q with active := q.active.erase y }

def singletonChild (ρ : I → J → Prop) (q : State ρ) (a : I) : State ρ := by
  classical
  exact { active := q.active.erase a
          rows := q.rows.filter (fun b => ¬ ρ a b) }

@[simp] theorem eraseRow_active (ρ : I → J → Prop) (q : State ρ) (c : J) :
    (eraseRow ρ q c).active = q.active := rfl

@[simp] theorem eraseColumn_rows (ρ : I → J → Prop) (q : State ρ) (y : I) :
    (eraseColumn ρ q y).rows = q.rows := rfl

def RowSubset (ρ : I → J → Prop) (q : State ρ) (b c : J) : Prop :=
  ∀ x ∈ q.active, ρ x b → ρ x c

def ColumnSubset (ρ : I → J → Prop) (q : State ρ) (x y : I) : Prop :=
  ∀ b ∈ q.rows, ρ x b → ρ y b

def IsolatedColumn (ρ : I → J → Prop) (q : State ρ) (x : I) : Prop :=
  ∀ b ∈ q.rows, ¬ ρ x b

def SingletonRow (ρ : I → J → Prop) (q : State ρ) (b : J) (a : I) : Prop :=
  b ∈ q.rows ∧ rowNeighborhood ρ q b = {a}

theorem rowSubset_neighborhood (ρ : I → J → Prop) (q : State ρ)
    {b c : J} (h : RowSubset ρ q b c) :
    rowNeighborhood ρ q b ⊆ rowNeighborhood ρ q c := by
  intro x hx
  rcases (mem_rowNeighborhood ρ q x b).mp hx with ⟨hxa, hxb⟩
  exact (mem_rowNeighborhood ρ q x c).mpr ⟨hxa, h x hxa hxb⟩

theorem columnSubset_neighborhood (ρ : I → J → Prop) (q : State ρ)
    {x y : I} (hy : y ∈ q.active) (h : ColumnSubset ρ q x y) :
    ∀ b ∈ q.rows, x ∈ rowNeighborhood ρ q b → y ∈ rowNeighborhood ρ q b := by
  intro b hb hx
  rcases (mem_rowNeighborhood ρ q x b).mp hx with ⟨hxa, hxb⟩
  exact (mem_rowNeighborhood ρ q y b).mpr ⟨hy, h b hb hxb⟩

theorem rootK_empty_rows (ρ : I → J → Prop) (q : State ρ) (h : q.rows = ∅) :
    rootK ρ q = ⊥ := by
  apply SetLike.coe_injective
  ext s
  simp [rootK, h]

theorem rootK_full_rows (ρ : I → J → Prop) (q : State ρ)
    (hn : q.rows.Nonempty)
    (hfull : ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active) :
    rootK ρ q = ⊥ := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, b, hb, hsub⟩
    have hse : s ⊆ (∅ : Finset I) := by simpa [hfull b hb] using hsub
    exact (hs.ne_empty (Finset.subset_empty.mp hse)).elim
  · simp

theorem rootK_empty_row (ρ : I → J → Prop) (q : State ρ) {b : J}
    (hb : b ∈ q.rows) (hempty : rowNeighborhood ρ q b = ∅) :
    rootK ρ q = incidenceSimplex q.active := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, _, _, hsub⟩
    exact ⟨hs, hsub.trans Finset.sdiff_subset⟩
  · rintro ⟨hs, hsub⟩
    exact ⟨hs, b, hb, by simpa [hempty] using hsub⟩

theorem rootK_row_erase (ρ : I → J → Prop) (q : State ρ)
    {b c : J} (hb : b ∈ q.rows) (hc : c ∈ q.rows) (hbc : b ≠ c)
    (hsub : RowSubset ρ q b c) :
    rootK ρ q = rootK ρ (eraseRow ρ q c) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, d, hd, hsd⟩
    by_cases hdc : d = c
    · subst d
      refine ⟨hs, b, Finset.mem_erase.mpr ⟨hbc, hb⟩, ?_⟩
      intro x hx
      rcases (mem_rowComplement ρ q x c).mp (hsd hx) with ⟨hxA, hxc⟩
      exact (mem_rowComplement ρ (eraseRow ρ q c) x b).mpr
        ⟨hxA, fun hxb => hxc (hsub x hxA hxb)⟩
    · exact ⟨hs, d, Finset.mem_erase.mpr ⟨hdc, hd⟩, hsd⟩
  · rintro ⟨hs, d, hd, hsd⟩
    exact ⟨hs, d, (Finset.mem_erase.mp hd).2, hsd⟩

theorem rootK_column_delete (ρ : I → J → Prop) (q : State ρ)
    {x y : I} (hy : y ∈ q.active) (hxy : x ≠ y)
    (hsub : ColumnSubset ρ q x y) :
    deletion (rootK ρ q) y = rootK ρ (eraseColumn ρ q y) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨⟨hs, b, hb, hsb⟩, hys⟩
    refine ⟨hs, b, hb, ?_⟩
    intro z hz
    rcases (mem_rowComplement ρ q z b).mp (hsb hz) with ⟨hzA, hzρ⟩
    exact (mem_rowComplement ρ (eraseColumn ρ q y) z b).mpr
      ⟨Finset.mem_erase.mpr ⟨fun hzy => hys (hzy ▸ hz), hzA⟩, hzρ⟩
  · rintro ⟨hs, b, hb, hsb⟩
    refine ⟨⟨hs, b, hb, ?_⟩, ?_⟩
    · intro z hz
      rcases (mem_rowComplement ρ (eraseColumn ρ q y) z b).mp (hsb hz) with
        ⟨hzA, hzρ⟩
      exact (mem_rowComplement ρ q z b).mpr ⟨Finset.mem_of_mem_erase hzA, hzρ⟩
    · intro hys
      have hyA := ((mem_rowComplement ρ (eraseColumn ρ q y) y b).mp (hsb hys)).1
      exact (Finset.mem_erase.mp hyA).1 rfl

theorem rootK_isolated_cone (ρ : I → J → Prop) (q : State ρ)
    {x : I} (hx : x ∈ q.active) (hrows : q.rows.Nonempty)
    (hiso : IsolatedColumn ρ q x) :
    rootK ρ q = cone x (rootK ρ (eraseColumn ρ q x)) := by
  classical
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, b, hb, hsb⟩
    refine ⟨hs, ?_⟩
    by_cases he : s.erase x = ∅
    · exact Or.inl he
    · right
      refine ⟨Finset.nonempty_iff_ne_empty.mpr he, b, hb, ?_⟩
      intro z hz
      rcases (mem_rowComplement ρ q z b).mp
        (hsb (Finset.mem_of_mem_erase hz)) with ⟨hzA, hzρ⟩
      exact (mem_rowComplement ρ (eraseColumn ρ q x) z b).mpr
        ⟨Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, hzA⟩, hzρ⟩
  · rintro ⟨hs, he | ⟨ht, b, hb, htb⟩⟩
    · obtain ⟨b, hb⟩ := hrows
      refine ⟨hs, b, hb, ?_⟩
      intro z hz
      have hzx : z = x := by
        by_contra hne
        have hzE : z ∈ s.erase x := Finset.mem_erase.mpr ⟨hne, hz⟩
        rw [he] at hzE
        exact Finset.notMem_empty z hzE
      subst z
      exact (mem_rowComplement ρ q x b).mpr ⟨hx, hiso b hb⟩
    · refine ⟨hs, b, hb, ?_⟩
      intro z hz
      by_cases hzx : z = x
      · subst z
        exact (mem_rowComplement ρ q x b).mpr ⟨hx, hiso b hb⟩
      · rcases (mem_rowComplement ρ (eraseColumn ρ q x) z b).mp
          (htb (Finset.mem_erase.mpr ⟨hzx, hz⟩)) with ⟨hzA, hzρ⟩
        exact (mem_rowComplement ρ q z b).mpr ⟨Finset.mem_of_mem_erase hzA, hzρ⟩

/-! ### Structural input certificate.  It contains no collapse/core field. -/

inductive Pruning (ρ : I → J → Prop) : State ρ → Type
  | void (q : State ρ) (hrows : q.rows = ∅) : Pruning ρ q
  | unit (q : State ρ) (hrows : q.rows.Nonempty)
      (hfull : ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active) : Pruning ρ q
  | emptyRow (q : State ρ) (b : J) (hb : b ∈ q.rows)
      (hempty : rowNeighborhood ρ q b = ∅) : Pruning ρ q
  | isolatedColumn (q : State ρ) (x : I) (hx : x ∈ q.active)
      (hrows : q.rows.Nonempty) (hiso : IsolatedColumn ρ q x) : Pruning ρ q
  | redundantRow (q : State ρ) (b c : J) (hb : b ∈ q.rows) (hc : c ∈ q.rows)
      (hbc : b ≠ c) (hsub : RowSubset ρ q b c)
      (child : Pruning ρ (eraseRow ρ q c)) : Pruning ρ q
  | dominatedColumn (q : State ρ) (x y : I) (hx : x ∈ q.active)
      (hy : y ∈ q.active) (hxy : x ≠ y) (hsub : ColumnSubset ρ q x y)
      (child : Pruning ρ (eraseColumn ρ q y)) : Pruning ρ q
  | singletonRow (q : State ρ) (b : J) (a : I)
      (hsingle : SingletonRow ρ q b a)
      (child : Pruning ρ (singletonChild ρ q a)) : Pruning ρ q

/-! ### Ordinary output and exact local specifications -/

inductive TerminalTag where
  | void
  | unit
deriving DecidableEq

def TerminalLaw (ρ : I → J → Prop) (q : State ρ) (tag : TerminalTag) : Prop :=
  match tag with
  | .void => q.rows = ∅
  | .unit => q.rows.Nonempty ∧
      ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active

structure Witness (ρ : I → J → Prop) (q : State ρ) where
  endpoint : PreAbstractSimplicialComplex I
  sequence : Sequence (rootK ρ q) endpoint
  core : PreAbstractSimplicialComplex I
  pivot : I
  pivot_mem : pivot ∈ q.active
  core_sequence : Sequence core (vertexComplex pivot)
  critical : Option (Finset I)
  endpoint_eq_core : critical = none → endpoint = core
  endpoint_eq_attach : ∀ σ, critical = some σ → endpoint = core ⊔ incidenceSimplex σ
  critical_nonempty : ∀ σ, critical = some σ → σ.Nonempty
  critical_outside : ∀ σ, critical = some σ → σ ∉ core
  critical_boundary : ∀ σ, critical = some σ → ∀ t, t ⊂ σ → t = ∅ ∨ t ∈ core

inductive Result (ρ : I → J → Prop) (q : State ρ) where
  | terminal (tag : TerminalTag) (hK : rootK ρ q = ⊥)
      (hLaw : TerminalLaw ρ q tag) : Result ρ q
  | regular (w : Witness ρ q) : Result ρ q

def augmentedTerminal (ρ : I → J → Prop) (q : State ρ) (tag : TerminalTag)
    (s : Finset I) : Prop :=
  match tag with
  | .void => s ∈ rootK ρ q
  | .unit => s = ∅ ∨ s ∈ rootK ρ q

theorem terminal_semantics (ρ : I → J → Prop) {q : State ρ}
    (tag : TerminalTag) (hK : rootK ρ q = ⊥) (s : Finset I) :
    augmentedTerminal ρ q tag s ↔
      match tag with | .void => False | .unit => s = ∅ := by
  cases tag <;> simp [augmentedTerminal, hK]

/-! Full simplex and cone constructors.  They use the native domination
    sequence, so every pair is a real `CollapsePair` on the original type. -/

private theorem simplex_singleton (p : I) :
    incidenceSimplex ({p} : Finset I) = vertexComplex p := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, hsub⟩
    change s = {p}
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hs, fun x hx => Finset.mem_singleton.mp (hsub hx)⟩
  · intro hs
    change s = {p} at hs
    subst s
    exact ⟨Finset.singleton_nonempty _, le_rfl⟩

private theorem simplex_empty : incidenceSimplex (∅ : Finset I) = ⊥ := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, hsub⟩
    exact (hs.ne_empty (Finset.subset_empty.mp hsub)).elim
  · simp

private theorem cone_bot_simplex (a : I) :
    cone a (⊥ : PreAbstractSimplicialComplex I) = incidenceSimplex ({a} : Finset I) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, he | he⟩
    · refine ⟨hs, ?_⟩
      intro x hx
      have hxa : x = a := by
        by_contra hne
        have hxE : x ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hx⟩
        rw [he] at hxE
        exact Finset.notMem_empty x hxE
      exact Finset.mem_singleton.mpr hxa
    · exact (show False from he).elim
  · rintro ⟨hs, hsub⟩
    refine ⟨hs, Or.inl ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_erase.mp hx).1
      (Finset.mem_singleton.mp (hsub (Finset.mem_of_mem_erase hx)))

private theorem simplex_extends (A : Finset I) {p y : I}
    (hp : p ∈ A) (hy : y ∈ A) (hpy : p ≠ y) :
    Extends (incidenceSimplex A) p y := by
  intro s hs hyS
  exact ⟨Finset.insert_nonempty _ _, Finset.insert_subset_iff.mpr ⟨hp, hs.2⟩⟩

private theorem simplex_delete (A : Finset I) {y : I} (hy : y ∈ A) :
    deletion (incidenceSimplex A) y = incidenceSimplex (A.erase y) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨⟨hs, hsA⟩, hys⟩
    exact ⟨hs, fun z hz => Finset.mem_erase.mpr
      ⟨fun hzy => hys (hzy ▸ hz), hsA hz⟩⟩
  · rintro ⟨hs, hsA⟩
    exact ⟨⟨hs, fun z hz => Finset.mem_of_mem_erase (hsA hz)⟩,
      fun hys => (Finset.mem_erase.mp (hsA hys)).1 rfl⟩

def simplexCollapse : ∀ (A : Finset I) (p : I), p ∈ A →
    Sequence (incidenceSimplex A) (vertexComplex p)
  | A, p, hp => by
      classical
      by_cases hrest : (A.erase p).Nonempty
      · obtain ⟨y, hy⟩ := hrest
        have hpy : p ≠ y := by
          intro h; exact (Finset.mem_erase.mp hy).1 h.symm
        let S := sequence (incidenceSimplex A) p y hpy
          (simplex_extends A hp (Finset.mem_of_mem_erase hy) hpy)
        let T := simplexCollapse (A.erase y) p
          (Finset.mem_erase.mpr ⟨hpy, hp⟩)
        exact S.append (T.cast (simplex_delete A (Finset.mem_of_mem_erase hy)).symm rfl)
      · have hA : A = {p} := by
          apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
          exact ⟨⟨p, hp⟩, fun x hx => by
            by_contra hxp
            exact hrest ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩⟩⟩
        have hK : incidenceSimplex A = vertexComplex p := by
          rw [hA]
          exact simplex_singleton p
        exact (Sequence.refl (incidenceSimplex A)).cast rfl hK
termination_by A.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (Finset.mem_of_mem_erase hy)

private theorem isolated_extends (ρ : I → J → Prop) (q : State ρ)
    {x y : I} (hx : x ∈ q.active) (hy : y ∈ q.active) (hxy : x ≠ y)
    (hrows : q.rows.Nonempty) (hiso : IsolatedColumn ρ q x) :
    Extends (rootK ρ q) x y := by
  rintro s ⟨hs, b, hb, hsb⟩ hyS
  refine ⟨Finset.insert_nonempty _ _, b, hb, ?_⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact (mem_rowComplement ρ q x b).mpr ⟨hx, hiso b hb⟩
  · exact hsb hz

def isolatedCollapse : ∀ (ρ : I → J → Prop) (q : State ρ) (x : I),
    x ∈ q.active → q.rows.Nonempty → IsolatedColumn ρ q x →
    Sequence (rootK ρ q) (vertexComplex x)
  | ρ, q, x, hx, hrows, hiso => by
      classical
      by_cases hrest : (q.active.erase x).Nonempty
      · obtain ⟨y, hy⟩ := hrest
        have hxy : x ≠ y := by
          intro h; exact (Finset.mem_erase.mp hy).1 h.symm
        let S := sequence (rootK ρ q) x y hxy
          (isolated_extends ρ q hx (Finset.mem_of_mem_erase hy) hxy hrows hiso)
        let T := isolatedCollapse ρ (eraseColumn ρ q y) x
          (Finset.mem_erase.mpr ⟨hxy, hx⟩) hrows (by
            intro b hb hxb
            exact hiso b hb hxb)
        exact S.append (T.cast (rootK_column_delete ρ q
          (Finset.mem_of_mem_erase hy) hxy
          (fun b hb hxb => (hiso b hb hxb).elim)).symm rfl)
      · have hq : q.active = {x} := by
          apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
          exact ⟨⟨x, hx⟩, fun y hy => by
            by_contra hyx
            exact hrest ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩⟩
        have hK : rootK ρ q = vertexComplex x := by
          apply SetLike.coe_injective
          ext s
          constructor
          · rintro ⟨hs, b, hb, hsb⟩
            change s = {x}
            apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
            refine ⟨hs, ?_⟩
            intro z hz
            have hzA := ((mem_rowComplement ρ q z b).mp (hsb hz)).1
            rw [hq] at hzA
            exact Finset.mem_singleton.mp hzA
          · intro hs
            change s = {x} at hs
            subst s
            obtain ⟨b, hb⟩ := hrows
            refine ⟨Finset.singleton_nonempty _, b, hb, ?_⟩
            intro z hz
            have hzx := Finset.mem_singleton.mp hz
            subst z
            exact (mem_rowComplement ρ q x b).mpr ⟨hx, hiso b hb⟩
        exact (Sequence.refl (rootK ρ q)).cast rfl hK
termination_by q.active.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (Finset.mem_of_mem_erase hy)

private theorem rootK_le_full (ρ : I → J → Prop) (q : State ρ) :
    rootK ρ q ≤ incidenceSimplex q.active := by
  rintro s ⟨hs, b, hb, hsb⟩
  exact ⟨hs, hsb.trans Finset.sdiff_subset⟩

private theorem fresh_of_active_erase (A : Finset I) (a : I) :
    Fresh a (incidenceSimplex (A.erase a)) := by
  intro s hs ha
  exact (Finset.mem_erase.mp (hs.2 ha)).1 rfl

/- A child core is lifted over the whole base; its terminal pair is used only
   in this separate core sequence, never across the retained critical simplex. -/
def liftCoreToBase (A : Finset I) (C : PreAbstractSimplicialComplex I)
    (a p : I) (hCD : C ≤ incidenceSimplex A)
    (haD : Fresh a (incidenceSimplex A))
    (S : Sequence C (vertexComplex p))
    (hpA : p ∈ A) (hap : a ≠ p) :
    Sequence (incidenceSimplex A ⊔ cone a C) (vertexComplex p) := by
  let D := incidenceSimplex A
  let L := S.liftOver D a hCD haD
  have hpd : ({p} : Finset I) ∈ D :=
    ⟨Finset.singleton_nonempty p, Finset.singleton_subset_iff.mpr hpA⟩
  let Q := terminalPair D a p haD hap hpd
  let T : Sequence Q.ambient D :=
    (Sequence.step Q (Sequence.refl Q.retained)).cast rfl
      (terminalPair_retained D a p haD hap hpd)
  exact (L.append T).append (simplexCollapse A p hpA)

/-! Singleton-row exact decomposition. -/
private theorem singleton_active (ρ : I → J → Prop) (q : State ρ)
    {b : J} {a : I} (hsingle : SingletonRow ρ q b a) : a ∈ q.active := by
  apply ((mem_rowNeighborhood ρ q a b).mp ?_).1
  rw [hsingle.2]
  exact Finset.mem_singleton_self _

private theorem singleton_base_le (ρ : I → J → Prop) (q : State ρ)
    {b : J} {a : I} (hsingle : SingletonRow ρ q b a) :
    incidenceSimplex (q.active.erase a) ≤ rootK ρ q := by
  rintro s ⟨hs, hsU⟩
  refine ⟨hs, b, hsingle.1, ?_⟩
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase (hsU hx), ?_⟩
  intro hxN
  rw [hsingle.2] at hxN
  exact (Finset.mem_erase.mp (hsU hx)).1 (Finset.mem_singleton.mp hxN)

theorem singleton_decomposition (ρ : I → J → Prop) (q : State ρ)
    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)
    (hapex : ({a} : Finset I) ∈ rootK ρ q) :
    rootK ρ q = incidenceSimplex (q.active.erase a) ⊔
      cone a (rootK ρ (singletonChild ρ q a)) := by
  classical
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, c, hc, hsc⟩
    by_cases ha : a ∈ s
    · refine Or.inr ⟨hs, ?_⟩
      by_cases he : s.erase a = ∅
      · exact Or.inl he
      · right
        have hac : ¬ ρ a c := ((mem_rowComplement ρ q a c).mp (hsc ha)).2
        refine ⟨Finset.nonempty_iff_ne_empty.mpr he, c,
          Finset.mem_filter.mpr ⟨hc, hac⟩, ?_⟩
        intro x hx
        rcases (mem_rowComplement ρ q x c).mp
          (hsc (Finset.mem_of_mem_erase hx)) with ⟨hxA, hxρ⟩
        exact (mem_rowComplement ρ (singletonChild ρ q a) x c).mpr
          ⟨Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hxA⟩, hxρ⟩
    · exact Or.inl ⟨hs, fun x hx => Finset.mem_erase.mpr
        ⟨fun hxa => ha (hxa ▸ hx), ((mem_rowComplement ρ q x c).mp (hsc hx)).1⟩⟩
  · rintro (hD | ⟨hs, he | ⟨ht, c, hc, hsc⟩⟩)
    · exact singleton_base_le ρ q hsingle hD
    · have hsEq : s = {a} := by
        apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        refine ⟨hs, ?_⟩
        intro x hx
        by_contra hxa
        have hxE : x ∈ s.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rw [he] at hxE
        exact Finset.notMem_empty x hxE
      rw [hsEq]
      exact hapex
    · refine ⟨hs, c, (Finset.mem_filter.mp hc).1, ?_⟩
      intro x hx
      by_cases hxa : x = a
      · subst x
        exact (mem_rowComplement ρ q a c).mpr
          ⟨singleton_active ρ q hsingle, (Finset.mem_filter.mp hc).2⟩
      · rcases (mem_rowComplement ρ (singletonChild ρ q a) x c).mp
          (hsc (Finset.mem_erase.mpr ⟨hxa, hx⟩)) with ⟨hxU, hxρ⟩
        exact (mem_rowComplement ρ q x c).mpr ⟨Finset.mem_of_mem_erase hxU, hxρ⟩

theorem singleton_no_apex (ρ : I → J → Prop) (q : State ρ)
    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)
    (hrows : (singletonChild ρ q a).rows = ∅) :
    rootK ρ q = incidenceSimplex (q.active.erase a) := by
  classical
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, c, hc, hsc⟩
    have ha : a ∉ s := by
      intro has
      have hac : ¬ ρ a c := ((mem_rowComplement ρ q a c).mp (hsc has)).2
      have hcf : c ∈ (singletonChild ρ q a).rows :=
        Finset.mem_filter.mpr ⟨hc, hac⟩
      rw [hrows] at hcf
      exact Finset.notMem_empty c hcf
    exact ⟨hs, fun x hx => Finset.mem_erase.mpr
      ⟨fun hxa => ha (hxa ▸ hx), ((mem_rowComplement ρ q x c).mp (hsc hx)).1⟩⟩
  · exact singleton_base_le ρ q hsingle

theorem singleton_apex_of_child_rows (ρ : I → J → Prop) (q : State ρ)
    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)
    (hrows : (singletonChild ρ q a).rows.Nonempty) :
    ({a} : Finset I) ∈ rootK ρ q := by
  classical
  obtain ⟨c, hc⟩ := hrows
  refine ⟨Finset.singleton_nonempty _, c, (Finset.mem_filter.mp hc).1, ?_⟩
  intro x hx
  have hxa := Finset.mem_singleton.mp hx
  subst x
  exact (mem_rowComplement ρ q a c).mpr
    ⟨singleton_active ρ q hsingle, (Finset.mem_filter.mp hc).2⟩

theorem singleton_apex_of_child_face (ρ : I → J → Prop) (q : State ρ)
    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)
    {s : Finset I} (hs : s ∈ rootK ρ (singletonChild ρ q a)) :
    ({a} : Finset I) ∈ rootK ρ q := by
  rcases hs with ⟨_, c, hc, _⟩
  exact singleton_apex_of_child_rows ρ q a hsingle ⟨c, hc⟩

private theorem cone_sup (a : I) (C E : PreAbstractSimplicialComplex I) :
    cone a (C ⊔ E) = cone a C ⊔ cone a E := by
  apply SetLike.coe_injective
  ext s
  change (s.Nonempty ∧ (s.erase a = ∅ ∨ (s.erase a ∈ C ∨ s.erase a ∈ E))) ↔
    ((s.Nonempty ∧ (s.erase a = ∅ ∨ s.erase a ∈ C)) ∨
     (s.Nonempty ∧ (s.erase a = ∅ ∨ s.erase a ∈ E)))
  constructor
  · rintro ⟨hs, he | hC | hE⟩
    · exact Or.inl ⟨hs, Or.inl he⟩
    · exact Or.inl ⟨hs, Or.inr hC⟩
    · exact Or.inr ⟨hs, Or.inr hE⟩
  · rintro (⟨hs, he | hC⟩ | ⟨hs, he | hE⟩)
    · exact ⟨hs, Or.inl he⟩
    · exact ⟨hs, Or.inr (Or.inl hC)⟩
    · exact ⟨hs, Or.inl he⟩
    · exact ⟨hs, Or.inr (Or.inr hE)⟩

private theorem cone_simplex (a : I) (τ : Finset I) :
    cone a (incidenceSimplex τ) = incidenceSimplex (insert a τ) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, he | ⟨ht, htτ⟩⟩
    · refine ⟨hs, ?_⟩
      intro x hx
      by_cases hxa : x = a
      · exact Finset.mem_insert.mpr (Or.inl hxa)
      · have hxE : x ∈ s.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rw [he] at hxE
        exact (Finset.notMem_empty x hxE).elim
    · refine ⟨hs, ?_⟩
      intro x hx
      by_cases hxa : x = a
      · exact Finset.mem_insert.mpr (Or.inl hxa)
      · exact Finset.mem_insert.mpr (Or.inr (htτ (Finset.mem_erase.mpr ⟨hxa, hx⟩)))
  · rintro ⟨hs, hsτ⟩
    refine ⟨hs, ?_⟩
    by_cases he : s.erase a = ∅
    · exact Or.inl he
    · refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr he, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp (hsτ (Finset.mem_of_mem_erase hx)) with hxa | hxτ
      · exact ((Finset.mem_erase.mp hx).1 hxa).elim
      · exact hxτ

/- The support inclusions use the endpoint description before sequence
   monotonicity.  core_sequence has the opposite direction for this purpose. -/
private theorem witness_core_le_endpoint {ρ : I → J → Prop} {q : State ρ}
    (w : Witness ρ q) : w.core ≤ w.endpoint := by
  cases hc : w.critical with
  | none => simpa only [w.endpoint_eq_core hc] using (le_rfl : w.core ≤ w.core)
  | some τ => rw [w.endpoint_eq_attach τ hc]; exact le_sup_left

private theorem witness_critical_support {ρ : I → J → Prop} {q : State ρ}
    (w : Witness ρ q) {τ : Finset I} (hc : w.critical = some τ) :
    τ ⊆ q.active := by
  have hτ : τ ∈ w.endpoint := by
    rw [w.endpoint_eq_attach τ hc]
    exact Or.inr ⟨w.critical_nonempty τ hc, le_rfl⟩
  exact (rootK_le_full ρ q (w.sequence.monotone hτ)).2

/-! ### Recursive constructor -/

def build {ρ : I → J → Prop} : {q : State ρ} → (c : Pruning ρ q) → Result ρ q
  | q, .void _ hrows =>
      .terminal .void (rootK_empty_rows ρ q hrows) hrows
  | q, .unit _ hrows hfull =>
      .terminal .unit (rootK_full_rows ρ q hrows hfull) ⟨hrows, hfull⟩
  | q, .emptyRow _ b hb hempty => by
      classical
      have hK := rootK_empty_row ρ q hb hempty
      by_cases hA : q.active.Nonempty
      · obtain ⟨p, hp⟩ := hA
        exact .regular {
          endpoint := vertexComplex p
          sequence := (simplexCollapse q.active p hp).cast hK.symm rfl
          core := vertexComplex p
          pivot := p
          pivot_mem := hp
          core_sequence := Sequence.refl _
          critical := none
          endpoint_eq_core := by intro; rfl
          endpoint_eq_attach := by intro σ h; cases h
          critical_nonempty := by intro σ h; cases h
          critical_outside := by intro σ h; cases h
          critical_boundary := by intro σ h; cases h }
      · have hAE : q.active = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hA ⟨x, hx⟩)
        have hfull : ∀ c ∈ q.rows, rowNeighborhood ρ q c = q.active := by
          intro c hc
          apply Finset.Subset.antisymm
          · intro x hx
            exact ((mem_rowNeighborhood ρ q x c).mp hx).1
          · rw [hAE]
            exact Finset.empty_subset _
        exact .terminal .unit (rootK_full_rows ρ q ⟨b, hb⟩ hfull) ⟨⟨b, hb⟩, hfull⟩
  | q, .isolatedColumn _ x hx hrows hiso => by
      exact .regular {
        endpoint := vertexComplex x
        sequence := isolatedCollapse ρ q x hx hrows hiso
        core := vertexComplex x
        pivot := x
        pivot_mem := hx
        core_sequence := Sequence.refl _
        critical := none
        endpoint_eq_core := by intro; rfl
        endpoint_eq_attach := by intro σ h; cases h
        critical_nonempty := by intro σ h; cases h
        critical_outside := by intro σ h; cases h
        critical_boundary := by intro σ h; cases h }
  | q, .redundantRow _ b c hb hc hbc hsub child => by
      classical
      have hK := rootK_row_erase ρ q hb hc hbc hsub
      have hbchild : b ∈ (eraseRow ρ q c).rows := Finset.mem_erase.mpr ⟨hbc, hb⟩
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              change (eraseRow ρ q c).rows = ∅ at hLaw
              rw [hLaw] at hbchild
              exact (Finset.notMem_empty b hbchild).elim
          | unit =>
              change (eraseRow ρ q c).rows.Nonempty ∧
                (∀ d ∈ (eraseRow ρ q c).rows,
                  rowNeighborhood ρ (eraseRow ρ q c) d = (eraseRow ρ q c).active) at hLaw
              have hfull : ∀ d ∈ q.rows, rowNeighborhood ρ q d = q.active := by
                intro d hd
                by_cases hdc : d = c
                · subst d
                  have hbfull : rowNeighborhood ρ q b = q.active := hLaw.2 b hbchild
                  apply Finset.Subset.antisymm
                  · intro x hx
                    exact ((mem_rowNeighborhood ρ q x c).mp hx).1
                  · intro x hx
                    apply rowSubset_neighborhood ρ q hsub
                    rw [hbfull]
                    exact hx
                · exact hLaw.2 d (Finset.mem_erase.mpr ⟨hdc, hd⟩)
              exact .terminal .unit (hK.trans hchild) ⟨⟨b, hb⟩, hfull⟩
      | regular w =>
          exact .regular {
            endpoint := w.endpoint
            sequence := w.sequence.cast hK.symm rfl
            core := w.core
            pivot := w.pivot
            pivot_mem := w.pivot_mem
            core_sequence := w.core_sequence
            critical := w.critical
            endpoint_eq_core := w.endpoint_eq_core
            endpoint_eq_attach := w.endpoint_eq_attach
            critical_nonempty := w.critical_nonempty
            critical_outside := w.critical_outside
            critical_boundary := w.critical_boundary }
  | q, .dominatedColumn _ x y hx hy hxy hsub child => by
      classical
      have hExt : Extends (rootK ρ q) x y := by
        rintro s ⟨hs, b, hb, hsb⟩ hyS
        refine ⟨Finset.insert_nonempty _ _, b, hb, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
          intro hxb
          exact (Finset.mem_sdiff.mp (hsb hyS)).2
            (columnSubset_neighborhood ρ q hy hsub b hb hxb)
        · exact hsb hz
      let P := sequence (rootK ρ q) x y hxy hExt
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              have hrows : q.rows = ∅ := hLaw
              exact .terminal .void (rootK_empty_rows ρ q hrows) hrows
          | unit =>
              change (eraseColumn ρ q y).rows.Nonempty ∧
                (∀ b ∈ (eraseColumn ρ q y).rows,
                  rowNeighborhood ρ (eraseColumn ρ q y) b = (eraseColumn ρ q y).active) at hLaw
              have hfull : ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active := by
                intro b hb
                have hρx : ρ x b := by
                  apply ((mem_rowNeighborhood ρ (eraseColumn ρ q y) x b).mp ?_).2
                  rw [hLaw.2 b hb]
                  exact Finset.mem_erase.mpr ⟨hxy, hx⟩
                apply Finset.Subset.antisymm
                · intro z hz
                  exact ((mem_rowNeighborhood ρ q z b).mp hz).1
                · intro z hz
                  apply (mem_rowNeighborhood ρ q z b).mpr
                  refine ⟨hz, ?_⟩
                  by_cases hzy : z = y
                  · subst z
                    exact hsub b hb hρx
                  · apply ((mem_rowNeighborhood ρ (eraseColumn ρ q y) z b).mp ?_).2
                    rw [hLaw.2 b hb]
                    exact Finset.mem_erase.mpr ⟨hzy, hz⟩
              exact .terminal .unit (rootK_full_rows ρ q hLaw.1 hfull) ⟨hLaw.1, hfull⟩
      | regular w =>
          have hdel := rootK_column_delete ρ q hy hxy hsub
          exact .regular {
            endpoint := w.endpoint
            sequence := P.append (w.sequence.cast hdel.symm rfl)
            core := w.core
            pivot := w.pivot
            pivot_mem := Finset.mem_of_mem_erase w.pivot_mem
            core_sequence := w.core_sequence
            critical := w.critical
            endpoint_eq_core := w.endpoint_eq_core
            endpoint_eq_attach := w.endpoint_eq_attach
            critical_nonempty := w.critical_nonempty
            critical_outside := w.critical_outside
            critical_boundary := w.critical_boundary }
  | q, .singletonRow _ b a hsingle child => by
      classical
      let U := q.active.erase a
      let D := incidenceSimplex U
      have haA : a ∈ q.active := singleton_active ρ q hsingle
      have haD : Fresh a D := fresh_of_active_erase q.active a
      cases build child with
      | terminal tag hchild hLaw =>
          cases tag with
          | void =>
              change (singletonChild ρ q a).rows = ∅ at hLaw
              have hK := singleton_no_apex ρ q a hsingle hLaw
              by_cases hU : U.Nonempty
              · obtain ⟨p, hp⟩ := hU
                exact .regular {
                  endpoint := vertexComplex p
                  sequence := (simplexCollapse U p hp).cast hK.symm rfl
                  core := vertexComplex p
                  pivot := p
                  pivot_mem := Finset.mem_of_mem_erase hp
                  core_sequence := Sequence.refl _
                  critical := none
                  endpoint_eq_core := by intro; rfl
                  endpoint_eq_attach := by intro σ h; cases h
                  critical_nonempty := by intro σ h; cases h
                  critical_outside := by intro σ h; cases h
                  critical_boundary := by intro σ h; cases h }
              · have hUE : U = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hU ⟨x, hx⟩)
                have hact : q.active = {a} := by
                  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
                  refine ⟨⟨a, haA⟩, ?_⟩
                  intro z hz
                  by_contra hza
                  exact hU ⟨z, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
                have hfull : ∀ c ∈ q.rows, rowNeighborhood ρ q c = q.active := by
                  intro c hc
                  have hac : ρ a c := by
                    by_contra hnot
                    have hcf : c ∈ (singletonChild ρ q a).rows :=
                      Finset.mem_filter.mpr ⟨hc, hnot⟩
                    rw [hLaw] at hcf
                    exact Finset.notMem_empty c hcf
                  apply Finset.Subset.antisymm
                  · intro z hz
                    exact ((mem_rowNeighborhood ρ q z c).mp hz).1
                  · intro z hz
                    have hza : z = a := by
                      rw [hact] at hz
                      exact Finset.mem_singleton.mp hz
                    subst z
                    exact (mem_rowNeighborhood ρ q a c).mpr ⟨haA, hac⟩
                exact .terminal .unit (hK.trans (by rw [hUE]; exact simplex_empty))
                  ⟨⟨b, hsingle.1⟩, hfull⟩
          | unit =>
              change (singletonChild ρ q a).rows.Nonempty ∧
                (∀ c ∈ (singletonChild ρ q a).rows,
                  rowNeighborhood ρ (singletonChild ρ q a) c =
                    (singletonChild ρ q a).active) at hLaw
              have hapex := singleton_apex_of_child_rows ρ q a hsingle hLaw.1
              have hdec := singleton_decomposition ρ q a hsingle hapex
              by_cases hU : U.Nonempty
              · obtain ⟨p, hp⟩ := hU
                let Kparent := D ⊔ cone a (⊥ : PreAbstractSimplicialComplex I)
                have hparent : rootK ρ q = Kparent := by
                  rw [hdec, hchild]
                exact .regular {
                  endpoint := Kparent
                  sequence := (Sequence.refl Kparent).cast hparent.symm rfl
                  core := D
                  pivot := p
                  pivot_mem := Finset.mem_of_mem_erase hp
                  core_sequence := simplexCollapse U p hp
                  critical := some ({a} : Finset I)
                  endpoint_eq_core := by intro h; cases h
                  endpoint_eq_attach := by
                    intro σ hσ
                    have he : ({a} : Finset I) = σ := Option.some.inj hσ
                    subst σ
                    change D ⊔ cone a (⊥ : PreAbstractSimplicialComplex I) =
                      D ⊔ incidenceSimplex {a}
                    rw [cone_bot_simplex]
                  critical_nonempty := by
                    intro σ hσ
                    have he : ({a} : Finset I) = σ := Option.some.inj hσ
                    subst σ
                    exact Finset.singleton_nonempty _
                  critical_outside := by
                    intro σ hσ hmem
                    have he : ({a} : Finset I) = σ := Option.some.inj hσ
                    subst σ
                    exact haD {a} hmem (Finset.mem_singleton_self _)
                  critical_boundary := by
                    intro σ hσ t ht
                    have he : ({a} : Finset I) = σ := Option.some.inj hσ
                    subst σ
                    left
                    by_contra hne
                    have hte : t = {a} :=
                      Finset.eq_singleton_iff_nonempty_unique_mem.mpr
                        ⟨Finset.nonempty_iff_ne_empty.mpr hne,
                          fun z hz => Finset.mem_singleton.mp (ht.subset hz)⟩
                    exact ht.ne hte }
              · have hUE : U = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => hU ⟨x, hx⟩)
                have hparent : rootK ρ q = vertexComplex a := by
                  rw [hdec, hchild]
                  change incidenceSimplex U ⊔ cone a (⊥ : PreAbstractSimplicialComplex I) = _
                  simp [hUE, simplex_empty, cone_bot_simplex, simplex_singleton]
                exact .regular {
                  endpoint := vertexComplex a
                  sequence := (Sequence.refl (vertexComplex a)).cast hparent.symm rfl
                  core := vertexComplex a
                  pivot := a
                  pivot_mem := haA
                  core_sequence := Sequence.refl _
                  critical := none
                  endpoint_eq_core := by intro; rfl
                  endpoint_eq_attach := by intro σ h; cases h
                  critical_nonempty := by intro σ h; cases h
                  critical_outside := by intro σ h; cases h
                  critical_boundary := by intro σ h; cases h }
      | regular w =>
          have hsourceD : rootK ρ (singletonChild ρ q a) ≤ D :=
            rootK_le_full ρ (singletonChild ρ q a)
          have hcoreRoot : w.core ≤ rootK ρ (singletonChild ρ q a) :=
            (witness_core_le_endpoint w).trans w.sequence.monotone
          have hcoreD : w.core ≤ D := hcoreRoot.trans hsourceD
          have hpU : w.pivot ∈ U := w.pivot_mem
          have hap : a ≠ w.pivot := by
            intro he
            exact (Finset.mem_erase.mp hpU).1 he.symm
          have hpCore : ({w.pivot} : Finset I) ∈ w.core :=
            w.core_sequence.monotone (show ({w.pivot} : Finset I) ∈ vertexComplex w.pivot from rfl)
          have hapex := singleton_apex_of_child_face ρ q a hsingle (hcoreRoot hpCore)
          have hdec := singleton_decomposition ρ q a hsingle hapex
          let main := (w.sequence.liftOver D a hsourceD haD).cast hdec.symm rfl
          let coreSeq := liftCoreToBase U w.core a w.pivot hcoreD haD
            w.core_sequence hpU hap
          exact .regular {
            endpoint := D ⊔ cone a w.endpoint
            sequence := main
            core := D ⊔ cone a w.core
            pivot := w.pivot
            pivot_mem := Finset.mem_of_mem_erase hpU
            core_sequence := coreSeq
            critical := w.critical.map (insert a)
            endpoint_eq_core := by
              intro h
              cases hc : w.critical with
              | none => rw [w.endpoint_eq_core hc]
              | some τ => simp [hc] at h
            endpoint_eq_attach := by
              intro σ hσ
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = σ := Option.some.inj (by simpa [hc] using hσ)
                  subst σ
                  rw [w.endpoint_eq_attach τ hc, cone_sup, cone_simplex, sup_assoc]
            critical_nonempty := by
              intro σ hσ
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = σ := Option.some.inj (by simpa [hc] using hσ)
                  subst σ
                  exact Finset.insert_nonempty _ _
            critical_outside := by
              intro σ hσ hmem
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = σ := Option.some.inj (by simpa [hc] using hσ)
                  subst σ
                  have hτU : τ ⊆ U := witness_critical_support w hc
                  have haτ : a ∉ τ := fun ha => (Finset.mem_erase.mp (hτU ha)).1 rfl
                  rcases hmem with hD | hcone
                  · exact haD (insert a τ) hD (Finset.mem_insert_self _ _)
                  · have haug : AugmentedFace w.core τ := by
                      simpa only [Finset.erase_insert haτ] using hcone.2
                    rcases haug with he | hτC
                    · exact (w.critical_nonempty τ hc).ne_empty he
                    · exact w.critical_outside τ hc hτC
            critical_boundary := by
              intro σ hσ t ht
              cases hc : w.critical with
              | none => simp [hc] at hσ
              | some τ =>
                  have he : insert a τ = σ := Option.some.inj (by simpa [hc] using hσ)
                  subst σ
                  have hτU : τ ⊆ U := witness_critical_support w hc
                  by_cases hte : t = ∅
                  · exact Or.inl hte
                  · right
                    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hte
                    by_cases hat : a ∈ t
                    · have het : t.erase a ⊆ τ := by
                        intro z hz
                        rcases Finset.mem_insert.mp (ht.subset (Finset.mem_of_mem_erase hz)) with hza | hzτ
                        · exact ((Finset.mem_erase.mp hz).1 hza).elim
                        · exact hzτ
                      have hstrict : t.erase a ⊂ τ := by
                        refine Finset.ssubset_iff_subset_ne.mpr ⟨het, ?_⟩
                        intro heq
                        apply ht.ne
                        calc
                          t = insert a (t.erase a) := (Finset.insert_erase hat).symm
                          _ = insert a τ := congrArg (insert a) heq
                      exact Or.inr ⟨htne, w.critical_boundary τ hc (t.erase a) hstrict⟩
                    · exact Or.inl ⟨htne, fun z hz => hτU (by
                        rcases Finset.mem_insert.mp (ht.subset hz) with hza | hzτ
                        · exact (hat (hza ▸ hz)).elim
                        · exact hzτ)⟩ }
termination_by structural c

/-! ### Public native-map and replay contracts -/

def nativeSDR {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :
    RelativeSDR (rootK ρ q) w.endpoint w.sequence.monotone := w.sequence.realize

def nativeInclusion {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :
    C(Space w.endpoint, Space (rootK ρ q)) := w.sequence.inclusion

def nativeRetraction {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :
    C(Space (rootK ρ q), Space w.endpoint) := w.sequence.sequenceRetraction

theorem nativeRetraction_inclusion {ρ : I → J → Prop} {q : State ρ}
    (w : Witness ρ q) (x : Space w.endpoint) :
    nativeRetraction w (nativeInclusion w x) = x :=
  w.sequence.sequenceRetraction_inclusion x

theorem nativeHomotopy_fixed {ρ : I → J → Prop} {q : State ρ}
    (w : Witness ρ q) (t : Set.Icc (0 : ℝ) 1) (x : Space (rootK ρ q))
    (hx : x.val ∈ realization w.endpoint) :
    w.sequence.collapseHomotopy (t, x) = x :=
  w.sequence.collapseHomotopy_fixed t x hx

def rootCertificate {ρ : I → J → Prop} {q : State ρ} (c : Pruning ρ q) :
    Result ρ q := build c

end D5.S3.Geometry.FiniteIncidenceRootCollapse
