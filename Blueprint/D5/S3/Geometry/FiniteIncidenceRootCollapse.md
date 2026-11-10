# Ordinary pendant and twin pruning on the original labels

## Abstract

Original-ground finite incidence root-K collapse certificates.

The constructor retains arbitrary Prop-valued incidence, the original ambient and row labels, nonempty ordinary faces, and full parent-base fixedness. The source headers below specify lexical scope.

**Definition 1.1 (State).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.State`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Original ambient vertex and row label types remain fixed. The state stores only an active finite ground and literal row labels.

### Source text

Authored Lean source header:structure State (ρ : I → J → Prop) where

  active : Finset I

  rows : Finset J

**Definition 1.2 (rowNeighborhood).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowNeighborhood`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowNeighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Classical predicate decidability defines the local neighborhood for arbitrary Prop-valued incidence, without an incidence-decidability hypothesis.

Authored Lean source header:def rowNeighborhood (ρ : I → J → Prop) (q : State ρ) (b : J) : Finset I

**Theorem 1.3 (mem_rowNeighborhood).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rowNeighborhood`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rowNeighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership is exactly active support together with incidence in the specified row.

### Source text

Authored Lean source header:@[simp] theorem mem_rowNeighborhood (ρ : I → J → Prop) (q : State ρ)

    (x : I) (b : J) :

    x ∈ rowNeighborhood ρ q b ↔ x ∈ q.active ∧ ρ x b

**Definition 1.4 (incidenceSimplex).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceSimplex`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceSimplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full nonempty-face simplex on the literal finite subset of the original ambient carrier.

Authored Lean source header:def incidenceSimplex (lambda : Finset I) : PreAbstractSimplicialComplex I

**Definition 1.5 (rootK).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonempty faces lie in the active complement of an actual row neighborhood. Inactive ambient labels remain ghosts.

### Source text

Authored Lean source header:def rootK (ρ : I → J → Prop) (q : State ρ) : PreAbstractSimplicialComplex I where

  faces := {s | s.Nonempty ∧ ∃ b ∈ q.rows, s ⊆ q.active \ rowNeighborhood ρ q b}

  isRelLowerSet_faces := by

    rintro s ⟨hs, b, hb, hsb⟩

    refine ⟨hs, ?_⟩

    intro t hts ht

    exact ⟨ht, b, hb, fun x hx => hsb (hts hx)⟩

**Theorem 1.6 (mem_rootK).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rootK`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rootK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact membership presentation for the original-ground root complex; the existential ranges over literal row labels.

### Source text

Authored Lean source header:@[simp] theorem mem_rootK (ρ : I → J → Prop) (q : State ρ) (s : Finset I) :

    s ∈ rootK ρ q ↔

      s.Nonempty ∧ ∃ b ∈ q.rows, s ⊆ q.active \ rowNeighborhood ρ q b

**Definition 1.7 (incidenceDual).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceDual`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonempty proper active subsets avoiding containment of every row neighborhood.

### Source text

Authored Lean source header:def incidenceDual (ρ : I → J → Prop) (q : State ρ) :

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

**Theorem 1.8 (rootK_dual).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-ground Alexander dual of rootK is exactly incidenceDual, including empty-ground and terminal cases.

### Source text

Authored Lean source header:theorem rootK_dual (ρ : I → J → Prop) (q : State ρ) :

    FiniteAlexanderDualCollapse.dual q.active (rootK ρ q) = incidenceDual ρ q

**Definition 1.9 (eraseRow).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase one row label and retain the original active vertex ground.

Authored Lean source header:def eraseRow (ρ : I → J → Prop) (q : State ρ) (c : J) : State ρ

**Definition 1.10 (eraseColumn).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase one active column label while retaining the original ambient type and row labels.

Authored Lean source header:def eraseColumn (ρ : I → J → Prop) (q : State ρ) (y : I) : State ρ

**Definition 1.11 (singletonChild).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singletonChild`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.singletonChild` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Erase the singleton apex from the active ground and retain exactly rows whose incidence avoids the apex, using classical decidability.

Authored Lean source header:def singletonChild (ρ : I → J → Prop) (q : State ρ) (a : I) : State ρ

**Theorem 1.12 (eraseRow_active).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow_active`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row erasure preserves the entire active vertex ground definitionally.

### Source text

Authored Lean source header:@[simp] theorem eraseRow_active (ρ : I → J → Prop) (q : State ρ) (c : J) :

    (eraseRow ρ q c).active = q.active

**Theorem 1.13 (eraseColumn_rows).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Column erasure preserves every literal row label definitionally.

### Source text

Authored Lean source header:@[simp] theorem eraseColumn_rows (ρ : I → J → Prop) (q : State ρ) (y : I) :

    (eraseColumn ρ q y).rows = q.rows

**Definition 1.14 (RowSubset).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.RowSubset`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.RowSubset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The directional incidence condition N(b) contained in N(c), restricted to the active ground.

Authored Lean source header:def RowSubset (ρ : I → J → Prop) (q : State ρ) (b c : J) : Prop

**Definition 1.15 (ColumnSubset).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.ColumnSubset`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.ColumnSubset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every retained row incident to x is incident to y; this direction allows insertion of x in a face containing y.

Authored Lean source header:def ColumnSubset (ρ : I → J → Prop) (q : State ρ) (x y : I) : Prop

**Definition 1.16 (IsolatedColumn).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.IsolatedColumn`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.IsolatedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The specified column is incident to no retained row; active support is supplied separately by its consumers.

Authored Lean source header:def IsolatedColumn (ρ : I → J → Prop) (q : State ρ) (x : I) : Prop

**Definition 1.17 (SingletonRow).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.SingletonRow`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.SingletonRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual retained row has local neighborhood exactly the singleton apex.

Authored Lean source header:def SingletonRow (ρ : I → J → Prop) (q : State ρ) (b : J) (a : I) : Prop

**Theorem 1.18 (rowSubset_neighborhood).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowSubset_neighborhood`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowSubset_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Converts row incidence inclusion to inclusion of the actual local neighborhoods.

### Source text

Authored Lean source header:theorem rowSubset_neighborhood (ρ : I → J → Prop) (q : State ρ)

    {b c : J} (h : RowSubset ρ q b c) :

    rowNeighborhood ρ q b ⊆ rowNeighborhood ρ q c

**Theorem 1.19 (columnSubset_neighborhood).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.columnSubset_neighborhood`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.columnSubset_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion requires active membership of y. Dominated-column input already supplies it; inactive ambient ghosts give a counterexample without it.

### Source text

Authored Lean source header:theorem columnSubset_neighborhood (ρ : I → J → Prop) (q : State ρ)

    {x y : I} (hy : y ∈ q.active) (h : ColumnSubset ρ q x y) :

    ∀ b ∈ q.rows, x ∈ rowNeighborhood ρ q b → y ∈ rowNeighborhood ρ q b

**Theorem 1.20 (rootK_empty_rows).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No retained rows gives the ordinary bottom complex, the VOID case.

### Source text

Authored Lean source header:theorem rootK_empty_rows (ρ : I → J → Prop) (q : State ρ) (h : q.rows = ∅) :

    rootK ρ q = ⊥

**Theorem 1.21 (rootK_full_rows).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_full_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_full_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonempty retained rows all equal to the active ground give the ordinary bottom complex, the UNIT case.

### Source text

Authored Lean source header:theorem rootK_full_rows (ρ : I → J → Prop) (q : State ρ)

    (hn : q.rows.Nonempty)

    (hfull : ∀ b ∈ q.rows, rowNeighborhood ρ q b = q.active) :

    rootK ρ q = ⊥

**Theorem 1.22 (rootK_empty_row).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One empty neighborhood realizes the full simplex on the active ground, without choosing a point on an empty ground.

### Source text

Authored Lean source header:theorem rootK_empty_row (ρ : I → J → Prop) (q : State ρ) {b : J}

    (hb : b ∈ q.rows) (hempty : rowNeighborhood ρ q b = ∅) :

    rootK ρ q = incidenceSimplex q.active

**Theorem 1.23 (rootK_row_erase).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_row_erase`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_row_erase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Erase c when N(b) is contained in N(c). Its complement simplex is already contained in the simplex supplied by b.

### Source text

Authored Lean source header:theorem rootK_row_erase (ρ : I → J → Prop) (q : State ρ)

    {b c : J} (hb : b ∈ q.rows) (hc : c ∈ q.rows) (hbc : b ≠ c)

    (hsub : RowSubset ρ q b c) :

    rootK ρ q = rootK ρ (eraseRow ρ q c)

**Theorem 1.24 (rootK_column_delete).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_column_delete`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_column_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal deletion equals the root complex with y erased from active. Both directions convert erased support and incidence explicitly; the equation retains the established public telescope.

### Source text

Authored Lean source header:theorem rootK_column_delete (ρ : I → J → Prop) (q : State ρ)

    {x y : I} (hy : y ∈ q.active) (hxy : x ≠ y)

    (hsub : ColumnSubset ρ q x y) :

    deletion (rootK ρ q) y = rootK ρ (eraseColumn ρ q y)

**Theorem 1.25 (rootK_isolated_cone).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_isolated_cone`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_isolated_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An active isolated column over nonempty rows is an actual cone apex, even when the child ordinary complex is bottom.

### Source text

Authored Lean source header:theorem rootK_isolated_cone (ρ : I → J → Prop) (q : State ρ)

    {x : I} (hx : x ∈ q.active) (hrows : q.rows.Nonempty)

    (hiso : IsolatedColumn ρ q x) :

    rootK ρ q = cone x (rootK ρ (eraseColumn ρ q x))

**Definition 1.26 (Pruning).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Pruning`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.Pruning` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seven actual structural constructors: VOID, UNIT, empty row, isolated column, redundant row with child, dominated column with child, singleton row with child. None supplies a desired collapse or output witness.

### Source text

Authored Lean source header:inductive Pruning (ρ : I → J → Prop) : State ρ → Type

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

**Definition 1.27 (TerminalTag).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalTag`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalTag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

VOID and UNIT are distinct augmented terminal labels although their ordinary root complexes are both bottom.

### Source text

Authored Lean source header:inductive TerminalTag where

  | void

  | unit

deriving DecidableEq

**Definition 1.28 (TerminalLaw).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalLaw`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

VOID records empty rows; UNIT records nonempty rows and full local neighborhoods on the original state.

Authored Lean source header:def TerminalLaw (ρ : I → J → Prop) (q : State ρ) (tag : TerminalTag) : Prop

**Definition 1.29 (Witness).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Witness`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.Witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A constructed native sequence, separate collapsible core and supported original pivot, plus optional critical face with exact endpoint, nonemptiness, outside and complete proper-boundary conditions.

### Source text

Authored Lean source header:structure Witness (ρ : I → J → Prop) (q : State ρ) where

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

**Definition 1.30 (Result).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Result`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.Result` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Either a truthful terminal tag with original-state law and bottom equation, or an ordinary regular geometric witness.

### Source text

Authored Lean source header:inductive Result (ρ : I → J → Prop) (q : State ρ) where

  | terminal (tag : TerminalTag) (hK : rootK ρ q = ⊥)

      (hLaw : TerminalLaw ρ q tag) : Result ρ q

  | regular (w : Witness ρ q) : Result ρ q

**Definition 1.31 (augmentedTerminal).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.augmentedTerminal`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.augmentedTerminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

VOID has only ordinary root membership. UNIT restores the empty face solely in this augmented predicate.

### Source text

Authored Lean source header:def augmentedTerminal (ρ : I → J → Prop) (q : State ρ) (tag : TerminalTag)

    (s : Finset I) : Prop

**Theorem 1.32 (terminal_semantics).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.terminal_semantics`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.terminal_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the ordinary bottom equation, VOID augmentation is false and UNIT augmentation is precisely the empty face.

### Source text

Authored Lean source header:theorem terminal_semantics (ρ : I → J → Prop) {q : State ρ}

    (tag : TerminalTag) (hK : rootK ρ q = ⊥) (s : Finset I) :

    augmentedTerminal ρ q tag s ↔

      match tag with | .void => False | .unit => s = ∅

**Definition 1.33 (simplexCollapse).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.simplexCollapse`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.simplexCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Actual dominated-vertex free-pair sequences recursively erase nonpivot labels, with strictly decreasing active cardinality, ending at the literal pivot vertex complex. In the nonempty erased-ground branch, Classical.choose hrest selects the original label y and Classical.choose_spec hrest proves y ∈ A.erase p. That membership supplies the inequality, native domination and deletion transports, and the strict cardinality decrease. The quotation gives the definition and its proof.

Definitions and proofs are in the paired Lean module.

Lean definition body:

def simplexCollapse : ∀ (A : Finset I) (p : I), p ∈ A →

    Sequence (incidenceSimplex A) (vertexComplex p)

  | A, p, hp => by

      classical

      by_cases hrest : (A.erase p).Nonempty

      · let y := Classical.choose hrest

        have hy := Classical.choose_spec hrest

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

Definitions and proofs are in the paired Lean module.

### Source text

Authored Lean source header:def simplexCollapse : ∀ (A : Finset I) (p : I), p ∈ A →

    Sequence (incidenceSimplex A) (vertexComplex p)

**Definition 1.34 (isolatedCollapse).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.isolatedCollapse`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.isolatedCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Actual domination sequences erase every nonapex active label, with strictly decreasing active cardinality, and collapse the original cone to its actual apex. Classical.choose hrest selects y on the same ambient type and Classical.choose_spec hrest proves y ∈ q.active.erase x. That membership supplies the native domination and deletion transports and the strict cardinality decrease. The row witness obtained inside hK remains local to an equality proof in Prop. The quotation gives the definition and its proof.

Definitions and proofs are in the paired Lean module.

Lean definition body:

def isolatedCollapse : ∀ (ρ : I → J → Prop) (q : State ρ) (x : I),

    x ∈ q.active → q.rows.Nonempty → IsolatedColumn ρ q x →

    Sequence (rootK ρ q) (vertexComplex x)

  | ρ, q, x, hx, hrows, hiso => by

      classical

      by_cases hrest : (q.active.erase x).Nonempty

      · let y := Classical.choose hrest

        have hy := Classical.choose_spec hrest

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

Definitions and proofs are in the paired Lean module.

### Source text

Authored Lean source header:def isolatedCollapse : ∀ (ρ : I → J → Prop) (q : State ρ) (x : I),

    x ∈ q.active → q.rows.Nonempty → IsolatedColumn ρ q x →

    Sequence (rootK ρ q) (vertexComplex x)

**Definition 1.35 (liftCoreToBase).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.liftCoreToBase`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.liftCoreToBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lift a core sequence over the full base, remove the genuine terminal pair only inside that core, then collapse the base to the same actual pivot. This sequence is separate from the main retained-critical sequence.

### Source text

Authored Lean source header:def liftCoreToBase (A : Finset I) (C : PreAbstractSimplicialComplex I)

    (a p : I) (hCD : C ≤ incidenceSimplex A)

    (haD : Fresh a (incidenceSimplex A))

    (S : Sequence C (vertexComplex p))

    (hpA : p ∈ A) (hap : a ≠ p) :

    Sequence (incidenceSimplex A ⊔ cone a C) (vertexComplex p)

**Theorem 1.36 (singleton_decomposition).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With an actual parent apex, every parent face belongs to the full erased-ground base or to the cone over the filtered child, and conversely. The full parent base retains all child-retired labels.

### Source text

Authored Lean source header:theorem singleton_decomposition (ρ : I → J → Prop) (q : State ρ)

    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)

    (hapex : ({a} : Finset I) ∈ rootK ρ q) :

    rootK ρ q = incidenceSimplex (q.active.erase a) ⊔

      cone a (rootK ρ (singletonChild ρ q a))

**Theorem 1.37 (singleton_no_apex).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_no_apex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_no_apex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Empty filtered child rows forbid the apex in every parent face and yield exactly the full erased-ground base simplex.

### Source text

Authored Lean source header:theorem singleton_no_apex (ρ : I → J → Prop) (q : State ρ)

    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)

    (hrows : (singletonChild ρ q a).rows = ∅) :

    rootK ρ q = incidenceSimplex (q.active.erase a)

**Theorem 1.38 (singleton_apex_of_child_rows).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A retained filtered child row supplies an actual apex singleton in the parent root complex.

### Source text

Authored Lean source header:theorem singleton_apex_of_child_rows (ρ : I → J → Prop) (q : State ρ)

    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)

    (hrows : (singletonChild ρ q a).rows.Nonempty) :

    ({a} : Finset I) ∈ rootK ρ q

**Theorem 1.39 (singleton_apex_of_child_face).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_face`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual child face supplies a filtered row, hence an actual parent apex singleton.

### Source text

Authored Lean source header:theorem singleton_apex_of_child_face (ρ : I → J → Prop) (q : State ρ)

    {b : J} (a : I) (hsingle : SingletonRow ρ q b a)

    {s : Finset I} (hs : s ∈ rootK ρ (singletonChild ρ q a)) :

    ({a} : Finset I) ∈ rootK ρ q

**Definition 1.40 (build).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.build`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.build` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Structural recursion on the real Pruning input constructs Result. Parent terminal laws are proved for each row or column transport. The empty-row nonempty-ground branch selects p by Classical.choose hA and obtains p ∈ q.active from Classical.choose_spec hA. Both singleton-row child-terminal branches with U.Nonempty select p by Classical.choose hU and obtain p ∈ U from Classical.choose_spec hU; Finset.mem_of_mem_erase supplies original active membership. The VOID-child branch casts the simplex-collapse main sequence and uses a reflexive separate core sequence. The UNIT-child branch uses a reflexive main sequence and a separate simplex-collapse core sequence, retaining critical singleton {a} and its full boundary laws. Regular singleton lifting uses source and core containments separately, the actual child pivot, explicit critical Option splitting, literal cone/simplex equations, and proper-boundary support. No output or collapse premise is added. The quotation gives the definition and its proof.

Definitions and proofs are in the paired Lean module.

Lean definition body:

def build {ρ : I → J → Prop} : {q : State ρ} → (c : Pruning ρ q) → Result ρ q

  | q, .void _ hrows =>

      .terminal .void (rootK_empty_rows ρ q hrows) hrows

  | q, .unit _ hrows hfull =>

      .terminal .unit (rootK_full_rows ρ q hrows hfull) ⟨hrows, hfull⟩

  | q, .emptyRow _ b hb hempty => by

      classical

      have hK := rootK_empty_row ρ q hb hempty

      by_cases hA : q.active.Nonempty

      · let p := Classical.choose hA

        have hp := Classical.choose_spec hA

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

              · let p := Classical.choose hU

                have hp := Classical.choose_spec hU

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

              · let p := Classical.choose hU

                have hp := Classical.choose_spec hU

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

Definitions and proofs are in the paired Lean module.

Authored Lean source header:def build {ρ : I → J → Prop} : {q : State ρ} → (c : Pruning ρ q) → Result ρ q

**Definition 1.41 (nativeSDR).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeSDR`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeSDR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applies the relative strong deformation retraction construction to the main sequence.

### Source text

Authored Lean source header:def nativeSDR {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :

    RelativeSDR (rootK ρ q) w.endpoint w.sequence.monotone

**Definition 1.42 (nativeInclusion).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeInclusion`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal original-coordinate inclusion of the final endpoint supplied by the constructed sequence.

### Source text

Authored Lean source header:def nativeInclusion {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :

    C(Space w.endpoint, Space (rootK ρ q))

**Definition 1.43 (nativeRetraction).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The composed native retraction supplied by the constructed main sequence.

### Source text

Authored Lean source header:def nativeRetraction {ρ : I → J → Prop} {q : State ρ} (w : Witness ρ q) :

    C(Space (rootK ρ q), Space w.endpoint)

**Theorem 1.44 (nativeRetraction_inclusion).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retraction after the literal endpoint inclusion equals the identity, by the actual Sequence contract.

### Source text

Authored Lean source header:theorem nativeRetraction_inclusion {ρ : I → J → Prop} {q : State ρ}

    (w : Witness ρ q) (x : Space w.endpoint) :

    nativeRetraction w (nativeInclusion w x) = x

**Theorem 1.45 (nativeHomotopy_fixed).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeHomotopy_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeHomotopy_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every real unit-interval time the native collapse homotopy fixes the complete realized endpoint, including the retained whole base. The time type is explicit and distinct from the ambient label type.

### Source text

Authored Lean source header:theorem nativeHomotopy_fixed {ρ : I → J → Prop} {q : State ρ}

    (w : Witness ρ q) (t : Set.Icc (0 : ℝ) 1) (x : Space (rootK ρ q))

    (hx : x.val ∈ realization w.endpoint) :

    w.sequence.collapseHomotopy (t, x) = x

**Definition 1.46 (rootCertificate).**

Lean statement: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootCertificate`

*Formalization.* `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public structural-certificate entry point invokes the substantive original-ground constructor. It supplies no unrestricted planar pruning theorem.

### Source text

Authored Lean source header:def rootCertificate {ρ : I → J → Prop} {q : State ρ} (c : Pruning ρ q) :

    Result ρ q

The named declarations below describe the combinatorial root construction. Equal-universe mem_rootK Reg semantics do not audit recursive build, Result, critical data or native maps. The unrestricted all-plane supplier is a separate obligation. FiniteSimplexBoundarySphere and FiniteCriticalCellSphere.AttachmentSphere provide the explicit simplex boundary, disk collar, attachment quotient and based sphere constructions.

## References

- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.ColumnSubset`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.IsolatedColumn`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Pruning`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Result`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.RowSubset`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.SingletonRow`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.State`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalLaw`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.TerminalTag`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.Witness`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.augmentedTerminal`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.build`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.columnSubset_neighborhood`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseColumn_rows`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.eraseRow_active`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceDual`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.incidenceSimplex`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.isolatedCollapse`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.liftCoreToBase`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rootK`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.mem_rowNeighborhood`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeHomotopy_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeInclusion`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeRetraction_inclusion`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.nativeSDR`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootCertificate`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_column_delete`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_dual`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_row`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_empty_rows`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_full_rows`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_isolated_cone`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rootK_row_erase`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowNeighborhood`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.rowSubset_neighborhood`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.simplexCollapse`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singletonChild`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_face`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_apex_of_child_rows`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_decomposition`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.singleton_no_apex`
- Truth anchor: `D5/S3/Geometry/FiniteIncidenceRootCollapse.terminal_semantics`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteVertexDominationCollapse](FiniteVertexDominationCollapse.md)
