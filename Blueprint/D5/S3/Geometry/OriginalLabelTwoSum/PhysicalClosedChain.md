# PhysicalClosedChain

## Abstract

Literal finite K4/W4 closed chains in one ambient consume actual graph histories, exact critical and ground formulas, and both native sequences.

**Definition 1.1 (Ambient).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.Ambient`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.Ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.Ambient

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

abbrev Ambient (n ghosts : Nat) : Type

Exact source declaration and real body:

abbrev Ambient (n ghosts : Nat) : Type := PhysicalHistory.Ambient n ghosts

Mathematical content:

One common Fin(3+4*n+ghosts) for all prefixes k<=n; n counts W4 attachments.

Actual source consumers:

p, u, v, r, interface, S, first, second, tail, retained, seedLabels, orientedEdge, nextInput, next_value, build, graph, total_label_recurrence, ground_disjoint, inactive, closed_ground, original_support, critical_boundaries, apex_retained, counts, mainSchedule, separateSchedule, endpoint_formula, current_pairs, native_geometry

**Definition 1.2 (p).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.p`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.p` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.p

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def p (n ghosts : Nat) : Ambient n ghosts

Exact source declaration and real body:

def p (n ghosts : Nat) : Ambient n ghosts := ⟨0,by omega⟩

Mathematical content:

Original retained apex coordinate 0, not a chosen replacement apex.

Actual source consumers:

retained, p_ne_interface, seed_root, retained_recurrence, ground_formula, ground_disjoint, earlier_interfaces_deleted, closed_ground, vertex_formula, apex_retained, separateSchedule, separate, current_pairs, native_geometry

**Definition 1.3 (u).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.u`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.u

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def u (n ghosts : Nat) : Ambient n ghosts

Exact source declaration and real body:

def u (n ghosts : Nat) : Ambient n ghosts := ⟨1,by omega⟩

Mathematical content:

Original seed spoke 1 and initial selected interface e1.

Actual source consumers:

interface, interface_bound, p_ne_interface, interface_not_S, interface_not_second, seed_root, retained_recurrence, ground_formula, ground_disjoint, critical_formula

**Definition 1.4 (v).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.v`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.v

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def v (n ghosts : Nat) : Ambient n ghosts

Exact source declaration and real body:

def v (n ghosts : Nat) : Ambient n ghosts := ⟨2,by omega⟩

Mathematical content:

Original seed spoke 2; survives in the second literal critical face.

Actual source consumers:

second, retained, interface_not_second, seed_root, retained_recurrence, ground_formula, ground_disjoint, earlier_interfaces_deleted, critical_formula, closed_critical, closed_ground

**Definition 1.5 (r).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.r`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.r` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.r

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def r (n ghosts j : Nat) (hj : j < n) (i : Fin 4) : Ambient n ghosts

Exact source declaration and real body:

def r (n ghosts j : Nat) (hj : j < n) (i : Fin 4) : Ambient n ghosts :=

  ⟨3+4*j+i.val,by have := i.isLt; omega⟩

Mathematical content:

Source r(j,i)=mathematical r(j+1,i+1), with val=3+4*j+i.val; j<n is a finite index bound.

Actual source consumers:

interface, interface_succ, interface_bound, p_ne_interface, interface_not_S, interface_not_second, S_union, tail_union, S_succ, critical_recurrence, input_labels, future_blocks_fresh, input_Y, ground_recurrence, retained_recurrence, ground_disjoint, earlier_interfaces_deleted, closed_critical, closed_ground, path_rows, raw_root_step

**Definition 1.6 (interface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.interface`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.interface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.interface

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def interface (n ghosts k : Nat) (hk : k ≤ n) : Ambient n ghosts

Exact source declaration and real body:

def interface (n ghosts k : Nat) (hk : k ≤ n) : Ambient n ghosts :=

  if h : k = 0 then u n ghosts else r n ghosts (k-1) (by omega) 0

Mathematical content:

At k=0 select u; after k>0 select r(k-1,0), the most recent first spoke.

Actual source consumers:

first, retained, interface_succ, interface_bound, p_ne_interface, interface_not_S, interface_not_second, critical_recurrence, nextInput, next_value, build, input_labels, input_valid, ground_recurrence, retained_recurrence, ground_formula, ground_disjoint, earlier_interfaces_deleted, critical_formula, critical_sizes, path_rows, raw_root_step, mainSchedule, separateSchedule, main_schedule_handoff, separate_schedule_handoff

**Definition 1.7 (S).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.S

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def S (n ghosts k : Nat) : Finset (Ambient n ghosts)

Exact source declaration and real body:

def S (n ghosts k : Nat) : Finset (Ambient n ghosts) :=

  Finset.univ.filter (fun x => 3 ≤ x.val ∧ x.val < 3+4*k ∧

    ((x.val-3)%4 = 2 ∨ (x.val-3)%4 = 3))

Mathematical content:

Literal common critical part; S_union proves the original-label union, not just a cardinality.

Actual source consumers:

first, second, interface_not_S, S_zero, S_union, S_succ, closed_critical

**Definition 1.8 (first).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.first`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.first` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.first

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def first (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts)

Exact source declaration and real body:

def first (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts) :=

  insert (interface n ghosts k hk) (S n ghosts k)

Mathematical content:

Literal first critical face insert(interface k)(S k). Its equality with the ACTUAL certificate is proved later.

Actual source consumers:

critical_recurrence, critical_formula, closed_critical, original_support, critical_sizes, critical_boundaries, mainSchedule, separateSchedule, endpoint_formula, main, current_pairs, native_geometry

**Definition 1.9 (second).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.second`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.second

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def second (n ghosts k : Nat) : Finset (Ambient n ghosts)

Exact source declaration and real body:

def second (n ghosts k : Nat) : Finset (Ambient n ghosts) :=

  insert (v n ghosts) (S n ghosts k)

Mathematical content:

Literal second critical face insert(v)(S k), with the actual raw critical equality proved later.

Actual source consumers:

interface_not_second, critical_recurrence, critical_formula, closed_critical, original_support, critical_sizes, critical_boundaries, mainSchedule, separateSchedule, endpoint_formula, main, current_pairs, native_geometry

**Definition 1.10 (tail).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.tail

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def tail (n ghosts k : Nat) : Finset (Ambient n ghosts)

Exact source declaration and real body:

def tail (n ghosts k : Nat) : Finset (Ambient n ghosts) :=

  Finset.univ.filter (fun x => 3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0)

Mathematical content:

All earlier block offsets 1,2,3, corresponding to mathematical spoke numbers 2,3,4.

Actual source consumers:

retained, tail_union, retained_recurrence, ground_formula, ground_disjoint, earlier_interfaces_deleted, closed_ground

**Definition 1.11 (retained).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.retained`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.retained` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.retained

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def retained (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts)

Exact source declaration and real body:

def retained (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts) :=

  {p n ghosts,v n ghosts,interface n ghosts k hk} ∪ tail n ghosts k

Mathematical content:

Literal {p,v,interface k} union block tail. Actual ground equality and disjointness are derived later.

Actual source consumers:

retained_recurrence, ground_formula, earlier_interfaces_deleted, closed_ground, original_support, separateSchedule

**Theorem 1.12 (S_union).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.S_union

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem S_union (n ghosts k : Nat) (hk : k ≤ n) :

    S n ghosts k = (Finset.range k).attach.biUnion (fun j =>

      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by

  ext x

  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,

    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]

  constructor

  · intro hx

    let j := (x.val-3)/4

    have hj : j < k := by dsimp [j]; omega

    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩

    rcases hx.2.2 with h2 | h3

    · left; apply Fin.ext; dsimp [r,j]; omega

    · right; apply Fin.ext; dsimp [r,j]; omega

  · rintro ⟨j,hx | hx⟩ <;> subst x <;>

      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

Exact source declaration and real body:

theorem S_union (n ghosts k : Nat) (hk : k ≤ n) :

    S n ghosts k = (Finset.range k).attach.biUnion (fun j =>

      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by

  ext x

  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,

    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]

  constructor

  · intro hx

    let j := (x.val-3)/4

    have hj : j < k := by dsimp [j]; omega

    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩

    rcases hx.2.2 with h2 | h3

    · left; apply Fin.ext; dsimp [r,j]; omega

    · right; apply Fin.ext; dsimp [r,j]; omega

  · rintro ⟨j,hx | hx⟩ <;> subst x <;>

      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

Mathematical content:

Exact finite union over original r(j+1,3),r(j+1,4). Div/mod arithmetic proves both membership directions.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.13 (tail_union).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.tail_union

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem tail_union (n ghosts k : Nat) (hk : k ≤ n) :

    tail n ghosts k = (Finset.range k).attach.biUnion (fun j =>

      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 1,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by

  ext x

  simp only [tail,Finset.mem_filter,Finset.mem_univ,true_and,

    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]

  constructor

  · intro hx

    let j := (x.val-3)/4

    have hj : j < k := by dsimp [j]; omega

    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩

    have hm : (x.val-3)%4 = 1 ∨ (x.val-3)%4 = 2 ∨ (x.val-3)%4 = 3 := by omega

    rcases hm with h1 | h2 | h3

    · left; apply Fin.ext; dsimp [r,j]; omega

    · right; left; apply Fin.ext; dsimp [r,j]; omega

    · right; right; apply Fin.ext; dsimp [r,j]; omega

  · rintro ⟨j,hx | hx | hx⟩ <;> subst x <;>

      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

Exact source declaration and real body:

theorem tail_union (n ghosts k : Nat) (hk : k ≤ n) :

    tail n ghosts k = (Finset.range k).attach.biUnion (fun j =>

      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 1,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,

       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by

  ext x

  simp only [tail,Finset.mem_filter,Finset.mem_univ,true_and,

    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]

  constructor

  · intro hx

    let j := (x.val-3)/4

    have hj : j < k := by dsimp [j]; omega

    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩

    have hm : (x.val-3)%4 = 1 ∨ (x.val-3)%4 = 2 ∨ (x.val-3)%4 = 3 := by omega

    rcases hm with h1 | h2 | h3

    · left; apply Fin.ext; dsimp [r,j]; omega

    · right; left; apply Fin.ext; dsimp [r,j]; omega

    · right; right; apply Fin.ext; dsimp [r,j]; omega

  · rintro ⟨j,hx | hx | hx⟩ <;> subst x <;>

      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

Mathematical content:

Exact finite union over original r(j+1,2),r(j+1,3),r(j+1,4). Both directions are proved from finite values.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Definition 1.14 (build).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.build`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.build` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.build

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def build (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    Σ A : Type, Σ g : GraphData A (Ambient n ghosts),

      {h : PhysicalHistory.History k A g //

        (∀ x ∈ g.ground, x.val < 3+4*k) ∧ interface n ghosts k hk ∈ g.ground}

Exact source declaration and real body:

def build (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    Σ A : Type, Σ g : GraphData A (Ambient n ghosts),

      {h : PhysicalHistory.History k A g //

        (∀ x ∈ g.ground, x.val < 3+4*k) ∧ interface n ghosts k hk ∈ g.ground}

  | 0, hk => ⟨Fin 4,PhysicalHistory.seedGraph (seedLabels n ghosts),

      PhysicalHistory.History.seed (seedLabels n ghosts),by

        constructor

        · intro x hx

          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx

          exact i.isLt

        · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩⟩

  | k+1, hk =>

    let old := build n ghosts k (by omega)

    let g := old.2.1

    let i := nextInput g (by omega : k < n) old.2.2.2.1 old.2.2.2.2

    ⟨(PhysicalHistory.step g i).Carrier,(PhysicalHistory.step g i).data,

      PhysicalHistory.History.attach old.2.2.1 i,by

        constructor

        · intro x hx

          rcases Finset.mem_union.mp hx with hold | hnew

          · have hb := old.2.2.2.1 x (Finset.mem_of_mem_erase hold)

            omega

          · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hnew

            have ha0 : a ≠ (0 : Wheel.Label) := by

              intro h; subst a; exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) ha

            have hv := next_value g (by omega) old.2.2.2.1 old.2.2.2.2 a ha0

            have := a.isLt

            change (i.labels a).val < _

            change (i.labels a).val = _ at hv

            omega

        · rw [interface_succ]

          apply Finset.mem_union_right

          exact Finset.mem_image.mpr ⟨1,by decide,rfl⟩⟩

Mathematical content:

Substantive finite recursion: constructs G3 Input/step/History from actual K4, actual Sym2 endpoints, proved prefix bounds and retained-interface membership. No desired result is an external field or premise.

Actual source consumers:

carrier, graph, history, input, prefix_bound

**Definition 1.15 (carrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.carrier`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.carrier

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

abbrev carrier (n ghosts k : Nat) (hk : k ≤ n) : Type

Exact source declaration and real body:

abbrev carrier (n ghosts k : Nat) (hk : k ≤ n) : Type := (build n ghosts k hk).1

Mathematical content:

Projection of the genuinely constructed G3 sum carrier, with no replacement graph authority.

Actual source consumers:

graph, history, counts

**Definition 1.16 (graph).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.graph`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.graph

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

abbrev graph (n ghosts k : Nat) (hk : k ≤ n) :

    GraphData (carrier n ghosts k hk) (Ambient n ghosts)

Exact source declaration and real body:

abbrev graph (n ghosts k : Nat) (hk : k ≤ n) :

    GraphData (carrier n ghosts k hk) (Ambient n ghosts) := (build n ghosts k hk).2.1

Mathematical content:

Projection of the actual constructed GraphData, retaining its total ambient edge map and physical graph/tree.

Actual source consumers:

history, input, input_valid, prefix_bound, future_blocks_fresh, seed_root, ground_recurrence, total_label_recurrence, ground_formula, earlier_interfaces_deleted, inactive, critical_formula, closed_ground, original_support, vertex_formula, apex_retained, counts, chord_equiv, chord_equiv_left, path_rows, raw_root_step, row_handoff, main, native_geometry

**Definition 1.17 (history).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.history

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

abbrev history (n ghosts k : Nat) (hk : k ≤ n) :

    PhysicalHistory.History k (carrier n ghosts k hk) (graph n ghosts k hk)

Exact source declaration and real body:

abbrev history (n ghosts k : Nat) (hk : k ≤ n) :

    PhysicalHistory.History k (carrier n ghosts k hk) (graph n ghosts k hk) :=

  (build n ghosts k hk).2.2.1

Mathematical content:

The constructed existing G3 History, not an assumed history or row-only sequence.

Actual source consumers:

history_succ, critical_formula, closed_critical, original_support, vertex_formula, critical_sizes, critical_boundaries, apex_retained, counts, row_handoff, main_schedule_handoff, separate_schedule_handoff, endpoint_formula, main, separate, list_equations, current_pairs, native_geometry

**Definition 1.18 (input).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.input

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

abbrev input (n ghosts k : Nat) (hk : k < n) :

    PhysicalHistory.Input (graph n ghosts k (by omega))

Exact source declaration and real body:

abbrev input (n ghosts k : Nat) (hk : k < n) :

    PhysicalHistory.Input (graph n ghosts k (by omega)) :=

  nextInput (graph n ghosts k (by omega)) hk

    (build n ghosts k (by omega)).2.2.2.1 (build n ghosts k (by omega)).2.2.2.2

Mathematical content:

The very nextInput used by build; actual endpoints and finite fresh block labels come from its proved prefix.

Actual source consumers:

history_succ, input_labels, input_valid, input_Y, ground_recurrence, total_label_recurrence, critical_formula, vertex_formula, chord_equiv, chord_equiv_right, path_rows, raw_root_step, mainSchedule, separateSchedule, main_schedule_handoff, separate_schedule_handoff

**Theorem 1.19 (history_succ).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.history_succ

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem history_succ (n ghosts k : Nat) (hk : k+1 ≤ n) :

    history n ghosts (k+1) hk = PhysicalHistory.History.attach

      (history n ghosts k (by omega)) (input n ghosts k (by omega))

Exact source declaration and real body:

theorem history_succ (n ghosts k : Nat) (hk : k+1 ≤ n) :

    history n ghosts (k+1) hk = PhysicalHistory.History.attach

      (history n ghosts k (by omega)) (input n ghosts k (by omega)) := rfl

Mathematical content:

Definitional identity with G3 History.attach, so all native consumers operate on precisely this recursion.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.20 (input_labels).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.input_labels

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem input_labels (n ghosts k : Nat) (hk : k < n) :

    (input n ghosts k hk).e = interface n ghosts k (by omega) ∧

    (input n ghosts k hk).labels 0 = interface n ghosts k (by omega) ∧

    (input n ghosts k hk).labels 1 = r n ghosts k hk 0 ∧

    (input n ghosts k hk).labels 2 = r n ghosts k hk 1 ∧

    (input n ghosts k hk).labels 3 = r n ghosts k hk 2 ∧

    (input n ghosts k hk).labels 4 = r n ghosts k hk 3

Exact source declaration and real body:

theorem input_labels (n ghosts k : Nat) (hk : k < n) :

    (input n ghosts k hk).e = interface n ghosts k (by omega) ∧

    (input n ghosts k hk).labels 0 = interface n ghosts k (by omega) ∧

    (input n ghosts k hk).labels 1 = r n ghosts k hk 0 ∧

    (input n ghosts k hk).labels 2 = r n ghosts k hk 1 ∧

    (input n ghosts k hk).labels 3 = r n ghosts k hk 2 ∧

    (input n ghosts k hk).labels 4 = r n ghosts k hk 3 :=

  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

Mathematical content:

Complete local G3 label 0/1/2/3/4 to interface/r-offset translation; prevents 0/1-based ambiguity.

Actual source consumers:

input_Y, critical_formula

**Theorem 1.21 (input_valid).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.input_valid

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem input_valid (n ghosts k : Nat) (hk : k < n) :

    interface n ghosts k (by omega) ∈ (graph n ghosts k (by omega)).ground ∧

    Disjoint (graph n ghosts k (by omega)).ground

      (Wheel.Y.image (input n ghosts k hk).labels) ∧

    (graph n ghosts k (by omega)).edge (interface n ghosts k (by omega)) =

      s((input n ghosts k hk).a,(input n ghosts k hk).b)

Exact source declaration and real body:

theorem input_valid (n ghosts k : Nat) (hk : k < n) :

    interface n ghosts k (by omega) ∈ (graph n ghosts k (by omega)).ground ∧

    Disjoint (graph n ghosts k (by omega)).ground

      (Wheel.Y.image (input n ghosts k hk).labels) ∧

    (graph n ghosts k (by omega)).edge (interface n ghosts k (by omega)) =

      s((input n ghosts k hk).a,(input n ghosts k hk).b) :=

  ⟨(input n ghosts k hk).retained,(input n ghosts k hk).fresh,

    (input n ghosts k hk).edge⟩

Mathematical content:

Derived actual interface retention, fresh block disjointness, and oriented edge identity. None is a build premise.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.22 (prefix_bound).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.prefix_bound

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem prefix_bound (n ghosts k : Nat) (hk : k ≤ n) :

    ∀ x ∈ (graph n ghosts k hk).ground, x.val < 3+4*k

Exact source declaration and real body:

theorem prefix_bound (n ghosts k : Nat) (hk : k ≤ n) :

    ∀ x ∈ (graph n ghosts k hk).ground, x.val < 3+4*k :=

  (build n ghosts k hk).2.2.2.1

Mathematical content:

Constructively proved active-label bound for each prefix in the common ambient.

Actual source consumers:

future_blocks_fresh, inactive

**Theorem 1.23 (future_blocks_fresh).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.future_blocks_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.future_blocks_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.future_blocks_fresh

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem future_blocks_fresh (n ghosts k j : Nat) (hk : k ≤ n)

    (hkj : k ≤ j) (hj : j < n) (a : Fin 4) :

    r n ghosts j hj a ∉ (graph n ghosts k hk).ground

Exact source declaration and real body:

theorem future_blocks_fresh (n ghosts k j : Nat) (hk : k ≤ n)

    (hkj : k ≤ j) (hj : j < n) (a : Fin 4) :

    r n ghosts j hj a ∉ (graph n ghosts k hk).ground := by

  intro h

  have hb := prefix_bound n ghosts k hk _ h

  change 3+4*j+a.val < 3+4*k at hb

  omega

Mathematical content:

Every future block coordinate is fresh by the proved prefix bound; no external supply hypothesis.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.24 (seed_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.seed_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.seed_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.seed_root

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem seed_root (n ghosts : Nat) :

    (graph n ghosts 0 (by omega)).rows.root =

      delta {p n ghosts} ⊔ delta {u n ghosts} ⊔ delta {v n ghosts}

Exact source declaration and real body:

theorem seed_root (n ghosts : Nat) :

    (graph n ghosts 0 (by omega)).rows.root =

      delta {p n ghosts} ⊔ delta {u n ghosts} ⊔ delta {v n ghosts} :=

  PhysicalHistory.seed_root (seedLabels n ghosts)

Mathematical content:

Actual K4 path-row raw root delta(p) union delta(u) union delta(v), including raw empty.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.25 (ground_recurrence).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.ground_recurrence

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem ground_recurrence (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).ground =

      (graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)) ∪

        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3}

Exact source declaration and real body:

theorem ground_recurrence (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).ground =

      (graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)) ∪

        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} := by

  change (graph n ghosts k (by omega)).ground.erase _ ∪

    Wheel.Y.image (input n ghosts k hk).labels = _

  rw [input_Y]

Mathematical content:

Literal physical erase(interface) then union of four fresh labels, derived from the existing step authority.

Actual source consumers:

ground_formula

**Theorem 1.26 (total_label_recurrence).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.total_label_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.total_label_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.total_label_recurrence

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem total_label_recurrence (n ghosts k : Nat) (hk : k < n)

    (x : Ambient n ghosts) (hx : x ∉ Wheel.Y.image (input n ghosts k hk).labels) :

    (graph n ghosts (k+1) (by omega)).edge x =

      Sym2.map (PhysicalHistory.step (graph n ghosts k (by omega))

        (input n ghosts k hk)).qL ((graph n ghosts k (by omega)).edge x)

Exact source declaration and real body:

theorem total_label_recurrence (n ghosts k : Nat) (hk : k < n)

    (x : Ambient n ghosts) (hx : x ∉ Wheel.Y.image (input n ghosts k hk).labels) :

    (graph n ghosts (k+1) (by omega)).edge x =

      Sym2.map (PhysicalHistory.step (graph n ghosts k (by omega))

        (input n ghosts k hk)).qL ((graph n ghosts k (by omega)).edge x) := by

  change (if x ∈ Wheel.Y.image (input n ghosts k hk).labels then _ else _) = _

  exact if_neg hx

Mathematical content:

All other ambient coordinates retain their total old edge value under the actual left embedding, including physically deleted/inactive coordinates.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.27 (ground_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.ground_formula

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem ground_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (graph n ghosts k hk).ground = retained n ghosts k hk

Exact source declaration and real body:

theorem ground_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (graph n ghosts k hk).ground = retained n ghosts k hk := by

  induction k with

  | zero =>

    change Finset.univ.image (seedLabels n ghosts) = retained n ghosts 0 hk

    have hu : (Finset.univ : Finset K4.SeedLabel) = {0,1,2} := by decide

    rw [hu]

    ext x

    simp only [Finset.mem_image,Finset.mem_insert,Finset.mem_singleton,retained,

      Finset.mem_union,tail,Finset.mem_filter,Finset.mem_univ,true_and]

    constructor

    · rintro ⟨i,hi,rfl⟩

      rcases hi with rfl | rfl | rfl <;> simp [seedLabels,p,v,interface,u]

    · intro hx

      rcases hx with (hx | hx | hx) | hx

      · exact ⟨0,Or.inl rfl,hx.symm⟩

      · exact ⟨2,Or.inr (Or.inr rfl),hx.symm⟩

      · exact ⟨1,Or.inr (Or.inl rfl),hx.symm⟩

      · omega

  | succ k ih =>

    rw [ground_recurrence n ghosts k (by omega),ih (by omega)]

    exact retained_recurrence n ghosts k (by omega)

Mathematical content:

Exact retained ground at every stage, with seed and positive stages proved by induction.

Actual source consumers:

earlier_interfaces_deleted, closed_ground, original_support, separate_schedule_handoff

**Theorem 1.28 (ground_disjoint).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.ground_disjoint

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem ground_disjoint (n ghosts k : Nat) (hk : k ≤ n) :

    Disjoint ({p n ghosts,v n ghosts,interface n ghosts k hk} : Finset (Ambient n ghosts))

      (tail n ghosts k)

Exact source declaration and real body:

theorem ground_disjoint (n ghosts k : Nat) (hk : k ≤ n) :

    Disjoint ({p n ghosts,v n ghosts,interface n ghosts k hk} : Finset (Ambient n ghosts))

      (tail n ghosts k) := by

  apply Finset.disjoint_left.mpr

  intro x hx ht

  have hh : 3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0 := by simpa [tail] using ht

  simp only [Finset.mem_insert,Finset.mem_singleton] at hx

  rcases hx with rfl | rfl | rfl

  · simp [p] at hh

  · simp [v] at hh

  · by_cases h0 : k = 0

    · simp [interface,h0,u] at hh

    · simp only [interface,dif_neg h0,r] at hh

      omega

Mathematical content:

The displayed base triple and all old retained block tails form a disjoint union.

Actual source consumers:

closed_ground

**Theorem 1.29 (earlier_interfaces_deleted).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.earlier_interfaces_deleted`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.earlier_interfaces_deleted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.earlier_interfaces_deleted

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem earlier_interfaces_deleted (n ghosts k j : Nat) (hk : k ≤ n)

    (hj : j+1 < k) : r n ghosts j (by omega) 0 ∉ (graph n ghosts k hk).ground

Exact source declaration and real body:

theorem earlier_interfaces_deleted (n ghosts k j : Nat) (hk : k ≤ n)

    (hj : j+1 < k) : r n ghosts j (by omega) 0 ∉ (graph n ghosts k hk).ground := by

  rw [ground_formula]

  intro h

  simp only [retained,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h

  have hv : (r n ghosts j (by omega) 0).val = 3+4*j := rfl

  rcases h with (h | h | h) | h

  · have := congrArg Fin.val h; simp only [r,p] at this; omega

  · have := congrArg Fin.val h; simp only [r,v] at this; omega

  · have := congrArg Fin.val h

    have h0 : k ≠ 0 := by omega

    simp only [r,interface,dif_neg h0] at this

    omega

  · have hh : 3 ≤ (r n ghosts j (by omega) 0).val ∧

        (r n ghosts j (by omega) 0).val < 3+4*k ∧

        ((r n ghosts j (by omega) 0).val-3)%4 ≠ 0 := by simpa [tail] using h

    rw [hv] at hh

    omega

Mathematical content:

All r(j+1,1) before the current first spoke are physically outside retained ground, while remaining Ambient coordinates.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.30 (inactive).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.inactive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.inactive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.inactive

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem inactive (n ghosts k : Nat) (hk : k ≤ n) (x : Ambient n ghosts)

    (hx : 3+4*k ≤ x.val) :

    x ∉ (graph n ghosts k hk).ground ∧

    ∀ s ∈ (graph n ghosts k hk).rows.root, x ∉ s

Exact source declaration and real body:

theorem inactive (n ghosts k : Nat) (hk : k ≤ n) (x : Ambient n ghosts)

    (hx : 3+4*k ≤ x.val) :

    x ∉ (graph n ghosts k hk).ground ∧

    ∀ s ∈ (graph n ghosts k hk).rows.root, x ∉ s := by

  have hn : x ∉ (graph n ghosts k hk).ground := by

    intro h; have := prefix_bound n ghosts k hk x h; omega

  exact ⟨hn,fun s hs hxs => hn ((graph n ghosts k hk).rows.root_supported s hs hxs)⟩

Mathematical content:

No future/inactive/ghost coordinate occurs in retained ground or any actual raw-root face; no ambient erasure.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.31 (critical_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.critical_formula

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem critical_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (PhysicalHistory.certificate (history n ghosts k hk)).critical =

      {first n ghosts k hk,second n ghosts k}

Exact source declaration and real body:

theorem critical_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (PhysicalHistory.certificate (history n ghosts k hk)).critical =

      {first n ghosts k hk,second n ghosts k} := by

  induction k with

  | zero =>

    change (K4.seed.critical.image (fun t => t.image (seedLabels n ghosts))) = _

    simp [K4.seed,first,second,S_zero,interface,seedLabels,u,v]

  | succ k ih =>

    change (PhysicalCertificate.certificate (graph n ghosts k (by omega))

      (input n ghosts k (by omega)).e (input n ghosts k (by omega)).retained

      (input n ghosts k (by omega)).a (input n ghosts k (by omega)).b

      (input n ghosts k (by omega)).edge (input n ghosts k (by omega)).labels

      (input n ghosts k (by omega)).zero (input n ghosts k (by omega)).fresh

      (PhysicalHistory.certificate (history n ghosts k (by omega)))).critical = _

    rw [PhysicalCertificate.certificate_critical,ih (by omega)]

    simp only [Finset.image_insert,Finset.image_singleton,

      (input_labels n ghosts k (by omega)).1,

      (input_labels n ghosts k (by omega)).2.2.1,

      (input_labels n ghosts k (by omega)).2.2.2.2.1,

      (input_labels n ghosts k (by omega)).2.2.2.2.2,

      (critical_recurrence n ghosts k (by omega)).1,

      (critical_recurrence n ghosts k (by omega)).2]

Mathematical content:

Equality of the ACTUAL PhysicalHistory.certificate critical finset with the two literal faces. Each induction step consumes the real PhysicalCertificate transform.

Actual source consumers:

closed_critical, original_support, critical_sizes, critical_boundaries, main_schedule_handoff, separate_schedule_handoff, endpoint_formula

**Theorem 1.32 (closed_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.closed_critical

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem closed_critical (n ghosts k : Nat) (hk : k < n) :

    (PhysicalHistory.certificate (history n ghosts (k+1) (by omega))).critical =

      {S n ghosts (k+1) ∪ {r n ghosts k hk 0},S n ghosts (k+1) ∪ {v n ghosts}}

Exact source declaration and real body:

theorem closed_critical (n ghosts k : Nat) (hk : k < n) :

    (PhysicalHistory.certificate (history n ghosts (k+1) (by omega))).critical =

      {S n ghosts (k+1) ∪ {r n ghosts k hk 0},S n ghosts (k+1) ∪ {v n ghosts}} := by

  rw [critical_formula]

  simp only [first,second,interface_succ,Finset.union_singleton]

Mathematical content:

Positive-stage actual critical equality in exact S union singleton form on original finite values.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.33 (closed_ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.closed_ground

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem closed_ground (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).ground =

      {p n ghosts,v n ghosts,r n ghosts k hk 0} ∪ tail n ghosts (k+1) ∧

    Disjoint ({p n ghosts,v n ghosts,r n ghosts k hk 0} : Finset (Ambient n ghosts))

      (tail n ghosts (k+1))

Exact source declaration and real body:

theorem closed_ground (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).ground =

      {p n ghosts,v n ghosts,r n ghosts k hk 0} ∪ tail n ghosts (k+1) ∧

    Disjoint ({p n ghosts,v n ghosts,r n ghosts k hk 0} : Finset (Ambient n ghosts))

      (tail n ghosts (k+1)) := by

  constructor

  · rw [ground_formula]

    simp only [retained,interface_succ]

  · simpa only [interface_succ] using ground_disjoint n ghosts (k+1) (by omega)

Mathematical content:

Positive-stage actual ground {p,v,r(k+1,1)} disjoint union tail; tail_union gives its explicit original-label expansion.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.34 (original_support).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.original_support`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.original_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.original_support

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem original_support (n ghosts k : Nat) (hk : k ≤ n) :

    Supported (retained n ghosts k hk) (graph n ghosts k hk).rows.root ∧

    Supported (retained n ghosts k hk) (PhysicalHistory.certificate (history n ghosts k hk)).core ∧

    ∀ s ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),

      s ⊆ retained n ghosts k hk

Exact source declaration and real body:

theorem original_support (n ghosts k : Nat) (hk : k ≤ n) :

    Supported (retained n ghosts k hk) (graph n ghosts k hk).rows.root ∧

    Supported (retained n ghosts k hk) (PhysicalHistory.certificate (history n ghosts k hk)).core ∧

    ∀ s ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),

      s ⊆ retained n ghosts k hk := by

  have hr := (graph n ghosts k hk).rows.root_supported

  have hc := (PhysicalHistory.certificate (history n ghosts k hk)).core_supported

  have hs := (PhysicalHistory.certificate (history n ghosts k hk)).critical_supported

  rw [ground_formula] at hr hc hs

  rw [critical_formula] at hs

  exact ⟨hr,hc,hs⟩

Mathematical content:

Actual root, native core and both critical faces supported on the exact retained formula.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.35 (vertex_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.vertex_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.vertex_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.vertex_formula

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem vertex_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (PhysicalHistory.certificate (history n ghosts k hk)).vertex = p n ghosts

Exact source declaration and real body:

theorem vertex_formula (n ghosts k : Nat) (hk : k ≤ n) :

    (PhysicalHistory.certificate (history n ghosts k hk)).vertex = p n ghosts := by

  induction k with

  | zero => rfl

  | succ k ih =>

    let i := input n ghosts k (by omega)

    change (PhysicalCertificate.certificate (graph n ghosts k (by omega)) i.e i.retained

      i.a i.b i.edge i.labels i.zero i.fresh

      (PhysicalHistory.certificate (history n ghosts k (by omega)))).vertex = _

    have haway : (PhysicalHistory.certificate (history n ghosts k (by omega))).vertex ≠ i.e := by

      rw [ih (by omega)]

      exact p_ne_interface n ghosts k (by omega)

    exact (PhysicalCertificate.certificate_away_from_core

      (graph n ghosts k (by omega)) i.e i.retained i.a i.b i.edge i.labels i.zero

      i.fresh (PhysicalHistory.certificate (history n ghosts k (by omega))) haway).trans

        (ih (by omega))

Mathematical content:

Actual source identity of the computed Certificate.vertex with p; each step uses certificate_away_from_core and the proved p!=interface, not choice/proof-irrelevance identification.

Actual source consumers:

apex_retained, separate_schedule_handoff, separate

**Theorem 1.36 (critical_sizes).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_sizes`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_sizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.critical_sizes

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem critical_sizes (n ghosts k : Nat) (hk : k ≤ n) :

    first n ghosts k hk ≠ second n ghosts k ∧

    (first n ghosts k hk).card = 2*k+1 ∧ (second n ghosts k).card = 2*k+1

Exact source declaration and real body:

theorem critical_sizes (n ghosts k : Nat) (hk : k ≤ n) :

    first n ghosts k hk ≠ second n ghosts k ∧

    (first n ghosts k hk).card = 2*k+1 ∧ (second n ghosts k).card = 2*k+1 := by

  have hne : first n ghosts k hk ≠ second n ghosts k := by

    intro h

    have hi : interface n ghosts k hk ∈ first n ghosts k hk := Finset.mem_insert_self _ _

    rw [h] at hi

    exact interface_not_second n ghosts k hk hi

  have hs := (PhysicalHistory.statistics (history n ghosts k hk)).2

  rw [critical_formula] at hs

  exact ⟨hne,hs _ (by simp),hs _ (by simp)⟩

Mathematical content:

Two distinct literal critical faces, each card=2*k+1; size is consumed from the actual constructed History statistics.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.37 (critical_boundaries).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_boundaries`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.critical_boundaries

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem critical_boundaries (n ghosts k : Nat) (hk : k ≤ n)

    (s : Finset (Ambient n ghosts))

    (hs : s = first n ghosts k hk ∨ s = second n ghosts k) :

    s.Nonempty ∧ s ∉ (PhysicalHistory.certificate (history n ghosts k hk)).core ∧

    (∀ t, t ⊂ s → t ∈ (PhysicalHistory.certificate (history n ghosts k hk)).core) ∧

    delta s ⊓ (PhysicalHistory.certificate (history n ghosts k hk)).core =

      (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family (Ambient n ghosts)) ∧

    ∀ t ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),

      s ⊆ t → s = t

Exact source declaration and real body:

theorem critical_boundaries (n ghosts k : Nat) (hk : k ≤ n)

    (s : Finset (Ambient n ghosts))

    (hs : s = first n ghosts k hk ∨ s = second n ghosts k) :

    s.Nonempty ∧ s ∉ (PhysicalHistory.certificate (history n ghosts k hk)).core ∧

    (∀ t, t ⊂ s → t ∈ (PhysicalHistory.certificate (history n ghosts k hk)).core) ∧

    delta s ⊓ (PhysicalHistory.certificate (history n ghosts k hk)).core =

      (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family (Ambient n ghosts)) ∧

    ∀ t ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),

      s ⊆ t → s = t := by

  have hm : s ∈ (PhysicalHistory.certificate (history n ghosts k hk)).critical := by

    rw [critical_formula]; simpa only [Finset.mem_insert,Finset.mem_singleton] using hs

  have hb := PhysicalHistory.boundaries (history n ghosts k hk) hm

  refine ⟨hb.1,hb.2.1,?_,hb.2.2.1,?_⟩

  · exact (PhysicalHistory.certificate (history n ghosts k hk)).cells.boundary s hm

  · intro t ht hst

    exact hb.2.2.2 t (by rwa [critical_formula]) hst

Mathematical content:

Nonempty and absent faces, every proper raw subface in ACTUAL core, exact full-boundary intersection and critical antichain.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.38 (apex_retained).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.apex_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.apex_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.apex_retained

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem apex_retained (n ghosts k : Nat) (hk : k ≤ n) :

    p n ghosts ∈ (graph n ghosts k hk).ground ∧

    ({p n ghosts} : Finset (Ambient n ghosts)) ∈

      (PhysicalHistory.certificate (history n ghosts k hk)).core

Exact source declaration and real body:

theorem apex_retained (n ghosts k : Nat) (hk : k ≤ n) :

    p n ghosts ∈ (graph n ghosts k hk).ground ∧

    ({p n ghosts} : Finset (Ambient n ghosts)) ∈

      (PhysicalHistory.certificate (history n ghosts k hk)).core := by

  have hv := PhysicalHistory.survives (history n ghosts k hk)

  have hc := (PhysicalHistory.certificate (history n ghosts k hk)).vertex_mem

  rw [vertex_formula] at hv hc

  exact ⟨hv,hc⟩

Mathematical content:

p is both an actual retained graph-tree label and a vertex of the actual constructed core.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.39 (counts).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.counts`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.counts

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem counts (n ghosts k : Nat) (hk : k ≤ n) :

    Nat.card (Ambient n ghosts) = 3+4*n+ghosts ∧

    Nat.card (carrier n ghosts k hk) = 4+3*k ∧

    (graph n ghosts k hk).ground.card = 3+3*k ∧

    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).tree.edgeSet} = 3+3*k ∧

    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).graph.edgeSet} = 6+6*k

Exact source declaration and real body:

theorem counts (n ghosts k : Nat) (hk : k ≤ n) :

    Nat.card (Ambient n ghosts) = 3+4*n+ghosts ∧

    Nat.card (carrier n ghosts k hk) = 4+3*k ∧

    (graph n ghosts k hk).ground.card = 3+3*k ∧

    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).tree.edgeSet} = 3+3*k ∧

    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).graph.edgeSet} = 6+6*k := by

  refine ⟨?_,PhysicalHistory.vertex_card (history n ghosts k hk),

    PhysicalHistory.ground_card (history n ghosts k hk),

    PhysicalHistory.tree_edge_card (history n ghosts k hk),

    PhysicalHistory.graph_edge_card (history n ghosts k hk)⟩

  rw [Nat.card_eq_fintype_card,Fintype.card_fin]

Mathematical content:

Actual carrier/graph/tree/ground counts through this History: 4+3*k,6+6*k,3+3*k,3+3*k; ambient 3+4*n+ghosts. Includes zero cases.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Definition 1.40 (chord_equiv).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.chord_equiv

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def chord_equiv (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).chords ≃

      (graph n ghosts k (by omega)).chords ⊕ {d : Fin 4 // d ≠ 0}

Exact source declaration and real body:

def chord_equiv (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).chords ≃

      (graph n ghosts k (by omega)).chords ⊕ {d : Fin 4 // d ≠ 0} :=

  PhysicalCertificate.attachment_chords (graph n ghosts k (by omega))

    (input n ghosts k hk).e (input n ghosts k hk).retained

    (input n ghosts k hk).a (input n ghosts k hk).b (input n ghosts k hk).edge

    (input n ghosts k hk).labels (input n ghosts k hk).zero (input n ghosts k hk).fresh

Mathematical content:

Existing local physical-survivor equivalence, preserving every old index and all three original surviving right indices. No row-set quotient.

Actual source consumers:

chord_equiv_left, chord_equiv_right, path_rows

**Theorem 1.41 (chord_equiv_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.chord_equiv_left

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem chord_equiv_left (n ghosts k : Nat) (hk : k < n)

    (c : (graph n ghosts k (by omega)).chords) :

    chord_equiv n ghosts k hk (.inl c) = .inl c

Exact source declaration and real body:

theorem chord_equiv_left (n ghosts k : Nat) (hk : k < n)

    (c : (graph n ghosts k (by omega)).chords) :

    chord_equiv n ghosts k hk (.inl c) = .inl c := rfl

Mathematical content:

Literal identity on each inherited index, including any coincident original row presentations.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.42 (chord_equiv_right).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.chord_equiv_right

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem chord_equiv_right (n ghosts k : Nat) (hk : k < n)

    (d : (Wheel.ambientGraph (input n ghosts k hk).labels).PhysicalSurvivor (0 : Fin 4)) :

    chord_equiv n ghosts k hk (.inr d) =

      .inr ⟨d.1,fun he => d.2 (congrArg (Wheel.ambientGraph (input n ghosts k hk).labels).kappa he)⟩

Exact source declaration and real body:

theorem chord_equiv_right (n ghosts k : Nat) (hk : k < n)

    (d : (Wheel.ambientGraph (input n ghosts k hk).labels).PhysicalSurvivor (0 : Fin 4)) :

    chord_equiv n ghosts k hk (.inr d) =

      .inr ⟨d.1,fun he => d.2 (congrArg (Wheel.ambientGraph (input n ghosts k hk).labels).kappa he)⟩ := rfl

Mathematical content:

Underlying right original index is unchanged; local wheel U* alone licenses physical deletion.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.43 (path_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.path_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.path_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.path_rows

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem path_rows (n ghosts k : Nat) (hk : k < n) :

    (∀ c : (graph n ghosts k (by omega)).chords,

      (graph n ghosts (k+1) (by omega)).rows.row

        ((chord_equiv n ghosts k hk).symm (.inl c)) =

      substitute (interface n ghosts k (by omega))

        {r n ghosts k hk 0,r n ghosts k hk 1} ((graph n ghosts k (by omega)).rows.row c)) ∧

    (∀ d : {d : Fin 4 // d ≠ 0},

      (graph n ghosts (k+1) (by omega)).rows.row

        ((chord_equiv n ghosts k hk).symm (.inr d)) =

      ![{r n ghosts k hk 0,r n ghosts k hk 1},

        {r n ghosts k hk 1,r n ghosts k hk 2},

        {r n ghosts k hk 2,r n ghosts k hk 3},

        {r n ghosts k hk 3,r n ghosts k hk 0}] d.1)

Exact source declaration and real body:

theorem path_rows (n ghosts k : Nat) (hk : k < n) :

    (∀ c : (graph n ghosts k (by omega)).chords,

      (graph n ghosts (k+1) (by omega)).rows.row

        ((chord_equiv n ghosts k hk).symm (.inl c)) =

      substitute (interface n ghosts k (by omega))

        {r n ghosts k hk 0,r n ghosts k hk 1} ((graph n ghosts k (by omega)).rows.row c)) ∧

    (∀ d : {d : Fin 4 // d ≠ 0},

      (graph n ghosts (k+1) (by omega)).rows.row

        ((chord_equiv n ghosts k hk).symm (.inr d)) =

      ![{r n ghosts k hk 0,r n ghosts k hk 1},

        {r n ghosts k hk 1,r n ghosts k hk 2},

        {r n ghosts k hk 2,r n ghosts k hk 3},

        {r n ghosts k hk 3,r n ghosts k hk 0}] d.1) := by

  let g := graph n ghosts k (by omega)

  let i := input n ghosts k hk

  have h := PhysicalHistory.step_rows g i

  constructor

  · intro c

    change (PhysicalHistory.step g i).data.rows.row (.inl c) = _

    rw [h.1 c]

    have hr : Wheel.R.image i.labels = {r n ghosts k hk 0,r n ghosts k hk 1} := by

      simp only [Wheel.R,Finset.image_insert,Finset.image_singleton]

      rfl

    rw [hr]

  · intro d

    let d' : (Wheel.ambientGraph i.labels).PhysicalSurvivor (0 : Fin 4) :=

      ⟨d.1,fun he => d.2 (Wheel.ambient_uniqueInterface i.labels d.1 he)⟩

    change (PhysicalHistory.step g i).data.rows.row (.inr d') = _

    rw [h.2 d']

    have hv : ∀ j : Fin 4,

        (![{(1 : Wheel.Label),2},{2,3},{3,4},{4,1}] j).image i.labels =

          ![{r n ghosts k hk 0,r n ghosts k hk 1},

            {r n ghosts k hk 1,r n ghosts k hk 2},

            {r n ghosts k hk 2,r n ghosts k hk 3},

            {r n ghosts k hk 3,r n ghosts k hk 0}] j := by

      intro j

      fin_cases j <;> simp only [Finset.image_insert,Finset.image_singleton] <;> rfl

    exact hv d.1

Mathematical content:

Actual unique-path rows: every inherited row conditionally replaces e by {r1,r2}; original right indices append 23,34,41. Inherited order/index identity is retained.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.44 (raw_root_step).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.raw_root_step`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.raw_root_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.raw_root_step

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem raw_root_step (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).rows.root =

      parentOf ((graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)))

        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3}

        {r n ghosts k hk 2,r n ghosts k hk 3} (interface n ghosts k (by omega))

        (renameFamily (input n ghosts k hk).labels Wheel.E)

        (graph n ghosts k (by omega)).rows.root

Exact source declaration and real body:

theorem raw_root_step (n ghosts k : Nat) (hk : k < n) :

    (graph n ghosts (k+1) (by omega)).rows.root =

      parentOf ((graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)))

        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3}

        {r n ghosts k hk 2,r n ghosts k hk 3} (interface n ghosts k (by omega))

        (renameFamily (input n ghosts k hk).labels Wheel.E)

        (graph n ghosts k (by omega)).rows.root := by

  let g := graph n ghosts k (by omega)

  let i := input n ghosts k hk

  have h := PhysicalCertificate.attachment_root g i.e i.retained i.a i.b i.edge

    i.labels i.zero i.fresh

  have hz : Wheel.Z.image i.labels = {r n ghosts k hk 2,r n ghosts k hk 3} := by

    simp only [Wheel.Z,Finset.image_insert,Finset.image_singleton]; rfl

  simpa only [input_Y n ghosts k hk,hz] using h

Mathematical content:

Exact actual raw parent formula BEFORE project; it is derived from G3/G2 physical correspondence rather than assumed as a desired-root premise.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.45 (row_handoff).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.row_handoff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.row_handoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.row_handoff

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem row_handoff (n ghosts k : Nat) (hk : k ≤ n) :

    (graph n ghosts k hk).ground = (PhysicalHistory.handoff (history n ghosts k hk)).1.ground ∧

    (∀ c : (graph n ghosts k hk).chords,

      (graph n ghosts k hk).rows.row c =

        (PhysicalHistory.handoff (history n ghosts k hk)).1.row

          ((PhysicalHistory.handoff (history n ghosts k hk)).2.2.index c)) ∧

    (graph n ghosts k hk).rows.root = (PhysicalHistory.handoff (history n ghosts k hk)).1.root

Exact source declaration and real body:

theorem row_handoff (n ghosts k : Nat) (hk : k ≤ n) :

    (graph n ghosts k hk).ground = (PhysicalHistory.handoff (history n ghosts k hk)).1.ground ∧

    (∀ c : (graph n ghosts k hk).chords,

      (graph n ghosts k hk).rows.row c =

        (PhysicalHistory.handoff (history n ghosts k hk)).1.row

          ((PhysicalHistory.handoff (history n ghosts k hk)).2.2.index c)) ∧

    (graph n ghosts k hk).rows.root = (PhysicalHistory.handoff (history n ghosts k hk)).1.root :=

  ⟨(PhysicalHistory.handoff (history n ghosts k hk)).2.2.ground,

    (PhysicalHistory.handoff (history n ghosts k hk)).2.2.row,

    PhysicalHistory.root_handoff (history n ghosts k hk)⟩

Mathematical content:

Actual ground, every indexed row and RAW root agree with the existing G3 handoff RowHistory, with explicit index correspondence.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Definition 1.46 (mainSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.mainSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.mainSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.mainSchedule

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def mainSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))

Exact source declaration and real body:

def mainSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))

  | 0, _ => []

  | k+1, hk => WheelSupplier.oneStepMainFrom (interface n ghosts k (by omega))

      (input n ghosts k (by omega)).labels {first n ghosts k (by omega),second n ghosts k}

      (mainSchedule n ghosts k (by omega))

Mathematical content:

Independent seed-empty closed-chain enumeration through the existing oneStepMainFrom. Retains actual chosen Gamma, fibre ordering and original local filling mechanism.

Actual source consumers:

main_schedule_handoff, list_equations

**Definition 1.47 (separateSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separateSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separateSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.separateSchedule

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def separateSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))

Exact source declaration and real body:

def separateSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →

    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))

  | 0, _ => []

  | k+1, hk => WheelSupplier.oneStepSeparateFrom

      ((retained n ghosts k (by omega)).erase (interface n ghosts k (by omega)))

      (interface n ghosts k (by omega)) (input n ghosts k (by omega)).labels

      {first n ghosts k (by omega),second n ghosts k} (p n ghosts)

      (separateSchedule n ghosts k (by omega))

Mathematical content:

Independent seed-empty separate enumeration: standalone collars, previous core replay, actual full-ground terminal at p. No collar is applied to the whole main endpoint.

Actual source consumers:

separate_schedule_handoff, list_equations

**Definition 1.48 (main).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.main`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.main` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.main

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def main (n ghosts k : Nat) (hk : k ≤ n) :

    Sequence (project (graph n ghosts k hk).rows.root)

      (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k)))

Exact source declaration and real body:

def main (n ghosts k : Nat) (hk : k ≤ n) :

    Sequence (project (graph n ghosts k hk).rows.root)

      (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))) :=

  (PhysicalHistory.certificate (history n ghosts k hk)).main.cast rfl

    (congrArg project (endpoint_formula n ghosts k hk))

Mathematical content:

ACTUAL G3 native main Sequence, with only the proved equality cast to core union its two literal critical simplices. No abstract sphere or zero attachment.

Actual source consumers:

list_equations, current_pairs, native_geometry

**Definition 1.49 (separate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.separate

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

def separate (n ghosts k : Nat) (hk : k ≤ n) :

    Sequence (project (PhysicalHistory.certificate (history n ghosts k hk)).core)

      (project (delta {p n ghosts}))

Exact source declaration and real body:

def separate (n ghosts k : Nat) (hk : k ≤ n) :

    Sequence (project (PhysicalHistory.certificate (history n ghosts k hk)).core)

      (project (delta {p n ghosts})) :=

  (PhysicalHistory.certificate (history n ghosts k hk)).separate.cast rfl

    (by rw [vertex_formula])

Mathematical content:

ACTUAL G3 separate Sequence on core ALONE to delta(p), via the proved source vertex identity.

Actual source consumers:

list_equations, current_pairs, native_geometry

**Theorem 1.50 (list_equations).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.list_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.list_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.list_equations

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem list_equations (n ghosts k : Nat) (hk : k ≤ n) :

    orderedPairs (main n ghosts k hk) = mainSchedule n ghosts k hk ∧

    orderedPairs (separate n ghosts k hk) = separateSchedule n ghosts k hk

Exact source declaration and real body:

theorem list_equations (n ghosts k : Nat) (hk : k ≤ n) :

    orderedPairs (main n ghosts k hk) = mainSchedule n ghosts k hk ∧

    orderedPairs (separate n ghosts k hk) = separateSchedule n ghosts k hk := by

  constructor

  · rw [main,orderedPairs_cast]

    exact (PhysicalHistory.main_order (history n ghosts k hk)).trans

      (main_schedule_handoff n ghosts k hk)

  · rw [separate,orderedPairs_cast]

    exact (PhysicalHistory.separate_order (history n ghosts k hk)).trans

      (separate_schedule_handoff n ghosts k hk)

Mathematical content:

Exact independent list equations via G3 main_order/separate_order and proved handoff recursions; cast preserves each ordered native pair.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.51 (current_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.current_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.current_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.current_pairs

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem current_pairs (n ghosts k : Nat) (hk : k ≤ n) :

    (∀ P ∈ (main n ghosts k hk).pairs, P.lower.Nonempty ∧

      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧

      project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k)) ≤ P.retained) ∧

    (∀ P ∈ (separate n ghosts k hk).pairs, P.lower.Nonempty ∧

      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧

      project (delta {p n ghosts}) ≤ P.retained)

Exact source declaration and real body:

theorem current_pairs (n ghosts k : Nat) (hk : k ≤ n) :

    (∀ P ∈ (main n ghosts k hk).pairs, P.lower.Nonempty ∧

      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧

      project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k)) ≤ P.retained) ∧

    (∀ P ∈ (separate n ghosts k hk).pairs, P.lower.Nonempty ∧

      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧

      project (delta {p n ghosts}) ≤ P.retained) := by

  have hc (P : CollapsePair (Ambient n ghosts)) :

      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper := by

    intro s hs hsub

    by_cases he : s = P.lower

    · exact Or.inl he

    · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,Ne.symm he⟩))

  exact ⟨fun P hP => ⟨P.lower_nonempty,hc P,(main n ghosts k hk).final_le_each_retained hP⟩,

    fun P hP => ⟨P.lower_nonempty,hc P,(separate n ghosts k hk).final_le_each_retained hP⟩⟩

Mathematical content:

Every emitted actual CollapsePair has nonempty lower, exactly the two current cofaces and the entire literal final endpoint in its retained complex.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

**Theorem 1.52 (native_geometry).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.native_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.native_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain.native_geometry

Complete public SOURCE telescope (all module parameters are explicit; not elaborated metadata):

theorem native_geometry (n ghosts k : Nat) (hk : k ≤ n) :

    (∀ (t : unitInterval) (x : Space (project (graph n ghosts k hk).rows.root)),

      x.val ∈ realization (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))) →

      ∀ a : Ambient n ghosts, ((main n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧

    (∀ (t : unitInterval) (x : Space (project (PhysicalHistory.certificate (history n ghosts k hk)).core)),

      x.val ∈ realization (project (delta {p n ghosts})) →

      ∀ a : Ambient n ghosts, ((separate n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧

    (∀ y : Space (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))),

      (main n ghosts k hk).sequenceRetraction ((main n ghosts k hk).inclusion y) = y) ∧

    (∀ z : Space (project (delta {p n ghosts})),

      (separate n ghosts k hk).sequenceRetraction ((separate n ghosts k hk).inclusion z) = z)

Exact source declaration and real body:

theorem native_geometry (n ghosts k : Nat) (hk : k ≤ n) :

    (∀ (t : unitInterval) (x : Space (project (graph n ghosts k hk).rows.root)),

      x.val ∈ realization (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))) →

      ∀ a : Ambient n ghosts, ((main n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧

    (∀ (t : unitInterval) (x : Space (project (PhysicalHistory.certificate (history n ghosts k hk)).core)),

      x.val ∈ realization (project (delta {p n ghosts})) →

      ∀ a : Ambient n ghosts, ((separate n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧

    (∀ y : Space (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))),

      (main n ghosts k hk).sequenceRetraction ((main n ghosts k hk).inclusion y) = y) ∧

    (∀ z : Space (project (delta {p n ghosts})),

      (separate n ghosts k hk).sequenceRetraction ((separate n ghosts k hk).inclusion z) = z) := by

  refine ⟨?_,?_,?_,?_⟩

  · intro t x hx a

    exact congrArg (fun y : Space (project (graph n ghosts k hk).rows.root) => y.val a)

      ((main n ghosts k hk).collapseHomotopy_fixed t x hx)

  · intro t x hx a

    exact congrArg (fun y : Space (project (PhysicalHistory.certificate (history n ghosts k hk)).core) => y.val a)

      ((separate n ghosts k hk).collapseHomotopy_fixed t x hx)

  · exact fun y => (main n ghosts k hk).sequenceRetraction_inclusion y

  · exact fun z => (separate n ghosts k hk).sequenceRetraction_inclusion z

Mathematical content:

Existing native homotopies fix all ORIGINAL ambient coordinates on their respective full endpoints, and actual sequenceRetraction/inclusion composites are identities. Separate source remains core alone.

Actual source consumers:

Exported C1 endpoint; no further in-file consumer is asserted.

## Source text

Private implementation bodies are included in full; none assumes a requested output.

private def seedLabels (n ghosts : Nat) : K4.SeedLabel ↪ Ambient n ghosts where

  toFun i := ⟨i.val,by have := i.isLt; omega⟩

  inj' := by intro a b h; exact Fin.ext (congrArg Fin.val h)

Actual consumers: build, seed_root, ground_formula, critical_formula

Definitions and proofs are in the paired Lean module.

private theorem interface_succ (n ghosts k : Nat) (hk : k+1 ≤ n) :

    interface n ghosts (k+1) hk = r n ghosts k (by omega) 0 := by

  simp [interface]

Actual consumers: critical_recurrence, build, retained_recurrence, closed_critical, closed_ground

Definitions and proofs are in the paired Lean module.

private theorem interface_bound (n ghosts k : Nat) (hk : k ≤ n) :

    (interface n ghosts k hk).val < 3+4*k := by

  by_cases h : k = 0

  · subst k; simp [interface,u]

  · simp only [interface,dif_neg h,r]

    omega

Actual consumers: retained_recurrence

Definitions and proofs are in the paired Lean module.

private theorem p_ne_interface (n ghosts k : Nat) (hk : k ≤ n) :

    p n ghosts ≠ interface n ghosts k hk := by

  intro h

  have hv := congrArg Fin.val h

  by_cases h0 : k = 0

  · simp [interface,h0,p,u] at hv

  · simp only [interface,dif_neg h0,p,r] at hv

    omega

Actual consumers: retained_recurrence, vertex_formula

Definitions and proofs are in the paired Lean module.

private theorem interface_not_S (n ghosts k : Nat) (hk : k ≤ n) :

    interface n ghosts k hk ∉ S n ghosts k := by

  intro h

  have hval : 3 ≤ (interface n ghosts k hk).val ∧

      (interface n ghosts k hk).val < 3+4*k ∧

      (((interface n ghosts k hk).val-3)%4 = 2 ∨

        ((interface n ghosts k hk).val-3)%4 = 3) := by simpa [S] using h

  by_cases h0 : k = 0

  · simp [interface,h0,u] at hval

  · simp only [interface,dif_neg h0,r] at hval

    omega

Actual consumers: interface_not_second, critical_recurrence

Definitions and proofs are in the paired Lean module.

private theorem interface_not_second (n ghosts k : Nat) (hk : k ≤ n) :

    interface n ghosts k hk ∉ second n ghosts k := by

  have hne : interface n ghosts k hk ≠ v n ghosts := by

    intro he

    have hv := congrArg Fin.val he

    by_cases h0 : k = 0

    · simp [interface,h0,u,v] at hv

    · simp only [interface,dif_neg h0,r,v] at hv

      omega

  simp only [second,Finset.mem_insert,not_or]

  exact ⟨hne,interface_not_S n ghosts k hk⟩

Actual consumers: critical_recurrence, retained_recurrence, critical_sizes

Definitions and proofs are in the paired Lean module.

private theorem S_zero (n ghosts : Nat) : S n ghosts 0 = ∅ := by

  ext x

  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.not_mem_empty] <;> omega

Actual consumers: critical_formula

Definitions and proofs are in the paired Lean module.

private theorem S_succ (n ghosts k : Nat) (hk : k < n) :

    S n ghosts (k+1) = S n ghosts k ∪ {r n ghosts k hk 2,r n ghosts k hk 3} := by

  ext x

  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,

    Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,r]

  omega

Actual consumers: critical_recurrence

Definitions and proofs are in the paired Lean module.

private theorem critical_recurrence (n ghosts k : Nat) (hk : k < n) :

    wheelCell (interface n ghosts k (by omega)) (r n ghosts k hk 0)

        (r n ghosts k hk 2) (r n ghosts k hk 3) (first n ghosts k (by omega)) =

      first n ghosts (k+1) (by omega) ∧

    wheelCell (interface n ghosts k (by omega)) (r n ghosts k hk 0)

        (r n ghosts k hk 2) (r n ghosts k hk 3) (second n ghosts k) =

      second n ghosts (k+1) := by

  constructor

  · simp only [first,wheelCell,Finset.mem_insert_self,if_pos,

      Finset.erase_insert (interface_not_S n ghosts k (by omega)),S_succ n ghosts k hk,

      interface_succ]

    ext x

    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]

    tauto

  · simp only [wheelCell,if_neg (interface_not_second n ghosts k (by omega)),

      second,S_succ n ghosts k hk]

    ext x

    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]

    tauto

Actual consumers: critical_formula

Definitions and proofs are in the paired Lean module.

private def orientedEdge {A : Type} {n ghosts : Nat}

    (g : GraphData A (Ambient n ghosts)) (e : Ambient n ghosts) :

    {ab : A × A // g.edge e = s(ab.1,ab.2)} := by

  have hex : ∃ a b : A, g.edge e = s(a,b) := by

    have all : ∀ d : Sym2 A, ∃ a b : A, d = s(a,b) := by

      apply Sym2.ind

      intro a b

      exact ⟨a,b,rfl⟩

    exact all (g.edge e)

  let a := Classical.choose hex

  let hb := Classical.choose_spec hex

  exact ⟨(a,Classical.choose hb),Classical.choose_spec hb⟩

Actual consumers: nextInput

Definitions and proofs are in the paired Lean module.

private def nextInput {A : Type} {n ghosts k : Nat}

    (g : GraphData A (Ambient n ghosts)) (hk : k < n)

    (bound : ∀ x ∈ g.ground, x.val < 3+4*k)

    (he : interface n ghosts k (by omega) ∈ g.ground) : PhysicalHistory.Input g :=

  let ab := orientedEdge g (interface n ghosts k (by omega))

  PhysicalHistory.blockInput g hk bound (interface n ghosts k (by omega)) he

    ab.1.1 ab.1.2 ab.2

Actual consumers: next_value, build, input

Definitions and proofs are in the paired Lean module.

private theorem next_value {A : Type} {n ghosts k : Nat}

    (g : GraphData A (Ambient n ghosts)) (hk : k < n)

    (bound : ∀ x ∈ g.ground, x.val < 3+4*k)

    (he : interface n ghosts k (by omega) ∈ g.ground)

    (i : Wheel.Label) (hi : i ≠ 0) :

    ((nextInput g hk bound he).labels i).val = 3+4*k+(i.val-1) := by

  change (if i = 0 then interface n ghosts k (by omega)

    else (⟨3+4*k+(i.val-1),by have := i.isLt; omega⟩ : Ambient n ghosts)).val = _

  rw [if_neg hi]

Actual consumers: build

Definitions and proofs are in the paired Lean module.

private theorem input_Y (n ghosts k : Nat) (hk : k < n) :

    Wheel.Y.image (input n ghosts k hk).labels =

      {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} := by

  simp only [Wheel.Y,Finset.image_insert,Finset.image_singleton,

    (input_labels n ghosts k hk).2.2.1,(input_labels n ghosts k hk).2.2.2.1,

    (input_labels n ghosts k hk).2.2.2.2.1,(input_labels n ghosts k hk).2.2.2.2.2]

Actual consumers: ground_recurrence, raw_root_step

Definitions and proofs are in the paired Lean module.

private theorem retained_recurrence (n ghosts k : Nat) (hk : k < n) :

    (retained n ghosts k (by omega)).erase (interface n ghosts k (by omega)) ∪

        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} =

      retained n ghosts (k+1) (by omega) := by

  have hp := p_ne_interface n ghosts k (by omega)

  have heT : interface n ghosts k (by omega) ∉ tail n ghosts k := by

    intro h

    have hh : 3 ≤ (interface n ghosts k (by omega)).val ∧

        (interface n ghosts k (by omega)).val < 3+4*k ∧

        ((interface n ghosts k (by omega)).val-3)%4 ≠ 0 := by simpa [tail] using h

    by_cases h0 : k = 0

    · simp [interface,h0,u] at hh

    · simp only [interface,dif_neg h0,r] at hh

      omega

  have hev : v n ghosts ≠ interface n ghosts k (by omega) := by

    intro h

    exact interface_not_second n ghosts k (by omega)

      (Finset.mem_insert.mpr (Or.inl h.symm))

  ext x

  simp only [retained,Finset.mem_union,Finset.mem_erase,Finset.mem_insert,

    Finset.mem_singleton,tail,Finset.mem_filter,Finset.mem_univ,true_and,interface_succ]

  have hxI := interface_bound n ghosts k (by omega)

  have hnT : x = interface n ghosts k (by omega) →

      ¬ (3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0) := by

    rintro rfl; simpa [tail] using heT

  have hpI : x = p n ghosts → x ≠ interface n ghosts k (by omega) := by

    rintro rfl; exact hp

  have hvI : x = v n ghosts → x ≠ interface n ghosts k (by omega) := by

    rintro rfl; exact hev

  simp only [Fin.ext_iff,p,v,r] at *

  omega

Actual consumers: ground_formula

Definitions and proofs are in the paired Lean module.

private theorem main_schedule_handoff (n ghosts k : Nat) (hk : k ≤ n) :

    rowHistoryMainSchedule (PhysicalHistory.handoff (history n ghosts k hk)).2.1 =

      mainSchedule n ghosts k hk := by

  induction k with

  | zero => rfl

  | succ k ih =>

    change WheelSupplier.oneStepMainFrom (interface n ghosts k (by omega))

      (input n ghosts k (by omega)).labels

      (rowHistoryCriticalSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)

      (rowHistoryMainSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1) = _

    rw [← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).1,

      critical_formula,ih (by omega)]

    rfl

Actual consumers: list_equations

Definitions and proofs are in the paired Lean module.

private theorem separate_schedule_handoff (n ghosts k : Nat) (hk : k ≤ n) :

    rowHistorySeparateSchedule (PhysicalHistory.handoff (history n ghosts k hk)).2.1 =

      separateSchedule n ghosts k hk := by

  induction k with

  | zero => rfl

  | succ k ih =>

    change WheelSupplier.oneStepSeparateFrom

      ((PhysicalHistory.handoff (history n ghosts k (by omega))).1.ground.erase

        (interface n ghosts k (by omega)))

      (interface n ghosts k (by omega)) (input n ghosts k (by omega)).labels

      (rowHistoryCriticalSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)

      (rowHistoryVertexSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)

      (rowHistorySeparateSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1) = _

    rw [← (PhysicalHistory.handoff (history n ghosts k (by omega))).2.2.ground,

      ground_formula,← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).1,

      critical_formula,← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).2,

      vertex_formula,ih (by omega)]

    rfl

Actual consumers: list_equations

Definitions and proofs are in the paired Lean module.

private theorem endpoint_formula (n ghosts k : Nat) (hk : k ≤ n) :

    endpoint (PhysicalHistory.certificate (history n ghosts k hk)).core

      (PhysicalHistory.certificate (history n ghosts k hk)).critical =

      (PhysicalHistory.certificate (history n ghosts k hk)).core ⊔

        delta (first n ghosts k hk) ⊔ delta (second n ghosts k) := by

  rw [critical_formula]

  apply SetLike.ext

  intro s

  change (s ∈ (PhysicalHistory.certificate (history n ghosts k hk)).core ∨

    ∃ a ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))), s ⊆ a) ↔ _

  simp only [Finset.mem_insert,Finset.mem_singleton,LowerSet.mem_sup_iff,delta,LowerSet.mem_mk]

  aesop

Actual consumers: main

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.Ambient`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.S_union`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.apex_retained`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.build`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.carrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.chord_equiv_right`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.closed_ground`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.counts`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_boundaries`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.critical_sizes`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.current_pairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.earlier_interfaces_deleted`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.first`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.future_blocks_fresh`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.graph`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_disjoint`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.ground_recurrence`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.history_succ`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.inactive`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_labels`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.input_valid`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.interface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.list_equations`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.main`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.mainSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.native_geometry`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.original_support`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.p`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.path_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.prefix_bound`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.r`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.raw_root_step`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.retained`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.row_handoff`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.second`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.seed_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.separateSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.tail_union`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.total_label_recurrence`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.u`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.v`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain.vertex_formula`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory](PhysicalHistory.md)
