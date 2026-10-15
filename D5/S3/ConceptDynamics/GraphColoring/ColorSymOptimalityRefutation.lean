/- GID: D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation.claim
   digest: A colorable K4 list assignment defeats every ColorSym execution. -/

/-
result
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#16679; Refuted)
  Direct frozen dependencies: none

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The list carrier is written directly as Fin n → Finset ℤ, and the algorithm
state uses the existing product of output and load functions.
The definitions and claim retain the expressions of #16679.
Paper vertices 1, 2, 3, 4 are represented by Fin 4 values 0, 1, 2, 3.
The load recursion forgets the chosen colors. Induction on the pool size
proves that every admissible choice has the same loads, and a second invariant
identifies loads with output cardinalities. This yields three colors at
vertex 2 for every admissible order and pick, despite an explicit 4-coloring.

Private predicate definitions (their compiled telescope types are not propositions):
  Coherent: used by runPool_coherent, afterPair_coherent, afterTriple_coherent
  Fresh: used by assign_coherent, assign_fresh, runPool_coherent

Private theorem classification (each has direct frozen dependencies: none;
escape_witness: none):
  witness_cards: bind-only; consumer: result
  witness_coloring: bind-only; consumer: witness_colorable
  witness_colorable: bind-only; consumer: result
  witness_atoms: bind-only; consumer: inactive_atom
  inactive_atom: bind-only; consumer: run_filter
  run_filter: content; consumer: run_reduction
  active_card_injective: bind-only; consumer: forced_order
  forced_order: bind-only; consumer: run_reduction
  runPool_w: content; consumers: afterPair_w, afterTriple_w
  assign_coherent: bind-only; consumer: runPool_coherent
  assign_fresh: bind-only; consumer: runPool_coherent
  runPool_coherent: content; consumers: afterPair_coherent, afterTriple_coherent
  runPool_subset: content; consumer: afterTriple_coherent
  initial_w: bind-only; consumer: afterPair_w
  pair_loads: bind-only; consumer: afterPair_w
  triple_loads: bind-only; consumer: afterTriple_w
  afterPair_w: content; consumer: afterTriple_w
  afterTriple_w: content; consumer: every_run_card
  afterPair_coherent: content; consumer: afterTriple_coherent
  afterTriple_coherent: content; consumer: every_run_card
  run_reduction: content; consumer: every_run_card
  every_run_card: content; consumer: no_output_coloring
  no_output_coloring: content; consumer: result
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.ColorSymOptimalityRefutation

def supp {n : ℕ} (L : (Fin n → Finset ℤ)) (c : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c ∈ L i)

def Ip {n : ℕ} (L : (Fin n → Finset ℤ)) (S : Finset (Fin n)) : Finset ℤ :=
  (Finset.univ.biUnion L).filter (fun c => supp L c = S)

def IsColoring {n : ℕ} (L : (Fin n → Finset ℤ)) (b : ℕ) (φ : (Fin n → Finset ℤ)) : Prop :=
  (∀ i, φ i ⊆ L i ∧ (φ i).card = b) ∧
    ∀ i j, i ≠ j → Disjoint (φ i) (φ j)

def Colorable {n : ℕ} (L : (Fin n → Finset ℤ)) (b : ℕ) : Prop :=
  ∃ φ, IsColoring L b φ

def AdmissibleOrder {n : ℕ} (ord : List (Finset (Fin n))) : Prop :=
  ord.Nodup ∧ (∀ S, S ∈ ord ↔ 2 ≤ S.card) ∧
    ord.Pairwise (fun S T => S.card ≤ T.card)

def AdmissiblePick (pick : Finset ℤ → ℤ) : Prop :=
  ∀ s, s.Nonempty → pick s ∈ s

-- Finset.sort uses ascending vertex index; filter retains exactly minimum loads.
def best {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℕ) : Option (Fin n) :=
  match (S.filter (fun i => ∀ j ∈ S, w i ≤ w j)).sort with
  | [] => none
  | j :: _ => some j

def stopped {n : ℕ} (b : ℕ) (st : ((Fin n → Finset ℤ) × (Fin n → ℕ))) : Bool :=
  decide (∀ j, b ≤ st.2 j)

def assign {n : ℕ} (st : ((Fin n → Finset ℤ) × (Fin n → ℕ))) (j : Fin n) (c : ℤ) :
    ((Fin n → Finset ℤ) × (Fin n → ℕ)) :=
  ⟨Function.update st.1 j (insert c (st.1 j)),
    Function.update st.2 j (st.2 j + 1)⟩

def runPool {n : ℕ} (S : Finset (Fin n)) (b : ℕ) (pick : Finset ℤ → ℤ) :
    ℕ → Finset ℤ → ((Fin n → Finset ℤ) × (Fin n → ℕ)) → ((Fin n → Finset ℤ) × (Fin n → ℕ))
  | 0, _, st => st
  | fuel + 1, pool, st =>
    if stopped b st then st
    else if pool = ∅ then st
    else match best S st.2 with
      | none => st
      | some j =>
        let c := pick pool
        runPool S b pick fuel (pool.erase c) (assign st j c)

def runSupports {n : ℕ} (L : (Fin n → Finset ℤ)) (b : ℕ) (pick : Finset ℤ → ℤ) :
    List (Finset (Fin n)) → ((Fin n → Finset ℤ) × (Fin n → ℕ)) → ((Fin n → Finset ℤ) × (Fin n → ℕ))
  | [], st => st
  | S :: ord, st =>
    runSupports L b pick ord (runPool S b pick (Ip L S).card (Ip L S) st)

def initial {n : ℕ} (L : (Fin n → Finset ℤ)) : ((Fin n → Finset ℤ) × (Fin n → ℕ)) :=
  ⟨fun i => Ip L {i}, fun i => (Ip L {i}).card⟩

def colorSym {n : ℕ} (L : (Fin n → Finset ℤ)) (b : ℕ)
    (ord : List (Finset (Fin n))) (pick : Finset ℤ → ℤ) : (Fin n → Finset ℤ) :=
  (runSupports L b pick ord (initial L)).1

def claim : Prop :=
  ∀ (n a b : ℕ) (L : (Fin n → Finset ℤ)),
    (∀ i, (L i).card = a) → Colorable L b →
    ∃ ord pick, AdmissibleOrder ord ∧ AdmissiblePick pick ∧
      ∃ φ, IsColoring L b φ ∧ ∀ i, φ i ⊆ colorSym L b ord pick i

-- Paper vertices 1,2,3,4 correspond to Fin values 0,1,2,3.
private def witness : (Fin 4 → Finset ℤ) :=
  ![{1,2,3,4,5,6}, {1,2,3,4,7,8}, {5,6,9,10,11,12}, {5,6,13,14,15,16}]

private def phi : (Fin 4 → Finset ℤ) :=
  ![{1,2,5,6}, {3,4,7,8}, {9,10,11,12}, {13,14,15,16}]

private def pair : Finset (Fin 4) := {0,1}
private def triple : Finset (Fin 4) := {0,2,3}

private theorem witness_cards : ∀ i, (witness i).card = 6 := by decide +kernel

private theorem witness_coloring : IsColoring witness 4 phi := by
  unfold IsColoring
  decide +kernel

private theorem witness_colorable : Colorable witness 4 := ⟨phi, witness_coloring⟩

private theorem witness_atoms : ∀ S : Finset (Fin 4),
    Ip witness S =
      if S = pair then {1,2,3,4}
      else if S = triple then {5,6}
      else if S = {1} then {7,8}
      else if S = {2} then {9,10,11,12}
      else if S = {3} then {13,14,15,16}
      else ∅ := by decide +kernel

private def active (S : Finset (Fin 4)) : Bool := decide (S = pair ∨ S = triple)

private theorem inactive_atom : ∀ S : Finset (Fin 4),
    2 ≤ S.card → active S = false → Ip witness S = ∅ := by
  intro S hc ha
  have hn : S ≠ pair ∧ S ≠ triple := by simpa [active, not_or] using ha
  have h1 : S ≠ {1} := by intro h; subst S; simp at hc
  have h2 : S ≠ {2} := by intro h; subst S; simp at hc
  have h3 : S ≠ {3} := by intro h; subst S; simp at hc
  simp only [witness_atoms, if_neg hn.1, if_neg hn.2,
    if_neg h1, if_neg h2, if_neg h3]

private theorem run_filter (ord : List (Finset (Fin 4))) (b : ℕ) (pick : Finset ℤ → ℤ)
    (hord : ∀ S ∈ ord, 2 ≤ S.card) (st : ((Fin 4 → Finset ℤ) × (Fin 4 → ℕ))) :
    runSupports witness b pick ord st =
      runSupports witness b pick (ord.filter active) st := by
  induction ord generalizing st with
  | nil => rfl
  | cons S ord ih =>
    have hS := hord S (by simp)
    have ht : ∀ T ∈ ord, 2 ≤ T.card := fun T hT => hord T (by simp [hT])
    cases h : active S with
    | false =>
      have he := inactive_atom S hS h
      simpa [runSupports, h, he, runPool] using ih ht st
    | true =>
      simpa [runSupports, h] using
        ih ht (runPool S b pick (Ip witness S).card (Ip witness S) st)

private theorem active_card_injective : ∀ S T : Finset (Fin 4),
    active S = true → active T = true → S.card ≤ T.card → T.card ≤ S.card → S = T := by
  decide +kernel

private theorem forced_order (ord : List (Finset (Fin 4))) (hord : AdmissibleOrder ord) :
    ord.filter active = [pair, triple] := by
  have hm : ∀ S, S ∈ ord.filter active ↔ S ∈ [pair, triple] := by
    intro S
    simp only [List.mem_filter, active, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨(hord.2.1 S).mpr ?_, h⟩
      rcases h with rfl | rfl <;> decide +kernel
  have hp : (ord.filter active).Perm [pair, triple] :=
    (List.perm_ext_iff_of_nodup (hord.1.filter active) (by decide +kernel)).mpr hm
  apply List.Perm.eq_of_pairwise (le := fun S T => S.card ≤ T.card) ?_
    (hord.2.2.filter active) (by decide +kernel) hp
  intro S T hS hT hST hTS
  exact active_card_injective S T (List.mem_filter.mp hS).2
    (List.mem_filter.mp ((hm T).mpr hT)).2 hST hTS

private def loadPool {n : ℕ} (S : Finset (Fin n)) (b : ℕ) : ℕ → (Fin n → ℕ) → (Fin n → ℕ)
  | 0, w => w
  | fuel + 1, w =>
    if (∀ j, b ≤ w j) then w
    else match best S w with
      | none => w
      | some j => loadPool S b fuel (Function.update w j (w j + 1))

private theorem runPool_w {n : ℕ} (S : Finset (Fin n)) (b : ℕ) (pick : Finset ℤ → ℤ)
    (hp : AdmissiblePick pick) (fuel : ℕ) (pool : Finset ℤ)
    (st : ((Fin n → Finset ℤ) × (Fin n → ℕ)))
    (hc : pool.card = fuel) :
    (runPool S b pick fuel pool st).2 = loadPool S b fuel st.2 := by
  induction fuel generalizing pool st with
  | zero => rfl
  | succ k ih =>
    have hne : pool ≠ ∅ := by intro he; simp [he] at hc
    have hm : pick pool ∈ pool := hp pool (Finset.nonempty_iff_ne_empty.mpr hne)
    have he : (pool.erase (pick pool)).card = k := by
      rw [Finset.card_erase_of_mem hm, hc]
      omega
    simp only [runPool, loadPool, stopped, decide_eq_true_eq, hne, ↓reduceIte]
    split
    · rfl
    · cases hb : best S st.2 with
      | none => simp
      | some j =>
          simpa [hb, assign] using
            (ih (pool.erase (pick pool)) (assign st j (pick pool)) he)

private def Coherent {n : ℕ} (st : ((Fin n → Finset ℤ) × (Fin n → ℕ))) : Prop :=
  ∀ i, (st.1 i).card = st.2 i

private def Fresh {n : ℕ} (pool : Finset ℤ) (st : ((Fin n → Finset ℤ) × (Fin n → ℕ))) : Prop :=
  ∀ i, Disjoint pool (st.1 i)

private theorem assign_coherent {n : ℕ} (pool : Finset ℤ) (st : ((Fin n → Finset ℤ) × (Fin n → ℕ)))
    (j : Fin n) (c : ℤ)
    (hc : Coherent st) (hf : Fresh pool st) (hm : c ∈ pool) : Coherent (assign st j c) := by
  intro i
  by_cases hij : i = j
  · subst i
    have hnot : c ∉ st.1 j := Finset.disjoint_left.mp (hf j) hm
    simp [assign, Finset.card_insert_of_notMem hnot, hc j]
  · simp [assign, hij, hc i]

private theorem assign_fresh {n : ℕ} (pool : Finset ℤ) (st : ((Fin n → Finset ℤ) × (Fin n → ℕ)))
    (j : Fin n) (c : ℤ)
    (hf : Fresh pool st) : Fresh (pool.erase c) (assign st j c) := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [assign, Function.update_self] using
      (Finset.disjoint_insert_right.mpr
        ⟨Finset.notMem_erase c pool, (hf j).mono_left (Finset.erase_subset c pool)⟩)
  · simpa only [assign, Function.update_of_ne hij] using
      (hf i).mono_left (Finset.erase_subset c pool)

private theorem runPool_coherent {n : ℕ} (S : Finset (Fin n)) (b : ℕ) (pick : Finset ℤ → ℤ)
    (hp : AdmissiblePick pick) (fuel : ℕ) (pool : Finset ℤ)
    (st : ((Fin n → Finset ℤ) × (Fin n → ℕ)))
    (hc : Coherent st) (hf : Fresh pool st) : Coherent (runPool S b pick fuel pool st) := by
  induction fuel generalizing pool st with
  | zero => exact hc
  | succ k ih =>
    simp only [runPool]
    split
    · exact hc
    · split
      · exact hc
      · rename_i hne
        have hm := hp pool (Finset.nonempty_iff_ne_empty.mpr hne)
        cases hb : best S st.2 with
        | none => simpa [hb] using hc
        | some j =>
          simpa [hb] using ih (pool.erase (pick pool)) (assign st j (pick pool))
            (assign_coherent pool st j (pick pool) hc hf hm)
            (assign_fresh pool st j (pick pool) hf)

private theorem runPool_subset {n : ℕ} (S : Finset (Fin n)) (b : ℕ) (pick : Finset ℤ → ℤ)
    (hp : AdmissiblePick pick) (fuel : ℕ) (pool : Finset ℤ)
    (st : ((Fin n → Finset ℤ) × (Fin n → ℕ))) :
    ∀ i, (runPool S b pick fuel pool st).1 i ⊆ st.1 i ∪ pool := by
  induction fuel generalizing pool st with
  | zero => exact fun i => Finset.subset_union_left
  | succ k ih =>
    simp only [runPool]
    split
    · exact fun i => Finset.subset_union_left
    · split
      · exact fun i => Finset.subset_union_left
      · rename_i hne
        have hm := hp pool (Finset.nonempty_iff_ne_empty.mpr hne)
        cases hb : best S st.2 with
        | none => simp
        | some j =>
          intro i d hd
          have hi := ih (pool.erase (pick pool)) (assign st j (pick pool)) i hd
          rcases Finset.mem_union.mp hi with hi | hi
          · by_cases hij : i = j
            · subst i
              simp only [assign, Function.update_self, Finset.mem_insert] at hi
              rcases hi with rfl | hi
              · exact Finset.mem_union_right _ hm
              · exact Finset.mem_union_left _ hi
            · exact Finset.mem_union_left _ (by simpa [assign, hij] using hi)
          · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hi)

private def afterPair (pick : Finset ℤ → ℤ) : ((Fin 4 → Finset ℤ) × (Fin 4 → ℕ)) :=
  runPool pair 4 pick 4 {1,2,3,4} (initial witness)

private def afterTriple (pick : Finset ℤ → ℤ) : ((Fin 4 → Finset ℤ) × (Fin 4 → ℕ)) :=
  runPool triple 4 pick 2 {5,6} (afterPair pick)

private theorem initial_w : (initial witness).2 = ![0,2,4,4] := by
  exact List.ofFn_inj.mp rfl

private theorem pair_loads : loadPool pair 4 4 ![0,2,4,4] = ![3,3,4,4] := by
  funext i
  fin_cases i <;> simp [loadPool, best, pair,
    Finset.filter_insert, Finset.filter_singleton, Finset.sort_insert,
    Fin.forall_fin_succ, Function.update_apply]

private theorem triple_loads : loadPool triple 4 2 ![3,3,4,4] = ![5,3,4,4] := by
  funext i
  fin_cases i <;> simp [loadPool, best, triple,
    Finset.filter_insert, Finset.filter_singleton, Finset.sort_insert,
    Fin.forall_fin_succ, Function.update_apply]

private theorem afterPair_w (pick : Finset ℤ → ℤ) (hp : AdmissiblePick pick) :
    (afterPair pick).2 = ![3,3,4,4] := by
  rw [afterPair, runPool_w pair 4 pick hp 4 _ _ (by decide +kernel), initial_w, pair_loads]

private theorem afterTriple_w (pick : Finset ℤ → ℤ) (hp : AdmissiblePick pick) :
    (afterTriple pick).2 = ![5,3,4,4] := by
  rw [afterTriple, runPool_w triple 4 pick hp 2 _ _ (by decide +kernel),
    afterPair_w pick hp, triple_loads]

private theorem afterPair_coherent (pick : Finset ℤ → ℤ) (hp : AdmissiblePick pick) :
    Coherent (afterPair pick) := by
  apply runPool_coherent pair 4 pick hp
  · intro i; rfl
  · unfold Fresh
    decide +kernel

private theorem afterTriple_coherent (pick : Finset ℤ → ℤ) (hp : AdmissiblePick pick) :
    Coherent (afterTriple pick) := by
  apply runPool_coherent triple 4 pick hp
  · exact afterPair_coherent pick hp
  · have hbase : ∀ i : Fin 4,
        Disjoint ({5,6} : Finset ℤ) ((initial witness).1 i ∪ {1,2,3,4}) := by
      decide +kernel
    intro i
    exact (hbase i).mono_right (runPool_subset pair 4 pick hp 4 _ _ i)

private theorem run_reduction (ord : List (Finset (Fin 4))) (pick : Finset ℤ → ℤ)
    (ho : AdmissibleOrder ord) :
    runSupports witness 4 pick ord (initial witness) = afterTriple pick := by
  rw [run_filter ord 4 pick (fun S hS => (ho.2.1 S).mp hS), forced_order ord ho]
  have hpair : Ip witness pair = {1,2,3,4} := by
    exact Finset.val_inj.mp rfl
  have htriple : Ip witness triple = {5,6} := by
    exact Finset.val_inj.mp rfl
  simp [runSupports, hpair, htriple, afterPair, afterTriple]

private theorem every_run_card (ord : List (Finset (Fin 4))) (pick : Finset ℤ → ℤ)
    (ho : AdmissibleOrder ord) (hp : AdmissiblePick pick) :
    (colorSym witness 4 ord pick 1).card = 3 := by
  unfold colorSym
  rw [run_reduction ord pick ho]
  rw [afterTriple_coherent pick hp 1, afterTriple_w pick hp]
  rfl

private theorem no_output_coloring (ord : List (Finset (Fin 4))) (pick : Finset ℤ → ℤ)
    (ho : AdmissibleOrder ord) (hp : AdmissiblePick pick) :
    ¬ ∃ φ, IsColoring witness 4 φ ∧ ∀ i, φ i ⊆ colorSym witness 4 ord pick i := by
  rintro ⟨φ, hc, hs⟩
  have hle := Finset.card_le_card (hs 1)
  rw [(hc.1 1).2, every_run_card ord pick ho hp] at hle
  omega

theorem result : ¬ claim := by
  intro h
  obtain ⟨ord, pick, ho, hp, hφ⟩ := h 4 6 4 witness witness_cards witness_colorable
  exact no_output_coloring ord pick ho hp hφ


end D5.S3.ConceptDynamics.GraphColoring.ColorSymOptimalityRefutation
