/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.Data.Fintype.EquivFin]
   utility: none
   digest: Finite unary Moore output separation and exact first-match table synthesis. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.OfFn

/-! Finite signature refinement and executable first-match synthesis, including the initial output. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation

section Refinement

variable {Q : Type*}

/-- The Boolean observation after exactly the given number of unary transitions. -/
private def stream (f : Q → Q) (g : Q → Bool) (q : Q) : ℕ → Bool
  | 0 => g q
  | n + 1 => stream f g (f q) n

private def signature (f : Q → Q) (g : Q → Bool) : ℕ → Q → List Bool
  | 0, _ => []
  | n + 1, q => g q :: signature f g n (f q)

private theorem signature_eq_iff (f : Q → Q) (g : Q → Bool) (n : ℕ) (q r : Q) :
    signature f g n q = signature f g n r ↔
      ∀ i < n, stream f g q i = stream f g r i := by
  induction n generalizing q r with
  | zero => simp [signature]
  | succ n ih =>
    rw [signature, signature, List.cons.injEq, ih]
    constructor
    · rintro ⟨hh, ht⟩ (i | i) hi
      · exact hh
      · exact ht i (by omega)
    · intro h
      exact ⟨h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩

private theorem signature_take (f : Q → Q) (g : Q → Bool) (n : ℕ) (q : Q) :
    (signature f g (n + 1) q).take n = signature f g n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [signature, List.take_succ_cons, ih, signature]

private def signatures [Fintype Q] (f : Q → Q) (g : Q → Bool) (n : ℕ) :
    Finset (List Bool) :=
  Finset.univ.image (signature f g n)

private theorem signatures_truncate [Fintype Q] (f : Q → Q) (g : Q → Bool) (n : ℕ) :
    (signatures f g (n + 1)).image (List.take n) = signatures f g n := by
  simp [signatures, Finset.image_image, Function.comp_def, signature_take]

private theorem stable_gives_all (f : Q → Q) (g : Q → Bool) (n : ℕ)
    (step : ∀ x y, signature f g n x = signature f g n y →
      signature f g (n + 1) x = signature f g (n + 1) y)
    (q r : Q) (h : signature f g n q = signature f g n r) :
    ∀ i, stream f g q i = stream f g r i := by
  intro i
  induction i generalizing q r with
  | zero => exact (signature_eq_iff f g _ _ _).mp (step q r h) 0 (by omega)
  | succ i ih =>
    exact ih (f q) (f r) (List.cons.inj (step q r h)).2

/-- Agreement through the first `card Q - 1` observations implies agreement forever. -/
private theorem stream_eq_of_agree_prefix [Fintype Q] (f : Q → Q) (g : Q → Bool) (q r : Q)
    (h : ∀ i < Fintype.card Q - 1, stream f g q i = stream f g r i) :
    ∀ i, stream f g q i = stream f g r i := by
  by_contra hall
  let N := Fintype.card Q - 1
  have strict : ∀ n ≤ N, (signatures f g n).card < (signatures f g (n + 1)).card := by
    intro n hle
    have htruncate := signatures_truncate f g n
    have hmono : (signatures f g n).card ≤ (signatures f g (n + 1)).card := by
      rw [← htruncate]
      exact Finset.card_image_le
    by_contra ht
    have heq : ((signatures f g (n + 1)).image (List.take n)).card =
        (signatures f g (n + 1)).card := by rw [htruncate]; omega
    have hinj := Finset.card_image_iff.mp heq
    apply hall
    refine stable_gives_all f g n ?_ q r ?_
    · intro x y hxy
      apply hinj
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
      simpa only [signature_take] using hxy
    · exact (signature_eq_iff f g _ _ _).mpr fun i hi => h i (lt_of_lt_of_le hi hle)
  have lower : ∀ n ≤ N + 1, n + 1 ≤ (signatures f g n).card := by
    intro n
    induction n with
    | zero =>
      intro _
      exact Finset.card_pos.mpr ⟨[], Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩
    | succ n ih =>
      intro hle
      have h1 := strict n (by omega)
      have h2 := ih (by omega)
      omega
  have hu : (signatures f g (N + 1)).card ≤ Fintype.card Q :=
    Finset.card_image_le.trans_eq Finset.card_univ
  have hl := lower (N + 1) (by omega)
  have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  omega

end Refinement

/-- Explicit labelled transition, output and start tables on Fin a. -/
structure Table (a : Nat) where
  transition : Fin a → Fin a
  label : Fin a → Bool
  start : Fin a

private def functions {A : Type} (xs : List A) : (n : Nat) → List (Fin n → A)
  | 0 => [Fin.elim0]
  | n + 1 => xs.flatMap (fun x => (functions xs n).map (fun f => Fin.cases x f))

private theorem mem_functions {A : Type} {xs : List A} (n : Nat) (f : Fin n → A)
    (hf : ∀ i, f i ∈ xs) : f ∈ functions xs n := by
  induction n with
  | zero =>
    have he : f = Fin.elim0 := by
      funext i
      exact Fin.elim0 i
    simpa [functions] using he
  | succ n ih =>
    rw [functions, List.mem_flatMap]
    refine ⟨f 0, hf 0, List.mem_map.mpr ⟨fun i => f i.succ, ih _ (fun i => hf i.succ), ?_⟩⟩
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

private theorem length_flatMap_const {A B : Type} (xs : List A) (g : A → List B) (m : Nat)
    (hg : ∀ x ∈ xs, (g x).length = m) : (xs.flatMap g).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, hg _ List.mem_cons_self,
      ih (fun y hy => hg y (List.mem_cons_of_mem x hy)), List.length_cons, Nat.succ_mul,
      Nat.add_comm]

private theorem length_functions {A : Type} (xs : List A) (n : Nat) :
    (functions xs n).length = xs.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [functions, length_flatMap_const xs _ (xs.length ^ n), Nat.pow_succ, Nat.mul_comm]
    intro x _
    rw [List.length_map, ih]

private def tables (a : Nat) : List (Table a) :=
  (functions (List.finRange a) a).flatMap (fun transition =>
    (functions [false, true] a).flatMap (fun label =>
      (List.finRange a).map (fun start => ⟨transition, label, start⟩)))

private theorem mem_tables {a : Nat} (t : Table a) : t ∈ tables a := by
  cases t with
  | mk transition label start =>
    exact List.mem_flatMap.mpr
      ⟨transition, mem_functions a transition (fun i => List.mem_finRange (transition i)),
        List.mem_flatMap.mpr ⟨label, mem_functions a label (fun i => by cases label i <;> decide),
          List.mem_map.mpr ⟨start, List.mem_finRange start, rfl⟩⟩⟩

private theorem length_tables (a : Nat) : (tables a).length = a ^ (a + 1) * 2 ^ a := by
  rw [tables, length_flatMap_const _ _ (2 ^ a * a), length_functions, List.length_finRange]
  · rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  · intro transition _
    rw [length_flatMap_const _ _ a, length_functions]
    · rfl
    · intro label _
      rw [List.length_map, List.length_finRange]

/-- Fixed size/transition/label/start enumeration, before deduplication. -/
def allTables (K : Nat) : List (Sigma Table) :=
  (List.range K).flatMap (fun n => (tables (n + 1)).map (fun t => ⟨n + 1, t⟩))

private theorem mem_allTables {K a : Nat} (t : Table a) :
    (⟨a, t⟩ : Sigma Table) ∈ allTables K ↔ 0 < a ∧ a ≤ K := by
  rw [allTables, List.mem_flatMap]
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    have he := congrArg Sigma.fst hu
    simp only [List.mem_range] at hn
    change n + 1 = a at he
    omega
  · rintro ⟨ha, hk⟩
    cases a with
    | zero => omega
    | succ n =>
      exact ⟨n, List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨t, mem_tables t, rfl⟩⟩

private theorem length_allTables (K : Nat) : (allTables K).length =
    ((List.range K).map (fun n => (n + 1) ^ (n + 2) * 2 ^ (n + 1))).sum := by
  rw [allTables, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro n _
  rw [List.length_map, length_tables]

universe u v

/-- An autonomous unary Moore source: emit the current label before stepping. -/
structure Machine (Q : Type u) where
  transition : Q → Q
  label : Q → Bool
  start : Q

/-- Zero-based source output, including output at the initial state. -/
def Machine.emit {Q : Type u} (m : Machine Q) : Nat → Bool :=
  stream m.transition m.label m.start

/-- Source outputs in observation order, without an uncounted initial symbol. -/
def observations {Q : Type u} (m : Machine Q) (n : Nat) : List Bool :=
  signature m.transition m.label n m.start

private theorem signature_eq_ofFn {Q : Type u} (f : Q → Q) (g : Q → Bool)
    (n : Nat) (q : Q) : signature f g n q = List.ofFn (fun i : Fin n => stream f g q i) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => rw [signature, List.ofFn_succ, ih]; rfl

private theorem observations_eq_iff {Q : Type u} {R : Type v} (m : Machine Q) (m' : Machine R)
    (n : Nat) : observations m n = observations m' n ↔
      ∀ i < n, m.emit i = m'.emit i := by
  rw [observations, observations, signature_eq_ofFn, signature_eq_ofFn, List.ofFn_inj]
  exact ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun j => h j j.isLt⟩

private theorem stream_iterate {Q : Type u} (f : Q → Q) (g : Q → Bool) (q : Q) (i : Nat) :
    stream f g q i = g (f^[i] q) := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih => rw [stream, ih, Function.iterate_succ_apply]

private theorem through_left {Q : Type u} {R : Type v} (m : Machine Q) (m' : Machine R)
    (q : Q) (i : Nat) :
    stream (Sum.elim (Sum.inl ∘ m.transition) (Sum.inr ∘ m'.transition))
        (Sum.elim m.label m'.label) (.inl q) i = stream m.transition m.label q i := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih => exact ih (m.transition q)

private theorem through_right {Q : Type u} {R : Type v} (m : Machine Q) (m' : Machine R)
    (q : R) (i : Nat) :
    stream (Sum.elim (Sum.inl ∘ m.transition) (Sum.inr ∘ m'.transition))
        (Sum.elim m.label m'.label) (.inr q) i = stream m'.transition m'.label q i := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih => exact ih (m'.transition q)

private theorem compare {Q : Type u} {R : Type v} [Fintype Q] [Fintype R]
    (m : Machine Q) (m' : Machine R) (K : Nat)
    (hq : Fintype.card Q ≤ K) (hr : Fintype.card R ≤ K)
    (h : observations m (2*K-1) = observations m' (2*K-1)) :
    ∀ i, m.emit i = m'.emit i := by
  have hcap : Fintype.card (Q ⊕ R) - 1 ≤ 2*K-1 := by rw [Fintype.card_sum]; omega
  have heq := stream_eq_of_agree_prefix
    (Sum.elim (Sum.inl ∘ m.transition) (Sum.inr ∘ m'.transition))
    (Sum.elim m.label m'.label) (.inl m.start) (.inr m'.start)
    (fun i hi => by rw [through_left, through_right]; exact
      (observations_eq_iff m m' _).mp h i (lt_of_lt_of_le hi hcap))
  intro i
  simpa only [through_left, through_right, Machine.emit] using heq i

/-- Execute a labelled table as a unary source. -/
def Table.machine {a : Nat} (t : Table a) : Machine (Fin a) :=
  ⟨t.transition, t.label, t.start⟩

private def relabel {Q : Type u} {a : Nat} (m : Machine Q) (e : Q ≃ Fin a) : Table a :=
  ⟨fun i => e (m.transition (e.symm i)), fun i => m.label (e.symm i), e m.start⟩

private theorem relabel_stream {Q : Type u} {a : Nat} (m : Machine Q) (e : Q ≃ Fin a)
    (q : Q) (i : Nat) :
    stream (Table.machine (relabel m e)).transition (Table.machine (relabel m e)).label
        (e q) i = stream m.transition m.label q i := by
  induction i generalizing q with
  | zero => simp [stream, Table.machine, relabel]
  | succ i ih => simpa only [stream, Table.machine, relabel, Equiv.symm_apply_apply] using (ih (m.transition q))

private def tableMatches (K : Nat) (word : List Bool) (x : Sigma Table) : Bool :=
  observations (Table.machine x.2) (2*K-1) == word

/-- First matching table, in fixed size/transition/label/start enumeration order. -/
def synthesize (K : Nat) (word : List Bool) : Option (Sigma Table) :=
  (allTables K).find? (tableMatches K word)

/-- Output at an arbitrary index of the actual table selected by synthesis. -/
def generated (K : Nat) (word : List Bool) (i : Nat) : Option Bool :=
  (synthesize K word).map (fun x => (Table.machine x.2).emit i)

private theorem matching_exists {Q : Type u} [Fintype Q] (m : Machine Q)
    (K : Nat) (hq : Fintype.card Q ≤ K) (word : List Bool)
    (hw : word = observations m (2*K-1)) :
    ∃ x, synthesize K word = some x := by
  let e := Fintype.equivFin Q
  let t := relabel m e
  have hmem := (mem_allTables (K := K) t).2 ⟨Fintype.card_pos_iff.mpr ⟨m.start⟩, hq⟩
  have hmatch : tableMatches K word ⟨Fintype.card Q, t⟩ = true := by
    rw [tableMatches, beq_iff_eq, hw, observations_eq_iff]
    intro i _
    exact relabel_stream m e m.start i
  cases h : synthesize K word with
  | none => exact ((List.find?_eq_none.mp h) _ hmem hmatch).elim
  | some x => exact ⟨x, rfl⟩

private theorem matching_correct {Q : Type u} [Fintype Q] (m : Machine Q)
    (K : Nat) (hq : Fintype.card Q ≤ K) (word : List Bool)
    (hw : word = observations m (2*K-1)) {x : Sigma Table}
    (hx : synthesize K word = some x) :
    0 < x.1 ∧ x.1 ≤ K ∧ ∀ i, (Table.machine x.2).emit i = m.emit i := by
  have hsize := (mem_allTables (K := K) x.2).mp (List.mem_of_find?_eq_some hx)
  have hmatch : tableMatches K word x = true := List.find?_some hx
  rw [tableMatches, beq_iff_eq, hw] at hmatch
  exact ⟨hsize.1, hsize.2, compare (Table.machine x.2) m K
    (by simpa only [Fintype.card_fin] using hsize.2) hq hmatch⟩

private theorem first_match {K : Nat} {word : List Bool} {x : Sigma Table}
    (hx : synthesize K word = some x) :
    ∃ earlier later, allTables K = earlier ++ x :: later ∧ ∀ y ∈ earlier,
      observations (Table.machine y.2) (2*K-1) ≠ word := by
  obtain ⟨_, earlier, later, hlist, hbad⟩ := List.find?_eq_some_iff_append.mp hx
  exact ⟨earlier, later, hlist, fun y hy he => by
    have hb := hbad y hy
    simp [tableMatches, he] at hb⟩

/-- The exact separation length and constructive synthesis for the unary promise. -/
theorem unary_moore_separation_and_synthesis (K : Nat) (_hK : 1 ≤ K) :
    (∀ (word : List Bool) (i : Nat) (Q : Type) [Fintype Q] (m : Machine Q),
      Fintype.card Q ≤ K → word = observations m (2*K-1) →
      generated K word i = some (m.emit i)) ∧
    (∀ (Q R : Type) [Fintype Q] [Fintype R] (m : Machine Q) (m' : Machine R),
      Fintype.card Q ≤ K → Fintype.card R ≤ K →
      observations m (2*K-1) = observations m' (2*K-1) → ∀ i, m.emit i = m'.emit i) ∧
    (∀ (word : List Bool) (Q : Type) [Fintype Q] (m : Machine Q),
      Fintype.card Q ≤ K → word = observations m (2*K-1) →
      ∃ x, synthesize K word = some x ∧
        0 < x.1 ∧ x.1 ≤ K ∧ (∀ i, (Table.machine x.2).emit i = m.emit i) ∧
        ∃ earlier later, allTables K = earlier ++ x :: later ∧ ∀ y ∈ earlier,
          observations (Table.machine y.2) (2*K-1) ≠ word) ∧
    (∀ (Q : Type) (m : Machine Q) (i : Nat), m.emit i = m.label (m.transition^[i] m.start)) ∧
    (allTables K).length =
      ((List.range K).map (fun n => (n+1)^(n+2)*2^(n+1))).sum := by
  refine ⟨?_, ?_, ?_, ?_, length_allTables K⟩
  · intro word i Q _ m hq hw
    obtain ⟨x, hx⟩ := matching_exists m K hq word hw
    rw [generated, hx, Option.map_some, (matching_correct m K hq word hw hx).2.2 i]
  · intro Q R _ _ m m' hq hr h
    exact compare m m' K hq hr h
  · intro word Q _ m hq hw
    obtain ⟨x, hx⟩ := matching_exists m K hq word hw
    obtain ⟨hp, hb, hc⟩ := matching_correct m K hq word hw hx
    exact ⟨x, hx, hp, hb, hc, first_match hx⟩
  · intro Q m i
    exact stream_iterate _ _ _ _

#print axioms unary_moore_separation_and_synthesis

end D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation
