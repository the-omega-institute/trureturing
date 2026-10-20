import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Graph
import LeanInformationAuditInterface.Contract.AuricFib

/-! Finite-depth derivation semantics for the graph recurrence. -/
namespace LeanInformationAudit.Tests.SearchReduction.GraphModel
open LeanInformationAudit.SearchReduction

private theorem finite_le_finite (a b : Nat) :
    (Bound.finite a) ≤ .finite b ↔ a ≤ b := Iff.rfl
private theorem top_not_le_finite (n : Nat) :
    ¬ (Bound.top ≤ .finite n) := by intro h; exact h
attribute [local simp] finite_le_finite top_not_le_finite

private def bmin : Bound → Bound → Bound
  | .top, b => b
  | b, .top => b
  | .finite a, .finite b => .finite (min a b)

private def bmax : Bound → Bound → Bound
  | .top, _ | _, .top => .top
  | .finite a, .finite b => .finite (max a b)

private theorem bmin_le (a b : Bound) (n : Nat) :
    bmin a b ≤ .finite n ↔ a ≤ .finite n ∨ b ≤ .finite n := by
  cases a <;> cases b <;> simp [bmin, min_le_iff]

private theorem bmax_le (a b : Bound) (n : Nat) :
    bmax a b ≤ .finite n ↔ a ≤ .finite n ∧ b ≤ .finite n := by
  cases a <;> cases b <;> simp [bmax, max_le_iff]

private theorem min_fold (xs : List Bound) (a : Bound) (n : Nat) :
    xs.foldl bmin a ≤ .finite n ↔ a ≤ .finite n ∨ ∃ x ∈ xs, x ≤ .finite n := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, bmin_le, or_assoc]

private theorem max_fold (xs : List Bound) (a : Bound) (n : Nat) :
    xs.foldl bmax a ≤ .finite n ↔ a ≤ .finite n ∧ ∀ x ∈ xs, x ≤ .finite n := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, bmax_le, and_assoc]

private theorem minBound_le (xs : List Bound) (n : Nat) :
    minBound xs ≤ .finite n ↔ ∃ x ∈ xs, x ≤ .finite n := by
  change xs.foldl bmin .top ≤ .finite n ↔ _
  rw [min_fold]
  simp []

private theorem boundMax_le (xs : List Bound) (n : Nat) :
    boundMax xs ≤ .finite n ↔ ∀ x ∈ xs, x ≤ .finite n := by
  change xs.foldl bmax (.finite 0) ≤ .finite n ↔ _
  rw [max_fold]
  simp []

private theorem boundAdd_le (b : Bound) (c n : Nat) :
    boundAdd b c ≤ .finite n ↔ c ≤ n ∧ b ≤ .finite (n - c) := by
  cases b <;> simp [boundAdd] <;> omega

/-- An AND/OR derivation tree of height at most fuel and min-max cost at most n.
This is a proof-tree predicate, independently of the numerical recurrence. -/
def Derivable (graph : ProofGraph) (price : GraphEdge → Nat) (seeds : List Nat) :
    Nat → Nat → Nat → Prop
  | 0, v, _ => v ∈ seeds
  | fuel + 1, v, n => v ∈ seeds ∨ ∃ edge ∈ incoming graph v,
      price edge ≤ n ∧ ∀ p ∈ edge.premises, Derivable graph price seeds fuel p (n - price edge)

/-- The reference DP is exactly the least achievable min-max depth. A finite
bound supplies a recursively recoverable author-edge derivation tree. -/
theorem depthFuel_le_iff_derivable (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) (fuel v n : Nat) :
    depthFuel graph weight seeds fuel v ≤ .finite n ↔
      Derivable graph (fun edge => weight edge.cost) seeds fuel v n := by
  induction fuel generalizing v n with
  | zero =>
    simp only [depthFuel, Derivable]
    split <;> simp_all []
  | succ fuel ih =>
    simp only [depthFuel, Derivable]
    split
    · simp_all []
    · rename_i h
      have hv : v ∉ seeds := by simpa using h
      simp only [hv, false_or]
      rw [minBound_le]
      simp [List.mem_map, edgeBound, boundAdd_le, boundMax_le, ih]

private theorem initial_size (graph : ProofGraph) (seeds : List Nat) :
    (initialTable graph seeds).size = graph.vertices.length := by simp [initialTable]

private theorem relax_size (weight : EdgeCost → Nat) (previous table : Array DPCell)
    (entry : GraphEdge × Nat) :
    (relaxEdge weight previous table entry).size = table.size := by
  simp only [relaxEdge]
  split <;> simp

private theorem relax_fold_size (weight : EdgeCost → Nat) (previous table : Array DPCell)
    (entries : List (GraphEdge × Nat)) :
    (entries.foldl (relaxEdge weight previous) table).size = table.size := by
  induction entries generalizing table with
  | nil => rfl
  | cons entry entries ih => simp only [List.foldl_cons, ih, relax_size]

private theorem choose_distance (a b : Bound) :
    (if better a b then a else b) = bmin b a := by
  cases a with
  | top => cases b <;> simp [better, bmin]
  | finite a =>
    cases b with
    | top => simp [better, bmin]
    | finite b =>
      by_cases h : a < b
      · simp [better, bmin, h, Nat.min_eq_right (Nat.le_of_lt h)]
      · simp [better, bmin, h, Nat.min_eq_left (by omega : b ≤ a)]

private theorem relax_distance (weight : EdgeCost → Nat) (previous table : Array DPCell)
    (entry : GraphEdge × Nat) (v : Nat) (hv : v < table.size) :
    ((relaxEdge weight previous table entry)[v]?.getD {}).distance =
      if entry.1.conclusion = v then
        bmin (table[v]?.getD {}).distance
          (edgeBound weight entry.1 (fun p => (previous[p]?.getD {}).distance))
      else (table[v]?.getD {}).distance := by
  obtain ⟨edge, index⟩ := entry
  by_cases hc : edge.conclusion = v
  · simp only [relaxEdge, hc, ↓reduceIte]
    split
    · rename_i h
      simp only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hv, Option.getD_some]
      simpa only [h, Bool.true_eq, ↓reduceIte] using (choose_distance
        (edgeBound weight edge (fun p => (previous[p]?.getD {}).distance))
        (table[v]?.getD {}).distance)
    · rename_i h
      have chosen := choose_distance
        (edgeBound weight edge (fun p => (previous[p]?.getD {}).distance))
        (table[v]?.getD {}).distance
      simpa [h] using chosen
  · simp only [relaxEdge]
    split <;> simp [hc, Array.getElem?_setIfInBounds_ne]

private theorem relax_fold_le (weight : EdgeCost → Nat) (previous table : Array DPCell)
    (entries : List (GraphEdge × Nat)) (v n : Nat) (hv : v < table.size) :
    ((entries.foldl (relaxEdge weight previous) table)[v]?.getD {}).distance ≤ .finite n ↔
      (table[v]?.getD {}).distance ≤ .finite n ∨ ∃ entry ∈ entries,
        entry.1.conclusion = v ∧
        edgeBound weight entry.1 (fun p => (previous[p]?.getD {}).distance) ≤ .finite n := by
  induction entries generalizing table with
  | nil => simp
  | cons entry entries ih =>
    rw [List.foldl_cons, ih _ (by simpa only [relax_size] using hv),
      relax_distance weight previous table entry v hv]
    by_cases hc : entry.1.conclusion = v
    · simp only [hc, ↓reduceIte, bmin_le, List.mem_cons]
      aesop
    · simp only [hc, ↓reduceIte, List.mem_cons]
      aesop

private theorem initial_le (graph : ProofGraph) (seeds : List Nat) (v n : Nat)
    (hv : v < graph.vertices.length)
    (indexed : ∀ i (h : i < graph.vertices.length), (graph.vertices[i]).id = i) :
    ((initialTable graph seeds)[v]?.getD {}).distance ≤ .finite n ↔ v ∈ seeds := by
  by_cases hs : v ∈ seeds <;>
    simp [initialTable, List.getElem?_eq_getElem hv, indexed v hv, hs]

/-- Every production Bellman round computes the independent min-max derivation
semantics. The hypotheses express array indexing and in-graph premises, not a
numerical result or the existence of an optimal derivation. Cycles are allowed
at this bounded stage. -/
theorem dpRounds_le_iff_derivable (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat)
    (indexed : ∀ i (h : i < graph.vertices.length), (graph.vertices[i]).id = i)
    (premisesBounded : ∀ edge ∈ graph.edges, ∀ p ∈ edge.premises,
      p < graph.vertices.length)
    (fuel v n : Nat) (hv : v < graph.vertices.length) :
    ((dpRounds graph weight seeds fuel)[v]?.getD {}).distance ≤ .finite n ↔
      Derivable graph (fun edge => weight edge.cost) seeds fuel v n := by
  induction fuel generalizing v n with
  | zero => exact initial_le graph seeds v n hv indexed
  | succ fuel ih =>
    rw [dpRounds, relax_fold_le weight _ _ _ v n (by simpa only [initial_size] using hv),
      initial_le graph seeds v n hv indexed]
    constructor
    · rintro (hs | ⟨⟨edge, index⟩, he, hcon, bound⟩)
      · exact Or.inl hs
      · have hem := List.fst_mem_of_mem_zipIdx he
        obtain ⟨hc, hp⟩ := (boundAdd_le _ _ _).mp bound
        refine Or.inr ⟨edge, List.mem_filter.mpr ⟨hem, by simpa using hcon⟩, hc, ?_⟩
        intro p hpm
        apply (ih p _ (premisesBounded edge hem p hpm)).mp
        exact (boundMax_le _ _).mp hp _ (List.mem_map.mpr ⟨p, hpm, rfl⟩)
    · rintro (hs | ⟨edge, he, hc, hp⟩)
      · exact Or.inl hs
      · have hem := (List.mem_filter.mp he).1
        have hcon : edge.conclusion = v := by simpa using (List.mem_filter.mp he).2
        have member : edge ∈ graph.edges.zipIdx.map Prod.fst := by simpa using hem
        obtain ⟨⟨old, index⟩, hi, equal⟩ := List.mem_map.mp member
        simp only at equal
        subst old
        refine Or.inr ⟨(edge, index), hi, hcon, (boundAdd_le _ _ _).mpr ⟨hc, ?_⟩⟩
        apply (boundMax_le _ _).mpr
        intro distance hd
        obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hd
        exact (ih p _ (premisesBounded edge hem p hpm)).mpr (hp p hpm)

private theorem bound_ext (a b : Bound)
    (same : ∀ n, a ≤ .finite n ↔ b ≤ .finite n) : a = b := by
  cases a with
  | top =>
    cases b with
    | top => rfl
    | finite b => exact False.elim ((same b).mpr (Nat.le_refl b))
  | finite a =>
    cases b with
    | top => exact False.elim ((same a).mp (Nat.le_refl a))
    | finite b =>
      exact congrArg Bound.finite (Nat.le_antisymm
        ((same b).mpr (Nat.le_refl b)) ((same a).mp (Nat.le_refl a)))

/-- The production table equals the reference recurrence at the actual number
of rounds. No acyclicity or optimality conclusion is assumed. -/
theorem dpTable_eq_depthFuel (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat)
    (indexed : ∀ i (h : i < graph.vertices.length), (graph.vertices[i]).id = i)
    (premisesBounded : ∀ edge ∈ graph.edges, ∀ p ∈ edge.premises,
      p < graph.vertices.length)
    (v : Nat) (hv : v < graph.vertices.length) :
    ((dpTable graph weight seeds)[v]?.getD {}).distance =
      depthFuel graph weight seeds graph.vertices.length v := by
  rw [dpTable_eq_dpRounds]
  apply bound_ext
  intro n
  exact (dpRounds_le_iff_derivable graph weight seeds indexed premisesBounded
    graph.vertices.length v n hv).trans (depthFuel_le_iff_derivable _ _ _ _ _ _).symm

/-- Monotonicity permits seed-dependent prices, provided enlarging the seed set
never makes a local reconstruction cost larger. No property of real budgets
is silently assumed by the model. -/
theorem derivable_mono (graph : ProofGraph) (price expensive : GraphEdge → Nat)
    (small large : List Nat) (seedInclusion : ∀ v ∈ small, v ∈ large)
    (localMonotone : ∀ edge, price edge ≤ expensive edge)
    (fuel v n : Nat) :
    Derivable graph expensive small fuel v n → Derivable graph price large fuel v n := by
  induction fuel generalizing v n with
  | zero => exact seedInclusion v
  | succ fuel ih =>
    rintro (hs | ⟨edge, he, hc, hp⟩)
    · exact Or.inl (seedInclusion v hs)
    · refine Or.inr ⟨edge, he, le_trans (localMonotone edge) hc, ?_⟩
      intro p hmem
      have h := ih p (n - expensive edge) (hp p hmem)
      -- Budget weakening is independent of adding seeds.
      have weaken : ∀ f v a b, a ≤ b → Derivable graph price large f v a →
          Derivable graph price large f v b := by
        intro f
        induction f with
        | zero => intro v a b _ h; exact h
        | succ f hf =>
          intro v a b hab h
          rcases h with hs | ⟨e, he, hc, hh⟩
          · exact Or.inl hs
          · exact Or.inr ⟨e, he, le_trans hc hab, fun p hp =>
              hf p (a - price e) (b - price e) (Nat.sub_le_sub_right hab _) (hh p hp)⟩
      exact weaken fuel p _ _ (Nat.sub_le_sub_left (localMonotone edge) n) h

/-- A zero-price path is sound whenever each local edge certificate and each
seed establishes its corresponding proposition. Shared premises need no
independence assumption. -/
theorem zero_path_sound (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (P : Nat → Prop)
    (seedProof : ∀ v ∈ seeds, P v)
    (edgeProof : ∀ edge ∈ graph.edges, price edge = 0 →
      (∀ p ∈ edge.premises, P p) → P edge.conclusion)
    (fuel v : Nat) (h : Derivable graph price seeds fuel v 0) : P v := by
  induction fuel generalizing v with
  | zero => exact seedProof v h
  | succ fuel ih =>
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact seedProof v hs
    · have hz : price edge = 0 := Nat.eq_zero_of_le_zero hc
      have hem : edge ∈ graph.edges := (List.mem_filter.mp he).1
      have hcon : edge.conclusion = v := by
        simpa using (List.mem_filter.mp he).2
      rw [← hcon]
      exact edgeProof edge hem hz (fun p hmem => ih p (by simpa [hz] using hp p hmem))

/-- Numerical monotonicity follows from derivation inclusion, including a
monotone local-cost change and an enlarged seed set. -/
theorem depthFuel_monotone (graph : ProofGraph) (cheap expensive : EdgeCost → Nat)
    (small large : List Nat) (seedInclusion : ∀ v ∈ small, v ∈ large)
    (costMonotone : ∀ c, cheap c ≤ expensive c) (fuel v : Nat) :
    depthFuel graph cheap large fuel v ≤ depthFuel graph expensive small fuel v := by
  cases hr : depthFuel graph expensive small fuel v with
  | top => cases depthFuel graph cheap large fuel v <;> trivial
  | finite n =>
    have hb : depthFuel graph expensive small fuel v ≤ .finite n := by
      rw [hr]
      exact Nat.le_refl n
    have derivation := (depthFuel_le_iff_derivable graph expensive small fuel v n).mp hb
    have lifted := derivable_mono graph (fun e => cheap e.cost) (fun e => expensive e.cost)
      small large seedInclusion (fun e => costMonotone e.cost) fuel v n derivation
    exact (depthFuel_le_iff_derivable graph cheap large fuel v n).mpr lifted

/-- Unknown endpoints enclose the exact zero/one recurrence. -/
theorem lower_le_upper (graph : ProofGraph) (seeds : List Nat) (fuel v : Nat) :
    depthFuel graph costLower seeds fuel v ≤ depthFuel graph costUpper seeds fuel v := by
  apply depthFuel_monotone graph costLower costUpper seeds seeds (fun _ h => h)
  intro c
  cases c <;> decide

/-- Adding edges, including dead or zero-price edges, preserves every
existing bounded derivation. Edge selection is an OR, never an obligation to
execute the newly added route. -/
theorem edge_extension_preserves_derivations (small large : ProofGraph)
    (price : GraphEdge → Nat) (seeds : List Nat)
    (included : ∀ edge ∈ small.edges, edge ∈ large.edges)
    (fuel v n : Nat) :
    Derivable small price seeds fuel v n → Derivable large price seeds fuel v n := by
  induction fuel generalizing v n with
  | zero => exact id
  | succ fuel ih =>
    rintro (hs | ⟨edge, he, hc, hp⟩)
    · exact Or.inl hs
    · have old := List.mem_filter.mp he
      have new : edge ∈ incoming large v := List.mem_filter.mpr ⟨included edge old.1, old.2⟩
      exact Or.inr ⟨edge, new, hc, fun p hmem => ih p _ (hp p hmem)⟩

private def withZeroRoot (graph : ProofGraph) : ProofGraph :=
  {graph with edges := {conclusion := graph.root, cost := .zero} :: graph.edges}

/-- An independently certified root route outside the author graph erases any
positive graph distance, for every seed set and every positive fuel. -/
theorem outside_zero_shortcut (graph : ProofGraph) (seeds : List Nat) (fuel : Nat) :
    depthFuel (withZeroRoot graph) costUpper seeds (fuel + 1) graph.root = .finite 0 := by
  have derivation : Derivable (withZeroRoot graph) (fun e => costUpper e.cost)
      seeds (fuel + 1) graph.root 0 := by
    right
    refine ⟨{conclusion := graph.root, cost := .zero}, ?_, by simp [costUpper], ?_⟩
    · simp [incoming, withZeroRoot]
    · simp
  have bound := (depthFuel_le_iff_derivable _ _ _ _ _ _).mpr derivation
  cases heq : depthFuel (withZeroRoot graph) costUpper seeds (fuel + 1) graph.root with
  | top => simp [heq] at bound
  | finite n =>
    have hn : n ≤ 0 := by simpa [heq] using bound
    have hz := Nat.eq_zero_of_le_zero hn
    simpa [hz]

/-- The public positive verdict excludes an actual unknown edge in either arm. -/
theorem unknown_not_nonBindOnly (reading : GraphReading)
    (unknown : ∃ edge ∈ reading.graph.edges, edge.cost = .unknown ∨ edge.pairedCost = .unknown) :
    classifyGraph reading ≠ .nonBindOnly := by
  intro h
  unfold classifyGraph at h
  split at h
  · contradiction
  · split at h
    · rename_i condition
      have allKnown : reading.graph.edges.all
          (fun e => e.cost != .unknown && e.pairedCost != .unknown) = true := by
        simp only [Bool.and_eq_true] at condition
        tauto
      obtain ⟨edge, member, bad⟩ := unknown
      have good := List.all_eq_true.mp allKnown edge member
      rcases bad with bad | bad <;> simp [bad] at good
    · contradiction

/-- Missing presentation evidence cannot supply the positive graph verdict. -/
theorem unchecked_presentation_not_nonBindOnly (reading : GraphReading)
    (unchecked : reading.presentationComplete = false) :
    classifyGraph reading ≠ .nonBindOnly := by
  simp [classifyGraph, unchecked]
  split <;> simp

/-- An incomplete extraction cannot supply the positive graph verdict. -/
theorem incomplete_not_nonBindOnly (reading : GraphReading)
    (incomplete : reading.graph.complete = false) :
    classifyGraph reading ≠ .nonBindOnly := by
  simp [classifyGraph, incomplete]
  split <;> simp

/-- All verdicts are distinct and the classifier selects exactly one. -/
theorem graph_verdict_partition (reading : GraphReading) :
    (classifyGraph reading = .bindOnly ∨ classifyGraph reading = .nonBindOnly ∨
      classifyGraph reading = .insufficient) ∧
    ¬ (classifyGraph reading = .bindOnly ∧ classifyGraph reading = .nonBindOnly) ∧
    ¬ (classifyGraph reading = .bindOnly ∧ classifyGraph reading = .insufficient) ∧
    ¬ (classifyGraph reading = .nonBindOnly ∧ classifyGraph reading = .insufficient) := by
  cases classifyGraph reading <;> simp

/-- Increasing a derivation budget preserves the same author-edge tree. -/
private theorem derivable_budget_mono (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (fuel v a b : Nat) (hab : a ≤ b)
    (h : Derivable graph price seeds fuel v a) :
    Derivable graph price seeds fuel v b := by
  induction fuel generalizing v a b with
  | zero => exact h
  | succ fuel ih =>
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact Or.inl hs
    · exact Or.inr ⟨edge, he, le_trans hc hab,
        fun p hm => ih p _ _ (Nat.sub_le_sub_right hab _) (hp p hm)⟩

private theorem seed_derivable (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (fuel v n : Nat) (h : v ∈ seeds) :
    Derivable graph price seeds fuel v n := by
  cases fuel with
  | zero => exact h
  | succ fuel => exact Or.inl h

private theorem derivable_fuel_mono (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (fuel v n extra : Nat)
    (h : Derivable graph price seeds fuel v n) :
    Derivable graph price seeds (fuel + extra) v n := by
  induction fuel generalizing v n with
  | zero => simpa using seed_derivable graph price seeds extra v n h
  | succ fuel ih =>
    rw [Nat.succ_add]
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact Or.inl hs
    · exact Or.inr ⟨edge, he, hc, fun p hm => ih p _ (hp p hm)⟩

/-- Graph simulation compares actual incoming hyperedges and their prices.
It covers cut/given ablations without assuming a numerical DP result. -/
theorem derivable_edge_simulation (expensive cheap : ProofGraph)
    (expensivePrice cheapPrice : GraphEdge → Nat) (small large : List Nat)
    (seedInclusion : ∀ v ∈ small, v ∈ large)
    (simulate : ∀ edge ∈ expensive.edges, ∃ replacement ∈ cheap.edges,
      replacement.conclusion = edge.conclusion ∧ replacement.premises = edge.premises ∧
      cheapPrice replacement ≤ expensivePrice edge)
    (fuel v n : Nat) (h : Derivable expensive expensivePrice small fuel v n) :
    Derivable cheap cheapPrice large fuel v n := by
  induction fuel generalizing v n with
  | zero => exact seedInclusion v h
  | succ fuel ih =>
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · exact Or.inl (seedInclusion v hs)
    · have hem := (List.mem_filter.mp he).1
      have hcon : edge.conclusion = v := by simpa using (List.mem_filter.mp he).2
      obtain ⟨replacement, member, con, premises, price⟩ := simulate edge hem
      refine Or.inr ⟨replacement, List.mem_filter.mpr ⟨member, by simp [con, hcon]⟩,
        le_trans price hc, ?_⟩
      intro p hm
      have h := ih p _ (hp p (premises ▸ hm))
      exact derivable_budget_mono cheap cheapPrice large fuel p _ _
        (Nat.sub_le_sub_left price n) h

/-- If every cut-priced edge has the same-premise given-priced route at no
larger price, then d_given ≤ d_cut. This also proves each-arm monotonicity
under strengthening R, including heterogeneous edge-price changes. -/
theorem cut_dominates_given (cut given : ProofGraph)
    (cutWeight givenWeight : EdgeCost → Nat) (small large : List Nat)
    (seedInclusion : ∀ v ∈ small, v ∈ large)
    (simulate : ∀ edge ∈ cut.edges, ∃ replacement ∈ given.edges,
      replacement.conclusion = edge.conclusion ∧ replacement.premises = edge.premises ∧
      givenWeight replacement.cost ≤ cutWeight edge.cost)
    (fuel v : Nat) :
    depthFuel given givenWeight large fuel v ≤ depthFuel cut cutWeight small fuel v := by
  cases hr : depthFuel cut cutWeight small fuel v with
  | top => cases depthFuel given givenWeight large fuel v <;> trivial
  | finite n =>
    have h : Derivable cut (fun e => cutWeight e.cost) small fuel v n :=
      (depthFuel_le_iff_derivable ..).mp (by rw [hr]; exact Nat.le_refl n)
    exact (depthFuel_le_iff_derivable ..).mpr
      (derivable_edge_simulation cut given _ _ small large seedInclusion simulate fuel v n h)

/-- A zero baseline remains zero when R is strengthened and seed information
is enlarged. This is the bind-only monotonic direction, not a claim about Δ. -/
theorem zero_baseline_monotone (graph : ProofGraph) (cheap expensive : EdgeCost → Nat)
    (small large : List Nat) (seedInclusion : ∀ v ∈ small, v ∈ large)
    (costMonotone : ∀ c, cheap c ≤ expensive c) (fuel v : Nat)
    (zero : depthFuel graph expensive small fuel v = .finite 0) :
    depthFuel graph cheap large fuel v = .finite 0 := by
  have bound := depthFuel_monotone graph cheap expensive small large seedInclusion
    costMonotone fuel v
  rw [zero] at bound
  cases heq : depthFuel graph cheap large fuel v with
  | top => simp [heq] at bound
  | finite n =>
    have hn : n ≤ 0 := by simpa [heq] using bound
    simpa [Nat.eq_zero_of_le_zero hn]

/-- Graph-locality depends only on incoming live edges and seed information on
an ancestor-closed region. Arbitrary components outside that region are ignored. -/
theorem derivable_locality (left right : ProofGraph) (price : GraphEdge → Nat)
    (leftSeeds rightSeeds : List Nat) (region : Nat → Prop)
    (sameSeeds : ∀ v, region v → (v ∈ leftSeeds ↔ v ∈ rightSeeds))
    (sameIncoming : ∀ v, region v → incoming left v = incoming right v)
    (closed : ∀ v, region v → ∀ edge ∈ incoming left v,
      ∀ p ∈ edge.premises, region p) (fuel v n : Nat) (hv : region v) :
    Derivable left price leftSeeds fuel v n ↔ Derivable right price rightSeeds fuel v n := by
  induction fuel generalizing v n with
  | zero => exact sameSeeds v hv
  | succ fuel ih =>
    simp only [Derivable]
    constructor
    · rintro (hs | ⟨edge, he, hc, hp⟩)
      · exact Or.inl ((sameSeeds v hv).mp hs)
      · exact Or.inr ⟨edge, (sameIncoming v hv) ▸ he, hc,
          fun p hm => (ih p _ (closed v hv edge he p hm)).mp (hp p hm)⟩
    · rintro (hs | ⟨edge, he, hc, hp⟩)
      · exact Or.inl ((sameSeeds v hv).mpr hs)
      · have old : edge ∈ incoming left v := (sameIncoming v hv).symm ▸ he
        exact Or.inr ⟨edge, old, hc,
          fun p hm => (ih p _ (closed v hv edge old p hm)).mpr (hp p hm)⟩

/-- Changing only disconnected components or seeds off the live ancestor region
preserves every min-max depth, including top and fuel-boundary cases. -/
theorem off_path_invariance (left right : ProofGraph) (weight : EdgeCost → Nat)
    (leftSeeds rightSeeds : List Nat) (region : Nat → Prop)
    (sameSeeds : ∀ v, region v → (v ∈ leftSeeds ↔ v ∈ rightSeeds))
    (sameIncoming : ∀ v, region v → incoming left v = incoming right v)
    (closed : ∀ v, region v → ∀ edge ∈ incoming left v,
      ∀ p ∈ edge.premises, region p) (fuel v : Nat) (hv : region v) :
    depthFuel left weight leftSeeds fuel v = depthFuel right weight rightSeeds fuel v := by
  apply bound_ext
  intro n
  rw [depthFuel_le_iff_derivable, depthFuel_le_iff_derivable]
  exact derivable_locality left right _ leftSeeds rightSeeds region sameSeeds
    sameIncoming closed fuel v n hv

/-- No artificial fuel bound is imposed on the mathematical least-cost semantics. -/
def Reachable (graph : ProofGraph) (price : GraphEdge → Nat) (seeds : List Nat)
    (v n : Nat) : Prop := ∃ fuel, Derivable graph price seeds fuel v n

private theorem eliminate_zero_seed (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (a zeroFuel : Nat)
    (zero : Derivable graph price seeds zeroFuel a 0) (fuel v n : Nat)
    (h : Derivable graph price (a :: seeds) fuel v n) :
    Derivable graph price seeds (fuel + zeroFuel) v n := by
  induction fuel generalizing v n with
  | zero =>
    rcases List.mem_cons.mp h with rfl | hs
    · simpa using derivable_budget_mono graph price seeds zeroFuel v 0 n (Nat.zero_le _) zero
    · simpa using seed_derivable graph price seeds zeroFuel v n hs
  | succ fuel ih =>
    rw [Nat.succ_add]
    rcases h with hs | ⟨edge, he, hc, hp⟩
    · rcases List.mem_cons.mp hs with rfl | hs
      · have hzero := derivable_budget_mono graph price seeds zeroFuel v 0 n (Nat.zero_le _) zero
        have h := derivable_fuel_mono graph price seeds zeroFuel v n (fuel + 1) hzero
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      · exact seed_derivable graph price seeds _ v n hs
    · exact Or.inr ⟨edge, he, hc, fun p hm => ih p _ (hp p hm)⟩

/-- A zero-cost derived fact is redundant as a seed for fixed local prices.
The quantification over fuel avoids a false claim at an unsaturated table. -/
theorem zero_seed_redundant (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (a : Nat) (zero : Reachable graph price seeds a 0) (w n : Nat) :
    Reachable graph price (a :: seeds) w n ↔ Reachable graph price seeds w n := by
  obtain ⟨zeroFuel, hz⟩ := zero
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel + zeroFuel, eliminate_zero_seed graph price seeds a zeroFuel hz fuel w n h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel, derivable_mono graph price price seeds (a :: seeds)
      (by intro v hv; exact List.mem_cons_of_mem a hv) (by intro e; exact Nat.le_refl _) fuel w n h⟩

/-- Infimum of reachable finite costs; no proof or optimal value is assumed. -/
noncomputable def semanticDepth (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (v : Nat) : WithTop Nat :=
  sInf ((fun n : Nat => (n : WithTop Nat)) '' {n | Reachable graph price seeds v n})

theorem semanticDepth_eq_zero_iff (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (v : Nat) :
    semanticDepth graph price seeds v = 0 ↔ Reachable graph price seeds v 0 := by
  constructor
  · intro zero
    by_contra missing
    have lower : (1 : WithTop Nat) ≤ semanticDepth graph price seeds v := by
      apply le_sInf
      rintro x ⟨n, hn, rfl⟩
      have positive : 1 ≤ n := by
        by_contra h
        have : n = 0 := by omega
        exact missing (this ▸ hn)
      exact WithTop.coe_le_coe.mpr positive
    simpa [zero] using lower
  · intro reachable
    apply le_antisymm
    · exact sInf_le ⟨0, reachable, rfl⟩
    · exact bot_le

/-- The full least min-max distance is unchanged by adding a zero-cost seed,
with fixed local prices. -/
theorem zero_seed_depth_eq (graph : ProofGraph) (price : GraphEdge → Nat)
    (seeds : List Nat) (a : Nat) (zero : Reachable graph price seeds a 0) (w : Nat) :
    semanticDepth graph price (a :: seeds) w = semanticDepth graph price seeds w := by
  unfold semanticDepth
  congr 2
  ext n
  exact zero_seed_redundant graph price seeds a zero w n

/-- A deterministic statement reconstructor may return both a price and its
actual premises. No author proof is an input. -/
def statementReconstruction (graph : ProofGraph) (seeds : List Nat)
    (rebuild : GraphEdge → List Nat → GraphEdge) : ProofGraph :=
  {graph with edges := graph.edges.map fun e => rebuild e (statementPremises e seeds)}

/-- Analytic premises are already visible before they become seeds. -/
theorem analytic_seed_visibility (edge : GraphEdge) (seeds : List Nat) (a : Nat)
    (analytic : a ∈ edge.premises → a ∈ edge.analytic) :
    statementPremises edge (a :: seeds) = statementPremises edge seeds := by
  apply List.filter_congr
  intro p hp
  by_cases h : p = a
  · subst p
    simp [statementPremises, analytic hp]
  · simp [List.contains_cons, h, Ne.symm h]

theorem analytic_seed_reconstruction_eq (graph : ProofGraph) (seeds : List Nat) (a : Nat)
    (rebuild : GraphEdge → List Nat → GraphEdge)
    (analytic : ∀ e ∈ graph.edges, a ∈ e.premises → a ∈ e.analytic) :
    statementReconstruction graph (a :: seeds) rebuild =
      statementReconstruction graph seeds rebuild := by
  unfold statementReconstruction
  congr 1
  apply List.map_congr_left
  intro e he
  rw [analytic_seed_visibility e seeds a (analytic e he)]

/-- A zero-depth fact analytic for every consumer changes neither local
reconstruction (including actual premises) nor any least min-max distance. -/
theorem analytic_zero_seed_depth_eq (graph : ProofGraph) (seeds : List Nat) (a : Nat)
    (rebuild : GraphEdge → List Nat → GraphEdge) (price : GraphEdge → Nat)
    (analytic : ∀ e ∈ graph.edges, a ∈ e.premises → a ∈ e.analytic)
    (zero : semanticDepth (statementReconstruction graph seeds rebuild) price seeds a = 0)
    (w : Nat) :
    semanticDepth (statementReconstruction graph (a :: seeds) rebuild) price (a :: seeds) w =
      semanticDepth (statementReconstruction graph seeds rebuild) price seeds w := by
  rw [analytic_seed_reconstruction_eq graph seeds a rebuild analytic]
  exact zero_seed_depth_eq _ price seeds a
    ((semanticDepth_eq_zero_iff _ price seeds a).mp zero) w

/-- Adding an existing seed changes no visible premise list or derivation. -/
theorem existing_seed_depth_eq (graph : ProofGraph) (seeds : List Nat) (a : Nat)
    (rebuild : GraphEdge → List Nat → GraphEdge) (price : GraphEdge → Nat)
    (member : a ∈ seeds) (w : Nat) :
    semanticDepth (statementReconstruction graph (a :: seeds) rebuild) price (a :: seeds) w =
      semanticDepth (statementReconstruction graph seeds rebuild) price seeds w := by
  have same : statementReconstruction graph (a :: seeds) rebuild =
      statementReconstruction graph seeds rebuild := by
    unfold statementReconstruction
    congr 1
    apply List.map_congr_left
    intro e he
    congr 1
    unfold statementPremises
    apply List.filter_congr
    intro p hp
    by_cases h : p = a
    · subst p; simp [member]
    · simp [List.contains_cons, h, Ne.symm h]
  rw [same]
  exact zero_seed_depth_eq _ price seeds a ⟨0, member⟩ w

/-- If the strongest R closes every local declaration, every reachable vertex
has zero depth. Unreachable vertices stay top instead of becoming false facts. -/
theorem top_reference_zero (graph : ProofGraph) (seeds : List Nat) (fuel v n : Nat)
    (reachable : Derivable graph (fun _ => 0) seeds fuel v n) :
    depthFuel graph (fun _ => 0) seeds fuel v = .finite 0 := by
  have lower : Derivable graph (fun _ => 0) seeds fuel v 0 := by
    induction fuel generalizing v n with
    | zero => exact reachable
    | succ fuel ih =>
      rcases reachable with hs | ⟨edge, he, _, hp⟩
      · exact Or.inl hs
      · exact Or.inr ⟨edge, he, Nat.zero_le _, fun p hm => ih p _ (hp p hm)⟩
  have bound := (depthFuel_le_iff_derivable graph (fun _ => 0) seeds fuel v 0).mpr lower
  cases heq : depthFuel graph (fun _ => 0) seeds fuel v with
  | top => simp [heq] at bound
  | finite n =>
    have hn : n ≤ 0 := by simpa [heq] using bound
    simpa [Nat.eq_zero_of_le_zero hn]

/-- The weakest R has no zero-depth route at a nonseed vertex; it prices each
edge one, rather than asserting that an entire multistep graph has depth one. -/
theorem bottom_reference_positive (graph : ProofGraph) (seeds : List Nat)
    (fuel v : Nat) (notSeed : v ∉ seeds) :
    ¬ depthFuel graph (fun _ => 1) seeds fuel v ≤ .finite 0 := by
  rw [depthFuel_le_iff_derivable]
  cases fuel with
  | zero => exact notSeed
  | succ fuel =>
    rintro (hs | ⟨_, _, hc, _⟩)
    · exact notSeed hs
    · exact Nat.not_succ_le_zero 0 hc

/-- The three routes b→s, b→t, s→t retain their actual premises. -/
def triangleGraph (direct via : EdgeCost) : ProofGraph where
  vertices := [{id := 0}, {id := 1}, {id := 2}]
  edges := [{conclusion := 1, premises := [0], cost := .one},
    {conclusion := 2, premises := [0], cost := direct},
    {conclusion := 2, premises := [1], cost := via}]
  root := 2

/-- Both arm distances are calculated by the production recurrence for every
known direct/via price assignment. -/
theorem triangle_distances (direct via : EdgeCost) :
    depthFuel (triangleGraph direct via) costUpper [0] 3 2 =
      .finite (min (costUpper direct) (1 + costUpper via)) ∧
    depthFuel (triangleGraph direct via) costUpper [0, 1] 3 2 =
      .finite (min (costUpper direct) (costUpper via)) := by
  cases direct <;> cases via <;> decide

/-- Strengthening only s→t creates a gain; then strengthening b→t erases it.
Every edge price weakly decreases along this sequence. -/
theorem delta_not_monotone :
    (let original := triangleGraph .one .one
     let middle := triangleGraph .one .zero
     let strongest := triangleGraph .zero .zero
     depthFuel original costUpper [0] 3 2 = .finite 1 ∧
     depthFuel original costUpper [0, 1] 3 2 = .finite 1 ∧
     depthFuel middle costUpper [0] 3 2 = .finite 1 ∧
     depthFuel middle costUpper [0, 1] 3 2 = .finite 0 ∧
     depthFuel strongest costUpper [0] 3 2 = .finite 0 ∧
     depthFuel strongest costUpper [0, 1] 3 2 = .finite 0 ∧
     (1 - 1 : Nat) < 1 - 0 ∧ (1 - 0 : Nat) > 0 - 0) := by
  decide

/-- An empty eligible auxiliary set is never a positive reduction verdict. -/
theorem no_auxiliary_not_nonBindOnly (reading : GraphReading)
    (empty : reading.noAuxiliary = true) : classifyGraph reading ≠ .nonBindOnly := by
  simp [classifyGraph, empty]
  split <;> simp

/-- The classifier cannot turn an unfinished target-part exclusion into content. -/
theorem target_part_incomplete_not_nonBindOnly (reading : GraphReading)
    (incomplete : reading.targetPartComplete = false) :
    classifyGraph reading ≠ .nonBindOnly := by
  simp [classifyGraph, incomplete]
  split <;> simp

/-- Positive classification requires an actual one-to-zero price change,
consuming a selected synthetic seed on the reported optimal route. -/
theorem nonBindOnly_has_witness_edge (reading : GraphReading)
    (positive : classifyGraph reading = .nonBindOnly) :
    ∃ edge ∈ reading.graph.edges, edge.cost = .one ∧ edge.pairedCost = .zero := by
  have witness : hasWitness reading = true := by
    unfold classifyGraph at positive
    split at positive
    · contradiction
    · split at positive
      · rename_i condition
        simp only [Bool.and_eq_true] at condition
        aesop
      · contradiction
  obtain ⟨edge, member, priced⟩ := List.any_eq_true.mp witness
  simp only [isWitnessEdge, Bool.and_eq_true, beq_iff_eq] at priced
  exact ⟨edge, member, priced.1.1, priced.1.2⟩

/-- Excluding every auxiliary vertex as target-part eliminates every eligible
synthetic witness, independently of the supplied numerical intervals. -/
theorem all_target_part_not_nonBindOnly (reading : GraphReading)
    (parts : ∀ v ∈ reading.graph.vertices,
      v.structureSeed = true → v.targetPart = true) :
    classifyGraph reading ≠ .nonBindOnly := by
  intro positive
  have witness : hasWitness reading = true := by
    unfold classifyGraph at positive
    split at positive
    · contradiction
    · split at positive
      · rename_i condition
        simp only [Bool.and_eq_true] at condition
        tauto
      · contradiction
  obtain ⟨edge, _, priced⟩ := List.any_eq_true.mp witness
  simp only [isWitnessEdge, Bool.and_eq_true] at priced
  obtain ⟨p, _, eligible⟩ := List.any_eq_true.mp priced.2
  cases found : reading.graph.vertices.find? (fun v => v.id == p) with
  | none => simp [found] at eligible
  | some v =>
    have member := List.mem_of_find?_eq_some found
    simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true] at eligible
    have targetPart := parts v member (by tauto)
    simp [targetPart] at eligible

private def modelPaired (graph : ProofGraph) : ProofGraph :=
  {graph with edges := graph.edges.map (fun e => {e with cost := e.pairedCost})}

/-- A finite model with a synthetic seed and actual per-arm edge prices. -/
def nondegenerateReading (direct : EdgeCost) : GraphReading := Id.run do
  let graph : ProofGraph := {
    vertices := [{id := 0}, {id := 1, structureSeed := true}, {id := 2}], root := 2
    edges := [
      {conclusion := 1, premises := [0], cost := .zero, pairedCost := .zero},
      {conclusion := 2, premises := [0], cost := direct, pairedCost := direct},
      {conclusion := 2, premises := [1], cost := .one, pairedCost := .zero,
        pairedUsedPremises := [1]}]}
  return {
    graph, baseline := graphInterval graph [0],
    paired := graphInterval (modelPaired graph) [0, 1], selectedSeeds := [1],
    pairedUsesSeed := true, presentationComplete := true, isolated := true,
    structureChecked := true, structureClean := true, witnessEdges := [2]}

/-- Both graph verdicts occur on readings whose distances are computed from
their actual hypergraphs, rather than supplied numerical intervals. -/
theorem graph_nondegeneracy :
    classifyGraph (nondegenerateReading .zero) = .bindOnly ∧
    classifyGraph (nondegenerateReading .one) = .nonBindOnly ∧
    classifyClosure (nondegenerateReading .one) = some .zero := by
  decide +kernel

/-- Assumption-monotone repricing alone does not make zero seeds redundant:
the newly available statement can turn another local edge from one to zero. -/
theorem zero_seed_repricing_counterexample :
    (let r := nondegenerateReading .one
     depthFuel r.graph costUpper [0] 3 1 = .finite 0 ∧
     depthFuel r.graph costUpper [0] 3 2 = .finite 1 ∧
     depthFuel (modelPaired r.graph) costUpper [0, 1] 3 2 = .finite 0 ∧
     ∀ edge ∈ r.graph.edges, costUpper edge.pairedCost ≤ costUpper edge.cost) := by
  decide

/-- A two-edge fine graph and its one-declaration contraction share their
boundary; their local reconstruction prices remain independent observations. -/
def twoStepGraph (cost : EdgeCost) : ProofGraph where
  vertices := [{id := 0}, {id := 1}, {id := 2}]
  root := 2
  edges := [{conclusion := 1, premises := [0], cost},
    {conclusion := 2, premises := [1], cost}]

def contractedGraph (cost : EdgeCost) : ProofGraph where
  vertices := [{id := 0}, {id := 2}]
  root := 2
  edges := [{conclusion := 2, premises := [0], cost}]

/-- Contracting declaration interiors changes both granularity and the object
priced by R. Min-max depth therefore has no unconditional order by granularity. -/
theorem granularity_unordered :
    depthFuel (contractedGraph .one) costUpper [0] 3 2 = .finite 1 ∧
    depthFuel (twoStepGraph .one) costUpper [0] 3 2 = .finite 2 ∧
    depthFuel (twoStepGraph .zero) costUpper [0] 3 2 = .finite 0 ∧
    (1 : Nat) < 2 ∧ (1 : Nat) > 0 := by
  decide

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open LeanInformationAudit.AuricFib.Contract

/-- Boolean features supply four ordinary atoms; the fifth is unused. -/
def featureWindow (x y : Bool) : Window :=
  match x, y with
  | false, false => .zero
  | true, false => .low
  | false, true => .high
  | true, true => .ends

/-- Pushforward of any finite probability distribution along two features. -/
noncomputable def booleanFeatureLaw {α : Type*} [Fintype α]
    (mass : α → ℝ) (x y : α → Bool) (w : Window) : ℝ :=
  ∑ a, if featureWindow (x a) (y a) = w then mass a else 0

/-- The unrestricted FIB encoding is available for arbitrary features and
arbitrary finite distributions, with no independence or search hypothesis. -/
theorem boolean_features_five_mode {α : Type*} [Fintype α]
    (mass : α → ℝ) (x y : α → Bool)
    (nonnegative : ∀ a, 0 ≤ mass a) (normalized : ∑ a, mass a = 1) :
    (∀ w, 0 ≤ booleanFeatureLaw mass x y w) ∧
    (booleanFeatureLaw mass x y .zero + booleanFeatureLaw mass x y .low +
      booleanFeatureLaw mass x y .high + booleanFeatureLaw mass x y .ends +
      booleanFeatureLaw mass x y .middle = 1) ∧
    Pyramid.Z (booleanFeatureLaw mass x y) = 0 ∧
    Pyramid.r (booleanFeatureLaw mass x y) = 1 := by
  have middle : booleanFeatureLaw mass x y .middle = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    cases hx : x a <;> cases hy : y a <;> simp [featureWindow, hx, hy]
  refine ⟨?_, ?_, middle, ?_⟩
  · intro w
    apply Finset.sum_nonneg
    intro a _
    split <;> simp_all
  · unfold booleanFeatureLaw
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    convert normalized using 1
    apply Finset.sum_congr rfl
    intro a _
    cases hx : x a <;> cases hy : y a <;> simp [featureWindow, hx, hy]
  · simp [Pyramid.r, Pyramid.Z, middle]

/-- Product Bernoulli law on two independently chosen data coordinates. -/
noncomputable def independentLaw (a b : ℝ) : Window → ℝ
  | .zero => (1 - a) * (1 - b)
  | .low => a * (1 - b)
  | .high => (1 - a) * b
  | .ends => a * b
  | .middle => 0

/-- The independent-candidate bridge supplies a normalized nonnegative law and
zero delta for all candidate proportions, rather than a fixed numerical law. -/
theorem independent_law_bridge (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) :
    (∀ w, 0 ≤ independentLaw a b w) ∧
    (independentLaw a b .zero + independentLaw a b .low +
      independentLaw a b .high + independentLaw a b .ends +
      independentLaw a b .middle = 1) ∧
    Pyramid.delta (independentLaw a b) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have ha0 := ha.1
    have hb0 := hb.1
    have ha1 : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
    have hb1 : 0 ≤ 1 - b := sub_nonneg.mpr hb.2
    cases w <;> simp only [independentLaw]
    all_goals positivity
  · simp only [independentLaw]
    ring
  · simp only [Pyramid.delta, Pyramid.r, Pyramid.Z, Pyramid.kappa,
      Pyramid.X, Pyramid.Y, independentLaw]
    ring

/-- Coupling varies the joint coordinate while both marginals stay fixed. -/
noncomputable def couplingLaw (a b joint : ℝ) : Window → ℝ
  | .zero => 1 - a - b + joint
  | .low => a - joint
  | .high => b - joint
  | .ends => joint
  | .middle => 0

/-- Two distinct feasible couplings with the same marginals are separated.
The four positivity assumptions specify a real interior family, not mere
sharing of syntax or an assertion that a single distribution is strict. -/
theorem coupling_law_bridge (a b k l : ℝ)
    (hk : 0 < 1 - a - b + k ∧ 0 < a - k ∧ 0 < b - k ∧ 0 < k)
    (hl : 0 < 1 - a - b + l ∧ 0 < a - l ∧ 0 < b - l ∧ 0 < l)
    (different : k ≠ l) :
    (∀ w, 0 ≤ couplingLaw a b k w ∧ 0 ≤ couplingLaw a b l w) ∧
    (couplingLaw a b k .zero + couplingLaw a b k .low +
      couplingLaw a b k .high + couplingLaw a b k .ends +
      couplingLaw a b k .middle = 1) ∧
    Pyramid.CoarseEq (couplingLaw a b k) (couplingLaw a b l) ∧
    Pyramid.delta (couplingLaw a b k) ≠ Pyramid.delta (couplingLaw a b l) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    cases w <;> simp only [couplingLaw] <;> constructor <;> linarith [hk.1, hk.2.1,
      hk.2.2.1, hk.2.2.2, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2]
  · simp only [couplingLaw]
    ring
  · simp only [Pyramid.CoarseEq, Pyramid.X, Pyramid.Y, Pyramid.Z, couplingLaw]
    constructor
    · ring
    constructor
    · ring
    · trivial
  · simp only [Pyramid.delta, Pyramid.r, Pyramid.X, Pyramid.Y, Pyramid.Z,
      Pyramid.kappa, couplingLaw]
    intro equality
    apply different
    nlinarith

/-- Separation already occurs on a two-point, explicitly enumerable family;
strictness alone supplies no growing search-space lower bound. -/
theorem two_point_strict_family :
    (let law := fun t : Bool => couplingLaw (1 / 2) (1 / 2)
       (if t then 3 / 8 else 1 / 8)
     Pyramid.CoarseEq (law false) (law true) ∧
     Pyramid.delta (law false) ≠ Pyramid.delta (law true) ∧
     (Finset.univ : Finset Bool).card = 2) := by
  dsimp
  have h := coupling_law_bridge (1 / 2) (1 / 2) (1 / 8) (3 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.2.2.1, h.2.2.2, by decide⟩

#print axioms triangle_distances
#print axioms delta_not_monotone
#print axioms no_auxiliary_not_nonBindOnly
#print axioms target_part_incomplete_not_nonBindOnly
#print axioms nonBindOnly_has_witness_edge
#print axioms all_target_part_not_nonBindOnly
#print axioms graph_nondegeneracy
#print axioms zero_seed_repricing_counterexample
#print axioms granularity_unordered
#print axioms boolean_features_five_mode
#print axioms independent_law_bridge
#print axioms coupling_law_bridge
#print axioms two_point_strict_family

#print axioms derivable_edge_simulation
#print axioms cut_dominates_given
#print axioms zero_baseline_monotone
#print axioms off_path_invariance
#print axioms zero_seed_depth_eq
#print axioms semanticDepth_eq_zero_iff
#print axioms analytic_seed_visibility
#print axioms analytic_seed_reconstruction_eq
#print axioms analytic_zero_seed_depth_eq
#print axioms existing_seed_depth_eq
#print axioms top_reference_zero
#print axioms bottom_reference_positive
#print axioms dpTable_eq_depthFuel
#print axioms dpRounds_le_iff_derivable
#print axioms edge_extension_preserves_derivations
#print axioms outside_zero_shortcut
#print axioms unknown_not_nonBindOnly
#print axioms unchecked_presentation_not_nonBindOnly
#print axioms depthFuel_monotone
#print axioms lower_le_upper
#print axioms depthFuel_le_iff_derivable
#print axioms derivable_mono
#print axioms zero_path_sound
#print axioms incomplete_not_nonBindOnly
#print axioms graph_verdict_partition
end LeanInformationAudit.Tests.SearchReduction.GraphModel
