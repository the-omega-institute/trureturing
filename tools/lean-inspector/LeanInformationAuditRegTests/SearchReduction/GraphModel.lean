import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Graph

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
