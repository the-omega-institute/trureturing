/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_sort_minimum_base; instance=D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.parallelSourceInput
   digest: Signed source occurrence cycles and minimum natural block bases. -/
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveBranchReduction
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeComputedEpochPotential
/-! Integer consistency and minimum natural ranks on the actual source graph. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover
open NativePositiveBranchReduction NativePositiveImageCover NativeTermUnification
open NativeGroundSolutionSpace Maths Maths.MaxPlusPotential
open Lambda Strata.Util
variable {X : Type} [DecidableEq X]
/-- Select one residual sort without identifying repeated or parallel edges. -/
def sortEdges (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  (sourceOffsetEdges B s).filter (fun e => e.1.1.2.2 == j)
abbrev Edge (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  Fin (sortEdges B s j).length × Bool
def signedGraph (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    EdgeGraph (Occurrence X) (Edge B s j) where
  source e := if e.2 then ((sortEdges B s j).get e.1).1.1
    else ((sortEdges B s j).get e.1).1.2
  target e := if e.2 then ((sortEdges B s j).get e.1).1.2
    else ((sortEdges B s j).get e.1).1.1
def signedWeight (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (e : Edge B s j) : Int :=
  if e.2 then -((sortEdges B s j).get e.1).2 else ((sortEdges B s j).get e.1).2
def ZeroCycles (B : List (BranchEquation X)) (s : X → Term X) (j : X) : Prop :=
  ∀ (v : Occurrence X) (c : (signedGraph B s j).Walk v v),
    walkWeight (signedWeight B s j) c = 0
def Potential (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) : Prop :=
  ∀ e ∈ sortEdges B s j, δ e.1.1 = δ e.1.2 + e.2
/-- The leaf carrier is arbitrary; nonemptiness is needed only to detect
inconsistent cycles. No shape or rank bound is imposed. -/
def BlockSolution (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    {L : Type} (u : Occurrence X → L → Nat) : Prop :=
  ∀ e ∈ sortEdges B s j, ∀ l, (u e.1.1 l : Int) = (u e.1.2 l : Int) + e.2
private theorem potential_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) :
    Potential B s j δ ↔ IsPotential (signedGraph B s j) (signedWeight B s j) δ := by
  constructor
  · intro h e
    have eq := h _ (List.get_mem (sortEdges B s j) e.1)
    cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
    have hf := h (i, false)
    have hb := h (i, true)
    simp only [signedGraph, signedWeight, Bool.false_eq_true, ↓reduceIte] at hf hb
    omega
private theorem walk_exact {B : List (BranchEquation X)} {s : X → Term X} {j : X}
    {δ : Occurrence X → Int} (h : Potential B s j δ)
    {v w : Occurrence X} (c : (signedGraph B s j).Walk v w) :
    walkWeight (signedWeight B s j) c = δ w - δ v := by
  induction c with
  | nil => simp [walkWeight]
  | concat c e legal ih =>
      have eq := h _ (List.get_mem (sortEdges B s j) e.1)
      rw [walkWeight_concat, ih]
      subst legal
      cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega
theorem zeroCycles_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    ZeroCycles B s j ↔ ∃ δ, Potential B s j δ := by
  constructor
  · intro h
    obtain ⟨δ, hδ⟩ :=
      (exists_isPotential_iff_forall_closedWalk_nonpos
        (G := signedGraph B s j) (signedWeight B s j)).mpr (fun v c => (h v c).le)
    exact ⟨δ, (potential_iff B s j δ).mpr hδ⟩
  · rintro ⟨δ, hδ⟩ v c
    simpa using walk_exact hδ c
/-- Enumerate the two signed orientations of every actual source edge.
The list retains separate indices for repeated and parallel comparisons. -/
def signedEdges (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    List (Edge B s j) :=
  (List.finRange (sortEdges B s j).length).flatMap fun i => [(i, false), (i, true)]
private theorem signedEdges_complete (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (e : Edge B s j) : e ∈ signedEdges B s j := by
  rcases e with ⟨i, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  cases b <;> simp
/-- Finite max-plus relaxation on the original source occurrence graph.
Zero is a lower bound at every vertex, including isolated occurrences. -/
def sourceRelaxation (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    Nat → Occurrence X → Int
  | 0, _ => 0
  | t + 1, v =>
      ((signedEdges B s j).map fun e =>
        if (signedGraph B s j).target e = v then
          sourceRelaxation B s j t ((signedGraph B s j).source e) + signedWeight B s j e
        else 0).foldr max 0
/-- An executable integer potential candidate, with no solution, potential,
path, cycle decision or classical choice supplied as input. The number of
rounds is the number of signed indexed source edges. -/
def computedSourcePotential (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    Occurrence X → Int :=
  sourceRelaxation B s j (2 * (sortEdges B s j).length)
private theorem sourceRelaxation_nonneg (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (v : Occurrence X) :
    0 ≤ sourceRelaxation B s j t v := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact NativeComputedEpochPotential.base_le_fold_max _ 0
private theorem sourceRelaxation_edge (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (e : Edge B s j) :
    sourceRelaxation B s j t ((signedGraph B s j).source e) + signedWeight B s j e ≤
      sourceRelaxation B s j (t + 1) ((signedGraph B s j).target e) := by
  apply List.le_max_of_le' (0 : Int)
  · exact List.mem_map.mpr ⟨e, signedEdges_complete B s j e, rfl⟩
  · simp only [ite_true]
    exact le_rfl
private theorem source_walk_le_relaxation (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) {v w : Occurrence X}
    (c : (signedGraph B s j).Walk v w) (hlen : c.length ≤ t) :
    walkWeight (signedWeight B s j) c ≤ sourceRelaxation B s j t w := by
  induction t generalizing v w with
  | zero =>
      cases c with
      | nil => simp [walkWeight, EdgeGraph.Walk.edges, sourceRelaxation]
      | concat c e legal => simp at hlen
  | succ t ih =>
      cases c with
      | nil => simpa [walkWeight, EdgeGraph.Walk.edges] using
          sourceRelaxation_nonneg B s j (t + 1) v
      | concat c e legal =>
          have hp := ih c (by simpa using Nat.le_of_succ_le_succ hlen)
          have he := sourceRelaxation_edge B s j t e
          rw [legal] at he
          rw [walkWeight_concat]
          omega
private theorem sourceRelaxation_attained (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (v : Occurrence X) :
    ∃ (start : Occurrence X) (c : (signedGraph B s j).Walk start v),
      c.length ≤ t ∧ sourceRelaxation B s j t v = walkWeight (signedWeight B s j) c := by
  induction t generalizing v with
  | zero => exact ⟨v, .nil, le_rfl, by simp [sourceRelaxation, walkWeight, EdgeGraph.Walk.edges]⟩
  | succ t ih =>
      apply NativeComputedEpochPotential.fold_max_property (b := 0)
        (P := fun z => ∃ (start : Occurrence X) (c : (signedGraph B s j).Walk start v),
          c.length ≤ t + 1 ∧ z = walkWeight (signedWeight B s j) c)
      · exact ⟨v, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩
      · intro z hz
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz
        by_cases he : (signedGraph B s j).target e = v
        · simp only [if_pos he]
          obtain ⟨start, c, hlen, hvalue⟩ := ih ((signedGraph B s j).source e)
          refine ⟨start, (c.concat e rfl).castFinish he, ?_, ?_⟩
          · simpa using Nat.add_le_add_right hlen 1
          · rw [walkWeight_castFinish, walkWeight_concat, hvalue]
        · simp only [if_neg he]
          exact ⟨v, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩
private theorem computed_source_potential (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (good : ZeroCycles B s j) :
    Potential B s j (computedSourcePotential B s j) := by
  apply (potential_iff B s j _).mpr
  intro e
  obtain ⟨start, c, _, hvalue⟩ := sourceRelaxation_attained B s j
    (2 * (sortEdges B s j).length) ((signedGraph B s j).source e)
  obtain ⟨pruned, hnodup, hweight⟩ := exists_nodup_visited_walkWeight_le
    (fun v c => (good v c).le) (c.concat e rfl).length (c.concat e rfl) le_rfl
  have hcard : pruned.length ≤ 2 * (sortEdges B s j).length := by
    simpa only [EdgeGraph.Walk.edges_length, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.mul_comm] using
      pruned.edges_nodup_of_visited_nodup hnodup |>.length_le_card
  have hbound := source_walk_le_relaxation B s j _ pruned hcard
  rw [walkWeight_concat] at hweight
  change sourceRelaxation B s j _ ((signedGraph B s j).source e) + signedWeight B s j e ≤
    sourceRelaxation B s j _ ((signedGraph B s j).target e)
  omega
/-- Check every original indexed source equation against the finite relaxation
candidate. Empty edge lists are accepted, and no vertex or integer bound is
assumed. All arithmetic and equality tests are executable. -/
def checkSourceConsistency (B : List (BranchEquation X)) (s : X → Term X) (j : X) : Bool :=
  (sortEdges B s j).all fun e => decide
    (computedSourcePotential B s j e.1.1 = computedSourcePotential B s j e.1.2 + e.2)
private theorem check_source_consistency_iff_potential
    (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    checkSourceConsistency B s j = true ↔ Potential B s j (computedSourcePotential B s j) := by
  simp only [checkSourceConsistency, List.all_eq_true, decide_eq_true_eq, Potential]
/-- The finite executable check is sound and complete for the original
condition on all closed walks of the labelled signed source graph. -/
theorem source_consistency_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    checkSourceConsistency B s j = true ↔ ZeroCycles B s j := by
  rw [check_source_consistency_iff_potential]
  constructor
  · intro h
    exact (zeroCycles_iff B s j).mpr ⟨computedSourcePotential B s j, h⟩
  · exact computed_source_potential B s j
/-- Return a certified computed potential precisely when the finite check
accepts. The certificate is erased during execution; rejection returns none. -/
def effectiveSourcePotential (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    Option {δ : Occurrence X → Int // Potential B s j δ} :=
  if h : checkSourceConsistency B s j = true then
    some ⟨computedSourcePotential B s j,
      (check_source_consistency_iff_potential B s j).mp h⟩
  else none
/-- Original shifts U=V+3, U=V+3, U=V+4 on their common residual sort. -/
def parallelSourceInput : List (BranchEquation Bool) × (Bool → Term Bool) × Bool :=
  ([.shift true 3 false, .shift true 3 false, .shift true 4 false],
    (fun _ => .of (.inr false)), false)
private theorem edge_spec (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {e : (Occurrence X × Occurrence X) × Int}
    (he : e ∈ sourceOffsetEdges B (action p S)) :
    e.1.1 ∈ occurrenceVertices p (action p S) ∧
    e.1.2 ∈ occurrenceVertices p (action p S) ∧ e.1.1.2.2 = e.1.2.2.2 := by
  apply (mgu_occurrence_graph_exact p (shapeEquations B) S hok).2.1
  rw [← source_comparison_graph_identification]
  exact List.mem_map.mpr ⟨e, he, rfl⟩
private theorem connected_sort (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = w.2.2 := by
  induction h with
  | rel a b he =>
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have hs := (edge_spec p B S hok he).2.2
      simpa only [eq] using hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
private theorem common_difference (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) {f g : Occurrence X → Int}
    (hf : Potential B (action p S) j f) (hg : Potential B (action p S) j g)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = j → f v - g v = f w - g w := by
  induction h with
  | rel v w he =>
      intro hv
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have pair : e.1 = (v,w) := eq
      have mem : e ∈ sortEdges B (action p S) j := by
        simp only [sortEdges, List.mem_filter, beq_iff_eq]
        exact ⟨he, by simpa only [pair] using hv⟩
      have h1 := hf e mem
      have h2 := hg e mem
      simp only [pair] at h1 h2
      omega
  | refl v => intro _; rfl
  | symm v w h ih =>
      intro hw
      have hv : v.2.2 = j := (connected_sort p B S hok h).trans hw
      exact (ih hv).symm
  | trans v w z h1 h2 ih1 ih2 =>
      intro hv
      have hw : w.2.2 = j := (connected_sort p B S hok h1).symm.trans hv
      exact (ih1 hv).trans (ih2 hw)
/-- The actual source comparison graph admits one minimum natural base per
occurring sort. Nonzero cycles exclude solutions on every inhabited leaf
carrier; zero cycles classify all natural solutions, including a singleton
isolated occurrence. The theorem does not assert native code reconstruction. -/
theorem source_sort_minimum_base (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j) :
    (¬ ZeroCycles B (action p S) j →
      ∀ (L : Type) [Nonempty L] (u : Occurrence X → L → Nat),
        ¬ BlockSolution B (action p S) j u) ∧
    (ZeroCycles B (action p S) j →
      ∃ (δ : Occurrence X → Int) (b : Occurrence X) (a : Occurrence X → Nat),
        δ = computedSourcePotential B (action p S) j ∧
        Potential B (action p S) j δ ∧
        b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          δ b ≤ δ v ∧ (a v : Int) = δ v - δ b) ∧
        (∀ (L : Type) (u : Occurrence X → L → Nat),
          BlockSolution B (action p S) j u ↔
          ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
            ∀ l, u v l = u b l + a v)) := by
  classical
  constructor
  · intro bad L _ u hu
    let l : L := Classical.choice (inferInstance : Nonempty L)
    apply bad
    exact (zeroCycles_iff B (action p S) j).mpr ⟨fun v => (u v l : Int), fun e he => hu e he l⟩
  · intro good
    have accepted := (source_consistency_iff B (action p S) j).mpr good
    have available : (effectiveSourcePotential B (action p S) j).isSome := by
      simp [effectiveSourcePotential, accepted]
    let certified := (effectiveSourcePotential B (action p S) j).get available
    let δ := certified.val
    have hδ : Potential B (action p S) j δ := certified.property
    have hcomputed : δ = computedSourcePotential B (action p S) j := by
      simp [δ, certified, effectiveSourcePotential, accepted]
    let V := (occurrenceVertices p (action p S)).toFinset.filter (fun v => v.2.2 = j)
    have hV : V.Nonempty := by
      obtain ⟨v, hv, hj⟩ := occurs
      exact ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩⟩
    obtain ⟨b, hb, hmin⟩ := V.exists_min_image δ hV
    have hb' := Finset.mem_filter.mp hb
    let a : Occurrence X → Nat := fun v => (δ v - δ b).toNat
    have ha : ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
        δ b ≤ δ v ∧ (a v : Int) = δ v - δ b := by
      intro v hv hj
      have hm := hmin v (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩)
      exact ⟨hm, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨δ, b, a, hcomputed, hδ, List.mem_toFinset.mp hb'.1, hb'.2, ?_, ha, ?_⟩
    · simp [a]
    · intro L u
      constructor
      · intro hu v hv hj l
        have conn := (source_connected_iff_sort p B S hok b v
          (List.mem_toFinset.mp hb'.1) hv).mpr (hb'.2.trans hj.symm)
        have hd := common_difference p B S hok j
          (f := fun w => (u w l : Int)) (g := δ)
          (fun e he => hu e he l) hδ conn hb'.2
        have hav := (ha v hv hj).2
        omega
      · intro hu e he l
        have he' := (List.mem_filter.mp he).1
        have hj : e.1.1.2.2 = j := by
          simpa only [beq_iff_eq] using (List.mem_filter.mp he).2
        have spec := edge_spec p B S hok he'
        have hu1 := hu e.1.1 spec.1 hj l
        have hu2 := hu e.1.2 spec.2.1 (spec.2.2.symm.trans hj) l
        have ha1 := (ha e.1.1 spec.1 hj).2
        have ha2 := (ha e.1.2 spec.2.1 (spec.2.2.symm.trans hj)).2
        have hed := hδ e he
        omega
/-- Leaves retain their ordered positions even when all ranks coincide. -/
def Leaves : FreeMagma Unit → Type
  | .of _ => Unit
  | .mul A B => Leaves A ⊕ Leaves B

instance leavesNonempty : (T : FreeMagma Unit) → Nonempty (Leaves T)
  | .of _ => inferInstanceAs (Nonempty Unit)
  | .mul A B =>
      letI := leavesNonempty A
      inferInstanceAs (Nonempty (Leaves A ⊕ Leaves B))
def fill : (T : FreeMagma Unit) → (Leaves T → Nat) → NativeFiniteNormalInversion.Code
  | .of _, r => .of (r ())
  | .mul A B, r => .mul (fill A (fun l => r (.inl l))) (fill B (fun l => r (.inr l)))
private theorem fill_shift (T : FreeMagma Unit) (r : Leaves T → Nat) (a : Nat) :
    fill T (fun l => r l + a) = NativeFiniteNormalInversion.shiftCode a (fill T r) := by
  induction T using FreeMagma.rec with
  | of => rfl
  | mul A B ihA ihB =>
      exact congrArg₂ FreeMagma.mul (ihA _) (ihB _)
private theorem normal_subtree (C : NativeFiniteNormalInversion.Code) (q : List Bool)
    (D : NativeFiniteNormalInversion.Code) (hC : NativeFiniteNormalInversion.Normal C)
    (h : subtree C q = some D) : NativeFiniteNormalInversion.Normal D := by
  induction q generalizing C with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      exact h ▸ hC
  | cons b q ih =>
      cases C with
      | of n => cases h
      | mul A B =>
          cases b
          · exact ih A hC.1 h
          · exact ih B hC.2.1 h
/-- Actual occurrence subtrees turn the minimum rank base into a normal
native block. Rank inverses and expansion recover the identical blocks. -/
theorem source_canonical_block_recovery (p : Presentation X)
    (B : List (BranchEquation X)) (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j)
    (good : ZeroCycles B (action p S) j) :
    ∃ (b : Occurrence X) (a : Occurrence X → Nat),
      b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
      (∀ o ∈ occurrenceVertices p (action p S), o.2.2 = j →
        computedSourcePotential B (action p S) j b ≤ computedSourcePotential B (action p S) j o ∧
        (a o : Int) = computedSourcePotential B (action p S) j o -
          computedSourcePotential B (action p S) j b) ∧
      ∀ (T : FreeMagma Unit) (u : Occurrence X → Leaves T → Nat)
        (C : X → NativeFiniteNormalInversion.Code),
        BlockSolution B (action p S) j u →
        (∀ x, NativeFiniteNormalInversion.Normal (C x)) →
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          subtree (C v.1) v.2.1 = some (fill T (u v))) →
        NativeFiniteNormalInversion.Normal (fill T (u b)) ∧
        ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) ∧
          NativeFiniteNormalInversion.expand (fill T (u v)) =
            GenealogicalFiberTransport.substitution^[a v]
              (NativeFiniteNormalInversion.expand (fill T (u b))) ∧
          (∀ l, NativeFiniteNormalInversion.rankInverse (a v) (u v l) = some (u b l)) := by
  obtain ⟨δ, b, a, hcomp, hδ, hb, hj, hab, hmin, law⟩ :=
    (source_sort_minimum_base p B S hok j occurs).2 good
  subst δ
  refine ⟨b, a, hb, hj, hab, hmin, ?_⟩
  intro T u C hu hC actual
  have ranks := (law (Leaves T) u).mp hu
  refine ⟨normal_subtree (C b.1) b.2.1 _ (hC b.1) (actual b hb hj), ?_⟩
  intro v hv hvj
  have heq : u v = fun l => u b l + a v := funext (ranks v hv hvj)
  have code : fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) := by
    rw [heq]
    exact fill_shift T (u b) (a v)
  refine ⟨code, ?_, ?_⟩
  · rw [code]
    exact NativeFiniteNormalInversion.shift_expand (a v) (fill T (u b))
  · intro l
    exact ((NativeFiniteNormalInversion.exact_natural_rank_inverse (a v) (u v l)).1
      (u b l)).mpr (ranks v hv hvj l).symm
/-- The actual code at an occurrence address. Invalid addresses have a
fixed default; all results below prove validity before using a block. -/
def occurrenceCode (C : X → NativeFiniteNormalInversion.Code) (v : Occurrence X) :
    NativeFiniteNormalInversion.Code :=
  (subtree (C v.1) v.2.1).getD (.of 0)
private def Fits (C : X → NativeFiniteNormalInversion.Code) :
    Term (Occurrence X) → NativeFiniteNormalInversion.Code → Prop
  | .of (.inl _), .of _ => True
  | .of (.inl _), .mul _ _ => False
  | .of (.inr v), D => D = occurrenceCode C v
  | .mul A B, .mul D E => Fits C A D ∧ Fits C B E
  | .mul _ _, .of _ => False
private theorem subtree_child {A : Type} (C : FreeMagma A) (q : List Bool)
    (D E : FreeMagma A) (h : subtree C q = some (.mul D E)) :
    subtree C (q ++ [false]) = some D ∧ subtree C (q ++ [true]) = some E := by
  induction q generalizing C with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      subst C
      constructor <;> simp [subtree]
  | cons b q ih =>
      cases C with
      | of a => cases h
      | mul A B => cases b <;> exact ih _ h
private theorem fits_decorate (C : X → NativeFiniteNormalInversion.Code)
    (w : X → NativeGroundSolutionSpace.Source) (x : X) (t : Term X)
    (q : List Bool) (D : NativeFiniteNormalInversion.Code)
    (actual : subtree (C x) q = some D)
    (sh : shape D = evaluate w t) : Fits C (decorateFrom x q t) D := by
  induction t generalizing q D with
  | of a =>
      cases a with
      | inl b => cases D <;> simp_all [shape, evaluate, Fits, decorateFrom]
      | inr j =>
          change D = (subtree (C x) q).getD (.of 0)
          rw [actual]
          rfl
  | mul A B ihA ihB =>
      cases D with
      | of n => cases sh
      | mul D E =>
          have hs : shape D = evaluate w A ∧ shape E = evaluate w B := by
            injection sh with hD hE
            exact ⟨hD, hE⟩
          have hc := subtree_child (C x) q D E actual
          exact ⟨ihA _ _ hc.1 hs.1, ihB _ _ hc.2 hs.2⟩
private theorem fits_offsets (C : X → NativeFiniteNormalInversion.Code)
    (A B : Term (Occurrence X)) (D E : NativeFiniteNormalInversion.Code)
    (a : Nat) (hA : Fits C A D) (hB : Fits C B E)
    (eq : D = NativeFiniteNormalInversion.shiftCode a E) :
    ∀ e ∈ offsetComparisonEdges (a : Int) A B,
      e.2 = (a : Int) ∧ occurrenceCode C e.1.1 =
        NativeFiniteNormalInversion.shiftCode a (occurrenceCode C e.1.2) := by
  induction A generalizing B D E with
  | of b =>
      cases B with
      | of c =>
          cases b with
          | inl b => cases c <;> simp [offsetComparisonEdges]
          | inr v =>
              cases c with
              | inl b => simp [offsetComparisonEdges]
              | inr w =>
                  intro e he
                  have heq : e = ((v, w), (a : Int)) := List.mem_singleton.mp he
                  subst e
                  simp only [Fits] at hA hB
                  exact ⟨rfl, by simpa only [hA, hB] using eq⟩
      | mul l r => simp [offsetComparisonEdges]
  | mul A₁ A₂ ihA ihB =>
      cases B with
      | of c => simp [offsetComparisonEdges]
      | mul U V =>
          cases E with
          | of n => cases hB
          | mul E F =>
              subst D
              rcases hA with ⟨hD, hE⟩
              rcases hB with ⟨hU, hV⟩
              intro e he
              rcases List.mem_append.mp he with he | he
              · exact ihA _ _ _ hD hU rfl e he
              · exact ihB _ _ _ hE hV rfl e he
private theorem actual_source_offsets (B : List (BranchEquation X))
    (s : X → Term X) (C : X → NativeFiniteNormalInversion.Code)
    (factor : ∀ x, evaluate (fun y => shape (C y)) (s x) = shape (C x))
    (sat : ∀ b ∈ B, b.Holds C) :
    ∀ e ∈ sourceOffsetEdges B s, ∃ a : Nat, e.2 = (a : Int) ∧
      occurrenceCode C e.1.1 = NativeFiniteNormalInversion.shiftCode a
        (occurrenceCode C e.1.2) := by
  have fit (x : X) : Fits C (decorate s x) (C x) :=
    fits_decorate C (fun y => shape (C y)) x (s x) [] (C x) (by simp [subtree]) (factor x).symm
  intro e he
  obtain ⟨b, hb, he⟩ := List.mem_flatMap.mp he
  have hs := sat b hb
  cases b with
  | primitive z n => cases he
  | collapse z x y => cases he
  | shift z a x => exact ⟨a, fits_offsets C _ _ _ _ a (fit z) (fit x) hs e he⟩
  | ordinary z x y =>
      refine ⟨0, fits_offsets C _ _ (C z) (.mul (C x) (C y)) 0 (fit z) ?_ ?_ e he⟩
      · exact ⟨fit x, fit y⟩
      · simpa only [NativePositiveBranchReduction.shift_zero, BranchEquation.Holds] using hs
  | same x y =>
      refine ⟨0, fits_offsets C _ _ _ _ 0 (fit x) (fit y) ?_ e he⟩
      simpa only [NativePositiveBranchReduction.shift_zero, BranchEquation.Holds] using hs
private def codeTree : NativeFiniteNormalInversion.Code → FreeMagma Unit
  | .of _ => .of ()
  | .mul A B => .mul (codeTree A) (codeTree B)
private def groundShape : FreeMagma Unit → NativeGroundSolutionSpace.Source
  | .of _ => .of true
  | .mul A B => .mul (groundShape A) (groundShape B)
private theorem codeTree_shape (D : NativeFiniteNormalInversion.Code) :
    groundShape (codeTree D) = shape D := by
  induction D with
  | of n => rfl
  | mul A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB
private def readRanks : (T : FreeMagma Unit) → NativeFiniteNormalInversion.Code → Leaves T → Nat
  | .of _, .of n => fun _ => n
  | .mul A B, .mul D E => Sum.elim (readRanks A D) (readRanks B E)
  | _, _ => fun _ => 0
private theorem fill_readRanks (T : FreeMagma Unit) (D : NativeFiniteNormalInversion.Code)
    (sh : shape D = groundShape T) : fill T (readRanks T D) = D := by
  induction T using FreeMagma.rec generalizing D with
  | of u => cases D with
    | of n => rfl
    | mul A B => cases sh
  | mul A B ihA ihB =>
      cases D with
      | of n => cases sh
      | mul D E =>
          have hs : shape D = groundShape A ∧ shape E = groundShape B := by
            injection sh with hD hE
            exact ⟨hD, hE⟩
          exact congrArg₂ FreeMagma.mul (ihA D hs.1) (ihB E hs.2)
private theorem readRanks_shift (T : FreeMagma Unit) (D : NativeFiniteNormalInversion.Code)
    (sh : shape D = groundShape T) (a : Nat) (l : Leaves T) :
    readRanks T (NativeFiniteNormalInversion.shiftCode a D) l = readRanks T D l + a := by
  induction T using FreeMagma.rec generalizing D with
  | of u => cases D with
    | of n => rfl
    | mul A B => cases sh
  | mul A B ihA ihB =>
      cases D with
      | of n => cases sh
      | mul D E =>
          have hs : shape D = groundShape A ∧ shape E = groundShape B := by
            injection sh with hD hE
            exact ⟨hD, hE⟩
          cases l with
          | inl l => exact ihA D hs.1 l
          | inr l => exact ihB E hs.2 l
private theorem code_at_residual (w : X → NativeGroundSolutionSpace.Source)
    (t : Term X) (D : NativeFiniteNormalInversion.Code) (q : List Bool) (j : X)
    (sh : shape D = evaluate w t)
    (occ : subtree t q = some (.of (.inr j))) :
    ∃ E, subtree D q = some E ∧ shape E = w j := by
  induction q generalizing t D with
  | nil =>
      simp only [subtree, Option.some.injEq] at occ
      subst t
      exact ⟨D, by simp [subtree], sh⟩
  | cons b q ih =>
      cases t with
      | of c => cases occ
      | mul A B =>
          cases D with
          | of n => cases sh
          | mul D E =>
              have hs : shape D = evaluate w A ∧ shape E = evaluate w B := by
                injection sh with hD hE
                exact ⟨hD, hE⟩
              cases b
              · exact ih A D hs.1 occ
              · exact ih B E hs.2 occ
private theorem actual_occurrence_code (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (C : X → NativeFiniteNormalInversion.Code)
    (factor : ∀ x, evaluate (fun y => shape (C y)) (action p S x) = shape (C x))
    (v : Occurrence X) (hv : v ∈ occurrenceVertices p (action p S)) :
    subtree (C v.1) v.2.1 = some (occurrenceCode C v) ∧
      shape (occurrenceCode C v) = shape (C v.2.2) := by
  have occ := (mgu_occurrence_graph_exact p (shapeEquations B) S hok).1 v |>.mp hv
  obtain ⟨D, hD, hs⟩ := code_at_residual (fun y => shape (C y))
    (action p S v.1) (C v.1) v.2.1 v.2.2 (factor v.1).symm occ
  have eq : occurrenceCode C v = D := by simp only [occurrenceCode, hD, Option.getD_some]
  exact ⟨by rw [eq]; exact hD, by rw [eq]; exact hs⟩
private theorem actual_rank_blocks (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (C : X → NativeFiniteNormalInversion.Code)
    (factor : ∀ x, evaluate (fun y => shape (C y)) (action p S x) = shape (C x))
    (sat : ∀ b ∈ B, b.Holds C) (j : X) :
    let T := codeTree (C j)
    let u := fun v => readRanks T (occurrenceCode C v)
    BlockSolution B (action p S) j u ∧
      ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
        subtree (C v.1) v.2.1 = some (fill T (u v)) := by
  dsimp only
  have valid (v : Occurrence X) (hv : v ∈ occurrenceVertices p (action p S))
      (hj : v.2.2 = j) : shape (occurrenceCode C v) = groundShape (codeTree (C j)) := by
    rw [(actual_occurrence_code p B S hok C factor v hv).2, hj, codeTree_shape]
  constructor
  · intro e he l
    have he' := (List.mem_filter.mp he).1
    have hj : e.1.1.2.2 = j := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp he).2
    have spec := edge_spec p B S hok he'
    obtain ⟨a, ha, code⟩ := actual_source_offsets B (action p S) C factor sat e he'
    have hr := readRanks_shift (codeTree (C j)) (occurrenceCode C e.1.2)
      (valid e.1.2 spec.2.1 (spec.2.2.symm.trans hj)) a l
    change (readRanks (codeTree (C j)) (occurrenceCode C e.1.1) l : Int) =
      (readRanks (codeTree (C j)) (occurrenceCode C e.1.2) l : Int) + e.2
    rw [code, hr, ha]
    omega
  · intro v hv hj
    rw [fill_readRanks _ _ (valid v hv hj)]
    exact (actual_occurrence_code p B S hok C factor v hv).1
/-- Explicit primitive positions and residual positions have separate labels. -/
abbrev ScalarPosition (X : Type) := X × List Bool
inductive RankExpression (X : Type) where
  | scalar : ScalarPosition X → RankExpression X
  | constant : Nat → RankExpression X
inductive DecoratedTerm (X : Type) where
  | scalar : Bool → RankExpression X → DecoratedTerm X
  | block : Occurrence X → DecoratedTerm X
  | pair : DecoratedTerm X → DecoratedTerm X → DecoratedTerm X
def RankExpression.value (r : ScalarPosition X → Nat) : RankExpression X → Nat
  | .scalar q => r q
  | .constant n => n
def DecoratedTerm.erase : DecoratedTerm X → Term X
  | .scalar b _ => .of (.inl b)
  | .block o => .of (.inr o.2.2)
  | .pair A B => .mul A.erase B.erase
def DecoratedTerm.value (r : ScalarPosition X → Nat)
    (u : Occurrence X → NativeFiniteNormalInversion.Code) :
    DecoratedTerm X → NativeFiniteNormalInversion.Code
  | .scalar _ n => .of (n.value r)
  | .block o => u o
  | .pair A B => .mul (A.value r u) (B.value r u)
def scalarDecorateFrom (x : X) (q : List Bool) : Term X → DecoratedTerm X
  | .of (.inl b) => .scalar b (.scalar (x,q))
  | .of (.inr j) => .block (x,q,j)
  | .mul A B => .pair (scalarDecorateFrom x (q ++ [false]) A)
      (scalarDecorateFrom x (q ++ [true]) B)
def scalarDecorate (s : X → Term X) (x : X) : DecoratedTerm X :=
  scalarDecorateFrom x [] (s x)
/-- A finite structural inventory. Every leaf equation is scalar or block;
there is no mixed scalar/block equation. -/
inductive ComparisonInventory (X : Type) where
  | scalar : RankExpression X → RankExpression X → Nat → ComparisonInventory X
  | block : Occurrence X → Occurrence X → Nat → ComparisonInventory X
  | both : ComparisonInventory X → ComparisonInventory X → ComparisonInventory X
  | incompatible : ComparisonInventory X
def ComparisonInventory.Holds (r : ScalarPosition X → Nat)
    (u : Occurrence X → NativeFiniteNormalInversion.Code) : ComparisonInventory X → Prop
  | .scalar n m a => (n.value r : Int) = (m.value r : Int) + (a : Int)
  | .block v w a => u v = NativeFiniteNormalInversion.shiftCode a (u w)
  | .both I J => I.Holds r u ∧ J.Holds r u
  | .incompatible => False
def comparisonInventory (a : Nat) : DecoratedTerm X → DecoratedTerm X →
    ComparisonInventory X
  | .scalar _ n, .scalar _ m => .scalar n m a
  | .block v, .block w => .block v w a
  | .pair A B, .pair C D =>
      .both (comparisonInventory a A C) (comparisonInventory a B D)
  | _, _ => .incompatible
private theorem scalar_decorate_erase (x : X) (q : List Bool) (t : Term X) :
    (scalarDecorateFrom x q t).erase = t := by
  induction t generalizing q with
  | of b => cases b <;> rfl
  | mul A B ihA ihB => exact congrArg₂ FreeMagma.mul (ihA _) (ihB _)
private def comparisonProjection : DecoratedTerm X → Term (Occurrence X)
  | .scalar b _ => .of (.inl b)
  | .block o => .of (.inr o)
  | .pair A B => .mul (comparisonProjection A) (comparisonProjection B)
/-- Project exactly the original indexed block equations, preserving repetitions. -/
def ComparisonInventory.blockEdges : ComparisonInventory X →
    List ((Occurrence X × Occurrence X) × Int)
  | .scalar _ _ _ => []
  | .block v w a => [((v,w),(a : Int))]
  | .both I J => I.blockEdges ++ J.blockEdges
  | .incompatible => []
private theorem comparison_inventory_edges (a : Nat) (A B : DecoratedTerm X) :
    (comparisonInventory a A B).blockEdges =
      offsetComparisonEdges (a : Int) (comparisonProjection A) (comparisonProjection B) := by
  induction A generalizing B with
  | scalar b n => cases B <;> rfl
  | block v => cases B <;> rfl
  | pair A₁ A₂ ihA ihB =>
      cases B with
      | scalar c m => rfl
      | block w => rfl
      | pair C D => simp only [comparisonInventory, ComparisonInventory.blockEdges,
          comparisonProjection, offsetComparisonEdges, ihA, ihB]
private theorem scalar_decorate_projection (x : X) (q : List Bool) (t : Term X) :
    comparisonProjection (scalarDecorateFrom x q t) = decorateFrom x q t := by
  induction t generalizing q with
  | of a => cases a <;> rfl
  | mul A B ihA ihB => exact congrArg₂ FreeMagma.mul (ihA _) (ihB _)
/-- Equality of the erased terms is the actual shape-unifier invariant.
The two valuations are otherwise arbitrary and independent. -/
private theorem comparison_inventory_iff (a : Nat) (A B : DecoratedTerm X)
    (r : ScalarPosition X → Nat) (u : Occurrence X → NativeFiniteNormalInversion.Code)
    (same : A.erase = B.erase) :
    (comparisonInventory a A B).Holds r u ↔
      A.value r u = NativeFiniteNormalInversion.shiftCode a (B.value r u) := by
  induction A generalizing B with
  | scalar b n =>
      cases B with
      | scalar c m =>
          change ((n.value r : Int) = (m.value r : Int) + (a : Int)) ↔
            FreeMagma.of (n.value r) = FreeMagma.of (m.value r + a)
          constructor
          · intro h
            congr 1
            omega
          · intro h
            have hn : n.value r = m.value r + a := by injection h
            omega
      | block w => cases same
      | pair C D => cases same
  | block v =>
      cases B with
      | scalar c m => cases same
      | block w => rfl
      | pair C D => cases same
  | pair A₁ A₂ ihA ihB =>
      cases B with
      | scalar c m => cases same
      | block w => cases same
      | pair C D =>
          have parts : A₁.erase = C.erase ∧ A₂.erase = D.erase := by
            injection same with hA hB
            exact ⟨hA,hB⟩
          change (_ ∧ _) ↔ FreeMagma.mul _ _ = FreeMagma.mul _ _
          constructor
          · intro h
            exact congrArg₂ FreeMagma.mul ((ihA C parts.1).mp h.1)
              ((ihB D parts.2).mp h.2)
          · intro h
            have hc : A₁.value r u = NativeFiniteNormalInversion.shiftCode a (C.value r u) ∧
                A₂.value r u = NativeFiniteNormalInversion.shiftCode a (D.value r u) := by
              injection h with h₁ h₂
              exact ⟨h₁,h₂⟩
            exact ⟨(ihA C parts.1).mpr hc.1, (ihB D parts.2).mpr hc.2⟩
/-- Each collapse has one natural witness shared by all three comparisons. -/
inductive BranchInventory (X : Type) where
  | comparison : ComparisonInventory X → BranchInventory X
  | collapse : (Nat → ComparisonInventory X) → BranchInventory X
def BranchInventory.Holds (r : ScalarPosition X → Nat)
    (u : Occurrence X → NativeFiniteNormalInversion.Code) : BranchInventory X → Prop
  | .comparison I => I.Holds r u
  | .collapse I => ∃ n : Nat, (I n).Holds r u
def branchInventory (s : X → Term X) : BranchEquation X → BranchInventory X
  | .primitive z n => .comparison
      (comparisonInventory 0 (scalarDecorate s z) (.scalar true (.constant n)))
  | .shift z a x => .comparison
      (comparisonInventory a (scalarDecorate s z) (scalarDecorate s x))
  | .ordinary z x y => .comparison
      (comparisonInventory 0 (scalarDecorate s z)
        (.pair (scalarDecorate s x) (scalarDecorate s y)))
  | .same x y => .comparison
      (comparisonInventory 0 (scalarDecorate s x) (scalarDecorate s y))
  | .collapse z x y => .collapse fun n => .both
      (comparisonInventory 0 (scalarDecorate s x) (.scalar true (.constant (n+1))))
      (.both (comparisonInventory 0 (scalarDecorate s y) (.scalar true (.constant n)))
        (comparisonInventory 0 (scalarDecorate s z) (.scalar true (.constant (n+2)))))
def BranchInventory.blockEdges : BranchInventory X →
    List ((Occurrence X × Occurrence X) × Int)
  | .comparison I => I.blockEdges
  | .collapse _ => []
private theorem branch_inventory_edges (s : X → Term X) (b : BranchEquation X) :
    (branchInventory s b).blockEdges = sourceOffsetEdges [b] s := by
  have proj (x : X) : comparisonProjection (scalarDecorate s x) = decorate s x :=
    scalar_decorate_projection x [] (s x)
  cases b with
  | primitive z n =>
      change (comparisonInventory 0 (scalarDecorate s z)
        (.scalar true (.constant n))).blockEdges = []
      rw [comparison_inventory_edges]
      cases comparisonProjection (scalarDecorate s z) with
      | of a => cases a <;> rfl
      | mul A B => rfl
  | collapse z x y => rfl
  | shift z a x =>
      change (comparisonInventory a (scalarDecorate s z) (scalarDecorate s x)).blockEdges =
        offsetComparisonEdges (a : Int) (decorate s z) (decorate s x) ++ []
      simp only [comparison_inventory_edges, proj, List.append_nil]
  | ordinary z x y =>
      change (comparisonInventory 0 (scalarDecorate s z)
        (.pair (scalarDecorate s x) (scalarDecorate s y))).blockEdges =
        offsetComparisonEdges 0 (decorate s z) (.mul (decorate s x) (decorate s y)) ++ []
      simp only [comparison_inventory_edges, comparisonProjection, proj, List.append_nil]
      norm_num
  | same x y =>
      change (comparisonInventory 0 (scalarDecorate s x) (scalarDecorate s y)).blockEdges =
        offsetComparisonEdges 0 (decorate s x) (decorate s y) ++ []
      simp only [comparison_inventory_edges, proj, List.append_nil]
      norm_num
/-- Complete normalization of one original comparison, including its natural
collapse witness. No scalar constraint is an external hypothesis. -/
private theorem branch_inventory_iff (s : X → Term X) (b : BranchEquation X)
    (r : ScalarPosition X → Nat) (u : Occurrence X → NativeFiniteNormalInversion.Code)
    (sh : ∀ e ∈ b.shapeEquations, substitute s e.1 = substitute s e.2) :
    (branchInventory s b).Holds r u ↔
      b.Holds (fun x => (scalarDecorate s x).value r u) := by
  have er (x : X) : (scalarDecorate s x).erase = s x :=
    scalar_decorate_erase x [] (s x)
  have cmp (a : Nat) (A B : DecoratedTerm X) (h : A.erase = B.erase) :=
    comparison_inventory_iff a A B r u h
  cases b with
  | primitive z n =>
      have h := sh _ (List.mem_singleton_self _)
      change s z = .of (.inl true) at h
      simpa only [branchInventory, BranchInventory.Holds, BranchEquation.Holds,
        DecoratedTerm.value, RankExpression.value, NativePositiveBranchReduction.shift_zero]
        using cmp 0 (scalarDecorate s z) (.scalar true (.constant n)) (by simpa only [DecoratedTerm.erase, er] using h)
  | shift z a x =>
      have h := sh _ (List.mem_singleton_self _)
      change s z = s x at h
      exact cmp a _ _ (by simpa only [er] using h)
  | ordinary z x y =>
      have h := sh _ (List.mem_singleton_self _)
      change s z = .mul (s x) (s y) at h
      simpa only [branchInventory, BranchInventory.Holds, BranchEquation.Holds,
        DecoratedTerm.value, NativePositiveBranchReduction.shift_zero]
        using cmp 0 (scalarDecorate s z) (.pair (scalarDecorate s x) (scalarDecorate s y))
          (by simpa only [DecoratedTerm.erase, er] using h)
  | same x y =>
      have h := sh _ (List.mem_singleton_self _)
      change s x = s y at h
      simpa only [branchInventory, BranchInventory.Holds, BranchEquation.Holds,
        NativePositiveBranchReduction.shift_zero]
        using cmp 0 (scalarDecorate s x) (scalarDecorate s y) (by simpa only [er] using h)
  | collapse z x y =>
      have hx := sh _ (List.mem_cons_self ..)
      have hy := sh _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hz := sh _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      change s x = .of (.inl true) at hx
      change s y = .of (.inl true) at hy
      change s z = .of (.inl true) at hz
      change (∃ n, _ ∧ _ ∧ _) ↔ ∃ n, _ ∧ _ ∧ _
      apply exists_congr
      intro n
      have cx := cmp 0 (scalarDecorate s x) (.scalar true (.constant (n+1)))
        (by simpa only [DecoratedTerm.erase, er] using hx)
      have cy := cmp 0 (scalarDecorate s y) (.scalar true (.constant n))
        (by simpa only [DecoratedTerm.erase, er] using hy)
      have cz := cmp 0 (scalarDecorate s z) (.scalar true (.constant (n+2)))
        (by simpa only [DecoratedTerm.erase, er] using hz)
      simpa only [DecoratedTerm.value, RankExpression.value,
        NativePositiveBranchReduction.shift_zero] using and_congr cx (and_congr cy cz)
private theorem source_inventory_edges (B : List (BranchEquation X)) (s : X → Term X) :
    B.flatMap (fun b => (branchInventory s b).blockEdges) = sourceOffsetEdges B s := by
  induction B with
  | nil => rfl
  | cons b B ih =>
      change (branchInventory s b).blockEdges ++
        B.flatMap (fun c => (branchInventory s c).blockEdges) = _
      rw [branch_inventory_edges, ih]
      simp [sourceOffsetEdges]
/-- The complete separately decorated system is equivalent to the same
original branch system, for every scalar and block assignment. -/
theorem source_decorated_comparison_equivalence (p : Presentation X)
    (B : List (BranchEquation X)) (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (r : ScalarPosition X → Nat) (u : Occurrence X → NativeFiniteNormalInversion.Code) :
    (B.flatMap (fun b => (branchInventory (action p S) b).blockEdges) =
      sourceOffsetEdges B (action p S)) ∧
    ((∀ b ∈ B, (branchInventory (action p S) b).Holds r u) ↔
      ∀ b ∈ B, b.Holds (fun x => (scalarDecorate (action p S) x).value r u)) := by
  refine ⟨source_inventory_edges B (action p S), ?_⟩
  have sh : ∀ e ∈ shapeEquations B,
      substitute (action p S) e.1 = substitute (action p S) e.2 := by
    intro e he
    have h := Constraints.unify_sound (encodeEquations p (shapeEquations B))
      SubstInfo.empty S hok (encode p e.1, encode p e.2)
      (List.mem_map.mpr ⟨e,he,rfl⟩)
    apply encode_injective p
    simpa only [action_substitute_encode p (shapeEquations B) S hok] using h
  exact forall_congr' fun b => forall_congr' fun hb =>
    branch_inventory_iff (action p S) b r u
      (fun e he => sh e (List.mem_flatMap.mpr ⟨b,hb,he⟩))
/-- Read the natural rank at an explicit primitive address. -/
def sourceScalarRanks (C : X → NativeFiniteNormalInversion.Code)
    (q : ScalarPosition X) : Nat :=
  match subtree (C q.1) q.2 with
  | some (.of n) => n
  | _ => 0
private theorem scalar_decorate_actual (C : X → NativeFiniteNormalInversion.Code)
    (w : X → NativeGroundSolutionSpace.Source) (x : X) (t : Term X)
    (q : List Bool) (D : NativeFiniteNormalInversion.Code)
    (actual : subtree (C x) q = some D) (sh : shape D = evaluate w t) :
    (scalarDecorateFrom x q t).value (sourceScalarRanks C) (occurrenceCode C) = D := by
  induction t generalizing q D with
  | of a =>
      cases a with
      | inl b =>
          cases D with
          | of n => simp [scalarDecorateFrom, DecoratedTerm.value,
              RankExpression.value, sourceScalarRanks, actual]
          | mul D E => cases sh
      | inr j =>
          change (subtree (C x) q).getD (.of 0) = D
          rw [actual]
          rfl
  | mul A B ihA ihB =>
      cases D with
      | of n => cases sh
      | mul D E =>
          have hs : shape D = evaluate w A ∧ shape E = evaluate w B := by
            injection sh with hD hE
            exact ⟨hD,hE⟩
          have hc := subtree_child (C x) q D E actual
          exact congrArg₂ FreeMagma.mul (ihA _ _ hc.1 hs.1) (ihB _ _ hc.2 hs.2)
/-- A genuine native solution supplies the block equations and literal
occurrence subtrees automatically. Primitive and collapse scalars remain
exactly in its selected branch, including r,r+1,r+2. -/
theorem native_source_block_recovery (p : Presentation X) (E : List (Equation X))
    (v : X → NativeGroundSolutionSpace.Source) (hv : ∀ e ∈ E, e.Holds v) :
    ∃ B ∈ branches E, ∃ S : SubstInfo,
      (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S ∧
      (∀ b ∈ B, b.Holds (fun x => NativeFiniteNormalInversion.encode (v x))) ∧
      (∀ x, (scalarDecorate (action p S) x).value
        (sourceScalarRanks (fun y => NativeFiniteNormalInversion.encode (v y)))
        (occurrenceCode (fun y => NativeFiniteNormalInversion.encode (v y))) =
          NativeFiniteNormalInversion.encode (v x)) ∧
      (∀ b ∈ B, (branchInventory (action p S) b).Holds
        (sourceScalarRanks (fun y => NativeFiniteNormalInversion.encode (v y)))
        (occurrenceCode (fun y => NativeFiniteNormalInversion.encode (v y)))) ∧
      ∀ j, (∃ o ∈ occurrenceVertices p (action p S), o.2.2 = j) →
        ∃ (b : Occurrence X) (a : Occurrence X → Nat),
          b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
          (∀ o ∈ occurrenceVertices p (action p S), o.2.2 = j →
            computedSourcePotential B (action p S) j b ≤ computedSourcePotential B (action p S) j o ∧
            (a o : Int) = computedSourcePotential B (action p S) j o -
              computedSourcePotential B (action p S) j b) ∧
          NativeFiniteNormalInversion.Normal
            (occurrenceCode (fun x => NativeFiniteNormalInversion.encode (v x)) b) ∧
          ∀ o ∈ occurrenceVertices p (action p S), o.2.2 = j →
            occurrenceCode (fun x => NativeFiniteNormalInversion.encode (v x)) o =
              NativeFiniteNormalInversion.shiftCode (a o)
                (occurrenceCode (fun x => NativeFiniteNormalInversion.encode (v x)) b) ∧
            NativeFiniteNormalInversion.expand
              (occurrenceCode (fun x => NativeFiniteNormalInversion.encode (v x)) o) =
              GenealogicalFiberTransport.substitution^[a o]
                (NativeFiniteNormalInversion.expand
                  (occurrenceCode (fun x => NativeFiniteNormalInversion.encode (v x)) b)) := by
  obtain ⟨B, hB, normal, sat, S, hok, factor, _, _⟩ :=
    (native_branch_reduction p E v).mp hv
  have reconstruction (x : X) := scalar_decorate_actual
    (fun y => NativeFiniteNormalInversion.encode (v y))
    (fun y => shape (NativeFiniteNormalInversion.encode (v y))) x (action p S x) []
    (NativeFiniteNormalInversion.encode (v x)) (by simp [subtree]) (factor x).symm
  have inventory := (source_decorated_comparison_equivalence p B S hok
    (sourceScalarRanks (fun y => NativeFiniteNormalInversion.encode (v y)))
    (occurrenceCode (fun y => NativeFiniteNormalInversion.encode (v y)))).2.mpr
      (by simpa only [scalarDecorate, reconstruction] using sat)
  refine ⟨B, hB, S, hok, sat, reconstruction, inventory, ?_⟩
  intro j occurs
  let C := fun x => NativeFiniteNormalInversion.encode (v x)
  let T := codeTree (C j)
  let u := fun o => readRanks T (occurrenceCode C o)
  have blocks := actual_rank_blocks p B S hok C factor sat j
  change BlockSolution B (action p S) j u ∧ _ at blocks
  have good : ZeroCycles B (action p S) j := by
    let l : Leaves T := Classical.choice (leavesNonempty T)
    exact (zeroCycles_iff B (action p S) j).mpr
      ⟨fun o => (u o l : Int), fun e he => blocks.1 e he l⟩
  obtain ⟨b, a, hb, hj, hab, hmin, recovery⟩ :=
    source_canonical_block_recovery p B S hok j occurs good
  have recovered := recovery T u C blocks.1 normal blocks.2
  have identity (o : Occurrence X) (ho : o ∈ occurrenceVertices p (action p S))
      (hoj : o.2.2 = j) : fill T (u o) = occurrenceCode C o := by
    have h1 := blocks.2 o ho hoj
    have h2 := (actual_occurrence_code p B S hok C factor o ho).1
    exact Option.some.inj (h1.symm.trans h2)
  refine ⟨b, a, hb, hj, hab, hmin, ?_, ?_⟩
  · simpa only [identity b hb hj] using recovered.1
  · intro o ho hoj
    constructor
    · simpa only [identity o ho hoj, identity b hb hj] using (recovered.2 o ho hoj).1
    · simpa only [identity o ho hoj, identity b hb hj] using (recovered.2 o ho hoj).2.1

#print axioms source_sort_minimum_base

#print axioms source_decorated_comparison_equivalence
#print axioms native_source_block_recovery
#print axioms source_canonical_block_recovery

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover
