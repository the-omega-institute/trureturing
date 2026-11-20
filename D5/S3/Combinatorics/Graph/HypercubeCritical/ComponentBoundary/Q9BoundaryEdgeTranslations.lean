/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Boundary-edge translations constrain subcubic subsets of Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! Counts of transverse cube edge translations and the induced-subcubic cut bound. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj flip_flip IsBalanced)
open BalancedCubeComponentBoundary (directions regular_directions)
open BalancedCubeGirth (no_selected_square)
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mem_directions directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

local notation "flip" => BalancedCriticalSpectrum.flip

/-- A cube edge is represented by its false-bit endpoint and its direction. -/
abbrev Edge := Q 9 × Fin 9

open Classical in
/-- The exterior vertices adjacent to the selected set. -/
def boundary (C : Finset (Q 9)) : Finset (Q 9) :=
  Finset.univ.filter fun x => x ∉ C ∧ (directions C x).Nonempty

private def steps (S T : Finset (Q 9)) : Finset Edge :=
  (S.product Finset.univ).filter fun e => flip e.1 e.2 ∈ T

@[simp] private theorem mem_steps {S T : Finset (Q 9)} {e : Edge} :
    e ∈ steps S T ↔ e.1 ∈ S ∧ flip e.1 e.2 ∈ T := by
  simp [steps]

/-- The edges with both endpoints selected, counted once at their false-bit endpoint. -/
def internalEdges (C : Finset (Q 9)) : Finset Edge :=
  (steps C C).filter fun e => e.1 e.2 = false

@[simp] private theorem mem_internalEdges {C : Finset (Q 9)} {e : Edge} :
    e ∈ internalEdges C ↔ (e.1 ∈ C ∧ flip e.1 e.2 ∈ C) ∧ e.1 e.2 = false := by
  simp [internalEdges]

private theorem card_filtered_product {α β : Type*} (S : Finset α) (T : Finset β)
    (p : α × β → Prop) [hp : DecidablePred p] :
    ((S.product T).filter p).card =
      ∑ a ∈ S, (@Finset.filter β (fun b => p (a, b)) (fun b => hp (a, b)) T).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S)]
  · apply Finset.sum_congr rfl
    intro a ha
    have hf : (((S.product T).filter p).filter fun e => e.1 = a) =
        ({a} : Finset α).product (T.filter fun b => p (a, b)) := by
      ext ⟨x, y⟩
      by_cases h : x = a
      · subst x
        simp [ha]
      · simp [h, Ne.symm h]
    rw [hf]
    exact (Finset.card_product _ _).trans (by simp)
  · intro e he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1

private theorem card_steps (S T : Finset (Q 9)) :
    (steps S T).card = ∑ x ∈ S, (directions T x).card := by
  calc
    (steps S T).card = ∑ x ∈ S, (Finset.univ.filter fun i => flip x i ∈ T).card :=
      card_filtered_product S Finset.univ (fun e : Edge => flip e.1 e.2 ∈ T)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1

private def reverseStep (e : Edge) : Edge := (flip e.1 e.2, e.2)

private theorem reverseStep_involutive : Function.Involutive reverseStep := by
  rintro ⟨x, t⟩
  simp [reverseStep]

private theorem reverseStep_mem {S T : Finset (Q 9)} {e : Edge}
    (he : e ∈ steps S T) : reverseStep e ∈ steps T S := by
  rw [mem_steps] at he ⊢
  simpa [reverseStep] using he.symm

private theorem card_steps_symm (S T : Finset (Q 9)) :
    (steps S T).card = (steps T S).card := by
  exact Finset.card_nbij' reverseStep reverseStep
    (fun _ h => reverseStep_mem h) (fun _ h => reverseStep_mem h)
    (fun e _ => reverseStep_involutive e) (fun e _ => reverseStep_involutive e)

private theorem twice_card_internalEdges (S : Finset (Q 9)) :
    2 * (internalEdges S).card = (steps S S).card := by
  let p : Edge → Prop := fun e => e.1 e.2 = false
  have partition := Finset.card_filter_add_card_filter_not (s := steps S S) p
  have swap : ((steps S S).filter p).card = ((steps S S).filter fun e => ¬ p e).card := by
    refine Finset.card_nbij' reverseStep reverseStep ?_ ?_ ?_ ?_
    · intro e he
      obtain ⟨hs, hp⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨reverseStep_mem hs,
        by simp [p, reverseStep, show e.1 e.2 = false from hp]⟩
    · intro e he
      obtain ⟨hs, hp⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨reverseStep_mem hs, ?_⟩
      change e.1 e.2 ≠ false at hp
      cases h : e.1 e.2 <;> simp_all [p, reverseStep]
    · intro e _
      exact reverseStep_involutive e
    · intro e _
      exact reverseStep_involutive e
  change 2 * ((steps S S).filter p).card = _
  omega

/-- The transverse axes sending both endpoints outside the selected set. -/
def transverseExterior (C : Finset (Q 9)) (e : Edge) : Finset (Fin 9) :=
  Finset.univ.filter fun i => i ≠ e.2 ∧ flip e.1 i ∉ C ∧ flip (flip e.1 e.2) i ∉ C

/-- Translation witnesses consist of an internal edge and one transverse axis
    whose flip sends both endpoints outside the selected set. -/
def witnesses (C : Finset (Q 9)) : Finset (Edge × Fin 9) :=
  ((internalEdges C).product Finset.univ).filter fun w => w.2 ∈ transverseExterior C w.1

/-- Translating the false-bit endpoint along a transverse axis preserves its edge orientation. -/
def translate (w : Edge × Fin 9) : Edge := (flip w.1.1 w.2, w.1.2)

/-- The distinct translated edge images. -/
def translatedEdges (C : Finset (Q 9)) : Finset Edge :=
  (witnesses C).image translate

/-- Number of translation witnesses for a given exterior edge. -/
def multiplicity (C : Finset (Q 9)) (e : Edge) : ℕ :=
  ((witnesses C).filter fun w => translate w = e).card

/-- Sum of the numbers of unordered pairs of distinct witnesses with the same image. -/
def collisionCount (C : Finset (Q 9)) : ℕ :=
  ∑ e ∈ internalEdges (boundary C), (multiplicity C e).choose 2

open Classical in
/-- A balanced cubic internal edge has exactly four transverse exterior directions. -/
theorem card_transverseExterior {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {e : Edge} (he : e ∈ internalEdges C) :
    (transverseExterior C e).card = 4 := by
  obtain ⟨⟨hx, hy⟩, _⟩ := mem_internalEdges.mp he
  let I := directions C e.1
  let J := directions C (flip e.1 e.2)
  have htI : e.2 ∈ I := (mem_directions _ _ _).mpr hy
  have htJ : e.2 ∈ J := (mem_directions _ _ _).mpr (by simpa using hx)
  have hdisj : Disjoint (I.erase e.2) (J.erase e.2) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨hit, hi'⟩ := Finset.mem_erase.mp hi
    have hxi := (mem_directions _ _ _).mp hi'
    have hyi := (mem_directions _ _ _).mp (Finset.mem_erase.mp hj).2
    exact no_selected_square hb hit.symm hx hy hxi hyi
  have hI := regular_directions C hr hx
  have hJ := regular_directions C hr hy
  change I.card = 3 at hI
  change J.card = 3 at hJ
  have hUnion : (I ∪ J).card = 5 := by
    have heq : I ∪ J = insert e.2 (I.erase e.2 ∪ J.erase e.2) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      by_cases hi : i = e.2
      · subst i
        simp [htI]
      · simp [hi]
    rw [heq, Finset.card_insert_of_notMem (by simp), Finset.card_union_of_disjoint hdisj,
      Finset.card_erase_of_mem htI, Finset.card_erase_of_mem htJ, hI, hJ]
  have heq : transverseExterior C e = Finset.univ \ (I ∪ J) := by
    ext i
    simp only [transverseExterior, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_union, not_or]
    simp only [I, J, mem_directions]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rintro rfl
    exact h.1 hy
  rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, hUnion]

open Classical in
/-- Four transverse translates per edge give six witnesses per selected vertex. -/
theorem card_witnesses (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : (witnesses C).card = 6 * C.card := by
  have hSteps : (steps C C).card = C.card * 3 := by
    rw [card_steps]
    exact Finset.sum_const_nat fun x hx => regular_directions C hr hx
  have hEdges := twice_card_internalEdges C
  have hFiber : (witnesses C).card = ∑ e ∈ internalEdges C,
      (Finset.univ.filter fun i => i ∈ transverseExterior C e).card :=
    card_filtered_product (internalEdges C) Finset.univ
      (fun w => w.2 ∈ transverseExterior C w.1)
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hFiber
  rw [Finset.sum_const_nat (fun _ he => card_transverseExterior hr hb he)] at hFiber
  omega

/-- Each distinct image is an edge of the induced exterior boundary. -/
theorem translatedEdges_subset_boundaryEdges (C : Finset (Q 9)) :
    translatedEdges C ⊆ internalEdges (boundary C) := by
  intro e he
  obtain ⟨⟨⟨x, t⟩, i⟩, hw, rfl⟩ := Finset.mem_image.mp he
  have hw' : ((x, t), i) ∈ (internalEdges C).product Finset.univ ∧
      i ∈ transverseExterior C (x, t) := Finset.mem_filter.mp hw
  obtain ⟨⟨hx, hy⟩, hbit⟩ := mem_internalEdges.mp (Finset.mem_product.mp hw'.1).1
  have htrans : i ∈ Finset.univ ∧ i ≠ t ∧ flip x i ∉ C ∧
      flip (flip x t) i ∉ C := Finset.mem_filter.mp hw'.2
  obtain ⟨_, hit, houtx, houty⟩ := htrans
  apply mem_internalEdges.mpr
  dsimp only [translate] at *
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      houtx, ⟨i, (mem_directions _ _ _).mpr (by simpa using hx)⟩⟩
  · rw [flip_comm x i t]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      houty, ⟨i, (mem_directions _ _ _).mpr (by simpa using hy)⟩⟩
  · simpa [BalancedCriticalSpectrum.flip, Function.update_of_ne hit.symm] using hbit

private theorem card_steps_partition (S U : Finset (Q 9)) :
    (steps S U).card + (steps S (Finset.univ \ U)).card = 9 * S.card := by
  have h := Finset.card_filter_add_card_filter_not (s := S.product Finset.univ)
    (fun e : Edge => flip e.1 e.2 ∈ U)
  simpa [steps, Finset.card_product, Nat.mul_comm] using h

private theorem boundary_subset_complement {C U : Finset (Q 9)}
    (hsep : ∀ x ∈ C, ∀ y ∈ U \ C, ¬ (hypercube 9).Adj x y) :
    boundary C ⊆ Finset.univ \ U := by
  intro y hy
  obtain ⟨hyC, i, hi⟩ := (Finset.mem_filter.mp hy).2
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hyU => ?_⟩
  exact hsep (flip y i) ((mem_directions _ _ _).mp hi) y
    (Finset.mem_sdiff.mpr ⟨hyU, hyC⟩) (flip_adj y i).symm

open Classical in
private theorem cut_bounds (U : Finset (Q 9))
    (hU : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3) :
    let T : Finset (Q 9) := Finset.univ \ U
    6 * U.card ≤ (steps U T).card ∧
      (steps U T).card + 2 * (internalEdges T).card = 9 * T.card := by
  let T : Finset (Q 9) := Finset.univ \ U
  have hInternalU : (steps U U).card ≤ U.card * 3 := by
    rw [card_steps, ← Finset.sum_const_nat (fun _ _ => rfl)]
    apply Finset.sum_le_sum
    intro x hx
    have hf : U.filter (fun y => (hypercube 9).Adj x y) =
        (hypercube 9).neighborFinset x ∩ U := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [directions_card, hf, selected_neighbor_card hx]
    exact (SimpleGraph.degree_le_maxDegree _ _).trans hU
  have hPartU : (steps U U).card + (steps U T).card = 9 * U.card :=
    card_steps_partition U U
  have hPartT : (steps T U).card + (steps T T).card = 9 * T.card :=
    card_steps_partition T U
  have hCut := card_steps_symm U T
  have hEdges := twice_card_internalEdges T
  change 6 * U.card ≤ (steps U T).card ∧
    (steps U T).card + 2 * (internalEdges T).card = 9 * T.card
  constructor <;> omega

open Classical in
/-- The cut bound with the number of distinct translated edge images. -/
theorem distinct_edge_bound (C U : Finset (Q 9)) (_hCU : C ⊆ U)
    (hsep : ∀ x ∈ C, ∀ y ∈ U \ C, ¬ (hypercube 9).Adj x y)
    (hU : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3) :
    15 * U.card + 2 * (translatedEdges C).card ≤ 4608 := by
  let T : Finset (Q 9) := Finset.univ \ U
  obtain ⟨hCut, hDegree⟩ := cut_bounds U hU
  have hbound := boundary_subset_complement hsep
  have hEdges : (internalEdges (boundary C)).card ≤ (internalEdges T).card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨⟨hx, hy⟩, hb⟩ := mem_internalEdges.mp he
    exact mem_internalEdges.mpr ⟨⟨hbound hx, hbound hy⟩, hb⟩
  have hImages := Finset.card_le_card (translatedEdges_subset_boundaryEdges C)
  have hCube : (Finset.univ : Finset (Q 9)).card = 512 := by
    simp [Q, Sensitivity.Q]
  have hTotal : T.card + U.card = 512 := by
    rw [← hCube]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
  change 6 * U.card ≤ (steps U T).card at hCut
  change (steps U T).card + 2 * (internalEdges T).card = 9 * T.card at hDegree
  omega

open Classical in
/-- The exterior-edge multiplicities sum to six times the component size. -/
theorem sum_multiplicity (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∑ e ∈ internalEdges (boundary C), multiplicity C e = 6 * C.card := by
  rw [← card_witnesses C hr hb]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro w hw
  exact translatedEdges_subset_boundaryEdges C (Finset.mem_image_of_mem translate hw)

private theorem le_one_add_choose_two (m : ℕ) : m ≤ 1 + m.choose 2 := by
  cases m with
  | zero => simp
  | succ k =>
    rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
    omega

private theorem witnesses_le_images_add_collisions (C : Finset (Q 9)) :
    (witnesses C).card ≤ (translatedEdges C).card + collisionCount C := by
  rw [Finset.card_eq_sum_card_image translate, collisionCount]
  have hsum : ∑ e ∈ translatedEdges C, multiplicity C e ≤
      ∑ e ∈ translatedEdges C, (1 + (multiplicity C e).choose 2) :=
    Finset.sum_le_sum fun e _ => le_one_add_choose_two (multiplicity C e)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  have hle : ∑ e ∈ translatedEdges C, (multiplicity C e).choose 2 ≤
      ∑ e ∈ internalEdges (boundary C), (multiplicity C e).choose 2 :=
    Finset.sum_le_sum_of_subset (translatedEdges_subset_boundaryEdges C)
  exact hsum.trans (Nat.add_le_add_left hle _)

open Classical in
/-- The direct collision bound for a balanced cubic component of a subcubic Q9 set.
    In additive form the inequality is `15 * |U| + 12 * |C| ≤ 4608 + 2 * Λ`. -/
theorem boundary_edge_bound (C U : Finset (Q 9)) (hCU : C ⊆ U)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ U \ C, ¬ (hypercube 9).Adj x y)
    (hU : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3) :
    15 * U.card + 12 * C.card ≤ 4608 + 2 * collisionCount C := by
  have hDistinct := distinct_edge_bound C U hCU hsep hU
  have hWitness := witnesses_le_images_add_collisions C
  rw [card_witnesses C hr hb] at hWitness
  omega

open Classical in
/-- At least 63 witness collisions are necessary for a 72-vertex component
    in a subcubic set of at least 258 vertices. -/
theorem collisionCount_ge_63 (C U : Finset (Q 9)) (hCU : C ⊆ U)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ U \ C, ¬ (hypercube 9).Adj x y)
    (hU : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3)
    (hCcard : C.card = 72) (hUcard : 258 ≤ U.card) :
    63 ≤ collisionCount C := by
  have h := boundary_edge_bound C U hCU hr hb hsep hU
  omega

#print axioms card_transverseExterior
#print axioms card_witnesses
#print axioms translatedEdges_subset_boundaryEdges
#print axioms distinct_edge_bound
#print axioms sum_multiplicity
#print axioms boundary_edge_bound
#print axioms collisionCount_ge_63

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations
