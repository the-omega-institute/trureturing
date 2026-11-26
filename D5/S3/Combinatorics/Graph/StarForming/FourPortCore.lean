/- GID: D5/S3/Combinatorics/Graph/StarForming/FourPortCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/FourPortCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual periodic equality core with its two disjoint cut edges. -/

import D5.S3.Combinatorics.Graph.StarForming.EqualityCore
import D5.S3.Combinatorics.Graph.StarForming.DissociationDeficiency
import D5.S3.Combinatorics.Graph.StarForming.WeightedBalance
import Mathlib.Data.Fin.VecNotation

/-! The actual Q_k and periodic integer weights of
CUBIC_EQUALITY_PADDING_RINGS, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The index permutation and marked cell are arbitrary; the cyclic instance
is the received Q_k. No list of core lengths is enumerated. -/
namespace D5.S3.Combinatorics.Graph.StarForming.FourPortCore
open StarFormingDissociationRefutation DegreeCapacity DissociationDeficiency
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

def cut (mark : I) (x y : I × Fin 20) : Prop :=
  x.1 = mark ∧ y.1 = mark ∧
    ((x.2 = 12 ∧ y.2 = 13) ∨ (x.2 = 13 ∧ y.2 = 12) ∨
     (x.2 = 14 ∧ y.2 = 15) ∨ (x.2 = 15 ∧ y.2 = 14))

instance (mark : I) : DecidableRel (cut mark) := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def graph (e : Equiv.Perm I) (mark : I) : SimpleGraph (I × Fin 20) where
  Adj x y := (EqualityCore.graph e).Adj x y ∧ ¬ cut mark x y
  symm := ⟨by intro x y h; refine ⟨h.1.symm, ?_⟩; simp only [cut] at *; tauto⟩
  loopless := ⟨by intro x h; exact (EqualityCore.graph e).irrefl h.1⟩

instance (e : Equiv.Perm I) (mark : I) : DecidableRel (graph e mark).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ ¬ _))

def ports (mark : I) : Finset (I × Fin 20) :=
  {(mark,12),(mark,13),(mark,14),(mark,15)}

private def neighbors (e : Equiv.Perm I) (mark : I) (x : I × Fin 20) :
    Finset (I × Fin 20) := (EqualityCore.neighbors e x).filter (fun y => ¬ cut mark x y)

private theorem mem_neighbors (e : Equiv.Perm I) (mark : I) (x y : I × Fin 20) :
    y ∈ neighbors e mark x ↔ (graph e mark).Adj x y := by
  simp [neighbors, EqualityCore.mem_neighbors, graph]

/-- Exactly the four actual ports have degree two; all other vertices have
degree three, even for fixed points of the index permutation. -/
theorem degree (e : Equiv.Perm I) (mark : I) (x : I × Fin 20) :
    DegreeCapacity.degree (graph e mark) x = if x ∈ ports mark then 2 else 3 := by
  have he : Finset.univ.filter ((graph e mark).Adj x) = neighbors e mark x := by
    ext y; simp [mem_neighbors]
  change (Finset.univ.filter _).card = _
  rw [he]
  rcases x with ⟨i,v⟩
  by_cases hi : i=mark
  · subst i
    fin_cases v <;> simp [neighbors, EqualityCore.neighbors, cut, ports,
      Finset.filter_insert, Finset.filter_singleton]
  · fin_cases v <;> simp [neighbors, EqualityCore.neighbors, cut, ports, hi,
      Finset.filter_insert, Finset.filter_singleton]

/-- Deficiency is the actual number of selected cut endpoints. -/
theorem selected_deficiency (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20)) :
    deficiency (graph e mark) 3 D = (D ∩ ports mark).card := by
  simp only [deficiency, degree]
  have h (v : I × Fin 20) : 3-(if v ∈ ports mark then 2 else 3) =
      if v ∈ ports mark then 1 else 0 := by split_ifs <;> rfl
  simp_rw [h]
  simpa [Finset.filter_mem_eq_inter] using Finset.sum_boole (· ∈ ports mark) D

/-- The complete cut identity is extracted from the actual Q graph. -/
theorem exact_identity (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20))
    (hD : IsKIndependent (graph e mark) 2 D) :
    5*D.card+4+(isolates (graph e mark) D).card+2*complementEdges (graph e mark) D =
      60*Fintype.card I+2*(D ∩ ports mark).card := by
  have h := DissociationDeficiency.exact_identity (graph e mark) D hD 3 (by decide)
    (by intro v; rw [degree]; split_ifs <;> omega)
  rw [selected_deficiency, selected_deficiency] at h
  simpa [ports, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- The four unrestricted port choices still permit at most twelve per cell. -/
theorem card_bound (e : Equiv.Perm I) (mark : I) (D : Finset (I × Fin 20))
    (hD : IsKIndependent (graph e mark) 2 D) : D.card ≤ 12*Fintype.card I := by
  have h := exact_identity e mark D hD
  have hp : (D ∩ ports mark).card ≤ 4 := by
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := D) (s₂ := ports mark))
    simpa [ports] using this
  omega

def weight : Fin 20 → ℤ := ![1,0,0,-1,2,-2,0,-1,1,0,-1,1,-1,2,-2,1,0,0,0,0]

/-- The written periodic weight has zero total at every actual core length. -/
theorem total_weight : (∑ v : I × Fin 20, weight v.2) = 0 := by
  rw [Fintype.sum_prod_type]
  have h : (∑ v : Fin 20, weight v) = 0 := by decide +kernel
  simp only [h, Finset.sum_const_zero]

/-- All actual cyclic neighborhood rows satisfy the integer balance identity. -/
theorem weight_balance (e : Equiv.Perm I) (x : I × Fin 20) :
    WeightedBalance.neighborSum (EqualityCore.graph e) (fun v => weight v.2) x +
      2*weight x.2 = 0 := by
  have he : WeightedBalance.neighborSum (EqualityCore.graph e) (fun v => weight v.2) x =
      ∑ y ∈ EqualityCore.neighbors e x, weight y.2 := by
    have hn : Finset.univ.filter ((EqualityCore.graph e).Adj x) =
        EqualityCore.neighbors e x := by
      ext y
      simp [EqualityCore.mem_neighbors]
    simp only [WeightedBalance.neighborSum, ← Finset.sum_filter, hn]
  rw [he]
  rcases x with ⟨i,v⟩
  fin_cases v <;> norm_num [EqualityCore.neighbors, weight]

private theorem selected_neighbors (e : Equiv.Perm I) (mark : I)
    (D : Finset (I × Fin 20)) (x : I × Fin 20) :
    selectedDegree (graph e mark) D x = ((neighbors e mark x).filter (· ∈ D)).card ∧
    selectedDegree (EqualityCore.graph e) D x =
      ((EqualityCore.neighbors e x).filter (· ∈ D)).card := by
  constructor <;> apply congrArg Finset.card <;> ext y
  · simp [selectedDegree, mem_neighbors, and_comm]
  · simp [selectedDegree, EqualityCore.mem_neighbors, and_comm]

private def mate (v : Fin 20) : Fin 20 :=
  if v = 12 then 13 else if v = 13 then 12 else if v = 14 then 15 else 14

/-- Restoring the two edges adds exactly the selected opposite endpoint,
with no fictitious boundary credit. -/
theorem restored_selected_degree (e : Equiv.Perm I) (mark : I)
    (D : Finset (I × Fin 20)) (x : I × Fin 20) :
    selectedDegree (EqualityCore.graph e) D x = selectedDegree (graph e mark) D x +
      if x ∈ ports mark ∧ (mark,mate x.2) ∈ D then 1 else 0 := by
  rcases selected_neighbors e mark D x with ⟨hq,hc⟩
  rw [hq,hc]
  rcases x with ⟨i,v⟩
  by_cases hi : i=mark
  · subst i
    fin_cases v <;>
      simp [neighbors, EqualityCore.neighbors, cut, ports, mate,
        Finset.filter_insert, Finset.filter_singleton] <;>
      split_ifs <;> simp_all
  · fin_cases v <;>
      simp [neighbors, EqualityCore.neighbors, cut, ports, hi,
        Finset.filter_insert, Finset.filter_singleton]

def pair (mark : I) (side : Bool) : Finset (I × Fin 20) :=
  if side then {(mark,14),(mark,15)} else {(mark,12),(mark,13)}

set_option maxHeartbeats 2000000 in
/-- Omitting either complete cut pair costs one vertex, uniformly in the
core size, with the other pair unrestricted. -/
theorem omitted_pair_strict (e : Equiv.Perm I) (mark : I)
    (D : Finset (I × Fin 20)) (hD : IsKIndependent (graph e mark) 2 D)
    (side : Bool) (hmiss : Disjoint D (pair mark side)) :
    D.card+1 ≤ 12*Fintype.card I := by
  have hcap := card_bound e mark D hD
  by_contra hnot
  have he : D.card=12*Fintype.card I := by omega
  have hsub : D ∩ ports mark ⊆ pair mark (!side) := by
    intro x hx
    have hd := (Finset.mem_inter.mp hx).1
    have hp := (Finset.mem_inter.mp hx).2
    have hn : x ∉ pair mark side := fun hm => Finset.disjoint_left.mp hmiss hd hm
    cases side <;> simp_all [ports,pair]
  have hp : (D ∩ ports mark).card ≤ 2 := by
    have := Finset.card_le_card hsub
    cases side <;> simpa [pair] using this
  have hid := exact_identity e mark D hD
  have hi : (isolates (graph e mark) D).card=0 := by omega
  have ht : complementEdges (graph e mark) D=0 := by omega
  have hp' : (D ∩ ports mark).card=2 := by omega
  have heq : D ∩ ports mark=pair mark (!side) :=
    Finset.eq_of_subset_of_card_le hsub (by cases side <;> simpa [pair,hp'])
  have hpattern (x : I × Fin 20) (hx : x ∈ ports mark) :
      x ∈ D ↔ x ∈ pair mark (!side) := by
    rw [← heq,Finset.mem_inter]
    tauto
  have hpoint (x : I × Fin 20) :
      (selectedDegree (EqualityCore.graph e) D x : ℤ) + 2*(if x ∈ D then 1 else 0) =
        3-(if x ∈ pair mark side then 1 else 0)+(if x ∈ pair mark (!side) then 1 else 0) := by
    have hq := tight_degrees (graph e mark) D hD hi ht x
    rw [restored_selected_degree, hq, degree]
    rcases x with ⟨i,v⟩
    by_cases hm : i=mark
    · subst i
      have h12 := hpattern (mark,12) (by simp [ports])
      have h13 := hpattern (mark,13) (by simp [ports])
      have h14 := hpattern (mark,14) (by simp [ports])
      have h15 := hpattern (mark,15) (by simp [ports])
      cases side <;> fin_cases v <;>
        simp_all [ports,pair,mate] <;> split_ifs <;> norm_num
    · cases side <;> fin_cases v <;>
        simp [ports,pair,hm] <;> split_ifs <;> norm_num
  have hz := WeightedBalance.annihilate (EqualityCore.graph e) (fun v => weight v.2)
    2 (weight_balance e) D
  simp_rw [hpoint,mul_add,mul_sub,mul_ite,mul_one,mul_zero] at hz
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hz
  have hconst : (∑ v : I × Fin 20, weight v.2*3)=0 := by
    rw [← Finset.sum_mul,total_weight]; rfl
  rw [hconst, ← Finset.sum_filter, ← Finset.sum_filter] at hz
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at hz
  cases side <;> norm_num [pair,weight] at hz

end D5.S3.Combinatorics.Graph.StarForming.FourPortCore
