/- GID: D5/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CompleteBipartiteBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Balanced isolate accounting need not imply zero compensation slack. -/

import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.Graph.StarForming.Comparison
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity

/-! The all-degree counterexample in REGULAR_COMPENSATION_EQUALITY,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The two components use opposite sides. Global isolate balance and tight
isolate accounting therefore do not imply zero compensation slack. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CompleteBipartiteBalance
open StarFormingDissociationRefutation DegreeCapacity
variable (d : ℕ)

def graph : SimpleGraph (Bool × Fin d) where
  Adj x y := x.1 ≠ y.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩
instance : DecidableRel (graph d).Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

def part (b : Bool) : Finset (Bool × Fin d) :=
  Finset.univ.image (fun i => (b,i))

@[simp]
theorem mem_part (b : Bool) (v : Bool × Fin d) : v ∈ part d b ↔ v.1=b := by
  rcases v with ⟨c,i⟩
  simp [part,eq_comm]

@[simp]
theorem part_card (b : Bool) : (part d b).card= d := by
  rw [part,Finset.card_image_of_injective]
  · simp
  · intro i j h; exact congrArg Prod.snd h

theorem neighbors (v : Bool × Fin d) :
    Finset.univ.filter ((graph d).Adj v) = part d (!v.1) := by
  ext x
  cases hv : v.1 <;> cases hx : x.1 <;> simp [graph,hv,hx]

theorem regular (v : Bool × Fin d) : degree (graph d) v= d := by
  unfold degree
  rw [neighbors,part_card]

theorem part_independent (b : Bool) : IsKIndependent (graph d) 2 (part d b) := by
  intro v hv
  have he : (part d b).filter ((graph d).Adj v)= ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hax
    exact hax (((mem_part d b v).mp hv).trans ((mem_part d b x).mp hx).symm)
  rw [he]
  simp

/-- A dissociation meeting both sides has at most one vertex in each side. -/
theorem independent_cap (hd : 2 ≤ d) (S : Finset (Bool × Fin d))
    (hS : IsKIndependent (graph d) 2 S) : S.card≤d := by
  let L := S.filter (fun v => v.1=false)
  let R := S.filter (fun v => v.1=true)
  have hcard : S.card=L.card+R.card := by
    have he : S.filter (fun v => ¬v.1=false)=R := by
      ext v
      cases h : v.1 <;> simp [R,h]
    have h := Finset.card_filter_add_card_filter_not (s:=S) (fun v : Bool × Fin d => v.1=false)
    rw [he] at h
    exact h.symm
  have hL : L.card≤d := by
    apply (le_of_le_of_eq (b:=(part d false).card) ?_ (part_card d false))
    apply Finset.card_le_card
    intro v hv
    exact (mem_part d false v).mpr (Finset.mem_filter.mp hv).2
  have hR : R.card≤d := by
    apply (le_of_le_of_eq (b:=(part d true).card) ?_ (part_card d true))
    apply Finset.card_le_card
    intro v hv
    exact (mem_part d true v).mpr (Finset.mem_filter.mp hv).2
  by_cases hl : L.Nonempty
  · by_cases hr : R.Nonempty
    · obtain ⟨l,hl⟩ := hl
      obtain ⟨r,hr⟩ := hr
      have hlS := (Finset.mem_filter.mp hl).1
      have hrS := (Finset.mem_filter.mp hr).1
      have hlc := (Finset.mem_filter.mp hl).2
      have hrc := (Finset.mem_filter.mp hr).2
      have hln : S.filter ((graph d).Adj l)=R := by
        ext v
        cases h : v.1 <;> simp [graph,R,hlc,h]
      have hrn : S.filter ((graph d).Adj r)=L := by
        ext v
        cases h : v.1 <;> simp [graph,L,hrc,h]
      have h1 := hS l hlS
      have h2 := hS r hrS
      rw [hln] at h1
      rw [hrn] at h2
      omega
    · have he : R= ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
      rw [he] at hcard
      simp only [Finset.card_empty,add_zero] at hcard
      omega
  · have he : L= ∅ := Finset.not_nonempty_iff_eq_empty.mp hl
    rw [he] at hcard
    simp only [Finset.card_empty,zero_add] at hcard
    omega

theorem beta_eq (hd : 2 ≤ d) : beta (graph d) 2= d := by
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    exact independent_cap d hd S (Finset.mem_filter.mp hS).2
  · have h := Finset.le_sup (s := Finset.univ.powerset.filter
      (IsKIndependent (graph d) 2)) (f := Finset.card)
      (Finset.mem_filter.mpr ⟨by simp,part_independent d false⟩)
    simpa [beta] using h

theorem part_minimal (hd : 2 ≤ d) (b : Bool) :
    IsMinimalStarForming (graph d) 2 (part d b) := by
  apply maximal_independent_minimal (graph d) (part d b) (part_independent d b)
  intro x hx hi
  have h := independent_cap d hd (insert x (part d b)) hi
  rw [Finset.card_insert_of_notMem hx,part_card] at h
  omega

abbrev pairGraph := (graph d).sum (graph d)
noncomputable instance : DecidableRel (pairGraph d).Adj := Classical.decRel _

def selection : Finset ((Bool × Fin d) ⊕ (Bool × Fin d)) :=
  (part d false).disjSum (part d true)

def color : ((Bool × Fin d) ⊕ (Bool × Fin d)) → Bool
  | .inl v => v.1
  | .inr v => v.1

theorem pair_coloring : (pairGraph d).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if color d v then (1 : Fin 2) else 0) ?_⟩
  intro v w h
  cases v with
  | inl v => cases w with
    | inl w => cases hv : v.1 <;> cases hw : w.1 <;>
        simp_all [pairGraph,graph,SimpleGraph.sum,color]
    | inr w => simp [pairGraph,SimpleGraph.sum] at h
  | inr v => cases w with
    | inl w => simp [pairGraph,SimpleGraph.sum] at h
    | inr w => cases hv : v.1 <;> cases hw : w.1 <;>
        simp_all [pairGraph,graph,SimpleGraph.sum,color]

theorem pair_regular (v : (Bool × Fin d) ⊕ (Bool × Fin d)) :
    degree (pairGraph d) v= d := by
  cases v with
  | inl v =>
    have he : Finset.univ.filter ((pairGraph d).Adj (.inl v)) =
        (part d (!v.1)).map Function.Embedding.inl := by
      apply Finset.ext
      intro w
      rw [Finset.mem_filter]
      cases w with
      | inl w => cases hv : v.1 <;> cases hw : w.1 <;>
          simp [pairGraph,SimpleGraph.sum,graph,hv,hw]
      | inr w => simp [pairGraph,SimpleGraph.sum]
    unfold degree
    rw [he,Finset.card_map,part_card]
  | inr v =>
    have he : Finset.univ.filter ((pairGraph d).Adj (.inr v)) =
        (part d (!v.1)).map Function.Embedding.inr := by
      apply Finset.ext
      intro w
      rw [Finset.mem_filter]
      cases w with
      | inl w => simp [pairGraph,SimpleGraph.sum]
      | inr w => cases hv : v.1 <;> cases hw : w.1 <;>
          simp [pairGraph,SimpleGraph.sum,graph,hv,hw]
    unfold degree
    rw [he,Finset.card_map,part_card]

theorem selection_minimal (hd : 2 ≤ d) :
    IsMinimalStarForming (pairGraph d) 2 (selection d) := by
  rw [minimalStarForming_sum_iff]
  constructor
  · simpa [selection] using part_minimal d hd false
  · simpa [selection] using part_minimal d hd true

theorem selection_card : (selection d).card=2*d := by
  simp [selection,Finset.card_disjSum];omega

theorem pair_beta (hd : 2 ≤ d) : beta (pairGraph d) 2=2*d := by
  rw [beta_sum, beta_eq d hd]
  omega

theorem selection_isolates : isolates (pairGraph d) (selection d)=selection d := by
  classical
  ext v
  simp only [isolates,Finset.mem_filter,and_iff_left_iff_imp]
  intro hv
  have he : (selection d).filter ((pairGraph d).Adj v)= ∅ := by
    ext w
    cases v with
    | inl v => cases w with
      | inl w => simp_all [selection,Finset.mem_disjSum,pairGraph,graph,SimpleGraph.sum]
      | inr w => simp [pairGraph,SimpleGraph.sum]
    | inr v => cases w with
      | inl w => simp [pairGraph,SimpleGraph.sum]
      | inr w => simp_all [selection,Finset.mem_disjSum,pairGraph,graph,SimpleGraph.sum]
  change ((selection d).filter ((pairGraph d).Adj v)).card=0
  rw [he]
  rfl

theorem color_balance :
    ((selection d).filter (fun v => color d v=false)).card= d ∧
    ((selection d).filter (fun v => color d v=true)).card= d := by
  have hl : (selection d).filter (fun v => color d v=false) =
      (part d false).map Function.Embedding.inl := by
    apply Finset.ext
    intro v
    rw [Finset.mem_filter]
    cases v <;> simp [selection,color]
  have hr : (selection d).filter (fun v => color d v=true) =
      (part d true).map Function.Embedding.inr := by
    apply Finset.ext
    intro v
    rw [Finset.mem_filter]
    cases v <;> simp [selection,color]
  rw [hl,hr]
  simp

/-- Actual balanced isolates have B=z=2d but compensation W=2d>0. -/
theorem tight_but_positive (hd : 2 ≤ d) :
    (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) -
      (2*(d:ℤ)-1)*(selection d).card = (isolates (pairGraph d) (selection d)).card ∧
    (d:ℤ)*Fintype.card ((Bool × Fin d) ⊕ (Bool × Fin d)) +
      2*(beta (pairGraph d) 2:ℤ) - (2*(d:ℤ)+1)*(selection d).card = 2*(d:ℤ) ∧
    0 < 2*(d:ℤ) := by
  rw [selection_isolates,selection_card,pair_beta d hd]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  push_cast
  constructor
  · ring
  constructor
  · ring
  · exact_mod_cast (by omega : 0<2*d)

end D5.S3.Combinatorics.Graph.StarForming.CompleteBipartiteBalance
