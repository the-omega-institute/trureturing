/- GID: D5/S3/Combinatorics/Graph/StarForming/EqualityCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/EqualityCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The actual periodic cubic equality cores with finite parameter attainment. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import D5.S3.Combinatorics.Graph.StarForming.PrivateClauses
import D5.S3.Combinatorics.Graph.StarForming.SubcubicCertificate

/-! The C_k core in CUBIC_STABILITY_PORTS, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. Each twenty-vertex
cell contains H(0..5), U(6..11), X(12..17), and hubs 18,19. A permutation
joins the end of each H/X segment to the start of the next. A cyclic
permutation on Fin k is precisely the written C_k, with no finite-size cap. -/

namespace D5.S3.Combinatorics.Graph.StarForming.EqualityCore
open StarFormingDissociationRefutation Regular
open scoped BigOperators

def edges : Finset (Fin 20 × Fin 20) :=
  {(0,1),(1,2),(2,3),(3,4),(4,5),(12,13),(13,14),(14,15),(15,16),(16,17),
   (0,6),(1,7),(2,8),(3,9),(4,10),(5,11),
   (6,12),(7,13),(8,14),(9,15),(10,16),(11,17),
   (6,18),(8,18),(10,18),(7,19),(9,19),(11,19)}

abbrev internal (v w : Fin 20) : Prop := (v,w) ∈ edges ∨ (w,v) ∈ edges

variable {I : Type} [Fintype I] [DecidableEq I]

def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 20) where
  Adj x y := (x.1 = y.1 ∧ internal x.2 y.2) ∨
    (x.2 = 5 ∧ y.2 = 0 ∧ next x.1 = y.1) ∨
    (x.2 = 0 ∧ y.2 = 5 ∧ next y.1 = x.1) ∨
    (x.2 = 17 ∧ y.2 = 12 ∧ next x.1 = y.1) ∨
    (x.2 = 12 ∧ y.2 = 17 ∧ next y.1 = x.1)
  symm := ⟨by
    intro x y h
    rcases h with ⟨he,hb⟩ | ⟨ha,hb,he⟩ | ⟨ha,hb,he⟩ | ⟨ha,hb,he⟩ | ⟨ha,hb,he⟩
    · exact Or.inl ⟨he.symm,hb.symm⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hb,ha,he⟩))
    · exact Or.inr (Or.inl ⟨hb,ha,he⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb,ha,he⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb,ha,he⟩)))⟩
  loopless := ⟨by
    rintro ⟨i,v⟩ h
    have hi : ∀ v : Fin 20, ¬ internal v v := by decide +kernel
    rcases h with ⟨_,h⟩ | ⟨h1,h2,_⟩ | ⟨h1,h2,_⟩ | ⟨h1,h2,_⟩ | ⟨h1,h2,_⟩
    · exact hi v h
    all_goals simp only [Prod.snd] at h1 h2; exact (by omega)⟩

instance (next : Equiv.Perm I) : DecidableRel (graph next).Adj := fun x y =>
  inferInstanceAs (Decidable ((x.1 = y.1 ∧ internal x.2 y.2) ∨
    (x.2 = 5 ∧ y.2 = 0 ∧ next x.1 = y.1) ∨
    (x.2 = 0 ∧ y.2 = 5 ∧ next y.1 = x.1) ∨
    (x.2 = 17 ∧ y.2 = 12 ∧ next x.1 = y.1) ∨
    (x.2 = 12 ∧ y.2 = 17 ∧ next y.1 = x.1)))

def neighbors (next : Equiv.Perm I) (x : I × Fin 20) : Finset (I × Fin 20) :=
  let i := x.1
  match x.2.val with
  | 0 => {(next.symm i,5),(i,1),(i,6)}
  | 1 => {(i,0),(i,2),(i,7)}
  | 2 => {(i,1),(i,3),(i,8)}
  | 3 => {(i,2),(i,4),(i,9)}
  | 4 => {(i,3),(i,5),(i,10)}
  | 5 => {(i,4),(next i,0),(i,11)}
  | 6 => {(i,0),(i,12),(i,18)}
  | 7 => {(i,1),(i,13),(i,19)}
  | 8 => {(i,2),(i,14),(i,18)}
  | 9 => {(i,3),(i,15),(i,19)}
  | 10 => {(i,4),(i,16),(i,18)}
  | 11 => {(i,5),(i,17),(i,19)}
  | 12 => {(next.symm i,17),(i,13),(i,6)}
  | 13 => {(i,12),(i,14),(i,7)}
  | 14 => {(i,13),(i,15),(i,8)}
  | 15 => {(i,14),(i,16),(i,9)}
  | 16 => {(i,15),(i,17),(i,10)}
  | 17 => {(i,16),(next i,12),(i,11)}
  | 18 => {(i,6),(i,8),(i,10)}
  | _ => {(i,7),(i,9),(i,11)}

set_option maxHeartbeats 1200000 in
-- This proves all twenty symbolic rows; the index type and permutation stay arbitrary.
theorem mem_neighbors (next : Equiv.Perm I) (x y : I × Fin 20) :
    y ∈ neighbors next x ↔ (graph next).Adj x y := by
  rcases x with ⟨i,v⟩
  rcases y with ⟨j,w⟩
  fin_cases v <;>
    simp [neighbors,graph,internal,edges,eq_comm,Equiv.eq_symm_apply] <;> tauto

/-- Every symbolic cell is cubic, including permutations with fixed points. -/
theorem regular (next : Equiv.Perm I) (x : I × Fin 20) :
    DegreeCapacity.degree (graph next) x = 3 := by
  have he : Finset.univ.filter ((graph next).Adj x) = neighbors next x := by
    ext y
    simp [mem_neighbors]
  change (Finset.univ.filter ((graph next).Adj x)).card = 3
  rw [he]
  rcases x with ⟨i,v⟩
  fin_cases v <;> simp [neighbors]

def color (v : Fin 20) : Bool :=
  if 6 ≤ v.val ∧ v.val < 12 then decide (v.val % 2 = 0) else decide (v.val % 2 = 1)

/-- The cell bipartition is unchanged by every interface permutation. -/
theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2 := by
  have hlocal : ∀ v w : Fin 20, internal v w → color v ≠ color w := by decide +kernel
  have hc : ∀ x y, (graph next).Adj x y → color x.2 ≠ color y.2 := by
    intro x y h
    rcases h with ⟨_,h⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩ | ⟨hx,hy,_⟩
    · exact hlocal _ _ h
    all_goals simp [hx,hy,color]
  refine ⟨SimpleGraph.Coloring.mk (fun x => if color x.2 then (1 : Fin 2) else 0) ?_⟩
  intro x y h he
  have hn := hc x y h
  cases ha : color x.2 <;> cases hb : color y.2 <;> simp_all

abbrev selected (v : Fin 20) : Prop := v.val < 12
abbrev dissociation (v : Fin 20) : Prop :=
  (6 ≤ v.val ∧ v.val < 12) ∨ v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 12 ∨ v = 14 ∨ v = 16

def S : Finset (I × Fin 20) := Finset.univ.product (Finset.univ.filter selected)
def D : Finset (I × Fin 20) := Finset.univ.product (Finset.univ.filter dissociation)

private theorem filter_neighbors (next : Equiv.Perm I) (A : Finset (I × Fin 20)) (x) :
    A.filter ((graph next).Adj x) = (neighbors next x).filter (· ∈ A) := by
  ext y
  simp [mem_neighbors,and_comm]

theorem D_valid (next : Equiv.Perm I) : IsKIndependent (graph next) 2 D := by
  rintro ⟨i,v⟩ hv
  rw [filter_neighbors]
  fin_cases v <;>
    simp_all [D,Finset.product_eq_sprod,dissociation,neighbors,Finset.filter_insert,
      Finset.filter_singleton]

private theorem unique_selected_X (next : Equiv.Perm I) (i : I) (n : Fin 6)
    (w : I × Fin 20) (hw : selected w.2)
    (ha : (graph next).Adj (i,⟨12+n.val,by omega⟩) w) :
    w = (i,⟨6+n.val,by omega⟩) := by
  rw [← mem_neighbors] at ha
  rcases w with ⟨j,v⟩
  fin_cases n <;> simp_all [neighbors,selected] <;>
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp_all

private theorem unique_selected_U (next : Equiv.Perm I) (i : I) (n : Fin 6)
    (w : I × Fin 20) (hw : selected w.2)
    (ha : (graph next).Adj (i,⟨6+n.val,by omega⟩) w) :
    w = (i,⟨n.val,by omega⟩) := by
  rw [← mem_neighbors] at ha
  rcases w with ⟨j,v⟩
  fin_cases n <;> simp_all [neighbors,selected] <;>
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp_all

theorem S_minimal (next : Equiv.Perm I) :
    IsMinimalStarForming (graph next) 2 S := by
  apply (regular_minimal_iff _ _).mp
  have hs (x : I × Fin 20) : x ∈ (S : Finset (I × Fin 20)) ↔ selected x.2 := by
    simp [S,Finset.product_eq_sprod]
  simp_rw [hs]
  apply Subcubic.minimal_of_deletion_failures
  · rintro ⟨i,v⟩ hv
    fin_cases v <;> simp [selected] at hv
    · exact Or.inr ⟨(i,6),(i,0),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inr ⟨(i,7),(i,1),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inr ⟨(i,8),(i,2),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inr ⟨(i,9),(i,3),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inr ⟨(i,10),(i,4),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inr ⟨(i,11),(i,5),by norm_num [selected],by norm_num [selected],
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inl ⟨(i,6),(i,8),by norm_num [selected],by norm_num [selected],by simp,
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
    · exact Or.inl ⟨(i,7),(i,9),by norm_num [selected],by norm_num [selected],by simp,
        (mem_neighbors next _ _).mp (by simp [neighbors]),
        (mem_neighbors next _ _).mp (by simp [neighbors])⟩
  · rintro ⟨i,v⟩ hv
    have hvl : v.val < 12 := hv
    let n : Fin 6 := ⟨v.val % 6,by omega⟩
    let x : I × Fin 20 := (i,⟨12+n.val,by omega⟩)
    let u : I × Fin 20 := (i,⟨6+n.val,by omega⟩)
    let h : I × Fin 20 := (i,⟨n.val,by omega⟩)
    have hvh : (i,v) = h ∨ (i,v) = u := by
      by_cases hh : v.val < 6
      · left; change (i,v) = (i,⟨n.val,by omega⟩); congr 1; apply Fin.ext; simp [n,Nat.mod_eq_of_lt hh]
      · right; change (i,v) = (i,⟨6+n.val,by omega⟩); congr 1; apply Fin.ext; dsimp [n]; omega
    refine ⟨x,by simp [x,selected],?_⟩
    rintro (⟨a,b,ha,hb,hab,hxa,hxb⟩ | ⟨c,l,hc,hl,hxc,hcl⟩)
    · exact hab ((unique_selected_X next i n a ha.1 hxa).trans
        (unique_selected_X next i n b hb.1 hxb).symm)
    · have hcu : c = u := unique_selected_X next i n c hc.1 hxc
      subst c
      have hlh : l = h := unique_selected_U next i n l hl.1 hcl
      rcases hvh with he | he
      · exact hl.2 (hlh.trans he.symm)
      · exact hc.2 he.symm

theorem selected_card : (S : Finset (I × Fin 20)).card = 12 * Fintype.card I := by
  have hc : (Finset.univ.filter selected).card = 12 := by decide +kernel
  simp [S,Finset.product_eq_sprod,hc,Nat.mul_comm]

theorem dissociation_card : (D : Finset (I × Fin 20)).card = 12 * Fintype.card I := by
  have hc : (Finset.univ.filter dissociation).card = 12 := by decide +kernel
  simp [D,Finset.product_eq_sprod,hc,Nat.mul_comm]

/-- Both finite extrema are attained by the written H/U and matching selections.
The bound is the all-order degree sum, not enumeration of the cell count. -/
theorem exact_parameters (next : Equiv.Perm I) :
    beta (graph next) 2 = 12 * Fintype.card I ∧
    SF (graph next) 2 = 12 * Fintype.card I := by
  classical
  have hSF := DegreeCapacity.sf_regular_bound (graph next) 3 (by decide) (regular next)
  have hS : (S : Finset (I × Fin 20)).card ≤ SF (graph next) 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,S_minimal next⟩)
  have hD : (D : Finset (I × Fin 20)).card ≤ beta (graph next) 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,D_valid next⟩)
  have hb := beta_le_sf (graph next)
  rw [selected_card] at hS
  rw [dissociation_card] at hD
  simp only [Fintype.card_prod,Fintype.card_fin] at hSF
  constructor <;> omega

end D5.S3.Combinatorics.Graph.StarForming.EqualityCore
