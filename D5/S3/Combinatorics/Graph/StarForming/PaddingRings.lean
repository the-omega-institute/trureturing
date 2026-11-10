/- GID: D5/S3/Combinatorics/Graph/StarForming/PaddingRings
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PaddingRings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual four-port rings with independently varying finite core sizes. -/

import D5.S3.Combinatorics.Graph.StarForming.PaddingModule
import Mathlib.Data.Fintype.BigOperators

/-! The two-parameter construction of CUBIC_EQUALITY_PADDING_RINGS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Each module has its own finite core index type and permutation.
The marked cell is actual data, so every nonempty module has positive size.
Module and core permutations are independent. In particular, arbitrary
positive cell sizes in a cyclic ring are retained. -/
namespace D5.S3.Combinatorics.Graph.StarForming.PaddingRings
open StarFormingDissociationRefutation
open scoped BigOperators

variable {J : Type} [Fintype J] [DecidableEq J]
variable (K : J → Type) [∀ j, Fintype (K j)] [∀ j, DecidableEq (K j)]
abbrev Vertex := (j : J) × PaddingModule.Vertex (K j)

inductive Within (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) :
    Vertex K → Vertex K → Prop
  | intro (j : J) (v w : PaddingModule.Vertex (K j))
      (h : (PaddingModule.graph (q j) (mark j)).Adj v w) :
      Within q mark ⟨j,v⟩ ⟨j,w⟩

variable {K}

private theorem within_same (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (j : J) (v w : PaddingModule.Vertex (K j)) :
    Within K q mark ⟨j,v⟩ ⟨j,w⟩ ↔ (PaddingModule.graph (q j) (mark j)).Adj v w := by
  constructor
  · intro h
    cases h with
    | intro _ _ _ h => exact h
  · exact Within.intro j v w

private theorem within_symm (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (x y : Vertex K) (h : Within K q mark x y) : Within K q mark y x := by
  cases h with
  | intro j v w h => exact Within.intro j w v h.symm

private theorem within_index (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (x y : Vertex K) (h : Within K q mark x y) : x.1=y.1 := by
  cases h
  rfl

def left (mark : ∀ j, K j) (j : J) : Vertex K :=
  ⟨j,PaddingModule.leftPort (mark j)⟩
def right (mark : ∀ j, K j) (j : J) : Vertex K :=
  ⟨j,PaddingModule.rightPort (mark j)⟩

private theorem left_ne_right (mark : ∀ j, K j) (i j : J) : left mark i ≠ right mark j := by
  intro h
  have he : i=j := congrArg Sigma.fst h
  subst j
  have hh := (Sigma.mk.inj_iff.mp h).2
  cases hh

def graph (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) :
    SimpleGraph (Vertex K) where
  Adj x y := Within K q mark x y ∨
    (∃ j, x=left mark j ∧ y=right mark (e j)) ∨
    (∃ j, y=left mark j ∧ x=right mark (e j))
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · cases h with
      | intro j v w h => exact Or.inl (Within.intro j w v h.symm)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | ⟨j,hx,hy⟩ | ⟨j,hx,hy⟩
    · cases h with
      | intro j v _ h => exact (PaddingModule.graph (q j) (mark j)).irrefl h
    all_goals exact left_ne_right mark j (e j) (hx.symm.trans hy)⟩

noncomputable instance (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) :
    DecidableRel (graph q mark e).Adj := Classical.decRel _

private def embed (j : J) : PaddingModule.Vertex (K j) ↪ Vertex K :=
  ⟨(fun v => (⟨j,v⟩ : Vertex K)),fun _ _ h => by simpa using h⟩

def neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) (x : Vertex K) : Finset (Vertex K) :=
  (PaddingModule.neighbors (q x.1) (mark x.1) x.2).map (embed x.1) ∪
    (if x=left mark x.1 then {right mark (e x.1)} else
     if x=right mark x.1 then {left mark (e.symm x.1)} else ∅)

private theorem within_neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (x y : Vertex K) :
    y ∈ (PaddingModule.neighbors (q x.1) (mark x.1) x.2).map (embed x.1) ↔
      Within K q mark x y := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_map.mp h
    subst y
    exact Within.intro x.1 x.2 w ((PaddingModule.mem_neighbors _ _ _ _).mp hw)
  · intro h
    cases h with
    | intro j v w h =>
      exact Finset.mem_map.mpr ⟨w,(PaddingModule.mem_neighbors _ _ _ _).mpr h,rfl⟩

private theorem interface_neighbors (mark : ∀ j, K j) (e : Equiv.Perm J)
    (x y : Vertex K) :
    y ∈ (if x=left mark x.1 then {right mark (e x.1)} else
     if x=right mark x.1 then {left mark (e.symm x.1)} else (∅ : Finset (Vertex K))) ↔
    (∃ j, x=left mark j ∧ y=right mark (e j)) ∨
    (∃ j, y=left mark j ∧ x=right mark (e j)) := by
  have hne := left_ne_right mark x.1 x.1
  constructor
  · intro h
    split_ifs at h with hl hr
    · exact Or.inl ⟨x.1,hl,Finset.mem_singleton.mp h⟩
    · exact Or.inr ⟨e.symm x.1,Finset.mem_singleton.mp h,by simpa using hr⟩
    · exact (Finset.notMem_empty y h).elim
  · rintro (⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩)
    · simp [left]
    · have hn := left_ne_right mark (e j) (e j)
      change left mark j ∈ (if right mark (e j)=left mark (e j) then _ else
        if right mark (e j)=right mark (e j) then _ else _)
      rw [if_neg (Ne.symm hn)]
      simp [right]

theorem mem_neighbors (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) (x y : Vertex K) :
    y ∈ neighbors q mark e x ↔ (graph q mark e).Adj x y := by
  rw [neighbors,Finset.mem_union,within_neighbors,interface_neighbors]
  rfl

def slice (S : Finset (Vertex K)) (j : J) : Finset (PaddingModule.Vertex (K j)) :=
  Finset.univ.filter (fun v => (⟨j,v⟩ : Vertex K) ∈ S)

/-- Actual dependent fibers partition every selected set; shared vertices are
never counted in a second module. -/
theorem card_slices (S : Finset (Vertex K)) : S.card=∑ j, (slice S j).card := by
  classical
  have he : S=Finset.univ.sigma (slice S) := by
    ext x
    simp [slice]
  calc
    S.card = (Finset.univ.sigma (slice S)).card := congrArg Finset.card he
    _ = _ := Finset.card_sigma _ _

private theorem slice_independent (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) (S : Finset (Vertex K)) (hS : IsKIndependent (graph q mark e) 2 S)
    (j : J) : IsKIndependent (PaddingModule.graph (q j) (mark j)) 2 (slice S j) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro v hv a ha b hb hva hvb
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    ⟨j,v⟩ (Finset.mem_filter.mp hv).2 ⟨j,a⟩ (Finset.mem_filter.mp ha).2
    ⟨j,b⟩ (Finset.mem_filter.mp hb).2
    (Or.inl (Within.intro j v a hva)) (Or.inl (Within.intro j v b hvb))
  exact (embed j).injective hh

/-- Every saturated Heawood surplus is paid by its own whole-core loss,
uniformly in all independently varying positive core sizes. -/
theorem beta_upper (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) :
    beta (graph q mark e) 2 ≤ 7*Fintype.card J+12*∑ j, Fintype.card (K j) := by
  classical
  apply Finset.sup_le
  intro S hS
  rw [card_slices]
  calc
    ∑ j, (slice S j).card ≤ ∑ j, (7+12*Fintype.card (K j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact PaddingModule.beta_cap (q j) (mark j) (slice S j)
        (slice_independent q mark e S (Finset.mem_filter.mp hS).2 j)
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

private theorem no_port_edge (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (i j : J) :
    ¬ Within K q mark (left mark i) (right mark j) := by
  intro h
  have hi := within_index q mark _ _ h
  change i=j at hi
  subst j
  have hh := (within_same q mark i _ _).mp h
  simp [PaddingModule.graph,PaddingModule.adjacency,PaddingModule.leftPort,
    PaddingModule.rightPort,FourPortCore.graph,FourPortCore.cut] at hh

private theorem local_neighbors_card (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (x : Vertex K) :
    ((PaddingModule.neighbors (q x.1) (mark x.1) x.2).map (embed x.1)).card =
      if x=left mark x.1 ∨ x=right mark x.1 then 2 else 3 := by
  rcases x with ⟨j,v⟩
  rw [Finset.card_map]
  have he : Finset.univ.filter ((PaddingModule.graph (q j) (mark j)).Adj v)=
      PaddingModule.neighbors (q j) (mark j) v := by
    ext y
    simp [PaddingModule.mem_neighbors]
  rw [← he]
  simpa [left,right,DegreeCapacity.degree] using PaddingModule.degree (q j) (mark j) v

/-- Every ring seam supplies exactly one missing degree, including restored
singleton seams, independently of the two permutations and all core sizes. -/
theorem regular (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J)
    (x : Vertex K) : DegreeCapacity.degree (graph q mark e) x=3 := by
  classical
  have he : Finset.univ.filter ((graph q mark e).Adj x)=neighbors q mark e x := by
    ext y
    simp [mem_neighbors]
  change (Finset.univ.filter _).card=3
  rw [he]
  have hc := local_neighbors_card q mark x
  by_cases hl : x=left mark x.1
  · have hn : right mark (e x.1) ∉
        (PaddingModule.neighbors (q x.1) (mark x.1) x.2).map (embed x.1) := by
      rw [within_neighbors]
      rw [hl]
      exact no_port_edge q mark _ _
    simp only [neighbors,if_pos hl,Finset.union_singleton,
      Finset.card_insert_of_notMem hn]
    rw [if_pos (Or.inl hl)] at hc
    omega
  · by_cases hr : x=right mark x.1
    · have hn : left mark (e.symm x.1) ∉
          (PaddingModule.neighbors (q x.1) (mark x.1) x.2).map (embed x.1) := by
        rw [within_neighbors]
        rw [hr]
        intro h
        exact no_port_edge q mark _ _ (within_symm q mark _ _ h)
      simp only [neighbors,if_neg hl,if_pos hr,Finset.union_singleton,
        Finset.card_insert_of_notMem hn]
      rw [if_pos (Or.inr hr)] at hc
      omega
    · simpa [neighbors,hl,hr] using hc

/-- The source bipartition is proper on internal edges and every ring seam. -/
theorem bipartite (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) :
    (graph q mark e).Colorable 2 := by
  let c : Vertex K → Bool := fun x => PaddingModule.color x.2
  have hp (x y : Vertex K) (h : (graph q mark e).Adj x y) : c x ≠ c y := by
    rcases h with h | ⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩
    · cases h with
      | intro j v w h => exact PaddingModule.proper_color (q j) (mark j) v w h
    all_goals simp [c,left,right,PaddingModule.color,PaddingModule.leftPort,
      PaddingModule.rightPort,EqualityCore.color]
  refine ⟨SimpleGraph.Coloring.mk (fun x => if c x then (1 : Fin 2) else 0) ?_⟩
  intro x y h he
  have hn := hp x y h
  cases hx : c x <;> cases hy : c y <;> simp_all

def independent : Finset (Vertex K) := Finset.univ.sigma (fun _ => PaddingModule.independent)
def forming : Finset (Vertex K) := Finset.univ.sigma (fun _ => PaddingModule.forming)

private theorem independent_edge (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) (x y : Vertex K) (hx : x ∈ independent) (hy : y ∈ independent)
    (h : (graph q mark e).Adj x y) : Within K q mark x y := by
  rcases h with h | ⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩
  · exact h
  · simp [independent,right,PaddingModule.independent,PaddingModule.rightPort,
      EqualityCore.D,EqualityCore.dissociation] at hy
  · simp [independent,right,PaddingModule.independent,PaddingModule.rightPort,
      EqualityCore.D,EqualityCore.dissociation] at hx

theorem independent_valid (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) : IsKIndependent (graph q mark e) 2 independent := by
  classical
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro v hv a ha b hb hva hvb
  have h1 := independent_edge q mark e v a hv ha hva
  have h2 := independent_edge q mark e v b hv hb hvb
  cases h1 with
  | intro j v a h1 =>
    cases h2 with
    | intro _ _ b h2 =>
      apply congrArg (Sigma.mk j)
      apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp
        (PaddingModule.independent_valid (q j) (mark j)) v
        (by simpa [independent] using hv) a (by simpa [independent] using ha)
        b (by simpa [independent] using hb) h1 h2

theorem independent_card : (independent : Finset (Vertex K)).card=
    7*Fintype.card J+12*∑ j, Fintype.card (K j) := by
  rw [independent,Finset.card_sigma]
  simp [PaddingModule.independent_card,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

theorem forming_card : (forming : Finset (Vertex K)).card=
    8*Fintype.card J+12*∑ j, Fintype.card (K j) := by
  rw [forming,Finset.card_sigma]
  simp [PaddingModule.forming_card,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

theorem order : Fintype.card (Vertex K)=14*Fintype.card J+20*∑ j, Fintype.card (K j) := by
  simp [Vertex,Fintype.card_sigma,Fintype.card_sum,Fintype.card_prod,
    Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_comm]

private theorem fiber_minimal (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) :
    Regular.Minimal (Within K q mark) (fun x : Vertex K => x.2∈PaddingModule.forming) := by
  classical
  have hm (j : J) := (regular_minimal_iff _ _).mpr (PaddingModule.forming_minimal (q j) (mark j))
  refine ⟨?_,?_⟩
  · rintro ⟨j,v⟩ hv
    rcases (hm j).1 v hv with ⟨a,b,ha,hb,hne,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩
    · exact Or.inl ⟨⟨j,a⟩,⟨j,b⟩,ha,hb,fun he => hne ((embed j).injective he),
        Within.intro j v a hva,Within.intro j v b hvb⟩
    · exact Or.inr ⟨⟨j,c⟩,⟨j,l⟩,hc,hl,Within.intro j v c hvc,Within.intro j c l hcl⟩
  · intro T hsub ⟨⟨j,d⟩,hd,hnot⟩ hT
    apply (hm j).2 (fun v => T ⟨j,v⟩) (fun v hv => hsub _ hv) ⟨d,hd,hnot⟩
    intro v hv
    rcases hT ⟨j,v⟩ hv with ⟨a,b,ha,hb,hne,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩
    · cases hva with
      | intro _ _ a hva =>
        cases hvb with
        | intro _ _ b hvb =>
          exact Or.inl ⟨a,b,ha,hb,fun he => hne (congrArg (Sigma.mk j) he),hva,hvb⟩
    · cases hvc with
      | intro _ _ c hvc =>
        cases hcl with
        | intro _ _ l hcl => exact Or.inr ⟨c,l,hc,hl,hvc,hcl⟩

/-- Every seam has both endpoints outside the full original selection;
formation and all deletion failures survive unchanged. -/
theorem forming_minimal (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j)
    (e : Equiv.Perm J) : IsMinimalStarForming (graph q mark e) 2 forming := by
  classical
  apply (regular_minimal_iff _ _).mp
  have hm : Regular.Minimal (graph q mark e).Adj
      (fun x : Vertex K => x.2∈PaddingModule.forming) := by
    apply Cubic.minimal_rewiring_forward _ _ _ ?_ (fiber_minimal q mark)
    intro x y hsel
    constructor
    · exact Or.inl
    · rintro (h | ⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩)
      · exact h
      all_goals rcases hsel with h | h
      all_goals
        have hh := Finset.inr_mem_disjSum.mp h
        have hv := (Finset.mem_filter.mp (Finset.mem_product.mp hh).2).2
        norm_num [EqualityCore.selected] at hv
  simpa [forming] using hm

/-- The exact finite maxima are both attained for arbitrary core types,
independent core permutations and any module permutation. -/
theorem parameters (q : ∀ j, Equiv.Perm (K j)) (mark : ∀ j, K j) (e : Equiv.Perm J) :
    beta (graph q mark e) 2 = 7*Fintype.card J+12*∑ j, Fintype.card (K j) ∧
    SF (graph q mark e) 2 = 8*Fintype.card J+12*∑ j, Fintype.card (K j) := by
  classical
  have hb := beta_upper q mark e
  have hl : (independent : Finset (Vertex K)).card ≤ beta (graph q mark e) 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,independent_valid q mark e⟩)
  rw [independent_card] at hl
  have hbeta := Nat.le_antisymm hb hl
  have hs : (forming : Finset (Vertex K)).card ≤ SF (graph q mark e) 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,forming_minimal q mark e⟩)
  rw [forming_card] at hs
  have hu := RegularCompensation.sf_regular_bound (graph q mark e) (bipartite q mark e)
    3 (regular q mark e)
  rw [hbeta,order] at hu
  norm_num at hu
  exact ⟨hbeta,by omega⟩

end D5.S3.Combinatorics.Graph.StarForming.PaddingRings
