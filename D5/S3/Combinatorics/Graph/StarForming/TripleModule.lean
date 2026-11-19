/- GID: D5/S3/Combinatorics/Graph/StarForming/TripleModule
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/TripleModule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual forty-eight-vertex module and nonoverlapping dissociation accounting. -/

import D5.S3.Combinatorics.Graph.StarForming.ClosedCore
import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation

/-! The open forty-eight-vertex module of CUBIC_TRIPLE_PORT_COMPENSATION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The triple-port core occupies labels zero through nineteen. Each of two
fourteen-vertex blocks retains its original cyclic labels. -/

namespace D5.S3.Combinatorics.Graph.StarForming.TripleModule
open StarFormingDissociationRefutation
open scoped BigOperators
set_option maxRecDepth 8192

def neighbors : Fin 48 → List (Fin 48) :=
  ![[1, 5, 6], [0, 2, 7], [1, 3, 8], [2, 4, 9], [3, 5, 10], [0, 4, 11], [0, 12, 18], [1, 13, 19], [2, 14, 18], [3, 15, 19], [4, 16, 18], [5, 17, 19], [6, 17, 28], [7, 14, 20], [8, 13, 42], [9, 16, 34], [10, 15], [11, 12], [6, 8, 10], [7, 9, 11], [13, 27, 30], [28, 29, 31], [29, 30, 32], [30, 31, 33], [27, 31, 32], [28, 32, 33], [27, 29, 33], [20, 24, 26], [12, 21, 25], [21, 22, 26], [20, 22, 23], [21, 23, 24], [22, 24, 25], [23, 25, 26], [15, 41, 44], [42, 43, 45], [43, 44, 46], [44, 45, 47], [41, 45, 46], [42, 46, 47], [41, 43, 47], [34, 38, 40], [14, 35, 39], [35, 36, 40], [34, 36, 37], [35, 37, 38], [36, 38, 39], [37, 39, 40]]

def graph : SimpleGraph (Fin 48) where
  Adj v w := w∈neighbors v
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_∈_))

def partition : Fin 48 ≃ (Fin 20 ⊕ (Fin 2 × Fin 14)) :=
  (finSumFinEquiv (m := 20) (n := 28)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin 20))
      (finProdFinEquiv (m := 2) (n := 14)).symm)

def core (v : Fin 20) : Fin 48 := partition.symm (.inl v)
def block (j : Fin 2) (v : Fin 14) : Fin 48 := partition.symm (.inr (j,v))

def coreSlice (D : Finset (Fin 48)) : Finset (Fin 20) := Finset.univ.filter (fun v => core v∈D)
def blockSlice (D : Finset (Fin 48)) (j : Fin 2) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => block j v∈D)

private theorem core_injective : Function.Injective core :=
  fun _ _ h => Sum.inl.inj (partition.symm.injective h)
private theorem block_injective (j : Fin 2) : Function.Injective (block j) :=
  fun _ _ h => congrArg Prod.snd (Sum.inr.inj (partition.symm.injective h))

private theorem core_edges : ∀ v w : Fin 20,
    ClosedCore.graph.Adj v w → graph.Adj (core v) (core w) := by decide +kernel
private theorem block_edges : ∀ j : Fin 2, ∀ v w : Fin 14,
    HeawoodPorts.graph.Adj v w → graph.Adj (block j v) (block j w) := by decide +kernel

private theorem core_independent (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) :
    IsKIndependent ClosedCore.graph 2 (coreSlice D) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  apply core_injective
  exact (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
    (core c) (Finset.mem_filter.mp hc).2 (core a) (Finset.mem_filter.mp ha).2
    (core b) (Finset.mem_filter.mp hb).2 (core_edges c a hca) (core_edges c b hcb)

private theorem block_independent (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) (j : Fin 2) :
    IsKIndependent HeawoodPorts.graph 2 (blockSlice D j) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  apply block_injective j
  exact (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
    (block j c) (Finset.mem_filter.mp hc).2 (block j a) (Finset.mem_filter.mp ha).2
    (block j b) (Finset.mem_filter.mp hb).2 (block_edges j c a hca) (block_edges j c b hcb)

theorem card_fibers {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) :
    S.card=∑ a : A, (Finset.univ.filter (fun b => (a,b)∈S)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (by intro _ _; simp)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.card_bij (fun x _ => x.2)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨by simp,by
      have h := Finset.mem_filter.mp hx
      have he : (a,x.2)=x := Prod.ext h.2.symm rfl
      rw [he]
      exact h.1⟩
  · intro x hx y hy he
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he
  · intro b hb
    exact ⟨(a,b),by simpa using hb,rfl⟩

/-- The actual disjoint core/block partition counts each selected vertex once. -/
theorem card_slices (D : Finset (Fin 48)) :
    D.card=(coreSlice D).card+∑ j : Fin 2, (blockSlice D j).card := by
  classical
  let T := D.image partition
  have ht : T.card=D.card := Finset.card_image_of_injective _ partition.injective
  have hl : T.toLeft=coreSlice D := by
    ext v
    simp only [Finset.mem_toLeft,Finset.mem_image,coreSlice,Finset.mem_filter,
      Finset.mem_univ,true_and,T]
    constructor
    · rintro ⟨a,ha,he⟩
      simpa [core,← he] using ha
    · intro hv
      exact ⟨core v,hv,partition.apply_symm_apply _⟩
  have hr (j : Fin 2) : (Finset.univ.filter (fun v => (j,v)∈T.toRight))=blockSlice D j := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_toRight,
      Finset.mem_image,T,blockSlice]
    constructor
    · rintro ⟨a,ha,he⟩
      simpa [block,← he] using ha
    · intro hv
      exact ⟨block j v,hv,partition.apply_symm_apply _⟩
  have h := Finset.card_toLeft_add_card_toRight (u := T)
  rw [hl,card_fibers] at h
  simp_rw [hr] at h
  omega

def evenPort (j : Fin 2) : Fin 20 := ⟨12+2*j.val,by omega⟩
def oddPort (j : Fin 2) : Fin 20 := ⟨13+2*j.val,by omega⟩

private theorem attachments : ∀ j : Fin 2,
    graph.Adj (block j 0) (core (oddPort j)) ∧ graph.Adj (block j 8) (core (evenPort j)) := by
  decide +kernel

private theorem core_block_distinct : ∀ j : Fin 2, ∀ v : Fin 20, ∀ w : Fin 14,
    core v≠block j w := by decide +kernel

/-- An eight-vertex block consumes its own pair of omitted core endpoints. -/
theorem saturated_omission (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D)
    (j : Fin 2) (h8 : (blockSlice D j).card=8) :
    evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D := by
  have hb := (HeawoodPorts.facts _ (block_independent D hD j)).2 h8
  have hi := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
  have exclude (p : Fin 14) (v : Fin 20) (hp : p∈blockSlice D j)
      (hd : DegreeCapacity.selectedDegree HeawoodPorts.graph (blockSlice D j) p=1)
      (ha : graph.Adj (block j p) (core v)) : v∉coreSlice D := by
    intro hv
    have hpos : 0 < ((blockSlice D j).filter (HeawoodPorts.graph.Adj p)).card := by
      change 0 < DegreeCapacity.selectedDegree HeawoodPorts.graph (blockSlice D j) p
      omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hpos
    have he := hi (block j p) (Finset.mem_filter.mp hp).2
      (core v) (Finset.mem_filter.mp hv).2
      (block j w) (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
      ha (block_edges j p w (Finset.mem_filter.mp hw).2)
    exact core_block_distinct j v w he
  exact ⟨exclude 8 (evenPort j) hb.2.1 hb.2.2.2 (attachments j).2,
    exclude 0 (oddPort j) hb.1 hb.2.2.1 (attachments j).1⟩

/-- Both actual block surpluses use distinct omitted core pairs. The stronger
closed-high deletion-core theorem supplies the local omission bound. -/
theorem beta_cap (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) : D.card≤26 := by
  have hc := ClosedCore.omission_bound _ (core_independent D hD)
  have hb (j : Fin 2) : (blockSlice D j).card ≤
      7+(if evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D then 1 else 0) := by
    have h := (HeawoodPorts.facts _ (block_independent D hD j)).1
    by_cases he : (blockSlice D j).card=8
    · have ho := saturated_omission D hD j he
      simp [ho,he]
    · split_ifs <;> omega
  have h0 := hb 0
  have h1 := hb 1
  rw [card_slices]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero]
  change (coreSlice D).card+((blockSlice D 0).card+(blockSlice D 1).card)≤26
  change (coreSlice D).card+
    ((if 12∉coreSlice D ∧ 13∉coreSlice D then 1 else 0)+
     (if 14∉coreSlice D ∧ 15∉coreSlice D then 1 else 0)+
     (if 16∉coreSlice D ∧ 17∉coreSlice D then 1 else 0))≤12 at hc
  norm_num [evenPort,oddPort] at h0 h1
  omega

end D5.S3.Combinatorics.Graph.StarForming.TripleModule
