/- GID: D5/S3/Combinatorics/Graph/StarForming/LongCoreRings
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/LongCoreRings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual long-core assemblies with exact dissociation and original attaining word. -/

import D5.S3.Combinatorics.Graph.StarForming.LongCoreOmission
import D5.S3.Combinatorics.Graph.StarForming.ClosedRingWitnesses

/-! L_k from LONG_CORE_WORD_OBSTRUCTION and LONG_CORE_SHARP_OMISSION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
Both H and X cross the forward module seam. The H seam is not silently
closed inside each module as in the distinct Z family. -/
namespace D5.S3.Combinatorics.Graph.StarForming.LongCoreRings
open StarFormingDissociationRefutation ClosedModule
open scoped BigOperators
set_option maxRecDepth 8192

def localNeighbors (v : Fin 62) : List (Fin 62) :=
  if v=0 then [1,6] else if v=5 then [4,11] else ClosedModule.neighbors v

def localGraph : SimpleGraph (Fin 62) where
  Adj v w := w∈localNeighbors v
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel localGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_∈_))

private theorem core_injective : Function.Injective core :=
  fun _ _ h => Sum.inl.inj (partition.symm.injective h)
private theorem block_injective (j : Fin 3) : Function.Injective (block j) :=
  fun _ _ h => congrArg Prod.snd (Sum.inr.inj (partition.symm.injective h))

private theorem core_edges : ∀ v w : Fin 20,
    LongCoreOmission.graph.Adj v w → localGraph.Adj (core v) (core w) := by decide +kernel
private theorem block_edges : ∀ j : Fin 3, ∀ v w : Fin 14,
    HeawoodPorts.graph.Adj v w → localGraph.Adj (block j v) (block j w) := by decide +kernel

private theorem block_independent (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) (j : Fin 3) :
    IsKIndependent HeawoodPorts.graph 2 (blockSlice D j) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  apply block_injective j
  exact (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
    (block j c) (Finset.mem_filter.mp hc).2 (block j a) (Finset.mem_filter.mp ha).2
    (block j b) (Finset.mem_filter.mp hb).2 (block_edges j c a hca) (block_edges j c b hcb)

private theorem attachments : ∀ j : Fin 3,
    localGraph.Adj (block j 0) (core (oddPort j)) ∧ localGraph.Adj (block j 8) (core (evenPort j)) := by
  decide +kernel

private theorem core_block_distinct : ∀ j : Fin 3, ∀ v : Fin 20, ∀ w : Fin 14,
    core v≠block j w := by decide +kernel

/-- An eight-vertex block consumes its own pair of omitted core endpoints. -/
theorem saturated_omission (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D)
    (j : Fin 3) (h8 : (blockSlice D j).card=8) :
    evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D := by
  have hb := (HeawoodPorts.facts _ (block_independent D hD j)).2 h8
  have hi := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
  have exclude (p : Fin 14) (v : Fin 20) (hp : p∈blockSlice D j)
      (hd : DegreeCapacity.selectedDegree HeawoodPorts.graph (blockSlice D j) p=1)
      (ha : localGraph.Adj (block j p) (core v)) : v∉coreSlice D := by
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

/-- Restriction to a module pays each saturated Heawood surplus with its
own actual omitted core pair; the remaining core score is retained. -/
theorem module_credit (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) :
    D.card≤21+(coreSlice D).card+LongCoreOmission.omitted (coreSlice D) false := by
  have hb (j : Fin 3) : (blockSlice D j).card≤
      7+(if evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D then 1 else 0) := by
    have h := (HeawoodPorts.facts _ (block_independent D hD j)).1
    by_cases he : (blockSlice D j).card=8
    · have ho := saturated_omission D hD j he
      simp [ho,he]
    · split_ifs <;> omega
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  rw [ClosedModule.card_slices]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero]
  change (coreSlice D).card + ((blockSlice D 0).card +
    ((blockSlice D 1).card + (blockSlice D 2).card))≤_
  norm_num [evenPort,oddPort] at h0 h1 h2
  change _≤21+(coreSlice D).card+
    ((if 12∉coreSlice D ∧ 13∉coreSlice D then 1 else 0)+
     (if 14∉coreSlice D ∧ 15∉coreSlice D then 1 else 0)+
     (if 16∉coreSlice D ∧ 17∉coreSlice D then 1 else 0))
  omega

variable {I : Type} [Fintype I] [DecidableEq I]

def forward (v w : Fin 62) : Prop := (v=5 ∧ w=0) ∨ (v=17 ∧ w=12)
instance : DecidableRel forward := fun _ _ => inferInstanceAs (Decidable ((_∧_)∨(_∧_)))

def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 62) where
  Adj a b := (a.1=b.1 ∧ localGraph.Adj a.2 b.2) ∨
    (e a.1=b.1 ∧ forward a.2 b.2) ∨ (e b.1=a.1 ∧ forward b.2 a.2)
  symm := ⟨by
    intro a b h
    rcases h with ⟨he,h⟩ | h | h
    · exact Or.inl ⟨he.symm,localGraph.adj_symm h⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h | h
    · exact localGraph.irrefl h.2
    all_goals rcases h.2 with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> omega⟩
instance (e : Equiv.Perm I) : DecidableRel (graph e).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((_∧_)∨(_∧_)∨(_∧_)))

def slice (S : Finset (I × Fin 62)) (i : I) : Finset (Fin 62) :=
  Finset.univ.filter (fun v => (i,v)∈S)

def coreSet (S : Finset (I × Fin 62)) : Finset (I × Fin 20) :=
  Finset.univ.filter (fun v => (v.1,core v.2)∈S)

private theorem local_independent (e : Equiv.Perm I) (S : Finset (I × Fin 62))
    (hS : IsKIndependent (graph e) 2 S) (i : I) :
    IsKIndependent localGraph 2 (slice S i) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  exact congrArg Prod.snd ((SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (i,c) (Finset.mem_filter.mp hc).2 (i,a) (Finset.mem_filter.mp ha).2
    (i,b) (Finset.mem_filter.mp hb).2 (Or.inl ⟨rfl,hca⟩) (Or.inl ⟨rfl,hcb⟩))

private theorem core_forward : ∀ a b : Fin 20,
    LongCoreWord.forward a b → forward (core a) (core b) := by decide +kernel

private theorem coreSet_independent (e : Equiv.Perm I) (S : Finset (I × Fin 62))
    (hS : IsKIndependent (graph e) 2 S) :
    IsKIndependent (LongCoreWord.graph e) 2 (coreSet S) := by
  have he (a b : I × Fin 20) (h : (LongCoreWord.graph e).Adj a b) :
      (graph e).Adj (a.1,core a.2) (b.1,core b.2) := by
    rcases h with ⟨hi,h⟩ | ⟨hi,h⟩ | ⟨hi,h⟩
    · exact Or.inl ⟨hi,core_edges _ _ h⟩
    · exact Or.inr (Or.inl ⟨hi,core_forward _ _ h⟩)
    · exact Or.inr (Or.inr ⟨hi,core_forward _ _ h⟩)
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (c.1,core c.2) (Finset.mem_filter.mp hc).2
    (a.1,core a.2) (Finset.mem_filter.mp ha).2
    (b.1,core b.2) (Finset.mem_filter.mp hb).2 (he _ _ hca) (he _ _ hcb)
  exact Prod.ext (congrArg (fun x : I × Fin 62 => x.1) hh)
    (core_injective (congrArg (fun x : I × Fin 62 => x.2) hh))

/-- Actual global upper beta bound, using the symbolic long-core score and
three disjoint attached Heawood blocks per module. -/
theorem beta_upper (e : Equiv.Perm I) :
    beta (graph e) 2≤33*Fintype.card I+Fintype.card I/2 := by
  classical
  apply Finset.sup_le
  intro S hS
  have hd := (Finset.mem_filter.mp hS).2
  have hc := LongCoreOmission.score_bound e (coreSet S) (coreSet_independent e S hd)
  have hs (i : I) : LongCoreOmission.slice (coreSet S) i=coreSlice (slice S i) := by
    ext v
    simp [LongCoreOmission.slice,coreSet,coreSlice,slice]
  have hm := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => module_credit (slice S i) (local_independent e S hd i))
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hm
  have hcard := ClosedModule.card_fibers S
  change S.card=∑ i : I, (slice S i).card at hcard
  rw [← hcard] at hm
  have hcore := ClosedModule.card_fibers (coreSet S)
  change (coreSet S).card=∑ i : I, (LongCoreOmission.slice (coreSet S) i).card at hcore
  simp_rw [hs] at hcore
  dsimp [LongCoreOmission.omissions] at hc
  simp_rw [hs] at hc
  rw [← hcore] at hm
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hm
  omega

def pattern (kind : Bool) : Finset (Fin 62) :=
  if kind then
    {0,1,4,5,8,9,12,13,16,17,18,19,21,22,24,25,27,30,33,
     34,35,36,37,41,42,46,47,49,50,52,53,55,58,61}
  else
    {1,4,6,7,8,9,10,11,14,15,20,21,22,23,27,28,32,33,
     35,36,38,39,41,44,47,48,49,50,51,55,56,60,61}

private theorem pattern_facts : ∀ kind : Bool,
    IsKIndependent localGraph 2 (pattern kind) ∧
    (pattern kind).card=(if kind then 34 else 33) := by
  intro kind
  constructor
  · apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    cases kind <;> decide +kernel
  · cases kind <;> decide +kernel

private theorem pattern_boundary : ∀ a b : Bool, ∀ v w : Fin 62,
    v∈pattern a → w∈pattern b → forward v w → a=true ∧ b=true := by
  decide +kernel

def selection (word : I → Bool) : Finset (I × Fin 62) :=
  Finset.univ.filter (fun v => v.2∈pattern (word v.1))

theorem selection_independent (e : Equiv.Perm I) (word : I → Bool)
    (hsep : ∀ i, ¬ (word i=true ∧ word (e i)=true)) :
    IsKIndependent (graph e) 2 (selection word) := by
  have internal (a b : I × Fin 62) (ha : a.2∈pattern (word a.1))
      (hb : b.2∈pattern (word b.1)) (h : (graph e).Adj a b) :
      a.1=b.1 ∧ localGraph.Adj a.2 b.2 := by
    rcases h with h | ⟨hi,h⟩ | ⟨hi,h⟩
    · exact h
    · have hh := pattern_boundary _ _ _ _ ha hb h
      exact (hsep a.1 ⟨hh.1,hi ▸ hh.2⟩).elim
    · have hh := pattern_boundary _ _ _ _ hb ha h
      exact (hsep b.1 ⟨hh.1,hi ▸ hh.2⟩).elim
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  rintro ⟨i,v⟩ hv ⟨j,a⟩ ha ⟨k,b⟩ hb hva hvb
  have hv' := (Finset.mem_filter.mp hv).2
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  obtain ⟨hij,hva'⟩ := internal (i,v) (j,a) hv' ha' hva
  obtain ⟨hik,hvb'⟩ := internal (i,v) (k,b) hv' hb' hvb
  change i=j at hij
  change i=k at hik
  subst j
  subst k
  exact Prod.ext rfl ((SubQuorum.DoubleStarGrafting.independent_iff _ _).mp
    (pattern_facts (word i)).1 v hv' a ha' b hb' hva' hvb')

/-- The exact attained dissociation value for every length, with the original
separated A/B word and actual compatible seven/eight-block selections. -/
theorem cyclic_beta (k : ℕ) : beta (graph (finRotate k)) 2=33*k+k/2 := by
  classical
  have hu := beta_upper (finRotate k)
  simp only [Fintype.card_fin] at hu
  apply le_antisymm hu
  let S := selection (I := Fin k) LongCoreOmission.cyclicWord
  have hi := selection_independent (finRotate k) LongCoreOmission.cyclicWord
    (LongCoreOmission.cyclicWord_separated k)
  have hc : S.card=33*k+k/2 := by
    rw [ClosedModule.card_fibers]
    have hf (i : Fin k) : (Finset.univ.filter (fun v => (i,v)∈S)).card=
        33+(if LongCoreOmission.cyclicWord i=true then 1 else 0) := by
      have he : (Finset.univ.filter (fun v => (i,v)∈S))=
          pattern (LongCoreOmission.cyclicWord i) := by
        ext v
        simp [S,selection]
      rw [he,(pattern_facts _).2]
      cases LongCoreOmission.cyclicWord i <;> decide
    simp_rw [hf]
    simp [Finset.sum_add_distrib,LongCoreOmission.cyclicWord_count,Nat.mul_comm]
  rw [← hc]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

def neighbors (e : Equiv.Perm I) (v : I × Fin 62) : List (I × Fin 62) :=
  (localNeighbors v.2).map (fun w => (v.1,w)) ++
    (if v.2=5 then [(e v.1,0)] else if v.2=0 then [(e.symm v.1,5)] else
     if v.2=17 then [(e v.1,12)] else if v.2=12 then [(e.symm v.1,17)] else [])

private theorem local_class :
    (∀ v w : Fin 62, localGraph.Adj v w → ClosedRingWitnesses.color v≠ClosedRingWitnesses.color w) ∧
    (∀ v : Fin 62, (localNeighbors v).Nodup) ∧
    (∀ v : Fin 62, (localNeighbors v).length=if v=0 ∨ v=5 ∨ v=12 ∨ v=17 then 2 else 3) := by
  decide +kernel

private theorem adjacency_neighbors (e : Equiv.Perm I) (v w : I × Fin 62) :
    (graph e).Adj v w ↔ w∈neighbors e v := by
  rcases v with ⟨i,v⟩
  rcases w with ⟨j,w⟩
  by_cases h5 : v=5 <;> by_cases h0 : v=0 <;>
    by_cases h17 : v=17 <;> by_cases h12 : v=12 <;>
    simp [graph,neighbors,forward,localGraph,h5,h0,h17,h12,
      Prod.mk.injEq,and_comm,and_left_comm,and_assoc,Equiv.eq_symm_apply,eq_comm]

private theorem neighbor_properties (e : Equiv.Perm I) (v : I × Fin 62) :
    (neighbors e v).Nodup ∧ (neighbors e v).length=3 := by
  rcases v with ⟨i,v⟩
  by_cases h5 : v=5
  · subst v; simp [neighbors,localNeighbors]
  by_cases h0 : v=0
  · subst v; simp [neighbors,localNeighbors]
  by_cases h17 : v=17
  · subst v; simp [neighbors,localNeighbors,ClosedModule.neighbors]
  by_cases h12 : v=12
  · subst v; simp [neighbors,localNeighbors,ClosedModule.neighbors]
  have hi : Function.Injective (fun w : Fin 62 => (i,w)) :=
    fun _ _ h => congrArg Prod.snd h
  have hn := (local_class.2.1 v).map hi
  have hl := local_class.2.2 v
  simpa [neighbors,h0,h5,h12,h17,hl] using And.intro hn hl

/-- The actual two-seam assembly is cubic, including singleton restoration. -/
theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3 := by
  classical
  intro v
  have he : Finset.univ.filter ((graph e).Adj v)=(neighbors e v).toFinset := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    exact adjacency_neighbors e v w
  change (Finset.univ.filter ((graph e).Adj v)).card=3
  rw [he,List.toFinset_card_of_nodup (neighbor_properties e v).1,(neighbor_properties e v).2]

theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => ClosedRingWitnesses.color v.2) ?_⟩
  rintro ⟨i,v⟩ ⟨j,w⟩ (⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩)
  · exact local_class.1 v w h
  all_goals
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> dsimp only <;> decide +kernel

private theorem local_forms : Regular.Forms localGraph.Adj ClosedRingWitnesses.forming := by
  unfold Regular.Forms Regular.TwoAt
  decide +kernel

private theorem local_failures : ∀ d : Fin 62, ClosedRingWitnesses.forming d →
    ¬ (ClosedRingWitnesses.forming (ClosedRingWitnesses.failure d) ∧ ClosedRingWitnesses.failure d≠d) ∧
    ¬ Regular.TwoAt localGraph.Adj (fun v => ClosedRingWitnesses.forming v ∧ v≠d)
      (ClosedRingWitnesses.failure d) := by
  unfold Regular.TwoAt
  decide +kernel

private theorem failure_boundary : ∀ d : Fin 62, ClosedRingWitnesses.forming d →
    ClosedRingWitnesses.failure d≠0 ∧ ClosedRingWitnesses.failure d≠5 := by decide +kernel

private theorem failure_centers : ∀ d v : Fin 62, ClosedRingWitnesses.forming d →
    ClosedRingWitnesses.forming v → v≠d →
    localGraph.Adj (ClosedRingWitnesses.failure d) v → v≠0 ∧ v≠5 ∧ v≠12 ∧ v≠17 := by
  decide +kernel

/-- The original actual thirty-six selection remains minimal when H also
crosses the module boundary. Its old X and block failure witnesses survive. -/
theorem forming_minimal (e : Equiv.Perm I) :
    Regular.Minimal (graph e).Adj (fun v => ClosedRingWitnesses.forming v.2) := by
  let F := ClosedRingWitnesses.forming
  let fail := ClosedRingWitnesses.failure
  apply Subcubic.minimal_of_deletion_failures
  · rintro ⟨i,v⟩ hv
    rcases local_forms v hv with ⟨a,b,ha,hb,hne,hva,hvb⟩ | ⟨c,l,hc,hl,hvc,hcl⟩
    · exact Or.inl ⟨(i,a),(i,b),ha,hb,fun h => hne (congrArg Prod.snd h),
        Or.inl ⟨rfl,hva⟩,Or.inl ⟨rfl,hvb⟩⟩
    · exact Or.inr ⟨(i,c),(i,l),hc,hl,Or.inl ⟨rfl,hvc⟩,Or.inl ⟨rfl,hcl⟩⟩
  · rintro ⟨i,d⟩ hd
    refine ⟨(i,fail d),?_,?_⟩
    · rintro ⟨hs,hn⟩
      exact (local_failures d hd).1 ⟨hs,fun he => hn (Prod.ext rfl he)⟩
    · have hneighbor (b : I × Fin 62) (hb : F b.2)
          (h : (graph e).Adj (i,fail d) b) :
          i=b.1 ∧ localGraph.Adj (fail d) b.2 := by
        rcases h with h | ⟨_,h⟩ | ⟨_,h⟩
        · exact h
        · rcases h with ⟨h5,h0⟩ | ⟨h17,h12⟩
          · exact ((failure_boundary d hd).2 h5).elim
          · exact (ClosedRingWitnesses.interface_states.1 (h12 ▸ hb)).elim
        · rcases h with ⟨h5,h0⟩ | ⟨h17,h12⟩
          · exact ((failure_boundary d hd).1 h0).elim
          · exact (ClosedRingWitnesses.interface_states.2.1 (h17 ▸ hb)).elim
      intro htwo
      apply (local_failures d hd).2
      rcases htwo with ⟨⟨j,a⟩,⟨k,b⟩,ha,hb,hn,hxa,hxb⟩ |
        ⟨⟨j,c⟩,⟨k,l⟩,hc,hl,hxc,hcl⟩
      · obtain ⟨hij,hxa⟩ := hneighbor (j,a) ha.1 hxa
        obtain ⟨hik,hxb⟩ := hneighbor (k,b) hb.1 hxb
        change i=j at hij
        change i=k at hik
        subst j
        subst k
        exact Or.inl ⟨a,b,⟨ha.1,fun he => ha.2 (Prod.ext rfl he)⟩,
          ⟨hb.1,fun he => hb.2 (Prod.ext rfl he)⟩,
          fun he => hn (Prod.ext rfl he),hxa,hxb⟩
      · obtain ⟨hij,hxc⟩ := hneighbor (j,c) hc.1 hxc
        change i=j at hij
        subst j
        have hcd : c≠d := fun he => hc.2 (Prod.ext rfl he)
        have hbd := failure_centers d c hd hc.1 hcd hxc
        have hcl' : i=k ∧ localGraph.Adj c l := by
          rcases hcl with h | ⟨_,h⟩ | ⟨_,h⟩
          · exact h
          · rcases h with ⟨h5,h0⟩ | ⟨h17,h12⟩
            · exact (hbd.2.1 h5).elim
            · exact (hbd.2.2.2 h17).elim
          · rcases h with ⟨h5,h0⟩ | ⟨h17,h12⟩
            · exact (hbd.1 h0).elim
            · exact (hbd.2.2.1 h12).elim
        obtain ⟨hik,hcl'⟩ := hcl'
        subst k
        exact Or.inr ⟨c,l,⟨hc.1,hcd⟩,⟨hl.1,fun he => hl.2 (Prod.ext rfl he)⟩,hxc,hcl'⟩

/-- Actual finite attainment supplies the all-length SF lower bound. -/
theorem sf_lower (e : Equiv.Perm I) : 36*Fintype.card I≤SF (graph e) 2 := by
  classical
  let S : Finset (I × Fin 62) := Finset.univ.filter (fun v => ClosedRingWitnesses.forming v.2)
  have hi : IsMinimalStarForming (graph e) 2 S := by
    apply (regular_minimal_iff _ _).mp
    simpa [S] using forming_minimal e
  have hc : S.card=36*Fintype.card I := by
    rw [ClosedModule.card_fibers]
    simp [S,ClosedRingWitnesses.forming_certificates.2,Nat.mul_comm]
  rw [← hc]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

end D5.S3.Combinatorics.Graph.StarForming.LongCoreRings
