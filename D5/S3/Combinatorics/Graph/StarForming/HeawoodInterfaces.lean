/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual arbitrary-port Heawood compositions and canonical finite maxima. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicExact
import D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
import D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts
import D5.S3.Combinatorics.Graph.StarForming.DominationComparison

/-! Graph assembly of the written arbitrary-interface theorem in
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
EXACT_CUBIC_COMPOSITION, Apache-2.0. The original Fano labels, eight-set,
local failures and ambient cap are reused. A simple graph on all ports permits
same-part interfaces, restored incidences and empty/disconnected families. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodInterfaces
open StarFormingDissociationRefutation Cubic Regular
open scoped BigOperators

def port (p : Fin 2) : Fin 14 := if p = 0 then 0 else 8

private theorem port_injective : Function.Injective port := by decide +kernel
private theorem port_not_selected (p : Fin 2) : ¬ fanoSelected (port p) := by decide +kernel +revert

/-- All internal edges of the broken block, with an arbitrary simple port graph. -/
def graph {I : Type} (P : SimpleGraph (I × Fin 2)) : SimpleGraph (I × Fin 14) where
  Adj x y := (x.1 = y.1 ∧ BrokenAdj x.2 y.2) ∨
    ∃ p q, x.2 = port p ∧ y.2 = port q ∧ P.Adj (x.1,p) (y.1,q)
  symm := ⟨by
    intro x y h
    rcases h with ⟨he,hb⟩ | ⟨p,q,hp,hq,h⟩
    · exact Or.inl ⟨he.symm,(broken_simple.2 _ _).mp hb⟩
    · exact Or.inr ⟨q,p,hq,hp,P.adj_symm h⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_,hb⟩ | ⟨p,q,hp,hq,h⟩
    · exact broken_simple.1 _ hb
    · have he : p = q := port_injective (hp.symm.trans hq)
      subst q
      exact P.irrefl h⟩

noncomputable instance {I : Type} (P : SimpleGraph (I × Fin 2)) :
    DecidableRel (graph P).Adj := Classical.decRel _

private def original {I : Type} (x y : I × Fin 14) : Prop :=
  x.1 = y.1 ∧ FanoAdj x.2 y.2

private theorem edge_agreement {I : Type} (P : SimpleGraph (I × Fin 2))
    (x y : I × Fin 14) (hs : fanoSelected x.2 ∨ fanoSelected y.2) :
    original x y ↔ (graph P).Adj x y := by
  have hk : ∀ a b : Fin 14, fanoSelected a ∨ fanoSelected b →
      (FanoAdj a b ↔ BrokenAdj a b) := by
    unfold FanoAdj BrokenAdj fanoSelected brokenNeighbors fanoNeighbors
    decide +kernel
  constructor
  · rintro ⟨he,h⟩
    exact Or.inl ⟨he,(hk _ _ hs).mp h⟩
  · rintro (⟨he,h⟩ | ⟨p,q,hp,hq,_⟩)
    · exact ⟨he,(hk _ _ hs).mpr h⟩
    · rcases hs with hs | hs
      · exact (port_not_selected p (hp ▸ hs)).elim
      · exact (port_not_selected q (hq ▸ hs)).elim

private theorem original_minimal {I : Type} :
    Minimal (@original I) (fun x => fanoSelected x.2) := by
  apply Subcubic.minimal_of_deletion_failures
  · intro x hx
    rcases fano_forms x.2 hx with ⟨a,b,ha,hb,he,hxa,hxb⟩ | ⟨c,l,hc,hl,hxc,hcl⟩
    · exact Or.inl ⟨(x.1,a),(x.1,b),ha,hb,
        (fun h => he (congrArg Prod.snd h)),⟨rfl,hxa⟩,⟨rfl,hxb⟩⟩
    · exact Or.inr ⟨(x.1,c),(x.1,l),hc,hl,⟨rfl,hxc⟩,⟨rfl,hcl⟩⟩
  · intro d hd
    refine ⟨(d.1,fanoFailure d.2),?_,?_⟩
    · intro h
      exact (fano_deletion_failures d.2 hd).1 ⟨h.1,fun he => h.2 (Prod.ext rfl he)⟩
    · intro h
      apply (fano_deletion_failures d.2 hd).2
      rcases h with ⟨a,b,ha,hb,he,hxa,hxb⟩ | ⟨c,l,hc,hl,hxc,hcl⟩
      · refine Or.inl ⟨a.2,b.2,⟨ha.1,?_⟩,⟨hb.1,?_⟩,?_,hxa.2,hxb.2⟩
        · intro h; exact ha.2 (Prod.ext hxa.1.symm h)
        · intro h; exact hb.2 (Prod.ext hxb.1.symm h)
        · intro h; exact he (Prod.ext (hxa.1.symm.trans hxb.1) h)
      · refine Or.inr ⟨c.2,l.2,⟨hc.1,?_⟩,⟨hl.1,?_⟩,hxc.2,hcl.2⟩
        · intro h; exact hc.2 (Prod.ext hxc.1.symm h)
        · intro h; exact hl.2 (Prod.ext (hxc.1.trans hcl.1).symm h)

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def chosen : Finset (I × Fin 14) :=
  Finset.univ.product HeawoodParameters.selectedSet

/-- The original port-omitting eight-set stays minimal under every port graph. -/
theorem chosen_minimal (P : SimpleGraph (I × Fin 2)) :
    IsMinimalStarForming (graph P) 2 chosen := by
  classical
  apply (regular_minimal_iff _ _).mp
  have hm := minimal_rewiring_forward (@original I) (graph P).Adj
    (fun x => fanoSelected x.2) (edge_agreement P) original_minimal
  simpa [chosen,Finset.product_eq_sprod,HeawoodParameters.selectedSet] using hm

noncomputable def slice (S : Finset (I × Fin 14)) (i : I) : Finset (Fin 14) := by
  classical
  exact Finset.univ.filter (fun v => (i,v) ∈ S)

private theorem card_slices (S : Finset (I × Fin 14)) :
    S.card = ∑ i : I, (slice S i).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := Finset.univ) (by intro x _; exact Finset.mem_univ x.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun x _ => x.2)
  · intro x hx
    obtain ⟨hs,he⟩ := Finset.mem_filter.mp hx
    simp only [slice,Finset.mem_filter,Finset.mem_univ,true_and]
    exact he ▸ hs
  · intro a ha b hb he
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) he
  · intro v hv
    exact ⟨(i,v),Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,rfl⟩,rfl⟩

/-- Every ambient minimal selection uses at most eight vertices in each block;
the original nonport-neighborhood hypotheses hold for the actual assembly. -/
theorem slice_cap (P : SimpleGraph (I × Fin 2)) (S : Finset (I × Fin 14))
    (hS : IsMinimalStarForming (graph P) 2 S) (i : I) : (slice S i).card ≤ 8 := by
  classical
  obtain ⟨m,hm⟩ := FiniteMasks.selection_mask (slice S i)
  have hmem (v : Fin 14) : Cubic.chosen m.val v = true ↔ (i,v) ∈ S := by
    simpa only [Cubic.chosen,slice,Finset.mem_filter,Finset.mem_univ,true_and] using hm v
  have hc := ambient_heawood_cap (graph P).Adj (· ∈ S) (fun v => (i,v)) m
    (fun _ _ h => (graph P).adj_symm h)
    (fun _ _ he => congrArg Prod.snd he)
    (fun _ _ h => Or.inl ⟨rfl,h⟩) (fun v => (hmem v).symm)
    (by
      intro v h0 h8 y hadj
      rcases hadj with ⟨he,h⟩ | ⟨p,q,hp,hq,_⟩
      · exact ⟨y.2,Prod.ext he.symm rfl,h⟩
      · have hh : port p = 0 ∨ port p = 8 := by unfold port; split <;> simp
        rcases hh with hh | hh
        · exact (h0 (hp.trans hh)).elim
        · exact (h8 (hp.trans hh)).elim)
    ((regular_minimal_iff _ _).mpr hS)
  have he : selectedCard m.val = (slice S i).card := by
    rw [selectedCard,FiniteMasks.list_count]
    congr 1
    ext v
    simpa [slice] using hmem v
  rwa [he] at hc

/-- Exact SF for every finite simple port interface, including empty I,
restored incidences, same-part edges and disconnected interaction graphs. -/
theorem sf_graph (P : SimpleGraph (I × Fin 2)) :
    SF (graph P) 2 = 8 * Fintype.card I := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [card_slices]
    calc
      _ ≤ ∑ _i : I, 8 := Finset.sum_le_sum
        (fun i _ => slice_cap P S (Finset.mem_filter.mp hS).2 i)
      _ = _ := by simp [Nat.mul_comm]
  · have hc : (chosen : Finset (I × Fin 14)).card = 8 * Fintype.card I := by
      have hh := fano_selected_card
      rw [FiniteMasks.list_count] at hh
      simp only [chosen,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ]
      have hs : HeawoodParameters.selectedSet.card = 8 := by
        simpa [HeawoodParameters.selectedSet] using hh
      rw [hs,Nat.mul_comm]
    rw [← hc]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,chosen_minimal P⟩)

/-- The collapsed interaction relation retains restored incidences as loops. -/
def interaction (P : SimpleGraph (I × Fin 2)) (i j : I) : Prop :=
  ∃ p q, P.Adj (i,p) (j,q)

/-- Loop-aware independence: even i=j is forbidden when that block's removed
incidence has been restored. Multiple interfaces are counted only once. -/
def IndependentBlocks (P : SimpleGraph (I × Fin 2)) (A : Finset I) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ¬ interaction P i j

noncomputable def alpha0 (P : SimpleGraph (I × Fin 2)) : ℕ := by
  classical
  exact (Finset.univ.powerset.filter (IndependentBlocks P)).sup Finset.card

private theorem alpha0_attained (P : SimpleGraph (I × Fin 2)) :
    ∃ A : Finset I, IndependentBlocks P A ∧ A.card = alpha0 P := by
  classical
  have hn : (Finset.univ.powerset.filter (IndependentBlocks P)).Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨by simp,?_⟩⟩
    intro i hi
    simp at hi
  obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨A,(Finset.mem_filter.mp hA).2,he.symm⟩

private theorem slice_dissociation (P : SimpleGraph (I × Fin 2))
    (D : Finset (I × Fin 14)) (hD : IsKIndependent (graph P) 2 D) (i : I) :
    IsKIndependent HeawoodPorts.graph 2 (slice D i) := by
  classical
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
    (i,c) (by simpa [slice] using hc) (i,a) (by simpa [slice] using ha)
    (i,b) (by simpa [slice] using hb) (Or.inl ⟨rfl,hca⟩) (Or.inl ⟨rfl,hcb⟩)
  exact congrArg Prod.snd hh

private theorem dense_blocks_independent (P : SimpleGraph (I × Fin 2))
    (D : Finset (I × Fin 14)) (hD : IsKIndependent (graph P) 2 D) :
    IndependentBlocks P (Finset.univ.filter (fun i => (slice D i).card = 8)) := by
  classical
  intro i hi j hj hij
  have fi := (HeawoodPorts.facts (slice D i) (slice_dissociation P D hD i)).2
    (Finset.mem_filter.mp hi).2
  have fj := (HeawoodPorts.facts (slice D j) (slice_dissociation P D hD j)).2
    (Finset.mem_filter.mp hj).2
  rcases hij with ⟨p,q,hpq⟩
  have hip : port p ∈ slice D i := by
    fin_cases p
    · simpa [port] using fi.1
    · simpa [port] using fi.2.1
  have hjq : port q ∈ slice D j := by
    fin_cases q
    · simpa [port] using fj.1
    · simpa [port] using fj.2.1
  have hsat : DegreeCapacity.selectedDegree HeawoodPorts.graph (slice D i) (port p) = 1 := by
    fin_cases p
    · simpa [port] using fi.2.2.1
    · simpa [port] using fi.2.2.2
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 <
    ((slice D i).filter (HeawoodPorts.graph.Adj (port p))).card by
      change ((slice D i).filter (HeawoodPorts.graph.Adj (port p))).card = 1 at hsat
      omega)
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD
    (i,port p) (by simpa [slice] using hip)
    (i,a) (by simpa [slice] using (Finset.mem_filter.mp ha).1)
    (j,port q) (by simpa [slice] using hjq)
    (Or.inl ⟨rfl,(Finset.mem_filter.mp ha).2⟩)
    (Or.inr ⟨p,q,rfl,rfl,hpq⟩)
  have hn : ∀ p q : Fin 2, ¬ BrokenAdj (port p) (port q) := by
    unfold BrokenAdj port brokenNeighbors fanoNeighbors
    decide +kernel
  have he : a = port q := congrArg Prod.snd hh
  have hadj : BrokenAdj (port p) a := (Finset.mem_filter.mp ha).2
  rw [he] at hadj
  exact hn p q hadj

private theorem sum_seven_indicator (A : Finset I) :
    (∑ i : I, (7 + if i ∈ A then 1 else 0)) = 7 * Fintype.card I + A.card := by
  classical
  simp [Finset.sum_add_distrib,Nat.mul_comm]

private theorem dissociation_upper (P : SimpleGraph (I × Fin 2))
    (D : Finset (I × Fin 14)) (hD : IsKIndependent (graph P) 2 D) :
    D.card ≤ 7 * Fintype.card I + alpha0 P := by
  classical
  let A := Finset.univ.filter (fun i => (slice D i).card = 8)
  have hA : A.card ≤ alpha0 P := Finset.le_sup (Finset.mem_filter.mpr
    ⟨by simp,dense_blocks_independent P D hD⟩)
  have hc : D.card ≤ 7 * Fintype.card I + A.card := by
    rw [card_slices,← sum_seven_indicator A]
    apply Finset.sum_le_sum
    intro i _
    have hh := (HeawoodPorts.facts (slice D i) (slice_dissociation P D hD i)).1
    by_cases hi : (slice D i).card = 8 <;> simp [A,hi] <;> omega
  omega

private noncomputable def attaining (A : Finset I) : Finset (I × Fin 14) := by
  classical
  exact Finset.univ.filter (fun x => x.2 ∈
    if x.1 ∈ A then HeawoodPorts.eightSet else HeawoodPorts.sevenSet)

private theorem attaining_mem (A : Finset I) (x : I × Fin 14) :
    x ∈ attaining A ↔ x.2 ∈
      if x.1 ∈ A then HeawoodPorts.eightSet else HeawoodPorts.sevenSet := by
  classical
  simp [attaining]

private theorem attaining_port (A : Finset I) (i : I) (p : Fin 2)
    (h : (i,port p) ∈ attaining A) : i ∈ A := by
  classical
  by_contra hn
  have hh : port p ∈ HeawoodPorts.sevenSet := by simpa [attaining_mem,hn] using h
  have hz : ∀ p : Fin 2, port p ∉ HeawoodPorts.sevenSet := by decide +kernel
  exact hz p hh

private theorem attaining_dissociation (P : SimpleGraph (I × Fin 2))
    (A : Finset I) (hA : IndependentBlocks P A) :
    IsKIndependent (graph P) 2 (attaining A) := by
  classical
  have hed (x y : I × Fin 14) (hx : x ∈ attaining A) (hy : y ∈ attaining A)
      (hxy : (graph P).Adj x y) : x.1 = y.1 ∧ BrokenAdj x.2 y.2 := by
    rcases hxy with h | ⟨p,q,hp,hq,h⟩
    · exact h
    · have hxp : (x.1,port p) ∈ attaining A := by simpa [← hp] using hx
      have hyq : (y.1,port q) ∈ attaining A := by simpa [← hq] using hy
      exact (hA x.1 (attaining_port A x.1 p hxp) y.1 (attaining_port A y.1 q hyq)
        ⟨p,q,h⟩).elim
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  obtain ⟨hca0,hca1⟩ := hed c a hc ha hca
  obtain ⟨hcb0,hcb1⟩ := hed c b hc hb hcb
  have hs : IsKIndependent HeawoodPorts.graph 2
      (if c.1 ∈ A then HeawoodPorts.eightSet else HeawoodPorts.sevenSet) := by
    split
    · exact HeawoodPorts.selections.1
    · exact HeawoodPorts.selections.2.2.1
  have hh := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hs c.2
    ((attaining_mem A c).mp hc) a.2
    (by simpa only [← hca0] using (attaining_mem A a).mp ha) b.2
    (by simpa only [← hcb0] using (attaining_mem A b).mp hb) hca1 hcb1
  exact Prod.ext (hca0.symm.trans hcb0) hh

private theorem attaining_card (A : Finset I) :
    (attaining A).card = 7 * Fintype.card I + A.card := by
  classical
  rw [card_slices,← sum_seven_indicator A]
  apply Finset.sum_congr rfl
  intro i _
  have hs : slice (attaining A) i =
      if i ∈ A then HeawoodPorts.eightSet else HeawoodPorts.sevenSet := by
    ext v
    simp [slice,attaining_mem]
  rw [hs]
  by_cases hi : i ∈ A <;> simp [hi,HeawoodPorts.selections.2.1,
    HeawoodPorts.selections.2.2.2.1]

/-- Exact beta for every simple port interface, using an actual attained
loop-aware independent set and the saturated-port local proof. -/
theorem beta_graph (P : SimpleGraph (I × Fin 2)) :
    beta (graph P) 2 = 7 * Fintype.card I + alpha0 P := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro D hD
    exact dissociation_upper P D (Finset.mem_filter.mp hD).2
  · obtain ⟨A,hA,he⟩ := alpha0_attained P
    have hl : (attaining A).card ≤ beta (graph P) 2 :=
      Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,attaining_dissociation P A hA⟩)
    rwa [attaining_card,he] at hl

/-- A cover of the collapsed interaction relation must also contain the
endpoint of every restored-incidence loop. -/
def VertexCoverBlocks (P : SimpleGraph (I × Fin 2)) (C : Finset I) : Prop :=
  ∀ i j, interaction P i j → i ∈ C ∨ j ∈ C

/-- The actual finite minimum vertex-cover cardinality, with loops retained. -/
noncomputable def tau0 (P : SimpleGraph (I × Fin 2)) : ℕ :=
  sInf {n | ∃ C : Finset I, VertexCoverBlocks P C ∧ C.card = n}

private theorem cover_complement_iff (P : SimpleGraph (I × Fin 2)) (C : Finset I) :
    VertexCoverBlocks P C ↔ IndependentBlocks P (Finset.univ \ C) := by
  classical
  simp only [VertexCoverBlocks,IndependentBlocks,Finset.mem_sdiff,Finset.mem_univ,
    true_and]
  constructor
  · intro h i hi j hj hij
    exact (h i j hij).elim hi hj
  · intro h i j hij
    by_contra hn
    exact h i (not_or.mp hn).1 j (not_or.mp hn).2 hij

/-- Complementation gives the exact loop-aware independent/cover duality. -/
theorem alpha0_add_tau0 (P : SimpleGraph (I × Fin 2)) :
    alpha0 P + tau0 P = Fintype.card I := by
  classical
  have hall : VertexCoverBlocks P (Finset.univ : Finset I) := by
    intro i j _; exact Or.inl (Finset.mem_univ i)
  obtain ⟨C,hC,hc⟩ := Nat.sInf_mem
    (show {n | ∃ C : Finset I, VertexCoverBlocks P C ∧ C.card = n}.Nonempty from
      ⟨_,Finset.univ,hall,rfl⟩)
  obtain ⟨A,hA,ha⟩ := alpha0_attained P
  have hcover : VertexCoverBlocks P (Finset.univ \ A) := by
    apply (cover_complement_iff P _).mpr
    simpa using hA
  have ht : tau0 P ≤ (Finset.univ \ A).card := Nat.sInf_le ⟨_,hcover,rfl⟩
  have hi : (Finset.univ \ C).card ≤ alpha0 P :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,(cover_complement_iff P C).mp hC⟩)
  have hca := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hcc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  simp only [Finset.card_univ] at hca hcc
  change C.card = tau0 P at hc
  omega

/-- The actual star-forming gap is exactly the loop-aware vertex-cover number. -/
theorem gap_eq_tau0 (P : SimpleGraph (I × Fin 2)) :
    SF (graph P) 2 - beta (graph P) 2 = tau0 P := by
  have h := alpha0_add_tau0 P
  rw [sf_graph,beta_graph]
  omega

/-- Equality holds precisely for an interface having no edges, including no
restored incidence. The statement is valid for the empty block type. -/
theorem sf_eq_beta_iff (P : SimpleGraph (I × Fin 2)) :
    SF (graph P) 2 = beta (graph P) 2 ↔ P = ⊥ := by
  classical
  constructor
  · intro he
    have ha : alpha0 P = Fintype.card I := by
      rw [sf_graph,beta_graph] at he; omega
    obtain ⟨A,hA,hc⟩ := alpha0_attained P
    have hfull : A = Finset.univ := Finset.eq_univ_of_card A (hc.trans ha)
    ext x y
    simp only [SimpleGraph.bot_adj,iff_false]
    intro hxy
    exact hA x.1 (by simp [hfull]) y.1 (by simp [hfull]) ⟨x.2,y.2,hxy⟩
  · rintro rfl
    have hi : IndependentBlocks (⊥ : SimpleGraph (I × Fin 2)) Finset.univ := by
      simp [IndependentBlocks,interaction]
    have hl : Fintype.card I ≤ alpha0 (⊥ : SimpleGraph (I × Fin 2)) := by
      unfold alpha0
      simpa only [Finset.card_univ] using
        Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨by simp,hi⟩)
    have ht := alpha0_add_tau0 (⊥ : SimpleGraph (I × Fin 2))
    rw [sf_graph,beta_graph]
    omega

/-- Interfaces joining opposite port types preserve the displayed Fano
bipartition. Arbitrary same-part interfaces require no such assertion. -/
theorem bipartite (P : SimpleGraph (I × Fin 2))
    (hP : ∀ i j p q, P.Adj (i,p) (j,q) → p ≠ q) :
    (graph P).Colorable 2 := by
  let c : I × Fin 14 → Fin 2 := fun x => if x.2.val < 7 then 0 else 1
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro x y h
  rcases h with ⟨_,hb⟩ | ⟨p,q,hp,hq,hpq⟩
  · have hl : ∀ a b : Fin 14, BrokenAdj a b →
        (if a.val < 7 then (0 : Fin 2) else 1) ≠
        (if b.val < 7 then (0 : Fin 2) else 1) := by
      unfold BrokenAdj brokenNeighbors
      decide +kernel
    exact hl _ _ hb
  · have hn := hP _ _ _ _ hpq
    fin_cases p <;> fin_cases q <;> simp_all [c,port]

end D5.S3.Combinatorics.Graph.StarForming.HeawoodInterfaces
