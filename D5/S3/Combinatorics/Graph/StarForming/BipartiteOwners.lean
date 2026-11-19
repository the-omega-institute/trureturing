/- GID: D5/S3/Combinatorics/Graph/StarForming/BipartiteOwners
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BipartiteOwners
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual owner completion and exact one-side dissociation optimization. -/

import D5.S3.Combinatorics.Graph.StarForming.DissociationCover
import D5.S3.Combinatorics.Graph.StarForming.BipartiteBounds
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity

/-! The exact owner formula in DISSOCIATION_GAIN_IN_COVERS at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Zero-neighbor right vertices and distinct left owners of
one-neighbor right vertices are actual finite sets in the graph. -/
namespace D5.S3.Combinatorics.Graph.StarForming.BipartiteOwners
open StarFormingDissociationRefutation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (color : V → Bool)

def Owns (A : Finset V) (a r : V) : Prop :=
  color r = true ∧ G.Adj r a ∧ ∀ u ∈ A, G.Adj r u → u = a

noncomputable def owners (A : Finset V) : Finset V := by
  classical
  exact A.filter (fun a => ∃ r, Owns G color A a r)

noncomputable def zero (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun r => color r = true ∧ ∀ a ∈ A, ¬ G.Adj r a)

private theorem choose_owned (A : Finset V) (a : ↥(owners G color A)) :
    ∃ r, Owns G color A a r := by
  classical
  exact (Finset.mem_filter.mp a.property).2

private noncomputable def representative (A : Finset V) (a : ↥(owners G color A)) : V :=
  Classical.choose (choose_owned G color A a)

private theorem representative_owns (A : Finset V) (a : ↥(owners G color A)) :
    Owns G color A a (representative G color A a) :=
  Classical.choose_spec (choose_owned G color A a)

private theorem owner_mem (A : Finset V) (a : ↥(owners G color A)) : (a : V) ∈ A := by
  classical
  exact (Finset.mem_filter.mp a.property).1

private theorem representative_injective (A : Finset V) :
    Function.Injective (representative G color A) := by
  intro a b he
  have ha := representative_owns G color A a
  have hb := representative_owns G color A b
  apply Subtype.ext
  exact (ha.2.2 b (owner_mem G color A b) (he.symm ▸ hb.2.1)).symm

private noncomputable def extra (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.image (representative G color A)

noncomputable def completion (A : Finset V) : Finset V :=
  A ∪ zero G color A ∪ extra G color A

private theorem extra_color (A : Finset V) (r : V) (hr : r ∈ extra G color A) :
    color r = true := by
  classical
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
  exact (representative_owns G color A a).1

/-- For an actual left-side selection, completion chooses all zero-neighbor
right vertices and exactly one right representative for each distinct owner. -/
theorem completion_card (A : Finset V) (hA : ∀ a ∈ A, color a = false) :
    (completion G color A).card = A.card + (zero G color A).card +
      (owners G color A).card := by
  classical
  have hAZ : Disjoint A (zero G color A) := by
    apply Finset.disjoint_left.mpr
    intro a ha hz
    have hc := (Finset.mem_filter.mp hz).2.1
    simp [hA a ha] at hc
  have hAE : Disjoint A (extra G color A) := by
    apply Finset.disjoint_left.mpr
    intro a ha he
    have hc := extra_color G color A a he
    simp [hA a ha] at hc
  have hZE : Disjoint (zero G color A) (extra G color A) := by
    apply Finset.disjoint_left.mpr
    intro r hz he
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hz).2.2 a (owner_mem G color A a)
      (representative_owns G color A a).2.1
  rw [completion,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAE,hZE⟩),
    Finset.card_union_of_disjoint hAZ,extra,
    Finset.card_image_of_injective _ (representative_injective G color A)]
  simp

/-- Completion is a genuine induced-degree-at-most-one selection. -/
theorem completion_dissociation (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (A : Finset V) (hA : ∀ a ∈ A, color a = false) :
    IsKIndependent G 2 (completion G color A) := by
  classical
  have hright (r : V) (hr : r ∈ zero G color A ∪ extra G color A) : color r = true := by
    rcases Finset.mem_union.mp hr with hz | he
    · exact (Finset.mem_filter.mp hz).2.1
    · exact extra_color G color A r he
  have hsplit (v : V) (hv : v ∈ completion G color A) :
      v ∈ A ∨ v ∈ zero G color A ∪ extra G color A := by
    simpa [completion,Finset.mem_union,or_assoc] using hv
  have hleftneighbor (a : V) (ha : a ∈ A) (r : V)
      (hr : r ∈ zero G color A ∪ extra G color A) (har : G.Adj a r) :
      ∃ b : ↥(owners G color A), representative G color A b = r ∧ (b : V) = a := by
    rcases Finset.mem_union.mp hr with hz | he
    · exact ((Finset.mem_filter.mp hz).2.2 a ha (G.adj_symm har)).elim
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he
      exact ⟨b,rfl,((representative_owns G color A b).2.2 a ha (G.adj_symm har)).symm⟩
  apply (SubQuorum.DoubleStarGrafting.independent_iff G _).mpr
  intro c hc a ha b hb hca hcb
  rcases hsplit c hc with hc | hc
  · have har : a ∈ zero G color A ∪ extra G color A := by
      rcases hsplit a ha with ha | ha
      · exact (hcolor c a hca ((hA c hc).trans (hA a ha).symm)).elim
      · exact ha
    have hbr : b ∈ zero G color A ∪ extra G color A := by
      rcases hsplit b hb with hb | hb
      · exact (hcolor c b hcb ((hA c hc).trans (hA b hb).symm)).elim
      · exact hb
    obtain ⟨x,hx,hxc⟩ := hleftneighbor c hc a har hca
    obtain ⟨y,hy,hyc⟩ := hleftneighbor c hc b hbr hcb
    have he : x = y := Subtype.ext (hxc.trans hyc.symm)
    exact hx.symm.trans (he ▸ hy)
  · have hal : a ∈ A := by
      rcases hsplit a ha with ha | ha
      · exact ha
      · exact (hcolor c a hca ((hright c hc).trans (hright a ha).symm)).elim
    have hbl : b ∈ A := by
      rcases hsplit b hb with hb | hb
      · exact hb
      · exact (hcolor c b hcb ((hright c hc).trans (hright b hb).symm)).elim
    obtain ⟨x,hx,hxa⟩ := hleftneighbor a hal c hc (G.adj_symm hca)
    obtain ⟨y,hy,hyb⟩ := hleftneighbor b hbl c hc (G.adj_symm hcb)
    have he := representative_injective G color A (hx.trans hy.symm)
    exact hxa.symm.trans ((congrArg Subtype.val he).trans hyb)

/-- Restricting any actual dissociation set to its left side gives the exact
owner upper bound: distinct positive-degree right vertices need distinct owners. -/
theorem restriction_upper (D : Finset V) (hD : IsKIndependent G 2 D) :
    let A := D.filter (fun v => color v = false)
    D.card ≤ A.card + (zero G color A).card + (owners G color A).card := by
  classical
  let A := D.filter (fun v => color v = false)
  let R := D.filter (fun v => color v = true)
  let Z := R.filter (fun r => ∀ a ∈ A, ¬ G.Adj r a)
  let P := R \ Z
  have hd : D.card = A.card + R.card := by
    have h := Finset.card_filter_add_card_filter_not (s := D) (p := fun v => color v = false)
    have he : D.filter (fun v => ¬ color v = false) = R := by
      ext v; cases hc : color v <;> simp [R,hc]
    rw [he] at h
    exact h.symm
  have hz : Z ⊆ zero G color A := by
    intro r hr
    obtain ⟨hr,hn⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2,hn⟩
  have hp : ∀ r : ↥P, ∃ a : ↥(owners G color A), G.Adj r a := by
    intro r
    have hr := Finset.mem_sdiff.mp r.property
    have he : ∃ a ∈ A, G.Adj r a := by
      by_contra hn
      apply hr.2
      apply Finset.mem_filter.mpr
      exact ⟨hr.1,by simpa only [not_exists,not_and] using hn⟩
    obtain ⟨a,ha,hadj⟩ := he
    have ho : Owns G color A a r := by
      refine ⟨(Finset.mem_filter.mp hr.1).2,hadj,?_⟩
      intro b hb hrb
      exact (SubQuorum.DoubleStarGrafting.independent_iff G D).mp hD r
        (Finset.mem_filter.mp hr.1).1 b (Finset.mem_filter.mp hb).1
        a (Finset.mem_filter.mp ha).1 hrb hadj
    exact ⟨⟨a,Finset.mem_filter.mpr ⟨ha,r,ho⟩⟩,hadj⟩
  choose f hf using hp
  have hi : Function.Injective f := by
    intro r s he
    apply Subtype.ext
    have ha : (f r : V) ∈ D :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (f r).property).1).1
    have hr := (Finset.mem_filter.mp (Finset.mem_sdiff.mp r.property).1).1
    have hs := (Finset.mem_filter.mp (Finset.mem_sdiff.mp s.property).1).1
    exact (SubQuorum.DoubleStarGrafting.independent_iff G D).mp hD (f r) ha
      r hr s hs (G.adj_symm (hf r)) (he.symm ▸ G.adj_symm (hf s))
  have hc : P.card ≤ (owners G color A).card := by
    simpa using Fintype.card_le_of_injective f hi
  have hzc := Finset.card_le_card hz
  have hpz := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (s := R)
    (p := fun r => ∀ a ∈ A, ¬ G.Adj r a))
  change P.card + Z.card = R.card at hpz
  change D.card ≤ A.card + (zero G color A).card + (owners G color A).card
  omega

/-- The exact finite one-side maximum formula for every bipartite graph.
No regularity, connectedness, nonemptiness or cover assumption is needed. -/
theorem beta_formula (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) :
    beta G 2 = ((Finset.univ.filter (fun v => color v = false)).powerset.sup
      (fun A => A.card + (zero G color A).card + (owners G color A).card)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro D hD
    have h := restriction_upper G color D (Finset.mem_filter.mp hD).2
    apply h.trans
    apply Finset.le_sup (f := fun A : Finset V =>
      A.card + (zero G color A).card + (owners G color A).card)
      (b := D.filter (fun v => color v = false))
    apply Finset.mem_powerset.mpr
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · apply Finset.sup_le
    intro A hA
    have hl : ∀ a ∈ A, color a = false := by
      intro a ha
      exact (Finset.mem_filter.mp (Finset.mem_powerset.mp hA ha)).2
    rw [← completion_card G color A hl]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      completion_dissociation G color hcolor A hl⟩)

/-- Actual right-side selected-neighbor counts, keeping all four cubic degrees. -/
def rightCount (A : Finset V) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun r => color r = true ∧ DegreeCapacity.selectedDegree G A r = j)).card

/-- Signed owner surplus; subtraction here is in integers, without truncation. -/
noncomputable def surplus (A : Finset V) : ℤ :=
  (owners G color A).card - 2 * ((rightCount G color A 1 : ℤ) - (owners G color A).card) -
    rightCount G color A 2

private theorem cubic_counts (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ)
    (hN : (Finset.univ.filter (fun v => color v = true)).card = N)
    (A : Finset V) (hA : ∀ a ∈ A, color a = false) :
    rightCount G color A 0 + rightCount G color A 1 + rightCount G color A 2 +
        rightCount G color A 3 = N ∧
      rightCount G color A 1 + 2*rightCount G color A 2 + 3*rightCount G color A 3 = 3*A.card := by
  classical
  let R := Finset.univ.filter (fun v => color v = true)
  have hd (v : V) : DegreeCapacity.selectedDegree G A v ≤ 3 := by
    change (A.filter (G.Adj v)).card ≤ 3
    rw [← hr v]
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
  have hmap : ∀ v ∈ R, DegreeCapacity.selectedDegree G A v ∈ Finset.range 4 := by
    intro v _
    exact Finset.mem_range.mpr (by have := hd v; omega)
  have hcards := Finset.card_eq_sum_card_fiberwise (s := R)
    (f := DegreeCapacity.selectedDegree G A) (t := Finset.range 4) hmap
  have hsum := Finset.sum_fiberwise_of_maps_to' hmap (fun j : ℕ => j)
  have hf (j : ℕ) : (R.filter (fun v => DegreeCapacity.selectedDegree G A v = j)).card =
      rightCount G color A j := by
    congr 1
    ext v
    simp [R,rightCount,and_assoc]
  have hcut : (∑ v ∈ R, DegreeCapacity.selectedDegree G A v) = 3*A.card := by
    have he (a : V) (ha : a ∈ A) : R.filter (G.Adj a) = Finset.univ.filter (G.Adj a) := by
      ext v
      simp only [R,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · tauto
      · intro hav
        have hn := hcolor a v hav
        have hv : color v = true := by cases hc : color v <;> simp_all [hA a ha]
        exact ⟨hv,hav⟩
    have ht := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A) (t := R) G.Adj
    have hl : (∑ a ∈ A, (R.filter (G.Adj a)).card) = 3*A.card := by
      calc
        _ = ∑ a ∈ A, DegreeCapacity.degree G a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [he a ha]
          rfl
        _ = _ := by simp [hr,Nat.mul_comm]
    have ht' : (∑ a ∈ A, (R.filter (G.Adj a)).card) =
        ∑ v ∈ R, DegreeCapacity.selectedDegree G A v := by
      simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,
        DegreeCapacity.selectedDegree,G.adj_comm] using ht
    exact ht'.symm.trans hl
  simp only [Finset.sum_const,smul_eq_mul,hf] at hsum
  simp only [hf] at hcards
  have hRc : R.card = N := hN
  norm_num [Finset.sum_range_succ] at hsum hcards
  constructor <;> omega

/-- Exact cubic owner-surplus identity before taking the finite maximum. -/
theorem cubic_surplus_identity (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ)
    (hN : (Finset.univ.filter (fun v => color v = true)).card = N)
    (A : Finset V) (hA : ∀ a ∈ A, color a = false) :
    3 * ((A.card : ℤ) + (zero G color A).card + (owners G color A).card - N) =
      surplus G color A := by
  classical
  have hc := cubic_counts G color hcolor hr N hN A hA
  have hz : (zero G color A).card = rightCount G color A 0 := by
    congr 1
    ext r
    simp only [zero,rightCount,Finset.mem_filter,Finset.mem_univ,true_and,
      DegreeCapacity.selectedDegree,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  have h0 : (rightCount G color A 0 : ℤ) + rightCount G color A 1 + rightCount G color A 2 +
      rightCount G color A 3 = N := by exact_mod_cast hc.1
  have h1 : (rightCount G color A 1 : ℤ) + 2*rightCount G color A 2 +
      3*rightCount G color A 3 = 3*A.card := by exact_mod_cast hc.2
  rw [hz]
  unfold surplus
  omega

/-- A true attained maximum formulation of the signed cubic owner budget.
The optimizer is an actual left subset; every other left subset has no larger
surplus. This includes empty and disconnected cubic bipartite graphs. -/
theorem cubic_surplus_maximum (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hr : ∀ v, DegreeCapacity.degree G v = 3) (N : ℕ)
    (hN : (Finset.univ.filter (fun v => color v = true)).card = N) :
    ∃ A : Finset V, (∀ a ∈ A, color a = false) ∧
      surplus G color A = 3*((beta G 2 : ℤ)-N) ∧
      ∀ B : Finset V, (∀ b ∈ B, color b = false) → surplus G color B ≤ surplus G color A := by
  classical
  let L := Finset.univ.filter (fun v => color v = false)
  have hn : L.powerset.Nonempty := ⟨∅,Finset.empty_mem_powerset L⟩
  obtain ⟨A,hA,ha⟩ := Finset.exists_mem_eq_sup L.powerset hn
    (fun A => A.card + (zero G color A).card + (owners G color A).card)
  have hal : ∀ a ∈ A, color a = false := by
    intro a ha; exact (Finset.mem_filter.mp (Finset.mem_powerset.mp hA ha)).2
  have he : A.card + (zero G color A).card + (owners G color A).card = beta G 2 := by
    rw [beta_formula G color hcolor]
    exact ha.symm
  have hid := cubic_surplus_identity G color hcolor hr N hN A hal
  have hac : surplus G color A = 3*((beta G 2 : ℤ)-N) := by
    have hh : (A.card : ℤ) + (zero G color A).card + (owners G color A).card = beta G 2 := by
      exact_mod_cast he
    omega
  refine ⟨A,hal,hac,?_⟩
  intro B hB
  have hmem : B ∈ L.powerset := Finset.mem_powerset.mpr (by
    intro b hb; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB b hb⟩)
  have hb : B.card + (zero G color B).card + (owners G color B).card ≤ beta G 2 := by
    rw [beta_formula G color hcolor]
    exact Finset.le_sup (f := fun A : Finset V =>
      A.card + (zero G color A).card + (owners G color A).card) hmem
  have hbi := cubic_surplus_identity G color hcolor hr N hN B hB
  have hh : (B.card : ℤ) + (zero G color B).card + (owners G color B).card ≤ beta G 2 := by
    exact_mod_cast hb
  omega

end D5.S3.Combinatorics.Graph.StarForming.BipartiteOwners
