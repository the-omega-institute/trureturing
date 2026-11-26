/- GID: D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/DissociationDeficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact actual dissociation cut counts with degree deficiency. -/

import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The graph-level deficiency identity used in CUBIC_STABILITY_PORTS and
CUBIC_EQUALITY_PADDING_RINGS, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
All terms below count actual graph vertices or edges. -/
namespace D5.S3.Combinatorics.Graph.StarForming.DissociationDeficiency
open StarFormingDissociationRefutation DegreeCapacity
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def deficiency (d : ℕ) (S : Finset V) : ℕ := ∑ v ∈ S, (d-degree G v)

def complementEdges (S : Finset V) : ℕ :=
  (G.induce (↑(Finset.univ \ S) : Set V)).edgeFinset.card

private theorem deficiency_sum (d : ℕ) (hd : ∀ v, degree G v≤d) (S : Finset V) :
    deficiency G d S + ∑ v ∈ S, degree G v=d*S.card := by
  rw [deficiency,← Finset.sum_add_distrib]
  calc
    _ = ∑ _v ∈ S,d := Finset.sum_congr rfl (fun v _ => Nat.sub_add_cancel (hd v))
    _ = _ := by simp [Nat.mul_comm]

private theorem internal_degree_sum (S : Finset V) :
    (∑ v ∈ S,selectedDegree G S v)=
      2*(G.induce (↑S : Set V)).edgeFinset.card := by
  let H := G.induce (↑S : Set V)
  have hd (v : ↥(↑S : Set V)) : H.degree v=selectedDegree G S v := by
    change (H.neighborFinset v).card=(S.filter (G.Adj v)).card
    apply Finset.card_bij (fun (w : ↥(↑S : Set V)) _ => (w : V))
    · intro w hw
      exact Finset.mem_filter.mpr ⟨w.property,(H.mem_neighborFinset v w).mp hw⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w,(Finset.mem_filter.mp hw).1⟩,
        (H.mem_neighborFinset v ⟨w,(Finset.mem_filter.mp hw).1⟩).mpr
          (Finset.mem_filter.mp hw).2,rfl⟩
  have h := H.sum_degrees_eq_twice_card_edges
  simp_rw [hd] at h
  change (∑ v : ↥S, selectedDegree G S (v : V)) =
    2*(G.induce (↑S : Set V)).edgeFinset.card at h
  rw [Finset.sum_coe_sort S (fun v => selectedDegree G S v)] at h
  exact h

/-- The exact deficiency identity retains both selected isolates and every
actual complementary edge; no port credit is consumed twice. -/
theorem exact_identity (D : Finset V) (hD : IsKIndependent G 2 D)
    (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) :
    (2*d-1)*D.card + deficiency G d Finset.univ + (isolates G D).card +
      2*complementEdges G D = d*Fintype.card V + 2*deficiency G d D := by
  classical
  let T := Finset.univ \ D
  have hdc := degree_sum_cut G D
  have htc := degree_sum_cut G T
  have htt : Finset.univ \ T=D := by ext v; simp [T]
  rw [htt] at htc
  have hcut : (∑ v ∈ D,selectedDegree G T v) = ∑ v ∈ T,selectedDegree G D v := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := D) (t := T) G.Adj
    simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,selectedDegree,G.adj_comm] using h
  rw [hcut] at htc
  have hiso := selected_degree_identity G D
  have hhigh : CertificateBound.high G D=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := Finset.mem_filter.mp hv
    have hi := hD v hh.1
    omega
  rw [hhigh] at hiso
  simp only [Finset.sum_empty,Nat.add_zero] at hiso
  have hdd := deficiency_sum G d hd D
  have hdt := deficiency_sum G d hd T
  have hdu := deficiency_sum G d hd Finset.univ
  have hdeg : (∑ v : V,degree G v)=(∑ v ∈ D,degree G v)+(∑ v ∈ T,degree G v) := by
    simpa only [T,Finset.compl_eq_univ_sdiff] using (Finset.sum_add_sum_compl (s := D) (f := degree G)).symm
  have he := internal_degree_sum G T
  change (∑ v ∈ T,selectedDegree G T v)=2*complementEdges G D at he
  have hc : D.card+T.card=Fintype.card V := by
    simpa [T,Nat.add_comm] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  have hm : (2*d-1)+1=2*d := by omega
  simp only [Finset.card_univ] at hdu
  nlinarith

/-- Dropping the nonnegative isolate and complementary-edge terms gives the
general maximum-degree deficiency inequality for every dissociation set. -/
theorem deficiency_bound (D : Finset V) (hD : IsKIndependent G 2 D)
    (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) :
    (2*d-1)*D.card + deficiency G d Finset.univ ≤
      d*Fintype.card V + 2*deficiency G d D := by
  have h := exact_identity G D hD d hdpos hd
  omega

/-- If the isolate and complementary-edge terms vanish, the selected set
induces a perfect matching and every omitted vertex has all its neighbors
selected. Both conclusions concern the same actual set. -/
theorem tight_degrees (D : Finset V) (hD : IsKIndependent G 2 D)
    (hi : (isolates G D).card = 0) (he : complementEdges G D = 0) (v : V) :
    selectedDegree G D v = if v ∈ D then 1 else degree G v := by
  classical
  by_cases hv : v ∈ D
  · have hz : selectedDegree G D v ≠ 0 := by
      intro hh
      have hm : v ∈ isolates G D := Finset.mem_filter.mpr ⟨hv,hh⟩
      rw [Finset.card_eq_zero.mp hi] at hm
      exact Finset.notMem_empty _ hm
    have hh := hD v hv
    change selectedDegree G D v < 2 at hh
    simp only [if_pos hv]
    omega
  · simp only [if_neg hv]
    have hb : G.induce (↑(Finset.univ \ D) : Set V) = ⊥ :=
      SimpleGraph.edgeFinset_eq_empty.mp (Finset.card_eq_zero.mp he)
    have hall (w : V) (ha : G.Adj v w) : w ∈ D := by
      by_contra hw
      let a : ↥(↑(Finset.univ \ D) : Set V) := ⟨v,by simp [hv]⟩
      let b : ↥(↑(Finset.univ \ D) : Set V) := ⟨w,by simp [hw]⟩
      have ha' : (G.induce (↑(Finset.univ \ D) : Set V)).Adj a b := ha
      simpa only [hb, SimpleGraph.bot_adj] using ha'
    unfold selectedDegree degree
    apply congrArg Finset.card
    apply Finset.ext
    intro w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right,fun ha => ⟨hall w ha,ha⟩⟩

end D5.S3.Combinatorics.Graph.StarForming.DissociationDeficiency
