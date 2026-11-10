/- GID: D5/S3/Combinatorics/Graph/StarForming/DominationComparison
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/DominationComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual upper domination and independence in finite bipartite graphs. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! The classical bipartite upper-domination identity, with the direct
private-neighbor proof written in REGULAR_STAR_FORMING_BOUND at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Alpha is Mathlib's actual independence number. Gamma below is
the actual maximum over inclusion-minimal dominating finite selections;
it is not the star-forming or sub-quorum parameter. -/
namespace D5.S3.Combinatorics.Graph.StarForming.DominationComparison
open StarFormingDissociationRefutation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Closed-neighborhood domination, including domination of selected vertices
by themselves. -/
def Dominates (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

def MinimalDominating (D : Finset V) : Prop :=
  Dominates G D ∧ ∀ E : Finset V, E ⊂ D → ¬ Dominates G E

noncomputable def Gamma : ℕ := by
  classical
  exact (Finset.univ.powerset.filter (MinimalDominating G)).sup Finset.card

private theorem minimal_private (D : Finset V) (hD : MinimalDominating G D)
    (v : V) (hv : v ∈ D) (hn : ∃ w ∈ D, G.Adj v w) :
    ∃ x, x ∉ D ∧ G.Adj x v ∧ ∀ w ∈ D, G.Adj x w → w = v := by
  classical
  have hf : ¬ Dominates G (D.erase v) := hD.2 _ (Finset.erase_ssubset hv)
  have hx : ∃ x, x ∉ D.erase v ∧ ∀ w ∈ D.erase v, ¬ G.Adj x w := by
    simpa only [Dominates,not_forall,not_or,not_exists,not_and] using hf
  obtain ⟨x,hx,hxe⟩ := hx
  have ho : x ∉ D := by
    intro hxd
    have he : x = v := by
      by_contra hne
      exact hx (Finset.mem_erase.mpr ⟨hne,hxd⟩)
    obtain ⟨w,hw,hvw⟩ := hn
    exact hxe w (Finset.mem_erase.mpr ⟨G.ne_of_adj hvw |>.symm,hw⟩) (he.symm ▸ hvw)
  obtain hxd | ⟨w,hw,hxw⟩ := hD.1 x
  · exact (ho hxd).elim
  · have he : w = v := by
      by_contra hne
      exact hxe w (Finset.mem_erase.mpr ⟨hne,hw⟩) hxw
    refine ⟨x,ho,he ▸ hxw,?_⟩
    intro u hu hxu
    by_contra hne
    exact hxe u (Finset.mem_erase.mpr ⟨hne,hu⟩) hxu

private def iso (D : Finset V) : Finset V :=
  D.filter (fun v => ∀ w ∈ D, ¬ G.Adj v w)

/-- Every actual minimal dominating set in a bipartite graph has an
independent selection of exactly the same cardinality. -/
theorem minimal_dominating_exchange (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (D : Finset V) (hD : MinimalDominating G D) :
    ∃ J : Finset V, G.IsIndepSet (J : Set V) ∧ J.card = D.card := by
  classical
  let I := iso G D
  let H := D \ I
  have hiso (v : V) (hv : v ∈ I) : ∀ w ∈ D, ¬ G.Adj v w :=
    (Finset.mem_filter.mp hv).2
  have hex (v : ↥H) : ∃ x, x ∉ D ∧ G.Adj x v ∧
      ∀ w ∈ D, G.Adj x w → w = v := by
    have hd := Finset.mem_sdiff.mp v.property
    apply minimal_private G D hD v hd.1
    by_contra hn
    apply hd.2
    exact Finset.mem_filter.mpr ⟨hd.1,by simpa only [not_exists,not_and] using hn⟩
  choose p hp using hex
  let f : V → V := fun v => if h : v ∈ H ∧ color v = true then p ⟨v,h.1⟩ else v
  have hmap (v : V) (hv : v ∈ D) : f v = v ∨
      (v ∉ I ∧ color v = true ∧ f v ∉ D ∧ G.Adj (f v) v ∧
        ∀ w ∈ D, G.Adj (f v) w → w = v) := by
    by_cases hh : v ∈ H ∧ color v = true
    · right
      have hpv := hp (⟨v,hh.1⟩ : ↥H)
      exact ⟨(Finset.mem_sdiff.mp hh.1).2,hh.2,by simpa [f,hh] using hpv.1,
        by simpa [f,hh] using hpv.2.1,by simpa [f,hh] using hpv.2.2⟩
    · left; simp [f,hh]
  have hfix (v : V) (hv : v ∈ I) : f v = v := by
    have hn : v ∉ H := fun h => (Finset.mem_sdiff.mp h).2 hv
    simp [f,hn]
  have hside (v : V) (hv : v ∈ D) (hi : v ∉ I) : color (f v) = false := by
    by_cases hc : color v = true
    · have hh : v ∈ H ∧ color v = true := ⟨Finset.mem_sdiff.mpr ⟨hv,hi⟩,hc⟩
      have hpv := hp (⟨v,hh.1⟩ : ↥H)
      have hn := hcolor (p ⟨v,hh.1⟩) v hpv.2.1
      have he : color (p ⟨v,hh.1⟩) = false := by
        cases he : color (p ⟨v,hh.1⟩) with
        | false => rfl
        | true => exact (hn (he.trans hc.symm)).elim
      simpa only [f,dif_pos hh] using he
    · have hh : ¬ (v ∈ H ∧ color v = true) := by tauto
      have he : color v = false := by
        cases he : color v with
        | false => rfl
        | true => exact (hc he).elim
      simpa only [f,dif_neg hh] using he
  have havoid (v : V) (hv : v ∈ D) (w : V) (hw : w ∈ I) : ¬ G.Adj (f v) w := by
    rcases hmap v hv with hf | ⟨hi,_,_,_,hpv⟩
    · rw [hf]
      exact fun h => hiso w hw v hv (G.adj_symm h)
    · intro h
      exact hi ((hpv w (Finset.mem_filter.mp hw).1 h) ▸ hw)
  have hinj : Set.InjOn f (D : Set V) := by
    intro v hv w hw he
    rcases hmap v hv with hf | ⟨_,_,ho,ha,hp⟩
    · rcases hmap w hw with hg | ⟨_,_,hwo,_,_⟩
      · simpa only [hf,hg] using he
      · exact (hwo (by rw [← he,hf]; exact hv)).elim
    · rcases hmap w hw with hg | ⟨_,_,_,hwa,_⟩
      · exact (ho (by rw [he,hg]; exact hw)).elim
      · exact (hp w hw (he.symm ▸ hwa)).symm
  refine ⟨D.image f,?_,Finset.card_image_iff.mpr hinj⟩
  intro a ha b hb hab hadj
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
  by_cases hvi : v ∈ I
  · rw [hfix v hvi] at hadj
    exact havoid w hw v hvi (G.adj_symm hadj)
  · by_cases hwi : w ∈ I
    · rw [hfix w hwi] at hadj
      exact havoid v hv w hwi hadj
    · exact hcolor _ _ hadj ((hside v hv hvi).trans (hside w hw hwi).symm)

private theorem maximum_independent_minimal (J : Finset V) (hJ : G.IsMaximumIndepSet J) :
    MinimalDominating G J := by
  classical
  have hdom : Dominates G J := by
    intro v
    by_cases hv : v ∈ J
    · exact Or.inl hv
    · right
      by_contra hn
      have hi : G.IsIndepSet ((insert v J : Finset V) : Set V) := by
        intro a ha b hb hab hadj
        simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact G.irrefl hadj
        · exact hn ⟨b,hb,hadj⟩
        · exact hn ⟨a,ha,G.adj_symm hadj⟩
        · exact hJ.isIndepSet ha hb hab hadj
      have hc := hJ.maximum _ hi
      rw [Finset.card_insert_of_notMem hv] at hc
      omega
  refine ⟨hdom,?_⟩
  intro E hE hdomE
  obtain ⟨v,hv,hve⟩ := Finset.exists_of_ssubset hE
  rcases hdomE v with he | ⟨w,hw,hadj⟩
  · exact hve he
  · have hwJ := hE.1 hw
    by_cases he : v = w
    · exact hve (he.symm ▸ hw)
    · exact hJ.isIndepSet hv hwJ he hadj

/-- Classical upper domination equals actual independence in every finite
bipartite graph, including empty and disconnected graphs. -/
theorem gamma_eq_alpha (hG : G.Colorable 2) : Gamma G = G.indepNum := by
  classical
  obtain ⟨color⟩ := hG
  let c : V → Bool := fun v => decide (color v = 1)
  have hc : ∀ v w, G.Adj v w → c v ≠ c w := by
    intro v w h he
    have hn := color.valid h
    have hvr : color v = 0 ∨ color v = 1 := by omega
    have hwr : color w = 0 ∨ color w = 1 := by omega
    rcases hvr with hv | hv <;> rcases hwr with hw | hw <;> simp_all [c]
  apply le_antisymm
  · apply Finset.sup_le
    intro D hD
    obtain ⟨J,hJ,he⟩ := minimal_dominating_exchange G c hc D (Finset.mem_filter.mp hD).2
    rw [← he]
    exact hJ.card_le_indepNum
  · obtain ⟨J,hJ⟩ := G.maximumIndepSet_exists
    rw [← G.maximumIndepSet_card_eq_indepNum J hJ]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,maximum_independent_minimal G J hJ⟩)

/-- Independence and dissociation are distinct actual finite maxima. -/
theorem alpha_le_beta : G.indepNum ≤ beta G 2 := by
  classical
  obtain ⟨J,hJ⟩ := G.maximumIndepSet_exists
  rw [← G.maximumIndepSet_card_eq_indepNum J hJ]
  apply Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,?_⟩)
  intro v hv
  have he : J.filter (G.Adj v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw h
    exact hJ.isIndepSet hv hw (G.ne_of_adj h) h
  rw [he]
  simp

private theorem independent_selected_zero (J : Finset V) (hJ : G.IsIndepSet (J : Set V))
    (v : V) (hv : v ∈ J) : DegreeCapacity.selectedDegree G J v = 0 := by
  have he : J.filter (G.Adj v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw h
    exact hJ hv hw (G.ne_of_adj h) h
  simp [DegreeCapacity.selectedDegree,he]

/-- Positive-regular bipartite graphs have their actual independence number
at half the order. The proof counts the cut of a maximum independent set;
no unproved perfect-matching or balance assumption is supplied. -/
theorem regular_alpha_card (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d)
    (hregular : ∀ v, DegreeCapacity.degree G v = d) :
    2 * G.indepNum = Fintype.card V := by
  classical
  have hu : 2 * G.indepNum ≤ Fintype.card V := by
    obtain ⟨J,hJ⟩ := G.maximumIndepSet_exists
    have hc := DegreeCapacity.degree_sum_cut G J
    have hz : (∑ v ∈ J, DegreeCapacity.selectedDegree G J v) = 0 :=
      Finset.sum_eq_zero (fun v hv => independent_selected_zero G J hJ.isIndepSet v hv)
    rw [hz,zero_add] at hc
    have hl : (∑ v ∈ J, DegreeCapacity.degree G v) = d * J.card := by
      simp [hregular,Nat.mul_comm]
    have hr : (∑ v ∈ Finset.univ \ J, DegreeCapacity.selectedDegree G J v) ≤
        d * (Finset.univ \ J).card := by
      calc
        _ ≤ ∑ v ∈ Finset.univ \ J, DegreeCapacity.degree G v := by
          apply Finset.sum_le_sum
          intro v _
          exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))
        _ = _ := by simp [hregular,Nat.mul_comm]
    rw [hl] at hc
    have ht := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    rw [Finset.card_univ] at ht
    have hj := G.maximumIndepSet_card_eq_indepNum J hJ
    rw [hj] at hc ht
    nlinarith
  obtain ⟨c⟩ := hG
  let L := Finset.univ.filter (fun v => c v = (0 : Fin 2))
  let R := Finset.univ.filter (fun v => c v = (1 : Fin 2))
  have hi (i : Fin 2) : G.IsIndepSet ((Finset.univ.filter (fun v => c v = i) : Finset V) : Set V) := by
    intro v hv w hw _ h
    exact c.valid h ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
  have hL : L.card ≤ G.indepNum := (hi 0).card_le_indepNum
  have hR : R.card ≤ G.indepNum := (hi 1).card_le_indepNum
  have he : L ∪ R = Finset.univ := by
    ext v
    have hh : c v = 0 ∨ c v = 1 := by omega
    simp [L,R,hh]
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h0 := (Finset.mem_filter.mp hv).2
    have h1 := (Finset.mem_filter.mp hw).2
    have hh : (0 : Fin 2) = 1 := h0.symm.trans h1
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  have hh := Finset.card_union_of_disjoint hdis
  rw [he,Finset.card_univ] at hh
  omega

end D5.S3.Combinatorics.Graph.StarForming.DominationComparison
