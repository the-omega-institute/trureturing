/- GID: D5/S3/Combinatorics/Graph/StarForming/WitnessBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/WitnessBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual injective high-witness payments and exact regular unused capacity. -/

import D5.S3.Combinatorics.Graph.StarForming.BipartiteExchange

/-! The exact witness budget in HEAWOOD_BLOCK_COMPENSATION and the regular
equality notes, subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. Payments below use the actual deletion witnesses. They are not
free numerical variables or assumed local credits. No bipartiteness is
needed for this general regular-graph budget. -/

namespace D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
open StarFormingDissociationRefutation DegreeCapacity
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S : Finset V) (hS : IsMinimalStarForming G 2 S)

noncomputable def payment (x : V) : ℕ := by
  classical
  exact ∑ v ∈ (CertificateBound.high G S).filter
    (fun v => BipartiteExchange.witness G S hS v=x), (selectedDegree G S v-1)

noncomputable def unused (d : ℕ) (x : V) : ℕ :=
  (d-selectedDegree G S x)-payment G S hS x

private theorem high_iff (v : V) :
    v ∈ CertificateBound.high G S ↔ Regular.High G.Adj (· ∈ S) v := by
  constructor
  · intro hv
    obtain ⟨hv,hd⟩ := Finset.mem_filter.mp hv
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega :
      1 < (S.filter (G.Adj v)).card)
    exact ⟨hv,a,b,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1,
      hab,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
  · rintro ⟨hv,a,b,ha,hb,hab,hva,hvb⟩
    refine Finset.mem_filter.mpr ⟨hv,?_⟩
    have hc := Finset.card_le_card (show ({a,b} : Finset V) ⊆ S.filter (G.Adj v) by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨ha,hva⟩
      · exact Finset.mem_filter.mpr ⟨hb,hvb⟩)
    simpa only [Finset.card_pair hab] using hc

private theorem witness_outside (v : V) (hv : v ∈ CertificateBound.high G S) :
    BipartiteExchange.witness G S hS v ∈ Finset.univ \ S := by
  have hf := BipartiteExchange.witness_failure G S hS v ((high_iff G S v).mp hv)
  simpa using hf.1

/-- An actual resource receives at most one high vertex's demand, which is
bounded by its unused selected-degree capacity. -/
theorem payment_le_capacity (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) :
    payment G S hS x ≤ d-selectedDegree G S x := by
  classical
  by_cases he : ∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x
  · obtain ⟨v,hv,hvx⟩ := he
    have hf : (CertificateBound.high G S).filter
        (fun w => BipartiteExchange.witness G S hS w=x) = {v} := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,hwx⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_singleton.mpr (BipartiteExchange.witness_injective G S hS w v
          ((high_iff G S w).mp hw) ((high_iff G S v).mp hv) (hwx.trans hvx.symm))
      · intro hw
        have he := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_filter.mpr ⟨hv,hvx⟩
    have hc := witness_degree_capacity G S d hdegree v x (by
      rw [← hvx]
      exact BipartiteExchange.witness_failure G S hS v ((high_iff G S v).mp hv))
    have hh : 2 ≤ selectedDegree G S v := (Finset.mem_filter.mp hv).2
    simp only [payment,hf,Finset.sum_singleton]
    omega
  · have hf : (CertificateBound.high G S).filter
        (fun w => BipartiteExchange.witness G S hS w=x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hv,hvx⟩ := Finset.mem_filter.mp hv
      exact he ⟨v,hv,hvx⟩
    simp only [payment,hf,Finset.sum_empty,Nat.zero_le]

/-- Summation charges the actual high demand exactly once, on its actual
outside witness. No local block ownership is presumed by this identity. -/
theorem payment_sum :
    ∑ x ∈ Finset.univ \ S, payment G S hS x =
      ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v-1) := by
  classical
  simp only [payment,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_eq_single (BipartiteExchange.witness G S hS v)]
  · simp
  · intro x hx hxv
    simp [Ne.symm hxv]
  · intro hn
    exact (hn (witness_outside G S hS v hv)).elim

/-- Payment plus the nonnegative residual exhausts each actual resource. -/
theorem payment_add_unused (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) :
    payment G S hS x + unused G S hS d x = d-selectedDegree G S x := by
  exact Nat.add_sub_of_le (payment_le_capacity G S hS d hdegree x)

/-- The complete exact regular budget, including selected isolates and the
sum of actual pointwise residual capacity. It applies in every degree at
least one and in graphs with triangles. -/
theorem regular_budget (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) :
    (2*d-1)*S.card + (isolates G S).card +
      (∑ x ∈ Finset.univ \ S, unused G S hS d x) = d*Fintype.card V := by
  classical
  have hid := selected_degree_identity G S
  have hcut := degree_sum_cut G S
  have hpay := payment_sum G S hS
  have hpaid : (∑ x ∈ Finset.univ \ S, payment G S hS x) +
      (∑ x ∈ Finset.univ \ S, unused G S hS d x) =
      ∑ x ∈ Finset.univ \ S, (d-selectedDegree G S x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    exact fun x _ => payment_add_unused G S hS d (fun v => (hdegree v).le) x
  have htotal : (∑ x ∈ Finset.univ \ S, (d-selectedDegree G S x)) +
      (∑ x ∈ Finset.univ \ S, selectedDegree G S x) = d*(Finset.univ \ S).card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x ∈ Finset.univ \ S, d := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Nat.sub_add_cancel ((Finset.card_le_card
          (Finset.filter_subset_filter (G.Adj x) (Finset.subset_univ S))).trans
            (hdegree x).le)
      _ = _ := by simp [Nat.mul_comm]
  have hsum : (∑ v ∈ S, degree G v)=d*S.card := by simp [hdegree,Nat.mul_comm]
  have hcard : (Finset.univ \ S).card+S.card=Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have ht : (2*d-1)+1=2*d := by omega
  rw [hsum] at hcut
  nlinarith

/-- At a chosen witness the actual payment is exactly its unique owner's demand. -/
theorem payment_at_witness (v : V) (hv : v ∈ CertificateBound.high G S) :
    payment G S hS (BipartiteExchange.witness G S hS v) = selectedDegree G S v-1 := by
  classical
  have hf : (CertificateBound.high G S).filter
      (fun w => BipartiteExchange.witness G S hS w=BipartiteExchange.witness G S hS v) = {v} := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hw,he⟩
      exact BipartiteExchange.witness_injective G S hS w v
        ((high_iff G S w).mp hw) ((high_iff G S v).mp hv) he
    · rintro rfl
      exact ⟨hv,rfl⟩
  simp only [payment,hf,Finset.sum_singleton]

/-- A resource outside the actual witness image receives no payment. -/
theorem payment_off_image (x : V)
    (hx : ¬ ∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) :
    payment G S hS x=0 := by
  classical
  apply Finset.sum_eq_zero
  intro v hv
  exact (hx ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩).elim

/-- Equality of regular capacity is exactly pointwise exhaustion of all actual
outside resources. No positive capacity can cancel another one. -/
theorem tight_iff_pointwise (d : ℕ) (hd : 1 ≤ d)
    (hdegree : ∀ v, degree G v=d) :
    (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V ↔
      ∀ x ∈ Finset.univ \ S, unused G S hS d x=0 := by
  have hb := regular_budget G S hS d hd hdegree
  constructor
  · intro ht
    have hz : (∑ x ∈ Finset.univ \ S, unused G S hS d x)=0 := by omega
    exact Finset.sum_eq_zero_iff.mp hz
  · intro ht
    have hz : (∑ x ∈ Finset.univ \ S, unused G S hS d x)=0 := Finset.sum_eq_zero ht
    omega

/-- Under exact capacity equality, the outside classes are precisely the
chosen witness image and full-selected-degree unused vertices. -/
theorem tight_outside_classes (d : ℕ) (hd : 1 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) :
    (∀ v ∈ CertificateBound.high G S,
      selectedDegree G S v+selectedDegree G S (BipartiteExchange.witness G S hS v)=d+1) ∧
    (∀ x ∈ Finset.univ \ S,
      (∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) ∨
        selectedDegree G S x=d) := by
  have hz := (tight_iff_pointwise G S hS d hd hdegree).mp ht
  have hmax (x : V) : selectedDegree G S x ≤ d :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans
      (hdegree x).le
  constructor
  · intro v hv
    have hp := payment_add_unused G S hS d (fun v => (hdegree v).le)
      (BipartiteExchange.witness G S hS v)
    rw [payment_at_witness G S hS v hv,
      hz _ (witness_outside G S hS v hv)] at hp
    have hh := (Finset.mem_filter.mp hv).2
    change 2 ≤ selectedDegree G S v at hh
    have hm := hmax (BipartiteExchange.witness G S hS v)
    omega
  · intro x hx
    by_cases he : ∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x
    · exact Or.inl he
    · right
      have hp := payment_add_unused G S hS d (fun v => (hdegree v).le) x
      rw [payment_off_image G S hS x he,hz x hx] at hp
      have hm := hmax x
      omega

/-- Actual tight high vertices have selected degree d-1 with an adjacent
two-neighbor witness, or degree d with a nonadjacent one-neighbor witness.
This includes triangles and does not claim the further leaf bijections. -/
theorem tight_witness_classes (d : ℕ) (hd : 1 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S) :
    let x := BipartiteExchange.witness G S hS v
    (selectedDegree G S v=d-1 ∧ selectedDegree G S x=2 ∧ G.Adj x v) ∨
    (selectedDegree G S v=d ∧ selectedDegree G S x=1 ∧ ¬ G.Adj x v) := by
  classical
  let x := BipartiteExchange.witness G S hS v
  have hf := BipartiteExchange.witness_failure G S hS v ((high_iff G S v).mp hv)
  have he := (tight_outside_classes G S hS d hd hdegree ht).1 v hv
  change selectedDegree G S v + selectedDegree G S x = d+1 at he
  have hx := failure_selected_degree_le_two G S v x hf
  by_cases ha : G.Adj x v
  · have hc := adjacent_failure_degree G S d (fun v => (hdegree v).le) v x hf ha
    left
    change selectedDegree G S v=d-1 ∧ selectedDegree G S x=2 ∧ G.Adj x v
    exact ⟨by omega,by omega,ha⟩
  · have hc : selectedDegree G S x ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha' b hb'
      exact Regular.nonadjacent_witness_unique_neighbor G.Adj (· ∈ S) v x a b hf ha
        (Finset.mem_filter.mp ha').1 (Finset.mem_filter.mp hb').1
        (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb').2
    have hm : selectedDegree G S v ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans
        (hdegree v).le
    right
    change selectedDegree G S v=d ∧ selectedDegree G S x=1 ∧ ¬ G.Adj x v
    exact ⟨by omega,by omega,ha⟩

/-- Tight capacity leaves no unreserved leaf: its actual failure would be a
positive-capacity outside resource disjoint from the high-witness image. -/
theorem tight_no_extra (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (u : V) : ¬ BipartiteExchange.Extra G S hS u := by
  classical
  intro hu
  let x := BipartiteExchange.activeWitness G S hS u
  have hf := BipartiteExchange.active_failure G S hS u (Or.inr hu)
  have hx : x ∈ Finset.univ \ S := by simpa using hf.1
  rcases (tight_outside_classes G S hS d (by omega) hdegree ht).2 x hx with he | he
  · obtain ⟨v,hv,hvx⟩ := he
    have hh := (high_iff G S v).mp hv
    have hw : BipartiteExchange.activeWitness G S hS v = x := by
      simpa only [BipartiteExchange.activeWitness,dif_pos hh] using hvx
    have huv := BipartiteExchange.activeWitness_injective G S color hcolor hS u v
      (Or.inr hu) (Or.inl hh) hw.symm
    obtain ⟨h,hl⟩ := hu.1
    exact BipartiteExchange.leaf_not_high G S u h hl (huv.symm ▸ hh)
  · have hc := failure_selected_degree_le_two G S u x hf
    omega

/-- Every selected leaf is paired to a nonadjacent chosen high witness under
tight regular capacity. This is used for the actual leaf bijections. -/
theorem tight_leaf_reserved (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (u h : V) (hu : BipartiteExchange.LeafAt G S u h) :
    BipartiteExchange.Reserved G S hS u := by
  by_contra hn
  exact tight_no_extra G S hS color hcolor d hd hdegree ht u ⟨⟨h,hu⟩,hn⟩

/-- A high vertex incident to a selected leaf has full selected degree. -/
theorem tight_leaf_full (hS : IsMinimalStarForming G 2 S) (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (u h : V) (hu : BipartiteExchange.LeafAt G S u h) :
    selectedDegree G S h=d := by
  obtain ⟨k,huk,hn,ha⟩ := BipartiteExchange.reserved_leaf G S hS u
    (tight_leaf_reserved G S hS color hcolor d hd hdegree ht u h hu)
  have he := BipartiteExchange.leaf_support_unique G S u k h huk hu
  subst k
  rcases tight_witness_classes G S hS d (by omega) hdegree ht h
    ((high_iff G S h).mpr hu.2.1) with hc | hc
  · exact (hn hc.2.2).elim
  · exact hc.1

/-- Every full-degree high vertex has exactly one selected leaf. Together
with tight_leaf_full this gives the C--U bijection of the source partition. -/
theorem tight_full_unique_leaf (hS : IsMinimalStarForming G 2 S) (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S)
    (hfull : selectedDegree G S v=d) :
    ∃! u, BipartiteExchange.LeafAt G S u v := by
  have hh := (high_iff G S v).mp hv
  have hn : ¬ G.Adj (BipartiteExchange.witness G S hS v) v := by
    rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
    · omega
    · exact hc.2.2
  obtain ⟨u,hu,hxu,hunique⟩ := BipartiteExchange.nonadjacent_leaf G S hS v
    (BipartiteExchange.witness G S hS v) hh
    (BipartiteExchange.witness_failure G S hS v hh) hn
  refine ⟨u,hu,?_⟩
  intro w hw
  obtain ⟨k,hwk,hnk,hxw⟩ := BipartiteExchange.reserved_leaf G S hS w
    (tight_leaf_reserved G S hS color hcolor d hd hdegree ht w v hw)
  have he := BipartiteExchange.leaf_support_unique G S w k v hwk hw
  subst k
  exact hunique w hw.1 hxw

private theorem nonhigh_neighbor_leaf (u h : V) (hu : u ∈ S)
    (hh : Regular.High G.Adj (· ∈ S) h) (hn : ¬ Regular.High G.Adj (· ∈ S) u)
    (huh : G.Adj u h) : BipartiteExchange.LeafAt G S u h := by
  exact ⟨hu,hh,huh,fun w hw huw =>
    BipartiteExchange.nonhigh_unique G S u w h hu hn hw hh.1 huw huh⟩

/-- The actual selected high graph in every isolate-tight regular bipartite
graph is (d-1)-regular, in all degrees d>=3. Full highs lose precisely their
unique selected leaf; degree-(d-1) highs have no selected leaf. -/
theorem tight_high_regular (hS : IsMinimalStarForming G 2 S) (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S) :
    selectedDegree G (CertificateBound.high G S) v=d-1 := by
  classical
  have hh := (high_iff G S v).mp hv
  rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
  · have he : (CertificateBound.high G S).filter (G.Adj v)=S.filter (G.Adj v) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy,ha⟩
        exact ⟨(Finset.mem_filter.mp hy).1,ha⟩
      · rintro ⟨hy,ha⟩
        refine ⟨(high_iff G S y).mpr ?_,ha⟩
        by_contra hn
        have hl := nonhigh_neighbor_leaf G S y v hy hh hn (G.adj_symm ha)
        have hf := tight_leaf_full G S hS color hcolor d hd hdegree ht y v hl
        omega
    change ((CertificateBound.high G S).filter (G.Adj v)).card=d-1
    rw [he]
    exact hc.1
  · obtain ⟨u,hu,hunique⟩ := tight_full_unique_leaf G S hS color hcolor d hd hdegree ht v hv hc.1
    have hum : u ∈ S.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hu.1,G.adj_symm hu.2.2.1⟩
    have he : (CertificateBound.high G S).filter (G.Adj v)=(S.filter (G.Adj v)).erase u := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hy,ha⟩
        refine ⟨?_,(Finset.mem_filter.mp hy).1,ha⟩
        intro hyu
        subst y
        exact BipartiteExchange.leaf_not_high G S u v hu ((high_iff G S u).mp hy)
      · rintro ⟨hyu,hy,ha⟩
        refine ⟨(high_iff G S y).mpr ?_,ha⟩
        by_contra hn
        exact hyu (hunique y (nonhigh_neighbor_leaf G S y v hy hh hn (G.adj_symm ha)))
    change ((CertificateBound.high G S).filter (G.Adj v)).card=d-1
    rw [he,Finset.card_erase_of_mem hum]
    change selectedDegree G S v-1=d-1
    rw [hc.1]

/-- Exact attainment of the order bound excludes all selected isolates. -/
theorem order_tight_isolates (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card=d*Fintype.card V) : (isolates G S).card=0 := by
  have hc := regular_selection_bound G S hS d hd hdegree
  omega

private theorem neighbor_of_no_isolates (hz : (isolates G S).card=0)
    (u : V) (hu : u ∈ S) : ∃ w, w ∈ S ∧ G.Adj u w := by
  have hn : selectedDegree G S u ≠ 0 := by
    intro he
    have hm : u ∈ isolates G S := Finset.mem_filter.mpr ⟨hu,he⟩
    have hn := Finset.eq_empty_iff_forall_notMem.mp (Finset.card_eq_zero.mp hz) u
    exact hn hm
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by
    change 0 < selectedDegree G S u
    omega : 0<(S.filter (G.Adj u)).card)
  exact ⟨w,(Finset.mem_filter.mp hw).1,(Finset.mem_filter.mp hw).2⟩

/-- In every regular order-bound equality graph, including graphs with
triangles, a selected leaf uses its support's actual chosen witness and its
support has full selected degree. No bipartition premise is present. -/
theorem order_tight_leaf_witness (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card=d*Fintype.card V)
    (u h : V) (hu : BipartiteExchange.LeafAt G S u h) :
    G.Adj (BipartiteExchange.witness G S hS h) u ∧ selectedDegree G S h=d := by
  classical
  have hz := order_tight_isolates G S hS d (by omega) hdegree ht
  have hcap : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V := by rw [hz]; omega
  obtain ⟨x,hf,hxu,hunique⟩ := Regular.selected_leaf_has_private_witness G.Adj (· ∈ S)
    (fun _ => G.irrefl) (fun _ _ ha => G.adj_symm ha)
    ((regular_minimal_iff G S).mpr hS)
    (neighbor_of_no_isolates G S hz) u h hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  have ha : selectedDegree G S x=1 := by
    have he : S.filter (G.Adj x)={u} := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨hw,hxw⟩; exact hunique w hw hxw
      · rintro rfl; exact ⟨hu.1,hxu⟩
    simp only [selectedDegree,he,Finset.card_singleton]
  have hx : x ∈ Finset.univ \ S := by simpa using hf.1
  rcases (tight_outside_classes G S hS d (by omega) hdegree hcap).2 x hx with he | he
  · obtain ⟨k,hk,hkx⟩ := he
    have hh := (high_iff G S k).mp hk
    have hnk : ¬ G.Adj x k := by
      intro hax
      have hku := hunique k hh.1 hax
      exact BipartiteExchange.leaf_not_high G S u h hu (hku ▸ hh)
    have hfk : Regular.Failure G.Adj (· ∈ S) k x := by
      rw [← hkx]
      exact BipartiteExchange.witness_failure G S hS k hh
    obtain ⟨w,hw,hxw,hwunique⟩ := BipartiteExchange.nonadjacent_leaf G S hS k x hh hfk hnk
    have hwu := hunique w hw.1 hxw
    subst w
    have hkh := BipartiteExchange.leaf_support_unique G S u k h hw hu
    subst k
    have hn : ¬ G.Adj (BipartiteExchange.witness G S hS h) h := by rw [hkx]; exact hnk
    refine ⟨by rw [hkx]; exact hxu,?_⟩
    rcases tight_witness_classes G S hS d (by omega) hdegree hcap h hk with hc | hc
    · exact (hn hc.2.2).elim
    · exact hc.1
  · omega

/-- All high selected vertices in an order-bound equality graph have full
selected degree, with no triangle-free or bipartite assumption. -/
theorem order_tight_high_full (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S) : selectedDegree G S v=d := by
  classical
  have hz := order_tight_isolates G S hS d (by omega) hdegree ht
  have hcap : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V := by rw [hz]; omega
  have hh := (high_iff G S v).mp hv
  rcases tight_witness_classes G S hS d (by omega) hdegree hcap v hv with hc | hc
  · let x := BipartiteExchange.witness G S hS v
    have hf := BipartiteExchange.witness_failure G S hS v hh
    have hxd : selectedDegree G S x = 2 := hc.2.1
    have htwo : 1<(S.filter (G.Adj x)).card := by
      change 1 < selectedDegree G S x
      omega
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp htwo
    have he : ∃ u, u ∈ S ∧ u≠v ∧ G.Adj x u := by
      by_cases hav : a=v
      · exact ⟨b,(Finset.mem_filter.mp hb).1,by intro h; exact hab (hav.trans h.symm),
          (Finset.mem_filter.mp hb).2⟩
      · exact ⟨a,(Finset.mem_filter.mp ha).1,hav,(Finset.mem_filter.mp ha).2⟩
    obtain ⟨u,hu,huv,hxu⟩ := he
    have hunique : ∀ w ∈ S, G.Adj u w → w=v := by
      intro w hw huw
      by_contra hwv
      exact hf.2 (Or.inr ⟨u,w,⟨hu,huv⟩,⟨hw,hwv⟩,hxu,huw⟩)
    obtain ⟨w,hw,huw⟩ := neighbor_of_no_isolates G S hz u hu
    have hwv := hunique w hw huw
    have huv' : G.Adj u v := hwv ▸ huw
    have hl : BipartiteExchange.LeafAt G S u v := ⟨hu,hh,huv',hunique⟩
    have hfull := (order_tight_leaf_witness G S hS d hd hdegree ht u v hl).2
    omega
  · exact hc.1

/-- Each high in every regular order-bound equality graph is paired with
exactly one selected leaf. The chosen outside witness has that leaf as its
unique selected neighbor; this is the actual H--U--X pairing. -/
theorem order_tight_unique_leaf (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S) :
    ∃! u, BipartiteExchange.LeafAt G S u v := by
  have hz := order_tight_isolates G S hS d (by omega) hdegree ht
  have hcap : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V := by rw [hz]; omega
  have hh := (high_iff G S v).mp hv
  have hfull := order_tight_high_full G S hS d hd hdegree ht v hv
  have hn : ¬ G.Adj (BipartiteExchange.witness G S hS v) v := by
    rcases tight_witness_classes G S hS d (by omega) hdegree hcap v hv with hc | hc
    · omega
    · exact hc.2.2
  obtain ⟨u,hu,hxu,hunique⟩ := BipartiteExchange.nonadjacent_leaf G S hS v
    (BipartiteExchange.witness G S hS v) hh
    (BipartiteExchange.witness_failure G S hS v hh) hn
  refine ⟨u,hu,?_⟩
  intro w hw
  exact hunique w hw.1 (order_tight_leaf_witness G S hS d hd hdegree ht w v hw).1

/-- Every omitted vertex of an isolate-tight regular selection has one, two,
or d selected neighbors. The low-capacity classes are actual witness images. -/
theorem tight_resource_degrees (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (x : V) (hx : x ∉ S) :
    selectedDegree G S x=1 ∨ selectedDegree G S x=2 ∨ selectedDegree G S x=d := by
  rcases (tight_outside_classes G S hS d (by omega) hdegree ht).2 x
    (by simpa using hx) with he | he
  · obtain ⟨v,hv,hvx⟩ := he
    rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
    · exact Or.inr (Or.inl (hvx ▸ hc.2.1))
    · exact Or.inl (hvx ▸ hc.2.1)
  · exact Or.inr (Or.inr he)

/-- A degree-one omitted resource is exactly the unique chosen witness of
an actual full selected-degree high. This is the C--X1 bijection. -/
theorem tight_one_owner (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (x : V) (hx : x ∉ S) (hone : selectedDegree G S x=1) :
    ∃! v, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d ∧
      BipartiteExchange.witness G S hS v=x := by
  rcases (tight_outside_classes G S hS d (by omega) hdegree ht).2 x
    (by simpa using hx) with he | he
  · obtain ⟨v,hv,hvx⟩ := he
    have hf : selectedDegree G S v=d := by
      rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
      · rw [hvx] at hc; omega
      · exact hc.1
    refine ⟨v,⟨hv,hf,hvx⟩,?_⟩
    rintro w ⟨hw,_,hwx⟩
    exact BipartiteExchange.witness_injective G S hS w v
      ((high_iff G S w).mp hw) ((high_iff G S v).mp hv) (hwx.trans hvx.symm)
  · omega

/-- A degree-two omitted resource is exactly the unique adjacent chosen
witness of a degree-(d-1) high. This is the A--X2 bijection. -/
theorem tight_two_owner (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (x : V) (hx : x ∉ S) (htwo : selectedDegree G S x=2) :
    ∃! v, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d-1 ∧
      BipartiteExchange.witness G S hS v=x ∧ G.Adj x v := by
  rcases (tight_outside_classes G S hS d (by omega) hdegree ht).2 x
    (by simpa using hx) with he | he
  · obtain ⟨v,hv,hvx⟩ := he
    have hf : selectedDegree G S v=d-1 ∧ G.Adj x v := by
      rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
      · exact ⟨hc.1,hvx ▸ hc.2.2⟩
      · rw [hvx] at hc; omega
    refine ⟨v,⟨hv,hf.1,hvx,hf.2⟩,?_⟩
    rintro w ⟨hw,_,hwx,_⟩
    exact BipartiteExchange.witness_injective G S hS w v
      ((high_iff G S w).mp hw) ((high_iff G S v).mp hv) (hwx.trans hvx.symm)
  · omega

/-- In a bipartite graph the second selected neighbor of X2 is an actual
selected isolate, uniquely. No extra isolate-support hypothesis is assumed. -/
theorem tight_two_isolate (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (x : V) (hx : x ∉ S) (htwo : selectedDegree G S x=2) :
    ∃ v u, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d-1 ∧
      BipartiteExchange.witness G S hS v=x ∧
      S.filter (G.Adj x)={v,u} ∧ BipartiteExchange.Isolate G S u := by
  classical
  obtain ⟨v,⟨hv,hdv,hvx,hxv⟩,_⟩ := tight_two_owner G S hS d hd hdegree ht x hx htwo
  have hvm : v ∈ S.filter (G.Adj x) := Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hv).1,hxv⟩
  have hc : ((S.filter (G.Adj x)).erase v).card=1 := by
    rw [Finset.card_erase_of_mem hvm]
    change selectedDegree G S x-1=1
    omega
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hc
  have hum : u ∈ (S.filter (G.Adj x)).erase v := by rw [hu]; simp
  have hne := (Finset.mem_erase.mp hum).1
  have hus := Finset.mem_filter.mp (Finset.mem_erase.mp hum).2
  have he : S.filter (G.Adj x)={v,u} := by
    rw [← Finset.insert_erase hvm,hu]
  have hf : Regular.Failure G.Adj (· ∈ S) v x := hvx ▸
    BipartiteExchange.witness_failure G S hS v ((high_iff G S v).mp hv)
  exact ⟨v,u,hv,hdv,hvx,he,
    BipartiteExchange.adjacent_other_isolate G S color hcolor v x u hf hxv hus.1 hne hus.2⟩

/-- The exact cardinalities of both low-resource classes equal those of
their actual high owners, with no finite graph-order enumeration. -/
theorem tight_resource_cardinalities (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) :
    ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d)).card =
      ((Finset.univ \ S).filter (fun x => selectedDegree G S x=1)).card ∧
    ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d-1)).card =
      ((Finset.univ \ S).filter (fun x => selectedDegree G S x=2)).card := by
  classical
  constructor
  · apply Finset.card_bij (fun v _ => BipartiteExchange.witness G S hS v)
    · intro v hv
      obtain ⟨hv,hvd⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨witness_outside G S hS v hv,?_⟩
      rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
      · omega
      · exact hc.2.1
    · intro v hv w hw he
      exact BipartiteExchange.witness_injective G S hS v w
        ((high_iff G S v).mp (Finset.mem_filter.mp hv).1)
        ((high_iff G S w).mp (Finset.mem_filter.mp hw).1) he
    · intro x hx
      obtain ⟨hx,hxd⟩ := Finset.mem_filter.mp hx
      obtain ⟨v,⟨hv,hvd,hvx⟩,_⟩ := tight_one_owner G S hS d hd hdegree ht x
        (Finset.mem_sdiff.mp hx).2 hxd
      exact ⟨v,Finset.mem_filter.mpr ⟨hv,hvd⟩,hvx⟩
  · apply Finset.card_bij (fun v _ => BipartiteExchange.witness G S hS v)
    · intro v hv
      obtain ⟨hv,hvd⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨witness_outside G S hS v hv,?_⟩
      rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
      · exact hc.2.1
      · omega
    · intro v hv w hw he
      exact BipartiteExchange.witness_injective G S hS v w
        ((high_iff G S v).mp (Finset.mem_filter.mp hv).1)
        ((high_iff G S w).mp (Finset.mem_filter.mp hw).1) he
    · intro x hx
      obtain ⟨hx,hxd⟩ := Finset.mem_filter.mp hx
      obtain ⟨v,⟨hv,hvd,hvx,_⟩,_⟩ := tight_two_owner G S hS d hd hdegree ht x
        (Finset.mem_sdiff.mp hx).2 hxd
      exact ⟨v,Finset.mem_filter.mpr ⟨hv,hvd⟩,hvx⟩

open scoped Classical in
/-- All selected leaves and all full-degree highs are paired bijectively in
an isolate-tight regular bipartite graph. -/
theorem tight_leaf_cardinality (hS : IsMinimalStarForming G 2 S)
    (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) :
    ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d)).card =
      (S.filter (fun u => ∃ v, BipartiteExchange.LeafAt G S u v)).card := by
  classical
  let C := (CertificateBound.high G S).filter (fun v => selectedDegree G S v=d)
  have existsLeaf (v : V) (hv : v ∈ C) : ∃! u, BipartiteExchange.LeafAt G S u v :=
    tight_full_unique_leaf G S hS color hcolor d hd hdegree ht v
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  let leaf (v : V) (hv : v ∈ C) : V := Classical.choose (existsLeaf v hv)
  have hl (v : V) (hv : v ∈ C) : BipartiteExchange.LeafAt G S (leaf v hv) v :=
    (Classical.choose_spec (existsLeaf v hv)).1
  apply Finset.card_bij leaf
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(hl v hv).1,v,hl v hv⟩
  · intro v hv w hw he
    exact BipartiteExchange.leaf_support_unique G S (leaf v hv) v w
      (hl v hv) (he ▸ hl w hw)
  · intro u hu
    obtain ⟨_,v,huv⟩ := Finset.mem_filter.mp hu
    have hv : v ∈ C := Finset.mem_filter.mpr
      ⟨(high_iff G S v).mpr huv.2.1,
        tight_leaf_full G S hS color hcolor d hd hdegree ht u v huv⟩
    exact ⟨v,hv,((Classical.choose_spec (existsLeaf v hv)).2 u huv).symm⟩

/-- In order-bound equality the actual high graph is (d-1)-regular even
when the original graph has triangles. -/
theorem order_tight_high_regular (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card=d*Fintype.card V)
    (v : V) (hv : v ∈ CertificateBound.high G S) :
    selectedDegree G (CertificateBound.high G S) v=d-1 := by
  classical
  have hh := (high_iff G S v).mp hv
  have hfull := order_tight_high_full G S hS d hd hdegree ht v hv
  obtain ⟨u,hu,hunique⟩ := order_tight_unique_leaf G S hS d hd hdegree ht v hv
  have hum : u ∈ S.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hu.1,G.adj_symm hu.2.2.1⟩
  have he : (CertificateBound.high G S).filter (G.Adj v)=(S.filter (G.Adj v)).erase u := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨hy,ha⟩
      refine ⟨?_,(Finset.mem_filter.mp hy).1,ha⟩
      intro hyu
      subst y
      exact BipartiteExchange.leaf_not_high G S u v hu ((high_iff G S u).mp hy)
    · rintro ⟨hyu,hy,ha⟩
      refine ⟨(high_iff G S y).mpr ?_,ha⟩
      by_contra hn
      exact hyu (hunique y (nonhigh_neighbor_leaf G S y v hy hh hn (G.adj_symm ha)))
  change ((CertificateBound.high G S).filter (G.Adj v)).card=d-1
  rw [he,Finset.card_erase_of_mem hum]
  change selectedDegree G S v-1=d-1
  rw [hfull]

private theorem degree_split (v : V) : degree G v=selectedDegree G S v+
    ((Finset.univ \ S).filter (G.Adj v)).card := by
  classical
  have he : Finset.univ.filter (G.Adj v) =
      (S.filter (G.Adj v)) ∪ ((Finset.univ \ S).filter (G.Adj v)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hd : Disjoint (S.filter (G.Adj v)) ((Finset.univ \ S).filter (G.Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1
  change (Finset.univ.filter (G.Adj v)).card = _
  rw [he,Finset.card_union_of_disjoint hd]
  rfl

/-- A high's only possible omitted neighbor is its own adjacent X2 witness.
Full-degree highs have no omitted neighbor at all. -/
theorem tight_high_outside (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (v x : V) (hv : v ∈ CertificateBound.high G S) (hx : x ∉ S) (hvx : G.Adj v x) :
    selectedDegree G S v=d-1 ∧ BipartiteExchange.witness G S hS v=x ∧
      selectedDegree G S x=2 := by
  classical
  have hs := degree_split G S v
  rw [hdegree v] at hs
  have hxm : x ∈ (Finset.univ \ S).filter (G.Adj v) := by
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact ⟨hx,hvx⟩
  have hp := Finset.card_pos.mpr ⟨x,hxm⟩
  rcases tight_witness_classes G S hS d (by omega) hdegree ht v hv with hc | hc
  · have hm : BipartiteExchange.witness G S hS v ∈
        (Finset.univ \ S).filter (G.Adj v) :=
      Finset.mem_filter.mpr ⟨witness_outside G S hS v hv,G.adj_symm hc.2.2⟩
    have he := Finset.card_le_one.mp (by omega :
      ((Finset.univ \ S).filter (G.Adj v)).card≤1) _ hm _ hxm
    exact ⟨hc.1,he,he ▸ hc.2.1⟩
  · omega

/-- Every Y vertex has only selected nonhigh neighbors. In particular Y is
independent and has no edge to any omitted resource. -/
theorem tight_full_resource_neighbors (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (y : V) (hy : y ∉ S) (hyd : selectedDegree G S y=d)
    (v : V) (hyv : G.Adj y v) : v ∈ S ∧ v ∉ CertificateBound.high G S := by
  classical
  have he : S.filter (G.Adj y)=Finset.univ.filter (G.Adj y) :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ (Finset.subset_univ S)) (by
      change degree G y≤selectedDegree G S y
      rw [hdegree y,hyd])
  have hvs : v ∈ S := (Finset.mem_filter.mp (he ▸
    (Finset.mem_filter.mpr ⟨Finset.mem_univ v,hyv⟩))).1
  refine ⟨hvs,?_⟩
  intro hv
  have hc := (tight_high_outside G S hS d hd hdegree ht v y hv hy (G.adj_symm hyv)).2.2
  omega

/-- Apart from its high support and the associated X1 resource, every
neighbor of a selected leaf lies in Y. All d-2 remaining leaf incidences are
therefore available for the exact class balance. -/
theorem tight_leaf_remaining_neighbors (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d)
    (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V)
    (u v : V) (hu : BipartiteExchange.LeafAt G S u v)
    (x : V) (hux : G.Adj u x) (hxv : x≠v)
    (hxw : x≠BipartiteExchange.witness G S hS v) :
    x ∉ S ∧ selectedDegree G S x=d := by
  classical
  have hxs : x ∉ S := fun hx => hxv (hu.2.2.2 x hx hux)
  refine ⟨hxs,?_⟩
  rcases tight_resource_degrees G S hS d hd hdegree ht x hxs with hx | hx | hx
  · obtain ⟨w,⟨hw,hwd,hwx⟩,_⟩ := tight_one_owner G S hS d hd hdegree ht x hxs hx
    have hf := BipartiteExchange.witness_failure G S hS w ((high_iff G S w).mp hw)
    have hn : ¬ G.Adj (BipartiteExchange.witness G S hS w) w := by
      rcases tight_witness_classes G S hS d (by omega) hdegree ht w hw with hc | hc
      · omega
      · exact hc.2.2
    obtain ⟨z,hz,hxz,hunique⟩ := BipartiteExchange.nonadjacent_leaf G S hS w
      (BipartiteExchange.witness G S hS w) ((high_iff G S w).mp hw) hf hn
    have huz : u=z := hunique u hu.1 (hwx ▸ G.adj_symm hux)
    have huv : w=v := BipartiteExchange.leaf_support_unique G S u w v (huz ▸ hz) hu
    subst w
    exact (hxw hwx.symm).elim
  · obtain ⟨w,z,hw,hwd,hwx,he,hz⟩ := tight_two_isolate G S hS color hcolor d hd hdegree ht x hxs hx
    have hum : u ∈ S.filter (G.Adj x) := Finset.mem_filter.mpr ⟨hu.1,G.adj_symm hux⟩
    rw [he] at hum
    simp only [Finset.mem_insert,Finset.mem_singleton] at hum
    rcases hum with huw | huz
    · exact (BipartiteExchange.leaf_not_high G S u v hu (huw ▸ (high_iff G S w).mp hw)).elim
    · subst z
      exact (hz.2 v hu.2.1.1 hu.2.2.1).elim
  · exact hx

/-- Attainment of the regular order bound by SF is equivalent to attainment
by beta in every finite bipartite graph of positive regular degree. The
isolate count is discharged from the actual attaining SF selection. -/
theorem order_endpoint_iff (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d)
    (hdegree : ∀ v, degree G v=d) :
    (2*d-1)*SF G 2=d*Fintype.card V ↔
      (2*d-1)*beta G 2=d*Fintype.card V := by
  classical
  have hm : 0<2*d-1 := by omega
  have upper := (Nat.le_div_iff_mul_le hm).mp (sf_regular_bound G d hd hdegree)
  have lower := beta_le_sf G
  constructor
  · intro he
    obtain ⟨A,hA,hcard⟩ := sf_attained G 2
    have ht : (2*d-1)*A.card=d*Fintype.card V := by rw [hcard]; exact he
    have hz := order_tight_isolates G A hA d hd hdegree ht
    have hc := BipartiteExchange.selection_compensation G hG A hA
    rw [hz,hcard] at hc
    have hb : beta G 2=SF G 2 := by omega
    rw [hb]
    exact he
  · intro he
    have hl := Nat.mul_le_mul_left (2*d-1) lower
    nlinarith

end D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
