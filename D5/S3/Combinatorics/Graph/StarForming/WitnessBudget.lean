/- GID: D5/S3/Combinatorics/Graph/StarForming/WitnessBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/WitnessBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange]
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

end D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
