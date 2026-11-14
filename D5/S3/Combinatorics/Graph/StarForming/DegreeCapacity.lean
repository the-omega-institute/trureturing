/- GID: D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/DegreeCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Injective deletion-witness capacity bounds actual finite degree sums. -/

import D5.S3.Combinatorics.Graph.StarForming.FiniteCover
import D5.S3.Combinatorics.Graph.StarForming.CertificateBound
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-! The sum form avoids truncating degree minus one at isolated vertices.
It is equivalent over integers to the received degree-capacity inequality. -/

namespace D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
open StarFormingDissociationRefutation
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def degree (v : V) : ℕ := (Finset.univ.filter (G.Adj v)).card

def selectedDegree (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

def isolates (S : Finset V) : Finset V := S.filter (fun v => selectedDegree G S v = 0)

private theorem selected_le_degree (S : Finset V) (v : V) :
    selectedDegree G S v ≤ degree G v :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))

/-- A deletion failure has at most two original selected neighbors. -/
theorem failure_selected_degree_le_two (S : Finset V) (v x : V)
    (hx : Regular.Failure G.Adj (· ∈ S) v x) : selectedDegree G S x ≤ 2 := by
  classical
  have haerase : ((S.erase v).filter (G.Adj x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hne
    exact hx.2 (Or.inl ⟨a,b,
      ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2,
       (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).1⟩,
      ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2,
       (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1⟩,
      hne,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩)
  have hax : selectedDegree G S x ≤ 2 := by
    have hsub : S.filter (G.Adj x) ⊆ insert v ((S.erase v).filter (G.Adj x)) := by
      intro a ha
      by_cases he : a = v
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨he,(Finset.mem_filter.mp ha).1⟩,
           (Finset.mem_filter.mp ha).2⟩))
    have hc := Finset.card_le_card hsub
    have hi := Finset.card_insert_le v ((S.erase v).filter (G.Adj x))
    unfold selectedDegree
    omega
  exact hax

/-- An outside edge to a failure excludes full selected degree at its owner. -/
theorem adjacent_failure_degree (S : Finset V) (D : ℕ)
    (hD : ∀ v, degree G v ≤ D) (v x : V)
    (hx : Regular.Failure G.Adj (· ∈ S) v x) (hedge : G.Adj x v) :
    selectedDegree G S v + 1 ≤ D := by
  classical
  have hxnot : x ∉ S.filter (G.Adj v) := fun h => hx.1 (Finset.mem_filter.mp h).1
  have hsub : insert x (S.filter (G.Adj v)) ⊆ Finset.univ.filter (G.Adj v) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,G.adj_symm hedge⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  have hc := (Finset.card_le_card hsub).trans (hD v)
  rw [Finset.card_insert_of_notMem hxnot] at hc
  exact hc
/-- A high vertex and its failure witness use at most one extra unit of capacity. -/
theorem witness_degree_capacity (S : Finset V) (D : ℕ)
    (hD : ∀ v, degree G v ≤ D) (v x : V)
    (hx : Regular.Failure G.Adj (· ∈ S) v x) :
    selectedDegree G S v + selectedDegree G S x ≤ D + 1 := by
  classical
  have hav : selectedDegree G S v ≤ D := (selected_le_degree G S v).trans (hD v)
  apply Regular.witness_capacity D (selectedDegree G S v) (selectedDegree G S x)
    (G.Adj x v) hav (failure_selected_degree_le_two G S v x hx)
  · exact adjacent_failure_degree G S D hD v x hx
  · intro hnon
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Regular.nonadjacent_witness_unique_neighbor G.Adj (· ∈ S) v x a b hx hnon
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

/-- The witness assignment counts each outside degree capacity once. -/
theorem high_capacity_sum (S : Finset V) (hS : IsMinimalStarForming G 2 S)
    (D : ℕ) (hD : ∀ v, degree G v ≤ D) :
    ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1) ≤
      ∑ x ∈ Finset.univ \ S, (D - selectedDegree G S x) := by
  classical
  let H := CertificateBound.high G S
  let T := Finset.univ \ S
  have hm := (regular_minimal_iff G S).mpr hS
  have hh (v : ↥H) : Regular.High G.Adj (· ∈ S) v := by
    have hv := Finset.mem_filter.mp v.property
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega :
      1 < (S.filter (G.Adj v)).card)
    exact ⟨hv.1,a,b,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1,
      hab,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
  choose f hf using fun v : ↥H =>
    Regular.high_has_failure G.Adj (· ∈ S) (fun _ => G.irrefl) hm v (hh v)
  let F : ↥H → ↥T := fun v => ⟨f v,by simp [T,(hf v).1]⟩
  have hF : Function.Injective F := by
    intro v w he
    have he' : f v = f w := congrArg Subtype.val he
    apply Subtype.ext
    exact Regular.failure_witnesses_disjoint G.Adj (· ∈ S) hm.1 v w (f v)
      (hh v) (hh w) (hf v) (by simpa only [← he'] using hf w)
  have hpay (v : ↥H) : selectedDegree G S v - 1 ≤ D - selectedDegree G S (F v) := by
    have hc := witness_degree_capacity G S D hD v (f v) (hf v)
    have hd := (selected_le_degree G S (f v)).trans (hD (f v))
    change selectedDegree G S v - 1 ≤ D - selectedDegree G S (f v)
    omega
  have hsum : ∑ v : ↥H, (selectedDegree G S v - 1) ≤
      ∑ x : ↥T, (D - selectedDegree G S x) := by
    calc
      _ ≤ ∑ v : ↥H, (D - selectedDegree G S (F v)) :=
        Finset.sum_le_sum (fun v _ => hpay v)
      _ = ∑ x ∈ Finset.univ.image F, (D - selectedDegree G S x) := by
        rw [Finset.sum_image]
        exact hF.injOn
      _ ≤ ∑ x : ↥T, (D - selectedDegree G S x) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_coe_sort H (fun v => selectedDegree G S v - 1),
    Finset.sum_coe_sort T (fun x => D - selectedDegree G S x)] at hsum
  exact hsum

/-- The two sides of the cut have the same edge count. -/
theorem degree_sum_cut (S : Finset V) :
    ∑ v ∈ S, degree G v =
      (∑ v ∈ S, selectedDegree G S v) +
      ∑ x ∈ Finset.univ \ S, selectedDegree G S x := by
  classical
  have hsplit (v : V) : degree G v = selectedDegree G S v +
      ((Finset.univ \ S).filter (G.Adj v)).card := by
    have he : Finset.univ.filter (G.Adj v) =
        (S.filter (G.Adj v)) ∪ ((Finset.univ \ S).filter (G.Adj v)) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
        Finset.mem_sdiff]
      tauto
    have hd : Disjoint (S.filter (G.Adj v)) ((Finset.univ \ S).filter (G.Adj v)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1
    change (Finset.univ.filter (G.Adj v)).card = _
    rw [he,Finset.card_union_of_disjoint hd]
    rfl
  simp_rw [hsplit,Finset.sum_add_distrib]
  congr 1
  have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := Finset.univ \ S) G.Adj
  simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,selectedDegree,G.adj_comm] using hc

/-- The exact selection identity separates isolates, matching vertices and high vertices. -/
theorem selected_degree_identity (S : Finset V) :
    (∑ v ∈ S, selectedDegree G S v) + (isolates G S).card = S.card +
      ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1) := by
  classical
  have hi : (isolates G S).card =
      ∑ v ∈ S, (if selectedDegree G S v = 0 then 1 else 0) := by
    simp only [isolates,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hh : (∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1)) =
      ∑ v ∈ S, (if 2 ≤ selectedDegree G S v then selectedDegree G S v - 1 else 0) := by
    simp only [CertificateBound.high,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have he : (S.filter (G.Adj v)).card = selectedDegree G S v := by
      unfold selectedDegree
      congr 1
    rw [he]
  rw [hi,hh,Finset.card_eq_sum_ones S,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  change selectedDegree G S v + (if selectedDegree G S v = 0 then 1 else 0) =
    1 + (if 2 ≤ selectedDegree G S v then selectedDegree G S v - 1 else 0)
  split_ifs <;> omega

/-- Degree capacity in a form valid even at ambient isolated vertices. -/
theorem degree_capacity (S : Finset V) (hS : IsMinimalStarForming G 2 S)
    (D : ℕ) (hD : ∀ v, degree G v ≤ D) :
    (∑ v ∈ S, degree G v) + (isolates G S).card ≤
      S.card + D * (Finset.univ \ S).card := by
  have hcap := high_capacity_sum G S hS D hD
  have hid := selected_degree_identity G S
  have hcut := degree_sum_cut G S
  have htotal : (∑ x ∈ Finset.univ \ S, (D - selectedDegree G S x)) +
      (∑ x ∈ Finset.univ \ S, selectedDegree G S x) = D * (Finset.univ \ S).card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x ∈ Finset.univ \ S, D := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Nat.sub_add_cancel ((selected_le_degree G S x).trans (hD x))
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- The regular order bound includes every minimal set and its actual isolates. -/
theorem regular_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S)
    (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) :
    (2 * d - 1) * S.card + (isolates G S).card ≤ d * Fintype.card V := by
  have hc := degree_capacity G S hS d (fun v => (hregular v).le)
  have he : (∑ v ∈ S, degree G v) = d * S.card := by simp [hregular,Nat.mul_comm]
  have ht : (Finset.univ \ S).card + S.card = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hm : (2 * d - 1) + 1 = 2 * d := by omega
  rw [he] at hc
  nlinarith

/-- The finite supremum obeys the sharp regular order upper bound. -/
theorem sf_regular_bound (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) :
    SF G 2 ≤ d * Fintype.card V / (2 * d - 1) := by
  classical
  apply Finset.sup_le
  intro S hS
  have hb := regular_selection_bound G S (Finset.mem_filter.mp hS).2 d hd hregular
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * d - 1)).mpr
  rw [Nat.mul_comm]
  omega

/-- The irregular endpoint retains both degree bounds and selected isolates. -/
theorem min_max_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S)
    (delta D : ℕ) (hpositive : 2 ≤ delta + D)
    (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) :
    (delta + D - 1) * S.card + (isolates G S).card ≤ D * Fintype.card V := by
  have hc := degree_capacity G S hS D hmax
  have hl : delta * S.card ≤ ∑ v ∈ S, degree G v := by
    calc
      _ = ∑ _v ∈ S, delta := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin v)
  have ht : (Finset.univ \ S).card + S.card = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hm : (delta + D - 1) + 1 = delta + D := by omega
  nlinarith

/-- The finite upper maximum inherits the irregular minimum/maximum endpoint. -/
theorem sf_min_max_bound (delta D : ℕ) (hpositive : 2 ≤ delta + D)
    (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) :
    SF G 2 ≤ D * Fintype.card V / (delta + D - 1) := by
  classical
  apply Finset.sup_le
  intro S hS
  have hb := min_max_selection_bound G S (Finset.mem_filter.mp hS).2
    delta D hpositive hmin hmax
  apply (Nat.le_div_iff_mul_le (by omega : 0 < delta + D - 1)).mpr
  rw [Nat.mul_comm]
  omega

/-- The deficiency-free form of the dissociation cut bound counts the actual
degrees on both sides, so it applies directly to broken regular blocks. -/
theorem dissociation_cut_bound (S : Finset V) (hS : IsKIndependent G 2 S) :
    2 * (∑ v ∈ S, degree G v) ≤
      S.card + ∑ v : V, degree G v := by
  classical
  have hcut := degree_sum_cut G S
  have hsel : (∑ v ∈ S, selectedDegree G S v) ≤ S.card := by
    calc
      _ ≤ ∑ _v ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro v hv
        have hh := hS v hv
        change selectedDegree G S v < 2 at hh
        omega
      _ = _ := by simp
  have hout : (∑ v ∈ Finset.univ \ S, selectedDegree G S v) ≤
      ∑ v ∈ Finset.univ \ S, degree G v :=
    Finset.sum_le_sum (fun v _ => selected_le_degree G S v)
  have hall : (∑ v ∈ S, degree G v) +
      (∑ v ∈ Finset.univ \ S, degree G v) = ∑ v : V, degree G v := by
    simpa only [Finset.compl_eq_univ_sdiff] using
      Finset.sum_add_sum_compl S (fun v => degree G v)
  omega

/-- Actual regular deficiency on selected vertices supplies twice its credit. -/
theorem dissociation_deficiency_bound (S : Finset V) (hS : IsKIndependent G 2 S)
    (d : ℕ) (hd : 1 ≤ d) (hmax : ∀ v, degree G v ≤ d) :
    (2 * d - 1) * S.card + (∑ v : V, (d - degree G v)) ≤
      d * Fintype.card V + 2 * (∑ v ∈ S, (d - degree G v)) := by
  classical
  have hc := dissociation_cut_bound G S hS
  have hs : (∑ v ∈ S, degree G v) + (∑ v ∈ S, (d - degree G v)) = d * S.card := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Nat.add_sub_of_le (hmax _)]
    simp [Nat.mul_comm]
  have ht : (∑ v : V, degree G v) + (∑ v : V, (d - degree G v)) =
      d * Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Nat.add_sub_of_le (hmax _)]
    simp [Nat.mul_comm]
  have hm : (2 * d - 1) + 1 = 2 * d := by omega
  nlinarith

end D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
