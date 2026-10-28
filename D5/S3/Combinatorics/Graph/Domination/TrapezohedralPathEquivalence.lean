/- GID: D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Ordered cut-cover complementation gives the actual labelled graph counting equivalence. -/

import D5.S3.Combinatorics.Graph.Domination.TrapezohedralTaggedCover
import D5.S3.Combinatorics.Graph.Domination.PathEndpointCount

/-! Actual cut covers are relabelled along the opened rim path. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TrapezohedralPathEquivalence

open TrapezohedralMinimalDomination TrapezohedralTaggedCover
open PathMaximalIndependentCount PathEndpointCount

section Order
variable {n : ℕ} [NeZero n]

/-- The ordered path begins just after the removed cyclic edge. -/
def order (j : Fin n) : Equiv.Perm (Fin n) := finCycle (finRotate n j)

omit [NeZero n] in
private theorem order_rotate (j i : Fin n) :
    order j (finRotate n i) = finRotate n (order j i) := by
  simp [order, finCycle_apply, finRotate_apply, add_assoc, add_comm, add_left_comm]

private theorem order_last (j : Fin n) : order j (-1) = j := by
  simp [order, finCycle_apply, finRotate_apply, add_assoc, add_comm, add_left_comm]

private theorem last_val (hn : 3 ≤ n) : ((-1 : Fin n) : ℕ) = n - 1 := by
  rw [Fin.val_neg']
  change (n - (1 % n)) % n = n - 1
  have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.mod_eq_of_lt (by omega)]

private theorem rotate_val {i : Fin n} (hi : i ≠ -1) :
    (finRotate n i).val = i.val + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hlast : i ≠ Fin.last k := by
    simpa only [← Fin.neg_last, neg_neg] using hi
  exact coe_finRotate_of_ne_last hlast

private theorem next_of_vals (hn : 3 ≤ n) {i k : Fin n}
    (h : i.val + 1 = k.val) : finRotate n i = k ∧ i ≠ -1 := by
  have hi : i ≠ -1 := by
    intro he
    have hv := last_val hn
    rw [he, hv] at h
    omega
  exact ⟨Fin.ext (by rw [rotate_val hi]; exact h), hi⟩

private theorem cut_iff_path (hn : 3 ≤ n) (j : Fin n) (C : Set (Fin n)) :
    CutCover j C ↔ (SimpleGraph.pathGraph n).IsVertexCover ((order j) ⁻¹' C) := by
  constructor
  · intro hc u v hadj
    rcases SimpleGraph.pathGraph_adj.mp hadj with h | h
    · obtain ⟨he, hne⟩ := next_of_vals hn h
      have hj : order j u ≠ j := by
        intro hh
        exact hne ((order j).injective (hh.trans (order_last j).symm))
      have hh := hc (order j u) hj
      rw [← order_rotate, he] at hh
      exact hh
    · obtain ⟨he, hne⟩ := next_of_vals hn h
      have hj : order j v ≠ j := by
        intro hh
        exact hne ((order j).injective (hh.trans (order_last j).symm))
      have hh := hc (order j v) hj
      rw [← order_rotate, he] at hh
      exact hh.symm
  · intro hc i hij
    let u := (order j).symm i
    have hu : u ≠ -1 := by
      intro he
      have hh := (order j).apply_symm_apply i
      change order j u = i at hh
      rw [he, order_last] at hh
      exact hij hh.symm
    have hadj : (SimpleGraph.pathGraph n).Adj u (finRotate n u) :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl (rotate_val hu).symm)
    have hh := hc hadj
    change order j u ∈ C ∨ order j (finRotate n u) ∈ C at hh
    simpa only [order_rotate, u, Equiv.apply_symm_apply] using hh

private theorem minimal_cut_iff (hn : 3 ≤ n) (j : Fin n) (C : Set (Fin n)) :
    MinimalCutCover j C ↔
      Maximal (SimpleGraph.pathGraph n).IsIndepSet (((order j) ⁻¹' C)ᶜ) := by
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨SimpleGraph.isIndepSet_compl_iff_isVertexCover.mpr
      ((cut_iff_path hn j C).mp hc), ?_⟩
    intro T hT hIT x hx
    have hcover : (SimpleGraph.pathGraph n).IsVertexCover Tᶜ :=
      SimpleGraph.isVertexCover_compl.mpr hT
    let D : Set (Fin n) := {i | (order j).symm i ∉ T}
    have hDC : D ⊆ C := by
      intro i hi
      by_contra hic
      exact hi (hIT (by simpa using hic))
    have hd : CutCover j D := (cut_iff_path hn j D).mpr (by
      convert hcover using 1
      ext x
      simp [D])
    have he := hm D hDC hd
    change order j x ∉ C
    intro hxc
    exact he hxc (by simpa [D] using hx)
  · rintro ⟨hi, hm⟩
    refine ⟨(cut_iff_path hn j C).mpr
      (SimpleGraph.isIndepSet_compl_iff_isVertexCover.mp hi), ?_⟩
    intro D hDC hd i hiC
    have hiD : (SimpleGraph.pathGraph n).IsIndepSet (((order j) ⁻¹' D)ᶜ) :=
      SimpleGraph.isIndepSet_compl_iff_isVertexCover.mpr ((cut_iff_path hn j D).mp hd)
    have hsub : ((order j) ⁻¹' C)ᶜ ⊆ ((order j) ⁻¹' D)ᶜ := by
      intro x hx hD
      exact hx (hDC hD)
    by_contra hnD
    have hx := hm hiD hsub (show (order j).symm i ∈ ((order j) ⁻¹' D)ᶜ by simpa)
    exact hx (by simpa using hiC)

/-- Selected natural labels are precisely the complement of the ordered cover. -/
noncomputable def encode (j : Fin n) (C : Set (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun t => order j t ∉ C)).image Fin.val

omit [NeZero n] in
private theorem mem_encode (j : Fin n) (C : Set (Fin n)) (t : Fin n) :
    t.val ∈ encode j C ↔ order j t ∉ C := by
  classical
  simp [encode, Fin.val_injective.eq_iff]

omit [NeZero n] in
private theorem encode_bounded (j : Fin n) (C : Set (Fin n)) :
    ∀ i ∈ encode j C, i < n := by
  classical
  intro i hi
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hi
  exact t.isLt

/-- The inverse retains all original cyclic labels. -/
def decode (j : Fin n) (I : Finset ℕ) : Set (Fin n) :=
  {i | ((order j).symm i).val ∉ I}

private theorem decode_encode (j : Fin n) (C : Set (Fin n)) :
    decode j (encode j C) = C := by
  classical
  ext i
  simp [decode, mem_encode]

private theorem encode_decode (j : Fin n) (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < n) : encode j (decode j I) = I := by
  classical
  ext i
  by_cases hi : i < n
  · have h := mem_encode j (decode j I) ⟨i, hi⟩
    simpa [decode] using h
  · exact iff_of_false (fun h => hi (encode_bounded j _ i h)) (fun h => hi (hI i h))

omit [NeZero n] in
private theorem restricted_iff (I : Finset ℕ) :
    I ∈ restrictedFamily n ↔
      (∀ i ∈ I, i < n) ∧
      Maximal (SimpleGraph.pathGraph n).IsIndepSet {i : Fin n | i.val ∈ I} ∧
      ¬ (0 ∈ I ∧ n - 1 ∈ I) := by
  classical
  simp only [restrictedFamily, family, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hb, hm⟩, he⟩
    exact ⟨fun i hi => Finset.mem_range.mp (hb hi), hm, he⟩
  · rintro ⟨hb, hm, he⟩
    exact ⟨⟨fun i hi => Finset.mem_range.mpr (hb i hi), hm⟩, he⟩

private theorem encode_iff (hn : 3 ≤ n) (j : Fin n) (C : Set (Fin n)) :
    encode j C ∈ restrictedFamily n ↔
      MinimalCutCover j C ∧ (j ∈ C ∨ finRotate n j ∈ C) := by
  classical
  rw [restricted_iff]
  have hs : {i : Fin n | i.val ∈ encode j C} = ((order j) ⁻¹' C)ᶜ := by
    ext i
    exact mem_encode j C i
  have h0 : 0 ∈ encode j C ↔ finRotate n j ∉ C := by
    simpa [order, finCycle_apply] using mem_encode j C (0 : Fin n)
  have hl : n - 1 ∈ encode j C ↔ j ∉ C := by
    simpa only [last_val hn, order_last] using mem_encode j C (-1 : Fin n)
  rw [hs, ← minimal_cut_iff hn j C, h0, hl]
  exact ⟨fun h => ⟨h.2.1, by tauto⟩,
    fun h => ⟨encode_bounded j C, h.1, by tauto⟩⟩

/-- The opened-rim bijection, with the removed edge label retained. -/
noncomputable def coverPathEquiv (hn : 3 ≤ n) :
    CoverData n ≃ Fin n × {I : Finset ℕ // I ∈ restrictedFamily n} where
  toFun d := ⟨d.1, ⟨encode d.1 d.2.val, (encode_iff hn d.1 d.2.val).mpr d.2.property⟩⟩
  invFun p := ⟨p.1, ⟨decode p.1 p.2.val, (encode_iff hn p.1 _).mp (by
    rw [encode_decode p.1 p.2.val ((restricted_iff p.2.val).mp p.2.property).1]
    exact p.2.property)⟩⟩
  left_inv d := by
    rcases d with ⟨j, C, hC⟩
    simp only [decode_encode]
    rfl
  right_inv p := by
    rcases p with ⟨j, I, hI⟩
    simp only [encode_decode j I ((restricted_iff I).mp hI).1]

end Order

/-- Actual labelled subsets, with both apex tags, have the exact restricted-path count. -/
theorem actual_count (n : ℕ) : actualCount n = 2 * n * restrictedCount n := by
  classical
  by_cases hn : 3 ≤ n
  · letI : NeZero n := ⟨by omega⟩
    rw [actualCount, if_pos hn, restrictedCount, if_pos hn]
    have he := Nat.card_congr ((actualTaggedEquiv hn).trans
      (Equiv.prodCongr (Equiv.refl Bool) (coverPathEquiv hn)))
    simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_coe, mul_assoc] using he
  · simp [actualCount, restrictedCount, hn]

end D5.S3.Combinatorics.Graph.Domination.TrapezohedralPathEquivalence
