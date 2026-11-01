/- GID: D5/S3/Geometry/Polygons/PolygonSimultaneousCompression
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonSimultaneousCompression
   mirror-E: none(waiver:general-structural-theorem)
   anchors: []
   utility: none
   digest: Common-support terminal compression of original conditioned triangulation families. -/

import D5.S3.Geometry.Polygons.PolygonCompressionTrace

/-! Two separate actual conditioned counts and the original-family bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
open Finset PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual
open PolygonCompressionTrace
open D5.S3.Combinatorics.SetFamily.SimultaneousCompression

variable {n : ℕ} [NeZero n]

/-- The actual deletion system; left and right count different complete fibres. -/
noncomputable def deletionSystem (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hK : (P ∪ Q).Nonempty) : DeletionSystem (E_K (P ∪ Q)) where
  feasible := feasible
  leftWeight := weight P Q
  rightWeight := weight Q P
  terminal := Independent
  left_nonneg := by intros; exact Nat.cast_nonneg _
  right_nonneg := by intros; exact Nat.cast_nonneg _
  projection := by intros; exact feasible_projection _ _
  left_marginal := by
    intro H _ t ht R hR
    exact marginal_weight (by omega) P Q H R t ht hR
  right_marginal := by
    intro H _ t ht R hR
    exact marginal_weight (by omega) Q P H R t ht hR
  local_move := by
    intro H hH hnt
    have hp := proper_of_subset_EK hK hH
    have hadj : ∃ b, b ∈ H ∧ b + 1 ∈ H := by
      by_contra h
      apply hnt
      intro b hb hb1
      exact h ⟨b, hb, hb1⟩
    obtain ⟨a, ha0, ha1, ha2⟩ := block_start H hp hadj
    have hval (k : ℕ) (hk : k < n) : (k : ZMod n).val = k :=
      ZMod.val_natCast_of_lt hk
    have hvone : (1 : ZMod n).val = 1 := by simpa using hval 1 (by omega)
    have hvtwo : (2 : ZMod n).val = 2 := by simpa using hval 2 (by omega)
    have hvthree : (3 : ZMod n).val = 3 := by simpa using hval 3 (by omega)
    have hst : a + (1 : ZMod n) ≠ a + 2 := by
      intro he
      have hv := congrArg ZMod.val (add_left_cancel he)
      rw [hvone, hvtwo] at hv
      omega
    have hsu : a + (1 : ZMod n) ≠ a + 3 := by
      intro he
      have hv := congrArg ZMod.val (add_left_cancel he)
      rw [hvone, hvthree] at hv
      omega
    refine ⟨a + 1, a + 2, a + 3, ha2, hst, hsu,
      fun X hX ht => local_excludes hX ht,
      fun X hX _ => shift_mem_feasible ha0 ha1 hX,
      fun X hX ht => local_weight_law hn hH ha0 ha1 ha2 hX ht, ?_⟩
    intro X hX ht
    exact local_weight_law hn (by simpa [union_comm] using hH) ha0 ha1 ha2 hX ht

/-- The full original conditioned family, with no observed trace restriction. -/
abbrev WholeFiber (P Q : Finset (ZMod n)) := ConditionFiber P Q ∅ ∅

/-- The traces of the selected original members, without saturating their fibres. -/
noncomputable def familyTraces (H : Finset (ZMod n)) {P Q : Finset (ZMod n)}
    (A : Finset (WholeFiber P Q)) : Finset (Finset (ZMod n)) :=
  A.image (fun T => EarCenters T.1 ∩ H)

theorem familyTraces_feasible (hn : 6 ≤ n) (H : Finset (ZMod n))
    {P Q : Finset (ZMod n)} (A : Finset (WholeFiber P Q)) :
    familyTraces H A ⊆ feasible H := by
  classical
  intro X hX
  obtain ⟨T, _, rfl⟩ := mem_image.mp hX
  exact trace_mem_feasible hn T.2.1 H

/-- Distinct original members in each trace fibre inject into the complete fibre. -/
theorem original_card_le_trace_mass (P Q H : Finset (ZMod n))
    (A : Finset (WholeFiber P Q)) :
    (A.card : ℝ) ≤ mass (weight P Q H) (familyTraces H A) := by
  classical
  have hc := card_eq_sum_card_image (fun T : WholeFiber P Q => EarCenters T.1 ∩ H) A
  have hbound (X : Finset (ZMod n)) :
      (A.filter (fun T => EarCenters T.1 ∩ H = X)).card ≤
        Nat.card (ConditionFiber P Q H X) := by
    let S := A.filter (fun T => EarCenters T.1 ∩ H = X)
    let f : S → ConditionFiber P Q H X := fun T =>
      ⟨T.1.1, T.1.2.1, T.1.2.2.1, T.1.2.2.2.1, (mem_filter.mp T.2).2⟩
    have hf : Function.Injective f := by
      intro T U he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ConditionFiber P Q H X => x.1) he
    have : Finite (ConditionFiber P Q H X) := by unfold ConditionFiber; infer_instance
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective f hf
  unfold mass familyTraces
  rw [hc, Nat.cast_sum]
  apply sum_le_sum
  intro X _
  unfold weight
  exact_mod_cast hbound X

/-- A common ear of opposite conditioned members lies in the entire allowed support. -/
theorem shared_ear_mem_EK {P Q : Finset (ZMod n)}
    (T : WholeFiber P Q) (U : WholeFiber Q P) {i : ZMod n}
    (hiT : i ∈ EarCenters T.1) (hiU : i ∈ EarCenters U.1) :
    i ∈ E_K (P ∪ Q) := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_, ?_⟩
  · intro hi
    rcases mem_union.mp hi with hiP | hiQ
    · exact (disjoint_left.mp U.2.2.2.1) hiP hiU
    · exact (disjoint_left.mp T.2.2.2.1) hiQ hiT
  · intro k hk hc
    rcases mem_union.mp hk with hkP | hkQ
    · exact T.2.1.noncrossing (ear i) (mem_earCenters.mp hiT)
        (ear k) (mem_earCenters.mp (T.2.2.1 hkP)) hc
    · exact U.2.1.noncrossing (ear i) (mem_earCenters.mp hiU)
        (ear k) (mem_earCenters.mp (U.2.2.1 hkQ)) hc

/-- Full-ear intersections equal intersections of the two allowed traces. -/
theorem common_ears_eq_trace_inter {P Q : Finset (ZMod n)}
    (T : WholeFiber P Q) (U : WholeFiber Q P) :
    EarCenters T.1 ∩ EarCenters U.1 =
      (EarCenters T.1 ∩ E_K (P ∪ Q)) ∩ (EarCenters U.1 ∩ E_K (P ∪ Q)) := by
  ext i
  constructor
  · rintro hi
    obtain ⟨hiT, hiU⟩ := mem_inter.mp hi
    have hiE := shared_ear_mem_EK T U hiT hiU
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨hiT, hiE⟩, mem_inter.mpr ⟨hiU, hiE⟩⟩
  · intro hi
    exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hi).1).1,
      (mem_inter.mp (mem_inter.mp hi).2).1⟩

/-- Full-ear cross-intersection descends to traces of the complete allowed support. -/
theorem familyTraces_cross {P Q : Finset (ZMod n)}
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.1) (EarCenters U.1)) :
    CrossIntersecting (familyTraces (E_K (P ∪ Q)) A) (familyTraces (E_K (P ∪ Q)) B) := by
  classical
  intro X hX Y hY hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hX
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hY
  apply hc T hT U hU
  rw [disjoint_iff_inter_eq_empty, common_ears_eq_trace_inter T U]
  exact disjoint_iff_inter_eq_empty.mp hd

/-- Actual terminal compression for the original finite triangulation families.
The two mass bounds use separate complete P|Q and Q|P counts; no saturation,
realizability, positive total count, rank bound or normalization is assumed. -/
theorem exists_original_terminal_compression (hn : 14 ≤ n)
    (P Q : Finset (ZMod n)) (hK : (P ∪ Q).Nonempty)
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.1) (EarCenters U.1)) :
    ∃ H : Finset (ZMod n), ∃ C D : Finset (Finset (ZMod n)),
      H ⊆ E_K (P ∪ Q) ∧ Independent H ∧
      (∀ i ∈ H, ∀ j ∈ H, ¬Cross (ear i) (ear j)) ∧
      C ⊆ H.powerset ∧ D ⊆ H.powerset ∧ CrossIntersecting C D ∧
      RelativelyUpper H.powerset C ∧ RelativelyUpper H.powerset D ∧
      (A.card : ℝ) ≤ mass (weight P Q H) C ∧
      (B.card : ℝ) ≤ mass (weight Q P H) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty) ∧
      (A.Nonempty → B.Nonempty → H.Nonempty) := by
  classical
  let J := E_K (P ∪ Q)
  let S := deletionSystem hn P Q hK
  obtain ⟨H, C, D, hHJ, hterm, hC, hD, hCD, huC, huD, hw, hv, hnC, hnD⟩ :=
    exists_terminal_compression J S (familyTraces J A) (familyTraces J B)
      (familyTraces_feasible (by omega) J A) (familyTraces_feasible (by omega) J B)
      (familyTraces_cross A B hc)
  change Independent H at hterm
  change C ⊆ feasible H at hC
  change D ⊆ feasible H at hD
  change RelativelyUpper (feasible H) C at huC
  change RelativelyUpper (feasible H) D at huD
  change mass (weight P Q J) (familyTraces J A) ≤ mass (weight P Q H) C at hw
  change mass (weight Q P J) (familyTraces J B) ≤ mass (weight Q P H) D at hv
  rw [feasible_of_independent hterm] at hC hD huC huD
  have hneC : A.Nonempty → C.Nonempty := fun h => hnC (h.image _)
  have hneD : B.Nonempty → D.Nonempty := fun h => hnD (h.image _)
  refine ⟨H, C, D, hHJ, hterm, (independent_iff_noncrossing (by omega) H).mp hterm,
    hC, hD, hCD, huC, huD, (original_card_le_trace_mass P Q J A).trans hw,
    (original_card_le_trace_mass Q P J B).trans hv, hneC, hneD, ?_⟩
  intro hA hB
  obtain ⟨X, hX⟩ := hneC hA
  obtain ⟨Y, hY⟩ := hneD hB
  obtain ⟨i, hi, _⟩ := not_disjoint_iff.mp (hCD X hX Y hY)
  exact ⟨i, (mem_powerset.mp (hC hX)) hi⟩

end D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
