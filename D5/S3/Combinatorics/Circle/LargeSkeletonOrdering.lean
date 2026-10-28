/- GID: D5/S3/Combinatorics/Circle/LargeSkeletonOrdering
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/LargeSkeletonOrdering
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.List]
   utility: none
   digest: Two-sided retained LARGE boundaries construct an order of every complete SMALL batch. -/
module
public import D5.S3.Combinatorics.Circle.SmallStepOrdering

/-! # Ordering the complete SMALL batches of a retained LARGE skeleton

Weights are arbitrary integers on physical labels. Only the prescribed start,
final endpoint and both sides of each LARGE occurrence are constrained. The
retained word need not itself stay in the strip. Complete SMALL batches are
permuted independently, preserving every occurrence and the literal LARGE list.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.LargeSkeletonOrdering
open SourceWidth SmallStepOrdering

/-- Construct a strip order by permuting complete SMALL batches between retained
LARGE occurrences. The boundary hypotheses concern the retained word R at the
prescribed start u, including BOTH departure and arrival at every LARGE. No old
strip order, constant shift, distinctness or source geometry is assumed. -/
theorem exists_order_preserving_large {α : Type*} (f : α → ℤ)
    (Q C : ℤ) (hQ : 0 < Q) (hwidth : 2 * Q - 2 ≤ C)
    (R : List α) (u : ℤ)
    (hstart : 0 ≤ u ∧ u ≤ C)
    (hend : 0 ≤ u + (R.map f).sum ∧ u + (R.map f).sum ≤ C)
    (hboundary : ∀ (R0 : List α) (i : α) (R1 : List α),
      R = R0 ++ [i] ++ R1 → Q ≤ |f i| →
      (0 ≤ u + (R0.map f).sum ∧ u + (R0.map f).sum ≤ C) ∧
      (0 ≤ u + (R0.map f).sum + f i ∧ u + (R0.map f).sum + f i ≤ C)) :
    ∃ E : List α, E.Perm R ∧
      E.filter (fun i => decide (Q ≤ |f i|)) =
        R.filter (fun i => decide (Q ≤ |f i|)) ∧
      InStrip f C u E := by
  classical
  have compatible (L : List α) (hL : ∀ i ∈ L, |f i| < Q) :
      ∀ p ∈ L, ∀ n ∈ L, 0 < f p → f n < 0 → f p - f n ≤ C := by
    intro p hp n hn hp0 hn0
    have hpQ := hL p hp
    have hnQ := hL n hn
    rw [abs_of_pos hp0] at hpQ
    rw [abs_of_neg hn0] at hnQ
    omega
  have filterSmall (L : List α) (hL : ∀ i ∈ L, |f i| < Q) :
      L.filter (fun i => decide (Q ≤ |f i|)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi hdecide
    exact (not_le.mpr (hL i hi)) (of_decide_eq_true hdecide)
  -- The sole scan carries the COMPLETE unfinished SMALL batch T.
  have scan (B T : List α) (h : ℤ)
      (hT : ∀ i ∈ T, |f i| < Q)
      (hbeg : 0 ≤ h ∧ h ≤ C)
      (hfinal : 0 ≤ h + ((T ++ B).map f).sum ∧
        h + ((T ++ B).map f).sum ≤ C)
      (hlarge : ∀ (B0 : List α) (i : α) (B1 : List α),
        T ++ B = B0 ++ [i] ++ B1 → Q ≤ |f i| →
        (0 ≤ h + (B0.map f).sum ∧ h + (B0.map f).sum ≤ C) ∧
        (0 ≤ h + (B0.map f).sum + f i ∧
          h + (B0.map f).sum + f i ≤ C)) :
      ∃ E : List α, E.Perm (T ++ B) ∧
        E.filter (fun i => decide (Q ≤ |f i|)) =
          (T ++ B).filter (fun i => decide (Q ≤ |f i|)) ∧
        InStrip f C h E := by
    induction B generalizing T h with
    | nil =>
      have hfinal' : 0 ≤ h + (T.map f).sum ∧ h + (T.map f).sum ≤ C := by
        simpa only [List.append_nil] using hfinal
      obtain ⟨E, hE, hsE⟩ := exists_order_between f T C h
        hbeg hfinal' (compatible T hT)
      have hEsmall : ∀ i ∈ E, |f i| < Q :=
        fun i hi => hT i (hE.mem_iff.mp hi)
      refine ⟨E, by simpa using hE, ?_, hsE⟩
      simp only [List.append_nil, filterSmall E hEsmall, filterSmall T hT]
    | cons i B ih =>
      by_cases hi : Q ≤ |f i|
      · have hgate := hlarge T i B
          (by simp only [List.append_assoc, List.cons_append, List.nil_append]) hi
        obtain ⟨E, hE, hsE⟩ := exists_order_between f T C h
          hbeg hgate.1 (compatible T hT)
        have hmE : (E.map f).sum = (T.map f).sum := (hE.map f).sum_eq
        have hfinal' :
            0 ≤ (h + (T.map f).sum + f i) + (([] ++ B).map f).sum ∧
            (h + (T.map f).sum + f i) + (([] ++ B).map f).sum ≤ C := by
          simpa only [List.nil_append, List.map_append, List.map_cons,
            List.sum_append, List.sum_cons, add_assoc] using hfinal
        have hlarge' : ∀ (B0 : List α) (j : α) (B1 : List α),
            [] ++ B = B0 ++ [j] ++ B1 → Q ≤ |f j| →
            (0 ≤ (h + (T.map f).sum + f i) + (B0.map f).sum ∧
              (h + (T.map f).sum + f i) + (B0.map f).sum ≤ C) ∧
            (0 ≤ (h + (T.map f).sum + f i) + (B0.map f).sum + f j ∧
              (h + (T.map f).sum + f i) + (B0.map f).sum + f j ≤ C) := by
          intro B0 j B1 hsplit hj
          have hsplit' : B = B0 ++ [j] ++ B1 := by simpa using hsplit
          have hb := hlarge (T ++ [i] ++ B0) j B1 (by
            rw [hsplit']
            simp only [List.append_assoc, List.cons_append, List.nil_append]) hj
          simpa only [List.map_append, List.map_cons, List.map_nil,
            List.sum_append, List.sum_cons, List.sum_nil, add_zero, add_assoc] using hb
        obtain ⟨L, hL, hLf, hsL⟩ := ih [] (h + (T.map f).sum + f i)
          (by simp) hgate.2 hfinal' hlarge'
        have hL' : L.Perm B := by simpa only [List.nil_append] using hL
        have hLf' : L.filter (fun j => decide (Q ≤ |f j|)) =
            B.filter (fun j => decide (Q ≤ |f j|)) := by
          simpa only [List.nil_append] using hLf
        have hEsmall : ∀ j ∈ E, |f j| < Q :=
          fun j hj => hT j (hE.mem_iff.mp hj)
        have hsGate : InStrip f C (h + (E.map f).sum) (i :: L) := by
          rw [hmE]
          exact ⟨hgate.1.1, hgate.1.2, hsL⟩
        refine ⟨E ++ i :: L, hE.append (hL'.cons i), ?_,
          inStrip_append hsE hsGate⟩
        simp [List.filter_append, filterSmall E hEsmall, filterSmall T hT, hi, hLf']
      · have hiSmall : |f i| < Q := lt_of_not_ge hi
        have hT' : ∀ j ∈ T ++ [i], |f j| < Q := by
          intro j hj
          rcases List.mem_append.mp hj with hj | hj
          · exact hT j hj
          · simpa only [List.mem_singleton.mp hj] using hiSmall
        have heq : T ++ i :: B = (T ++ [i]) ++ B := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        obtain ⟨E, hE, hEf, hsE⟩ := ih (T ++ [i]) h hT' hbeg
          (by simpa only [← heq] using hfinal) (by
            intro B0 j B1 hsplit hj
            exact hlarge B0 j B1 (heq.trans hsplit) hj)
        exact ⟨E, by simpa only [← heq] using hE,
          by simpa only [← heq] using hEf, hsE⟩
  exact scan R [] u (by simp) hstart (by simpa using hend) (by
    intro R0 i R1 hsplit hi
    exact hboundary R0 i R1 (by simpa using hsplit) hi)

end D5.S3.Combinatorics.Circle.LargeSkeletonOrdering
