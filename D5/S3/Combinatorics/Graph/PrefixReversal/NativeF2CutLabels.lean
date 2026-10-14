/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: F2 cuts have exact generator classifications and selected terminal labels. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleTerminalEdge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleTerminalEdge
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification

private theorem first_a_cut {m : ℕ} (hm : 4 ≤ m) :
    NativeCoreSplicing.cutStart (.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2)) = 1 ∧
      cutGenerator (.inl ⟨m - 1, by omega⟩ : Fin m ⊕ Fin (m - 2)) = a m := by
  simp [NativeCoreSplicing.cutStart, cutGenerator, (by omega : m - 2 ≤ m - 1)]

private theorem second_a_cut {m : ℕ} (hm : 4 ≤ m) :
    NativeCoreSplicing.cutStart (.inl ⟨m - 2, by omega⟩ : Fin m ⊕ Fin (m - 2)) =
        Equiv.swap (0 : Fin (m + 1)) (Fin.last m) ∧
      cutGenerator (.inl ⟨m - 2, by omega⟩ : Fin m ⊕ Fin (m - 2)) = a m := by
  constructor
  · simp only [NativeCoreSplicing.cutStart, Fin.val_mk, if_neg (by omega : m - 2 ≠ m - 1),
      tCircleAnchor, gapAnchor]
    simpa only [tHalfWord, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, List.prod_flatten, List.map_replicate, List.prod_replicate] using
      native_t_halfword_swap (by omega : 3 ≤ m)
  · simp [cutGenerator]

private theorem a_ne_b {m : ℕ} (hm : 4 ≤ m) : a m ≠ b m := by
  intro he
  have hv := congrArg (fun f : Configuration m => (f (Fin.last m)).val) he
  simp only [a_apply, Fin.val_rev, Fin.val_last, Nat.sub_self, b_last] at hv
  omega

private theorem edge_generator_unique {m : ℕ} (x y g h : Configuration m)
    (hg : g * g = 1) (he : s(x, x * g) = s(y, y * h)) : g = h := by
  rcases Sym2.eq_iff.mp he with ⟨hxy, hend⟩ | ⟨hxy, hend⟩
  · subst y
    exact mul_left_cancel hend
  · rw [← hend] at hxy
    have hgh : g * h = 1 := mul_left_cancel (by
      simpa only [mul_assoc, mul_one] using hxy.symm)
    have ht := congrArg (g * ·) hgh
    simpa only [← mul_assoc, hg, one_mul, mul_one] using ht.symm

/-- Among all actual a edges the complete F2 cut set consists of exactly
the two literal core cuts, with normalized actual permutation endpoints. -/
theorem native_f2_a_cut_classification {m : ℕ} (hm : 4 ≤ m) (x : Configuration m) :
    F2DeletedEdge m s(x, x * a m) ↔
      s(x, x * a m) = s(1, a m) ∨
        s(x, x * a m) = s(Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
          Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * a m) := by
  constructor
  · rintro (⟨p, he⟩ | ⟨j, i, he⟩)
    · have ha := edge_generator_unique x (NativeCoreSplicing.cutStart p) (a m) (cutGenerator p) (a_sq m) he
      cases p with
      | inl i =>
        have hi : m - 2 ≤ i.val := by
          by_contra hn
          have hb : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = b m := by
            simp only [cutGenerator, if_neg hn]
          exact a_ne_b hm (ha.trans hb)
        have hcases : i.val = m - 1 ∨ i.val = m - 2 := by have hlt := i.isLt; omega
        rcases hcases with hi | hi
        · have hie : i = ⟨m - 1, by omega⟩ := Fin.ext hi
          rw [hie] at he
          exact Or.inl (by simpa only [(first_a_cut hm).1, (first_a_cut hm).2, one_mul] using he)
        · have hie : i = ⟨m - 2, by omega⟩ := Fin.ext hi
          rw [hie] at he
          exact Or.inr (by simpa only [(second_a_cut hm).1, (second_a_cut hm).2] using he)
      | inr j => exact (a_ne_b hm ha).elim
    · exact (a_ne_b hm (edge_generator_unique x _ (a m) (b m) (a_sq m) he)).elim
  · rintro (he | he)
    · refine Or.inl ⟨.inl ⟨m - 1, by omega⟩, ?_⟩
      simpa only [(first_a_cut hm).1, (first_a_cut hm).2, one_mul] using he
    · refine Or.inl ⟨.inl ⟨m - 2, by omega⟩, ?_⟩
      simpa only [(second_a_cut hm).1, (second_a_cut hm).2] using he

private theorem contact_gap_last {m : ℕ} (hm : 4 ≤ m) (j : Fin (m - 2)) (i : Fin m) :
    gapAnchor (contactAnchor j) i (Fin.last m) = 0 := by
  have hp : ((b m * c m) ^ i.val) (Fin.last m) = Fin.last m := by
    apply Fin.ext
    simp only [native_bc_pow_val (by omega : 2 ≤ m), Fin.val_last,
      lt_self_iff_false, if_false]
  rw [gapAnchor, Equiv.Perm.mul_apply, hp]
  apply Fin.ext
  change (if m < j.val + 1 then m + 1 else if m = j.val + 1 then m
    else if m < m then m else 0) = 0
  have hj := j.isLt
  rw [if_neg (by omega : ¬ m < j.val + 1), if_neg (by omega : m ≠ j.val + 1),
    if_neg (by omega : ¬ m < m)]

private theorem b_edge_geometry {m : ℕ} (z x : Configuration m)
    (he : s(x, x * b m) = s(z, z * b m)) :
    Circle z x ∧ x (Fin.last m) = z (Fin.last m) := by
  have hv : x ∈ s(z, z * b m) := he ▸ (by simp)
  refine ⟨native_circle_edge_endpoint z x _
    ⟨z, b m, Or.inl rfl, Or.inr rfl, rfl⟩ hv, ?_⟩
  rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · rfl
  · rw [Equiv.Perm.mul_apply, b_last]

/-- An actual b edge is a literal F2 cut exactly at the selected terminal
label in a lower/upper T circle or a remaining full supplier star. -/
theorem native_f2_b_cut_classification {m : ℕ} (hm : 4 ≤ m) (x : Configuration m) :
    F2DeletedEdge m s(x, x * b m) ↔
      (∃ j : Fin (m - 2), Circle (lowerPort j) x ∧ x (Fin.last m) = 0) ∨
      (∃ j : Fin (m - 2), Circle (upperPort j) x ∧ x (Fin.last m) = Fin.last m) ∨
      ∃ j : Fin (m - 2), SupplierStar (contactAnchor j) x ∧ x (Fin.last m) = 0 := by
  constructor
  · rintro (⟨p, he⟩ | ⟨j, i, he⟩)
    · have hg : cutGenerator p = b m :=
        (edge_generator_unique x (NativeCoreSplicing.cutStart p) (b m)
          (cutGenerator p) (Equiv.ext (fun i =>
            PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
              (L := m) (by omega) i)) he).symm
      cases p with
      | inl i =>
        have hi : i.val < m - 2 := by
          by_contra hn
          have ha : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = a m := by
            simp only [cutGenerator, if_pos (by omega : m - 2 ≤ i.val)]
          exact a_ne_b hm (ha.symm.trans hg)
        let j : Fin (m - 2) := ⟨i.val, hi⟩
        have hs : NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) =
            lowerPort j := by
          simp only [NativeCoreSplicing.cutStart, if_neg (by omega : i.val ≠ m - 1),
            tCircleAnchor, gapAnchor, lowerPort, j]
        rw [hg, hs] at he
        have hc := b_edge_geometry (lowerPort j) x he
        exact Or.inl ⟨j, hc.1, hc.2.trans (native_lower_last hm j)⟩
      | inr j =>
        change s(x, x * b m) = s(upperPort j, upperPort j * b m) at he
        have hc := b_edge_geometry (upperPort j) x he
        exact Or.inr (Or.inl ⟨j, hc.1, hc.2.trans (native_upper_last hm j)⟩)
    · have hc := b_edge_geometry (gapAnchor (contactAnchor j) i) x he
      exact Or.inr (Or.inr ⟨j,
        (native_star_circle_partition (by omega : 3 ≤ m) (contactAnchor j) x).mpr
          ⟨i, hc.1⟩,
        hc.2.trans (contact_gap_last hm j i)⟩)
  · rintro (⟨j, hc, hl⟩ | ⟨j, hc, hl⟩ | ⟨j, hc, hl⟩)
    · have he := native_circle_terminal_b_edge (by omega : 3 ≤ m) (lowerPort j) x hc
        (hl.trans (native_lower_last hm j).symm)
      let i : Fin m := ⟨j.val, by have hj := j.isLt; omega⟩
      have hs : NativeCoreSplicing.cutStart (.inl i : Fin m ⊕ Fin (m - 2)) =
          lowerPort j := by
        have hj := j.isLt
        simp only [NativeCoreSplicing.cutStart, i, Fin.val_mk,
          if_neg (by omega : j.val ≠ m - 1), tCircleAnchor, gapAnchor, lowerPort]
      have hg : cutGenerator (.inl i : Fin m ⊕ Fin (m - 2)) = b m := by
        simp only [cutGenerator, i, Fin.val_mk, if_neg (Nat.not_le.mpr j.isLt)]
      exact Or.inl ⟨.inl i, by simpa only [hs, hg] using he⟩
    · have he := native_circle_terminal_b_edge (by omega : 3 ≤ m) (upperPort j) x hc
        (hl.trans (native_upper_last hm j).symm)
      exact Or.inl ⟨.inr j, he⟩
    · obtain ⟨i, hi⟩ := (native_star_circle_partition (by omega : 3 ≤ m)
        (contactAnchor j) x).mp hc
      exact Or.inr ⟨j, i, native_circle_terminal_b_edge (by omega : 3 ≤ m) _ x hi
        (hl.trans (contact_gap_last hm j i).symm)⟩

#print axioms native_f2_b_cut_classification

#print axioms native_f2_a_cut_classification

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
