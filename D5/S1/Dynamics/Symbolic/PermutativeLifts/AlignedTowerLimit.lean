/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact aligned tower limits with periodic coordinates and a balanced realization. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.EqualLengthTiling
import D5.S1.Dynamics.Symbolic.PermutativeLifts.TwoRunRefinement
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords

/-! # Aligned tower limits

Compact aligned images give actual simultaneous tilings. Common prefixes and
suffixes of unbounded length make every physical coordinate periodic. This
property permits periodic points; nonperiodicity is a separate obligation. -/

set_option autoImplicit false

open Set

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- Each coordinate has a positive period, with all positive and negative
integer multiples allowed. This does not assert nonperiodicity of the point. -/
def HasPeriodicCoordinates (y : ℤ → Bool) : Prop :=
  ∀ i : ℤ, ∃ p : ℕ, 0 < p ∧ ∀ k : ℤ, y (i + k * (p : ℤ)) = y i

namespace AlignedTowerLimit

open TwoRunRefinement

/-- Nesting concerns visible images of actual origin-aligned tilings; no
compatibility, recognizability, or continuity of chosen refinements is needed. -/
theorem aligned_intersection_nonempty (W : ℕ → Bool → List Bool)
    (hW : ∀ n a, 0 < (W n a).length)
    (hnest : ∀ n, alignedConfigurations (W (n + 1)) ⊆ alignedConfigurations (W n)) :
    (⋂ n : ℕ, alignedConfigurations (W n)).Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => alignedConfigurations (W n)) hnest
    (fun n => (alignedConfigurations_compact_nonempty (W n) (hW n)).2)
    (alignedConfigurations_compact_nonempty (W 0) (hW 0)).1
    (fun n => (alignedConfigurations_compact_nonempty (W n) (hW n)).1.isClosed)

private theorem shared_column (V W : Bool → List Bool) (l L : ℕ)
    (hV : ∀ a, (V a).length = l) (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (hprefix : ∀ a, V false <+: W a) (hsuffix : ∀ a, V true <:+ W a)
    (x : MarkedTiling W) (hzero : (x.1 0).2.val = 0)
    (i : ℤ) (hi : i.natAbs < l) :
    (W false).get ⟨(x.1 i).2.val, by simpa only [hW] using (x.1 i).2.isLt⟩ =
      (W true).get ⟨(x.1 i).2.val, by simpa only [hW] using (x.1 i).2.isLt⟩ := by
  have hle : l ≤ L := by
    simpa only [hV, hW] using (hprefix false).length_le
  have hphase := tiled_offset_aligned W L hW hL x hzero i
  cases i with
  | ofNat m =>
    have hm : m < l := hi
    have hmL : (m : ℤ) < (L : ℤ) := by omega
    simp only [Int.ofNat_eq_natCast] at hphase ⊢
    rw [Int.emod_eq_of_lt (by omega) hmL] at hphase
    have hoff : (x.1 (m : ℤ)).2.val = m := by omega
    have hf := (hprefix false).getElem (show m < (V false).length by rw [hV]; exact hm)
    have ht := (hprefix true).getElem (show m < (V false).length by rw [hV]; exact hm)
    simpa only [List.get_eq_getElem, hoff] using hf.symm.trans ht
  | negSucc m =>
    have hm : m < l := by simpa only [Int.natAbs_negSucc] using (Nat.lt_trans (Nat.lt_succ_self m) hi)
    have hmL : (m : ℤ) < (L : ℤ) := by omega
    rw [Int.negSucc_emod m (by omega), Int.emod_eq_of_lt (by omega) hmL] at hphase
    let j : ℕ := l - 1 - m
    have hj : j < (V true).length := by dsimp [j]; rw [hV]; omega
    have hoff : (x.1 (Int.negSucc m)).2.val = L - l + j := by dsimp [j]; omega
    have hf := (hsuffix false).getElem hj
    have ht := (hsuffix true).getElem hj
    simpa only [List.get_eq_getElem, hV, hW, hoff] using hf.symm.trans ht

/-- Unbounded common prefixes and suffixes cover every signed coordinate.
The period at a coordinate is the length of a sufficiently high actual tile. -/
theorem has_periodic_coordinates_of_aligned_tower
    (W : ℕ → Bool → List Bool) (L : ℕ → ℕ)
    (hW : ∀ n a, (W n a).length = L n) (hL : ∀ n, 0 < L n)
    (hprefix : ∀ n a, W n false <+: W (n + 1) a)
    (hsuffix : ∀ n a, W n true <:+ W (n + 1) a)
    (hunbounded : ∀ r : ℕ, ∃ n, r < L n)
    (y : ℤ → Bool) (hy : ∀ n, y ∈ alignedConfigurations (W n)) :
    HasPeriodicCoordinates y := by
  intro i
  obtain ⟨n, hn⟩ := hunbounded i.natAbs
  obtain ⟨x, hx, rfl⟩ := hy (n + 1)
  refine ⟨L (n + 1), hL (n + 1), ?_⟩
  exact tiled_common_column_periodic (W (n + 1)) (L (n + 1)) (hW (n + 1))
    (hL (n + 1)) x i
    (shared_column (W n) (W (n + 1)) (L n) (L (n + 1)) (hW n) (hW (n + 1))
      (hL (n + 1)) (hprefix n) (hsuffix n) x hx i hn)

/-- A compact aligned tower has an actual limit with periodic coordinates.
Membership gives an actual marked tiling at every level, without a decoder. -/
theorem exists_aligned_periodic_point
    (W : ℕ → Bool → List Bool) (L : ℕ → ℕ)
    (hW : ∀ n a, (W n a).length = L n) (hL : ∀ n, 0 < L n)
    (hnest : ∀ n, alignedConfigurations (W (n + 1)) ⊆ alignedConfigurations (W n))
    (hprefix : ∀ n a, W n false <+: W (n + 1) a)
    (hsuffix : ∀ n a, W n true <:+ W (n + 1) a)
    (hunbounded : ∀ r : ℕ, ∃ n, r < L n) :
    ∃ y : ℤ → Bool, (∀ n, y ∈ alignedConfigurations (W n)) ∧ HasPeriodicCoordinates y := by
  obtain ⟨y, hy⟩ := aligned_intersection_nonempty W
    (fun n a => by rw [hW]; exact hL n) hnest
  have hy' := Set.mem_iInter.mp hy
  exact ⟨y, hy', has_periodic_coordinates_of_aligned_tower W L hW hL
    hprefix hsuffix hunbounded y hy'⟩

end AlignedTowerLimit

namespace Balanced

/-- An actual binary configuration tiled at every balanced level, with the
origin at a boundary and every signed coordinate periodic. Nonperiodicity is
not part of this type and must be supplied independently for a Toeplitz point. -/
noncomputable def alignedPeriodicPoint :
    {y : ℤ → Bool // (∀ n, y ∈ TwoRunRefinement.alignedConfigurations (balancedWord n)) ∧
      HasPeriodicCoordinates y} := by
  have hnest : ∀ n, TwoRunRefinement.alignedConfigurations (balancedWord (n + 1)) ⊆
      TwoRunRefinement.alignedConfigurations (balancedWord n) := by
    intro n
    have hword : balancedWord (n + 1) = TwoRunRefinement.word (balancedWord n)
        (fun a => (if a then 1 else 2) * (n + 1).factorial)
        (fun a => (if a then 2 else 1) * (n + 1).factorial) := by
      funext a
      rfl
    rw [hword]
    exact TwoRunRefinement.alignedConfigurations_subset (balancedWord n)
      (fun a => by rw [balancedWord_length]; exact height_pos n) _ _
      (fun a => by cases a <;> simp [Nat.factorial_pos])
      (fun a => by cases a <;> simp [Nat.factorial_pos])
  have h := AlignedTowerLimit.exists_aligned_periodic_point balancedWord height
    balancedWord_length height_pos hnest balancedWord_prefix_false balancedWord_suffix_true
    (fun r => ⟨r, height_lower_bound r⟩)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Balanced

end D5.S1.Dynamics.Symbolic.PermutativeLifts
