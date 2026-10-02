/- GID: D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The last site of the cyclic nearest-neighbor QES chain tends to infinity. -/

/-
proof_shape: result: content
escape_witness: result constructs the cyclic prefix identity with its wrap-around reciprocal
by induction, compares increasing solutions at a maximal coordinate difference, and derives
H_(N-1) < 2 R^2 on the live path to last-site divergence (public conclusion form (2)).
Prefix sums use Fin.partialSum ξ ⟨k, by omega⟩ directly; gapAt ξ k hk is the
zero-based consecutive gap ξ_k − ξ_(k−1). All auxiliary proofs, including uniqueness
and normalization, are local haves inside result.
Information-escape registration is paused under CLAUDE.md §3.9.
admission_basis: open-problem-resolution (#11858; Proved)
Direct frozen dependencies:
D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.Sites
  statement_id: sha256:a5dcbcd7d2b47b91ce4d9bd0f0fb522fd4ee770793909b04a982aaff41d84e91
The non-vacuity example additionally uses
D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.result
  statement_id: sha256:337a95eda33a97d3b25ec73163a820dec65aff6c6a1ab735c5bb504023817234
-/

import D5.S3.Quantum.SpinChains.NearestNeighborFreezingUniqueMinimum
import Mathlib.Data.Fin.Tuple.Take

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
open D5.S3.Quantum.SpinChains.NearestNeighborFreezingUniqueMinimum
namespace D5.S3.Quantum.SpinChains.NearestNeighborLastSiteDivergence

/-- The last-site divergence question for the cyclic site equations (6). -/
def claim : Prop :=
  ∀ B : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ξ : Fin N → ℝ, ∀ hN : 3 ≤ N,
    StrictMono ξ → Sites ξ → B < ξ ⟨N - 1, by omega⟩

/-- Consecutive gap between source sites `k` and `k+1`, used for `1 ≤ k < N`. -/
private def gapAt {N : ℕ} (ξ : Fin N → ℝ) (k : ℕ) (hk : k < N) : ℝ :=
  ξ ⟨k, hk⟩ - ξ ⟨k - 1, by omega⟩

/-- The last site exceeds every fixed real bound for all sufficiently long chains. -/
theorem result : claim := by
  have no_fixed {N : ℕ} (hN : 3 ≤ N) : ∀ i : Fin N, (finRotate N) i ≠ i := by
    intro i he
    have : NeZero N := ⟨by omega⟩
    simp only [finRotate_apply] at he
    have he' : (1 : Fin N) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using he)
    have hv := congrArg Fin.val he'
    simp [Nat.mod_eq_of_lt (by omega : 1 < N)] at hv
  have telescoping {N : ℕ} (hN : 3 ≤ N) {ξ : Fin N → ℝ} (hξ : StrictMono ξ)
      (s : Sites ξ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N) :
      Fin.partialSum ξ ⟨k, by omega⟩ =
        -(1 / (ξ ⟨N - 1, by omega⟩ - ξ ⟨0, by omega⟩)) - 1 / gapAt ξ k hkN := by
    let : NeZero N := ⟨by omega⟩
    have htel : ∀ m : ℕ, 1 ≤ m → ∀ hmN : m < N,
        Fin.partialSum ξ ⟨m, by omega⟩ =
          -(1 / (ξ ⟨N - 1, by omega⟩ - ξ ⟨0, by omega⟩)) - 1 / gapAt ξ m hmN := by
      intro m
      induction m with
      | zero => intro hm; omega
      | succ m ih =>
        intro hm1 hmN
        by_cases hm0 : m = 0
        · subst m
          change Fin.partialSum ξ (Fin.succ (⟨0, by omega⟩ : Fin N)) = _
          rw [Fin.partialSum_succ]
          change Fin.partialSum ξ (0 : Fin (N + 1)) + ξ ⟨0, by omega⟩ = _
          rw [Fin.partialSum_zero, zero_add]
          have h0 := s (⟨0, by omega⟩ : Fin N)
          simp [finRotate_apply, finRotate_symm_apply] at h0
          have hn1 : (-1 : Fin N) = ⟨N - 1, by omega⟩ := by
            obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
            apply Fin.ext
            exact Fin.coe_neg_one
          have hp1 : (1 : Fin N) = ⟨1, by omega⟩ := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (by omega : 1 < N)]
          rw [hn1, hp1] at h0
          change ξ (⟨0, by omega⟩ : Fin N) = _
          dsimp [gapAt]
          rw [show ξ 0 - ξ ⟨N - 1, by omega⟩ = -(ξ ⟨N - 1, by omega⟩ - ξ 0) by ring,
            show ξ 0 - ξ ⟨1, by omega⟩ = -(ξ ⟨1, by omega⟩ - ξ 0) by ring,
            inv_neg, inv_neg] at h0
          simpa only [one_div, Nat.sub_self, sub_eq_add_neg] using h0
        · have hm1' : 1 ≤ m := by omega
          have hmN' : m < N := by omega
          have hi := ih hm1' hmN'
          change Fin.partialSum ξ (Fin.succ (⟨m, hmN'⟩ : Fin N)) = _
          rw [Fin.partialSum_succ]
          change Fin.partialSum ξ (⟨m, by omega⟩ : Fin (N + 1)) + ξ ⟨m, hmN'⟩ = _
          rw [hi]
          have hk := s ⟨m, hmN'⟩
          simp [finRotate_apply, finRotate_symm_apply] at hk
          have hp : (⟨m, hmN'⟩ : Fin N) - 1 = ⟨m - 1, by omega⟩ := by
            apply Fin.ext
            rw [Fin.val_sub_one_of_ne_zero (by
              intro h
              have hz := congrArg Fin.val h
              simp at hz
              omega)]
          have hn : (⟨m, hmN'⟩ : Fin N) + 1 = ⟨m + 1, by omega⟩ := by
            apply Fin.ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < N), Nat.mod_eq_of_lt hmN]
          rw [hp, hn] at hk
          have hneg : ξ ⟨m, hmN'⟩ - ξ ⟨m + 1, hmN⟩ =
              -(ξ ⟨m + 1, hmN⟩ - ξ ⟨m, hmN'⟩) := by ring
          rw [hneg, inv_neg] at hk
          dsimp [gapAt]
          simp only [one_div]
          linarith
    exact htel k hk1 hkN
  have symmetry {N : ℕ} (hN : 3 ≤ N) {ξ : Fin N → ℝ}
      (hξ : StrictMono ξ) (sξ : Sites ξ) :
      ξ ⟨0, by omega⟩ = -ξ ⟨N - 1, by omega⟩ := by
    classical
    let : NeZero N := ⟨by omega⟩
    have uniq {x y : Fin N → ℝ} (hx : StrictMono x) (hy : StrictMono y)
        (sx : Sites x) (sy : Sites y) : x = y := by
      have le_sites {x y : Fin N → ℝ} (hx : StrictMono x) (hy : StrictMono y)
          (sx : Sites x) (sy : Sites y) : ∀ j, x j ≤ y j := by
        obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => x i - y i)
          ⟨0, Finset.mem_univ 0⟩
        have hcmp (j : Fin N) (hne : i ≠ j) :
            1 / (x i - x j) ≤ 1 / (y i - y j) := by
          have hs : 0 < (x i - x j) * (y i - y j) := by
            rcases lt_or_gt_of_ne hne with hij | hij
            · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx hij)) (sub_neg.mpr (hy hij))
            · exact mul_pos (sub_pos.mpr (hx hij)) (sub_pos.mpr (hy hij))
          have hm := hmax j (Finset.mem_univ j)
          have ha : x i - x j ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hs)).1
          have hb : y i - y j ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hs)).2
          have hsub : 1 / (x i - x j) - 1 / (y i - y j) ≤ 0 := by
            rw [one_div, one_div, inv_sub_inv ha hb]
            apply div_nonpos_of_nonpos_of_nonneg _ hs.le
            linarith
          linarith
        have hn := no_fixed hN i
        have hp : i ≠ (finRotate N).symm i := by
          intro he
          apply hn
          simpa using congrArg (finRotate N) he
        have h1 := hcmp ((finRotate N).symm i) hp
        have h2 := hcmp ((finRotate N) i) hn.symm
        have hi_le : x i ≤ y i := by rw [sx i, sy i]; linarith
        intro j
        have hm := hmax j (Finset.mem_univ j)
        linarith
      funext i
      exact le_antisymm (le_sites hx hy sx sy i) (le_sites hy hx sy sx i)
    let y : Fin N → ℝ := fun i => -ξ i.rev
    have hy : StrictMono y := by
      intro i j hij
      dsimp [y]
      exact neg_lt_neg (hξ (Fin.rev_strictAnti hij))
    have rev_next (i : Fin N) : ((finRotate N) i).rev = (finRotate N).symm i.rev := by
      simp only [finRotate_apply, finRotate_symm_apply]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
      rw [← Fin.last_sub, ← Fin.last_sub]
      abel
    have rev_prev (i : Fin N) : ((finRotate N).symm i).rev = (finRotate N) i.rev := by
      simp only [finRotate_apply, finRotate_symm_apply]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
      rw [← Fin.last_sub, ← Fin.last_sub]
      abel
    have sy : Sites y := by
      intro i
      have hs := sξ i.rev
      dsimp [y]
      rw [rev_prev, rev_next]
      have ha : -ξ i.rev - -ξ ((finRotate N) i.rev) =
          -(ξ i.rev - ξ ((finRotate N) i.rev)) := by ring
      have hb : -ξ i.rev - -ξ ((finRotate N).symm i.rev) =
          -(ξ i.rev - ξ ((finRotate N).symm i.rev)) := by ring
      rw [ha, hb, one_div, one_div, inv_neg, inv_neg]
      simp only [one_div] at hs
      linarith
    have he := uniq hξ hy sξ sy
    have he0 := congrFun he (0 : Fin N)
    dsimp [y] at he0
    have hrev : (0 : Fin N).rev = ⟨N - 1, by omega⟩ := by
      apply Fin.ext
      simp
    simpa [hrev] using he0
  have gap_bound {N : ℕ} (hN : 3 ≤ N) {ξ : Fin N → ℝ}
      (hξ : StrictMono ξ) (sξ : Sites ξ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N) :
      1 / (k : ℝ) < ξ ⟨N - 1, by omega⟩ * gapAt ξ k hkN := by
    let : NeZero N := ⟨by omega⟩
    let R := ξ ⟨N - 1, by omega⟩
    have hsym := symmetry hN hξ sξ
    have hR : 0 < R := by
      have hlt := hξ (show (⟨0, by omega⟩ : Fin N) < ⟨N - 1, by omega⟩ from by
        change 0 < N - 1
        omega)
      dsimp [R]
      linarith
    have hd : 0 < gapAt ξ k hkN := by
      apply sub_pos.mpr
      apply hξ
      change k - 1 < k
      omega
    have hp := telescoping hN hξ sξ k hk1 hkN
    have hlower : -(k : ℝ) * R ≤ Fin.partialSum ξ ⟨k, by omega⟩ := by
      calc
        -(k : ℝ) * R = ∑ _i : Fin k, -R := by simp
        _ ≤ Fin.partialSum ξ ⟨k, by omega⟩ := by
          change (∑ _i : Fin k, -R) ≤ ((List.ofFn ξ).take k).sum
          rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt hkN), List.sum_ofFn]
          apply Finset.sum_le_sum
          intro i hi
          have hx := hξ.monotone
            (show (⟨0, by omega⟩ : Fin N) ≤ Fin.castLE (Nat.le_of_lt hkN) i from Fin.zero_le _)
          dsimp [R]
          linarith
    have hwrap : 0 < 1 / (ξ ⟨N - 1, by omega⟩ - ξ ⟨0, by omega⟩) := by
      apply one_div_pos.mpr
      dsimp [R] at hR
      linarith
    have hrecip : 1 / gapAt ξ k hkN < (k : ℝ) * R := by linarith
    have hmul : 1 < ((k : ℝ) * R) * gapAt ξ k hkN := (div_lt_iff₀ hd).mp hrecip
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    apply (div_lt_iff₀ hkpos).mpr
    nlinarith
  have sum_gaps {N : ℕ} (hN : 3 ≤ N) (ξ : Fin N → ℝ) :
      (∑ i : Fin (N - 1), gapAt ξ (i.val + 1) (by omega)) =
        ξ ⟨N - 1, by omega⟩ - ξ ⟨0, by omega⟩ := by
    have hg : ∀ n : ℕ, ∀ hn : n < N,
        (∑ i : Fin n, gapAt ξ (i.val + 1) (by omega)) = ξ ⟨n, hn⟩ - ξ ⟨0, by omega⟩ := by
      intro n
      induction n with
      | zero => intro hn; simp
      | succ n ih =>
        intro hn
        rw [Fin.sum_univ_castSucc]
        have he : (∑ i : Fin n, gapAt ξ (i.castSucc.val + 1) (by omega)) =
            ∑ i : Fin n, gapAt ξ (i.val + 1) (by omega) := rfl
        rw [he, ih (by omega)]
        dsimp [gapAt]
        ring
    exact hg (N - 1) (by omega)
  have harmonic_bound {N : ℕ} (hN : 3 ≤ N) {ξ : Fin N → ℝ}
      (hξ : StrictMono ξ) (sξ : Sites ξ) :
      (∑ i ∈ Finset.range (N - 1), (1 / (i + 1) : ℝ)) < 2 * ξ ⟨N - 1, by omega⟩ ^ 2 := by
    rw [Finset.sum_range]
    have hsum : (∑ i : Fin (N - 1), (1 / ((i.val : ℝ) + 1))) <
        ∑ i : Fin (N - 1), ξ ⟨N - 1, by omega⟩ * gapAt ξ (i.val + 1) (by omega) := by
      apply Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      intro i hi
      simpa only [Nat.cast_add, Nat.cast_one] using
        gap_bound hN hξ sξ (i.val + 1) (by omega) (by omega)
    rw [← Finset.mul_sum, sum_gaps hN ξ, symmetry hN hξ sξ] at hsum
    nlinarith
  intro B
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (Filter.eventually_gt_atTop (2 * B ^ 2)))
  refine ⟨m + 1, ?_⟩
  intro N hNm ξ hN hξ sξ
  have hb := harmonic_bound hN hξ sξ
  have hh := hm (N - 1) (by omega)
  have hsym := symmetry hN hξ sξ
  have hR : 0 < ξ ⟨N - 1, by omega⟩ := by
    have hlt := hξ (show (⟨0, by omega⟩ : Fin N) < ⟨N - 1, by omega⟩ from by
      change 0 < N - 1
      omega)
    linarith
  by_contra h
  have hle : ξ ⟨N - 1, by omega⟩ ≤ B := le_of_not_gt h
  have hB : 0 ≤ B := le_trans hR.le hle
  have hsq : ξ ⟨N - 1, by omega⟩ ^ 2 ≤ B ^ 2 := by nlinarith
  nlinarith

example (N : ℕ) (hN : 3 ≤ N) : ∃ ξ : Fin N → ℝ, StrictMono ξ ∧ Sites ξ := by
  obtain ⟨ξ, hξ, sξ, hmin⟩ := NearestNeighborFreezingUniqueMinimum.result N hN
  exact ⟨ξ, hξ, sξ⟩

#check Fin.partialSum
#check gapAt
#print axioms result

end D5.S3.Quantum.SpinChains.NearestNeighborLastSiteDivergence
