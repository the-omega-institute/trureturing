/- GID: D5/S3/Combinatorics/Kozlov/LatticeCount
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:literal-kozlov-lattice-count)
   anchors: []
   utility: none
   digest: Literal lattice points of a dilation are counted by chained equal-shift tuples. -/

import D5.S3.Combinatorics.Kozlov.ConvexHull

set_option autoImplicit false

open Finset Matrix
open scoped BigOperators Pointwise

namespace D5.S3.Combinatorics.Kozlov

variable {n : ℕ}

abbrev ZVector (n : ℕ) := Fin (n + 1) → ℤ

def intVector (f : FVector n) : ZVector n := fun j => f j

def castIntVector (f : ZVector n) : RVector n := fun j => f j

def dilateLattice (n r : ℕ) : Set (ZVector n) :=
  {z | castIntVector z ∈ (r : ℝ) • convexHull ℝ (realVectors n)}

theorem cast_intVector (f : FVector n) : castIntVector (intVector f) = realVector f := by
  funext j
  exact Int.cast_natCast _

def natDilation (hn : 1 ≤ n) (r : ℕ) : Set (FVector n) :=
  {x | Normalized hn r (realVector x)}

theorem dilateLattice_eq_image (hn : 1 ≤ n) {r : ℕ} (hr : 0 < r) :
    dilateLattice n r = intVector '' natDilation hn r := by
  ext z
  change (castIntVector z ∈ (r : ℝ) • convexHull ℝ (realVectors n)) ↔ _
  rw [mem_dilate_iff hn hr]
  constructor
  · intro h
    let x : FVector n := fun j => (z j).toNat
    have he : intVector x = z := by
      funext j
      apply Int.toNat_of_nonneg
      have hh := h.nonneg j
      change (0 : ℝ) ≤ (z j : ℝ) at hh
      exact_mod_cast hh
    refine ⟨x, ?_, he⟩
    change Normalized hn r (realVector x)
    rw [← cast_intVector, he]
    exact h
  · rintro ⟨x, hx, rfl⟩
    rwa [cast_intVector]

theorem normalized_one_bounded (hn : 1 ≤ n) {f : FVector n}
    (h : Normalized hn 1 (realVector f)) : Bounded f := by
  intro j
  have h' := (div_le_iff₀ (cap_pos_real j)).mp (h.ratio_le j)
  simp only [realVector, Nat.cast_one, one_mul] at h'
  exact_mod_cast h'

theorem normalized_one_fixed (hn : 1 ≤ n) {f : FVector n}
    (h : Normalized hn 1 (realVector f)) : Fixed hn f := by
  have h0 : (f 0 : ℝ) = 1 := by simpa [realVector] using h.zero
  have h1 : (f (firstDegree hn) : ℝ) = (n : ℝ) := by simpa [realVector] using h.one
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

noncomputable def latticeVectors (hn : 1 ≤ n) : Finset (FVector n) := by
  classical
  exact (Fintype.piFinset fun j : Fin (n + 1) => range (cap j + 1)).filter
    (fun f => Normalized hn 1 (realVector f))

@[simp] theorem mem_latticeVectors (hn : 1 ≤ n) {f : FVector n} :
    f ∈ latticeVectors hn ↔ Normalized hn 1 (realVector f) := by
  classical
  simp only [latticeVectors, mem_filter, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
  exact ⟨And.right, fun h => ⟨normalized_one_bounded hn h, h⟩⟩

theorem skeleton_mem_latticeVectors (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    skeleton n k ∈ latticeVectors hn := by
  apply (mem_latticeVectors hn).mpr
  apply (lymChain_iff_normalized hn).mp
  rw [← hull_eq_lymChain hn]
  exact subset_convexHull ℝ _ ⟨_, skeleton_mem_SnF hk, rfl⟩

theorem lattice_terminal (hn : 1 ≤ n) {f : FVector n} (hf : f ∈ latticeVectors hn)
    (ht : top f = (n : ℤ)) : f = skeleton n n := by
  have hf' := (mem_latticeVectors hn).mp hf
  have hpos : 0 < f (Fin.last n) := by
    unfold top at ht
    split at ht
    · rename_i hne
      let j := (univ.filter fun j : Fin (n + 1) => 0 < f j).max' hne
      have hj : j = Fin.last n := Fin.ext (by
        change (j.val : ℤ) = (n : ℤ) at ht
        simp only [Fin.val_last]
        omega)
      rw [← hj]
      exact (mem_filter.mp (max'_mem _ hne)).2
    · omega
  have hlast : f (Fin.last n) = 1 := by
    have hb := normalized_one_bounded hn hf' (Fin.last n)
    simp [cap] at hb
    omega
  funext j
  have hle := hf'.anti (Fin.le_last j)
  change (f (Fin.last n) : ℝ) / _ ≤ (f j : ℝ) / (cap j : ℝ) at hle
  simp only [hlast, cap, Fin.val_last, Nat.choose_self, Nat.cast_one, div_one] at hle
  have hge := (le_div_iff₀ (cap_pos_real j)).mp hle
  rw [one_mul] at hge
  have hge' : cap j ≤ f j := by exact_mod_cast hge
  rw [show skeleton n n j = cap j by simp [skeleton, show j.val ≤ n by omega]]
  exact (normalized_one_bounded hn hf' j).antisymm hge'

private def clipped (x : FVector n) : FVector n := fun j => min (cap j) (x j)

private def remainder (x : FVector n) : FVector n := fun j => x j - cap j

private theorem ratio_clipped (x : FVector n) (j : Fin (n + 1)) :
    realVector (clipped x) j / (cap j : ℝ) = min 1 (realVector x j / (cap j : ℝ)) := by
  change ((min (cap j) (x j) : ℕ) : ℝ) / (cap j : ℝ) = min 1 ((x j : ℝ) / (cap j : ℝ))
  by_cases h : x j ≤ cap j
  · rw [min_eq_right h, min_eq_right]
    apply (div_le_iff₀ (cap_pos_real j)).mpr
    simpa only [one_mul] using (show (x j : ℝ) ≤ (cap j : ℝ) by exact_mod_cast h)
  · have h' := le_of_not_ge h
    rw [min_eq_left h', div_self (cap_pos_real j).ne', min_eq_left]
    apply (le_div_iff₀ (cap_pos_real j)).mpr
    simpa only [one_mul] using (show (cap j : ℝ) ≤ (x j : ℝ) by exact_mod_cast h')

private theorem ratio_remainder (x : FVector n) (j : Fin (n + 1)) :
    realVector (remainder x) j / (cap j : ℝ) =
      max 0 (realVector x j / (cap j : ℝ) - 1) := by
  change (((x j - cap j : ℕ) : ℝ) / (cap j : ℝ)) =
    max 0 ((x j : ℝ) / (cap j : ℝ) - 1)
  by_cases h : cap j ≤ x j
  · rw [Nat.cast_sub h, sub_div, div_self (cap_pos_real j).ne', max_eq_right]
    apply sub_nonneg.mpr
    exact (le_div_iff₀ (cap_pos_real j)).mpr (by simpa using (show (cap j : ℝ) ≤ x j by exact_mod_cast h))
  · have h' := le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, zero_div, max_eq_left]
    apply sub_nonpos.mpr
    exact (div_le_iff₀ (cap_pos_real j)).mpr (by simpa using (show (x j : ℝ) ≤ cap j by exact_mod_cast h'))

private theorem head_coordinates (hn : 1 ≤ n) {r : ℕ} {x : FVector n}
    (h : Normalized hn r (realVector x)) :
    x 0 = r ∧ x (firstDegree hn) = r * n := by
  have h0 : (x 0 : ℝ) = (r : ℝ) := h.zero
  have h1 : (x (firstDegree hn) : ℝ) = (r : ℝ) * (n : ℝ) := h.one
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

private theorem clipped_normalized (hn : 1 ≤ n) {r : ℕ} {x : FVector n}
    (h : Normalized hn (r + 1) (realVector x)) :
    Normalized hn 1 (realVector (clipped x)) := by
  have hh := head_coordinates hn h
  have hnr : n ≤ (r + 1) * n := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, ?_, ?_, fun _ => Nat.cast_nonneg _⟩
  · simp [realVector, clipped, cap, hh.1]
  · have hcap : cap (firstDegree hn) = n := by simp [cap, firstDegree]
    simp [realVector, clipped, hcap, hh.2, min_eq_left hnr]
  · intro i j hij
    dsimp only
    rw [ratio_clipped, ratio_clipped]
    exact min_le_min_left _ (h.anti hij)

private theorem remainder_normalized (hn : 1 ≤ n) {r : ℕ} {x : FVector n}
    (h : Normalized hn (r + 1) (realVector x)) :
    Normalized hn r (realVector (remainder x)) := by
  have hh := head_coordinates hn h
  refine ⟨?_, ?_, ?_, fun _ => Nat.cast_nonneg _⟩
  · simp [realVector, remainder, cap, hh.1]
  · have hcap : cap (firstDegree hn) = n := by simp [cap, firstDegree]
    simp [realVector, remainder, hcap, hh.2, Nat.add_mul]
  · intro i j hij
    dsimp only
    rw [ratio_remainder, ratio_remainder]
    exact max_le_max_left _ (sub_le_sub_right (h.anti hij) _)

theorem lattice_chained_exists (hn : 1 ≤ n) (r : ℕ) {x : FVector n}
    (hx : x ∈ natDilation hn r) :
    ∃ s : Fin r → FVector n,
      (∀ i, s i ∈ latticeVectors hn) ∧ Chained s ∧ sumTuple s = x := by
  induction r generalizing x with
  | zero =>
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun {i} => i.elim0, ?_⟩
    funext j
    have h := (div_le_iff₀ (cap_pos_real j)).mp (hx.ratio_le j)
    simp only [realVector, Nat.cast_zero, zero_mul] at h
    have h' : x j ≤ 0 := by exact_mod_cast h
    simpa [sumTuple] using (Nat.eq_zero_of_le_zero h').symm
  | succ r ih =>
    obtain ⟨s, hs, hc, he⟩ := ih (remainder_normalized hn hx)
    let b := clipped x
    have hb : b ∈ latticeVectors hn := (mem_latticeVectors hn).mpr (clipped_normalized hn hx)
    have hall (i : Fin (r + 1)) : (Fin.snoc s b : Fin (r + 1) → FVector n) i ∈ latticeVectors hn := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hb
      · simpa using hs j
    refine ⟨Fin.snoc s b, hall, ?_, ?_⟩
    · have hf (i : Fin (r + 1)) :=
        normalized_one_fixed hn ((mem_latticeVectors hn).mp (hall i))
      cases r with
      | zero => intro i j hij; have := j.isLt; omega
      | succ r =>
        apply (chainG_iff hn hf).mp
        apply (chainG_snoc_iff (σ := topState hn) (cond := cond hn) (q := s) (x := b)).mpr
        refine ⟨(chainG_iff hn (fun i => normalized_one_fixed hn ((mem_latticeVectors hn).mp (hs i)))).mpr hc, ?_⟩
        have ht : top (s (Fin.last r)) < (indeg b : ℤ) := by
          rcases indeg_eq_sentinel_or_missing b with hs' | ⟨k, hk, hmiss⟩
          · rw [hs']
            have := top_le (s (Fin.last r))
            omega
          · rw [← hk]
            change b k < cap k at hmiss
            have hk' : x k < cap k := lt_of_not_ge fun hh => by
              have hm : b k = cap k := min_eq_left hh
              omega
            apply top_lt_of_vanish
            intro j hj
            have hl := (div_le_iff₀ (cap_pos_real j)).mp
              ((hx.anti (show k ≤ j from hj)).trans
                ((div_le_iff₀ (cap_pos_real k)).mpr (by
                  rw [one_mul]
                  change (x k : ℝ) ≤ cap k
                  exact_mod_cast hk'.le)))
            rw [one_mul] at hl
            have hj' : x j ≤ cap j := by
              change (x j : ℝ) ≤ cap j at hl
              exact_mod_cast hl
            have hz : sumTuple s j = 0 := by
              rw [he]
              exact Nat.sub_eq_zero_of_le hj'
            have hsle : s (Fin.last r) j ≤ sumTuple s j :=
              Finset.single_le_sum (f := fun i => s i j) (fun _ _ => Nat.zero_le _) (mem_univ _)
            omega
        have hst := topState_val hn (normalized_one_fixed hn
          ((mem_latticeVectors hn).mp (hs (Fin.last r))))
        change (topState hn (s (Fin.last r))).val + 1 < indeg b
        omega
    · funext j
      simp only [sumTuple, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      change sumTuple s j + b j = x j
      rw [he]
      change x j - cap j + min (cap j) (x j) = x j
      omega

private theorem normalized_sum (hn : 1 ≤ n) {r : ℕ} {s : Fin r → FVector n}
    (hs : ∀ i, Normalized hn 1 (realVector (s i))) :
    Normalized hn r (realVector (sumTuple s)) := by
  have hsum j : realVector (sumTuple s) j = ∑ i, realVector (s i) j := by
    simp [realVector, sumTuple, Nat.cast_sum]
  refine ⟨?_, ?_, ?_, fun j => Nat.cast_nonneg _⟩
  · simp [hsum, fun i => (hs i).zero]
  · simp [hsum, fun i => (hs i).one, nsmul_eq_mul]
  · intro i j hij
    simp only [hsum, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_le_sum fun p _ => by simpa only [div_eq_mul_inv] using (hs p).anti hij

theorem lattice_count_transfer (hn : 1 ≤ n) (r : ℕ) :
    (dilateLattice n (r + 1)).ncard =
      uG (latticeVectors hn) (topState hn) ᵥ* transfer hn (latticeVectors hn) ^ r ⬝ᵥ (fun _ => 1) := by
  rw [dilateLattice_eq_image hn (by omega : 0 < r + 1)]
  have hinj : Function.Injective (intVector (n := n)) := by
    intro x y he
    funext j
    have h : (x j : ℤ) = (y j : ℤ) := congrFun he j
    exact_mod_cast h
  rw [Set.InjOn.ncard_image hinj.injOn]
  apply card_of_chained_image hn (latticeVectors hn)
  · exact fun f hf => normalized_one_bounded hn ((mem_latticeVectors hn).mp hf)
  · exact fun f hf => normalized_one_fixed hn ((mem_latticeVectors hn).mp hf)
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact normalized_sum hn (fun i => (mem_latticeVectors hn).mp (hs.1 i))
  · intro hx
    obtain ⟨s, hs, hc, he⟩ := lattice_chained_exists hn (r + 1) hx
    exact ⟨s, ⟨hs, hc⟩, he⟩

end D5.S3.Combinatorics.Kozlov
