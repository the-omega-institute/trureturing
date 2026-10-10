/- GID: D5/S3/Combinatorics/Partitions/SparseThickFrameFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/SparseThickFrameFamily
   mirror-E: none(waiver:unbounded-source-family)
   anchors: []
   utility: none
   digest: Full sparse-area joint capacity and actual separated thick-frame words. -/

import D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.SparseThickFrameFamily

open scoped BigOperators
open D5.S3.Combinatorics.Partitions.PaddedWordPartition
open D5.S3.Combinatorics.Partitions.WordPartitionInverse
open D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge

def side (k : ℕ) : ℕ := Nat.sqrt (k - 1) + 1
def thickness (k U : ℕ) : ℕ := (k + U - 1)/U
def gridCount (U h : ℕ) : ℕ := (U/6 - (U + 7)/8)/(128 * h) + 1
def grid (U h : ℕ) (i : Fin (gridCount U h)) : ℕ := (U + 7)/8 + 128 * h * i.val
def level (k : ℕ) : ℕ := Nat.log2 (1 + side k/560)

private theorem side_guards (k : ℕ) (hk : 4096 ≤ k) :
    64 ≤ side k ∧ k ≤ (side k) ^ 2 ∧ (side k) ^ 2 ≤ 2 * k ∧ Nat.sqrt k ≤ side k := by
  have hl := Nat.sqrt_le' (k - 1)
  have hu := Nat.lt_succ_sqrt' (k - 1)
  have hm : k - 1 + 1 = k := by omega
  have hz : 63 ≤ Nat.sqrt (k - 1) := (Nat.le_sqrt').2 (by omega)
  have hs : k ≤ (side k) ^ 2 := by simpa [side, hm] using Nat.succ_le_succ_sqrt' (k - 1)
  refine ⟨by simp only [side]; omega, hs, ?_, ?_⟩
  · dsimp [side]
    nlinarith
  · have hsk := Nat.sqrt_le' k
    nlinarith

private theorem dimension_guards (k U : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hsparse : 4096 * k ≤ U ^ 2) :
    4096 ≤ U ∧ 32 * side k ≤ U ∧
    1 ≤ thickness k U ∧ thickness k U ≤ side k ∧
    k ≤ thickness k U * U ∧ thickness k U * U ≤ 2 * k ∧
    32 * thickness k U ≤ Nat.sqrt k := by
  obtain ⟨hh, hkh, hhk, hzh⟩ := side_guards k hk
  have hU : 4096 ≤ U := by nlinarith
  have hUp : 0 < U := by omega
  have h32 : 32 * side k ≤ U := by nlinarith
  have hlo := Nat.lt_mul_div_succ (k + U - 1) hUp
  have hhi := Nat.div_mul_le_self (k + U - 1) U
  have hprod : k ≤ thickness k U * U ∧ thickness k U * U < k + U := by
    dsimp [thickness]
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm U ((k + U - 1)/U)] at hlo
    constructor <;> omega
  have hr : 1 ≤ thickness k U := by nlinarith [hprod.1]
  have hz64 : 64 ≤ Nat.sqrt k := (Nat.le_sqrt').2 hk
  have hzU : 64 * Nat.sqrt k ≤ U := by
    have hz := Nat.sqrt_le' k
    nlinarith
  have hzup := Nat.lt_succ_sqrt' k
  have hrt : 32 * thickness k U ≤ Nat.sqrt k := by
    by_cases hz : Nat.sqrt k = 64
    · have hrr : thickness k U ≤ 2 := by
        have hm := Nat.mul_le_mul_left (thickness k U - 1) hzU
        have he : (thickness k U - 1) * U + U = thickness k U * U := by
          rw [← Nat.succ_mul]; congr 1; omega
        nlinarith [hprod.2]
      omega
    · have hz65 : 65 ≤ Nat.sqrt k := by omega
      by_contra hb
      have hhrr : Nat.sqrt k < 32 * thickness k U := by omega
      have hm := Nat.mul_le_mul_left (thickness k U - 1) hzU
      have he : (thickness k U - 1) * U + U = thickness k U * U := by
        rw [← Nat.succ_mul]; congr 1; omega
      have hm2 := Nat.mul_le_mul_left (Nat.sqrt k) (Nat.succ_le_of_lt hhrr)
      nlinarith
  refine ⟨hU, h32, hr, ?_, hprod.1, by omega, hrt⟩
  omega

private theorem grid_guards (U h : ℕ) (hU : 4096 ≤ U) (hh : 0 < h)
    (i : Fin (gridCount U h)) :
    U ≤ 8 * grid U h i ∧ 6 * grid U h i ≤ U ∧
    U ≤ 6144 * h * gridCount U h := by
  have hlo : (U + 7)/8 ≤ U/6 := by omega
  have hgap : U ≤ 48 * (U/6 - (U + 7)/8) := by omega
  have hpos : 0 < 128 * h := by omega
  have hic : i.val ≤ (U/6 - (U + 7)/8)/(128 * h) := by
    have := i.isLt
    dsimp [gridCount] at this
    omega
  have him := Nat.mul_le_mul_left (128 * h) hic
  have hdiv := Nat.mul_div_le (U/6 - (U + 7)/8) (128 * h)
  have hcard := Nat.lt_mul_div_succ (U/6 - (U + 7)/8) hpos
  dsimp [grid]
  refine ⟨by omega, ?_, ?_⟩
  · have hb : (U + 7)/8 + 128 * h * i.val ≤ U/6 := by omega
    omega
  · dsimp [gridCount]
    nlinarith

private theorem level_guards (k : ℕ) :
    8 * coreSide (level k) ≤ side k ∧ side k < 1120 * q (level k) := by
  have hlo := Nat.log2_self_le (by omega : 1 + side k/560 ≠ 0)
  have hhi := Nat.lt_log2_self (n := 1 + side k/560)
  have hd := Nat.div_mul_le_self (side k) 560
  have hu := Nat.lt_mul_div_succ (side k) (by norm_num : 0 < 560)
  have hq : 1 ≤ q (level k) := Nat.one_le_two_pow
  dsimp [level, PrescribedAreaSquareWordCore.q] at *
  refine ⟨?_, ?_⟩
  · dsimp [coreSide, PrescribedAreaSquareWordCore.q, level]
    omega
  · rw [Nat.pow_succ] at hhi
    nlinarith

def residualArea (k U V L H : ℕ) : ℕ :=
  k - (thickness k U * L + thickness k V * H) + thickness k U * thickness k V

private theorem residual_guards (k U V : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hVk : V ≤ k)
    (hU : 4096 * k ≤ U ^ 2) (hV : 4096 * k ≤ V ^ 2)
    (i : Fin (gridCount U (side k))) (j : Fin (gridCount V (side k))) :
    thickness k V + side k ≤ grid U (side k) i ∧
    thickness k U + side k ≤ grid V (side k) j ∧
    thickness k U * grid U (side k) i + thickness k V * grid V (side k) j ≤ k ∧
    1024 * (thickness k U * thickness k V) ≤ k ∧
    (side k) ^ 2 ≤ 8 * residualArea k U V (grid U (side k) i) (grid V (side k) j) ∧
    8 * residualArea k U V (grid U (side k) i) (grid V (side k) j) ≤ 7 * (side k) ^ 2 := by
  obtain ⟨h64, hkh, hhk, _⟩ := side_guards k hk
  obtain ⟨hU0, hUh, hr0, hrh, hrU, hrU2, hrz⟩ := dimension_guards k U hk hUk hU
  obtain ⟨hV0, hVh, hs0, hsh, hsV, hsV2, hsz⟩ := dimension_guards k V hk hVk hV
  obtain ⟨hL0, hL1, _⟩ := grid_guards U (side k) hU0 (by omega) i
  obtain ⟨hH0, hH1, _⟩ := grid_guards V (side k) hV0 (by omega) j
  have hLp : thickness k V + side k ≤ grid U (side k) i := by omega
  have hHp : thickness k U + side k ≤ grid V (side k) j := by omega
  have hrL0 := Nat.mul_le_mul_left (thickness k U) hL0
  have hsH0 := Nat.mul_le_mul_left (thickness k V) hH0
  have hrL1 := Nat.mul_le_mul_left (thickness k U) hL1
  have hsH1 := Nat.mul_le_mul_left (thickness k V) hH1
  have hsum :
      3 * (thickness k U * grid U (side k) i + thickness k V * grid V (side k) j) ≤ 2 * k := by
    nlinarith
  have hsum0 : k ≤ 4 * (thickness k U * grid U (side k) i + thickness k V * grid V (side k) j) := by
    nlinarith
  have hrs : 1024 * (thickness k U * thickness k V) ≤ k := by
    have hm := Nat.mul_le_mul hrz hsz
    have hz := Nat.sqrt_le' k
    nlinarith
  have hnon : thickness k U * grid U (side k) i + thickness k V * grid V (side k) j ≤ k := by omega
  have hsub := Nat.sub_add_cancel hnon
  refine ⟨hLp, hHp, hnon, hrs, ?_, ?_⟩ <;>
    dsimp [residualArea] <;> omega

def frameRows (r s L H h : ℕ) (mu : List ℕ) : List ℕ :=
  List.replicate r L ++ mu.map (fun a => s + a) ++ List.replicate (H - r - h) s

private theorem shift_statistics (s : ℕ) (l : List ℕ) :
    (l.map (fun a => s + a)).sum = s * l.length + l.sum ∧
    squareRows (l.map (fun a => s + a)) =
      (l.length : ℝ) * s ^ 2 + 2 * s * (l.sum : ℝ) + squareRows l ∧
    oddRows (l.map (fun a => s + a)) = (s : ℝ) * l.length ^ 2 + oddRows l := by
  induction l with
  | nil => simp [squareRows, oddRows]
  | cons a l ih =>
    obtain ⟨hs, hp, hr⟩ := ih
    simp only [List.map_cons, List.length_cons, List.sum_cons, hs]
    refine ⟨by ring, ?_, ?_⟩
    · simp only [squareRows, List.map_cons, List.sum_cons] at hp ⊢
      rw [hp]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · rw [oddRows, hr, hs, oddRows]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

private theorem append_statistics (l m : List ℕ) :
    squareRows (l ++ m) = squareRows l + squareRows m ∧
    oddRows (l ++ m) = oddRows l + oddRows m + 2 * l.length * (m.sum : ℝ) := by
  constructor
  · simp [squareRows]
  · induction l with
    | nil => simp [oddRows]
    | cons a l ih =>
      simp only [List.cons_append, oddRows, ih, List.length_cons, List.sum_append]
      push_cast
      ring

private theorem replicate_statistics (n a : ℕ) :
    squareRows (List.replicate n a) = (n : ℝ) * a ^ 2 ∧
    oddRows (List.replicate n a) = (n : ℝ) ^ 2 * a := by
  constructor
  · simp [squareRows]
  · rw [oddRows_fin]
    simp only [List.getElem_replicate]
    rw [← Finset.sum_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((2 * i + 1 : ℕ) : ℝ)), odd_range]
    simp only [List.length_replicate]

private theorem moment_bounds (l : List ℕ) (a : ℕ) (ha : ∀ x ∈ l, x ≤ a) :
    0 ≤ squareRows l ∧ squareRows l ≤ (a : ℝ) * l.sum ∧
    0 ≤ oddRows l ∧ oddRows l ≤ 2 * (l.length : ℝ) * l.sum := by
  induction l with
  | nil => simp [squareRows, oddRows]
  | cons x l ih =>
    have hx : (x : ℝ) ≤ a := by exact_mod_cast ha x (by simp)
    obtain ⟨hp0, hp1, hr0, hr1⟩ := ih (by intro y hy; exact ha y (by simp [hy]))
    have hx0 : (0 : ℝ) ≤ x := by positivity
    have hs0 : (0 : ℝ) ≤ l.sum := by positivity
    simp only [squareRows, List.map_cons, List.sum_cons, oddRows, List.length_cons] at *
    simp only [Nat.cast_add, Nat.cast_one]
    refine ⟨add_nonneg (sq_nonneg _) hp0, ?_, by linarith, ?_⟩
    · nlinarith
    · nlinarith

private theorem frame_statistics (r s L H h t : ℕ) (mu : List ℕ)
    (hlen : mu.length = h) (harea : mu.sum = t)
    (hH : r + h ≤ H) (hs : s ≤ L) :
    (frameRows r s L H h mu).length = H ∧
    (frameRows r s L H h mu).sum = r * L + s * (H - r) + t ∧
    squareRows (frameRows r s L H h mu) =
      (r : ℝ) * L ^ 2 + (H - r : ℕ) * s ^ 2 + 2 * s * t + squareRows mu ∧
    oddRows (frameRows r s L H h mu) =
      (s : ℝ) * H ^ 2 + (L - s : ℕ) * r ^ 2 + 2 * r * t + oddRows mu := by
  obtain ⟨hms, hmp, hmr⟩ := shift_statistics s mu
  have hlens : (mu.map (fun a => s + a)).length = h := by simp [hlen]
  have htail : H - r - h + r + h = H := by omega
  have hHr : (H - r - h : ℕ) + h = H - r := by omega
  refine ⟨by simp [frameRows, hlen]; omega, ?_, ?_, ?_⟩
  · simp only [frameRows, List.sum_append, List.sum_replicate, smul_eq_mul, hms, hlen, harea]
    nlinarith
  · rw [frameRows, (append_statistics _ _).1, (append_statistics _ _).1,
      (replicate_statistics _ _).1, (replicate_statistics _ _).1, hmp, hlen, harea]
    have hc : ((H - r - h : ℕ) : ℝ) + (h : ℝ) = (H - r : ℕ) := by exact_mod_cast hHr
    nlinarith
  · rw [frameRows, (append_statistics _ _).2, (append_statistics _ _).2,
      (replicate_statistics _ _).2, (replicate_statistics _ _).2, hmr, hms, hlen, harea]
    simp only [List.length_append, List.length_replicate, List.length_map,
      hlen, List.sum_replicate, smul_eq_mul]
    have hc : ((H - r - h : ℕ) : ℝ) + (r : ℝ) + h = H := by exact_mod_cast htail
    have hLs : ((L - s : ℕ) : ℝ) + (s : ℝ) = L := by exact_mod_cast Nat.sub_add_cancel hs
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [← hc, ← hLs]
    ring

private theorem frame_shape (r s L H h : ℕ) (mu : List ℕ)
    (hsorted : mu.SortedGE) (hbound : ∀ a ∈ mu, a ≤ h) (hL : s + h ≤ L) :
    (frameRows r s L H h mu).SortedGE ∧
    (∀ a ∈ frameRows r s L H h mu, a ≤ L) := by
  have hm : (mu.map (fun a => s + a)).Pairwise (fun a b => b ≤ a) :=
    hsorted.pairwise.map _ (by intro a b hab; omega)
  have hl : (List.replicate r L).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_replicate.mpr (Or.inr le_rfl)
  have ht : (List.replicate (H - r - h) s).Pairwise (fun a b => b ≤ a) :=
    List.pairwise_replicate.mpr (Or.inr le_rfl)
  have hmb : ∀ a ∈ mu.map (fun a => s + a), s ≤ a ∧ a ≤ L := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have := hbound b hb
    omega
  constructor
  · apply List.Pairwise.sortedGE
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨hl, hm, ?_⟩, ht, ?_⟩
    · intro a ha b hb
      have he : a = L := List.eq_of_mem_replicate ha
      simpa [he] using (hmb b hb).2
    · intro a ha b hb
      have he : b = s := List.eq_of_mem_replicate hb
      rw [he]
      rcases List.mem_append.mp ha with ha | ha
      · have he : a = L := List.eq_of_mem_replicate ha
        omega
      · exact (hmb a ha).1
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact le_of_eq (List.eq_of_mem_replicate ha)
      · exact (hmb a ha).2
    · have he : a = s := List.eq_of_mem_replicate ha
      omega

private theorem frame_bands (k U V r s L H h t : ℕ) (mu : List ℕ)
    (hlen : mu.length = h) (harea : mu.sum = t) (hbound : ∀ a ∈ mu, a ≤ h)
    (hH : r + h ≤ H) (hL : s + h ≤ L)
    (hr : r ≤ h) (hs : s ≤ h) (hLU : L ≤ U) (hHV : H ≤ V)
    (hrU : r * U ≤ 2 * k) (hsV : s * V ≤ 2 * k) (ht : t ≤ k) :
    (r : ℝ) * L ^ 2 ≤ squareRows (frameRows r s L H h mu) ∧
    squareRows (frameRows r s L H h mu) ≤ (r : ℝ) * L ^ 2 + 7 * k * h ∧
    (s : ℝ) * H ^ 2 ≤ oddRows (frameRows r s L H h mu) ∧
    oddRows (frameRows r s L H h mu) ≤ (s : ℝ) * H ^ 2 + 7 * k * h := by
  obtain ⟨_, _, hp, hR⟩ := frame_statistics r s L H h t mu hlen harea hH (by omega)
  obtain ⟨hp0, hp1, hR0, hR1⟩ := moment_bounds mu h hbound
  rw [harea] at hp1
  rw [hlen, harea] at hR1
  have hrR : (r : ℝ) ≤ h := by exact_mod_cast hr
  have hsR : (s : ℝ) ≤ h := by exact_mod_cast hs
  have htR : (t : ℝ) ≤ k := by exact_mod_cast ht
  have hrUR : (r : ℝ) * U ≤ 2 * k := by exact_mod_cast hrU
  have hsVR : (s : ℝ) * V ≤ 2 * k := by exact_mod_cast hsV
  have hHV' : ((H - r : ℕ) : ℝ) ≤ V := by exact_mod_cast (by omega : H - r ≤ V)
  have hLU' : ((L - s : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : L - s ≤ U)
  have hst : (s : ℝ) * t ≤ (h : ℝ) * k :=
    mul_le_mul hsR htR (by positivity) (by positivity)
  have hrt : (r : ℝ) * t ≤ (h : ℝ) * k :=
    mul_le_mul hrR htR (by positivity) (by positivity)
  have hht : (h : ℝ) * t ≤ (h : ℝ) * k := mul_le_mul_of_nonneg_left htR (by positivity)
  have hpc : ((H - r : ℕ) : ℝ) * s ^ 2 ≤ 2 * (k : ℝ) * h := by
    calc
      _ = (((H - r : ℕ) : ℝ) * s) * s := by ring
      _ ≤ ((s : ℝ) * V) * s := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ (2 * (k : ℝ)) * h := mul_le_mul hsVR hsR (by positivity) (by positivity)
  have hrc : ((L - s : ℕ) : ℝ) * r ^ 2 ≤ 2 * (k : ℝ) * h := by
    calc
      _ = (((L - s : ℕ) : ℝ) * r) * r := by ring
      _ ≤ ((r : ℝ) * U) * r := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ (2 * (k : ℝ)) * h := mul_le_mul hrUR hrR (by positivity) (by positivity)
  have hpC0 : (0 : ℝ) ≤ (H - r : ℕ) * s ^ 2 := by positivity
  have hRC0 : (0 : ℝ) ≤ (L - s : ℕ) * r ^ 2 := by positivity
  have hst0 : (0 : ℝ) ≤ s * t := by positivity
  have hrt0 : (0 : ℝ) ≤ r * t := by positivity
  have hkh0 : (0 : ℝ) ≤ k * h := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private theorem grid_band_separation (k U h r : ℕ) (hk : 0 < k) (hh : 0 < h)
    (hU : 4096 ≤ U) (hrU : k ≤ r * U)
    (i j : Fin (gridCount U h)) (hij : i < j) :
    (r : ℝ) * (grid U h i) ^ 2 + 7 * k * h < (r : ℝ) * (grid U h j) ^ 2 := by
  have hL := (grid_guards U h hU hh i).1
  have hrl : (k : ℝ) ≤ 8 * (r : ℝ) * grid U h i := by
    have hm := Nat.mul_le_mul_left r hL
    exact_mod_cast (by nlinarith : k ≤ 8 * r * grid U h i)
  have hgap : grid U h i + 128 * h ≤ grid U h j := by
    have hm := Nat.mul_le_mul_left (128 * h) (show i.val + 1 ≤ j.val by exact hij)
    dsimp [grid]
    nlinarith
  have hgapR : (128 : ℝ) * h ≤ (grid U h j : ℝ) - grid U h i := by
    have hc : (grid U h i : ℝ) + 128 * h ≤ grid U h j := by exact_mod_cast hgap
    linarith
  have hb := mul_le_mul_of_nonneg_right hrl (show (0 : ℝ) ≤ h by positivity)
  have hm := mul_le_mul_of_nonneg_left hgapR
    (show (0 : ℝ) ≤ 2 * r * grid U h i by positivity)
  have he := mul_nonneg (show (0 : ℝ) ≤ r by positivity)
    (sq_nonneg ((grid U h j : ℝ) - grid U h i))
  have hkh : (0 : ℝ) < k * h := by exact_mod_cast Nat.mul_pos hk hh
  nlinarith only [hb, hm, he, hkh]

abbrev FrameIndex (k U V : ℕ) :=
  Fin (gridCount U (side k)) × Fin (gridCount V (side k)) × CoreIndex (level k)

def sourceRows (k U V : ℕ) (x : FrameIndex k U V) : List ℕ :=
  let L := grid U (side k) x.1
  let H := grid V (side k) x.2.1
  frameRows (thickness k U) (thickness k V) L H (side k)
    (rows (W (level k) (side k) (residualArea k U V L H) x.2.2))

def sourceWord (u v k U V : ℕ) (x : FrameIndex k U V) : List Bool :=
  wordOfRows u (sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0)

private theorem source_rows_spec (k U V : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hVk : V ≤ k) (hU : 4096 * k ≤ U ^ 2) (hV : 4096 * k ≤ V ^ 2)
    (x : FrameIndex k U V) :
    (sourceRows k U V x).length = grid V (side k) x.2.1 ∧
    (sourceRows k U V x).SortedGE ∧ (∀ a ∈ sourceRows k U V x, a ≤ grid U (side k) x.1) ∧
    (sourceRows k U V x).sum = k ∧
    (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 ≤ squareRows (sourceRows k U V x) ∧
    squareRows (sourceRows k U V x) ≤
      (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 + 7 * k * side k ∧
    (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 ≤ oddRows (sourceRows k U V x) ∧
    oddRows (sourceRows k U V x) ≤
      (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 + 7 * k * side k := by
  obtain ⟨h64, hkh, hhk, _⟩ := side_guards k hk
  obtain ⟨hU0, _, _, hrh, _, hrU2, _⟩ := dimension_guards k U hk hUk hU
  obtain ⟨hV0, _, _, hsh, _, hsV2, _⟩ := dimension_guards k V hk hVk hV
  obtain ⟨hL, hH, hnon, hrs, ht0, ht1⟩ := residual_guards k U V hk hUk hVk hU hV x.1 x.2.1
  obtain ⟨_, _, _, _, hlen, hsort, hbound, harea, _⟩ :=
    (square_family (level k) (side k)
      (residualArea k U V (grid U (side k) x.1) (grid V (side k) x.2.1))
      (by omega) (level_guards k).1 ht0 ht1).2.2.1 x.2.2
  obtain ⟨hlenF, hareaF, _, _⟩ := frame_statistics (thickness k U) (thickness k V)
    (grid U (side k) x.1) (grid V (side k) x.2.1) (side k)
    (residualArea k U V (grid U (side k) x.1) (grid V (side k) x.2.1))
    _ hlen harea hH (by omega)
  obtain ⟨hshape, hb⟩ := frame_shape (thickness k U) (thickness k V)
    (grid U (side k) x.1) (grid V (side k) x.2.1) (side k) _ hsort hbound hL
  have hsum : (sourceRows k U V x).sum = k := by
    dsimp [sourceRows]
    rw [hareaF]
    have hsub := Nat.sub_add_cancel hnon
    have hHr := Nat.sub_add_cancel (show thickness k U ≤ grid V (side k) x.2.1 by omega)
    have hm := congrArg (fun n : ℕ => thickness k V * n) hHr
    rw [Nat.mul_add, Nat.mul_comm (thickness k V) (thickness k U)] at hm
    dsimp [residualArea]
    omega
  have ht : residualArea k U V (grid U (side k) x.1) (grid V (side k) x.2.1) ≤ k := by
    have hm := Nat.mul_le_mul_left (thickness k U)
      (show thickness k V ≤ grid U (side k) x.1 by omega)
    have hsub := Nat.sub_add_cancel hnon
    dsimp [residualArea]
    omega
  have hLU := (grid_guards U (side k) hU0 (by omega) x.1).2.1
  have hHV := (grid_guards V (side k) hV0 (by omega) x.2.1).2.1
  refine ⟨hlenF, hshape, hb, hsum, ?_⟩
  exact frame_bands k U V (thickness k U) (thickness k V)
    (grid U (side k) x.1) (grid V (side k) x.2.1) (side k)
    (residualArea k U V (grid U (side k) x.1) (grid V (side k) x.2.1)) _
      hlen harea hbound hH hL hrh hsh
    (by omega) (by omega) hrU2 hsV2 ht

private theorem global_row_injection (k U V : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hVk : V ≤ k) (hU : 4096 * k ≤ U ^ 2) (hV : 4096 * k ≤ V ^ 2) :
    Function.Injective (fun x : FrameIndex k U V =>
      (squareRows (sourceRows k U V x), oddRows (sourceRows k U V x))) := by
  intro x y hxy
  have he := congrArg Prod.fst hxy
  have hf := congrArg Prod.snd hxy
  dsimp only at he hf
  obtain ⟨_, _, _, _, hxP0, hxP1, hxR0, hxR1⟩ := source_rows_spec k U V hk hUk hVk hU hV x
  obtain ⟨_, _, _, _, hyP0, hyP1, hyR0, hyR1⟩ := source_rows_spec k U V hk hUk hVk hU hV y
  obtain ⟨hU0, _, _, _, hrU, _, _⟩ := dimension_guards k U hk hUk hU
  obtain ⟨hV0, _, _, _, hsV, _, _⟩ := dimension_guards k V hk hVk hV
  have hh : 0 < side k := by have := (side_guards k hk).1; omega
  have hi : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hij | hij | hij
    · have := grid_band_separation k U (side k) (thickness k U) (by omega) hh hU0 hrU x.1 y.1 hij
      linarith
    · exact hij
    · have := grid_band_separation k U (side k) (thickness k U) (by omega) hh hU0 hrU y.1 x.1 hij
      linarith
  have hj : x.2.1 = y.2.1 := by
    rcases lt_trichotomy x.2.1 y.2.1 with hij | hij | hij
    · have := grid_band_separation k V (side k) (thickness k V) (by omega) hh
        hV0 hsV x.2.1 y.2.1 hij
      linarith
    · exact hij
    · have := grid_band_separation k V (side k) (thickness k V) (by omega) hh
        hV0 hsV y.2.1 x.2.1 hij
      linarith
  rcases x with ⟨i, j, a⟩
  rcases y with ⟨i', j', b⟩
  dsimp only at hi hj
  subst i'
  subst j'
  obtain ⟨hL, hH, _, _, ht0, ht1⟩ := residual_guards k U V hk hUk hVk hU hV i j
  have supplier := square_family (level k) (side k)
    (residualArea k U V (grid U (side k) i) (grid V (side k) j))
    hh (level_guards k).1 ht0 ht1
  have hcore : a = b := by
    apply supplier.2.2.2.2.2.1
    obtain ⟨_, _, _, _, haLen, _, _, haSum, _⟩ := supplier.2.2.1 a
    obtain ⟨_, _, _, _, hbLen, _, _, hbSum, _⟩ := supplier.2.2.1 b
    obtain ⟨_, _, haP, haR⟩ := frame_statistics (thickness k U) (thickness k V)
      (grid U (side k) i) (grid V (side k) j) (side k)
      (residualArea k U V (grid U (side k) i) (grid V (side k) j)) _ haLen haSum hH (by omega)
    obtain ⟨_, _, hbP, hbR⟩ := frame_statistics (thickness k U) (thickness k V)
      (grid U (side k) i) (grid V (side k) j) (side k)
      (residualArea k U V (grid U (side k) i) (grid V (side k) j)) _ hbLen hbSum hH (by omega)
    dsimp only [sourceRows] at he hf
    rw [haP, hbP] at he
    rw [haR, hbR] at hf
    exact Prod.ext (by linarith only [he]) (by linarith only [hf])
  subst b
  rfl

private theorem zero_padding_statistics (l : List ℕ) (n : ℕ) :
    squareRows (l ++ List.replicate n 0) = squareRows l ∧
    oddRows (l ++ List.replicate n 0) = oddRows l := by
  obtain ⟨hp, hr⟩ := append_statistics l (List.replicate n 0)
  obtain ⟨hzP, hzR⟩ := replicate_statistics n 0
  simp only [Nat.cast_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0)] at hzP hzR
  simp [hp, hr, hzP, hzR]

private theorem source_word_spec (u v k U V : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hVk : V ≤ k) (hU : 4096 * k ≤ U ^ 2) (hV : 4096 * k ≤ V ^ 2)
    (hUu : U ≤ u) (hVv : V ≤ v) (x : FrameIndex k U V) :
    sourceWord u v k U V x ∈ wordFiber u v k ∧
    (sourceWord u v k U V x).count true = u ∧ (sourceWord u v k U V x).count false = v ∧
    scatteredTrueFalseCount (sourceWord u v k U V x) = k ∧
    rows (sourceWord u v k U V x) =
      sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0 ∧
    squareRows (rows (sourceWord u v k U V x)) = squareRows (sourceRows k U V x) ∧
    oddRows (rows (sourceWord u v k U V x)) = oddRows (sourceRows k U V x) := by
  obtain ⟨hlen, hs, hb, ha, _⟩ := source_rows_spec k U V hk hUk hVk hU hV x
  have hU0 := (dimension_guards k U hk hUk hU).1
  have hV0 := (dimension_guards k V hk hVk hV).1
  have hh : 0 < side k := by have := (side_guards k hk).1; omega
  have hLU : grid U (side k) x.1 ≤ U := by
    have := (grid_guards U (side k) hU0 hh x.1).2.1
    omega
  have hHV : grid V (side k) x.2.1 ≤ V := by
    have := (grid_guards V (side k) hV0 hh x.2.1).2.1
    omega
  have hlenv : (sourceRows k U V x).length ≤ v := by omega
  have hsorted :
      (sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0).SortedGE := by
    apply List.Pairwise.sortedGE
    apply List.pairwise_append.mpr
    refine ⟨hs.pairwise, List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
    intro a ha b hb
    have he : b = 0 := List.eq_of_mem_replicate hb
    omega
  have hbound :
      ∀ a ∈ sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0, a ≤ u := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hb a ha).trans (hLU.trans hUu)
    · have he : a = 0 := List.eq_of_mem_replicate ha
      omega
  obtain ⟨ht, hf, hr⟩ := wordOfRows_spec _ hsorted u hbound
  change (sourceWord u v k U V x).count true = u at ht
  change rows (sourceWord u v k U V x) = _ at hr
  have hf' : (sourceWord u v k U V x).count false = v := by
    change (sourceWord u v k U V x).count false = _ at hf
    simpa [List.length_append, List.length_replicate, Nat.add_sub_of_le hlenv] using hf
  have harea : scatteredTrueFalseCount (sourceWord u v k U V x) = k := by
    rw [← rows_sum, hr]
    simp [ha]
  have hne : sourceWord u v k U V x ≠ [] := by
    intro he
    rw [he] at ht
    simp only [List.count_nil] at ht
    omega
  refine ⟨⟨hne, by exact_mod_cast ht, by exact_mod_cast hf', by exact_mod_cast harea⟩,
    ht, hf', harea, hr, ?_⟩
  rw [hr]
  exact zero_padding_statistics _ _

private theorem global_word_injection (u v k U V : ℕ) (hk : 4096 ≤ k)
    (hUk : U ≤ k) (hVk : V ≤ k) (hU : 4096 * k ≤ U ^ 2) (hV : 4096 * k ≤ V ^ 2)
    (hUu : U ≤ u) (hVv : V ≤ v) :
    Function.Injective (fun x : FrameIndex k U V =>
      ((G (sourceWord u v k U V x)).e, (G (sourceWord u v k U V x)).f)) := by
  intro x y hxy
  have he := congrArg Prod.fst hxy
  have hf := congrArg Prod.snd hxy
  dsimp only at he hf
  obtain ⟨_, hxt, hxf, hxa, _, hxP, hxR⟩ := source_word_spec u v k U V hk hUk hVk hU hV hUu hVv x
  obtain ⟨_, hyt, hyf, hya, _, hyP, hyR⟩ := source_word_spec u v k U V hk hUk hVk hU hV hUu hVv y
  rw [direct_list_fan, direct_list_fan, hxt, hxf, hxa, hyt, hyf, hya] at he hf
  dsimp only at he hf
  rw [hxP, hyP] at he
  rw [hxR, hyR] at hf
  apply global_row_injection k U V hk hUk hVk hU hV
  exact Prod.ext (by linarith) (by linarith)

def c0 : ℝ := 1 / ((6144 : ℝ) ^ 2 * (1120 : ℝ) ^ 6)

private theorem grid_constant_bound (U V k h n m Q : ℕ)
    (hU : U ≤ 6144 * h * n) (hV : V ≤ 6144 * h * m)
    (hq : h ≤ 1120 * Q) (hk : k ≤ h ^ 2) :
    c0 * U * V * (k : ℝ) ^ 2 ≤ (n * m * Q ^ 6 : ℕ) := by
  have hUR : (U : ℝ) ≤ 6144 * h * n := by exact_mod_cast hU
  have hVR : (V : ℝ) ≤ 6144 * h * m := by exact_mod_cast hV
  have hqR : (h : ℝ) ≤ 1120 * Q := by exact_mod_cast hq
  have hkR : (k : ℝ) ≤ (h : ℝ) ^ 2 := by exact_mod_cast hk
  have hb : (U : ℝ) * V * k ^ 2 ≤
      ((6144 : ℝ) ^ 2 * (1120 : ℝ) ^ 6) * ((n : ℝ) * m * Q ^ 6) := by
    calc
      _ ≤ (U : ℝ) * V * ((h : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (U : ℝ) * V * h ^ 4 := by ring
      _ ≤ (6144 * (h : ℝ) * n) * (6144 * (h : ℝ) * m) * h ^ 4 := by gcongr
      _ = (6144 : ℝ) ^ 2 * n * m * h ^ 6 := by ring
      _ ≤ (6144 : ℝ) ^ 2 * n * m * (1120 * (Q : ℝ)) ^ 6 := by gcongr
      _ = _ := by ring
  have hd : (0 : ℝ) < (6144 : ℝ) ^ 2 * (1120 : ℝ) ^ 6 := by positivity
  rw [c0, show (1 / ((6144 : ℝ) ^ 2 * (1120 : ℝ) ^ 6)) * U * V * (k : ℝ) ^ 2 =
    ((U : ℝ) * V * k ^ 2) / ((6144 : ℝ) ^ 2 * (1120 : ℝ) ^ 6) by ring]
  apply (div_le_iff₀ hd).2
  simpa only [Nat.cast_mul, Nat.cast_pow, mul_comm] using hb

/-- Computed sparse grids support actual fixed-area words with a separated joint moment image. -/
theorem separated_frame_family (u v k : ℕ) (hk : 4096 ≤ k)
    (hu : 4096 * k ≤ u ^ 2) (hv : 4096 * k ≤ v ^ 2) :
    let U := min u k
    let V := min v k
    (∀ x : FrameIndex k U V,
      sourceWord u v k U V x ∈ wordFiber u v k ∧
      (sourceWord u v k U V x).count true = u ∧
      (sourceWord u v k U V x).count false = v ∧
      scatteredTrueFalseCount (sourceWord u v k U V x) = k ∧
      rows (sourceWord u v k U V x) =
        sourceRows k U V x ++ List.replicate (v - (sourceRows k U V x).length) 0 ∧
      (sourceRows k U V x).length = grid V (side k) x.2.1 ∧
      (sourceRows k U V x).SortedGE ∧
      (∀ a ∈ sourceRows k U V x, a ≤ grid U (side k) x.1) ∧
      (sourceRows k U V x).sum = k ∧
      (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 ≤ squareRows (sourceRows k U V x) ∧
      squareRows (sourceRows k U V x) ≤
        (thickness k U : ℝ) * (grid U (side k) x.1) ^ 2 + 7 * k * side k ∧
      (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 ≤ oddRows (sourceRows k U V x) ∧
      oddRows (sourceRows k U V x) ≤
        (thickness k V : ℝ) * (grid V (side k) x.2.1) ^ 2 + 7 * k * side k) ∧
    Function.Injective (fun x : FrameIndex k U V =>
      (squareRows (sourceRows k U V x), oddRows (sourceRows k U V x))) ∧
    Function.Injective (fun x : FrameIndex k U V =>
      ((G (sourceWord u v k U V x)).e, (G (sourceWord u v k U V x)).f)) ∧
    Function.Injective (sourceWord u v k U V) ∧
    (Set.range (sourceWord u v k U V)).ncard =
      gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ∧
    (Set.range (fun x : FrameIndex k U V =>
      ((G (sourceWord u v k U V x)).e, (G (sourceWord u v k U V x)).f))).ncard =
      gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ∧
    gridCount U (side k) * gridCount V (side k) * (q (level k)) ^ 6 ≤ capacity u v k ∧
    U ≤ 6144 * side k * gridCount U (side k) ∧
    V ≤ 6144 * side k * gridCount V (side k) ∧
    side k < 1120 * q (level k) ∧ k ≤ (side k) ^ 2 ∧
    c0 * U * V * (k : ℝ) ^ 2 ≤ capacity u v k := by
  dsimp only
  have hU : 4096 * k ≤ (min u k) ^ 2 := by
    rcases le_total u k with h | h
    · simpa [min_eq_left h] using hu
    · rw [min_eq_right h]
      nlinarith
  have hV : 4096 * k ≤ (min v k) ^ 2 := by
    rcases le_total v k with h | h
    · simpa [min_eq_left h] using hv
    · rw [min_eq_right h]
      nlinarith
  have hjoint := global_word_injection u v k (min u k) (min v k) hk
    (min_le_right _ _) (min_le_right _ _) hU hV (min_le_left _ _) (min_le_left _ _)
  have hword : Function.Injective (sourceWord u v k (min u k) (min v k)) := by
    intro x y he
    apply hjoint
    exact congrArg (fun w => ((G w).e, (G w).f)) he
  have hcard : Nat.card (FrameIndex k (min u k) (min v k)) =
      gridCount (min u k) (side k) * gridCount (min v k) (side k) * (q (level k)) ^ 6 := by
    simp [FrameIndex, CoreIndex, ← pow_add]
    ring
  have hjointcard := (Set.ncard_range_of_injective hjoint).trans hcard
  have hmem (x : FrameIndex k (min u k) (min v k)) :=
    source_word_spec u v k (min u k) (min v k) hk
      (min_le_right _ _) (min_le_right _ _) hU hV (min_le_left _ _) (min_le_left _ _) x
  have hcapacity : gridCount (min u k) (side k) * gridCount (min v k) (side k) *
      (q (level k)) ^ 6 ≤ capacity u v k := by
    rw [capacity, ← hjointcard]
    apply Set.ncard_le_ncard _ ((fiber_finite u v k).image _)
    rintro _ ⟨x, rfl⟩
    exact ⟨sourceWord u v k (min u k) (min v k) x, (hmem x).1, rfl⟩
  refine ⟨?_, global_row_injection _ _ _ hk (min_le_right _ _) (min_le_right _ _) hU hV,
    hjoint, hword, (Set.ncard_range_of_injective hword).trans hcard, hjointcard, hcapacity, ?_⟩
  · intro x
    obtain ⟨hm, ht, hf, ha, hr, _⟩ := hmem x
    exact ⟨hm, ht, hf, ha, hr,
      source_rows_spec _ _ _ hk (min_le_right _ _) (min_le_right _ _) hU hV x⟩
  · have hh : 0 < side k := by have := (side_guards k hk).1; omega
    have hU0 := (dimension_guards k (min u k) hk (min_le_right _ _) hU).1
    have hV0 := (dimension_guards k (min v k) hk (min_le_right _ _) hV).1
    let i : Fin (gridCount (min u k) (side k)) := ⟨0, by simp [gridCount]⟩
    let j : Fin (gridCount (min v k) (side k)) := ⟨0, by simp [gridCount]⟩
    have hUc := (grid_guards _ _ hU0 hh i).2.2
    have hVc := (grid_guards _ _ hV0 hh j).2.2
    have hqc := (level_guards k).2
    have hkc := (side_guards k hk).2.1
    refine ⟨hUc, hVc, hqc, hkc, ?_⟩
    apply (grid_constant_bound _ _ _ _ _ _ _ hUc hVc hqc.le hkc).trans
    exact_mod_cast hcapacity

private def natSquare (l : List ℕ) : ℕ := (l.map fun a => a ^ 2).sum

private theorem natural_statistics (l : List ℕ) :
    squareRows l = (natSquare l : ℝ) ∧ l.sum ≤ natSquare l := by
  constructor
  · simp [squareRows, natSquare, Function.comp_def]
  · induction l with
    | nil => simp [natSquare]
    | cons a l ih =>
      have ha : a ≤ a ^ 2 := by nlinarith
      simp only [natSquare, List.map_cons, List.sum_cons] at ih ⊢
      omega

private theorem column_area (w : List Bool) :
    (∑ j ∈ Finset.range (w.count true), (diagram w).colLen j) = (rows w).sum := by
  have hcol (j : ℕ) : (diagram w).colLen j =
      ∑ i ∈ Finset.range (rows w).length, if (i, j) ∈ diagram w then 1 else 0 := by
    simp_rw [YoungDiagram.mem_iff_lt_colLen]
    rw [← Finset.sum_filter]
    have hf : (Finset.range (rows w).length).filter
        (fun i => i < (diagram w).colLen j) = Finset.range ((diagram w).colLen j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have := diagram_col_bound w j
      omega
    rw [hf]
    simp
  have hrow (i : ℕ) :
      (∑ j ∈ Finset.range (w.count true), if (i, j) ∈ diagram w then 1 else 0) =
        (diagram w).rowLen i := by
    simp_rw [YoungDiagram.mem_iff_lt_rowLen]
    rw [← Finset.sum_filter]
    have hf : (Finset.range (w.count true)).filter
        (fun j => j < (diagram w).rowLen i) = Finset.range ((diagram w).rowLen i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have := diagram_row_bound w i
      omega
    rw [hf]
    simp
  simp_rw [hcol]
  rw [Finset.sum_comm]
  simp_rw [hrow]
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [diagram_row]
  simp

private theorem column_moment_bound (w : List Bool) :
    oddRows (rows w) ≤ (min (w.count false) (scatteredTrueFalseCount w) : ℕ) *
      (scatteredTrueFalseCount w : ℝ) := by
  have hb (j : ℕ) (hj : j ∈ Finset.range (w.count true)) :
      (diagram w).colLen j ≤ min (w.count false) (scatteredTrueFalseCount w) := by
    refine le_min (by simpa only [rows_length] using diagram_col_bound w j) ?_
    rw [← rows_sum, ← column_area]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← same_diagram_columns]
  unfold R
  simp only [YoungDiagram.rowLen_transpose]
  calc
    _ ≤ ∑ j ∈ Finset.range (w.count true),
        (min (w.count false) (scatteredTrueFalseCount w) : ℕ) *
          ((diagram w).colLen j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hc : ((diagram w).colLen j : ℝ) ≤
          (min (w.count false) (scatteredTrueFalseCount w) : ℕ) := by exact_mod_cast hb j hj
      nlinarith [Nat.cast_nonneg (α := ℝ) ((diagram w).colLen j)]
    _ = _ := by rw [← Finset.mul_sum, ← Nat.cast_sum, column_area, rows_sum]

private def natColumns (w : List Bool) : ℕ :=
  ∑ j ∈ Finset.range (w.count true), (diagram w).colLen j ^ 2

private theorem natural_columns (w : List Bool) :
    oddRows (rows w) = (natColumns w : ℝ) ∧ scatteredTrueFalseCount w ≤ natColumns w := by
  constructor
  · rw [← same_diagram_columns]
    simp [R, natColumns, YoungDiagram.rowLen_transpose]
  · rw [← rows_sum, ← column_area]
    dsimp [natColumns]
    exact Finset.sum_le_sum (fun j _ => by nlinarith)

private theorem capacity_upper (u v k : ℕ) (hk : 1 ≤ k) :
    capacity u v k ≤ min u k * min v k * k ^ 2 := by
  let ambient : Set (ℕ × ℕ) := Set.Icc 1 (min u k * k) ×ˢ Set.Icc 1 (min v k * k)
  let affine : ℕ × ℕ → ℝ × ℝ := fun p =>
    ((u : ℝ) ^ 2 * v - 6 * u * k + 6 * p.1,
      -(u : ℝ) * v ^ 2 + 6 * v * k - 6 * p.2)
  have hfinite : ambient.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hsubset : jointImage u v k ⊆ affine '' ambient := by
    rintro _ ⟨w, ⟨hne, ht, hf, ha⟩, rfl⟩
    have htu : w.count true = u := by exact_mod_cast ht
    have hfv : w.count false = v := by exact_mod_cast hf
    have hak : scatteredTrueFalseCount w = k := by exact_mod_cast ha
    have hs : (rows w).sum = k := by rw [rows_sum, hak]
    have hb : ∀ a ∈ rows w, a ≤ min u k := by
      intro a ha
      apply le_min
      · simpa only [htu] using rows_bound w a ha
      · rw [← hs]
        exact List.single_le_sum (fun a _ => Nat.zero_le a) a ha
    obtain ⟨hp, hp0⟩ := natural_statistics (rows w)
    obtain ⟨hr, hr0⟩ := natural_columns w
    have hP := (moment_bounds (rows w) (min u k) hb).2.1
    have hR := column_moment_bound w
    rw [hfv, hak] at hR
    rw [hs] at hP hp0
    rw [hak] at hr0
    have hPn : natSquare (rows w) ≤ min u k * k := by rw [hp] at hP; exact_mod_cast hP
    have hRn : natColumns w ≤ min v k * k := by
      rw [hr] at hR
      exact_mod_cast hR
    refine ⟨(natSquare (rows w), natColumns w), ⟨⟨by omega, hPn⟩, ⟨by omega, hRn⟩⟩, ?_⟩
    dsimp [affine]
    rw [direct_list_fan, htu, hfv, hak]
    simp only [hp, hr]
  have hc := (Set.ncard_le_ncard hsubset (hfinite.image affine)).trans (Set.ncard_image_le hfinite)
  have hcard : ambient.ncard = min u k * min v k * k ^ 2 := by
    dsimp [ambient]
    rw [Set.ncard_prod, Set.ncard_Icc_nat, Set.ncard_Icc_nat]
    simp only [Nat.add_sub_cancel]
    ring
  simpa only [capacity, hcard] using hc

private def smallWord (u v k : ℕ) : List Bool := wordOfRows u (k :: List.replicate (v - 1) 0)

private theorem small_capacity (u v k : ℕ) (hk : 1 ≤ k) (hk1 : k < 4096)
    (hu : 4096 * k ≤ u ^ 2) (hv : 4096 * k ≤ v ^ 2) :
    c0 * min u k * min v k * (k : ℝ) ^ 2 ≤ capacity u v k := by
  have hku : k ≤ u := by nlinarith
  have hkv : k ≤ v := by nlinarith
  have hs : (k :: List.replicate (v - 1) 0).SortedGE := by
    apply List.Pairwise.sortedGE
    simp only [List.pairwise_cons]
    refine ⟨?_, List.pairwise_replicate.mpr (Or.inr le_rfl)⟩
    intro a ha
    have he : a = 0 := List.eq_of_mem_replicate ha
    omega
  have hb : ∀ a ∈ k :: List.replicate (v - 1) 0, a ≤ u := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hku
    · have he : a = 0 := List.eq_of_mem_replicate ha
      omega
  obtain ⟨ht, hf, hr⟩ := wordOfRows_spec _ hs u hb
  have hft : (smallWord u v k).count true = u := ht
  have hff : (smallWord u v k).count false = v := by
    simpa only [smallWord, List.length_cons, List.length_replicate,
      Nat.sub_add_cancel (show 1 ≤ v by omega)] using hf
  have hfa : scatteredTrueFalseCount (smallWord u v k) = k := by
    rw [← rows_sum]
    change (rows (wordOfRows u _)).sum = k
    rw [hr]
    simp
  have hmem : smallWord u v k ∈ wordFiber u v k := by
    refine ⟨?_, by exact_mod_cast hft, by exact_mod_cast hff, by exact_mod_cast hfa⟩
    intro he
    rw [he] at hft
    simp only [List.count_nil] at hft
    omega
  have hcap : 1 ≤ capacity u v k :=
    (Set.ncard_pos ((fiber_finite u v k).image _)).2
      ⟨_, smallWord u v k, hmem, rfl⟩
  have hsmall : c0 * min u k * min v k * (k : ℝ) ^ 2 ≤ 1 := by
    have hc : 0 ≤ c0 := by norm_num [c0]
    have hkR : (k : ℝ) ≤ 4096 := by exact_mod_cast hk1.le
    calc
      _ ≤ c0 * k * k * (k : ℝ) ^ 2 := by gcongr <;> exact_mod_cast min_le_right _ _
      _ = c0 * (k : ℝ) ^ 4 := by ring
      _ ≤ c0 * (4096 : ℝ) ^ 4 := by gcongr
      _ ≤ 1 := by norm_num [c0]
  exact hsmall.trans (by exact_mod_cast hcap)

def normalizedArea (u v K : ℤ) : ℕ := (min K (u * v - K)).toNat

abbrev OriginalIndex (u v K : ℤ) := FrameIndex (normalizedArea u v K)
  (min u.toNat (normalizedArea u v K)) (min v.toNat (normalizedArea u v K))

def originalWord (u v K : ℤ) (x : OriginalIndex u v K) : List Bool :=
  let k := normalizedArea u v K
  let w := sourceWord u.toNat v.toNat k (min u.toNat k) (min v.toNat k) x
  if K = (k : ℤ) then w else w.reverse

def originalFamilySize (u v K : ℤ) : ℕ :=
  let k := normalizedArea u v K
  gridCount (min u.toNat k) (side k) * gridCount (min v.toNat k) (side k) *
    (q (level k)) ^ 6

private theorem integer_guards (u v K : ℤ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (_hK0 : 0 ≤ K) (_hK1 : K ≤ u * v) (hk : 1 ≤ min K (u * v - K))
    (hs : 4096 * min K (u * v - K) ≤ (min u v) ^ 2) :
    (u.toNat : ℤ) = u ∧ (v.toNat : ℤ) = v ∧
    (normalizedArea u v K : ℤ) = min K (u * v - K) ∧
    1 ≤ normalizedArea u v K ∧
    4096 * normalizedArea u v K ≤ u.toNat ^ 2 ∧
    4096 * normalizedArea u v K ≤ v.toNat ^ 2 ∧
    (K = (normalizedArea u v K : ℤ) ∨ K = u * v - normalizedArea u v K) ∧
    capacity u v K = capacity u.toNat v.toNat (normalizedArea u v K) := by
  have huc : (u.toNat : ℤ) = u := Int.toNat_of_nonneg (by omega)
  have hvc : (v.toNat : ℤ) = v := Int.toNat_of_nonneg (by omega)
  have hkc : (normalizedArea u v K : ℤ) = min K (u * v - K) :=
    Int.toNat_of_nonneg (by omega)
  have hd0 : (0 : ℤ) ≤ min u v := le_min (by omega) (by omega)
  have hdu := min_le_left u v
  have hdv := min_le_right u v
  have hsu : 4096 * min K (u * v - K) ≤ u ^ 2 := by nlinarith only [hs, hd0, hdu, hu]
  have hsv : 4096 * min K (u * v - K) ≤ v ^ 2 := by nlinarith only [hs, hd0, hdv, hv]
  have hkn : 1 ≤ normalizedArea u v K := by
    exact_mod_cast (show (1 : ℤ) ≤ normalizedArea u v K by omega)
  have hun : 4096 * normalizedArea u v K ≤ u.toNat ^ 2 := by
    apply Int.ofNat_le.mp
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, huc, hkc]
    exact hsu
  have hvn : 4096 * normalizedArea u v K ≤ v.toNat ^ 2 := by
    apply Int.ofNat_le.mp
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hvc, hkc]
    exact hsv
  have hcase : K = (normalizedArea u v K : ℤ) ∨ K = u * v - normalizedArea u v K := by
    rcases le_total K (u * v - K) with h | h
    · left; rw [hkc, min_eq_left h]
    · right; rw [hkc, min_eq_right h]; ring
  refine ⟨huc, hvc, hkc, hkn, hun, hvn, hcase, ?_⟩
  rw [huc, hvc]
  rcases hcase with h | h
  · exact congrArg (capacity u v) h
  · calc
      capacity u v K = capacity u v (u * v - normalizedArea u v K) :=
        congrArg (capacity u v) h
      _ = capacity u v (normalizedArea u v K) :=
        congrArg Set.ncard (joint_image_reverse u v (normalizedArea u v K)).symm

/-- The full integer sparse-area capacity bounds and the explicit large-area separated family. -/
theorem sparse_joint_moment_capacity (u v K : ℤ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hK0 : 0 ≤ K) (hK1 : K ≤ u * v) (hk : 1 ≤ min K (u * v - K))
    (hs : 4096 * min K (u * v - K) ≤ (min u v) ^ 2) :
    let k := min K (u * v - K)
    let U := min u k
    let V := min v k
    c0 * (U : ℝ) * (V : ℝ) * (k : ℝ) ^ 2 ≤ capacity u v K ∧
    (capacity u v K : ℤ) ≤ U * V * k ^ 2 ∧
    (4096 ≤ k →
      (∀ x : OriginalIndex u v K, originalWord u v K x ∈ wordFiber u v K) ∧
      Function.Injective (fun x : OriginalIndex u v K =>
        ((G (originalWord u v K x)).e, (G (originalWord u v K x)).f)) ∧
      Function.Injective (originalWord u v K) ∧
      (Set.range (originalWord u v K)).ncard = originalFamilySize u v K ∧
      (Set.range (fun x : OriginalIndex u v K =>
        ((G (originalWord u v K x)).e, (G (originalWord u v K x)).f))).ncard =
        originalFamilySize u v K) := by
  dsimp only
  obtain ⟨huc, hvc, hkc, hkn, hun, hvn, hcase, hcapacity⟩ :=
    integer_guards u v K hu hv hK0 hK1 hk hs
  have hUc : ((min u.toNat (normalizedArea u v K) : ℕ) : ℤ) = min u (min K (u * v - K)) := by
    rw [Nat.cast_min, huc, hkc]
  have hVc : ((min v.toNat (normalizedArea u v K) : ℕ) : ℤ) = min v (min K (u * v - K)) := by
    rw [Nat.cast_min, hvc, hkc]
  have hUR : ((min u.toNat (normalizedArea u v K) : ℕ) : ℝ) = (min u (min K (u * v - K)) : ℤ) := by
    exact_mod_cast hUc
  have hVR : ((min v.toNat (normalizedArea u v K) : ℕ) : ℝ) = (min v (min K (u * v - K)) : ℤ) := by
    exact_mod_cast hVc
  have hkR : (normalizedArea u v K : ℝ) = (min K (u * v - K) : ℤ) := by exact_mod_cast hkc
  have hlarge (hl : 4096 ≤ normalizedArea u v K) :=
    separated_frame_family u.toNat v.toNat (normalizedArea u v K) hl hun hvn
  have hlow : c0 * min u.toNat (normalizedArea u v K) * min v.toNat (normalizedArea u v K) *
      (normalizedArea u v K : ℝ) ^ 2 ≤ capacity u.toNat v.toNat (normalizedArea u v K) := by
    by_cases hl : 4096 ≤ normalizedArea u v K
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb⟩ := hlarge hl
      exact hb
    · exact small_capacity _ _ _ hkn (by omega) hun hvn
  have hup := capacity_upper u.toNat v.toNat (normalizedArea u v K) hkn
  have hupZ : (capacity u.toNat v.toNat (normalizedArea u v K) : ℤ) ≤
      ((min u.toNat (normalizedArea u v K) : ℕ) : ℤ) * (min v.toNat (normalizedArea u v K) : ℕ) *
      (normalizedArea u v K : ℤ) ^ 2 := by exact_mod_cast hup
  rw [← hcapacity, hUR, hVR, hkR] at hlow
  rw [← hcapacity, hUc, hVc, hkc] at hupZ
  refine ⟨hlow, hupZ, ?_⟩
  intro hklarge
  have hl : 4096 ≤ normalizedArea u v K := by
    exact_mod_cast (show (4096 : ℤ) ≤ normalizedArea u v K by omega)
  obtain ⟨hsource, _, hjoint, _, _, _, _, _, _, _, _, _⟩ := hlarge hl
  have hsig (x : OriginalIndex u v K) :
      ((G (originalWord u v K x)).e, (G (originalWord u v K x)).f) =
      ((G (sourceWord u.toNat v.toNat (normalizedArea u v K)
        (min u.toNat (normalizedArea u v K)) (min v.toNat (normalizedArea u v K)) x)).e,
       (G (sourceWord u.toNat v.toNat (normalizedArea u v K)
        (min u.toNat (normalizedArea u v K)) (min v.toNat (normalizedArea u v K)) x)).f) := by
    dsimp only [originalWord]
    split
    · rfl
    · exact Prod.ext (outer_reverse_contract _).2.2.2.1 (outer_reverse_contract _).2.2.2.2
  have hj : Function.Injective (fun x : OriginalIndex u v K =>
      ((G (originalWord u v K x)).e, (G (originalWord u v K x)).f)) := by
    intro x y he
    apply hjoint
    exact (hsig x).symm.trans (he.trans (hsig y))
  have hw : Function.Injective (originalWord u v K) := by
    intro x y he
    exact hj (congrArg (fun w => ((G w).e, (G w).f)) he)
  have hcard : Nat.card (OriginalIndex u v K) = originalFamilySize u v K := by
    simp only [OriginalIndex, FrameIndex, originalFamilySize, CoreIndex,
      Nat.card_prod, Nat.card_fin]
    ring
  refine ⟨?_, hj, hw, (Set.ncard_range_of_injective hw).trans hcard,
    (Set.ncard_range_of_injective hj).trans hcard⟩
  intro x
  obtain ⟨hne, ht, hf, ha⟩ := (hsource x).1
  dsimp only [originalWord]
  split_ifs with he
  · exact ⟨hne, ht.trans huc, hf.trans hvc, ha.trans he.symm⟩
  · have hflip : K = u * v - normalizedArea u v K := hcase.resolve_left he
    obtain ⟨hrt, hrf, hra, _, _⟩ := outer_reverse_contract
      (sourceWord u.toNat v.toNat (normalizedArea u v K)
        (min u.toNat (normalizedArea u v K)) (min v.toNat (normalizedArea u v K)) x)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hnil
      apply hne
      have hr := congrArg List.reverse hnil
      simpa only [List.reverse_reverse, List.reverse_nil] using hr
    · rw [hrt]; exact ht.trans huc
    · rw [hrf]; exact hf.trans hvc
    · rw [hra, Nat.cast_sub (pair_count_bound _), Nat.cast_mul, ht, hf, ha, huc, hvc]
      exact hflip.symm

#check sparse_joint_moment_capacity
#print axioms sparse_joint_moment_capacity
#check separated_frame_family
#print axioms separated_frame_family

end D5.S3.Combinatorics.Partitions.SparseThickFrameFamily
