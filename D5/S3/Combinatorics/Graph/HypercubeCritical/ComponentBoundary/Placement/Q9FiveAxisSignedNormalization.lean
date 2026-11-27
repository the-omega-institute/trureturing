/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisSignedNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed covariance transports the Huang switching vector. The character given by the odd-indexed coordinates converts the sign convention to the parity of the preceding occupied bits. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import Mathlib.Data.Fintype.Fin

/-! Transport a balanced cubic support to the sign convention of the five-axis inputs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedNormalization

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj switchingVector ambient_eigenvector)
open Q9IsotropicHuang (flipSign)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_row edge from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private normalize_flip_axis from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-- For the little-endian cube encoding, the exponent is the popcount of
`x & ((1 << i) - 1)` in the Python generator. -/
def rupFlipSign {n : ℕ} (i : Fin n) (x : Q n) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun j => j < i ∧ x j = true)).card

theorem rupFlipSign_eq {n : ℕ} (i : Fin n) (x : Q n) :
    rupFlipSign i x = (-1 : ℤ) ^ i.val * flipSign i x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          change rupFlipSign (0 : Fin (n + 1)) x = (-1 : ℤ) ^ (0 : ℕ) * 1
          simp [rupFlipSign]
      | succ i =>
          change rupFlipSign i.succ x = (-1 : ℤ) ^ (i.val + 1) *
            ((if x 0 then 1 else -1) * flipSign i (Sensitivity.π x))
          have hhead : rupFlipSign i.succ x =
              (if x 0 then -1 else 1) * rupFlipSign i (Sensitivity.π x) := by
            unfold rupFlipSign
            rw [Fin.card_filter_univ_succ', pow_add]
            cases h : x 0 <;> simp [h, Fin.succ_pos i, Fin.succ_lt_succ_iff, Sensitivity.π]
          rw [hhead, ih, pow_succ]
          cases h : x 0 <;> simp [h, mul_assoc]

/-- The character that is negative when an odd number of odd-indexed bits are set. -/
private def alternatingCharacter {n : ℕ} (x : Q n) : ℝ :=
  ∏ j : Fin n, if x j then (-1 : ℝ) ^ j.val else 1

private theorem axisSign_mul_self (k : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> simp [h]

private theorem alternatingCharacter_sq {n : ℕ} (x : Q n) :
    alternatingCharacter x ^ 2 = 1 := by
  rw [pow_two]
  unfold alternatingCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  cases h : x j <;> simp [h, axisSign_mul_self]

private theorem alternatingCharacter_flip {n : ℕ} (x : Q n) (i : Fin n) :
    alternatingCharacter x * alternatingCharacter (flip x i) = (-1 : ℝ) ^ i.val := by
  unfold alternatingCharacter
  rw [← Finset.prod_mul_distrib]
  calc
    _ = (if x i then (-1 : ℝ) ^ i.val else 1) *
          (if flip x i i then (-1 : ℝ) ^ i.val else 1) := by
      apply Fintype.prod_eq_single i
      intro j hji
      have hflip : flip x i j = x j := Function.update_of_ne hji _ _
      cases h : x j <;> simp [hflip, h, axisSign_mul_self]
    _ = _ := by
      rw [BalancedCriticalSpectrum.flip_apply_same]
      cases h : x i <;> simp [h]

private theorem cast_rupFlipSign {n : ℕ} (i : Fin n) (x : Q n) :
    (rupFlipSign i x : ℝ) = alternatingCharacter x * (flipSign i x : ℝ) *
      alternatingCharacter (flip x i) := by
  rw [rupFlipSign_eq, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_right_comm (alternatingCharacter x), alternatingCharacter_flip]

open Classical in
/-- The mapped support has an integer signing, zero off the support. Its exterior
rows cancel and its selected edge products are the Python coefficients. -/
theorem exists_normalized_signing (C : Finset (Q 9)) (π : Equiv.Perm (Fin 9)) (o : Q 9)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    let S := C.map (normalize π o).toEmbedding
    ∃ s : Q 9 → ℤ,
      (∀ x ∈ S, s x = 1 ∨ s x = -1) ∧
      (∀ x ∉ S, s x = 0) ∧
      (∀ x ∉ S, ∑ i : Fin 9, rupFlipSign i x * s (flip x i) = 0) ∧
      ∀ x ∈ S, ∀ i : Fin 9, flip x i ∈ S → rupFlipSign i x = s x * s (flip x i) := by
  classical
  let g := normalize π o
  let S := C.map g.toEmbedding
  have hm (x : Q 9) : x ∈ S ↔ g.symm x ∈ C := Finset.mem_map_equiv
  have hg (x : Q 9) (i : Fin 9) : g (flip x i) = flip (g x) (π.symm i) := by
    simpa only [Equiv.apply_symm_apply] using normalize_flip_axis π o x (π.symm i)
  obtain ⟨a, ha, hedge, hcov⟩ := HuangCubeCovariance.exists_signed_covariance g π.symm hg
  obtain ⟨σ, hσ⟩ := hb
  let f : Q 9 → ℝ := fun x => a (g.symm x) * switchingVector C σ (g.symm x)
  have hzero (x : Q 9) (hx : x ∉ S) : f x = 0 := by
    have hx' := (not_congr (hm x)).mp hx
    simp [f, switchingVector, hx']
  have hunit (x : Q 9) (hx : x ∈ S) : f x = 1 ∨ f x = -1 := by
    have hx' := (hm x).mp hx
    rcases ha (g.symm x) with h | h <;>
      rcases hσ.1 _ hx' with h' | h' <;> simp [f, switchingVector, hx', h, h']
  have hrow (x : Q 9) (hx : x ∉ S) :
      ∑ i : Fin 9, (flipSign i x : ℝ) * f (flip x i) = 0 := by
    have he := hcov (switchingVector C σ)
    rw [ambient_eigenvector (d := 3) C σ hr hσ] at he
    have hx' := (not_congr (hm x)).mp hx
    have hAt := congrFun he x
    change (huangMatrix 9).mulVec f x =
      a (g.symm x) * (3 * switchingVector C σ (g.symm x)) at hAt
    have h : (huangMatrix 9).mulVec f x = 0 := by
      simpa [switchingVector, hx'] using hAt
    rw [matrix_row] at h
    simpa only [edge, flipSign_cast] using h
  have hflipEdge (x : Q 9) (i : Fin 9) (hx : x ∈ S) (hy : flip x i ∈ S) :
      (flipSign i x : ℝ) = f x * f (flip x i) := by
    have hflip : g (flip (g.symm x) (π i)) = flip x i := by
      rw [hg, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    have hpre : g.symm (flip x i) = flip (g.symm x) (π i) := by
      rw [← hflip, Equiv.symm_apply_apply]
    have hx' := (hm x).mp hx
    have hy' := (hm (flip x i)).mp hy
    have hyC : flip (g.symm x) (π i) ∈ C := by rwa [← hpre]
    have he := hedge (g.symm x) (π i)
    rw [Equiv.apply_symm_apply, hflip, hσ.2 _ hx' _ hyC (flip_adj _ _)] at he
    rw [flipSign_cast, he]
    simp only [f, switchingVector, hpre, ite_eq_left hx', ite_eq_left hyC]
    ring
  let t : Q 9 → ℝ := fun x => alternatingCharacter x * f x
  have ht (x : Q 9) (hx : x ∈ S) : t x = 1 ∨ t x = -1 := by
    rcases sq_eq_one_iff.mp (alternatingCharacter_sq x) with h | h <;>
      rcases hunit x hx with hf | hf <;> simp [t, h, hf]
  have ht0 (x : Q 9) (hx : x ∉ S) : t x = 0 := by simp [t, hzero x hx]
  have htInt (x : Q 9) : ∃ q : ℤ, (q : ℝ) = t x := by
    by_cases hx : x ∈ S
    · rcases ht x hx with h | h
      · exact ⟨1, by simp [h]⟩
      · exact ⟨-1, by simp [h]⟩
    · exact ⟨0, by simp [ht0 x hx]⟩
  choose s hs using htInt
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases ht x hx with h | h
    · left
      exact_mod_cast (hs x).trans h
    · right
      exact_mod_cast (hs x).trans h
  · intro x hx
    exact_mod_cast (hs x).trans (ht0 x hx)
  · intro x hx
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_zero, Int.cast_sum, Int.cast_mul, hs]
    calc
      _ = alternatingCharacter x * (∑ i : Fin 9, (flipSign i x : ℝ) * f (flip x i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [cast_rupFlipSign]
        calc
          _ = (alternatingCharacter x * ((flipSign i x : ℝ) * f (flip x i))) *
                alternatingCharacter (flip x i) ^ 2 := by dsimp only [t]; ring
          _ = _ := by rw [alternatingCharacter_sq, mul_one]
      _ = 0 := by rw [hrow x hx, mul_zero]
  · intro x hx i hy
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_mul, hs]
    rw [cast_rupFlipSign, hflipEdge x i hx hy]
    dsimp only [t]
    ring

#print axioms exists_normalized_signing

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedNormalization
