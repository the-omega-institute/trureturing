/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed fragment boundary forces contacts and bounds the order of balanced cubic completions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A known signed fragment of a cubic component reserves exterior contacts
for cancellation. This restricts every separated balanced cubic component. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary

open scoped BigOperators Classical
open BalancedCriticalSpectrum (Q IsSwitching switchingVector flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions directions_card)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Finset
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_row from D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-- The signed sum visible from an exterior vertex when only the fragment
and its switching values are fixed. -/
def signedFragment (K : Finset (Q 9)) (σ : Q 9 → ℝ) (v : Q 9) : ℝ :=
  ∑ i ∈ directions K v, huangMatrix 9 v (flip v i) * σ (flip v i)

private theorem fullRow_zero {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (v : Q 9) (hv : v ∉ C) : signedFragment C σ v = 0 := by
  classical
  let f := switchingVector C σ
  have he := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C σ hr hs) v
  rw [matrix_row] at he
  have hrow : (∑ i : Fin 9, huangMatrix 9 v (flip v i) * f (flip v i)) = 0 := by
    simpa [f, switchingVector, hv] using he
  unfold signedFragment
  rw [← hrow]
  calc
    _ = ∑ i ∈ directions C v, huangMatrix 9 v (flip v i) * f (flip v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, switchingVector, (mem_directions C v i).mp hi]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have h : flip v i ∉ C := fun hx => hi ((mem_directions C v i).mpr hx)
      simp [f, switchingVector, h]

/-- Canceling the signed contribution of a known fragment uses at least
its absolute value in further contacts of the same cubic component. -/
theorem card_add_abs_le {K C : Finset (Q 9)} (hKC : K ⊆ C) {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (v : Q 9) (hv : v ∉ C) :
    ((directions K v).card : ℝ) + |signedFragment K σ v| ≤ (directions C v).card := by
  classical
  let I := directions K v
  let J := directions C v
  let a := fun i : Fin 9 => huangMatrix 9 v (flip v i) * σ (flip v i)
  have hIJ : I ⊆ J := fun i hi =>
    (mem_directions C v i).mpr (hKC ((mem_directions K v i).mp hi))
  have hzero : ∑ i ∈ J, a i = 0 := fullRow_zero hr hs v hv
  have hsplit : (∑ i ∈ J \ I, a i) + ∑ i ∈ I, a i = 0 :=
    (Finset.sum_sdiff hIJ).trans hzero
  have hneg : (∑ i ∈ J \ I, a i) = -(∑ i ∈ I, a i) := by linarith
  have hunit (i : Fin 9) (hi : i ∈ J \ I) : |a i| = 1 := by
    have him := (mem_directions C v i).mp (Finset.mem_sdiff.mp hi).1
    have hmat := SupportedEigenSaturation.matrix_abs_of_adj (flip_adj v i)
    rcases hs.1 _ him with h | h <;> simp [a, h, hmat]
  have habs : |∑ i ∈ I, a i| ≤ ((J \ I).card : ℝ) := by
    rw [← abs_neg (∑ i ∈ I, a i), ← hneg]
    calc
      _ ≤ ∑ i ∈ J \ I, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ J \ I, (1 : ℝ) := Finset.sum_congr rfl hunit
      _ = ((J \ I).card : ℝ) := by simp
  have hcard : ((J \ I).card : ℝ) + (I.card : ℝ) = (J.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hIJ
  change (I.card : ℝ) + |∑ i ∈ I, a i| ≤ J.card
  linarith

open Classical in
/-- A separating component sees at most the remaining part of the six
shared contacts, measured using the given signed fragment alone. -/
theorem shared_contacts_le_of_fragment {K C D : Finset (Q 9)} (hKC : K ⊆ C)
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : BalancedCriticalSpectrum.IsBalanced D)
    (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (v : Q 9) (hKpos : 0 < (directions K v).card) :
    ((directions D v).card : ℝ) ≤
      max 0 (6 - (directions K v).card - |signedFragment K σ v|) := by
  by_cases hpos : 0 < (directions D v).card
  · have hvC : v ∉ C := by
      intro hvC
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact hcross v hvC _ ((mem_directions D v i).mp hi) (flip_adj v i)
    have hvD : v ∉ D := by
      intro hvD
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hKpos
      exact hcross _ (hKC ((mem_directions K v i).mp hi)) v hvD (flip_adj v i).symm
    have hC : 0 < (directions C v).card := by
      apply hKpos.trans_le
      apply Finset.card_le_card
      intro i hi
      exact (mem_directions C v i).mpr (hKC ((mem_directions K v i).mp hi))
    have h6 := BalancedCubeComponentBoundary.neighbor_card_add_le_six C D hrC hrD
      ⟨σ, hs⟩ hbD hdisj hcross v hvC hvD
      (by simpa only [directions_card] using hC) (by simpa only [directions_card] using hpos)
    rw [← directions_card C v, ← directions_card D v] at h6
    have h6R : ((directions C v).card : ℝ) + ((directions D v).card : ℝ) ≤ 6 := by
      exact_mod_cast h6
    have hfrag := card_add_abs_le hKC hrC hs v hvC
    apply le_trans _ (le_max_right _ _)
    linarith
  · have hzero : (directions D v).card = 0 := by omega
    simp [hzero]


private theorem signedFragment_eq_switching_card {K C : Finset (Q 9)} (hKC : K ⊆ C)
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ) (v : Q 9) (hv : v ∈ C) :
    signedFragment K σ v = (directions K v).card * σ v := by
  classical
  calc
    _ = ∑ _i ∈ directions K v, σ v := by
      unfold signedFragment
      apply Finset.sum_congr rfl
      intro i hi
      have hw := hKC ((mem_directions K v i).mp hi)
      rw [hs.2 v hv _ hw (flip_adj v i), mul_assoc, ← pow_two,
        BalancedCriticalSpectrum.switching_sq hs hw, mul_one]
    _ = _ := by simp

/-- The total signed boundary of a fixed fragment constrains the order of
every balanced cubic completion, including its exterior cancellation. -/
theorem fragment_size_bound {K C : Finset (Q 9)} (hKC : K ⊆ C) {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) :
    3 * (K.card : ℝ) + (∑ v : Q 9, |signedFragment K σ v|) ≤ 6 * C.card := by
  classical
  let k := fun v : Q 9 => ((directions K v).card : ℝ)
  let c := fun v : Q 9 => ((directions C v).card : ℝ)
  have hloc (v : Q 9) :
      k v + |signedFragment K σ v| ≤ c v + if v ∈ C then 2 * k v - 3 else 0 := by
    by_cases hv : v ∈ C
    · have hreg : c v = 3 := by
        dsimp only [c]
        exact_mod_cast BalancedCubeComponentBoundary.regular_directions C hr hv
      have habs : |signedFragment K σ v| = k v := by
        rw [signedFragment_eq_switching_card hKC hs v hv, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (directions K v).card)]
        rcases hs.1 v hv with h | h <;> simp [h, k]
      simp [hreg, habs, hv] <;> linarith
    · simpa [k, c, hv] using card_add_abs_le hKC hr hs v hv
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Q 9)))
    (fun v _ => hloc v)
  have hd (S : Finset (Q 9)) (v : Q 9) :
      ((directions S v).card : ℝ) = ∑ w ∈ S, if (hypercube 9).Adj v w then 1 else 0 := by
    rw [directions_card, Finset.sum_boole]
  have htotal (S : Finset (Q 9)) :
      (∑ v : Q 9, ((directions S v).card : ℝ)) = 9 * S.card := by
    simp_rw [hd]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _w ∈ S, (9 : ℝ) := by
        apply Finset.sum_congr rfl
        intro w _
        calc
          _ = ∑ v : Q 9, if (hypercube 9).Adj w v then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            rw [SimpleGraph.adj_comm]
          _ = _ := by
            rw [← hd Finset.univ]
            have he : directions (Finset.univ : Finset (Q 9)) w = Finset.univ := by
              ext i
              simp [mem_directions]
            simp [he]
      _ = _ := by simp [mul_comm]
  have hinside : (∑ v ∈ C, k v) = 3 * K.card := by
    simp_rw [k, hd]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _w ∈ K, (3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro w hw
        calc
          _ = ∑ v ∈ C, if (hypercube 9).Adj w v then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            rw [SimpleGraph.adj_comm]
          _ = _ := by
            rw [← hd C]
            exact_mod_cast BalancedCubeComponentBoundary.regular_directions C hr (hKC hw)
      _ = _ := by simp [mul_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
  have hf : Finset.univ.filter (· ∈ C) = C := by ext v; simp
  rw [hf, Finset.sum_sub_distrib, ← Finset.mul_sum, hinside] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hk := htotal K
  have hc := htotal C
  change (∑ v, k v) = _ at hk
  change (∑ v, c v) = _ at hc
  rw [hk, hc] at hsum
  linarith


end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary
