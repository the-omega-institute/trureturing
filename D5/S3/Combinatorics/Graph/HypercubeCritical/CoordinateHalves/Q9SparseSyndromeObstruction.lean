/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9SparseSyndromeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction, lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeAnalyticWeightTwelve]
   utility: none
   digest: Bound signed lift energy from shell capacity and exclude sparse nonempty order-seventy-two syndromes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeAnalyticWeightTwelve

/-! The signed energy bound depends on the syndrome's shell intersections and
therefore applies beyond a fixed chart or a fixed choice of dimer signs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
namespace Q9SparseSyndromeObstruction

open scoped BigOperators symmDiff
open Finset
open BalancedCriticalSpectrum (Q)
open EightCubeBits (Vertex Word cube toggle toggle_injective shell shell_symm
  asFunction coeff row_eq_card isKernel_iff_adjacency asFunction_symmDiff)
open BinaryCubeKernelSupport (binarySites four_dvd_binarySites_card)
open BinaryCubeAnalyticWeightTwelve (weight_less_twelve_one_shell weight_twelve_two_shells)
open BinaryCubeSplitReconstruction (delta)
open Q9PairedGeometricObstruction (card_le_weighted_cover)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold (transverse)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (flipSign)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open private activeDirections bitRow bitRow_sum bitRow_energy flipSign_unit shell_card
  transverse_square transverse_energy from Q9PairedGeometricObstruction
open private shell_asFunction from EightCubeBits
open private adjacency_add from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel

private theorem active_card_eq_inter (S : Word) (x : Vertex) :
    (activeDirections S x).card = (shell x ∩ S).card := by
  have h : (activeDirections S x).image (toggle x) = shell x ∩ S := by
    ext y
    simp only [activeDirections, mem_inter, shell, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  rw [← h, card_image_of_injective _ (toggle_injective x)]

private theorem unit_rows {S B : Word} {g : Vertex → ℤ}
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hunit : ∀ x ∈ S, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ S, g x = 0) (x : Vertex) :
    (bitRow g x = 0 ∨ bitRow g x = 2 ∨ bitRow g x = -2) ∧
      (x ∉ B → bitRow g x = 0) := by
  let A := activeDirections S x
  let a := fun i : Fin 8 => flipSign i (cube x) * g (toggle x i)
  have hrow : bitRow g x = ∑ i ∈ A, a i := by
    rw [bitRow_sum]
    symm
    apply sum_subset (subset_univ A)
    intro i _ hi
    have hz : toggle x i ∉ S := by simpa [A, activeDirections] using hi
    simp [a, hzero _ hz]
  have ha (i : Fin 8) (hi : i ∈ A) : a i = 1 ∨ a i = -1 := by
    have hs : toggle x i ∈ S := (mem_filter.mp hi).2
    rcases flipSign_unit i (cube x) with h | h <;>
      rcases hunit _ hs with h' | h' <;> simp [a, h, h']
  have hd : A.card = _ := (active_card_eq_inter S x).trans (hdegree x)
  by_cases hx : x ∈ B
  · rw [ite_eq_left hx] at hd
    obtain ⟨i, j, hij, hA⟩ := card_eq_two.mp hd
    have hi := ha i (by simp [hA])
    have hj := ha j (by simp [hA])
    rw [hrow, hA, sum_pair hij]
    refine ⟨?_, fun h => False.elim (h hx)⟩
    omega
  · rw [ite_eq_right hx] at hd
    rw [hrow, card_eq_zero.mp hd, sum_empty]
    simp

private theorem unit_energy {S : Word} {g : Vertex → ℤ}
    (hunit : ∀ x ∈ S, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ S, g x = 0) :
    (∑ x, g x ^ 2) = S.card := by
  calc
    _ = ∑ x ∈ S, g x ^ 2 := by
      symm
      apply sum_subset (subset_univ _)
      intro x _ hx
      simp [hzero x hx]
    _ = ∑ _x ∈ S, (1 : ℤ) := by
      apply sum_congr rfl
      intro x hx
      rcases hunit x hx with h | h <;> norm_num [h]
    _ = S.card := by simp

private theorem unit_row_support_card {S B : Word} {g : Vertex → ℤ}
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hunit : ∀ x ∈ S, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ S, g x = 0) :
    ((univ : Word).filter (fun x => bitRow g x ≠ 0)).card = 2 * S.card := by
  let T := (univ : Word).filter fun x => bitRow g x ≠ 0
  have henergy := bitRow_energy g
  rw [unit_energy hunit hzero] at henergy
  have hsum : (∑ x, bitRow g x ^ 2) = 4 * (T.card : ℤ) := by
    calc
      _ = ∑ x ∈ T, bitRow g x ^ 2 := by
        symm
        apply sum_subset (subset_univ _)
        intro x _ hx
        have hz : bitRow g x = 0 := by simpa [T] using hx
        simp [hz]
      _ = ∑ _x ∈ T, (4 : ℤ) := by
        apply sum_congr rfl
        intro x hx
        have hn : bitRow g x ≠ 0 := (mem_filter.mp hx).2
        rcases (unit_rows hdegree hunit hzero x).1 with h | h | h
        · exact False.elim (hn h)
        · norm_num [h]
        · norm_num [h]
      _ = _ := by simp [mul_comm]
  rw [hsum] at henergy
  change T.card = 2 * S.card
  omega

/-- With at most two syndrome neighbors per row, the shell capacity of
exterior corrections gives a lower bound for any lift in the mod-four kernel. -/
theorem sparse_syndrome_energy (S B : Word) (v : Vertex → ℤ) (c : ℤ)
    (hc : 4 ≤ c)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hcapacity : ∀ x, v x ≠ 0 → x ∉ S → ((shell x ∩ B).card : ℤ) ≤ c)
    (hsyndrome : ∀ x, v x % 2 = 1 ↔ x ∈ S)
    (hdiv : ∀ x, 4 ∣ transverse (v ∘ cube.symm) (cube x)) :
    8 * (S.card : ℤ) ≤ c * ((∑ x, v x ^ 2) - (S.card : ℤ)) := by
  classical
  let g : Vertex → ℤ := fun x =>
    if x ∈ S then if v x < 0 then -1 else 1 else 0
  have hg_unit (x : Vertex) (hx : x ∈ S) : g x = 1 ∨ g x = -1 := by
    simp only [g, ite_eq_left hx]
    split <;> simp
  have hg_zero (x : Vertex) (hx : x ∉ S) : g x = 0 := by simp [g, hx]
  let T := (univ : Word).filter fun x => bitRow g x ≠ 0
  let Z := (univ : Word).filter fun x => v x ≠ g x
  let w := fun x => v x ^ 2 - g x ^ 2
  have hT : T.card = 2 * S.card := unit_row_support_card hdegree hg_unit hg_zero
  have hTB : T ⊆ B := by
    intro x hx
    by_contra hn
    exact (mem_filter.mp hx).2 ((unit_rows hdegree hg_unit hg_zero x).2 hn)
  have hcover (t : Vertex) (ht : t ∈ T) :
      ∃ z ∈ Z, t ∈ shell z := by
    by_contra! hn
    have he : bitRow v t = bitRow g t := by
      rw [bitRow_sum, bitRow_sum]
      apply sum_congr rfl
      intro i _
      have hs : t ∈ shell (toggle t i) :=
        shell_symm.mp (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
      have hz : toggle t i ∉ Z := fun h => hn _ h hs
      have hv : v (toggle t i) = g (toggle t i) := by simpa [Z] using hz
      rw [hv]
    have hd : 4 ∣ bitRow g t := by
      rw [← he]
      exact hdiv t
    have hne : bitRow g t ≠ 0 := (mem_filter.mp ht).2
    rcases (unit_rows hdegree hg_unit hg_zero t).1 with h | h | h <;> omega
  have hcost (x : Vertex) (hx : x ∈ Z) :
      (if x ∈ S then (8 : ℤ) else 4) ≤ w x := by
    have hne : v x ≠ g x := (mem_filter.mp hx).2
    by_cases hs : x ∈ S
    · have hm := (hsyndrome x).2 hs
      simp only [ite_eq_left hs, w, g]
      by_cases hn : v x < 0
      · have h : v x ≤ -3 := by simp [g, hs, hn] at hne; omega
        simp [hn]
        nlinarith
      · have h : 3 ≤ v x := by simp [g, hs, hn] at hne; omega
        simp [hn]
        nlinarith
    · have hm : v x % 2 = 0 := by
        have hh := Int.emod_two_eq_zero_or_one (v x)
        have hno : v x % 2 ≠ 1 := fun h => hs ((hsyndrome x).1 h)
        omega
      have hv : v x ≠ 0 := by simpa [hg_zero x hs] using hne
      simp only [ite_eq_right hs, w, hg_zero x hs, zero_pow (by decide : 2 ≠ 0), sub_zero]
      have h : v x ≤ -2 ∨ 2 ≤ v x := by omega
      rcases h with h | h <;> nlinarith
  let cap : Vertex → ℤ := fun z => if z ∈ S then 8 else c
  have hcap (z : Vertex) (hz : z ∈ Z) :
      ((T.bipartiteAbove (fun z t : Vertex => t ∈ shell z) z).card : ℤ) ≤ cap z := by
    have hsub : T.bipartiteAbove (fun z t : Vertex => t ∈ shell z) z ⊆ shell z ∩ B := by
      intro t ht
      have ht' : t ∈ T ∧ t ∈ shell z := by simpa [Finset.bipartiteAbove] using ht
      obtain ⟨htT, htS⟩ := ht'
      exact mem_inter.mpr ⟨htS, hTB htT⟩
    have hle := card_le_card hsub
    by_cases hs : z ∈ S
    · have hb : (shell z ∩ B).card ≤ 8 := by
        exact (card_le_card inter_subset_left).trans (shell_card z).le
      simp only [cap, if_pos hs]
      exact_mod_cast (hle.trans hb)
    · have hv : v z ≠ 0 := by
        have hn : v z ≠ g z := (mem_filter.mp hz).2
        simpa [hg_zero z hs] using hn
      simp only [cap, if_neg hs]
      have hleInt : ((T.bipartiteAbove (fun z t : Vertex => t ∈ shell z) z).card : ℤ) ≤
          ((shell z ∩ B).card : ℤ) := by exact_mod_cast hle
      exact hleInt.trans (hcapacity z hv hs)
  have hweighted := card_le_weighted_cover Z T (fun z t : Vertex => t ∈ shell z) cap hcover hcap
  have hscaled : 4 * (T.card : ℤ) ≤ c * ∑ z ∈ Z, w z := by
    calc
      4 * (T.card : ℤ) ≤ 4 * ∑ z ∈ Z, cap z := by linarith
      _ = ∑ z ∈ Z, 4 * cap z := mul_sum ..
      _ ≤ ∑ z ∈ Z, c * w z := by
        apply sum_le_sum
        intro z hz
        have h := hcost z hz
        by_cases hs : z ∈ S
        · simp only [cap, if_pos hs] at h ⊢
          exact (mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℤ) ≤ 8)).trans
            (mul_le_mul_of_nonneg_left h (by omega))
        · simp only [cap, if_neg hs] at h ⊢
          rw [mul_comm 4 c]
          exact mul_le_mul_of_nonneg_left h (by omega)
      _ = c * ∑ z ∈ Z, w z := (mul_sum ..).symm
  have hTInt : (T.card : ℤ) = 2 * (S.card : ℤ) := by exact_mod_cast hT
  rw [hTInt] at hscaled
  have hsum : (∑ x ∈ Z, w x) = ∑ x, w x := by
    apply sum_subset (subset_univ _)
    intro x _ hx
    have he : v x = g x := by simpa [Z] using hx
    simp [w, he]
  rw [hsum] at hscaled
  change 4 * (2 * (S.card : ℤ)) ≤ c * ∑ x, (v x ^ 2 - g x ^ 2) at hscaled
  rw [sum_sub_distrib, unit_energy hg_unit hg_zero] at hscaled
  calc
    8 * (S.card : ℤ) = 4 * (2 * (S.card : ℤ)) := by ring
    _ ≤ _ := hscaled

private theorem small_sparse_syndrome_eq_empty {S B : Word}
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hsmall : S.card ≤ 15) : S = ∅ := by
  classical
  let f := asFunction S
  have hf : adjacency f = 0 := by
    apply (isKernel_iff_adjacency S).mp
    intro x
    rw [row_eq_card, hdegree]
    split <;> decide
  have hsites : binarySites f = S.map cube.toEmbedding := by
    ext q
    obtain ⟨x, rfl⟩ := cube.surjective q
    simp only [binarySites, mem_filter, mem_univ, true_and, f, asFunction,
      mem_map_equiv, Equiv.symm_apply_apply]
    by_cases hx : x ∈ S <;> simp [coeff, hx]
  have hcard : (binarySites f).card = S.card := by rw [hsites, card_map]
  have hdiv := four_dvd_binarySites_card (m := 2) (by decide) hf
  rw [hcard] at hdiv
  have hsingle (x : Vertex) : asFunction {x} = delta (cube x) := by
    funext q
    obtain ⟨y, rfl⟩ := cube.surjective q
    simp [asFunction, coeff, delta]
  have hshell (x : Vertex) : asFunction (shell x) = adjacency (delta (cube x)) := by
    rw [shell_asFunction, hsingle]
  have hinj {U V : Word} (h : asFunction U = asFunction V) : U = V := by
    ext x
    have hx := congrFun h (cube x)
    simp only [asFunction, Equiv.symm_apply_apply, coeff] at hx
    by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp [hu, hv] at hx ⊢
  by_contra hne
  have hpos : 0 < S.card := card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have h12 : S.card ≤ 12 := by omega
  by_cases hw : S.card = 12
  · obtain ⟨p, q, _, h⟩ := weight_twelve_two_shells f hf (hcard.trans hw)
    obtain ⟨x, rfl⟩ := cube.surjective p
    obtain ⟨y, rfl⟩ := cube.surjective q
    have hS : S = shell x ∆ shell y := by
      apply hinj
      rw [asFunction_symmDiff, hshell, hshell, ← adjacency_add]
      exact h
    have hdiff : ((shell x ∪ shell y) \ (shell x ∩ shell y)).card = 12 := by
      rw [hS] at hw
      simpa only [symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter] using hw
    have hunion := card_union_add_card_inter (shell x) (shell y)
    have hparts := card_sdiff_add_card_eq_card
      (inter_subset_union (s := shell x) (t := shell y))
    rw [shell_card, shell_card] at hunion
    rw [hdiff] at hparts
    have hinter : (shell x ∩ shell y).card = 2 := by omega
    have heq : shell x ∩ S = shell x \ shell y := by
      rw [hS]
      ext z
      simp only [mem_inter, mem_symmDiff, mem_sdiff]
      tauto
    have hs := hdegree x
    rw [heq, card_sdiff, inter_comm, shell_card, hinter] at hs
    split at hs <;> omega
  · obtain ⟨_, p, h⟩ := weight_less_twelve_one_shell f hf
      (by omega) (by omega)
    obtain ⟨x, rfl⟩ := cube.surjective p
    have hS : S = shell x := hinj (h.trans (hshell x).symm)
    have hs := hdegree x
    rw [hS, inter_self, shell_card] at hs
    split at hs <;> omega

/-- An order-72 signed fold with twelve dimers admits no nonempty syndrome
with zero or two neighbors per row and exterior capacity at most seven. -/
theorem sparse_syndrome_empty_at_order_72
    (d e o : Q 8 → ℤ) (S B : Word)
    (hd : (∑ x, d x ^ 2) = 12)
    (hdisj : ∀ x, d x * e x = 0)
    (hcount : (∑ x, e x ^ 2) + (∑ x, o x ^ 2) = 48)
    (hsum : ∀ x, transverse (fun y => 2 * d y + e y) x = 4 * o x)
    (hfold : ∀ x, transverse o x = 4 * d x + 2 * e x)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hcapacity : ∀ x, transverse d (cube x) - 2 * o (cube x) ≠ 0 →
      x ∉ S → (shell x ∩ B).card ≤ 7)
    (hsyndrome : ∀ x, (transverse d (cube x) - 2 * o (cube x)) % 2 = 1 ↔ x ∈ S) :
    S = ∅ := by
  let v : Q 8 → ℤ := fun x => transverse d x - 2 * o x
  have hrow (x : Q 8) : transverse v x = -4 * e x := by
    have hlinear : transverse v x = transverse (transverse d) x - 2 * transverse o x := by
      unfold v transverse
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hlinear, transverse_square, hfold]
    ring
  have hdiv (x : Vertex) : 4 ∣ transverse ((v ∘ cube) ∘ cube.symm) (cube x) := by
    have he : (v ∘ cube) ∘ cube.symm = v := by
      funext y
      simp
    rw [he, hrow]
    exact ⟨-e (cube x), by ring⟩
  have hbound := sparse_syndrome_energy S B (v ∘ cube) 7 (by norm_num)
    hdegree (fun x hx hout => by exact_mod_cast hcapacity x hx hout) hsyndrome hdiv
  change 8 * (S.card : ℤ) ≤ 7 * ((∑ x : Vertex, v (cube x) ^ 2) - _) at hbound
  rw [Equiv.sum_comp cube (fun x => v x ^ 2)] at hbound
  have henergy₁ := transverse_energy v
  simp_rw [hrow] at henergy₁
  have henergy₂ := transverse_energy (fun x => 2 * d x + e x)
  simp_rw [hsum] at henergy₂
  have hscale (w : Q 8 → ℤ) (a : ℤ) :
      (∑ x, (a * w x) ^ 2) = a ^ 2 * ∑ x, w x ^ 2 := by
    simp only [mul_pow, mul_sum]
  rw [hscale] at henergy₁ henergy₂
  have hin : (∑ x, (2 * d x + e x) ^ 2) = 48 + ∑ x, e x ^ 2 := by
    have hsite (x : Q 8) : (2 * d x + e x) ^ 2 = 4 * d x ^ 2 + e x ^ 2 := by
      linear_combination 4 * hdisj x
    simp_rw [hsite]
    rw [sum_add_distrib, ← mul_sum, hd]
    norm_num
  rw [hin] at henergy₂
  norm_num at henergy₁ henergy₂
  exact small_sparse_syndrome_eq_empty hdegree (by omega)

#print axioms sparse_syndrome_energy
#print axioms sparse_syndrome_empty_at_order_72

end Q9SparseSyndromeObstruction
end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
