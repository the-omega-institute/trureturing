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
  asFunction coeff row_eq_card isKernel_iff_adjacency asFunction_symmDiff distance relabel)
open BinaryCubeKernelSupport (binarySites four_dvd_binarySites_card)
open BinaryCubeAnalyticWeightTwelve (weight_less_twelve_one_shell weight_twelve_two_shells)
open BinaryCubeSplitReconstruction (delta)
open Q9PairedGeometricObstruction (card_le_weighted_cover)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold (transverse)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (flipSign)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open private activeDirections bitRow bitRow_sum bitRow_energy flipSign_unit shell_card
  transverse_square transverse_energy from Q9PairedGeometricObstruction
open private shell_asFunction relabel_center relabel_shell from EightCubeBits
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

/-- In the order-72 signed fold, a nonempty syndrome with zero or two
neighbors per row has weight sixteen and an exterior residual site all of
whose neighbors are rows with two syndrome neighbors. -/
private theorem sparse_syndrome_at_order_72
    (d e o : Q 8 → ℤ) (S B : Word)
    (hd : (∑ x, d x ^ 2) = 12)
    (hdisj : ∀ x, d x * e x = 0)
    (hcount : (∑ x, e x ^ 2) + (∑ x, o x ^ 2) = 48)
    (hsum : ∀ x, transverse (fun y => 2 * d y + e y) x = 4 * o x)
    (hfold : ∀ x, transverse o x = 4 * d x + 2 * e x)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hsyndrome : ∀ x, (transverse d (cube x) - 2 * o (cube x)) % 2 = 1 ↔ x ∈ S) :
    S = ∅ ∨ (S.card = 16 ∧ ∃ x : Vertex,
      transverse d (cube x) - 2 * o (cube x) ≠ 0 ∧ x ∉ S ∧ shell x ⊆ B) := by
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
  have hnorm : (∑ x, v x ^ 2) = 32 := by omega
  have hbound (c : ℤ) (hc : 4 ≤ c)
      (hcap : ∀ x : Vertex, v (cube x) ≠ 0 → x ∉ S → ((shell x ∩ B).card : ℤ) ≤ c) :
      8 * (S.card : ℤ) ≤ c * (32 - (S.card : ℤ)) := by
    have h := sparse_syndrome_energy S B (v ∘ cube) c hc hdegree hcap hsyndrome hdiv
    change 8 * (S.card : ℤ) ≤ c * ((∑ x : Vertex, v (cube x) ^ 2) - _) at h
    rw [Equiv.sum_comp cube (fun x => v x ^ 2), hnorm] at h
    exact h
  by_cases hsmall : S.card ≤ 15
  · exact Or.inl (small_sparse_syndrome_eq_empty hdegree hsmall)
  · have h8 := hbound 8 (by norm_num) (fun x _ _ => by
      have h := (card_le_card (inter_subset_left : shell x ∩ B ⊆ shell x)).trans
        (shell_card x).le
      exact_mod_cast h)
    refine Or.inr ⟨by omega, ?_⟩
    by_contra hnone
    have hcap (x : Vertex) (hx : v (cube x) ≠ 0) (hout : x ∉ S) :
        ((shell x ∩ B).card : ℤ) ≤ 7 := by
      have hproper : shell x ∩ B ⊂ shell x := by
        refine ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
        intro heq
        exact hnone ⟨x, hx, hout, heq ▸ (inter_subset_right : shell x ∩ B ⊆ B)⟩
      have hlt := card_lt_card hproper
      rw [shell_card] at hlt
      omega
    have h7 := hbound 7 (by norm_num) hcap
    omega

private def weightLayer (k : ℕ) : Word :=
  univ.filter fun x => distance 0 x = k

private theorem mem_weightLayer {x : Vertex} {k : ℕ} :
    x ∈ weightLayer k ↔ distance 0 x = k := by
  simp [weightLayer]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem level_counts :
    weightLayer 1 = shell 0 ∧
    ∀ x : Vertex, (x ∈ weightLayer 1 → shell x ⊆ insert 0 (weightLayer 2)) ∧
      (x ∈ weightLayer 2 → (shell x ∩ weightLayer 1).card = 2 ∧
        (shell x ∩ weightLayer 3).card = 6) ∧
      (x ∈ weightLayer 3 → shell x ⊆ weightLayer 2 ∪ weightLayer 4) ∧
      (x ∈ weightLayer 4 → (shell x ∩ weightLayer 3).card = 4 ∧
        (shell x ∩ weightLayer 5).Nonempty) ∧
      (x ∈ weightLayer 5 → Disjoint (shell x) (weightLayer 2)) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem common_lower_row_of_two {k : ℕ} (hk : k = 2 ∨ k = 4)
    (t x y : Vertex) (ht : t ∈ weightLayer (k + 1))
    (hx : x ∈ shell t ∩ weightLayer k) (hy : y ∈ shell t ∩ weightLayer k)
    (hne : x ≠ y) :
    (shell x ∩ shell y ∩ weightLayer (k - 1)).Nonempty ∧
      shell x ∩ shell y ∩ weightLayer (k + 1) ⊆ {t} := by
  obtain rfl | rfl := hk
  · have h : ∀ t : Vertex, t ∈ weightLayer 3 → ∀ x : Vertex, x ∈ shell t ∩ weightLayer 2 →
        ∀ y : Vertex, y ∈ shell t ∩ weightLayer 2 → x ≠ y →
        (shell x ∩ shell y ∩ weightLayer 1).Nonempty ∧
          shell x ∩ shell y ∩ weightLayer 3 ⊆ {t} := by
      decide +kernel
    exact h t ht x hx y hy hne
  · have h : ∀ t : Vertex, t ∈ weightLayer 5 → ∀ x : Vertex, x ∈ shell t ∩ weightLayer 4 →
        ∀ y : Vertex, y ∈ shell t ∩ weightLayer 4 → x ≠ y →
        (shell x ∩ shell y ∩ weightLayer 3).Nonempty ∧
          shell x ∩ shell y ∩ weightLayer 5 ⊆ {t} := by
      decide +kernel
    exact h t ht x hx y hy hne

private theorem sum_shell_inter_comm (U V : Word) :
    (∑ u ∈ U, (shell u ∩ V).card) = ∑ v ∈ V, (shell v ∩ U).card := by
  have h₁ (u : Vertex) :
      V.bipartiteAbove (fun u v : Vertex => v ∈ shell u) u = shell u ∩ V := by
    ext v
    simp [Finset.bipartiteAbove, and_comm]
  have h₂ (v : Vertex) :
      U.bipartiteBelow (fun u v : Vertex => v ∈ shell u) v = shell v ∩ U := by
    ext u
    simp only [Finset.bipartiteBelow, mem_filter, mem_inter]
    rw [shell_symm (x := v) (y := u), and_comm]
  simpa only [h₁, h₂] using
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := U) (t := V) (fun u v : Vertex => v ∈ shell u)

private theorem no_full_shell_at_zero {S B : Word} (hsize : S.card = 16)
    (hz : 0 ∉ S) (hfull : shell 0 ⊆ B)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0) : False := by
  classical
  let L := S ∩ weightLayer 2
  let P := S ∩ weightLayer 4
  let T := (weightLayer 3).filter fun x => (shell x ∩ L).card = 1
  let D := (weightLayer 3).filter fun x => (shell x ∩ L).card = 2
  have hLsub : L ⊆ S := inter_subset_left
  have hPsub : P ⊆ S := inter_subset_left
  have hLlevel : L ⊆ weightLayer 2 := inter_subset_right
  have hPlevel : P ⊆ weightLayer 4 := inter_subset_right
  have hLP : Disjoint L P := by
    apply disjoint_left.mpr
    intro x hx hy
    have h₂ := mem_weightLayer.mp (hLlevel hx)
    have h₄ := mem_weightLayer.mp (hPlevel hy)
    omega
  have hrow_of_pos (x : Vertex) (hx : (shell x ∩ S).Nonempty) :
      (shell x ∩ S).card = 2 := by
    have h := hdegree x
    have hpos := card_pos.mpr hx
    split at h <;> omega
  have hLrow (x : Vertex) (hx : x ∈ weightLayer 1) : (shell x ∩ L).card = 2 := by
    have hb : x ∈ B := hfull (level_counts.1 ▸ hx)
    have heq : shell x ∩ L = shell x ∩ S := by
      apply Subset.antisymm
      · intro y hy
        exact mem_inter.mpr ⟨(mem_inter.mp hy).1, hLsub (mem_inter.mp hy).2⟩
      · intro y hy
        obtain ⟨hyx, hyS⟩ := mem_inter.mp hy
        have h := (level_counts.2 x).1 hx hyx
        rcases mem_insert.mp h with rfl | h
        · exact False.elim (hz hyS)
        · exact mem_inter.mpr ⟨hyx, mem_inter.mpr ⟨hyS, h⟩⟩
    rw [heq, hdegree, if_pos hb]
  have hLcard : L.card = 8 := by
    have h := sum_shell_inter_comm (weightLayer 1) L
    rw [show (∑ x ∈ weightLayer 1, (shell x ∩ L).card) =
        ∑ _x ∈ weightLayer 1, (2 : ℕ) from sum_congr rfl hLrow] at h
    rw [show (∑ x ∈ L, (shell x ∩ weightLayer 1).card) =
        ∑ _x ∈ L, (2 : ℕ) from sum_congr rfl
          (fun x hx => ((level_counts.2 x).2.1 (hLlevel hx)).1)] at h
    rw [level_counts.1] at h
    simp only [sum_const, nsmul_eq_mul, shell_card] at h
    omega
  let r := fun u t : Vertex => shell u ∩ L ⊆ shell t ∩ L
  have hcoverD (t : Vertex) (ht : t ∈ D) : ∃ u ∈ weightLayer 1, r u t := by
    obtain ⟨ht₃, ht₂⟩ := mem_filter.mp ht
    obtain ⟨x, y, hxy, heq⟩ := card_eq_two.mp ht₂
    have hx : x ∈ shell t ∩ L := by simp [heq]
    have hy : y ∈ shell t ∩ L := by simp [heq]
    obtain ⟨u, hu⟩ := (common_lower_row_of_two (Or.inl rfl) t x y ht₃
      (mem_inter.mpr ⟨(mem_inter.mp hx).1, hLlevel (mem_inter.mp hx).2⟩)
      (mem_inter.mpr ⟨(mem_inter.mp hy).1, hLlevel (mem_inter.mp hy).2⟩) hxy).1
    obtain ⟨huShell, hu₁⟩ := mem_inter.mp hu
    obtain ⟨hux, huy⟩ := mem_inter.mp huShell
    have hpair : ({x, y} : Word) ⊆ shell u ∩ L := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_inter.mpr ⟨shell_symm.mp hux, (mem_inter.mp hx).2⟩
      · rw [mem_singleton] at hv
        subst v
        exact mem_inter.mpr ⟨shell_symm.mp huy, (mem_inter.mp hy).2⟩
    refine ⟨u, hu₁, ?_⟩
    change shell u ∩ L ⊆ shell t ∩ L
    rw [heq]
    exact (eq_of_subset_of_card_le hpair (by rw [hLrow u hu₁, card_pair hxy])).ge
  have hcapD (u : Vertex) (hu : u ∈ weightLayer 1) :
      ((D.bipartiteAbove r u).card : ℤ) ≤ 1 := by
    suffices h : (D.bipartiteAbove r u).card ≤ 1 by exact_mod_cast h
    apply card_le_one.mpr
    intro t ht t' ht'
    obtain ⟨htD, htR⟩ : t ∈ D ∧ r u t := by
      simpa [Finset.bipartiteAbove] using ht
    obtain ⟨ht'D, ht'R⟩ : t' ∈ D ∧ r u t' := by
      simpa [Finset.bipartiteAbove] using ht'
    obtain ⟨x, y, hxy, heq⟩ := card_eq_two.mp (hLrow u hu)
    have hx : x ∈ shell u ∩ L := by simp [heq]
    have hy : y ∈ shell u ∩ L := by simp [heq]
    have hxt := mem_inter.mp (htR hx)
    have hyt := mem_inter.mp (htR hy)
    have hxt' := mem_inter.mp (ht'R hx)
    have hyt' := mem_inter.mp (ht'R hy)
    have h := (common_lower_row_of_two (Or.inl rfl) t x y (mem_filter.mp htD).1
      (mem_inter.mpr ⟨hxt.1, hLlevel hxt.2⟩)
      (mem_inter.mpr ⟨hyt.1, hLlevel hyt.2⟩) hxy).2
      (mem_inter.mpr ⟨mem_inter.mpr ⟨shell_symm.mp hxt'.1, shell_symm.mp hyt'.1⟩,
        (mem_filter.mp ht'D).1⟩)
    exact (mem_singleton.mp h).symm
  have hDcard : D.card ≤ 8 := by
    have h := card_le_weighted_cover (weightLayer 1) D r (fun _ => 1) hcoverD hcapD
    rw [level_counts.1] at h
    simp only [sum_const, nsmul_eq_mul, shell_card, Nat.cast_ofNat, mul_one] at h
    omega
  have hTcard : 32 ≤ T.card := by
    have h := sum_shell_inter_comm (weightLayer 3) L
    rw [show (∑ x ∈ L, (shell x ∩ weightLayer 3).card) =
        ∑ _x ∈ L, (6 : ℕ) from sum_congr rfl
          (fun x hx => ((level_counts.2 x).2.1 (hLlevel hx)).2)] at h
    simp only [sum_const, nsmul_eq_mul, hLcard] at h
    have heq (x : Vertex) (hx : x ∈ weightLayer 3) :
        (shell x ∩ L).card = (if (shell x ∩ L).card = 1 then 1 else 0) +
          2 * (if (shell x ∩ L).card = 2 then 1 else 0) := by
      have hsub : shell x ∩ L ⊆ shell x ∩ S :=
        fun y hy => mem_inter.mpr ⟨(mem_inter.mp hy).1, hLsub (mem_inter.mp hy).2⟩
      have hle := card_le_card hsub
      rw [hdegree] at hle
      split at hle <;> split <;> split <;> omega
    rw [sum_congr rfl heq, sum_add_distrib, ← mul_sum, ← sum_filter, ← sum_filter] at h
    change (∑ _x ∈ T, (1 : ℕ)) + 2 * (∑ _x ∈ D, (1 : ℕ)) = _ at h
    simp only [sum_const, nsmul_eq_mul, mul_one] at h
    omega
  have hProw (x : Vertex) (hx : x ∈ T) : (shell x ∩ P).card = 1 := by
    obtain ⟨hx₃, hx₁⟩ := mem_filter.mp hx
    have heq : shell x ∩ S = (shell x ∩ L) ∪ (shell x ∩ P) := by
      ext y
      simp only [mem_inter, mem_union, L, P]
      constructor
      · rintro ⟨hyx, hyS⟩
        rcases mem_union.mp ((level_counts.2 x).2.2.1 hx₃ hyx) with h | h
        · exact Or.inl ⟨hyx, hyS, h⟩
        · exact Or.inr ⟨hyx, hyS, h⟩
      · rintro (⟨hyx, hyS, _⟩ | ⟨hyx, hyS, _⟩) <;> exact ⟨hyx, hyS⟩
    have hdisj : Disjoint (shell x ∩ L) (shell x ∩ P) :=
      hLP.mono inter_subset_right inter_subset_right
    have hne : (shell x ∩ S).Nonempty := by
      rw [heq]
      obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < (shell x ∩ L).card)
      exact ⟨y, mem_union_left _ hy⟩
    have h := hrow_of_pos x hne
    rw [heq, card_union_of_disjoint hdisj, hx₁] at h
    omega
  have hTsum : ∑ x ∈ P, (shell x ∩ T).card = T.card := by
    rw [sum_shell_inter_comm P T, sum_congr rfl hProw]
    simp
  have hboundP (x : Vertex) (hx : x ∈ P) : (shell x ∩ T).card ≤ 4 := by
    have hsub : shell x ∩ T ⊆ shell x ∩ weightLayer 3 :=
      fun y hy => mem_inter.mpr ⟨(mem_inter.mp hy).1, (mem_filter.mp (mem_inter.mp hy).2).1⟩
    exact (card_le_card hsub).trans_eq ((level_counts.2 x).2.2.2.1 (hPlevel hx)).1
  have hsumle : T.card ≤ 4 * P.card := by
    have h := sum_le_sum hboundP
    rw [hTsum] at h
    simpa [mul_comm] using h
  have hSsub : L ∪ P ⊆ S := union_subset hLsub hPsub
  have hsizeLP := card_le_card hSsub
  rw [card_union_of_disjoint hLP, hLcard, hsize] at hsizeLP
  have hPcard : P.card = 8 := by omega
  have hSeq : L ∪ P = S := eq_of_subset_of_card_le hSsub (by
    rw [card_union_of_disjoint hLP, hLcard, hPcard, hsize])
  have hlow (p : Vertex) (hp : p ∈ P) : shell p ∩ weightLayer 3 ⊆ T := by
    have heq : (shell p ∩ T).card = 4 := by
      by_contra hn
      have hlt : (shell p ∩ T).card < 4 := by have := hboundP p hp; omega
      have h := sum_lt_sum hboundP ⟨p, hp, hlt⟩
      rw [hTsum] at h
      simp only [sum_const, nsmul_eq_mul, hPcard] at h
      omega
    have hsub : shell p ∩ T ⊆ shell p ∩ weightLayer 3 :=
      fun y hy => mem_inter.mpr ⟨(mem_inter.mp hy).1, (mem_filter.mp (mem_inter.mp hy).2).1⟩
    have hfull := eq_of_subset_of_card_le hsub (by
      rw [heq, ((level_counts.2 p).2.2.2.1 (hPlevel hp)).1])
    intro y hy
    have hy' : y ∈ shell p ∩ T := by rwa [hfull]
    exact (mem_inter.mp hy').2
  obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < P.card)
  obtain ⟨t, ht⟩ := ((level_counts.2 p).2.2.2.1 (hPlevel hp)).2
  obtain ⟨htp, ht₅⟩ := mem_inter.mp ht
  have heqTop : shell t ∩ S = shell t ∩ P := by
    ext y
    rw [← hSeq, mem_inter, mem_inter, mem_union]
    constructor
    · rintro ⟨hyt, hy | hy⟩
      · exact False.elim (disjoint_left.mp ((level_counts.2 t).2.2.2.2 ht₅)
          hyt (hLlevel hy))
      · exact ⟨hyt, hy⟩
    · exact fun ⟨hyt, hy⟩ => ⟨hyt, Or.inr hy⟩
  have hpRow : p ∈ shell t ∩ P := mem_inter.mpr ⟨shell_symm.mp htp, hp⟩
  have htwo : (shell t ∩ P).card = 2 := by
    rw [← heqTop]
    exact hrow_of_pos t ⟨p, heqTop.symm ▸ hpRow⟩
  obtain ⟨x, y, hxy, heq⟩ := card_eq_two.mp htwo
  have hx : x ∈ shell t ∩ P := by simp [heq]
  have hy : y ∈ shell t ∩ P := by simp [heq]
  obtain ⟨u, hu⟩ := (common_lower_row_of_two (Or.inr rfl) t x y ht₅
    (mem_inter.mpr ⟨(mem_inter.mp hx).1, hPlevel (mem_inter.mp hx).2⟩)
    (mem_inter.mpr ⟨(mem_inter.mp hy).1, hPlevel (mem_inter.mp hy).2⟩) hxy).1
  obtain ⟨huxy, hu₃⟩ := mem_inter.mp hu
  obtain ⟨hux, huy⟩ := mem_inter.mp huxy
  have huT := hlow x (mem_inter.mp hx).2 (mem_inter.mpr ⟨hux, hu₃⟩)
  have hpair : ({x, y} : Word) ⊆ shell u ∩ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_inter.mpr ⟨shell_symm.mp hux, (mem_inter.mp hx).2⟩
    · rw [mem_singleton] at hv
      subst v
      exact mem_inter.mpr ⟨shell_symm.mp huy, (mem_inter.mp hy).2⟩
  have hle := card_le_card hpair
  rw [hProw u huT, card_pair hxy] at hle
  omega

private theorem no_full_exterior_shell_at_weight_sixteen {S B : Word} (hsize : S.card = 16)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (z : Vertex) (hz : z ∉ S) (hfull : shell z ⊆ B) : False := by
  let σ := Equiv.refl (Fin 8)
  let e := relabel σ z
  have he : e z = 0 := relabel_center σ z
  have hshell (x : Vertex) : (shell x).map e.toEmbedding = shell (e x) :=
    relabel_shell σ z x
  have hS : (S.map e.toEmbedding).card = 16 := by rwa [card_map]
  have hzero : (0 : Vertex) ∉ S.map e.toEmbedding := by
    rw [← he, mem_map_equiv, Equiv.symm_apply_apply]
    exact hz
  have hshell0 : shell 0 ⊆ B.map e.toEmbedding := by
    rw [← he, ← hshell]
    intro x hx
    rw [mem_map_equiv] at hx ⊢
    exact hfull hx
  apply no_full_shell_at_zero hS hzero hshell0
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← hshell, ← map_inter, card_map, mem_map_equiv, Equiv.symm_apply_apply]
  exact hdegree y

/-- The residual of an order-72 signed fold with twelve dimers has empty odd
support whenever every row meets that support in zero or two neighbors. -/
theorem sparse_syndrome_empty_at_order_72
    (d e o : Q 8 → ℤ) (S B : Word)
    (hd : (∑ x, d x ^ 2) = 12)
    (hdisj : ∀ x, d x * e x = 0)
    (hcount : (∑ x, e x ^ 2) + (∑ x, o x ^ 2) = 48)
    (hsum : ∀ x, transverse (fun y => 2 * d y + e y) x = 4 * o x)
    (hfold : ∀ x, transverse o x = 4 * d x + 2 * e x)
    (hdegree : ∀ x, (shell x ∩ S).card = if x ∈ B then 2 else 0)
    (hsyndrome : ∀ x, (transverse d (cube x) - 2 * o (cube x)) % 2 = 1 ↔ x ∈ S) :
    S = ∅ := by
  rcases sparse_syndrome_at_order_72 d e o S B hd hdisj hcount hsum hfold hdegree hsyndrome with
    h | ⟨hsize, z, _, hz, hshell⟩
  · exact h
  · exact (no_full_exterior_shell_at_weight_sixteen hsize hdegree z hz hshell).elim

#print axioms sparse_syndrome_energy
#print axioms sparse_syndrome_empty_at_order_72

end Q9SparseSyndromeObstruction
end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
