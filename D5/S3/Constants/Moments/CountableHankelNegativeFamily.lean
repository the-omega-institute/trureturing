/- GID: D5/S3/Constants/Moments/CountableHankelNegativeFamily
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelNegativeFamily
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: A common head and exponent give a complete-spectrum negative family. -/

import D5.S3.Constants.Moments.CountableHankelNegativeWitness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-! The selector contains distinct, pairwise separated conjugate pairs. The
entire absolutely summable complement is bounded uniformly in the real vector.
No additional nonreality hypothesis is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial Filter
open scoped BigOperators ComplexConjugate Topology

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

/-- One real polynomial family has a uniform unit negative gap on every real
combination. Every original node and weight is retained, including the tail. -/
theorem exists_real_negative_family {ι : Type*} {k : ℕ} (z w : ι → ℂ)
    (c : Equiv.Perm ι) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hzi : Function.Injective z) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (hfinite : ∀ r : ℝ, 0 < r → {i | r ≤ ‖z i‖}.Finite)
    (s : Fin k → ι) (hs : Function.Injective s)
    (hsep : ∀ a b, s a ≠ c (s b)) (hws : ∀ j, w (s j) ≠ 0) :
    ∃ p : Fin k → ℝ[X], ∀ t : Fin k → ℝ,
      (∑' i, w i * ((∑ j, t j • p j).eval₂ Complex.ofRealHom (z i)) ^ 2).re ≤
        -(∑ j, (t j) ^ 2) := by
  classical
  by_cases hk : k = 0
  · subst k
    exact ⟨fun j => Fin.elim0 j, by simp⟩
  have hnonempty : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_univ _⟩
  have hni (j : Fin k) : conj (z (s j)) ≠ z (s j) := by
    intro h
    apply hsep j j
    exact (hzi ((hzc (s j)).trans h)).symm
  have hzs (j : Fin k) : z (s j) ≠ 0 := by
    intro h
    apply hni j
    simp [h]
  let ρ : ℝ := Finset.univ.inf' hnonempty (fun j => ‖z (s j)‖)
  have hρ : 0 < ρ := by
    exact (Finset.lt_inf'_iff hnonempty).mpr (fun j _ => norm_pos_iff.mpr (hzs j))
  have hρj (j : Fin k) : ρ ≤ ‖z (s j)‖ :=
    Finset.inf'_le _ (Finset.mem_univ j)
  let E := (hfinite (ρ / 4) (by positivity)).toFinset
  have hE (i : ι) : i ∈ E ↔ ρ / 4 ≤ ‖z i‖ := by simp [E]
  have hEc (i : ι) : i ∈ E ↔ c i ∈ E := by
    rw [hE, hE, hzc, Complex.norm_conj]
  have hsE (j : Fin k) : s j ∈ E := (hE _).mpr (by linarith [hρj j])
  choose p hp using fun j => pair_polynomial z c hzc E hEc (s j) (hsE j) (hni j)
  choose b hb using fun j =>
    IsAlgClosed.exists_pow_nat_eq (-1 / w (s j)) (by omega : 0 < (2 : ℕ))
  have hwb (j : Fin k) : w (s j) * (b j) ^ 2 = -1 := by
    rw [hb j]
    field_simp [hws j]
  let P (m : ℕ) (j : Fin k) : ℝ[X] := peak (p j) (z (s j)) (b j) m
  let q (m : ℕ) (t : Fin k → ℝ) : ℝ[X] := ∑ j, t j • P m j
  have hconj (v : ℝ[X]) (i : ι) :
      v.eval₂ Complex.ofRealHom (z (c i)) = conj (v.eval₂ Complex.ofRealHom (z i)) := by
    rw [hzc]
    exact Polynomial.aeval_conj v (z i)
  have hvalue (m : ℕ) (j l : Fin k) :
      (P m j).eval₂ Complex.ofRealHom (z (s l)) = if j = l then b j else 0 := by
    by_cases hjl : j = l
    · subst l
      have hpj : (p j).eval₂ Complex.ofRealHom (z (s j)) = Complex.I := by
        simpa using hp j (s j) (hsE j)
      simpa [P] using peak_at (p j) (z (s j)) (b j) (hzs j) hpj m
    · have hnode : z (s l) ≠ z (s j) := fun h => hjl (hs (hzi h)).symm
      have hpair : z (s l) ≠ conj (z (s j)) := by
        intro h
        exact hsep l j (hzi (h.trans (hzc (s j)).symm))
      have hpzero : (p j).eval₂ Complex.ofRealHom (z (s l)) = 0 := by
        simpa [hnode, hpair] using hp j (s l) (hsE l)
      simp [P, peak, Polynomial.eval₂_pow, hpzero, hjl]
  have hqvalue (m : ℕ) (t : Fin k → ℝ) (j : Fin k) :
      (q m t).eval₂ Complex.ofRealHom (z (s j)) = (t j : ℂ) * b j := by
    simp [q, Polynomial.eval₂_finsetSum, Polynomial.eval₂_smul, hvalue, mul_ite]
  let L : Finset ι := Finset.univ.image s
  let R : Finset ι := Finset.univ.image (fun j => c (s j))
  have hLR : Disjoint L R := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiL hiR
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hiL
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hiR
    exact hsep a b (ha.trans hb.symm)
  have hhead (m : ℕ) (t : Fin k → ℝ) :
      (∑ i ∈ E, w i * ((q m t).eval₂ Complex.ofRealHom (z i)) ^ 2) =
        -2 * (∑ j, ((t j : ℂ) ^ 2)) := by
    have hsubset : L ∪ R ⊆ E := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
        exact hsE j
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
        exact (hEc _).mp (hsE j)
    have hout (i : ι) (hi : i ∈ E) (hnot : i ∉ L ∪ R) :
        (q m t).eval₂ Complex.ofRealHom (z i) = 0 := by
      have hzj (j : Fin k) : z i ≠ z (s j) := by
        intro h
        apply hnot
        exact Finset.mem_union_left R (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (hzi h).symm⟩)
      have hzcj (j : Fin k) : z i ≠ conj (z (s j)) := by
        intro h
        apply hnot
        exact Finset.mem_union_right L (Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, (hzi (h.trans (hzc (s j)).symm)).symm⟩)
      have hpzero (j : Fin k) : (p j).eval₂ Complex.ofRealHom (z i) = 0 := by
        simpa [hzj j, hzcj j] using hp j i hi
      simp [q, P, peak, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, hpzero]
    calc
      _ = ∑ i ∈ L ∪ R, w i * ((q m t).eval₂ Complex.ofRealHom (z i)) ^ 2 := by
        symm
        apply Finset.sum_subset hsubset
        intro i hi hnot
        simp [hout i hi hnot]
      _ = (∑ j, w (s j) * ((q m t).eval₂ Complex.ofRealHom (z (s j))) ^ 2) +
          ∑ j, w (c (s j)) * ((q m t).eval₂ Complex.ofRealHom (z (c (s j)))) ^ 2 := by
        rw [Finset.sum_union hLR]
        congr 1
        · exact Finset.sum_image (fun a _ b _ h => hs h)
        · exact Finset.sum_image (fun a _ b _ h => hs (c.injective h))
      _ = ∑ j, (-2 * (t j : ℂ) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [hconj, hqvalue, hwc]
        have hcb : conj (w (s j)) * (conj (b j)) ^ 2 = -1 := by
          simpa only [map_mul, map_pow, map_neg, map_one] using congrArg conj (hwb j)
        simp only [map_mul, Complex.conj_ofReal, mul_pow]
        calc
          _ = (t j : ℂ) ^ 2 * (w (s j) * (b j) ^ 2) +
              (t j : ℂ) ^ 2 * (conj (w (s j)) * (conj (b j)) ^ 2) := by ring
          _ = _ := by rw [hwb, hcb]; ring
      _ = _ := by rw [Finset.mul_sum]
  let C (j : Fin k) : ℝ := ∑ a ∈ (p j).support, |(p j).coeff a|
  let B (j : Fin k) : ℝ := ‖b j‖ * ((C j) ^ 2 + C j)
  let K : ℝ := ∑ j, (B j) ^ 2
  have hC (j : Fin k) : 0 ≤ C j := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB (j : Fin k) : 0 ≤ B j := by dsimp [B]; positivity
  have htail (m : ℕ) (j : Fin k) (i : {i // i ∉ E}) :
      ‖(P m j).eval₂ Complex.ofRealHom (z i)‖ ≤ B j * (1 / 4 : ℝ) ^ m := by
    have hsmall : ‖z i‖ < ρ / 4 := lt_of_not_ge (by simpa only [← hE] using i.property)
    have hratio : ‖z i‖ / ‖z (s j)‖ ≤ 1 / 4 := by
      apply (div_le_iff₀ (norm_pos_iff.mpr (hzs j))).mpr
      linarith [hρj j]
    exact (peak_bound (p j) (z (s j)) (b j) (z i) (hzs j) (hz i) m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio m) (hB j))
  have htail_sq (m : ℕ) (t : Fin k → ℝ) (i : {i // i ∉ E}) :
      ‖(q m t).eval₂ Complex.ofRealHom (z i)‖ ^ 2 ≤
        K * (1 / 16 : ℝ) ^ m * (∑ j, (t j) ^ 2) := by
    have hnorm : ‖(q m t).eval₂ Complex.ofRealHom (z i)‖ ≤
        (∑ j, |t j| * B j) * (1 / 4 : ℝ) ^ m := by
      calc
        _ = ‖∑ j, (t j : ℂ) * (P m j).eval₂ Complex.ofRealHom (z i)‖ := by
          simp [q, Polynomial.eval₂_finsetSum, Polynomial.eval₂_smul]
        _ ≤ ∑ j, ‖(t j : ℂ) * (P m j).eval₂ Complex.ofRealHom (z i)‖ := norm_sum_le _ _
        _ ≤ ∑ j, |t j| * (B j * (1 / 4 : ℝ) ^ m) := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (htail m j i) (abs_nonneg _)
        _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |t j|) B
    have hpow : ((1 / 4 : ℝ) ^ m) ^ 2 = (1 / 16 : ℝ) ^ m := by
      rw [← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    calc
      _ ≤ ((∑ j, |t j| * B j) * (1 / 4 : ℝ) ^ m) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = (∑ j, |t j| * B j) ^ 2 * (1 / 16 : ℝ) ^ m := by rw [mul_pow, hpow]
      _ ≤ ((∑ j, (t j) ^ 2) * K) * (1 / 16 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [sq_abs, K] using hcs
      _ = _ := by ring
  let W := ∑' i : {i // i ∉ E}, ‖w i‖
  have hW : Summable (fun i : {i // i ∉ E} => ‖w i‖) := hw.subtype _
  have htail_sum (m : ℕ) (t : Fin k → ℝ) :
      ‖∑' i : {i // i ∉ E}, w i * ((q m t).eval₂ Complex.ofRealHom (z i)) ^ 2‖ ≤
        W * K * (1 / 16 : ℝ) ^ m * (∑ j, (t j) ^ 2) := by
    calc
      _ ≤ ∑' i : {i // i ∉ E}, ‖w i‖ *
          (K * (1 / 16 : ℝ) ^ m * (∑ j, (t j) ^ 2)) := by
        apply tsum_of_norm_bounded (hW.mul_right _).hasSum
        intro i
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (htail_sq m t i) (norm_nonneg _)
      _ = _ := by rw [tsum_mul_right]; dsimp [W]; ring
  have hlim : Tendsto (fun m : ℕ => W * K * (1 / 16 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (W * K)
  obtain ⟨m, hm⟩ := (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  refine ⟨P m, ?_⟩
  intro t
  have hsplit := (square_summable z w hz hw (q m t)).sum_add_tsum_subtype_compl E
  change (∑' i, w i * ((q m t).eval₂ Complex.ofRealHom (z i)) ^ 2).re ≤ _
  rw [← hsplit, hhead, Complex.add_re]
  have hre := Complex.re_le_norm (∑' i : {i // i ∉ E},
    w i * ((q m t).eval₂ Complex.ofRealHom (z i)) ^ 2)
  have hS : 0 ≤ ∑ j, (t j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound := mul_le_mul_of_nonneg_right hm.le hS
  have htail_re := hre.trans (htail_sum m t)
  have hhead_re : (-2 * (∑ j, (t j : ℂ) ^ 2)).re = -2 * (∑ j, (t j) ^ 2) := by
    simp [pow_two, Complex.mul_re]
  rw [hhead_re]
  linarith

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
