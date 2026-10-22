/- GID: D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The half-density K-exclusion mode for small and large positive parameters. -/
/-
proof_shape: result: bind-only; every private theorem is a consumed bind-only helper.
escape_witness: none
admission_basis: open-problem-resolution (#18570; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19903
Direct frozen dependencies:
D5.S3.Combinatorics.CylindricPartition.LiUncuDefs.gauss:
sha256:f926774c1dcfc4f25ac8221be84ee089ae2dae1d643c4699259ccb4d03819006
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt:
sha256:0e125cb16efe1cee78886ce2c6b059bc6a36c38c6740dcddafa53b67a66ba327
The weights, configurations and claim use the source expressions of arXiv:2310.03343v2.
The proof is symbolic for all parameters and contains no finite numeric certificate.
The finite q-binomial induction adapts LeanPool/lean-pool, commit
 ae357410e8e2711ccd7fdb77e41859142331d355,
 LeanPool/PentagonalNumberTheoremAnalytic/QSeries/FiniteBinomial.lean.
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska.
Released under the Apache 2.0 license reproduced in the repository LICENSE.
-/
import D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import Mathlib.Data.Nat.Choose.Vandermonde

set_option autoImplicit false
namespace D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode
open Finset Polynomial Filter Topology
open D5.S3.Combinatorics.CylindricPartition.LiUncu
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
universe u
variable {R : Type*} {α : Type u} [Fintype α] [DecidableEq α]

noncomputable def qnum (t : ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, t ^ j
noncomputable def qfact (t : ℝ) (k : ℕ) : ℝ := ∏ j ∈ range k, qnum t (j + 1)
noncomputable def qbinom (t : ℝ) (k i : ℕ) : ℝ := if i ≤ k then qfact t k / (qfact t (k - i) * qfact t i) else 0
noncomputable def wt (K L : ℕ) (t : ℝ) (η : Fin L → Fin (K + 1)) : ℝ := ∏ i, t ^ (((η i : ℕ) * (η i : ℕ) + 2 - 3 * (η i : ℕ)) / 2) * qbinom t K (η i)
def configs (K L n : ℕ) : Finset (Fin L → Fin (K + 1)) := univ.filter fun η => ∑ i, (η i : ℕ) = n
noncomputable def occProb (K L n : ℕ) (t : ℝ) (s : Fin L) (a : ℕ) : ℝ := (∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), wt K L t η) / ∑ η ∈ configs K L n, wt K L t η
def claim : Prop := ∀ r K k : ℕ, ∀ hr : 2 ≤ r, 1 ≤ K → k < K →
    let π := (occProb K (2 * r) ((2 * k + 1) * r)); let s : Fin (2 * r) := (⟨0, by omega⟩)
    ∃ ε > 0, ∀ t : ℝ, 0 < t → (t < ε ∨ 1 / ε < t) → (2 * k + 1 < K → ∀ b ≤ K, b ≠ k → π t s b < π t s k) ∧ (K < 2 * k + 1 → ∀ b ≤ K, b ≠ k + 1 → π t s b < π t s (k + 1)) ∧ (2 * k + 1 = K → π t s k = π t s (k + 1) ∧ ∀ b ≤ K, b ≠ k → b ≠ k + 1 → π t s b < π t s k)
private noncomputable def gaussValue [CommRing R] (q : R) (n k : ℕ) : R := Polynomial.eval₂ (Int.castRingHom R) q (gauss n k)
@[simp] private theorem gaussValue_zero_right [CommRing R] (q : R) (n : ℕ) : gaussValue q n 0 = 1 := by simp [gaussValue, gauss]
@[simp] private theorem gaussValue_zero_succ [CommRing R] (q : R) (k : ℕ) : gaussValue q 0 (k + 1) = 0 := by simp [gaussValue, gauss]
private theorem gaussValue_pascal [CommRing R] (n k : ℕ) (q : R) : gaussValue q (n + 1) (k + 1) = gaussValue q n (k + 1) + q ^ (n - k) * gaussValue q n k := by simp [gaussValue, gauss]
private theorem gaussValue_zero_of_lt [CommRing R] (q : R) {n k : ℕ} (hk : n < k) : gaussValue q n k = 0 := by simp [gaussValue, gauss_zero_of_lt n k hk]
private theorem finite_q_binomial_from_gauss [CommRing R] (q z : R) (n : ℕ) : ∏ k ∈ Finset.range n, (1 + z * q ^ k) = ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * gaussValue q n k * z ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]; rw [Finset.sum_range_succ' (fun k => q ^ k.choose 2 * gaussValue q (n + 1) k * z ^ k) (n + 1)]; simp only [Nat.choose_zero_succ, pow_zero, gaussValue_zero_right, mul_one]
      have stepB : (∑ k ∈ Finset.range (n + 1), q ^ (k + 1).choose 2 * gaussValue q (n + 1) (k + 1) * z ^ (k + 1)) = (∑ k ∈ Finset.range (n + 1), q ^ (k + 1).choose 2 * gaussValue q n (k + 1) * z ^ (k + 1)) + ∑ k ∈ Finset.range (n + 1), q ^ (k + 1).choose 2 * q ^ (n - k) * gaussValue q n k * z ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; rw [gaussValue_pascal]; ring
      rw [stepB]; have stepC : (∑ k ∈ Finset.range (n + 1), q ^ (k + 1).choose 2 * q ^ (n - k) * gaussValue q n k * z ^ (k + 1)) = z * q ^ n * ∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * gaussValue q n k * z ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk; have hkle : k ≤ n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)); have hchoose : (k + 1).choose 2 = k.choose 2 + k := (by simpa only [Nat.choose_two_right] using Nat.triangle_succ k); rw [hchoose, pow_add q (k.choose 2) k, mul_assoc (q ^ k.choose 2) (q ^ k) (q ^ (n - k)), ← pow_add q k (n - k), show k + (n - k) = n from by omega, pow_succ z k]; ring
      rw [stepC]; have stepD : (∑ k ∈ Finset.range (n + 1), q ^ k.choose 2 * gaussValue q n k * z ^ k) = (∑ k ∈ Finset.range (n + 1), q ^ (k + 1).choose 2 * gaussValue q n (k + 1) * z ^ (k + 1)) + 1 := by
        have h := (Finset.sum_range_succ' (fun k => q ^ k.choose 2 * gaussValue q n k * z ^ k) (n + 1)); simp only [Nat.choose_zero_succ, pow_zero, gaussValue_zero_right, mul_one] at h; rw [Finset.sum_range_succ (f := fun k => q ^ k.choose 2 * gaussValue q n k * z ^ k) (n := n + 1), gaussValue_zero_of_lt q (Nat.lt_succ_self n)] at h; simp only [mul_zero, zero_mul, add_zero] at h; exact h
      linear_combination stepD
private theorem qnum_pos {t : ℝ} (ht : 0 < t) {a : ℕ} (ha : 0 < a) : 0 < qnum t a := by exact geom_sum_pos ht.le (Nat.ne_of_gt ha)
private theorem qfact_pos {t : ℝ} (ht : 0 < t) (a : ℕ) : 0 < qfact t a := by exact Finset.prod_pos (fun j _ => qnum_pos ht (by omega))
private theorem qnum_add (t : ℝ) (a b : ℕ) : qnum t (a + b) = qnum t a + t ^ a * qnum t b := by simp only [qnum, Finset.sum_range_add, pow_add, Finset.mul_sum]
private theorem qfact_succ (t : ℝ) (a : ℕ) : qfact t (a + 1) = qfact t a * qnum t (a + 1) := by exact Finset.prod_range_succ _ _
private theorem qbinom_symm (t : ℝ) {K a : ℕ} (ha : a ≤ K) : qbinom t K a = qbinom t K (K - a) := by
  simp only [qbinom, ite_eq_left ha, ite_eq_left (Nat.sub_le K a), Nat.sub_sub_self ha]; rw [mul_comm]
private theorem qbinom_zero (t : ℝ) {K a : ℕ} (ha : K < a) : qbinom t K a = 0 := by simp [qbinom, Nat.not_le.mpr ha]
private theorem qbinom_zero_right {t : ℝ} (ht : 0 < t) (K : ℕ) : qbinom t K 0 = 1 := by
  have h0 : qfact t 0 = 1 := (by simp [qfact]); simp [qbinom, h0, (qfact_pos ht K).ne']
private theorem qbinom_diag {t : ℝ} (ht : 0 < t) (K : ℕ) : qbinom t K K = 1 := by
  have h0 : qfact t 0 = 1 := (by simp [qfact]); simp [qbinom, h0, (qfact_pos ht K).ne']
private theorem qbinom_pascal {t : ℝ} (ht : 0 < t) (K a : ℕ) : qbinom t (K + 1) (a + 1) = qbinom t K (a + 1) + t ^ (K - a) * qbinom t K a := by
  by_cases ha : a < K
  · have h1 : a + 1 ≤ K := by omega
    have h2 : a ≤ K := (by omega); have h3 : a + 1 ≤ K + 1 := (by omega); have hd : K + 1 - (a + 1) = K - a := (by omega); have hd' : K - a = (K - (a + 1)) + 1 := (by omega); have hs : qnum t (K + 1) = qnum t (K - a) + t ^ (K - a) * qnum t (a + 1) := by
      rw [← qnum_add]
      congr 1
      omega
    have fK := ((qfact_pos ht K).ne'); have fa := ((qfact_pos ht a).ne'); have fd := ((qfact_pos ht (K - (a + 1))).ne'); have na := ((qnum_pos ht (show 0 < a + 1 by omega)).ne'); have nd := ((qnum_pos ht (show 0 < K - a by omega)).ne'); simp only [qbinom, ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, hd]; rw [qfact_succ t K, qfact_succ t a, hs]
    conv_lhs => rw [hd', qfact_succ]
    conv_rhs => rhs; rw [hd', qfact_succ]
    have nd' : qnum t (K - (a + 1) + 1) ≠ 0 := ((qnum_pos ht (by omega)).ne'); field_simp [fK, fa, fd, na, nd']
  · by_cases he : a = K
    · subst a
      simp [qbinom_diag ht, qbinom_zero t (show K < K + 1 by omega)]
    · rw [qbinom_zero t (by omega), qbinom_zero t (by omega), qbinom_zero t (by omega)]
      ring
private theorem gaussValue_eq_qbinom {t : ℝ} (ht : 0 < t) (K a : ℕ) : gaussValue t K a = qbinom t K a := by
  induction K generalizing a with
  | zero =>
      cases a with
      | zero => simpa using (qbinom_zero_right ht 0).symm
      | succ a => rw [gaussValue_zero_succ, qbinom_zero t (by omega)]
  | succ K ih =>
      cases a with
      | zero => simpa using (qbinom_zero_right ht (K + 1)).symm
      | succ a => rw [gaussValue_pascal, qbinom_pascal ht, ih, ih]
private theorem gaussValue_C (t : ℝ) (K a : ℕ) : gaussValue (Polynomial.C t) K a = Polynomial.C (gaussValue t K a) := by
  unfold gaussValue; rw [Polynomial.hom_eval₂]
  congr 1
private theorem site_generating_polynomial {t : ℝ} (ht : 0 < t) (K : ℕ) : (∏ j ∈ Finset.range K, (1 + Polynomial.C (t ^ j) * Polynomial.X)) = ∑ a ∈ Finset.range (K + 1), Polynomial.C (t ^ a.choose 2 * qbinom t K a) * Polynomial.X ^ a := by
  have h := (finite_q_binomial_from_gauss (Polynomial.C t) Polynomial.X K)
  simp_rw [gaussValue_C, gaussValue_eq_qbinom ht, ← Polynomial.C_pow, ← Polynomial.C_mul] at h
  simpa only [mul_comm Polynomial.X] using h
private theorem coeff_prod_one_add {α R : Type*} [DecidableEq α] [CommRing R] (S : Finset α) (w : α → R) (n : ℕ) : (∏ a ∈ S, (1 + Polynomial.C (w a) * Polynomial.X)).coeff n = ∑ T ∈ S.powersetCard n, ∏ a ∈ T, w a := by
  classical
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]; have hterm (T : Finset α) : (∏ a ∈ T, Polynomial.C (w a) * Polynomial.X) = Polynomial.C (∏ a ∈ T, w a) * Polynomial.X ^ T.card := by
    rw [Finset.prod_mul_distrib, ← map_prod]; simp
  simp_rw [hterm, Polynomial.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext T
    simp [Finset.mem_powersetCard, eq_comm]
  · intro T _
    rfl
private theorem single_site_fin_slot_sum {t : ℝ} (ht : 0 < t) (K a : ℕ) (ha : a ≤ K) : (∑ S ∈ (Finset.univ : Finset (Fin K)).powersetCard a, t ^ (∑ j ∈ S, j.val)) = t ^ a.choose 2 * qbinom t K a := by
  have hp : (∏ j : Fin K, (1 + Polynomial.C (t ^ j.val) * Polynomial.X)) = ∑ a ∈ Finset.range (K + 1), Polynomial.C (t ^ a.choose 2 * qbinom t K a) * Polynomial.X ^ a := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (1 + Polynomial.C (t ^ j) * Polynomial.X)) K]; exact site_generating_polynomial ht K
  have h := (congrArg (fun p : ℝ[X] => p.coeff a) hp); rw [coeff_prod_one_add, Polynomial.finsetSum_coeff] at h
  simp_rw [Finset.prod_pow_eq_pow_sum, Polynomial.coeff_C_mul_X_pow] at h
  rw [Finset.sum_eq_single a] at h
  · simpa using h
  · intro b hb hba
    simp [Ne.symm hba]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
private noncomputable def assignmentOcc {K L : ℕ} (C : Fin L → Finset (Fin K)) : Fin L → Fin (K + 1) := fun i => ⟨(C i).card, by
      have h := (Finset.card_le_card (Finset.subset_univ (C i))); simp only [Finset.card_univ, Fintype.card_fin] at h
      omega⟩
private theorem slotWt_assignment_fiber {K L : ℕ} {t : ℝ} (ht : 0 < t) (η : Fin L → Fin (K + 1)) : (∏ i, t ^ (η i : ℕ).choose 2 * qbinom t K (η i)) = ∑ C ∈ (Finset.univ : Finset (Fin L → Finset (Fin K))).filter (fun C => assignmentOcc C = η), t ^ (∑ i, ∑ j ∈ C i, j.val) := by
  classical
  have hsite (i : Fin L) : t ^ (η i : ℕ).choose 2 * qbinom t K (η i) = ∑ S : Finset (Fin K), if S.card = (η i : ℕ) then t ^ (∑ j ∈ S, j.val) else 0 := (by rw [← single_site_fin_slot_sum ht K (η i) (Nat.le_of_lt_succ (η i).isLt), Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.sum_filter])
  simp_rw [hsite]
  rw [Fintype.prod_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C _; rw [Fintype.prod_ite_zero, Finset.prod_pow_eq_pow_sum]; have he : (∀ i, (C i).card = (η i : ℕ)) ↔ assignmentOcc C = η := (by simp only [funext_iff, assignmentOcc, Fin.ext_iff]); simp only [he]
private theorem assignment_marginal_sum {K L : ℕ} {t : ℝ} (ht : 0 < t) (P : (Fin L → Fin (K + 1)) → Prop) [DecidablePred P] : (∑ η ∈ (Finset.univ : Finset (Fin L → Fin (K + 1)) ).filter P, ∏ i, t ^ (η i : ℕ).choose 2 * qbinom t K (η i)) = ∑ C ∈ (Finset.univ : Finset (Fin L → Finset (Fin K))).filter (fun C => P (assignmentOcc C)), t ^ (∑ i, ∑ j ∈ C i, j.val) := by
  classical
  simp_rw [slotWt_assignment_fiber ht]
  have h := (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin L → Finset (Fin K))) ((Finset.univ : Finset (Fin L → Fin (K + 1))).filter P) assignmentOcc (fun C => t ^ (∑ i, ∑ j ∈ C i, j.val)))
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
private def flattenSlots {K L : ℕ} (C : Fin L → Finset (Fin K)) : Finset (Fin L × Fin K) := (Finset.univ.sigma C).map (Equiv.sigmaEquivProd (Fin L) (Fin K)).toEmbedding
private noncomputable def slotRows {K L : ℕ} (S : Finset (Fin L × Fin K)) : Fin L → Finset (Fin K) := fun i => Finset.preimage S (Prod.mk i) (by intro a _ b _ h; exact (Prod.mk.inj h).2)
private theorem flattenSlots_slotRows {K L : ℕ} (S : Finset (Fin L × Fin K)) : flattenSlots (slotRows S) = S := by
  ext a
  rcases a with ⟨i,j⟩
  simp [flattenSlots, slotRows, Equiv.sigmaEquivProd, Equiv.toEmbedding]
  exact Finset.mem_preimage
private theorem slotRows_flattenSlots {K L : ℕ} (C : Fin L → Finset (Fin K)) : slotRows (flattenSlots C) = C := by
  funext i
  ext j
  simp [flattenSlots, slotRows, Equiv.sigmaEquivProd, Equiv.toEmbedding, Finset.mem_preimage]
private theorem flattenSlots_card {K L : ℕ} (C : Fin L → Finset (Fin K)) : (flattenSlots C).card = ∑ i, (C i).card := by
  simp [flattenSlots, Finset.card_sigma]
private theorem flattenSlots_energy {K L : ℕ} (C : Fin L → Finset (Fin K)) : (∑ a ∈ flattenSlots C, a.2.val) = ∑ i, ∑ j ∈ C i, j.val := by
  simp [flattenSlots, Finset.sum_sigma, Equiv.sigmaEquivProd, Equiv.toEmbedding]
private theorem flattenSlots_fiber {K L : ℕ} (C : Fin L → Finset (Fin K)) (s : Fin L) : ((flattenSlots C).filter (fun a => a.1 = s)).card = (C s).card := by
  simp [flattenSlots, Finset.filter_map, Finset.filter_sigma, Equiv.sigmaEquivProd, Equiv.toEmbedding]
  simp_rw [apply_ite Finset.card]
  simp
private theorem assignment_to_global_sum {K L : ℕ} (P : ℕ → ℕ → Prop) [DecidableRel P] (s : Fin L) (t : ℝ) : (∑ C ∈ (Finset.univ : Finset (Fin L → Finset (Fin K))).filter (fun C => P (∑ i, (C i).card) (C s).card), t ^ (∑ i, ∑ j ∈ C i, j.val)) = ∑ S ∈ (Finset.univ : Finset (Finset (Fin L × Fin K))).filter (fun S => P S.card (S.filter (fun p => p.1 = s)).card), t ^ (∑ p ∈ S, p.2.val) := by
  classical
  apply Finset.sum_bij (fun C _ => flattenSlots C)
  · intro C hC
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, flattenSlots_card, flattenSlots_fiber] using hC
  · intro C hC D hD he
    simpa only [slotRows_flattenSlots] using congrArg slotRows he
  · intro S hS
    refine ⟨slotRows S, ?_, flattenSlots_slotRows S⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢; have hc := (flattenSlots_card (slotRows S)); have hf := (flattenSlots_fiber (slotRows S) s); rw [flattenSlots_slotRows] at hc hf; rw [← hc, ← hf]; exact hS
  · intro C hC
    rw [flattenSlots_energy]
private def siteExponent (a : ℕ) : ℕ := (a * a + 2 - 3 * a) / 2
private theorem siteExponent_twice (a : ℕ) : 2 * siteExponent a + 3 * a = a * a + 2 := by
  rcases a with _ | _ | a
  · norm_num [siteExponent]
  · norm_num [siteExponent]
  · have he : (a + 2) * (a + 2) + 2 = a * (a + 1) + 3 * (a + 2) := by ring
    have hs : (a + 2) * (a + 2) + 2 - 3 * (a + 2) = a * (a + 1) := (by omega); change 2 * (((a + 2) * (a + 2) + 2 - 3 * (a + 2)) / 2) + 3 * (a + 2) = _; rw [hs]; have hd := (Nat.two_dvd_mul_add_one a); rw [Nat.mul_div_cancel' hd]; exact he.symm
private theorem siteExponent_shift (a : ℕ) : siteExponent a + a = 1 + a.choose 2 := by
  have h := (siteExponent_twice a); have hc : 2 * a.choose 2 + a = a * a := by
    cases a with
    | zero => simp
    | succ a =>
        rw [Nat.choose_two_right, Nat.succ_sub_one]; have hd : 2 ∣ (a + 1) * a := (by simpa only [Nat.mul_comm] using Nat.two_dvd_mul_add_one a); rw [Nat.mul_div_cancel' hd]; ring
  omega
private noncomputable def slotWt (K L : ℕ) (t : ℝ) (η : Fin L → Fin (K + 1)) : ℝ := ∏ i, t ^ (η i : ℕ).choose 2 * qbinom t K (η i)
private theorem wt_shift {K L n : ℕ} (η : Fin L → Fin (K + 1)) (t : ℝ) (hn : ∑ i, (η i : ℕ) = n) : t ^ n * wt K L t η = t ^ L * slotWt K L t η := by
  have hi (i : Fin L) : t ^ (η i : ℕ) * (t ^ siteExponent (η i : ℕ) * qbinom t K (η i)) = t * (t ^ (η i : ℕ).choose 2 * qbinom t K (η i)) := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm (η i : ℕ), siteExponent_shift, pow_add, pow_one]; ring
  have h := (Finset.prod_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) => hi i)); simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hn] at h
  simpa only [wt, slotWt, siteExponent, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] using h
private theorem occProb_slotWt {K L n : ℕ} {t : ℝ} (ht : t ≠ 0) (s : Fin L) (a : ℕ) : occProb K L n t s a = (∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), slotWt K L t η) / ∑ η ∈ configs K L n, slotWt K L t η := by
  classical
  let c := (t ^ L / t ^ n); have hw (η : Fin L → Fin (K + 1)) (hη : η ∈ configs K L n) : wt K L t η = c * slotWt K L t η := by
    apply (mul_left_cancel₀ (pow_ne_zero n ht))
    have hn := ((Finset.mem_filter.mp hη).2); rw [wt_shift η t hn]; dsimp [c]; field_simp
  unfold occProb; have hnum : (∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), wt K L t η) = c * ∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), slotWt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun η hη => hw η (Finset.mem_filter.mp hη).1)
  have hden : (∑ η ∈ configs K L n, wt K L t η) = c * ∑ η ∈ configs K L n, slotWt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl hw
  rw [hnum, hden, mul_div_mul_left _ _ (div_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ ht))]
private noncomputable def slotNum (K L n : ℕ) (t : ℝ) (s : Fin L) (a : ℕ) : ℝ := ∑ S ∈ ((Finset.univ : Finset (Fin L × Fin K)).powersetCard n).filter (fun S => (S.filter (fun p => p.1 = s)).card = a), t ^ (∑ p ∈ S, p.2.val)
private noncomputable def slotDen (K L n : ℕ) (t : ℝ) : ℝ := ∑ S ∈ (Finset.univ : Finset (Fin L × Fin K)).powersetCard n, t ^ (∑ p ∈ S, p.2.val)
private theorem slotWt_sum_to_slots {K L : ℕ} {t : ℝ} (ht : 0 < t) (s : Fin L) (P : ℕ → ℕ → Prop) [DecidableRel P] : (∑ η ∈ (Finset.univ : Finset (Fin L → Fin (K + 1))).filter (fun η => P (∑ i, (η i : ℕ)) (η s)), slotWt K L t η) = ∑ S ∈ (Finset.univ : Finset (Finset (Fin L × Fin K))).filter (fun S => P S.card (S.filter (fun p => p.1 = s)).card), t ^ (∑ p ∈ S, p.2.val) := by
  classical
  unfold slotWt; rw [assignment_marginal_sum ht]; change (∑ C ∈ (Finset.univ : Finset (Fin L → Finset (Fin K))).filter (fun C => P (∑ i, (C i).card) (C s).card), t ^ (∑ i, ∑ j ∈ C i, j.val)) = _; exact assignment_to_global_sum P s t
private theorem occProb_slots {K L n : ℕ} {t : ℝ} (ht : 0 < t) (s : Fin L) (a : ℕ) : occProb K L n t s a = slotNum K L n t s a / slotDen K L n t := by
  classical
  rw [occProb_slotWt ht.ne' s a]; have hnum := (slotWt_sum_to_slots (K := K) ht s (fun N b => N = n ∧ b = a)); have hden := (slotWt_sum_to_slots (K := K) ht s (fun N _ => N = n)); have hconfigs : (configs K L n).filter (fun η => (η s : ℕ) = a) = (Finset.univ : Finset (Fin L → Fin (K + 1))).filter (fun η => (∑ i, (η i : ℕ)) = n ∧ (η s : ℕ) = a) := by
    ext η
    simp [configs]
  have hslots : ((Finset.univ : Finset (Fin L × Fin K)).powersetCard n).filter (fun S => (S.filter (fun p => p.1 = s)).card = a) = (Finset.univ : Finset (Finset (Fin L × Fin K))).filter (fun S => S.card = n ∧ (S.filter (fun p => p.1 = s)).card = a) := by
    ext S
    simp [Finset.mem_powersetCard]
  unfold slotNum slotDen; rw [hconfigs, hslots, hnum]
  congr 1
  simpa only [configs, Finset.powersetCard_eq_filter, Finset.powerset_univ] using hden
private def reflectedCompl (e : α ≃ α) (S : Finset α) : Finset α := (S.map e.toEmbedding)ᶜ
private theorem mem_reflectedCompl (e : α ≃ α) (S : Finset α) (a : α) : a ∈ reflectedCompl e S ↔ e.symm a ∉ S := by simp [reflectedCompl]
private theorem reflectedCompl_involutive (e : α ≃ α) (he : Function.Involutive e) : Function.Involutive (reflectedCompl e) := by
  have hinv (a : α) : e.symm a = e a := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  intro S
  ext a
  simp only [mem_reflectedCompl, hinv, not_not]; rw [he a]
private theorem reflectedCompl_card (e : α ≃ α) (S : Finset α) : (reflectedCompl e S).card + S.card = Fintype.card α := by
  have h := (Finset.card_compl_add_card (S.map e.toEmbedding))
  simpa only [reflectedCompl, Finset.card_map] using h
private theorem reflected_energy_pair (e : α ≃ α) (w : α → ℕ) (c : ℕ) (hw : ∀ a, w (e a) + w a = c) (S : Finset α) : (∑ a ∈ S.map e.toEmbedding, w a) + (∑ a ∈ S, w a) = c * S.card := by
  rw [Finset.sum_map, ← Finset.sum_add_distrib]; simp only [Equiv.toEmbedding_apply, hw, Finset.sum_const, nsmul_eq_mul]; exact Nat.mul_comm _ _
private theorem total_reflected_energy (e : α ≃ α) (w : α → ℕ) (c n : ℕ) (hw : ∀ a, w (e a) + w a = c) (hsize : Fintype.card α = 2 * n) : (∑ a, w a) = c * n := by
  have h := (reflected_energy_pair e w c hw Finset.univ); simp only [Finset.map_univ_equiv, Finset.card_univ] at h; rw [hsize] at h; nlinarith
private theorem reflectedCompl_energy (e : α ≃ α) (w : α → ℕ) (c n : ℕ) (hw : ∀ a, w (e a) + w a = c) (hsize : Fintype.card α = 2 * n) (S : Finset α) (hS : S.card = n) : (∑ a ∈ reflectedCompl e S, w a) = ∑ a ∈ S, w a := by
  have hpair := (reflected_energy_pair e w c hw S); have hcompl := (Finset.sum_compl_add_sum (S.map e.toEmbedding) w); rw [total_reflected_energy e w c n hw hsize] at hcompl; rw [hS] at hpair; change (∑ a ∈ reflectedCompl e S, w a) + (∑ a ∈ S.map e.toEmbedding, w a) = _ at hcompl; omega
private theorem reflectedCompl_fiber_card (e : α ≃ α) (p : α → Prop) [DecidablePred p] (hp : ∀ a, p (e a) ↔ p a) (S : Finset α) : ((reflectedCompl e S).filter p).card + (S.filter p).card = (Finset.univ.filter p).card := by
  have hmap : ((S.map e.toEmbedding).filter p).card = (S.filter p).card := (by simp only [Finset.filter_map, Function.comp_def, Equiv.toEmbedding_apply, hp, Finset.card_map]); have h := ((Finset.univ.filter p).card_filter_add_card_filter_not (fun a => a ∈ S.map e.toEmbedding)); have hleft : (Finset.univ.filter p).filter (fun a => a ∈ S.map e.toEmbedding) = (S.map e.toEmbedding).filter p := (by ext a; simp [and_comm])
  have hright : (Finset.univ.filter p).filter (fun a => a ∉ S.map e.toEmbedding) = (reflectedCompl e S).filter p := (by ext a; simp [reflectedCompl, and_comm]); rw [hleft, hright, hmap] at h; omega
private theorem reflection_pairing (e : α ≃ α) (he : Function.Involutive e) (w : α → ℕ) (c n k : ℕ) (p : α → Prop) [DecidablePred p] (hw : ∀ a, w (e a) + w a = c) (hp : ∀ a, p (e a) ↔ p a) (hsize : Fintype.card α = 2 * n) (hfiber : (Finset.univ.filter p).card = 2 * k + 1) (t : ℝ) : (∑ S ∈ ((Finset.univ : Finset α).powersetCard n).filter (fun S => (S.filter p).card = k), t ^ (∑ a ∈ S, w a)) = ∑ S ∈ ((Finset.univ : Finset α).powersetCard n).filter (fun S => (S.filter p).card = k + 1), t ^ (∑ a ∈ S, w a) := by
  classical
  have hinv := (reflectedCompl_involutive e he); have memflip (S : Finset α) (hS : S.card = n) : (reflectedCompl e S).card = n := by
    have h := (reflectedCompl_card e S); omega
  apply Finset.sum_bij (fun S _ => reflectedCompl e S)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS ⊢
    refine ⟨memflip S hS.1, ?_⟩
    have h := (reflectedCompl_fiber_card e p hp S); rw [hS.2, hfiber] at h; omega
  · intro S hS T hT h
    exact hinv.injective h
  · intro S hS
    refine ⟨reflectedCompl e S, ?_, hinv S⟩
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS ⊢
    refine ⟨memflip S hS.1, ?_⟩
    have h := (reflectedCompl_fiber_card e p hp S); rw [hS.2, hfiber] at h; omega
  · intro S hS
    have hcard : S.card = n := ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2); rw [reflectedCompl_energy e w c n hw hsize S hcard]
private theorem slot_defect_identity (w : α → ℕ) (z : α → Bool) (k : ℕ) : (∑ a, if z a then w a else 0) + (∑ a, if w a < k then k else 0) = (∑ a, if z a then k else 0) + (∑ a, if w a < k then w a else 0) + ∑ a, if z a then w a - k else k - w a := by
  have h (a : α) : (if z a then w a else 0) + (if w a < k then k else 0) = (if z a then k else 0) + (if w a < k then w a else 0) + (if z a then w a - k else k - w a) := (by cases hz : z a <;> by_cases hw : w a < k <;> simp [hw] <;> omega)
  simpa only [Finset.sum_add_distrib] using Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset α)) => h a)
private theorem block_reflection_pairing (r k : ℕ) (s : Fin (2 * r)) (t : ℝ) : (∑ S ∈ ((Finset.univ : Finset (Fin (2 * r) × Fin (2 * k + 1))).powersetCard ((2 * k + 1) * r)).filter (fun S => (S.filter (fun a => a.1 = s)).card = k), t ^ (∑ a ∈ S, a.2.val)) = ∑ S ∈ ((Finset.univ : Finset (Fin (2 * r) × Fin (2 * k + 1))).powersetCard ((2 * k + 1) * r)).filter (fun S => (S.filter (fun a => a.1 = s)).card = k + 1), t ^ (∑ a ∈ S, a.2.val) := by
  classical
  let e : (Fin (2 * r) × Fin (2 * k + 1)) ≃ (Fin (2 * r) × Fin (2 * k + 1)) := (Equiv.prodCongr (Equiv.refl _) Fin.revPerm); have he : Function.Involutive e := by
    rintro ⟨i, j⟩
    apply Prod.ext
    · rfl
    · exact Fin.rev_rev j
  have hw (a : Fin (2 * r) × Fin (2 * k + 1)) : (e a).2.val + a.2.val = 2 * k := by
    change (Fin.rev a.2).val + a.2.val = 2 * k; rw [Fin.val_rev]; omega
  have hp (a : Fin (2 * r) × Fin (2 * k + 1)) : (e a).1 = s ↔ a.1 = s := (Iff.rfl); have hsize : Fintype.card (Fin (2 * r) × Fin (2 * k + 1)) = 2 * ((2 * k + 1) * r) := (by simp only [Fintype.card_prod, Fintype.card_fin]; ring)
  have hfiber : ((Finset.univ : Finset (Fin (2 * r) × Fin (2 * k + 1))).filter (fun a => a.1 = s)).card = 2 * k + 1 := by
    have hset : ((Finset.univ : Finset (Fin (2 * r) × Fin (2 * k + 1))).filter (fun a => a.1 = s)) = {s} ×ˢ Finset.univ := by
      ext a
      rcases a with ⟨i, j⟩
      simp [eq_comm]
    rw [hset]; simp
  exact reflection_pairing e he (fun a => a.2.val) (2 * k) ((2 * k + 1) * r) k (fun a => a.1 = s) hw hp hsize hfiber t
private theorem restricted_slot_pairing (r K k : ℕ) (hK : 2*k+1 ≤ K) (s : Fin (2*r)) (t : ℝ) : (∑ S ∈ (((Finset.univ : Finset (Fin (2*r) × Fin K)).filter (fun a => a.2.val < 2*k+1)).powersetCard ((2*k+1)*r)).filter (fun S => (S.filter (fun a => a.1=s)).card = k), t^(∑ a ∈ S, a.2.val)) = ∑ S ∈ (((Finset.univ : Finset (Fin (2*r) × Fin K)).filter (fun a => a.2.val < 2*k+1)).powersetCard ((2*k+1)*r)).filter (fun S => (S.filter (fun a => a.1=s)).card = k+1), t^(∑ a ∈ S, a.2.val) := by
  classical
  let e : (Fin (2*r) × Fin (2*k+1)) ↪ (Fin (2*r) × Fin K) := ⟨fun a => (a.1, ⟨a.2.val, lt_of_lt_of_le a.2.isLt hK⟩), by
      rintro ⟨i,j⟩ ⟨i',j'⟩ h
      have hi : i = i' := (congrArg Prod.fst h); have hj : j = j' := (Fin.ext (congrArg (fun a => a.2.val) h))
      cases hi
      cases hj
      rfl⟩
  have hs : ((Finset.univ : Finset (Fin (2*r) × Fin K)).filter (fun a => a.2.val < 2*k+1)) = Finset.univ.map e := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro ha
      exact ⟨(a.1,⟨a.2.val,ha⟩), by exact Prod.ext rfl (Fin.ext rfl)⟩
    · rintro ⟨b,hb⟩
      rw [← hb]; exact b.2.isLt
  have hf (S : Finset (Fin (2*r) × Fin (2*k+1))) : ((S.map e).filter (fun a => a.1=s)).card = (S.filter (fun a => a.1=s)).card := by
    rw [Finset.filter_map, Finset.card_map]; rfl
  have hem (S : Finset (Fin (2*r) × Fin (2*k+1))) : (Finset.mapEmbedding e).toEmbedding S = S.map e := (rfl); simp only [hs, Finset.powersetCard_map, Finset.filter_map, Function.comp_def, hem, Finset.card_map, Finset.sum_map]; exact block_reflection_pairing r k s t
private theorem slotsOfMask_maskOfSlots (S : Finset α) : (Set.toFinset {a | decide (a ∈ S)}) = S := by
  ext a
  simp
private theorem maskOfSlots_slotsOfMask (z : α → Bool) : (fun a => decide (a ∈ Set.toFinset {a | z a})) = z := by
  funext a
  cases hz : z a <;> simp [hz]
private theorem slotsOfMask_card (z : α → Bool) : ((Set.toFinset {a | z a})).card = ∑ a, if z a then (1 : ℕ) else 0 := by simp [Set.toFinset_ofPred]
private theorem slotsOfMask_sum (z : α → Bool) (w : α → ℕ) : (∑ a ∈ (Set.toFinset {a | z a}), w a) = ∑ a, if z a then w a else 0 := by simp [Set.toFinset_ofPred, Finset.sum_filter]
private theorem slotsOfMask_occupation {L K : ℕ} (z : Fin L × Fin K → Bool) (s : Fin L) : (((Set.toFinset {a | z a})).filter (fun a => a.1=s)).card = ∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0 := by
  classical
  have h : (((Set.toFinset {a | z a})).filter (fun a => a.1=s)) = {s} ×ˢ ((Finset.univ : Finset (Fin K)).filter (fun j => z (s,j))) := by
    ext a
    rcases a with ⟨i,j⟩
    by_cases hi : i=s
    · subst i
      simp [Set.toFinset_ofPred]
    · have hi' : s ≠ i := Ne.symm hi
      simp [Set.toFinset_ofPred,hi,hi']
  rw [h,Finset.card_product,Finset.card_singleton,one_mul]; simp
private theorem sum_slots_masks (P : Finset α → Prop) [DecidablePred P] (f : Finset α → ℝ) : (∑ S ∈ (Finset.univ : Finset (Finset α)).filter P, f S) = ∑ z ∈ (Finset.univ : Finset (α → Bool)).filter (fun z => P ((Set.toFinset {a | z a}))), f ((Set.toFinset {a | z a})) := by
  classical
  symm
  apply Finset.sum_bij (fun z _ => (Set.toFinset {a | z a}))
  · intro z hz
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hz
  · intro z hz w hw he
    simpa only [maskOfSlots_slotsOfMask] using congrArg (fun S a => decide (a ∈ S)) he
  · intro S hS
    refine ⟨(fun a => decide (a ∈ S)), ?_, slotsOfMask_maskOfSlots S⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,slotsOfMask_maskOfSlots] using hS
  · intro z hz
    rfl
private noncomputable def highSlotNum (K L n c : ℕ) (t : ℝ) (s : Fin L) (b : ℕ) : ℝ := ∑ S ∈ (((Finset.univ : Finset (Fin L × Fin K)).powersetCard n).filter (fun S => (S.filter (fun p => p.1=s)).card=b)).filter (fun S => ∃ a ∈ S, c ≤ a.2.val), t^(∑ a ∈ S, a.2.val)
private theorem slotNum_split (K L n c b : ℕ) (t : ℝ) (s : Fin L) : slotNum K L n t s b = highSlotNum K L n c t s b + ∑ S ∈ (((Finset.univ : Finset (Fin L × Fin K)).filter (fun a => a.2.val < c)).powersetCard n).filter (fun S => (S.filter (fun p => p.1=s)).card=b), t^(∑ a ∈ S,a.2.val) := by
  classical
  let A := (((Finset.univ : Finset (Fin L × Fin K)).powersetCard n).filter (fun S => (S.filter (fun p => p.1=s)).card=b)); have hlow : (A.filter (fun S => ¬ ∃ a ∈ S, c ≤ a.2.val)) = (((Finset.univ : Finset (Fin L × Fin K)).filter (fun a => a.2.val < c)).powersetCard n).filter (fun S => (S.filter (fun p => p.1=s)).card=b) := by
    ext S
    simp only [A,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    constructor
    · rintro ⟨⟨hcard,hocc⟩,hn⟩
      refine ⟨⟨?_,hcard⟩,hocc⟩
      intro a ha; simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      by_contra he
      exact hn ⟨a,ha,by omega⟩
    · rintro ⟨⟨hsub,hcard⟩,hocc⟩
      refine ⟨⟨hcard,hocc⟩,?_⟩
      rintro ⟨a,ha,he⟩
      have hlo := ((Finset.mem_filter.mp (hsub ha)).2); omega
  have h := (Finset.sum_filter_add_sum_filter_not A (fun S => ∃ a ∈ S, c ≤ a.2.val) (fun S => t^(∑ a ∈ S,a.2.val))); rw [hlow] at h; exact h.symm
private theorem slot_adjacent_difference (r K k : ℕ) (hK : 2*k+1 ≤ K) (s : Fin (2*r)) (t : ℝ) : slotNum K (2*r) ((2*k+1)*r) t s k - slotNum K (2*r) ((2*k+1)*r) t s (k+1) = highSlotNum K (2*r) ((2*k+1)*r) (2*k+1) t s k - highSlotNum K (2*r) ((2*k+1)*r) (2*k+1) t s (k+1) := by
  rw [slotNum_split K (2*r) ((2*k+1)*r) (2*k+1) k, slotNum_split K (2*r) ((2*k+1)*r) (2*k+1) (k+1), restricted_slot_pairing r K k hK s t]; ring
private theorem highSlotNum_masks (K L n c b : ℕ) (t : ℝ) (s : Fin L) : highSlotNum K L n c t s b = ∑ z ∈ (Finset.univ : Finset (Fin L × Fin K → Bool)).filter (fun z => (∑ a, if z a then (1 : ℕ) else 0)=n ∧ (∃ a, z a=true ∧ c ≤ a.2.val) ∧ (∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0)=b), t^(∑ a, if z a then a.2.val else 0) := by
  classical
  unfold highSlotNum; have hset : (((Finset.univ : Finset (Fin L × Fin K)).powersetCard n).filter (fun S => (S.filter (fun p => p.1=s)).card=b)).filter (fun S => ∃ a ∈ S,c ≤ a.2.val) = (Finset.univ : Finset (Finset (Fin L × Fin K))).filter (fun S => S.card=n ∧ (∃ a ∈ S,c ≤ a.2.val) ∧ (S.filter (fun p => p.1=s)).card=b) := by
    ext S
    simp [Finset.mem_powersetCard,and_comm,and_left_comm,and_assoc]
  rw [hset,sum_slots_masks]; simp only [slotsOfMask_card,slotsOfMask_sum,slotsOfMask_occupation]; simp only [Set.toFinset_ofPred,Finset.mem_filter,Finset.mem_univ,true_and]
private theorem fin_cutoff_sum (f : ℕ → ℕ) {k K : ℕ} (hk : k ≤ K) : (∑ j : Fin K, if (j : ℕ) < k then f j else 0) = ∑ j ∈ Finset.range k, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then f j else 0) K]; rw [← Finset.sum_filter]; have hset : (Finset.range K).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
private theorem ground_energy_defect (r K k : ℕ) (hk : k ≤ K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) : (∑ a, if z a then a.2.val else 0) = r * k ^ 2 + ∑ a, if z a then a.2.val - k else k - a.2.val := by
  have h := (slot_defect_identity (fun a : Fin (2 * r) × Fin K => a.2.val) z k); have hc : (∑ a, if z a then k else 0) = k * ((2 * k + 1) * r) := by
    calc
      _ = ∑ a, k * (if z a then (1 : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        cases hz : z a <;> simp
      _ = k * (∑ a, if z a then (1 : ℕ) else 0) := by rw [Finset.mul_sum]
      _ = _ := by rw [hn]
  have hl : (∑ a : Fin (2 * r) × Fin K, if a.2.val < k then k else 0) = (2 * r) * (k * k) := by
    rw [Fintype.sum_prod_type]
    simp_rw [fin_cutoff_sum (fun _ => k) hk]
    simp [Nat.mul_comm]
  have hw : (∑ a : Fin (2 * r) × Fin K, if a.2.val < k then a.2.val else 0) = (2 * r) * (∑ j ∈ Finset.range k, j) := by
    rw [Fintype.sum_prod_type]
    simp_rw [fin_cutoff_sum (fun j => j) hk]
    simp [Nat.mul_comm]
  rw [hc, hl, hw] at h; have hs := (congrArg (fun a => r * a) (Finset.sum_range_id_mul_two k)); have hp : k * (k - 1) + k = k * k := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hp' := (congrArg (fun a => r * a) hp); nlinarith
private theorem ground_energy_lower_bound (r K k : ℕ) (hk : k ≤ K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) : r * k ^ 2 ≤ ∑ a, if z a then a.2.val else 0 := by
  rw [ground_energy_defect r K k hk z hn]; omega
private theorem unmatched_energy_lower_bound (r K k : ℕ) (hk : k ≤ K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) (hu : ∃ a, z a = true ∧ 2 * k + 1 ≤ a.2.val) : r * k ^ 2 + k + 1 ≤ ∑ a, if z a then a.2.val else 0 := by
  obtain ⟨a, hz, ha⟩ := hu
  have hs : (if z a then a.2.val - k else k - a.2.val) ≤ ∑ b, if z b then b.2.val - k else k - b.2.val := by
    apply Finset.single_le_sum (f := fun b : Fin (2 * r) × Fin K =>
      if z b then b.2.val - k else k - b.2.val) (s := Finset.univ)
    · intro b _
      exact Nat.zero_le _
    · exact Finset.mem_univ a
  simp [hz] at hs; have he := (ground_energy_defect r K k hk z hn); omega
private theorem ground_site_count {L K k : ℕ} (hk : k < K) (z : Fin L × Fin K → Bool) (hD : ∀ a, (if z a then a.2.val - k else k - a.2.val) = 0) (s : Fin L) : (∑ j : Fin K, if z (s, j) then (1 : ℕ) else 0) = k + (if z (s, ⟨k, hk⟩) then 1 else 0) := by
  classical
  let δ : ℕ := (if z (s, ⟨k, hk⟩) then 1 else 0); have hterm (j : Fin K) : (if z (s, j) then (1 : ℕ) else 0) = (if j.val < k then 1 else 0) + (if j.val = k then δ else 0) := by
    have hd := (hD (s, j))
    by_cases hj : j.val < k
    · have hne : j.val ≠ k := by omega
      cases hz : z (s, j) <;> simp [hz, hj, hne] at hd ⊢ <;> omega
    · by_cases he : j.val = k
      · have he' : j = (⟨k, hk⟩ : Fin K) := Fin.ext he
        subst j; simp [δ]
      · have hg : k < j.val := by omega
        cases hz : z (s, j) <;> simp [hz, hj, he] at hd ⊢ <;> omega
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [fin_cutoff_sum (fun _ => 1) hk.le]; have hsingle : (∑ j : Fin K, if j.val = k then δ else 0) = δ := by
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin K)]
    · simp
    · intro j _ hne
      have hv : j.val ≠ k := (by intro h; exact hne (Fin.ext h))
      simp [hv]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hsingle]; simp [δ]
private theorem ground_site_occupation (r K k : ℕ) (hk : k < K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) (hE : (∑ a, if z a then a.2.val else 0) = r * k ^ 2) (s : Fin (2 * r)) : (∑ j : Fin K, if z (s, j) then (1 : ℕ) else 0) = k ∨ (∑ j : Fin K, if z (s, j) then (1 : ℕ) else 0) = k + 1 := by
  have he := (ground_energy_defect r K k hk.le z hn); have hsum : (∑ a, if z a then a.2.val - k else k - a.2.val) = 0 := (by omega); have hd (a : Fin (2 * r) × Fin K) : (if z a then a.2.val - k else k - a.2.val) = 0 := by
    have h := (Finset.single_le_sum (fun b _ => Nat.zero_le (if z b then b.2.val - k else k - b.2.val)) (Finset.mem_univ a)); omega
  rw [ground_site_count hk z hd s]
  cases z (s, ⟨k, hk⟩) <;> simp
private def floorMask {L K : ℕ} (k : ℕ) (A : Finset (Fin L)) (a : Fin L × Fin K) : Bool := decide (a.2.val < k ∨ a.2.val = k ∧ a.1 ∈ A)
private theorem floorMask_defect {L K : ℕ} (k : ℕ) (A : Finset (Fin L)) (a : Fin L × Fin K) : (if floorMask k A a then a.2.val - k else k - a.2.val) = 0 := by
  by_cases hlo : a.2.val < k <;> by_cases heq : a.2.val = k <;>
    by_cases hA : a.1 ∈ A <;> simp [floorMask, hlo, heq, hA] <;> omega
private theorem floorMask_site_count {L K k : ℕ} (hk : k < K) (A : Finset (Fin L)) (s : Fin L) : (∑ j : Fin K, if floorMask k A (s, j) then (1 : ℕ) else 0) = k + if s ∈ A then 1 else 0 := by
  rw [ground_site_count hk (floorMask k A) (floorMask_defect k A) s]; simp [floorMask]
private theorem ground_from_sites (r K k : ℕ) (hk : k < K) (A : Finset (Fin (2 * r))) (hA : A.card = r) : ∃ z : Fin (2 * r) × Fin K → Bool, (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r ∧ (∑ a, if z a then a.2.val else 0) = r * k ^ 2 ∧ ∀ s, (∑ j : Fin K, if z (s, j) then (1 : ℕ) else 0) = k + if s ∈ A then 1 else 0 := by
  classical
  let z : Fin (2 * r) × Fin K → Bool := floorMask k A
  have hd (a : Fin (2 * r) × Fin K) : (if z a then a.2.val - k else k - a.2.val) = 0 := by
    exact floorMask_defect k A a
  have hcount (s : Fin (2 * r)) : (∑ j : Fin K, if z (s, j) then (1 : ℕ) else 0) = k + if s ∈ A then 1 else 0 := by
    exact floorMask_site_count hk A s
  have hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r := by
    rw [Fintype.sum_prod_type]
    simp_rw [hcount]
    rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; have hi : (∑ s : Fin (2 * r), if s ∈ A then (1 : ℕ) else 0) = A.card := (by simp); rw [hi, hA]
    norm_cast <;> ring
  refine ⟨z, hn, ?_, hcount⟩
  rw [ground_energy_defect r K k hk.le z hn]; simp [hd]
private theorem continuous_positive_near_zero (f : ℝ → ℝ) (hf : ContinuousAt f 0) (h0 : 0 < f 0) : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → 0 < f t := by
  have h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < f t := (hf.eventually_const_lt h0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε, hε, ?_⟩
  intro t ht hte
  apply he
  simpa [Real.dist_eq, abs_of_pos ht] using hte
private theorem finite_monomial_comparison {α : Type*} (A B : Finset α) (H : α → ℕ) (d : ℕ) (hA : ∀ i ∈ A, d ≤ H i) (hB : ∀ i ∈ B, d ≤ H i) (hmin : (A.filter (fun i => H i = d)).card < (B.filter (fun i => H i = d)).card) : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → (∑ i ∈ A, t ^ H i) < ∑ i ∈ B, t ^ H i := by
  classical
  let f (t : ℝ) := ((∑ i ∈ B, t ^ (H i - d)) - ∑ i ∈ A, t ^ (H i - d)); have hc : ContinuousAt f 0 := by
    unfold f; fun_prop
  have hz (S : Finset α) (hs : ∀ i ∈ S, d ≤ H i) : (∑ i ∈ S, (0 : ℝ) ^ (H i - d)) = (S.filter (fun i => H i = d)).card := by
    calc
      _ = ∑ i ∈ S, if H i = d then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : H i = d
        · simp [he]
        · have hne : H i - d ≠ 0 := by have := hs i hi; omega
          simp [he, zero_pow hne]
      _ = _ := Finset.sum_boole _ _
  have h0 : 0 < f 0 := by
    dsimp [f]; rw [hz B hB, hz A hA]; exact sub_pos.mpr (by exact_mod_cast hmin)
  obtain ⟨ε, hε, he⟩ := continuous_positive_near_zero f hc h0
  refine ⟨ε, hε, ?_⟩
  intro t ht hte; have hpos := (mul_pos (pow_pos ht d) (he t ht hte)); have factor (S : Finset α) (hs : ∀ i ∈ S, d ≤ H i) : t ^ d * (∑ i ∈ S, t ^ (H i - d)) = ∑ i ∈ S, t ^ H i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi; rw [← pow_add, Nat.add_sub_of_le (hs i hi)]
  dsimp [f] at hpos; rw [mul_sub, factor B hB, factor A hA] at hpos; exact sub_pos.mp hpos
private theorem boundary_count_positive (r : ℕ) (hr : 2 ≤ r) : ((2 * r - 2) * Nat.choose (2 * r - 1) (r - 1) : ℕ) = (2 * r - 1) * Nat.choose (2 * r - 1) (r - 2) + 3 * Nat.choose (2 * r - 1) (r - 2) ∧ 0 < 3 * Nat.choose (2 * r - 1) (r - 2) := by
  have h := (Nat.choose_succ_right_eq (2 * r - 1) (r - 2)); have hr1 : r - 2 + 1 = r - 1 := (by omega); have hr2 : 2 * r - 1 - (r - 2) = r + 1 := (by omega); rw [hr1, hr2] at h; have he : 2 * r - 2 = 2 * (r - 1) := (by omega)
  constructor
  · rw [he]
    have hL : 2 * r - 1 + 3 = 2 * (r + 1) := (by omega)
    calc
      _ = 2 * (Nat.choose (2 * r - 1) (r - 1) * (r - 1)) := by ring
      _ = 2 * (Nat.choose (2 * r - 1) (r - 2) * (r + 1)) := by rw [h]
      _ = _ := by rw [← Nat.add_mul, hL]; ring
  · exact Nat.mul_pos (by decide) (Nat.choose_pos (by omega))
private def maskFamily (r K k b : ℕ) (s : Fin (2*r)) : Finset (Fin (2*r) × Fin K → Bool) := Finset.univ.filter fun z =>
    (∑ a, if z a then (1 : ℕ) else 0) = (2*k+1)*r ∧
    (∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0) = b
private theorem ground_at_adjacent (r K k : ℕ) (hr : 2 ≤ r) (hk : k < K) (s : Fin (2*r)) : (∃ z ∈ maskFamily r K k k s, (∑ a, if z a then a.2.val else 0) = r*k^2) ∧ (∃ z ∈ maskFamily r K k (k+1) s, (∑ a, if z a then a.2.val else 0) = r*k^2) := by
  classical
  have hc : r ≤ ((Finset.univ : Finset (Fin (2*r))).erase s).card := (by simp; omega)
  obtain ⟨A,hAS,hAc⟩ := Finset.exists_subset_card_eq hc
  have hs : s ∉ A := (fun h => (Finset.mem_erase.mp (hAS h)).1 rfl); have hAc' : Aᶜ.card = r := by
    have h := (Finset.card_compl_add_card A); simp only [Finset.card_univ,Fintype.card_fin] at h; omega
  obtain ⟨z0,hn0,hE0,hocc0⟩ := ground_from_sites r K k hk A hAc
  obtain ⟨z1,hn1,hE1,hocc1⟩ := ground_from_sites r K k hk Aᶜ hAc'
  constructor
  · refine ⟨z0, ?_, hE0⟩
    simp only [maskFamily,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hn0,by simpa [hs] using hocc0 s⟩
  · refine ⟨z1, ?_, hE1⟩
    simp only [maskFamily,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hn1,by simpa [hs] using hocc1 s⟩
private theorem nonadjacent_small_t (r K k b a : ℕ) (hr : 2 ≤ r) (hk : k < K) (hb0 : b ≠ k) (hb1 : b ≠ k+1) (ha : a=k ∨ a=k+1) (s : Fin (2*r)) : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → (∑ z ∈ maskFamily r K k b s, t^(∑ p, if z p then p.2.val else 0)) < ∑ z ∈ maskFamily r K k a s, t^(∑ p, if z p then p.2.val else 0) := by
  classical
  have hbound (c : ℕ) (z : Fin (2*r) × Fin K → Bool) (hz : z ∈ maskFamily r K k c s) : r*k^2 ≤ ∑ p, if z p then p.2.val else 0 := (by exact ground_energy_lower_bound r K k hk.le z (Finset.mem_filter.mp hz).2.1); have hbad : ((maskFamily r K k b s).filter (fun z => (∑ p, if z p then p.2.val else 0) = r*k^2)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hz,hE⟩ := Finset.mem_filter.mp hz
    obtain ⟨hn,hb⟩ := (Finset.mem_filter.mp hz).2
    have h := (ground_site_occupation r K k hk z hn hE s); omega
  have hgood : 0 < ((maskFamily r K k a s).filter (fun z => (∑ p, if z p then p.2.val else 0) = r*k^2)).card := by
    obtain ⟨h0,h1⟩ := ground_at_adjacent r K k hr hk s
    have h : ∃ z ∈ maskFamily r K k a s, (∑ p, if z p then p.2.val else 0) = r*k^2 := by
      rcases ha with rfl | rfl
      · exact h0
      · exact h1
    obtain ⟨z,hz,hE⟩ := h
    exact Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hE⟩⟩
  apply finite_monomial_comparison (maskFamily r K k b s) (maskFamily r K k a s) (fun z => ∑ p, if z p then p.2.val else 0) (r*k^2) (hbound b) (hbound a)
  omega
private theorem finite_uniform_radius {β : Type*} (B : Finset β) (P : β → ℝ → Prop) (hP : ∀ b ∈ B, ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → P b t) : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → ∀ b ∈ B, P b t := by
  classical
  revert hP
  induction B using Finset.induction_on with
  | empty => intro _; exact ⟨1,by norm_num,by simp⟩
  | @insert b B hb ih =>
    intro hP
    obtain ⟨ε0,hε0,h0⟩ := hP b (Finset.mem_insert_self b B)
    obtain ⟨ε1,hε1,h1⟩ := ih (fun c hc => hP c (Finset.mem_insert_of_mem hc))
    refine ⟨min ε0 ε1,lt_min hε0 hε1,?_⟩
    intro t ht hte c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact h0 t ht (lt_of_lt_of_le hte (min_le_left _ _))
    · exact h1 t ht (lt_of_lt_of_le hte (min_le_right _ _)) c hc
private def boundaryMask {L K k : ℕ} (hK : 2 * k + 1 < K) (A : Finset (Fin L)) (h : Fin L) (a : Fin L × Fin K) : Bool := floorMask k A a || decide (a = (h, ⟨2 * k + 1, hK⟩))
private theorem boundaryMask_indicator {L K k : ℕ} (hK : 2 * k + 1 < K) (A : Finset (Fin L)) (h : Fin L) (a : Fin L × Fin K) : (if boundaryMask hK A h a then (1 : ℕ) else 0) = (if floorMask k A a then 1 else 0) + (if a = (h, ⟨2 * k + 1, hK⟩) then 1 else 0) := by
  by_cases he : a = (h, ⟨2 * k + 1, hK⟩)
  · subst a
    have hne : 2 * k + 1 ≠ k := (by omega); have hlt : ¬2 * k + 1 < k := (by omega); simp [boundaryMask, floorMask, hne, hlt]
  · simp [boundaryMask, he]
private theorem boundaryMask_site_count {L K k : ℕ} (hK : 2 * k + 1 < K) (A : Finset (Fin L)) (h s : Fin L) : (∑ j : Fin K, if boundaryMask hK A h (s, j) then (1 : ℕ) else 0) = k + (if s ∈ A then 1 else 0) + (if h = s then 1 else 0) := by
  classical
  simp_rw [boundaryMask_indicator, Finset.sum_add_distrib]
  rw [floorMask_site_count (by omega)]; have he (j : Fin K) : (s, j) = (h, (⟨2 * k + 1, hK⟩ : Fin K)) ↔ s = h ∧ j = (⟨2 * k + 1, hK⟩ : Fin K) := (by simp only [Prod.mk.injEq])
  simp_rw [he]
  by_cases hs : s = h
  · simp [hs]
  · have hs' : h ≠ s := Ne.symm hs
    simp [hs,hs']
private theorem boundaryMask_defect {L K k : ℕ} (hK : 2 * k + 1 < K) (A : Finset (Fin L)) (h : Fin L) (a : Fin L × Fin K) : (if boundaryMask hK A h a then a.2.val - k else k - a.2.val) = if a = (h, ⟨2 * k + 1, hK⟩) then k + 1 else 0 := by
  by_cases he : a = (h, ⟨2 * k + 1, hK⟩)
  · subst a
    simp [boundaryMask]; omega
  · simpa only [boundaryMask, he, decide_false, Bool.or_false, ite_false] using floorMask_defect k A a
private theorem boundaryMask_total_count {L K k : ℕ} (hK : 2 * k + 1 < K) (A : Finset (Fin L)) (h : Fin L) : (∑ a, if boundaryMask hK A h a then (1 : ℕ) else 0) = L * k + A.card + 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [boundaryMask_site_count, Finset.sum_add_distrib]
  simp
private theorem boundaryMask_data (r K k : ℕ) (hr : 2 ≤ r) (hK : 2 * k + 1 < K) (A : Finset (Fin (2 * r))) (hA : A.card = r - 1) (h : Fin (2 * r)) : (∑ a, if boundaryMask hK A h a then (1 : ℕ) else 0) = (2 * k + 1) * r ∧ (∑ a, if boundaryMask hK A h a then a.2.val else 0) = r * k ^ 2 + k + 1 ∧ ∃ a, boundaryMask hK A h a = true ∧ 2 * k + 1 ≤ a.2.val := by
  classical
  have hn : (∑ a, if boundaryMask hK A h a then (1 : ℕ) else 0) = (2 * k + 1) * r := by
    rw [boundaryMask_total_count hK A h, hA]
    have hh : r - 1 + 1 = r := by omega
    nlinarith
  refine ⟨hn, ?_, ?_⟩
  · rw [ground_energy_defect r K k (by omega) (boundaryMask hK A h) hn]
    simp_rw [boundaryMask_defect]
    simp; omega
  · refine ⟨(h, ⟨2 * k + 1, hK⟩), ?_, le_rfl⟩
    simp [boundaryMask]
private theorem unmatched_energy_equality_iff (r K k : ℕ) (hk : k ≤ K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) (hu : ∃ a, z a = true ∧ 2 * k + 1 ≤ a.2.val) : (∑ a, if z a then a.2.val else 0) = r * k ^ 2 + k + 1 ↔ ∃ a, z a = true ∧ a.2.val = 2 * k + 1 ∧ ∀ b, b ≠ a → (if z b then b.2.val - k else k - b.2.val) = 0 := by
  classical
  let D (a : Fin (2 * r) × Fin K) := (if z a then a.2.val - k else k - a.2.val); have he := (ground_energy_defect r K k hk z hn); change (∑ a, if z a then a.2.val else 0) = r * k ^ 2 + ∑ a, D a at he
  constructor
  · intro hE
    have hD : ∑ a, D a = k + 1 := (by omega)
    obtain ⟨a, hz, ha⟩ := hu
    have hDa : D a ≤ ∑ b, D b := (Finset.single_le_sum (fun b _ => Nat.zero_le (D b)) (Finset.mem_univ a)); have hka : k + 1 ≤ D a := (by dsimp [D]; rw [hz]; simp; omega)
    have hDa' : D a = k + 1 := (by omega); have hlev : a.2.val = 2 * k + 1 := (by dsimp [D] at hDa'; rw [hz] at hDa'; simp at hDa'; omega)
    refine ⟨a, hz, hlev, ?_⟩
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin (2 * r) × Fin K)) D (Finset.mem_univ a)); have hzero : ∑ b ∈ (Finset.univ : Finset (Fin (2 * r) × Fin K)).erase a, D b = 0 := (by omega); intro b hba; have hDb := (Finset.single_le_sum (fun c _ => Nat.zero_le (D c)) (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)); change D b = 0; omega
  · rintro ⟨a, hz, ha, hrest⟩
    have hDa : D a = k + 1 := (by dsimp [D]; rw [hz, ha]; simp; omega)
    have hs : ∑ b, D b = D a := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        exact hrest b hba
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))
    omega
private theorem boundary_occupancy_shape (r K k : ℕ) (hk : k ≤ K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) (hu : ∃ a, z a = true ∧ 2 * k + 1 ≤ a.2.val) (hE : (∑ a, if z a then a.2.val else 0) = r * k ^ 2 + k + 1) : ∃ a, z a = true ∧ a.2.val = 2 * k + 1 ∧ (∀ b, b.2.val < k → z b = true) ∧ (∀ b, k < b.2.val → b ≠ a → z b = false) := by
  obtain ⟨a, hz, ha, hrest⟩ := (unmatched_energy_equality_iff r K k hk z hn hu).mp hE
  refine ⟨a, hz, ha, ?_, ?_⟩
  · intro b hb
    have hba : b ≠ a := (by intro h; subst b; omega)
    have h := (hrest b hba)
    cases hzb : z b <;> simp [hzb] at h ⊢ <;> omega
  · intro b hb hba
    have h := (hrest b hba)
    cases hzb : z b <;> simp [hzb] at h ⊢ <;> omega
private theorem boundaryMask_injective {L K k : ℕ} (hK : 2 * k + 1 < K) : Function.Injective (fun p : Fin L × Finset (Fin L) => boundaryMask hK p.2 p.1) := by
  classical
  rintro ⟨h, A⟩ ⟨h', A'⟩ he
  have hne : 2 * k + 1 ≠ k := (by omega); have hlt : ¬2 * k + 1 < k := (by omega); have hfirst : h = h' := by
    have hp := (congrFun he (h, ⟨2 * k + 1, hK⟩))
    simpa [boundaryMask, floorMask, hne, hlt] using hp
  subst h'
  suffices A = A' from congrArg (fun B => (h,B)) this
  ext i
  have hp := (congrFun he (i, ⟨k, by omega⟩)); have hkhi : k ≠ 2 * k + 1 := (by omega)
  simpa [boundaryMask, floorMask, hkhi] using hp
private theorem boundaryMask_surjective (r K k : ℕ) (hr : 2 ≤ r) (hK : 2 * k + 1 < K) (z : Fin (2 * r) × Fin K → Bool) (hn : (∑ a, if z a then (1 : ℕ) else 0) = (2 * k + 1) * r) (hu : ∃ a, z a = true ∧ 2 * k + 1 ≤ a.2.val) (hE : (∑ a, if z a then a.2.val else 0) = r * k ^ 2 + k + 1) : ∃ p : Fin (2 * r) × Finset (Fin (2 * r)), p.2.card = r - 1 ∧ boundaryMask hK p.2 p.1 = z := by
  classical
  obtain ⟨a, hza, halevel, hlow, hhigh⟩ := boundary_occupancy_shape r K k (by omega) z hn hu hE
  let A : Finset (Fin (2 * r)) := (Finset.univ.filter (fun i => z (i, ⟨k, by omega⟩) = true)); have ha : a = (a.1, (⟨2 * k + 1, hK⟩ : Fin K)) := (Prod.ext rfl (Fin.ext halevel)); have hz : boundaryMask hK A a.1 = z := by
    funext b
    rcases b with ⟨i, j⟩
    by_cases hj : j.val < k
    · have hb := hlow (i, j) hj
      simp [boundaryMask, floorMask, hj, hb]
    · by_cases he : j.val = k
      · have he' : j = (⟨k, by omega⟩ : Fin K) := Fin.ext he
        simp only [he']; have hkhi : k ≠ 2 * k + 1 := (by omega); simp [boundaryMask, floorMask, A, hkhi]
      · have hgt : k < j.val := by omega
        by_cases hb : (i, j) = a
        · rw [hb, hza, ha]
          simp [boundaryMask]
        · have hbz := hhigh (i, j) hgt hb
          have hb' : (i, j) ≠ (a.1, (⟨2 * k + 1, hK⟩ : Fin K)) := (by simpa only [← ha] using hb); simp [boundaryMask, floorMask, hj, he, hb', hbz]
  refine ⟨(a.1, A), ?_, hz⟩
  have hc := (boundaryMask_total_count hK A a.1); rw [hz, hn] at hc; have hcard : A.card + 1 = r := (by nlinarith); change A.card = r-1; omega
private def boundaryPairOcc {r : ℕ} (k : ℕ) (s : Fin (2 * r)) (p : Fin (2 * r) × Finset (Fin (2 * r))) : ℕ := k + (if s ∈ p.2 then 1 else 0) + (if p.1 = s then 1 else 0)
private theorem boundary_pair_counts (r k : ℕ) (hr : 2 ≤ r) (s : Fin (2 * r)) : let F := (Finset.univ : Finset (Fin (2 * r))) ×ˢ (Finset.univ : Finset (Fin (2 * r))).powersetCard (r - 1); (F.filter (fun p => boundaryPairOcc k s p = k)).card = (2 * r - 1) * Nat.choose (2 * r - 1) (r - 1) ∧ (F.filter (fun p => boundaryPairOcc k s p = k + 1)).card = Nat.choose (2 * r - 1) (r - 1) + (2 * r - 1) * Nat.choose (2 * r - 1) (r - 2) := by
  classical
  dsimp only; let U := ((Finset.univ : Finset (Fin (2 * r)))); have hnot : (U.powersetCard (r - 1)).filter (fun S => s ∉ S) = (U.erase s).powersetCard (r - 1) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase]
    tauto
  have hyes : ((U.powersetCard (r - 1)).filter (fun S => s ∈ S)).card = Nat.choose (2 * r - 1) (r - 2) := by
    have h := (Finset.card_filter_powersetCard_subset {s} U (r - 1) (Finset.singleton_subset_iff.mpr (Finset.mem_univ s)) (by simp; omega))
    simpa only [U, Finset.singleton_subset_iff, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, show r - 1 - 1 = r - 2 by omega] using h
  have hzero : ((U ×ˢ U.powersetCard (r - 1)).filter (fun p => boundaryPairOcc k s p = k)) = U.erase s ×ˢ (U.erase s).powersetCard (r - 1) := by
    rw [← hnot]
    ext p
    rcases p with ⟨h, S⟩
    by_cases hS : s ∈ S <;> by_cases hh : h = s <;>
      simp [boundaryPairOcc, hS, hh, U, Finset.mem_erase, eq_comm, and_comm] <;> omega
  have hone : ((U ×ˢ U.powersetCard (r - 1)).filter (fun p => boundaryPairOcc k s p = k + 1)) = ({s} ×ˢ (U.erase s).powersetCard (r - 1)) ∪ (U.erase s ×ˢ (U.powersetCard (r - 1)).filter (fun S => s ∈ S)) := by
    rw [← hnot]
    ext p
    rcases p with ⟨h, S⟩
    by_cases hS : s ∈ S <;> by_cases hh : h = s <;>
      simp [boundaryPairOcc, hS, hh, U, Finset.mem_erase, eq_comm, and_comm, and_assoc] <;> omega
  have hdis : Disjoint ({s} ×ˢ (U.erase s).powersetCard (r - 1)) (U.erase s ×ˢ (U.powersetCard (r - 1)).filter (fun S => s ∈ S)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨h, S⟩ hleft hright
    have he : h = s := (Finset.mem_singleton.mp (Finset.mem_product.mp hleft).1); have hne : h ≠ s := ((Finset.mem_erase.mp (Finset.mem_product.mp hright).1).1); exact hne he
  have hcard : (U.erase s).card = 2 * r - 1 := (by simp [U])
  constructor
  · rw [hzero, Finset.card_product, Finset.card_powersetCard, hcard]
  · rw [hone, Finset.card_union_of_disjoint hdis, Finset.card_product, Finset.card_product, Finset.card_singleton, Finset.card_powersetCard, hcard, hyes, one_mul]
private theorem boundary_pair_excess (r k : ℕ) (hr : 2 ≤ r) (s : Fin (2 * r)) : let F := (Finset.univ : Finset (Fin (2 * r))) ×ˢ (Finset.univ : Finset (Fin (2 * r))).powersetCard (r - 1); (F.filter (fun p => boundaryPairOcc k s p = k)).card = (F.filter (fun p => boundaryPairOcc k s p = k + 1)).card + 3 * Nat.choose (2 * r - 1) (r - 2) ∧ 0 < 3 * Nat.choose (2 * r - 1) (r - 2) := by
  obtain ⟨hc0, hc1⟩ := boundary_pair_counts r k hr s
  obtain ⟨hb, hp⟩ := boundary_count_positive r hr
  dsimp only at hc0 hc1 ⊢; rw [hc0, hc1]
  refine ⟨?_, hp⟩
  have hL : 2 * r - 1 = (2 * r - 2) + 1 := (by omega)
  calc
    (2 * r - 1) * Nat.choose (2 * r - 1) (r - 1) = (2 * r - 2) * Nat.choose (2 * r - 1) (r - 1) + Nat.choose (2 * r - 1) (r - 1) := by
        conv_lhs => lhs; rw [hL]
        ring
    _ = _ := by rw [hb]; ring
private def boundaryLayer (r K k b : ℕ) (s : Fin (2*r)) : Finset (Fin (2*r) × Fin K → Bool) := Finset.univ.filter fun z =>
    (∑ a, if z a then (1 : ℕ) else 0) = (2*k+1)*r ∧
    (∑ a, if z a then a.2.val else 0) = r*k^2+k+1 ∧
    (∃ a, z a = true ∧ 2*k+1 ≤ a.2.val) ∧
    (∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0) = b
private theorem boundary_layer_card (r K k b : ℕ) (hr : 2 ≤ r) (hK : 2*k+1 < K) (s : Fin (2*r)) : (boundaryLayer r K k b s).card = (((Finset.univ : Finset (Fin (2*r))) ×ˢ (Finset.univ : Finset (Fin (2*r))).powersetCard (r-1)).filter (fun p => boundaryPairOcc k s p = b)).card := by
  classical
  symm
  apply Finset.card_bij (fun p _ => boundaryMask hK p.2 p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, Finset.mem_univ, true_and] at hp
    obtain ⟨hn,hE,hu⟩ := boundaryMask_data r K k hr hK p.2 hp.1 p.1
    simp only [boundaryLayer, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hn,hE,hu, by simpa only [boundaryMask_site_count, boundaryPairOcc] using hp.2⟩
  · intro p hp q hq he
    exact boundaryMask_injective hK he
  · intro z hz
    simp only [boundaryLayer, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨p,hpc,hp⟩ := boundaryMask_surjective r K k hr hK z hz.1 hz.2.2.1 hz.2.1
    refine ⟨p, ?_, hp⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, Finset.mem_univ, true_and]
    refine ⟨hpc, ?_⟩
    have hocc := (hz.2.2.2); rw [← hp, boundaryMask_site_count] at hocc; exact hocc
private theorem first_unmatched_layer_excess (r K k : ℕ) (hr : 2 ≤ r) (hK : 2*k+1 < K) (s : Fin (2*r)) : (boundaryLayer r K k k s).card = (boundaryLayer r K k (k+1) s).card + 3 * Nat.choose (2*r-1) (r-2) ∧ 0 < 3 * Nat.choose (2*r-1) (r-2) := by
  rw [boundary_layer_card r K k k hr hK s, boundary_layer_card r K k (k+1) hr hK s]; exact boundary_pair_excess r k hr s
private def unmatchedFamily (r K k b : ℕ) (s : Fin (2*r)) : Finset (Fin (2*r) × Fin K → Bool) := Finset.univ.filter fun z =>
    (∑ a, if z a then (1 : ℕ) else 0) = (2*k+1)*r ∧
    (∃ a, z a = true ∧ 2*k+1 ≤ a.2.val) ∧
    (∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0) = b
private theorem unmatched_small_t_adjacent (r K k : ℕ) (hr : 2 ≤ r) (hK : 2*k+1 < K) (s : Fin (2*r)) : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → (∑ z ∈ unmatchedFamily r K k (k+1) s, t^(∑ a, if z a then a.2.val else 0)) < ∑ z ∈ unmatchedFamily r K k k s, t^(∑ a, if z a then a.2.val else 0) := by
  classical
  have hbound (b : ℕ) (z : Fin (2*r) × Fin K → Bool) (hz : z ∈ unmatchedFamily r K k b s) : r*k^2+k+1 ≤ ∑ a, if z a then a.2.val else 0 := by
    simp only [unmatchedFamily, Finset.mem_filter, Finset.mem_univ, true_and] at hz; exact unmatched_energy_lower_bound r K k (by omega) z hz.1 hz.2.1
  have hlayer (b : ℕ) : ((unmatchedFamily r K k b s).filter (fun z => (∑ a, if z a then a.2.val else 0) = r*k^2+k+1)) = boundaryLayer r K k b s := by
    ext z
    simp only [unmatchedFamily, boundaryLayer, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hn,hu,hocc⟩,he⟩
      exact ⟨hn,he,hu,hocc⟩
    · rintro ⟨hn,he,hu,hocc⟩
      exact ⟨⟨hn,hu,hocc⟩,he⟩
  obtain ⟨he,hp⟩ := first_unmatched_layer_excess r K k hr hK s
  apply finite_monomial_comparison (unmatchedFamily r K k (k+1) s) (unmatchedFamily r K k k s) (fun z => ∑ a, if z a then a.2.val else 0) (r*k^2+k+1) (hbound (k+1)) (hbound k)
  rw [hlayer,hlayer]; omega
private theorem siteExponent_compl {K a : ℕ} (ha : a ≤ K) : (2 : ℤ) * (siteExponent (K - a) : ℤ) - 2 * siteExponent a = ((K : ℤ) - 3) * ((K : ℤ) - 2 * a) := by
  have h := (siteExponent_twice a); have hc := (siteExponent_twice (K - a)); have hs : ((K - a : ℕ) : ℤ) = (K : ℤ) - a := (Int.ofNat_sub ha); have h' : (2 : ℤ) * siteExponent a + 3 * a = (a : ℤ) * a + 2 := (by exact_mod_cast h); have hc' : (2 : ℤ) * siteExponent (K - a) + 3 * ((K - a : ℕ) : ℤ) = ((K - a : ℕ) : ℤ) * ((K - a : ℕ) : ℤ) + 2 := (by exact_mod_cast hc); rw [hs] at hc'; nlinarith
private theorem complement_involutive {K L : ℕ} : Function.Involutive (fun (η : Fin L → Fin (K + 1)) i => (η i).rev) := by
  intro η
  funext i
  simp
private theorem complement_val {K L : ℕ} (η : Fin L → Fin (K + 1)) (i : Fin L) : ((η i).rev : ℕ) = K - (η i : ℕ) := by simpa only [Nat.add_sub_add_right] using Fin.val_rev (η i)
private theorem complement_sum {K L : ℕ} (η : Fin L → Fin (K + 1)) : (∑ i, ((η i).rev : ℕ)) + ∑ i, (η i : ℕ) = K * L := by
  rw [← Finset.sum_add_distrib]
  simp_rw [complement_val]
  have hi (i : Fin L) : K - (η i : ℕ) + (η i : ℕ) = K := (Nat.sub_add_cancel (Nat.le_of_lt_succ (η i).isLt))
  simp_rw [hi]
  simp [Nat.mul_comm]
private theorem complement_energy {K L n : ℕ} (η : Fin L → Fin (K + 1)) (hn : ∑ i, (η i : ℕ) = n) (hc : 2 * n = K * L) : (∑ i, siteExponent ((η i).rev : ℕ)) = ∑ i, siteExponent (η i : ℕ) := by
  have hi (i : Fin L) := (siteExponent_compl (Nat.le_of_lt_succ (η i).isLt)); have hs := (Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) => hi i))
  simp_rw [← complement_val η] at hs
  have hn' : (∑ i, ((η i : ℕ) : ℤ)) = (n : ℤ) := (by exact_mod_cast hn); have hc' : (2 : ℤ) * n = (K : ℤ) * L := (by exact_mod_cast hc); simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs; rw [hn'] at hs; have hzero : ((K : ℤ) - 3) * ((L : ℤ) * K - 2 * n) = 0 := (by nlinarith); have hout : (∑ i, (siteExponent ((η i).rev : ℕ) : ℤ)) = ∑ i, (siteExponent (η i : ℕ) : ℤ) := (by nlinarith)
  exact_mod_cast hout
private theorem wt_complement {K L n : ℕ} (η : Fin L → Fin (K + 1)) (t : ℝ) (hn : ∑ i, (η i : ℕ) = n) (hc : 2 * n = K * L) : wt K L t ((fun i => (η i).rev)) = wt K L t η := by
  unfold wt; change (∏ i, t ^ siteExponent ((η i).rev : ℕ) * qbinom t K ((η i).rev)) = ∏ i, t ^ siteExponent (η i : ℕ) * qbinom t K (η i); rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, complement_energy η hn hc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _; rw [complement_val]; exact (qbinom_symm t (Nat.le_of_lt_succ (η i).isLt)).symm
private theorem half_filling_pair {r K k : ℕ} (hK : K = 2 * k + 1) (s : Fin (2 * r)) (t : ℝ) : occProb K (2 * r) ((2 * k + 1) * r) t s k = occProb K (2 * r) ((2 * k + 1) * r) t s (k + 1) := by
  classical
  let n := ((2 * k + 1) * r); have hc : 2 * n = K * (2 * r) := (by dsimp [n]; rw [hK]; ring)
  have hflip (η : Fin (2 * r) → Fin (K + 1)) (hn : ∑ i, (η i : ℕ) = n) : ∑ i, ((η i).rev : ℕ) = n := by
    have h := (complement_sum η); rw [hn] at h; omega
  unfold occProb
  congr 1
  apply Finset.sum_bij (fun η _ => (fun i => (η i).rev))
  · intro η hη
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    refine ⟨hflip η hη.1, ?_⟩
    rw [complement_val, hη.2, hK]; omega
  · intro η hη ξ hξ he
    exact complement_involutive.injective he
  · intro η hη
    refine ⟨(fun i => (η i).rev), ?_, complement_involutive η⟩
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    refine ⟨hflip η hη.1, ?_⟩
    rw [complement_val, hη.2, hK]; omega
  · intro η hη
    have hn : ∑ i, (η i : ℕ) = n := ((Finset.mem_filter.mp (Finset.mem_filter.mp hη).1).2); exact (wt_complement η t hn hc).symm
private theorem complement_energy_general {K L n : ℕ} (η : Fin L → Fin (K+1)) (hn : ∑ i, (η i : ℕ) = n) : (∑ i, (siteExponent ((η i).rev : ℕ) : ℤ)) = (∑ i, (siteExponent (η i : ℕ) : ℤ)) + (((K : ℤ)-3) * ((K : ℤ)*L-2*n))/2 := by
  have hi (i : Fin L) := (siteExponent_compl (Nat.le_of_lt_succ (η i).isLt)); have hs := (Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) => hi i))
  simp_rw [← complement_val η] at hs
  have hn' : (∑ i, ((η i : ℕ) : ℤ)) = (n : ℤ) := (by exact_mod_cast hn); simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn'] at hs; have he : (((K : ℤ)-3) * ((K : ℤ)*L-2*n)) = 2*((∑ i, (siteExponent ((η i).rev : ℕ) : ℤ)) - ∑ i, (siteExponent (η i : ℕ) : ℤ)) := (by nlinarith); rw [he]; omega
private theorem wt_complement_general {K L n : ℕ} (η : Fin L → Fin (K+1)) {t : ℝ} (ht : t ≠ 0) (hn : ∑ i, (η i : ℕ) = n) : wt K L t ((fun i => (η i).rev)) = t ^ ((((K : ℤ)-3)*((K : ℤ)*L-2*n))/2) * wt K L t η := by
  unfold wt; change (∏ i, t^siteExponent ((η i).rev : ℕ) * qbinom t K ((η i).rev)) = _ * ∏ i, t^siteExponent (η i : ℕ) * qbinom t K (η i); have hq (i : Fin L) : qbinom t K ((η i).rev) = qbinom t K (η i) := by
    rw [complement_val]; exact (qbinom_symm t (Nat.le_of_lt_succ (η i).isLt)).symm
  simp_rw [hq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← zpow_natCast t, ← zpow_natCast t]; simp only [Nat.cast_sum]; rw [complement_energy_general η hn, zpow_add₀ ht]; ring
private theorem config_sum_complement {K L n : ℕ} (hn : n ≤ K*L) (P : (Fin L → Fin (K+1)) → Prop) [DecidablePred P] (f : (Fin L → Fin (K+1)) → ℝ) : (∑ η ∈ (configs K L (K*L-n)).filter P, f η) = ∑ η ∈ (configs K L n).filter (fun η => P ((fun i => (η i).rev))), f ((fun i => (η i).rev)) := by
  classical
  apply Finset.sum_bij (fun η _ => (fun i => (η i).rev))
  · intro η hη
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    refine ⟨?_, by simpa only [complement_involutive η] using hη.2⟩
    have h := (complement_sum η); rw [hη.1] at h; omega
  · intro η hη ξ hξ he
    exact complement_involutive.injective he
  · intro η hη
    refine ⟨(fun i => (η i).rev), ?_, complement_involutive η⟩
    simp only [configs, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    refine ⟨?_, hη.2⟩
    have h := (complement_sum η); rw [hη.1] at h; omega
  · intro η hη
    exact congrArg f (complement_involutive η).symm
private theorem occProb_complement {K L n a : ℕ} (hn : n ≤ K*L) (ha : a ≤ K) {t : ℝ} (ht : t ≠ 0) (s : Fin L) : occProb K L (K*L-n) t s (K-a) = occProb K L n t s a := by
  classical
  let c := (t ^ ((((K : ℤ)-3)*((K : ℤ)*L-2*n))/2)); have hw (η : Fin L → Fin (K+1)) (hη : η ∈ configs K L n) : wt K L t ((fun i => (η i).rev)) = c * wt K L t η := (wt_complement_general η ht (Finset.mem_filter.mp hη).2); have hf : ((configs K L n).filter (fun η => ((η s).rev : ℕ) = K-a)) = (configs K L n).filter (fun η => (η s : ℕ)=a) := by
    have hi (η : Fin L → Fin (K+1)) : ((η s).rev : ℕ)=K-a ↔ (η s : ℕ)=a := by
      rw [complement_val η s]; have hη : (η s : ℕ) ≤ K := (Nat.le_of_lt_succ (η s).isLt); omega
    ext η
    simp only [Finset.mem_filter,hi]
  unfold occProb; rw [config_sum_complement hn (fun η => (η s : ℕ)=K-a) (wt K L t), hf]; have hd := (config_sum_complement hn (fun _ => True) (wt K L t)); simp only [Finset.filter_true] at hd; rw [hd]; have hnum : (∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ)=a), wt K L t ((fun i => (η i).rev))) = c * ∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ)=a), wt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun η hη => hw η (Finset.mem_filter.mp hη).1)
  have hden : (∑ η ∈ configs K L n, wt K L t ((fun i => (η i).rev))) = c * ∑ η ∈ configs K L n, wt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl hw
  rw [hnum,hden,mul_div_mul_left _ _ (zpow_ne_zero _ ht)]
private theorem qnum_recip {t : ℝ} (ht : t ≠ 0) (a : ℕ) : t ^ a * qnum t⁻¹ (a + 1) = qnum t (a + 1) := by
  unfold qnum; rw [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (a + 1), t ^ (a - j) := by
      apply Finset.sum_congr rfl
      intro j hj; rw [inv_pow, ← pow_sub₀ t ht (by have := Finset.mem_range.mp hj; omega)]
    _ = _ := by simpa using Finset.sum_range_reflect (fun j => t ^ j) (a + 1)
private theorem qfact_recip {t : ℝ} (ht : t ≠ 0) (a : ℕ) : t ^ a.choose 2 * qfact t⁻¹ a = qfact t a := by
  have hs : a.choose 2 = ∑ j ∈ Finset.range a, j := (by rw [Finset.sum_range_id, Nat.choose_two_right]); rw [hs, ← Finset.prod_pow_eq_pow_sum, qfact, ← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun j _ => qnum_recip ht j)
private theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  omega
private theorem qbinom_recip {t : ℝ} (ht : t ≠ 0) {K a : ℕ} (ha : a ≤ K) : t ^ (a * (K - a)) * qbinom t⁻¹ K a = qbinom t K a := by
  have he : K.choose 2 = (K - a).choose 2 + a.choose 2 + a * (K - a) := by
    have h := (choose_two_add (K - a) a); rw [Nat.sub_add_cancel ha, Nat.mul_comm (K - a) a] at h; exact h
  have hf (b : ℕ) : qfact t⁻¹ b = qfact t b / t ^ b.choose 2 := by
    apply (eq_div_iff (pow_ne_zero _ ht)).mpr
    simpa [mul_comm] using qfact_recip ht b
  simp only [qbinom, ite_eq_left ha, hf]; rw [he, pow_add, pow_add]; field_simp
private theorem prod_zpow_eq_zpow_sum {α : Type*} (S : Finset α) (f : α → ℤ) {t : ℝ} (ht : t ≠ 0) : (∏ a ∈ S, t ^ f a) = t ^ (∑ a ∈ S, f a) := by
  let u : ℝˣ := Units.mk0 t ht
  have h := map_prod (zpowersHom (ℝˣ) u) (fun a => Multiplicative.ofAdd (f a)) S
  have h' := congrArg (fun v : ℝˣ => (v : ℝ)) h
  simpa [← ofAdd_sum, u] using h'.symm
private theorem site_weight_recip {t : ℝ} (ht : t ≠ 0) {K a : ℕ} (ha : a ≤ K) : (t⁻¹ ^ siteExponent a * qbinom t⁻¹ K a) = t ^ (-(((K : ℤ) - 3) * a + 2)) * (t ^ siteExponent a * qbinom t K a) := by
  have hb : qbinom t⁻¹ K a = t ^ (-((a * (K - a) : ℕ) : ℤ)) * qbinom t K a := by
    have h := (qbinom_recip ht ha); rw [zpow_neg, zpow_natCast]
    apply mul_left_cancel₀ (pow_ne_zero (a * (K - a)) ht)
    rw [h]; field_simp
  rw [hb, ← zpow_natCast t⁻¹ (siteExponent a), inv_zpow, ← zpow_neg, ← zpow_natCast t (siteExponent a), ← mul_assoc, ← zpow_add₀ ht, ← mul_assoc, ← zpow_add₀ ht]
  congr 2
  have h := (siteExponent_twice a); have h' : (2 : ℤ) * siteExponent a + 3 * a = (a : ℤ) * a + 2 := (by exact_mod_cast h); rw [Nat.cast_mul, Int.ofNat_sub ha]; nlinarith
private theorem wt_recip {K L n : ℕ} (η : Fin L → Fin (K + 1)) {t : ℝ} (ht : t ≠ 0) (hn : ∑ i, (η i : ℕ) = n) : wt K L t⁻¹ η = t ^ (-(((K : ℤ) - 3) * n + 2 * L)) * wt K L t η := by
  unfold wt; change (∏ i, t⁻¹ ^ siteExponent (η i : ℕ) * qbinom t⁻¹ K (η i)) = _; have hi (i : Fin L) := (site_weight_recip ht (Nat.le_of_lt_succ (η i).isLt))
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ _ ht]
  congr 2
  have hn' : (∑ i, ((η i : ℕ) : ℤ)) = (n : ℤ) := (by exact_mod_cast hn); simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn']; ring
private theorem occProb_recip {K L n : ℕ} {t : ℝ} (ht : t ≠ 0) (s : Fin L) (a : ℕ) : occProb K L n t⁻¹ s a = occProb K L n t s a := by
  classical
  let c := (t ^ (-(((K : ℤ) - 3) * n + 2 * L))); have hw (η : Fin L → Fin (K + 1)) (hη : η ∈ configs K L n) : wt K L t⁻¹ η = c * wt K L t η := (wt_recip η ht (Finset.mem_filter.mp hη).2); unfold occProb; have hnum : (∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), wt K L t⁻¹ η) = c * ∑ η ∈ (configs K L n).filter (fun η => (η s : ℕ) = a), wt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun η hη => hw η (Finset.mem_filter.mp hη).1)
  have hden : (∑ η ∈ configs K L n, wt K L t⁻¹ η) = c * ∑ η ∈ configs K L n, wt K L t η := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl hw
  rw [hnum, hden, mul_div_mul_left _ _ (zpow_ne_zero _ ht)]
private theorem slotNum_masks (K L n b : ℕ) (t : ℝ) (s : Fin L) : slotNum K L n t s b = ∑ z ∈ (Finset.univ : Finset (Fin L × Fin K → Bool)).filter (fun z => (∑ a, if z a then (1 : ℕ) else 0)=n ∧ (∑ j : Fin K, if z (s,j) then (1 : ℕ) else 0)=b), t^(∑ a, if z a then a.2.val else 0) := by
  classical
  unfold slotNum; rw [Finset.powersetCard_eq_filter,Finset.powerset_univ,Finset.filter_filter]; rw [sum_slots_masks]; simp only [slotsOfMask_card,slotsOfMask_sum,slotsOfMask_occupation]
private theorem slotDen_pos {K L n : ℕ} (hn : n ≤ L*K) {t : ℝ} (ht : 0<t) : 0 < slotDen K L n t := by
  apply Finset.sum_pos (fun S _ => pow_pos ht _)
  apply Finset.powersetCard_nonempty.mpr
  simpa using hn
private theorem small_t_low_slots (r K k : ℕ) (hr : 2≤r) (hK : 2*k+1<K) (s : Fin (2*r)) : ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → ∀ b≤K, b≠k → slotNum K (2*r) ((2*k+1)*r) t s b < slotNum K (2*r) ((2*k+1)*r) t s k := by
  classical
  obtain ⟨εa,hεa,ha⟩ := unmatched_small_t_adjacent r K k hr hK s
  have hadj (t : ℝ) (ht : 0<t) (hte : t<εa) : slotNum K (2*r) ((2*k+1)*r) t s (k+1) < slotNum K (2*r) ((2*k+1)*r) t s k := by
    have h := (ha t ht hte); have hd := (slot_adjacent_difference r K k hK.le s t); rw [highSlotNum_masks,highSlotNum_masks] at hd; change _ = (∑ z ∈ unmatchedFamily r K k k s, _) - (∑ z ∈ unmatchedFamily r K k (k+1) s, _) at hd; linarith
  obtain ⟨εb,hεb,hb⟩ := finite_uniform_radius ((Finset.range (K+1)).filter (fun b => b≠k ∧ b≠k+1)) (fun b t => slotNum K (2*r) ((2*k+1)*r) t s b < slotNum K (2*r) ((2*k+1)*r) t s k) (by
      intro b hb
      obtain ⟨_,hb0,hb1⟩ := Finset.mem_filter.mp hb
      obtain ⟨ε,hε,he⟩ := nonadjacent_small_t r K k b k hr (by omega) hb0 hb1 (Or.inl rfl) s
      refine ⟨ε,hε,?_⟩
      intro t ht hte
      simpa only [slotNum_masks,maskFamily] using he t ht hte)
  refine ⟨min εa εb,lt_min hεa hεb,?_⟩
  intro t ht hte b hbK hbk
  by_cases hb1 : b=k+1
  · subst b
    exact hadj t ht (lt_of_lt_of_le hte (min_le_left _ _))
  · apply hb t ht (lt_of_lt_of_le hte (min_le_right _ _)) b
    simp only [Finset.mem_filter,Finset.mem_range]; exact ⟨by omega,hbk,hb1⟩
private theorem small_t_low (r K k : ℕ) (hr : 2≤r) (hK : 2*k+1<K) (s : Fin (2*r)) : ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → ∀ b≤K, b≠k → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s k := by
  obtain ⟨ε,hε,he⟩ := small_t_low_slots r K k hr hK s
  refine ⟨ε,hε,?_⟩
  intro t ht hte b hb hbk; rw [occProb_slots ht,occProb_slots ht]
  apply (div_lt_div_iff_of_pos_right (slotDen_pos (by nlinarith [Nat.mul_le_mul_right r (show 2*k+1 ≤ 2*K by omega)]) ht)).mpr
  exact he t ht hte b hb hbk
private theorem small_t_central (r K k : ℕ) (hr : 2≤r) (hK : 2*k+1=K) (s : Fin (2*r)) : ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → occProb K (2*r) ((2*k+1)*r) t s k = occProb K (2*r) ((2*k+1)*r) t s (k+1) ∧ ∀ b≤K, b≠k → b≠k+1 → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s k := by
  classical
  obtain ⟨ε,hε,he⟩ := finite_uniform_radius ((Finset.range (K+1)).filter (fun b => b≠k ∧ b≠k+1)) (fun b t => occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s k) (by
      intro b hb
      obtain ⟨_,hb0,hb1⟩ := Finset.mem_filter.mp hb
      obtain ⟨ε,hε,hb⟩ := nonadjacent_small_t r K k b k hr (by omega) hb0 hb1 (Or.inl rfl) s
      refine ⟨ε,hε,?_⟩
      intro t ht hte; rw [occProb_slots ht,occProb_slots ht]
      apply (div_lt_div_iff_of_pos_right (slotDen_pos (by nlinarith [Nat.mul_le_mul_right r (show 2*k+1 ≤ 2*K by omega)]) ht)).mpr
      simpa only [slotNum_masks,maskFamily] using hb t ht hte)
  refine ⟨ε,hε,?_⟩
  intro t ht hte
  refine ⟨half_filling_pair hK.symm s t,?_⟩
  intro b hb hb0 hb1
  apply he t ht hte b
  simp only [Finset.mem_filter,Finset.mem_range]; exact ⟨by omega,hb0,hb1⟩
private theorem small_t_high (r K k : ℕ) (hr : 2≤r) (hk : k<K) (hK : K<2*k+1) (s : Fin (2*r)) : ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → ∀ b≤K, b≠k+1 → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s (k+1) := by
  let j := (K-k-1); have hj : j<K := (by dsimp [j]; omega)
  have hjlow : 2*j+1<K := (by dsimp [j]; omega)
  have hjk : K-j=k+1 := (by dsimp [j]; omega)
  have hcount : K*(2*r)-(2*j+1)*r=(2*k+1)*r := by
    have hsum : (2*j+1)+(2*k+1)=2*K := (by dsimp [j]; omega)
    have htotal : (2*j+1)*r+(2*k+1)*r=K*(2*r) := (by nlinarith [congrArg (fun u : ℕ => u*r) hsum]); omega
  have hn : (2*j+1)*r ≤ K*(2*r) := (by nlinarith [Nat.mul_le_mul_right r hjlow.le])
  obtain ⟨ε,hε,he⟩ := small_t_low r K j hr hjlow s
  refine ⟨ε,hε,?_⟩
  intro t ht hte b hb hbk; have hp (a : ℕ) (ha : a≤K) : occProb K (2*r) ((2*k+1)*r) t s a = occProb K (2*r) ((2*j+1)*r) t s (K-a) := by
    have h := (occProb_complement hn (Nat.sub_le K a) ht.ne' s); rw [hcount,Nat.sub_sub_self ha] at h; exact h
  rw [hp b hb,hp (k+1) (by omega)]; have heq : K-(k+1)=j := (by dsimp [j];omega); rw [heq]; exact he t ht hte (K-b) (Nat.sub_le K b) (by omega)
private theorem extremes_of_reciprocal (P : ℝ → Prop) (hP : ∃ ε>0, ∀ t : ℝ, 0<t → t<ε → P t) (hinv : ∀ t : ℝ, 0<t → P t⁻¹ → P t) : ∃ ε>0, ∀ t : ℝ, 0<t → (t<ε ∨ 1/ε<t) → P t := by
  obtain ⟨ε,hε,he⟩ := hP
  refine ⟨ε,hε,?_⟩
  intro t ht hte
  rcases hte with hsmall | hlarge
  · exact he t ht hsmall
  · apply hinv t ht
    apply he t⁻¹ (inv_pos.mpr ht)
    exact (inv_lt_comm₀ ht hε).mpr (by simpa only [one_div] using hlarge)
theorem result : claim := by
  intro r K k hr hK hk; dsimp only; let s : Fin (2*r) := (⟨0,by omega⟩); let P (t : ℝ) : Prop := ((2*k+1<K → ∀ b≤K, b≠k → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s k) ∧ (K<2*k+1 → ∀ b≤K, b≠k+1 → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s (k+1)) ∧ (2*k+1=K → occProb K (2*r) ((2*k+1)*r) t s k = occProb K (2*r) ((2*k+1)*r) t s (k+1) ∧ ∀ b≤K, b≠k → b≠k+1 → occProb K (2*r) ((2*k+1)*r) t s b < occProb K (2*r) ((2*k+1)*r) t s k))
  change ∃ ε>0, ∀ t : ℝ, 0<t → (t<ε ∨ 1/ε<t) → P t
  apply extremes_of_reciprocal P
  · rcases lt_trichotomy (2*k+1) K with hlo | heq | hhi
    · obtain ⟨ε,hε,he⟩ := small_t_low r K k hr hlo s
      refine ⟨ε,hε,?_⟩
      intro t ht hte; exact ⟨fun _ => he t ht hte,fun h => False.elim (by omega),fun h => False.elim (by omega)⟩
    · obtain ⟨ε,hε,he⟩ := small_t_central r K k hr heq s
      refine ⟨ε,hε,?_⟩
      intro t ht hte; exact ⟨fun h => False.elim (by omega),fun h => False.elim (by omega),fun _ => he t ht hte⟩
    · obtain ⟨ε,hε,he⟩ := small_t_high r K k hr hk hhi s
      refine ⟨ε,hε,?_⟩
      intro t ht hte; exact ⟨fun h => False.elim (by omega),fun _ => he t ht hte,fun h => False.elim (by omega)⟩
  · intro t ht hp; dsimp only [P] at hp ⊢
    simpa only [occProb_recip ht.ne'] using hp
end D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode
