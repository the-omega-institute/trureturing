/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A satisfaction cap forces a pairwise total-variation lower bound. -/
/-
proof_shape: pointwise_min_sum: content
escape_witness: pointwise_min_sum: support erasure counts the off-diagonal summands and bounds their total.
admission_basis: escape-witness
proof_shape: finite_overlap_lower_bound: content
escape_witness: finite_overlap_lower_bound: sum over distinct ordered pairs, then select a pair below the overlap average.
admission_basis: escape-witness
proof_shape: literal_index_lower: content
escape_witness: literal_index_lower: extreme full correlators force zero density on each violating table.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/TotalVariation/Pinsker.totalVariation; statement_id: sha256:417383b2f5f4a4f7c56881e521c516e431c6f287d2d24996ca4ec3797e2e61f3
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Model
import D5.S3.TotalVariation.Pinsker

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section
private def densityOverlap {A : Type*} [Fintype A] (p q : A → ℝ) : ℝ :=
  ∑ a, min (p a) (q a)

theorem pointwise_min_sum {S : Type*} [Fintype S] [DecidableEq S]
    (r : S → ℝ) (hnonneg : ∀ x, 0 ≤ r x) (m : ℕ)
    (hsupport : (Finset.univ.filter fun x => r x ≠ 0).card ≤ m) :
    (∑ x, ∑ y, if x = y then 0 else min (r x) (r y)) ≤
      (m - 1 : ℝ) * ∑ x, r x := by
  classical
  let supp := Finset.univ.filter fun x => r x ≠ 0
  have rz : ∀ x ∉ supp, r x = 0 := by
    intro x hx
    simpa [supp] using hx
  have inner (x : S) :
      (∑ y, if x = y then 0 else min (r x) (r y)) ≤
        ((supp.card : ℝ) - 1) * r x := by
    by_cases hx : x ∈ supp
    · have eq : (∑ y, if x = y then 0 else min (r x) (r y)) =
          ∑ y ∈ supp.erase x, min (r x) (r y) := by
        symm
        calc
          _ = ∑ y ∈ supp.erase x, if x = y then 0 else min (r x) (r y) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hxy : x ≠ y := Ne.symm (Finset.mem_erase.mp hy).1
            simp [hxy]
          _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
            intro y _ hy
            by_cases hxy : x = y
            · simp [hxy]
            · have hys : y ∉ supp := by simpa [Finset.mem_erase, Ne.symm hxy] using hy
              simp [hxy, rz y hys, min_eq_right (hnonneg x)])
      rw [eq]
      calc
        _ ≤ ∑ y ∈ supp.erase x, r x := Finset.sum_le_sum fun y hy => min_le_left _ _
        _ = ((supp.card : ℝ) - 1) * r x := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx]
          rw [Nat.cast_sub (by exact Finset.card_pos.mpr ⟨x,hx⟩), Nat.cast_one]
    · simp [rz x hx, min_eq_left (hnonneg _)]
  have bound := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset S)) => inner x)
  rw [← Finset.mul_sum] at bound
  exact bound.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hsupport) 1)
    (Finset.sum_nonneg fun x _ => hnonneg x))

theorem finite_overlap_lower_bound {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] (rho : S → A → ℝ) (m : ℕ)
    (hcard : 2 ≤ Fintype.card S)
    (hnonneg : ∀ x a, 0 ≤ rho x a)
    (hnorm : ∀ x, ∑ a, rho x a = 1)
    (hsupport : ∀ a, (Finset.univ.filter fun x => rho x a ≠ 0).card ≤ m) :
    ∃ x y, x ≠ y ∧
      ((Fintype.card S : ℝ) - m) / ((Fintype.card S : ℝ) - 1) ≤
        D5.S3.TotalVariation.Pinsker.totalVariation (rho x) (rho y) := by
  have sum_offdiag_const {S : Type _} [Fintype S] [DecidableEq S]
      (x : S) (c : ℝ) :
      (∑ y, if x = y then 0 else c) = ((Fintype.card S : ℝ) - 1) * c := by
    have point : ∀ y, (if x = y then 0 else c) = c - (if x = y then c else 0) := by
      intro y
      split_ifs <;> ring
    simp_rw [point]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have tv_eq_one_sub_overlap {A : Type _} [Fintype A]
      (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
      D5.S3.TotalVariation.Pinsker.totalVariation p q = 1 - densityOverlap p q := by
    have point : ∀ a, |p a - q a| = p a + q a - 2 * min (p a) (q a) := by
      intro a
      rcases le_total (p a) (q a) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    unfold D5.S3.TotalVariation.Pinsker.totalVariation densityOverlap
    simp_rw [point]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
    ring
  classical
  have hn : 1 < (Fintype.card S : ℝ) := by exact_mod_cast hcard
  have hn0 : (Fintype.card S : ℝ) - 1 ≠ 0 := by linarith
  let c : ℝ := (m - 1 : ℝ) / ((Fintype.card S : ℝ) - 1)
  let pairs := (Finset.univ.product (Finset.univ : Finset S)).filter fun xy => xy.1 ≠ xy.2
  have pairs_sum (f : S → S → ℝ) :
      (∑ xy ∈ pairs, f xy.1 xy.2) = ∑ x, ∑ y, if x = y then 0 else f x y := by
    simp only [pairs, Finset.sum_filter]
    rw [Finset.product_eq_sprod]
    rw [Finset.sum_product (Finset.univ : Finset S) (Finset.univ : Finset S)
      (fun xy : S × S => if xy.1 ≠ xy.2 then f xy.1 xy.2 else 0)]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : x = y <;> simp [h]
  have pairs_ne : pairs.Nonempty := by
    haveI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,hxy⟩ := exists_pair_ne S
    exact ⟨(x,y),by simp [pairs,hxy]⟩
  have total : (∑ xy ∈ pairs, densityOverlap (rho xy.1) (rho xy.2)) ≤
      ((m : ℝ) - 1) * Fintype.card S := by
    rw [pairs_sum (fun x y => densityOverlap (rho x) (rho y))]
    have exchange :
        (∑ x, ∑ y, if x = y then 0 else densityOverlap (rho x) (rho y)) =
          ∑ a, ∑ x, ∑ y, if x = y then 0 else min (rho x a) (rho y a) := by
      unfold densityOverlap
      have point : ∀ x y, (if x = y then 0 else ∑ a, min (rho x a) (rho y a)) =
          ∑ a, if x = y then 0 else min (rho x a) (rho y a) := by
        intro x y
        by_cases h : x = y <;> simp [h]
      simp_rw [point]
      simp_rw [Finset.sum_comm (f := fun y a => if _ = y then 0 else min (rho _ a) (rho y a))]
      rw [Finset.sum_comm]
    rw [exchange]
    calc
      _ ≤ ∑ a, ((m : ℝ) - 1) * ∑ x, rho x a := Finset.sum_le_sum
        fun a _ => pointwise_min_sum (fun x => rho x a) (fun x => hnonneg x a) m (hsupport a)
      _ = ((m : ℝ) - 1) * Fintype.card S := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hnorm]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have constants : (∑ xy ∈ pairs, c) = ((m : ℝ) - 1) * Fintype.card S := by
    rw [pairs_sum (fun _ _ => c)]
    change (∑ x : S, ∑ y : S, if x = y then 0 else c) = _
    have rows : (∑ x : S, ∑ y : S, if x = y then 0 else c) =
        ∑ _ : S, ((Fintype.card S : ℝ) - 1) * c :=
      Finset.sum_congr rfl (fun x _ => sum_offdiag_const x c)
    rw [rows]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [c]
    field_simp
  obtain ⟨xy,hxy,hle⟩ := Finset.exists_le_of_sum_le pairs_ne (total.trans_eq constants.symm)
  refine ⟨xy.1,xy.2,(Finset.mem_filter.mp hxy).2,?_⟩
  rw [tv_eq_one_sub_overlap _ _ (hnorm _) (hnorm _)]
  have algebra :
      ((Fintype.card S : ℝ) - m) / ((Fintype.card S : ℝ) - 1) = 1 - c := by
    dsimp [c]
    field_simp
    ring
  rw [algebra]
  linarith

theorem literal_index_lower {n : ℕ} {S : Type*} [Fintype S]
    (embed : S → Setting n) (m : ℕ) (hcard : 2 ≤ Fintype.card S)
    (hcap : ∀ lambda : Strategy n,
      (Finset.univ.filter fun x => response lambda (embed x) Finset.univ = target (embed x)).card ≤ m)
    (rho : Setting n → Strategy n → ℝ) (hfaith : Faithful rho) :
    ((Fintype.card S : ℝ) - m) / ((Fintype.card S : ℝ) - 1) ≤ F rho := by
  have boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
    cases b <;> simp [boolSign]
  have density_supported_of_extreme {A : Type _} [Fintype A]
      (p r : A → ℝ) (t : ℝ) (hp : ∀ a, 0 ≤ p a)
      (hnorm : ∑ a, p a = 1) (hr : ∀ a, r a = 1 ∨ r a = -1)
      (ht : t = 1 ∨ t = -1) (hfull : ∑ a, p a * r a = t) :
      ∀ a, r a ≠ t → p a = 0 := by
    classical
    have hnonneg : ∀ a, 0 ≤ p a * (1 - t * r a) := by
      intro a
      rcases ht with ht | ht <;> rcases hr a with ha | ha <;> simp [ht,ha] <;>
        nlinarith [hp a]
    have hsum : ∑ a, p a * (1 - t * r a) = 0 := by
      have hpoint : ∀ a, p a * (1 - t * r a) = p a - t * (p a * r a) := by
        intro a
        ring
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hfull]
      rcases ht with ht | ht <;> simp [ht]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnonneg a)).mp hsum
    intro a hat
    have ha := hz a (Finset.mem_univ a)
    rcases ht with ht | ht <;> rcases hr a with ha' | ha' <;> simp_all <;> linarith
  have response_cases {n : ℕ} (lambda : Strategy n) (x : Setting n)
      (I : Finset (Fin n)) : response lambda x I = 1 ∨ response lambda x I = -1 := by
    classical
    unfold response
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
        rw [Finset.prod_insert hi]
        rcases boolSign_cases (responseBit lambda x i) with h | h <;>
          rcases ih with ih | ih <;> simp [h,ih]
  have faithful_support {n : ℕ} (rho : Setting n → Strategy n → ℝ) (h : Faithful rho) :
      ∀ x lambda, response lambda x Finset.univ ≠ target x → rho x lambda = 0 := by
    intro x
    exact density_supported_of_extreme (rho x) (fun lambda => response lambda x Finset.univ)
      (target x) (h.1.1 x) (h.1.2 x) (fun lambda => response_cases lambda x Finset.univ)
      (boolSign_cases _) (h.2.1 x)
  have pair_tv_le_F {n : ℕ} (rho : Setting n → Strategy n → ℝ) (x y : Setting n) :
      D5.S3.TotalVariation.Pinsker.totalVariation (rho x) (rho y) ≤ F rho := by
    have h := le_csSup (Set.finite_range
      (fun xy : Setting n × Setting n => ∑ lambda, |rho xy.1 lambda-rho xy.2 lambda|)).bddAbove
      (show (∑ lambda, |rho x lambda-rho y lambda|) ∈
        Set.range (fun xy : Setting n × Setting n => ∑ lambda, |rho xy.1 lambda-rho xy.2 lambda|)
        from ⟨(x,y),rfl⟩)
    unfold D5.S3.TotalVariation.Pinsker.totalVariation F M
    linarith
  classical
  have hs (lambda : Strategy n) :
      (Finset.univ.filter fun x => rho (embed x) lambda ≠ 0).card ≤ m := by
    apply le_trans (Finset.card_le_card ?_) (hcap lambda)
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x,?_⟩
    by_contra hbad
    exact (Finset.mem_filter.mp hx).2 (faithful_support rho hfaith (embed x) lambda hbad)
  obtain ⟨x,y,hxy,hle⟩ := finite_overlap_lower_bound
    (fun x lambda => rho (embed x) lambda) m hcard
    (fun x lambda => hfaith.1.1 (embed x) lambda) (fun x => hfaith.1.2 (embed x)) hs
  exact hle.trans (pair_tv_le_F rho (embed x) (embed y))
end
end D5.S3.QuantumBounds.MerminMeasurementDependence
