/- GID: D5/S3/Fourier/Concentration/SparseCyclicMajorants
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/SparseCyclicMajorants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character support forces a mean floor and subgroup equality for nonnegative cyclic majorants. -/

import D5.S3.Fourier.FinitePoisson

set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.SparseCyclicMajorants

open Finset
open scoped ZMod
open D5.S3.Fourier.FinitePoisson

noncomputable section

private theorem sparse_dft_deficit (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (S : Finset (ZMod q))
    (hS : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0) :
    (S.card : ℝ) * (∑ x, K x) - (q : ℝ) * K 0 =
      ∑ k ∈ S, ∑ x : ZMod q, K x * (1 - (ZMod.stdAddChar (-(x * k))).re) := by
  classical
  let f : ZMod q → ℂ := fun x => (K x : ℂ)
  change ∀ k ∉ S, ZMod.dft f k = 0 at hS
  have hsum : (∑ k : ZMod q, ZMod.dft f k) = (q : ℂ) * f 0 := by
    have h := congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply f) 0
    rw [ZMod.invDFT_apply] at h
    simp only [mul_zero, AddChar.map_zero_eq_one, smul_eq_mul, one_mul] at h
    exact (inv_mul_eq_iff_eq_mul₀ (by exact_mod_cast (NeZero.ne q))).mp h
  have hsumS : (∑ k ∈ S, ZMod.dft f k) = (q : ℂ) * f 0 := by
    rw [← hsum]
    exact sum_subset (subset_univ S) (fun k _ hk => hS k hk)
  have hsumRe : (∑ k ∈ S, (ZMod.dft f k).re) = (q : ℝ) * K 0 := by
    simpa [Complex.re_sum, f] using congrArg Complex.re hsumS
  have hcoeff (k : ZMod q) :
      (ZMod.dft f k).re = ∑ x, K x * (ZMod.stdAddChar (-(x * k))).re := by
    rw [ZMod.dft_apply, Complex.re_sum]
    exact sum_congr rfl fun x _ => by simp [f, Complex.mul_re, mul_comm]
  rw [← hsumRe, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [hcoeff, ← sum_sub_distrib]
  exact sum_congr rfl fun x _ => by ring

/-- Recorded character modes impose a lower bound on the mean of a nonnegative majorant. -/
theorem sparse_dft_majorant_gap (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (hK : ∀ x, 0 ≤ K x) (S R : Finset (ZMod q))
    (hS : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0)
    (hR : ∀ x ∈ R, 1 ≤ K x) :
    let modeCount : ℝ := S.card
    (∑ k ∈ S, ∑ x ∈ R, (1 - (ZMod.stdAddChar (-(x * k))).re)) ≤
      modeCount * (∑ x, K x) - (q : ℝ) * K 0 := by
  classical
  dsimp only
  rw [sparse_dft_deficit q K S hS]
  refine sum_le_sum fun k _ => ?_
  have hphase (x : ZMod q) : 0 ≤ 1 - (ZMod.stdAddChar (-(x * k))).re := by
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq
      ((ZMod.stdAddChar (N := q)).norm_apply _))
  calc
    _ ≤ ∑ x ∈ R, K x * (1 - (ZMod.stdAddChar (-(x * k))).re) := by
      refine sum_le_sum fun x hx => ?_
      simpa using mul_le_mul_of_nonneg_right (hR x hx) (hphase x)
    _ ≤ ∑ x, K x * (1 - (ZMod.stdAddChar (-(x * k))).re) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ R) fun x _ _ => mul_nonneg (hK x) (hphase x)

private theorem phase_eq_one_of_re_eq_one (q : ℕ) [NeZero q] (x : ZMod q)
    (h : (ZMod.stdAddChar x).re = 1) : ZMod.stdAddChar x = 1 := by
  have hn := (ZMod.stdAddChar (N := q)).norm_apply x
  have hs := Complex.sq_norm (ZMod.stdAddChar x)
  rw [hn, Complex.normSq_apply, h] at hs
  apply Complex.ext h
  change (ZMod.stdAddChar x).im = 0
  nlinarith [sq_nonneg (ZMod.stdAddChar x).im]

private theorem sparse_dft_floor_eq (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (hK : ∀ x, 0 ≤ K x) (S : Finset (ZMod q))
    (hS : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0)
    (h0 : 0 < K 0)
    (hEq : (S.card : ℝ) * (∑ x, K x) = (q : ℝ) * K 0) :
    ∃ H : AddSubgroup (ZMod q),
      (∀ x, K x = @ite ℝ (x ∈ H) (Classical.propDecidable _) (K 0) 0) ∧
        ∀ k, k ∈ S ↔ k ∈ annihilator H := by
  classical
  let f : ZMod q → ℂ := fun x => (K x : ℂ)
  let H : AddSubgroup (ZMod q) := annihilator (AddSubgroup.closure (S : Set (ZMod q)))
  change ∀ k ∉ S, ZMod.dft f k = 0 at hS
  have hphase (k x : ZMod q) : 0 ≤ 1 - (ZMod.stdAddChar (-(x * k))).re := by
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq
      ((ZMod.stdAddChar (N := q)).norm_apply _))
  have hsum : (∑ k ∈ S, ∑ x : ZMod q, K x *
      (1 - (ZMod.stdAddChar (-(x * k))).re)) = 0 := by
    rw [← sparse_dft_deficit q K S hS, sub_eq_zero.mpr hEq]
  have hphasePos (k : ZMod q) (hk : k ∈ S) (x : ZMod q) (hx : 0 < K x) :
      ZMod.stdAddChar (-(x * k)) = 1 := by
    have hrows := (sum_eq_zero_iff_of_nonneg fun j _ =>
      sum_nonneg fun y _ => mul_nonneg (hK y) (hphase j y)).mp hsum k hk
    have hterm := (sum_eq_zero_iff_of_nonneg fun y _ =>
      mul_nonneg (hK y) (hphase k y)).mp hrows x (mem_univ x)
    apply phase_eq_one_of_re_eq_one q _
    rcases mul_eq_zero.mp hterm with h | h
    · exact (hx.ne' h).elim
    · linarith
  have hker (x : ZMod q) : x ∈ H ↔ ∀ k ∈ S, character x k = 1 := by
    constructor
    · intro hx k hk
      exact hx k (AddSubgroup.subset_closure hk)
    · intro hx
      have hle : AddSubgroup.closure (S : Set (ZMod q)) ≤
          (character x).toAddMonoidHom.ker :=
        (AddSubgroup.closure_le _).mpr fun k hk => AddMonoidHom.mem_ker.mpr (hx k hk)
      intro k hk
      exact AddMonoidHom.mem_ker.mp (hle hk)
  have hposMem (x : ZMod q) (hx : 0 < K x) : x ∈ H := by
    refine (hker x).mpr fun k hk => ?_
    rw [character_apply]
    have hneg := congrArg (ZMod.stdAddChar (N := q)) (neg_neg (x * k))
    rw [← hneg, AddChar.map_neg_eq_inv, hphasePos k hk x hx, inv_one]
  have hpoint (x : ZMod q) : K x = if x ∈ H then K 0 else 0 := by
    by_cases hx : x ∈ H
    · rw [ite_eq_left hx]
      have hs (y : ZMod q) : f y = (q : ℂ)⁻¹ *
          ∑ k ∈ S, ZMod.stdAddChar (k * y) * ZMod.dft f k := by
        have h := congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply f) y
        rw [ZMod.invDFT_apply, smul_eq_mul] at h
        refine h.symm.trans (congrArg _ (sum_subset (subset_univ S) ?_).symm)
        intro k _ hk
        simp [hS k hk, smul_eq_mul]
      have h := calc
        f x = (q : ℂ)⁻¹ * ∑ k ∈ S, ZMod.dft f k := by
          rw [hs]
          congr 1
          refine sum_congr rfl fun k hk => ?_
          have hh := (hker x).mp hx k hk
          rw [mul_comm k x, ← character_apply, hh, one_mul]
        _ = f 0 := by rw [hs]; simp
      simpa [f] using h
    · rw [ite_eq_right hx]
      exact le_antisymm (le_of_not_gt fun h => hx (hposMem x h)) (hK x)
  refine ⟨H, hpoint, fun k => ⟨?_, ?_⟩⟩
  · intro hk x hx
    rw [character_apply, mul_comm, ← character_apply]
    exact (hker x).mp hx k hk
  · intro hk
    by_contra hn
    have hd := hS k hn
    have hform : ZMod.dft f k = ∑ x, f x := by
      rw [ZMod.dft_apply]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ H
      · have hchar : ZMod.stdAddChar (-(x * k)) = 1 := by
          rw [AddChar.map_neg_eq_inv, mul_comm, ← character_apply, hk x hx, inv_one]
        rw [hchar, one_smul]
      · have hx0 : f x = 0 := by simp [f, hpoint x, hx]
        simp [hx0]
    rw [hform] at hd
    have htotal : 0 < ∑ x, K x :=
      sum_pos' (fun x _ => hK x) ⟨0, mem_univ _, h0⟩
    have hre := congrArg Complex.re hd
    simp [f, Complex.re_sum, htotal.ne'] at hre

/-- Equality at positive height occurs precisely for scaled subgroup indicators
and their annihilators as the selected frequency set. -/
theorem sparse_dft_floor_eq_iff (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (hK : ∀ x, 0 ≤ K x) (S : Finset (ZMod q))
    (hS : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0)
    (h0 : 0 < K 0) :
    let modeCount : ℝ := S.card
    modeCount * (∑ x, K x) = (q : ℝ) * K 0 ↔
      ∃ H : AddSubgroup (ZMod q),
        (∀ x, K x = @ite ℝ (x ∈ H) (Classical.propDecidable _) (K 0) 0) ∧
          ∀ k, k ∈ S ↔ k ∈ annihilator H := by
  classical
  dsimp only
  refine ⟨sparse_dft_floor_eq q K hK S hS h0, ?_⟩
  rintro ⟨H, hpoint, hfreq⟩
  apply sub_eq_zero.mp
  rw [sparse_dft_deficit q K S hS]
  refine sum_eq_zero fun k hk => sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ H
  · have hchar := (hfreq k).mp hk x hx
    simp [AddChar.map_neg_eq_inv, mul_comm x k, ← character_apply, hchar]
  · have hz : K x = 0 := (hpoint x).trans (ite_eq_right hx)
    rw [hz, zero_mul]

#print axioms sparse_dft_majorant_gap
#print axioms sparse_dft_floor_eq_iff

end

end D5.S3.Fourier.Concentration.SparseCyclicMajorants
