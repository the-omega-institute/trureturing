/- GID: D5/S1/Eigenstructure/WiersigFragmentedResponse
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/WiersigFragmentedResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp passive fragmented response and the minimum loss rank at a sole eigenvalue. -/

/- sharp_passive_fragmented_response
   proof_shape: content
   escape_witness: One block-shift construction realizes every positive fragmented partition
     and attains both the response bound and the eigenspace loss-rank floor.
   admission_basis: open-problem-resolution (#35071, whole-space collision)
   Direct frozen dependencies:
     D5/S1/Eigenstructure/NilpotentJordanChains.nilpotent_jordan_chains_rank -/

import OmegaBuild.Commands
import D5.S1.Eigenstructure.NilpotentJordanChains
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Passive fragmented response at a sole eigenvalue -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Module

namespace D5.S1.Eigenstructure.WiersigFragmentedResponse

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem normalized_cayley_contraction (A : Matrix n n ℂ) (hA : IsNilpotent A)
    (hG : (1 + A + Aᴴ).PosSemidef) :
    ‖A * (↑(hA.isUnit_one_add.unit⁻¹) : Matrix n n ℂ)‖ ≤ 1 := by
  let B : Matrix n n ℂ := 1 + A
  let C : Matrix n n ℂ := (↑(hA.isUnit_one_add.unit⁻¹) : Matrix n n ℂ)
  let T : Matrix n n ℂ := A * C
  have hB : IsUnit B := by
    exact hA.isUnit_one_add
  have hBC : B * C = 1 := by
    exact hB.mul_val_inv
  have hG' : Bᴴ * B - Aᴴ * A = 1 + A + Aᴴ := by
    dsimp [B]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring
  have hcong : (Cᴴ * (1 + A + Aᴴ) * C).PosSemidef := by
    exact hG.conjTranspose_mul_mul_same C
  have hident : 1 - Tᴴ * T = Cᴴ * (1 + A + Aᴴ) * C := by
    rw [hG'.symm]
    dsimp [T]
    simp only [Matrix.conjTranspose_mul]
    have hBCstar : Cᴴ * Bᴴ = 1 := by
      rw [← conjTranspose_mul, hBC, conjTranspose_one]
    have hunit : Cᴴ * (Bᴴ * (B * C)) = 1 := by simp [hBC, hBCstar]
    noncomm_ring [hunit]
  have hPSD : (1 - Tᴴ * T).PosSemidef := by
    rw [hident]
    exact hcong
  have horder : Tᴴ * T ≤ 1 := by
    rw [Matrix.le_iff]
    exact hPSD
  have hTnonneg : 0 ≤ Tᴴ * T := by
    exact (Matrix.posSemidef_conjTranspose_mul_self T).nonneg
  have hnormsq : ‖Tᴴ * T‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hTnonneg).2 horder
  have hsq : ‖T‖ * ‖T‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hnormsq
    exact hnormsq
  have hTnorm : ‖T‖ ≤ 1 := by
    nlinarith [norm_nonneg T]
  simpa [T, C] using hTnorm

private theorem normalized_cayley_top_power (A : Matrix n n ℂ) (hA : IsNilpotent A) {p : ℕ}
    (hp_pos : 0 < p) (hp : A ^ p = 0) :
    (A * (↑(hA.isUnit_one_add.unit⁻¹) : Matrix n n ℂ)) ^ (p - 1) = A ^ (p - 1) := by
  let B : Matrix n n ℂ := 1 + A
  let C : Matrix n n ℂ := (↑(hA.isUnit_one_add.unit⁻¹) : Matrix n n ℂ)
  let T : Matrix n n ℂ := A * C
  have hB : IsUnit B := by exact hA.isUnit_one_add
  have hBC : B * C = 1 := by exact hB.mul_val_inv
  have hCB : C * B = 1 := by exact hB.val_inv_mul
  have hAB : Commute A B := by
    change A * B = B * A
    dsimp [B]
    noncomm_ring
  have hAC : Commute A C := by
    calc
      A * C = (C * B) * A * C := by rw [hCB]; simp
      _ = C * (B * A) * C := by simp [mul_assoc]
      _ = C * (A * B) * C := by rw [hAB.eq]
      _ = C * A * (B * C) := by simp [mul_assoc]
      _ = C * A := by rw [hBC, mul_one]
  have hCBcomm : Commute C B := hCB.trans hBC.symm
  have hTpow (k : ℕ) : T ^ k = A ^ k * C ^ k := by
    dsimp [T]
    exact hAC.mul_pow k
  have hpowB (k : ℕ) : B ^ k = 1 + A * ∑ j ∈ Finset.range k, B ^ j := by
    have hBpowA (j : ℕ) : B ^ j * A = A * B ^ j :=
      (hAB.symm.pow_left j).eq
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Finset.sum_range_succ]
      have hsum : (∑ j ∈ Finset.range k, B ^ j) * A =
          A * ∑ j ∈ Finset.range k, B ^ j := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j hj => hBpowA j)
      change (1 + A * ∑ j ∈ Finset.range k, B ^ j) * (1 + A) = _
      simp only [mul_add, mul_one, add_mul, one_mul]
      rw [mul_assoc A (∑ j ∈ Finset.range k, B ^ j) A, hsum]
      rw [ih]
      noncomm_ring
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp_pos))
  have hTkA : T ^ (p - 1) * A = 0 := by
    rw [hTpow]
    calc
      A ^ (p - 1) * C ^ (p - 1) * A =
          A ^ (p - 1) * (C ^ (p - 1) * A) := by simp [mul_assoc]
      _ = A ^ (p - 1) * (A * C ^ (p - 1)) := by
        rw [(hAC.symm.pow_left (p - 1)).eq]
      _ = A ^ p * C ^ (p - 1) := by
        calc
          A ^ (p - 1) * (A * C ^ (p - 1)) =
              (A ^ (p - 1) * A) * C ^ (p - 1) := by simp [mul_assoc]
          _ = A ^ ((p - 1) + 1) * C ^ (p - 1) := by rw [pow_succ]
          _ = A ^ p * C ^ (p - 1) := by rw [hp1]
      _ = 0 := by rw [hp, zero_mul]
  have hEq : T ^ (p - 1) * B ^ (p - 1) = T ^ (p - 1) := by
    rw [hpowB, mul_add, mul_one, ← mul_assoc, hTkA, zero_mul, add_zero]
  have hTB : T ^ (p - 1) * B ^ (p - 1) = A ^ (p - 1) := by
    rw [hTpow]
    calc
      A ^ (p - 1) * C ^ (p - 1) * B ^ (p - 1) =
          A ^ (p - 1) * (C ^ (p - 1) * B ^ (p - 1)) := by simp [mul_assoc]
      _ = A ^ (p - 1) * (C * B) ^ (p - 1) := by rw [← hCBcomm.mul_pow]
      _ = A ^ (p - 1) := by rw [hCB, one_pow, mul_one]
  have htop : T ^ (p - 1) = A ^ (p - 1) := hEq.symm.trans hTB
  simpa [T, C] using htop

omit [Fintype n] in
private theorem loss_of_shift {E : ℂ} (A : Matrix n n ℂ) :
    let β : ℝ := -2 * E.im
    let c : ℂ := -Complex.I * β
    let H := E • (1 : Matrix n n ℂ) + c • A
    Complex.I • (H - Hᴴ) = (β : ℂ) • (1 + A + Aᴴ) := by
  dsimp
  set β : ℝ := -2 * E.im
  have hE : Complex.I * (E - star E) = (β : ℂ) := by
    apply Complex.ext
    · simp [β, Complex.mul_re]
      ring
    · simp [β, Complex.mul_im]
  have hI : Complex.I * (-Complex.I * (β : ℂ)) = β := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have hs : star (-Complex.I * (β : ℂ)) = Complex.I * β := by simp
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hs]
  simp only [smul_sub, smul_add, smul_smul, hI]
  have hstar : Complex.I * (Complex.I * (β : ℂ)) = -(β : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hscalar : (Complex.I * E) • (1 : Matrix n n ℂ) -
      (Complex.I * star E) • (1 : Matrix n n ℂ) = (β : ℂ) • (1 : Matrix n n ℂ) := by
    rw [← sub_smul, ← mul_sub, hE]
  rw [hstar, neg_smul]
  calc
    _ = ((Complex.I * E) • (1 : Matrix n n ℂ) - (Complex.I * star E) • 1) +
        (β : ℂ) • A + (β : ℂ) • Aᴴ := by abel
    _ = _ := by rw [hscalar]; rfl

private theorem rank_le_loss_of_shift {A : Matrix n n ℂ}
    (β : ℝ) (hβ : β ≠ 0) :
    Module.finrank ℂ (LinearMap.ker A.mulVecLin) ≤
      ((β : ℂ) • (1 + A + Aᴴ)).rank := by
  let G : Matrix n n ℂ := 1 + A + Aᴴ
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hβc)]
  let K := LinearMap.ker A.mulVecLin
  let f := G.mulVecLin.comp K.subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hAx : A *ᵥ (x : n → ℂ) = 0 := x.property
    have hGx : G *ᵥ (x : n → ℂ) = 0 := hx
    have hleft : star (x : n → ℂ) ᵥ* Aᴴ = 0 := by
      rw [← star_mulVec, hAx, star_zero]
    have hquad : star (x : n → ℂ) ⬝ᵥ (x : n → ℂ) = 0 := by
      have hh := congrArg (fun y : n → ℂ => star (x : n → ℂ) ⬝ᵥ y) hGx
      simpa [G, add_mulVec, hAx, dotProduct_add, dotProduct_mulVec, hleft] using hh
    exact Subtype.ext (dotProduct_star_self_eq_zero.mp hquad)
  calc
    Module.finrank ℂ K = Module.finrank ℂ (LinearMap.range f) :=
      (LinearMap.finrank_range_of_inj hf).symm
    _ ≤ G.rank := Submodule.finrank_mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩)

private theorem finite_resolvent (H : Matrix n n ℂ) (E : ℂ) {p : ℕ}
    (hp : (H - E • (1 : Matrix n n ℂ)) ^ p = 0) (z : ℂ) (hz : z ≠ E) :
    IsUnit (z • (1 : Matrix n n ℂ) - H) ∧
    (z • (1 : Matrix n n ℂ) - H)⁻¹ =
      ∑ k ∈ Finset.range p, ((z - E)⁻¹) ^ (k + 1) • (H - E • (1 : Matrix n n ℂ)) ^ k := by
  let N := H - E • (1 : Matrix n n ℂ)
  let t := z - E
  let Q := t⁻¹ • N
  have ht : t ≠ 0 := sub_ne_zero.mpr hz
  have hpQ : Q ^ p = 0 := by simp [Q, smul_pow, hp, N]
  have hzH : z • (1 : Matrix n n ℂ) - H = t • (1 - Q) := by
    rw [smul_sub]
    change _ = t • (1 : Matrix n n ℂ) - t • (t⁻¹ • N)
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    simp only [t, N, sub_smul]
    abel
  have hsum :
      (∑ k ∈ Finset.range p, t⁻¹ ^ (k + 1) • N ^ k) =
        t⁻¹ • ∑ k ∈ Finset.range p, Q ^ k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = t⁻¹ • (t⁻¹ • N) ^ k
    rw [smul_pow, smul_smul, pow_succ']
  change IsUnit _ ∧ _ = ∑ k ∈ Finset.range p, t⁻¹ ^ (k + 1) • N ^ k
  rw [hzH, hsum]
  have hleft : (t⁻¹ • ∑ k ∈ Finset.range p, Q ^ k) * (t • (1 - Q)) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ ht, one_smul,
      geom_sum_mul_neg, hpQ, sub_zero]
  exact ⟨IsUnit.of_mul_eq_one _ (mul_eq_one_comm.mp hleft), Matrix.inv_eq_left_inv hleft⟩

private theorem shift_estimates (H : Matrix n n ℂ) (E : ℂ) {p : ℕ} (hp : 2 ≤ p)
    (hβ : 0 < -2 * E.im) (hN : (H - E • (1 : Matrix n n ℂ)) ^ p = 0)
    (hG : (Complex.I • (H - Hᴴ)).PosSemidef) :
    ‖(H - E • (1 : Matrix n n ℂ)) ^ (p - 1)‖ ≤ (-2 * E.im) ^ (p - 1) ∧
      Module.finrank ℂ
        (LinearMap.ker (H - E • (1 : Matrix n n ℂ)).mulVecLin) ≤
      (Complex.I • (H - Hᴴ)).rank := by
  let β : ℝ := -2 * E.im
  let c : ℂ := -Complex.I * β
  let N := H - E • (1 : Matrix n n ℂ)
  let A := c⁻¹ • N
  have hβ' : 0 < β := hβ
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ'.ne'
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hβc
  have hcnorm : ‖c‖ = β := by
    simp [c, hβ'.le]
  have hNA : c • A = N := by simp [A, smul_smul, mul_inv_cancel₀ hc]
  have hH : E • (1 : Matrix n n ℂ) + c • A = H := by
    rw [hNA]
    dsimp [N]
    abel
  have hloss : Complex.I • (H - Hᴴ) = (β : ℂ) • (1 + A + Aᴴ) := by
    rw [← hH]
    exact loss_of_shift A
  have hAp : A ^ p = 0 := by simp [A, smul_pow, hN, N]
  have hAnil : IsNilpotent A := ⟨p, hAp⟩
  have hGn : (1 + A + Aᴴ).PosSemidef := by
    have h := hG
    rw [hloss] at h
    have hs : (0 : ℂ) ≤ (β : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv]
      exact_mod_cast (inv_nonneg.mpr hβ'.le)
    have hh := h.smul hs
    change ((β : ℂ)⁻¹ • ((β : ℂ) • (1 + A + Aᴴ))).PosSemidef at hh
    rwa [smul_smul, inv_mul_cancel₀ hβc, one_smul] at hh
  have hnorm := normalized_cayley_contraction A hAnil hGn
  have htop := normalized_cayley_top_power A hAnil (by omega) hAp
  have hApnorm : ‖A ^ (p - 1)‖ ≤ 1 := by
    rw [← htop]
    exact (norm_pow_le' _ (by omega : 0 < p - 1)).trans (pow_le_one₀ (norm_nonneg _) hnorm)
  have hker : LinearMap.ker N.mulVecLin = LinearMap.ker A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, A, smul_mulVec]
    exact ⟨fun h => by simp [h], fun h => (smul_eq_zero.mp h).resolve_left (inv_ne_zero hc)⟩
  change ‖N ^ (p - 1)‖ ≤ β ^ (p - 1) ∧
    Module.finrank ℂ (LinearMap.ker N.mulVecLin) ≤ _
  constructor
  · rw [← hNA, smul_pow, norm_smul, norm_pow, hcnorm]
    exact mul_le_of_le_one_right (pow_nonneg hβ.le _) hApnorm
  · rw [hker, hloss]
    exact rank_le_loss_of_shift β hβ.ne'

/-- A passive whole-space collision has the linewidth-only response bound, and its
loss rank is at least the dimension of the eigenspace. The finite resolvent
expansion identifies the highest-pole coefficient when the top power is nonzero. -/
private theorem passive_response_bound_and_loss_rank (H : Matrix n n ℂ) (E : ℂ) {p : ℕ}
    (hp : 2 ≤ p) (hβ : 0 < -2 * E.im)
    (hN : (H - E • (1 : Matrix n n ℂ)) ^ p = 0)
    (hG : (Complex.I • (H - Hᴴ)).PosSemidef) :
    let N := H - E • (1 : Matrix n n ℂ)
    ‖N ^ (p - 1)‖ ≤ (-2 * E.im) ^ (p - 1) ∧
      Module.finrank ℂ (LinearMap.ker N.mulVecLin) ≤ (Complex.I • (H - Hᴴ)).rank ∧
      ∀ z : ℂ, z ≠ E → IsUnit (z • (1 : Matrix n n ℂ) - H) ∧
        (z • (1 : Matrix n n ℂ) - H)⁻¹ =
        ∑ k ∈ Finset.range p, ((z - E)⁻¹) ^ (k + 1) • N ^ k := by
  obtain ⟨hnorm, hrank⟩ := shift_estimates H E hp hβ hN hG
  exact ⟨hnorm, hrank, finite_resolvent H E hN⟩

private abbrev Positions {b : ℕ} (m : Fin b → ℕ+) := Σ j, Fin (m j)

private def shiftPower {b : ℕ} (m : Fin b → ℕ+) (k : ℕ) :
    Matrix (Positions m) (Positions m) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.val = y.2.val + k then 1 else 0

private theorem shiftPower_column {b : ℕ} (m : Fin b → ℕ+) (k : ℕ) (y : Positions m) :
    (shiftPower m k).col y =
      if h : y.2.val + k < m y.1 then Pi.single ⟨y.1, ⟨y.2.val + k, h⟩⟩ 1 else 0 := by
  funext x
  by_cases hy : y.2.val + k < m y.1
  · rw [dite_eq_left hy, Pi.single_apply]
    have he : x = (⟨y.1, ⟨y.2.val + k, hy⟩⟩ : Positions m) ↔
        x.1 = y.1 ∧ x.2.val = y.2.val + k := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rcases x with ⟨i, x⟩
        rcases y with ⟨j, y⟩
        rintro ⟨rfl, hh⟩
        exact congrArg (Sigma.mk i) (Fin.ext hh)
    simp [shiftPower, he]
  · rw [dite_eq_right hy]
    change (if x.1 = y.1 ∧ x.2.val = y.2.val + k then 1 else 0) = 0
    refine ite_eq_right ?_
    rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    rintro ⟨rfl, he⟩
    exact hy (he ▸ x.isLt)

private theorem shift_pow {b : ℕ} (m : Fin b → ℕ+) (k : ℕ) :
    shiftPower m 1 ^ k = shiftPower m k := by
  induction k with
  | zero =>
    ext x y
    change (1 : Matrix (Positions m) (Positions m) ℂ) x y = _
    change _ = ((shiftPower m 0).col y) x
    rw [shiftPower_column]
    simp only [Nat.add_zero, Fin.isLt, dite_eq_left]
    have he : (⟨y.1, ⟨y.2.val, y.2.isLt⟩⟩ : Positions m) = y := by cases y; rfl
    rw [he, one_apply, Pi.single_apply]
  | succ k ih =>
    rw [pow_succ', ih]
    apply Matrix.ext_of_mulVec_single
    intro y
    rw [← mulVec_mulVec, mulVec_single_one, shiftPower_column,
      mulVec_single_one, shiftPower_column]
    by_cases hy : y.2.val + k < m y.1
    · rw [dite_eq_left hy, mulVec_single_one, shiftPower_column]
      simp only [Nat.add_assoc]
    · rw [dite_eq_right hy, mulVec_zero, dite_eq_right (by omega)]

private theorem shift_nilpotent {b p : ℕ} (m : Fin b → ℕ+)
    (hm : ∀ j, (m j : ℕ) ≤ p) : shiftPower m 1 ^ p = 0 := by
  rw [shift_pow]
  apply Matrix.ext_of_mulVec_single
  intro y
  rw [mulVec_single_one, shiftPower_column, dite_eq_right (by have := hm y.1; omega), zero_mulVec]

private theorem shift_gram {b : ℕ} (m : Fin b → ℕ+) (k : ℕ) :
    (shiftPower m k)ᴴ * shiftPower m k =
      diagonal (fun y : Positions m => if y.2.val + k < m y.1 then 1 else 0) := by
  let S := shiftPower m k
  ext x y
  change star (S.col x) ⬝ᵥ S.col y = _
  rw [shiftPower_column, shiftPower_column]
  by_cases hx : x.2.val + k < m x.1 <;> by_cases hy : y.2.val + k < m y.1
  · rw [dite_eq_left hx, dite_eq_left hy]
    have he : (⟨x.1, ⟨x.2.val + k, hx⟩⟩ : Positions m) =
        ⟨y.1, ⟨y.2.val + k, hy⟩⟩ ↔ x = y := by
      constructor
      · intro h
        have hi := congrArg Sigma.fst h
        have hj := congrArg (fun z : Positions m => z.2.val) h
        rcases x with ⟨i, x⟩
        rcases y with ⟨j, y⟩
        dsimp at hi hj
        subst j
        exact congrArg (Sigma.mk i) (Fin.ext (by omega))
      · rintro rfl
        rfl
    simp [Pi.single_apply, he, diagonal_apply, hx, eq_comm]
  · have hxy : x ≠ y := fun h => hy (h ▸ hx)
    simp [hx, hy, hxy]
  · have hxy : x ≠ y := fun h => hx (h ▸ hy)
    simp [hx, hy, hxy]
  · simp [hx, hy, diagonal_apply]

private theorem shift_rank {b : ℕ} (m : Fin b → ℕ+) (k : ℕ) :
    (shiftPower m 1 ^ k).rank = ∑ j, ((m j : ℕ) - k) := by
  classical
  rw [shift_pow, ← rank_conjTranspose_mul_self, shift_gram, rank_diagonal]
  let e : {x : Positions m // x.2.val + k < m x.1} ≃ (Σ j, Fin ((m j : ℕ) - k)) :=
    { toFun := fun x => ⟨x.val.1, ⟨x.val.2.val, by have := x.property; omega⟩⟩
      invFun := fun x =>
        ⟨⟨x.1, ⟨x.2.val, by have := x.2.isLt; omega⟩⟩, by
          change x.2.val + k < m x.1
          have := x.2.isLt
          omega⟩
      left_inv := by rintro ⟨⟨j, x⟩, hx⟩; rfl
      right_inv := by rintro ⟨j, x⟩; rfl }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

private theorem shift_sum_entries {b p : ℕ} (m : Fin b → ℕ+)
    (hm : ∀ j, (m j : ℕ) ≤ p) (x y : Positions m) :
    (∑ k ∈ Finset.range p, shiftPower m 1 ^ k : Matrix (Positions m) (Positions m) ℂ) x y =
      if x.1 = y.1 ∧ y.2.val ≤ x.2.val then 1 else 0 := by
  simp only [shift_pow, Matrix.sum_apply]
  change (∑ k ∈ Finset.range p, if x.1 = y.1 ∧ x.2.val = y.2.val + k then (1 : ℂ) else 0) = _
  by_cases h : x.1 = y.1 ∧ y.2.val ≤ x.2.val
  · rw [ite_eq_left h, Finset.sum_eq_single (x.2.val - y.2.val)]
    · simp [h.1, Nat.add_sub_of_le h.2]
    · intro k _ hk
      exact ite_eq_right (fun hxy => hk (by omega))
    · intro hk
      exfalso
      have := x.2.isLt
      have := hm x.1
      simp only [Finset.mem_range] at hk
      omega
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (fun hh => h ⟨hh.1, by omega⟩)

private theorem block_loss {b p : ℕ} (m : Fin b → ℕ+)
    (hm : ∀ j, (m j : ℕ) ≤ p) :
    let B : Matrix (Positions m) (Positions m) ℂ := ∑ k ∈ Finset.range p, shiftPower m 1 ^ k
    let A := B - 1
    let R : Matrix (Fin b) (Positions m) ℂ := Matrix.of fun i y => if i = y.1 then 1 else 0
    1 + A + Aᴴ = Rᴴ * R ∧ R.rank = b := by
  dsimp only
  let B : Matrix (Positions m) (Positions m) ℂ := ∑ k ∈ Finset.range p, shiftPower m 1 ^ k
  let R : Matrix (Fin b) (Positions m) ℂ := Matrix.of fun i y => if i = y.1 then 1 else 0
  have hR (x y : Positions m) : (Rᴴ * R) x y = if x.1 = y.1 then 1 else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x.1]
    · simp [R, conjTranspose_apply]
    · intro i _ hi
      simp [R, hi, conjTranspose_apply]
    · simp
  constructor
  · ext x y
    change ((1 + (B - 1) + (B - 1)ᴴ : Matrix (Positions m) (Positions m) ℂ)) x y =
      (Rᴴ * R) x y
    simp only [hR, conjTranspose_sub, conjTranspose_one, Matrix.add_apply, Matrix.sub_apply,
      conjTranspose_apply]
    change (1 : Matrix (Positions m) (Positions m) ℂ) x y +
      (B x y - (1 : Matrix (Positions m) (Positions m) ℂ) x y) +
      (star (B y x) - (1 : Matrix (Positions m) (Positions m) ℂ) x y) = _
    dsimp only [B]
    rw [shift_sum_entries m hm x y, shift_sum_entries m hm y x, one_apply]
    by_cases he : x = y
    · subst y
      simp
    · by_cases hb : x.1 = y.1
      · have hv : x.2.val ≠ y.2.val := by
          intro h
          apply he
          rcases x with ⟨i, x⟩
          rcases y with ⟨j, y⟩
          dsimp at hb h
          subst j
          exact congrArg (Sigma.mk i) (Fin.ext h)
        rcases lt_or_gt_of_ne hv with h | h
        · rw [ite_eq_right (show ¬ (x.1 = y.1 ∧ y.2.val ≤ x.2.val) from
              fun hxy => (not_le.mpr h) hxy.2),
            ite_eq_left (show y.1 = x.1 ∧ x.2.val ≤ y.2.val from ⟨hb.symm, h.le⟩),
            ite_eq_right he, ite_eq_left hb]
          simp
        · rw [ite_eq_left (show x.1 = y.1 ∧ y.2.val ≤ x.2.val from ⟨hb, h.le⟩),
            ite_eq_right (show ¬ (y.1 = x.1 ∧ x.2.val ≤ y.2.val) from
              fun hxy => (not_le.mpr h) hxy.2),
            ite_eq_right he, ite_eq_left hb]
          simp
      · simp [he, hb, Ne.symm hb]
  · let e : Fin b → Positions m := fun i => ⟨i, ⟨0, (m i).pos⟩⟩
    have hsub : R.submatrix id e = (1 : Matrix (Fin b) (Fin b) ℂ) := by
      ext i j
      simp [R, e, one_apply, submatrix_apply]
    have hl : b ≤ R.rank := by
      calc b = (R.submatrix id e).rank := by rw [hsub, rank_one, Fintype.card_fin]
        _ ≤ _ := Matrix.rank_submatrix_le _ _ _
    exact hl.antisymm' (by simpa using Matrix.rank_le_card_height R)

private theorem shift_top_norm_lower {b p : ℕ} (m : Fin b → ℕ+)
    (hmax : ∃ j, (m j : ℕ) = p) :
    1 ≤ ‖shiftPower m 1 ^ (p - 1)‖ := by
  obtain ⟨j, hj⟩ := hmax
  let y : Positions m := ⟨j, ⟨0, (m j).pos⟩⟩
  have hk : 0 + (p - 1) < m j := by have := (m j).pos; omega
  let x : Positions m := ⟨j, ⟨0 + (p - 1), hk⟩⟩
  rw [shift_pow]
  have hv : (shiftPower m (p - 1)) *ᵥ Pi.single y 1 = Pi.single x 1 := by
    rw [mulVec_single_one, shiftPower_column, dite_eq_left hk]
  have h := (shiftPower m (p - 1)).l2_opNorm_mulVec (EuclideanSpace.single y 1)
  simpa [hv] using h

private theorem block_witness {b p : ℕ} (m : Fin b → ℕ+) (hp : 2 ≤ p)
    (hm : ∀ j, (m j : ℕ) ≤ p) (hmax : ∃ j, (m j : ℕ) = p)
    (E : ℂ) (hβ : 0 < -2 * E.im) :
    ∃ H : Matrix (Positions m) (Positions m) ℂ,
      (∀ k : ℕ, ((H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ k).rank =
        ∑ j, ((m j : ℕ) - k)) ∧
      (Complex.I • (H - Hᴴ)).PosSemidef ∧
      ‖(H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ (p - 1)‖ =
        (-2 * E.im) ^ (p - 1) ∧ (Complex.I • (H - Hᴴ)).rank = b := by
  let β : ℝ := -2 * E.im
  let c : ℂ := -Complex.I * β
  let S := shiftPower m 1
  let B := ∑ k ∈ Finset.range p, S ^ k
  let A := B - 1
  let H := E • (1 : Matrix (Positions m) (Positions m) ℂ) + c • A
  have hSp : S ^ p = 0 := shift_nilpotent m hm
  have hBInv : B * (1 - S) = 1 := by
    change (∑ k ∈ Finset.range p, S ^ k) * (1 - S) = 1
    rw [geom_sum_mul_neg, hSp, sub_zero]
  have hInvB : (1 - S) * B = 1 := by
    change (1 - S) * (∑ k ∈ Finset.range p, S ^ k) = 1
    rw [mul_neg_geom_sum, hSp, sub_zero]
  have hB : IsUnit B := .of_mul_eq_one _ hBInv
  have hAS : A = S * B := by
    change B - 1 = S * B
    rw [sub_mul, one_mul] at hInvB
    exact (sub_eq_iff_eq_add.mp hInvB).trans (add_comm _ _) |> sub_eq_iff_eq_add.mpr
  have hSB : Commute S B := by
    change S * (∑ k ∈ Finset.range p, S ^ k) = (∑ k ∈ Finset.range p, S ^ k) * S
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => ((Commute.refl S).pow_right k).eq)
  have hAp : A ^ p = 0 := by rw [hAS, hSB.mul_pow, hSp, zero_mul]
  have hβ' : 0 < β := hβ
  have hc : c ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hβ'.ne')
  have hshift : H - E • (1 : Matrix (Positions m) (Positions m) ℂ) = c • A := by
    dsimp only [H]
    abel
  obtain ⟨hG, hR⟩ := block_loss m hm
  have hloss := loss_of_shift (E := E) A
  change Complex.I • (H - Hᴴ) = (β : ℂ) • (1 + A + Aᴴ) at hloss
  rw [hG] at hloss
  have hβnn : (0 : ℂ) ≤ (β : ℂ) := by exact_mod_cast hβ'.le
  have hpsd : (Complex.I • (H - Hᴴ)).PosSemidef := by
    rw [hloss]
    exact (posSemidef_conjTranspose_mul_self _).smul hβnn
  have hN : (H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ p = 0 := by
    rw [hshift, smul_pow, hAp, smul_zero]
  refine ⟨H, ?_, hpsd, ?_, ?_⟩
  · intro k
    rw [hshift, smul_pow, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hc)), hAS, hSB.mul_pow,
      rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp (hB.pow _))]
    exact shift_rank m k
  · refine le_antisymm (shift_estimates H E hp hβ hN hpsd).1 ?_
    have hAnil : IsNilpotent A := ⟨p, hAp⟩
    have hAB : 1 + A = B := by dsimp [A]; abel
    have hBinv : (↑(hAnil.isUnit_one_add.unit⁻¹) : Matrix (Positions m) (Positions m) ℂ) =
        1 - S := by
      apply left_inv_eq_right_inv (a := B)
      · rw [← hAB]
        exact hAnil.isUnit_one_add.val_inv_mul
      · exact hBInv
    have hT :
        A * (↑(hAnil.isUnit_one_add.unit⁻¹) : Matrix (Positions m) (Positions m) ℂ) = S := by
      rw [hBinv, hAS, mul_assoc, hBInv, mul_one]
    have htop := normalized_cayley_top_power A hAnil (by omega) hAp
    rw [hT] at htop
    have hcnorm : ‖c‖ = β := by simp [c, hβ'.le]
    rw [hshift, smul_pow, norm_smul, norm_pow, hcnorm, ← htop]
    exact le_mul_of_one_le_right (pow_nonneg hβ'.le _) (shift_top_norm_lower m hmax)
  · rw [hloss, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (Complex.ofReal_ne_zero.mpr hβ'.ne')),
      rank_conjTranspose_mul_self]
    exact hR

omit [DecidableEq n] in
private theorem rank_zero_eq {M : Matrix n n ℂ} (h : M.rank = 0) : M = 0 := by
  classical
  change Module.finrank ℂ (LinearMap.range M.mulVecLin) = 0 at h
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_zero]
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)

private theorem block_count_of_ranks {ι : Type*} [Fintype ι] (s : ι → ℕ+) (k : ℕ) :
    (∑ i, ((s i : ℕ) - k)) + (∑ i, ((s i : ℕ) - (k + 2))) =
      2 * (∑ i, ((s i : ℕ) - (k + 1))) +
        Fintype.card {i // (s i : ℕ) = k + 1} := by
  classical
  have hcard : Fintype.card {i // (s i : ℕ) = k + 1} =
      ∑ i, if (s i : ℕ) = k + 1 then 1 else 0 := by
    rw [Fintype.card_subtype]
    simp
  rw [hcard, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> omega

private theorem profile_has_chains {b : ℕ} (m : Fin b → ℕ+) (N : Matrix n n ℂ)
    (hN : IsNilpotent N)
    (hprofile : ∀ k : ℕ, (N ^ k).rank = ∑ j, ((m j : ℕ) - k)) :
    ∃ B : Basis (Σ j, Fin (m j)) ℂ (n → ℂ),
      ∀ (k : ℕ) (j : Fin b) (a : Fin (m j)),
        (N ^ k) *ᵥ B ⟨j, a⟩ =
          if h : a.val + k < m j then B ⟨j, ⟨a.val + k, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, hι, s, B, hact, hrank⟩ :=
    NilpotentJordanChains.nilpotent_jordan_chains_rank (Matrix.toLinAlgEquiv' N)
      (hN.map (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)))
  let _ : Fintype ι := hι
  have heq (k : ℕ) : (∑ j, ((m j : ℕ) - k)) = ∑ i, ((s i : ℕ) - k) := by
    rw [← hprofile, ← hrank, ← map_pow]
    rfl
  have hc (k : ℕ) :
      Fintype.card {j // (m j : ℕ) = k + 1} =
        Fintype.card {i // (s i : ℕ) = k + 1} := by
    have h := block_count_of_ranks m k
    have h' := block_count_of_ranks s k
    rw [heq k, heq (k + 1), heq (k + 2)] at h
    omega
  have hfiber (k : ℕ+) :
      Fintype.card {j // m j = k} = Fintype.card {i // s i = k} := by
    have hk : (k : ℕ) - 1 + 1 = (k : ℕ) := by have := k.pos; omega
    simpa only [hk, PNat.coe_inj] using hc ((k : ℕ) - 1)
  let f (k : ℕ+) : {j // m j = k} ≃ {i // s i = k} :=
    Classical.choice (Fintype.card_eq.mp (hfiber k))
  let e : Fin b ≃ ι := Equiv.ofFiberEquiv f
  have he (j : Fin b) : s (e j) = m j := Equiv.ofFiberEquiv_map f j
  let e' : (Σ j, Fin (m j)) ≃ (Σ i, Fin (s i)) :=
    Equiv.sigmaCongr e (fun j => finCongr (congrArg PNat.val (he j).symm))
  refine ⟨B.reindex e'.symm, ?_⟩
  intro k j a
  simp only [Basis.reindex_apply, Equiv.symm_symm]
  change (Matrix.toLinAlgEquiv' (N ^ k)) (B (e' ⟨j, a⟩)) = _
  rw [map_pow]
  have hh := hact k (e j) ((finCongr (congrArg PNat.val (he j).symm)) a)
  change (Matrix.toLinAlgEquiv' N ^ k) (B ⟨e j, finCongr (congrArg PNat.val (he j).symm) a⟩) =
    if h : a.val + k < m j then
      B ⟨e j, finCongr (congrArg PNat.val (he j).symm) ⟨a.val + k, h⟩⟩ else 0
  rw [hh]
  by_cases h : a.val + k < m j
  · have h' : ((finCongr (congrArg PNat.val (he j).symm)) a).val + k < s (e j) := by
      simpa only [finCongr_apply_coe, he] using h
    rw [dite_eq_left h', dite_eq_left h]
    rfl
  · have h' : ¬ ((finCongr (congrArg PNat.val (he j).symm)) a).val + k < s (e j) := by
      simpa only [finCongr_apply_coe, he] using h
    rw [dite_eq_right h', dite_eq_right h]

private theorem nullity_of_profile {b : ℕ} (m : Fin b → ℕ+) (N : Matrix n n ℂ)
    (hprofile : ∀ k : ℕ, (N ^ k).rank = ∑ j, ((m j : ℕ) - k)) :
    Module.finrank ℂ (LinearMap.ker N.mulVecLin) = b := by
  have h0 : Fintype.card n = ∑ j, (m j : ℕ) := by simpa using hprofile 0
  have h1 : N.rank = ∑ j, ((m j : ℕ) - 1) := by simpa using hprofile 1
  have hsum : (∑ j, ((m j : ℕ) - 1)) + b = ∑ j, (m j : ℕ) := by
    have hones : (∑ _ : Fin b, (1 : ℕ)) = b := by simp
    calc
      _ = (∑ j, ((m j : ℕ) - 1)) + ∑ _ : Fin b, (1 : ℕ) :=
        congrArg _ hones.symm
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by have := (m j).pos; omega)
  have hdim := N.mulVecLin.finrank_range_add_finrank_ker
  change N.rank + _ = _ at hdim
  rw [Module.finrank_pi, h0, h1] at hdim
  omega

private theorem nilpotent_order_of_profile {b p : ℕ} (m : Fin b → ℕ+) (N : Matrix n n ℂ)
    (hm : ∀ j, (m j : ℕ) ≤ p) (hmax : ∃ j, (m j : ℕ) = p)
    (hprofile : ∀ k : ℕ, (N ^ k).rank = ∑ j, ((m j : ℕ) - k)) :
    N ^ p = 0 ∧ N ^ (p - 1) ≠ 0 := by
  constructor
  · apply rank_zero_eq
    rw [hprofile]
    exact Finset.sum_eq_zero fun i _ => Nat.sub_eq_zero_of_le (hm i)
  · intro h
    have hz := hprofile (p - 1)
    rw [h, rank_zero] at hz
    obtain ⟨j, hj⟩ := hmax
    have hl : (m j : ℕ) - (p - 1) ≤ ∑ i, ((m i : ℕ) - (p - 1)) :=
      Finset.single_le_sum (f := fun i : Fin b => (m i : ℕ) - (p - 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hpos := (m j).pos
    omega

private theorem chains_have_profile {b : ℕ} (m : Fin b → ℕ+) (N : Matrix n n ℂ)
    (B : Basis (Positions m) ℂ (n → ℂ))
    (hB : ∀ (k : ℕ) (j : Fin b) (a : Fin (m j)),
      (N ^ k) *ᵥ B ⟨j, a⟩ =
        if h : a.val + k < m j then B ⟨j, ⟨a.val + k, h⟩⟩ else 0) :
    ∀ k : ℕ, (N ^ k).rank = ∑ j, ((m j : ℕ) - k) := by
  intro k
  let e := B.equivFun.symm
  have he (a : Positions m) : e (Pi.single a 1) = B a := by
    simp [e, Basis.equivFun_symm_apply]
  have hmaps : (N ^ k).mulVecLin.comp e.toLinearMap =
      e.toLinearMap.comp (shiftPower m k).mulVecLin := by
    apply (Pi.basisFun ℂ (Positions m)).ext
    rintro ⟨j, a⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe,
      Pi.basisFun_apply]
    rw [he, hB, mulVec_single_one, shiftPower_column]
    split
    · exact (he _).symm
    · exact e.map_zero.symm
  change Module.finrank ℂ (LinearMap.range (N ^ k).mulVecLin) = _
  rw [← LinearMap.range_comp_of_range_eq_top (N ^ k).mulVecLin e.range, hmaps, LinearMap.range_comp]
  rw [e.finrank_map_eq]
  change (shiftPower m k).rank = _
  rw [← shift_pow]
  exact shift_rank m k

/-- For every fragmented partition of a whole-space collision with positive linewidth,
the leading Euclidean resolvent coefficient is bounded by the linewidth to the power
of the largest block size minus one. Every admissible loss has rank at least the
number of chains. One passive matrix of the prescribed partition attains both bounds. -/
theorem sharp_passive_fragmented_response {b p : ℕ} (m : Fin b → ℕ+)
    (_hb : 2 ≤ b) (hp : 2 ≤ p) (hm : ∀ j, (m j : ℕ) ≤ p)
    (hmax : ∃ j, (m j : ℕ) = p) (E : ℂ) (hβ : 0 < -2 * E.im) :
    let admissible := fun H : Matrix (Positions m) (Positions m) ℂ =>
      (Complex.I • (H - Hᴴ)).PosSemidef ∧
      ∃ B : Basis (Σ j, Fin (m j)) ℂ (Positions m → ℂ),
        ∀ (k : ℕ) (j : Fin b) (a : Fin (m j)),
          ((H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ k) *ᵥ B ⟨j, a⟩ =
            if h : a.val + k < m j then B ⟨j, ⟨a.val + k, h⟩⟩ else 0
    (∀ H, admissible H →
      let N := H - E • (1 : Matrix (Positions m) (Positions m) ℂ)
      N ^ (p - 1) ≠ 0 ∧
      ‖N ^ (p - 1)‖ ≤ (-2 * E.im) ^ (p - 1) ∧
      b ≤ (Complex.I • (H - Hᴴ)).rank ∧
      (∀ z : ℂ, ¬ IsUnit (z • (1 : Matrix (Positions m) (Positions m) ℂ) - H) ↔ z = E) ∧
      ∀ z : ℂ, z ≠ E → (z • (1 : Matrix (Positions m) (Positions m) ℂ) - H)⁻¹ =
        ∑ k ∈ Finset.range p, ((z - E)⁻¹) ^ (k + 1) • N ^ k) ∧
    (∃ H, admissible H ∧
      ‖(H - E • (1 : Matrix (Positions m) (Positions m) ℂ)) ^ (p - 1)‖ = (-2 * E.im) ^ (p - 1) ∧
      (Complex.I • (H - Hᴴ)).rank = b) := by
  dsimp only
  constructor
  · rintro H ⟨hG, B, hB⟩
    let N := H - E • (1 : Matrix (Positions m) (Positions m) ℂ)
    have hprofile := chains_have_profile m N B hB
    obtain ⟨hNp, hNtop⟩ := nilpotent_order_of_profile m N hm hmax hprofile
    obtain ⟨hnorm, hrank, hres⟩ := passive_response_bound_and_loss_rank H E hp hβ hNp hG
    rw [nullity_of_profile m N hprofile] at hrank
    refine ⟨hNtop, hnorm, hrank, ?_, fun z hz => (hres z hz).2⟩
    intro z
    constructor
    · intro h
      by_contra hz
      exact h (hres z hz).1
    · rintro rfl
      have _ := nontrivial_of_ne _ _ hNtop
      rw [← neg_sub]
      exact (IsNilpotent.neg (show IsNilpotent N from ⟨p, hNp⟩)).not_isUnit
  · obtain ⟨H, hprofile, hG, hnorm, hrank⟩ := block_witness m hp hm hmax E hβ
    let N := H - E • (1 : Matrix (Positions m) (Positions m) ℂ)
    have hNp := (nilpotent_order_of_profile m N hm hmax hprofile).1
    exact ⟨H, ⟨hG, profile_has_chains m N ⟨p, hNp⟩ hprofile⟩, hnorm, hrank⟩


end D5.S1.Eigenstructure.WiersigFragmentedResponse
