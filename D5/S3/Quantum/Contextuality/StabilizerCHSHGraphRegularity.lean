/- GID: D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The qudit CHSH stabilizer-projector orthogonality graph has degree (2p-1)(p-1). -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Observer.WindowRegister

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix Kronecker

/-! The normalized spectral-projector model for the qudit CHSH graph. -/

namespace D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity

noncomputable section

/-- The primitive phase used by the qudit Weyl operators. -/
def omega (p : ℕ) : ℂ := D5.S3.Observer.WindowRegister.windowRoot p

/-- The cyclic shift matrix, with `shiftX p |x⟩ = |x+1⟩`. -/
def shiftX (p : ℕ) [Fact p.Prime] : Matrix (ZMod p) (ZMod p) ℂ :=
  D5.S3.Observer.WindowRegister.shiftMatrix p

/-- The clock matrix, with `clockZ p |x⟩ = omega p ^ x |x⟩`. -/
def clockZ (p : ℕ) [Fact p.Prime] : Matrix (ZMod p) (ZMod p) ℂ :=
  D5.S3.Observer.WindowRegister.clockMatrix p

/-- Alice's CHSH measurement operator. -/
def aliceOp (p : ℕ) [Fact p.Prime] (j : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if j = 0 then shiftX p else Complex.I • (shiftX p * clockZ p)
  else
    omega p ^ (j * (j + 1)).val • (shiftX p * clockZ p ^ j.val)

/-- Bob's CHSH measurement operator. -/
def bobOp (p : ℕ) [Fact p.Prime] (k : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if k = 0 then shiftX p else Complex.I • (shiftX p * clockZ p)
  else
    let h : ZMod p := (2 : ZMod p)⁻¹
    omega p ^ (h ^ 2 * (k ^ 2 + 2 * k)).val • (shiftX p * clockZ p ^ (h * k).val)

/-- The normalized spectral projector for an eigenvalue indexed by `a`. -/
def eigenProj (p : ℕ) [Fact p.Prime] (M : Matrix (ZMod p) (ZMod p) ℂ) (a : ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  (p : ℂ)⁻¹ • ∑ m : Fin p,
    omega p ^ (-(m : ZMod p) * a).val • M ^ m.val

/-- The rank-one projector selected by the qudit CHSH decomposition. -/
def vertexProj (p : ℕ) [Fact p.Prime] (v : ZMod p × ZMod p × ZMod p) :
    Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ :=
  eigenProj p (aliceOp p v.1) v.2.2 ⊗ₖ
    eigenProj p (bobOp p v.2.1) (-v.1 * v.2.1 - v.2.2)

/-- The all-prime regularity assertion for the CHSH orthogonality graph. -/
def claim : Prop :=
  ∀ (p : ℕ), ∀ [Fact p.Prime],
    Function.Injective (vertexProj p) ∧
      (∀ v, Matrix.trace (vertexProj p v) = 1 ∧
        vertexProj p v * vertexProj p v = vertexProj p v) ∧
      ∀ v,
        (Finset.univ.filter
          (fun w => w ≠ v ∧ vertexProj p v * vertexProj p w = 0)).card =
          (2 * p - 1) * (p - 1)

private theorem phase_eq (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    omega p ^ t.val = ZMod.stdAddChar t := by
  have h : omega p = ZMod.stdAddChar (1 : ZMod p) := by
    simpa [omega, D5.S3.Observer.WindowRegister.windowRoot] using
      (ZMod.stdAddChar_coe (N := p) (1 : ℤ)).symm
  rw [h, ← AddChar.map_nsmul_eq_pow]
  simp

private theorem phase_add (p : ℕ) [Fact p.Prime] (s t : ZMod p) :
    omega p ^ s.val * omega p ^ t.val = omega p ^ (s + t).val := by
  simp only [phase_eq, AddChar.map_add_eq_mul]

private theorem phase_sum (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ x : ZMod p, omega p ^ (c * x).val) = if c = 0 then (p : ℂ) else 0 := by
  simpa only [phase_eq, mul_comm c, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    (AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar p))

private theorem char_star (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  simpa only [AddChar.inv_apply, starRingEnd_apply] using
    (AddChar.starComp_apply (R := ZMod p) (φ := ZMod.stdAddChar)
      (by rw [ringChar.eq (ZMod p) p]; exact (Fact.out : p.Prime).pos) t)

private theorem char_unit (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ZMod.stdAddChar t * star (ZMod.stdAddChar t) = 1 := by
  rw [char_star, ← AddChar.map_add_eq_mul]
  simp

private theorem char_ne (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ZMod.stdAddChar t ≠ 0 := by
  have h := char_unit p t
  intro ht
  simpa [ht] using h

private def twistedShift (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  fun x y => if x = y + 1 then u x * star (u y) else 0

private theorem twistedShift_pow (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (m : ℕ) (x y : ZMod p) :
    (twistedShift p u ^ m) x y =
      if x = y + (m : ZMod p) then u x * star (u y) else 0 := by
  classical
  induction m generalizing x y with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, add_zero, Matrix.one_apply]
      split_ifs with h
      · subst y; exact (hu x).symm
      · rfl
  | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp only [twistedShift, ih, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true, ite_mul, zero_mul, Nat.cast_succ]
      have he : y + 1 + (m : ZMod p) = y + ((m : ZMod p) + 1) := by ring
      rw [he]
      split_ifs with h
      · have hunit := hu (y + 1)
        calc
          (u x * star (u (y + 1))) * (u (y + 1) * star (u y)) =
              u x * (u (y + 1) * star (u (y + 1))) * star (u y) := by ring
          _ = u x * star (u y) := by rw [hunit]; ring
      · rfl

private theorem sum_fin_cast (p : ℕ) [Fact p.Prime] (f : ZMod p → ℂ) :
    (∑ m : Fin p, f (m.val : ZMod p)) = ∑ m : ZMod p, f m := by
  let e : Fin p ≃ ZMod p :=
    { toFun := fun m => (m.val : ZMod p)
      invFun := fun t => ⟨t.val, t.val_lt⟩
      left_inv := fun m => Fin.ext (ZMod.val_natCast_of_lt m.isLt)
      right_inv := ZMod.natCast_zmod_val }
  exact e.sum_comp f

private theorem twisted_eigenProj (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (a x y : ZMod p) :
    eigenProj p (twistedShift p u) a x y =
      (p : ℂ)⁻¹ * ZMod.stdAddChar (-a * (x - y)) * u x * star (u y) := by
  classical
  simp only [eigenProj, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    twistedShift_pow p u hu, phase_eq]
  have hs :
      (∑ m : Fin p, ZMod.stdAddChar (-(m.val : ZMod p) * a) *
        (if x = y + (m.val : ZMod p) then u x * star (u y) else 0)) =
        ZMod.stdAddChar (-a * (x - y)) * (u x * star (u y)) := by
    simp_rw [mul_ite, mul_zero]
    rw [sum_fin_cast p (fun m => if x = y + m then
      ZMod.stdAddChar (-m * a) * (u x * star (u y)) else 0)]
    have he (m : ZMod p) : x = y + m ↔ m = x - y := by
      constructor <;> intro h <;> linear_combination -h
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 2
    ring
  rw [hs]
  ring

private def pureProj (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  (p : ℂ)⁻¹ • Matrix.vecMulVec u (star u)

private theorem twisted_eigenProj_pure (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (a : ZMod p) :
    eigenProj p (twistedShift p u) a =
      pureProj p (fun x => ZMod.stdAddChar (-a * x) * u x) := by
  ext x y
  rw [twisted_eigenProj p u hu]
  simp only [pureProj, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    star_mul, char_star, smul_eq_mul]
  rw [show -a * (x - y) = -a * x + -(-a * y) by ring,
    AddChar.map_add_eq_mul]
  ring

private theorem pure_trace (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) : Matrix.trace (pureProj p u) = 1 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simp only [pureProj, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct,
    Pi.star_apply, hu, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀ hp]

private theorem pure_idem (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) : pureProj p u * pureProj p u = pureProj p u := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hn : star u ⬝ᵥ u = (p : ℂ) := by
    simp only [dotProduct, Pi.star_apply, mul_comm, hu, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  simp only [pureProj, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, hn, Matrix.vecMulVec_smul, smul_smul]
  congr 1
  field_simp

private theorem pure_trace_mul (p : ℕ) [Fact p.Prime] (u v : ZMod p → ℂ) :
    Matrix.trace (pureProj p u * pureProj p v) =
      (p : ℂ)⁻¹ ^ 2 * (star u ⬝ᵥ v) * (star v ⬝ᵥ u) := by
  simp only [pureProj, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
    Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [dotProduct_comm u]
  ring

private theorem pure_mul_zero (p : ℕ) [Fact p.Prime] (u v : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (hv : ∀ x, v x * star (v x) = 1) :
    pureProj p u * pureProj p v = 0 ↔ star u ⬝ᵥ v = 0 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hun : u ≠ 0 := by
    intro h
    have hx := hu 0
    simp [h] at hx
  have hvn : star v ≠ 0 := by
    intro h
    have hx := hv 0
    have hz := congrFun h 0
    simp only [Pi.star_apply, Pi.zero_apply] at hz
    simp [hz] at hx
  simp only [pureProj, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, smul_eq_zero, inv_eq_zero, hp,
    false_or, Matrix.vecMulVec_eq_zero, hun, hvn, or_false]

private def chirp (p : ℕ) [Fact p.Prime] (j c : ZMod p) (x : ZMod p) : ℂ :=
  ZMod.stdAddChar (c * x + j * (2 : ZMod p)⁻¹ * x * (x - 1))

private theorem chirp_unit (p : ℕ) [Fact p.Prime] (j c x : ZMod p) :
    chirp p j c x * star (chirp p j c x) = 1 := char_unit p _

private theorem clock_pow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    clockZ p ^ n = Matrix.diagonal (fun y => ZMod.stdAddChar ((n : ZMod p) * y)) := by
  rw [clockZ, D5.S3.Observer.WindowRegister.clockMatrix, Matrix.diagonal_pow]
  congr 1
  funext y
  change (omega p ^ y.val) ^ n = _
  rw [phase_eq, ← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul]

private theorem weyl_chirp (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (j c : ZMod p) :
    omega p ^ c.val • (shiftX p * clockZ p ^ j.val) =
      twistedShift p (chirp p j c) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hi : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ htwo
  ext x y
  simp only [clock_pow, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    shiftX, D5.S3.Observer.WindowRegister.shiftMatrix, Matrix.circulant_apply,
    phase_eq, twistedShift, chirp, char_star]
  have he : x - y = 1 ↔ x = y + 1 := sub_eq_iff_eq_add'
  simp only [he]
  split_ifs with h
  · subst x
    simp only [one_mul, ZMod.natCast_zmod_val, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination -(j * y) * hi
  · simp

private theorem char_sum (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (c * x)) = if c = 0 then (p : ℂ) else 0 := by
  simpa only [phase_eq] using phase_sum p c

private theorem quadratic_energy (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (d e : ZMod p) (hd : d ≠ 0) :
    (∑ x : ZMod p, ZMod.stdAddChar (d * x ^ 2 + e * x)) *
      (∑ y : ZMod p, ZMod.stdAddChar (-(d * y ^ 2 + e * y))) = (p : ℂ) := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  calc
    _ = ∑ x : ZMod p, ∑ y : ZMod p,
        ZMod.stdAddChar ((d * x ^ 2 + e * x) - (d * y ^ 2 + e * y)) := by
      simp only [Fintype.sum_mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul]
    _ = ∑ h : ZMod p, ∑ y : ZMod p,
        ZMod.stdAddChar ((2 * d * h) * y + (d * h ^ 2 + e * h)) := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ y : ZMod p, ∑ h : ZMod p,
            ZMod.stdAddChar ((2 * d * h) * y + (d * h ^ 2 + e * h)) := by
          apply Finset.sum_congr rfl
          intro y _
          symm
          apply Fintype.sum_equiv (Equiv.addRight y)
          intro h
          congr 1
          change (2 * d * h) * y + (d * h ^ 2 + e * h) =
            (d * (h + y) ^ 2 + e * (h + y)) - (d * y ^ 2 + e * y)
          ring
        _ = _ := Finset.sum_comm
    _ = ∑ h : ZMod p,
        (∑ y : ZMod p, ZMod.stdAddChar ((2 * d * h) * y)) *
          ZMod.stdAddChar (d * h ^ 2 + e * h) := by
      simp only [AddChar.map_add_eq_mul, Finset.sum_mul]
    _ = _ := by
      simp_rw [char_sum]
      simp [mul_eq_zero, htwo, hd]

private theorem chirp_eigenProj (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (j c a : ZMod p) :
    eigenProj p (omega p ^ c.val • (shiftX p * clockZ p ^ j.val)) a =
      pureProj p (chirp p j (c - a)) := by
  rw [weyl_chirp p hp, twisted_eigenProj_pure p _ (chirp_unit p j c)]
  congr 1
  funext x
  simp only [chirp, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem neighbor_count (p : ℕ) [Fact p.Prime]
    (v : ZMod p × ZMod p × ZMod p) :
    (Finset.univ.filter (fun w : ZMod p × ZMod p × ZMod p =>
      (w.1 = v.1 ∧ w.2.2 ≠ v.2.2) ∨
      (w.2.1 = v.2.1 ∧ -w.1 * w.2.1 - w.2.2 ≠ -v.1 * v.2.1 - v.2.2))).card =
      (2 * p - 1) * (p - 1) := by
  classical
  have hne (j k a : ZMod p) :
      -j * k - a ≠ -v.1 * v.2.1 - v.2.2 ↔
        a ≠ -j * k + v.1 * v.2.1 + v.2.2 := by
    constructor <;> contrapose! <;> intro h <;> linear_combination -h
  simp_rw [hne]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  have hinner (j : ZMod p) :
      (∑ k : ZMod p, ∑ a : ZMod p,
        if (j = v.1 ∧ a ≠ v.2.2) ∨
          (k = v.2.1 ∧ a ≠ -j * k + v.1 * v.2.1 + v.2.2)
        then (1 : ℕ) else 0) =
        if j = v.1 then p * (p - 1) else p - 1 := by
    by_cases hj : j = v.1
    · subst j
      simp only [true_and, ite_true]
      have hcond (k a : ZMod p) :
          ((a ≠ v.2.2) ∨
            (k = v.2.1 ∧ a ≠ -v.1 * k + v.1 * v.2.1 + v.2.2)) ↔
            a ≠ v.2.2 := by
        constructor
        · rintro (h | ⟨rfl, h⟩)
          · exact h
          · simpa only [neg_mul, neg_add_cancel, zero_add] using h
        · exact fun h => Or.inl h
      simp_rw [hcond]
      have hc (b : ZMod p) : (∑ a : ZMod p, if a ≠ b then (1 : ℕ) else 0) = p - 1 := by
        simpa only [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card] using (Finset.card_filter (s := Finset.univ) (p := fun a : ZMod p => a ≠ b)).symm
      simp_rw [hc]
      simp [ZMod.card]
    · simp only [hj, false_and, false_or, ite_false]
      simp_rw [ite_and, Finset.sum_ite_irrel]
      simp only [Finset.sum_const_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      simpa only [ite_not, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card] using (Finset.card_filter (s := Finset.univ)
          (p := fun a : ZMod p => a ≠ -j * v.2.1 + v.1 * v.2.1 + v.2.2)).symm
  simp_rw [hinner]
  rw [Finset.sum_ite]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_singleton, Finset.filter_ne', Finset.card_erase_of_mem,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp := (Fact.out : p.Prime).two_le
  have h : 2 * p - 1 = p + (p - 1) := by omega
  rw [h, add_mul]
  simp

theorem result : claim := by
  sorry

end

end D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
