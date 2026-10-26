/- GID: D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The qudit CHSH stabilizer-projector orthogonality graph has degree (2p-1)(p-1). -/

import D5.S3.Fourier.SparseGeneratorFamily
import D5.S3.Observer.BornReduction
import D5.S3.Observer.MatrixUnitCertificate
import D5.S3.Quantum.PureState.PureStateHandshake

/-! The normalized spectral-projector model for the qudit CHSH graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix Kronecker

open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Observer.WindowRegister (windowRoot shiftMatrix clockMatrix)
open D5.S3.Fourier.SparseGeneratorGapObstruction (char_sum)

namespace D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity

noncomputable section

/-- Alice's CHSH measurement operator. -/
def aliceOp (p : ℕ) [Fact p.Prime] (j : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if j = 0 then shiftMatrix p else Complex.I • (shiftMatrix p * clockMatrix p)
  else
    windowRoot p ^ (j * (j + 1)).val • (shiftMatrix p * clockMatrix p ^ j.val)

/-- Bob's CHSH measurement operator. -/
def bobOp (p : ℕ) [Fact p.Prime] (k : ZMod p) : Matrix (ZMod p) (ZMod p) ℂ :=
  if p = 2 then
    if k = 0 then shiftMatrix p else Complex.I • (shiftMatrix p * clockMatrix p)
  else
    let h : ZMod p := (2 : ZMod p)⁻¹
    windowRoot p ^ (h ^ 2 * (k ^ 2 + 2 * k)).val • (shiftMatrix p * clockMatrix p ^ (h * k).val)

/-- The normalized spectral projector for an eigenvalue indexed by `a`. -/
def eigenProj (p : ℕ) [Fact p.Prime] (M : Matrix (ZMod p) (ZMod p) ℂ) (a : ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  (p : ℂ)⁻¹ • ∑ m : Fin p,
    windowRoot p ^ (-(m : ZMod p) * a).val • M ^ m.val

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

/-- A cyclic shift conjugated by the diagonal matrix of unit phases. -/
private def twistedShift (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  fun x y => if x = y + 1 then u x * star (u y) else 0

/-- Intermediate phases cancel along a translated column. -/
private theorem twistedShift_pow (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (m : ℕ) (x y : ZMod p) :
    (twistedShift p u ^ m) x y =
      if x = y + (m : ZMod p) then u x * star (u y) else 0 := by
  classical
  let U : (Matrix (ZMod p) (ZMod p) ℂ)ˣ :=
    { val := Matrix.diagonal u
      inv := Matrix.diagonal (star u)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
        funext i
        exact hu i
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
        funext i
        exact (mul_comm _ _).trans (hu i) }
  have hconj : twistedShift p u = (U : Matrix (ZMod p) (ZMod p) ℂ) *
      shiftMatrix p * (↑U⁻¹ : Matrix (ZMod p) (ZMod p) ℂ) := by
    ext i j
    change (if i = j + 1 then u i * star (u j) else 0) =
      (Matrix.diagonal u * shiftMatrix p * Matrix.diagonal (star u)) i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
      D5.S3.Observer.WindowRegister.shiftMatrix, Matrix.circulant_apply, sub_eq_iff_eq_add']
    split_ifs <;> simp
  rw [hconj, Units.conj_pow]
  change (Matrix.diagonal u * shiftMatrix p ^ m * Matrix.diagonal (star u)) x y = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
    D5.S3.Observer.MatrixUnitCertificate.shift_matrix_pow_apply, sub_eq_iff_eq_add']
  split_ifs <;> simp

private theorem twisted_eigenProj (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (a x y : ZMod p) :
    eigenProj p (twistedShift p u) a x y =
      (p : ℂ)⁻¹ * ZMod.stdAddChar (-a * (x - y)) * u x * star (u y) := by
  have hphase (t : ZMod p) : windowRoot p ^ t.val = ZMod.stdAddChar t := by
    have hroot : windowRoot p = ZMod.stdAddChar (1 : ZMod p) := by
      simpa [windowRoot] using (ZMod.stdAddChar_coe (N := p) (1 : ℤ)).symm
    rw [hroot, ← AddChar.map_nsmul_eq_pow]
    simp
  classical
  rw [eigenProj.eq_1]
  let T : Matrix (ZMod p) (ZMod p) ℂ := twistedShift p u
  have hT : T = twistedShift p u := rfl
  rw [← hT]
  have hpow (m : Fin p) :
      T ^ m.val = fun i j =>
        if i = j + (m.val : ZMod p) then u i * star (u j) else 0 := by
    rw [hT]
    exact funext (fun i => funext (fun j => twistedShift_pow p u hu m.val i j))
  simp_rw [hpow]
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply]
  simp only [hphase]
  change (p : ℂ)⁻¹ * (∑ m : Fin p,
    ZMod.stdAddChar (-(m.val : ZMod p) * a) *
      (if x = y + (m.val : ZMod p) then u x * star (u y) else 0)) = _
  have hs :
      (∑ m : Fin p, ZMod.stdAddChar (-(m.val : ZMod p) * a) *
        (if x = y + (m.val : ZMod p) then u x * star (u y) else 0)) =
        ZMod.stdAddChar (-a * (x - y)) * (u x * star (u y)) := by
    have hcast (m : Fin p) : (ZMod.finEquiv p).toEquiv m = (m.val : ZMod p) := by
      cases p with
      | zero => exact Fin.elim0 m
      | succ n => exact (ZMod.natCast_zmod_val (n := n + 1) m).symm
    have hsum :
        (∑ m : Fin p, ZMod.stdAddChar (-(m.val : ZMod p) * a) *
          (if x = y + (m.val : ZMod p) then u x * star (u y) else 0)) =
          ∑ m : Fin p, (fun m : ZMod p =>
            ZMod.stdAddChar (-m * a) *
              (if x = y + m then u x * star (u y) else 0))
            ((ZMod.finEquiv p).toEquiv m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hcast m]
    rw [hsum]
    rw [(ZMod.finEquiv p).toEquiv.sum_comp (fun m =>
      ZMod.stdAddChar (-m * a) * (if x = y + m then u x * star (u y) else 0))]
    simp_rw [mul_ite, mul_zero]
    have he (m : ZMod p) : x = y + m ↔ m = x - y := by
      constructor <;> intro h <;> linear_combination -h
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 2
    ring
  rw [hs]
  ring

/-- A phase vector has squared length p; this is its normalized outer product. -/
private def pureProj (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  (p : ℂ)⁻¹ • rankOneDensity u

private theorem twisted_eigenProj_pure (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) (a : ZMod p) :
    eigenProj p (twistedShift p u) a =
      pureProj p (fun x => ZMod.stdAddChar (-a * x) * u x) := by
  have hstar (t : ZMod p) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
    simpa only [AddChar.inv_apply, starRingEnd_apply] using
      (AddChar.starComp_apply (R := ZMod p) (φ := ZMod.stdAddChar)
        (by rw [ringChar.eq (ZMod p) p]; exact (Fact.out : p.Prime).pos) t)
  ext x y
  rw [twisted_eigenProj p u hu]
  rw [pureProj.eq_1]
  simp only [rankOneDensity, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    star_mul, hstar, smul_eq_mul]
  rw [show -a * (x - y) = -a * x + -(-a * y) by ring,
    AddChar.map_add_eq_mul]
  ring

private theorem pure_trace (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) : Matrix.trace (pureProj p u) = 1 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [pureProj.eq_1]
  simp only [rankOneDensity, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct,
    Pi.star_apply, hu, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀ hp]

private theorem pure_idem (p : ℕ) [Fact p.Prime] (u : ZMod p → ℂ)
    (hu : ∀ x, u x * star (u x) = 1) : pureProj p u * pureProj p u = pureProj p u := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hn : star u ⬝ᵥ u = (p : ℂ) := by
    simp only [dotProduct, Pi.star_apply, mul_comm, hu, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  unfold pureProj
  simp only [rankOneDensity, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, hn, Matrix.vecMulVec_smul, smul_smul]
  congr 1
  field_simp

private theorem pure_trace_mul (p : ℕ) [Fact p.Prime] (u v : ZMod p → ℂ) :
    Matrix.trace (pureProj p u * pureProj p v) =
      (p : ℂ)⁻¹ ^ 2 * (star u ⬝ᵥ v) * (star v ⬝ᵥ u) := by
  rw [pureProj.eq_1, pureProj.eq_1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul]
  have hover := D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
    (fun _ : Unit => rankOneDensity u) (rankOneDensity v) () u v rfl rfl
  change Matrix.trace (rankOneDensity v * rankOneDensity u) = _ at hover
  rw [Matrix.trace_mul_comm, ← Complex.normSq_eq_norm_sq] at hover
  rw [hover]
  rw [Matrix.star_dotProduct v u, ← Complex.mul_conj]
  simp only [smul_eq_mul, Complex.star_def]
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
  unfold pureProj
  simp only [rankOneDensity, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, smul_eq_zero, inv_eq_zero, hp,
    false_or, Matrix.vecMulVec_eq_zero, hun, hvn, or_false]

private def chirp (p : ℕ) [Fact p.Prime] (j c : ZMod p) (x : ZMod p) : ℂ :=
  ZMod.stdAddChar (c * x + j * (2 : ZMod p)⁻¹ * x * (x - 1))

/-- The quadratic chirp has successive phase difference c+j*y. -/
private theorem weyl_chirp (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (j c : ZMod p) :
    windowRoot p ^ c.val • (shiftMatrix p * clockMatrix p ^ j.val) =
      twistedShift p (chirp p j c) := by
  have hstar (t : ZMod p) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
    simpa only [AddChar.inv_apply, starRingEnd_apply] using
      (AddChar.starComp_apply (R := ZMod p) (φ := ZMod.stdAddChar)
        (by rw [ringChar.eq (ZMod p) p]; exact (Fact.out : p.Prime).pos) t)
  have hphase (t : ZMod p) : windowRoot p ^ t.val = ZMod.stdAddChar t := by
    have hroot : windowRoot p = ZMod.stdAddChar (1 : ZMod p) := by
      simpa [windowRoot] using (ZMod.stdAddChar_coe (N := p) (1 : ℤ)).symm
    rw [hroot, ← AddChar.map_nsmul_eq_pow]
    simp
  have hclock : clockMatrix p ^ j.val =
      Matrix.diagonal (fun y => ZMod.stdAddChar (j * y)) := by
    rw [D5.S3.Observer.WindowRegister.clockMatrix, Matrix.diagonal_pow]
    congr 1
    funext y
    change (windowRoot p ^ y.val) ^ j.val = _
    rw [hphase, ← AddChar.map_nsmul_eq_pow]
    simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hi : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ htwo
  ext x y
  unfold twistedShift chirp
  simp only [hclock, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    D5.S3.Observer.WindowRegister.shiftMatrix, Matrix.circulant_apply,
    hphase, hstar]
  have he : x - y = 1 ↔ x = y + 1 := sub_eq_iff_eq_add'
  simp only [he]
  split_ifs with h
  · subst x
    simp only [one_mul, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination -(j * y) * hi
  · simp

/-- In the squared quadratic sum, translation leaves a nontrivial linear
character except at the zero shift. -/
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
    eigenProj p (windowRoot p ^ c.val • (shiftMatrix p * clockMatrix p ^ j.val)) a =
      pureProj p (chirp p j (c - a)) := by
  rw [weyl_chirp p hp, twisted_eigenProj_pure p _ (fun x => by
      unfold chirp
      simp only [ZMod.stdAddChar_apply, Complex.star_def, Complex.mul_conj,
      Circle.normSq_coe, Complex.ofReal_one])]
  congr 1
  funext x
  unfold chirp
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem chirp_overlap (p : ℕ) [Fact p.Prime] (j c l d : ZMod p) :
    star (chirp p j c) ⬝ᵥ chirp p l d =
      ∑ x : ZMod p, ZMod.stdAddChar
        (((l - j) * (2 : ZMod p)⁻¹) * x ^ 2 +
          (d - c - (l - j) * (2 : ZMod p)⁻¹) * x) := by
  have hstar (t : ZMod p) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
    simpa only [AddChar.inv_apply, starRingEnd_apply] using
      (AddChar.starComp_apply (R := ZMod p) (φ := ZMod.stdAddChar)
        (by rw [ringChar.eq (ZMod p) p]; exact (Fact.out : p.Prime).pos) t)
  apply Finset.sum_congr rfl
  intro x _
  unfold chirp
  simp only [Pi.star_apply, hstar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem chirp_overlap_energy (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (j c l d : ZMod p) :
    (star (chirp p j c) ⬝ᵥ chirp p l d) *
        (star (chirp p l d) ⬝ᵥ chirp p j c) =
      if j = l then (if c = d then (p : ℂ) ^ 2 else 0) else p := by
  classical
  by_cases hj : j = l
  · subst l
    rw [chirp_overlap, chirp_overlap]
    simp only [sub_self, zero_mul, sub_zero,
      zero_add, char_sum, sub_eq_zero, ite_true]
    by_cases hc : c = d
    · simp [hc]; ring
    · simp [hc, Ne.symm hc]
  · have htwo : (2 : ZMod p) ≠ 0 :=
      Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
    rw [ite_eq_right hj, chirp_overlap, chirp_overlap]
    have hpoly (x : ZMod p) :
        (j - l) * (2 : ZMod p)⁻¹ * x ^ 2 +
            (c - d - (j - l) * (2 : ZMod p)⁻¹) * x =
          -(((l - j) * (2 : ZMod p)⁻¹) * x ^ 2 +
            (d - c - (l - j) * (2 : ZMod p)⁻¹) * x) := by ring
    simp_rw [hpoly]
    exact quadratic_energy p hp _ _ (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hj))
      (inv_ne_zero htwo))

private def aliceVec (p : ℕ) [Fact p.Prime] (j a : ZMod p) : ZMod p → ℂ :=
  if p = 2 then
    fun x => ZMod.stdAddChar (-a * x) * (if j = 0 then 1 else Complex.I ^ x.val)
  else chirp p j (j * (j + 1) - a)

private def bobVec (p : ℕ) [Fact p.Prime] (k b : ZMod p) : ZMod p → ℂ :=
  if p = 2 then aliceVec p k b else
    chirp p ((2 : ZMod p)⁻¹ * k)
      ((2 : ZMod p)⁻¹ ^ 2 * (k ^ 2 + 2 * k) - b)

private theorem alice_unit (p : ℕ) [Fact p.Prime] (j a x : ZMod p) :
    aliceVec p j a x * star (aliceVec p j a x) = 1 := by
  by_cases hp : p = 2
  · subst p
    unfold aliceVec
    rw [if_pos rfl, star_mul]
    have hx : (if j = 0 then 1 else Complex.I ^ x.val) *
        star (if j = 0 then 1 else Complex.I ^ x.val) = 1 := by
      split_ifs
      · simp
      · fin_cases x <;> norm_num [ZMod.val, Complex.star_def]
    calc
      _ = (ZMod.stdAddChar (-a * x) * star (ZMod.stdAddChar (-a * x))) *
          ((if j = 0 then 1 else Complex.I ^ x.val) *
          star (if j = 0 then 1 else Complex.I ^ x.val)) := by ring
      _ = 1 := by
        rw [hx]
        simp only [ZMod.stdAddChar_apply, Complex.star_def, Complex.mul_conj,
          Circle.normSq_coe, Complex.ofReal_one, mul_one]
  · unfold aliceVec
    rw [if_neg hp]
    unfold chirp
    simp only [ZMod.stdAddChar_apply, Complex.star_def, Complex.mul_conj,
      Circle.normSq_coe, Complex.ofReal_one]

private theorem bob_unit (p : ℕ) [Fact p.Prime] (k b x : ZMod p) :
    bobVec p k b x * star (bobVec p k b x) = 1 := by
  by_cases hp : p = 2
  · unfold bobVec
    rw [if_pos hp]
    exact alice_unit p k b x
  · unfold bobVec
    rw [if_neg hp]
    unfold chirp
    simp only [ZMod.stdAddChar_apply, Complex.star_def, Complex.mul_conj,
      Circle.normSq_coe, Complex.ofReal_one]

private theorem alice_pure (p : ℕ) [Fact p.Prime] (j a : ZMod p) :
    eigenProj p (aliceOp p j) a = pureProj p (aliceVec p j a) := by
  have hroot_two : windowRoot 2 = -1 :=
    (D5.S3.Observer.WindowRegister.windowRoot_isPrimitiveRoot 2).eq_neg_one_of_two_right
  classical
  by_cases hp : p = 2
  · subst p
    let u : ZMod 2 → ℂ := fun x => if j = 0 then 1 else Complex.I ^ x.val
    have hu : ∀ x, u x * star (u x) = 1 := by
      intro x
      dsimp [u]
      split_ifs
      · simp
      · fin_cases x <;> norm_num [ZMod.val, Complex.star_def]
    have hm : aliceOp 2 j = twistedShift 2 u := by
      ext x y
      have hcases (z : ZMod 2) : z = 0 ∨ z = 1 :=
        (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
          ∀ z : ZMod 2, z = 0 ∨ z = 1) z
      rcases hcases j with rfl | rfl <;>
        rcases hcases x with rfl | rfl <;>
        rcases hcases y with rfl | rfl
      all_goals unfold aliceOp twistedShift
      all_goals norm_num [shiftMatrix, clockMatrix, u,
          ZMod.val_zero, ZMod.val_one_eq_one_mod,
          show (-1 : ZMod 2) = 1 by rfl, show (2 : ZMod 2) = 0 by rfl,
          Matrix.circulant_apply, Matrix.mul_diagonal, hroot_two]
      all_goals simp [show (-1 : ZMod 2) = 1 by rfl, show (2 : ZMod 2) = 0 by rfl]
    rw [hm, twisted_eigenProj_pure 2 u hu]
    rfl
  · have hop : aliceOp p j =
        windowRoot p ^ (j * (j + 1)).val •
          (shiftMatrix p * clockMatrix p ^ j.val) := by
      rw [aliceOp.eq_1, if_neg hp]
    have hvec : aliceVec p j a = chirp p j (j * (j + 1) - a) := by
      rw [aliceVec.eq_1, if_neg hp]
    rw [hop, hvec]
    exact chirp_eigenProj p hp j (j * (j + 1)) a

private theorem bob_pure (p : ℕ) [Fact p.Prime] (k b : ZMod p) :
    eigenProj p (bobOp p k) b = pureProj p (bobVec p k b) := by
  by_cases hp : p = 2
  · have hop : bobOp p k = aliceOp p k := by
      rw [bobOp.eq_1, aliceOp.eq_1, if_pos hp, if_pos hp]
    have hvec : bobVec p k b = aliceVec p k b := by
      rw [bobVec.eq_1, if_pos hp]
    rw [hop, hvec]
    exact alice_pure p k b
  · have hop : bobOp p k =
        windowRoot p ^ ((2 : ZMod p)⁻¹ ^ 2 * (k ^ 2 + 2 * k)).val •
          (shiftMatrix p * clockMatrix p ^ ((2 : ZMod p)⁻¹ * k).val) := by
      rw [bobOp.eq_1, if_neg hp]
    have hvec : bobVec p k b =
        chirp p ((2 : ZMod p)⁻¹ * k)
          ((2 : ZMod p)⁻¹ ^ 2 * (k ^ 2 + 2 * k) - b) := by
      rw [bobVec.eq_1, if_neg hp]
    rw [hop, hvec]
    exact chirp_eigenProj p hp ((2 : ZMod p)⁻¹ * k)
      ((2 : ZMod p)⁻¹ ^ 2 * (k ^ 2 + 2 * k)) b

/-- Equal settings give orthogonal outcomes; unequal settings are mutually unbiased. -/
private theorem alice_energy (p : ℕ) [Fact p.Prime] (j a l b : ZMod p) :
    (star (aliceVec p j a) ⬝ᵥ aliceVec p l b) *
        (star (aliceVec p l b) ⬝ᵥ aliceVec p j a) =
      if j = l then (if a = b then (p : ℂ) ^ 2 else 0) else p := by
  classical
  have hchar_two (x : ZMod 2) :
      ZMod.stdAddChar x = if x = 0 then (1 : ℂ) else -1 := by
    have hroot_two : windowRoot 2 = -1 :=
      (D5.S3.Observer.WindowRegister.windowRoot_isPrimitiveRoot 2).eq_neg_one_of_two_right
    have hphase (t : ZMod 2) : windowRoot 2 ^ t.val = ZMod.stdAddChar t := by
      have hroot : windowRoot 2 = ZMod.stdAddChar (1 : ZMod 2) := by
        simpa [windowRoot] using (ZMod.stdAddChar_coe (N := 2) (1 : ℤ)).symm
      rw [hroot, ← AddChar.map_nsmul_eq_pow]
      simp
    have hcases : x = 0 ∨ x = 1 :=
      (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
        ∀ x : ZMod 2, x = 0 ∨ x = 1) x
    rcases hcases with rfl | rfl <;>
      norm_num [← hphase, hroot_two, ZMod.val_zero, ZMod.val_one_eq_one_mod]
  by_cases hp : p = 2
  · subst p
    change (∑ x : Fin 2, star (aliceVec 2 j a x) * aliceVec 2 l b x) *
        (∑ x : Fin 2, star (aliceVec 2 l b x) * aliceVec 2 j a x) = _
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    change
      (star (aliceVec 2 j a 0) * aliceVec 2 l b 0 +
        star (aliceVec 2 j a 1) * aliceVec 2 l b 1) *
      (star (aliceVec 2 l b 0) * aliceVec 2 j a 0 +
        star (aliceVec 2 l b 1) * aliceVec 2 j a 1) = _
    have hcases (z : ZMod 2) : z = 0 ∨ z = 1 :=
      (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
        ∀ z : ZMod 2, z = 0 ∨ z = 1) z
    rcases hcases j with rfl | rfl <;>
      rcases hcases a with rfl | rfl <;>
      rcases hcases l with rfl | rfl <;>
      rcases hcases b with rfl | rfl
    all_goals unfold aliceVec
    all_goals norm_num [hchar_two, ZMod.val_zero,
        ZMod.val_one_eq_one_mod, Pi.star_apply, Complex.star_def] <;> ring_nf <;> norm_num
  · have hvec : ∀ (j a : ZMod p), aliceVec p j a = chirp p j (j * (j + 1) - a) := by
      intro j a
      rw [aliceVec.eq_1, if_neg hp]
    rw [hvec j a, hvec l b]
    rw [chirp_overlap_energy p hp]
    by_cases hj : j = l
    · subst l
      simp
    · simp [hj]

private theorem bob_energy (p : ℕ) [Fact p.Prime] (k a l b : ZMod p) :
    (star (bobVec p k a) ⬝ᵥ bobVec p l b) *
        (star (bobVec p l b) ⬝ᵥ bobVec p k a) =
      if k = l then (if a = b then (p : ℂ) ^ 2 else 0) else p := by
  classical
  by_cases hp : p = 2
  · have hvec : ∀ (k b : ZMod p), bobVec p k b = aliceVec p k b := by
      intro k b
      rw [bobVec.eq_1, if_pos hp]
    rw [hvec k a, hvec l b]
    exact alice_energy p k a l b
  · have htwo : (2 : ZMod p) ≠ 0 :=
      Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
    have hvec : ∀ (k b : ZMod p), bobVec p k b =
        chirp p ((2 : ZMod p)⁻¹ * k)
          ((2 : ZMod p)⁻¹ ^ 2 * (k ^ 2 + 2 * k) - b) := by
      intro k b
      rw [bobVec.eq_1, if_neg hp]
    rw [hvec k a, hvec l b]
    rw [chirp_overlap_energy p hp]
    have he : (2 : ZMod p)⁻¹ * k = (2 : ZMod p)⁻¹ * l ↔ k = l :=
      ⟨mul_left_cancel₀ (inv_ne_zero htwo), congrArg ((2 : ZMod p)⁻¹ * ·)⟩
    simp only [he]
    by_cases hk : k = l
    · subst l
      simp
    · simp [hk]

private theorem pure_overlap (p : ℕ) [Fact p.Prime] (u v : ZMod p → ℂ)
    (j a l b : ZMod p) (hu : ∀ x, u x * star (u x) = 1)
    (hv : ∀ x, v x * star (v x) = 1)
    (he : (star u ⬝ᵥ v) * (star v ⬝ᵥ u) =
      if j = l then (if a = b then (p : ℂ) ^ 2 else 0) else p) :
    Matrix.trace (pureProj p u * pureProj p v) =
        (if j = l then (if a = b then 1 else 0) else (p : ℂ)⁻¹) ∧
      (pureProj p u * pureProj p v = 0 ↔ j = l ∧ a ≠ b) := by
  classical
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hz : (star u ⬝ᵥ v) * (star v ⬝ᵥ u) = 0 ↔ star u ⬝ᵥ v = 0 := by
    rw [Matrix.star_dotProduct v u]
    simp only [mul_eq_zero, star_eq_zero, or_self]
  constructor
  · rw [pure_trace_mul, mul_assoc, he]
    by_cases hj : j = l <;> by_cases ha : a = b <;>
      simp [hj, ha] <;> field_simp
  · rw [pure_mul_zero p u v hu hv, ← hz, he]
    by_cases hj : j = l <;> by_cases ha : a = b <;> simp [hj, ha, hp]

private theorem alice_overlap (p : ℕ) [Fact p.Prime] (j a l b : ZMod p) :
    Matrix.trace (eigenProj p (aliceOp p j) a * eigenProj p (aliceOp p l) b) =
        (if j = l then (if a = b then 1 else 0) else (p : ℂ)⁻¹) ∧
      (eigenProj p (aliceOp p j) a * eigenProj p (aliceOp p l) b = 0 ↔
        j = l ∧ a ≠ b) := by
  rw [alice_pure, alice_pure]
  exact pure_overlap p _ _ j a l b (alice_unit p j a) (alice_unit p l b)
    (alice_energy p j a l b)

private theorem bob_overlap (p : ℕ) [Fact p.Prime] (k a l b : ZMod p) :
    Matrix.trace (eigenProj p (bobOp p k) a * eigenProj p (bobOp p l) b) =
        (if k = l then (if a = b then 1 else 0) else (p : ℂ)⁻¹) ∧
      (eigenProj p (bobOp p k) a * eigenProj p (bobOp p l) b = 0 ↔
        k = l ∧ a ≠ b) := by
  rw [bob_pure, bob_pure]
  exact pure_overlap p _ _ k a l b (bob_unit p k a) (bob_unit p l b)
    (bob_energy p k a l b)

/-- Fixing Alice's setting separates the count into p*(p-1) and (p-1)^2. -/
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
          Finset.card_univ, ZMod.card] using
          (Finset.card_filter (s := Finset.univ) (p := fun a : ZMod p => a ≠ b)).symm
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

private theorem kronecker_zero (p : ℕ) [Fact p.Prime]
    (A B : Matrix (ZMod p) (ZMod p) ℂ) :
    A ⊗ₖ B = 0 ↔ A = 0 ∨ B = 0 := by
  have he : A ⊗ₖ B = 0 ↔
      Matrix.vecMulVec (fun ij : ZMod p × ZMod p => A ij.1 ij.2)
        (fun ij : ZMod p × ZMod p => B ij.1 ij.2) = 0 := by
    constructor
    · intro h
      ext ⟨i, j⟩ ⟨k, l⟩
      exact congrFun₂ h (i, k) (j, l)
    · intro h
      ext ⟨i, k⟩ ⟨j, l⟩
      exact congrFun₂ h (i, j) (k, l)
  rw [he, Matrix.vecMulVec_eq_zero]
  simp only [funext_iff, Prod.forall, Pi.zero_apply]
  exact or_congr ⟨Matrix.ext, fun h i j => congrFun₂ h i j⟩
    ⟨Matrix.ext, fun h i j => congrFun₂ h i j⟩

private theorem vertex_laws (p : ℕ) [Fact p.Prime]
    (v : ZMod p × ZMod p × ZMod p) :
    Matrix.trace (vertexProj p v) = 1 ∧ vertexProj p v * vertexProj p v = vertexProj p v := by
  rw [vertexProj.eq_1, alice_pure, bob_pure]
  constructor
  · rw [Matrix.trace_kronecker, pure_trace p _ (alice_unit p _ _),
      pure_trace p _ (bob_unit p _ _), one_mul]
  · rw [← Matrix.mul_kronecker_mul, pure_idem p _ (alice_unit p _ _),
      pure_idem p _ (bob_unit p _ _)]

private theorem vertex_orth (p : ℕ) [Fact p.Prime]
    (v w : ZMod p × ZMod p × ZMod p) :
    vertexProj p v * vertexProj p w = 0 ↔
      (w.1 = v.1 ∧ w.2.2 ≠ v.2.2) ∨
      (w.2.1 = v.2.1 ∧ -w.1 * w.2.1 - w.2.2 ≠ -v.1 * v.2.1 - v.2.2) := by
  rw [vertexProj.eq_1, vertexProj.eq_1, ← Matrix.mul_kronecker_mul, kronecker_zero,
    (alice_overlap p _ _ _ _).2, (bob_overlap p _ _ _ _).2]
  simp only [eq_comm, ne_comm]

private theorem vertex_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (vertexProj p) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpn : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hi : (p : ℂ)⁻¹ ≠ 1 := by
    rw [ne_eq, inv_eq_one]
    exact_mod_cast hp.ne_one
  have hisq : (p : ℂ)⁻¹ * (p : ℂ)⁻¹ ≠ 1 := by
    intro h
    field_simp [hpn] at h
    have hn : 1 = p ^ 2 := by exact_mod_cast h
    nlinarith [hp.two_le]
  intro v w he
  have ht : (1 : ℂ) = Matrix.trace (vertexProj p v * vertexProj p w) := by
    rw [← he, (vertex_laws p v).2, (vertex_laws p v).1]
  rw [vertexProj.eq_1, vertexProj.eq_1, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    (alice_overlap p _ _ _ _).1, (bob_overlap p _ _ _ _).1] at ht
  by_cases hj : v.1 = w.1
  · by_cases ha : v.2.2 = w.2.2
    · by_cases hk : v.2.1 = w.2.1
      · exact Prod.ext hj (Prod.ext hk ha)
      · simp only [ite_eq_left hj, ite_eq_left ha, ite_eq_right hk, one_mul] at ht
        exact (hi ht.symm).elim
    · simp only [ite_eq_left hj, ite_eq_right ha, zero_mul] at ht
      exact (one_ne_zero ht).elim
  · by_cases hk : v.2.1 = w.2.1
    · by_cases hb : -v.1 * v.2.1 - v.2.2 = -w.1 * w.2.1 - w.2.2
      · simp only [ite_eq_right hj, ite_eq_left hk, ite_eq_left hb, mul_one] at ht
        exact (hi ht.symm).elim
      · simp only [ite_eq_right hj, ite_eq_left hk, ite_eq_right hb, mul_zero] at ht
        exact (one_ne_zero ht).elim
    · simp only [ite_eq_right hj, ite_eq_right hk] at ht
      exact (hisq ht.symm).elim

/-- The normalized qudit CHSH projectors give the asserted regular graph for every prime. -/
theorem result : claim := by
  classical
  intro p inst
  refine ⟨vertex_injective p, vertex_laws p, ?_⟩
  intro v
  convert neighbor_count p v using 1
  congr 1
  ext w
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_univ _, (vertex_orth p v w).mp h.2.2⟩
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨?_, (vertex_orth p v w).mpr h.2⟩
    rintro rfl
    simp at h

end

end D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
