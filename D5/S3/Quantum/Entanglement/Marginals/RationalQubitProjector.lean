/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitProjector
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rational rank-two completions from qubit Bloch coordinates. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Measurement.FourQubitParentConstruction

/-! Hermitian qubit matrices in rational Bloch coordinates. -/

open Matrix Complex
open scoped ComplexConjugate ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment (idempotent_trace_rank)
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Measurement.FourQubitParentConstruction
  (B B_formula_core B_real_smul B_sum trace_B_mul)

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector

private abbrev Qubit := Matrix Bool Bool ℂ
private abbrev Bloch := Fin 3 → ℚ

private abbrev pairing (a b : Bloch) : ℚ := a ⬝ᵥ b

/-- The traceless Hermitian matrix with the specified rational Pauli coefficients. -/
noncomputable def rationalBlochMatrix (a : Fin 3 → ℚ) : Matrix Bool Bool ℂ :=
  (B (WithLp.toLp 2 fun i => (a i : ℝ))).submatrix finTwoEquiv.symm finTwoEquiv.symm

private noncomputable abbrev spin := rationalBlochMatrix

private theorem spin_apply (a : Bloch) (i j : Bool) :
    spin a i j = match i, j with
      | false, false => (a 2 : ℂ)
      | false, true => (a 0 : ℂ) - Complex.I * (a 1 : ℂ)
      | true, false => (a 0 : ℂ) + Complex.I * (a 1 : ℂ)
      | true, true => -(a 2 : ℂ) := by
  cases i <;> cases j <;> simp [spin, rationalBlochMatrix, B_formula_core, finTwoEquiv]

private theorem spin_selfAdjoint (a : Bloch) : (spin a)ᴴ = spin a := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.conjTranspose_apply, spin_apply]; ring

private theorem spin_trace (a : Bloch) : (spin a).trace = 0 := by
  simp [Matrix.trace, spin_apply]

private theorem spin_mul_trace (a b : Bloch) :
    (spin a * spin b).trace = (2 : ℂ) * (pairing a b : ℂ) := by
  unfold spin rationalBlochMatrix
  rw [Matrix.submatrix_mul_equiv _ _ finTwoEquiv.symm finTwoEquiv.symm finTwoEquiv.symm]
  have htrace (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (A.submatrix finTwoEquiv.symm finTwoEquiv.symm).trace = A.trace := by
    simp [Matrix.trace, Fin.sum_univ_two, finTwoEquiv, add_comm]
  rw [htrace, trace_B_mul]
  simp [PiLp.inner_apply, dotProduct, Fin.sum_univ_three, Rat.cast_add, Rat.cast_mul, mul_comm]

private theorem spin_anticomm (a b : Bloch) :
    spin a * spin b + spin b * spin a = ((2 : ℂ) * (pairing a b : ℂ)) • 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, spin_apply, dotProduct, Fin.sum_univ_three, Rat.cast_add,
      Rat.cast_mul] <;> ring_nf <;> simp

private theorem spin_square (a : Bloch) :
    spin a * spin a = (pairing a a : ℂ) • 1 := by
  apply (smul_right_injective (M := Qubit) (by norm_num : (2 : ℂ) ≠ 0))
  simpa only [smul_smul, two_smul] using spin_anticomm a a

private theorem spin_smul (t : ℚ) (a : Bloch) :
    spin (t • a) = (t : ℂ) • spin a := by
  let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => (a i : ℝ)
  have heq : (WithLp.toLp 2 fun i => ((t • a) i : ℝ)) = (t : ℝ) • x := by
    apply (WithLp.equiv 2 _).injective
    funext i
    simp [x, Rat.cast_mul]
  unfold spin rationalBlochMatrix
  rw [heq, B_real_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

private theorem spin_add (a b : Bloch) : spin (a + b) = spin a + spin b := by
  let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => (a i : ℝ)
  let y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => (b i : ℝ)
  have heq : (WithLp.toLp 2 fun i => ((a + b) i : ℝ)) = x + y := by
    apply (WithLp.equiv 2 _).injective
    funext i
    simp [x, y, Rat.cast_add]
  have hadd : B (x + y) = B x + B y := by
    simp [← B_sum (Finset.univ : Finset (Fin 2)) ![x, y], Fin.sum_univ_two]
  unfold spin rationalBlochMatrix
  rw [heq, hadd]
  rfl

private theorem spin_rational (a : Bloch) (i j : Bool) : RationalEntry (spin a i j) := by
  have hq (x : ℚ) : RationalEntry (x : ℂ) := SubfieldClass.ratCast_mem rationalComplex x
  have hi : RationalEntry Complex.I := by
    exact ⟨0, 1, by simp, by simp⟩
  cases i <;> cases j <;> rw [spin_apply]
  · exact hq _
  · exact rationalComplex.sub_mem (hq _) (rationalComplex.mul_mem hi (hq _))
  · exact rationalComplex.add_mem (hq _) (rationalComplex.mul_mem hi (hq _))
  · exact rationalComplex.neg_mem (hq _)

private abbrev Joint := Matrix (Bool × Bool) (Bool × Bool) ℂ

private theorem anti_of_orthogonal {a b : Bloch} (h : pairing a b = 0) :
    spin a * spin b = -(spin b * spin a) :=
  eq_neg_of_add_eq_zero_left (by simpa [h] using spin_anticomm a b)

private theorem kron_neg (A B : Qubit) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext i j
  simp

private theorem neg_kron (A B : Qubit) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j
  simp

private theorem traceRight_kron (A B : Qubit) :
    partialTraceRight (A ⊗ₖ B) = B.trace • A :=
  partialTraceRight_kronecker A B

private theorem traceLeft_kron (A B : Qubit) :
    partialTraceLeft (A ⊗ₖ B) = A.trace • B :=
  partialTraceLeft_kronecker A B

private theorem rational_completion_of_projector_coordinates
    (u v k m : Fin 3 → ℚ) (c : ℚ)
    (hkv : pairing k v = 0) (hum : pairing u m = 0)
    (hunit : pairing k k + pairing u u * pairing v v = 1)
    (hk : 0 < pairing k k)
    (hbound : c ^ 2 * pairing u u + pairing m m / pairing k k < 1) :
    ∃ T : Joint, T.PosSemidef ∧ T.rank = 2 ∧ (∀ i j, RationalEntry (T i j)) ∧
      partialTraceRight T = (1 / 2 : ℂ) • (1 + spin (c • u + m)) ∧
      partialTraceLeft T =
        (1 / 2 : ℂ) • (1 + spin (k + (c * pairing u u) • v)) := by
  let U := spin u
  let V := spin v
  let K := spin k
  let M := spin m
  let d : ℂ := (pairing k k : ℚ)
  let s : ℂ := c
  let F : Joint := (1 : Qubit) ⊗ₖ K + U ⊗ₖ V
  let P : Joint := (1 / 2 : ℂ) • (1 + F)
  let E : Joint := s • (U ⊗ₖ (1 : Qubit)) + d⁻¹ • (M ⊗ₖ K)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast hk.ne'
  have hKU : K * V = -(V * K) := anti_of_orthogonal hkv
  have hUM : U * M = -(M * U) := anti_of_orthogonal hum
  have hFF : F * F = 1 := by
    dsimp only [F]
    simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul, one_mul, mul_one, hKU,
      kron_neg, ← add_assoc, add_neg_cancel_right]
    change (1 : Qubit) ⊗ₖ (spin k * spin k) + (spin u * spin u) ⊗ₖ (spin v * spin v) = 1
    have h := congrArg (fun q : ℚ => (q : ℂ)) hunit
    push_cast at h
    rw [mul_comm] at h
    simp only [spin_square, Matrix.kronecker_smul, Matrix.smul_kronecker,
      Matrix.one_kronecker_one, smul_smul, ← add_smul, h, one_smul]
  have hPP : P * P = P := by
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul,
      mul_one, hFF]
    module
  have hPself : Pᴴ = P := by
    simp [P, F, U, V, K, Matrix.conjTranspose_kronecker, spin_selfAdjoint]
  have hPtrace : P.trace = 2 := by
    norm_num [P, F, U, K, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one,
      Matrix.trace_kronecker, spin_trace, Fintype.card_prod]
  have hFE : F * E = E * F := by
    dsimp only [F, E]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_kronecker_mul, mul_one, one_mul, hKU, hUM, neg_kron, kron_neg]
    abel
  have hPE : P * E = E * P := by
    simp [P, add_mul, mul_add, hFE]
  have hEself : Eᴴ = E := by
    simp [E, s, d, U, M, K, Matrix.conjTranspose_kronecker, spin_selfAdjoint]
  let e : ℚ := c ^ 2 * pairing u u + pairing m m / pairing k k
  have hEE : E * E = (e : ℂ) • 1 := by
    dsimp only [E]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_kronecker_mul, one_mul, mul_one, hUM, neg_kron, smul_neg]
    rw [mul_comm d⁻¹ s]
    simp only [← add_assoc, add_neg_cancel_right]
    simp only [U, M, K, spin_square, Matrix.smul_kronecker, Matrix.kronecker_smul,
      Matrix.one_kronecker_one, smul_smul, ← add_smul]
    congr 1
    push_cast [e]
    dsimp [s, d] at hd ⊢
    field_simp
  have hhalf : 0 ≤ (1 / 2 : ℂ) := by
    norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
  have hIpos : (1 + E).PosSemidef := by
    have hJself : (1 + E)ᴴ = 1 + E := by simp [hEself]
    have hprod := Matrix.posSemidef_conjTranspose_mul_self (1 + E)
    rw [hJself] at hprod
    have hn : 0 ≤ (1 : ℂ) - (e : ℂ) := by
      simp only [Complex.nonneg_iff, Complex.sub_re, Complex.one_re, Complex.ratCast_re,
        Complex.sub_im, Complex.one_im, Complex.ratCast_im, sub_self, and_true]
      exact_mod_cast (sub_nonneg.mpr hbound.le : 0 ≤ (1 : ℚ) - e)
    have hp := hprod.add ((Matrix.PosSemidef.one : (1 : Joint).PosSemidef).smul hn)
    have heq : (1 + E) * (1 + E) + ((1 : ℂ) - (e : ℂ)) • (1 : Joint) =
        (2 : ℂ) • (1 + E) := by
      simp only [add_mul, mul_add, one_mul, mul_one, hEE]
      module
    rw [heq] at hp
    convert hp.smul hhalf using 1
    rw [smul_smul]
    norm_num
  let T : Joint := (1 / 2 : ℂ) • (P * (1 + E))
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · have ht := hIpos.conjTranspose_mul_mul_same P
    rw [hPself, mul_assoc, show (1 + E) * P = P * (1 + E) by simp [mul_add, add_mul, hPE],
      ← mul_assoc, hPP] at ht
    exact ht.smul hhalf
  · have hRank := idempotent_trace_rank P hPP
    rw [hPtrace] at hRank
    have hr : P.rank = 2 := by exact_mod_cast hRank.symm
    rw [← hr]
    apply le_antisymm
    · have hmat : T = P * ((1 / 2 : ℂ) • (1 + E)) := by rw [Matrix.mul_smul]
      rw [hmat]
      exact Matrix.rank_mul_le_left _ _
    · have hfactor : (1 + E) * (1 - E) = (1 - (e : ℂ)) • (1 : Joint) := by
        simp only [add_mul, mul_sub, one_mul, mul_one, hEE]
        module
      have hrecover : T * (1 - E) = ((1 - (e : ℂ)) / 2) • P := by
        rw [show T = (1 / 2 : ℂ) • (P * (1 + E)) from rfl,
          Matrix.smul_mul, mul_assoc, hfactor, Matrix.mul_smul, mul_one, smul_smul]
        congr 1
        ring
      have hne : (1 - (e : ℂ)) / 2 ≠ 0 := by
        exact div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hbound.ne.symm)) (by norm_num)
      calc
        P.rank = (T * (1 - E)).rank := by
          rw [hrecover, Matrix.rank_smul_of_mem_nonZeroDivisors P
            (mem_nonZeroDivisors_of_ne_zero hne)]
        _ ≤ T.rank := Matrix.rank_mul_le_left _ _
  · have hOne {n : Type} [DecidableEq n] (i j : n) :
        RationalEntry ((1 : Matrix n n ℂ) i j) := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h,
        show RationalEntry 0 from rationalComplex.zero_mem,
        show RationalEntry 1 from rationalComplex.one_mem]
    have hc (q : ℚ) : RationalEntry (q : ℂ) := SubfieldClass.ratCast_mem rationalComplex q
    have hHalf : RationalEntry (1 / 2 : ℂ) := by
      simpa using hc (1 / 2)
    have hP (i j : Bool × Bool) : RationalEntry (P i j) :=
      rationalComplex.mul_mem hHalf (rationalComplex.add_mem (hOne i j)
        (rationalComplex.add_mem
          (rationalComplex.mul_mem (hOne i.1 j.1) (spin_rational k i.2 j.2))
          (rationalComplex.mul_mem (spin_rational u i.1 j.1) (spin_rational v i.2 j.2))))
    have hIE (i j : Bool × Bool) : RationalEntry ((1 + E) i j) :=
      rationalComplex.add_mem (hOne i j) (rationalComplex.add_mem
        (rationalComplex.mul_mem (hc c)
          (rationalComplex.mul_mem (spin_rational u i.1 j.1) (hOne i.2 j.2)))
        (rationalComplex.mul_mem (rationalComplex.inv_mem (hc (pairing k k)))
          (rationalComplex.mul_mem (spin_rational m i.1 j.1) (spin_rational k i.2 j.2))))
    intro i j
    have hp : (P * (1 + E)) i j ∈ rationalComplex := by
      rw [Matrix.mul_apply]
      exact rationalComplex.sum_mem fun l _ => rationalComplex.mul_mem (hP i l) (hIE l j)
    exact rationalComplex.mul_mem hHalf hp
  · rw [spin_add, spin_smul]
    have hTraceOne : (1 : Qubit).trace = 2 := by norm_num [Matrix.trace_one]
    have hVKtrace : (spin v * spin k).trace = 0 := by
      rw [Matrix.trace_mul_comm]
      simp [spin_mul_trace, hkv]
    simp only [T, P, F, E, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul,
      mul_one, ← Matrix.mul_kronecker_mul]
    simp only [← Matrix.one_kronecker_one (m := Bool) (n := Bool) (α := ℂ),
      smul_add, ← Matrix.smul_kronecker, partialTraceRight_add, traceRight_kron,
      hTraceOne, hVKtrace, U, V, K, M, spin_trace, spin_square, Matrix.trace_smul,
      smul_smul]
    dsimp only [s]
    rw [show (pairing k k : ℂ) = d from rfl]
    match_scalars <;> field_simp <;> simp [smul_eq_mul, mul_comm]
  · rw [spin_add, spin_smul]
    have hTraceOne : (1 : Qubit).trace = 2 := by norm_num [Matrix.trace_one]
    simp only [T, P, F, E, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, one_mul,
      mul_one, ← Matrix.mul_kronecker_mul]
    simp only [← Matrix.one_kronecker_one (m := Bool) (n := Bool) (α := ℂ),
      smul_add, ← Matrix.smul_kronecker, partialTraceLeft_add, traceLeft_kron, hTraceOne,
      U, V, K, M, spin_trace, spin_mul_trace, Matrix.trace_smul, hum, Rat.cast_zero,
      mul_zero, zero_smul, smul_zero, add_zero, zero_add]
    push_cast
    dsimp only [s]
    module

private theorem pairing_self_nonneg (a : Bloch) : 0 ≤ pairing a a := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]

/-- A rational zero of the quadratic form on the marginal hyperplane supplies
a rational positive semidefinite rank-two completion of the two Bloch marginals. -/
theorem rational_rank_two_of_quadratic_witness (a b y v : Fin 3 → ℚ)
    (hordered : a ⬝ᵥ a < b ⬝ᵥ b) (hy : 0 < y ⬝ᵥ y)
    (hlinear : a ⬝ᵥ y = b ⬝ᵥ v)
    (hquad : y ⬝ᵥ y = (1 - b ⬝ᵥ b) * (v ⬝ᵥ v) + (b ⬝ᵥ v) ^ 2) :
    ∃ T : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      T.PosSemidef ∧ T.rank = 2 ∧ (∀ i j, RationalEntry (T i j)) ∧
      partialTraceRight T = (1 / 2 : ℂ) • (1 + rationalBlochMatrix a) ∧
      partialTraceLeft T = (1 / 2 : ℂ) • (1 + rationalBlochMatrix b) := by
  have hv : 0 < v ⬝ᵥ v := by
    refine lt_of_le_of_ne (pairing_self_nonneg v) ?_
    intro hz
    obtain rfl := dotProduct_self_eq_zero.mp hz.symm
    have hyzero : y ⬝ᵥ y = 0 := by
      simpa only [dotProduct_zero, zero_dotProduct, mul_zero, zero_pow (by decide : 2 ≠ 0),
        add_zero] using hquad
    exact hy.ne' hyzero
  let u := (pairing v v)⁻¹ • y
  let g := pairing a u
  let c := g / pairing u u
  let m := a - c • u
  let k := b - g • v
  have hu : 0 < pairing u u := by
    change 0 < ((pairing v v)⁻¹ • y) ⬝ᵥ ((pairing v v)⁻¹ • y)
    rw [smul_dotProduct, dotProduct_smul]
    exact mul_pos (inv_pos.mpr hv) (mul_pos (inv_pos.mpr hv) hy)
  have hg : g = pairing b v / pairing v v := by
    change a ⬝ᵥ ((pairing v v)⁻¹ • y) = pairing b v / pairing v v
    rw [dotProduct_smul, smul_eq_mul, hlinear, div_eq_mul_inv, mul_comm]
  have hgv : g * pairing v v = pairing b v := (eq_div_iff hv.ne').mp hg
  have hcu : c * pairing u u = g := div_mul_cancel₀ g hu.ne'
  have hkv : pairing k v = 0 := by
    change (b - g • v) ⬝ᵥ v = 0
    rw [sub_dotProduct, smul_dotProduct, show g • (v ⬝ᵥ v) = g * pairing v v from rfl, hgv]
    exact sub_self _
  have hum : pairing u m = 0 := by
    change u ⬝ᵥ (a - c • u) = 0
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm u a,
      show c • (u ⬝ᵥ u) = c * pairing u u from rfl, hcu]
    exact sub_self _
  have hb : k + g • v = b := sub_add_cancel _ _
  have ha : c • u + m = a := add_sub_cancel _ _
  have hb_length : pairing b b = pairing k k + g ^ 2 * pairing v v := by
    calc
      pairing b b = pairing (k + g • v) (k + g • v) := by rw [hb]
      _ = _ := by
        simp only [pairing, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          hkv, dotProduct_comm v k, smul_eq_mul]
        ring
  have ha_length : pairing a a = c ^ 2 * pairing u u + pairing m m := by
    calc
      pairing a a = pairing (c • u + m) (c • u + m) := by rw [ha]
      _ = _ := by
        simp only [pairing, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          hum, dotProduct_comm m u, smul_eq_mul]
        ring
  have hv_length : pairing u u * pairing v v =
      (1 - pairing b b) + g ^ 2 * pairing v v := by
    calc
      pairing u u * pairing v v = pairing y y / pairing v v := by
        dsimp only [pairing, u]
        rw [smul_dotProduct, dotProduct_smul]
        simp only [smul_eq_mul]
        field_simp
      _ = _ := by
        rw [show pairing y y = (1 - pairing b b) * pairing v v + pairing b v ^ 2 from hquad, hg]
        field_simp
        <;> ring
  have hunit : pairing k k + pairing u u * pairing v v = 1 := by
    linarith only [hb_length, hv_length]
  have hlength : g ^ 2 * pairing v v = (c ^ 2 * pairing u u) * (1 - pairing k k) := by
    rw [show 1 - pairing k k = pairing u u * pairing v v by linarith only [hunit], ← hcu]
    ring
  have hk : 0 < pairing k k := by
    have h := pairing_self_nonneg k
    by_contra! hnot
    have hzero : pairing k k = 0 := le_antisymm hnot h
    rw [hzero] at hb_length hlength
    linarith only [show pairing a a < pairing b b from hordered, ha_length, hb_length,
      hlength, pairing_self_nonneg m]
  have hbound : c ^ 2 * pairing u u + pairing m m / pairing k k < 1 := by
    rw [← lt_sub_iff_add_lt', div_lt_iff₀ hk]
    nlinarith only [show pairing a a < pairing b b from hordered, ha_length, hb_length, hlength]
  obtain ⟨T, hT, hRank, hQ, hR, hL⟩ :=
    rational_completion_of_projector_coordinates u v k m c hkv hum hunit hk hbound
  rw [ha] at hR
  rw [hcu, hb] at hL
  exact ⟨T, hT, hRank, hQ, hR, hL⟩

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
