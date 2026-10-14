/- GID: D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SteeringEllipsoidCHSH
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CHSH nonlocality is sharply bounded by the steering-ellipsoid centre. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen centre canonical_bound)
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

abbrev TwoQubit := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
def spin (u : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ i, (u i : ℂ) • pauli i
def bell (a a' b b' : Fin 3 → ℝ) : TwoQubit := spin a ⊗ₖ spin (b + b') + spin a' ⊗ₖ spin (b - b')
def chshValues (ρ : TwoQubit) : Set ℝ :=
  {r | ∃ a a' b b' : Fin 3 → ℝ, vlen a = 1 ∧ vlen a' = 1 ∧ vlen b = 1 ∧ vlen b' = 1 ∧
     r = ‖Matrix.trace (ρ * bell a a' b b')‖}
noncomputable def chsh (ρ : TwoQubit) : ℝ := sSup (chshValues ρ)
def bound (t : ℝ) : ℝ := max (2 * Real.sqrt (2 * (1 - t))) 2
def claim : Prop :=
  (∀ ρ : TwoQubit, ρ.PosSemidef → Matrix.trace ρ = 1 → chsh ρ ≤ bound (vlen (centre ρ))) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ ρ : TwoQubit,
     ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ vlen (centre ρ) = t ∧ bound t - ε < chsh ρ)

private lemma unit_coord (u : Fin 3 → ℝ) (hu : vlen u = 1) (i : Fin 3) : |u i| ≤ 1 := by
  have hs : ∑ j, u j ^ 2 = 1 := by
    have he := congrArg (fun r : ℝ => r ^ 2) hu
    rw [vlen, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (u j))] at he
    simpa only [one_pow] using he
  have hi : u i ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)).trans_eq hs
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

private lemma bell_trace_expansion (ρ : TwoQubit) (a a' b b' : Fin 3 → ℝ) :
    trace (ρ * bell a a' b b') = ∑ i, ∑ j,
      ((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
        trace (ρ * (pauli i ⊗ₖ pauli j)) := by
  simp only [bell.eq_def, spin.eq_def, Fin.sum_univ_three, add_kronecker, kronecker_add,
    smul_kronecker, kronecker_smul, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul,
    smul_eq_mul, Pi.add_apply, Pi.sub_apply, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul]
  ring

private lemma chshValues_nonempty (ρ : TwoQubit) : (chshValues ρ).Nonempty := by
  refine ⟨_, ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1], ?_, ?_, ?_, ?_, rfl⟩ <;>
    norm_num [vlen, Fin.sum_univ_succ]

private lemma chshValues_bddAbove (ρ : TwoQubit) : BddAbove (chshValues ρ) := by
  refine ⟨4 * ∑ i, ∑ j, ‖trace (ρ * (pauli i ⊗ₖ pauli j))‖, ?_⟩
  rintro r ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩
  rw [bell_trace_expansion]
  calc
    ‖∑ i, ∑ j, ((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
        trace (ρ * (pauli i ⊗ₖ pauli j))‖
      ≤ ∑ i, ∑ j, ‖((a i * (b j + b' j) + a' i * (b j - b' j) : ℝ) : ℂ) *
          trace (ρ * (pauli i ⊗ₖ pauli j))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, 4 * ‖trace (ρ * (pauli i ⊗ₖ pauli j))‖ := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        |a i * (b j + b' j) + a' i * (b j - b' j)|
          ≤ |a i| * (|b j| + |b' j|) + |a' i| * (|b j| + |b' j|) := by
            calc
              _ ≤ |a i * (b j + b' j)| + |a' i * (b j - b' j)| := abs_add_le _ _
              _ ≤ |a i| * (|b j| + |b' j|) + |a' i| * (|b j| + |b' j|) := by
                rw [abs_mul, abs_mul]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left
                    (by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (b j) (-b' j))
                    (abs_nonneg _))
        _ ≤ 1 * (1 + 1) + 1 * (1 + 1) := by
          gcongr <;> first | exact unit_coord a ha i | exact unit_coord a' ha' i |
            exact unit_coord b hb j | exact unit_coord b' hb' j
        _ = 4 := by norm_num
    _ = _ := by simp only [Finset.mul_sum]

private lemma setting_le_chsh (ρ : TwoQubit) (a a' b b' : Fin 3 → ℝ)
    (ha : vlen a = 1) (ha' : vlen a' = 1) (hb : vlen b = 1) (hb' : vlen b' = 1) :
    ‖trace (ρ * bell a a' b b')‖ ≤ chsh ρ :=
  le_csSup (chshValues_bddAbove ρ) ⟨a, a', b, b', ha, ha', hb, hb', rfl⟩

private def delta (X : TwoQubit) : ℝ :=
  (trace (X * X)).re - (trace (partialTraceRight X * partialTraceRight X)).re

private def filterBob (F : Matrix (Fin 2) (Fin 2) ℂ) (X : TwoQubit) : TwoQubit :=
  ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F) * X *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F)ᴴ

private lemma det_polarization (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (A * B) - trace A * trace B = det A + det B - det (A + B) := by
  simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two,
    Matrix.add_apply]
  ring

private lemma det_polarization_filter (A B F : Matrix (Fin 2) (Fin 2) ℂ) :
    trace ((F * A * Fᴴ) * (F * B * Fᴴ)) - trace (F * A * Fᴴ) * trace (F * B * Fᴴ) =
      (Complex.normSq (det F) : ℂ) * (trace (A * B) - trace A * trace B) := by
  rw [det_polarization, det_polarization,
    ← Matrix.add_mul, ← Matrix.mul_add]
  simp only [det_mul, det_conjTranspose]
  rw [← Complex.mul_conj (det F)]
  change det F * det A * star (det F) + det F * det B * star (det F) -
    det F * det (A + B) * star (det F) =
      (det F * star (det F)) * (det A + det B - det (A + B))
  ring

private def aliceBlock (X : TwoQubit) (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun k l => X (i, k) (j, l)

private lemma delta_filter (X : TwoQubit) (F : Matrix (Fin 2) (Fin 2) ℂ) :
    delta (filterBob F X) = Complex.normSq (det F) * delta X := by
  have hentry (i j : Fin 2) :
      aliceBlock (filterBob F X) i j = F * aliceBlock X i j * Fᴴ := by
    ext k l
    change (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F) * X *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F)ᴴ) (i, k) (j, l) = _
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      conjTranspose_apply, kronecker_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  have hblocks (Y : TwoQubit) :
      trace (Y * Y) - trace (partialTraceRight Y * partialTraceRight Y) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          (trace (aliceBlock Y i j * aliceBlock Y j i) -
            trace (aliceBlock Y i j) * trace (aliceBlock Y j i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, partialTraceRight, aliceBlock.eq_def]
    ring
  change (trace (filterBob F X * filterBob F X)).re -
    (trace (partialTraceRight (filterBob F X) * partialTraceRight (filterBob F X))).re =
      Complex.normSq (det F) *
        ((trace (X * X)).re - (trace (partialTraceRight X * partialTraceRight X)).re)
  rw [← Complex.sub_re, ← Complex.sub_re, hblocks, hblocks X]
  simp only [hentry, det_polarization_filter, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

private lemma sum_sq_le_two_mass {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (L : ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hcap : ∀ i, x i ≤ L) (hL₀ : 1 / 2 ≤ L) :
    ∑ i, x i ^ 2 ≤ L ^ 2 + (1 - L) ^ 2 := by
  classical
  by_cases hsmall : ∀ i, x i ≤ 1 / 2
  · calc
      ∑ i, x i ^ 2 ≤ ∑ i, (1 / 2 : ℝ) * x i :=
        Finset.sum_le_sum fun i _ => by nlinarith [mul_nonneg (hx i) (sub_nonneg.mpr (hsmall i))]
      _ = 1 / 2 := by rw [← Finset.mul_sum, hsum]; ring
      _ ≤ L ^ 2 + (1 - L) ^ 2 := by nlinarith [sq_nonneg (L - 1 / 2)]
  · push Not at hsmall
    obtain ⟨j, hj⟩ := hsmall
    have hrest : ∑ i ∈ Finset.univ.erase j, x i = 1 - x j := by
      have he := Finset.sum_erase_add (s := Finset.univ) x (Finset.mem_univ j)
      rw [hsum] at he
      linarith
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ.erase j) (fun i _ => hx i)
    rw [hrest] at hsq
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (fun i => x i ^ 2)
      (Finset.mem_univ j)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hcap j))
      (show 0 ≤ L + x j - 1 by linarith)]

private lemma bloch_marginals (ρ : TwoQubit) (hρ : ρ.PosSemidef) :
    WithLp.toLp 2 (blochA ρ) =
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceRight ρ) ∧
      WithLp.toLp 2 (blochB ρ) =
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceLeft ρ) := by
  have hR := (partialTraceRight_posSemidef hρ).isHermitian.apply 1 0
  have hL := (partialTraceLeft_posSemidef hρ).isHermitian.apply 1 0
  have hRre := congrArg Complex.re hR
  have hRim := congrArg Complex.im hR
  have hLre := congrArg Complex.re hL
  have hLim := congrArg Complex.im hL
  simp only [partialTraceRight, partialTraceLeft, Fin.sum_univ_two, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im] at hRre hRim hLre hLim
  constructor <;> ext i <;> fin_cases i <;>
    simp [blochA, blochB, pauli,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch,
      Matrix.trace, Matrix.mul_apply, partialTraceRight, partialTraceLeft,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re] <;> linarith

private lemma canonical_delta_le (σ : TwoQubit) (hσ : σ.PosSemidef)
    (hB : partialTraceLeft σ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    delta σ ≤ 1 / 2 - vlen (blochA σ) := by
  have htr : trace σ = 1 := by
    rw [← trace_partialTraceLeft, hB, trace_smul, trace_one]
    norm_num
  have hread := (bloch_marginals σ hσ).1
  have hnorm : vlen (blochA σ) =
      ‖D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch (partialTraceRight σ)‖ := by
    rw [← hread, EuclideanSpace.norm_eq]
    simp only [vlen, Real.norm_eq_abs, sq_abs]
  have hc : vlen (blochA σ) ≤ 1 := by
    rw [hnorm]
    simpa only [trace_partialTraceRight, htr, Complex.one_re] using
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef
        (partialTraceRight σ) (partialTraceRight_posSemidef hσ)
  have hsum : ∑ i, hσ.isHermitian.eigenvalues i = 1 := by
    have ht := congrArg Complex.re htr
    rw [hσ.isHermitian.trace_eq_sum_eigenvalues] at ht
    simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
      Complex.one_re] using ht
  have hcap (i : Fin 2 × Fin 2) : hσ.isHermitian.eigenvalues i ≤ 1 - vlen (blochA σ) / 2 := by
    have hn : (star (⇑(hσ.isHermitian.eigenvectorBasis i)) ⬝ᵥ
        ⇑(hσ.isHermitian.eigenvectorBasis i)).re = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      simp only [inner_self_eq_norm_sq_to_K, hσ.isHermitian.eigenvectorBasis.orthonormal.1 i,
        one_pow, RCLike.ofReal_one, Complex.one_re]
    rw [hσ.isHermitian.eigenvalues_eq]
    change (star (⇑(hσ.isHermitian.eigenvectorBasis i)) ⬝ᵥ
      (σ *ᵥ ⇑(hσ.isHermitian.eigenvectorBasis i))).re ≤ _
    simpa only [hn, mul_one] using
      canonical_bound σ hσ hB (⇑(hσ.isHermitian.eigenvectorBasis i))
  have hsq : (trace (σ * σ)).re = ∑ i, hσ.isHermitian.eigenvalues i ^ 2 := by
    conv_lhs => rw [hσ.isHermitian.spectral_theorem, ← map_mul]
    rw [diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
    simp only [Complex.re_sum, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  have hpurA : (trace (partialTraceRight σ * partialTraceRight σ)).re =
      (1 + vlen (blochA σ) ^ 2) / 2 := by
    rw [hnorm]
    conv_lhs =>
      rw [(D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
        (partialTraceRight σ) (partialTraceRight_posSemidef hσ).isHermitian).1]
    rw [trace_partialTraceRight, htr, Complex.one_re, EuclideanSpace.real_norm_sq_eq]
    simp only [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      ]
    norm_num
    ring
  have hmass := sum_sq_le_two_mass hσ.isHermitian.eigenvalues (1 - vlen (blochA σ) / 2)
    hσ.eigenvalues_nonneg hsum hcap (by linarith)
  change (trace (σ * σ)).re - (trace (partialTraceRight σ * partialTraceRight σ)).re ≤ _
  rw [hsq, hpurA]
  nlinarith

private lemma exists_canonical_filter (ρ : TwoQubit) (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) (hb : vlen (blochB ρ) < 1) :
    ∃ (σ : TwoQubit) (F : Matrix (Fin 2) (Fin 2) ℂ), σ.PosSemidef ∧
      partialTraceLeft σ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      blochA σ = centre ρ ∧ ρ = filterBob F σ ∧
      Complex.normSq (det F) = 1 - vlen (blochB ρ) ^ 2 := by
  set P := partialTraceLeft ρ with hPdef
  have hP : P.PosSemidef := partialTraceLeft_posSemidef hρ
  have htrP : trace P = 1 := by rw [hPdef, trace_partialTraceLeft, htr]
  set p := (P 0 0).re with hpdef
  set r := (P 1 1).re with hrdef
  set q := P 0 1 with hqdef
  have d0 := Complex.le_def.mp (hP.diag_nonneg (i := 0))
  have d1 := Complex.le_def.mp (hP.diag_nonneg (i := 1))
  have hP00 : P 0 0 = (p : ℂ) := Complex.ext rfl (by simpa using d0.2.symm)
  have hP11 : P 1 1 = (r : ℂ) := Complex.ext rfl (by simpa using d1.2.symm)
  have hP10 : P 1 0 = star q := (hP.isHermitian.apply 1 0).symm
  have hpr : p + r = 1 := by
    have ht := congrArg Complex.re htrP
    rw [trace_fin_two, hP00, hP11] at ht
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.one_re] using ht
  have hbP : blochB ρ = ![2 * q.re, -2 * q.im, p - r] := by
    have he := congrArg WithLp.ofLp (bloch_marginals ρ hρ).2
    simpa only [WithLp.ofLp_toLp,
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch] using he
  set d := p * r - Complex.normSq q with hd
  have hlen : vlen (blochB ρ) ^ 2 = 1 - 4 * d := by
    rw [hbP, vlen, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      hd, Complex.normSq_apply]
    nlinarith [sq_nonneg (p + r - 1)]
  have hd0 : 0 < d := by
    have hb0 : 0 ≤ vlen (blochB ρ) := Real.sqrt_nonneg _
    nlinarith
  have hp : 0 < p := by
    have hp0 : 0 ≤ p := d0.1
    rcases eq_or_lt_of_le hp0 with h | h
    · exfalso; rw [hd, ← h, zero_mul] at hd0; linarith [Complex.normSq_nonneg q]
    · exact h
  set u := Real.sqrt d with hudef
  have hu : u * u = d := Real.mul_self_sqrt hd0.le
  have huC : (u : ℂ) * u = d := by exact_mod_cast hu
  have hdC : (d : ℂ) = p * r - q * (starRingEnd ℂ) q := by
    rw [hd, Complex.mul_conj]; push_cast; ring
  have hprC : (p : ℂ) + r = 1 := by exact_mod_cast hpr
  have hPmat : P = !![(p : ℂ), q; star q, (r : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hP00, hP11, hP10, hqdef]
  set H : Matrix (Fin 2) (Fin 2) ℂ := !![(u : ℂ), 0; -star q, (p : ℂ)] with hHdef
  set G : Matrix (Fin 2) (Fin 2) ℂ := !![(p : ℂ), 0; star q, (u : ℂ)] with hGdef
  have H1 : H * P * Hᴴ = ((p * d : ℝ) : ℂ) • 1 := by
    rw [hPmat]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals first | ring1 | linear_combination (p : ℂ) * huC |
      linear_combination (-(p : ℂ)) * hdC
  have H2 : G * H = ((p * u : ℝ) : ℂ) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, hGdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals ring1
  have H4 : Hᴴ * H = (p : ℂ) • (1 - P) := by
    rw [hPmat]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hHdef, Matrix.mul_apply, Fin.sum_univ_two, -mul_eq_mul_left_iff,
        -mul_eq_mul_right_iff, -mul_eq_zero]
    all_goals first | ring1 | linear_combination huC + hdC + (p : ℂ) * hprC |
      linear_combination (p : ℂ) * hprC
  have hbloch : (1 : Matrix (Fin 2) (Fin 2) ℂ) - P =
      (1 / 2 : ℂ) • (1 - ∑ j, (blochB ρ j : ℂ) • pauli j) := by
    rw [hPmat, hbP, Fin.sum_univ_three]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [pauli, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
        Complex.mul_re, Complex.mul_im] <;> linarith
  set c : ℝ := 1 / (2 * p * d) with hcdef
  set X : TwoQubit := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ H with hXdef
  set σ : TwoQubit := (c : ℂ) • (X * ρ * Xᴴ) with hσdef
  have hc0 : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr (by positivity)
  have hσ : σ.PosSemidef := (hρ.mul_mul_conjTranspose_same X).smul hc0
  have hσB : partialTraceLeft σ = (1 / 2 : ℂ) • 1 := by
    have he : partialTraceLeft σ = (c : ℂ) • (H * P * Hᴴ) := by
      rw [hσdef, hXdef, hPdef]
      ext b k; fin_cases b <;> fin_cases k <;>
        simp [partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
          Matrix.conjTranspose_apply] <;> ring
    rw [he, H1, smul_smul]
    congr 1; rw [hcdef]; push_cast; field_simp
  have hσA : blochA σ = centre ρ := by
    rw [centre, if_neg (ne_of_lt hb)]
    funext i
    have ht : trace (σ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) =
        ((1 / (4 * d) : ℝ) : ℂ) * (trace (ρ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) -
          ∑ j, (blochB ρ j : ℂ) * trace (ρ * (pauli i ⊗ₖ pauli j))) := by
      have hk : Xᴴ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X =
          pauli i ⊗ₖ (Hᴴ * H) := by
        rw [hXdef, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
          ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
      have hcy : trace (X * ρ * Xᴴ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) =
          trace (ρ * (pauli i ⊗ₖ (Hᴴ * H))) := by
        rw [Matrix.mul_assoc, trace_mul_cycle, hk, trace_mul_comm]
      have hdistr : pauli i ⊗ₖ (1 - ∑ j, (blochB ρ j : ℂ) • pauli j) =
          pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) -
            ∑ j, (blochB ρ j : ℂ) • (pauli i ⊗ₖ pauli j) := by
        ext k l
        simp [Fin.sum_univ_three, mul_sub, mul_add, mul_comm, mul_left_comm]
      rw [hσdef, Matrix.smul_mul, trace_smul, hcy, H4, hbloch, smul_smul,
        kronecker_smul, Matrix.mul_smul, trace_smul, hdistr, Matrix.mul_sub, trace_sub]
      simp only [Fin.sum_univ_three, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul,
        smul_eq_mul]
      rw [hcdef]; push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hp.ne', Complex.ofReal_ne_zero.mpr hd0.ne']
      ring
    change (trace (σ * (pauli i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))).re = _
    rw [ht, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_sum]
    simp only [Complex.re_ofReal_mul, corr]
    rw [hlen]
    change 1 / (4 * d) * (blochA ρ i - ∑ j, blochB ρ j * corr ρ i j) = _
    simp only [Fin.sum_univ_three]
    field_simp [hd0.ne']
    simp only [corr]
    ring
  set Y : TwoQubit := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G with hYdef
  have hYX : Y * X = ((p * u : ℝ) : ℂ) • 1 := by
    rw [hYdef, hXdef, ← mul_kronecker_mul, Matrix.one_mul, H2, kronecker_smul,
      one_kronecker_one]
  have hT : Y * σ * Yᴴ = ((p / 2 : ℝ) : ℂ) • ρ := by
    have he : Y * σ * Yᴴ = (c : ℂ) • ((Y * X) * ρ * (Y * X)ᴴ) := by
      rw [hσdef, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [he, hYX]
    rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
    congr 1
    rw [hcdef, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    nlinarith [hu]
  set v := Real.sqrt (2 / p) with hvdef
  have hv : v ^ 2 = 2 / p := Real.sq_sqrt (by positivity)
  set F : Matrix (Fin 2) (Fin 2) ℂ := (v : ℂ) • G with hFdef
  have hback : filterBob F σ = ρ := by
    rw [filterBob.eq_def, hFdef, kronecker_smul, ← hYdef, conjTranspose_smul,
      Complex.star_def, Complex.conj_ofReal]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hT, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    norm_cast
    rw [show v * v = v ^ 2 by ring, hv]
    field_simp
    exact one_smul _ _
  have hdet : Complex.normSq (det F) = 4 * d := by
    rw [hFdef, det_smul, hGdef, det_fin_two]
    simp only [Fintype.card_fin, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_mul, sub_zero, ← Complex.ofReal_mul,
      ← Complex.ofReal_pow, Complex.normSq_ofReal]
    calc
      _ = (v ^ 2) ^ 2 * p ^ 2 * (u * u) := by ring
      _ = 4 * d := by rw [hv, hu]; field_simp; ring
  exact ⟨σ, F, hσ, hσB, hσA, hback.symm, hdet.trans (by linarith [hlen])⟩

end D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
