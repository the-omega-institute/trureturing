/- GID: D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Biased post-processed interferometric improvements fail faithfulness. -/

import D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
import D5.S3.Quantum.Algebra.Unitary.BalancedUnitarySum
import D5.S3.Quantum.Schatten.TraceNorm

/-! Biased interferometric priors cannot detect all coherence-creating channels. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue (IsChannel)
open D5.S3.Quantum.Algebra.Unitary.BalancedUnitarySum (halfIdentity)
open D5.S3.Quantum.FiniteDimensional (qubitX)
open D5.S3.Quantum.Schatten.TraceNorm (traceNormUINorm)

namespace D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful

/-- Full dephasing in the coordinate basis, as a complex linear map. -/
def dephase {n : ℕ} : MatrixMap (Fin n) (Fin n) ℂ :=
  (Matrix.diagonalLinearMap (Fin n) ℂ ℂ).comp (Matrix.diagLinearMap (Fin n) ℂ ℂ)

/-- Maximally incoherent operations preserve the diagonal matrices. -/
def IsMIO {a b : ℕ} (ψ : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  IsChannel ψ ∧ ∀ x, ψ (dephase x) = dephase (ψ (dephase x))

private def phaseUnitary {m : ℕ} (φ : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun i => Complex.exp ((φ i : ℂ) * Complex.I))

/-- The interferometer's fixed diagonal unitary conjugation. -/
def phaseChannel {m : ℕ} (φ : Fin m → ℝ) : MatrixMap (Fin m) (Fin m) ℂ :=
  MatrixMap.conj (phaseUnitary φ)

/-- The induced trace norm uses the full complex matrix unit ball. -/
def inducedTraceNorm {a b : ℕ} (f : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x, traceNorm x ≤ 1 ∧ traceNorm (f x) = r}

/-- The optimized post-processed improvement with prior `l` and phases `φ`. -/
def postImprovement {a b m : ℕ} (l : ℝ) (φ : Fin m → ℝ)
    (θ : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ψ : MatrixMap (Fin b) (Fin m) ℂ, IsMIO ψ ∧
    inducedTraceNorm ((((l : ℂ) • LinearMap.id -
      ((1 - l : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp (θ.comp dephase)) = r} -
    |l - (1 - l)|

private def prepare {a b : ℕ} (ρ : Matrix (Fin b) (Fin b) ℂ) :
    MatrixMap (Fin a) (Fin b) ℂ :=
  (Matrix.traceLinearMap (Fin a) ℂ ℂ).smulRight ρ

private def rho (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, (t : ℂ) / 2; (t : ℂ) / 2, 1 / 2]

private def halfPauli : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℝ) • qubitX

private theorem phase_properties {m : ℕ} (φ : Fin m → ℝ) :
    (∀ a, (phaseChannel φ a).trace = a.trace) ∧
    (∀ a, a.PosSemidef → (phaseChannel φ a).PosSemidef) ∧
    (∀ a, dephase a = a → phaseChannel φ a = a) := by
  have hunit (i : Fin m) :
      Complex.exp ((φ i : ℂ) * Complex.I) *
        star (Complex.exp ((φ i : ℂ) * Complex.I)) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj]
    rw [Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hentry (a : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
      phaseChannel φ a i j = Complex.exp ((φ i : ℂ) * Complex.I) * a i j *
        star (Complex.exp ((φ j : ℂ) * Complex.I)) := by
    change (phaseUnitary φ * a * (phaseUnitary φ)ᴴ) i j = _
    rw [phaseUnitary, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change (∑ i, phaseChannel φ a i i) = ∑ i, a i i
    apply Finset.sum_congr rfl
    intro i _
    rw [hentry, mul_right_comm, hunit, one_mul]
  · intro a ha
    exact ha.mul_mul_conjTranspose_same (phaseUnitary φ)
  · intro a ha
    ext i j
    rw [hentry]
    by_cases hij : i = j
    · subst j
      rw [mul_right_comm, hunit, one_mul]
    · have hz : a i j = 0 := by
        have he := congrFun (congrFun ha i) j
        change diagonal (diag a) i j = a i j at he
        rw [diagonal_apply_ne _ hij] at he
        exact he.symm
      rw [hz, mul_zero, zero_mul]

private theorem sandwich {m : ℕ} (l : ℝ) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (φ : Fin m → ℝ) (d e : Matrix (Fin m) (Fin m) ℂ)
    (hd : dephase d = d) (hp : (d + e).PosSemidef) (hn : (d - e).PosSemidef) :
    (d + (l • e - (1 - l) • phaseChannel φ e)).PosSemidef ∧
    (d - (l • e - (1 - l) • phaseChannel φ e)).PosSemidef := by
  obtain ⟨_, hpos, hfix⟩ := phase_properties φ
  have hfixd := hfix d hd
  constructor
  · have h := (hp.smul hl).add ((hpos _ hn).smul (sub_nonneg.mpr hl1))
    convert h using 1
    rw [map_sub, hfixd]
    module
  · have h := (hn.smul hl).add ((hpos _ hp).smul (sub_nonneg.mpr hl1))
    convert h using 1
    rw [map_add, hfixd]
    module

private theorem biased_norm {m : ℕ} (l t : ℝ) (φ : Fin m → ℝ)
    (d e : Matrix (Fin m) (Fin m) ℂ) (hd : d.PosSemidef) (htrd : d.trace = 1)
    (htre : e.trace = 0) (ht : 0 ≤ t) (htδ : t ≤ |2 * l - 1|)
    (hs : (d + (l • e - (1 - l) • phaseChannel φ e)).PosSemidef ∧
      (d - (l • e - (1 - l) • phaseChannel φ e)).PosSemidef) :
    traceNorm ((2 * l - 1) • d + t • (l • e - (1 - l) • phaseChannel φ e)) =
      |2 * l - 1| := by
  have hphase := (phase_properties φ).1 e
  let f := l • e - (1 - l) • phaseChannel φ e
  have htrf : f.trace = 0 := by
    dsimp only [f]
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, htre, hphase, htre]
    simp only [smul_zero, sub_zero]
  have htr : (((2 * l - 1) • d + t • f).trace).re = 2 * l - 1 := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htrd, htrf]
    simp [Complex.real_smul]
  by_cases hc : 0 ≤ 2 * l - 1
  · have hct : 0 ≤ (2 * l - 1) - t := by
      rw [abs_of_nonneg hc] at htδ
      linarith
    have hpos := (hd.smul hct).add (hs.1.smul ht)
    have heq : (2 * l - 1) • d + t • f =
        (2 * l - 1 - t) • d + t • (d + f) := by module
    have hn : traceNorm ((2 * l - 1) • d + t • f) =
        (((2 * l - 1) • d + t • f).trace).re := by
      simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
        congrArg Complex.re (traceNorm_of_posSemidef (heq.symm ▸ hpos))
    exact hn.trans (htr.trans (abs_of_nonneg hc).symm)
  · have hc : 2 * l - 1 ≤ 0 := le_of_not_ge hc
    have hct : 0 ≤ -(2 * l - 1) - t := by
      rw [abs_of_nonpos hc] at htδ
      linarith
    have hpos := (hd.smul hct).add (hs.2.smul ht)
    have heq : -((2 * l - 1) • d + t • f) =
        (-(2 * l - 1) - t) • d + t • (d - f) := by module
    have hn : traceNorm (-((2 * l - 1) • d + t • f)) =
        (-((2 * l - 1) • d + t • f)).trace.re := by
      simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
        congrArg Complex.re (traceNorm_of_posSemidef (heq.symm ▸ hpos))
    rw [traceNorm_neg, Matrix.trace_neg, Complex.neg_re, htr] at hn
    exact hn.trans (abs_of_nonpos hc).symm

private theorem qubit_positive (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (halfIdentity + s • halfPauli).PosSemidef := by
  delta halfIdentity halfPauli qubitX
  have h := (Matrix.posSemidef_vecMulVec_self_star (![1, (s : ℂ)] : Fin 2 → ℂ)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rcases hs with rfl | rfl <;> fin_cases i <;> fin_cases j <;> norm_num

private theorem prepare_channel {a b : ℕ} (ρ : Matrix (Fin b) (Fin b) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) : IsChannel (prepare (a := a) ρ) := by
  constructor
  · apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
    have he : (prepare (a := a) ρ).choi_matrix =
        Matrix.kroneckerMap (· * ·) ρ (1 : Matrix (Fin a) (Fin a) ℂ) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      change (Matrix.single j l (1 : ℂ)).trace * ρ i k = _
      rw [Matrix.kroneckerMap_apply]
      by_cases hjl : j = l
      · subst l
        rw [Matrix.trace_single_eq_same, Matrix.one_apply_eq, one_mul, mul_one]
      · rw [Matrix.trace_single_eq_of_ne _ _ _ hjl, Matrix.one_apply_ne hjl,
          zero_mul, mul_zero]
    rw [he]
    exact hρ.kronecker Matrix.PosSemidef.one
  · intro x
    change (x.trace • ρ).trace = x.trace
    rw [Matrix.trace_smul, htr, smul_eq_mul, mul_one]

private theorem postprocessing_data {m : ℕ} (ψ : MatrixMap (Fin 2) (Fin m) ℂ)
    (hψ : IsMIO ψ) :
    dephase (ψ halfIdentity) = ψ halfIdentity ∧ (ψ halfIdentity).PosSemidef ∧
      (ψ halfIdentity).trace = 1 ∧ (ψ halfPauli).trace = 0 ∧
      (ψ halfIdentity + ψ halfPauli).PosSemidef ∧
      (ψ halfIdentity - ψ halfPauli).PosSemidef := by
  have hid : dephase (halfIdentity (n := Fin 2)) = halfIdentity := by
    change diagonal (diag ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = _
    rw [Matrix.diag_smul, Matrix.diag_one, Matrix.diagonal_smul, Matrix.diagonal_one']
    rfl
  have hpos (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a.PosSemidef) : (ψ a).PosSemidef := by
    exact hψ.1.1.IsPositive ha
  refine ⟨?_, hpos _ ?_,
    ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun x => dephase (ψ x)) hid).symm.trans
      ((hψ.2 halfIdentity).symm.trans (congrArg ψ hid))
  · exact Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1 / 2 by
      norm_num [Complex.nonneg_iff])
  · rw [hψ.1.2]
    rw [Matrix.trace_fin_two]
    delta halfIdentity
    norm_num
  · rw [hψ.1.2]
    rw [Matrix.trace_fin_two]
    delta halfPauli qubitX
    norm_num
  · rw [← map_add]
    have hp := qubit_positive 1 (Or.inl rfl)
    rw [one_smul] at hp
    exact hpos _ hp
  · rw [← map_sub]
    have hn := qubit_positive (-1) (Or.inr rfl)
    rw [neg_one_smul, ← sub_eq_add_neg] at hn
    exact hpos _ hn

private theorem prepared_channel (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsChannel (prepare (a := 2) (rho t)) := by
  apply prepare_channel
  · have hn := (qubit_positive (-1) (Or.inr rfl)).smul
      (show 0 ≤ (1 - t) / 2 by linarith)
    -- A convex combination of the two Pauli eigenstates has the required coherence.
    have h := ((qubit_positive 1 (Or.inl rfl)).smul
      (show 0 ≤ (1 + t) / 2 by linarith)).add hn
    convert h using 1
    delta rho halfIdentity halfPauli qubitX
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num <;> ring
  · rw [Matrix.trace_fin_two]
    delta rho
    norm_num

private theorem prepared_not_mio (t : ℝ) (ht : t ≠ 0) :
    ¬ IsMIO (prepare (a := 2) (rho t)) := by
  intro h
  have he := congrFun (congrFun (h.2 (Matrix.single 0 0 1)) 0) 1
  have hdiag : dephase (Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.single 0 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hdiag] at he
  change ((Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace • rho t) 0 1 =
    diagonal (diag ((Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace •
      rho t)) (0 : Fin 2) 1 at he
  rw [Matrix.diagonal_apply_ne _ (by decide), Matrix.trace_single_eq_same, one_smul] at he
  have hz : (t : ℂ) = 0 := by
    change (t : ℂ) / 2 = 0 at he
    exact (div_eq_zero_iff).mp he |>.resolve_right (by norm_num)
  exact ht (Complex.ofReal_eq_zero.mp hz)

private theorem trace_bound {a : ℕ} (x : Matrix (Fin a) (Fin a) ℂ) :
    ‖x.trace‖ ≤ traceNorm x := by
  by_cases hz : x.trace = 0
  · rw [hz, norm_zero]
    exact traceNorm_nonneg x
  let c : ℂ := star x.trace / (‖x.trace‖ : ℂ)
  have hne : ‖x.trace‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : ‖c‖ = 1 := by
    dsimp only [c]
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hne]
  have hcstar : c * star c = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hc]
    norm_num
  have hu : diagonal (fun _ : Fin a => c) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change diagonal (fun _ : Fin a => c) * (diagonal (fun _ : Fin a => c))ᴴ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change diagonal (fun _ : Fin a => c * star c) = 1
    rw [hcstar, Matrix.diagonal_one]
  have hmul : diagonal (fun _ : Fin a => c) * x = c • x := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  have hval : c * x.trace = (‖x.trace‖ : ℂ) := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, RCLike.star_def, RCLike.conj_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal]
    field_simp
  have h := (traceNorm_eq_max_re_tr_U x).2 ⟨⟨_, hu⟩, rfl⟩
  change ((diagonal (fun _ : Fin a => c) * x).trace).re ≤ traceNorm x at h
  rw [hmul, Matrix.trace_smul] at h
  change (c * x.trace).re ≤ traceNorm x at h
  rw [hval] at h
  exact h

private theorem norm_prepare {a b : ℕ} (ha : 1 ≤ a)
    (h : Matrix (Fin b) (Fin b) ℂ) :
    inducedTraceNorm (prepare (a := a) h) = traceNorm h := by
  let j : Fin a := ⟨0, ha⟩
  let p : Matrix (Fin a) (Fin a) ℂ := diagonal (fun i => if i = j then 1 else 0)
  have hp : p.PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    split_ifs <;> norm_num)
  have htr : p.trace = 1 := by
    change (diagonal (fun i : Fin a => if i = j then (1 : ℂ) else 0)).trace = 1
    rw [Matrix.trace_diagonal]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hnorm : traceNorm p = 1 := by
    have hv := traceNorm_of_posSemidef hp
    rw [htr] at hv
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.one_re] using
      congrArg Complex.re hv
  have hattain : ∃ x : Matrix (Fin a) (Fin a) ℂ,
      traceNorm x ≤ 1 ∧ traceNorm (prepare h x) = traceNorm h := by
    refine ⟨p, hnorm.le, ?_⟩
    change traceNorm (p.trace • h) = traceNorm h
    rw [htr, one_smul]
  have hbound : ∀ r ∈ {r : ℝ | ∃ x, traceNorm x ≤ 1 ∧
      traceNorm (prepare (a := a) h x) = r}, r ≤ traceNorm h := by
    rintro r ⟨x, hx, rfl⟩
    change traceNorm (x.trace • h) ≤ traceNorm h
    rw [show traceNorm (x.trace • h) = ‖x.trace‖ * traceNorm h from
      (traceNormUINorm b).smul_eq x.trace h]
    exact mul_le_of_le_one_left (traceNorm_nonneg h) ((trace_bound x).trans hx)
  exact IsGreatest.csSup_eq ⟨hattain, hbound⟩

private theorem postprocessed_norm {m : ℕ} (l : ℝ) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (φ : Fin m → ℝ) (ψ : MatrixMap (Fin 2) (Fin m) ℂ) (hψ : IsMIO ψ) :
    inducedTraceNorm ((((l : ℂ) • LinearMap.id -
      ((1 - l : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp
        ((prepare (a := 2) (rho (|2 * l - 1| / 2))).comp dephase)) =
      |2 * l - 1| := by
  obtain ⟨hdiag, hd, htrd, htre, hp, hn⟩ := postprocessing_data ψ hψ
  have hs := sandwich l hl hl1 φ (ψ halfIdentity) (ψ halfPauli) hdiag hp hn
  have hv := biased_norm l (|2 * l - 1| / 2) φ (ψ halfIdentity) (ψ halfPauli)
    hd htrd htre (by positivity) (by linarith [abs_nonneg (2 * l - 1)]) hs
  let h := (2 * l - 1) • ψ halfIdentity +
    (|2 * l - 1| / 2) • (l • ψ halfPauli - (1 - l) • phaseChannel φ (ψ halfPauli))
  have hr := norm_prepare (a := 2) (by omega) h
  have hρ (t : ℝ) : rho t = halfIdentity + t • halfPauli := by
    delta rho halfIdentity halfPauli qubitX
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num <;> ring
  have hfix : phaseChannel φ (ψ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = ψ 1 := by
    have hf := (phase_properties φ).2.2 _ hdiag
    change phaseChannel φ (ψ ((1 / 2 : ℂ) • 1)) = ψ ((1 / 2 : ℂ) • 1) at hf
    simp only [map_smul] at hf
    exact smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) hf
  have he : (((((l : ℂ) • LinearMap.id - ((1 - l : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp
      ((prepare (a := 2) (rho (|2 * l - 1| / 2))).comp dephase))) =
      prepare (a := 2) h := by
    apply LinearMap.ext
    intro x
    have htrace : (dephase x).trace = x.trace := by
      change (diagonal (diag x)).trace = x.trace
      rw [Matrix.trace_diagonal]
      rfl
    change (l : ℂ) • ψ ((dephase x).trace • rho _) -
      ((1 - l : ℝ) : ℂ) • phaseChannel φ (ψ ((dephase x).trace • rho _)) = x.trace • h
    dsimp only [halfIdentity] at hρ
    dsimp only [h, halfIdentity]
    simp only [htrace, map_smul, hρ, map_add, LinearMap.map_smul_of_tower, hfix]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  rw [he, hr]
  exact hv

private theorem mio_nonempty (m : ℕ) (hm : 1 ≤ m) :
    ∃ ψ : MatrixMap (Fin 2) (Fin m) ℂ, IsMIO ψ := by
  let j : Fin m := ⟨0, hm⟩
  let p : Matrix (Fin m) (Fin m) ℂ := diagonal (fun i => if i = j then 1 else 0)
  have hp : p.PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    split_ifs <;> norm_num)
  have htr : p.trace = 1 := by
    change (diagonal (fun i : Fin m => if i = j then (1 : ℂ) else 0)).trace = 1
    rw [Matrix.trace_diagonal]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine ⟨prepare p, prepare_channel p hp htr, ?_⟩
  intro x
  change (dephase x).trace • p = diagonal (diag ((dephase x).trace • p))
  rw [Matrix.diag_smul]
  change _ = diagonal ((dephase x).trace • diag (diagonal _))
  rw [Matrix.diag_diagonal, Matrix.diagonal_smul]

private theorem improvement_zero {m : ℕ} (hm : 1 ≤ m) (l : ℝ)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (φ : Fin m → ℝ) :
    postImprovement l φ (prepare (a := 2) (rho (|2 * l - 1| / 2))) = 0 := by
  obtain ⟨ψ, hψ⟩ := mio_nonempty m hm
  have hvalue := postprocessed_norm l hl hl1 φ ψ hψ
  have he : {r : ℝ | ∃ ψ : MatrixMap (Fin 2) (Fin m) ℂ, IsMIO ψ ∧
      inducedTraceNorm ((((l : ℂ) • LinearMap.id -
        ((1 - l : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp
          ((prepare (a := 2) (rho (|2 * l - 1| / 2))).comp dephase)) = r} =
      {|2 * l - 1|} := by
    ext r
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact postprocessed_norm l hl hl1 φ χ hχ
    · intro hr
      exact ⟨ψ, hψ, hvalue.trans (Set.mem_singleton_iff.mp hr).symm⟩
  change sSup _ - |l - (1 - l)| = 0
  rw [he, csSup_singleton]
  have hδ : l - (1 - l) = 2 * l - 1 := by ring
  rw [hδ, sub_self]

/-- Every biased prior admits a coherent qubit channel with zero optimized improvement. -/
theorem result (l : ℝ) (hl : 0 ≤ l) (hl1 : l ≤ 1) (hbiased : l ≠ 1 / 2)
    (m : ℕ) (hm : 1 ≤ m) (φ : Fin m → ℝ) :
    ∃ θ : MatrixMap (Fin 2) (Fin 2) ℂ,
      IsChannel θ ∧ ¬ IsMIO θ ∧ postImprovement l φ θ = 0 := by
  have hδ : |2 * l - 1| ≠ 0 := by
    intro h
    have := abs_eq_zero.mp h
    apply hbiased
    linarith
  refine ⟨prepare (rho (|2 * l - 1| / 2)),
    prepared_channel _ (by positivity) ?_, prepared_not_mio _ ?_,
    improvement_zero hm l hl hl1 φ⟩
  · have hbound : |2 * l - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · exact div_ne_zero hδ (by norm_num)

end D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
