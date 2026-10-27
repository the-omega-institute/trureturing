/- GID: D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.claim; result=D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result; claim=D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.claim
   digest: Tensor products need not preserve non-local Schmidt-number annihilation. -/

import D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
import D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation

/-! Two replacements onto a Schmidt-rank-two qutrit state yield Schmidt rank four. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
  (BipartiteOp coeff proj SchmidtNumberLE)

namespace D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation

def NonLocal {d : ℕ} (e : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  ¬ ∃ e₁ e₂ : MatrixMap (Fin d) (Fin d) ℂ,
    IsCPTP e₁ ∧ IsCPTP e₂ ∧ e = MatrixMap.kron e₁ e₂

def IsPEA (d r : ℕ) (e : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsCPTP e ∧ NonLocal e ∧ r < d ∧
    ∀ ρ : BipartiteOp d, ρ.PosSemidef → ρ.trace = 1 → SchmidtNumberLE (e ρ) r

def alignedTensor {d : ℕ}
    (e f : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    MatrixMap (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ :=
  let a := (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin d) (Fin d)).trans
    (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  let t := Matrix.reindexLinearEquiv ℂ ℂ a a
  t.toLinearMap.comp ((MatrixMap.kron e f).comp t.symm.toLinearMap)

def claim : Prop :=
  ∀ (d r : ℕ) (e f : MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ),
    IsPEA d r e → IsPEA d r f → IsPEA (d * d) r (alignedTensor e f)

private def phi : Ket (Fin 3 × Fin 3) :=
  ⟨fun x => if x.1 = x.2 ∧ x.1 < 2 then (1 : ℂ) / (Real.sqrt 2 : ℂ) else 0,
    by
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, norm_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
        Real.sq_sqrt]⟩

private def replacement : MatrixMap (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (Matrix.traceLinearMap (Fin 3 × Fin 3) ℂ ℂ).smulRight (proj phi)

private theorem phi_rank : (coeff phi).rank = 2 := by
  classical
  have hn : (1 : ℂ) / (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
  have he : coeff phi = diagonal ![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ), 0] := by
    rw [phi.eq_1]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [coeff, phi, Matrix.diagonal_apply]
  rw [he, Matrix.rank_diagonal, Fintype.card_subtype]
  norm_num [Fin.card_filter_univ_succ, hn, one_div]

private theorem replacement_cptp : IsCPTP replacement := by
  let k : (Fin 3 × Fin 3) → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun j => vecMulVec phi.vec (Pi.single j 1)
  have he : replacement = MatrixMap.of_kraus k k := by
    rw [replacement.eq_1]
    ext x a b
    change x.trace * ((MState.pure phi).m a b) = _
    rw [MState.pure_apply]
    rw [MatrixMap.of_kraus]
    simp only [LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      k, Matrix.vecMulVec_apply, Pi.single_apply, mul_one, mul_zero,
      apply_ite, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    unfold Matrix.trace
    simp only [Matrix.diag, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change x j j * (phi.vec a * star (phi.vec b)) =
      phi.vec a * x j j * star (phi.vec b)
    ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact MatrixMap.of_kraus_isCompletelyPositive k
  · intro x
    change (x.trace • (MState.pure phi).m).trace = x.trace
    rw [Matrix.trace_smul, MState.tr', smul_eq_mul, mul_one]

private theorem replacement_nonlocal : NonLocal replacement := by
  rintro ⟨e, f, _, _, he⟩
  have hh := congrArg (fun g : MatrixMap (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ =>
    g (Matrix.single (0, 0) (0, 0) 1)) he
  have hp (i j : Fin 3 × Fin 3) :
      (proj phi) i j = e (Matrix.single 0 0 1) i.1 j.1 *
        f (Matrix.single 0 0 1) i.2 j.2 := by
    rcases i with ⟨a, c⟩
    rcases j with ⟨b, d⟩
    have h := congrArg (fun x : BipartiteOp 3 => x (a, c) (b, d)) hh
    rw [MatrixMap.kron_def] at h
    simpa [replacement, LinearMap.smulRight_apply, Matrix.single_apply, ite_and] using h
  have ha := hp (0, 0) (0, 0)
  have hb := hp (1, 1) (1, 1)
  have hz := hp (0, 1) (0, 1)
  change (MState.pure phi).m _ _ = _ at ha hb hz
  rw [MState.pure_apply] at ha hb hz
  norm_num [Ket.apply, phi, Complex.conj_ofReal] at ha hb hz
  have hn : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ ≠ 0 := by
    apply mul_ne_zero <;> positivity
  rcases hz with h | h
  · exact hn (ha.trans (by rw [h, zero_mul]))
  · exact hn (hb.trans (by rw [h, mul_zero]))

private theorem replacement_schmidt (ρ : BipartiteOp 3) (hρ : ρ.trace = 1) :
    SchmidtNumberLE (replacement ρ) 2 := by
  refine ⟨1, fun _ => 1, fun _ => phi, ?_, ?_, ?_, ?_⟩
  · intro k; norm_num
  · simp
  · intro k; exact phi_rank.le
  · simp [replacement, LinearMap.smulRight_apply, hρ]

private theorem replacement_pea : IsPEA 3 2 replacement := by
  refine ⟨replacement_cptp, replacement_nonlocal, by norm_num, ?_⟩
  intro ρ _ hρ
  exact replacement_schmidt ρ hρ

private def psi : Ket (Fin 9 × Fin 9) :=
  ⟨fun x =>
    let a := finProdFinEquiv.symm x.1
    let b := finProdFinEquiv.symm x.2
    phi.vec (a.1, b.1) * phi.vec (a.2, b.2), by
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, finProdFinEquiv,
        Fin.divNat, Fin.modNat, phi, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg 2), ← pow_two, inv_pow, Real.sq_sqrt]⟩

private theorem psi_rank : (coeff psi).rank = 4 := by
  classical
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
  have he : coeff psi = diagonal (fun i : Fin 9 =>
      if i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4 then (1 / 2 : ℂ) else 0) := by
    rw [psi.eq_1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coeff, psi, phi, finProdFinEquiv, Fin.divNat, Fin.modNat,
        Matrix.diagonal_apply, ← pow_two,
        D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq]
  rw [he, Matrix.rank_diagonal, Fintype.card_subtype]
  norm_num [Fin.card_filter_univ_succ]

private theorem pure_rank_le {d r : ℕ} (u : Ket (Fin d × Fin d))
    (h : SchmidtNumberLE (proj u) r) : (coeff u).rank ≤ r := by
  classical
  rcases h with ⟨N, p, w, hp, ht, hr, havg⟩
  let e : D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Ensemble
      (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity u.vec) := {
    N := N
    weight := p
    nonneg := hp
    le_one := fun i => by
      calc
        p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
        _ = 1 := ht
    total := ht
    psi := fun i => (w i).vec
    unit := fun i => (w i).normalized'
    average := by
      change ∑ i, (p i : ℂ) • proj (w i) = proj u
      exact havg.symm }
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hp j)).mp
    (show 0 < ∑ j, p j by rw [ht]; norm_num)
  obtain ⟨z, hz, heq⟩ :=
    D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation.positive_phase
      u.vec u.normalized' e i hi
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hc : coeff (w i) = z • coeff u := by
    ext a b
    exact congrFun heq (a, b)
  have hri := hr i
  rwa [hc, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero hz0)] at hri

private theorem replacement_kron
    (x : Matrix ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
      ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) ℂ) :
    MatrixMap.kron replacement replacement x = x.trace • kronecker (proj phi) (proj phi) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  rw [MatrixMap.kron_def]
  simp only [replacement, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply,
    Matrix.smul_apply, smul_eq_mul]
  have ht (i j : Fin 3 × Fin 3) : (Matrix.single i j (1 : ℂ)).trace =
      if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  simp only [ht, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  change (∑ i, ∑ j, proj phi a b * proj phi c d * x (i, j) (i, j)) =
    x.trace * (proj phi a b * proj phi c d)
  conv_rhs => rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem tensor_output :
    alignedTensor replacement replacement (proj psi) = proj psi := by
  let a : ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) ≃ (Fin 9 × Fin 9) :=
    (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin 3) (Fin 3)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  change Matrix.reindex a a
    (MatrixMap.kron replacement replacement (Matrix.reindex a.symm a.symm (proj psi))) = _
  have ht : (Matrix.reindex a.symm a.symm (proj psi)).trace = 1 := by
    change (∑ i, (proj psi) (a i) (a i)) = 1
    rw [Equiv.sum_comp a (fun i => (proj psi) i i)]
    exact MState.tr' (MState.pure psi)
  rw [replacement_kron, ht]
  simp only [one_smul]
  ext i j
  change (MState.pure phi).m _ _ * (MState.pure phi).m _ _ = (MState.pure psi).m i j
  rw [MState.pure_apply, MState.pure_apply, MState.pure_apply]
  change phi.vec (a.symm i).1 * star (phi.vec (a.symm j).1) *
    (phi.vec (a.symm i).2 * star (phi.vec (a.symm j).2)) = psi.vec i * star (psi.vec j)
  simp only [a, psi, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodProdProdComm_symm,
    Equiv.prodCongr_apply, Equiv.prodProdProdComm_apply,
    Prod.map_fst, Prod.map_snd]
  rw [star_mul]
  ring

private theorem tensor_not_pea : ¬ IsPEA 9 2 (alignedTensor replacement replacement) := by
  intro h
  have hs := h.2.2.2 (proj psi) (MState.psd (MState.pure psi))
    (MState.tr' (MState.pure psi))
  rw [tensor_output] at hs
  have hr := pure_rank_le psi hs
  rw [psi_rank] at hr
  omega

theorem result : ¬ claim := by
  intro h
  exact tensor_not_pea (h 3 2 replacement replacement replacement_pea replacement_pea)

end D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation
