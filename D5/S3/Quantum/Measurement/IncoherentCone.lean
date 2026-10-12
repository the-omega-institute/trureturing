/- GID: D5/S3/Quantum/Measurement/IncoherentCone
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/IncoherentCone
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: IncoherentCone supports the overlap bound. -/

/-
proof_shape: gram_entry_bound: bind-only; consumer: psd_entry_bound
escape_witness: gram_entry_bound: none
Direct frozen dependencies: gram_entry_bound: none
proof_shape: psd_sqrt_gram_factor: bind-only; consumer: psd_entry_bound
escape_witness: psd_sqrt_gram_factor: none
Direct frozen dependencies: psd_sqrt_gram_factor: F1, F2, F3
proof_shape: incoherent_zero: bind-only; consumer: incoherent_separation
escape_witness: incoherent_zero: none
Direct frozen dependencies: incoherent_zero: none
proof_shape: incoherent_add: bind-only; consumer: incoherent_separation
escape_witness: incoherent_add: none
Direct frozen dependencies: incoherent_add: none
proof_shape: incoherent_smul: bind-only; consumer: incoherent_separation
escape_witness: incoherent_smul: none
Direct frozen dependencies: incoherent_smul: none
proof_shape: psd_closed: bind-only; consumer: incoherent_closed
escape_witness: psd_closed: none
Direct frozen dependencies: psd_closed: none
proof_shape: psd_diag_le_trace: bind-only; consumer: psd_entry_bound_of_trace
escape_witness: psd_diag_le_trace: none
Direct frozen dependencies: psd_diag_le_trace: F4
proof_shape: flatten_inner: bind-only; consumer: incoherent_separation
escape_witness: flatten_inner: none
Direct frozen dependencies: flatten_inner: F5, F6
proof_shape: trace_hermitianPart: bind-only; consumer: incoherent_separation
escape_witness: trace_hermitianPart: none
Direct frozen dependencies: trace_hermitianPart: F4
proof_shape: rankone_trace: bind-only; consumer: incoherent_separation
escape_witness: rankone_trace: none
Direct frozen dependencies: rankone_trace: F4, F7
proof_shape: incoherent_rankone: bind-only; consumer: incoherent_separation
escape_witness: incoherent_rankone: none
Direct frozen dependencies: incoherent_rankone: none
proof_shape: psd_entry_bound: bind-only; consumer: psd_entry_bound_of_trace, quantitative_spectral_condition
escape_witness: psd_entry_bound: none
Direct frozen dependencies: psd_entry_bound: F1, F2, F3
proof_shape: psd_entry_bound_of_trace: bind-only; consumer: incoherent_closed
escape_witness: psd_entry_bound_of_trace: none
Direct frozen dependencies: psd_entry_bound_of_trace: F4, F1, F2, F3
proof_shape: incoherent_closed: content; consumer: incoherent_separation
escape_witness: incoherent_closed: incoherent_closed
Direct frozen dependencies: incoherent_closed: F4, F1, F2, F3
proof_shape: incoherent_separation: content; consumer: spectral_balanced_incoherent
escape_witness: incoherent_separation: incoherent_separation
Direct frozen dependencies: incoherent_separation: F5, F4, F1, F2, F3, F7, F6
admission_basis: escape-witness
Frozen declaration identities:
F1: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap
  statement_id: sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F2: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_isHermitian
  statement_id: sha256:8eaaf395a5d8810c697d036c8729b5974aade8efbc4111a5132de5a598ab00b6
F3: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_mul
  statement_id: sha256:7676c10505b22f0e9db5f08c8be82f86e9eb4db5a663554bc93b31c13a2aa6dc
F4: D5/S3/Weil/ZetaLinear/PosIndex.rtrace
  statement_id: sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F5: D5/S3/Quantum/Matrix/CartesianVariance.vectorize
  statement_id: sha256:965518d7298ad8acdfeb6d0b33fc04a6e526724592513da04e49a30b340e8ddb
F6: D5/S3/Quantum/Matrix/CartesianVariance.matrix_pairing
  statement_id: sha256:bc7f3a1d092a6b296a75b0e9d5c7f8c0d2698b6b92d137a30a311713b8e68880
F7: D5/S3/Weil/ZetaLinear/Sylvester.hermForm
  statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Quantum.Matrix.CartesianVariance

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.IncoherentCone
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private theorem gram_entry_bound (V : Matrix ι κ ℂ)
    (hdiag : ∀ i, ((V * Vᴴ) i i).re ≤ 1) (i j : ι) : ‖(V * Vᴴ) i j‖ ≤ 1 := by
  let xi : EuclideanSpace ℂ κ := WithLp.toLp 2 (V i)
  let xj : EuclideanSpace ℂ κ := WithLp.toLp 2 (V j)
  have hin : inner ℂ xj xi = (V * Vᴴ) i j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [xi, xj, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct]
    rfl
  have hsq : ∀ k : ι, ‖(WithLp.toLp 2 (V k) : EuclideanSpace ℂ κ)‖ ^ 2 = ((V * Vᴴ) k k).re := by
    intro k
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    change _ = Complex.reAddGroupHom (∑ j, V k j * star (V k j))
    rw [map_sum]
    apply sum_congr rfl
    intro l _
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  have hi : ‖xi‖ ≤ 1 := by
    have hs := hsq i
    change ‖xi‖ ^ 2 = _ at hs
    nlinarith [hdiag i, norm_nonneg xi]
  have hj : ‖xj‖ ≤ 1 := by
    have hs := hsq j
    change ‖xj‖ ^ 2 = _ at hs
    nlinarith [hdiag j, norm_nonneg xj]
  rw [← hin]
  exact (norm_inner_le_norm xj xi).trans
    ((mul_le_mul hj hi (norm_nonneg xi) (by norm_num)).trans_eq (by ring))

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private theorem psd_sqrt_gram_factor {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    RHLinalg.specMap hA.isHermitian Real.sqrt *
      (RHLinalg.specMap hA.isHermitian Real.sqrt)ᴴ = A := by
  rw [(RHLinalg.specMap_isHermitian hA.isHermitian Real.sqrt).eq,
    ← RHLinalg.specMap_mul]
  have he : (Real.sqrt * Real.sqrt) ∘ hA.isHermitian.eigenvalues =
      hA.isHermitian.eigenvalues := by
    funext k
    exact Real.mul_self_sqrt (hA.eigenvalues_nonneg k)
  unfold RHLinalg.specMap
  conv_rhs => rw [hA.isHermitian.spectral_theorem]
  congr 1
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Pi.mul_apply]
    exact_mod_cast Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  · simp [Matrix.diagonal_apply_ne _ hij]

end

section
variable {n : ℕ}

private theorem incoherent_zero : IsIncoherent (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun _ => 0, fun _ => Matrix.PosSemidef.zero, by simp, by simp⟩

end

section
variable {n : ℕ}

private theorem incoherent_add {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsIncoherent A) (hB : IsIncoherent B) : IsIncoherent (A+B) := by
  obtain ⟨F,hF,rfl,hzF⟩ := hA
  obtain ⟨H,hH,rfl,hzH⟩ := hB
  exact ⟨fun i => F i+H i, fun i => (hF i).add (hH i), by simp [Finset.sum_add_distrib],
    fun i => by simp [Matrix.add_apply,hzF,hzH]⟩

end

section
variable {n : ℕ}

private theorem incoherent_smul {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsIncoherent A)
    (r : ℝ) (hr : 0 ≤ r) : IsIncoherent (r • A) := by
  obtain ⟨F,hF,rfl,hz⟩ := hA
  refine ⟨fun i => r • F i, fun i => (hF i).smul hr, by simp [Finset.smul_sum], ?_⟩
  intro i
  simp [Matrix.smul_apply,hz]

end

section
variable {n : ℕ}

private theorem psd_closed : IsClosed {A : Matrix (Fin n) (Fin n) ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_Ici.preimage (continuous_const.star.dotProduct
      (continuous_id.matrix_mulVec continuous_const))

end

section
variable {n : ℕ}

private theorem psd_diag_le_trace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (j : Fin n) : (A j j).re ≤ RHLinalg.rtrace A := by
  change (A j j).re ≤ (Matrix.trace A).re
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  exact single_le_sum (fun i _ => (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1) (mem_univ j)

end

section
variable {n : ℕ}

private theorem flatten_inner (A Z : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) A) ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) Z) = RHLinalg.rtrace (Aᴴ*Z) := by
  calc
    inner ℝ (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A)
        (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n Z) =
        (inner ℂ (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A)
          (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n Z)).re := by
      simp only [PiLp.inner_apply, Complex.re_sum]
      rfl
    _ = _ := congrArg Complex.re
      (D5.S3.Quantum.Matrix.CartesianVariance.matrix_pairing A Z)

end

section
variable {n : ℕ}

private theorem trace_hermitianPart {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    RHLinalg.rtrace (G*(selfAdjointPart ℝ Z : Matrix (Fin n) (Fin n) ℂ))=RHLinalg.rtrace (G*Z) := by
  have hs : (G*Zᴴ).trace = star ((G*Z).trace) := by
    calc
      (G*Zᴴ).trace = ((Z*G)ᴴ).trace := by rw [Matrix.conjTranspose_mul,hG.eq]
      _ = star ((Z*G).trace) := Matrix.trace_conjTranspose _
      _ = star ((G*Z).trace) := by rw [Matrix.trace_mul_comm]
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv, star_eq_conjTranspose]; unfold RHLinalg.rtrace
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, hs]
  simp only [RCLike.re_eq_complex_re, Complex.real_smul, Complex.ofReal_inv]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  norm_num
  ring

end

section
variable {n : ℕ}

private theorem rankone_trace (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    RHLinalg.rtrace ((Matrix.vecMulVec x (star x))*Y) = RHLinalg.hermForm Y x := by
  unfold RHLinalg.rtrace RHLinalg.hermForm
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

end

section
variable {n : ℕ}

private theorem incoherent_rankone (j : Fin n) (x : Fin n → ℂ) (hx : x j=0) :
    IsIncoherent (Matrix.vecMulVec x (star x)) := by
  let S := Matrix.vecMulVec x (star x)
  refine ⟨fun i => if i=j then S else 0, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact Matrix.posSemidef_vecMulVec_self_star x
    · exact Matrix.PosSemidef.zero
  · simp [S]
  · intro i
    dsimp only
    split_ifs with hi
    · subst i
      simp [S,Matrix.vecMulVec_apply,hx]
    · rfl

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem psd_entry_bound {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hdiag : ∀ i, (A i i).re ≤ 1) (i j : ι) : ‖A i j‖ ≤ 1 := by
  rw [← psd_sqrt_gram_factor hA] at hdiag ⊢
  exact gram_entry_bound _ hdiag i j

end

section
variable {n : ℕ}

private theorem psd_entry_bound_of_trace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (R : ℝ) (hR : 0 < R) (htr : RHLinalg.rtrace A ≤ R) (i j : Fin n) : ‖A i j‖ ≤ R := by
  have hpsd : (R⁻¹ • A).PosSemidef := hA.smul (inv_nonneg.mpr hR.le)
  have hd : ∀ k, ((R⁻¹ • A) k k).re ≤ 1 := by
    intro k
    simp only [Matrix.smul_apply, Complex.real_smul, Complex.re_ofReal_mul]
    have hk := (psd_diag_le_trace hA k).trans htr
    have hm := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hR.le)
    simpa [hR.ne'] using hm
  have hb := psd_entry_bound hpsd hd i j
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hR.le)] at hb
  have hc := mul_le_mul_of_nonneg_left hb hR.le
  simpa [← mul_assoc, hR.ne'] using hc

end

section
variable {n : ℕ}

theorem incoherent_closed :
    IsClosed {A : Matrix (Fin n) (Fin n) ℂ | IsIncoherent A} := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  letI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) := by
    change FirstCountableTopology (Fin n → Fin n → ℂ)
    infer_instance
  rw [← isSeqClosed_iff_isClosed]
  intro u A hu hlim
  choose F hF hsum hz using hu
  have htrcont : Continuous (fun B : Matrix (Fin n) (Fin n) ℂ => RHLinalg.rtrace B) := by
    unfold RHLinalg.rtrace Matrix.trace
    fun_prop
  have htrlim := (htrcont.tendsto A).comp hlim
  obtain ⟨R,hR,hbound⟩ := (Metric.isBounded_range_of_tendsto _ htrlim).exists_pos_norm_le
  have htrF : ∀ k i, RHLinalg.rtrace (F k i) ≤ R := by
    intro k i
    have ht : RHLinalg.rtrace (F k i) ≤ RHLinalg.rtrace (u k) := by
      rw [← hsum k]
      simp only [RHLinalg.rtrace, Matrix.trace_sum, map_sum]
      exact single_le_sum (fun j _ =>
        (Complex.nonneg_iff.mp (hF k j).trace_nonneg).1) (mem_univ i)
    exact ht.trans ((le_abs_self _).trans (hbound _ ⟨k,rfl⟩))
  have hFnorm : ∀ k, ‖F k‖ ≤ R := by
    intro k
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro l
    exact psd_entry_bound_of_trace (hF k i) R hR (htrF k i) j l
  have hFin : ∀ k, F k ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hFnorm
  obtain ⟨F0,hF0,φ,hφ,hFlim⟩ := (isCompact_closedBall 0 R).tendsto_subseq hFin
  have hFlim_i : ∀ i, Tendsto (fun k => F (φ k) i) atTop (nhds (F0 i)) := by
    intro i
    exact ((continuous_apply i).tendsto F0).comp hFlim
  have hpsd : ∀ i, (F0 i).PosSemidef := by
    intro i
    exact psd_closed.mem_of_tendsto (hFlim_i i)
      (Eventually.of_forall fun k => hF (φ k) i)
  have hzero : ∀ i, F0 i i i=0 := by
    intro i
    have hc : IsClosed {B : Matrix (Fin n) (Fin n) ℂ | B i i=0} :=
      isClosed_eq (continuous_id.matrix_elem i i) continuous_const
    exact hc.mem_of_tendsto (hFlim_i i) (Eventually.of_forall fun k => hz (φ k) i)
  have hsumcont : Continuous (fun H : Fin n → Matrix (Fin n) (Fin n) ℂ => ∑ i,H i) := by
    fun_prop
  have hsumlim := (hsumcont.tendsto F0).comp hFlim
  have hulim := hlim.comp hφ.tendsto_atTop
  have heq : (fun k => ∑ i,F (φ k) i) = u ∘ φ := by funext k; exact hsum (φ k)
  change Tendsto (fun k => ∑ i,F (φ k) i) atTop (nhds (∑ i,F0 i)) at hsumlim
  rw [heq] at hsumlim
  exact ⟨F0,hpsd,(tendsto_nhds_unique hsumlim hulim),hzero⟩

end

section
variable {n : ℕ}

theorem incoherent_separation (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hnot : ¬IsIncoherent A) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, LocallyPsd Y ∧ RHLinalg.rtrace (A*Y) < 0 := by
  let E := EuclideanSpace ℂ (Fin n × Fin n)
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] E := ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n)).restrictScalars ℝ
  have hclosed : IsClosed {x : E | IsIncoherent (e.symm x)} :=
    incoherent_closed.preimage e.symm.toLinearMap.continuous_of_finiteDimensional
  let C : ConvexCone ℝ E := ⟨{x | IsIncoherent (e.symm x)},
    fun r hr x hx => by
      change IsIncoherent (e.symm (r • x))
      rw [map_smul]
      exact incoherent_smul hx r hr.le,
    fun x hx y hy => by
      change IsIncoherent (e.symm (x+y))
      rw [map_add]
      exact incoherent_add hx hy⟩
  have hCnonempty : (C : Set E).Nonempty := ⟨0,by
    change IsIncoherent (e.symm 0)
    rw [map_zero]
    exact incoherent_zero⟩
  have hCclosed : IsClosed (C : Set E) := hclosed
  lift C to ProperCone ℝ E using ⟨hCnonempty,hCclosed⟩ with K hK
  have hAnot : e A ∉ K := by
    intro ha
    have hc : e A∈C := by rw [←hK];exact ha
    change IsIncoherent (e.symm (e A)) at hc
    exact hnot (by simpa using hc)
  obtain ⟨W,hW,hAW⟩ := K.hyperplane_separation' hAnot
  let Z := e.symm W
  have hmem : ∀ S, IsIncoherent S → e S∈K := by
    intro S hs
    have hc : e S∈C := by
      change IsIncoherent (e.symm (e S))
      simpa using hs
    change e S∈(K : ConvexCone ℝ E)
    rw [hK]
    exact hc
  have hpair : ∀ S, IsIncoherent S → S.IsHermitian → 0 ≤ RHLinalg.rtrace (S*Z) := by
    intro S hS hSH
    have hh := hW (e S) (hmem S hS)
    have hWeq : W=e Z := (e.apply_symm_apply W).symm
    rw [hWeq] at hh
    change 0 ≤ inner ℝ ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) S) ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) Z) at hh
    rw [flatten_inner,hSH.eq] at hh
    exact hh
  refine ⟨(selfAdjointPart ℝ Z : Matrix (Fin n) (Fin n) ℂ),⟨(selfAdjointPart ℝ Z).property.isHermitian,?_⟩,?_⟩
  · intro j x hx
    let S := Matrix.vecMulVec x (star x)
    have hS := (Matrix.posSemidef_vecMulVec_self_star x).isHermitian
    have hp := hpair S (incoherent_rankone j x hx) hS
    rw [← trace_hermitianPart hS Z] at hp
    exact (rankone_trace ((selfAdjointPart ℝ Z : Matrix (Fin n) (Fin n) ℂ)) x) ▸ hp
  · have hWeq : W=e Z := (e.apply_symm_apply W).symm
    rw [hWeq] at hAW
    change inner ℝ ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) A) ((D5.S3.Quantum.Matrix.CartesianVariance.vectorize n) Z) < 0 at hAW
    rw [flatten_inner,hA.eq] at hAW
    rw [trace_hermitianPart hA Z]
    exact hAW

end

end
end D5.S3.Quantum.Measurement.IncoherentCone
