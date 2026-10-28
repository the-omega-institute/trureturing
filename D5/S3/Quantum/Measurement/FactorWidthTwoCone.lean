/- GID: D5/S3/Quantum/Measurement/FactorWidthTwoCone
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FactorWidthTwoCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed finite support cones and factor-width-two duality. -/

/-
admission_basis: escape-witness
escape_witness: block_closed: compactness for arbitrary finite support families, used by block_separation and fw2_duality
proof_shape: IsKSparse: bind-only; consumers: IsKIncoherentSum, sparse_of_supported
proof_shape: IsKIncoherentSum: bind-only; consumers: fw2_duality, AbsoluteTwoIncoherencePurityRefutation.IsAbsolutelyKIncoherent
proof_shape: IsBlockSum: bind-only; consumers: block_zero, block_closed, block_separation, block_to_sparse
proof_shape: IsLocally2: bind-only; consumers: fw2_duality, local2_pair, AbsoluteTwoIncoherencePurityRefutation.near_saturation_data
proof_shape: block_zero: bind-only; consumers: block_separation
proof_shape: block_add: bind-only; consumers: block_separation
proof_shape: block_smul: bind-only; consumers: block_separation
proof_shape: block_closed: content; consumers: block_separation
proof_shape: block_rankone: bind-only; consumers: block_separation
proof_shape: block_separation: content; consumers: fw2_duality
proof_shape: sparse_of_supported: bind-only; consumers: block_to_sparse
proof_shape: block_to_sparse: bind-only; consumers: fw2_duality
proof_shape: fw2_duality: content; consumers: AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
proof_shape: local2_pair: bind-only; consumers: local2_diagonal, local2_minor
proof_shape: local2_diagonal: bind-only; consumers: local2_trace_nonneg, local2_trace_zero, AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
proof_shape: local2_minor: bind-only; consumers: local2_trace_zero, AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
proof_shape: local2_smul: bind-only; consumers: AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
proof_shape: local2_trace_nonneg: bind-only; consumers: AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
proof_shape: local2_trace_zero: bind-only; consumers: AbsoluteTwoIncoherencePurityRefutation.result (through its helpers)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18980
-/

import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Measurement.IncoherentCone
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Weil.ZetaLinear.Sylvester

set_option autoImplicit false
set_option maxHeartbeats 600000
open Matrix Finset Filter
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace
noncomputable section

namespace D5.S3.Quantum.Measurement.FactorWidthTwoCone

/-- A vector of `ℂⁿ` with at most `k` nonzero entries. -/
def IsKSparse {n : ℕ} (k : ℕ) (v : Fin n → ℂ) : Prop :=
  (Finset.univ.filter fun i => v i ≠ 0).card ≤ k

/-- Johnston–Moein–Pereira–Plosker, Section 2.1: `X = ∑ⱼ vⱼ vⱼ*` for finitely many vectors
`vⱼ`, each with at most `k` nonzero entries (`X` has factor width at most `k`). -/
def IsKIncoherentSum {n : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (m : ℕ) (v : Fin m → Fin n → ℂ), (∀ j, IsKSparse k (v j)) ∧
    X = ∑ j, vecMulVec (v j) (star (v j))

variable {n : ℕ} {ι : Type*} [Fintype ι]

private def IsBlockSum (s : ι → Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ F : ι → Matrix (Fin n) (Fin n) ℂ,
    (∀ i, (F i).PosSemidef) ∧ ∑ i, F i = X ∧
      ∀ i j, j ∉ s i → F i j j = 0

private theorem block_zero (s : ι → Finset (Fin n)) : IsBlockSum s 0 := by
  exact ⟨fun _ => 0, fun _ => PosSemidef.zero, by simp, by simp⟩

private theorem block_add (s : ι → Finset (Fin n)) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsBlockSum s A) (hB : IsBlockSum s B) : IsBlockSum s (A + B) := by
  {
    obtain ⟨F,hF,rfl,hzF⟩ := hA
    obtain ⟨G,hG,rfl,hzG⟩ := hB
    exact ⟨fun i => F i + G i, fun i => (hF i).add (hG i),
      by simp [sum_add_distrib], fun i j hj => by simp [hzF i j hj, hzG i j hj]⟩
  }

private theorem block_smul (s : ι → Finset (Fin n)) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsBlockSum s A) (c : ℝ) (hc : 0 ≤ c) : IsBlockSum s (c • A) := by
  {
    obtain ⟨F,hF,rfl,hz⟩ := hA
    exact ⟨fun i => c • F i, fun i => (hF i).smul hc,
      by simp [smul_sum], fun i j hj => by simp [hz i j hj]⟩
  }

private theorem block_closed (s : ι → Finset (Fin n)) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℂ | IsBlockSum s A} := by
  {
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
      exact D5.S3.Quantum.Measurement.IncoherentCone.psd_entry_bound_of_trace (hF k i) R hR (htrF k i) j l
    have hFin : ∀ k, F k ∈ Metric.closedBall 0 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hFnorm
    obtain ⟨F0,hF0,φ,hφ,hFlim⟩ := (isCompact_closedBall 0 R).tendsto_subseq hFin
    have hFlim_i : ∀ i, Tendsto (fun k => F (φ k) i) atTop (nhds (F0 i)) := by
      intro i
      exact ((continuous_apply i).tendsto F0).comp hFlim
    have hpsd : ∀ i, (F0 i).PosSemidef := by
      intro i
      exact (D5.S3.Quantum.Measurement.IncoherentCone.psd_closed).mem_of_tendsto (hFlim_i i)
        (Eventually.of_forall fun k => hF (φ k) i)
    have hzero : ∀ i j, j ∉ s i → F0 i j j = 0 := by
      intro i j hj
      have hc : IsClosed {B : Matrix (Fin n) (Fin n) ℂ | B j j = 0} :=
        isClosed_eq (continuous_id.matrix_elem j j) continuous_const
      exact hc.mem_of_tendsto (hFlim_i i) (Eventually.of_forall fun k => hz (φ k) i j hj)
    have hsumcont : Continuous (fun H : ι → Matrix (Fin n) (Fin n) ℂ => ∑ i,H i) := by
      fun_prop
    have hsumlim := (hsumcont.tendsto F0).comp hFlim
    have hulim := hlim.comp hφ.tendsto_atTop
    have heq : (fun k => ∑ i,F (φ k) i) = u ∘ φ := by funext k; exact hsum (φ k)
    change Tendsto (fun k => ∑ i,F (φ k) i) atTop (nhds (∑ i,F0 i)) at hsumlim
    rw [heq] at hsumlim
    exact ⟨F0,hpsd,tendsto_nhds_unique hsumlim hulim,hzero⟩
  }

private theorem block_rankone (s : ι → Finset (Fin n)) (i : ι) (x : Fin n → ℂ)
    (hx : ∀ j, j ∉ s i → x j = 0) : IsBlockSum s (vecMulVec x (star x)) := by
  classical
  {
    let S := vecMulVec x (star x)
    refine ⟨fun k => if k = i then S else 0, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      split_ifs
      · exact posSemidef_vecMulVec_self_star x
      · exact PosSemidef.zero
    · simp [S]
    · intro k j hj
      dsimp only
      split_ifs with hk
      · subst k
        simp [S, vecMulVec_apply, hx j hj]
      · rfl
  }

private theorem block_separation (s : ι → Finset (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hnot : ¬IsBlockSum s A) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, (Y.IsHermitian ∧ ∀ i x, (∀ j, j ∉ s i → x j = 0) → 0 ≤ RHLinalg.hermForm Y x) ∧ RHLinalg.rtrace (A*Y) < 0 := by
  {
    let E := EuclideanSpace ℂ (Fin n × Fin n)
    let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] E :=
      (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n).restrictScalars ℝ
    have hclosed : IsClosed {x : E | IsBlockSum s (e.symm x)} :=
      (block_closed s).preimage e.symm.toLinearMap.continuous_of_finiteDimensional
    let C : ConvexCone ℝ E := ⟨{x | IsBlockSum s (e.symm x)},
      fun c hc x hx => by
        change IsBlockSum s (e.symm (c • x))
        rw [map_smul]
        exact block_smul s hx c hc.le,
      fun x hx y hy => by
        change IsBlockSum s (e.symm (x+y))
        rw [map_add]
        exact block_add s hx hy⟩
    have hCnonempty : (C : Set E).Nonempty := ⟨0,by
      change IsBlockSum s (e.symm 0)
      rw [map_zero]
      exact block_zero s⟩
    have hCclosed : IsClosed (C : Set E) := hclosed
    lift C to ProperCone ℝ E using ⟨hCnonempty,hCclosed⟩ with K hK
    have hAnot : e A ∉ K := by
      intro ha
      have hc : e A ∈ C := by rw [←hK];exact ha
      change IsBlockSum s (e.symm (e A)) at hc
      exact hnot (by simpa using hc)
    obtain ⟨W,hW,hAW⟩ := K.hyperplane_separation' hAnot
    let Z := e.symm W
    have hmem : ∀ S, IsBlockSum s S → e S ∈ K := by
      intro S hs
      have hc : e S ∈ C := by
        change IsBlockSum s (e.symm (e S))
        simpa using hs
      change e S ∈ (K : ConvexCone ℝ E)
      rw [hK]
      exact hc
    have hpair : ∀ S, IsBlockSum s S → S.IsHermitian → 0 ≤ RHLinalg.rtrace (S*Z) := by
      intro S hS hSH
      have hh := hW (e S) (hmem S hS)
      have hWeq : W = e Z := (e.apply_symm_apply W).symm
      rw [hWeq] at hh
      change 0 ≤ inner ℝ (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n S)
        (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n Z) at hh
      rw [D5.S3.Quantum.Measurement.IncoherentCone.flatten_inner,hSH.eq] at hh
      exact hh
    refine ⟨(selfAdjointPart ℝ Z : Matrix (Fin n) (Fin n) ℂ),
      ⟨(selfAdjointPart ℝ Z).property.isHermitian,?_⟩,?_⟩
    · intro i x hx
      let S := vecMulVec x (star x)
      have hS := (posSemidef_vecMulVec_self_star x).isHermitian
      have hp := hpair S (block_rankone s i x hx) hS
      rw [← D5.S3.Quantum.Measurement.IncoherentCone.trace_hermitianPart hS Z] at hp
      exact (D5.S3.Quantum.Measurement.IncoherentCone.rankone_trace ((selfAdjointPart ℝ Z : Matrix (Fin n) (Fin n) ℂ)) x) ▸ hp
    · have hWeq : W = e Z := (e.apply_symm_apply W).symm
      rw [hWeq] at hAW
      change inner ℝ (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n A)
        (D5.S3.Quantum.Matrix.CartesianVariance.vectorize n Z) < 0 at hAW
      rw [D5.S3.Quantum.Measurement.IncoherentCone.flatten_inner,hA.eq] at hAW
      rw [D5.S3.Quantum.Measurement.IncoherentCone.trace_hermitianPart hA Z]
      exact hAW
  }

def IsLocally2 {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Y.IsHermitian ∧ ∀ (s : {s : Finset (Fin n) // s.card ≤ 2}) (x : Fin n → ℂ),
    (∀ j, j ∉ s.val → x j = 0) → 0 ≤ RHLinalg.hermForm Y x

variable {n : ℕ}

private theorem sparse_of_supported {v : Fin n → ℂ} (s : Finset (Fin n)) (hs : s.card ≤ 2)
    (hv : ∀ j, j ∉ s → v j = 0) : IsKSparse 2 v := by
  apply (Finset.card_le_card ?_).trans hs
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj
  by_contra hn
  exact hj (hv j hn)

private theorem block_to_sparse {ι : Type*} [Fintype ι]
    (s : ι → Finset (Fin n)) (hs : ∀ i, (s i).card ≤ 2)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsBlockSum s A) : IsKIncoherentSum 2 A := by
  classical
  obtain ⟨F,hF,hSum,hZero⟩ := hA
  choose m v hDec using (fun i => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hF i))
  have hv : ∀ i k, IsKSparse 2 (v i k) := by
    intro i k
    apply sparse_of_supported (s i) (hs i)
    intro j hj
    have hz : ∑ l : Fin (m i), Complex.normSq (v i l j) = 0 := by
      have hd := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M j j).re) (hDec i)
      rw [hZero i j hj] at hd
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Complex.mul_conj] using hd.symm
    have hk : Complex.normSq (v i k j) ≤ 0 := by
      rw [← hz]
      exact single_le_sum (fun l _ => Complex.normSq_nonneg (v i l j)) (mem_univ k)
    exact Complex.normSq_eq_zero.mp (le_antisymm hk (Complex.normSq_nonneg _))
  let σ := (i : ι) × Fin (m i)
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  refine ⟨Fintype.card σ, fun k => v (e.symm k).1 (e.symm k).2, ?_, ?_⟩
  · intro k
    exact hv _ _
  · calc
      A = ∑ i, F i := hSum.symm
      _ = ∑ i, ∑ j, vecMulVec (v i j) (star (v i j)) := by simp_rw [hDec]
      _ = ∑ k : σ, vecMulVec (v k.1 k.2) (star (v k.1 k.2)) := by
        rw [Fintype.sum_sigma]
      _ = _ := Fintype.sum_equiv e _ _ (by intro k; dsimp only; rw [e.symm_apply_apply])

theorem fw2_duality (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (hdual : ∀ A : Matrix (Fin n) (Fin n) ℂ, IsLocally2 A → 0 ≤ RHLinalg.rtrace (X*A)) :
    IsKIncoherentSum 2 X := by
  apply block_to_sparse (fun s : {s : Finset (Fin n) // s.card ≤ 2} => s.val) (fun s => s.property)
  by_contra hn
  obtain ⟨Y,hY,hneg⟩ := block_separation (fun s : {s : Finset (Fin n) // s.card ≤ 2} => s.val) X hX hn
  exact (not_lt_of_ge (hdual Y hY)) hneg

variable {n : ℕ}

private theorem local2_pair (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A) (i j : Fin n) :
    (A.submatrix (![i,j] : Fin 2 → Fin n) (![i,j] : Fin 2 → Fin n)).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hA.1.submatrix _,?_⟩
  intro z
  let x : Fin n → ℂ := Pi.single i (z 0) + Pi.single j (z 1)
  have hx : ∀ k, k ∉ ({i,j} : Finset (Fin n)) → x k = 0 := by
    intro k hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    simp [x,Pi.single_apply,hk.1,hk.2]
  have hpos := hA.2 ⟨{i,j},Finset.card_le_two⟩ x hx
  have he : star x ⬝ᵥ (A *ᵥ x) =
      star z ⬝ᵥ ((A.submatrix (![i,j] : Fin 2 → Fin n) (![i,j] : Fin 2 → Fin n)) *ᵥ z) := by
    dsimp only [x]
    simp only [star_add, Pi.star_single, Matrix.mulVec_add, add_dotProduct,
      dotProduct_add, single_dotProduct, Matrix.mulVec_single, Pi.smul_apply,
      Matrix.col_apply, smul_eq_mul]
    simp [dotProduct,Matrix.mulVec,Fin.sum_univ_succ,Matrix.submatrix_apply]
    ring
  have hre : 0 ≤ (star x ⬝ᵥ (A*ᵥx)).re := hpos
  rw [he] at hre
  have him := hA.1.im_star_dotProduct_mulVec_self x
  rw [he] at him
  exact Complex.nonneg_iff.mpr ⟨hre,him.symm⟩

theorem local2_diagonal (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A) (i : Fin n) :
    0 ≤ (A i i).re := by
  have h := (Complex.nonneg_iff.mp ((local2_pair A hA i i).diag_nonneg (i:=0))).1
  simpa using h

theorem local2_minor (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A) (i j : Fin n) :
    Complex.normSq (A i j) ≤ (A i i).re * (A j j).re := by
  simpa using D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound (local2_pair A hA i j)
    (0 : Fin 2) (1 : Fin 2)

variable {n : ℕ}

theorem local2_smul (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A)
    (c : ℝ) (hc : 0 ≤ c) : IsLocally2 (c • A) := by
  refine ⟨hA.1.smul (by simp [isSelfAdjoint_iff]), ?_⟩
  intro i x hx
  have hp := hA.2 i x hx
  have he : RHLinalg.hermForm (c • A) x = c * RHLinalg.hermForm A x := by
    simp [RHLinalg.hermForm,Matrix.smul_mulVec,dotProduct_smul,Complex.real_smul]
  rw [he]
  exact mul_nonneg hc hp

theorem local2_trace_nonneg (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A) :
    0 ≤ RHLinalg.rtrace A := by
  change 0 ≤ (∑ i, A i i).re
  rw [Complex.re_sum]
  exact sum_nonneg (fun i _ => local2_diagonal A hA i)

theorem local2_trace_zero (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsLocally2 A)
    (ht : RHLinalg.rtrace A = 0) : A = 0 := by
  have hsum : ∑ i, (A i i).re = 0 := by
    simpa [RHLinalg.rtrace,Matrix.trace,Complex.re_sum] using ht
  have hd : ∀ i, (A i i).re = 0 := by
    intro i
    apply le_antisymm _ (local2_diagonal A hA i)
    rw [← hsum]
    exact single_le_sum (fun j _ => local2_diagonal A hA j) (mem_univ i)
  ext i j
  have hm := local2_minor A hA i j
  rw [hd i,hd j,zero_mul] at hm
  exact Complex.normSq_eq_zero.mp (le_antisymm hm (Complex.normSq_nonneg _))

end D5.S3.Quantum.Measurement.FactorWidthTwoCone
end
