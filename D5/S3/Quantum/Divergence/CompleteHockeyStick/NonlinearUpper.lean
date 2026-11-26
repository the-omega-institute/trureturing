/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: A dimension-uniform nonlinear hockey-stick bound for full Kraus-product span. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Divergence.PositiveKrausCompression
import D5.S3.Quantum.Recovery.CanonicalEntanglementFidelity
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Full Kraus-product span gives a nonlinear upper bound on hockey-stick divergence
with equal reference marginals, uniformly over finite references. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

section

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickOutputEffect

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_embed_mul)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open RHLinalg (rtrace rtrace_sub)

universe u

variable {S E : Type u} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

private theorem norm_environment_amplification_le (W : Matrix E E ℂ) :
    ‖Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W)‖ ≤
      ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) W‖ := by
  let lift : Matrix E E ℂ →⋆ₙₐ[ℂ] Matrix (S × E) (S × E) ℂ := {
    toFun W := (1 : Matrix S S ℂ) ⊗ₖ W
    map_zero' := Matrix.kronecker_zero _
    map_add' X Y := Matrix.kronecker_add _ X Y
    map_smul' z X := Matrix.kronecker_smul z _ X
    map_mul' X Y := by
      simpa only [Matrix.one_mul] using
        Matrix.mul_kronecker_mul (1 : Matrix S S ℂ) (1 : Matrix S S ℂ) X Y
    map_star' X := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one]
  }
  rw [← Matrix.cstar_norm_def, ← Matrix.cstar_norm_def]
  exact NonUnitalStarAlgHom.norm_apply_le lift W

private theorem inner_effect_eq_trace (T : Matrix S S ℂ) (v : S × E → ℂ) :
    inner ℂ (WithLp.toLp 2 v)
        (Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ)
          (T ⊗ₖ (1 : Matrix E E ℂ)) (WithLp.toLp 2 v)) =
      (T * partialTraceRight (Matrix.vecMulVec v (star v))).trace := by
  calc
    _ = ((T ⊗ₖ (1 : Matrix E E ℂ)) * Matrix.vecMulVec v (star v)).trace := by
      rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
        Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    _ = _ := by
      rw [← trace_partialTraceRight ((T ⊗ₖ (1 : Matrix E E ℂ)) * Matrix.vecMulVec v (star v)),
        partialTraceRight_embed_mul]

omit [DecidableEq S] [DecidableEq E] in
private theorem norm_sq_eq_rtrace_marginal (v : S × E → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (S × E))‖ ^ 2 =
      rtrace (partialTraceRight (Matrix.vecMulVec v (star v))) := by
  rw [rtrace, trace_partialTraceRight, Matrix.trace_vecMulVec]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 v)).symm

private theorem effect_piece (p q : S × E → ℂ) (W : Matrix E E ℂ)
    (hW : ‖Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W)‖ ≤ 1)
    (T : Matrix S S ℂ) (hT : 0 ≤ T) :
    let D := Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W)
    let F := Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) (T ⊗ₖ (1 : Matrix E E ℂ))
    let x := rtrace (T * partialTraceRight (Matrix.vecMulVec p (star p)))
    let y := rtrace (T * partialTraceRight (Matrix.vecMulVec q (star q)))
    0 ≤ x ∧ 0 ≤ y ∧
      ‖inner ℂ (WithLp.toLp 2 p) (F (D (WithLp.toLp 2 q)))‖ ≤ Real.sqrt (x * y) := by
  intro D F x y
  let B := CFC.sqrt T ⊗ₖ (1 : Matrix E E ℂ)
  let L := Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B
  have hroot : (CFC.sqrt T)ᴴ = CFC.sqrt T :=
    (CFC.sqrt_nonneg T).posSemidef.isHermitian.eq
  have hB : Bᴴ = B := by
    dsimp only [B]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hroot]
  have hadj : L.adjoint = L := by
    change star (Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B) =
      Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B
    rw [← map_star, Matrix.star_eq_conjTranspose, hB]
  have hBsq : B * B = T ⊗ₖ (1 : Matrix E E ℂ) := by
    dsimp only [B]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, CFC.sqrt_mul_sqrt_self T hT]
  have hsquare : L * L = F := by
    change Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B *
      Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B =
      Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) (T ⊗ₖ (1 : Matrix E E ℂ))
    rw [← map_mul, hBsq]
  -- The square root and the contraction act on different tensor factors.
  have hBcomm : B * ((1 : Matrix S S ℂ) ⊗ₖ W) = ((1 : Matrix S S ℂ) ⊗ₖ W) * B := by
    simp only [B, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hcomm (v : EuclideanSpace ℂ (S × E)) : D (L v) = L (D v) := by
    have hmul : D * L = L * D := by
      change Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W) *
        Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B =
        Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) B *
        Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W)
      simp only [← map_mul, hBcomm]
    exact congrArg (fun A : EuclideanSpace ℂ (S × E) →L[ℂ] EuclideanSpace ℂ (S × E) =>
      A v) hmul
  have hnorm (v : S × E → ℂ) :
      ‖L (WithLp.toLp 2 v)‖ ^ 2 = rtrace (T * partialTraceRight (Matrix.vecMulVec v (star v))) := by
    calc
      _ = (inner ℂ (L (WithLp.toLp 2 v)) (L (WithLp.toLp 2 v))).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ (WithLp.toLp 2 v) (F (WithLp.toLp 2 v))).re := by
        rw [← ContinuousLinearMap.adjoint_inner_right, hadj]
        change (inner ℂ (WithLp.toLp 2 v) ((L * L) (WithLp.toLp 2 v))).re = _
        rw [hsquare]
      _ = _ := congrArg Complex.re (inner_effect_eq_trace T v)
  have hoverlap :
      inner ℂ (L (WithLp.toLp 2 p)) (D (L (WithLp.toLp 2 q))) =
        inner ℂ (WithLp.toLp 2 p) (F (D (WithLp.toLp 2 q))) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hcomm]
    change inner ℂ (WithLp.toLp 2 p) ((L * L) (D (WithLp.toLp 2 q))) = _
    rw [hsquare]
  have hcontract (v : EuclideanSpace ℂ (S × E)) : ‖D v‖ ≤ ‖v‖ :=
    (D.le_opNorm v).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hW (norm_nonneg v))
  have hx : ‖L (WithLp.toLp 2 p)‖ ^ 2 = x := hnorm p
  have hy : ‖L (WithLp.toLp 2 q)‖ ^ 2 = y := hnorm q
  have hx0 : 0 ≤ x := by
    rw [← hx]
    exact sq_nonneg _
  have hy0 : 0 ≤ y := by
    rw [← hy]
    exact sq_nonneg _
  refine ⟨hx0, hy0, ?_⟩
  calc
    _ = ‖inner ℂ (L (WithLp.toLp 2 p)) (D (L (WithLp.toLp 2 q)))‖ := by rw [hoverlap]
    _ ≤ ‖L (WithLp.toLp 2 p)‖ * ‖D (L (WithLp.toLp 2 q))‖ := norm_inner_le_norm _ _
    _ ≤ ‖L (WithLp.toLp 2 p)‖ * ‖L (WithLp.toLp 2 q)‖ :=
      mul_le_mul_of_nonneg_left (hcontract _) (norm_nonneg _)
    _ = Real.sqrt (x * y) := by
      rw [Real.sqrt_mul hx0, ← hx, ← hy, Real.sqrt_sq (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]

/-- A system effect splits the overlap against an environment contraction into two
Cauchy–Schwarz bounds. The effect expectations are evaluated on the reduced matrices. -/
private theorem norm_environment_overlap_le (p q : S × E → ℂ) (W : Matrix E E ℂ)
    (hW : ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℂ) W‖ ≤ 1)
    (M : Matrix S S ℂ) (hM : 0 ≤ M) (hI : M ≤ 1) :
    let a := ‖(WithLp.toLp 2 p : EuclideanSpace ℂ (S × E))‖ ^ 2
    let b := ‖(WithLp.toLp 2 q : EuclideanSpace ℂ (S × E))‖ ^ 2
    let x := rtrace (M * partialTraceRight (Matrix.vecMulVec p (star p)))
    let y := rtrace (M * partialTraceRight (Matrix.vecMulVec q (star q)))
    ‖inner ℂ (WithLp.toLp 2 p)
      (Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ)
        ((1 : Matrix S S ℂ) ⊗ₖ W) (WithLp.toLp 2 q))‖ ≤
        Real.sqrt (x * y) + Real.sqrt ((a - x) * (b - y)) ∧
    Real.sqrt (x * y) + Real.sqrt ((a - x) * (b - y)) ≤ Real.sqrt ((a + b) * (a - x + y)) := by
  intro a b x y
  have hcontract := (norm_environment_amplification_le (S := S) W).trans hW
  obtain ⟨_, hy0, hfirst⟩ := effect_piece p q W hcontract M hM
  obtain ⟨hax0, _, hsecond⟩ := effect_piece p q W hcontract (1 - M) (sub_nonneg.mpr hI)
  have hcomplement (v : S × E → ℂ) :
      rtrace ((1 - M) * partialTraceRight (Matrix.vecMulVec v (star v))) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (S × E))‖ ^ 2 -
          rtrace (M * partialTraceRight (Matrix.vecMulVec v (star v))) := by
    rw [sub_mul, Matrix.one_mul, rtrace_sub, ← norm_sq_eq_rtrace_marginal]
  simp only [hcomplement] at hax0 hsecond
  let D := Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ) ((1 : Matrix S S ℂ) ⊗ₖ W)
  have hsum : (M ⊗ₖ (1 : Matrix E E ℂ)) + ((1 - M) ⊗ₖ (1 : Matrix E E ℂ)) = 1 := by
    rw [← Matrix.add_kronecker, add_comm M, sub_add_cancel, Matrix.one_kronecker_one]
  have hsplit : inner ℂ (WithLp.toLp 2 p) (D (WithLp.toLp 2 q)) =
      inner ℂ (WithLp.toLp 2 p)
        (Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ)
          (M ⊗ₖ (1 : Matrix E E ℂ)) (D (WithLp.toLp 2 q))) +
      inner ℂ (WithLp.toLp 2 p)
        (Matrix.toEuclideanCLM (n := S × E) (𝕜 := ℂ)
          ((1 - M) ⊗ₖ (1 : Matrix E E ℂ)) (D (WithLp.toLp 2 q))) := by
    rw [← inner_add_right, ← _root_.add_apply, ← map_add, hsum, map_one,
      one_apply_eq_self]
  constructor
  · change ‖inner ℂ (WithLp.toLp 2 p) (D (WithLp.toLp 2 q))‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  · change 0 ≤ y at hy0
    change 0 ≤ a - x at hax0
    have ha : 0 ≤ a := sq_nonneg _
    have hb : 0 ≤ b := sq_nonneg _
    let f : Fin 2 → ℝ := ![a, b]
    let g : Fin 2 → ℝ := ![y, a - x]
    have hf : ∀ i, 0 ≤ f i := by
      intro i
      fin_cases i
      · exact ha
      · exact hb
    have hg : ∀ i, 0 ≤ g i := by
      intro i
      fin_cases i
      · exact hy0
      · exact hax0
    have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2)) hf hg
    calc
      _ ≤ Real.sqrt (a * y) + Real.sqrt (b * (a - x)) := by
        apply add_le_add
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (sub_nonneg.mp hax0) hy0)
        · rw [mul_comm b (a - x)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (sub_le_self b hy0) hax0)
      _ ≤ _ := by
        rw [Real.sqrt_mul ha, Real.sqrt_mul hb, Real.sqrt_mul (add_nonneg ha hb),
          add_comm (a - x) y]
        simpa only [Fin.sum_univ_two, f, g, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] using hCS


end D5.S3.Quantum.Divergence.CompleteHockeyStickOutputEffect

end

section

open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (ptr)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_of_posSemidef)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Recovery.CanonicalEntanglementFidelity (vector)

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickPurificationGram

open private rectangular_douglas from
  D5.S3.Quantum.Divergence.PositiveKrausCompression

private theorem sqrtVector_partialTraceRight {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℂ) (hT : T.PosSemidef) :
    partialTraceRight (Matrix.vecMulVec (vector T ∘ Prod.swap)
      (star (vector T ∘ Prod.swap))) = T := by
  have hadj : (cfc Real.sqrt T)ᴴ = cfc Real.sqrt T :=
    (cfc_predicate Real.sqrt T : IsSelfAdjoint (cfc Real.sqrt T)).star_eq
  have hs : cfc Real.sqrt T = CFC.sqrt T := by
    rw [CFC.sqrt_eq_real_sqrt _ hT.nonneg, cfcₙ_eq_cfc]
  calc
    _ = cfc Real.sqrt T * (cfc Real.sqrt T)ᴴ := by
      ext i j
      simp only [partialTraceRight, Matrix.vecMulVec_apply, Pi.star_apply, Function.comp_apply,
        Prod.swap, vector, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = T := by rw [hadj, hs, CFC.sqrt_mul_sqrt_self _ hT.nonneg]

variable {R A : Type*} [Fintype R] [Fintype A]

private theorem norm_sq_eq_traceNorm_of_marginal {E : Type*} [Fintype E]
    (p : R × (A × E) → ℂ) {P : Matrix (R × A) (R × A) ℂ} (hP : P.PosSemidef)
    (hm : partialTraceRight (Matrix.vecMulVec (p ∘ Equiv.prodAssoc R A E)
      (star (p ∘ Equiv.prodAssoc R A E))) = P) :
    ‖(WithLp.toLp 2 p : EuclideanSpace ℂ (R × (A × E)))‖ ^ 2 = traceNorm P := by
  classical
  let e := Equiv.prodAssoc R A E
  have htrace : (Matrix.vecMulVec p (star p)).trace = P.trace := by
    calc
      _ = (Matrix.vecMulVec (p ∘ e) (star (p ∘ e))).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Pi.star_apply,
          Function.comp_apply]
        exact (e.sum_comp (fun j => p j * star (p j))).symm
      _ = _ := (trace_partialTraceRight _).symm.trans (congrArg Matrix.trace hm)
  let v : EuclideanSpace ℂ (R × (A × E)) := WithLp.toLp 2 p
  have hv : (Matrix.vecMulVec p (star p)).trace = (‖v‖ : ℂ) ^ 2 := by
    rw [Matrix.trace_vecMulVec]
    exact (EuclideanSpace.inner_eq_star_dotProduct v v).symm.trans
      (inner_self_eq_norm_sq_to_K v)
  have hnorm : (‖v‖ : ℂ) ^ 2 = (traceNorm P : ℂ) :=
    hv.symm.trans (htrace.trans (traceNorm_of_posSemidef hP).symm)
  have ht := congrArg Complex.re hnorm
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, v] using ht

variable [DecidableEq R] [DecidableEq A]

/-- Ordered reference marginals admit unnormalized purifications related by a contraction
on the input and the common purifying system `R × A`. The squared ket norms are the trace
norms of the original PSD matrices. -/
private theorem exists_purifications_of_ptr_le (P Q : Matrix (R × A) (R × A) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hm : ptr P ≤ ptr Q) :
    ∃ (p q : R × (A × (R × A)) → ℂ) (U : Matrix (A × (R × A)) (A × (R × A)) ℂ),
      partialTraceRight (Matrix.vecMulVec (p ∘ Equiv.prodAssoc R A (R × A))
        (star (p ∘ Equiv.prodAssoc R A (R × A)))) = P ∧
      partialTraceRight (Matrix.vecMulVec (q ∘ Equiv.prodAssoc R A (R × A))
        (star (q ∘ Equiv.prodAssoc R A (R × A)))) = Q ∧
      ‖(WithLp.toLp 2 p : EuclideanSpace ℂ (R × (A × (R × A))))‖ ^ 2 = traceNorm P ∧
      ‖(WithLp.toLp 2 q : EuclideanSpace ℂ (R × (A × (R × A))))‖ ^ 2 = traceNorm Q ∧
      ‖Matrix.toEuclideanCLM (n := A × (R × A)) (𝕜 := ℂ) U‖ ≤ 1 ∧
      p = ((1 : Matrix R R ℂ) ⊗ₖ U) *ᵥ q := by
  -- Keep the reference as the row and group the input with the purifying index.
  let coefficients (T : Matrix (R × A) (R × A) ℂ) : Matrix R (A × (R × A)) ℂ :=
    fun r x => vector T (x.2, (r, x.1))
  let X := coefficients P
  let Y := coefficients Q
  have hgram (T : Matrix (R × A) (R × A) ℂ) (hT : T.PosSemidef) :
      coefficients T * (coefficients T)ᴴ = ptr T := by
    calc
      _ = ptr (partialTraceRight (Matrix.vecMulVec (vector T ∘ Prod.swap)
          (star (vector T ∘ Prod.swap)))) := by
        ext r s
        simp only [coefficients, Matrix.mul_apply, Matrix.conjTranspose_apply, ptr,
          partialTraceRight, Matrix.vecMulVec_apply, Pi.star_apply, Function.comp_apply,
          Prod.swap, Fintype.sum_prod_type]
      _ = ptr T := congrArg ptr (sqrtVector_partialTraceRight T hT)
  have hYX : (Y * Yᴴ - X * Xᴴ).PosSemidef := by
    change (coefficients Q * (coefficients Q)ᴴ -
      coefficients P * (coefficients P)ᴴ).PosSemidef
    rw [hgram Q hQ, hgram P hP]
    exact (sub_nonneg.mpr hm).posSemidef
  obtain ⟨C, hYC, hC⟩ := rectangular_douglas Y X 1 zero_le_one (by simpa using hYX)
  have hp := sqrtVector_partialTraceRight P hP
  have hq := sqrtVector_partialTraceRight Q hQ
  refine ⟨Matrix.vec Xᵀ, Matrix.vec Yᵀ, Cᵀ, hp, hq, ?_, ?_, ?_, ?_⟩
  · exact norm_sq_eq_traceNorm_of_marginal (Matrix.vec Xᵀ) hP hp
  · exact norm_sq_eq_traceNorm_of_marginal (Matrix.vec Yᵀ) hQ hq
  · rw [Matrix.l2_opNorm_toEuclideanCLM, ← Matrix.l2_opNorm_conjTranspose Cᵀ,
      ← Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    -- The adjoint of the transpose acts by conjugating the input and output of C.
    let z' : EuclideanSpace ℂ (A × (R × A)) := WithLp.toLp 2 (star z.ofLp)
    have norm_conj (v : A × (R × A) → ℂ) :
        ‖(WithLp.toLp 2 (star v) : EuclideanSpace ℂ (A × (R × A)))‖ =
          ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (A × (R × A)))‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [EuclideanSpace.norm_sq_eq, Pi.star_apply, norm_star]
    change ‖(WithLp.toLp 2 (Cᵀᴴ *ᵥ z.ofLp) : EuclideanSpace ℂ (A × (R × A)))‖ ≤
      1 * ‖z‖
    rw [Matrix.mulVec_conjTranspose, Matrix.vecMul_transpose, norm_conj]
    have hz' := hC z'
    change ‖(WithLp.toLp 2 (C *ᵥ star z.ofLp) : EuclideanSpace ℂ (A × (R × A)))‖ ≤
      Real.sqrt 1 * ‖z'‖ at hz'
    have hz : ‖z'‖ = ‖z‖ := norm_conj z.ofLp
    rwa [Real.sqrt_one, hz] at hz'
  · rw [Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.mul_one,
      ← Matrix.transpose_mul, hYC]

end D5.S3.Quantum.Divergence.CompleteHockeyStickPurificationGram

end

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearUpper

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm_of_posSemidef)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_posSemidef trace_partialTraceRight)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation krausColumn)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (E posTrace ptr amp act amp_entry amp_smul amp_sub_smul ptr_sub_smul ptr_amp)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (amp_mono)
open D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift
open D5.S3.Quantum.Divergence.CompleteHockeyStickPurificationGram (exists_purifications_of_ptr_le)
open D5.S3.Quantum.Divergence.CompleteHockeyStickOutputEffect
  (norm_environment_overlap_le norm_sq_eq_rtrace_marginal)
open RHLinalg (rtrace rtrace_sub)

universe ua ub ur ue uk

private def inputOrder (R : Type ur) (A : Type ua) (F : Type ue) :
    R × (A × F) ≃ R × (F × A) :=
  (Equiv.refl R).prodCongr (Equiv.prodComm A F)

private def outputOrder (R : Type ur) (B : Type ub) (F : Type ue) (κ : Type uk) :
    (R × B) × (F × κ) ≃ R × (F × (B × κ)) where
  toFun z := (z.1.1, z.2.1, z.1.2, z.2.2)
  invFun z := ((z.1, z.2.2.1), (z.2.1, z.2.2.2))
  left_inv := by rintro ⟨⟨r, b⟩, f, c⟩; rfl
  right_inv := by rintro ⟨r, f, b, c⟩; rfl

section MatrixBridge

variable {A : Type ua} {B : Type ub} {R : Type ur} {F : Type ue} {κ : Type uk}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype R] [DecidableEq R] [Fintype F] [DecidableEq F] [Fintype κ] [DecidableEq κ]

/-- The Stinespring column leaving the reference and purification indices untouched. -/
private def outputColumn (K : κ → Matrix B A ℂ) :
    Matrix ((R × B) × (F × κ)) (R × (A × F)) ℂ :=
  ((1 : Matrix R R ℂ) ⊗ₖ ((1 : Matrix F F ℂ) ⊗ₖ krausColumn K)).submatrix
    (outputOrder R B F κ) (inputOrder R A F)

omit [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype κ] [DecidableEq κ] in
private theorem outputColumn_mulVec_apply (K : κ → Matrix B A ℂ)
    (p : R × (A × F) → ℂ) (r : R) (b : B) (f : F) (c : κ) :
    (outputColumn K *ᵥ p) ((r, b), (f, c)) = ∑ i : A, K c b i * p (r, i, f) := by
  classical
  have hentry (s : R) (i : A) (g : F) :
      outputColumn K ((r, b), (f, c)) (s, i, g) =
        if r = s then (if f = g then K c b i else 0) else 0 := by
    change (1 : Matrix R R ℂ) r s * ((1 : Matrix F F ℂ) f g * K c b i) = _
    by_cases hrs : r = s <;> by_cases hfg : f = g <;> simp [Matrix.one_apply, hrs, hfg]
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    simp only [hentry, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · intro s _ hs
    apply Finset.sum_eq_zero
    rintro ⟨i, g⟩ _
    simp [hentry, Ne.symm hs]
  · simp

private theorem partialTraceRight_outputColumn
    (N : QuantumChannel A B) (p : R × (A × F) → ℂ) :
    let K := (actual_kraus_representation N).kraus
    let p' := outputColumn K *ᵥ p
    let p₀ := p ∘ Equiv.prodAssoc R A F
    partialTraceRight (Matrix.vecMulVec p' (star p')) =
      amp N (partialTraceRight (Matrix.vecMulVec p₀ (star p₀))) := by
  classical
  intro K p' p₀
  let Z := partialTraceRight (Matrix.vecMulVec p₀ (star p₀))
  change partialTraceRight (Matrix.vecMulVec p' (star p')) = amp N Z
  ext ⟨r, b⟩ ⟨s, d⟩
  rw [amp_entry]
  let T : Matrix A A ℂ := fun i j => Z (r, i) (s, j)
  change partialTraceRight (Matrix.vecMulVec p' (star p')) (r, b) (s, d) = act N T b d
  have hK : act N T = ∑ c, K c * T * (K c)ᴴ :=
    (actual_kraus_representation N).haction T
  rw [hK]
  simp only [partialTraceRight, Matrix.vecMulVec_apply, Pi.star_apply, p', Matrix.sum_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [outputColumn_mulVec_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    T, Z, partialTraceRight, Matrix.vecMulVec_apply, Pi.star_apply, p₀,
    Function.comp_apply, Equiv.prodAssoc_apply]
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset F))]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset A))]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro f _
  ring

omit [Fintype A] [DecidableEq A] [DecidableEq κ] in
private theorem outputColumn_compress (K : κ → Matrix B A ℂ)
    (W : Matrix (F × κ) (F × κ) ℂ) (U : Matrix (A × F) (A × F) ℂ)
    (hW : amplifiedComplementCompression (krausColumn K) W =
      Matrix.reindex (Equiv.prodComm A F) (Equiv.prodComm A F) U) :
    (outputColumn (R := R) (F := F) K)ᴴ * ((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ W) *
      outputColumn (R := R) (F := F) K = (1 : Matrix R R ℂ) ⊗ₖ U := by
  classical
  let e := outputOrder R B F κ
  let i := inputOrder R A F
  let o := referenceOutputOrder B F κ
  let H := Matrix.reindex o o ((1 : Matrix B B ℂ) ⊗ₖ W)
  let V := (1 : Matrix F F ℂ) ⊗ₖ krausColumn K
  have henv : (1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ W =
      ((1 : Matrix R R ℂ) ⊗ₖ H).submatrix e e := by
    rw [← Matrix.one_kronecker_one (m := R) (n := B)]
    ext ⟨⟨r, b⟩, f, c⟩ ⟨⟨s, d⟩, g, k⟩
    change ((1 : Matrix R R ℂ) r s * (1 : Matrix B B ℂ) b d) * W (f, c) (g, k) =
      (1 : Matrix R R ℂ) r s * ((1 : Matrix B B ℂ) b d * W (f, c) (g, k))
    exact mul_assoc _ _ _
  change (((1 : Matrix R R ℂ) ⊗ₖ V).submatrix e i)ᴴ *
    ((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ W) *
    ((1 : Matrix R R ℂ) ⊗ₖ V).submatrix e i = _
  rw [henv, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ _ e,
    Matrix.submatrix_mul_equiv _ _ _ e, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul]
  change ((1 : Matrix R R ℂ) ⊗ₖ amplifiedComplementCompression (krausColumn K) W).submatrix
    i i = _
  rw [hW]
  ext ⟨r, a, f⟩ ⟨s, b, g⟩
  rfl

omit [DecidableEq A] [DecidableEq κ] in
private theorem outputColumn_overlap (K : κ → Matrix B A ℂ)
    (W : Matrix (F × κ) (F × κ) ℂ) (U : Matrix (A × F) (A × F) ℂ)
    (hW : amplifiedComplementCompression (krausColumn K) W =
      Matrix.reindex (Equiv.prodComm A F) (Equiv.prodComm A F) U)
    (p q : R × (A × F) → ℂ) (hpq : p = ((1 : Matrix R R ℂ) ⊗ₖ U) *ᵥ q) (z : ℂ) :
    let V := outputColumn K
    let p' := V *ᵥ p
    let q' := V *ᵥ q
    star p' ⬝ᵥ (((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ (z • W)) *ᵥ q') =
      z * (‖(WithLp.toLp 2 p : EuclideanSpace ℂ (R × (A × F)))‖ : ℂ) ^ 2 := by
  intro V p' q'
  let H := (1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ (z • W)
  have hcomp : Vᴴ * H * V = z • ((1 : Matrix R R ℂ) ⊗ₖ U) := by
    change Vᴴ * ((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ (z • W)) * V = _
    rw [Matrix.kronecker_smul, Matrix.mul_smul, Matrix.smul_mul,
      outputColumn_compress K W U hW]
  change star (V *ᵥ p) ⬝ᵥ (H *ᵥ (V *ᵥ q)) = _
  calc
    _ = star p ⬝ᵥ ((Vᴴ * H * V) *ᵥ q) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        dotProduct_mulVec (star p) Vᴴ, Matrix.vecMul_conjTranspose, star_star]
    _ = z * (star p ⬝ᵥ p) := by
      rw [hcomp, Matrix.smul_mulVec, ← hpq, dotProduct_smul, smul_eq_mul]
    _ = _ := by
      congr 1
      rw [dotProduct_comm]
      exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
        (WithLp.toLp 2 p : EuclideanSpace ℂ (R × (A × F)))

end MatrixBridge

/-- Use the output-effect supplier on finite enumerations of both index types. -/
private theorem environment_overlap_le {S : Type ub} {G : Type ue}
    [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    (p q : S × G → ℂ) (W : Matrix G G ℂ) (hW : ‖W‖ ≤ 1)
    (M : Matrix S S ℂ) (hM : 0 ≤ M) (hI : M ≤ 1) :
    let P := partialTraceRight (Matrix.vecMulVec p (star p))
    let Q := partialTraceRight (Matrix.vecMulVec q (star q))
    ‖star p ⬝ᵥ (((1 : Matrix S S ℂ) ⊗ₖ W) *ᵥ q)‖ ≤
      Real.sqrt ((rtrace P + rtrace Q) * (rtrace P - rtrace (M * P) + rtrace (M * Q))) := by
  classical
  let e := Fintype.equivFin S
  let f := Fintype.equivFin G
  let g := e.prodCongr f
  let p' := p ∘ g.symm
  let q' := q ∘ g.symm
  let W' := Matrix.reindex f f W
  let M' := M.submatrix e.symm e.symm
  let H := (1 : Matrix S S ℂ) ⊗ₖ W
  let H' := (1 : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) ℂ) ⊗ₖ W'
  have hH : H' = H.submatrix g.symm g.symm := by
    ext ⟨i, k⟩ ⟨j, l⟩
    change (1 : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) ℂ) i j *
      W (f.symm k) (f.symm l) = (1 : Matrix S S ℂ) (e.symm i) (e.symm j) *
      W (f.symm k) (f.symm l)
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have hdot : star p' ⬝ᵥ (H' *ᵥ q') = star p ⬝ᵥ (H *ᵥ q) := by
    have hq : q' ∘ g = q := by
      funext x
      simp [q', Function.comp_apply]
    rw [hH, Matrix.submatrix_mulVec_equiv]
    change star p' ⬝ᵥ ((H *ᵥ (q' ∘ g)) ∘ g.symm) = _
    rw [hq]
    change (∑ i, star (p (g.symm i)) * (H *ᵥ q) (g.symm i)) = _
    exact g.symm.sum_comp (fun i => star (p i) * (H *ᵥ q) i)
  have hred (v : S × G → ℂ) :
      partialTraceRight (Matrix.vecMulVec (v ∘ g.symm) (star (v ∘ g.symm))) =
        (partialTraceRight (Matrix.vecMulVec v (star v))).submatrix e.symm e.symm := by
    ext i j
    change (∑ k, v (e.symm i, f.symm k) * star (v (e.symm j, f.symm k))) =
      ∑ k, v (e.symm i, k) * star (v (e.symm j, k))
    exact f.symm.sum_comp (fun k : G => v (e.symm i, k) * star (v (e.symm j, k)))
  have htrace (T : Matrix S S ℂ) : rtrace (T.submatrix e.symm e.symm) = rtrace T := by
    unfold rtrace
    apply congrArg (RCLike.re : ℂ → ℝ)
    exact e.symm.sum_comp (fun i => T i i)
  have hnorm (v : S × G → ℂ) :
      ‖(WithLp.toLp 2 (v ∘ g.symm) : EuclideanSpace ℂ
        (Fin (Fintype.card S) × Fin (Fintype.card G)))‖ ^ 2 =
        rtrace (partialTraceRight (Matrix.vecMulVec v (star v))) := by
    rw [norm_sq_eq_rtrace_marginal, hred, htrace]
  have hscore (v : S × G → ℂ) :
      rtrace (M' * partialTraceRight (Matrix.vecMulVec (v ∘ g.symm) (star (v ∘ g.symm)))) =
        rtrace (M * partialTraceRight (Matrix.vecMulVec v (star v))) := by
    rw [hred]
    change rtrace (M.submatrix e.symm e.symm *
      (partialTraceRight (Matrix.vecMulVec v (star v))).submatrix e.symm e.symm) = _
    rw [Matrix.submatrix_mul_equiv _ _ _ e.symm, htrace]
  have hW' : ‖Matrix.toEuclideanCLM (n := Fin (Fintype.card G)) (𝕜 := ℂ) W'‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact (norm_reindex f W).le.trans hW
  have hM' : 0 ≤ M' := (hM.posSemidef.submatrix e.symm).nonneg
  have hI' : M' ≤ 1 := by
    apply sub_nonneg.mp
    have h : 0 ≤ (1 - M).submatrix e.symm e.symm :=
      ((sub_nonneg.mpr hI).posSemidef.submatrix e.symm).nonneg
    rw [Matrix.submatrix_sub] at h
    change 0 ≤ (1 : Matrix S S ℂ).submatrix e.symm e.symm - M' at h
    rwa [Matrix.submatrix_one_equiv] at h
  obtain ⟨h₁, h₂⟩ := norm_environment_overlap_le p' q' W' hW' M' hM' hI'
  have h := h₁.trans h₂
  change ‖inner ℂ (WithLp.toLp 2 p')
      (Matrix.toEuclideanCLM (n := Fin (Fintype.card S) × Fin (Fintype.card G)) (𝕜 := ℂ)
        H' (WithLp.toLp 2 q'))‖ ≤ _ at h
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp,
    dotProduct_comm (H' *ᵥ q') (star p'), hdot] at h
  simpa only [p', q', hnorm, hscore] using h

private theorem exists_effect_attaining_posTrace {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℂ) (hT : T.IsHermitian) :
    ∃ M : Matrix n n ℂ, 0 ≤ M ∧ M ≤ 1 ∧ rtrace (M * T) = posTrace T := by
  classical
  let d : n → ℂ := fun i => if 0 < hT.eigenvalues i then 1 else 0
  let U : Matrix n n ℂ := ↑hT.eigenvectorUnitary
  let M := U * Matrix.diagonal d * Uᴴ
  have hU : Uᴴ * U = 1 := hT.eigenvectorUnitary.2.1
  have hUU : U * Uᴴ = 1 := hT.eigenvectorUnitary.2.2
  have hd : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    by_cases hi : 0 < hT.eigenvalues i <;> simp [d, hi]
  have hId : (1 - Matrix.diagonal d).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    by_cases hi : 0 < hT.eigenvalues i <;> simp [d, hi]
  have hIM : 1 - M = U * (1 - Matrix.diagonal d) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUU]
  have hTdiag : T = U * Matrix.diagonal (Complex.ofReal ∘ hT.eigenvalues) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U,
      RCLike.ofReal_eq_complex_ofReal] using hT.spectral_theorem
  have hTpos : T⁺ = U * Matrix.diagonal
      (Complex.ofReal ∘ (fun x : ℝ => x⁺) ∘ hT.eigenvalues) * Uᴴ := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp), hT.cfc_eq]
    rfl
  have hDiag : Matrix.diagonal d * Matrix.diagonal (Complex.ofReal ∘ hT.eigenvalues) =
      Matrix.diagonal (Complex.ofReal ∘ (fun x : ℝ => x⁺) ∘ hT.eigenvalues) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : 0 < hT.eigenvalues i
    · simp [Function.comp_apply, d, hi, posPart_eq_self.mpr hi.le]
    · simp [Function.comp_apply, d, hi, posPart_eq_zero.mpr (le_of_not_gt hi)]
  have hMT : M * T = T⁺ := by
    rw [hTpos]
    conv_lhs => rw [hTdiag]
    simp only [M, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal d), hDiag]
  refine ⟨M, (hd.mul_mul_conjTranspose_same U).nonneg, sub_nonneg.mp ?_, ?_⟩
  · rw [hIM]
    exact (hId.mul_mul_conjTranspose_same U).nonneg
  · change rtrace (M * T) = rtrace T⁺
    rw [hMT]

private theorem nonlinear_bound_of_overlap {C x y γ : ℝ} (hC : 0 < C) (hx : 0 < x)
    (hγ : 1 ≤ γ) (h : x / C ≤ Real.sqrt ((2 * x + γ - 1) * (x - y))) :
    y ≤ x - x ^ 2 / (C ^ 2 * (2 * x + γ - 1)) := by
  have hn : 0 ≤ (2 * x + γ - 1) * (x - y) := by
    by_contra! hn
    rw [Real.sqrt_eq_zero_of_nonpos hn.le] at h
    exact (not_le_of_gt (div_pos hx hC)) h
  have hs := (sq_le_sq₀ (div_nonneg hx.le hC.le) (Real.sqrt_nonneg _)).2 h
  rw [div_pow, Real.sq_sqrt hn] at hs
  have hC2 : 0 < C ^ 2 := by positivity
  have hd : 0 < 2 * x + γ - 1 := by linarith
  have hmul := (div_le_iff₀ hC2).mp hs
  have hfrac : x ^ 2 / (C ^ 2 * (2 * x + γ - 1)) ≤ x - y := by
    apply (div_le_iff₀ (mul_pos hC2 hd)).mpr
    calc
      x ^ 2 ≤ (2 * x + γ - 1) * (x - y) * C ^ 2 := hmul
      _ = (x - y) * (C ^ 2 * (2 * x + γ - 1)) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- A full span of canonical Kraus products supplies one nonlinear bound for all finite
reference systems, equal-reference density pairs, and parameters at least one. -/
theorem exists_uniform_nonlinear_upper {A : Type ua} {B : Type ub}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B)
    (hspan : Submodule.span ℂ
      (Set.range fun p : (Fin (Fintype.card B) × Fin (Fintype.card A)) ×
          (Fin (Fintype.card B) × Fin (Fintype.card A)) =>
        ((actual_kraus_representation N).kraus p.1)ᴴ *
          (actual_kraus_representation N).kraus p.2) = ⊤) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (R : Type ur) [Fintype R] [DecidableEq R] (γ : ℝ) (hγ : 1 ≤ γ)
        (ρ σ : DensityState (R × A)),
        let ρ₀ := (toMState ρ).m
        let σ₀ := (toMState σ).m
        ptr ρ₀ = ptr σ₀ →
        let x := E γ ρ₀ σ₀
        0 < x →
        E γ (amp N ρ₀) (amp N σ₀) ≤ x - x ^ 2 / (C ^ 2 * (2 * x + γ - 1)) := by
  classical
  obtain ⟨C, hC, hLift⟩ := exists_uniform_complement_lift_of_full_span.{ua, ub, 0, max ua ur}
    (actual_kraus_representation N).kraus hspan
  refine ⟨C, hC, ?_⟩
  intro R _ _ γ hγ ρ σ ρ₀ σ₀ hm x hx
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let D := ρ₀ - γ • σ₀
  let P := D⁺
  let Q := D⁻
  have hρ : ρ₀.PosSemidef := (toMState ρ).psd
  have hσ : σ₀.PosSemidef := (toMState σ).psd
  have hρt : ρ₀.trace = 1 := (toMState ρ).tr'
  have hσt : σ₀.trace = 1 := (toMState σ).tr'
  have hD : P - Q = D :=
    CFC.posPart_sub_negPart D (hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ)))
  have hP : P.PosSemidef := (CFC.posPart_nonneg D).posSemidef
  have hQ : Q.PosSemidef := (CFC.negPart_nonneg D).posSemidef
  have hptr : ptr P ≤ ptr Q := by
    have hPQ : ptr P - ptr Q = ptr σ₀ - γ • ptr σ₀ := calc
      _ = ptr (P - Q) := by
        simpa only [one_smul] using (ptr_sub_smul 1 P Q).symm
      _ = _ := by
        rw [hD]
        change ptr (ρ₀ - γ • σ₀) = _
        rw [ptr_sub_smul, hm]
    apply sub_nonpos.mp
    rw [hPQ]
    have hσptr : (ptr σ₀).PosSemidef := partialTraceRight_posSemidef hσ
    have h := (hσptr.smul (sub_nonneg.mpr hγ)).nonneg
    rw [sub_smul, one_smul] at h
    exact sub_nonpos.mpr (sub_nonneg.mp h)
  have hPt : rtrace P = x := rfl
  have hQt : rtrace Q = x + γ - 1 := by
    have hDt : rtrace D = 1 - γ := by
      change (ρ₀ - γ • σ₀).trace.re = _
      rw [Matrix.trace_sub, Matrix.trace_smul, hρt, hσt,
        Complex.real_smul, mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    have ht := congrArg rtrace hD
    rw [rtrace_sub, hPt, hDt] at ht
    linarith
  obtain ⟨p, q, U, hp, hq, hpn, _, hU, hpq⟩ := exists_purifications_of_ptr_le P Q hP hQ hptr
  let F := R × A
  let U' := Matrix.reindex (Equiv.prodComm A F) (Equiv.prodComm A F) U
  have hU' : ‖U'‖ ≤ 1 := by
    change ‖Matrix.reindex (Equiv.prodComm A F) (Equiv.prodComm A F) U‖ ≤ 1
    rw [norm_reindex, ← Matrix.l2_opNorm_toEuclideanCLM]
    exact hU
  obtain ⟨W, hW, hWn⟩ := hLift F U' hU'
  let z : ℂ := ((C⁻¹ : ℝ) : ℂ)
  let Ws := z • W
  have hWs : ‖Ws‖ ≤ 1 := calc
    ‖Ws‖ = C⁻¹ * ‖W‖ := by
      change ‖((C⁻¹ : ℝ) : ℂ) • W‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hC0.le)]
    _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hWn (inv_nonneg.mpr hC0.le)
    _ = 1 := inv_mul_cancel₀ hC0.ne'
  let K := (actual_kraus_representation N).kraus
  let p' := outputColumn K *ᵥ p
  let q' := outputColumn K *ᵥ q
  have hp' : partialTraceRight (Matrix.vecMulVec p' (star p')) = amp N P :=
    (partialTraceRight_outputColumn N p).trans (congrArg (amp N) hp)
  have hq' : partialTraceRight (Matrix.vecMulVec q' (star q')) = amp N Q :=
    (partialTraceRight_outputColumn N q).trans (congrArg (amp N) hq)
  have hpn' : ‖(WithLp.toLp 2 p : EuclideanSpace ℂ (R × (A × F)))‖ ^ 2 = x := by
    rw [hpn, ← hPt]
    have h := congrArg (RCLike.re : ℂ → ℝ) (traceNorm_of_posSemidef hP)
    simpa only [rtrace, RCLike.ofReal_re] using h
  have hoverlap :
      ‖star p' ⬝ᵥ (((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ Ws) *ᵥ q')‖ = x / C := by
    have h := outputColumn_overlap K W U hW p q hpq z
    change star p' ⬝ᵥ (((1 : Matrix (R × B) (R × B) ℂ) ⊗ₖ Ws) *ᵥ q') = _ at h
    rw [h, ← Complex.ofReal_pow, hpn']
    change ‖((C⁻¹ : ℝ) : ℂ) * (x : ℂ)‖ = x / C
    rw [← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hC0.le) hx.le), div_eq_mul_inv, mul_comm]
  let T := amp N ρ₀ - γ • amp N σ₀
  have hT : T = amp N P - amp N Q := calc
    _ = amp N D := (amp_sub_smul N γ ρ₀ σ₀).symm
    _ = amp N (P - Q) := congrArg (amp N) hD.symm
    _ = _ := by simpa only [one_smul] using (amp_sub_smul N 1 P Q)
  have hAmpPos (X : Matrix (R × A) (R × A) ℂ) (hX : X.PosSemidef) :
      (amp N X).PosSemidef := by
    have h := amp_mono N hX.nonneg
    have hzero : amp N (0 : Matrix (R × A) (R × A) ℂ) = 0 := by
      simpa only [zero_smul] using amp_smul N 0 X
    rw [hzero] at h
    exact h.posSemidef
  have hTh : T.IsHermitian :=
    (hAmpPos ρ₀ hρ).isHermitian.sub ((hAmpPos σ₀ hσ).isHermitian.smul (IsSelfAdjoint.all γ))
  obtain ⟨M, hM, hI, hMT⟩ := exists_effect_attaining_posTrace T hTh
  let y := E γ (amp N ρ₀) (amp N σ₀)
  have hScore : rtrace (M * amp N P) - rtrace (M * amp N Q) = y := by
    change rtrace (M * amp N P) - rtrace (M * amp N Q) = posTrace T
    rw [← rtrace_sub, ← Matrix.mul_sub, ← hT, hMT]
  have hTraceAmp (X : Matrix (R × A) (R × A) ℂ) : rtrace (amp N X) = rtrace X := by
    unfold rtrace
    apply congrArg (RCLike.re : ℂ → ℝ)
    rw [← trace_partialTraceRight (amp N X)]
    change (ptr (amp N X)).trace = X.trace
    rw [ptr_amp]
    exact trace_partialTraceRight X
  have h := environment_overlap_le p' q' Ws hWs M hM hI
  dsimp only at h
  rw [hp', hq', hoverlap, hTraceAmp P, hTraceAmp Q, hPt, hQt] at h
  have hsum : x + (x + γ - 1) = 2 * x + γ - 1 := by ring
  have hloss : x - rtrace (M * amp N P) + rtrace (M * amp N Q) = x - y := by
    linarith [hScore]
  rw [hsum, hloss] at h
  exact nonlinear_bound_of_overlap hC0 hx hγ h


end D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearUpper
