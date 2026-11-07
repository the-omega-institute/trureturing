/- GID: D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation
   generality: I
   mirror-B: D5/B/S3/Quantum/GeorgeTomamichelMaximalCorrelation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Geometric maximal correlation one forces arithmetic maximal correlation one. -/
import D5.S3.Quantum.FiniteCorrelationRecovery
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.FixedPointProjection
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

/-!
admission_basis: open-problem-resolution (#19997; Proved)
escape_witness: none
The public proposition keeps the prescribed partial sums and mean operators
inline. Proofs use the existing partialTraceRight and partialTraceLeft owners
through definitional equality, without duplicate marginal declarations.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22403
-/

open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
section GeorgeTomamichelMaximalCorrelation

/-! Binding conventions for I. George and M. Tomamichel, "A Unified Approach to Quantum Contraction and Correlation
Coefficients", arXiv:2505.15281v3 (29 March 2026).

* Section II: `J_{f,σ} = f(L_σ R_σ⁻¹) R_σ` and `⟨X, Y⟩_{f,σ} = ⟨X, J_{f,σ}(Y)⟩` (15), with the arithmetic mean
  `f_AM(x) = (x + 1)/2`, so `J_{AM,σ}(Y) = (σY + Yσ)/2`, and the geometric mean `f_GM(x) = √x`, so
  `J_{GM,σ}(Y) = σ^{1/2} Y σ^{1/2}`.
* Definition 24, Eq. (54): `µ_f(A : B)_ρ := max |Tr[X ⊗ Y* ρ_AB]|` subject to `⟨1, X⟩_{f,ρ_A} = ⟨1, Y⟩_{f,ρ_B} = 0` and
  `⟨X, X⟩_{f,ρ_A} = ⟨Y, Y⟩_{f,ρ_B} = 1`, over `X ∈ Herm(A)`, `Y ∈ Herm(B)`; the linear constraints are
  `Tr[ρ_A X] = 0 = Tr[ρ_B Y]` (Proposition 17).
* Section VII: "Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?" -/

namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation

open _root_.Matrix MatrixOrder ComplexOrder

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Eq. (54) for a given `J`: the feasible correlation values `|Tr[(X ⊗ Y) ρ]|`. -/
def correlationValues (J : ∀ {c : Type} [Fintype c] [DecidableEq c], Matrix c c ℂ → Matrix c c ℂ → Matrix c c ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) : Set ℝ :=
  {r | ∃ X : Matrix a a ℂ, ∃ Y : Matrix b b ℂ, X.IsHermitian ∧ Y.IsHermitian ∧
    (Matrix.of (fun i j => ∑ k, ρ (i, k) (j, k)) * X).trace = 0 ∧ (Matrix.of (fun k l => ∑ i, ρ (i, k) (i, l)) * Y).trace = 0 ∧
    (Xᴴ * J ((fun i j => ∑ k, ρ (i, k) (j, k))) X).trace = 1 ∧ (Yᴴ * J ((fun k l => ∑ i, ρ (i, k) (i, l))) Y).trace = 1 ∧
    r = ‖(kroneckerMap (· * ·) X Yᴴ * ρ).trace‖}

/-- `µ_AM(A : B)_ρ`. -/
noncomputable def muAM (ρ : Matrix (a × b) (a × b) ℂ) : ℝ := sSup (correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => (1 / 2 : ℂ) • (σ * Y + Y * σ)) ρ)

/-- `µ_GM(A : B)_ρ`. -/
noncomputable def muGM (ρ : Matrix (a × b) (a × b) ℂ) : ℝ := sSup (correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ρ)

/-- Section VII, first question, answered in the negative: for every state, `µ_GM = 1` forces `µ_AM = 1`. -/
def claim : Prop :=
  ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ),
    ρ.PosSemidef → ρ.trace = 1 → muGM ρ = 1 → muAM ρ = 1

end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
end GeorgeTomamichelMaximalCorrelation
section generic_node
noncomputable section
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
section r3_hilbert_schmidt
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt
open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
private def vec {n : Type} [Fintype n] : Matrix n n ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card n) × Fin (Fintype.card n))) :=
  (Matrix.reindexLinearEquiv ℂ ℂ (Fintype.equivFin n) (Fintype.equivFin n)).trans
    (vectorize (Fintype.card n))
variable {a b s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
private lemma pairing (X Y : Matrix a a ℂ) : inner ℂ (vec X) (vec Y) = (Xᴴ * Y).trace := by
  change inner ℂ (vectorize (Fintype.card a) (X.submatrix (Fintype.equivFin a).symm (Fintype.equivFin a).symm))
    (vectorize (Fintype.card a) (Y.submatrix (Fintype.equivFin a).symm (Fintype.equivFin a).symm)) = _
  rw [matrix_pairing, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Fintype.equivFin a).symm.sum_comp (fun i : a => (Xᴴ * Y) i i)
@[simp] private lemma liftVec (L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (X : Matrix a a ℂ) :
    ((LinearEquiv.arrowCongr (vec (n := a)) (vec (n := b))) L).toContinuousLinearMap (vec X) = vec (L X) := by
  simp only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.arrowCongr_apply,
    LinearEquiv.symm_apply_apply]
private lemma normSq (X : Matrix a a ℂ) : ((‖vec X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
  calc
    _ = inner ℂ (vec X) (vec X) := by
      simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (vec X)).symm
    _ = _ := pairing X X
private lemma rawApply (K : s → Matrix b a ℂ) (X : Matrix a a ℂ) :
    (MatrixMap.of_kraus (K) (K)) X = ∑ i, K i * X * (K i)ᴴ := by
  simp only [ MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
private lemma rawStar (K : s → Matrix b a ℂ) (X : Matrix a a ℂ) :
    ((MatrixMap.of_kraus K K) X)ᴴ = (MatrixMap.of_kraus K K) Xᴴ := by
  simpa only [rawApply] using D5.S3.Quantum.FixedPointProjection.Kraus.rawStar K X
private lemma rawPair (K : s → Matrix b a ℂ) (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((MatrixMap.of_kraus K K) X * Y).trace =
      (X * (MatrixMap.of_kraus (fun i => (K i)ᴴ) (fun i => (K i)ᴴ)) Y).trace := by
  simpa only [rawApply, Matrix.conjTranspose_conjTranspose] using
    D5.S3.Quantum.FixedPointProjection.Kraus.rawPair K X Y
private lemma rawNonneg (K : s → Matrix b a ℂ) (X : Matrix a a ℂ) (hX : 0 ≤ X) :
    0 ≤ (MatrixMap.of_kraus (K) (K)) X := by
  rw [rawApply]
  exact (Matrix.posSemidef_sum _ fun i _ =>
    (Matrix.nonneg_iff_posSemidef.mp hX).mul_mul_conjTranspose_same (K i)).nonneg
private lemma liftRawAdjoint (K : s → Matrix b a ℂ) :
    (((LinearEquiv.arrowCongr (vec (n := a)) (vec (n := b))) (MatrixMap.of_kraus K K)).toContinuousLinearMap :
      (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))) →L[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card b) × Fin (Fintype.card b)))).adjoint =
    (((LinearEquiv.arrowCongr (vec (n := b)) (vec (n := a)))
      (MatrixMap.of_kraus (fun i => (K i)ᴴ) (fun i => (K i)ᴴ))).toContinuousLinearMap :
      (EuclideanSpace ℂ (Fin (Fintype.card b) × Fin (Fintype.card b))) →L[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a)))) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  obtain ⟨X,rfl⟩ := (vec (n := a)).surjective x
  obtain ⟨Y,rfl⟩ := (vec (n := b)).surjective y
  rw [ContinuousLinearMap.adjoint_inner_right, liftVec, liftVec, pairing, pairing,
    rawStar, rawPair]
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt
end r3_hilbert_schmidt
section r3_quarter_root
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
variable {n : Type} [Fintype n] [DecidableEq n]
private lemma sqrtTranspose (S : Matrix n n ℂ) (hS : S.PosSemidef) :
    CFC.sqrt Sᵀ = (CFC.sqrt S)ᵀ := by
  apply CFC.sqrt_unique
  · rw [← Matrix.transpose_mul, CFC.sqrt_mul_sqrt_self S hS.nonneg]
  · exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).transpose.nonneg
private lemma quarterRootHermitian (S : Matrix n n ℂ) : ((CFC.sqrt (CFC.sqrt S))).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt S))).isHermitian
private lemma quarterRootSq (S : Matrix n n ℂ) : (CFC.sqrt (CFC.sqrt S)) * (CFC.sqrt (CFC.sqrt S)) = CFC.sqrt S :=
  CFC.sqrt_mul_sqrt_self (CFC.sqrt S) (CFC.sqrt_nonneg S)
private lemma quarterRootUnit (S : Matrix n n ℂ) (hS : S.PosDef) : IsUnit ((CFC.sqrt (CFC.sqrt S))) := by
  apply (CFC.isUnit_sqrt_iff (CFC.sqrt S) (CFC.sqrt_nonneg S)).mpr
  exact (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
private lemma quarterRootInvMul (S : Matrix n n ℂ) (hS : S.PosDef) :
    ((CFC.sqrt (CFC.sqrt S)))⁻¹ * (CFC.sqrt (CFC.sqrt S)) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (quarterRootUnit S hS))
private lemma quarterRootMulInv (S : Matrix n n ℂ) (hS : S.PosDef) :
    (CFC.sqrt (CFC.sqrt S)) * ((CFC.sqrt (CFC.sqrt S)))⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (quarterRootUnit S hS))
private lemma quarterRootInvSq (S : Matrix n n ℂ) :
    ((CFC.sqrt (CFC.sqrt S)))⁻¹ * ((CFC.sqrt (CFC.sqrt S)))⁻¹ = (CFC.sqrt S)⁻¹ := by
  rw [← Matrix.mul_inv_rev, quarterRootSq]
private lemma quarterRootSqrtInvLeft (S : Matrix n n ℂ) (hS : S.PosDef) :
    (CFC.sqrt S)⁻¹ * (CFC.sqrt (CFC.sqrt S)) = ((CFC.sqrt (CFC.sqrt S)))⁻¹ := by
  rw [← quarterRootInvSq S, Matrix.mul_assoc, quarterRootInvMul S hS, Matrix.mul_one]
private lemma quarterRootSqrtInvRight (S : Matrix n n ℂ) (hS : S.PosDef) :
    (CFC.sqrt (CFC.sqrt S)) * (CFC.sqrt S)⁻¹ = ((CFC.sqrt (CFC.sqrt S)))⁻¹ := by
  rw [← quarterRootInvSq S, ← Matrix.mul_assoc, quarterRootMulInv S hS, Matrix.one_mul]
private lemma sqrtNormalize (S : Matrix n n ℂ) (hS : S.PosDef) :
    (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ = 1 := by
  have hu : IsUnit (CFC.sqrt S) := (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
  have hleft := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hright := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  calc
    _ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S)⁻¹ :=
      congrArg (fun Z : Matrix n n ℂ => (CFC.sqrt S)⁻¹ * Z * (CFC.sqrt S)⁻¹)
        (CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg).symm
    _ = ((CFC.sqrt S)⁻¹ * CFC.sqrt S) * (CFC.sqrt S * (CFC.sqrt S)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hleft, hright, Matrix.one_mul]
private lemma quarterRootSqrtSandwich (S : Matrix n n ℂ) (hS : S.PosSemidef) :
    (CFC.sqrt (CFC.sqrt S)) * CFC.sqrt S * (CFC.sqrt (CFC.sqrt S)) = S := by
  calc
    _ = ((CFC.sqrt (CFC.sqrt S)) * (CFC.sqrt (CFC.sqrt S))) * ((CFC.sqrt (CFC.sqrt S)) * (CFC.sqrt (CFC.sqrt S))) := by
      calc
        _ = (CFC.sqrt (CFC.sqrt S)) * ((CFC.sqrt (CFC.sqrt S)) * (CFC.sqrt (CFC.sqrt S))) * (CFC.sqrt (CFC.sqrt S)) :=
          congrArg (fun Z => (CFC.sqrt (CFC.sqrt S)) * Z * (CFC.sqrt (CFC.sqrt S))) (quarterRootSq S).symm
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = S := by rw [quarterRootSq S, CFC.sqrt_mul_sqrt_self S hS.nonneg]
private lemma quarterRootQuadratic (S X : Matrix n n ℂ) :
    (((CFC.sqrt (CFC.sqrt S)) * X * (CFC.sqrt (CFC.sqrt S)))ᴴ * ((CFC.sqrt (CFC.sqrt S)) * X * (CFC.sqrt (CFC.sqrt S)))).trace =
      (Xᴴ * (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) S X).trace := by
  let A := (CFC.sqrt (CFC.sqrt S))
  have hA : Aᴴ = A := (quarterRootHermitian S).eq
  change ((A * X * A)ᴴ * (A * X * A)).trace = _
  calc
    _ = (Xᴴ * (A * A) * X * (A * A)).trace := by
      simpa only [Matrix.conjTranspose_mul, hA, Matrix.mul_assoc] using
        Matrix.trace_mul_comm A (Xᴴ * A * A * X * A)
    _ = _ := by rw [quarterRootSq]; simp only [ Matrix.mul_assoc]
private lemma quarterRootCenter (S X : Matrix n n ℂ) (hS : S.PosSemidef) :
    (CFC.sqrt S * ((CFC.sqrt (CFC.sqrt S)) * X * (CFC.sqrt (CFC.sqrt S)))).trace = (S * X).trace := by
  let A := (CFC.sqrt (CFC.sqrt S))
  have hASA : A * CFC.sqrt S * A = S := quarterRootSqrtSandwich S hS
  calc
    _ = ((A * CFC.sqrt S * A) * X).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (CFC.sqrt S * A) X A
    _ = _ := by rw [hASA]
private lemma gmTraceTranspose (S X : Matrix n n ℂ) (hS : S.PosSemidef) (hX : X.IsHermitian) :
    ((Xᵀ)ᴴ * (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) Sᵀ Xᵀ).trace = (Xᴴ * (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) S X).trace := by
  rw [hX.transpose.eq, hX.eq]
  simp only [ sqrtTranspose S hS]
  calc
    _ = ((CFC.sqrt S * X * CFC.sqrt S * X)ᵀ).trace := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (CFC.sqrt S * X * CFC.sqrt S * X).trace := Matrix.trace_transpose _
    _ = _ := by simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm (CFC.sqrt S) (X * CFC.sqrt S * X)
private lemma centerTranspose (S X : Matrix n n ℂ) : (Sᵀ * Xᵀ).trace = (S * X).trace := by
  rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root
end r3_quarter_root
section r3_normalized_kraus
open _root_.Matrix MatrixOrder ComplexOrder
open scoped Matrix.Norms.L2Operator
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Normalized
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root
variable {a b s : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
private def sandwichEquiv (A AI : Matrix a a ℂ) (hl : AI * A = 1) (hr : A * AI = 1) :
    Matrix a a ℂ ≃ₗ[ℂ] Matrix a a ℂ :=
  let u : (Matrix a a ℂ)ˣ := ⟨A, AI, hr, hl⟩
  (u.mulLeftLinearEquiv ℂ _).trans (u.mulRightLinearEquiv ℂ)
private lemma rawSandwich (K : s → Matrix b a ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (X : Matrix a a ℂ) :
    (MatrixMap.of_kraus ((fun i => B * K i * A)) ((fun i => B * K i * A))) X = B * (MatrixMap.of_kraus (K) (K)) (A * X * A) * B := by
  simp only [rawApply, Matrix.conjTranspose_mul, hA.eq, hB.eq,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
private def normalizedC (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ) :
    (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))) →L[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card b) × Fin (Fintype.card b))) := ((LinearEquiv.arrowCongr (vec (n := a)) (vec (n := b))) ((MatrixMap.of_kraus ((fun i => ((CFC.sqrt (CFC.sqrt τ)))⁻¹ * K i * ((CFC.sqrt (CFC.sqrt σ)))⁻¹)) ((fun i => ((CFC.sqrt (CFC.sqrt τ)))⁻¹ * K i * ((CFC.sqrt (CFC.sqrt σ)))⁻¹))))).toContinuousLinearMap
private lemma normalizedCVec (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (X : Matrix a a ℂ) : normalizedC K σ τ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X) =
      D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * (MatrixMap.of_kraus (K) (K)) (((CFC.sqrt (CFC.sqrt σ)))⁻¹ * X * ((CFC.sqrt (CFC.sqrt σ)))⁻¹) * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) := by
  rw [normalizedC, liftVec, rawSandwich K _ _ (quarterRootHermitian σ).inv
    (quarterRootHermitian τ).inv]
private lemma normalizedCAdjointVec (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (Y : Matrix b b ℂ) : (normalizedC K σ τ).adjoint (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec Y) =
      D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (((CFC.sqrt (CFC.sqrt σ)))⁻¹ * (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ)))
        (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * Y * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) * ((CFC.sqrt (CFC.sqrt σ)))⁻¹) := by
  rw [normalizedC, liftRawAdjoint, liftVec]
  have hh : (fun i : s => (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * K i * ((CFC.sqrt (CFC.sqrt σ)))⁻¹)ᴴ) =
      (fun i : s => ((CFC.sqrt (CFC.sqrt σ)))⁻¹ * (K i)ᴴ * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) := by
    funext i
    simp only [Matrix.conjTranspose_mul, (quarterRootHermitian σ).inv.eq,
      (quarterRootHermitian τ).inv.eq, Matrix.mul_assoc]
  rw [hh, rawSandwich _ _ _ (quarterRootHermitian τ).inv (quarterRootHermitian σ).inv]
private def recoveryComposite (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ) :
    Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ :=
  ((MatrixMap.of_kraus ((fun i => (K i)ᴴ * (CFC.sqrt τ)⁻¹)) ((fun i => (K i)ᴴ * (CFC.sqrt τ)⁻¹)))).comp ((MatrixMap.of_kraus ((fun i => K i * (CFC.sqrt σ)⁻¹)) ((fun i => K i * (CFC.sqrt σ)⁻¹))))
private lemma recoveryCompositeAction (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (X : Matrix a a ℂ) : recoveryComposite K σ τ X =
      (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) ((CFC.sqrt τ)⁻¹ *
        (MatrixMap.of_kraus (K) (K)) ((CFC.sqrt σ)⁻¹ * X * (CFC.sqrt σ)⁻¹) * (CFC.sqrt τ)⁻¹) := by
  have hσ : ((CFC.sqrt σ)⁻¹).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).isHermitian.inv
  have hτ : ((CFC.sqrt τ)⁻¹).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg τ)).isHermitian.inv
  have hE := rawSandwich K (CFC.sqrt σ)⁻¹ (1 : Matrix b b ℂ) hσ Matrix.isHermitian_one X
  have hR := rawSandwich (fun i => (K i)ᴴ) (CFC.sqrt τ)⁻¹ (1 : Matrix a a ℂ) hτ
    Matrix.isHermitian_one ((MatrixMap.of_kraus ((fun i => K i * (CFC.sqrt σ)⁻¹)) ((fun i => K i * (CFC.sqrt σ)⁻¹))) X)
  simp only [Matrix.one_mul, Matrix.mul_one] at hE hR
  exact hR.trans (congrArg (fun Z : Matrix b b ℂ => (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ)))
    ((CFC.sqrt τ)⁻¹ * Z * (CFC.sqrt τ)⁻¹)) hE)
private lemma recoveryCompositeNonneg (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (X : Matrix a a ℂ) (hX : 0 ≤ X) : 0 ≤ recoveryComposite K σ τ X :=
  rawNonneg _ _ (rawNonneg _ X hX)
private lemma recoveryCompositeFixed (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (hσ : σ.PosDef) (hτ : τ.PosDef) (hE : (MatrixMap.of_kraus (K) (K)) 1 = τ) (hD : (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) 1 = σ) :
    recoveryComposite K σ τ σ = σ := by
  rw [recoveryCompositeAction, sqrtNormalize σ hσ, hE, sqrtNormalize τ hτ, hD]
private def weightEquiv (σ : Matrix a a ℂ) (hσ : σ.PosDef) : (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))) ≃ₗ[ℂ] Matrix a a ℂ :=
  (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a)).symm.trans (sandwichEquiv ((CFC.sqrt (CFC.sqrt σ))) ((CFC.sqrt (CFC.sqrt σ)))⁻¹
    (quarterRootInvMul σ hσ) (quarterRootMulInv σ hσ))
private lemma weightEquivVec (σ : Matrix a a ℂ) (hσ : σ.PosDef) (X : Matrix a a ℂ) :
    weightEquiv σ hσ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X) = (CFC.sqrt (CFC.sqrt σ)) * X * (CFC.sqrt (CFC.sqrt σ)) := by
  change (CFC.sqrt (CFC.sqrt σ)) * ((D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a)).symm (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X)) * (CFC.sqrt (CFC.sqrt σ)) = _
  rw [LinearEquiv.symm_apply_apply]
private lemma normalizedSimilarity (K : s → Matrix b a ℂ) (σ : Matrix a a ℂ) (τ : Matrix b b ℂ)
    (hσ : σ.PosDef) : ∀ x : (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))),
      recoveryComposite K σ τ (weightEquiv σ hσ x) =
        weightEquiv σ hσ ((normalizedC K σ τ).adjoint (normalizedC K σ τ x)) := by
  intro x
  obtain ⟨X,rfl⟩ := (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a)).surjective x
  let Z := (MatrixMap.of_kraus (K) (K)) (((CFC.sqrt (CFC.sqrt σ)))⁻¹ * X * ((CFC.sqrt (CFC.sqrt σ)))⁻¹)
  let W := (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) ((CFC.sqrt τ)⁻¹ * Z * (CFC.sqrt τ)⁻¹)
  have hc : (CFC.sqrt σ)⁻¹ * ((CFC.sqrt (CFC.sqrt σ)) * X * (CFC.sqrt (CFC.sqrt σ))) * (CFC.sqrt σ)⁻¹ =
      ((CFC.sqrt (CFC.sqrt σ)))⁻¹ * X * ((CFC.sqrt (CFC.sqrt σ)))⁻¹ := by
    calc
      _ = ((CFC.sqrt σ)⁻¹ * (CFC.sqrt (CFC.sqrt σ))) * X * ((CFC.sqrt (CFC.sqrt σ)) * (CFC.sqrt σ)⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [quarterRootSqrtInvLeft σ hσ, quarterRootSqrtInvRight σ hσ]
  have hl : recoveryComposite K σ τ (weightEquiv σ hσ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X)) = W := by
    rw [weightEquivVec, recoveryCompositeAction, hc]
  have hb : ((CFC.sqrt (CFC.sqrt τ)))⁻¹ * (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * Z * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) * ((CFC.sqrt (CFC.sqrt τ)))⁻¹ =
      (CFC.sqrt τ)⁻¹ * Z * (CFC.sqrt τ)⁻¹ := by
    calc
      _ = (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) * Z *
          (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [quarterRootInvSq τ]
  have hr : weightEquiv σ hσ
      ((normalizedC K σ τ).adjoint (normalizedC K σ τ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X))) = W := by
    rw [normalizedCVec, normalizedCAdjointVec, weightEquivVec]
    change (CFC.sqrt (CFC.sqrt σ)) * (((CFC.sqrt (CFC.sqrt σ)))⁻¹ *
      (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * (((CFC.sqrt (CFC.sqrt τ)))⁻¹ * Z * ((CFC.sqrt (CFC.sqrt τ)))⁻¹) *
        ((CFC.sqrt (CFC.sqrt τ)))⁻¹) * ((CFC.sqrt (CFC.sqrt σ)))⁻¹) * (CFC.sqrt (CFC.sqrt σ)) = W
    rw [hb]
    change (CFC.sqrt (CFC.sqrt σ)) * (((CFC.sqrt (CFC.sqrt σ)))⁻¹ * W * ((CFC.sqrt (CFC.sqrt σ)))⁻¹) * (CFC.sqrt (CFC.sqrt σ)) = W
    calc
      _ = ((CFC.sqrt (CFC.sqrt σ)) * ((CFC.sqrt (CFC.sqrt σ)))⁻¹) * W * (((CFC.sqrt (CFC.sqrt σ)))⁻¹ * (CFC.sqrt (CFC.sqrt σ))) := by
        simp only [Matrix.mul_assoc]
      _ = W := by rw [quarterRootMulInv σ hσ, quarterRootInvMul σ hσ, Matrix.one_mul, Matrix.mul_one]
  exact hl.trans hr.symm
private lemma normalizedCContraction [Nonempty a] (K : s → Matrix b a ℂ)
    (σ : Matrix a a ℂ) (τ : Matrix b b ℂ) (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hE : (MatrixMap.of_kraus (K) (K)) 1 = τ) (hD : (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) 1 = σ) : ‖normalizedC K σ τ‖ ≤ 1 := by
  exact D5.S3.Quantum.FiniteCorrelationRecovery.Gram.gramContractionOfPositiveSimilarity (normalizedC K σ τ)
    (recoveryComposite K σ τ) (recoveryCompositeNonneg K σ τ) σ hσ.isStrictlyPositive
    (recoveryCompositeFixed K σ τ hσ hτ hE hD) (weightEquiv σ hσ)
    (normalizedSimilarity K σ τ hσ)
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Normalized
end r3_normalized_kraus
end
end generic_node
section binding_node
noncomputable section
section r3_actual_correlation
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root D5.S3.Quantum.FixedPointProjection.Choi
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private def C (ρ : Matrix (a × b) (a × b) ℂ) : (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))) →L[ℂ] (EuclideanSpace ℂ (Fin (Fintype.card b) × Fin (Fintype.card b))) :=
  ((LinearEquiv.arrowCongr (vec (n := a)) (vec (n := b))) (((LinearMap.mulLeftRight ℂ (((((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹)), ((((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹))))).comp
    (((MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap))).comp ((LinearMap.mulLeftRight ℂ (((((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹)), ((((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹)))))))).toContinuousLinearMap
private def inputEmbed (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) : (EuclideanSpace ℂ (Fin (Fintype.card a) × Fin (Fintype.card a))) :=
  D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) * Xᵀ * (CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))
private def outputEmbed (ρ : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ) : (EuclideanSpace ℂ (Fin (Fintype.card b) × Fin (Fintype.card b))) :=
  D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec ((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))) * Y * (CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))
private lemma CVec (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) :
    C ρ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec X) = D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹ *
      (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) (((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹ * X * ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹) *
      ((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹) := by
  unfold C
  rw [liftVec]
  rfl
private lemma inputNormSq (ρ : Matrix (a × b) (a × b) ℂ) (hA : (partialTraceRight ρ).PosSemidef)
    (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    ((‖inputEmbed ρ X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) (partialTraceRight ρ) X).trace := by
  rw [inputEmbed, D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.normSq, quarterRootQuadratic]
  exact gmTraceTranspose _ X hA hX
private lemma outputNormSq (ρ : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ) :
    ((‖outputEmbed ρ Y‖ ^ 2 : ℝ) : ℂ) = (Yᴴ * (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) (partialTraceLeft ρ) Y).trace := by
  rw [outputEmbed, D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.normSq, quarterRootQuadratic]
private lemma inputCenter (ρ : Matrix (a × b) (a × b) ℂ) (hA : (partialTraceRight ρ).PosSemidef)
    (X : Matrix a a ℂ) :
    inner ℂ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) (inputEmbed ρ X) = (partialTraceRight ρ * X).trace := by
  rw [inputEmbed, pairing, (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (((partialTraceRight (ρ))ᵀ)))).isHermitian.eq,
    quarterRootCenter (((partialTraceRight (ρ))ᵀ)) Xᵀ hA.transpose]
  exact centerTranspose _ X
private lemma outputCenter (ρ : Matrix (a × b) (a × b) ℂ) (hB : (partialTraceLeft ρ).PosSemidef)
    (Y : Matrix b b ℂ) :
    inner ℂ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt ((partialTraceLeft (ρ))))) (outputEmbed ρ Y) = (partialTraceLeft ρ * Y).trace := by
  rw [outputEmbed, pairing, (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((partialTraceLeft (ρ))))).isHermitian.eq,
    quarterRootCenter ((partialTraceLeft (ρ))) Y hB]
private lemma CInput (ρ : Matrix (a × b) (a × b) ℂ) (hA : (partialTraceRight ρ).PosDef)
    (X : Matrix a a ℂ) :
    C ρ (inputEmbed ρ X) = D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹ *
      (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ * ((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹) := by
  have hcan : ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹ *
      ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) * Xᵀ * (CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ))))) * ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹ = Xᵀ := by
    calc
      _ = (((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹ * (CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ))))) * Xᵀ *
          ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) * ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Xᵀ := by rw [quarterRootInvMul (((partialTraceRight (ρ))ᵀ)) hA.transpose, quarterRootMulInv (((partialTraceRight (ρ))ᵀ)) hA.transpose,
        Matrix.one_mul, Matrix.mul_one]
  unfold C inputEmbed
  rw [liftVec]
  change D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹ * (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap))
    (((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹ * ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) * Xᵀ * (CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ))))) *
      ((CFC.sqrt (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))))⁻¹) * ((CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ))))))⁻¹) = _
  rw [hcan]
private lemma objective (ρ : Matrix (a × b) (a × b) ℂ)
    (hA : (partialTraceRight ρ).PosDef) (hB : (partialTraceLeft ρ).PosDef)
    (X : Matrix a a ℂ) (Y : Matrix b b ℂ) (hY : Y.IsHermitian) :
    inner ℂ (outputEmbed ρ Y) (C ρ (inputEmbed ρ X)) =
      (kroneckerMap (· * ·) X Yᴴ * ρ).trace := by
  rw [CInput ρ hA X, outputEmbed, pairing]
  let B := (CFC.sqrt (CFC.sqrt ((partialTraceLeft (ρ)))))
  have hBstar : Bᴴ = B := (quarterRootHermitian _).eq
  have hl : B * B⁻¹ = 1 := quarterRootMulInv ((partialTraceLeft (ρ))) hB
  have hr : B⁻¹ * B = 1 := quarterRootInvMul ((partialTraceLeft (ρ))) hB
  change ((B * Y * B)ᴴ * (B⁻¹ * (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ * B⁻¹)).trace = _
  calc
    _ = (Y * (B * B⁻¹) * (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ * (B⁻¹ * B)).trace := by
      simpa only [Matrix.conjTranspose_mul, hBstar, hY.eq, Matrix.mul_assoc] using
        Matrix.trace_mul_comm B (Y * B * B⁻¹ * (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ * B⁻¹)
    _ = (Y * (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ).trace := by
      rw [hl, hr, Matrix.mul_one, Matrix.mul_one]
    _ = ((MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) Xᵀ * Y).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [fromBipartitePairing, Matrix.transpose_transpose, hY.eq]
private lemma gmValuesSubset (ρ : Matrix (a × b) (a × b) ℂ)
    (hA : (partialTraceRight ρ).PosDef) (hB : (partialTraceLeft ρ).PosDef) :
    correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ρ ⊆ D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint.centeredCorrelationValues (C ρ)
      (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt ((partialTraceLeft (ρ))))) := by
  rintro r ⟨X,Y,hX,hY,hx0,hy0,hx1,hy1,hr⟩
  have hx : ‖inputEmbed ρ X‖ = 1 := by
    have hh := congrArg Complex.re ((inputNormSq ρ hA.posSemidef X hX).trans hx1)
    simp only [Complex.ofReal_re, Complex.one_re] at hh
    nlinarith [norm_nonneg (inputEmbed ρ X)]
  have hy : ‖outputEmbed ρ Y‖ = 1 := by
    have hh := congrArg Complex.re ((outputNormSq ρ Y).trans hy1)
    simp only [Complex.ofReal_re, Complex.one_re] at hh
    nlinarith [norm_nonneg (outputEmbed ρ Y)]
  refine ⟨⟨inputEmbed ρ X,outputEmbed ρ Y⟩,
    ⟨⟨hx,?left⟩,⟨hy,?right⟩⟩,?value⟩
  case left => exact (inputCenter ρ hA.posSemidef X).trans hx0
  case right => exact (outputCenter ρ hB.posSemidef Y).trans hy0
  case value =>
    change ‖inner ℂ (C ρ (inputEmbed ρ X)) (outputEmbed ρ Y)‖ = r
    rw [norm_inner_symm, objective ρ hA hB X Y hY]
    exact hr.symm
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation
end r3_actual_correlation
section r3_actual_contraction
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root D5.S3.Quantum.FixedPointProjection.Choi D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Normalized
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private lemma existsChoiKraus (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) :
    ∃ K : (b × a) → Matrix b a ℂ,
      (∀ X : Matrix a a ℂ, (MatrixMap.of_kraus (K) (K)) X = (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) X) ∧
      (MatrixMap.of_kraus (K) (K)) 1 = (partialTraceLeft (ρ)) ∧ (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) 1 = ((partialTraceRight (ρ))ᵀ) := by
  obtain ⟨K,hK⟩ := MatrixMap.exists_kraus_of_choi_PSD _ (hρ.submatrix Prod.swap)
  have hF (X : Matrix a a ℂ) : (MatrixMap.of_kraus (K) (K)) X = (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) X := by
    change MatrixMap.of_kraus K K X = MatrixMap.of_choi_matrix (ρ.submatrix Prod.swap Prod.swap) X
    rw [hK, MatrixMap.choi_map_inv]
  refine ⟨K,hF,?_,?_⟩
  · exact (hF 1).trans (fromBipartiteOne ρ)
  · apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    change (X * (MatrixMap.of_kraus ((fun i => (K i)ᴴ)) ((fun i => (K i)ᴴ))) 1).trace = (X * ((partialTraceRight (ρ))ᵀ)).trace
    rw [← rawPair K X 1, Matrix.mul_one, hF, fromBipartiteTrace, Matrix.trace_mul_comm]
private lemma CEqNormalized (ρ : Matrix (a × b) (a × b) ℂ) (K : (b × a) → Matrix b a ℂ)
    (hF : ∀ X : Matrix a a ℂ, (MatrixMap.of_kraus (K) (K)) X = (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) X) :
    C ρ = normalizedC K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X,rfl⟩ := (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a)).surjective x
  rw [CVec, normalizedCVec, hF]
private lemma CNormLeOne [Nonempty a] (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef)
    (hA : (partialTraceRight ρ).PosDef) (hB : (partialTraceLeft ρ).PosDef) : ‖C ρ‖ ≤ 1 := by
  obtain ⟨K,hF,hE,hD⟩ := existsChoiKraus ρ hρ
  rw [CEqNormalized ρ K hF]
  exact normalizedCContraction K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) hA.transpose hB hE hD
private lemma weightIdentity (σ : Matrix a a ℂ) (hσ : σ.PosDef) :
    weightEquiv σ hσ (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt σ)) = σ := by
  rw [weightEquivVec, quarterRootSqrtSandwich σ hσ.posSemidef]
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation
end r3_actual_contraction
end
end binding_node
section r2_channel_projection_transport
open _root_.Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
noncomputable section
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Transport
open D5.S3.Quantum.FixedPointProjection.Transport
variable {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
private lemma channelAdjointNonneg (Φ : QuantumChannel a b) (D : Matrix b b ℂ) (hD : 0 ≤ D) :
    0 ≤ (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ D := by
  exact D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.rawNonneg
    (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) D hD
private lemma channelAdjointOne (Φ : QuantumChannel a b) : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ 1 = 1 := by
  simpa only [ MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_one] using (actual_kraus_representation Φ).hkraus
private lemma channelAdjointTracePair (Φ : QuantumChannel a b) (σ : DensityState a)
    (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (X * (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ Y).trace =
      (CStarMatrix.ofMatrix.symm
        (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) * Y).trace := by
  let M := supported_relative_modular_model Φ σ σ (supportContained_refl σ)
  have hΨ : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ Y = M.data.Ψ Y := by
    simp only [ MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose,
      SupportedRelativeModularData.Ψ, M.kraus_eq]
  rw [hΨ]
  exact M.tracePair X Y
private lemma channelProjectionTransport (Φ : QuantumChannel a b) (σ : DensityState a)
    (hτ : (CStarMatrix.ofMatrix.symm (Φ.mapState σ).1).PosDef)
    (P : Matrix a a ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (Q : Matrix b b ℂ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hQP : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ Q = P) : Q.IsHermitian ∧ Q * Q = Q := by
  let M := supported_relative_modular_model Φ σ σ (supportContained_refl σ)
  have hΨ (Y : Matrix b b ℂ) : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ Y = M.data.Ψ Y := by
    simp only [ MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose,
      SupportedRelativeModularData.Ψ, M.kraus_eq]
  apply projectionOfImageProjection ((fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) Φ)
    (CStarMatrix.ofMatrix.symm σ.1) (CStarMatrix.ofMatrix.symm (Φ.mapState σ).1)
    hτ (channelAdjointNonneg Φ) _ _ P hP hPP Q hQ0 hQ1 hQP
  · intro D
    exact channelAdjointTracePair Φ σ (CStarMatrix.ofMatrix.symm σ.1) D
  · intro D
    rw [hΨ, hΨ]
    exact M.schwarzRight D
private lemma recoveredProjection (E : QuantumChannel a b) (R : QuantumChannel b a)
    (σ : DensityState a) (hτ : (CStarMatrix.ofMatrix.symm (E.mapState σ).1).PosDef)
    (P : Matrix a a ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (hfix : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) E ((fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P) = P) :
    ((fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P).IsHermitian ∧
      (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P * (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P = (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P := by
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have hP0 : 0 ≤ P := hproj.nonneg
  have hP1 : P ≤ 1 := sub_nonneg.mp hproj.one_sub.nonneg
  have hQ0 : 0 ≤ (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P := channelAdjointNonneg R P hP0
  have hQ1 : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P ≤ 1 := by
    have h := channelAdjointNonneg R (1 - P) (sub_nonneg.mpr hP1)
    rw [map_sub, channelAdjointOne] at h
    exact sub_nonneg.mp h
  exact channelProjectionTransport E σ hτ P hP hPP _ hQ0 hQ1 hfix
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Transport
end
end r2_channel_projection_transport

section r3_recovery_endpoint
open _root_.Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
noncomputable section
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Recovery
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Normalized D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation D5.S3.Quantum.FixedPointProjection.Choi
open D5.S3.Quantum.FixedPointProjection.Projection D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Transport
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private lemma faithfulGmProjectionPair
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hA : (partialTraceRight ρ).PosDef) (hB : (partialTraceLeft ρ).PosDef) (hgm : muGM ρ = 1) :
    ∃ P : Matrix a a ℂ, ∃ Q : Matrix b b ℂ,
      P.IsHermitian ∧ P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧ Commute (((partialTraceRight (ρ))ᵀ)) P ∧
      Q.IsHermitian ∧ Q * Q = Q ∧
      ∀ X : Matrix a a ℂ, ((MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) X * Q).trace =
        (X * (CFC.sqrt (((partialTraceRight (ρ))ᵀ)) * P * CFC.sqrt (((partialTraceRight (ρ))ᵀ)))).trace := by
  classical
  haveI : Nonempty a := by
    rcases isEmpty_or_nonempty a with he | hn
    · letI := he
      have hz : ρ.trace = 0 := by simp [Matrix.trace]
      exact False.elim (zero_ne_one (hz.symm.trans hρ1))
    · exact hn
  haveI : Nonempty b := by
    rcases isEmpty_or_nonempty b with he | hn
    · letI := he
      have hz : ρ.trace = 0 := by simp [Matrix.trace]
      exact False.elim (zero_ne_one (hz.symm.trans hρ1))
    · exact hn
  have hσ : (((partialTraceRight (ρ))ᵀ)).PosDef := hA.transpose
  have hτ : ((partialTraceLeft (ρ))).PosDef := hB
  have hσ1 : (((partialTraceRight (ρ))ᵀ)).trace = 1 := by
    change ((partialTraceRight ρ)ᵀ).trace = 1
    rw [Matrix.trace_transpose]
    exact (trace_partialTraceRight ρ).trans hρ1
  let ds : DensityState a := ⟨CStarMatrix.ofMatrix (((partialTraceRight (ρ))ᵀ)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hσ.posSemidef.nonneg, hσ1⟩
  obtain ⟨K,hF,hK1,hKdual⟩ := existsChoiKraus ρ hρ
  let S := (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))⁻¹
  let W := (CFC.sqrt ((partialTraceLeft (ρ))))⁻¹
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (((partialTraceRight (ρ))ᵀ)))).isHermitian.inv
  have hW : W.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((partialTraceLeft (ρ))))).isHermitian.inv
  obtain ⟨E,hE,hEσ⟩ := normalizedBipartiteChannel ρ hρ S hS
    (sqrtNormalize (((partialTraceRight (ρ))ᵀ)) hσ)
  let L := fun i => K i * S
  let H := fun i => (K i)ᴴ * W
  have hL (X : Matrix a a ℂ) : (MatrixMap.of_kraus (L) (L)) X = (MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) (S * X * S) := by
    have hh := rawSandwich K S (1 : Matrix b b ℂ) hS Matrix.isHermitian_one X
    simp only [Matrix.one_mul, Matrix.mul_one] at hh
    exact hh.trans (hF _)
  have hEn (X : Matrix a a ℂ) :
      E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) = CStarMatrix.ofMatrix ((MatrixMap.of_kraus (L) (L)) X) := by
    simpa only [Equiv.apply_symm_apply] using
      congrArg CStarMatrix.ofMatrix ((hE X).trans (hL X).symm)
  have hH : (∑ i, (H i)ᴴ * H i) = 1 := by
    calc
      _ = W * (MatrixMap.of_kraus (K) (K)) 1 * W := by
        simp only [H, rawApply, Matrix.conjTranspose_mul, hW.eq,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_one,
          Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hK1]; exact sqrtNormalize ((partialTraceLeft (ρ))) hτ
  obtain ⟨R,hRsum⟩ := finite_kraus_quantum_channel H hH
  have hR (Y : Matrix b b ℂ) :
      CStarMatrix.ofMatrix.symm (R.toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) = (MatrixMap.of_kraus (H) (H)) Y :=
    (hRsum Y).trans (rawApply H Y).symm
  let T := QuantumChannel.comp R E
  have hT (X : Matrix a a ℂ) :
      (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X = recoveryComposite K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) X := by
    change CStarMatrix.ofMatrix.symm
      (R.toCompletelyPositiveMap (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = (MatrixMap.of_kraus (H) (H)) ((MatrixMap.of_kraus (L) (L)) X)
    rw [hEn, hR]
  have hU : (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap = recoveryComposite K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) := by
    apply LinearMap.ext
    exact hT
  have hfix : (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap (((partialTraceRight (ρ))ᵀ)) = ((partialTraceRight (ρ))ᵀ) := by
    rw [hU]
    exact recoveryCompositeFixed K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) hσ hτ hK1 hKdual
  have hv0 : D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt (((partialTraceRight (ρ))ᵀ))) ≠ 0 := by
    intro hz
    have hsqrt : CFC.sqrt (((partialTraceRight (ρ))ᵀ)) = 0 :=
      (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a)).injective (hz.trans (map_zero (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (n := a))).symm)
    have hsigma : ((partialTraceRight (ρ))ᵀ) = 0 := by
      rw [← CFC.sqrt_mul_sqrt_self (((partialTraceRight (ρ))ᵀ)) hσ.posSemidef.nonneg, hsqrt, Matrix.zero_mul]
    rw [hsigma, Matrix.trace_zero] at hσ1
    exact zero_ne_one hσ1
  have hdim : 1 < Module.finrank ℂ ((fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap).fixedSubmodule := by
    rw [hU]
    apply D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint.fixedDimensionOfCenteredCorrelation (C ρ) (CNormLeOne ρ hρ hA hB)
      (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt (((partialTraceRight (ρ))ᵀ)))) (D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.HilbertSchmidt.vec (CFC.sqrt ((partialTraceLeft (ρ))))) hv0
      (recoveryComposite K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ)))) (weightEquiv (((partialTraceRight (ρ))ᵀ)) hσ)
    · intro x
      rw [CEqNormalized ρ K hF]
      exact normalizedSimilarity K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) hσ x
    · rw [weightIdentity]
      exact recoveryCompositeFixed K (((partialTraceRight (ρ))ᵀ)) ((partialTraceLeft (ρ))) hσ hτ hK1 hKdual
    · exact gmValuesSubset ρ hA hB
    · exact hgm
  obtain ⟨P,hP,hPP,hP0,hP1,hcomm,hPfix⟩ :=
    D5.S3.Quantum.FixedPointProjection.Channel.channelCommutingFixedProjection T (((partialTraceRight (ρ))ᵀ)) hσ hfix hdim
  let Q := (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P
  have hEP : (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) E Q = P := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    calc
      _ = (CStarMatrix.ofMatrix.symm
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) * (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) R P).trace :=
        channelAdjointTracePair E ds X Q
      _ = ((fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X * P).trace := by
        exact channelAdjointTracePair R (E.mapState ds)
          (CStarMatrix.ofMatrix.symm (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) P
      _ = (P * (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X).trace := Matrix.trace_mul_comm _ _
      _ = (P * X).trace := hPfix X
      _ = (X * P).trace := Matrix.trace_mul_comm _ _
  have hτmap : (CStarMatrix.ofMatrix.symm (E.mapState ds).1).PosDef := by
    change (CStarMatrix.ofMatrix.symm
      (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (((partialTraceRight (ρ))ᵀ))))).PosDef
    have hh : CStarMatrix.ofMatrix.symm
        (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (((partialTraceRight (ρ))ᵀ)))) = (partialTraceLeft (ρ)) := hEσ
    rw [hh]
    exact hB
  obtain ⟨hQ,hQQ⟩ := recoveredProjection E R ds hτmap P hP hPP hEP
  refine ⟨P,Q,hP,hPP,hP0,hP1,hcomm,hQ,hQQ,?_⟩
  intro X
  have hp (Z : Matrix a a ℂ) : ((MatrixMap.of_choi_matrix ((ρ).submatrix Prod.swap Prod.swap)) (S * Z * S) * Q).trace = (Z * P).trace := by
    calc
      _ = (CStarMatrix.ofMatrix.symm
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix Z)) * Q).trace := by rw [hE]
      _ = (Z * (fun (Φ : QuantumChannel _ _) => MatrixMap.of_kraus (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ) (fun c => ((actual_kraus_representation Φ).kraus c)ᴴ)) E Q).trace := (channelAdjointTracePair E ds Z Q).symm
      _ = _ := by rw [hEP]
  let D := CFC.sqrt (((partialTraceRight (ρ))ᵀ))
  have hDu : IsUnit D := (CFC.isUnit_sqrt_iff (((partialTraceRight (ρ))ᵀ)) hσ.posSemidef.nonneg).mpr hσ.isUnit
  have hSD : S * D = 1 := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det D).mp hDu)
  have hDS : D * S = 1 := Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hDu)
  have hcan : S * (D * X * D) * S = X := by
    calc
      _ = (S * D) * X * (D * S) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hSD,hDS,Matrix.one_mul,Matrix.mul_one]
  have hh := hp (D * X * D)
  rw [hcan] at hh
  calc
    _ = (D * X * D * P).trace := hh
    _ = (X * (D * P * D)).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm D (X * D * P)

end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Recovery
end
end r3_recovery_endpoint
section r3_gm_transport
open _root_.Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Compression
open D5.S3.Quantum.FiniteCorrelationRecovery.Compression
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
open scoped Kronecker
private lemma correlationPairCompress (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (ρ : Matrix (c × d) (c × d) ℂ) (X : Matrix a a ℂ) (Y : Matrix b b ℂ)
    (hY : Y.IsHermitian) :
    ((X ⊗ₖ Yᴴ) * (((U ⊗ₖ V)) * (ρ) * ((U ⊗ₖ V))ᴴ)).trace =
      ((((U)ᴴ * (X) * (U)) ⊗ₖ (((V)ᴴ * (Y) * (V)))ᴴ) * ρ).trace := by
  rw [hY.eq, (pullHermitian V Y hY).eq, Matrix.trace_mul_comm,
    tracePair, pullTensor, Matrix.trace_mul_comm]
private lemma gmValuesPush (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (ρ : Matrix (c × d) (c × d) ℂ)
    (hA : (partialTraceRight ρ).PosSemidef) (hB : (partialTraceLeft ρ).PosSemidef) :
    correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ((((U ⊗ₖ V)) * (ρ) * ((U ⊗ₖ V))ᴴ)) = correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ρ := by
  ext r
  constructor
  · rintro ⟨X,Y,hX,hY,hx0,hy0,hx1,hy1,hr⟩
    refine ⟨((U)ᴴ * (X) * (U)),((V)ᴴ * (Y) * (V)),pullHermitian U X hX,pullHermitian V Y hY,?_,?_,?_,?_,?_⟩
    · change (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) * X).trace = 0 at hx0
      rw [marginalAPush U V hV, tracePair] at hx0
      exact hx0
    · change (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) * Y).trace = 0 at hy0
      rw [marginalBPush U V hU, tracePair] at hy0
      exact hy0
    · change (Xᴴ * (CFC.sqrt (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) * X * CFC.sqrt (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)))).trace = 1 at hx1
      rw [marginalAPush U V hV, gmPairCompress U hU _ hA X hX] at hx1
      exact hx1
    · change (Yᴴ * (CFC.sqrt (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) * Y * CFC.sqrt (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)))).trace = 1 at hy1
      rw [marginalBPush U V hU, gmPairCompress V hV _ hB Y hY] at hy1
      exact hy1
    · rw [correlationPairCompress U V ρ X Y hY] at hr
      exact hr
  · rintro ⟨X,Y,hX,hY,hx0,hy0,hx1,hy1,hr⟩
    have hXo := pushHermitian U X hX
    have hYo := pushHermitian V Y hY
    refine ⟨((U) * (X) * (U)ᴴ),((V) * (Y) * (V)ᴴ),hXo,hYo,?_,?_,?_,?_,?_⟩
    · change (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) * (U * X * Uᴴ)).trace = 0
      rw [marginalAPush U V hV, tracePair, pullPush U hU]
      exact hx0
    · change (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ) * (V * Y * Vᴴ)).trace = 0
      rw [marginalBPush U V hU, tracePair, pullPush V hV]
      exact hy0
    · change ((U * X * Uᴴ)ᴴ * (CFC.sqrt (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) * (U * X * Uᴴ) * CFC.sqrt (partialTraceRight ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)))).trace = 1
      rw [marginalAPush U V hV, gmPairCompress U hU _ hA _ hXo, pullPush U hU]
      exact hx1
    · change ((V * Y * Vᴴ)ᴴ * (CFC.sqrt (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)) * (V * Y * Vᴴ) * CFC.sqrt (partialTraceLeft ((U ⊗ₖ V) * ρ * (U ⊗ₖ V)ᴴ)))).trace = 1
      rw [marginalBPush U V hU, gmPairCompress V hV _ hB _ hYo, pullPush V hV]
      exact hy1
    · rw [correlationPairCompress U V ρ _ _ hYo, pullPush U hU, pullPush V hV]
      exact hr
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Compression
end
end r3_gm_transport
section r3_support_reduction
open _root_.Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Compression
open D5.S3.Quantum.FiniteCorrelationRecovery.Compression
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
open D5.S3.Quantum.Information.PartialTraceMutualInformation
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private structure FaithfulBipartiteReduction (ρ : Matrix (a × b) (a × b) ℂ) where
  α : Type
  β : Type
  [finiteA : Fintype α]
  [decidableA : DecidableEq α]
  [finiteB : Fintype β]
  [decidableB : DecidableEq β]
  U : Matrix a α ℂ
  V : Matrix b β ℂ
  isoU : Uᴴ * U = 1
  isoV : Vᴴ * V = 1
  state : Matrix (α × β) (α × β) ℂ
  positive : state.PosSemidef
  trace_eq : state.trace = ρ.trace
  reconstruct : (((kroneckerMap (· * ·) U V)) * (state) * ((kroneckerMap (· * ·) U V))ᴴ) = ρ
  faithfulA : (partialTraceRight state).PosDef
  faithfulB : (partialTraceLeft state).PosDef
  gm_values : correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) state = correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ρ
attribute [instance] FaithfulBipartiteReduction.finiteA FaithfulBipartiteReduction.finiteB
  FaithfulBipartiteReduction.decidableA FaithfulBipartiteReduction.decidableB
private lemma faithfulBipartiteReduction (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) :
    Nonempty (FaithfulBipartiteReduction ρ) := by
  classical
  have hA : (partialTraceRight ρ).PosSemidef := partialTraceRight_posSemidef hρ
  have hB : (partialTraceLeft ρ).PosSemidef := partialTraceLeft_posSemidef hρ
  let FA := Classical.choice (existsFaithfulFrame (partialTraceRight ρ) hA)
  let FB := Classical.choice (existsFaithfulFrame (partialTraceLeft ρ) hB)
  let K := kroneckerMap (· * ·) FA.U FB.U
  let τ := ((K)ᴴ * (ρ) * (K))
  have hK : Kᴴ * K = 1 := tensorIso FA.U FB.U FA.iso FB.iso
  have hτ : τ.PosSemidef := hρ.conjTranspose_mul_mul_same K
  have hre : ((K) * (τ) * (K)ᴴ) = ρ :=
    jointSupportFrame ρ hρ FA.U FB.U FA.iso FB.iso FA.small FB.small
      FA.reconstruct.symm FB.reconstruct.symm
  have hmA : partialTraceRight τ = FA.small := by
    have hh : ((FA.U) * ((partialTraceRight τ)) * (FA.U)ᴴ) = ((FA.U) * (FA.small) * (FA.U)ᴴ) := by
      rw [← marginalAPush FA.U FB.U FB.iso, hre, FA.reconstruct]
    have ht := congrArg ((fun (X : Matrix _ _ ℂ) => (FA.U)ᴴ * X * (FA.U))) hh
    simpa only [pullPush FA.U FA.iso] using ht
  have hmB : partialTraceLeft τ = FB.small := by
    have hh : ((FB.U) * ((partialTraceLeft τ)) * (FB.U)ᴴ) = ((FB.U) * (FB.small) * (FB.U)ᴴ) := by
      rw [← marginalBPush FA.U FB.U FA.iso, hre, FB.reconstruct]
    have ht := congrArg ((fun (X : Matrix _ _ ℂ) => (FB.U)ᴴ * X * (FB.U))) hh
    simpa only [pullPush FB.U FB.iso] using ht
  have ht : τ.trace = ρ.trace :=
    (pushTrace K hK τ).symm.trans (congrArg Matrix.trace hre)
  have hτA : (partialTraceRight τ).PosDef := hmA.symm ▸ FA.positive
  have hτB : (partialTraceLeft τ).PosDef := hmB.symm ▸ FB.positive
  have hg : correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) τ = correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) ρ :=
    (gmValuesPush FA.U FB.U FA.iso FB.iso τ hτA.posSemidef hτB.posSemidef).symm.trans
      (congrArg (fun M : Matrix (a × b) (a × b) ℂ => correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) M) hre)
  exact ⟨⟨FA.ι,FB.ι,FA.U,FB.U,FA.iso,FB.iso,τ,hτ,ht,hre,
    hmA.symm ▸ FA.positive,hmB.symm ▸ FB.positive,hg⟩⟩
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Compression
end
end r3_support_reduction
section binding_am
noncomputable section
section r3_am_witness
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Arithmetic
open D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private lemma amEndpointFromSharedProjections
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1)
    (P : Matrix a a ℂ) (Q : Matrix b b ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hpA : (partialTraceRight ρ * P).trace = (p : ℂ))
    (hpB : (partialTraceLeft ρ * Q).trace = (p : ℂ))
    (hpAB : (kroneckerMap (· * ·) P Q * ρ).trace = (p : ℂ)) : muAM ρ = 1 := by
  have hA1 : (partialTraceRight ρ).trace = 1 := (trace_partialTraceRight ρ).trans hρ1
  have hB1 : (partialTraceLeft ρ).trace = 1 := (trace_partialTraceLeft ρ).trans hρ1
  have hP1 : traceCorrelation ρ P 1 = (p : ℂ) := by
    change (kroneckerMap (· * ·) P (1 : Matrix b b ℂ) * ρ).trace = _
    rw [D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalLeft, Matrix.trace_mul_comm]
    exact hpA
  have hQ1 : traceCorrelation ρ 1 Q = (p : ℂ) := by
    change (kroneckerMap (· * ·) (1 : Matrix a a ℂ) Q * ρ).trace = _
    rw [D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalRight, Matrix.trace_mul_comm]
    exact hpB
  have hI : traceCorrelation ρ 1 1 = 1 := by
    change (kroneckerMap (· * ·) (1 : Matrix a a ℂ) (1 : Matrix b b ℂ) * ρ).trace = _
    simpa only [Matrix.one_kronecker_one, Matrix.one_mul] using hρ1
  have hw := sharedBinaryCorrelation ρ P Q p hp0 hp1 hpAB hP1 hQ1 hI
  have hone : (1 : ℝ) ∈ correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => (1 / 2 : ℂ) • (σ * Y + Y * σ)) ρ := by
    refine ⟨binaryObservable P p, binaryObservable Q p,
      binaryObservableHermitian P hP p, binaryObservableHermitian Q hQ p,
      binaryObservableCentered _ _ p hA1 hpA, binaryObservableCentered _ _ p hB1 hpB,
      binaryObservableAmUnit _ _ hP p hp0 hp1 hA1 hpA hPP,
      binaryObservableAmUnit _ _ hQ p hp0 hp1 hB1 hpB hQQ, ?_⟩
    rw [(binaryObservableHermitian Q hQ p).eq]
    change 1 = ‖traceCorrelation ρ (binaryObservable P p) (binaryObservable Q p)‖
    rw [hw, norm_one]
  have hupper : ∀ r ∈ correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => (1 / 2 : ℂ) • (σ * Y + Y * σ)) ρ, r ≤ 1 := by
    intro r hr
    obtain ⟨X,Y,hX,hY,_,_,hx,hy,rfl⟩ := hr
    exact amCorrelationLeOne ρ hρ X Y hX hY hx hy
  change sSup (correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => (1 / 2 : ℂ) • (σ * Y + Y * σ)) ρ) = 1
  apply le_antisymm
  · exact csSup_le ⟨1, hone⟩ hupper
  · exact le_csSup ⟨1, hupper⟩ hone
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Arithmetic
end r3_am_witness
section r3_shared_probabilities
open _root_.Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Shared
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Correlation D5.S3.Quantum.FixedPointProjection.Choi D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Root
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private lemma faithfulSharedProjections
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hA : (partialTraceRight ρ).PosDef) (hB : (partialTraceLeft ρ).PosDef) (hgm : muGM ρ = 1) :
    ∃ A : Matrix a a ℂ, ∃ B : Matrix b b ℂ, ∃ p : ℝ,
      A.IsHermitian ∧ A * A = A ∧ B.IsHermitian ∧ B * B = B ∧
      0 < p ∧ p < 1 ∧ (partialTraceRight ρ * A).trace = (p : ℂ) ∧
      (partialTraceLeft ρ * B).trace = (p : ℂ) ∧
      (kroneckerMap (· * ·) A B * ρ).trace = (p : ℂ) := by
  obtain ⟨P,Q,hP,hPP,hP0,hP1,hcomm,hQ,hQQ,hpair⟩ :=
    D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Recovery.faithfulGmProjectionPair ρ hρ hρ1 hA hB hgm
  have hσ1 : (((partialTraceRight (ρ))ᵀ)).trace = 1 := by
    change ((partialTraceRight ρ)ᵀ).trace = 1
    rw [Matrix.trace_transpose]
    exact (trace_partialTraceRight ρ).trans hρ1
  obtain ⟨p,hp0,hp1,hp⟩ := D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic.projectionProbability (((partialTraceRight (ρ))ᵀ)) P hA.transpose hσ1 hP hPP hP0 hP1
  let D := CFC.sqrt (((partialTraceRight (ρ))ᵀ))
  have hD : Commute D P := hcomm.cfcₙ_nnreal NNReal.sqrt
  have hDPD : D * P * D = ((partialTraceRight (ρ))ᵀ) * P := by
    calc
      _ = D * (P * D) := Matrix.mul_assoc _ _ _
      _ = D * (D * P) := by rw [hD.eq]
      _ = (D * D) * P := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (((partialTraceRight (ρ))ᵀ)) hA.transpose.posSemidef.nonneg]
  have hPa : Pᵀ * Pᵀ = Pᵀ := by rw [← Matrix.transpose_mul,hPP]
  have hpA : (partialTraceRight ρ * Pᵀ).trace = (p : ℂ) := by
    have hh : (((partialTraceRight (ρ))ᵀ) * P).trace = (partialTraceRight ρ * Pᵀ).trace :=
      centerTranspose (partialTraceRight ρ) Pᵀ
    exact hh.symm.trans hp
  have hpB : (partialTraceLeft ρ * Q).trace = (p : ℂ) := by
    have hh := hpair 1
    rw [fromBipartiteOne, Matrix.one_mul, hDPD] at hh
    exact hh.trans hp
  have hpAB : (kroneckerMap (· * ·) Pᵀ Q * ρ).trace = (p : ℂ) := by
    rw [← fromBipartitePairing]
    rw [hpair P, hDPD]
    calc
      _ = (((partialTraceRight (ρ))ᵀ) * (P * P)).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm P (((partialTraceRight (ρ))ᵀ) * P)
      _ = _ := by rw [hPP,hp]
  exact ⟨Pᵀ,Q,p,hP.transpose,hPa,hQ,hQQ,hp0,hp1,hpA,hpB,hpAB⟩
end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Shared
end r3_shared_probabilities
section r3_result_body
open _root_.Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation D5.S3.Quantum.FiniteCorrelationRecovery.Compression D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Compression

namespace D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
theorem result : D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.claim := by
  intro a b _ _ _ _ ρ hρ hρ1 hgm
  classical
  obtain ⟨F⟩ := faithfulBipartiteReduction ρ hρ
  have hF1 : F.state.trace = 1 := F.trace_eq.trans hρ1
  have hFgm : muGM F.state = 1 := by
    change sSup (correlationValues (fun {c : Type} [Fintype c] [DecidableEq c] (σ Y : Matrix c c ℂ) => CFC.sqrt σ * Y * CFC.sqrt σ) F.state) = 1
    rw [F.gm_values]
    exact hgm
  obtain ⟨P,Q,p,hP,hPP,hQ,hQQ,hp0,hp1,hpA,hpB,hpAB⟩ :=
    D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Shared.faithfulSharedProjections F.state F.positive hF1 F.faithfulA F.faithfulB hFgm
  let K := kroneckerMap (· * ·) F.U F.V
  have hK : Kᴴ * K = 1 := tensorIso F.U F.V F.isoU F.isoV
  have hBP : (((F.U) * (P) * (F.U)ᴴ)).IsHermitian := pushHermitian F.U P hP
  have hBQ : (((F.V) * (Q) * (F.V)ᴴ)).IsHermitian := pushHermitian F.V Q hQ
  have hBPP : ((F.U) * (P) * (F.U)ᴴ) * ((F.U) * (P) * (F.U)ᴴ) = ((F.U) * (P) * (F.U)ᴴ) :=
    (pushMul F.U F.isoU P P).trans (congrArg ((fun (X : Matrix _ _ ℂ) => (F.U) * X * (F.U)ᴴ)) hPP)
  have hBQQ : ((F.V) * (Q) * (F.V)ᴴ) * ((F.V) * (Q) * (F.V)ᴴ) = ((F.V) * (Q) * (F.V)ᴴ) :=
    (pushMul F.V F.isoV Q Q).trans (congrArg ((fun (X : Matrix _ _ ℂ) => (F.V) * X * (F.V)ᴴ)) hQQ)
  have hBpA : (partialTraceRight (((K) * (F.state) * (K)ᴴ)) * ((F.U) * (P) * (F.U)ᴴ)).trace = (p : ℂ) := by
    rw [marginalAPush F.U F.V F.isoV, tracePair, pullPush F.U F.isoU]
    exact hpA
  have hBpB : (partialTraceLeft (((K) * (F.state) * (K)ᴴ)) * ((F.V) * (Q) * (F.V)ᴴ)).trace = (p : ℂ) := by
    rw [marginalBPush F.U F.V F.isoU, tracePair, pullPush F.V F.isoV]
    exact hpB
  have hBpAB : (kroneckerMap (· * ·) (((F.U) * (P) * (F.U)ᴴ)) (((F.V) * (Q) * (F.V)ᴴ)) * ((K) * (F.state) * (K)ᴴ)).trace = (p : ℂ) := by
    rw [Matrix.trace_mul_comm, tracePair, pullTensor,
      pullPush F.U F.isoU, pullPush F.V F.isoV, Matrix.trace_mul_comm]
    exact hpAB
  have hBig : (((K) * (F.state) * (K)ᴴ)).PosSemidef := F.positive.mul_mul_conjTranspose_same K
  have hBig1 : (((K) * (F.state) * (K)ᴴ)).trace = 1 := (pushTrace K hK F.state).trans hF1
  have ham : muAM (((K) * (F.state) * (K)ᴴ)) = 1 :=
    D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation.Arithmetic.amEndpointFromSharedProjections (((K) * (F.state) * (K)ᴴ)) hBig hBig1
      (((F.U) * (P) * (F.U)ᴴ)) (((F.V) * (Q) * (F.V)ᴴ)) hBP hBQ hBPP hBQQ p hp0 hp1 hBpA hBpB hBpAB
  exact (congrArg (fun Z => muAM Z) F.reconstruct).symm.trans ham

end D5.S3.Quantum.GeorgeTomamichelMaximalCorrelation
end r3_result_body
end
end binding_am
