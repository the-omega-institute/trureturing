/- GID: D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separable two-qubit mixtures outside every local-unitary stabilizer frame. -/

/-
result
proof_shape: content
escape_witness: family_nonmembership, via ensemble_support and the overlap obstruction.
admission_basis: open-problem-resolution (#14115; Proved)
The parameter-family argument is on the live proof path of the rational witness.
The finite Gaussian-integer certificates are consumed bind-only normalization helpers;
the new mathematical conclusion excludes a continuous family of local-unitary orbits.
Utility is none: these proof-normalization certificates supply no independent finite
instance, checker interface, numerical approximation, or conditional numerical reduction.
Information-escape registration is paused under CLAUDE.md section 3.9.
Direct frozen dependencies (declaration statement_id, from baseline Freeze events):
D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.unitaryEvolution
  sha256:e09d20adbc78becc29a640f4fb9bab3d1627ee36e10e97ed437a96cd4b7596f5
D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry.productVector
  sha256:abd91178d81d87303977d321faf2d072bb352c3a01e21f5a90ecb65451661832
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
  sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
  sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake
  sha256:3f3685dfb0637d23f5f799f8ec2e875fbc8fee9823e2940f31ba7983a7b83b1e
D5/S3/Quantum/Information/SignedPauliSumNormRefutation.pauliZ
  sha256:61ea0b0971de26d2479eb5faaefb162074ffdfe2562ca9621d05f53503521f36
D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral
  sha256:58bd36c8db884685792b2678f181ebca66942a07bcbcaee2e7dcbc648428c26a
D5/S3/Quantum/Magic/WignerDistanceMinimum.eigenVector
  sha256:c5204f0e664257bf63f638761ad1ece981a1b9b7c22f39e57af86168fda8fecd
D5/S3/Quantum/Magic/WignerDistanceMinimum.spectral_stabilizer
  sha256:d62ad9cb01d5fb9fdd3b7e929050226246f7dc58861af5ee77618f6f09c576b1
D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity
  sha256:0386217fa1109c4358c01b5fe2db195888fa2f776c05e63cec2e880416d1c8ff
D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli
  sha256:3758fca32bf974298628515ed91492adafcdff8dc216bac5d000b130b08b04fc
D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
  sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
D5/S3/Quantum/FiniteDimensional.qubitX
  sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
D5/S3/Quantum/FiniteDimensional.qubitZ
  sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
-/

import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.SignedPauliSumNormRefutation
import D5.S3.Quantum.Magic.WignerDistanceMinimum
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
open Matrix
open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry (productVector)
open scoped ComplexOrder Kronecker BigOperators
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.SignedPauliSumNormRefutation (pauliZ)
open D5.S3.Quantum.Magic.WignerDistanceMinimum (spectral eigenVector spectral_stabilizer)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (IsDensity)
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
namespace D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
noncomputable section
def unitVector {n : Type*} [Fintype n] (x : n → ℂ) : Prop := star x ⬝ᵥ x = 1
def IsHermitianPauli (P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : Prop :=
  ∃ a b : Pauli, P = pauliMatrix a ⊗ₖ pauliMatrix b ∨
    P = -(pauliMatrix a ⊗ₖ pauliMatrix b)
def PureStabilizer (ψ : (Fin 2 × Fin 2 → ℂ)) : Prop :=
  unitVector ψ ∧ ∃ P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    IsHermitianPauli P ∧ IsHermitianPauli Q ∧
    P ≠ 1 ∧ P ≠ -1 ∧ Q ≠ 1 ∧ Q ≠ -1 ∧
    Q ≠ P ∧ Q ≠ -P ∧ P * Q = Q * P ∧
    P *ᵥ ψ = ψ ∧ Q *ᵥ ψ = ψ
def STAB : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := convexHull ℝ {A | ∃ ψ : (Fin 2 × Fin 2 → ℂ), PureStabilizer ψ ∧ A = rankOneDensity ψ}
def localMatrix (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  (UA : (Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ (UB : (Matrix (Fin 2) (Fin 2) ℂ))
def localAction (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution (localMatrix UA UB) ρ
def ProductPureProjectors : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  {A | ∃ a b : (Fin 2 → ℂ), unitVector a ∧ unitVector b ∧ A = rankOneDensity (productVector a b)}
def Separable (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : Prop := ρ ∈ convexHull ℝ ProductPureProjectors
def claim : Prop := ∃ ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), IsDensity ρ ∧ Separable ρ ∧
  ∀ UA UB : Matrix.unitaryGroup (Fin 2) ℂ, localAction UA UB ρ ∉ STAB
private def ProductVector (ψ : (Fin 2 × Fin 2 → ℂ)) : Prop := ∃ a b : (Fin 2 → ℂ), ψ = productVector a b
private def MaximallyEntangled (ψ : (Fin 2 × Fin 2 → ℂ)) : Prop :=
  unitVector ψ ∧ partialTraceRight (rankOneDensity ψ) = (1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))
private def b (c s : ℝ) : (Fin 2 → ℂ) := ![(c : ℂ), (s : ℂ)]
private def rho (p c s : ℝ) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := p • rankOneDensity (productVector ![1, 0] ![1, 0]) + (1-p) • rankOneDensity (productVector (b c s) (b c s))
private def supportVector (c s : ℝ) (α β : ℂ) : (Fin 2 × Fin 2 → ℂ) := α • (productVector ![1, 0] ![1, 0]) + β • productVector (b c s) (b c s)
private def FamilyParameters (p c s : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < s ∧ c^2+s^2 = 1 ∧ c^2 ≠ 1/2
private def FamilyClaim : Prop := ∀ p c s : ℝ, FamilyParameters p c s →
  IsDensity (rho p c s) ∧ Separable (rho p c s) ∧
  ∀ UA UB : Matrix.unitaryGroup (Fin 2) ℂ, localAction UA UB (rho p c s) ∉ STAB
private theorem tensor_smul_left (a b : (Fin 2 → ℂ)) (z : ℂ) : productVector (z • a) b = z • productVector a b := by
  ext i; simp [productVector, mul_assoc,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
private theorem trace_projector {n : Type*} [Fintype n] (x : n → ℂ) : (rankOneDensity x).trace = star x ⬝ᵥ x := by
  simp only [rankOneDensity, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
    dotProduct]; apply Finset.sum_congr rfl; intro i hi; exact mul_comm _ _
private theorem unit_e0 : unitVector ![1, 0] := by
  norm_num [unitVector, dotProduct, Fin.sum_univ_two]
private theorem unit_b {c s : ℝ} (h : c^2+s^2=1) : unitVector (b c s) := by
  unfold unitVector b
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.star_def, Complex.conj_ofReal]
  exact_mod_cast (by nlinarith [h] : c*c+s*s=1)
private theorem unit_tensor {a b : (Fin 2 → ℂ)} (ha : unitVector a) (hb : unitVector b) : unitVector (productVector a b) := by
  unfold unitVector productVector at *
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply,
    star_mul,Function.uncurry_apply_pair,Matrix.vecMulVec_apply] at *
  calc
    _ = (star (a 0)*a 0+star (a 1)*a 1) *
      (star (b 0)*b 0+star (b 1)*b 1) := by ring
    _ = 1 := by rw [ha, hb]; norm_num
private theorem rho_density {p c s : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hcs : c^2+s^2=1) : IsDensity (rho p c s) := by
  have hu := unit_tensor unit_e0 unit_e0
  have hv := unit_tensor (unit_b hcs) (unit_b hcs)
  constructor
  · exact ((Matrix.posSemidef_vecMulVec_self_star (productVector ![1, 0] ![1, 0])).smul hp).add
      ((Matrix.posSemidef_vecMulVec_self_star (productVector (b c s) (b c s))).smul (sub_nonneg.mpr hp1))
  · simp only [rho, Matrix.trace_add, Matrix.trace_smul, trace_projector]
    change (p : ℂ) * (star (productVector ![1, 0] ![1, 0]) ⬝ᵥ (productVector ![1, 0] ![1, 0])) + ((1-p : ℝ) : ℂ) * (star (productVector (b c s) (b c s)) ⬝ᵥ productVector (b c s) (b c s)) = 1
    change unitVector (productVector ![1, 0] ![1, 0]) at hu
    change unitVector (productVector (b c s) (b c s)) at hv
    rw [hu, hv]; push_cast; ring
private theorem rho_separable {p c s : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hcs : c^2+s^2=1) : Separable (rho p c s) := by
  apply (convex_convexHull ℝ ProductPureProjectors)
    (subset_convexHull ℝ ProductPureProjectors ⟨![1, 0],![1, 0],unit_e0,unit_e0,rfl⟩)
    (subset_convexHull ℝ ProductPureProjectors ⟨b c s,b c s,unit_b hcs,unit_b hcs,rfl⟩)
    hp (sub_nonneg.mpr hp1)
  linarith
private theorem product_determinant_zero {ψ : (Fin 2 × Fin 2 → ℂ)} (h : ProductVector ψ) : ψ (0,0)*ψ (1,1)-ψ (0,1)*ψ (1,0)=0 := by
  obtain ⟨a,b,rfl⟩ := h
  simp only [productVector,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]; ring
private theorem support_determinant (c s : ℝ) (α β : ℂ) : (supportVector c s α β) (0,0)*(supportVector c s α β) (1,1)- (supportVector c s α β) (0,1)*(supportVector c s α β) (1,0) = α*β*(s : ℂ)^2 := by
  simp [supportVector, productVector, b,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]; ring
private theorem support_product_iff {c s : ℝ} (hs : s ≠ 0) (α β : ℂ) : ProductVector (supportVector c s α β) ↔ α = 0 ∨ β = 0 := by
  constructor
  · intro h
    have hd := product_determinant_zero h
    rw [support_determinant] at hd
    have hsC : (s : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs)
    exact mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hsC)
  · rintro (rfl | rfl)
    · refine ⟨β • b c s, b c s, ?_⟩
      simp only [supportVector, zero_smul, zero_add, tensor_smul_left]
    · refine ⟨α • ![1, 0], ![1, 0], ?_⟩
      simp only [supportVector, zero_smul, add_zero, tensor_smul_left]
private theorem support_marginal_offdiag {c s : ℝ} (hcs : c^2+s^2=1) (α β : ℂ) : partialTraceRight (rankOneDensity (supportVector c s α β)) 0 1 = (c : ℂ)*(s : ℂ)*(α+β)*star β := by
  have hcsC : (c : ℂ)^2+(s : ℂ)^2=1 := by exact_mod_cast hcs
  simp [partialTraceRight, rankOneDensity, Matrix.vecMulVec_apply, supportVector, productVector, b,
    Fin.sum_univ_two,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
  linear_combination (β * ((starRingEnd ℂ) β) * (c : ℂ) * (s : ℂ)) * hcsC
private theorem support_maxent_ray {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) (hcs : c^2+s^2=1) (α β : ℂ) (h : MaximallyEntangled (supportVector c s α β)) : α = -β := by
  obtain ⟨hn,hM⟩ := h
  have h01 := congrFun (congrFun hM 0) 1
  rw [support_marginal_offdiag hcs] at h01
  simp only [Matrix.smul_apply, Matrix.one_apply, show (0 : Fin 2) ≠ 1 by decide, if_false,
    smul_eq_mul, mul_zero] at h01
  have hb : β ≠ 0 := by
    intro hb
    have h11 := congrFun (congrFun hM 1) 1
    norm_num [partialTraceRight, rankOneDensity, Matrix.vecMulVec_apply, supportVector, productVector, b,
      Fin.sum_univ_two, hb,Function.uncurry_apply_pair,Matrix.vecMulVec_apply] at h11
  have hnz := mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc)
    (Complex.ofReal_ne_zero.mpr hs)) (star_ne_zero.mpr hb)
  have hab : α+β=0 := (mul_eq_zero.mp (by convert h01 using 1 <;> ring :
    ((c : ℂ)*(s : ℂ)*star β)*(α+β)=0)).resolve_left hnz
  exact eq_neg_of_add_eq_zero_left hab
private theorem local_star_mul (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) : (localMatrix UA UB)ᴴ * localMatrix UA UB = 1 := by
  unfold localMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hA := Matrix.mem_unitaryGroup_iff'.mp UA.property
  have hB := Matrix.mem_unitaryGroup_iff'.mp UB.property
  simp only [Matrix.star_eq_conjTranspose] at hA hB
  rw [hA,hB,Matrix.one_kronecker_one]
private theorem unitary_preserves_overlap {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : Aᴴ * A = 1) (x y : n → ℂ) : star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hA, Matrix.one_mulVec]
private theorem local_preserves_unit (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) {ψ : (Fin 2 × Fin 2 → ℂ)} (h : unitVector ψ) : unitVector (localMatrix UA UB *ᵥ ψ) := by
  unfold unitVector at *
  rw [unitary_preserves_overlap _ (local_star_mul UA UB)]
  exact h
private theorem kronecker_mul_tensor (A B : (Matrix (Fin 2) (Fin 2) ℂ)) (a b : (Fin 2 → ℂ)) : (A ⊗ₖ B) *ᵥ productVector a b = productVector (A *ᵥ a) (B *ᵥ b) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, productVector,
    Fintype.sum_prod_type, Fin.sum_univ_two,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
  ring
private theorem local_preserves_product (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) {ψ : (Fin 2 × Fin 2 → ℂ)} (h : ProductVector ψ) : ProductVector (localMatrix UA UB *ᵥ ψ) := by
  obtain ⟨a,b,rfl⟩ := h
  exact ⟨(UA : (Matrix (Fin 2) (Fin 2) ℂ))*ᵥ a,(UB : (Matrix (Fin 2) (Fin 2) ℂ))*ᵥ b,kronecker_mul_tensor _ _ _ _⟩
theorem marginal_amplitude (ψ : (Fin 2 × Fin 2 → ℂ)) : partialTraceRight (rankOneDensity ψ) = (Matrix.of ∘ Function.curry) ψ * ((Matrix.of ∘ Function.curry) ψ)ᴴ := by
  ext i j
  simp [partialTraceRight, rankOneDensity, Matrix.vecMulVec_apply,Function.curry,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Function.comp_apply, Function.curry]
private theorem local_amplitude (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (ψ : (Fin 2 × Fin 2 → ℂ)) : (Matrix.of ∘ Function.curry) (localMatrix UA UB *ᵥ ψ) = (UA : (Matrix (Fin 2) (Fin 2) ℂ)) * (Matrix.of ∘ Function.curry) ψ * (UB : (Matrix (Fin 2) (Fin 2) ℂ))ᵀ := by
  ext i j
  simp only [Matrix.of_apply,Function.comp_apply,Function.curry,localMatrix, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring
private theorem local_preserves_maxent (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) {ψ : (Fin 2 × Fin 2 → ℂ)} (h : MaximallyEntangled ψ) : MaximallyEntangled (localMatrix UA UB *ᵥ ψ) := by
  refine ⟨local_preserves_unit UA UB h.1, ?_⟩
  rw [marginal_amplitude, local_amplitude, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  have hB : (UB : (Matrix (Fin 2) (Fin 2) ℂ))ᵀ * ((UB : (Matrix (Fin 2) (Fin 2) ℂ))ᵀ)ᴴ = 1 := by
    have hh := congrArg Matrix.transpose (Matrix.mem_unitaryGroup_iff'.mp UB.property)
    simpa only [Matrix.star_eq_conjTranspose, Matrix.transpose_mul,
      Matrix.transpose_one, Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose]
      using hh
  have hA : (UA : (Matrix (Fin 2) (Fin 2) ℂ)) * (UA : (Matrix (Fin 2) (Fin 2) ℂ))ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp UA.property
  have hM := h.2
  rw [marginal_amplitude] at hM
  calc
    _ = (UA : (Matrix (Fin 2) (Fin 2) ℂ)) * ((Matrix.of ∘ Function.curry) ψ * ((Matrix.of ∘ Function.curry) ψ)ᴴ) * (UA : (Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ((UB : (Matrix (Fin 2) (Fin 2) ℂ))ᵀ), hB,
        Matrix.one_mul]
    _ = (1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) := by rw [hM]; simp [Matrix.mul_smul, Matrix.smul_mul, hA]
private theorem projector_conjugation {n : Type*} [Fintype n] (A : Matrix n n ℂ) (ψ : n → ℂ) : rankOneDensity (A *ᵥ ψ) = A * rankOneDensity ψ * Aᴴ := by
  ext i j
  simp only [rankOneDensity, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.conjTranspose_apply,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring
private theorem fixed_mul_projector {n : Type*} [Fintype n] (E : Matrix n n ℂ) (ψ : n → ℂ) (h : E *ᵥ ψ = ψ) : E * rankOneDensity ψ = rankOneDensity ψ := by
  ext i j
  simp only [Matrix.mul_apply, rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [show (∑ k, E i k*(ψ k*star (ψ j))) =
    (E *ᵥ ψ) i*star (ψ j) by simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]]
  rw [h]
private theorem trace_one_projection_eq_projector {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (hE : Eᴴ = E) (hEE : E*E=E) (htr : E.trace=1) (ψ : n → ℂ) (hn : unitVector ψ) (hfix : E *ᵥ ψ = ψ) : E = rankOneDensity ψ := by
  have hleft := fixed_mul_projector E ψ hfix
  have hright : rankOneDensity ψ * E = rankOneDensity ψ := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa [hE, rankOneDensity] using h
  have hproj := (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake ψ hn 0).1
  have hid : IsIdempotentElem (E-rankOneDensity ψ) := by
    unfold IsIdempotentElem
    calc
      _ = E*E - E*rankOneDensity ψ - rankOneDensity ψ*E + rankOneDensity ψ*rankOneDensity ψ := by
        noncomm_ring
      _ = E-rankOneDensity ψ := by rw [hEE,hleft,hright,hproj]; abel
  have htr0 : (E-rankOneDensity ψ).trace=0 := by rw [Matrix.trace_sub,htr,trace_projector,hn]; ring
  have hlin : IsIdempotentElem (Matrix.toLin' (E-rankOneDensity ψ)) :=
    hid.map Matrix.toLinAlgEquiv'.toRingHom
  have hz := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hlin
    (by simpa only [Matrix.trace_toLin'_eq] using htr0)
  have hzero : E-rankOneDensity ψ=0 := Matrix.toLin'.injective
    (by simpa using hz)
  exact sub_eq_zero.mp hzero
private def jointProjector (P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := (1 / 4 : ℂ) • (1 + P + Q + P*Q)
private theorem joint_fixed (P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (ψ : (Fin 2 × Fin 2 → ℂ)) (hP : P *ᵥ ψ=ψ) (hQ : Q *ᵥ ψ=ψ) : jointProjector P Q *ᵥ ψ=ψ := by
  simp only [jointProjector, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hP,hQ]
  ext i; simp [smul_eq_mul]; ring
private theorem joint_idempotent (P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (hP : P*P=1) (hQ : Q*Q=1) (hc : P*Q=Q*P) : jointProjector P Q * jointProjector P Q=jointProjector P Q := by
  have hPPP : P*Q*P=Q := by rw [hc,Matrix.mul_assoc,hP,Matrix.mul_one]
  have hPQQ : P*Q*Q=P := by rw [Matrix.mul_assoc,hQ,Matrix.mul_one]
  have hQPQ : Q*(P*Q)=P := by rw [← Matrix.mul_assoc,← hc,Matrix.mul_assoc,hQ,Matrix.mul_one]
  have hPPQ : P*(P*Q)=Q := by rw [← Matrix.mul_assoc,hP,Matrix.one_mul]
  have hPQPQ : (P*Q)*(P*Q)=1 := by rw [← Matrix.mul_assoc,hPPP,hQ]
  unfold jointProjector
  simp only [smul_mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, hP,hQ,← hc,hPPP,hPQQ,hQPQ,hPPQ,hPQPQ]
  module
private theorem pauli_square (p : Pauli) : pauliMatrix p * pauliMatrix p = 1 := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
private theorem pauli_hermitian (p : Pauli) : (pauliMatrix p)ᴴ=pauliMatrix p := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
private theorem hermitianPauli_square {P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (h : IsHermitianPauli P) : P*P=1 := by
  obtain ⟨a,b,h|h⟩ := h <;> rw [h]
  · rw [← Matrix.mul_kronecker_mul,pauli_square,pauli_square,Matrix.one_kronecker_one]
  · simp only [neg_mul_neg]; rw [← Matrix.mul_kronecker_mul,pauli_square,pauli_square,
      Matrix.one_kronecker_one]
private theorem hermitianPauli_hermitian {P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (h : IsHermitianPauli P) : Pᴴ=P := by
  obtain ⟨a,b,h|h⟩ := h <;> rw [h] <;>
    simp [Matrix.conjTranspose_kronecker,pauli_hermitian]
private theorem joint_hermitian (P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (hP : Pᴴ=P) (hQ : Qᴴ=Q) (hc : P*Q=Q*P) : (jointProjector P Q)ᴴ=jointProjector P Q := by
  simp [jointProjector,Matrix.conjTranspose_add,Matrix.conjTranspose_mul,hP,hQ,hc]
private theorem pauli_trace_pair (p q : Pauli) : (pauliMatrix p * pauliMatrix q).trace = if p=q then 2 else 0 := by
  cases p <;> cases q <;>
    simp [pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
private theorem hermitianPauli_trace_zero {P : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (h : IsHermitianPauli P) (h1 : P ≠ 1) (hn1 : P ≠ -1) : P.trace=0 := by
  obtain ⟨a,b,rfl|rfl⟩ := h <;> cases a <;> cases b <;>
    simp_all [pauliMatrix,qubitX,qubitZ,Matrix.one_kronecker_one,
      Matrix.trace_kronecker,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
private theorem independent_trace_zero {P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (hP : IsHermitianPauli P) (hQ : IsHermitianPauli Q) (hne : Q ≠ P) (hneg : Q ≠ -P) : (P*Q).trace=0 := by
  obtain ⟨a,b,rfl|rfl⟩ := hP <;> obtain ⟨c,d,rfl|rfl⟩ := hQ
  all_goals
    by_cases hac : a=c <;> by_cases hbd : b=d
  all_goals
    try { subst c; subst d; simp_all }
  all_goals
    have ht : ((pauliMatrix a ⊗ₖ pauliMatrix b) *
        (pauliMatrix c ⊗ₖ pauliMatrix d)).trace=0 := by
      rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,pauli_trace_pair,
        pauli_trace_pair]
      simp_all
    simpa only [neg_mul, mul_neg, neg_neg, neg_mul_neg, Matrix.trace_neg,
      ht, neg_zero] using ht
private theorem stabilizer_projector {ψ : (Fin 2 × Fin 2 → ℂ)} (h : PureStabilizer ψ) : ∃ P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), IsHermitianPauli P ∧ IsHermitianPauli Q ∧ P ≠ 1 ∧ P ≠ -1 ∧ Q ≠ 1 ∧ Q ≠ -1 ∧ Q ≠ P ∧ Q ≠ -P ∧ P*Q=Q*P ∧ rankOneDensity ψ=jointProjector P Q := by
  obtain ⟨hn,P,Q,hP,hQ,hP1,hPn1,hQ1,hQn1,hne,hneg,hc,hPf,hQf⟩ := h
  refine ⟨P,Q,hP,hQ,hP1,hPn1,hQ1,hQn1,hne,hneg,hc,?_⟩
  apply Eq.symm
  apply trace_one_projection_eq_projector _
    (joint_hermitian P Q (hermitianPauli_hermitian hP) (hermitianPauli_hermitian hQ) hc)
    (joint_idempotent P Q (hermitianPauli_square hP) (hermitianPauli_square hQ) hc)
    ?_ ψ hn (joint_fixed P Q ψ hPf hQf)
  simp only [jointProjector,Matrix.trace_smul,Matrix.trace_add,
    hermitianPauli_trace_zero hP hP1 hPn1,hermitianPauli_trace_zero hQ hQ1 hQn1,
    independent_trace_zero hP hQ hne hneg,add_zero]
  norm_num [Matrix.trace_one]
private def PauliProductProjector (A : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : Prop := ∃ p q : Pauli,
  p ≠ .I ∧ q ≠ .I ∧ ∃ ep eq : Bool,
    A = spectral p (if ep then 1 else 0) ⊗ₖ spectral q (if eq then 1 else 0)
private theorem pauli_overlap_spectrum (p q : Pauli) (hp : p ≠ .I) (hq : q ≠ .I) (ep eq : Bool) : (spectral p (if ep then 1 else 0) * spectral q (if eq then 1 else 0)).trace = 0 ∨ (spectral p (if ep then 1 else 0) * spectral q (if eq then 1 else 0)).trace = 1/2 ∨ (spectral p (if ep then 1 else 0) * spectral q (if eq then 1 else 0)).trace = 1 := by
  cases p <;> cases q <;> cases ep <;> cases eq <;>
    norm_num [spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fin.sum_univ_two] at *
  all_goals norm_num [Complex.ext_iff,Complex.mul_re,Complex.mul_im]
private theorem projector_tensor (a b : (Fin 2 → ℂ)) : rankOneDensity (productVector a b)=rankOneDensity a ⊗ₖ rankOneDensity b := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [rankOneDensity,Matrix.vecMulVec_apply,productVector,star_mul,Matrix.kroneckerMap_apply,Function.uncurry_apply_pair,Matrix.vecMulVec_apply];ring
private theorem unitVector_smul {n : Type*} [Fintype n] (z : ℂ) (ψ : n → ℂ) : star (z • ψ) ⬝ᵥ (z • ψ) = (Complex.normSq z : ℂ)*(star ψ ⬝ᵥ ψ) := by
  simp only [dotProduct,Pi.star_apply,Pi.smul_apply,smul_eq_mul,star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.star_def];ring
private theorem equal_projectors_ray {ψ χ : (Fin 2 × Fin 2 → ℂ)} (hn : unitVector ψ) (he : rankOneDensity ψ=rankOneDensity χ) : ∃ z : ℂ,ψ=z • χ := by
  refine ⟨star χ ⬝ᵥ ψ,?_⟩
  have hψ : rankOneDensity ψ *ᵥ ψ=ψ := by
    ext i
    simp only [rankOneDensity,Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.star_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change ψ i*(star ψ ⬝ᵥ ψ)=ψ i
    rw [hn,mul_one]
  rw [he] at hψ
  calc
    ψ = rankOneDensity χ *ᵥ ψ := hψ.symm
    _ = (star χ ⬝ᵥ ψ) • χ := by
      ext i
      simp only [rankOneDensity,Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,
        Pi.star_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
private theorem PauliProductProjector_vector {ψ : (Fin 2 × Fin 2 → ℂ)} (hn : unitVector ψ) (h : PauliProductProjector (rankOneDensity ψ)) : ProductVector ψ := by
  obtain ⟨p,q,hp,hq,ep,eq,he⟩ := h
  have hpE := (spectral_stabilizer p (if ep then 1 else 0) hp).2.choose_spec.2.2.2.2.2
  have hqE := (spectral_stabilizer q (if eq then 1 else 0) hq).2.choose_spec.2.2.2.2.2
  have he' : rankOneDensity ψ = rankOneDensity
      (productVector (eigenVector p (if ep then 1 else 0)) (eigenVector q (if eq then 1 else 0))) := by
    rw [projector_tensor]
    exact he.trans (by rw [hpE,hqE]; rfl)
  obtain ⟨z,hz⟩ := equal_projectors_ray hn he'
  exact ⟨z • eigenVector p (if ep then 1 else 0),eigenVector q (if eq then 1 else 0),
    by rw [tensor_smul_left];exact hz⟩
private theorem quadratic_projector {n : Type*} [Fintype n] (z ψ : n → ℂ) : star z ⬝ᵥ (rankOneDensity ψ *ᵥ z) = (Complex.normSq (star z ⬝ᵥ ψ) : ℂ) := by
  simp only [rankOneDensity,Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [← Complex.mul_conj]
  simp only [map_sum,map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← Complex.star_def, star_star]
  ring
theorem ensemble_kernel {n ι : Type*} [Fintype n] [Fintype ι] (ψ : ι → n → ℂ) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (z : n → ℂ) (hzero : star z ⬝ᵥ ((∑ i,w i • rankOneDensity (ψ i)) *ᵥ z)=0) : ∀ i,0 < w i → star z ⬝ᵥ ψ i = 0 := by
  have he : ∑ i,w i*Complex.normSq (star z ⬝ᵥ ψ i)=0 := by
    have hC : ((∑ i,w i*Complex.normSq (star z ⬝ᵥ ψ i) : ℝ) : ℂ)=0 := by
      push_cast
      simpa only [Matrix.sum_mulVec,dotProduct_sum,Matrix.smul_mulVec,
        dotProduct_smul,quadratic_projector,Complex.real_smul,smul_eq_mul] using hzero
    exact Complex.ofReal_eq_zero.mp hC
  have hn : ∀ i ∈ (Finset.univ : Finset ι),0 ≤ w i*Complex.normSq (star z ⬝ᵥ ψ i) :=
    fun i _ => mul_nonneg (hw i) (Complex.normSq_nonneg _)
  intro i hi
  have hwi := (Finset.sum_eq_zero_iff_of_nonneg hn).mp he i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hwi).resolve_left (ne_of_gt hi))
private theorem support_of_relations {c s : ℝ} (hs : s ≠ 0) (ψ : (Fin 2 × Fin 2 → ℂ)) (h1 : ψ (0,1)=ψ (1,0)) (h2 : (s : ℂ)*ψ (0,1)=(c : ℂ)*ψ (1,1)) : ∃ α β : ℂ,ψ=supportVector c s α β := by
  let β : ℂ := ψ (1,1)/(s : ℂ)^2
  refine ⟨ψ (0,0)-β*(c : ℂ)^2,β,?_⟩
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [supportVector,productVector,b,β,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
  · ring
  · field_simp
    linear_combination h2
  · field_simp
    linear_combination h2 - (s : ℂ)*h1
  · field_simp
private def normal2 (c s : ℝ) : (Fin 2 × Fin 2 → ℂ) := (s : ℂ) • Pi.single (0,1) 1 - (c : ℂ) • Pi.single (1,1) 1
private theorem normal1_support (c s : ℝ) (α β : ℂ) : star (Pi.single (0,1) (1 : ℂ) - Pi.single (1,0) (1 : ℂ)) ⬝ᵥ supportVector c s α β=0 := by
  simp [Pi.single_apply,supportVector,productVector,b,dotProduct,Fintype.sum_prod_type,
    Fin.sum_univ_two,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]; ring
private theorem normal2_support (c s : ℝ) (α β : ℂ) : star (normal2 c s) ⬝ᵥ supportVector c s α β=0 := by
  simp [normal2,Pi.single_apply,supportVector,productVector,b,dotProduct,Fintype.sum_prod_type,
    Fin.sum_univ_two,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]; ring
private theorem rho_normal_zero (p c s : ℝ) (z : (Fin 2 × Fin 2 → ℂ)) (hu : star z ⬝ᵥ (productVector ![1, 0] ![1, 0])=0) (hv : star z ⬝ᵥ productVector (b c s) (b c s)=0) : star z ⬝ᵥ (rho p c s *ᵥ z)=0 := by
  simp only [rho,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,
    dotProduct_smul,quadratic_projector,hu,hv,Complex.normSq_zero,Complex.ofReal_zero,
    smul_zero,add_zero]
private theorem ensemble_support {ι : Type*} [Fintype ι] (p c s : ℝ) (hs : s ≠ 0) (ψ : ι → (Fin 2 × Fin 2 → ℂ)) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (he : (∑ i,w i • rankOneDensity (ψ i))=rho p c s) : ∀ i,0 < w i → ∃ α β : ℂ,ψ i=supportVector c s α β := by
  have hu1 : star (Pi.single (0,1) (1 : ℂ) - Pi.single (1,0) (1 : ℂ)) ⬝ᵥ (productVector ![1, 0] ![1, 0])=0 := by simpa [supportVector] using normal1_support c s 1 0
  have hv1 : star (Pi.single (0,1) (1 : ℂ) - Pi.single (1,0) (1 : ℂ)) ⬝ᵥ productVector (b c s) (b c s)=0 := by simpa [supportVector] using normal1_support c s 0 1
  have hu2 : star (normal2 c s) ⬝ᵥ (productVector ![1, 0] ![1, 0])=0 := by simpa [supportVector] using normal2_support c s 1 0
  have hv2 : star (normal2 c s) ⬝ᵥ productVector (b c s) (b c s)=0 := by simpa [supportVector] using normal2_support c s 0 1
  have hz1 := ensemble_kernel ψ w hw (Pi.single (0,1) (1 : ℂ) - Pi.single (1,0) (1 : ℂ)) (by rw [he];exact rho_normal_zero p c s _ hu1 hv1)
  have hz2 := ensemble_kernel ψ w hw (normal2 c s) (by rw [he];exact rho_normal_zero p c s _ hu2 hv2)
  intro i hi
  apply support_of_relations hs (ψ i)
  · have hh := hz1 i hi
    simpa [Pi.single_apply,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,← sub_eq_add_neg,sub_eq_zero] using hh
  · have hh := hz2 i hi
    simpa [normal2,Pi.single_apply,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,mul_comm,← sub_eq_add_neg,sub_eq_zero] using hh
private def coefficient01 (c s : ℝ) (A : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : ℂ :=
  (s : ℂ)^2*A (0,0) (1,1)-(c : ℂ)^2*A (1,1) (1,1)
private theorem coefficient01_projector (c s : ℝ) (α β : ℂ) : coefficient01 c s (rankOneDensity (supportVector c s α β)) = (s : ℂ)^4 * (α * star β) := by
  simp [coefficient01,rankOneDensity,Matrix.vecMulVec_apply,supportVector,productVector,b,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
  ring
private theorem coefficient01_rho (p c s : ℝ) : coefficient01 c s (rho p c s)=0 := by
  simp [coefficient01,rho,rankOneDensity,Matrix.vecMulVec_apply,productVector,b,Function.uncurry_apply_pair,Matrix.vecMulVec_apply]
  ring
private theorem ensemble_offdiag {ι : Type*} [Fintype ι] (p c s : ℝ) (hs : s ≠ 0) (α β : ι → ℂ) (w : ι → ℝ) (he : (∑ i,w i • rankOneDensity (supportVector c s (α i) (β i)))=rho p c s) : ∑ i,(w i : ℂ)*(α i*star (β i))=0 := by
  have hh := congrArg (coefficient01 c s) he
  rw [coefficient01_rho] at hh
  have hsum : coefficient01 c s (∑ i,w i • rankOneDensity (supportVector c s (α i) (β i))) =
      (s : ℂ)^4*(∑ i,(w i : ℂ)*(α i*star (β i))) := by
    unfold coefficient01
    simp only [Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul,
      Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hc := coefficient01_projector c s (α i) (β i)
    unfold coefficient01 at hc
    linear_combination (w i : ℂ)*hc
  rw [hsum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs))
private theorem real_cross_nonpos {α β : ℂ} (h : α=0 ∨ β=0 ∨ α = -β) : (α*star β).re ≤ 0 := by
  rcases h with rfl|rfl|rfl
  · simp
  · simp
  · simp only [neg_mul,Complex.neg_re,Complex.star_def,Complex.mul_conj,Complex.ofReal_re]
    exact neg_nonpos.mpr (Complex.normSq_nonneg β)
private theorem cross_zero_excludes_maxent {α β : ℂ} (hz : (α*star β).re=0) (hab : α = -β) : β=0 := by
  rw [hab] at hz
  simp only [neg_mul,Complex.neg_re,Complex.star_def,Complex.mul_conj,Complex.ofReal_re,
    neg_eq_zero] at hz
  exact Complex.normSq_eq_zero.mp hz
private theorem ensemble_no_entangled_coefficients {ι : Type*} [Fintype ι] (α β : ι → ℂ) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (hcross : ∑ i,(w i : ℂ)*(α i*star (β i))=0) (hclass : ∀ i,0 < w i → α i=0 ∨ β i=0 ∨ α i = -β i) : ∀ i,0 < w i → α i=0 ∨ β i=0 := by
  have hre : ∑ i,w i*(α i*star (β i)).re=0 := by
    have hh := congrArg Complex.re hcross
    rw [show (∑ i,(w i : ℂ)*(α i*star (β i))).re =
      ∑ i,((w i : ℂ)*(α i*star (β i))).re from
      map_sum Complex.reAddGroupHom _ _] at hh
    simpa only [Complex.re_ofReal_mul,Complex.zero_re] using hh
  have hn : ∀ i ∈ (Finset.univ : Finset ι),w i*(α i*star (β i)).re ≤ 0 := by
    intro i hi
    by_cases hz : w i=0
    · simp [hz]
    · exact mul_nonpos_of_nonneg_of_nonpos (hw i)
        (real_cross_nonpos (hclass i (lt_of_le_of_ne (hw i) (Ne.symm hz))))
  intro i hi
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hre i (Finset.mem_univ i)
  have hz0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hi)
  rcases hclass i hi with hα|hβ|hent
  · exact Or.inl hα
  · exact Or.inr hβ
  · exact Or.inr (cross_zero_excludes_maxent hz0 hent)
private theorem projector_smul {n : Type*} (z : ℂ) (a : n → ℂ) : rankOneDensity (z • a) = (Complex.normSq z : ℂ) • rankOneDensity a := by
  rw [Complex.normSq_eq_conj_mul_self]
  ext i j
  simp only [rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply,Pi.smul_apply,
    smul_eq_mul,star_mul,Matrix.smul_apply,← Complex.star_def]
  ring
private theorem unit_projector_ray {n : Type*} [Fintype n] {ψ χ : n → ℂ} (hψ : unitVector ψ) (hχ : unitVector χ) (z : ℂ) (hz : ψ=z • χ) : rankOneDensity ψ=rankOneDensity χ := by
  have hn : (Complex.normSq z : ℂ)=1 := by
    rw [hz,unitVector,unitVector_smul,hχ,mul_one] at hψ
    exact hψ
  rw [hz,projector_smul,hn,one_smul]
private theorem pauli_projector_trace (p : Pauli) (hp : p ≠ .I) (ep : Bool) : (spectral p (if ep then 1 else 0)).trace=1 := by
  cases p <;> cases ep <;>
    norm_num [spectral,pauliMatrix,qubitX,qubitZ,Matrix.trace,Matrix.diag,
      Matrix.mul_apply,Fin.sum_univ_two] at *
private theorem pauli_product_marginal {A : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (h : PauliProductProjector A) : ∃ p : Pauli, p ≠ .I ∧ ∃ ep : Bool, partialTraceRight A=spectral p (if ep then 1 else 0) := by
  obtain ⟨p,q,hp,hq,ep,eq,rfl⟩ := h
  refine ⟨p,hp,ep,?_⟩
  change partialTraceRight (Matrix.kronecker (spectral p (if ep then 1 else 0)) (spectral q (if eq then 1 else 0)))=_
  rw [partialTraceRight_kronecker,pauli_projector_trace q hq eq,one_smul]
private theorem product_marginal (a b : (Fin 2 → ℂ)) (hb : unitVector b) : partialTraceRight (rankOneDensity (productVector a b))=rankOneDensity a := by
  rw [projector_tensor]
  change partialTraceRight (Matrix.kronecker (rankOneDensity a) (rankOneDensity b))=_
  rw [partialTraceRight_kronecker,trace_projector,hb,one_smul]
private theorem trace_projector_overlap {n : Type*} [Fintype n] (a b : n → ℂ) : (rankOneDensity a * rankOneDensity b).trace=(Complex.normSq (star a ⬝ᵥ b) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,rankOneDensity,
    Matrix.vecMulVec_apply,Pi.star_apply]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [dotProduct,Pi.star_apply,map_sum,map_mul,← Complex.star_def,star_star,
    Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
private theorem unitary_unit (A : Matrix.unitaryGroup (Fin 2) ℂ) {a : (Fin 2 → ℂ)} (ha : unitVector a) : unitVector ((A : (Matrix (Fin 2) (Fin 2) ℂ))*ᵥ a) := by
  unfold unitVector at *
  rw [unitary_preserves_overlap _ (Matrix.mem_unitaryGroup_iff'.mp A.property)]
  exact ha
private theorem local_product_projector (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (a b : (Fin 2 → ℂ)) : localAction UA UB (rankOneDensity (productVector a b))= rankOneDensity (productVector ((UA : (Matrix (Fin 2) (Fin 2) ℂ))*ᵥ a) ((UB : (Matrix (Fin 2) (Fin 2) ℂ))*ᵥ b)) := by
  rw [localAction,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
    Matrix.star_eq_conjTranspose,← projector_conjugation,localMatrix,kronecker_mul_tensor]
private theorem local_pauli_overlap {c s : ℝ} (hcs : c^2+s^2=1) (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (hu : PauliProductProjector (localAction UA UB (rankOneDensity (productVector ![1, 0] ![1, 0])))) (hv : PauliProductProjector (localAction UA UB (rankOneDensity (productVector (b c s) (b c s))))) : c^2=0 ∨ c^2=1/2 ∨ c^2=1 := by
  obtain ⟨pa,hpa,ep,he⟩ := pauli_product_marginal hu
  obtain ⟨pb,hpb,eq,hf⟩ := pauli_product_marginal hv
  have hspectrum := pauli_overlap_spectrum pa pb hpa hpb ep eq
  rw [← he,← hf] at hspectrum
  rw [show (productVector ![1, 0] ![1, 0])=productVector ![1, 0] ![1, 0] from rfl,show productVector (b c s) (b c s)=productVector (b c s) (b c s) from rfl,
    local_product_projector,local_product_projector,
    product_marginal _ _ (unitary_unit UB unit_e0),
    product_marginal _ _ (unitary_unit UB (unit_b hcs)),trace_projector_overlap,
    unitary_preserves_overlap _ (Matrix.mem_unitaryGroup_iff'.mp UA.property)] at hspectrum
  have ho : star ![1, 0] ⬝ᵥ b c s=(c : ℂ) := by
    simp [b,dotProduct,Fin.sum_univ_two]
  rw [ho,Complex.normSq_ofReal] at hspectrum
  have hhalf : ((1/2 : ℝ) : ℂ)=(1/2 : ℂ) := by norm_num
  rw [← hhalf] at hspectrum
  have hR : c*c=0 ∨ c*c=1/2 ∨ c*c=1 := by exact_mod_cast hspectrum
  simpa only [← pow_two] using hR
private theorem local_inverse (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) : localMatrix UA⁻¹ UB⁻¹=(localMatrix UA UB)ᴴ := by
  simp [localMatrix,Matrix.conjTranspose_kronecker,Matrix.star_eq_conjTranspose]
private theorem local_mul_star (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) : localMatrix UA UB * (localMatrix UA UB)ᴴ=1 := by
  have hA : (UA : (Matrix (Fin 2) (Fin 2) ℂ))*(UA : (Matrix (Fin 2) (Fin 2) ℂ))ᴴ=1 := Matrix.mem_unitaryGroup_iff.mp UA.property
  have hB : (UB : (Matrix (Fin 2) (Fin 2) ℂ))*(UB : (Matrix (Fin 2) (Fin 2) ℂ))ᴴ=1 := Matrix.mem_unitaryGroup_iff.mp UB.property
  unfold localMatrix
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hA,hB,Matrix.one_kronecker_one]
private theorem local_inverse_vector (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (ψ : (Fin 2 × Fin 2 → ℂ)) : localMatrix UA UB *ᵥ (localMatrix UA⁻¹ UB⁻¹ *ᵥ ψ)=ψ := by
  rw [local_inverse,Matrix.mulVec_mulVec,local_mul_star,Matrix.one_mulVec]
private theorem pullback_ensemble {ι : Type*} [Fintype ι] (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) (ψ : ι → (Fin 2 × Fin 2 → ℂ)) (w : ι → ℝ) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) (he : (∑ i,w i • rankOneDensity (ψ i))=localAction UA UB ρ) : (∑ i,w i • rankOneDensity (localMatrix UA⁻¹ UB⁻¹ *ᵥ ψ i))=ρ := by
  simp_rw [projector_conjugation,local_inverse]
  calc
    _ = (localMatrix UA UB)ᴴ * (∑ i,w i • rankOneDensity (ψ i)) * localMatrix UA UB := by
      simp [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
    _ = ρ := by
      rw [he,localAction,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
        Matrix.star_eq_conjTranspose]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc (localMatrix UA UB)ᴴ,
        local_star_mul,Matrix.one_mul,Matrix.mul_one]
private def codeOp (i : Fin 32) : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  match i.val with
  | 0 => (pauliMatrix .I ⊗ₖ pauliMatrix .I)
  | 1 => (pauliMatrix .I ⊗ₖ pauliMatrix .X)
  | 2 => (pauliMatrix .I ⊗ₖ pauliMatrix .Y)
  | 3 => (pauliMatrix .I ⊗ₖ pauliMatrix .Z)
  | 4 => (pauliMatrix .X ⊗ₖ pauliMatrix .I)
  | 5 => (pauliMatrix .X ⊗ₖ pauliMatrix .X)
  | 6 => (pauliMatrix .X ⊗ₖ pauliMatrix .Y)
  | 7 => (pauliMatrix .X ⊗ₖ pauliMatrix .Z)
  | 8 => (pauliMatrix .Y ⊗ₖ pauliMatrix .I)
  | 9 => (pauliMatrix .Y ⊗ₖ pauliMatrix .X)
  | 10 => (pauliMatrix .Y ⊗ₖ pauliMatrix .Y)
  | 11 => (pauliMatrix .Y ⊗ₖ pauliMatrix .Z)
  | 12 => (pauliMatrix .Z ⊗ₖ pauliMatrix .I)
  | 13 => (pauliMatrix .Z ⊗ₖ pauliMatrix .X)
  | 14 => (pauliMatrix .Z ⊗ₖ pauliMatrix .Y)
  | 15 => (pauliMatrix .Z ⊗ₖ pauliMatrix .Z)
  | 16 => -(pauliMatrix .I ⊗ₖ pauliMatrix .I)
  | 17 => -(pauliMatrix .I ⊗ₖ pauliMatrix .X)
  | 18 => -(pauliMatrix .I ⊗ₖ pauliMatrix .Y)
  | 19 => -(pauliMatrix .I ⊗ₖ pauliMatrix .Z)
  | 20 => -(pauliMatrix .X ⊗ₖ pauliMatrix .I)
  | 21 => -(pauliMatrix .X ⊗ₖ pauliMatrix .X)
  | 22 => -(pauliMatrix .X ⊗ₖ pauliMatrix .Y)
  | 23 => -(pauliMatrix .X ⊗ₖ pauliMatrix .Z)
  | 24 => -(pauliMatrix .Y ⊗ₖ pauliMatrix .I)
  | 25 => -(pauliMatrix .Y ⊗ₖ pauliMatrix .X)
  | 26 => -(pauliMatrix .Y ⊗ₖ pauliMatrix .Y)
  | 27 => -(pauliMatrix .Y ⊗ₖ pauliMatrix .Z)
  | 28 => -(pauliMatrix .Z ⊗ₖ pauliMatrix .I)
  | 29 => -(pauliMatrix .Z ⊗ₖ pauliMatrix .X)
  | 30 => -(pauliMatrix .Z ⊗ₖ pauliMatrix .Y)
  | 31 => -(pauliMatrix .Z ⊗ₖ pauliMatrix .Z)
  | _ => 1
private theorem hermitianPauli_code {A : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (h : IsHermitianPauli A) : ∃ i : Fin 32,A=codeOp i := by
  obtain ⟨a,b,rfl|rfl⟩ := h <;> cases a <;> cases b
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩
  · exact ⟨10,rfl⟩
  · exact ⟨11,rfl⟩
  · exact ⟨12,rfl⟩
  · exact ⟨13,rfl⟩
  · exact ⟨14,rfl⟩
  · exact ⟨15,rfl⟩
  · exact ⟨16,rfl⟩
  · exact ⟨17,rfl⟩
  · exact ⟨18,rfl⟩
  · exact ⟨19,rfl⟩
  · exact ⟨20,rfl⟩
  · exact ⟨21,rfl⟩
  · exact ⟨22,rfl⟩
  · exact ⟨23,rfl⟩
  · exact ⟨24,rfl⟩
  · exact ⟨25,rfl⟩
  · exact ⟨26,rfl⟩
  · exact ⟨27,rfl⟩
  · exact ⟨28,rfl⟩
  · exact ⟨29,rfl⟩
  · exact ⟨30,rfl⟩
  · exact ⟨31,rfl⟩
private def codeNum (i : Fin 32) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt :=
  match i.val with
  | 0 => (pauliZ .I ⊗ₖ pauliZ .I)
  | 1 => (pauliZ .I ⊗ₖ pauliZ .X)
  | 2 => (pauliZ .I ⊗ₖ pauliZ .Y)
  | 3 => (pauliZ .I ⊗ₖ pauliZ .Z)
  | 4 => (pauliZ .X ⊗ₖ pauliZ .I)
  | 5 => (pauliZ .X ⊗ₖ pauliZ .X)
  | 6 => (pauliZ .X ⊗ₖ pauliZ .Y)
  | 7 => (pauliZ .X ⊗ₖ pauliZ .Z)
  | 8 => (pauliZ .Y ⊗ₖ pauliZ .I)
  | 9 => (pauliZ .Y ⊗ₖ pauliZ .X)
  | 10 => (pauliZ .Y ⊗ₖ pauliZ .Y)
  | 11 => (pauliZ .Y ⊗ₖ pauliZ .Z)
  | 12 => (pauliZ .Z ⊗ₖ pauliZ .I)
  | 13 => (pauliZ .Z ⊗ₖ pauliZ .X)
  | 14 => (pauliZ .Z ⊗ₖ pauliZ .Y)
  | 15 => (pauliZ .Z ⊗ₖ pauliZ .Z)
  | 16 => -(pauliZ .I ⊗ₖ pauliZ .I)
  | 17 => -(pauliZ .I ⊗ₖ pauliZ .X)
  | 18 => -(pauliZ .I ⊗ₖ pauliZ .Y)
  | 19 => -(pauliZ .I ⊗ₖ pauliZ .Z)
  | 20 => -(pauliZ .X ⊗ₖ pauliZ .I)
  | 21 => -(pauliZ .X ⊗ₖ pauliZ .X)
  | 22 => -(pauliZ .X ⊗ₖ pauliZ .Y)
  | 23 => -(pauliZ .X ⊗ₖ pauliZ .Z)
  | 24 => -(pauliZ .Y ⊗ₖ pauliZ .I)
  | 25 => -(pauliZ .Y ⊗ₖ pauliZ .X)
  | 26 => -(pauliZ .Y ⊗ₖ pauliZ .Y)
  | 27 => -(pauliZ .Y ⊗ₖ pauliZ .Z)
  | 28 => -(pauliZ .Z ⊗ₖ pauliZ .I)
  | 29 => -(pauliZ .Z ⊗ₖ pauliZ .X)
  | 30 => -(pauliZ .Z ⊗ₖ pauliZ .Y)
  | 31 => -(pauliZ .Z ⊗ₖ pauliZ .Z)
  | _ => 1
private def jointNum (i j : Fin 32) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt :=
  1 + codeNum i + codeNum j + codeNum i * codeNum j
private def certificate (i j : Fin 32) : Prop :=
  codeNum i = 1 ∨ codeNum i = -1 ∨ codeNum j = 1 ∨ codeNum j = -1 ∨
  codeNum j = codeNum i ∨ codeNum j = -codeNum i ∨
  codeNum i * codeNum j ≠ codeNum j * codeNum i ∨
  (∃ p q : Pauli, p ≠ .I ∧ q ≠ .I ∧ ∃ ep eq : Bool,
    jointNum i j = (1 + if ep then -pauliZ p else pauliZ p) ⊗ₖ
      (1 + if eq then -pauliZ q else pauliZ q)) ∨
  (∀ a b : Fin 2, ∑ k : Fin 2, jointNum i j (a,k) (b,k) =
    (2 : GaussianInt) * (1 : Matrix (Fin 2) (Fin 2) GaussianInt) a b)
private theorem certificate_0 : ∀ j : Fin 32, certificate 0 j := by unfold certificate; decide +kernel
private theorem certificate_1 : ∀ j : Fin 32, certificate 1 j := by unfold certificate; decide +kernel
private theorem certificate_2 : ∀ j : Fin 32, certificate 2 j := by unfold certificate; decide +kernel
private theorem certificate_3 : ∀ j : Fin 32, certificate 3 j := by unfold certificate; decide +kernel
private theorem certificate_4 : ∀ j : Fin 32, certificate 4 j := by unfold certificate; decide +kernel
private theorem certificate_5 : ∀ j : Fin 32, certificate 5 j := by unfold certificate; decide +kernel
private theorem certificate_6 : ∀ j : Fin 32, certificate 6 j := by unfold certificate; decide +kernel
private theorem certificate_7 : ∀ j : Fin 32, certificate 7 j := by unfold certificate; decide +kernel
private theorem certificate_8 : ∀ j : Fin 32, certificate 8 j := by unfold certificate; decide +kernel
private theorem certificate_9 : ∀ j : Fin 32, certificate 9 j := by unfold certificate; decide +kernel
private theorem certificate_10 : ∀ j : Fin 32, certificate 10 j := by unfold certificate; decide +kernel
private theorem certificate_11 : ∀ j : Fin 32, certificate 11 j := by unfold certificate; decide +kernel
private theorem certificate_12 : ∀ j : Fin 32, certificate 12 j := by unfold certificate; decide +kernel
private theorem certificate_13 : ∀ j : Fin 32, certificate 13 j := by unfold certificate; decide +kernel
private theorem certificate_14 : ∀ j : Fin 32, certificate 14 j := by unfold certificate; decide +kernel
private theorem certificate_15 : ∀ j : Fin 32, certificate 15 j := by unfold certificate; decide +kernel
private theorem certificate_16 : ∀ j : Fin 32, certificate 16 j := by unfold certificate; decide +kernel
private theorem certificate_17 : ∀ j : Fin 32, certificate 17 j := by unfold certificate; decide +kernel
private theorem certificate_18 : ∀ j : Fin 32, certificate 18 j := by unfold certificate; decide +kernel
private theorem certificate_19 : ∀ j : Fin 32, certificate 19 j := by unfold certificate; decide +kernel
private theorem certificate_20 : ∀ j : Fin 32, certificate 20 j := by unfold certificate; decide +kernel
private theorem certificate_21 : ∀ j : Fin 32, certificate 21 j := by unfold certificate; decide +kernel
private theorem certificate_22 : ∀ j : Fin 32, certificate 22 j := by unfold certificate; decide +kernel
private theorem certificate_23 : ∀ j : Fin 32, certificate 23 j := by unfold certificate; decide +kernel
private theorem certificate_24 : ∀ j : Fin 32, certificate 24 j := by unfold certificate; decide +kernel
private theorem certificate_25 : ∀ j : Fin 32, certificate 25 j := by unfold certificate; decide +kernel
private theorem certificate_26 : ∀ j : Fin 32, certificate 26 j := by unfold certificate; decide +kernel
private theorem certificate_27 : ∀ j : Fin 32, certificate 27 j := by unfold certificate; decide +kernel
private theorem certificate_28 : ∀ j : Fin 32, certificate 28 j := by unfold certificate; decide +kernel
private theorem certificate_29 : ∀ j : Fin 32, certificate 29 j := by unfold certificate; decide +kernel
private theorem certificate_30 : ∀ j : Fin 32, certificate 30 j := by unfold certificate; decide +kernel
private theorem certificate_31 : ∀ j : Fin 32, certificate 31 j := by unfold certificate; decide +kernel
private theorem pauliZ_cast (p : Pauli) : (pauliZ p).map GaussianInt.toComplex = pauliMatrix p := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix,pauliZ,qubitX,qubitZ,GaussianInt.toComplex_def]
private theorem kronecker_cast (A B : Matrix (Fin 2) (Fin 2) GaussianInt) : (A ⊗ₖ B).map GaussianInt.toComplex = A.map GaussianInt.toComplex ⊗ₖ B.map GaussianInt.toComplex := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.kroneckerMap_apply]
private theorem code_cast (i : Fin 32) : (codeNum i).map GaussianInt.toComplex = codeOp i := by
  have hneg (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt) :
      (-A).map GaussianInt.toComplex = -A.map GaussianInt.toComplex :=
    map_neg GaussianInt.toComplex.mapMatrix A
  fin_cases i <;> simp only [codeNum,codeOp,hneg,kronecker_cast,pauliZ_cast]
private theorem joint_cast (i j : Fin 32) : (jointNum i j).map GaussianInt.toComplex = 1 + codeOp i + codeOp j + codeOp i * codeOp j := by
  change GaussianInt.toComplex.mapMatrix (jointNum i j) = _
  simp only [jointNum,map_add,map_one,map_mul,RingHom.mapMatrix_apply,code_cast]
private theorem row_classification (i j : Fin 32) (h : certificate i j) (hP1 : codeOp i ≠ 1) (hPn1 : codeOp i ≠ -1) (hQ1 : codeOp j ≠ 1) (hQn1 : codeOp j ≠ -1) (hne : codeOp j ≠ codeOp i) (hneg : codeOp j ≠ -codeOp i) (hc : codeOp i * codeOp j = codeOp j * codeOp i) : PauliProductProjector (jointProjector (codeOp i) (codeOp j)) ∨ partialTraceRight (jointProjector (codeOp i) (codeOp j)) = (1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hone : (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt).map GaussianInt.toComplex = 1 :=
    map_one GaussianInt.toComplex.mapMatrix
  have hnegmap (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt) :
      (-A).map GaussianInt.toComplex = -A.map GaussianInt.toComplex :=
    map_neg GaussianInt.toComplex.mapMatrix A
  rcases h with h|h|h|h|h|h|h|h|h
  · exact False.elim (hP1 (by rw [← code_cast,h,hone]))
  · exact False.elim (hPn1 (by rw [← code_cast,h,hnegmap,hone]))
  · exact False.elim (hQ1 (by rw [← code_cast,h,hone]))
  · exact False.elim (hQn1 (by rw [← code_cast,h,hnegmap,hone]))
  · exact False.elim (hne (by rw [← code_cast,← code_cast,h]))
  · exact False.elim (hneg (by rw [← code_cast,← code_cast,h,hnegmap]))
  · apply False.elim
    apply h
    have hm : ((codeNum i * codeNum j).map GaussianInt.toComplex) =
        ((codeNum j * codeNum i).map GaussianInt.toComplex) := by
      change GaussianInt.toComplex.mapMatrix _ = GaussianInt.toComplex.mapMatrix _
      simpa only [map_mul,RingHom.mapMatrix_apply,code_cast] using hc
    apply Matrix.ext
    intro a b
    exact GaussianInt.toComplex_injective (congrFun (congrFun hm a) b)
  · obtain ⟨p,q,hp,hq,ep,eq,he⟩ := h
    left
    refine ⟨p,q,hp,hq,ep,eq,?_⟩
    have hm := congrArg (fun A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) GaussianInt =>
      A.map GaussianInt.toComplex) he
    rw [joint_cast,kronecker_cast] at hm
    have hsigned (p : Pauli) (e : Bool) :
        (1 + if e then -pauliZ p else pauliZ p).map GaussianInt.toComplex =
          1 + if e then -pauliMatrix p else pauliMatrix p := by
      change GaussianInt.toComplex.mapMatrix _ = _
      cases e <;> simp only [Bool.false_eq_true,if_false,if_true,map_add,map_neg,map_one,
        RingHom.mapMatrix_apply,pauliZ_cast]
    rw [hsigned,hsigned] at hm
    unfold jointProjector
    rw [hm]
    cases ep <;> cases eq <;>
      simp only [spectral,Bool.false_eq_true,if_false,if_true,pow_zero,pow_one,one_smul,neg_one_smul,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Fin.val_zero,Fin.val_one] <;> congr 1 <;> norm_num
  · right
    ext a b
    have hh := congrArg GaussianInt.toComplex (h a b)
    have hm : (∑ k : Fin 2,(1 + codeOp i + codeOp j + codeOp i * codeOp j) (a,k) (b,k)) =
        (2 : ℂ) * (1 : (Matrix (Fin 2) (Fin 2) ℂ)) a b := by
      simpa only [map_sum,map_mul,map_ofNat,Matrix.one_apply,apply_ite,map_one,map_zero,
        ← Matrix.map_apply,← Matrix.sum_apply,joint_cast] using hh
    simp only [partialTraceRight,jointProjector,Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum]
    rw [hm]
    simp [Matrix.smul_apply,smul_eq_mul]; ring
private theorem joint_pauli_classification {P Q : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)} (hP : IsHermitianPauli P) (hQ : IsHermitianPauli Q) (hP1 : P ≠ 1) (hPn1 : P ≠ -1) (hQ1 : Q ≠ 1) (hQn1 : Q ≠ -1) (hne : Q ≠ P) (hneg : Q ≠ -P) (hc : P*Q=Q*P) : PauliProductProjector (jointProjector P Q) ∨ partialTraceRight (jointProjector P Q)=(1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) := by
  obtain ⟨i,rfl⟩ := hermitianPauli_code hP
  obtain ⟨j,rfl⟩ := hermitianPauli_code hQ
  apply row_classification i j _ hP1 hPn1 hQ1 hQn1 hne hneg hc
  fin_cases i
  · exact certificate_0 j
  · exact certificate_1 j
  · exact certificate_2 j
  · exact certificate_3 j
  · exact certificate_4 j
  · exact certificate_5 j
  · exact certificate_6 j
  · exact certificate_7 j
  · exact certificate_8 j
  · exact certificate_9 j
  · exact certificate_10 j
  · exact certificate_11 j
  · exact certificate_12 j
  · exact certificate_13 j
  · exact certificate_14 j
  · exact certificate_15 j
  · exact certificate_16 j
  · exact certificate_17 j
  · exact certificate_18 j
  · exact certificate_19 j
  · exact certificate_20 j
  · exact certificate_21 j
  · exact certificate_22 j
  · exact certificate_23 j
  · exact certificate_24 j
  · exact certificate_25 j
  · exact certificate_26 j
  · exact certificate_27 j
  · exact certificate_28 j
  · exact certificate_29 j
  · exact certificate_30 j
  · exact certificate_31 j
private theorem stabilizer_projector_classification {ψ : (Fin 2 × Fin 2 → ℂ)} (h : PureStabilizer ψ) : PauliProductProjector (rankOneDensity ψ) ∨ MaximallyEntangled ψ := by
  obtain ⟨P,Q,hP,hQ,hP1,hPn1,hQ1,hQn1,hne,hneg,hc,he⟩ := stabilizer_projector h
  rcases joint_pauli_classification hP hQ hP1 hPn1 hQ1 hQn1 hne hneg hc with hp|hm
  · exact Or.inl (he ▸ hp)
  · exact Or.inr ⟨h.1,he ▸ hm⟩
private theorem stabilizer_classification {ψ : (Fin 2 × Fin 2 → ℂ)} (h : PureStabilizer ψ) : ProductVector ψ ∨ MaximallyEntangled ψ := by
  rcases stabilizer_projector_classification h with hp|hm
  · exact Or.inl (PauliProductProjector_vector h.1 hp)
  · exact Or.inr hm
private theorem rho_ne_u {p c s : ℝ} (hp1 : p < 1) (hs : 0 < s) : rho p c s ≠ rankOneDensity (productVector ![1, 0] ![1, 0]) := by
  intro he
  have hh := congrFun (congrFun he (1,1)) (1,1)
  simp [rho,rankOneDensity,Matrix.vecMulVec_apply,productVector,b,Function.uncurry_apply_pair,Matrix.vecMulVec_apply] at hh
  rcases hh with h|h
  · have hR : 1-p=0 := by exact_mod_cast h
    linarith
  · have hR : s=0 := by exact_mod_cast h
    linarith
private theorem rho_ne_v {p c s : ℝ} (hp : 0 < p) (hs : 0 < s) : rho p c s ≠ rankOneDensity (productVector (b c s) (b c s)) := by
  intro he
  have hh := congrFun (congrFun he (1,1)) (1,1)
  simp [rho,rankOneDensity,Matrix.vecMulVec_apply,productVector,b,Function.uncurry_apply_pair,Matrix.vecMulVec_apply] at hh
  have hR : (1-p)*(s*s*(s*s))=s*s*(s*s) := by exact_mod_cast hh
  have hpos : 0 < p*(s*s*(s*s)) := by positivity
  nlinarith
private theorem ensemble_both_rays {ι : Type*} [Fintype ι] {p c s : ℝ} (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s) (ψ : ι → (Fin 2 × Fin 2 → ℂ)) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i) (hwsum : ∑ i,w i=1) (he : (∑ i,w i • rankOneDensity (ψ i))=rho p c s) (hr : ∀ i,0 < w i → rankOneDensity (ψ i)=rankOneDensity (productVector ![1, 0] ![1, 0]) ∨ rankOneDensity (ψ i)=rankOneDensity (productVector (b c s) (b c s))) : (∃ i,0 < w i ∧ rankOneDensity (ψ i)=rankOneDensity (productVector ![1, 0] ![1, 0])) ∧ (∃ i,0 < w i ∧ rankOneDensity (ψ i)=rankOneDensity (productVector (b c s) (b c s))) := by
  constructor
  · by_contra hnone
    apply rho_ne_v hp hs
    rw [← he]
    calc
      _ = ∑ i,w i • rankOneDensity (productVector (b c s) (b c s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hz : w i=0
        · simp [hz]
        · have hpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hz)
          rcases hr i hpos with hu|hv
          · exact False.elim (hnone ⟨i,hpos,hu⟩)
          · rw [hv]
      _ = rankOneDensity (productVector (b c s) (b c s)) := by rw [← Finset.sum_smul,hwsum,one_smul]
  · by_contra hnone
    apply rho_ne_u hp1 hs
    rw [← he]
    calc
      _ = ∑ i,w i • rankOneDensity (productVector ![1, 0] ![1, 0]) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hz : w i=0
        · simp [hz]
        · have hpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hz)
          rcases hr i hpos with hu|hv
          · rw [hu]
          · exact False.elim (hnone ⟨i,hpos,hv⟩)
      _ = rankOneDensity (productVector ![1, 0] ![1, 0]) := by rw [← Finset.sum_smul,hwsum,one_smul]
private theorem family_nonmembership {p c s : ℝ} (hpar : FamilyParameters p c s) (UA UB : Matrix.unitaryGroup (Fin 2) ℂ) : localAction UA UB (rho p c s) ∉ STAB := by
  obtain ⟨hp,hp1,hc,hs,hcs,hneq⟩ := hpar
  intro hstab
  obtain ⟨ι,inst,w,A,hw,hwsum,hA,hensemble⟩ :=
    mem_convexHull_iff_exists_fintype.mp hstab
  letI := inst
  choose φ hφ hproj using hA
  have hE : (∑ i,w i • rankOneDensity (φ i))=localAction UA UB (rho p c s) := by
    simpa only [hproj] using hensemble
  let χ : ι → (Fin 2 × Fin 2 → ℂ) := fun i => localMatrix UA⁻¹ UB⁻¹ *ᵥ φ i
  have hχunit : ∀ i,unitVector (χ i) := fun i => local_preserves_unit _ _ (hφ i).1
  have hχE : (∑ i,w i • rankOneDensity (χ i))=rho p c s := pullback_ensemble _ _ _ _ _ hE
  have hsupport := ensemble_support p c s (ne_of_gt hs) χ w hw hχE
  have hcoeff : ∀ i,∃ α β : ℂ,0 < w i → χ i=supportVector c s α β := by
    intro i
    by_cases hi : 0 < w i
    · obtain ⟨α,β,he⟩ := hsupport i hi
      exact ⟨α,β,fun _ => he⟩
    · exact ⟨0,0,fun hi' => False.elim (hi hi')⟩
  choose α β hab using hcoeff
  have hαβE : (∑ i,w i • rankOneDensity (supportVector c s (α i) (β i)))=rho p c s := by
    rw [← hχE]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : w i=0
    · simp [hz]
    · rw [hab i (lt_of_le_of_ne (hw i) (Ne.symm hz))]
  have hclass : ∀ i,0 < w i → α i=0 ∨ β i=0 ∨ α i = -β i := by
    intro i hi
    rcases stabilizer_classification (hφ i) with hproduct|hent
    · have hχprod := local_preserves_product UA⁻¹ UB⁻¹ hproduct
      change ProductVector (χ i) at hχprod
      rw [hab i hi] at hχprod
      rcases (support_product_iff (ne_of_gt hs) _ _).mp hχprod with hα|hβ
      · exact Or.inl hα
      · exact Or.inr (Or.inl hβ)
    · have hχent := local_preserves_maxent UA⁻¹ UB⁻¹ hent
      change MaximallyEntangled (χ i) at hχent
      rw [hab i hi] at hχent
      exact Or.inr (Or.inr (support_maxent_ray (ne_of_gt hc) (ne_of_gt hs) hcs _ _ hχent))
  have hproductcoeff := ensemble_no_entangled_coefficients α β w hw
    (ensemble_offdiag p c s (ne_of_gt hs) α β w hαβE) hclass
  have hnotent : ∀ i,0 < w i → ¬MaximallyEntangled (χ i) := by
    intro i hi hχent
    rw [hab i hi] at hχent
    have hopposite := support_maxent_ray (ne_of_gt hc) (ne_of_gt hs) hcs _ _ hχent
    rcases hproductcoeff i hi with hzero|hzero
    · have hβzero : β i=0 := by simpa [hzero] using hopposite.symm
      have hunit := hχent.1
      simp [hzero,hβzero,supportVector,unitVector] at hunit
    · have hαzero : α i=0 := by simpa [hzero] using hopposite
      have hunit := hχent.1
      simp [hzero,hαzero,supportVector,unitVector] at hunit
  have hrays : ∀ i,0 < w i → rankOneDensity (χ i)=rankOneDensity (productVector ![1, 0] ![1, 0]) ∨ rankOneDensity (χ i)=rankOneDensity (productVector (b c s) (b c s)) := by
    intro i hi
    rcases hproductcoeff i hi with hα|hβ
    · right
      apply unit_projector_ray (hχunit i) (unit_tensor (unit_b hcs) (unit_b hcs)) (β i)
      simp [hab i hi,hα,supportVector]
    · left
      apply unit_projector_ray (hχunit i) (unit_tensor unit_e0 unit_e0) (α i)
      simp [hab i hi,hβ,supportVector]
  obtain ⟨⟨i,hi,hiu⟩,⟨j,hj,hjv⟩⟩ := ensemble_both_rays hp hp1 hs χ w hw hwsum hχE hrays
  have hPPP : ∀ k,0 < w k → PauliProductProjector (localAction UA UB (rankOneDensity (χ k))) := by
    intro k hk
    have he : rankOneDensity (φ k)=localAction UA UB (rankOneDensity (χ k)) := by
      rw [localAction,D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
        Matrix.star_eq_conjTranspose,← projector_conjugation]
      dsimp [χ]
      rw [local_inverse_vector]
    rcases stabilizer_projector_classification (hφ k) with hprod|hent
    · exact he ▸ hprod
    · exact False.elim (hnotent k hk (local_preserves_maxent UA⁻¹ UB⁻¹ hent))
  have hpu := hPPP i hi
  have hpv := hPPP j hj
  rw [hiu] at hpu
  rw [hjv] at hpv
  rcases local_pauli_overlap hcs UA UB hpu hpv with hzero|hhalf|hone
  · nlinarith
  · exact hneq hhalf
  · nlinarith
private theorem family_result : FamilyClaim := by
  intro p c s hpar
  exact ⟨rho_density (le_of_lt hpar.1) (le_of_lt hpar.2.1) hpar.2.2.2.2.1,
    rho_separable (le_of_lt hpar.1) (le_of_lt hpar.2.1) hpar.2.2.2.2.1,
    family_nonmembership hpar⟩
theorem result : claim := by
  refine ⟨rho (1/2) (3/5) (4/5),?_⟩
  apply family_result
  norm_num [FamilyParameters]
#print axioms family_result
#print axioms result
end
end D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
