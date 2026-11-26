/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Exact heralded reversal from the Bell-complement output kernel. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
import D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction

/-! Direct Kraus recovery from the Bell-complement output kernel.
The reference index comes first, as in `recovery-proof.txt` (Direct Kraus
construction for formalization). -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open UnitaryReconstruction.LiuWildChoiObstruction (bell bell_norm diagonalVector outer)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act amp amp_entry)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceLeft_kronecker partialTraceLeft_posSemidef)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)

namespace D5.S3.Quantum.Divergence.ConditionalExpansion

variable {A B I J : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype I] [Fintype J]

/-- Finite Kraus amplification on the second factor. -/
def amplifyKraus {S : Type*} [Fintype S] [DecidableEq S]
    (K : I → Matrix B A ℂ) (X : Matrix (S × A) (S × A) ℂ) :
    Matrix (S × B) (S × B) ℂ :=
  ∑ i, ((1 : Matrix S S ℂ) ⊗ₖ K i) * X * ((1 : Matrix S S ℂ) ⊗ₖ K i)ᴴ

/-- Conjugate reshaping with the normalized Bell factor. -/
def bellRecoveryKraus (v : J → A × B → ℂ) (j : J) : Matrix A B ℂ :=
  (↑(Real.sqrt (Fintype.card A)) : ℂ)⁻¹ • Matrix.of (fun a b => star (v j (a, b)))

private theorem congruence_outer {m n : Type*} [Fintype n]
    (M : Matrix m n ℂ) (x : n → ℂ) : M * outer x * Mᴴ = outer (M *ᵥ x) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

private theorem trace_outer_mul_outer {n : Type*} [Fintype n] (x y : n → ℂ) :
    (outer x * outer y).trace = star (star y ⬝ᵥ x) * (star y ⬝ᵥ x) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_comm x (star y), Matrix.star_dotProduct x y]

private theorem one_kronecker_mulVec_entry {S m n : Type*} [Fintype S] [DecidableEq S]
    [Fintype n] (M : Matrix m n ℂ) (x : S × n → ℂ) (s : S) (a : m) :
    (((1 : Matrix S S ℂ) ⊗ₖ M) *ᵥ x) (s, a) = ∑ b, M a b * x (s, b) := by
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.kronecker_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

/-- The finite amplification agrees with the existing canonical channel action
whenever `K` is a Kraus representation of that channel. -/
private theorem amp_eq_amplifyKraus {S : Type*} [Fintype S] [DecidableEq S]
    (N : QuantumChannel A B) (K : I → Matrix B A ℂ)
    (hK : ∀ X : Matrix A A ℂ, act N X = MatrixMap.of_kraus K K X)
    (X : Matrix (S × A) (S × A) ℂ) : amp N X = amplifyKraus K X := by
  classical
  apply Matrix.ext
  rintro ⟨r, b⟩ ⟨s, b'⟩
  let Y : Matrix A A ℂ := Matrix.of (fun a a' => X (r, a) (s, a'))
  rw [amp_entry]
  change act N Y b b' = _
  rw [hK Y]
  simp only [amplifyKraus, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  let T := (1 : Matrix S S ℂ) ⊗ₖ K i
  change (K i * Y * (K i)ᴴ) b b' = (T * X * Tᴴ) (r, b) (s, b')
  have hleft (a' : A) : (T * X) (r, b) (s, a') = (K i * Y) b a' :=
    one_kronecker_mulVec_entry (K i) (X.col (s, a')) r b
  symm
  calc
    (T * X * Tᴴ) (r, b) (s, b') = (star (T *ᵥ star ((T * X).row (r, b)))) (s, b') :=
      congrFun (Matrix.vecMul_conjTranspose T ((T * X).row (r, b))) (s, b')
    _ = (K i * Y * (K i)ᴴ) b b' := by
      change (star (((1 : Matrix S S ℂ) ⊗ₖ K i) *ᵥ star ((T * X).row (r, b))))
        (s, b') = ∑ a', (K i * Y) b a' * (K i)ᴴ a' b'
      rw [Pi.star_apply, one_kronecker_mulVec_entry, star_sum]
      simp only [star_mul, Pi.star_apply, star_star, Matrix.row_apply, hleft,
        Matrix.conjTranspose_apply]

/-- The kernel condition says that the rank-one matrices of `v` sum to the
orthogonal kernel projection. An orthonormal basis of the kernel has this
property. The theorem also allows a finite family with the same Gram sum.
The weight is given as a complex trace quotient and is real nonnegative in
`ComplexOrder`. For arbitrary `K` the input family can have any normalization. -/
theorem direct_bell_kernel_recovery [Nonempty A]
    (K : I → Matrix B A ℂ) (v : J → A × B → ℂ)
    (hkernel : (∑ j, outer (v j)) =
      1 - spectralSupport (amplifyKraus K (1 - outer (bell A)))) :
    let P := outer (bell A)
    let B₀ := amplifyKraus K (1 - P)
    let X₀ := amplifyKraus K P
    let Q := ∑ j, outer (v j)
    let R := bellRecoveryKraus v
    let d : ℂ := Fintype.card A
    let p := (Q * X₀).trace / d ^ 2
    B₀.PosSemidef ∧ IsStarProjection Q ∧
    (∀ x : A × B → ℂ, B₀ *ᵥ x = 0 ↔ Q *ᵥ x = x) ∧
    (∑ j, (R j)ᴴ * R j) = d⁻¹ • partialTraceLeft Q ∧
    (∑ j, (R j)ᴴ * R j) ≤ (1 : Matrix B B ℂ) ∧
    (MatrixMap.of_kraus R R).IsCompletelyPositive ∧ 0 ≤ p ∧
    ∀ X : Matrix A A ℂ, MatrixMap.of_kraus R R (MatrixMap.of_kraus K K X) = p • X := by
  classical
  let Φ := bell A
  let P := outer Φ
  let D := (1 : Matrix (A × A) (A × A) ℂ) - P
  let T : I → Matrix (A × B) (A × A) ℂ := fun i => (1 : Matrix A A ℂ) ⊗ₖ K i
  let B₀ := amplifyKraus K D
  let X₀ := amplifyKraus K P
  let Q := ∑ j, outer (v j)
  let R := bellRecoveryKraus v
  let d : ℂ := Fintype.card A
  let δ := d⁻¹
  let s : ℂ := (↑(Real.sqrt (Fintype.card A)) : ℂ)⁻¹
  have hd : d ≠ 0 := by
    change (Fintype.card A : ℂ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hδreal : δ = (↑((Fintype.card A : ℝ)⁻¹) : ℂ) := by
    simp only [δ, d, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hδstar : star δ = δ := by rw [hδreal]; simp
  have hsstar : star s = s := by
    rw [show s = (↑((Real.sqrt (Fintype.card A))⁻¹) : ℂ) by
      simp only [s, Complex.ofReal_inv]]
    simp
  have hss : s * s = δ := by
    have hsq : (↑(Real.sqrt (Fintype.card A)) : ℂ) ^ 2 = d := by
      change (↑(Real.sqrt (Fintype.card A)) : ℂ) ^ 2 = (Fintype.card A : ℂ)
      exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card A)
    calc
      s * s = ((↑(Real.sqrt (Fintype.card A)) : ℂ) ^ 2)⁻¹ := by
        rw [← pow_two]
        simp only [s, inv_pow]
      _ = δ := by simp only [hsq, δ]
  have hP : IsStarProjection P := by
    refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
    · change outer Φ * outer Φ = outer Φ
      rw [Matrix.vecMulVec_mul_vecMulVec, show star Φ ⬝ᵥ Φ = 1 from bell_norm, one_smul]
    · change (outer Φ)ᴴ = outer Φ
      simp only [Matrix.conjTranspose_vecMulVec, star_star]
  have hD : IsStarProjection D := hP.one_sub
  have hDadj : Dᴴ = D := hD.isSelfAdjoint.star_eq
  have hDidem : D * D = D := hD.isIdempotentElem
  have hB : B₀.PosSemidef :=
    Matrix.posSemidef_sum Finset.univ
      (fun i _ => hD.nonneg.posSemidef.mul_mul_conjTranspose_same (T i))
  let S := spectralSupport B₀
  obtain ⟨hRadj, -, hSadj, hSidem, -, -, hSB, -⟩ := spectral_sqrt_normalization B₀ hB
  obtain ⟨-, hWR, -, -⟩ := spectral_sqrt_inverse_products B₀ hB
  have hS : IsStarProjection S := isStarProjection_iff'.mpr ⟨hSidem, hSadj⟩
  have hQ : Q = 1 - S := hkernel
  have hQproj : IsStarProjection Q := by
    rw [hQ]
    exact hS.one_sub
  have hBS : B₀ * S = B₀ := by
    simpa only [Matrix.conjTranspose_mul, hSadj, hB.isHermitian.eq]
      using congrArg Matrix.conjTranspose hSB
  have hBQ : B₀ * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, hBS, sub_self]
  have hfix (x : A × B → ℂ) : B₀ *ᵥ x = 0 ↔ Q *ᵥ x = x := by
    constructor
    · intro hx
      have hRx : CFC.sqrt B₀ *ᵥ x = 0 := by
        apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt B₀) x).mp
        rw [hRadj, CFC.sqrt_mul_sqrt_self B₀ hB.nonneg]
        exact hx
      have hSx : S *ᵥ x = 0 := by
        change spectralSupport B₀ *ᵥ x = 0
        rw [← hWR, ← Matrix.mulVec_mulVec, hRx, Matrix.mulVec_zero]
      rw [hQ, Matrix.sub_mulVec, Matrix.one_mulVec, hSx, sub_zero]
    · intro hx
      calc
        B₀ *ᵥ x = B₀ *ᵥ (Q *ᵥ x) := by rw [hx]
        _ = 0 := by rw [Matrix.mulVec_mulVec, hBQ, Matrix.zero_mulVec]
  -- Compress the positive sum by the matrix of kernel vectors.
  let V : Matrix (A × B) J ℂ := Matrix.of (fun x j => v j x)
  have hV : V * Vᴴ = Q := by
    apply Matrix.ext
    intro x y
    simp only [V, Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have hBV : B₀ * V = 0 := by
    apply Matrix.self_mul_conjTranspose_eq_zero.mp
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc B₀ V, ← Matrix.mul_assoc V Vᴴ,
      hV, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]
  let L : I → Matrix (A × A) J ℂ := fun i => D * (T i)ᴴ * V
  have hLgram (i : I) : (L i)ᴴ * L i = Vᴴ * (T i * D * (T i)ᴴ) * V := by
    calc
      _ = Vᴴ * (T i * (D * D) * (T i)ᴴ) * V := by
        simp only [L, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hDadj, Matrix.mul_assoc]
      _ = _ := by rw [hDidem]
  have hLsum : (∑ i, (L i)ᴴ * L i) = 0 := by
    calc
      _ = ∑ i, Vᴴ * (T i * D * (T i)ᴴ) * V := Finset.sum_congr rfl (fun i _ => hLgram i)
      _ = Vᴴ * B₀ * V := by simp only [B₀, amplifyKraus, T, Matrix.mul_sum, Matrix.sum_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hBV, Matrix.mul_zero]
  have hL (i : I) : L i = 0 := by
    have hnonneg : (0 : I → Matrix J J ℂ) ≤ (fun i => (L i)ᴴ * L i) :=
      fun i => (Matrix.posSemidef_conjTranspose_mul_self (L i)).nonneg
    exact Matrix.conjTranspose_mul_self_eq_zero.mp
      (congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hLsum) i)
  let c : I → J → ℂ := fun i j => star Φ ⬝ᵥ ((T i)ᴴ *ᵥ v j)
  have hpull (i : I) (j : J) : (T i)ᴴ *ᵥ v j = c i j • Φ := by
    have hzero := congrArg (fun M : Matrix (A × A) J ℂ => M.col j) (hL i)
    change (D * (T i)ᴴ * V).col j = 0 at hzero
    rw [Matrix.col_mul_eq_mulVec_col, ← Matrix.mulVec_mulVec] at hzero
    change D *ᵥ ((T i)ᴴ *ᵥ v j) = 0 at hzero
    rw [show D = 1 - P from rfl, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hzero
    calc
      (T i)ᴴ *ᵥ v j = P *ᵥ ((T i)ᴴ *ᵥ v j) := hzero
      _ = c i j • Φ := by
        change outer Φ *ᵥ ((T i)ᴴ *ᵥ v j) = c i j • Φ
        rw [Matrix.vecMulVec_mulVec]
        funext x
        exact mul_comm (Φ x) (c i j)
  -- Bell reshaping turns each composed Kraus operator into a scalar.
  let α : J → I → ℂ := fun j i => δ * star (c i j)
  have hscalar (j : J) (i : I) : R j * K i = α j i • (1 : Matrix A A ℂ) := by
    apply Matrix.ext
    intro a a'
    have hbell : Φ (a, a') = s * (1 : Matrix A A ℂ) a a' := by
      simp [Φ, bell, diagonalVector, s, Matrix.one_apply]
    have hone : star ((1 : Matrix A A ℂ) a a') = (1 : Matrix A A ℂ) a a' := by
      by_cases h : a = a' <;> simp [Matrix.one_apply, h]
    calc
      (R j * K i) a a' = s * star (((T i)ᴴ *ᵥ v j) (a, a')) := by
        rw [show (T i)ᴴ = (1 : Matrix A A ℂ) ⊗ₖ (K i)ᴴ by
          simp only [T, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one],
          one_kronecker_mulVec_entry, star_sum, Finset.mul_sum]
        simp only [Matrix.mul_apply, R, bellRecoveryKraus, Matrix.smul_apply, smul_eq_mul,
          Matrix.of_apply, Matrix.conjTranspose_apply, star_mul, star_star]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        change (s * star (v j (a, b))) * K i b a' = s * (star (v j (a, b)) * K i b a')
        exact mul_assoc _ _ _
      _ = _ := by
        rw [hpull]
        simp only [Pi.smul_apply, hbell, star_mul, hsstar, hone, Matrix.smul_apply, smul_eq_mul, α]
        rw [← hss]
        ring
  -- The partial trace of the kernel projection bounds the recovery effect.
  have heffect : (∑ j, (R j)ᴴ * R j) = δ • partialTraceLeft Q := by
    apply Matrix.ext
    intro b b'
    simp only [partialTraceLeft, Q, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, R, bellRecoveryKraus, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    change (∑ j, ∑ a, star (s * star (v j (a, b))) * (s * star (v j (a, b')))) = _
    rw [Finset.sum_comm]
    simp only [star_mul, star_star, hsstar, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => by rw [← hss]; ring))
  have hbound : (∑ j, (R j)ᴴ * R j) ≤ (1 : Matrix B B ℂ) := by
    have hptr := partialTraceLeft_posSemidef (Matrix.le_iff.mp hQproj.le_one)
    have hptr_sub : partialTraceLeft (1 - Q) =
        d • (1 : Matrix B B ℂ) - partialTraceLeft Q := by
      have hone : partialTraceLeft (1 : Matrix (A × B) (A × B) ℂ) =
          d • (1 : Matrix B B ℂ) := by
        have h := partialTraceLeft_kronecker (1 : Matrix A A ℂ) (1 : Matrix B B ℂ)
        rw [Matrix.trace_one] at h
        exact (congrArg partialTraceLeft Matrix.one_kronecker_one.symm).trans h
      rw [← hone]
      apply Matrix.ext
      intro b b'
      simp only [partialTraceLeft, Matrix.sub_apply, Finset.sum_sub_distrib]
    rw [hptr_sub] at hptr
    have hspos : 0 ≤ (Fintype.card A : ℝ)⁻¹ := by positivity
    have hscaled := hptr.smul hspos
    change ((↑((Fintype.card A : ℝ)⁻¹) : ℂ) •
      (d • (1 : Matrix B B ℂ) - partialTraceLeft Q)).PosSemidef at hscaled
    rw [← hδreal] at hscaled
    rw [heffect, Matrix.le_iff]
    simpa only [smul_sub, smul_smul, smul_eq_mul, δ, inv_mul_cancel₀ hd, one_smul] using hscaled
  -- The Bell-output overlap determines the common scalar weight.
  let y : I → A × B → ℂ := fun i => T i *ᵥ Φ
  have hX : X₀ = ∑ i, outer (y i) := by
    change (∑ i, T i * P * (T i)ᴴ) = _
    exact Finset.sum_congr rfl (fun i _ => congruence_outer (T i) Φ)
  have hc (i : I) (j : J) : star (y i) ⬝ᵥ v j = c i j := by
    change star (T i *ᵥ Φ) ⬝ᵥ v j = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have htrace : (Q * X₀).trace = ∑ j, ∑ i, star (c i j) * c i j := by
    change ((∑ j, outer (v j)) * X₀).trace = _
    rw [hX, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Matrix.mul_sum, Matrix.trace_sum, trace_outer_mul_outer, hc]
  have hweight : (∑ j, ∑ i, star (α j i) * α j i) = (Q * X₀).trace / d ^ 2 := by
    calc
      _ = (δ * δ) * ∑ j, ∑ i, star (c i j) * c i j := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by
          simp only [α, star_mul, star_star, hδstar]
          ring))
      _ = _ := by
        rw [← htrace, ← pow_two]
        change (d⁻¹) ^ 2 * (Q * X₀).trace = _
        rw [inv_pow, div_eq_mul_inv, mul_comm]
  refine ⟨hB, hQproj, hfix, heffect, hbound, MatrixMap.of_kraus_isCompletelyPositive R,
    ?_, ?_⟩
  · change 0 ≤ (Q * X₀).trace / d ^ 2
    rw [← hweight]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => star_mul_self_nonneg _))
  · intro X
    change MatrixMap.of_kraus R R (MatrixMap.of_kraus K K X) = ((Q * X₀).trace / d ^ 2) • X
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_sum, Matrix.sum_mul]
    rw [← hweight, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    calc
      R j * (K i * X * (K i)ᴴ) * (R j)ᴴ = (R j * K i) * X * (R j * K i)ᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (star (α j i) * α j i) • X := by
        rw [hscalar]
        simp [Matrix.conjTranspose_smul, smul_smul, mul_comm]

#print axioms amplifyKraus
#print axioms bellRecoveryKraus
#print axioms direct_bell_kernel_recovery

end D5.S3.Quantum.Divergence.ConditionalExpansion
