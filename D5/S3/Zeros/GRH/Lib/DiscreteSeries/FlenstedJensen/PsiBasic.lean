/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/PsiBasic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/PsiBasic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.FlenstedJensen.PsiBasic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/FlenstedJensen/PsiBasic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic.HolomorphicExtension
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Basic properties of the coefficient: polar formula, inversion, conjugation, values on
K. -/


open Matrix MeasureTheory ComplexConjugate ComplexOrder U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (g : USign ε)
attribute [local simp] flenstedJensen dsCoeff ne_of_gt
attribute [local simp↓ ←] maxCompactU.coe_inv principalMinor_coe_inv integral_conj

lemma weightMinors_unitary_inv w : weightMinors w g.1.1⁻¹ = conj (weightMinors w
  g) := by simp [↓conj_weightMinors, weightMinors, ← principalMinor_of_forall (p := ⊤)]

instance {J : Matrix n n ℂ} : SigmaCompactSpace (U J) := inferInstance

/-- The function ψ_λ takes the value 1 at the identity matrix. -/
@[simp] lemma dsCoeff_one : l.dsCoeff 1 = 1 := by simp [RCLike.mul_conj, field]; norm_cast

include hg

/-- For a parameter l = 2λ, p, q in K and z in U(diag ε) positive definite, ψ_λ(pzq⁻¹) = c_Λ⁻¹ ∫_K
m_Λ(pu) conj(m_Λ(qu)) / m_{−μ}(u*zu) du, c_Λ = ∫_K |m_Λ|², Haar probability on K. -/
lemma dsCoeff_polar (p q : maxCompactU ε) {z : USign ε} (hz : z.1.1.PosDef) :
  l.dsCoeff (p * z * q⁻¹ :) = (∫ u, weightMinors l.lowestKType (p * u.1) * conj (weightMinors
  l.lowestKType (q * u)) / weightMinors (-paramAddRho l) (u.1.1.1ᴴ * z * u) ∂haarK ε) /
  l.lowestKType.kTypeNormSq := by
    rw [dsCoeff_eq_flenstedJensen hg (mem_maxCompactU.1 (p * q⁻¹).2),
      flenstedJensen, ← integral_mul_left_eq_self _ q]
    · simp [mul_assoc]
    simpa [mul_assoc] using hz.isAccretive.conjTranspose_mul_mul (k := ↑q⁻¹)

/-- For a parameter λ of gap h and g in U(diag ε), ψ_λ(g⁻¹) is the complex conjugate of ψ_λ(g). -/
lemma dsCoeff_inv : l.dsCoeff ↑g⁻¹ = conj (l.dsCoeff g) := by
  obtain ⟨k, z, ⟨hz⟩⟩ := exists_polar g
  obtain ⟨⟩ := dsCoeff_polar hg 1 k (z := z⁻¹) (by simpa), dsCoeff_polar hg k 1 hz,
    (weightMinors_unitary_inv <| ·⁻¹ * z * ·)
  simp_all [mul_assoc, mul_comm]

/-- For a parameter λ of gap h and g in U(diag ε), ψ_{−λ}(g) is the complex conjugate of ψ_λ(g). -/
@[simp] lemma dsCoeff_neg : (-l).dsCoeff g = conj (l.dsCoeff g) := by
  obtain ⟨k, z, ⟨b⟩⟩ := exists_polar g
  obtain ⟨⟩ := dsCoeff_polar hg k 1 b, dsCoeff_polar hg.neg k 1 b
  simp_all [kTypeNormSq, (by grind [two_mul_paramAddRho, hg.neg, twoRho_neg, Pi.neg_def] :
    paramAddRho (-l) = -paramAddRho l)]
  norm_cast; simp [↓weightMinors_neg, ↓weightMinors_unitary_inv]

/-- For a parameter λ of gap h and k in K = U(diag ε) ∩ U(n), ψ_λ(k) = m_Λ(k), the product of
principal minors of weight Λ = λ + ρ − 2ρ_c. -/
lemma dsCoeff_of_mem_maxCompactU {k} (hk : k ∈ maxCompactU ε) : l.dsCoeff k =
  weightMinors l.lowestKType k := by simp_all [mem_maxCompactU,
  by simpa using (isHolOfWeight_weightMinors hg.neg.1 k fun () ↦
  hg.isKDominant_lowestKType).integral_mul_conj_weightMinors hg.neg.1 hg.isKDominant_lowestKType]
