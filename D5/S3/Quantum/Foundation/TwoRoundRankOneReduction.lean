/- GID: D5/S3/Quantum/Foundation/TwoRoundRankOneReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundRankOneReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-marginal rank-one repairs and the complete scalar tester objective. -/

import D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

noncomputable section

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Foundation.TwoRoundRankOneReduction

open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Foundation.TwoRoundSpectralEvents

private def realOuter (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (fun i => (u i : ℂ)) (star (fun i => (u i : ℂ)))

private def gramU (u : Fin 3 → ℝ) : ℝ := ∑ i, u i ^ 2
private def gramW (u v : Fin 3 → ℝ) : ℝ := ∑ i, u i * v i

private def positiveRoot (u v : Fin 3 → ℝ) : ℝ :=
  (gramU u - gramU v + Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)) / 2

private def negativeRoot (u v : Fin 3 → ℝ) : ℝ :=
  (gramU u - gramU v - Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)) / 2

private theorem gram_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ gramU u ∧ 0 ≤ gramU v ∧ gramW u v ^ 2 ≤ gramU u * gramU v := by
  refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _),
    Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  dsimp [gramU, gramW]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem root_relations (u v : Fin 3 → ℝ) :
    0 ≤ positiveRoot u v ∧ negativeRoot u v ≤ 0 ∧
      positiveRoot u v + negativeRoot u v = gramU u - gramU v ∧
      positiveRoot u v * negativeRoot u v = gramW u v ^ 2 - gramU u * gramU v := by
  obtain ⟨hU, hV, hW⟩ := gram_nonneg u v
  have hd : 0 ≤ (gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2 := by
    nlinarith [sq_nonneg (gramU u - gramU v)]
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2)
  have hb : |gramU u - gramU v| ≤
      Real.sqrt ((gramU u + gramU v) ^ 2 - 4 * gramW u v ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (gramU u - gramU v)]
  dsimp [positiveRoot, negativeRoot]
  refine ⟨by linarith [abs_le.mp hb], by linarith [abs_le.mp hb], by ring, ?_⟩
  nlinarith [hs]

private theorem difference_charpoly (u v : Fin 3 → ℝ) :
    (realOuter u - realOuter v).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (positiveRoot u v : ℂ)) *
        (Polynomial.X - Polynomial.C (negativeRoot u v : ℂ)) := by
  obtain ⟨_, _, hs, hp⟩ := root_relations u v
  have hs' := congrArg (fun r : ℝ => (r : ℂ)) hs
  have hp' := congrArg (fun r : ℝ => (r : ℂ)) hp
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow] at hs' hp'
  have hsum : Polynomial.C (positiveRoot u v : ℂ) + Polynomial.C (negativeRoot u v : ℂ) =
      Polynomial.C ((gramU u : ℂ) - (gramU v : ℂ)) := by rw [← map_add, hs']
  have hprod : Polynomial.C (positiveRoot u v : ℂ) * Polynomial.C (negativeRoot u v : ℂ) =
      Polynomial.C ((gramW u v : ℂ) ^ 2 - (gramU u : ℂ) * (gramU v : ℂ)) := by
    rw [← map_mul, hp']
  calc
    _ = Polynomial.X ^ 3 -
        Polynomial.C ((gramU u : ℂ) - (gramU v : ℂ)) * Polynomial.X ^ 2 +
        Polynomial.C ((gramW u v : ℂ) ^ 2 - (gramU u : ℂ) * (gramU v : ℂ)) * Polynomial.X := by
      simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three,
        realOuter, Matrix.vecMulVec_apply, Matrix.scalar, Matrix.diagonal,
        gramU, gramW, Fin.sum_univ_three, Polynomial.C_add, Polynomial.C_sub,
        Polynomial.C_mul, Polynomial.C_pow]
      ring
    _ = _ := by rw [← hsum, ← hprod]; ring

private theorem positive_mass_diagonal (d : Fin 3 → ℝ)
    (hD : (diagonal (fun i => (d i : ℂ))).IsHermitian) :
    positiveSpectralMass hD = ∑ i, max (d i) 0 := by
  have hr := hD.roots_charpoly_eq_eigenvalues
  rw [charpoly_diagonal, Polynomial.roots_prod] at hr
  · have hm := congrArg (fun s : Multiset ℂ => (s.map (fun z => max z.re 0)).sum) hr
    simpa [positiveSpectralMass, Fin.sum_univ_three, add_assoc] using hm.symm
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)

private theorem rank_one_positive_mass (u v : Fin 3 → ℝ) :
    positiveSpectralMass
      ((posSemidef_vecMulVec_self_star (fun i => (u i : ℂ))).isHermitian.sub
        (posSemidef_vecMulVec_self_star (fun i => (v i : ℂ))).isHermitian) =
      positiveRoot u v := by
  let hB : (realOuter u - realOuter v).IsHermitian :=
    (posSemidef_vecMulVec_self_star _).isHermitian.sub
      (posSemidef_vecMulVec_self_star _).isHermitian
  let d : Fin 3 → ℝ := ![positiveRoot u v, negativeRoot u v, 0]
  let hD : (diagonal (fun i => (d i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.mpr (fun i => by
      change IsSelfAdjoint (d i : ℂ); simp [IsSelfAdjoint])
  have hc : (realOuter u - realOuter v).charpoly = (diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [difference_charpoly, charpoly_diagonal]
    simp [d, Fin.prod_univ_three]
    ring
  have he := (hB.eigenvalues_eq_eigenvalues_iff hD).mpr hc
  change positiveSpectralMass hB = _
  change (∑ i, max (hB.eigenvalues i) 0) = _
  rw [he]
  change positiveSpectralMass hD = _
  rw [positive_mass_diagonal]
  obtain ⟨hp, hn, _, _⟩ := root_relations u v
  simp [d, Fin.sum_univ_three, max_eq_left hp, max_eq_right hn]

private def quadratic {n : Type*} [Fintype n] (A : Matrix n n ℂ) (z : n → ℂ) : ℝ :=
  (star z ⬝ᵥ (A *ᵥ z)).re

private theorem quadratic_real {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (z : n → ℝ) :
    quadratic A (fun i => (z i : ℂ)) = ∑ i, ∑ j, (A i j).re * z i * z j := by
  simp only [quadratic, dotProduct, mulVec, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quadratic_le_mass {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : n → ℂ) :
    quadratic A z ≤ positiveSpectralMass hA * (star z ⬝ᵥ z).re := by
  classical
  let L := positiveSpectralMass hA
  let U := hA.eigenvectorUnitary
  let a := conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hL (i : n) : hA.eigenvalues i ≤ L := by
    calc
      _ ≤ max (hA.eigenvalues i) 0 := le_max_left _ _
      _ ≤ ∑ j, max (hA.eigenvalues j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
  have hd : diagonal (fun i => ((L - hA.eigenvalues i : ℝ) : ℂ)) =
      (L : ℂ) • (1 : Matrix n n ℂ) - diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have ha : a (diagonal (fun i => ((L - hA.eigenvalues i : ℝ) : ℂ))) =
      (L : ℂ) • (1 : Matrix n n ℂ) - A := by
    rw [hd, map_sub, map_smul, map_one]
    congr 1
    exact hA.spectral_theorem.symm
  have hpos : ((L : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef := by
    rw [← ha, conjStarAlgAut_apply]
    apply PosSemidef.mul_mul_conjTranspose_same
    exact PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr
      ⟨by simpa using sub_nonneg.mpr (hL i), by simp⟩)
  have h := hpos.re_dotProduct_nonneg z
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h
  change 0 ≤ ((L : ℂ) * (star z ⬝ᵥ z) - star z ⬝ᵥ (A *ᵥ z)).re at h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  change quadratic A z ≤ L * _
  dsimp [quadratic]
  linarith

private theorem real_eigenvalue_le_mass {H : Matrix (Fin 3) (Fin 3) ℝ}
    (hH : H.IsHermitian) {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.IsHermitian)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j) (hentry : ∀ i j, H i j ≤ (A i j).re)
    {lam : ℝ} (hlam : lam ∈ spectrum ℝ H) : lam ≤ positiveSpectralMass hA := by
  obtain ⟨k, hk⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hlam
  let v : Fin 3 → ℝ := hH.eigenvectorBasis k
  let z : Fin 3 → ℝ := fun i => |v i|
  have hv : ∑ i, v i ^ 2 = 1 := by
    have hn := hH.eigenvectorBasis.orthonormal.1 k
    have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (hH.eigenvectorBasis k)
    rw [hn, one_pow] at hs
    simpa [v, Real.norm_eq_abs, sq_abs] using hs.symm
  have he : lam = ∑ i, ∑ j, H i j * v i * v j := by
    rw [← hk, hH.eigenvalues_eq]
    simp only [RCLike.re_to_real, star_trivial, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcomp : (∑ i, ∑ j, H i j * v i * v j) ≤
      ∑ i, ∑ j, (A i j).re * z i * z j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hnorm : H i j * v i * v j ≤ H i j * z i * z j := by
      by_cases hij : i = j
      · subst j
        dsimp [z]
        apply le_of_eq
        calc
          _ = H i i * (v i ^ 2) := by ring
          _ = H i i * (|v i| ^ 2) := by rw [sq_abs]
          _ = H i i * |v i| * |v i| := by ring
      · have hb : v i * v j ≤ z i * z j := by
          simpa only [z, abs_mul] using le_abs_self (v i * v j)
        nlinarith [mul_le_mul_of_nonneg_left hb (hoff i j hij)]
    exact hnorm.trans (by
      have hb := mul_le_mul_of_nonneg_right (hentry i j)
        (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))
      simpa only [mul_assoc, z] using hb)
  have hq := quadratic_le_mass hA (fun i => (z i : ℂ))
  have hz : (star (fun i => (z i : ℂ)) ⬝ᵥ (fun i => (z i : ℂ))).re = 1 := by
    simpa [dotProduct, z, ← Complex.ofReal_mul, ← sq, ← Complex.ofReal_pow,
      sq_abs] using hv
  rw [quadratic_real, hz, mul_one] at hq
  rw [he]
  exact hcomp.trans hq

/-- The saturated principal-block amplitudes at the original marginal parameter. -/
def repairVector (p : ℝ) (i : Fin 3) : ℝ :=
  if i = 2 then Real.sqrt p else Real.sqrt (1 - p)

def rankOneBlock (p : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (fun i => (repairVector p i : ℂ)) (star (fun i => (repairVector p i : ℂ)))

/-- The complementary mass is part of the causal repair. -/
def rankOneRepair (p : ℝ) : Matrix Wire Wire ℂ := causalCompletion p (rankOneBlock p)

def scalarU (eps q t : ℝ) : ℝ := q + (1 - eps) * (1 - q) + eps * t
def scalarV (p t : ℝ) : ℝ := 1 - p + p * t
def scalarW (eps p q t : ℝ) : ℝ :=
  Real.sqrt (1 - p) * (q + Real.sqrt (1 - eps) * (1 - q)) + Real.sqrt (eps * p) * t

/-- The exact positive spectral root, including collinear and zero vectors. -/
def scalarLambda (eps p q t : ℝ) : ℝ :=
  (scalarU eps q t - scalarV p t +
    Real.sqrt ((scalarU eps q t + scalarV p t) ^ 2 - 4 * scalarW eps p q t ^ 2)) / 2

private def inputVector (eps : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then 1 else if i = 1 then Real.sqrt (1 - eps) else Real.sqrt eps

private def weightVector (q t : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then Real.sqrt q else if i = 1 then Real.sqrt (1 - q) else Real.sqrt t

private def weightedInput (eps q t : ℝ) (i : Fin 3) : ℝ :=
  weightVector q t i * inputVector eps i

private def weightedRepair (p q t : ℝ) (i : Fin 3) : ℝ :=
  weightVector q t i * repairVector p i

private theorem rankOneBlock_pos (p : ℝ) : (rankOneBlock p).PosSemidef :=
  posSemidef_vecMulVec_self_star _

private theorem rankOneBlock_budgets (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (rankOneBlock p 0 0).re = 1 - p ∧ (rankOneBlock p 1 1).re = 1 - p ∧
      (rankOneBlock p 2 2).re = p := by
  simp [rankOneBlock, repairVector, vecMulVec_apply, Real.mul_self_sqrt hp,
    Real.mul_self_sqrt (sub_nonneg.mpr hp1)]

private theorem normalization_sqrt (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) :
    CFC.sqrt (compressedNormalization q t) =
      diagonal (fun i => (weightVector q t i : ℂ)) := by
  let D : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => (weightVector q t i : ℂ))
  have hD : D.PosSemidef := PosSemidef.diagonal (fun i =>
    Complex.nonneg_iff.mpr ⟨by dsimp [weightVector]; split_ifs <;> positivity, by simp⟩)
  have hs : D * D = compressedNormalization q t := by
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compressedNormalization, weightVector, diagonal,
        ← Complex.ofReal_mul, Real.mul_self_sqrt hq,
        Real.mul_self_sqrt (sub_nonneg.mpr hq1), Real.mul_self_sqrt ht]
  exact CFC.sqrt_unique hs hD.nonneg

private theorem input_compression (eps : ℝ) :
    (candidate eps).submatrix mainAddress mainAddress = realOuter (inputVector eps) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [candidate, candidateVector, mainAddress, realOuter, inputVector, vecMulVec_apply]

private theorem weighted_difference (eps q t : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    weightedOperator (compressedNormalization q t) (compressedDifference eps P) =
      diagonal (fun i => (weightVector q t i : ℂ)) *
        (realOuter (inputVector eps) - P) * diagonal (fun i => (weightVector q t i : ℂ)) := by
  rw [weightedOperator, normalization_sqrt q t hq hq1 ht]
  have hD : (diagonal (fun i => (weightVector q t i : ℂ)))ᴴ =
      diagonal (fun i => (weightVector q t i : ℂ)) := by simp [diagonal_conjTranspose]
  rw [hD, compressedDifference, input_compression]

private theorem weighted_rank_one_difference (eps p q t : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    weightedOperator (compressedNormalization q t) (compressedDifference eps (rankOneBlock p)) =
      realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t) := by
  rw [weighted_difference eps q t _ hq hq1 ht]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, realOuter, rankOneBlock,
    weightedInput, weightedRepair, vecMulVec_apply, Complex.ofReal_mul]
  ring

private theorem weighted_grams (eps p q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    gramU (weightedInput eps q t) = scalarU eps q t ∧
      gramU (weightedRepair p q t) = scalarV p t ∧
      gramW (weightedInput eps q t) (weightedRepair p q t) = scalarW eps p q t := by
  constructor
  · simp [gramU, weightedInput, weightVector, inputVector, Fin.sum_univ_three, mul_pow,
      Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht,
      Real.sq_sqrt he, Real.sq_sqrt (sub_nonneg.mpr he1), scalarU]
    ring
  constructor
  · simp [gramU, weightedRepair, weightVector, repairVector, Fin.sum_univ_three, mul_pow,
      Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht,
      Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr hp1), scalarV]
    ring
  · simp [gramW, weightedInput, weightedRepair, weightVector, inputVector, repairVector,
      scalarW, Fin.sum_univ_three, Real.sqrt_mul he]
    ring_nf
    simp [Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht]
    ring

private theorem mass_congr {A B : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    positiveSpectralMass hA = positiveSpectralMass hB := by
  subst B
  rfl

private theorem compressed_rank_one_mass (eps p q t : ℝ)
    (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    compressedPositiveMass eps q t (rankOneBlock_pos p) = scalarLambda eps p q t := by
  have hB := weighted_rank_one_difference eps p q t hq hq1 ht
  unfold compressedPositiveMass weightedPositiveMass
  have hmass := rank_one_positive_mass (weightedInput eps q t) (weightedRepair p q t)
  let hRight : (realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t)).IsHermitian :=
    (posSemidef_vecMulVec_self_star _).isHermitian.sub
      (posSemidef_vecMulVec_self_star _).isHermitian
  obtain ⟨hU, hV, hW⟩ := weighted_grams eps p q t he he1 hp hp1 hq hq1 ht
  calc
    _ = positiveSpectralMass hRight := mass_congr _ hRight hB
    _ = positiveRoot (weightedInput eps q t) (weightedRepair p q t) := hmass
    _ = scalarLambda eps p q t := by simp only [positiveRoot, scalarLambda, hU, hV, hW]

private theorem budget_entry_bound {P : Matrix (Fin 3) (Fin 3) ℂ} (hP : P.PosSemidef)
    (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) (hd : ∀ i, (P i i).re ≤ v i ^ 2)
    (i j : Fin 3) : (P i j).re ≤ v i * v j := by
  have h := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.psd_entry_bound hP i j
  have hb := mul_le_mul (hd i) (hd j)
    (Complex.nonneg_iff.mp (hP.diag_nonneg (i := j))).1 (sq_nonneg (v i))
  have hsq : (P i j).re ^ 2 ≤ (v i * v j) ^ 2 := by
    simp only [Complex.normSq_apply] at h
    nlinarith [sq_nonneg (P i j).im]
  nlinarith [mul_nonneg (hv i) (hv j)]

private theorem repair_offdiagonal (eps p : ℝ) (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2)
    (hp : 0 ≤ p) (hplo : 1 - Real.sqrt (1 - eps) ≤ p) (hphi : p ≤ eps) :
    ∀ i j : Fin 3, i ≠ j →
      0 ≤ inputVector eps i * inputVector eps j - repairVector p i * repairVector p j := by
  have he1 : eps ≤ 1 := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hc := Real.sqrt_nonneg (1 - eps)
  have hs := Real.sqrt_nonneg eps
  have ha := Real.sqrt_nonneg (1 - p)
  have hb := Real.sqrt_nonneg p
  have hcs := Real.sq_sqrt (sub_nonneg.mpr he1)
  have hss := Real.sq_sqrt he
  have has := Real.sq_sqrt (sub_nonneg.mpr hp1)
  have hbs := Real.sq_sqrt hp
  have hab : (Real.sqrt p * Real.sqrt (1 - p)) ^ 2 = p * (1 - p) := by
    rw [mul_pow, hbs, has]
  have hcsprod : (Real.sqrt (1 - eps) * Real.sqrt eps) ^ 2 = (1 - eps) * eps := by
    rw [mul_pow, hcs, hss]
  have hmon : p * (1 - p) ≤ eps * (1 - eps) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hphi) (show 0 ≤ 1 - eps - p by linarith)]
  have hxy : 0 ≤ Real.sqrt (1 - eps) - Real.sqrt (1 - p) * Real.sqrt (1 - p) := by
    nlinarith
  have hxz : 0 ≤ Real.sqrt eps - Real.sqrt p * Real.sqrt (1 - p) := by
    nlinarith [mul_nonneg hb ha]
  have hyz : 0 ≤ Real.sqrt (1 - eps) * Real.sqrt eps -
      Real.sqrt p * Real.sqrt (1 - p) := by
    nlinarith [mul_nonneg hc hs, mul_nonneg hb ha]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim |
      (simp [inputVector, repairVector, Fin.ext_iff]; nlinarith)

private def realWeightedDifference (eps p q t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  vecMulVec (weightedInput eps q t) (weightedInput eps q t) -
    vecMulVec (weightedRepair p q t) (weightedRepair p q t)

private theorem realWeightedDifference_map (eps p q t : ℝ) :
    (realWeightedDifference eps p q t).map Complex.ofRealHom =
      realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t) := by
  ext i j
  simp [realWeightedDifference, realOuter, vecMulVec_apply]

private theorem positiveRoot_mem_spectrum (eps p q t : ℝ) :
    positiveRoot (weightedInput eps q t) (weightedRepair p q t) ∈
      spectrum ℝ (realWeightedDifference eps p q t) := by
  let lam := positiveRoot (weightedInput eps q t) (weightedRepair p q t)
  have hz : (realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t)).charpoly.eval
      (lam : ℂ) = 0 := by
    rw [difference_charpoly]
    simp [lam]
  rw [← realWeightedDifference_map, Matrix.charpoly_map] at hz
  change ((realWeightedDifference eps p q t).charpoly.map Complex.ofRealHom).eval
    (Complex.ofRealHom lam) = 0 at hz
  rw [Polynomial.eval_map_apply] at hz
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  apply Complex.ofReal_injective
  exact hz

/-- The same marginal repair has the complete scalar event value in both directions. -/
theorem rank_one_scalar_events (eps p q t : ℝ)
    (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Causal (rankOneRepair p) (diagonalMarginal p) ∧
    ∃ Ep En : Matrix Wire Wire ℂ,
      Tester (diagonalTester q t) Ep ∧ Tester (diagonalTester q t) En ∧
      response (candidate eps - rankOneRepair p) Ep = scalarLambda eps p q t ∧
      response (rankOneRepair p - candidate eps) En = scalarLambda eps p q t + eps * (1 - q - t) ∧
      (∀ E, Tester (diagonalTester q t) E →
        response (candidate eps - rankOneRepair p) E ≤ scalarLambda eps p q t ∧
        response (rankOneRepair p - candidate eps) E ≤ scalarLambda eps p q t + eps * (1 - q - t)) ∧
      IsGreatest {r : ℝ | ∃ E, Tester (diagonalTester q t) E ∧
        |response (candidate eps - rankOneRepair p) E| = r}
        (scalarLambda eps p q t + max (eps * (1 - q - t)) 0) := by
  obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets p hp hp1
  have h := compressed_completion_tester_value eps p q t (rankOneBlock p) he he1 hp hp1
    hq hq1 ht ht1 (rankOneBlock_pos p) h0.le h1.le h2.le
  rw [compressed_rank_one_mass eps p q t he he1 hp hp1 hq hq1 ht] at h
  exact h

/-- All original full testers are controlled exactly by the two scalar normalization parameters. -/
theorem rank_one_full_objective (eps p b : ℝ)
    (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ErrorBound (candidate eps - rankOneRepair p) b ↔
      ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
        scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ b := by
  constructor
  · intro hError q t hq hq1 ht ht1
    obtain ⟨_, _, _, _, _, _, _, hgreat⟩ :=
      (rank_one_scalar_events eps p q t he he1 hp hp1 hq hq1 ht ht1).2
    obtain ⟨E, hE, hv⟩ := hgreat.1
    exact hv.symm.trans_le (hError _ _ hE)
  · intro hScalar
    obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets p hp hp1
    apply (full_tester_compressed_objective eps p (rankOneBlock p) he he1 hp hp1
      (rankOneBlock_pos p) h0.le h1.le h2.le b).mpr
    intro q t hq hq1 ht ht1
    rw [compressed_rank_one_mass eps p q t he he1 hp hp1 hq hq1 ht]
    exact hScalar q t hq hq1 ht ht1

private theorem compressed_rank_one_domination (eps p q t : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℂ) (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2)
    (hp : 0 ≤ p) (hplo : 1 - Real.sqrt (1 - eps) ≤ p) (hphi : p ≤ eps)
    (hP : P.PosSemidef) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p)
    (h2 : (P 2 2).re ≤ p) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    scalarLambda eps p q t ≤ compressedPositiveMass eps q t hP := by
  have he1 : eps ≤ 1 := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hv (i : Fin 3) : 0 ≤ repairVector p i := by
    dsimp [repairVector]
    split_ifs <;> positivity
  have hd (i : Fin 3) : (P i i).re ≤ repairVector p i ^ 2 := by
    fin_cases i
    · simpa [repairVector, Real.sq_sqrt (sub_nonneg.mpr hp1)] using h0
    · simpa [repairVector, Real.sq_sqrt (sub_nonneg.mpr hp1)] using h1
    · simpa [repairVector, Real.sq_sqrt hp] using h2
  have hw (i : Fin 3) : 0 ≤ weightVector q t i := by
    dsimp [weightVector]
    split_ifs <;> positivity
  let H := realWeightedDifference eps p q t
  let A := weightedOperator (compressedNormalization q t) (compressedDifference eps P)
  have hH : H.IsHermitian := by
    apply isHermitian_iff_isSymm.mpr
    ext i j
    dsimp [H, realWeightedDifference, Matrix.transpose, vecMulVec]
    ring
  have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _
    (((posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.submatrix
      mainAddress).sub hP.isHermitian)
  have hHentry (i j : Fin 3) : H i j = weightVector q t i *
      (inputVector eps i * inputVector eps j - repairVector p i * repairVector p j) *
        weightVector q t j := by
    dsimp [H, realWeightedDifference, vecMulVec, weightedInput, weightedRepair]
    ring
  have hAentry (i j : Fin 3) : (A i j).re = weightVector q t i *
      (inputVector eps i * inputVector eps j - (P i j).re) * weightVector q t j := by
    dsimp [A]
    rw [weighted_difference eps q t P hq hq1 ht]
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, realOuter, vecMulVec_apply,
      Complex.mul_re]
  have hoff (i j : Fin 3) (hij : i ≠ j) : 0 ≤ H i j := by
    rw [hHentry]
    exact mul_nonneg (mul_nonneg (hw i)
      (repair_offdiagonal eps p he hehalf hp hplo hphi i j hij)) (hw j)
  have hentry (i j : Fin 3) : H i j ≤ (A i j).re := by
    rw [hHentry, hAentry]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_left (budget_entry_bound hP _ hv hd i j) _)
        (hw i)) (hw j)
  have hbound := real_eigenvalue_le_mass hH hA hoff hentry (positiveRoot_mem_spectrum eps p q t)
  obtain ⟨hU, hV, hW⟩ := weighted_grams eps p q t he he1 hp hp1 hq hq1 ht
  have hroot : positiveRoot (weightedInput eps q t) (weightedRepair p q t) =
      scalarLambda eps p q t := by simp only [positiveRoot, scalarLambda, hU, hV, hW]
  rw [hroot] at hbound
  exact hbound

/-- Every original complex causal repair with marginal in the comparison interval is dominated
by the explicit repair at exactly that marginal, for the complete original tester set. -/
theorem same_p_error_domination (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2)
    (hS : Causal S sigma) (hplo : 1 - Real.sqrt (1 - eps) ≤ (sigma 1 1).re)
    (hphi : (sigma 1 1).re ≤ eps) :
    let p := (sigma 1 1).re
    Causal (rankOneRepair p) (diagonalMarginal p) ∧
      diagonalMarginal p 1 1 = sigma 1 1 ∧
      ∀ b : ℝ, ErrorBound (candidate eps - S) b →
        ErrorBound (candidate eps - rankOneRepair p) b ∧
        ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
          scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ b := by
  intro p
  have he1 : eps ≤ 1 := by linarith
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  obtain ⟨hb0, hb1, hb2⟩ := rankOneBlock_budgets p hp hp1
  have hLift := compressed_block_causal_lift p (rankOneBlock p) hp hp1 (rankOneBlock_pos p)
    hb0.le hb1.le hb2.le
  refine ⟨hLift.1, ?_, ?_⟩
  · rw [hLift.2.2]
    exact (Complex.eq_re_of_ofReal_le (r := 0) hS.2.1.diag_nonneg).symm
  · intro b hError
    have hComp := (causal_compressed_repair_domination eps S sigma he he1 hS).2.2.2 b hError
    have hScalar := (full_tester_compressed_objective eps p
      (S.submatrix mainAddress mainAddress) he he1 hp hp1 hP h0 h1 h2 b).mp hComp
    have hRepair : ErrorBound (candidate eps - rankOneRepair p) b := by
      apply (rank_one_full_objective eps p b he he1 hp hp1).mpr
      intro q t hq hq1 ht ht1
      have hdom := compressed_rank_one_domination eps p q t
        (S.submatrix mainAddress mainAddress) he hehalf hp hplo hphi hP h0 h1 h2 hq hq1 ht
      linarith [hScalar q t hq hq1 ht ht1]
    exact ⟨hRepair, (rank_one_full_objective eps p b he he1 hp hp1).mp hRepair⟩

end D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
