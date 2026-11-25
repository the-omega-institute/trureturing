/- GID: D5/S3/Quantum/Semigroups/WuPhysicalProductCut
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuPhysicalProductCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-mode Clifford cuts have exact rank and imbalance. -/

import D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford

/-! Physical two-mode Clifford projections and their occupation imbalance. -/

noncomputable section

open Matrix Kronecker
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open scoped Matrix ComplexOrder

namespace WuRankOneEndpointFloor

/-- The four degree-one quadratures of the signed two-mode CAR representation. -/
def carDirection (a b c d : ℝ) : TwoMode :=
  (a : ℂ) • pauliWord .I .X + (b : ℂ) • pauliWord .I .Y +
    (c : ℂ) • pauliWord .X .Z + (d : ℂ) • pauliWord .Y .Z

/-- Occupation imbalance in the physical order 00, 01, 10, 11. -/
def carImbalance : TwoMode :=
  (1 / 2 : ℂ) • (pauliWord .Z .I + pauliWord .I .Z)

/-- Paired occupation observable associated with a normalized Clifford direction. -/
def carPartner (G : TwoMode) : TwoMode :=
  carImbalance - G * carImbalance * G

/-- Projection onto one physical occupation or coherent one-mode line. -/
def carProductCut (G : TwoMode) (u rho : ℝ) : TwoMode :=
  (1 / 2 : ℂ) • (1 + (u : ℂ) • G + (rho : ℂ) • carPartner G)

set_option maxHeartbeats 1000000 in
-- Expanding all sixteen Pauli-matrix entries exceeds the default limit.
private theorem carDirection_apply (a b c d : ℝ) (i j : Mode) :
    carDirection a b c d i j =
      if i.1 = j.1 then
        if i.2 = j.2 then 0
        else (a : ℂ) + (if i.2 = 0 then -(b : ℂ) * Complex.I else (b : ℂ) * Complex.I)
      else if i.2 = j.2 then
        (if i.2 = 0 then 1 else -1) *
          ((c : ℂ) + (if i.1 = 0 then -(d : ℂ) * Complex.I else (d : ℂ) * Complex.I))
      else 0 := by
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carDirection, pauliWord, pauliMatrix, qubitX, qubitZ,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, smul_eq_mul] <;> ring

private theorem carImbalance_apply (i j : Mode) :
    carImbalance i j = if i = j then
      if i = (0,0) then 1 else if i = (1,1) then -1 else 0
      else 0 := by
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carImbalance, pauliWord, pauliMatrix, qubitZ,
      Matrix.kroneckerMap_apply, Matrix.one_apply, smul_eq_mul]

private theorem carDirection_hermitian (a b c d : ℝ) :
    (carDirection a b c d)ᴴ = carDirection a b c d := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carDirection_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def, Complex.I_mul_I]

set_option maxHeartbeats 1000000 in
-- The square expands sixteen entries, each with a four-term matrix product.
private theorem carDirection_square (a b c d : ℝ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    carDirection a b c d * carDirection a b c d = 1 := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    apply Complex.ext <;>
    norm_num [carDirection_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im] <;>
    ring_nf <;> linarith only [h]

private theorem carImbalance_hermitian : carImbalanceᴴ = carImbalance := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carImbalance_apply, Matrix.conjTranspose_apply, Matrix.one_apply]

private theorem carDirection_even (a b c d : ℝ) :
    carImbalance * carDirection a b c d * carImbalance = 0 := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carDirection_apply, carImbalance_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem carDirection_parity (a b c d : ℝ) :
    carDirection a b c d * (carImbalance * carImbalance) =
      (1 - carImbalance * carImbalance) * carDirection a b c d := by
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [carDirection_apply, carImbalance_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

private theorem carDirection_trace (a b c d : ℝ) :
    (carDirection a b c d).trace = 0 ∧
      (carImbalance * carDirection a b c d).trace = 0 := by
  constructor <;>
    norm_num [Matrix.trace, Matrix.diag, carDirection_apply, carImbalance_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

private theorem carImbalance_trace :
    carImbalance.trace = 0 ∧ (carImbalance * carImbalance).trace = 2 := by
  constructor <;>
    norm_num [Matrix.trace, Matrix.diag, carImbalance_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

set_option maxHeartbeats 2000000 in
/-- Every unit Clifford direction and unit real pair give a rank-two Hermitian
projection with the exact physical imbalance. -/
theorem carProductCut_projection (a b c d u rho : ℝ)
    (hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (hu : u ^ 2 + rho ^ 2 = 1) :
    let P := carProductCut (carDirection a b c d) u rho
    P.IsHermitian ∧ P * P = P ∧ P.trace = 2 ∧
      (carImbalance * P).trace.re = rho := by
  dsimp only
  let G := carDirection a b c d
  let F := carImbalance
  let Z := carPartner G
  have hG : Gᴴ = G := carDirection_hermitian _ _ _ _
  have hF : Fᴴ = F := carImbalance_hermitian
  have hGG : G * G = 1 := carDirection_square _ _ _ _ hn
  have hFGF : F * G * F = 0 := carDirection_even _ _ _ _
  have hGF : G * (F * F) = (1 - F * F) * G := carDirection_parity _ _ _ _
  have hZ : Zᴴ = Z := by
    change (F - G * F * G)ᴴ = F - G * F * G
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hF, hG, Matrix.mul_assoc]
  have hGZ : G * Z + Z * G = 0 := by
    change G * (F - G * F * G) + (F - G * F * G) * G = 0
    calc
      G * (F - G * F * G) + (F - G * F * G) * G =
          G * F - (G * G) * F * G + (F * G - G * F * (G * G)) := by
        noncomm_ring
      _ = 0 := by rw [hGG]; simp
  have hZZ : Z * Z = 1 := by
    change (F - G * F * G) * (F - G * F * G) = 1
    calc
      (F - G * F * G) * (F - G * F * G) =
          F * F - (F * G * F) * G - G * (F * G * F) +
            G * F * (G * G) * F * G := by noncomm_ring
      _ = 1 := by
        rw [hFGF, hGG]
        simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.mul_one]
        rw [show G * F * F * G = (G * (F * F)) * G by noncomm_ring,
          hGF, Matrix.mul_assoc, hGG, Matrix.mul_one]
        abel
  have htrG : G.trace = 0 := (carDirection_trace _ _ _ _).1
  have htrFG : (F * G).trace = 0 := (carDirection_trace _ _ _ _).2
  have htrF : F.trace = 0 := carImbalance_trace.1
  have htrFF : (F * F).trace = 2 := carImbalance_trace.2
  have htrZ : Z.trace = 0 := by
    change (F - G * F * G).trace = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (G * F) G, ← Matrix.mul_assoc,
      hGG, Matrix.one_mul, sub_self]
  have htrFZ : (F * Z).trace = 2 := by
    change (F * (F - G * F * G)).trace = 2
    rw [Matrix.mul_sub, Matrix.trace_sub,
      show F * (G * F * G) = (F * G * F) * G by noncomm_ring, hFGF]
    simp only [Matrix.zero_mul, Matrix.trace_zero, sub_zero, htrFF]
  let H := (u : ℂ) • G + (rho : ℂ) • Z
  have hH : Hᴴ = H := by
    simp [H, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hG, hZ]
  have hHH : H * H = 1 := by
    change (u • G + rho • Z) * (u • G + rho • Z) = (1 : TwoMode)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, hGG, hZZ]
    rw [mul_comm rho u]
    have hc : u * u + rho * rho = 1 := by simpa only [pow_two] using hu
    calc
      _ = (u * u) • (1 : TwoMode) + (rho * rho) • (1 : TwoMode) +
          ((u * rho) • (G * Z) + (u * rho) • (Z * G)) := by abel
      _ = 1 := by rw [← add_smul, hc, one_smul, ← smul_add, hGZ, smul_zero, add_zero]
  have hP : carProductCut G u rho = (1 / 2 : ℂ) • (1 + H) := by
    simp only [carProductCut, H, Z, add_assoc]
  change (carProductCut G u rho).IsHermitian ∧
    carProductCut G u rho * carProductCut G u rho = carProductCut G u rho ∧
    (carProductCut G u rho).trace = 2 ∧ (F * carProductCut G u rho).trace.re = rho
  rw [hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ((1 / 2 : ℂ) • (1 + H))ᴴ = _
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    rw [add_comm H (1 : TwoMode), ← add_smul,
      show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, one_smul]
  · norm_num [H, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one,
      Fintype.card_prod, htrG, htrZ, smul_eq_mul]
  · simp only [H, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
      Matrix.trace_add, htrF, htrFG, htrFZ, smul_eq_mul, mul_zero, zero_add]
    rw [show (1 / 2 : ℂ) * ((rho : ℂ) * 2) = (rho : ℂ) by ring, Complex.ofReal_re]

#print axioms carProductCut_projection

end WuRankOneEndpointFloor
