/- GID: D5/S3/Quantum/Semigroups/WuPhysicalProductCut
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuPhysicalProductCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-mode Clifford cuts have exact rank and imbalance. -/

import D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford

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

/-- Normalized trace coordinates of a two-mode matrix in the physical Pauli frame. -/
def carCoordinate (H : TwoMode) (p q : Pauli) : ℝ :=
  (H * pauliWord p q).trace.re / 4

/-- The magnitude of the degree-one Clifford component. -/
def carFirstNorm (H : TwoMode) : ℝ :=
  Real.sqrt ((carCoordinate H .I .X) ^ 2 + (carCoordinate H .I .Y) ^ 2 +
    (carCoordinate H .X .Z) ^ 2 + (carCoordinate H .Y .Z) ^ 2)

private theorem carDirection_overlap (H : TwoMode) (a b c d : ℝ) :
    (H * carDirection a b c d).trace.re =
      4 * (a * carCoordinate H .I .X + b * carCoordinate H .I .Y +
        c * carCoordinate H .X .Z + d * carCoordinate H .Y .Z) := by
  simp [carDirection, carCoordinate, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.add_re] <;> ring

set_option maxHeartbeats 1000000 in
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
      Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def, Complex.I_mul_I] <;> ring

set_option maxHeartbeats 1000000 in
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
    first | ring | nlinarith only [h]

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
    norm_num [Matrix.trace, Matrix.diag, carImbalance_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

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
    change (F - G * F * G)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hF, hG]
    simp [Z, carPartner, Matrix.mul_assoc]
  have hGZ : G * Z + Z * G = 0 := by
    dsimp [Z, carPartner]
    calc
      G * (F - G * F * G) + (F - G * F * G) * G =
          G * F - (G * G) * F * G + (F * G - G * F * (G * G)) := by
        noncomm_ring
      _ = 0 := by rw [hGG]; simp
  have hZZ : Z * Z = 1 := by
    dsimp [Z, carPartner]
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
    dsimp [Z, carPartner]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (G * F) G, ← Matrix.mul_assoc,
      hGG, Matrix.one_mul, sub_self]
  have htrFZ : (F * Z).trace = 2 := by
    dsimp [Z, carPartner]
    rw [Matrix.mul_sub, Matrix.trace_sub,
      show F * (G * F * G) = (F * G * F) * G by noncomm_ring, hFGF]
    simp [htrFF]
  let H := (u : ℂ) • G + (rho : ℂ) • Z
  have hH : Hᴴ = H := by
    simp [H, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hG, hZ]
  have hHH : H * H = 1 := by
    dsimp [H]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hGG, hZZ]
    rw [mul_comm (rho : ℂ) (u : ℂ)]
    have hc : (u : ℂ) * u + (rho : ℂ) * rho = 1 := by
      exact_mod_cast (by nlinarith only [hu] : u * u + rho * rho = 1)
    calc
      _ = ((u : ℂ) * u) • (1 : TwoMode) + ((rho : ℂ) * rho) • (1 : TwoMode) +
          (((u : ℂ) * rho) • (G * Z) + ((u : ℂ) * rho) • (Z * G)) := by abel
      _ = 1 := by rw [← add_smul, hc, one_smul, ← smul_add, hGZ, smul_zero, add_zero]
  change ((1 / 2 : ℂ) • (1 + H)).IsHermitian ∧
    ((1 / 2 : ℂ) • (1 + H)) * ((1 / 2 : ℂ) • (1 + H)) =
      (1 / 2 : ℂ) • (1 + H) ∧
    ((1 / 2 : ℂ) • (1 + H)).trace = 2 ∧
    (F * ((1 / 2 : ℂ) • (1 + H))).trace.re = rho
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ((1 / 2 : ℂ) • (1 + H))ᴴ = _
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    rw [show (1 : TwoMode) + H + (H + 1) = (2 : ℂ) • (1 + H) by
      rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
      abel, smul_smul]
    norm_num
  · norm_num [H, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_prod, htrG, htrZ, smul_eq_mul]
  · norm_num [H, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
      htrF, htrFG, htrFZ, smul_eq_mul, Complex.mul_re]

/-- The parity-preserving component, in the actual two-mode occupation order. -/
private def carEvenPart (H : TwoMode) : TwoMode :=
  Matrix.of fun i j => if (i.1 = i.2 ↔ j.1 = j.2) then H i j else 0

set_option maxHeartbeats 3000000 in
private theorem carFirst_even_anticommutes (H : TwoMode)
    (hH : H.IsHermitian) (hHH : H * H = 1) (htr : H.trace = 0) :
    let G := carDirection (carCoordinate H .I .X) (carCoordinate H .I .Y)
      (carCoordinate H .X .Z) (carCoordinate H .Y .Z)
    carEvenPart H * G + G * carEvenPart H = 0 := by
  dsimp only
  have hreal (i j : Mode) : (H j i).re = (H i j).re := by
    simpa using congrArg Complex.re (hH.apply i j)
  have himag (i j : Mode) : -(H j i).im = (H i j).im := by
    simpa using congrArg Complex.im (hH.apply i j)
  have hi (i j : Mode) : (H j i).im = -(H i j).im := by
    linarith only [himag i j]
  have hd (i : Mode) : (H i i).im = 0 := by
    linarith only [himag i i]
  have hsum := congrArg Complex.re htr
  norm_num [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re] at hsum
  have hlast : (H (1,1) (1,1)).re =
      -(H (0,0) (0,0)).re - (H (0,1) (0,1)).re - (H (1,0) (1,0)).re := by
    linarith only [hsum]
  have hzero (i j : Mode) (h : i ≠ j) : (H * H) i j = 0 := by
    rw [hHH, Matrix.one_apply_ne h]
  have h01r := congrArg Complex.re (hzero (0,0) (0,1) (by decide))
  have h01i := congrArg Complex.im (hzero (0,0) (0,1) (by decide))
  have h02r := congrArg Complex.re (hzero (0,0) (1,0) (by decide))
  have h02i := congrArg Complex.im (hzero (0,0) (1,0) (by decide))
  have h31r := congrArg Complex.re (hzero (1,1) (0,1) (by decide))
  have h31i := congrArg Complex.im (hzero (1,1) (0,1) (by decide))
  have h32r := congrArg Complex.re (hzero (1,1) (1,0) (by decide))
  have h32i := congrArg Complex.im (hzero (1,1) (1,0) (by decide))
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.zero_re, Complex.zero_im] at h01r h01i h02r h02i h31r h31i h32r h32i
  simp only [hreal (0,0) (0,1), hreal (0,0) (1,0), hreal (0,0) (1,1),
    hreal (0,1) (1,0), hreal (0,1) (1,1), hreal (1,0) (1,1),
    hi (0,0) (0,1), hi (0,0) (1,0), hi (0,0) (1,1),
    hi (0,1) (1,0), hi (0,1) (1,1), hi (1,0) (1,1), hd, hlast] at
    h01r h01i h02r h02i h31r h31i h32r h32i
  apply Matrix.ext
  rintro ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    apply Complex.ext <;>
    norm_num [carEvenPart, carDirection_apply, carCoordinate, pauliWord, pauliMatrix,
      qubitX, qubitZ, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, hreal (0,0) (0,1), hreal (0,0) (1,0),
      hreal (0,0) (1,1), hreal (0,1) (1,0), hreal (0,1) (1,1),
      hreal (1,0) (1,1), hi (0,0) (0,1), hi (0,0) (1,0), hi (0,0) (1,1),
      hi (0,1) (1,0), hi (0,1) (1,1), hi (1,0) (1,1), hd, hlast] <;>
    first | ring | linarith only [h01r, h01i, h02r, h02i, h31r, h31i, h32r, h32i]

private theorem carDirection_scale (a b c d t : ℝ) :
    carDirection (t * a) (t * b) (t * c) (t * d) =
      (t : ℂ) • carDirection a b c d := by
  simp [carDirection, smul_add, smul_smul]

set_option maxHeartbeats 3000000 in
private theorem carEven_direction (H : TwoMode)
    (hH : H.IsHermitian) (hHH : H * H = 1) (htr : H.trace = 0) :
    ∃ a b c d : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧
      carEvenPart H * carDirection a b c d + carDirection a b c d * carEvenPart H = 0 := by
  let p := ((H (0,0) (0,0)).re - (H (1,1) (1,1)).re) / 2
  let q := ((H (0,1) (0,1)).re - (H (1,0) (1,0)).re) / 2
  let x := (H (0,0) (1,1)).re
  let y := (H (0,0) (1,1)).im
  let z := (H (0,1) (1,0)).re
  let w := (H (0,1) (1,0)).im
  have hreal (i j : Mode) : (H j i).re = (H i j).re := by
    simpa using congrArg Complex.re (hH.apply i j)
  have himag (i j : Mode) : -(H j i).im = (H i j).im := by
    simpa using congrArg Complex.im (hH.apply i j)
  have hi (i j : Mode) : (H j i).im = -(H i j).im := by
    linarith only [himag i j]
  have hd (i : Mode) : (H i i).im = 0 := by
    linarith only [himag i i]
  have hsum := congrArg Complex.re htr
  norm_num [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re] at hsum
  have hlast : (H (1,1) (1,1)).re =
      -(H (0,0) (0,0)).re - (H (0,1) (0,1)).re - (H (1,0) (1,0)).re := by
    linarith only [hsum]
  have hdiag (i : Mode) : (H * H) i i = 1 := by rw [hHH, Matrix.one_apply_eq]
  have h0 := congrArg Complex.re (hdiag (0,0))
  have h1 := congrArg Complex.re (hdiag (0,1))
  have h2 := congrArg Complex.re (hdiag (1,0))
  have h3 := congrArg Complex.re (hdiag (1,1))
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re, Complex.mul_re, Complex.one_re,
    hreal (0,0) (0,1), hreal (0,0) (1,0), hreal (0,0) (1,1),
    hreal (0,1) (1,0), hreal (0,1) (1,1), hreal (1,0) (1,1),
    hi (0,0) (0,1), hi (0,0) (1,0), hi (0,0) (1,1),
    hi (0,1) (1,0), hi (0,1) (1,1), hi (1,0) (1,1), hd, hlast] at h0 h1 h2 h3
  have hmatch : p ^ 2 + x ^ 2 + y ^ 2 = q ^ 2 + z ^ 2 + w ^ 2 := by
    dsimp [p, q, x, y, z, w]
    rw [hlast]
    linarith only [h0, h1, h2, h3]
  have hanti (b c d : ℝ)
      (e0 : c * (z - x) + d * (y - w) = 0)
      (e1 : b * (p + q) + d * (x + z) + c * (y + w) = 0)
      (e2 : c * (p - q) - b * (y - w) = 0)
      (e3 : -d * (p - q) + b * (x - z) = 0) :
      carEvenPart H * carDirection 0 b c d + carDirection 0 b c d * carEvenPart H = 0 := by
    dsimp [p, q, x, y, z, w] at e0 e1 e2 e3
    simp only [hlast] at e1 e2 e3
    apply Matrix.ext
    rintro ⟨i,k⟩ ⟨j,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      apply Complex.ext <;>
      norm_num [carEvenPart, carDirection_apply, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.of_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.neg_re, Complex.neg_im, hreal (0,0) (1,1), hreal (0,1) (1,0),
        hi (0,0) (1,1), hi (0,1) (1,0), hd, hlast] <;>
      first | ring | linarith only [e0,e1,e2,e3]
  obtain ⟨b,c,d,hpos,hbcd⟩ : ∃ b c d : ℝ, 0 < b ^ 2 + c ^ 2 + d ^ 2 ∧
      carEvenPart H * carDirection 0 b c d + carDirection 0 b c d * carEvenPart H = 0 := by
    by_cases hs : p = q ∧ x = z ∧ y = w
    · obtain ⟨hp,hx,hy⟩ := hs
      by_cases hz : p = 0 ∧ x = 0
      · refine ⟨1, 0, 0, by norm_num, hanti 1 0 0 ?_ ?_ ?_ ?_⟩ <;>
          simp [← hp, ← hx, ← hy, hz.1, hz.2]
      · refine ⟨x, 0, -p, ?_, hanti x 0 (-p) ?_ ?_ ?_ ?_⟩
        · by_contra! hn
          have hx0 : x = 0 := by nlinarith [sq_nonneg p, sq_nonneg x]
          have hp0 : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg x]
          exact hz ⟨hp0, hx0⟩
        all_goals simp [← hp, ← hx, ← hy] <;> ring
    · refine ⟨-(p-q), -(y-w), -(x-z), ?_, hanti _ _ _ ?_ ?_ ?_ ?_⟩
      · by_contra! hn
        have hpq : p = q := by nlinarith [sq_nonneg (p-q), sq_nonneg (x-z), sq_nonneg (y-w)]
        have hxz : x = z := by nlinarith [sq_nonneg (p-q), sq_nonneg (x-z), sq_nonneg (y-w)]
        have hyw : y = w := by nlinarith [sq_nonneg (p-q), sq_nonneg (x-z), sq_nonneg (y-w)]
        exact hs ⟨hpq,hxz,hyw⟩
      · ring
      · linarith only [hmatch]
      · ring
      · ring
  let n := Real.sqrt (b ^ 2 + c ^ 2 + d ^ 2)
  have hn : 0 < n := Real.sqrt_pos.2 hpos
  have hn2 : n ^ 2 = b ^ 2 + c ^ 2 + d ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨0, b/n, c/n, d/n, ?_, ?_⟩
  · field_simp [ne_of_gt hn]
    linarith only [hn2]
  · have hscale : carDirection 0 (b/n) (c/n) (d/n) =
        ((1/n : ℝ) : ℂ) • carDirection 0 b c d := by
      rw [← carDirection_scale]
      congr 1 <;> ring
    rw [hscale, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, hbcd, smul_zero]

set_option maxHeartbeats 1000000 in
private theorem carEven_trace (H : TwoMode) (a b c d : ℝ) :
    let G := carDirection a b c d
    (carImbalance * carEvenPart H).trace = (carImbalance * H).trace ∧
    (carImbalance * (G * carEvenPart H * G)).trace =
      (carImbalance * (G * H * G)).trace := by
  dsimp only
  constructor <;>
    norm_num [carEvenPart, carDirection_apply, carImbalance_apply, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.of_apply]

private theorem carPartner_overlap (H : TwoMode) (a b c d : ℝ)
    (hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1)
    (hanti : carEvenPart H * carDirection a b c d +
      carDirection a b c d * carEvenPart H = 0) :
    (H * carPartner (carDirection a b c d)).trace =
      2 * (carImbalance * H).trace := by
  let G := carDirection a b c d
  let E := carEvenPart H
  let F := carImbalance
  have hGG : G * G = 1 := carDirection_square _ _ _ _ hn
  have hEG : E * G = -(G * E) := by
    calc
      E * G = E * G + G * E - G * E := by abel
      _ = -(G * E) := by rw [hanti]; simp
  have hGEG : G * E * G = -E := by
    rw [Matrix.mul_assoc, hEG, Matrix.mul_neg, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  have hE := carEven_trace H a b c d
  change (F * E).trace = (F * H).trace ∧
    (F * (G * E * G)).trace = (F * (G * H * G)).trace at hE
  have hcyc : (H * (G * F * G)).trace = (F * (G * H * G)).trace := by
    calc
      _ = ((H * G * F) * G).trace := by simp only [Matrix.mul_assoc]
      _ = (G * (H * G * F)).trace := Matrix.trace_mul_comm _ _
      _ = ((G * H * G) * F).trace := by simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  change (H * (F - G * F * G)).trace = _
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_mul_comm H F, hcyc,
    ← hE.2, hGEG, Matrix.mul_neg, Matrix.trace_neg, hE.1]
  ring

/-- Exact Hilbert--Schmidt squared distance from an arbitrary complex rank-two
projection to the physical cut, resolved into its two Clifford overlaps. -/
theorem carProductCut_distance (P : TwoMode) (hP : P.IsHermitian)
    (hPP : P * P = P) (htrP : P.trace = 2)
    (a b c d u rho : ℝ)
    (hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (hu : u ^ 2 + rho ^ 2 = 1) :
    let G := carDirection a b c d
    let H := (2 : ℂ) • P - 1
    let Q := carProductCut G u rho
    ((P - Q)ᴴ * (P - Q)).trace.re =
      2 - (u * (H * G).trace.re + rho * (H * carPartner G).trace.re) / 2 := by
  dsimp only
  let G := carDirection a b c d
  let H := (2 : ℂ) • P - 1
  let Z := carPartner G
  let Q := carProductCut G u rho
  change ((P - Q)ᴴ * (P - Q)).trace.re =
    2 - (u * (H * G).trace.re + rho * (H * Z).trace.re) / 2
  obtain ⟨hQ, hQQ, htrQ, _⟩ := carProductCut_projection a b c d u rho hn hu
  change Qᴴ = Q at hQ
  change Q * Q = Q at hQQ
  change Q.trace = 2 at htrQ
  have htrG : G.trace = 0 := (carDirection_trace _ _ _ _).1
  have htrZ : Z.trace = 0 := by
    have hGG : G * G = 1 := carDirection_square _ _ _ _ hn
    dsimp [Z, carPartner]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (G * carImbalance) G,
      ← Matrix.mul_assoc, hGG, Matrix.one_mul, sub_self]
  have hPG : (H * G).trace = 2 * (P * G).trace := by
    dsimp [H]
    simp [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, htrG,
      smul_eq_mul]
  have hPZ : (H * Z).trace = 2 * (P * Z).trace := by
    dsimp [H]
    simp [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, htrZ,
      smul_eq_mul]
  have hPQ : (P * Q).trace =
      (1 / 2 : ℂ) * (2 + (u : ℂ) * (P * G).trace + (rho : ℂ) * (P * Z).trace) := by
    dsimp [Q, carProductCut, Z]
    simp [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
      htrP, smul_eq_mul]
  change Pᴴ = P at hP
  rw [Matrix.conjTranspose_sub, hP, hQ]
  rw [show (P - Q) * (P - Q) = P - P * Q - Q * P + Q by
    calc
      _ = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
      _ = _ := by rw [hPP, hQQ]]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm Q P, htrP, htrQ, hPQ, hPG, hPZ]
  norm_num [Complex.mul_re, Complex.add_re, Complex.sub_re] <;> ring

set_option maxHeartbeats 2000000 in
/-- Physical product-cut transport of every complex rank-two projection.
The distance and the signed imbalance use ordinary trace. -/
theorem carProductCut_transport (P : TwoMode) (hP : P.IsHermitian)
    (hPP : P * P = P) (htrP : P.trace = 2) :
    let H := (2 : ℂ) • P - 1
    let k := carFirstNorm H
    let R := (carImbalance * P).trace.re
    let theta := Real.sqrt (k ^ 2 + R ^ 2)
    ∃ a b c d u rho : ℝ,
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧ u ^ 2 + rho ^ 2 = 1 ∧
      theta ≤ 1 ∧ theta * u = k ∧ theta * rho = R ∧
      (let Q := carProductCut (carDirection a b c d) u rho
       Q.IsHermitian ∧ Q * Q = Q ∧ Q.trace = 2 ∧
       (carImbalance * Q).trace.re = rho ∧
       ((P - Q)ᴴ * (P - Q)).trace.re = 2 * (1 - theta)) := by
  dsimp only
  let H := (2 : ℂ) • P - 1
  let k := carFirstNorm H
  let R := (carImbalance * P).trace.re
  let theta := Real.sqrt (k ^ 2 + R ^ 2)
  have hH : H.IsHermitian := by
    change ((2 : ℂ) • P - 1)ᴴ = _
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]
  have hHH : H * H = 1 := by
    change ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1) = _
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hPP, Matrix.one_mul, Matrix.mul_one]
    norm_num <;> module
  have htrH : H.trace = 0 := by
    norm_num [H, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod, htrP, smul_eq_mul]
  let x := carCoordinate H .I .X
  let y := carCoordinate H .I .Y
  let z := carCoordinate H .X .Z
  let w := carCoordinate H .Y .Z
  have hk2 : k ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 :=
    Real.sq_sqrt (by positivity)
  have htheta2 : theta ^ 2 = k ^ 2 + R ^ 2 := Real.sq_sqrt (by positivity)
  have hkn : 0 ≤ k := Real.sqrt_nonneg _
  have htn : 0 ≤ theta := Real.sqrt_nonneg _
  obtain ⟨a,b,c,d,hn,hanti,hoverG⟩ :
      ∃ a b c d : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧
        carEvenPart H * carDirection a b c d + carDirection a b c d * carEvenPart H = 0 ∧
        (H * carDirection a b c d).trace.re = 4 * k := by
    by_cases hk : 0 < k
    · let a := x / k
      let b := y / k
      let c := z / k
      let d := w / k
      let G := carDirection a b c d
      have hn : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
        dsimp [a, b, c, d]
        field_simp [ne_of_gt hk]
        nlinarith only [hk2]
      have hnorm : G = ((1 / k : ℝ) : ℂ) • carDirection x y z w := by
        dsimp [G, a, b, c, d]
        rw [← carDirection_scale]
        congr 1 <;> ring
      have hanti : carEvenPart H * G + G * carEvenPart H = 0 := by
        rw [hnorm, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
        change ((1 / k : ℝ) : ℂ) •
          (carEvenPart H * carDirection x y z w + carDirection x y z w * carEvenPart H) = 0
        rw [carFirst_even_anticommutes H hH hHH htrH, smul_zero]
      have hoverG : (H * G).trace.re = 4 * k := by
        rw [carDirection_overlap]
        change 4 * (a * x + b * y + c * z + d * w) = _
        dsimp [a, b, c, d]
        field_simp [ne_of_gt hk]
        nlinarith only [hk2]
      exact ⟨a,b,c,d,hn,hanti,hoverG⟩
    · have hk0 : k = 0 := le_antisymm (le_of_not_gt hk) hkn
      have hx0 : x = 0 := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg w]
      have hz0 : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg w]
      have hw0 : w = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      obtain ⟨a,b,c,d,hn,hanti⟩ := carEven_direction H hH hHH htrH
      refine ⟨a,b,c,d,hn,hanti,?_⟩
      rw [carDirection_overlap]
      change 4 * (a*x + b*y + c*z + d*w) = 4*k
      simp [hx0,hy0,hz0,hw0,hk0]
  let G := carDirection a b c d
  obtain ⟨u,rho,hu,huu,hur,hsum⟩ : ∃ u rho : ℝ,
      u ^ 2 + rho ^ 2 = 1 ∧ theta * u = k ∧ theta * rho = R ∧
      u * k + rho * R = theta := by
    by_cases ht : 0 < theta
    · refine ⟨k/theta, R/theta, ?_, ?_, ?_, ?_⟩
      · field_simp [ne_of_gt ht]
        nlinarith only [htheta2]
      · field_simp [ne_of_gt ht]
      · field_simp [ne_of_gt ht]
      · field_simp [ne_of_gt ht]
        nlinarith only [htheta2]
    · have ht0 : theta = 0 := le_antisymm (le_of_not_gt ht) htn
      have hks : k = 0 := by nlinarith [sq_nonneg R]
      have hrs : R = 0 := by nlinarith [sq_nonneg k]
      exact ⟨1,0,by norm_num,by simp [ht0,hks],by simp [ht0,hrs],by simp [ht0,hks,hrs]⟩
  have hoverZ : (H * carPartner G).trace.re = 4 * R := by
    rw [carPartner_overlap H a b c d hn hanti]
    change (2 * (carImbalance * ((2 : ℂ) • P - 1)).trace).re = _
    simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      carImbalance_trace.1, R, smul_eq_mul, Complex.mul_re]
    ring
  let Q := carProductCut G u rho
  have hdist : ((P - Q)ᴴ * (P - Q)).trace.re = 2 * (1 - theta) := by
    rw [carProductCut_distance P hP hPP htrP a b c d u rho hn hu,
      hoverG, hoverZ]
    linarith only [hsum]
  have hpos : 0 ≤ ((P - Q)ᴴ * (P - Q)).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (P - Q)).trace_nonneg).1
  have hle : theta ≤ 1 := by linarith only [hpos, hdist]
  obtain ⟨hQ, hQQ, htrQ, hR⟩ := carProductCut_projection a b c d u rho hn hu
  exact ⟨a, b, c, d, u, rho, hn, hu, hle, huu, hur, hQ, hQQ, htrQ, hR, hdist⟩

#print axioms carProductCut_projection
#print axioms carProductCut_distance
#print axioms carProductCut_transport

end WuRankOneEndpointFloor
