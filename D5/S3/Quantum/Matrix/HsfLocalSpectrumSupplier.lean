/- GID: D5/S3/Quantum/Matrix/HsfLocalSpectrumSupplier
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfLocalSpectrumSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: General finite-spectrum coefficient algebra for the local two-thirds supplier. -/

import D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Matrix.CartesianVariance

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Frobenius norm, fixed independently of the operator norm used by CFC. -/
def frob (M : Matrix n n ℂ) : ℝ :=
  @norm _ (Matrix.frobeniusNormedAddCommGroup (n := n) (m := n) (α := ℂ)).toNorm M

private def tr (M : Matrix n n ℂ) : ℂ := M.trace

private theorem tr_comm (A B : Matrix n n ℂ) : tr (A*B) = tr (B*A) :=
  Matrix.trace_mul_comm A B

private theorem tr_cycle (A B C : Matrix n n ℂ) : tr (A*B*C) = tr (B*C*A) :=
  (Matrix.trace_mul_cycle B C A).symm

section Actual
open scoped Matrix.Norms.L2Operator
private theorem actual_trace_normalization {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian) :
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := RpowPencilTaylor.jetCoeff
      (fun t : ℝ => P⁻¹*CFC.rpow (Y+t • K) (2/3 : ℝ)*P⁻¹)
    let Q := K*(P⁻¹)^3
    tr (B 2)-tr (B 1*B 1)/2 = -tr (Q^2)/3 ∧
      tr (B 3)-tr (B 1*B 2)+tr (B 1*B 1*B 1)/3 = 2*tr (Q^3)/9 := by
  simpa only [tr] using HsfLocalSpectrumTrace.actual_trace_normalization hY hK

end Actual

section Frobenius
open scoped Matrix.Norms.Frobenius

private theorem frob_nonneg (M : Matrix n n ℂ) : 0 ≤ frob M := norm_nonneg M

private theorem frob_mul (M N : Matrix n n ℂ) : frob (M*N) ≤ frob M*frob N :=
  Matrix.frobenius_norm_mul M N

private theorem frob_sq (M : Matrix n n ℂ) :
    frob M^2 = (Mᴴ*M).trace.re := by
  have h := congrArg Complex.re (GNSMatrix.frobenius_norm_sq_eq_trace M)
  simpa only [frob, Complex.ofReal_re] using h

private theorem frob_sq_sum (M : Matrix n n ℂ) :
    frob M^2 = ∑ i, ∑ j, ‖M i j‖^2 := by
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (M i))‖^2 = _
  simp [PiLp.norm_sq_eq_of_L2]

private theorem abs_reTrace_mul {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ) :
    |(M*N).trace.re| ≤ frob M*frob N := by
  have h := CartesianVariance.trace_product_cauchy M N
  change Complex.normSq (M*N).trace ≤ (Mᴴ*M).trace.re*(Nᴴ*N).trace.re at h
  rw [← frob_sq, ← frob_sq] at h
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (frob_nonneg _) (frob_nonneg _))).mp
  rw [sq_abs, mul_pow]
  rw [Complex.normSq_apply] at h
  nlinarith [sq_nonneg ((M*N).trace.im)]

private theorem abs_reTrace_cube {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |(M^3).trace.re| ≤ frob M^3 := by
  have h := (abs_reTrace_mul M (M*M)).trans
    (mul_le_mul_of_nonneg_left (frob_mul M M) (frob_nonneg M))
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

private theorem frob_sq_hermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (M*M).trace.re = frob M^2 := by rw [frob_sq, hM.eq]

private theorem quadratic_remainder_bound {d : ℕ}
    (A D R : Matrix (Fin d) (Fin d) ℂ) (hR : R.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/2)
    (hA : frob A ≤ r) (hD : frob D ≤ 2*r^2) :
    -24*r^4 ≤ 12*(((1+A)*R*R).trace.re-(D*R).trace.re) := by
  let q := frob R
  have hq : 0 ≤ q := frob_nonneg R
  have ha : |(A*(R*R)).trace.re| ≤ r*q^2 := by
    calc
      _ ≤ frob A*frob (R*R) := abs_reTrace_mul A (R*R)
      _ ≤ r*(q*q) := mul_le_mul hA (frob_mul R R)
        (frob_nonneg _) hr
      _ = r*q^2 := by ring
  have hd : |(D*R).trace.re| ≤ 2*r^2*q :=
    (abs_reTrace_mul D R).trans (mul_le_mul_of_nonneg_right hD hq)
  have he : ((1+A)*R*R).trace.re = q^2+(A*(R*R)).trace.re := by
    simp only [add_mul, one_mul, Matrix.trace_add, Complex.add_re, mul_assoc,
      frob_sq_hermitian hR]
    rfl
  have hlow := (abs_le.mp ha).1
  have hhigh := (abs_le.mp hd).2
  rw [he]
  have hhalf : (1/2 : ℝ)*q^2 ≤ (1-r)*q^2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg q)
  nlinarith [sq_nonneg (q-2*r^2)]

private theorem local_scalar_margin (δ r g h e : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (hsmall : 32*r ≤ 3*δ)
    (hg : δ*r^2 ≤ g) (hh : -20*r^3 ≤ h) (he : -24*r^4 ≤ e) :
    3*δ*r^2 ≤ 6*g+h+e := by
  have hquartic : 24*r^4 ≤ 12*r^3 := by
    have h := mul_le_mul_of_nonneg_right hrhalf (by positivity : 0 ≤ 24*r^3)
    nlinarith only [h]
  have hrad := mul_le_mul_of_nonneg_right hsmall (sq_nonneg r)
  nlinarith

end Frobenius
/-- The positive divisor of the ordered cubic linearization. -/
def spectralDen (a b : ℝ) : ℝ := a^2+a*b+b^2

/-- The general-spectrum first-jet Schur multiplier. -/
def spectralTau (a b : ℝ) : ℝ :=
  3*Real.sqrt (a*b)*(a+b)/(2*spectralDen a b)

/-- The second-jet kernel, with its middle spectral value explicit. -/
def spectralKernel (a b c : ℝ) : ℝ :=
  Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/
    (spectralDen a b*spectralDen a c*spectralDen c b)

private theorem spectralDen_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < spectralDen a b := by unfold spectralDen; positivity

private theorem spectralTau_gap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1-spectralTau a b^2 =
      (a-b)^2*(4*a^2+7*a*b+4*b^2)/(4*(spectralDen a b)^2) := by
  have hd := (spectralDen_pos ha hb).ne'
  have hs := Real.sq_sqrt (mul_pos ha hb).le
  unfold spectralTau
  field_simp
  rw [hs]
  unfold spectralDen
  ring

private theorem spectralTau_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < spectralTau a b ∧ spectralTau a b ≤ 1 := by
  have ht : 0 < spectralTau a b := by
    unfold spectralTau
    exact div_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos ha hb)))
      (add_pos ha hb)) (mul_pos (by norm_num) (spectralDen_pos ha hb))
  refine ⟨ht, ?_⟩
  have hgap := spectralTau_gap ha hb
  have hnonneg : 0 ≤ (a-b)^2*(4*a^2+7*a*b+4*b^2)/(4*(spectralDen a b)^2) := by positivity
  nlinarith

private theorem spectralTau_strict {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) : 0 < 1-spectralTau a b^2 := by
  rw [spectralTau_gap ha hb]
  have hd := spectralDen_pos ha hb
  have hsq : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  positivity

private theorem spectralKernel_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < spectralKernel a b c ∧ spectralKernel a b c ≤ 2/3 := by
  have hd := spectralDen_pos ha hb
  have he := spectralDen_pos ha hc
  have hf := spectralDen_pos hc hb
  have hs := Real.sqrt_pos.mpr (mul_pos ha hb)
  refine ⟨by unfold spectralKernel; positivity, ?_⟩
  have ht := (spectralTau_bounds ha hb).2
  have ht' : 3*Real.sqrt (a*b)*(a+b) ≤ 2*spectralDen a b := by
    exact (div_le_one (by positivity : 0 < 2*spectralDen a b)).mp ht
  have hp : c^3*(a*b+c*(a+b)) ≤ (a+b)*spectralDen a c*spectralDen c b := by
    have hh : 0 ≤ (a+b)*spectralDen a c*spectralDen c b-c^3*(a*b+c*(a+b)) := by
      unfold spectralDen
      ring_nf
      positivity
    linarith
  have hh := mul_le_mul_of_nonneg_right ht' (by positivity :
    0 ≤ c^3*(a*b+c*(a+b)))
  have hi := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*spectralDen a b)
  unfold spectralKernel
  apply (div_le_iff₀ (by positivity : 0 < spectralDen a b*spectralDen a c*spectralDen c b)).mpr
  have hj : 3*Real.sqrt (a*b)*c^3*(a*b+c*(a+b)) ≤
      2*(spectralDen a b*spectralDen a c*spectralDen c b) := by
    apply (mul_le_mul_iff_right₀ (add_pos ha hb)).mp
    nlinarith only [hh.trans hi]
  linarith

section Spectrum

private def crossPairs (p : n → ℝ) : Finset (n × n) :=
  Finset.univ.filter (fun ij => p ij.1 ≠ p ij.2)

private theorem crossPairs_nonempty {p : n → ℝ} (h : ∃ i j, p i ≠ p j) :
    (crossPairs p).Nonempty := by
  obtain ⟨i, j, hij⟩ := h
  exact ⟨(i,j), by simp [crossPairs, hij]⟩

/-- Minimum over distinct spectral levels; multiplicities are retained. -/
def crossGap (p : n → ℝ) (h : ∃ i j, p i ≠ p j) : ℝ :=
  ((crossPairs p).image (fun ij => 1-spectralTau (p ij.1) (p ij.2)^2)).min'
    ((crossPairs_nonempty h).image _)

private theorem crossGap_pos {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (h : ∃ i j, p i ≠ p j) : 0 < crossGap p h := by
  have hm := Finset.min'_mem
    ((crossPairs p).image (fun ij => 1-spectralTau (p ij.1) (p ij.2)^2))
    ((crossPairs_nonempty h).image _)
  obtain ⟨ij, hij, heq⟩ := Finset.mem_image.mp hm
  change 0 < crossGap p h
  have hpos := spectralTau_strict (hp ij.1) (hp ij.2) (by simpa [crossPairs] using hij)
  unfold crossGap
  rw [← heq]
  exact hpos

private theorem crossGap_le {p : n → ℝ} (h : ∃ i j, p i ≠ p j)
    {i j : n} (hij : p i ≠ p j) :
    crossGap p h ≤ 1-spectralTau (p i) (p j)^2 :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(i,j), by simp [crossPairs, hij], rfl⟩)

private theorem crossGap_le_one {p : n → ℝ} (h : ∃ i j, p i ≠ p j) :
    crossGap p h ≤ 1 := by
  obtain ⟨i, j, hij⟩ := h
  exact (crossGap_le ⟨i,j,hij⟩ hij).trans (by nlinarith [sq_nonneg (spectralTau (p i) (p j))])

private def schurFirst (p : n → ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (spectralTau (p i) (p j) : ℂ)*H i j

private theorem schurFirst_hermitian (p : n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) : (schurFirst p H).IsHermitian := by
  ext i j
  have ht : spectralTau (p j) (p i) = spectralTau (p i) (p j) := by
    unfold spectralTau
    rw [mul_comm (p j) (p i), add_comm (p j) (p i)]
    congr 1
    unfold spectralDen
    ring
  simp only [schurFirst, Matrix.conjTranspose_apply, star_mul, Complex.star_def,
    Complex.conj_ofReal, ht]
  have hh := hH.apply i j
  simp only [Complex.star_def] at hh
  rw [hh]
  ring

open scoped Matrix.Norms.Frobenius

private theorem schurFirst_norm {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) : frob (schurFirst p H) ≤ frob H := by
  apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
  rw [frob_sq_sum, frob_sq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have ht := spectralTau_bounds (hp i) (hp j)
  simp only [schurFirst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht.1, mul_pow]
  have hsq : spectralTau (p i) (p j)^2 ≤ 1 := by nlinarith [ht.1, ht.2]
  simpa using mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖H i j‖)

private theorem schurFirst_gap {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (h : ∃ i j, p i ≠ p j) (H : Matrix n n ℂ)
    (hsupport : ∀ i j, p i = p j → H i j = 0) :
    crossGap p h*frob H^2 ≤ frob H^2-frob (schurFirst p H)^2 := by
  simp only [frob_sq_sum]
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : p i = p j
  · simp [schurFirst, hsupport i j hij]
  · have hd := crossGap_le h hij
    have ht := (spectralTau_bounds (hp i) (hp j)).1
    simp only [schurFirst, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖H i j‖)]

end Spectrum
section Defect
open scoped Matrix.Norms.Frobenius

private def quadraticDefect (p : n → ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ k, ((3*spectralKernel (p i) (p j) (p k)-
    spectralTau (p i) (p k)*spectralTau (p k) (p j)/3 : ℝ) : ℂ)*H i k*H k j

private theorem defect_kernel_bound {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |3*spectralKernel a b c-spectralTau a c*spectralTau c b/3| ≤ 2 := by
  have hk := spectralKernel_bounds ha hb hc
  have ht := spectralTau_bounds ha hc
  have hu := spectralTau_bounds hc hb
  have hv : 0 ≤ spectralTau a c*spectralTau c b := mul_nonneg ht.1.le hu.1.le
  have hw : spectralTau a c*spectralTau c b ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul ht.2 hu.2 hu.1.le (by norm_num)
      _ = 1 := by ring
  apply abs_le.mpr
  constructor <;> nlinarith [hk.1, hk.2]

private theorem frob_entry_mono (M N : Matrix n n ℂ)
    (h : ∀ i j, ‖M i j‖ ≤ ‖N i j‖) : frob M ≤ frob N := by
  apply (sq_le_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
  rw [frob_sq_sum, frob_sq_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h i j)

private theorem quadraticDefect_norm {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) : frob (quadraticDefect p H) ≤ 2*frob H^2 := by
  let E : Matrix n n ℂ := fun i j => (‖H i j‖ : ℂ)
  have hE : frob E = frob H := by
    apply (sq_eq_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
    simp only [frob_sq_sum, E, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  have hentry (i j : n) : ‖quadraticDefect p H i j‖ ≤ ‖((2 : ℝ) • (E*E)) i j‖ := by
    have he : (E*E) i j = ((∑ k, ‖H i k‖*‖H k j‖ : ℝ) : ℂ) := by
      simp [E, Matrix.mul_apply]
    have hs : 0 ≤ ∑ k, ‖H i k‖*‖H k j‖ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    calc
      _ ≤ ∑ k, ‖((3*spectralKernel (p i) (p j) (p k)-
          spectralTau (p i) (p k)*spectralTau (p k) (p j)/3 : ℝ) : ℂ)*H i k*H k j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k, 2*(‖H i k‖*‖H k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hk := defect_kernel_bound (hp i) (hp j) (hp k)
        nlinarith [mul_le_mul_of_nonneg_right hk
          (mul_nonneg (norm_nonneg (H i k)) (norm_nonneg (H k j)))]
      _ = 2*∑ k, ‖H i k‖*‖H k j‖ := (Finset.mul_sum ..).symm
  calc
    _ ≤ frob ((2 : ℝ) • (E*E)) := frob_entry_mono _ _ hentry
    _ = 2*frob (E*E) := by change ‖(2 : ℝ) • (E*E)‖ = _; rw [norm_smul]; norm_num [frob]
    _ ≤ 2*(frob E*frob E) := mul_le_mul_of_nonneg_left (frob_mul E E) (by norm_num)
    _ = 2*frob H^2 := by rw [hE]; ring

end Defect

section DiagonalJets
open scoped Matrix.Norms.L2Operator

private def rootP (p : n → ℝ) : Matrix n n ℂ := diagonal (fun i => (p i : ℂ))
private def balanceP (p : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => (p i*Real.sqrt (p i) : ℂ))
private def pencilDirection (p : n → ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  balanceP p*X*balanceP p

private theorem rootP_posDef {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    (rootP p).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast hp i

private theorem rootP_cube_posDef {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    ((rootP p)^3).PosDef := by
  have hP := rootP_posDef hp
  rw [← CFC.rpow_natCast _ 3 hP.posSemidef.nonneg]
  exact (IsStrictlyPositive.rpow _ (3 : ℝ) hP.isStrictlyPositive).posDef

private theorem rootP_cubeRoot {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    CFC.rpow ((rootP p)^3) (1/3 : ℝ) = rootP p := by
  have hP := rootP_posDef hp
  simp only [CFC.rpow_eq_pow]
  rw [← CFC.rpow_natCast _ 3 hP.posSemidef.nonneg,
    CFC.rpow_rpow _ _ _ (by norm_num) hP.isStrictlyPositive]
  norm_num [CFC.rpow_one _ hP.posSemidef.nonneg]

private theorem pencilDirection_hermitian (p : n → ℝ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (pencilDirection p X).IsHermitian := by
  have hv : (balanceP p)ᴴ = balanceP p := by
    simp [balanceP, Matrix.diagonal_conjTranspose]
  change (balanceP p*X*balanceP p)ᴴ = balanceP p*X*balanceP p
  simp only [Matrix.conjTranspose_mul, hv, hX.eq, mul_assoc]

private theorem cubicLinear_diagonal_entry (p : n → ℝ) (C : Matrix n n ℂ) (i j : n) :
    RpowPencilTaylor.cubicLinear (rootP p) C i j =
      (spectralDen (p i) (p j) : ℂ)*C i j := by
  exact RpowPencilTaylor.cubicLinear_coordinates_entry
    (StarAlgEquiv.refl ℂ (Matrix n n ℂ)) (rootP p) C p rfl i j

private theorem first_root_entry {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (X C : Matrix n n ℂ)
    (hC : RpowPencilTaylor.cubicLinear (rootP p) C = pencilDirection p X)
    (i j : n) :
    C i j = ((p i*Real.sqrt (p i)*(p j*Real.sqrt (p j))/
      spectralDen (p i) (p j) : ℝ) : ℂ)*X i j := by
  have he := congrArg (fun M : Matrix n n ℂ => M i j) hC
  rw [cubicLinear_diagonal_entry] at he
  simp only [pencilDirection, balanceP, Matrix.diagonal_mul,
    Matrix.mul_diagonal] at he
  have hd : (spectralDen (p i) (p j) : ℂ) ≠ 0 := by
    exact_mod_cast (spectralDen_pos (hp i) (hp j)).ne'
  push_cast
  apply (mul_left_cancel₀ hd)
  rw [he]
  field_simp <;> ring

private theorem rootP_inverse {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    (rootP p)⁻¹ = diagonal (fun i => (p i : ℂ)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  simp only [rootP, Matrix.diagonal_mul_diagonal]
  convert (Matrix.diagonal_one : diagonal (1 : n → ℂ) = 1) using 1
  congr 1
  funext i
  exact mul_inv_cancel₀ (by exact_mod_cast (hp i).ne')

private theorem first_balanced_entry {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (X C : Matrix n n ℂ)
    (hC : RpowPencilTaylor.cubicLinear (rootP p) C = pencilDirection p X)
    (i j : n) :
    ((rootP p)⁻¹*(rootP p*C+C*rootP p)*(rootP p)⁻¹) i j =
      ((2/3 : ℝ) : ℂ)*schurFirst p X i j := by
  rw [rootP_inverse hp]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, rootP, first_root_entry hp X C hC, schurFirst]
  have hi : (p i : ℂ) ≠ 0 := by exact_mod_cast (hp i).ne'
  have hj : (p j : ℂ) ≠ 0 := by exact_mod_cast (hp j).ne'
  have hd : (spectralDen (p i) (p j) : ℂ) ≠ 0 := by
    exact_mod_cast (spectralDen_pos (hp i) (hp j)).ne'
  unfold spectralTau
  rw [Real.sqrt_mul (hp i).le]
  push_cast
  field_simp <;> ring

private theorem second_root_entry (p : n → ℝ) (C E : Matrix n n ℂ)
    (hE : RpowPencilTaylor.cubicLinear (rootP p) E =
      -(rootP p*C*C+C*rootP p*C+C*C*rootP p)) (i j : n) :
    (spectralDen (p i) (p j) : ℂ)*E i j =
      -∑ k, ((p i+p k+p j : ℝ) : ℂ)*C i k*C k j := by
  have he := congrArg (fun M : Matrix n n ℂ => M i j) hE
  rw [cubicLinear_diagonal_entry] at he
  rw [he]
  have ha : (rootP p*C*C) i j = ∑ k, (p i : ℂ)*C i k*C k j := by
    rw [Matrix.mul_apply]
    simp only [rootP, Matrix.diagonal_mul]
  have hb : (C*rootP p*C) i j = ∑ k, C i k*(p k : ℂ)*C k j := by
    rw [Matrix.mul_apply]
    simp only [rootP, Matrix.mul_diagonal]
  have hc : (C*C*rootP p) i j = ∑ k, C i k*C k j*(p j : ℂ) := by
    change (C*C*diagonal (fun i => (p i : ℂ))) i j = _
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
  simp only [Matrix.neg_apply, Matrix.add_apply, ha, hb, hc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem second_kernel_algebra {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1/(a*b))*(1-(a+b)*(a+b+c)/spectralDen a b)*
      (a*Real.sqrt a*(c*Real.sqrt c)/spectralDen a c)*
      (c*Real.sqrt c*(b*Real.sqrt b)/spectralDen c b) =
        -spectralKernel a b c := by
  have hd := (spectralDen_pos ha hb).ne'
  have he := (spectralDen_pos ha hc).ne'
  have hf := (spectralDen_pos hc hb).ne'
  have hs := Real.sq_sqrt hc.le
  unfold spectralKernel
  rw [Real.sqrt_mul ha.le]
  field_simp
  unfold spectralDen
  ring_nf
  rw [hs]
  ring

private theorem second_balanced_entry {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (X C E : Matrix n n ℂ)
    (hC : RpowPencilTaylor.cubicLinear (rootP p) C = pencilDirection p X)
    (hE : RpowPencilTaylor.cubicLinear (rootP p) E =
      -(rootP p*C*C+C*rootP p*C+C*C*rootP p)) (i j : n) :
    ((rootP p)⁻¹*(rootP p*E+C*C+E*rootP p)*(rootP p)⁻¹) i j =
      -∑ k, (spectralKernel (p i) (p j) (p k) : ℂ)*X i k*X k j := by
  have hd : (spectralDen (p i) (p j) : ℂ) ≠ 0 := by
    exact_mod_cast (spectralDen_pos (hp i) (hp j)).ne'
  have he : E i j = (-∑ k, ((p i+p k+p j : ℝ) : ℂ)*C i k*C k j)/
      (spectralDen (p i) (p j) : ℂ) := by
    apply (eq_div_iff hd).mpr
    rw [mul_comm]
    exact second_root_entry p C E hE i j
  rw [rootP_inverse hp]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply]
  simp only [rootP, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.mul_apply, he]
  simp only [Finset.sum_div, ← Finset.sum_neg_distrib, mul_add, add_mul,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [first_root_entry hp X C hC i k, first_root_entry hp X C hC k j]
  have hk := congrArg (fun x : ℝ => (x : ℂ))
    (second_kernel_algebra (hp i) (hp j) (hp k))
  push_cast at hk ⊢
  linear_combination (X i k*X k j)*hk

private def secondSchur (p : n → ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => -∑ k, (spectralKernel (p i) (p j) (p k) : ℂ)*X i k*X k j

private def actualCoeff (p : n → ℝ) (X : Matrix n n ℂ) : ℕ → Matrix n n ℂ :=
  RpowPencilTaylor.jetCoeff (fun t : ℝ =>
    (rootP p)⁻¹*CFC.rpow ((rootP p)^3+t • pencilDirection p X) (2/3 : ℝ)*(rootP p)⁻¹)

private theorem actual_first_second {p : n → ℝ} (hp : ∀ i, 0 < p i)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    actualCoeff p X 1 = (2/3 : ℝ) • schurFirst p X ∧
      actualCoeff p X 2 = secondSchur p X := by
  let Y := (rootP p)^3
  let K := pencilDirection p X
  let C := RpowPencilTaylor.jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
  have hY : Y.PosDef := rootP_cube_posDef hp
  have hK : K.IsHermitian := pencilDirection_hermitian p hX
  have hp₀ : CFC.rpow Y (1/3 : ℝ) = rootP p := rootP_cubeRoot hp
  have hc := RpowPencilTaylor.cubeRoot_jet_recurrences hY hK
  change C 0 = _ ∧ _ at hc
  rw [hp₀] at hc
  have hj₁ := RpowPencilTaylor.normalized_twoThirds_jet hY hK 1 (by omega)
  have hj₂ := RpowPencilTaylor.normalized_twoThirds_jet hY hK 2 (by omega)
  change RpowPencilTaylor.jetCoeff _ 1 = (CFC.rpow Y (1/3 : ℝ))⁻¹*
    (∑ a ∈ Finset.range (1+1), C a*C (1-a))*(CFC.rpow Y (1/3 : ℝ))⁻¹ at hj₁
  change RpowPencilTaylor.jetCoeff _ 2 = (CFC.rpow Y (1/3 : ℝ))⁻¹*
    (∑ a ∈ Finset.range (2+1), C a*C (2-a))*(CFC.rpow Y (1/3 : ℝ))⁻¹ at hj₂
  simp only [hp₀, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    Nat.reduceSub, hc.1, zero_add] at hj₁ hj₂
  change actualCoeff p X 1 = _ at hj₁
  change actualCoeff p X 2 = _ at hj₂
  refine ⟨?_, ?_⟩
  · rw [hj₁]
    ext i j
    exact first_balanced_entry hp X (C 1) hc.2.1 i j
  · rw [hj₂]
    ext i j
    exact second_balanced_entry hp X (C 1) (C 2) hc.2.1 hc.2.2.1 i j

private theorem spectralTau_self {a : ℝ} (ha : 0 < a) : spectralTau a a = 1 := by
  unfold spectralTau spectralDen
  rw [Real.sqrt_mul_self ha.le]
  field_simp
  ring

private theorem spectralKernel_self {a : ℝ} (ha : 0 < a) :
    spectralKernel a a a = 1/9 := by
  unfold spectralKernel spectralDen
  rw [Real.sqrt_mul_self ha.le]
  field_simp
  ring

private theorem spectralKernel_radial {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    spectralKernel a b a+spectralKernel a b b = (2/9)*spectralTau a b := by
  have hd := (spectralDen_pos ha hb).ne'
  unfold spectralKernel spectralTau spectralDen at *
  field_simp
  ring

private theorem schurFirst_radial {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) : schurFirst p (1+H) = 1+schurFirst p H := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [schurFirst, spectralTau_self (hp i)]
  · simp [schurFirst, Matrix.one_apply, hij]

private theorem secondSchur_radial {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) :
    secondSchur p (1+H) = -(1/9 : ℝ) • (1 : Matrix n n ℂ)-
      (2/9 : ℝ) • schurFirst p H+secondSchur p H := by
  ext i j
  simp only [secondSchur, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
    Matrix.smul_apply, schurFirst, mul_add, add_mul, Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, spectralKernel_self (hp i),
      spectralTau_self (hp i)]
    simp only [Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  · simp only [hij, ite_false, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hk := congrArg (fun x : ℝ => (x : ℂ)) (spectralKernel_radial (hp i) (hp j))
    simp only [Complex.real_smul, smul_eq_mul, mul_zero, zero_sub]
    push_cast at hk ⊢
    linear_combination -H i j*hk

private theorem quadraticDefect_eq (p : n → ℝ) (H : Matrix n n ℂ) :
    quadraticDefect p H = -(3 : ℝ) • secondSchur p H-
      (1/3 : ℝ) • (schurFirst p H*schurFirst p H) := by
  ext i j
  change (∑ k, ((3*spectralKernel (p i) (p j) (p k)-
      spectralTau (p i) (p k)*spectralTau (p k) (p j)/3 : ℝ) : ℂ)*H i k*H k j) =
    -(3 : ℝ) • (-∑ k, (spectralKernel (p i) (p j) (p k) : ℂ)*H i k*H k j)-
      (1/3 : ℝ) • (∑ k, ((spectralTau (p i) (p k) : ℂ)*H i k)*
        ((spectralTau (p k) (p j) : ℂ)*H k j))
  simp only [Complex.real_smul, smul_eq_mul, neg_mul, mul_neg, neg_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem balanceP_posDef {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    (balanceP p).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast mul_pos (hp i) (Real.sqrt_pos.mpr (hp i))

private theorem balanceP_square {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    balanceP p*balanceP p = (rootP p)^3 := by
  simp only [balanceP, rootP, Matrix.diagonal_mul_diagonal, Matrix.diagonal_pow]
  congr 1
  funext i
  change (p i*Real.sqrt (p i) : ℂ)*(p i*Real.sqrt (p i) : ℂ) = (p i : ℂ)^3
  have hs : ((Real.sqrt (p i) : ℝ) : ℂ)^2 = (p i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hp i).le
  ring_nf
  rw [hs]
  ring

private theorem balanceP_rpow {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    balanceP p = CFC.rpow (rootP p) (3/2 : ℝ) := by
  have hP := rootP_posDef hp
  calc
    balanceP p = CFC.sqrt ((rootP p)^3) :=
      (CFC.sqrt_unique (balanceP_square hp) (balanceP_posDef hp).posSemidef.nonneg).symm
    _ = CFC.rpow (rootP p) (3/2 : ℝ) := by
      simp only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow]
      rw [← CFC.rpow_natCast _ 3 hP.posSemidef.nonneg,
        CFC.rpow_rpow _ _ _ (by norm_num) hP.isStrictlyPositive]
      norm_num

private theorem balanced_trace_normalization {p : n → ℝ} (hp : ∀ i, 0 < p i)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    tr (actualCoeff p X 2)-tr (actualCoeff p X 1*actualCoeff p X 1)/2 = -tr (X^2)/3 ∧
      tr (actualCoeff p X 3)-tr (actualCoeff p X 1*actualCoeff p X 2)+
        tr (actualCoeff p X 1*actualCoeff p X 1*actualCoeff p X 1)/3 = 2*tr (X^3)/9 := by
  let P := rootP p
  let V := balanceP p
  let u := (rootP_posDef hp).isUnit.unit
  let v := (balanceP_posDef hp).isUnit.unit
  have hu : u.val = P := (rootP_posDef hp).isUnit.unit_spec
  have hv : v.val = V := (balanceP_posDef hp).isUnit.unit_spec
  have hd : P⁻¹ = u.inv := Matrix.inv_eq_right_inv (by rw [← hu]; exact u.val_inv)
  have hvd : V⁻¹ = v.inv := Matrix.inv_eq_right_inv (by rw [← hv]; exact v.val_inv)
  have hpp : P^3*(P⁻¹)^3 = 1 := by
    rw [hd, ← hu]
    simp [Units.inv_eq_val_inv, pow_succ, mul_assoc]
  have hvp : V*(P⁻¹)^3 = v.inv := by
    have hh : V*(V*(P⁻¹)^3) = 1 := by
      rw [← mul_assoc, balanceP_square hp, hpp]
    exact (Matrix.inv_eq_right_inv hh).symm.trans hvd
  let Q := pencilDirection p X*(P⁻¹)^3
  have hq : Q = v.val*X*v.inv := by
    change V*X*V*(P⁻¹)^3 = _
    rw [mul_assoc, hvp, hv]
  have hq₂ : tr (Q^2) = tr (X^2) := by
    rw [hq]
    rw [show (v.val*X*v.inv)^2 = v.val*(X^2)*v.inv by
      simp [Units.inv_eq_val_inv, pow_two, mul_assoc]]
    rw [tr_cycle]
    simp [Units.inv_eq_val_inv, mul_assoc, tr]
  have hq₃ : tr (Q^3) = tr (X^3) := by
    rw [hq]
    rw [show (v.val*X*v.inv)^3 = v.val*(X^3)*v.inv by
      simp [Units.inv_eq_val_inv, pow_succ, mul_assoc]]
    rw [tr_cycle]
    simp [Units.inv_eq_val_inv, mul_assoc, tr]
  have ht := actual_trace_normalization (rootP_cube_posDef hp) (pencilDirection_hermitian p hX)
  simp only [rootP_cubeRoot hp] at ht
  change _ = -tr (Q^2)/3 ∧ _ = 2*tr (Q^3)/9 at ht
  simpa only [actualCoeff, hq₂, hq₃] using ht

/-- Ordered trace completion of the all-Z quadratic; this is finite matrix
algebra and does not construct a Sylvester inverse. -/
private theorem allZ_polynomial (T D Z E : Matrix n n ℂ) (x : ℂ)
    (h : let C := (2/3 : ℝ) • T
         let B := -(1/9 : ℝ) • (T*T)-(1/3 : ℝ) • D
         tr E-tr (C*B)+tr (C*C*C)/3 = 2*x/9) :
    let C := (2/3 : ℝ) • T
    let B := -(1/9 : ℝ) • (T*T)-(1/3 : ℝ) • D
    let R := Z-(1/6 : ℝ) • T
    18*(tr E+2*tr (Z*B)+tr (C*Z*Z)-(5/48 : ℂ)*tr (C*C*C)) =
      4*x-4*tr (T*T*T)-6*tr (T*D)+12*(tr (T*R*R)-tr (D*R)) := by
  dsimp only at h ⊢
  simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, tr, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.real_smul, smul_eq_mul, ← mul_assoc] at h ⊢
  have ha := tr_cycle T Z T
  have hb := tr_cycle Z T T
  have hc := tr_cycle Z T Z
  have hd := tr_comm D T
  have he := tr_comm D Z
  dsimp only [tr] at ha hb hc hd he
  rw [ha, hb, hd, he]
  norm_num at h ⊢
  linear_combination (18 : ℂ)*h

private theorem radial_trace_reduction (H A D : Matrix n n ℂ)
    (hlin : tr H = tr A) (hD : tr D = tr (H*H)-tr (A*A)) :
    4*tr ((1+H)^3)-4*tr ((1+A)^3)-6*tr ((1+A)*D) =
      6*(tr (H*H)-tr (A*A))+4*tr (H^3)-4*tr (A^3)-6*tr (A*D) := by
  simp only [tr] at hlin hD ⊢
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_add, add_mul,
    Matrix.trace_add, ← mul_assoc]
  rw [hlin, hD]
  ring

private theorem radial_coefficients {p : n → ℝ} (hp : ∀ i, 0 < p i)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    let A := schurFirst p H
    let D := quadraticDefect p H
    let T := (1 : Matrix n n ℂ)+A
    actualCoeff p (1+H) 1 = (2/3 : ℝ) • T ∧
      actualCoeff p (1+H) 2 = -(1/9 : ℝ) • (T*T)-(1/3 : ℝ) • D ∧
        tr D = tr (H*H)-tr (A*A) := by
  let A := schurFirst p H
  let D := quadraticDefect p H
  let T := (1 : Matrix n n ℂ)+A
  have hs : ((1 : Matrix n n ℂ)+H).IsHermitian := Matrix.isHermitian_one.add hH
  have hc := actual_first_second hp hs
  have hc₁ : actualCoeff p (1+H) 1 = (2/3 : ℝ) • T := by
    rw [hc.1, schurFirst_radial hp]
  have hc₂ : actualCoeff p (1+H) 2 = -(1/9 : ℝ) • (T*T)-(1/3 : ℝ) • D := by
    rw [hc.2, secondSchur_radial hp]
    dsimp only [T, D, A]
    rw [quadraticDefect_eq]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_sub, smul_add, smul_smul]
    module
  have hlin : tr A = tr H := by
    simp [A, schurFirst, tr, Matrix.trace, Matrix.diag, spectralTau_self (hp _)]
  have ht := (balanced_trace_normalization hp hs).1
  rw [hc₁, hc₂] at ht
  change _ ∧ _ ∧ _
  refine ⟨hc₁, hc₂, ?_⟩
  dsimp only [T] at ht
  simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_add, add_mul,
    one_mul, mul_one, tr, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.real_smul, smul_eq_mul] at ht
  dsimp only [tr] at hlin ⊢
  rw [hlin] at ht
  norm_num at ht
  linear_combination -(3 : ℂ)*ht

private theorem actual_local_supplier {d : ℕ} {p : Fin d → ℝ}
    (hp : ∀ i, 0 < p i) (hlevels : ∃ i j, p i ≠ p j)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (hsupport : ∀ i j, p i = p j → H i j = 0)
    (hradius : frob H ≤ 3 * crossGap p hlevels / 32)
    {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.IsHermitian) :
    crossGap p hlevels * frob H ^ 2 / 6 ≤
      (tr (actualCoeff p (1 + H) 3 +
        (2 : ℝ) • (Z * actualCoeff p (1 + H) 2) +
        actualCoeff p (1 + H) 1 * Z ^ 2 -
        (5 / 48 : ℝ) • (actualCoeff p (1 + H) 1) ^ 3)).re := by
  let r := frob H
  let δ := crossGap p hlevels
  let A := schurFirst p H
  let D := quadraticDefect p H
  let T := (1 : Matrix (Fin d) (Fin d) ℂ) + A
  let R := Z - (1 / 6 : ℝ) • T
  have hr : 0 ≤ r := frob_nonneg H
  have hsmall : 32 * r ≤ 3 * δ := by dsimp [r, δ]; linarith
  have hrhalf : r ≤ 1 / 2 := by
    have := crossGap_le_one (p := p) hlevels
    dsimp [r, δ] at *
    linarith
  have hA : frob A ≤ r := schurFirst_norm hp H
  have hD : frob D ≤ 2 * r ^ 2 := quadraticDefect_norm hp H
  have hAh : A.IsHermitian := schurFirst_hermitian p hH
  have hTh : T.IsHermitian := Matrix.isHermitian_one.add hAh
  have hRh : R.IsHermitian :=
    hZ.sub (hTh.smul (IsSelfAdjoint.of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)))
  have hg : δ * r ^ 2 ≤ (tr (H * H) - tr (A * A)).re := by
    simpa only [Complex.sub_re, tr, frob_sq_hermitian hH,
      frob_sq_hermitian hAh] using schurFirst_gap hp hlevels H hsupport
  have hh : -20 * r ^ 3 ≤ (4 * tr (H ^ 3) - 4 * tr (A ^ 3) - 6 * tr (A * D)).re := by
    have hcH := abs_reTrace_cube H
    have hcA := (abs_reTrace_cube A).trans (pow_le_pow_left₀ (frob_nonneg A) hA 3)
    have hcD : |(A * D).trace.re| ≤ 2 * r ^ 3 := by
      calc
        _ ≤ frob A * frob D := abs_reTrace_mul A D
        _ ≤ r * (2 * r ^ 2) := mul_le_mul hA hD (frob_nonneg D) hr
        _ = 2 * r ^ 3 := by ring
    norm_num [tr, Complex.sub_re, Complex.mul_re]
    have h₁ := (abs_le.mp hcH).1
    have h₂ := (abs_le.mp hcA).2
    have h₃ := (abs_le.mp hcD).2
    dsimp only [r] at *
    linarith
  have he := quadratic_remainder_bound A D R hRh r hr hrhalf hA hD
  have hs : ((1 : Matrix (Fin d) (Fin d) ℂ) + H).IsHermitian :=
    Matrix.isHermitian_one.add hH
  obtain ⟨hc₁, hc₂, htraceD⟩ := radial_coefficients hp hH
  have ht := (balanced_trace_normalization hp hs).2
  rw [hc₁, hc₂] at ht
  have hpoly := allZ_polynomial T D Z (actualCoeff p (1 + H) 3)
    (tr ((1 + H) ^ 3)) ht
  have hlin : tr H = tr A := by
    simp [A, schurFirst, tr, Matrix.trace, Matrix.diag, spectralTau_self (hp _)]
  have hrad := radial_trace_reduction H A D hlin htraceD
  have hid :
      18 * (tr (actualCoeff p (1 + H) 3 +
        (2 : ℝ) • (Z * actualCoeff p (1 + H) 2) +
        actualCoeff p (1 + H) 1 * Z ^ 2 -
        (5 / 48 : ℝ) • (actualCoeff p (1 + H) 1) ^ 3)) =
      6 * (tr (H * H) - tr (A * A)) +
        (4 * tr (H ^ 3) - 4 * tr (A ^ 3) - 6 * tr (A * D)) +
        12 * (tr (T * R * R) - tr (D * R)) := by
    rw [hc₁, hc₂]
    dsimp only at hpoly
    simp only [tr, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul, smul_eq_mul, pow_succ, pow_zero, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← mul_assoc] at hpoly ⊢
    simp only [tr, pow_succ, pow_zero, mul_one, one_mul] at hrad
    dsimp only [T, R, A, D] at hpoly hrad ⊢
    norm_num at hpoly ⊢
    linear_combination hpoly + hrad
  have hidre := congrArg Complex.re hid
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr] at hidre
  have hmargin := local_scalar_margin δ r
    (tr (H * H) - tr (A * A)).re
    (4 * tr (H ^ 3) - 4 * tr (A ^ 3) - 6 * tr (A * D)).re
    (12 * (tr (T * R * R) - tr (D * R))).re hr hrhalf hsmall hg hh
    (by simpa [Complex.mul_re, Complex.sub_re, tr, T] using he)
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr] at hmargin
  change δ * r ^ 2 / 6 ≤ _
  norm_num [tr, Complex.add_re, Complex.sub_re, Complex.mul_re]
  linarith

/-- Quantitative local all-Z supplier for actual factorial CFC derivatives at
an arbitrary finite positive diagonal spectrum. Equal-level blocks of H vanish;
the spectrum may have repeated levels, and H = 0 is included. -/
theorem finite_spectrum_local_supplier {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (hlevels : ∃ i j, p i ≠ p j)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (hsupport : ∀ i j, p i = p j → H i j = 0)
    (hradius : frob H ≤ 3 * crossGap p hlevels / 32)
    (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Z.IsHermitian) :
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ) + H
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P ^ 3 + t • (CFC.rpow P (3 / 2 : ℝ) * S *
        CFC.rpow P (3 / 2 : ℝ))) (2 / 3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 < crossGap p hlevels ∧ crossGap p hlevels * frob H ^ 2 / 6 ≤
      (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
        (5 / 48 : ℝ) • (B 1) ^ 3).trace.re := by
  dsimp only
  refine ⟨crossGap_pos hp hlevels, ?_⟩
  simpa only [actualCoeff, RpowPencilTaylor.jetCoeff, pencilDirection,
    balanceP_rpow hp, rootP, tr] using
      actual_local_supplier hp hlevels hH hsupport hradius hZ

#print axioms finite_spectrum_local_supplier

end DiagonalJets

section Uniform

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem spectralDen_comm (a b : ℝ) : spectralDen a b = spectralDen b a := by
  unfold spectralDen; ring

private theorem spectralTau_comm (a b : ℝ) : spectralTau a b = spectralTau b a := by
  unfold spectralTau
  rw [mul_comm a b, add_comm a b, spectralDen_comm a b]

private def spectralRho (a b : ℝ) : ℝ := Real.sqrt (1-spectralTau a b^2)

private theorem spectralRho_nonneg (a b : ℝ) : 0 ≤ spectralRho a b :=
  Real.sqrt_nonneg _

private theorem spectralRho_comm (a b : ℝ) : spectralRho a b = spectralRho b a := by
  unfold spectralRho; rw [spectralTau_comm a b]

private theorem spectralRho_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    spectralRho a b^2 = 1-spectralTau a b^2 := by
  have ht := spectralTau_bounds ha hb
  exact Real.sq_sqrt (by nlinarith [ht.1, ht.2])

private def gramPolynomial (a b c : ℝ) : ℝ :=
  4*a^4*b^2+7*a^4*b*c+4*a^4*c^2+7*a^3*b^3+26*a^3*b^2*c+
  26*a^3*b*c^2+7*a^3*c^3+4*a^2*b^4+26*a^2*b^3*c+48*a^2*b^2*c^2+
  26*a^2*b*c^3+4*a^2*c^4+7*a*b^4*c+26*a*b^3*c^2+26*a*b^2*c^3+
  7*a*b*c^4+4*b^4*c^2+7*b^3*c^3+4*b^2*c^4

private theorem spectralTau_gram {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ 1-spectralTau a b^2-spectralTau b c^2-spectralTau a c^2+
      2*spectralTau a b*spectralTau b c*spectralTau a c := by
  have hd := (spectralDen_pos ha hb).ne'
  have he := (spectralDen_pos hb hc).ne'
  have hf := (spectralDen_pos ha hc).ne'
  have hs₁ := Real.sq_sqrt ha.le
  have hs₂ := Real.sq_sqrt hb.le
  have hs₃ := Real.sq_sqrt hc.le
  have hid : 1-spectralTau a b^2-spectralTau b c^2-spectralTau a c^2+
      2*spectralTau a b*spectralTau b c*spectralTau a c =
      (a-b)^2*(a-c)^2*(b-c)^2*gramPolynomial a b c /
        (4*(spectralDen a b)^2*(spectralDen a c)^2*(spectralDen b c)^2) := by
    unfold spectralTau
    rw [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul ha.le]
    field_simp
    ring_nf
    rw [hs₁, hs₂, hs₃]
    unfold spectralDen gramPolynomial
    ring
  rw [hid]
  unfold gramPolynomial
  positivity

private theorem spectralRho_triangle {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    spectralRho a c ≤ spectralRho a b+spectralRho b c := by
  let u := spectralTau a b
  let v := spectralTau b c
  let w := spectralTau a c
  let x := spectralRho a b
  let y := spectralRho b c
  let z := spectralRho a c
  have hu := spectralTau_bounds ha hb
  have hv := spectralTau_bounds hb hc
  have hw := spectralTau_bounds ha hc
  have hx : 0 ≤ x := spectralRho_nonneg _ _
  have hy : 0 ≤ y := spectralRho_nonneg _ _
  have hz : 0 ≤ z := spectralRho_nonneg _ _
  have hx₂ : x^2 = 1-u^2 := spectralRho_sq ha hb
  have hy₂ : y^2 = 1-v^2 := spectralRho_sq hb hc
  have hz₂ : z^2 = 1-w^2 := spectralRho_sq ha hc
  have hg := spectralTau_gram ha hb hc
  change 0 ≤ 1-u^2-v^2-w^2+2*u*v*w at hg
  change z ≤ x+y
  have hxy : 0 ≤ x*y := mul_nonneg hx hy
  by_cases h : u^2+v^2 ≤ 1
  · nlinarith [sq_nonneg w]
  · have huv : x*y ≤ u*v := by
      have hid : (u*v)^2-(x*y)^2 = u^2+v^2-1 := by rw [mul_pow, mul_pow, hx₂, hy₂]; ring
      have hp : 0 ≤ u*v := mul_nonneg hu.1.le hv.1.le
      nlinarith
    have hsq : (w-u*v)^2 ≤ (x*y)^2 := by rw [mul_pow, hx₂, hy₂]; nlinarith only [hg]
    have hwlow : u*v-x*y ≤ w := by nlinarith
    have hlow : 0 ≤ u*v-x*y := sub_nonneg.mpr huv
    have hbound : (u*v-x*y)^2 ≤ w^2 :=
      (sq_le_sq₀ hlow hw.1.le).mpr hwlow
    have hid : 1-(u*v-x*y)^2 = (u*y+v*x)^2 := by
      nlinarith only [hx₂, hy₂, mul_nonneg (sq_nonneg u) (sq_nonneg v),
        show (u*v-x*y)^2+(u*y+v*x)^2 = 1 by
          calc
            _ = (u^2+x^2)*(v^2+y^2) := by ring
            _ = 1 := by rw [hx₂, hy₂]; ring]
    have hnonneg : 0 ≤ u*y+v*x := add_nonneg (mul_nonneg hu.1.le hy) (mul_nonneg hv.1.le hx)
    have hzbound : z ≤ u*y+v*x := by nlinarith only [hz₂, hbound, hid, hz, hnonneg]
    have hu' : u*y ≤ y := by nlinarith [mul_le_mul_of_nonneg_right hu.2 hy]
    have hv' : v*x ≤ x := by nlinarith [mul_le_mul_of_nonneg_right hv.2 hx]
    linarith

private def cyclicPolynomial (a b c : ℝ) : ℝ :=
  a^2*b^2*(a+b)*(4*a^2+5*a*b+4*b^2)+
  a*b*c*(4*(a^4+b^4)+4*a*b*(a^2+b^2)+2*a^2*b^2)+
  14*a*b*c^2*(a+b)*spectralDen a b+a^2*b^2*c^3+3*(a^3+b^3)*c^4

private def cyclicResidual (a b c : ℝ) : ℝ :=
  let U := a^2+b^2
  let V := a*b
  let s := a+b
  let R := 4*U+7*V
  R*V^4+4*V^4*s*c+V^2*(4*U^2+29*U*V+40*V^2)*c^2+
  2*V*s*U*(4*U+V)*c^3+(4*U^3+23*U^2*V+56*U*V^2+47*V^3)*c^4+
  2*s*(4*U^2+12*U*V+17*V^2)*c^5+R*(3*U+4*V)*c^6+2*R*s*c^7+R*c^8

private theorem cyclicResidual_identity (a b c : ℝ) :
    (4*a^2+7*a*b+4*b^2)*(spectralDen a c)^2*(spectralDen b c)^2-
      2*a*b*c*cyclicPolynomial a b c = cyclicResidual a b c := by
  unfold cyclicResidual cyclicPolynomial spectralDen
  ring

private def cyclicGamma (a b c : ℝ) : ℝ :=
  spectralTau a b*spectralKernel a b c+
  spectralTau b c*spectralKernel b c a+
  spectralTau c a*spectralKernel c a b-
  spectralTau a b*spectralTau b c*spectralTau c a/3

private theorem cyclicGamma_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ cyclicGamma a b c ∧ cyclicGamma a b c ≤
      (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2) := by
  have hd := (spectralDen_pos ha hb).ne'
  have he := (spectralDen_pos hb hc).ne'
  have hf := (spectralDen_pos hc ha).ne'
  have hd' := (spectralDen_pos hb ha).ne'
  have he' := (spectralDen_pos hc hb).ne'
  have hf' := (spectralDen_pos ha hc).ne'
  have hs₁ := Real.sq_sqrt ha.le
  have hs₂ := Real.sq_sqrt hb.le
  have hs₃ := Real.sq_sqrt hc.le
  let Π := spectralDen a b*spectralDen b c*spectralDen c a
  have hΠ : 0 < Π := mul_pos (mul_pos (spectralDen_pos ha hb) (spectralDen_pos hb hc))
    (spectralDen_pos hc ha)
  have hformula : cyclicGamma a b c = 3*a*b*c/(8*Π^2)*
      ((a-b)^2*cyclicPolynomial a b c+(b-c)^2*cyclicPolynomial b c a+
        (c-a)^2*cyclicPolynomial c a b) := by
    unfold cyclicGamma spectralTau spectralKernel Π
    simp only [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul hc.le]
    field_simp
    ring_nf
    rw [hs₁, hs₂, hs₃]
    unfold spectralDen cyclicPolynomial
    ring
  have hres : (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2)-
      cyclicGamma a b c = 3/(16*Π^2)*
      ((a-b)^2*cyclicResidual a b c+(b-c)^2*cyclicResidual b c a+
        (c-a)^2*cyclicResidual c a b) := by
    rw [spectralRho_sq ha hb, spectralRho_sq hb hc, spectralRho_sq hc ha,
      spectralTau_gap ha hb, spectralTau_gap hb hc, spectralTau_gap hc ha, hformula]
    rw [← cyclicResidual_identity, ← cyclicResidual_identity, ← cyclicResidual_identity]
    dsimp only [Π]
    field_simp
    unfold spectralDen
    ring
  constructor
  · rw [hformula]
    unfold cyclicPolynomial spectralDen
    positivity
  · have hnonneg : 0 ≤ (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2)-
        cyclicGamma a b c := by
      rw [hres]
      unfold cyclicResidual
      positivity
    linarith

private theorem spectralRho_distance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a-b| ≤ spectralRho a b*(a+b) := by
  have hd : 0 < 4*(spectralDen a b)^2 := by have := spectralDen_pos ha hb; positivity
  have hgap := spectralRho_sq ha hb
  rw [spectralTau_gap ha hb] at hgap
  have hm := (eq_div_iff hd.ne').mp hgap
  have hp : 0 ≤ (a-b)^2*((a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2) := by
    rw [show (a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2 =
      a*b*(7*a^2+10*a*b+7*b^2) by unfold spectralDen; ring]
    positivity
  have hid : (spectralRho a b^2*(a+b)^2-(a-b)^2)*(4*(spectralDen a b)^2) =
      (a-b)^2*((a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2) := by
    linear_combination (a+b)^2*hm
  have hs : (a-b)^2 ≤ spectralRho a b^2*(a+b)^2 := by nlinarith only [hp, hid, hd]
  have hn := mul_nonneg (spectralRho_nonneg a b) (add_pos ha hb).le
  nlinarith only [hs, hn, abs_nonneg (a-b), sq_abs (a-b)]

private def linearPolynomial (a b c : ℝ) : ℝ :=
  a^2*b+a*b^2/2+a^2*c+(7/2)*a*b*c+2*a*c^2+2*b*c^2

private theorem defect_kernel_uniform {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |3*spectralKernel a b c-spectralTau a c*spectralTau c b/3| ≤
      (16/9)*(spectralRho a c+spectralRho c b) := by
  let Π := spectralDen a b*spectralDen a c*spectralDen b c
  let W := (a+b)*(a+c)*(b+c)
  let f := 3*c*Real.sqrt (a*b)/(4*Π)
  have hd := spectralDen_pos ha hb
  have he := spectralDen_pos ha hc
  have hf := spectralDen_pos hb hc
  have hf' := spectralDen_pos hc hb
  have hΠ : 0 < Π := mul_pos (mul_pos hd he) hf
  have hW : 0 < W := mul_pos (mul_pos (add_pos ha hb) (add_pos ha hc)) (add_pos hb hc)
  have hfn : 0 ≤ f := by dsimp [f]; positivity
  have hpoly (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      0 ≤ linearPolynomial a b c ∧ linearPolynomial a b c ≤ 2*((a+b)*(a+c)*(b+c)) := by
    constructor
    · unfold linearPolynomial; positivity
    · have hp : 0 ≤ a^2*b+(3/2)*a*b^2+a^2*c+(1/2)*a*b*c+2*b^2*c := by positivity
      unfold linearPolynomial
      linarith only [hp, show 2*((a+b)*(a+c)*(b+c))-
        (a^2*b+a*b^2/2+a^2*c+(7/2)*a*b*c+2*a*c^2+2*b*c^2) =
        a^2*b+(3/2)*a*b^2+a^2*c+(1/2)*a*b*c+2*b^2*c by ring]
  have hB := hpoly a b c ha hb hc
  have hB' := hpoly b a c hb ha hc
  have hid : 3*spectralKernel a b c-spectralTau a c*spectralTau c b/3 =
      f*((c-a)*linearPolynomial a b c+(c-b)*linearPolynomial b a c) := by
    unfold spectralKernel spectralTau f Π
    rw [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le, Real.sqrt_mul ha.le]
    have hs := Real.sq_sqrt hc.le
    field_simp
    ring_nf
    rw [hs]
    unfold spectralDen linearPolynomial
    ring
  have hq (u v : ℝ) : (3/4)*(u+v)^2 ≤ spectralDen u v := by
    unfold spectralDen; nlinarith [sq_nonneg (u-v)]
  have hprod : (27/64)*W^2 ≤ Π := by
    have h := mul_le_mul (mul_le_mul (hq a b) (hq a c)
      (by positivity : 0 ≤ (3/4)*(a+c)^2) hd.le) (hq b c)
      (by positivity : 0 ≤ (3/4)*(b+c)^2) (mul_nonneg hd.le he.le)
    dsimp [W, Π]
    nlinarith only [h]
  have hsqrt : 2*Real.sqrt (a*b) ≤ a+b := by
    have hs := Real.sq_sqrt (mul_pos ha hb).le
    have hn := Real.sqrt_nonneg (a*b)
    nlinarith [sq_nonneg (a-b)]
  have hfW : f*(2*W)*(a+c) ≤ 16/9 ∧ f*(2*W)*(b+c) ≤ 16/9 := by
    have hf₁ : f*(2*W) ≤ (16/9)*(a+b)*c/W := by
      dsimp only [f]
      apply (div_le_iff₀ hW).mpr
      have hid : 3*c*Real.sqrt (a*b)/(4*Π)*(2*W)*W =
          (3/2)*c*Real.sqrt (a*b)*W^2/Π := by field_simp; ring
      rw [hid]
      apply (div_le_iff₀ hΠ).mpr
      have h₁ := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ (3/4)*c*W^2)
      have h₂ := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (16/9)*(a+b)*c)
      nlinarith only [h₁, h₂]
    constructor
    · have h := mul_le_mul_of_nonneg_right hf₁ (add_pos ha hc).le
      have hid : ((16/9)*(a+b)*c/W)*(a+c) = (16/9)*c/(b+c) := by dsimp [W]; field_simp; ring
      rw [hid] at h
      exact h.trans ((div_le_iff₀ (add_pos hb hc)).mpr (by linarith))
    · have h := mul_le_mul_of_nonneg_right hf₁ (add_pos hb hc).le
      have hid : ((16/9)*(a+b)*c/W)*(b+c) = (16/9)*c/(a+c) := by dsimp [W]; field_simp; ring
      rw [hid] at h
      exact h.trans ((div_le_iff₀ (add_pos ha hc)).mpr (by linarith))
  have hd₁ := spectralRho_distance ha hc
  have hd₂ := spectralRho_distance hb hc
  rw [hid, abs_mul, abs_of_nonneg hfn]
  calc
    _ ≤ f*(|c-a|*linearPolynomial a b c+|c-b|*linearPolynomial b a c) := by
      apply mul_le_mul_of_nonneg_left _ hfn
      simpa only [abs_mul, abs_of_nonneg hB.1, abs_of_nonneg hB'.1] using
        abs_add_le ((c-a)*linearPolynomial a b c) ((c-b)*linearPolynomial b a c)
    _ ≤ f*(2*W)*(|a-c|+|b-c|) := by
      rw [abs_sub_comm c a, abs_sub_comm c b]
      have hB'' : linearPolynomial b a c ≤ 2*W := by dsimp [W]; nlinarith only [hB'.2]
      have h₁ := mul_le_mul_of_nonneg_left hB.2 (abs_nonneg (a-c))
      have h₂ := mul_le_mul_of_nonneg_left hB'' (abs_nonneg (b-c))
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hfn]
    _ ≤ f*(2*W)*(spectralRho a c*(a+c)+spectralRho b c*(b+c)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd₁ hd₂) (mul_nonneg hfn (by positivity))
    _ ≤ (16/9)*(spectralRho a c+spectralRho c b) := by
      rw [spectralRho_comm c b]
      have h₁ := mul_le_mul_of_nonneg_right hfW.1 (spectralRho_nonneg a c)
      have h₂ := mul_le_mul_of_nonneg_right hfW.2 (spectralRho_nonneg b c)
      nlinarith only [h₁, h₂]


open scoped Matrix.Norms.Frobenius

private def modulusMatrix (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (‖H i j‖ : ℂ)

private def rhoMatrix (p : n → ℝ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (spectralRho (p i) (p j)*‖H i j‖ : ℝ)

private theorem modulusMatrix_frob (H : Matrix n n ℂ) : frob (modulusMatrix H) = frob H := by
  apply (sq_eq_sq₀ (frob_nonneg _) (frob_nonneg _)).mp
  simp only [frob_sq_sum, modulusMatrix, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem rhoMatrix_gap {p : n → ℝ} (hp : ∀ i, 0 < p i) (H : Matrix n n ℂ) :
    frob (rhoMatrix p H)^2 = frob H^2-frob (schurFirst p H)^2 := by
  simp only [frob_sq_sum, rhoMatrix, schurFirst, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (spectralRho_nonneg _ _) (norm_nonneg _)),
    sq_abs, mul_pow, spectralRho_sq (hp _) (hp _), ← Finset.sum_sub_distrib]
  congr 1
  funext i
  congr 1
  funext j
  ring

private theorem quadraticDefect_uniform {p : n → ℝ} (hp : ∀ i, 0 < p i)
    (H : Matrix n n ℂ) :
    frob (quadraticDefect p H)^2 ≤ (1024/81)*frob H^2*
      (frob H^2-frob (schurFirst p H)^2) := by
  let B := modulusMatrix H
  let W := rhoMatrix p H
  have hentry (i j : n) : ‖quadraticDefect p H i j‖ ≤
      ‖((16/9 : ℝ) • (W*B+B*W)) i j‖ := by
    have he : (W*B+B*W) i j = ((∑ k,
        (spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖ : ℝ) : ℂ) := by
      simp only [W, B, rhoMatrix, modulusMatrix, Matrix.add_apply, Matrix.mul_apply,
        ← Finset.sum_add_distrib, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hn : 0 ≤ ∑ k, (spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖ := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (mul_nonneg (add_nonneg (spectralRho_nonneg _ _) (spectralRho_nonneg _ _))
        (norm_nonneg _)) (norm_nonneg _)
    simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 16/9), he, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hn]
    calc
      _ ≤ ∑ k, ‖((3*spectralKernel (p i) (p j) (p k)-
          spectralTau (p i) (p k)*spectralTau (p k) (p j)/3 : ℝ) : ℂ)*H i k*H k j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k, (16/9)*((spectralRho (p i) (p k)+spectralRho (p k) (p j))*‖H i k‖*‖H k j‖) := by
        apply Finset.sum_le_sum
        intro k _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        nlinarith only [mul_le_mul_of_nonneg_right
          (defect_kernel_uniform (hp i) (hp j) (hp k))
          (mul_nonneg (norm_nonneg (H i k)) (norm_nonneg (H k j)))]
      _ = _ := by rw [Finset.mul_sum]
  have hnorm : frob (quadraticDefect p H) ≤ (32/9)*frob W*frob H := by
    calc
      _ ≤ frob ((16/9 : ℝ) • (W*B+B*W)) := frob_entry_mono _ _ hentry
      _ = (16/9)*frob (W*B+B*W) := by
        change ‖(16/9 : ℝ) • (W*B+B*W)‖ = _
        rw [norm_smul]; norm_num [frob]
      _ ≤ (16/9)*(frob (W*B)+frob (B*W)) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ (16/9)*(frob W*frob B+frob B*frob W) :=
        mul_le_mul_of_nonneg_left (add_le_add (frob_mul W B) (frob_mul B W)) (by norm_num)
      _ = _ := by rw [show frob B = frob H from modulusMatrix_frob H]; ring
  have hs := (sq_le_sq₀ (frob_nonneg (quadraticDefect p H))
    (by positivity : 0 ≤ (32/9)*frob W*frob H)).mpr hnorm
  have hg : frob W^2 = frob H^2-frob (schurFirst p H)^2 := rhoMatrix_gap hp H
  nlinarith only [hs, show ((32/9)*frob W*frob H)^2 =
    (1024/81)*frob H^2*frob W^2 by ring, hg]

private theorem sum_cycle {R : Type*} [AddCommMonoid R] (f : n → n → n → R) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f j k i := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private def phase (H : Matrix n n ℂ) (i j k : n) : ℂ := H i j*H j k*H k i

private theorem phase_sum_cycle (f : n → n → n → ℝ) (H : Matrix n n ℂ) :
    (∑ i, ∑ j, ∑ k, (f j k i : ℂ)*phase H i j k) =
      ∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k := by
  rw [sum_cycle]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  dsimp [phase]
  ring

private theorem trace_cube_sum (M : Matrix n n ℂ) :
    tr (M^3) = ∑ i, ∑ j, ∑ k, phase M i j k := by
  simp only [tr, pow_succ, pow_zero, mul_one, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rfl

private theorem spectralKernel_comm (a b c : ℝ) : spectralKernel a b c = spectralKernel b a c := by
  unfold spectralKernel
  rw [mul_comm a b, add_comm a b, spectralDen_comm b a,
    spectralDen_comm b c, spectralDen_comm c a]
  ring

private theorem trace_defect_cycle (p : n → ℝ) (H : Matrix n n ℂ) :
    tr (schurFirst p H*quadraticDefect p H) =
      ∑ i, ∑ j, ∑ k, (cyclicGamma (p i) (p j) (p k) : ℂ)*phase H i j k := by
  let f := fun i j k => spectralTau (p i) (p j)*spectralKernel (p i) (p j) (p k)
  have hc₁ := phase_sum_cycle f H
  have hc₂ := phase_sum_cycle (fun i j k => f j k i) H
  have hc₃ : (∑ i, ∑ j, ∑ k, (f k i j : ℂ)*phase H i j k) =
      ∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k := hc₂.trans hc₁
  have hentry : tr (schurFirst p H*quadraticDefect p H) =
      ∑ i, ∑ j, ∑ k,
        ((3*f i j k-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i)/3 : ℝ) : ℂ)*
          phase H i j k := by
    simp only [tr, Matrix.trace, Matrix.diag, Matrix.mul_apply, quadraticDefect,
      schurFirst, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f, phase]
    rw [spectralKernel_comm (p j) (p i) (p k), spectralTau_comm (p i) (p k)]
    push_cast
    ring
  rw [hentry]
  have hg (i j k : n) : cyclicGamma (p i) (p j) (p k) =
      f i j k+f j k i+f k i j-
        spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i)/3 := rfl
  simp only [hg, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, sub_mul, add_mul, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hc₁ hc₃ ⊢
  rw [hc₁, hc₃]
  ring

private theorem phase_norm (H : Matrix n n ℂ) (i j k : n) :
    ‖phase H i j k‖ = ‖H i j‖*‖H j k‖*‖H k i‖ := by simp only [phase, norm_mul]

private theorem phase_sum_bound (f : n → n → n → ℝ) (H : Matrix n n ℂ) :
    |(∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k).re| ≤
      ∑ i, ∑ j, ∑ k, |f i j k|*‖H i j‖*‖H j k‖*‖H k i‖ := by
  calc
    _ ≤ ‖∑ i, ∑ j, ∑ k, (f i j k : ℂ)*phase H i j k‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ∑ k, ‖(f i j k : ℂ)*phase H i j k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _))
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, phase_norm, mul_assoc]

private def cyclicMass (p : n → ℝ) (H : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ∑ k, (spectralRho (p i) (p j)^2+spectralRho (p j) (p k)^2+
    spectralRho (p k) (p i)^2)*‖H i j‖*‖H j k‖*‖H k i‖

private theorem cyclicMass_bound {d : ℕ} {p : Fin d → ℝ} (hp : ∀ i, 0 < p i)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    cyclicMass p H ≤ 6*frob H*(frob H^2-frob (schurFirst p H)^2) := by
  let B := modulusMatrix H
  let W := rhoMatrix p H
  let t := fun i j k => spectralRho (p i) (p j)^2*‖H i j‖*‖H j k‖*‖H k i‖
  let u := fun i j k => spectralRho (p i) (p j)*spectralRho (p j) (p k)*‖H i j‖*‖H j k‖*‖H k i‖
  have hs (i j : Fin d) : ‖H j i‖ = ‖H i j‖ := by
    have hh := hH.apply i j
    rw [← norm_star (H j i), hh]
  have hr (i j : Fin d) : spectralRho (p j) (p i) = spectralRho (p i) (p j) := spectralRho_comm _ _
  have ht₁ := sum_cycle t
  have ht₂ := sum_cycle (fun i j k => t j k i)
  have ht₃ : (∑ i, ∑ j, ∑ k, t k i j) = ∑ i, ∑ j, ∑ k, t i j k := (ht₁.trans ht₂).symm
  have hmass : cyclicMass p H = 3*∑ i, ∑ j, ∑ k, t i j k := by
    dsimp [cyclicMass, t] at *
    simp only [add_mul, Finset.sum_add_distrib]
    have he₁ : (∑ i, ∑ j, ∑ k, spectralRho (p j) (p k)^2*‖H i j‖*‖H j k‖*‖H k i‖) =
        ∑ i, ∑ j, ∑ k, spectralRho (p i) (p j)^2*‖H i j‖*‖H j k‖*‖H k i‖ := by
      convert ht₁.symm using 1 <;> congr 1 <;> ext i <;> congr 1 <;> ext j <;> congr 1 <;> ext k <;> ring
    have he₂ : (∑ i, ∑ j, ∑ k, spectralRho (p k) (p i)^2*‖H i j‖*‖H j k‖*‖H k i‖) =
        ∑ i, ∑ j, ∑ k, spectralRho (p i) (p j)^2*‖H i j‖*‖H j k‖*‖H k i‖ := by
      convert ht₃ using 1 <;> congr 1 <;> ext i <;> congr 1 <;> ext j <;> congr 1 <;> ext k <;> ring
    rw [he₁, he₂]; ring
  have htbound : (∑ i, ∑ j, ∑ k, t i j k) ≤ 2*∑ i, ∑ j, ∑ k, u i j k := by
    have hm : (∑ i, ∑ j, ∑ k, t i j k) ≤
        (∑ i, ∑ j, ∑ k, u i j k)+(∑ i, ∑ j, ∑ k, u k i j) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have htri := spectralRho_triangle (hp i) (hp k) (hp j)
      rw [spectralRho_comm (p k) (p j)] at htri
      have h := mul_le_mul_of_nonneg_right htri
        (mul_nonneg (mul_nonneg (mul_nonneg (spectralRho_nonneg _ _) (norm_nonneg (H i j)))
          (norm_nonneg (H j k))) (norm_nonneg (H k i)))
      dsimp [t, u]
      rw [spectralRho_comm (p k) (p i)]
      nlinarith only [h]
    have hu₁ := sum_cycle u
    have hu₂ := sum_cycle (fun i j k => u j k i)
    rw [← hu₂, ← hu₁] at hm
    linarith
  have htrace : (∑ i, ∑ j, ∑ k, u i j k) = (W*W*B).trace.re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul,
      W, B, rhoMatrix, modulusMatrix]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
    dsimp only [u]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hbound : (W*W*B).trace.re ≤ frob W^2*frob H := by
    calc
      _ ≤ |(W*W*B).trace.re| := le_abs_self _
      _ ≤ frob (W*W)*frob B := abs_reTrace_mul (W*W) B
      _ ≤ (frob W*frob W)*frob B := mul_le_mul_of_nonneg_right (frob_mul W W) (frob_nonneg B)
      _ = _ := by rw [show frob B = frob H from modulusMatrix_frob H]; ring
  have hgap := rhoMatrix_gap hp H
  change frob W^2 = _ at hgap
  rw [hmass]
  rw [htrace] at htbound
  nlinarith only [htbound, hbound, hgap]

private theorem cubic_uniform_bound {d : ℕ} {p : Fin d → ℝ} (hp : ∀ i, 0 < p i)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    |(4*tr (H^3)-4*tr ((schurFirst p H)^3)-6*tr (schurFirst p H*quadraticDefect p H)).re| ≤
      51*frob H*(frob H^2-frob (schurFirst p H)^2) := by
  have hAD : |(tr (schurFirst p H*quadraticDefect p H)).re| ≤ (3/4)*cyclicMass p H := by
    rw [trace_defect_cycle]
    apply (phase_sum_bound (fun i j k => cyclicGamma (p i) (p j) (p k)) H).trans
    rw [cyclicMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hg := cyclicGamma_bounds (hp i) (hp j) (hp k)
    rw [abs_of_nonneg hg.1]
    nlinarith only [mul_le_mul_of_nonneg_right hg.2
      (mul_nonneg (mul_nonneg (norm_nonneg (H i j)) (norm_nonneg (H j k))) (norm_nonneg (H k i)))]
  have hc : |(tr (H^3)-tr ((schurFirst p H)^3)).re| ≤ cyclicMass p H := by
    have he : tr (H^3)-tr ((schurFirst p H)^3) =
        ∑ i, ∑ j, ∑ k, ((1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) : ℝ) : ℂ)*
          phase H i j k := by
      rw [trace_cube_sum, trace_cube_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [phase, schurFirst]
      push_cast
      ring
    rw [he]
    apply (phase_sum_bound _ H).trans
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    have ht := spectralTau_bounds (hp i) (hp j)
    have hu := spectralTau_bounds (hp j) (hp k)
    have hv := spectralTau_bounds (hp k) (hp i)
    have hn : 0 ≤ 1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) := by
      have h := mul_le_mul (mul_le_mul ht.2 hu.2 hu.1.le (by norm_num : (0 : ℝ) ≤ 1)) hv.2 hv.1.le (by norm_num : (0 : ℝ) ≤ 1*1)
      norm_num at h
      linarith
    have hb : 1-spectralTau (p i) (p j)*spectralTau (p j) (p k)*spectralTau (p k) (p i) ≤
        spectralRho (p i) (p j)^2+spectralRho (p j) (p k)^2+spectralRho (p k) (p i)^2 := by
      rw [spectralRho_sq (hp i) (hp j), spectralRho_sq (hp j) (hp k), spectralRho_sq (hp k) (hp i)]
      have h₁ : 0 ≤ (1-spectralTau (p i) (p j))*(1-spectralTau (p j) (p k)) := by positivity
      have h₂ : 0 ≤ (1-spectralTau (p k) (p i))*(1-spectralTau (p i) (p j)*spectralTau (p j) (p k)) := by positivity
      have h₃ : 0 ≤ spectralTau (p i) (p j)*(1-spectralTau (p i) (p j)) := by positivity
      have h₄ : 0 ≤ spectralTau (p j) (p k)*(1-spectralTau (p j) (p k)) := by positivity
      have h₅ : 0 ≤ spectralTau (p k) (p i)*(1-spectralTau (p k) (p i)) := by positivity
      nlinarith only [h₁, h₂, h₃, h₄, h₅]
    rw [abs_of_nonneg hn]
    nlinarith only [mul_le_mul_of_nonneg_right hb
      (mul_nonneg (mul_nonneg (norm_nonneg (H i j)) (norm_nonneg (H j k))) (norm_nonneg (H k i)))]
  have hs := cyclicMass_bound hp hH
  have hsum := abs_add_le (4*(tr (H^3)-tr ((schurFirst p H)^3)).re)
    (-6*(tr (schurFirst p H*quadraticDefect p H)).re)
  norm_num [Complex.sub_re, Complex.mul_re, abs_mul] at hsum ⊢
  linarith

private theorem quadratic_remainder_uniform {d : ℕ}
    (A D R : Matrix (Fin d) (Fin d) ℂ) (hR : R.IsHermitian)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/2) (hA : frob A ≤ r) :
    -6*frob D^2 ≤ 12*(((1+A)*R*R).trace.re-(D*R).trace.re) := by
  let q := frob R
  have hq : 0 ≤ q := frob_nonneg R
  have ha : |(A*(R*R)).trace.re| ≤ r*q^2 := by
    calc
      _ ≤ frob A*frob (R*R) := abs_reTrace_mul A (R*R)
      _ ≤ r*(q*q) := mul_le_mul hA (frob_mul R R) (frob_nonneg _) hr
      _ = r*q^2 := by ring
  have hd : |(D*R).trace.re| ≤ frob D*q := abs_reTrace_mul D R
  have he : ((1+A)*R*R).trace.re = q^2+(A*(R*R)).trace.re := by
    simp only [add_mul, one_mul, Matrix.trace_add, Complex.add_re, mul_assoc,
      frob_sq_hermitian hR]
    rfl
  rw [he]
  have hlow := (abs_le.mp ha).1
  have hhigh := (abs_le.mp hd).2
  have hhalf := mul_le_mul_of_nonneg_right hrsmall (sq_nonneg q)
  nlinarith [sq_nonneg (q-frob D)]


private theorem actual_uniform_supplier {d : ℕ} {p : Fin d → ℝ}
    (hp : ∀ i, 0 < p i) {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (hradius : frob H ≤ 1/20) {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.IsHermitian) :
    (frob H^2-frob (schurFirst p H)^2)/6 ≤
      (tr (actualCoeff p (1+H) 3+(2 : ℝ) • (Z*actualCoeff p (1+H) 2)+
        actualCoeff p (1+H) 1*Z^2-(5/48 : ℝ) • (actualCoeff p (1+H) 1)^3)).re := by
  let r := frob H
  let A := schurFirst p H
  let D := quadraticDefect p H
  let T := (1 : Matrix (Fin d) (Fin d) ℂ)+A
  let R := Z-(1/6 : ℝ) • T
  let g := frob H^2-frob A^2
  have hr : 0 ≤ r := frob_nonneg H
  have hrsmall : r ≤ 1/20 := hradius
  have hrhalf : r ≤ 1/2 := by linarith
  have hA : frob A ≤ r := schurFirst_norm hp H
  have hAh : A.IsHermitian := schurFirst_hermitian p hH
  have hTh : T.IsHermitian := Matrix.isHermitian_one.add hAh
  have hRh : R.IsHermitian :=
    hZ.sub (hTh.smul (IsSelfAdjoint.of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)))
  have hg : 0 ≤ g := by
    have hg := rhoMatrix_gap hp H
    change _ = g at hg
    rw [← hg]
    positivity
  have hD : frob D^2 ≤ (1024/81)*r^2*g := quadraticDefect_uniform hp H
  have hh := cubic_uniform_bound hp hH
  change |(4*tr (H^3)-4*tr (A^3)-6*tr (A*D)).re| ≤ 51*r*g at hh
  have he := quadratic_remainder_uniform A D R hRh r hr hrhalf hA
  have hs : ((1 : Matrix (Fin d) (Fin d) ℂ)+H).IsHermitian := Matrix.isHermitian_one.add hH
  obtain ⟨hc₁, hc₂, htraceD⟩ := radial_coefficients hp hH
  have ht := (balanced_trace_normalization hp hs).2
  rw [hc₁, hc₂] at ht
  have hpoly := allZ_polynomial T D Z (actualCoeff p (1+H) 3) (tr ((1+H)^3)) ht
  have hlin : tr H = tr A := by
    simp [A, schurFirst, tr, Matrix.trace, Matrix.diag, spectralTau_self (hp _)]
  have hrad := radial_trace_reduction H A D hlin htraceD
  have hid : 18*(tr (actualCoeff p (1+H) 3+
        (2 : ℝ) • (Z*actualCoeff p (1+H) 2)+actualCoeff p (1+H) 1*Z^2-
        (5/48 : ℝ) • (actualCoeff p (1+H) 1)^3)) =
      6*(tr (H*H)-tr (A*A))+(4*tr (H^3)-4*tr (A^3)-6*tr (A*D))+
        12*(tr (T*R*R)-tr (D*R)) := by
    rw [hc₁, hc₂]
    dsimp only at hpoly
    simp only [tr, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      Complex.real_smul, smul_eq_mul, pow_succ, pow_zero, mul_one, one_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← mul_assoc] at hpoly ⊢
    simp only [tr, pow_succ, pow_zero, mul_one, one_mul] at hrad
    dsimp only [T, R, A, D] at hpoly hrad ⊢
    norm_num at hpoly ⊢
    linear_combination hpoly+hrad
  have hidre := congrArg Complex.re hid
  have hgap : (tr (H*H)-tr (A*A)).re = g := by
    simp only [Complex.sub_re, tr, frob_sq_hermitian hH, frob_sq_hermitian hAh]
    rfl
  have hmargin : 3*g ≤ 6*g-51*r*g-6*frob D^2 := by
    have hr₂ : r^2 ≤ (1/20 : ℝ)^2 := (sq_le_sq₀ hr (by norm_num)).mpr hrsmall
    have h₁ := mul_le_mul_of_nonneg_right hrsmall hg
    have h₂ := mul_le_mul_of_nonneg_right hr₂ hg
    nlinarith only [hD, h₁, h₂, hg]
  have hl := (abs_le.mp hh).1
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr] at hidre hgap hl
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, tr, T] at he
  change g/6 ≤ _
  norm_num [tr, Complex.add_re, Complex.sub_re, Complex.mul_re]
  linarith

section UniformActual
open scoped Matrix.Norms.L2Operator

/-- Uniform-radius local all-Z supplier for actual factorial-normalized CFC
jets. The spectrum is arbitrary positive, including empty and repeated levels;
H and Z are arbitrary Hermitian matrices, with only a Frobenius bound on H. -/
theorem finite_spectrum_uniform_local_supplier {d : ℕ} (p : Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (hradius : frob H ≤ 1/20) (Z : Matrix (Fin d) (Fin d) ℂ) (hZ : Z.IsHermitian) :
    let P : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (p i : ℂ))
    let S := (1 : Matrix (Fin d) (Fin d) ℂ)+H
    let F := fun t : ℝ => P⁻¹*
      CFC.rpow (P^3+t • (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let A : Matrix (Fin d) (Fin d) ℂ := fun i j => (spectralTau (p i) (p j) : ℂ)*H i j
    (frob H^2-frob A^2)/6 ≤
      (B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re := by
  dsimp only
  simpa only [actualCoeff, RpowPencilTaylor.jetCoeff, pencilDirection,
    balanceP_rpow hp, rootP, tr, schurFirst] using actual_uniform_supplier hp hH hradius hZ

#print axioms finite_spectrum_uniform_local_supplier
end UniformActual

end Uniform

end D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
