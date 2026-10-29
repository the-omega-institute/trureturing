/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite normalized two-input coefficients on the original integer twisted sector. -/

import D5.S3.VertexAlgebra.CorrectedInversion.Dual
import D5.S3.VertexAlgebra.TwistedGround.ActualEnergyRestrictedDual
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-!
The target is the direct sum of full duals of the theta-fixed source grades.
The two inputs are in the negative eigenspace of the original actualParity.
For rank twenty-four these are the integer conformal weights, starting at two.
The chosen actualForm, its ordered slots, and the rank/16 zero mode are retained.
The public index m is the coefficient of z^(-m-1).

This coefficient construction does not assert translation, mixed Jacobi,
skew exchange, an identification with the original source, or three-twisted
crossing. Those identities require further proofs about this same coefficient.
Classical carrier conventions are FLM, PNAS 81 (1984), pp.3257--3258, (5).
The finite coefficient derivation here is a repository Lean construction;
the announcement is not cited as a detailed proof of this formula.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint
open CorrectedInversion ActualOddGradeOrthogonality
open HalfFock.ActualEnergyCovariance
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)

/-- The full original fixed-source grade. -/
def fixedGrade (D : LatticeData) (d : ℤ) : Submodule ℂ (Carrier D) :=
  grade D d ⊓ fixedSpace D

/-- The algebraic graded restricted dual of the actual theta-fixed source. -/
abbrev FixedRestrictedDual (D : LatticeData) :=
  ⨁ d : ℤ, Module.Dual ℂ (fixedGrade D d)

private theorem theta_omega_fixed (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    theta D (LatticeActualConformalState.omega D H) =
      LatticeActualConformalState.omega D H := by
  change thetaLinear D (LatticeActualConformalState.omega D H) = _
  simp [LatticeActualConformalState.omega,
    LatticeActualConformalState.conformalPolynomial, theta_single,
    sigma, sigma_X, map_mul, map_add, map_sum, smul_eq_mul]

private abbrev originalL0 (D : LatticeData) : Module.End ℂ (Carrier D) :=
  sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 0

private abbrev originalL1 (D : LatticeData) : Module.End ℂ (Carrier D) :=
  sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1

private theorem original_l1_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (q : ℕ) :
    originalL0 D ((originalL1 D ^ q) a) =
      ((d - (q : ℤ) : ℤ) : ℂ) • ((originalL1 D ^ q) a) := by
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  have h0 : originalL0 D a = (d : ℂ) • a := by
    exact (actualL0_eigen_iff_grade D (LatticeSugawaraCurrents.gramComplex D)⁻¹ hHG hGH d a).mpr ha
  induction q with
  | zero => simpa using h0
  | succ q ih =>
    have hcomm := congrArg (fun A : Module.End ℂ (Carrier D) =>
      A ((originalL1 D ^ q) a))
      (sugawaraMode_virasoro D (LatticeSugawaraCurrents.gramComplex D)⁻¹ hHG hGH 0 1)
    have hcomm' : originalL0 D (originalL1 D ((originalL1 D ^ q) a)) -
        originalL1 D (originalL0 D ((originalL1 D ^ q) a)) =
          (-1 : ℂ) • originalL1 D ((originalL1 D ^ q) a) := by
      simpa [originalL0, originalL1] using hcomm
    rw [ih, map_smul, sub_eq_iff_eq_add] at hcomm'
    simp only [pow_succ', Module.End.mul_apply]
    rw [hcomm', ← add_smul]
    congr 1
    push_cast
    ring

private theorem original_l1_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (q : ℕ) :
    (originalL1 D ^ q) a ∈ grade D (d - (q : ℤ)) := by
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  apply (actualL0_eigen_iff_grade D (LatticeSugawaraCurrents.gramComplex D)⁻¹ hHG hGH
    (d - (q : ℤ)) ((originalL1 D ^ q) a)).mp
  exact original_l1_eigen D hu d a ha q

private theorem original_l1_fixed (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (ha : a ∈ fixedSpace D) (q : ℕ) :
    theta D ((originalL1 D ^ q) a) = (originalL1 D ^ q) a := by
  have h0 : theta D a = a := (mem_fixedSpace D a).mp ha
  induction q with
  | zero => simpa using h0
  | succ q ih =>
    simp only [pow_succ', Module.End.mul_apply]
    have haG : LatticeActualConformalState.omega D (LatticeSugawaraCurrents.gramComplex D)⁻¹ ∈ fixedSpace D :=
      (mem_fixedSpace D _).mpr (theta_omega_fixed D (LatticeSugawaraCurrents.gramComplex D)⁻¹)
    have hq : (originalL1 D ^ q) a ∈ fixedSpace D :=
      (mem_fixedSpace D _).mpr ih
    have hclosed := fixed_mode_closed D
      (LatticeActualConformalState.omega D (LatticeSugawaraCurrents.gramComplex D)⁻¹) ((originalL1 D ^ q) a)
      haG hq 2
    have htheta := (mem_fixedSpace D _).mp hclosed
    have hm : ((Y D (LatticeActualConformalState.omega D (LatticeSugawaraCurrents.gramComplex D)⁻¹))[[2]]) =
        sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1 := by
      simpa using (LatticeActualConformalState.omega_modes D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1)
    rw [hm] at htheta
    exact htheta

/-- The finite opposite action on the original fixed grades.  The source
L1-flow is cut at its actual finite support bound; every summand has the
corrected original-space grade `e + m - d + 1`. -/
def oppositeMode (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) (e : ℤ) :
    fixedGrade D e →ₗ[ℂ] fixedGrade D (e + m - d + 1) where
  toFun b := by
    classical
    let R := a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))
    refine ⟨(∑ ell ∈ Finset.range (R + 1),
      (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) b.val), ?_⟩
    apply (fixedGrade D (e + m - d + 1)).sum_mem
    intro ell hell
    have haell : (originalL1 D ^ ell) a.val ∈ grade D (d - (ell : ℤ)) :=
      original_l1_grade D hu d a.val a.property.1 ell
    have hg := positive_actual_mode_grade D hD (d - (ell : ℤ)) e
      (2*d-(ell : ℤ)-m-2) ((originalL1 D ^ ell) a.val) b.val haell b.property.1
    have hga : ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) b.val ∈
        grade D (e + m - d + 1) := by
      convert hg using 1 <;> ring_nf
    have hta := original_l1_fixed D hu a.val a.property.2 ell
    have htb : theta D b.val = b.val := (mem_fixedSpace D b.val).mp b.property.2
    have hta' : theta D ((originalL1 D ^ ell) a.val) =
        (1 : ℂ) • (originalL1 D ^ ell) a.val := by simpa using hta
    have htb' : theta D b.val = (1 : ℂ) • b.val := by simpa using htb
    have htheta := mode_eigenvalue_selection D 1 1 ((originalL1 D ^ ell) a.val) b.val
      hta' htb' (2*d-(ell : ℤ)-m-2)
    have hfs : ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) b.val ∈
        fixedSpace D := (mem_fixedSpace D _).mpr (by simpa using htheta)
    exact (fixedGrade D _).smul_mem _ ⟨hga, hfs⟩
  map_add' b c := by
    apply Subtype.ext
    change (∑ ell ∈ Finset.range
      (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c)) + 1),
      (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) (b.val + c.val)) =
      (∑ ell ∈ Finset.range
        (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c)) + 1),
        (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) b.val) +
      (∑ ell ∈ Finset.range
        (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c)) + 1),
        (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) c.val)
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' z b := by
    apply Subtype.ext
    change (∑ ell ∈ Finset.range
      (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c)) + 1),
      (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) (z • b.val)) =
      z • (∑ ell ∈ Finset.range
        (a.val.support.sup (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c)) + 1),
        (((-1 : ℂ) ^ d) / (ell.factorial : ℂ)) •
      ((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-2]]) b.val)
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ell hell
    exact smul_comm _ _ _

/-- The induced opposite action on the fixed restricted dual.  A dual input
of grade `e` is pulled back along the original action from grade
`e + d - m - 1`, which is the corrected dual-space direction. -/
private def oppositePull (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) (e : ℤ) :
    fixedGrade D (e + d - m - 1) →ₗ[ℂ] fixedGrade D e where
  toFun b := by
    let c := oppositeMode D hu hD d m a (e + d - m - 1) b
    have hg : c.val ∈ grade D e := by
      have h : e + d - m - 1 + m - d + 1 = e := by ring
      have hg := c.property.1
      change c.val ∈ grade D (e + d - m - 1 + m - d + 1) at hg
      exact (congrArg (fun k : ℤ => (c : Carrier D) ∈ grade D k) h).mp hg
    exact ⟨c.val, hg, c.property.2⟩
  map_add' b c := by
    apply Subtype.ext
    change (oppositeMode D hu hD d m a (e + d - m - 1) (b + c)).val = _
    simp only [map_add, Submodule.coe_add]
  map_smul' z b := by
    apply Subtype.ext
    change (oppositeMode D hu hD d m a (e + d - m - 1) (z • b)).val = _
    simp only [map_smul, RingHom.id_apply, Submodule.coe_smul]
def oppositeDualMode (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d m : ℤ) (a : fixedGrade D d) (e : ℤ) :
    Module.Dual ℂ (fixedGrade D e) →ₗ[ℂ]
      Module.Dual ℂ (fixedGrade D (e + d - m - 1)) where
  toFun f := f.comp (oppositePull D hu hD d m a e)
  map_add' f g := by
    ext b
    rfl
  map_smul' z f := by
    ext b
    rfl


private abbrev T (D : LatticeData) (hu : IsUnit D.G.det) :=
  tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1

private abbrev TensorIndex (D : LatticeData) (hu : IsUnit D.G.det) :=
  OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu)

private theorem lowering_bracket (D : LatticeData) (hu : IsUnit D.G.det) :
    actualTensorL0 D hu * T D hu - T D hu * actualTensorL0 D hu = -T D hu := by
  apply TensorProduct.ext'
  intro p t
  have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A p ⊗ₜ[ℂ] t)
    (L_virasoro D (HalfFockSpectralFiberSource.actualInverse D)
      (HalfFockSpectralFiberSource.actualInverse_left D hu)
      (HalfFockSpectralFiberSource.actualInverse_right D hu) 0 1)
  norm_num at h
  simpa only [actualTensorL0, T, tensorL, tensorEnd, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.neg_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.neg_tmul] using h

private theorem lowering_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℤ) (u : ActualTensor D hu)
    (huN : actualTensorL0 D hu u = ((D.rank : ℂ)/16 + (N : ℂ)/2) • u)
    (q : ℕ) :
    actualTensorL0 D hu ((T D hu ^ q) u) =
      ((D.rank : ℂ)/16 + ((N - 2*(q : ℤ) : ℤ) : ℂ)/2) • ((T D hu ^ q) u) := by
  induction q with
  | zero => simpa using huN
  | succ q ih =>
    have h := LinearMap.congr_fun (lowering_bracket D hu) ((T D hu ^ q) u)
    change actualTensorL0 D hu (T D hu ((T D hu ^ q) u)) -
      T D hu (actualTensorL0 D hu ((T D hu ^ q) u)) =
        -T D hu ((T D hu ^ q) u) at h
    rw [ih, map_smul, sub_eq_iff_eq_add] at h
    simp only [pow_succ', Module.End.mul_apply]
    rw [h, ← neg_one_smul ℂ (T D hu ((T D hu ^ q) u)), ← add_smul]
    congr 1
    push_cast
    ring

private theorem negative_eigen_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℤ) (hN : N < 0) (u : ActualTensor D hu)
    (huN : actualTensorL0 D hu u = ((D.rank : ℂ)/16 + (N : ℂ)/2) • u) : u = 0 := by
  classical
  apply (actualAmbientBasis D hu).repr.injective
  ext i
  have h := congrArg (fun x => (actualAmbientBasis D hu).repr x i) huN
  rw [actualTensorL0_repr] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have gap : (D.rank : ℂ)/16 + (oddWeight D i.1 : ℂ)/2 -
      ((D.rank : ℂ)/16 + (N : ℂ)/2) ≠ 0 := by
    intro hz
    have hc : (oddWeight D i.1 : ℂ) = (N : ℂ) := by linear_combination 2*hz
    have hi : (oddWeight D i.1 : ℤ) = N := by exact_mod_cast hc
    have hn : 0 ≤ (oddWeight D i.1 : ℤ) := by positivity
    omega
  have hz := sub_eq_zero.mpr h
  rw [← sub_mul] at hz
  simpa using (mul_eq_zero.mp hz).resolve_left gap

private theorem lowering_killed (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℤ) (u : ActualTensor D hu)
    (huN : actualTensorL0 D hu u = ((D.rank : ℂ)/16 + (N : ℂ)/2) • u)
    (q : ℕ) (hq : N < 2*(q : ℤ)) : (T D hu ^ q) u = 0 :=
  negative_eigen_zero D hu (N-2*(q : ℤ)) (by omega) _
    (lowering_eigen D hu N u huN q)

private def liftGrade (D : LatticeData) (d : ℤ) :
    Module.Dual ℂ (Carrier D) →ₗ[ℂ] FixedRestrictedDual D :=
  (DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h)) d).comp
    (fixedGrade D d).dualRestrict

/-- The finite homogeneous kernel, with the original right orientation of B. -/
private def kernel (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (m : ℤ) (u v : ActualTensor D hu) : Module.Dual ℂ (Carrier D) :=
  ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
    let s : ℤ := m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
    (((-1 : ℂ)^((H : ℤ)+s)) / ((p.factorial : ℂ)*(q.factorial : ℂ))) •
      K_R D hu (2*s) ((T D hu ^ p) v) ((T D hu ^ q) u)

private theorem K_R_add_left (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x z y : ActualTensor D hu) (a : Carrier D) :
    K_R D hu e (x + z) y a = K_R D hu e x y a + K_R D hu e z y a := by
  change actualForm D hu (x + z) ((correctedField D hu a).coeff e y) =
    actualForm D hu x ((correctedField D hu a).coeff e y) +
      actualForm D hu z ((correctedField D hu a).coeff e y)
  exact LinearMap.BilinForm.add_left (B := actualForm D hu) x z
    ((correctedField D hu a).coeff e y)

private theorem K_R_smul_left (D : LatticeData) (hu : IsUnit D.G.det)
    (c : ℂ) (e : ℤ) (x y : ActualTensor D hu) (a : Carrier D) :
    K_R D hu e (c • x) y a = c • K_R D hu e x y a := by
  change actualForm D hu (c • x) ((correctedField D hu a).coeff e y) =
    c • actualForm D hu x ((correctedField D hu a).coeff e y)
  simpa only [smul_eq_mul] using
    (LinearMap.BilinForm.smul_left (B := actualForm D hu) c x
      ((correctedField D hu a).coeff e y))

private theorem K_R_add_right (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y z : ActualTensor D hu) (a : Carrier D) :
    K_R D hu e x (y + z) a = K_R D hu e x y a + K_R D hu e x z a := by
  change actualForm D hu x ((correctedField D hu a).coeff e (y + z)) =
    actualForm D hu x ((correctedField D hu a).coeff e y) +
      actualForm D hu x ((correctedField D hu a).coeff e z)
  rw [map_add]
  exact LinearMap.BilinForm.add_right (B := actualForm D hu) x
    ((correctedField D hu a).coeff e y) ((correctedField D hu a).coeff e z)

private theorem K_R_smul_right (D : LatticeData) (hu : IsUnit D.G.det)
    (c : ℂ) (e : ℤ) (x y : ActualTensor D hu) (a : Carrier D) :
    K_R D hu e x (c • y) a = c • K_R D hu e x y a := by
  change actualForm D hu x ((correctedField D hu a).coeff e (c • y)) =
    c • actualForm D hu x ((correctedField D hu a).coeff e y)
  rw [map_smul]
  simpa only [smul_eq_mul] using
    (LinearMap.BilinForm.smul_right (B := actualForm D hu) c x
      ((correctedField D hu a).coeff e y))

set_option maxHeartbeats 4000000 in
private def kernelBilinear (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (m : ℤ) :
    ActualTensor D hu →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] Module.Dual ℂ (Carrier D) where
  toFun u :=
    { toFun := kernel D hu H K m u
      map_add' := by
        intro v w
        apply LinearMap.ext
        intro a
        change kernel D hu H K m u (v + w) a = _
        simp [kernel, K_R_add_left, K_R_add_right, map_add, mul_add, ← Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro a
        change kernel D hu H K m u (c • v) a = _
        simp [kernel, K_R_smul_left, K_R_smul_right, map_smul, Finset.mul_sum, smul_smul, mul_left_comm, ← Finset.sum_smul] }
  map_add' := by
    intro u w
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro a
    change kernel D hu H K m (u + w) v a = _
    simp [kernel, K_R_add_left, K_R_add_right, map_add, mul_add, ← Finset.sum_add_distrib]
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro a
    change kernel D hu H K m (c • u) v a = _
    simp [kernel, K_R_smul_left, K_R_smul_right, map_smul, Finset.mul_sum, smul_smul, mul_left_comm, ← Finset.sum_smul]

private theorem kernel_energy_selection (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (m d : ℤ) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u =
      ((D.rank : ℂ)/16 + ((2*(H : ℤ)-3 : ℤ) : ℂ)/2) • u)
    (hvK : actualTensorL0 D hu v =
      ((D.rank : ℂ)/16 + ((2*(K : ℤ)-3 : ℤ) : ℂ)/2) • v)
    (a : Carrier D) (ha : a ∈ grade D d)
    (hd : d ≠ (H : ℤ)+(K : ℤ)-m-1) : kernel D hu H K m u v a = 0 := by
  classical
  simp only [kernel, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  let s : ℤ := m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
  have hleft := lowering_eigen D hu (2*(K : ℤ)-3) v hvK p
  have hright := correctedField_signed_output D hu d
    (2*(H : ℤ)-3-2*(q : ℤ)) (2*s) a ha ((T D hu ^ q) u)
    (lowering_eigen D hu (2*(H : ℤ)-3) u huH q)
  have hz := actualForm_oddGrade_orthogonal D hu
    (2*(K : ℤ)-3-2*(p : ℤ))
    ((2*(H : ℤ)-3-2*(q : ℤ))+2*s+2*d)
    ((T D hu ^ p) v) ((correctedField D hu a).coeff (2*s) ((T D hu ^ q) u))
    hleft hright (by dsimp [s]; omega)
  change _ * actualForm D hu ((T D hu ^ p) v)
    ((correctedField D hu a).coeff (2*s) ((T D hu ^ q) u)) = 0
  rw [hz, mul_zero]

private theorem kernel_term_outside (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (hH : 2 ≤ H) (hK : 2 ≤ K) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u =
      ((D.rank : ℂ)/16 + ((2*(H : ℤ)-3 : ℤ) : ℂ)/2) • u)
    (hvK : actualTensorL0 D hu v =
      ((D.rank : ℂ)/16 + ((2*(K : ℤ)-3 : ℤ) : ℂ)/2) • v)
    (e : ℤ) (p q : ℕ) (hout : K-1 ≤ p ∨ H-1 ≤ q) :
    K_R D hu e ((T D hu ^ p) v) ((T D hu ^ q) u) = 0 := by
  rcases hout with hp | hq
  · have hz := lowering_killed D hu (2*(K : ℤ)-3) v hvK p (by omega)
    ext a
    simp [K_R, hz]
  · have hz := lowering_killed D hu (2*(H : ℤ)-3) u huH q (by omega)
    ext a
    simp [K_R, hz]

private theorem kernel_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (hH : 2 ≤ H) (hK : 2 ≤ K) (m : ℤ) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u =
      ((D.rank : ℂ)/16 + ((2*(H : ℤ)-3 : ℤ) : ℂ)/2) • u)
    (hvK : actualTensorL0 D hu v =
      ((D.rank : ℂ)/16 + ((2*(K : ℤ)-3 : ℤ) : ℂ)/2) • v) :
    Function.HasFiniteSupport (fun pq : ℕ × ℕ =>
      let s : ℤ := m+1-(pq.1 : ℤ)-2*(H : ℤ)+(pq.2 : ℤ)
      (((-1 : ℂ)^((H : ℤ)+s))/((pq.1.factorial : ℂ)*(pq.2.factorial : ℂ))) •
        K_R D hu (2*s) ((T D hu ^ pq.1) v) ((T D hu ^ pq.2) u)) := by
  classical
  apply ((Finset.range (K-1)).product (Finset.range (H-1))).finite_toSet.subset
  intro pq hpq
  by_contra hout
  have ho : K-1 ≤ pq.1 ∨ H-1 ≤ pq.2 := by
    have hnot : ¬ (pq.1 < K - 1 ∧ pq.2 < H - 1) := by
      intro hmem
      apply hout
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hmem.1,
        Finset.mem_range.mpr hmem.2⟩
    omega
  let s : ℤ := m + 1 - (pq.1 : ℤ) - 2 * (H : ℤ) + (pq.2 : ℤ)
  have hz : K_R D hu (2 * s) ((T D hu ^ pq.1) v) ((T D hu ^ pq.2) u) = 0 :=
    kernel_term_outside D hu H K hH hK u v huH hvK (2 * s) pq.1 pq.2 ho
  apply hpq
  change (((-1 : ℂ)^((H : ℤ)+s))/((pq.1.factorial : ℂ)*(pq.2.factorial : ℂ))) •
    K_R D hu (2*s) ((T D hu ^ pq.1) v) ((T D hu ^ pq.2) u) = 0
  rw [hz, smul_zero]

private def basisCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (m : ℤ)
    (i j : TensorIndex D hu) : FixedRestrictedDual D := by
  classical
  let H := (oddWeight D i.1+3)/2
  let K := (oddWeight D j.1+3)/2
  exact if oddWeight D i.1 % 2 = 1 ∧ oddWeight D j.1 % 2 = 1 then
    liftGrade D ((H : ℤ)+(K : ℤ)-m-1)
      (kernelBilinear D hu H K m (actualAmbientBasis D hu i) (actualAmbientBasis D hu j))
    else 0

private def ambientCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (m : ℤ) :
    ActualTensor D hu →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] FixedRestrictedDual D :=
  (actualAmbientBasis D hu).constr ℂ
    (fun i => (actualAmbientBasis D hu).constr ℂ (basisCoefficient D hu m i))

private theorem homogeneous_support (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (i : TensorIndex D hu) (hi : i ∈ ((actualAmbientBasis D hu).repr u).support) :
    oddWeight D i.1+3 = 2*H := by
  have hc := congrArg (fun x => (actualAmbientBasis D hu).repr x i) huH
  rw [actualTensorL0_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hs := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) hc
  rw [h24] at hs
  have hw : (oddWeight D i.1 : ℂ)+3 = 2*(H : ℂ) := by
    norm_num at hs
    linear_combination 2*hs
  exact_mod_cast hw

private theorem homogeneous_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (m : ℤ) (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (hvK : actualTensorL0 D hu v = (K : ℂ) • v) :
    ambientCoefficient D hu m u v =
      liftGrade D ((H : ℤ)+(K : ℤ)-m-1) (kernel D hu H K m u v) := by
  classical
  let b := actualAmbientBasis D hu
  change ambientCoefficient D hu m u v =
    liftGrade D ((H : ℤ)+(K : ℤ)-m-1) (kernelBilinear D hu H K m u v)
  rw [← b.linearCombination_repr u]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← b.linearCombination_repr v]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hiW := homogeneous_support D hu h24 H u huH i hi
  have hjW := homogeneous_support D hu h24 K v hvK j hj
  have hiH : (oddWeight D i.1+3)/2 = H := by omega
  have hjK : (oddWeight D j.1+3)/2 = K := by omega
  have hodd : oddWeight D i.1 % 2 = 1 ∧ oddWeight D j.1 % 2 = 1 := by omega
  change ambientCoefficient D hu m (b i) (b j) = _
  dsimp [ambientCoefficient, b]
  rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  simp [basisCoefficient, b, hodd, hiH, hjK]

/-- Genuine linear coefficient maps on both actual integer twisted inputs. -/
def normalizedCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (m : ℤ) :
    paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ] FixedRestrictedDual D where
  toFun u := (ambientCoefficient D hu m u.val).comp (paritySpace D hu (-1)).subtype
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply DFinsupp.ext
    intro d
    apply LinearMap.ext
    intro a
    change ambientCoefficient D hu m (u.val + v.val) w.val d a = _
    simp only [Submodule.coe_add, DirectSum.add_apply, Submodule.dualRestrict_apply,
      LinearMap.add_apply]
    exact congrArg (fun z : FixedRestrictedDual D => z d a)
      (LinearMap.congr_fun ((ambientCoefficient D hu m).map_add u.val v.val) w.val)
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    apply DFinsupp.ext
    intro d
    apply LinearMap.ext
    intro a
    change ambientCoefficient D hu m (c • u.val) w.val d a = _
    simp only [Submodule.coe_smul, DirectSum.smul_apply, Submodule.dualRestrict_apply,
      LinearMap.smul_apply, RingHom.id_apply]
    exact congrArg (fun z : FixedRestrictedDual D => z d a)
      (LinearMap.congr_fun ((ambientCoefficient D hu m).map_smul c u.val) w.val)

/-- Evaluation on every actual fixed-grade test vector, in standard modes.
The original zero mode gives the target grade H+K-m-1; other grades vanish
by the original form's orthogonality, not by discarding test vectors. -/
theorem normalizedCoefficient_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (m : ℤ)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (d : ℤ) (a : fixedGrade D d) :
    normalizedCoefficient D hu m u v d a =
      ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
        let s : ℤ := m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
        (((-1 : ℂ)^((H : ℤ)+s))/((p.factorial : ℂ)*(q.factorial : ℂ))) *
          actualForm D hu
            ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ p) v.val)
            ((correctedField D hu a.val).coeff (2*s)
              ((tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 ^ q) u.val)) := by
  classical
  change ((ambientCoefficient D hu m u.val).comp
    (paritySpace D hu (-1)).subtype) v d a = _
  simp only [LinearMap.comp_apply, Submodule.dualRestrict_apply]
  have hvsub : (paritySpace D hu (-1)).subtype v = v.val := rfl
  rw [hvsub]
  rw [homogeneous_coefficient D hu h24 H K m u.val v.val huH hvK]
  by_cases hd : d = (H : ℤ)+(K : ℤ)-m-1
  · subst d
    simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply,
      DirectSum.smul_apply, Submodule.dualRestrict_apply, kernel, K_R, smul_eq_mul]
  · have hzero :
        liftGrade D ((H : ℤ)+(K : ℤ)-m-1)
            (kernel D hu H K m u.val v.val) d a = 0 := by
      simp [liftGrade, DirectSum.lof_eq_of, DirectSum.of_apply, hd, Ne.symm hd]
    rw [hzero]
    have huOdd : actualTensorL0 D hu u.val =
        ((D.rank : ℂ)/16 + ((2*(H : ℤ)-3 : ℤ) : ℂ)/2) • u.val := by
      rw [huH, h24]
      congr 1
      push_cast
      ring
    have hvOdd : actualTensorL0 D hu v.val =
        ((D.rank : ℂ)/16 + ((2*(K : ℤ)-3 : ℤ) : ℂ)/2) • v.val := by
      rw [hvK, h24]
      congr 1
      push_cast
      ring
    have hz := kernel_energy_selection D hu H K m d u.val v.val huOdd hvOdd
      a.val a.property.1 hd
    simpa [kernel, K_R, smul_eq_mul] using hz.symm

private theorem liftGrade_negative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (d : ℤ) (hd : d < 0) (f : Module.Dual ℂ (Carrier D)) : liftGrade D d f = 0 := by
  classical
  have hgrade : grade D d = ⊥ := by
    rw [grade_eq_span]
    have hempty : {a : Label D | energy D a = d} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have hpos := chargeEnergy_nonneg D hD a.1
      have hos : 0 ≤ (oscillatorEnergy a.2 : ℤ) := by positivity
      change chargeEnergy D a.1 + (oscillatorEnergy a.2 : ℤ) ≠ d
      omega
    simp [hempty]
  have hf : (fixedGrade D d).dualRestrict f = 0 := by
    ext a
    have hz : (a : Carrier D) = 0 := by
      have h := a.property.1
      rw [hgrade] at h
      exact h
    change f (a : Carrier D) = 0
    rw [hz, map_zero]
  change DirectSum.lof ℂ ℤ (fun h => Module.Dual ℂ (fixedGrade D h)) d
    ((fixedGrade D d).dualRestrict f) = 0
  rw [hf, map_zero]

private theorem basisCoefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m : ℤ)
    (i j : TensorIndex D hu)
    (hm : (oddWeight D i.1 : ℤ)+(oddWeight D j.1 : ℤ)+3 < m) :
    basisCoefficient D hu m i j = 0 := by
  classical
  unfold basisCoefficient
  split_ifs
  · apply liftGrade_negative D hD
    have hi : ((oddWeight D i.1+3)/2 : ℕ) ≤ oddWeight D i.1+2 := by omega
    have hj : ((oddWeight D j.1+3)/2 : ℕ) ≤ oddWeight D j.1+2 := by omega
    omega
  · rfl

private theorem ambientCoefficient_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (u v : ActualTensor D hu)
    (hm : (ActualEnergyRestrictedDual.maxOddWeight D hu u : ℤ)+
      (ActualEnergyRestrictedDual.maxOddWeight D hu v : ℤ)+3 < m) :
    ambientCoefficient D hu m u v = 0 := by
  classical
  let b := actualAmbientBasis D hu
  rw [← b.linearCombination_repr u]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply smul_eq_zero.mpr
  right
  rw [← b.linearCombination_repr v]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  have hiW : oddWeight D i.1 ≤ ActualEnergyRestrictedDual.maxOddWeight D hu u :=
    Finset.le_sup (f := fun k : TensorIndex D hu => oddWeight D k.1) hi
  have hjW : oddWeight D j.1 ≤ ActualEnergyRestrictedDual.maxOddWeight D hu v :=
    Finset.le_sup (f := fun k : TensorIndex D hu => oddWeight D k.1) hj
  have hz : ambientCoefficient D hu m (b i) (b j) = 0 := by
    dsimp [ambientCoefficient, b]
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact basisCoefficient_zero D hu hD m i j (by omega)
  rw [hz, smul_zero]

/-- All actual vectors have an explicit standard-mode upper cutoff. -/
theorem normalizedCoefficient_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (u v : paritySpace D hu (-1)) (m : ℤ)
    (hm : (ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ)+
      (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ)+3 < m) :
    normalizedCoefficient D hu m u v = 0 :=
  ambientCoefficient_zero D hu hD m u.val v.val hm

/-- The sharp homogeneous standard-mode cutoff. -/
theorem normalizedCoefficient_homogeneous_truncation
    (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h24 : D.rank = 24) (H K : ℕ) (m : ℤ)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hm : (H : ℤ) + (K : ℤ) - 1 < m) :
    normalizedCoefficient D hu m u v = 0 := by
  apply DFinsupp.ext
  intro d
  apply LinearMap.ext
  intro a
  change ambientCoefficient D hu m u.val v.val d a = 0
  rw [homogeneous_coefficient D hu h24 H K m u.val v.val huH hvK]
  have hd : (H : ℤ) + (K : ℤ) - m - 1 < 0 := by omega
  have hz := liftGrade_negative D hD ((H : ℤ) + (K : ℤ) - m - 1) hd
    (kernel D hu H K m u.val v.val)
  rw [hz]
  rfl

/-- The normalized coefficients form an actual heterogeneous formal field. -/
def normalizedField (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (u : paritySpace D hu (-1)) :
    HVertexOperator ℤ ℂ (paritySpace D hu (-1)) (FixedRestrictedDual D) :=
  HVertexOperator.of_coeff (fun e => normalizedCoefficient D hu (-e-1) u) (by
    intro v
    have hb : BddBelow (Function.support (fun e : ℤ =>
        normalizedCoefficient D hu (-e-1) u v)) := by
      refine ⟨-((ActualEnergyRestrictedDual.maxOddWeight D hu u.val : ℤ)+
        (ActualEnergyRestrictedDual.maxOddWeight D hu v.val : ℤ)+4), ?_⟩
      intro e he
      by_contra hout
      exact he (normalizedCoefficient_truncation D hu hD u v (-e-1) (by omega))
    exact hb.isWF.isPWO)

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
