/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite Mobius coefficient transport for the mixed field calculation. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
import D5.S3.Arith.Lattices.Golay.RealLeech
import Batteries.Tactic.OpenPrivate

/-! Finite transport on the original carriers. The rectangle is bounded by
actual tensor supports before the change (i,j) -> (n=i+j,i). Neither a numeric
infinite exponential nor a full mixed Jacobi identity is assumed. The full
signed normalized mixed identity remains a separate proof obligation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint CorrectedInversion
open ActualOddGradeOrthogonality HalfFock.ActualEnergyCovariance
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)
open private T lowering_killed originalL1 original_l1_grade
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private theorem lowering_after_tensor_support (D : LatticeData) (hu : IsUnit D.G.det)
    (v : ActualTensor D hu) (q : ℕ)
    (hq : (ActualEnergyRestrictedDual.maxOddWeight D hu v : ℤ) < 2 * (q : ℤ)) :
    (T D hu ^ q) v = 0 := by
  classical
  let b := actualAmbientBasis D hu
  rw [← b.linearCombination_repr v]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  have bound : oddWeight D i.1 ≤ ActualEnergyRestrictedDual.maxOddWeight D hu v :=
    Finset.le_sup (f := fun i => oddWeight D i.1) hi
  have killed := lowering_killed D hu (oddWeight D i.1) (b i)
    (actual_basis_eigenvalue D hu i.1 i.2) q (by omega)
  rw [killed, smul_zero]

private theorem lowering_finite_family (D : LatticeData) (hu : IsUnit D.G.det)
    (J : ℕ) (v : ℕ → ActualTensor D hu) :
    let R := (Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu (v j)) + 1
    ∀ j < J, ∀ q : ℕ, R ≤ q → (T D hu ^ q) (v j) = 0 := by
  classical
  intro R j hj q hq
  apply lowering_after_tensor_support D hu (v j) q
  have bound := Finset.le_sup (f := fun j => ActualEnergyRestrictedDual.maxOddWeight D hu (v j))
    (Finset.mem_range.mpr hj)
  dsimp only [R] at hq
  omega

private def mobiusCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) : ℕ :=
  let J := ActualEnergyRestrictedDual.maxOddWeight D hu x + 1
  max J ((Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu
    ((correctedField D hu a).coeff e ((T D hu ^ j) x))) + 1)

private theorem mobius_rectangle_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) (i j : ℕ)
    (outside : mobiusCutoff D hu a e x ≤ i ∨ mobiusCutoff D hu a e x ≤ j) :
    (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x)) = 0 := by
  classical
  let J := ActualEnergyRestrictedDual.maxOddWeight D hu x + 1
  have inputBound : J ≤ mobiusCutoff D hu a e x := le_max_left _ _
  by_cases hj : J ≤ j
  · have killed := lowering_after_tensor_support D hu x j (by dsimp [J] at hj; omega)
    rw [killed, map_zero, map_zero]
  · have hi : mobiusCutoff D hu a e x ≤ i := outside.resolve_right (by omega)
    have outputBound :
        (Finset.range J).sup (fun j => ActualEnergyRestrictedDual.maxOddWeight D hu
          ((correctedField D hu a).coeff e ((T D hu ^ j) x))) + 1 ≤ i :=
      le_trans (le_max_right _ _) hi
    exact lowering_finite_family D hu J
      (fun j => (correctedField D hu a).coeff e ((T D hu ^ j) x)) j (by omega) i outputBound

private theorem rectangle_to_diagonals {V : Type*} [AddCommGroup V]
    (R : ℕ) (f : ℕ → ℕ → V)
    (tail : ∀ i j, R ≤ i ∨ R ≤ j → f i j = 0) :
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R, f i j) =
      ∑ n ∈ Finset.range (2*R), ∑ i ∈ Finset.range (n+1), f i (n-i) := by
  classical
  have flip := Finset.sum_range_diag_flip (2*R) f
  calc
    _ = ∑ i ∈ Finset.range (2*R), ∑ j ∈ Finset.range (2*R-i), f i j := by
      symm
      calc
        _ = ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range (2*R-i), f i j := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro i hi outside
          have bi : R ≤ i := by simpa using outside
          apply Finset.sum_eq_zero
          intro j hj
          exact tail i j (Or.inl bi)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          have bi := Finset.mem_range.mp hi
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro j hj outside
          exact tail i j (Or.inr (by simpa using outside))
    _ = _ := flip.symm

/-- The original all-order formal Mobius formula has an actual finite
rectangle evaluation on every source and tensor vector. Both target powers
are bounded before diagonal reindexing, including negative raw exponents. -/
theorem finite_mobius_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) (z : ℂ) :
    let R := mobiusCutoff D hu a e x
    (∑ i ∈ Finset.range R, ∑ j ∈ Finset.range R,
      (z^i * (-z)^j / ((i.factorial : ℂ)*(j.factorial : ℂ))) •
        (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x))) =
    ∑ n ∈ Finset.range (2*R), z^n •
      (∑ h ∈ stateEnergies D a, ∑ k ∈ Finset.range (n+1),
        (Ring.choose (2*(h : ℂ)+(e : ℂ)/2-(k : ℂ)-1) (n-k) /
          (k.factorial : ℂ)) •
        (correctedField D hu ((originalL1 D ^ k) (gradeProjection D h a))).coeff
          (e-2*(n : ℤ)+2*(k : ℤ)) x) := by
  classical
  intro R
  let f (i j : ℕ) :=
    (z^i * (-z)^j / ((i.factorial : ℂ)*(j.factorial : ℂ))) •
      (T D hu ^ i) ((correctedField D hu a).coeff e ((T D hu ^ j) x))
  have tail (i j : ℕ) (outside : R ≤ i ∨ R ≤ j) : f i j = 0 := by
    dsimp only [f]
    rw [mobius_rectangle_tail D hu a e x i j outside, smul_zero]
  rw [rectangle_to_diagonals R f tail]
  apply Finset.sum_congr rfl
  intro n hn
  have transport := LinearMap.congr_fun
    (HalfFock.ActualMobiusAllOrder.corrected_field_mobius_coefficient D hu n e a) x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at transport
  rw [← transport, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [f]
  rw [smul_smul]
  congr 1
  have bound : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have split : i+(n-i)=n := Nat.add_sub_of_le bound
  rw [neg_pow]
  have hz : z^i * z^(n-i) = z^n := by rw [← pow_add, split]
  calc
    _ = (-1 : ℂ)^(n-i) * (z^i * z^(n-i)) /
        ((i.factorial : ℂ)*((n-i).factorial : ℂ)) := by ring
    _ = _ := by rw [hz]; ring

private def homogeneousTransposeTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (d e : ℤ) (x y : ActualTensor D hu) (ell : ℕ) : Module.Dual ℂ (Carrier D) :=
  (((-1 : ℂ)^d)/(ell.factorial : ℂ)) •
    (K_R D hu (-e-4*d+2*(ell : ℤ)) x y).comp (originalL1 D ^ ell)

private theorem homogeneousTranspose_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (d e : ℤ) (x y : ActualTensor D hu) (a : Carrier D) :
    Function.HasFiniteSupport (fun ell => homogeneousTransposeTerm D hu d e x y ell a) := by
  classical
  let R := a.support.sup
    (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a c))+1
  apply (Finset.range R).finite_toSet.subset
  intro ell hell
  by_contra outside
  have bound : R ≤ ell := by simpa using outside
  have killed : (originalL1 D ^ R) a = 0 := SourceMobius.actual_sugawara_one_bound D hu a
  have tail : (originalL1 D ^ ell) a = 0 := by
    rw [show ell = (ell-R)+R by omega, pow_add, Module.End.mul_apply, killed, map_zero]
  apply hell
  simp only [homogeneousTransposeTerm, LinearMap.smul_apply, LinearMap.comp_apply,
      tail, map_zero, smul_zero]

private def homogeneousTranspose (D : LatticeData) (hu : IsUnit D.G.det)
    (d e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) where
  toFun a := ∑ᶠ ell, homogeneousTransposeTerm D hu d e x y ell a
  map_add' a b := by
    simp only [map_add]
    exact finsum_add_distrib (homogeneousTranspose_finite D hu d e x y a)
      (homogeneousTranspose_finite D hu d e x y b)
  map_smul' c a := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum _ _).symm

private theorem actual_homogeneous_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (d e : ℤ) (a : Carrier D) (ha : a ∈ grade D d) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu a).coeff e x) y =
      ∑ᶠ ell : ℕ, (((-1 : ℂ)^d)/(ell.factorial : ℂ)) *
        actualForm D hu x ((correctedField D hu ((originalL1 D ^ ell) a)).coeff
          (-e-4*d+2*(ell : ℤ)) y) := by
  classical
  change K_L D hu e x y a = homogeneousTranspose D hu d e x y a
  have span : grade D d ≤ LinearMap.ker
      (K_L D hu e x y - homogeneousTranspose D hu d e x y) := by
    rw [grade_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨c,mon⟩, energy, rfl⟩
    let R := mon.weight (sourceWeight D)
    have gradeWeight : chargeEnergy D c + (R : ℤ) = d := energy
    have normWeight : chargeNorm D c = 2*chargeEnergy D c := by
      simpa [chargeNorm] using (two_chargeEnergy D c).symm
    have phase : paritySign (chargeNorm D c / 2) * (-1 : ℂ)^R = (-1 : ℂ)^d := by
      have half : chargeNorm D c / 2 = chargeEnergy D c := by omega
      rw [half]
      have sign : paritySign (chargeEnergy D c) = (-1 : ℂ)^(chargeEnergy D c) := by
        rw [paritySign, neg_one_zpow_eq_ite]
      rw [sign, ← zpow_natCast, ← zpow_add₀ (by norm_num), gradeWeight]
    have inversion := actual_corrected_monomial_inversion D hu c mon e x y
    have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
    have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
    have finiteR : homogeneousTranspose D hu d e x y (carrierBasis D (c,mon)) =
        ∑ ell ∈ Finset.range (R+1),
          homogeneousTransposeTerm D hu d e x y ell (carrierBasis D (c,mon)) := by
      apply finsum_eq_sum_of_support_subset
      intro ell hell
      by_contra outside
      have bound : R+1 ≤ ell := by simpa using outside
      have killed : (originalL1 D ^ (R+1)) (carrierBasis D (c,mon)) = 0 := by
        simpa only [originalL1, carrierBasis_apply, R] using
          SourceMobius.actual_sugawara_one_monomial_bound D hu c mon (1 : ℂ)
      have tail : (originalL1 D ^ ell) (carrierBasis D (c,mon)) = 0 := by
        rw [show ell = (ell-(R+1))+(R+1) by omega, pow_add, Module.End.mul_apply, killed, map_zero]
      apply hell
      simp only [homogeneousTransposeTerm, LinearMap.smul_apply, LinearMap.comp_apply,
      tail, map_zero, smul_zero]
    change K_L D hu e x y (carrierBasis D (c,mon)) -
      homogeneousTranspose D hu d e x y (carrierBasis D (c,mon)) = 0
    apply sub_eq_zero.mpr
    rw [finiteR]
    simp only [carrierBasis_apply]
    change actualForm D hu
      ((correctedField D hu (Finsupp.single c (MvPolynomial.monomial mon 1))).coeff e x) y = _
    rw [inversion, phase, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ell hell
    simp only [homogeneousTransposeTerm, LinearMap.smul_apply, LinearMap.comp_apply,
      originalL1, SourceMobius.sugawara_pow_single D _ hHG hGH,
      ← Finsupp.smul_single, map_smul, Pi.smul_apply, smul_eq_mul]
    have exponent : -e-2*chargeNorm D c-4*(R : ℤ)+2*(ell : ℤ) = -e-4*d+2*(ell : ℤ) := by
      omega
    rw [exponent]
    simp only [K_R, LinearMap.coe_mk, AddHom.coe_mk, div_eq_mul_inv, mul_assoc]
  exact sub_eq_zero.mp (span ha)

open private A S ad dividedAd homogeneous c
  from D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder

private theorem one_sided_divided_ad (D : LatticeData) (hu : IsUnit D.G.det)
    (q : ℕ) (e : ℤ) (a : Carrier D) :
    ((q.factorial : ℂ)⁻¹) • (T D hu ^ q * A D hu e a) =
      ∑ i ∈ Finset.range (q+1), ((i.factorial : ℂ)⁻¹) •
        (dividedAd D hu (q-i) e a * T D hu ^ i) := by
  let R := LinearMap.mulRight ℂ (T D hu)
  have commute : Commute (ad D hu) R := by
    change (_ - R) * R = R * (_ - R)
    rw [sub_mul, mul_sub, (LinearMap.commute_mulLeft_right
      (R := ℂ) (T D hu) (T D hu)).eq]
  have split : ad D hu + R = LinearMap.mulLeft ℂ (T D hu) := by
    dsimp [ad, R]
    module
  have expansion := congrArg (fun F : Module.End ℂ (Module.End ℂ (ActualTensor D hu)) =>
    F (A D hu e a)) (commute.symm.add_pow q)
  rw [add_comm R, split, LinearMap.pow_mulLeft] at expansion
  dsimp only [R] at expansion
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.natCast_apply,
    LinearMap.pow_mulRight, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    ← Nat.cast_smul_eq_nsmul ℂ] at expansion
  rw [expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have bound : i ≤ q := by have := Finset.mem_range.mp hi; omega
  simp only [dividedAd, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, Algebra.smul_mul_assoc, smul_smul]
  rw [Nat.cast_choose ℂ bound]
  congr 1
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hqi : ((q-i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (q-i)
  field_simp

private theorem lowering_field_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (a : Carrier D) (ha : a ∈ grade D d)
    (q : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    ((q.factorial : ℂ)⁻¹) • (T D hu ^ q) ((correctedField D hu a).coeff e x) =
      ∑ i ∈ Finset.range (q+1), ∑ ell ∈ Finset.range (q-i+1),
        (Ring.choose (2*(d : ℂ)+(e : ℂ)/2-(ell : ℂ)-1) (q-i-ell) /
          ((i.factorial : ℂ)*(ell.factorial : ℂ))) •
        (correctedField D hu ((originalL1 D ^ ell) a)).coeff
          (e-2*((q-i : ℕ) : ℤ)+2*(ell : ℤ)) ((T D hu ^ i) x) := by
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  have eigen : S D 0 a = (d : ℂ) • a :=
    (actualL0_eigen_iff_grade D _ hHG hGH d a).mpr ha
  have expansion := LinearMap.congr_fun (one_sided_divided_ad D hu q e a) x
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sum_apply] at expansion
  simp only [A, LinearMap.comp_apply, LinearMap.proj_apply] at expansion
  rw [expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [homogeneous D hu d a eigen (q-i) e]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [c, ite_eq_left (by have := Finset.mem_range.mp hell; omega)]
  simp only [smul_smul]
  have arg : 2*(d : ℂ)+(e : ℂ)/2-1-(ell : ℂ) =
      2*(d : ℂ)+(e : ℂ)/2-(ell : ℂ)-1 := by ring
  rw [arg]
  congr 1
  ring

set_option backward.isDefEq.respectTransparency true in
/-- The lowering and inversion needed in the mixed coefficient calculation,
with both actual input slots retained. Every outer index is a finite triangle;
the inner source sum is finite by actual original-source nilpotence. -/
theorem lowered_field_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (d : ℤ) (a : Carrier D) (ha : a ∈ grade D d)
    (q : ℕ) (e : ℤ) (x y : ActualTensor D hu) :
    ((q.factorial : ℂ)⁻¹) *
        actualForm D hu ((T D hu ^ q) ((correctedField D hu a).coeff e x)) y =
      ∑ i ∈ Finset.range (q+1), ∑ ell ∈ Finset.range (q-i+1),
        (Ring.choose (2*(d : ℂ)+(e : ℂ)/2-(ell : ℂ)-1) (q-i-ell) /
          ((i.factorial : ℂ)*(ell.factorial : ℂ))) *
        (∑ᶠ k : ℕ, (((-1 : ℂ)^(d-(ell : ℤ)))/(k.factorial : ℂ)) *
          actualForm D hu ((T D hu ^ i) x)
            ((correctedField D hu ((originalL1 D ^ (k+ell)) a)).coeff
              (-e-4*d+2*((q-i : ℕ) : ℤ)+2*((k+ell : ℕ) : ℤ)) y)) := by
  have expansion := congrArg (fun v : ActualTensor D hu => actualForm D hu v y)
    (lowering_field_expansion D hu d a ha q e x)
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at expansion
  rw [expansion]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro ell hell
  rw [actual_homogeneous_transpose D hu (d-(ell : ℤ))
    (e-2*((q-i : ℕ) : ℤ)+2*(ell : ℤ)) ((originalL1 D ^ ell) a)
    (original_l1_grade D hu d a ha ell) ((T D hu ^ i) x) y]
  refine congrArg (fun z : ℂ =>
    (Ring.choose (2*(d : ℂ)+(e : ℂ)/2-(ell : ℂ)-1) (q-i-ell) /
      ((i.factorial : ℂ)*(ell.factorial : ℂ))) * z) ?_
  apply finsum_congr
  intro k
  have exponent : -(e-2*((q-i : ℕ) : ℤ)+2*(ell : ℤ))-
      4*(d-(ell : ℤ))+2*(k : ℤ) =
      -e-4*d+2*((q-i : ℕ) : ℤ)+2*((k+ell : ℕ) : ℤ) := by
    push_cast
    ring
  have source : (originalL1 D ^ k) ((originalL1 D ^ ell) a) =
      (originalL1 D ^ (k+ell)) a := by
    rw [pow_add, Module.End.mul_apply]
  rw [exponent, source]

open private binomial_reflection
  from D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder

private theorem mixed_signed_diagonal (x y : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), Ring.choose x j * (-1 : ℂ)^(k-j) *
      Ring.choose (y-(j : ℂ)) (k-j)) =
      (-1 : ℂ)^k * Ring.choose (y-x) k := by
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := x) (s := -y+(k : ℂ)-1) k (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  calc
    _ = ∑ j ∈ Finset.range (k+1),
        Ring.choose x j * Ring.choose (-y+(k : ℂ)-1) (k-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have bound : j ≤ k := by have := Finset.mem_range.mp hj; omega
      rw [mul_assoc, binomial_reflection]
      congr 2
      rw [Nat.cast_sub bound]
      ring
    _ = Ring.choose (x+(-y+(k : ℂ)-1)) k := vandermonde.symm
    _ = _ := by
      rw [binomial_reflection]
      congr 1
      ring

private theorem signed_supported_transform (R : ℕ) (f : ℕ → ℂ)
    (tail : ∀ k, R ≤ k → f k = 0) (x y : ℂ) :
    (∑ j ∈ Finset.range R, ∑ h ∈ Finset.range R,
      Ring.choose x j * (-1 : ℂ)^h * Ring.choose (y-(j : ℂ)) h * f (j+h)) =
      ∑ k ∈ Finset.range R,
        ((-1 : ℂ)^k * Ring.choose (y-x) k) * f k := by
  calc
    _ = ∑ j ∈ Finset.range R, ∑ h ∈ Finset.range (R-j),
        Ring.choose x j * (-1 : ℂ)^h * Ring.choose (y-(j : ℂ)) h * f (j+h) := by
      apply Finset.sum_congr rfl
      intro j hj
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
      intro h hh outside
      rw [tail (j+h) (by have := Finset.mem_range.not.mp outside; omega), mul_zero]
    _ = ∑ k ∈ Finset.range R, ∑ j ∈ Finset.range (k+1),
        Ring.choose x j * (-1 : ℂ)^(k-j) *
          Ring.choose (y-(j : ℂ)) (k-j) * f k := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (by have := Finset.mem_range.mp hj; omega)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_mul, mixed_signed_diagonal]

private def orderedCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (e : ℤ) (u : ActualTensor D hu) : ℕ :=
  (e-((HahnModule.of ℂ).symm ((correctedField D hu a) u)).order).toNat+1

private theorem ordered_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (e f : ℤ) (u v : ActualTensor D hu) (k : ℕ)
    (hk : orderedCutoff D hu a e u ≤ k) :
    actualForm D hu v
      ((correctedField D hu b).coeff (f+2*(k : ℤ))
        ((correctedField D hu a).coeff (e-2*(k : ℤ)) u)) = 0 := by
  have zero : (correctedField D hu a).coeff (e-2*(k : ℤ)) u = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_order
    dsimp [orderedCutoff] at hk
    omega
  rw [zero, map_zero, map_zero]

/-- Signed triangular transport of an actual ordered product. Finiteness is
established from the actual rightmost field applied to the actual input before
using (j,h) -> (k=j+h,j). Both binomial parameters may be negative. -/
theorem ordered_signed_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (e f : ℤ) (u v : ActualTensor D hu) (x y : ℂ) :
    let R := orderedCutoff D hu a e u
    (∑ j ∈ Finset.range R, ∑ h ∈ Finset.range R,
      (Ring.choose x j * (-1 : ℂ)^h * Ring.choose (y-(j : ℂ)) h) *
        actualForm D hu v ((correctedField D hu b).coeff (f+2*((j+h : ℕ) : ℤ))
          ((correctedField D hu a).coeff (e-2*((j+h : ℕ) : ℤ)) u))) =
      ∑ k ∈ Finset.range R,
        ((-1 : ℂ)^k * Ring.choose (y-x) k) *
          actualForm D hu v ((correctedField D hu b).coeff (f+2*(k : ℤ))
            ((correctedField D hu a).coeff (e-2*(k : ℤ)) u)) := by
  intro R
  exact signed_supported_transform R _ (ordered_tail D hu a b e f u v) x y

open private vacuum_coeff
  from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open private basis_parity
  from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private theorem weight_two_vacuum_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (2 : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (2 : ℂ) • v.val)
    (a : fixedGrade D 0) (ha : a.val = vacuum D) :
    normalizedCoefficient D hu 3 u v 0 a = actualForm D hu v.val u.val := by
  rw [normalizedCoefficient_pairing D hu h24 2 2 3 u v huH hvK]
  simp only [show (2 : ℕ)-1 = 1 by decide, Finset.sum_range_one,
    Nat.cast_zero, Nat.cast_ofNat, pow_zero, Module.End.one_apply,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_one, ha]
  norm_num only
  rw [vacuum_coeff]
  norm_num

/-- A nonzero normalized vacuum channel on the actual Golay Leech lattice,
at standard mode I_3 and actual twisted weight two. The original ordered
bilinear form is used; no positive form or symmetry premise is introduced. -/
theorem actual_leech_vacuum_channel :
    ∃ (D : LatticeData)
      (e : Charge D ≃ₗ[ℤ] D5.S3.Arith.Lattices.Golay.RealLeech.lattice)
      (hu : IsUnit D.G.det),
      D.rank = 24 ∧ Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) ∧
      (∀ a c : Charge D, (bilinear D a c : ℝ) =
        D5.S3.Arith.Lattices.Golay.RealLeech.pairing (e a) (e c)) ∧
      ∃ (a : fixedGrade D 0) (u v : paritySpace D hu (-1)),
        a.val = vacuum D ∧
        actualTensorL0 D hu u.val = (2 : ℂ) • u.val ∧
        actualTensorL0 D hu v.val = (2 : ℂ) • v.val ∧
        normalizedCoefficient D hu 3 u v 0 a = actualForm D hu v.val u.val ∧
        normalizedCoefficient D hu 3 u v 0 a ≠ 0 := by
  classical
  obtain ⟨D,e,h24,hu,hpos,hpair⟩ :=
    D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  let b := actualAmbientBasis D hu
  let i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) :=
    (Finsupp.single (⟨0, by omega⟩,0) 1, 0)
  have iw : oddWeight D i.1 = 1 := by
    simp [i, oddWeight, Finsupp.weight_single, LatticeHalfFockChargedCoefficients.omega]
  have ui : actualTensorL0 D hu (b i) = (2 : ℂ) • b i := by
    rw [actual_basis_eigenvalue, iw]
    have scalar : (D.rank : ℂ)/16 + (1 : ℂ)/2 = 2 := by rw [h24]; norm_num
    simp only [Nat.cast_one]
    rw [scalar]
  have detects : ∃ x : ActualTensor D hu, actualForm D hu x (b i) ≠ 0 := by
    by_contra absent
    push Not at absent
    exact b.ne_zero i ((actualForm_nondegenerate D hu).2 _ absent)
  obtain ⟨x,hx⟩ := detects
  have detects_basis : ∃ j, actualForm D hu (b j) (b i) ≠ 0 := by
    by_contra absent
    push Not at absent
    apply hx
    rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    simp [absent]
  obtain ⟨j,hj⟩ := detects_basis
  have jw : oddWeight D j.1 = 1 := by
    by_contra different
    apply hj
    apply actualForm_oddGrade_orthogonal D hu (oddWeight D j.1) 1 (b j) (b i)
    · simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu j.1 j.2
    · simpa [iw] using actual_basis_eigenvalue D hu i.1 i.2
    · exact_mod_cast different
  have vj : actualTensorL0 D hu (b j) = (2 : ℂ) • b j := by
    rw [actual_basis_eigenvalue, jw]
    have scalar : (D.rank : ℂ)/16 + (1 : ℂ)/2 = 2 := by rw [h24]; norm_num
    simp only [Nat.cast_one]
    rw [scalar]
  have iparity : b i ∈ paritySpace D hu (-1) := by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simpa only [iw, pow_one] using basis_parity D hu i
  have jparity : b j ∈ paritySpace D hu (-1) := by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simpa only [jw, pow_one] using basis_parity D hu j
  have avac : vacuum D ∈ fixedGrade D 0 := by
    constructor
    · rw [grade_zero D hpos]
      exact Submodule.subset_span (by simp)
    · exact (mem_fixedSpace D _).mpr (theta_vacuum D)
  let a : fixedGrade D 0 := ⟨vacuum D,avac⟩
  let u : paritySpace D hu (-1) := ⟨b i,iparity⟩
  let v : paritySpace D hu (-1) := ⟨b j,jparity⟩
  have evaluation := weight_two_vacuum_pairing D hu h24 u v ui vj a rfl
  refine ⟨D,e,hu,h24,hpos,hpair,a,u,v,rfl,ui,vj,evaluation,?_⟩
  rw [evaluation]
  exact hj


open private homogeneous_coefficient ambientCoefficient liftGrade kernel oppositePull
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

set_option backward.isDefEq.respectTransparency true in
private theorem normalized_opposite_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k d t E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = ((H : ℤ)+(K : ℤ)-k-1)+d-t-1) (b : fixedGrade D E) :
    (oppositeAction D hu hD t (⟨a.val,a.property.2⟩ : FixedCarrier D)
      (normalizedCoefficient D hu k u v)) E b =
    ∑ ell ∈ Finset.range (a.val.support.sup
        (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))+1),
      (((-1 : ℂ)^d)/(ell.factorial : ℂ)) *
      (∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
        let s : ℤ := k+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
        (((-1 : ℂ)^((H : ℤ)+s))/((p.factorial : ℂ)*(q.factorial : ℂ))) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu
            (((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-t-2]]) b.val)).coeff
              (2*s) ((T D hu ^ q) u.val))) := by
  subst E
  rw [oppositeAction_homogeneous]
  change (oppositeHomogeneous D hu hD d t a
    (ambientCoefficient D hu k u.val v.val)) _ b = _
  rw [homogeneous_coefficient D hu h24 H K k u.val v.val huH hvK]
  change ((DirectSum.toModule ℂ ℤ (FixedRestrictedDual D)
    (fun e => (DirectSum.lof ℂ ℤ (fun f => Module.Dual ℂ (fixedGrade D f))
      (e+d-t-1)).comp (oppositeDualMode D hu hD d t a e)))
    (DirectSum.lof ℂ ℤ (fun f => Module.Dual ℂ (fixedGrade D f))
      ((H : ℤ)+(K : ℤ)-k-1)
      ((fixedGrade D ((H : ℤ)+(K : ℤ)-k-1)).dualRestrict
        (kernel D hu H K k u.val v.val)))) _ b = _
  rw [DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
  change kernel D hu H K k u.val v.val
    ((oppositeMode D hu hD d t a (((H : ℤ)+(K : ℤ)-k-1)+d-t-1) b).val) = _
  change kernel D hu H K k u.val v.val
    (∑ ell ∈ Finset.range (a.val.support.sup
      (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))+1),
      (((-1 : ℂ)^d)/(ell.factorial : ℂ)) •
        (((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-t-2]]) b.val)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul]
  simp only [smul_eq_mul, kernel, LinearMap.sum_apply, LinearMap.smul_apply, K_R,
    LinearMap.coe_mk, AddHom.coe_mk]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Evaluation of the entire first dual-action branch of the signed mixed
identity on its actual fixed target grade. The outer cutoff follows from the
normalized field's sharp energy truncation; source lowering uses its original
finite monomial bound. All mode labels are standard signed modes. -/
theorem mixed_first_branch_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (d m n r E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hE : E = (H : ℤ)+(K : ℤ)+d-m-n-r-2) (b : fixedGrade D E) :
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) E b =
    ∑ j ∈ Finset.range (((H : ℤ)+(K : ℤ)-n).toNat+1),
      (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) *
      (∑ ell ∈ Finset.range (a.val.support.sup
        (fun c => MvPolynomial.weightedTotalDegree (sourceWeight D) (a.val c))+1),
        (((-1 : ℂ)^d)/(ell.factorial : ℂ)) *
        (∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (H-1),
          let s : ℤ := n+(j : ℤ)+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
          (((-1 : ℂ)^((H : ℤ)+s))/((p.factorial : ℂ)*(q.factorial : ℂ))) *
          actualForm D hu ((T D hu ^ p) v.val)
            ((correctedField D hu
              (((Y D ((originalL1 D ^ ell) a.val))[[2*d-(ell : ℤ)-m-r+(j : ℤ)-2]])
                b.val)).coeff (2*s) ((T D hu ^ q) u.val)))) := by
  classical
  let J := ((H : ℤ)+(K : ℤ)-n).toNat+1
  have finite : (∑ᶠ j : ℕ, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v)) =
      ∑ j ∈ Finset.range J, (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have bound : J ≤ j := by simpa using outside
    have zero := normalizedCoefficient_homogeneous_truncation D hu hD h24 H K
      (n+(j : ℤ)) u v huH hvK (by dsimp [J] at bound; omega)
    apply hj
    change (((-1 : ℂ)^j)*Ring.choose (r : ℂ) j) •
      oppositeAction D hu hD (m+r-(j : ℤ))
        (⟨a.val,a.property.2⟩ : FixedCarrier D)
        (normalizedCoefficient D hu (n+(j : ℤ)) u v) = 0
    rw [zero, map_zero, smul_zero]
  rw [finite]
  simp only [DirectSum.sum_apply, LinearMap.sum_apply, DirectSum.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have branch := normalized_opposite_pairing D hu hD h24 H K (n+(j : ℤ)) d
    (m+r-(j : ℤ)) E a u v huH hvK (by rw [hE]; ring) b
  have mode (ell : ℕ) : 2*d-(ell : ℤ)-(m+r-(j : ℤ))-2 =
      2*d-(ell : ℤ)-m-r+(j : ℤ)-2 := by ring
  simp_rw [mode] at branch
  rw [branch]


set_option backward.isDefEq.respectTransparency true in
private theorem fixed_mode_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (K W : ℕ) (d l : ℤ) (a : fixedGrade D d) (v : paritySpace D hu (-1))
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hW : (W : ℤ) = (K : ℤ)+d-l-1) :
    actualTensorL0 D hu
      (((fixedParitySlice D hu (-1) (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) v).val =
    (W : ℂ) •
      (((fixedParitySlice D hu (-1) (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) v).val := by
  have value :
      (((fixedParitySlice D hu (-1) (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) v).val =
        (correctedField D hu a.val).coeff (-2*l-2) v.val := by
    change (correctedField D hu a.val).coeff (2*(-l-1)) v.val = _
    rw [show 2*(-l-1) = -2*l-2 by ring]
  rw [value]
  have cov := LinearMap.congr_fun
    (correctedField_L_zero_commutator D hu d a.val a.property.1 (-2*l-2)) v.val
  change actualTensorL0 D hu ((correctedField D hu a.val).coeff (-2*l-2) v.val) -
    (correctedField D hu a.val).coeff (-2*l-2) (actualTensorL0 D hu v.val) =
    (((-2*l-2 : ℤ) : ℂ)/2+(d : ℂ)) •
      (correctedField D hu a.val).coeff (-2*l-2) v.val at cov
  rw [hvK, map_smul, sub_eq_iff_eq_add] at cov
  rw [cov, ← add_smul]
  congr 1
  have weights : (W : ℂ) = (K : ℂ)+(d : ℂ)-(l : ℂ)-1 := by exact_mod_cast hW
  push_cast
  linear_combination -weights

set_option backward.isDefEq.respectTransparency true in
/-- The normalized coefficient with an actual fixed-source mode acting in
its second twisted input. The transformed input's energy is derived from
actual zero-mode covariance. Lowering and transpose expand on the unchanged
ordered bilinear form, with a genuinely finite original-source inner sum. -/
theorem mixed_second_input_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K W : ℕ) (d k l E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hW : (W : ℤ) = (K : ℤ)+d-l-1) (b : fixedGrade D E) :
    normalizedCoefficient D hu k u
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) v) E b =
    ∑ p ∈ Finset.range (W-1), ∑ q ∈ Finset.range (H-1),
      let s : ℤ := k+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
      (((-1 : ℂ)^((H : ℤ)+s))/(q.factorial : ℂ)) *
      (∑ i ∈ Finset.range (p+1), ∑ ell ∈ Finset.range (p-i+1),
        (Ring.choose (2*(d : ℂ)-(l : ℂ)-(ell : ℂ)-2) (p-i-ell) /
          ((i.factorial : ℂ)*(ell.factorial : ℂ))) *
        (∑ᶠ z : ℕ, (((-1 : ℂ)^(d-(ell : ℤ)))/(z.factorial : ℂ)) *
          actualForm D hu ((T D hu ^ i) v.val)
            ((correctedField D hu ((originalL1 D ^ (z+ell)) a.val)).coeff
              (2*l+2-4*d+2*((p-i : ℕ) : ℤ)+2*((z+ell : ℕ) : ℤ))
              ((correctedField D hu b.val).coeff (2*s) ((T D hu ^ q) u.val))))) := by
  let w := ((fixedParitySlice D hu (-1)
    (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) v
  have value : w.val = (correctedField D hu a.val).coeff (-2*l-2) v.val := by
    change (correctedField D hu a.val).coeff (2*(-l-1)) v.val = _
    rw [show 2*(-l-1) = -2*l-2 by ring]
  have energy := fixed_mode_energy D hu K W d l a v hvK hW
  rw [normalizedCoefficient_pairing D hu h24 H W k u w huH energy]
  simp only [value]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  let s : ℤ := k+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
  have expansion := lowered_field_transpose D hu d a.val a.property.1 p (-2*l-2)
    v.val ((correctedField D hu b.val).coeff (2*s) ((T D hu ^ q) u.val))
  have parameter (ell : ℕ) :
      2*(d : ℂ)+((-2*l-2 : ℤ) : ℂ)/2-(ell : ℂ)-1 =
        2*(d : ℂ)-(l : ℂ)-(ell : ℂ)-2 := by push_cast; ring
  have exponent (i z ell : ℕ) :
      -(-2*l-2)-4*d+2*((p-i : ℕ) : ℤ)+2*((z+ell : ℕ) : ℤ) =
        2*l+2-4*d+2*((p-i : ℕ) : ℤ)+2*((z+ell : ℕ) : ℤ) := by ring
  simp_rw [parameter, exponent] at expansion
  calc
    _ = (((-1 : ℂ)^((H : ℤ)+s))/(q.factorial : ℂ)) *
        (((p.factorial : ℂ)⁻¹) * actualForm D hu
          ((T D hu ^ p) ((correctedField D hu a.val).coeff (-2*l-2) v.val))
          ((correctedField D hu b.val).coeff (2*s) ((T D hu ^ q) u.val))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [expansion]


set_option backward.isDefEq.respectTransparency true in
/-- The normalized coefficient with an actual fixed-source mode acting in
its first twisted input. Actual covariance determines the signed output energy;
one-sided lowering retains the complete finite triangle of source powers and
lowered actual inputs. No iterate law is assumed. -/
theorem mixed_first_input_pairing (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K W : ℕ) (d k l E : ℤ) (a : fixedGrade D d)
    (u v : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hW : (W : ℤ) = (H : ℤ)+d-l-1) (b : fixedGrade D E) :
    normalizedCoefficient D hu k
      (((fixedParitySlice D hu (-1)
        (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) u) v E b =
    ∑ p ∈ Finset.range (K-1), ∑ q ∈ Finset.range (W-1),
      let s : ℤ := k+1-(p : ℤ)-2*(W : ℤ)+(q : ℤ)
      (((-1 : ℂ)^((W : ℤ)+s))/(p.factorial : ℂ)) *
      (∑ i ∈ Finset.range (q+1), ∑ ell ∈ Finset.range (q-i+1),
        (Ring.choose (2*(d : ℂ)-(l : ℂ)-(ell : ℂ)-2) (q-i-ell) /
          ((i.factorial : ℂ)*(ell.factorial : ℂ))) *
        actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff (2*s)
            ((correctedField D hu ((originalL1 D ^ ell) a.val)).coeff
              (-2*l-2-2*((q-i : ℕ) : ℤ)+2*(ell : ℤ)) ((T D hu ^ i) u.val)))) := by
  let w := ((fixedParitySlice D hu (-1)
    (⟨a.val,a.property.2⟩ : FixedCarrier D))[[l]]) u
  have value : w.val = (correctedField D hu a.val).coeff (-2*l-2) u.val := by
    change (correctedField D hu a.val).coeff (2*(-l-1)) u.val = _
    rw [show 2*(-l-1) = -2*l-2 by ring]
  have energy := fixed_mode_energy D hu H W d l a u huH hW
  rw [normalizedCoefficient_pairing D hu h24 W K k w v energy hvK]
  simp only [value]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  let s : ℤ := k+1-(p : ℤ)-2*(W : ℤ)+(q : ℤ)
  let F : Module.Dual ℂ (ActualTensor D hu) :=
    (actualForm D hu ((T D hu ^ p) v.val)).comp ((correctedField D hu b.val).coeff (2*s))
  have expansion := congrArg F (lowering_field_expansion D hu d a.val a.property.1 q
    (-2*l-2) u.val)
  simp only [map_smul, map_sum, smul_eq_mul, F, LinearMap.comp_apply] at expansion
  have parameter (ell : ℕ) :
      2*(d : ℂ)+((-2*l-2 : ℤ) : ℂ)/2-(ell : ℂ)-1 =
        2*(d : ℂ)-(l : ℂ)-(ell : ℂ)-2 := by push_cast; ring
  simp_rw [parameter] at expansion
  calc
    _ = (((-1 : ℂ)^((W : ℤ)+s))/(p.factorial : ℂ)) *
        (((q.factorial : ℂ)⁻¹) * actualForm D hu ((T D hu ^ p) v.val)
          ((correctedField D hu b.val).coeff (2*s)
            ((T D hu ^ q) ((correctedField D hu a.val).coeff (-2*l-2) u.val)))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [expansion]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
