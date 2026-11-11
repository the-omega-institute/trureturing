/- GID: D5/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Energy/LatticeCosetCompressedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual compressed signed modes preserve the intrinsic rational energy with the Schur shift. -/
/- Delivery scope and attribution: the supplied native import-to-EOF proof
source is preserved exactly. Source export SHA256 06bff7ca57e6a16b2380849110c31102a078d4ae273a65d66e6695c84d91e910.
proof_shape: content for actual_compressed_mode_grade and actual_scalar_numerator;
all private normalization/decomposition helpers are consumed on their live paths.
admission_basis: escape-witness. Actual injection/projection oscillator support
and the unreduced Schur charge-energy shift give signed compressed grading;
finite homogeneous input decompositions and finite output-weight tests then
compute the exact binary H/Psi degree support and unique scalar polynomials.
The existing scalar extraction supplier is reused rather than reimplemented.
utility: none: these are general symbolic algebraic results over arbitrary
original states, ranks including zero, matrices B and symmetric-even C, and
signed modes/cutoffs; no bounded enumeration, checker, numerical reduction or
certified finite instance is delivered. Only the original Gram is positive.
The actual fields, projection, injection and half-diagonal cocycle are retained.
No ambient positivity, analytic sewing, category, string or AdS/CFT completion
is claimed. Imported suppliers retain their attribution; no literature-priority
claim is made. The Blueprint mirror is produced by make emit. No separate
experimental artifact is specified; mirror-E uses the canonical route's
formal-manifest representation, not an escape-audit exemption.
The bounded typed source-family audit is incomplete: rejected interventions,
readout sensitivity, observational dependence and exact raw occurrence binding
remain unproved. Failed Reg attempts are excluded from retained targets.
Details: https://github.com/the-omega-institute/trureturing/issues/29386.
No Contract registration or declared_validated status is claimed. -/

import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetGrading
import D5.S3.VertexAlgebra.Sewing.CompressedOccupation
import D5.S3.VertexAlgebra.Sectors.LatticeCosetChargedJacobi
import Batteries.Tactic.OpenPrivate

/-!
The ambient energy used here is combinatorial.
Only the original Gram form is positive definite. In particular this file
does not construct, or assume, an inverse of the ambient Gram form.

The literal injection and projection are treated on the full monomial basis.
The projection support is supplied by the already checked frequency-preserving
transpose substitution, applied to the CONJUGATE TRANSPOSE matrix. No adjoint
identity is postulated. The resulting mode grade is consumed by the actual
scalar numerator proof in Sectors/LatticeCosetScalarNumerator. The existing
LatticeDualCosetEnergy.moduleL_eigen_iff identifies rationalGrade with the
actual original-omega eigenspace; shift_dual below supplies its duality
condition for beta=B*a. No renamed eigen-identification wrapper is added.

All statements quantify over both zero ranks, arbitrary B, symmetric even C,
all signed modes and the entire original carrier. There is no C comparison:
fixed integer modes are C dependent. The retained Schur correction includes
the external C term, and the original half-diagonal cocycle is unchanged.

Admission: the support transfer and its numerator consumer are the proposed
mathematical increment; normalization helpers below are consumed helpers,
not independent deliverables. No finite-instance computation is involved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCompressedEnergy

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeCosetCompression LatticeDualCosetEnergy MvPolynomial
open LatticeDiscriminantTheta (gramReal)
open scoped BigOperators VertexOperator

noncomputable section

open private coefficientGrade coefficient_mem from
  D5.S3.VertexAlgebra.Sectors.LatticeDualCosetGrading
open private gram_longitudinal injection_single projection_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
-- Only the algebraic symmetry helper is used, never charged_borcherds.
open private schur_swap from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetChargedJacobi

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ)
variable (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

local notation "E" => ambient D e B C hC hCe

/-- The original-module momentum shift P*a, where P=G^{-1}B. -/
def moduleShift (a : Fin e → ℤ) : Fin D.rank → ℚ :=
  Matrix.mulVec (longitudinal D B) (fun j => (a j : ℚ))

private def sigma (a : Fin e → ℤ) : ℚ := schur D B C a a / 2

private theorem shift_dual (hD : (gramReal D).PosDef) (a : Fin e → ℤ)
    (i : Fin D.rank) :
    ∑ j, (D.G i j : ℚ) * moduleShift D B a j =
      ((Matrix.mulVec B a i : ℤ) : ℚ) := by
  classical
  simp only [moduleShift, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, gram_longitudinal D B hD]
  simp [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

include hC in
private theorem sigma_add (a b : Fin e → ℤ) :
    sigma D B C (a+b) = sigma D B C a + sigma D B C b + schur D B C a b := by
  have h : schur D B C (a+b) (a+b) =
      schur D B C a a + schur D B C a b +
        schur D B C b a + schur D B C b b := by
    simp only [schur, Pi.add_apply, Int.cast_add, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring
  unfold sigma
  rw [h, schur_swap D B C hC a b]
  ring

private theorem charge_shift (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) :
    (chargeEnergy E (liftCharge D B C hC hCe a n) : ℚ) =
      chargeWeight D (moduleShift D B a) n + sigma D B C a := by
  classical
  let mixed : ℚ := ((∑ i, n i * Matrix.mulVec B a i : ℤ) : ℚ)
  let ext : ℚ := ∑ j, ∑ k, (a j : ℚ) * (C j k : ℚ) * (a k : ℚ)
  have cross : (∑ j, ∑ i, (a j : ℚ) * (B i j : ℚ) * (n i : ℚ)) =
      ∑ i, ∑ j, (n i : ℚ) * (B i j : ℚ) * (a j : ℚ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have block : (bilinear E (liftCharge D B C hC hCe a n)
      (liftCharge D B C hC hCe a n) : ℚ) =
        (bilinear D n n : ℚ) + 2*mixed + ext := by
    simp only [bilinear, liftCharge, ambient, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, Int.cast_add, Int.cast_sum,
      Int.cast_mul, Finset.sum_add_distrib]
    dsimp only [mixed, ext]
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    rw [cross]
    ring_nf
    simp only [← Finset.sum_mul]
    ring
  have norm : pairing D (moduleShift D B a) (moduleShift D B a) =
      ∑ i, moduleShift D B a i * ((Matrix.mulVec B a i : ℤ) : ℚ) := by
    unfold pairing
    simp_rw [mul_assoc, ← Finset.mul_sum, shift_dual D B hD a]
  have contraction :
      (∑ j, ∑ k, (a j : ℚ) *
        (∑ i, (B i j : ℚ) * longitudinal D B i k) * (a k : ℚ)) =
      ∑ i, moduleShift D B a i * ((Matrix.mulVec B a i : ℤ) : ℚ) := by
    calc
      _ = ∑ j, ∑ k, ∑ i, (a j : ℚ) *
          ((B i j : ℚ) * longitudinal D B i k) * (a k : ℚ) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k, ∑ i, ∑ j, (a j : ℚ) *
          ((B i j : ℚ) * longitudinal D B i k) * (a k : ℚ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ k, ∑ j, (a j : ℚ) *
          ((B i j : ℚ) * longitudinal D B i k) * (a k : ℚ) :=
        Finset.sum_comm
      _ = _ := by
        simp only [moduleShift, Matrix.mulVec, dotProduct, Int.cast_sum,
          Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have sch : schur D B C a a =
      ext - pairing D (moduleShift D B a) (moduleShift D B a) := by
    rw [norm]
    simp only [schur, ext, sub_mul, mul_sub, Finset.sum_sub_distrib,
      contraction]
  have eh : (2 : ℚ) * (chargeEnergy E (liftCharge D B C hC hCe a n) : ℚ) =
      (bilinear E (liftCharge D B C hC hCe a n)
        (liftCharge D B C hC hCe a n) : ℚ) := by
    exact_mod_cast two_chargeEnergy E (liftCharge D B C hC hCe a n)
  have en : (2 : ℚ) * (chargeEnergy D n : ℚ) = (bilinear D n n : ℚ) := by
    exact_mod_cast two_chargeEnergy D n
  have hw := chargeWeight_expansion D (Matrix.mulVec B a) (moduleShift D B a)
    (shift_dual D B hD a) n
  have hz : chargeWeight D (moduleShift D B a) 0 =
      pairing D (moduleShift D B a) (moduleShift D B a) / 2 := by
    simp [chargeWeight]
  rw [block] at eh
  rw [hw, hz]
  unfold sigma
  rw [sch]
  dsimp only [mixed] at eh
  linear_combination (eh-en)/2

private theorem reconstruct_charge (n : Charge E) :
    liftCharge D B C hC hCe (externalCharge D B C hC hCe n)
      (oldCharge D B C hC hCe n) = n := by
  ext i
  induction i using Fin.addCases <;>
    simp [liftCharge, oldCharge, externalCharge]

private theorem coefficient_span (A : LatticeData) (w : Label A → ℚ) (h : ℚ) :
    coefficientGrade A w h =
      Submodule.span ℂ (carrierBasis A '' {t : Label A | w t = h}) := by
  ext v
  change ((carrierCoeffEquiv A v).support : Set (Label A)) ⊆ {t | w t = h} ↔ _
  exact (carrierBasis A).mem_span_image.symm

private theorem coefficient_basis (A : LatticeData) (w : Label A → ℚ)
    (t : Label A) : carrierBasis A t ∈ coefficientGrade A w (w t) := by
  rw [coefficient_span]
  exact Submodule.subset_span ⟨t, rfl, rfl⟩

private theorem map_coefficient_grade (A F : LatticeData)
    (w : Label A → ℚ) (z : Label F → ℚ) (h k : ℚ)
    (f : Carrier A →ₗ[ℂ] Carrier F)
    (basis : ∀ t, w t = h → f (carrierBasis A t) ∈ coefficientGrade F z k)
    (v : Carrier A) (hv : v ∈ coefficientGrade A w h) :
    f v ∈ coefficientGrade F z k := by
  rw [coefficient_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact basis t ht
  | zero => simpa using (coefficientGrade F z k).zero_mem
  | add x y hx hy ihx ihy => simpa using (coefficientGrade F z k).add_mem ihx ihy
  | smul c x hx ih => simpa using (coefficientGrade F z k).smul_mem c ih

private abbrev ambientGrade (h : ℚ) : Submodule ℂ (Carrier E) :=
  coefficientGrade E (fun t => (energy E t : ℚ)) h

private theorem integer_grade_rational (A : LatticeData) (n : ℤ)
    (v : Carrier A) (hv : v ∈ grade A n) :
    v ∈ coefficientGrade A (fun t => (energy A t : ℚ)) (n : ℚ) := by
  rw [coefficient_mem]
  intro t ht
  exact (mem_grade_iff A n v).mp hv t (by intro he; apply ht; exact_mod_cast he)

private theorem ambient_mode_grade (h k : ℚ) (u v : Carrier E) (m : ℤ)
    (hu : u ∈ ambientGrade D B C hC hCe h)
    (hv : v ∈ ambientGrade D B C hC hCe k) :
    ((Y E u)[[m]]) v ∈ ambientGrade D B C hC hCe (h+k-(m : ℚ)-1) := by
  classical
  dsimp only [ambientGrade] at hu hv ⊢
  rw [coefficient_span] at hu hv
  induction hu using Submodule.span_induction generalizing v with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    change (energy E s : ℚ) = h at hs
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, ht, rfl⟩ := hy
      change (energy E t : ℚ) = k at ht
      have hg := LatticeCoefficientEnergy.actual_mode_grade E (energy E s) (energy E t)
        m (carrierBasis E s) (carrierBasis E t)
        (by rw [grade_eq_span]; exact Submodule.subset_span ⟨s,rfl,rfl⟩)
        (by rw [grade_eq_span]; exact Submodule.subset_span ⟨t,rfl,rfl⟩)
      have hr := integer_grade_rational E _ _ hg
      simpa only [Int.cast_sub, Int.cast_add, Int.cast_one, hs, ht] using hr
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using
        (ambientGrade D B C hC hCe (h+k-(m : ℚ)-1)).add_mem ihx ihy
    | smul c x hx ih =>
      simpa only [map_smul] using
        (ambientGrade D B C hC hCe (h+k-(m : ℚ)-1)).smul_mem c ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using
      (ambientGrade D B C hC hCe (h+k-(m : ℚ)-1)).add_mem (ihx v hv) (ihy v hv)
  | smul c x hx ih =>
    simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply] using
      (ambientGrade D B C hC hCe (h+k-(m : ℚ)-1)).smul_mem c (ih v hv)

private theorem injection_grade (hD : (gramReal D).PosDef) (a : Fin e → ℤ)
    (h : ℚ) (v : Carrier D) (hv : v ∈ rationalGrade D (moduleShift D B a) h) :
    injection D B C hC hCe a v ∈ ambientGrade D B C hC hCe (h+sigma D B C a) := by
  apply map_coefficient_grade D E (weight D (moduleShift D B a))
    (fun t => (energy E t : ℚ)) h (h+sigma D B C a)
    (injection D B C hC hCe a) ?_ v hv
  rintro ⟨n,d⟩ hd
  rw [carrierBasis_apply, injection_single]
  have hi := CompressedOccupationSewing.injection_basis D B C hC hCe d
  change polynomialInjection D B C hC hCe (monomial d 1) =
    monomial (CompressedOccupationSewing.oldOccupation D B C hC hCe d) 1 at hi
  rw [hi, ← carrierBasis_apply E (liftCharge D B C hC hCe a n,
    CompressedOccupationSewing.oldOccupation D B C hC hCe d)]
  have he : (energy E (liftCharge D B C hC hCe a n,
      CompressedOccupationSewing.oldOccupation D B C hC hCe d) : ℚ) =
        h+sigma D B C a := by
    have hl := CompressedOccupationSewing.oldOccupation_level D B C hC hCe d
    change oscillatorEnergy (CompressedOccupationSewing.oldOccupation D B C hC hCe d) =
      oscillatorEnergy d at hl
    simp only [energy, Int.cast_add, Int.cast_natCast, charge_shift D B C hC hCe hD, hl]
    change (oscillatorEnergy d : ℚ) + chargeWeight D (moduleShift D B a) n = h at hd
    linarith
  rw [← he]
  exact coefficient_basis E _ _

private theorem projection_monomial_energy (d : Exponent E) (t : Exponent D)
    (ht : (polynomialProjection D B C hC hCe (monomial d 1)).coeff t ≠ 0) :
    oscillatorEnergy t = oscillatorEnergy d := by
  let Q := CompressedOccupationSewing.projectionMatrix D B
  let Qstar : Matrix (Fin (D.rank+e)) (Fin D.rank) ℂ := fun j i => star (Q i j)
  have he : polynomialProjection D B C hC hCe =
      LongitudinalFockTranspose.transposeSub Qstar := by
    rw [CompressedOccupationSewing.projection_eq_linearSub D B C hC hCe]
    unfold LongitudinalFockTranspose.transposeSub
    congr 1
    ext i j
    simp [Qstar, Q]
  rw [he] at ht
  exact LongitudinalFockTranspose.transpose_monomial_energy Qstar d ht

private theorem projection_grade (hD : (gramReal D).PosDef) (a : Fin e → ℤ)
    (h : ℚ) (v : Carrier E) (hv : v ∈ ambientGrade D B C hC hCe h) :
    projection D B C hC hCe a v ∈
      rationalGrade D (moduleShift D B a) (h-sigma D B C a) := by
  classical
  apply map_coefficient_grade E D (fun t => (energy E t : ℚ))
    (weight D (moduleShift D B a)) h (h-sigma D B C a)
    (projection D B C hC hCe a) ?_ v hv
  rintro ⟨n,d⟩ hd
  rw [carrierBasis_apply, projection_single]
  split_ifs with hn
  · rw [coefficient_mem]
    rintro ⟨l,t⟩ ht
    change (Finsupp.single (oldCharge D B C hC hCe n)
      (polynomialProjection D B C hC hCe (monomial d 1)) l).coeff t = 0
    by_cases hl : oldCharge D B C hC hCe n = l
    · rw [Finsupp.single_apply, if_pos hl]
      by_contra nonzero
      have lev := projection_monomial_energy D B C hC hCe d t nonzero
      have nc : liftCharge D B C hC hCe a l = n := by
        rw [← hl, ← hn]
        exact reconstruct_charge D B C hC hCe n
      have hc := charge_shift D B C hC hCe hD a l
      rw [nc] at hc
      change ((chargeEnergy E n + (oscillatorEnergy d : ℤ) : ℤ) : ℚ) = h at hd
      simp only [Int.cast_add, Int.cast_natCast] at hd
      apply ht
      unfold weight
      rw [lev]
      linarith
    · simp [hl]
  · exact (rationalGrade D (moduleShift D B a) (h-sigma D B C a)).zero_mem

/-- Actual homogeneous compressed-mode grading, with the unreduced rational
Schur correction. The numerator proof consumes this theorem twice per JP.
There is no ambient positivity, inverse or conformal-operator premise. -/
theorem actual_compressed_mode_grade (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (hu hv : ℚ) (u v : Carrier D) (m : ℤ)
    (hU : u ∈ rationalGrade D (moduleShift D B a) hu)
    (hV : v ∈ rationalGrade D (moduleShift D B b) hv) :
    compressed D B C hC hCe a b u m v ∈
      rationalGrade D (moduleShift D B (a+b))
        (hu+hv-(m : ℚ)-1-schur D B C a b) := by
  have h := ambient_mode_grade D B C hC hCe _ _ _ _ m
    (injection_grade D B C hC hCe hD a hu u hU)
    (injection_grade D B C hC hCe hD b hv v hV)
  have hp := projection_grade D B C hC hCe hD (a+b) _ _ h
  have he : hu+sigma D B C a+(hv+sigma D B C b)-(m : ℚ)-1-
      sigma D B C (a+b) = hu+hv-(m : ℚ)-1-schur D B C a b := by
    rw [sigma_add D B C hC]
    ring
  rw [he] at hp
  exact hp

end
end D5.S3.VertexAlgebra.LatticeCosetCompressedEnergy
