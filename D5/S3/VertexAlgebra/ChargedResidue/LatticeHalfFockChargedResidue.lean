/- GID: D5/S3/VertexAlgebra/ChargedResidue/LatticeHalfFockChargedResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged two-order residue branches and the public all-N source comparison. -/

/- proof_shape: charged_source_comparison: content
   admission_basis: escape-witness
   escape_witness: The four reflected projected-ground components are expanded on the
   original Carrier and each component is transported by the public all-N collision
   theorem to the actual tensor carrier. The two ordered physical branches remain
   separate in the residue definitions.
   literature_status: classical twisted-lattice residue calculus; no novelty claim. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
import D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
import D5.S3.VertexAlgebra.LatticeAllStateLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCollision
open LatticeHalfFockCorrectedField
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField
open LatticeHalfFockGroundRightCurrentTransport
open LatticeHalfFockPhysicalRescaling
open LatticeAllStateField
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

/- The two signed charge components of a projected ground source. -/
def reflectedCharge {D : LatticeData} (charge : Charge D) (u : Bool) : Charge D :=
  if u then -charge else charge

def projectedSign (epsilon : Bool) : ℂ :=
  if epsilon then -1 else 1

theorem projectedGround_expansion (D : LatticeData) (alpha : Charge D)
    (epsilon : Bool) :
    projectedGround D alpha epsilon =
      (2 : ℂ)⁻¹ • Finsupp.single alpha (1 : Oscillator D) +
        ((2 : ℂ)⁻¹ * projectedSign epsilon) •
          Finsupp.single (-alpha) (1 : Oscillator D) := by
  simp only [projectedGround, projectedSign, Bool.cond_eq_if]
  cases epsilon <;> module

/- The normalized collision term is kept as an actual tensor endomorphism. -/
def chargedCollisionTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (q e : ℤ) (x : ActualTensor D hu) : ActualTensor D hu :=
  if -q - 1 - bilinear D sigma tau < 0 then 0 else
    epsilon D sigma tau • collisionCoefficient D hu sigma tau
      (-q - 1 - bilinear D sigma tau).toNat e x

def chargedCollisionFour (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (q e : ℤ)
    (x : ActualTensor D hu) : ActualTensor D hu :=
  (1 / 4 : ℂ) • (
    chargedCollisionTerm D hu (reflectedCharge sigma false)
      (reflectedCharge tau false) q e x +
    projectedSign eta • chargedCollisionTerm D hu (reflectedCharge sigma false)
      (reflectedCharge tau true) q e x +
    projectedSign epsilon • chargedCollisionTerm D hu (reflectedCharge sigma true)
      (reflectedCharge tau false) q e x +
    (projectedSign epsilon * projectedSign eta) •
      chargedCollisionTerm D hu (reflectedCharge sigma true)
        (reflectedCharge tau true) q e x)

def chargedGroundSource (D : LatticeData) (sigma tau : Charge D)
    (epsilon eta : Bool) (q : ℤ) : Carrier D :=
  LatticeAllStateReconstruction.mu D (projectedGround D sigma epsilon) q
    (projectedGround D tau eta)

def chargedGroundSourceCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (q e : ℤ)
    (x : ActualTensor D hu) : ActualTensor D hu :=
  (correctedField D hu (chargedGroundSource D sigma tau epsilon eta q)).coeff e x

private theorem corrected_coeff_add (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu (a + b)).coeff e x =
      (correctedField D hu a).coeff e x + (correctedField D hu b).coeff e x := by
  rw [map_add]
  change ((HahnModule.of ℂ).symm (((correctedField D hu a) x +
      (correctedField D hu b) x))).coeff e = _
  simp only [HahnModule.of_symm_add, HahnSeries.coeff_add,
    HVertexOperator.coeff_apply_apply]

private theorem corrected_coeff_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (c : ℂ) (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu (c • a)).coeff e x =
      c • (correctedField D hu a).coeff e x := by
  rw [map_smul]
  change ((HahnModule.of ℂ).symm (c • ((correctedField D hu a) x))).coeff e = _
  simp only [HahnModule.of_symm_smul, HahnSeries.coeff_smul,
    HVertexOperator.coeff_apply_apply]

/- The empty correction word is the charged singleton field on the actual
   tensor carrier.  This is the concrete bridge used by the projected slice
   expansion below; it does not introduce a second field construction. -/
private theorem corrected_singleton_coeff_charged (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu (Finsupp.single charge (1 : Oscillator D))).coeff e x =
      (chargedField D hu charge).coeff e x := by
  have emptyEnumeration : ([] : List (Index D)).Perm
      (LatticeAllStateField.occurrences D (0 : Index D →₀ ℕ)) := by
    simp [LatticeAllStateField.occurrences]
  have correction := Corr_monomial_enumeration D charge 0 [] emptyEnumeration
  have corrOne : Corr D charge (1 : Oscillator D) =
      Finsupp.single 0 (1 : Oscillator D) := by
    calc
      _ = shiftCoefficients D (1 : Polynomial (Oscillator D)) := by
        simpa only [show (MvPolynomial.monomial 0 (1 : ℂ) : Oscillator D) = 1 by simp,
          correctionWord, map_one] using correction
      _ = _ := by
        apply Finsupp.ext
        intro n
        change (1 : Polynomial (Oscillator D)).coeff n = (Finsupp.single 0 1) n
        simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]
  rw [correctedField, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
    corrOne, correctedSum, Finsupp.lsum_single, LinearMap.comp_apply]
  rw [shiftField_coefficient_public]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [show (1 : Oscillator D) = MvPolynomial.monomial 0 (1 : ℂ) by simp,
    polynomialField_monomial_public]
  have emptyOccurrences : LatticeHalfFockFockNormalField.occurrences D
      (0 : Index D →₀ ℕ) = [] := by
    simp [LatticeHalfFockFockNormalField.occurrences]
  rw [emptyOccurrences]
  rw [wordField_coefficient]
  change (∑ᶠ _ : Unit, (chargedField D hu charge).coeff e x) = _
  rw [finsum_eq_single _ () (by
    intro modes distinct
    exact (distinct (Subsingleton.elim _ _)).elim)]

/- The two projected components are expanded before any residue regrouping.
   This keeps the two signed charge fields and the projected sign explicit on
   the original actual tensor carrier. -/
theorem projectedGround_slice_mode_expansion (D : LatticeData)
    (hu : IsUnit D.G.det) (alpha : Charge D) (epsilon : Bool)
    (shift mode : ℤ) (x : ActualTensor D hu) :
    ((physicalSlice D hu (correctedField D hu (projectedGround D alpha epsilon)) shift)[[mode]]) x =
      (2 : ℂ)⁻¹ •
          ((physicalSlice D hu (chargedField D hu alpha) shift)[[mode]]) x +
        ((2 : ℂ)⁻¹ * projectedSign epsilon) •
          ((physicalSlice D hu (chargedField D hu (-alpha)) shift)[[mode]]) x := by
  rw [physicalSlice_mode D hu
    (correctedField D hu (projectedGround D alpha epsilon)) shift mode,
    projectedGround_expansion]
  simp only [corrected_coeff_add, corrected_coeff_smul,
    corrected_singleton_coeff_charged]
  rw [physicalSlice_mode D hu (chargedField D hu alpha) shift mode,
    physicalSlice_mode D hu (chargedField D hu (-alpha)) shift mode]

theorem charged_source_pair_collision (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (q e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[q]])
        (Finsupp.single tau (1 : Oscillator D)))).coeff e x =
      chargedCollisionTerm D hu sigma tau q e x := by
  simp only [chargedCollisionTerm]
  rw [charged_normalized_source_product_allN]
  by_cases h : -q - 1 - bilinear D sigma tau < 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    have addLeft (a b c : Charge D) : bilinear D (a + b) c =
        bilinear D a c + bilinear D b c := by
      simp [bilinear, add_mul, Finset.sum_add_distrib]
    have addRight (a b c : Charge D) : bilinear D a (b + c) =
        bilinear D a b + bilinear D a c := by
      simp [bilinear, mul_add, Finset.sum_add_distrib]
    have normAdd : chargeNorm D (sigma + tau) =
        chargeNorm D sigma + chargeNorm D tau + 2 * bilinear D sigma tau := by
      unfold chargeNorm
      rw [addLeft, addRight, addRight,
        LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
      ring
    have normalization : chargeScalar D sigma * chargeScalar D tau *
        (2 : ℂ) ^ (-2 * bilinear D sigma tau) = chargeScalar D (sigma + tau) := by
      unfold chargeScalar
      rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
        ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
      omega
    rw [normalization, LatticeHalfFockGroundProducts.ground_action_product]
    simp only [TensorProduct.map_smul_right, chargedCollisionTerm, h,
      collisionCoefficient, LinearMap.smul_apply, smul_smul]
    module

theorem charged_ground_source_expansion (D : LatticeData) (sigma tau : Charge D)
    (epsilon eta : Bool) (q : ℤ) :
    chargedGroundSource D sigma tau epsilon eta q =
      (1 / 4 : ℂ) • (
        ((LatticeAllStateField.Y D
          (Finsupp.single (reflectedCharge sigma false) (1 : Oscillator D)))[[q]])
          (Finsupp.single (reflectedCharge tau false) (1 : Oscillator D)) +
        projectedSign eta •
          ((LatticeAllStateField.Y D
            (Finsupp.single (reflectedCharge sigma false) (1 : Oscillator D)))[[q]])
            (Finsupp.single (reflectedCharge tau true) (1 : Oscillator D)) +
        projectedSign epsilon •
          ((LatticeAllStateField.Y D
            (Finsupp.single (reflectedCharge sigma true) (1 : Oscillator D)))[[q]])
            (Finsupp.single (reflectedCharge tau false) (1 : Oscillator D)) +
        (projectedSign epsilon * projectedSign eta) •
          ((LatticeAllStateField.Y D
            (Finsupp.single (reflectedCharge sigma true) (1 : Oscillator D)))[[q]])
            (Finsupp.single (reflectedCharge tau true) (1 : Oscillator D))) := by
  have single_smul (a : Charge D) (c : ℂ) :
      Finsupp.single a (c • (1 : Oscillator D)) =
        c • Finsupp.single a (1 : Oscillator D) :=
    (Finsupp.smul_single c a (1 : Oscillator D)).symm
  unfold chargedGroundSource LatticeAllStateReconstruction.mu
  cases epsilon <;> cases eta <;>
    simp [projectedGround, projectedSign, reflectedCharge,
      LatticeAllStateField.Y_single, LatticeAllStateReconstruction.mu]
  all_goals simp_rw [single_smul]
  all_goals simp only [map_smul]
  all_goals module

/- The all-N comparison is composed only after the four reflected source terms
   have been expanded on the original Carrier. -/
theorem charged_ground_source_collision (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (q e : ℤ)
    (x : ActualTensor D hu) :
    chargedGroundSourceCoefficient D hu sigma tau epsilon eta q e x =
      chargedCollisionFour D hu sigma tau epsilon eta q e x := by
  unfold chargedGroundSourceCoefficient
  rw [charged_ground_source_expansion]
  unfold chargedCollisionFour
  simp only [corrected_coeff_add, corrected_coeff_smul]
  rw [charged_source_pair_collision, charged_source_pair_collision,
    charged_source_pair_collision, charged_source_pair_collision]

/- The concrete physical branches retain both ordered contributions and their
   actual translated mode indices. -/
def physicalResidueWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * StateFieldResidueReconstruction.integerBinomial r j

def physicalResidueLeft {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) : M :=
  ∑ᶠ j : ℕ, physicalResidueWeight r j •
    ((A[[r - j]]) ((B[[n + j]]) x))

def physicalResidueRight {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) : M :=
  ∑ᶠ j : ℕ, physicalResidueWeight r j •
    ((B[[r + n - j]]) ((A[[j]]) x))

def physicalResidueCoefficient {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) : M :=
  physicalResidueLeft A B r n x - (-1 : ℂ) ^ r • physicalResidueRight A B r n x

def chargedPhysicalOutputExponent (gamma delta n l : ℤ) : ℤ :=
  -2 * (n - l) - gamma - delta - 2

def chargedPhysicalCollisionRow (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ) (l : ℕ)
    (x : ActualTensor D hu) : ActualTensor D hu :=
  chargedCollisionFour D hu sigma tau epsilon eta (r + l)
    (chargedPhysicalOutputExponent gamma delta n l) x

def chargedPhysicalSourceRow (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ) (l : ℕ)
    (x : ActualTensor D hu) : ActualTensor D hu :=
  chargedGroundSourceCoefficient D hu sigma tau epsilon eta (r + l)
    (chargedPhysicalOutputExponent gamma delta n l) x

def chargedPhysicalResidueRow (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (l : ℕ) (x : ActualTensor D hu) : ActualTensor D hu :=
  physicalResidueCoefficient
    (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
    (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)
    (r + l) (n - l) x

theorem reflected_bilinear_natAbs (D : LatticeData) (sigma tau : Charge D)
    (u v : Bool) :
    (bilinear D (reflectedCharge sigma u) (reflectedCharge tau v)).natAbs =
      (bilinear D sigma tau).natAbs := by
  cases u <;> cases v <;>
    simp [reflectedCharge, LatticeFiniteNegativeGeneration.bilinear_neg_left,
      LatticeFiniteNegativeGeneration.bilinear_neg_right]

theorem chargedPhysicalSourceRow_eq_collision (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (l : ℕ) (x : ActualTensor D hu) :
    chargedPhysicalSourceRow D hu sigma tau epsilon eta gamma delta r n l x =
      chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n l x := by
  unfold chargedPhysicalSourceRow chargedPhysicalCollisionRow
  exact charged_ground_source_collision D hu sigma tau epsilon eta
    (r + l) (chargedPhysicalOutputExponent gamma delta n l) x

/- The four reflected collision rows have an independent unweighted outer
   tail.  This is a source-degree calculation: it uses only the actual
   locality cutoff and the reflected bilinear, before any residue row or
   inverse is invoked. -/
theorem chargedPhysicalCollisionRow_tail (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (K : ℕ)
    (hK : (bilinear D sigma tau).natAbs ≤ K)
    (l : ℕ) (hl : ((K : ℤ) - r).toNat ≤ l) (x : ActualTensor D hu) :
    chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n l x = 0 := by
  have natAbs_lower (z : ℤ) : -(z.natAbs : ℤ) ≤ z := by
    cases z <;> simp [Int.natAbs] <;> omega
  have cutoff (u v : Bool) :
      -((r + (l : ℤ)) : ℤ) - 1 - bilinear D (reflectedCharge sigma u)
          (reflectedCharge tau v) < 0 := by
    have hreflect := reflected_bilinear_natAbs D sigma tau u v
    have hbound :
        (bilinear D (reflectedCharge sigma u) (reflectedCharge tau v)).natAbs ≤ K := by
      simpa [hreflect] using hK
    have hrl : (K : ℤ) ≤ r + (l : ℤ) := by
      by_cases hkr : 0 ≤ (K : ℤ) - r
      · have hcast : (((K : ℤ) - r).toNat : ℤ) = (K : ℤ) - r :=
          Int.toNat_of_nonneg hkr
        omega
      · omega
    have hlower := natAbs_lower
      (bilinear D (reflectedCharge sigma u) (reflectedCharge tau v))
    omega
  unfold chargedPhysicalCollisionRow chargedCollisionFour chargedCollisionTerm
  simp only [reflectedCharge, Bool.false_eq_true, if_false, if_true]
  have h00 : -(r + (l : ℤ)) - 1 - bilinear D sigma tau < 0 := by
    simpa [reflectedCharge] using cutoff false false
  have h01 : -(r + (l : ℤ)) - 1 - bilinear D sigma (-tau) < 0 := by
    simpa [reflectedCharge] using cutoff false true
  have h10 : -(r + (l : ℤ)) - 1 - bilinear D (-sigma) tau < 0 := by
    simpa [reflectedCharge] using cutoff true false
  have h11 : -(r + (l : ℤ)) - 1 - bilinear D (-sigma) (-tau) < 0 := by
    simpa [reflectedCharge] using cutoff true true
  rw [if_pos h00, if_pos h01, if_pos h10, if_pos h11]
  simp

/- The source tail is then obtained from the already proved public all-N
   source comparison, still independently of the physical residue rows. -/
theorem chargedPhysicalSourceRow_tail (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (K : ℕ)
    (hK : (bilinear D sigma tau).natAbs ≤ K)
    (l : ℕ) (hl : ((K : ℤ) - r).toNat ≤ l) (x : ActualTensor D hu) :
    chargedPhysicalSourceRow D hu sigma tau epsilon eta gamma delta r n l x = 0 := by
  rw [chargedPhysicalSourceRow_eq_collision]
  exact chargedPhysicalCollisionRow_tail D hu sigma tau epsilon eta gamma delta r n K hK l hl x

/- The finite inverse is proved on the actual charged triangular family.  The
   input rows are finite sums, so the argument also covers the zero cutoff. -/
theorem charged_finite_binomial_inverse {M : Type*} [AddCommGroup M] [Module ℂ M]
    (a : ℂ) (L : ℕ) (C R : ℕ → M)
    (hforward : ∀ l, l < L →
      R l = ∑ k ∈ Finset.range (L - l), Ring.choose a k • C (l + k))
    (htail : ∀ l, L ≤ l → C l = 0) :
    C 0 = ∑ l ∈ Finset.range L, Ring.choose (-a) l • R l := by
  classical
  by_cases hL : L = 0
  · subst L
    simpa using (htail 0 (by simp))
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have expanded :
      (∑ l ∈ Finset.range L, Ring.choose (-a) l • R l) =
        ∑ l ∈ Finset.range L,
          Ring.choose (-a) l •
            ∑ k ∈ Finset.range (L - l), Ring.choose a k • C (l + k) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hforward l (Finset.mem_range.mp hl)]
  apply Eq.symm
  rw [expanded]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_range_diag_flip L
    (fun l k => Ring.choose (-a) l • Ring.choose a k • C (l + k))]
  have diagonal (m : ℕ) :
      (∑ l ∈ Finset.range (m + 1),
        Ring.choose (-a) l • Ring.choose a (m - l) • C m) =
        Ring.choose (0 : ℂ) m • C m := by
    calc
      _ = ∑ l ∈ Finset.range (m + 1),
          (Ring.choose (-a) l * Ring.choose a (m - l)) • C m := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [smul_smul]
      _ = (∑ l ∈ Finset.range (m + 1),
          Ring.choose (-a) l * Ring.choose a (m - l)) • C m := by
        exact (Finset.sum_smul).symm
      _ = Ring.choose (0 : ℂ) m • C m := by
        rw [show m + 1 = Nat.succ m by omega]
        have hsum :
            (∑ l ∈ Finset.range m.succ,
              Ring.choose (-a) l * Ring.choose a (m - l)) =
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                Ring.choose (-a) ij.1 * Ring.choose a ij.2 := by
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        rw [hsum]
        have hscalar :
            (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
              Ring.choose (-a) ij.1 * Ring.choose a ij.2) =
              Ring.choose (0 : ℂ) m := by
          rw [← Ring.add_choose_eq m (Commute.all (-a) a)]
          have hzero : -a + a = (0 : ℂ) := by ring
          rw [hzero]
        rw [hscalar]
  have diagonal_sum :
      (∑ m ∈ Finset.range L, ∑ l ∈ Finset.range (m + 1),
        Ring.choose (-a) l • Ring.choose a (m - l) • C m) =
        ∑ m ∈ Finset.range L, Ring.choose (0 : ℂ) m • C m := by
    apply Finset.sum_congr rfl
    intro m hm
    exact diagonal m
  have reindex :
      (∑ m ∈ Finset.range L, ∑ k ∈ Finset.range (m + 1),
        Ring.choose (-a) k • Ring.choose a (m - k) • C (k + (m - k))) =
        ∑ m ∈ Finset.range L, ∑ k ∈ Finset.range (m + 1),
          Ring.choose (-a) k • Ring.choose a (m - k) • C m := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by
      have hlt := Finset.mem_range.mp hk
      omega
    rw [Nat.add_sub_of_le hkm]
  rw [reindex]
  rw [diagonal_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hne
    have hbpos : 0 < b := Nat.pos_of_ne_zero hne
    rw [Ring.choose_zero_pos ℂ hbpos, zero_smul]
  · simp [hLpos]

theorem physicalResidueLeft_finite {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    Function.HasFiniteSupport (fun j : ℕ => physicalResidueWeight r j •
      ((A[[r - (j : ℤ)]]) ((B[[n + (j : ℤ)]]) x))) := by
  refine BddAbove.finite (bddAbove_def.mpr ⟨
    (-((HahnModule.of ℂ).symm (B x)).order - n - 1).toNat, ?_⟩)
  intro j supported
  by_contra outside
  apply supported
  have zero : (B[[n + (j : ℤ)]]) x = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [zero]

theorem physicalResidueRight_finite {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    Function.HasFiniteSupport (fun j : ℕ => physicalResidueWeight r j •
      ((B[[r + n - (j : ℤ)]]) ((A[[(j : ℤ)]]) x))) := by
  refine BddAbove.finite (bddAbove_def.mpr ⟨
    (-((HahnModule.of ℂ).symm (A x)).order - 1).toNat, ?_⟩)
  intro j supported
  by_contra outside
  apply supported
  have zero : (A[[(j : ℤ)]]) x = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [zero]

/- The actual two ordered physical supports are pointwise finite before any
   regrouping.  These are the supports of the rows used by the residue
   coefficient, with no assertion that either ordered branch vanishes. -/
theorem chargedPhysicalResidueRow_left_finite (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (l : ℕ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport
      (fun j : ℕ => physicalResidueWeight (r + l) j •
        ((physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma
            [[(r + l) - (j : ℤ)]])
          ((physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta
            [[(n - l) + (j : ℤ)]]) x))) := by
  simpa [physicalResidueWeight] using
    physicalResidueLeft_finite
      (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
      (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)
      (r + l) (n - l) x

theorem chargedPhysicalResidueRow_right_finite (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (l : ℕ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport
      (fun j : ℕ => physicalResidueWeight (r + l) j •
        ((physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta
            [[(r + l) + (n - l) - (j : ℤ)]])
          ((physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma
            [[(j : ℤ)]]) x))) := by
  simpa [physicalResidueWeight] using
    physicalResidueRight_finite
      (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
      (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)
      (r + l) (n - l) x


end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
