/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithfulness of charge-zero restriction for signed Leech mixed fields. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
import D5.S3.VertexAlgebra.LatticeActualMixedLocality
import D5.S3.VertexAlgebra.LatticeAllStateJacobi

/-!
The signed Borcherds law makes agreement stable under fixed-algebra modes.
Two-current iterates then propagate agreement from the charge-zero source to
the descendants of every odd charged vacuum.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeInvolution
open LatticeSugawaraCurrents LatticeActualMixedLocality MvPolynomial
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open ActualLeechHyperbolic (leechData leech_spec)
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator

open private bilinear_unit neutralMode_truncation from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

noncomputable section

/-- Coefficient n corresponds to physical mode n + 1/2 and doubled exponent -2*n-3. -/
abbrev MixedCoefficients (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :=
  ℤ → OddCarrier D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu (!s)

/-- The full signed coefficient identity with the native fixed actions on both parities. -/
def mixedBorcherds (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F : MixedCoefficients D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p q r : ℤ) : Prop :=
  let ρ := fun (t : Bool) (m : ℤ) => (fixedParitySlice D hu (paritySign t) a)[[m]]
  let left := fun i : ℕ => integerBinomial p i • F (p+q-i) (oddMode D a (r+i) b) v
  let first := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
    ρ (!s) (p+r-i) (F (q+i) b v)
  let second := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • F (q+r-i) b (ρ s (p+i) v))
  Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
    Function.HasFiniteSupport second ∧
    (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i)

/-- Arbitrary lower-truncated mixed fields with physical translation and the full
signed Jacobi law relative to the actual fixed lattice algebra. -/
structure LawfulMixedField (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) where
  coeff : MixedCoefficients D hu s
  truncation : ∀ b v, ∃ N : ℤ, ∀ n ≥ N, coeff n b v = 0
  derivative : ∀ (b : OddCarrier D) (v : Twisted D hu s) (n : ℤ),
    coeff n (oddTranslation D b) v = (-((n : ℂ) + 1/2)) • coeff (n-1) b v
  borcherds : ∀ a b v p q r, mixedBorcherds D hu s coeff a b v p q r

/-- The native parity-changing field belongs to the full signed coefficient space. -/
def nativeMixedField (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    LawfulMixedField D hu s where
  coeff := J D hu s
  truncation := J_truncation D hu s
  derivative := J_derivative D hu s
  borcherds := J_borcherds D hu s

private theorem mixed_iterate (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F : LawfulMixedField D hu s) (a : FixedCarrier D) (b : OddCarrier D)
    (v : Twisted D hu s) (q r : ℤ) :
    let ρ := fun (t : Bool) (m : ℤ) => (fixedParitySlice D hu (paritySign t) a)[[m]]
    F.coeff q (oddMode D a r b) v =
      (∑ᶠ i : ℕ, (((-1 : ℂ)^i)*integerBinomial r i) •
        ρ (!s) (r-i) (F.coeff (q+i) b v)) -
      (∑ᶠ i : ℕ, (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • F.coeff (q+r-i) b (ρ s i v))) := by
  have law := F.borcherds a b v 0 q r
  unfold mixedBorcherds at law
  have h := law.2.2.2
  dsimp only at h
  rw [finsum_eq_single _ 0] at h
  · simpa [integerBinomial, Ring.choose_zero_right] using h
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- All source vectors on which two mixed coefficient families agree. Its
specialization to the zero family is the source kernel. -/
def mixedAgreement (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F G : MixedCoefficients D hu s) : Submodule ℂ (OddCarrier D) :=
  ⨅ n : ℤ, LinearMap.ker (F n - G n)

@[simp] theorem mem_mixedAgreement (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F G : MixedCoefficients D hu s) (b : OddCarrier D) :
    b ∈ mixedAgreement D hu s F G ↔ ∀ n, F n b = G n b := by
  simp only [mixedAgreement, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero]

/-- Agreement propagates through every fixed mode, by the signed p = 0 residue. -/
theorem mixedAgreement_stable (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F G : LawfulMixedField D hu s) (a : FixedCarrier D) (r : ℤ) (b : OddCarrier D)
    (hb : b ∈ mixedAgreement D hu s F.coeff G.coeff) :
    oddMode D a r b ∈ mixedAgreement D hu s F.coeff G.coeff := by
  rw [mem_mixedAgreement] at hb ⊢
  intro q
  apply LinearMap.ext
  intro v
  rw [mixed_iterate D hu s F, mixed_iterate D hu s G]
  dsimp only
  simp only [hb]

/-- In particular, every lawful mixed field has a fixed-mode-stable source kernel. -/
theorem mixedKernel_stable (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F : LawfulMixedField D hu s) (a : FixedCarrier D) (r : ℤ) (b : OddCarrier D)
    (hb : b ∈ mixedAgreement D hu s F.coeff 0) :
    oddMode D a r b ∈ mixedAgreement D hu s F.coeff 0 := by
  rw [mem_mixedAgreement] at hb ⊢
  intro q
  apply LinearMap.ext
  intro v
  rw [mixed_iterate D hu s F]
  dsimp only
  simp only [hb, Pi.zero_apply, LinearMap.zero_apply, map_zero, smul_zero,
    finsum_zero, sub_zero]

/-- The charge-zero part of the actual odd untwisted carrier. -/
def chargeZeroOdd (D : LatticeData) : Submodule ℂ (OddCarrier D) :=
  (Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))).comap (minusSpace D).subtype

private def antisymmetrize (D : LatticeData) : Carrier D →ₗ[ℂ] OddCarrier D :=
  LinearMap.codRestrict (minusSpace D) (LinearMap.id - (theta D).toLinearMap) (fun v => by
    change v - theta D v ∈ eigenspace D (-1)
    rw [mem_eigenspace, map_sub, neg_one_smul]
    rw [show theta D (theta D v) = v from theta_involutive D v, neg_sub])

/-- The odd state obtained from a polynomial at charge c and its theta image. -/
def oddChargedPolynomial (D : LatticeData) (c : Charge D) (p : Oscillator D) :
    OddCarrier D :=
  antisymmetrize D (Finsupp.single c p)

/-- The invariant lattice exponential sum for the realized reflection. -/
def fixedChargedVacuum (D : LatticeData) (c : Charge D) : FixedCarrier D :=
  ⟨Finsupp.single c 1 + Finsupp.single (-c) 1, by
    rw [mem_fixedSpace, map_add]
    change thetaLinear D (Finsupp.single c 1) + thetaLinear D (Finsupp.single (-c) 1) = _
    rw [theta_single, theta_single, neg_neg, map_one, add_comm]⟩

/-- The current h(-1)1 with h the actual lattice charge vector c. -/
def chargeCurrent (D : LatticeData) (c : Charge D) : OddCarrier D :=
  ∑ i : Fin D.rank, (c i : ℂ) • oddCurrent D i

private theorem charge_pairing_sum (D : LatticeData) (c : Charge D) :
    (∑ i : Fin D.rank, (c i : ℂ) * (bilinear D (unitCharge D i) c : ℂ)) =
      (bilinear D c c : ℂ) := by
  simp_rw [bilinear_unit]
  simp only [bilinear, Int.cast_sum, Int.cast_mul, Finset.mul_sum, mul_assoc]

private theorem charged_zero_on_current (D : LatticeData) (c : Charge D)
    (i : Fin D.rank) :
    ((actualField D c)[[0]]) (oddCurrent D i).val =
      (-(bilinear D (unitCharge D i) c : ℂ)) • Finsupp.single c 1 := by
  have h := LinearMap.congr_fun (neutral_actual_commutator D i c (-1) 0) (vacuum D)
  have hzero : ((actualField D c)[[0]]) (vacuum D) = 0 := by
    rw [← stateField_ground]
    exact stateField_creativity D _ 0 le_rfl
  have hcreate : ((actualField D c)[[-1]]) (vacuum D) = Finsupp.single c 1 := by
    rw [← stateField_ground, stateField_creation]
  simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply,
    neutralField_ncoeff, LinearMap.smul_apply, hzero, map_zero, zero_sub, add_zero, hcreate] at h
  change ((actualField D c)[[0]]) (neutralMode D i (-1) (vacuum D)) = _
  rw [neg_smul, ← h, neg_neg]

private theorem fixedChargedVacuum_zero_current (D : LatticeData) (c : Charge D)
    (i : Fin D.rank) :
    oddMode D (fixedChargedVacuum D c) 0 (oddCurrent D i) =
      (-(bilinear D (unitCharge D i) c : ℂ)) • oddChargedPolynomial D c 1 := by
  apply Subtype.ext
  change mu D (Finsupp.single c 1 + Finsupp.single (-c) 1) 0 (oddCurrent D i).val =
    (-(bilinear D (unitCharge D i) c : ℂ)) •
      (Finsupp.single c 1 - thetaLinear D (Finsupp.single c 1))
  have e : mu D (Finsupp.single c 1 + Finsupp.single (-c) 1) 0 (oddCurrent D i).val =
      ((actualField D c)[[0]]) (oddCurrent D i).val +
        ((actualField D (-c))[[0]]) (oddCurrent D i).val := by
    simp only [mu, map_add, Pi.add_apply, LinearMap.add_apply, stateField_ground]
  simp only [e, charged_zero_on_current, theta_single, map_one, bilinear_neg_right,
    Int.cast_neg, neg_neg, neg_smul, smul_sub]
  abel

/-- The fixed exponential zero mode produces the odd charged vacuum, with
scalar the negative of the actual squared charge norm. -/
theorem fixedChargedVacuum_zero_chargeCurrent (D : LatticeData) (c : Charge D) :
    oddMode D (fixedChargedVacuum D c) 0 (chargeCurrent D c) =
      (-(bilinear D c c : ℂ)) • oddChargedPolynomial D c 1 := by
  simp only [chargeCurrent, map_sum, map_smul, fixedChargedVacuum_zero_current,
    smul_smul, mul_neg]
  rw [← Finset.sum_smul, Finset.sum_neg_distrib, charge_pairing_sum]

private theorem chargeCurrent_mem (D : LatticeData) (c : Charge D) :
    chargeCurrent D c ∈ chargeZeroOdd D := by
  unfold chargeCurrent
  apply (chargeZeroOdd D).sum_mem
  intro i _
  apply (chargeZeroOdd D).smul_mem
  change neutralMode D i (-1) (Finsupp.single 0 1) ∈
    Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))
  rw [neutralMode_single]
  exact Finsupp.single_mem_supported ℂ _ (by simp)

private theorem current_mode (D : LatticeData) (i : Fin D.rank) (m : ℤ) (v : Carrier D) :
    mu D (oddCurrent D i).val m v = neutralMode D i m v := by
  change ((Y D (neutralMode D i (-1) (vacuum D)))[[m]]) v = _
  rw [← neutralField_ncoeff D i (-1), stateField_current, neutralField_ncoeff]

set_option maxHeartbeats 1000000 in
-- Elaborating the two-current Borcherds identity and its finite sums needs extra heartbeats.
/-- A pair of neutral current modes preserves the underlying space of a
fixed-mode-stable odd submodule. -/
theorem current_pair_mem_map (D : LatticeData) (S : Submodule ℂ (OddCarrier D))
    (stable : ∀ a n b, b ∈ S → oddMode D a n b ∈ S)
    (b : OddCarrier D) (hb : b ∈ S) (i j : Fin D.rank) (k q : ℤ) :
    neutralMode D i k (neutralMode D j q b.val) ∈ S.map (minusSpace D).subtype := by
  classical
  let T := S.map (minusSpace D).subtype
  let X := b.val
  let a := (oddCurrent D i).val
  let c := (oddCurrent D j).val
  have a_mode (m : ℤ) (v : Carrier D) : mu D a m v = neutralMode D i m v :=
    current_mode D i m v
  have c_mode (m : ℤ) (v : Carrier D) : mu D c m v = neutralMode D j m v :=
    current_mode D j m v
  have iterates (r m : ℤ) : mu D (mu D a r c) m X ∈ T := by
    let fixed : FixedCarrier D := ⟨mu D a r c, by
      rw [mem_fixedSpace, a_mode, theta_neutralMode]
      have hc := (mem_eigenspace D (-1) c).mp (oddCurrent D j).property
      rw [hc, neg_one_smul, map_neg, neg_neg]⟩
    exact Submodule.mem_map.mpr ⟨oddMode D fixed m b, stable fixed m b hb, rfl⟩
  obtain ⟨P, hP⟩ := neutralMode_truncation D i X
  obtain ⟨Q, hQ⟩ := neutralMode_truncation D j X
  let p : ℤ := (P : ℤ) + 1
  let cutoff : ℤ := (Q : ℤ) + 1
  have outer_zero (t : ℕ) : mu D a (p + t) X = 0 := by
    rw [a_mode]
    exact hP _ (by dsimp [p]; omega)
  have c_zero (m : ℤ) : mu D c m 0 = 0 := by rw [c_mode, map_zero]
  have inner_zero (m : ℤ) (hm : cutoff ≤ m) : neutralMode D j m X = 0 := by
    exact hQ m (by dsimp [cutoff] at hm; omega)
  let product (k q : ℤ) := neutralMode D i k (neutralMode D j q X)
  -- Choose p beyond outer truncation. The reversed terms vanish, and each
  -- forward tail has strictly larger second mode than the pair being recovered.
  have descend (d : ℕ) :
      ∀ q : ℤ, (cutoff - q).toNat = d → ∀ k : ℤ, product k q ∈ T := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd k
      by_cases hq : cutoff ≤ q
      · dsimp only [product]
        rw [inner_zero q hq, map_zero]
        exact T.zero_mem
      have distance : (d : ℤ) = cutoff - q := by
        rw [← hd]
        exact Int.toNat_of_nonneg (by omega)
      let r : ℤ := k - p
      have hpr : p + r = k := by dsimp [r]; omega
      let left := LatticeAllStateJacobi.jacobiLeftTerm D p q r a c X
      let first (t : ℕ) := (((-1 : ℂ)^t) * integerBinomial r t) •
        product (k-t) (q+t)
      have law := LatticeAllStateJacobi.borcherds D a c X p q r
      have h := law.2.2.2
      simp only [outer_zero, c_zero, smul_zero, sub_zero] at h
      have forward : (∑ᶠ t, left t) = ∑ᶠ t, first t := by
        simpa only [left, first, hpr, a_mode, c_mode, product] using h
      have left_mem : (∑ᶠ t, left t) ∈ T := by
        rw [finsum_eq_sum left (show Function.HasFiniteSupport left from law.1)]
        apply T.sum_mem
        intro t _
        exact T.smul_mem _ (iterates (r+t) (p+q-t))
      have supported : Function.support first ⊆ (↑(Finset.range (d+1)) : Set ℕ) := by
        intro t ht
        by_contra outside
        simp only [Finset.mem_coe, Finset.mem_range] at outside
        exact ht (by
          dsimp only [first, product]
          rw [inner_zero (q+t) (by omega), map_zero, smul_zero])
      have leading : first 0 = product k q := by
        simp [first, integerBinomial]
      have tail_mem : (∑ t ∈ Finset.range d, first (t+1)) ∈ T := by
        apply T.sum_mem
        intro t _
        dsimp only [first]
        apply T.smul_mem
        exact ih _ (by omega : (cutoff - (q + ((t+1 : ℕ) : ℤ))).toNat < d) _ rfl _
      rw [finsum_eq_sum_of_support_subset _ supported, Finset.sum_range_succ', leading] at forward
      have recover : product k q = (∑ᶠ t, left t) -
          (∑ t ∈ Finset.range d, first (t+1)) :=
        eq_sub_iff_add_eq.mpr ((add_comm _ _).trans forward.symm)
      rw [recover]
      exact T.sub_mem left_mem tail_mem
  exact descend (cutoff - q).toNat q rfl k

private theorem current_pair_antisymmetrize (D : LatticeData) (i j : Fin D.rank)
    (k q : ℤ) (v : Carrier D) :
    neutralMode D i k (neutralMode D j q (antisymmetrize D v).val) =
      (antisymmetrize D (neutralMode D i k (neutralMode D j q v))).val := by
  change neutralMode D i k (neutralMode D j q (v - theta D v)) =
    neutralMode D i k (neutralMode D j q v) -
      theta D (neutralMode D i k (neutralMode D j q v))
  simp only [map_sub, theta_neutralMode, map_neg, neg_neg]

private theorem charged_create_mem (D : LatticeData)
    (S : Submodule ℂ (OddCarrier D))
    (stable : ∀ a n b, b ∈ S → oddMode D a n b ∈ S)
    (c : Charge D) (j : Fin D.rank) (hj : (bilinear D (unitCharge D j) c : ℂ) ≠ 0)
    (x : Index D) (p : Oscillator D) (hp : oddChargedPolynomial D c p ∈ S) :
    oddChargedPolynomial D c (MvPolynomial.X x * p) ∈ S := by
  obtain ⟨b, hb, he⟩ := Submodule.mem_map.mp
    (current_pair_mem_map D S stable _ hp x.1 j (-(x.2 : ℤ)-1) 0)
  change b.val = neutralMode D x.1 (-(x.2 : ℤ)-1)
    (neutralMode D j 0 (antisymmetrize D (Finsupp.single c p)).val) at he
  have hzero : neutralMode D j 0 (Finsupp.single c p) =
      (bilinear D (unitCharge D j) c : ℂ) • Finsupp.single c p := by
    rw [neutralMode_single, Finsupp.smul_single]
    simp [neutralPolynomialMode]
  rw [current_pair_antisymmetrize, hzero, map_smul, neutralMode_single,
    neutralPolynomialMode_negative, LinearMap.mulLeft_apply, map_smul,
    Submodule.coe_smul] at he
  have hb' : b = (bilinear D (unitCharge D j) c : ℂ) •
      oddChargedPolynomial D c (MvPolynomial.X x * p) := Subtype.ext he
  rw [hb'] at hb
  simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using
    S.smul_mem (bilinear D (unitCharge D j) c : ℂ)⁻¹ hb

/-- Every fixed-mode-stable submodule containing charge-zero odd states contains
the entire odd lattice carrier. -/
theorem oddSource_eq_top (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (S : Submodule ℂ (OddCarrier D)) (hneutral : chargeZeroOdd D ≤ S)
    (stable : ∀ a n b, b ∈ S → oddMode D a n b ∈ S) : S = ⊤ := by
  classical
  have all_charges (c : Charge D) (p : Oscillator D) : oddChargedPolynomial D c p ∈ S := by
    by_cases hc : c = 0
    · subst c
      apply hneutral
      change Finsupp.single (0 : Charge D) p - thetaLinear D (Finsupp.single 0 p) ∈
        Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))
      rw [theta_single, neg_zero]
      exact Submodule.sub_mem _ (Finsupp.single_mem_supported ℂ _ (by simp))
        (Finsupp.single_mem_supported ℂ _ (by simp))
    have hnorm : (bilinear D c c : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (norm_positive D hD c hc))
    obtain ⟨j, hj⟩ : ∃ j : Fin D.rank, (bilinear D (unitCharge D j) c : ℂ) ≠ 0 := by
      by_contra! hall
      apply hnorm
      rw [← charge_pairing_sum]
      simp only [hall, mul_zero, Finset.sum_const_zero]
    have hseed := stable (fixedChargedVacuum D c) 0 (chargeCurrent D c)
      (hneutral (chargeCurrent_mem D c))
    rw [fixedChargedVacuum_zero_chargeCurrent] at hseed
    have hground : oddChargedPolynomial D c 1 ∈ S := by
      simpa only [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hnorm), one_smul] using
        S.smul_mem (-(bilinear D c c : ℂ))⁻¹ hseed
    induction p using MvPolynomial.induction_on with
    | C z =>
      have hz : MvPolynomial.C z = z • (1 : Oscillator D) := by rw [← C_mul', mul_one]
      simp only [oddChargedPolynomial, hz, ← Finsupp.smul_single, map_smul]
      exact S.smul_mem z hground
    | add p p' hp hp' =>
      simpa only [oddChargedPolynomial, Finsupp.single_add, map_add] using S.add_mem hp hp'
    | mul_X p x hp =>
      rw [mul_comm p (MvPolynomial.X x)]
      exact charged_create_mem D S stable c j hj x p hp
  apply top_unique
  intro b _
  have hsum : (∑ c ∈ b.val.support, antisymmetrize D (Finsupp.single c (b.val c))) ∈ S :=
    S.sum_mem (fun c _ => all_charges c (b.val c))
  rw [← map_sum] at hsum
  change antisymmetrize D (b.val.sum Finsupp.single) ∈ S at hsum
  rw [Finsupp.sum_single] at hsum
  have hdouble : antisymmetrize D b.val = (2 : ℂ) • b := by
    apply Subtype.ext
    change b.val - theta D b.val = _
    have hb := (mem_eigenspace D (-1) b.val).mp b.property
    rw [hb, neg_one_smul, sub_neg_eq_add, two_smul, Submodule.coe_add]
  rw [hdouble] at hsum
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using
    S.smul_mem (2 : ℂ)⁻¹ hsum

/-- Restrict the source to the genuine charge-zero odd Heisenberg carrier. -/
def restrictChargeZero (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F : LawfulMixedField D hu s) :
    ℤ → chargeZeroOdd D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu (!s) :=
  fun n => (F.coeff n).comp (chargeZeroOdd D).subtype

/-- For both Leech twisted parities, restriction to the charge-zero odd first
inputs faithfully detects all lawful signed mixed fields. -/
theorem leech_restrictChargeZero_injective (s : Bool) :
    Function.Injective (restrictChargeZero leechData leechUnit s) := by
  intro F G h
  let S := mixedAgreement leechData leechUnit s F.coeff G.coeff
  have hneutral : chargeZeroOdd leechData ≤ S := by
    intro b hb
    apply (mem_mixedAgreement leechData leechUnit s _ _ _).mpr
    intro n
    exact LinearMap.congr_fun (congrFun h n) ⟨b, hb⟩
  have htop : S = ⊤ := oddSource_eq_top leechData leech_spec.2.2.1 S hneutral
    (fun a n b hb => mixedAgreement_stable leechData leechUnit s F G a n b hb)
  have hcoeff : F.coeff = G.coeff := by
    funext n
    apply LinearMap.ext
    intro b
    have hb : b ∈ S := htop.symm ▸ Submodule.mem_top
    exact (mem_mixedAgreement leechData leechUnit s _ _ _).mp hb n
  cases F
  cases G
  cases hcoeff
  rfl

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
