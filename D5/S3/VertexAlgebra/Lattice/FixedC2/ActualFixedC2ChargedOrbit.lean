/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite charge support of the intrinsic fixed Leech C₂ quotient. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2ChargedOscillator
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2Projection
import D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeInvolution
open LatticeActualStateFieldCalculus LatticeActualAnnihilation MvPolynomial
open LatticePositiveEnergy
open ActualLeechHyperbolic (leechData)
open scoped VertexOperator

open private jet polynomialLength polynomial_word_mem polynomial_create_mem annihilate_word_mem
  from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
open private quadratic_iterate quadratic_mem_c2_sup_orbit ground_mem_sup_orbit
  from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2ChargedOscillator
open private fixedGroundOrbit_val from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2GroundCharge
open private E ground from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private derivative_modes derivative_creation
  from D5.S3.VertexAlgebra.LatticeAllStateField
open private shortCharges_finite from D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite

noncomputable section

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The fixed state obtained by summing the two charge translates of a word under the involution. -/
def fixedChargedWord (D : LatticeData) (c : Charge D) (w : List (Index D)) :
    FixedCarrier D :=
  fixedChargedPolynomial D c (neutralPolynomial D w)

/-- The span of fixed words in one orbit with strictly fewer than `n` oscillators. -/
def fixedChargedWordBelow (D : LatticeData) (c : Charge D) (n : ℕ) :
    Submodule ℂ (FixedCarrier D) :=
  Submodule.span ℂ {v | ∃ w : List (Index D), w.length < n ∧ v = fixedChargedWord D c w}

private def symmetrize (D : LatticeData) : Carrier D →ₗ[ℂ] FixedCarrier D :=
  (2 : ℂ) • plusProjection D

private theorem symmetrize_val (D : LatticeData) (v : Carrier D) :
    (symmetrize D v).val = v + theta D v := by
  change (2 : ℂ) • ((2 : ℂ)⁻¹ • (v + theta D v)) = _
  rw [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem symmetrize_single (D : LatticeData) (c : Charge D) (p : Oscillator D) :
    symmetrize D (Finsupp.single c p) = fixedChargedPolynomial D c p := by
  apply Subtype.ext
  rw [symmetrize_val]
  change Finsupp.single c p + thetaLinear D (Finsupp.single c p) =
    Finsupp.single c p + Finsupp.single (-c) (sigma D p)
  rw [theta_single]

private theorem symmetrize_mode (D : LatticeData) (a : FixedCarrier D) (m : ℤ)
    (v : Carrier D) :
    symmetrize D (mu D a.val m v) = fixedMode D a m (symmetrize D v) := by
  apply Subtype.ext
  rw [symmetrize_val]
  change ((Y D a.val)[[m]]) v + theta D (((Y D a.val)[[m]]) v) =
    ((Y D a.val)[[m]]) (symmetrize D v).val
  rw [symmetrize_val, stateField_theta, (mem_fixedSpace D _).mp a.property, map_add]

private theorem polynomialLength_symmetrize_mem (D : LatticeData) (c : Charge D)
    (k n : ℕ) (hkn : k < n) (p : Oscillator D) (hp : p ∈ polynomialLength D k) :
    symmetrize D (Finsupp.single c p) ∈ fixedChargedWordBelow D c n := by
  change p ∈ (fixedChargedWordBelow D c n).comap
    ((symmetrize D).comp (Finsupp.lsingle c))
  refine (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨w, hw, rfl⟩
  change symmetrize D (Finsupp.single c (neutralPolynomial D w)) ∈ fixedChargedWordBelow D c n
  rw [symmetrize_single]
  exact Submodule.subset_span ⟨w, hw ▸ hkn, rfl⟩

private theorem charged_jet_negative (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : m < 0) (c : Charge D) (n : ℕ) (p : Oscillator D) (hp : p ∈ polynomialLength D n) :
    ∃ q ∈ polynomialLength D (n + 1),
      ((jet D x)[[m]]) (Finsupp.single c p) = Finsupp.single c q := by
  let k := (-(m - (x.2 : ℤ)) - 1).toNat
  have hmode : m - (x.2 : ℤ) = -(k : ℤ) - 1 := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  rw [derivative_modes, LinearMap.smul_apply, hmode]
  change ∃ q ∈ polynomialLength D (n + 1),
    ((Ring.choose (-m - 1 + (x.2 : ℤ)) x.2 : ℤ) : ℂ) •
      neutralMode D x.1 (-(k : ℤ) - 1) (Finsupp.single c p) = Finsupp.single c q
  rw [neutralMode_single, neutralPolynomialMode_negative, LinearMap.mulLeft_apply]
  rw [Finsupp.smul_single]
  exact ⟨_, Submodule.smul_mem _ _ (polynomial_create_mem D (x.1, k) n p hp), rfl⟩

private theorem charged_jet_nonneg_word (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : 0 ≤ m) (c : Charge D) (w : List (Index D)) :
    ∃ k ≤ w.length, ∃ p ∈ polynomialLength D k,
      ((jet D x)[[m]]) (Finsupp.single c (neutralPolynomial D w)) = Finsupp.single c p := by
  rw [derivative_modes, LinearMap.smul_apply]
  rcases lt_trichotomy m (x.2 : ℤ) with h | h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m - 1 + (x.2 : ℤ) by omega)
    rw [hk, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show k < x.2 by omega)]
    exact ⟨w.length, le_rfl, 0, Submodule.zero_mem _, by simp⟩
  · rw [show m - (x.2 : ℤ) = 0 by omega]
    change ∃ k ≤ w.length, ∃ p ∈ polynomialLength D k,
      ((Ring.choose (-m - 1 + (x.2 : ℤ)) x.2 : ℤ) : ℂ) •
        neutralMode D x.1 0 (Finsupp.single c (neutralPolynomial D w)) = Finsupp.single c p
    rw [neutralMode_single]
    simp only [neutralPolynomialMode, lt_self_iff_false, ite_false, ite_true,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [Finsupp.smul_single]
    exact ⟨w.length, le_rfl, _, Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (polynomial_word_mem D w)), rfl⟩
  · let k := (m - (x.2 : ℤ) - 1).toNat
    have hmode : m - (x.2 : ℤ) = (k : ℤ) + 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [hmode]
    change ∃ l ≤ w.length, ∃ p ∈ polynomialLength D l,
      ((Ring.choose (-m - 1 + (x.2 : ℤ)) x.2 : ℤ) : ℂ) •
        neutralMode D x.1 ((k : ℤ) + 1) (Finsupp.single c (neutralPolynomial D w)) =
          Finsupp.single c p
    rw [neutralMode_single, neutralPolynomialMode_positive, LinearMap.smul_apply]
    rw [Finsupp.smul_single]
    exact ⟨w.length - 1, Nat.sub_le _ _, _, Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (annihilate_word_mem D x.1 k w)), rfl⟩

private theorem symmetrize_jet_contraction_mem (D : LatticeData) (x y : Index D)
    (m n : ℤ) (hm : m < 0) (hn : 0 ≤ n) (c : Charge D) (w : List (Index D)) :
    symmetrize D (((jet D x)[[m]]) (((jet D y)[[n]])
      (Finsupp.single c (neutralPolynomial D w)))) ∈ fixedChargedWordBelow D c (w.length + 2) := by
  obtain ⟨k, hk, p, hp, he⟩ := charged_jet_nonneg_word D y n hn c w
  rw [he]
  obtain ⟨q, hq, he⟩ := charged_jet_negative D x m hm c k p hp
  rw [he]
  exact polynomialLength_symmetrize_mem D c (k + 1) _ (by omega) q hq

/-- The actual quadratic `(-1)` mode has pair concatenation as its leading term.
All corrections are fixed words on the same orbit of length at most `w.length + 1`. -/
theorem fixed_quadratic_charged_word_length (D : LatticeData) (c : Charge D)
    (x y : Index D) (w : List (Index D)) :
    fixedMode D (neutralPair D x.1 y.1 x.2 y.2) (-1) (fixedChargedWord D c w) -
      fixedChargedWord D c (x :: y :: w) ∈ fixedChargedWordBelow D c (w.length + 2) := by
  let v := Finsupp.single c (neutralPolynomial D w)
  let a := neutralPair D x.1 y.1 x.2 y.2
  let first (j : ℕ) := ((jet D x)[[-(j : ℤ) - 1]]) (((jet D y)[[(-1 : ℤ) + j]]) v)
  let second (j : ℕ) := ((jet D y)[[(-1 : ℤ) - 1 - (j : ℤ)]]) (((jet D x)[[j]]) v)
  obtain ⟨hf, hs, he⟩ : Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      mu D a.val (-1) v = (∑ᶠ j, first j) + (∑ᶠ j, second j) :=
    quadratic_iterate D x y v (-1)
  have leading : symmetrize D (first 0) = fixedChargedWord D c (x :: y :: w) := by
    change symmetrize D (((jet D x)[[-1]]) (((jet D y)[[-1]])
      (Finsupp.single c (neutralPolynomial D w)))) = _
    rw [derivative_creation D y c, derivative_creation D x c, symmetrize_single]
    rfl
  let S := fixedChargedWordBelow D c (w.length + 2)
  let Q := S.mkQ.comp (symmetrize D)
  have first_image : Q (∑ᶠ j, first j) = Q (first 0) := by
    rw [map_finsum Q hf]
    apply finsum_eq_single _ 0
    intro j hj
    change S.mkQ (symmetrize D (first j)) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (symmetrize_jet_contraction_mem D x y _ _ (by omega) (by omega) c w)
  have second_image : Q (∑ᶠ j, second j) = 0 := by
    rw [map_finsum Q hs]
    exact finsum_eq_zero_of_forall_eq_zero fun j =>
      (Submodule.Quotient.mk_eq_zero S).mpr
        (symmetrize_jet_contraction_mem D y x _ _ (by omega) (by omega) c w)
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQ (fixedMode D a (-1) (fixedChargedWord D c w) - _) = 0
  rw [show fixedChargedWord D c w = symmetrize D v from (symmetrize_single D c _).symm,
    ← symmetrize_mode, ← leading, map_sub]
  change Q (mu D a.val (-1) v) - Q (first 0) = 0
  rw [he, map_add, first_image, second_image, add_zero, sub_self]

private theorem fixed_charged_polynomial_mem_orbit (D : LatticeData) (c : Charge D)
    (p : Oscillator D) : fixedChargedPolynomial D c p ∈ fixedChargeOrbit D c := by
  change Finsupp.single c p + Finsupp.single (-c) (sigma D p) ∈
    Finsupp.supported (Oscillator D) ℂ ({c, -c} : Set (Charge D))
  exact Submodule.add_mem _ (Finsupp.single_mem_supported ℂ _ (by simp))
    (Finsupp.single_mem_supported ℂ _ (by simp))

private theorem fixed_mem_of_symmetrized_support (D : LatticeData)
    (S : Submodule ℂ (FixedCarrier D)) (v : FixedCarrier D)
    (h : ∀ c ∈ v.val.support, symmetrize D (Finsupp.single c (v.val c)) ∈ S) :
    v ∈ S := by
  classical
  have hv : (∑ c ∈ v.val.support, symmetrize D (Finsupp.single c (v.val c))) ∈ S :=
    S.sum_mem h
  rw [← map_sum] at hv
  change symmetrize D (v.val.sum Finsupp.single) ∈ S at hv
  rw [Finsupp.sum_single] at hv
  have he : symmetrize D v.val = (2 : ℂ) • v := by
    change (2 : ℂ) • plusProjection D v.val = _
    rw [plusProjection_fixed]
  rw [he] at hv
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] using
    S.smul_mem (2 : ℂ)⁻¹ hv

/-- The fixed words span the full fixed orbit, including at the coincident charge zero. -/
theorem fixed_charge_orbit_eq_span_words (D : LatticeData) (c : Charge D) :
    fixedChargeOrbit D c = Submodule.span ℂ (Set.range (fixedChargedWord D c)) := by
  let S := Submodule.span ℂ (Set.range (fixedChargedWord D c))
  have all_polynomials (p : Oscillator D) : fixedChargedPolynomial D c p ∈ S := by
    let f : Oscillator D →ₗ[ℂ] FixedCarrier D := (symmetrize D).comp (Finsupp.lsingle c)
    have hle : (⊤ : Submodule ℂ (Oscillator D)) ≤ S.comap f := by
      rw [← (basisMonomials (Index D) ℂ).span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨e, rfl⟩
      change symmetrize D (Finsupp.single c (monomial e 1)) ∈ S
      rw [symmetrize_single, ← occurrences_product D e]
      exact Submodule.subset_span ⟨occurrences D e, rfl⟩
    have hp : p ∈ S.comap f := hle Submodule.mem_top
    change symmetrize D (Finsupp.single c p) ∈ S at hp
    rwa [symmetrize_single] at hp
  apply le_antisymm
  · intro v hv
    apply fixed_mem_of_symmetrized_support D S v
    intro d hd
    change v.val ∈ Finsupp.supported (Oscillator D) ℂ ({c, -c} : Set (Charge D)) at hv
    have hdc := (Finsupp.mem_supported ℂ v.val).mp hv hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdc
    rw [symmetrize_single]
    rcases hdc with rfl | rfl
    · exact all_polynomials (v.val d)
    · have he (p : Oscillator D) :
          fixedChargedPolynomial D (-c) p = fixedChargedPolynomial D c (sigma D p) := by
        apply Subtype.ext
        change Finsupp.single (-c) p + Finsupp.single (-(-c)) (sigma D p) =
          Finsupp.single c (sigma D p) + Finsupp.single (-c) (sigma D (sigma D p))
        rw [neg_neg, sigma_involutive D p, add_comm]
      rw [he]
      exact all_polynomials _
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    exact fixed_charged_polynomial_mem_orbit D c _

private theorem fixed_charged_word_nil (D : LatticeData) (c : Charge D) :
    fixedChargedWord D c [] = fixedGroundOrbit D c := by
  apply Subtype.ext
  rw [fixedGroundOrbit_val]
  simp [fixedChargedWord, fixedChargedPolynomial, neutralPolynomial, E, ground]

/-- A quadratic-stable submodule containing the ground and every single oscillator
contains the entire fixed charge orbit. -/
theorem fixed_charge_orbit_le_of_ground_and_singles (D : LatticeData) (c : Charge D)
    (S : Submodule ℂ (FixedCarrier D)) (hground : fixedGroundOrbit D c ∈ S)
    (hsingle : ∀ (i : Fin D.rank) (k : ℕ), fixedChargedOscillator D i k c ∈ S)
    (hmode : ∀ (x y : Index D) (v : FixedCarrier D), v ∈ S →
      fixedMode D (neutralPair D x.1 y.1 x.2 y.2) (-1) v ∈ S) :
    fixedChargeOrbit D c ≤ S := by
  have words (n : ℕ) (w : List (Index D)) (hw : w.length = n) :
      fixedChargedWord D c w ∈ S := by
    induction n using Nat.strong_induction_on generalizing w with
    | h n ih =>
        cases w with
        | nil => simpa only [fixed_charged_word_nil] using hground
        | cons x w =>
            cases w with
            | nil =>
                simpa only [fixedChargedWord, neutralPolynomial, List.map_cons,
                  List.map_nil, List.prod_cons, List.prod_nil, mul_one, fixedChargedOscillator]
                  using hsingle x.1 x.2
            | cons y w =>
                have ht : w.length < n := by simp only [List.length_cons] at hw; omega
                have hprod := hmode x y _ (ih w.length ht w rfl)
                have hle : fixedChargedWordBelow D c (w.length + 2) ≤ S := by
                  refine Submodule.span_le.mpr ?_
                  rintro _ ⟨u, hu, rfl⟩
                  exact ih u.length (by simp only [List.length_cons] at hw; omega) u rfl
                have h := S.sub_mem hprod (hle (fixed_quadratic_charged_word_length D c x y w))
                rwa [sub_sub_cancel] at h
  rw [fixed_charge_orbit_eq_span_words]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  exact words w.length w rfl

/-- A ground reduction into one orbit extends to its entire fixed oscillator sector. -/
theorem fixed_charge_orbit_le_sup_orbit (D : LatticeData) (c δ : Charge D)
    (hB : 4 ≤ bilinear D c c) (hE : fixedGroundOrbit D c ∈ fixedC2 D ⊔ fixedChargeOrbit D δ) :
    fixedChargeOrbit D c ≤ fixedC2 D ⊔ fixedChargeOrbit D δ :=
  fixed_charge_orbit_le_of_ground_and_singles D c _ hE
    (fixed_charged_oscillator_mem_sup_orbit D c δ hB hE) fun x y v hv =>
      quadratic_mem_c2_sup_orbit D x y (-1) (Or.inr rfl) δ v hv

/-- The signed basis step reduces the whole fixed orbit of each outside-short Leech charge. -/
theorem leech_fixed_charge_orbit_step_outside_short (c : Charge leechData)
    (hc : c ∉ ActualC2Cofinite.shortCharges leechData) :
    ∃ (i : Fin leechData.rank) (a : Charge leechData),
      (a = unitCharge leechData i ∨ a = -unitCharge leechData i) ∧
      let δ := c - (2 : ℤ) • a
      (chargeEnergy leechData δ).toNat < (chargeEnergy leechData c).toNat ∧
      fixedChargeOrbit leechData c ≤ fixedC2 leechData ⊔ fixedChargeOrbit leechData δ := by
  obtain ⟨i, a, ha, hs, hground, henergy, hdecrease⟩ :=
    leech_fixed_ground_charge_step_outside_short c hc
  let δ := c - (2 : ℤ) • a
  change chargeEnergy leechData c - chargeEnergy leechData δ = _ at henergy
  have hn := chargeEnergy_nonneg leechData ActualLeechHyperbolic.leech_spec.2.2.1 δ
  have hb := two_chargeEnergy leechData c
  refine ⟨i, a, ha, hdecrease, fixed_charge_orbit_le_sup_orbit leechData c δ ?_ ?_⟩
  · omega
  · exact ground_mem_sup_orbit leechData _ c δ _ hground

private theorem leech_charge_orbit_le_c2_sup_short (c : Charge leechData) :
    fixedChargeOrbit leechData c ≤ fixedC2 leechData ⊔
      ⨆ d : ActualC2Cofinite.shortCharges leechData, fixedChargeOrbit leechData d.val := by
  let S := ⨆ d : ActualC2Cofinite.shortCharges leechData, fixedChargeOrbit leechData d.val
  change fixedChargeOrbit leechData c ≤ fixedC2 leechData ⊔ S
  generalize he : (chargeEnergy leechData c).toNat = n
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
      by_cases hc : c ∈ ActualC2Cofinite.shortCharges leechData
      · exact (le_iSup (fun d : ActualC2Cofinite.shortCharges leechData =>
          fixedChargeOrbit leechData d.val) ⟨c, hc⟩).trans le_sup_right
      · obtain ⟨_, a, _, hd, hle⟩ := leech_fixed_charge_orbit_step_outside_short c hc
        exact hle.trans (sup_le le_sup_left (ih _ (he ▸ hd) (c - (2 : ℤ) • a) rfl))

/-- The intrinsic fixed Leech C₂ quotient is spanned by the images of the finitely
many fixed charge orbits indexed by the exact Gram-coordinate short set. -/
theorem leech_fixed_c2_finite_charge_support :
    (ActualC2Cofinite.shortCharges leechData).Finite ∧
    (⨆ c : ActualC2Cofinite.shortCharges leechData,
      (fixedChargeOrbit leechData c.val).map (fixedC2 leechData).mkQ) = ⊤ := by
  refine ⟨shortCharges_finite leechData ActualLeechHyperbolic.leech_spec.2.2.1, ?_⟩
  rw [← Submodule.map_iSup, Submodule.map_mkQ_eq_top, eq_top_iff]
  intro v _
  apply fixed_mem_of_symmetrized_support leechData _ v
  intro c _
  rw [symmetrize_single]
  exact leech_charge_orbit_le_c2_sup_short c (fixed_charged_polynomial_mem_orbit leechData c _)

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_quadratic_charged_word_length
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charge_orbit_eq_span_words
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charge_orbit_le_of_ground_and_singles
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_charge_orbit_le_sup_orbit
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_charge_orbit_step_outside_short
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_c2_finite_charge_support
