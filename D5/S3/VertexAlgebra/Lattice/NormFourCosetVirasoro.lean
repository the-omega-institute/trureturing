/- GID: D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual mixed Sugawara products and the norm-four commuting Virasoro complement. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import D5.S3.VertexAlgebra.LatticeActualConformalWard
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-!
The norm-four state is the classical formula recorded by Shimakura,
arXiv:1202.6107, (1.3), attributed there to Dong--Mason--Zhu, Theorem 6.3.
The lattice fields follow Bakalov--Kac, math/0402315, section 4.1.
The imported normal-product and Sugawara sources retain their Carnahan and
Kytola Apache 2.0 attribution. The new calculation here is the actual mixed
OPE, its reverse via the vacuum commutator, and the actual field complement.
No simplicity, fusion, commutant-VOA or Monster construction is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open private currentStateAlong currentMode currentMode_sum currentMode_negative
  currentMode_current osc_zero central_binomial
  from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

namespace D5.S3.VertexAlgebra.Lattice.NormFourCosetVirasoro

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open LatticeActualConformalState LatticeActualConformalWard
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeSugawaraVirasoro
open NormFourVirasoroVector
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator

noncomputable section

/-- The complement is a state of the original full lattice carrier. -/
def cosetVector (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a : Charge D) (s : ℂ) : Carrier D := omega D H - vector D a s

/-- Modes of the actual state field, with Virasoro indexing. -/
def cosetMode (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a : Charge D) (s : ℂ) (m : ℤ) : Module.End ℂ (Carrier D) :=
  ((Y D (cosetVector D H a s))[[m + 1]])

private theorem current_step (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ) (v : Carrier D) :
    sugawaraMode D H m (currentMode D a (-1) v) =
      currentMode D a (-1) (sugawaraMode D H m v) + currentMode D a (m - 1) v := by
  classical
  have h : sugawaraMode D H m * currentMode D a (-1) -
      currentMode D a (-1) * sugawaraMode D H m = currentMode D a (m - 1) := by
    rw [currentMode_sum, currentMode_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, ← Finset.sum_sub_distrib, ← smul_sub,
      sugawaraMode_current_commutator D H hHG hGH]
    norm_num [currentMode_sum, sub_eq_add_neg]
  have hv := LinearMap.congr_fun h v
  change sugawaraMode D H m (currentMode D a (-1) v) -
    currentMode D a (-1) (sugawaraMode D H m v) = _ at hv
  exact (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)

private theorem sugawara_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (hm : -1 ≤ m) :
    sugawaraMode D H m (vacuum D) = 0 := by
  rw [← omega_modes]
  exact stateField_creativity D (omega D H) (m + 1) (by omega)

private theorem current_creation (D : LatticeData) (a : Charge D) :
    currentMode D a (-1) (vacuum D) = currentStateAlong D a :=
  stateField_creation D (currentStateAlong D a)

private theorem quadratic_creation (D : LatticeData) (a : Charge D) :
    currentMode D a (-1) (currentStateAlong D a) = quadraticState D a := by
  simpa [currentStateAlong, quadraticState, osc_zero, pow_two] using
    currentMode_negative D a 0 0 (chargePolynomial D a)

private theorem sugawara_current (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ) (hm : 0 ≤ m) :
    sugawaraMode D H m (currentStateAlong D a) =
      if m = 0 then currentStateAlong D a else 0 := by
  rw [← current_creation D a, current_step D H hHG hGH,
    sugawara_vacuum D H m (by omega), map_zero, zero_add]
  by_cases hz : m = 0
  · subst m
    simp [current_creation]
  · rw [ite_eq_right hz]
    exact stateField_creativity D (currentStateAlong D a) (m - 1) (by omega)

private theorem sugawara_quadratic (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (m : ℤ) (hm : 0 ≤ m) :
    sugawaraMode D H m (quadraticState D a) =
      if m = 0 then (2 : ℂ) • quadraticState D a
      else if m = 2 then (bilinear D a a : ℂ) • vacuum D else 0 := by
  rw [← quadratic_creation D a, current_step D H hHG hGH,
    sugawara_current D H hHG hGH a m hm]
  by_cases hz : m = 0
  · subst m
    simp only [ite_true, zero_sub, quadratic_creation]
    module
  · rw [ite_eq_right hz, ite_eq_right hz, map_zero, zero_add,
      currentMode_current D a (m - 1) (by omega)]
    simp only [show m - 1 = 1 ↔ m = 2 by omega]

private theorem forward_products (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    mu D (omega D H) 0 (vector D a s) = translation D (vector D a s) ∧
    mu D (omega D H) 1 (vector D a s) = (2 : ℂ) • vector D a s ∧
    mu D (omega D H) 2 (vector D a s) = 0 ∧
    mu D (omega D H) 3 (vector D a s) = (1 / 4 : ℂ) • vacuum D ∧
    ∀ j : ℤ, 4 ≤ j → mu D (omega D H) j (vector D a s) = 0 := by
  have ground_zero (b : Charge D) (hb : bilinear D b b = 4) :
      sugawaraMode D H 0 (Finsupp.single b (1 : Oscillator D)) =
        (2 : ℂ) • Finsupp.single b (1 : Oscillator D) := by
    rw [sugawaraMode_ground_zero, chargeQuadratic_eq D H hHG hGH, hb]
    norm_num
  have negnorm : bilinear D (-a) (-a) = 4 := by
    rw [bilinear_neg_left, bilinear_neg_right, neg_neg, ha]
  have positive (m : ℤ) (hm : 0 < m) :
      sugawaraMode D H m (vector D a s) =
        if m = 2 then (1 / 4 : ℂ) • vacuum D else 0 := by
    simp only [vector, chargedState, map_add, map_smul,
      sugawaraMode_ground_positive D H a m hm,
      sugawaraMode_ground_positive D H (-a) m hm, add_zero, smul_zero,
      sugawara_quadratic D H hHG hGH a m hm.le, ite_eq_right (ne_of_gt hm), ha]
    split_ifs <;> norm_num [smul_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [omega_product, show (0 : ℤ) - 1 = -1 by omega,
      sugawaraMode_minus_one_eq_translation D H hHG hGH]
  · rw [omega_product, sub_self]
    simp only [vector, chargedState, map_add, map_smul,
      ground_zero a ha, ground_zero (-a) negnorm,
      sugawara_quadratic D H hHG hGH a 0 (by omega), ite_true]
    module
  · rw [omega_product, show (2 : ℤ) - 1 = 1 by omega, positive 1 (by omega)]
    norm_num
  · rw [omega_product, show (3 : ℤ) - 1 = 2 by omega, positive 2 (by omega)]
    norm_num
  · intro j hj
    rw [omega_product, positive (j - 1) (by omega), ite_eq_right (by omega)]

private theorem mixed_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (m n : ℤ) :
    sugawaraMode D H m * mode D a s n - mode D a s n * sugawaraMode D H m =
      ((m : ℂ) - (n : ℂ)) • mode D a s (m + n) +
        (if m + n = 0 then
          (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (Carrier D))
        else 0) := by
  classical
  obtain ⟨h0, h1, h2, h3, ht⟩ := forward_products D H hHG hGH a ha s
  have action (j : ℤ) : sugawaraMode D H (j - 1) (vector D a s) =
      mu D (omega D H) j (vector D a s) := (omega_product D H _ j).symm
  have finite : (∑ᶠ j : ℕ, wardTerm D H (vector D a s) m (n + 1) j) =
      ∑ j ∈ Finset.range 4, wardTerm D H (vector D a s) m (n + 1) j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra outside
    exact hj (by simp [wardTerm, action, ht j (by omega)])
  have term0 : wardTerm D H (vector D a s) m (n + 1) 0 =
      -((m + n + 2 : ℤ) : ℂ) • mode D a s (m + n) := by
    unfold wardTerm
    simp only [Nat.cast_zero]
    rw [action, h0, show m + (n + 1) + 1 - (0 : ℤ) = m + n + 2 by omega,
      state_derivative_modes, show m + n + 2 - 1 = m + n + 1 by omega]
    simp only [integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul] <;> rfl
  have term1 : wardTerm D H (vector D a s) m (n + 1) 1 =
      (2 * ((m + 1 : ℤ) : ℂ)) • mode D a s (m + n) := by
    unfold wardTerm
    simp only [Nat.cast_one]
    rw [action, h1]
    simp only [map_smul, Pi.smul_apply, smul_smul, integerBinomial,
      Ring.choose_one_right]
    rw [show m + (n + 1) + 1 - (1 : ℤ) = m + n + 1 by omega]
    change _ • mode D a s (m + n) = _
    congr 1
    ring
  have term2 : wardTerm D H (vector D a s) m (n + 1) 2 = 0 := by
    have h2' : sugawaraMode D H 1 (vector D a s) = 0 := by
      simpa only [omega_product, show (2 : ℤ) - 1 = 1 by omega] using h2
    simp [wardTerm, h2']
  have term3 : wardTerm D H (vector D a s) m (n + 1) 3 =
      if m + n = 0 then
        (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (Carrier D)) else 0 := by
    unfold wardTerm
    norm_num only [Nat.cast_ofNat]
    have h3' : sugawaraMode D H 2 (vector D a s) = (1 / 4 : ℂ) • vacuum D := by
      simpa only [omega_product, show (3 : ℤ) - 1 = 2 by omega] using h3
    rw [h3']
    simp only [map_smul, Pi.smul_apply, stateField_vacuum, identity_modes, smul_smul]
    rw [show m + (n + 1) + 1 - (3 : ℤ) = m + n - 1 by omega]
    by_cases hmn : m + n = 0
    · rw [ite_eq_left hmn, ite_eq_left (show m + n - 1 = -1 by omega)]
      change _ • (1 : Module.End ℂ (Carrier D)) = _
      congr 1
      simpa only [mul_comm] using central_binomial m
    · simp [hmn, show m + n - 1 ≠ -1 by omega]
  have h := ward_commutator D H (vector D a s) m (n + 1)
  change sugawaraMode D H m * mode D a s n - mode D a s n * sugawaraMode D H m = _ at h
  rw [finite] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h
  rw [term0, term1, term2, term3] at h
  rw [h]
  push_cast
  module

private theorem reverse_action (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (m : ℤ) (hm : -1 ≤ m) :
    mode D a s m (omega D H) =
      ((m : ℂ) + 2) • mode D a s (m - 2) (vacuum D) +
        (if m = 2 then (1 / 4 : ℂ) • vacuum D else 0) := by
  have hv : mode D a s m (vacuum D) = 0 :=
    stateField_creativity D (vector D a s) (m + 1) (by omega)
  have ho : sugawaraMode D H (-2) (vacuum D) = omega D H := by
    rw [← omega_modes]
    exact stateField_creation D (omega D H)
  have h := LinearMap.congr_fun (mixed_commutator D H hHG hGH a ha s (-2) m) (vacuum D)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_zero, ho,
    LinearMap.add_apply, LinearMap.smul_apply, zero_sub,
    show (-2 : ℤ) + m = m - 2 by omega] at h
  by_cases he : m = 2
  · subst m
    norm_num at h ⊢
    linear_combination (norm := module) -h
  · simp only [ite_eq_right (show ¬(m - 2 = 0) by omega),
      LinearMap.zero_apply, add_zero] at h
    rw [ite_eq_right he, add_zero]
    linear_combination (norm := module) -h

/-- Both actual singular OPE orientations, including every nonnegative tail.
The mixed commutator is an equality of endomorphisms of the entire carrier. -/
theorem mixed_products (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    (∀ j : ℤ, 0 ≤ j →
      mu D (omega D H) j (vector D a s) =
        (if j = 0 then translation D (vector D a s)
         else if j = 1 then (2 : ℂ) • vector D a s
         else if j = 3 then (1 / 4 : ℂ) • vacuum D else 0) ∧
      mu D (vector D a s) j (omega D H) =
        (if j = 0 then translation D (vector D a s)
         else if j = 1 then (2 : ℂ) • vector D a s
         else if j = 3 then (1 / 4 : ℂ) • vacuum D else 0)) ∧
    (∀ m n : ℤ,
      sugawaraMode D H m * mode D a s n - mode D a s n * sugawaraMode D H m =
        ((m : ℂ) - (n : ℂ)) • mode D a s (m + n) +
          (if m + n = 0 then
            (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (Carrier D)) else 0)) := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := forward_products D H hHG hGH a ha s
  refine ⟨?_, mixed_commutator D H hHG hGH a ha s⟩
  intro j hj
  constructor
  · by_cases z : j = 0
    · subst j; simpa using h0
    · by_cases o : j = 1
      · subst j; simpa using h1
      · by_cases t : j = 3
        · subst j; simpa using h3
        · by_cases two : j = 2
          · subst j; simpa using h2
          · simpa [z, o, t] using ht j (by omega)
  · have index : j = (j - 1) + 1 := by omega
    unfold mu
    conv_lhs => rw [index]
    change mode D a s (j - 1) (omega D H) = _
    rw [reverse_action D H hHG hGH a ha s (j - 1) (by omega)]
    by_cases z : j = 0
    · subst j
      norm_num [mode, ← LatticeActualVertexAlgebra.translation_as_mode]
    · by_cases o : j = 1
      · subst j
        norm_num [mode, stateField_creation]
      · by_cases t : j = 3
        · subst j
          norm_num [mode, stateField_creativity D (vector D a s) 1 (by omega)]
        · have hv : mode D a s (j - 1 - 2) (vacuum D) = 0 := by
            apply stateField_creativity
            omega
          simp [z, o, t, hv, show j - 1 ≠ 2 by omega]

private theorem coset_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) (s : ℂ) (m : ℤ) :
    cosetMode D H a s m = sugawaraMode D H m - mode D a s m := by
  simp only [cosetMode, cosetVector, map_sub, VertexOperator.ncoeff,
    Pi.sub_apply, mode, ← omega_modes]

/-- The actual complementary field and modes on the full production carrier:
all integer modes commute with the norm-four action and satisfy Virasoro with
central charge rank minus one half. -/
theorem coset_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Y D (cosetVector D H a s) = sugawaraField D H - Y D (vector D a s) ∧
    (∀ m : ℤ, cosetMode D H a s m = sugawaraMode D H m - mode D a s m) ∧
    (∀ m n : ℤ,
      cosetMode D H a s m * mode D a s n - mode D a s n * cosetMode D H a s m = 0) ∧
    (∀ m n : ℤ,
      cosetMode D H a s m * cosetMode D H a s n -
          cosetMode D H a s n * cosetMode D H a s m =
        ((m : ℂ) - (n : ℂ)) • cosetMode D H a s (m + n) +
          (if m + n = 0 then
            (((D.rank : ℂ) - 1 / 2) / 12 * ((m : ℂ)^3 - (m : ℂ))) •
              (1 : Module.End ℂ (Carrier D)) else 0)) := by
  have mixed := (mixed_products D H hHG hGH a ha s).2
  have commuting (m n : ℤ) :
      cosetMode D H a s m * mode D a s n - mode D a s n * cosetMode D H a s m = 0 := by
    rw [coset_modes]
    calc
      _ = (sugawaraMode D H m * mode D a s n - mode D a s n * sugawaraMode D H m) -
          (mode D a s m * mode D a s n - mode D a s n * mode D a s m) := by
            simp only [sub_mul, mul_sub]
            abel
      _ = 0 := by rw [mixed, virasoro_commutator D a ha s hs]; abel
  refine ⟨?_, coset_modes D H a s, commuting, ?_⟩
  · simp only [cosetVector, map_sub, Y_omega]
  · intro m n
    have hmn := commuting m n
    have hnm := commuting n m
    simp only [coset_modes, sub_mul, mul_sub] at hmn hnm
    rw [coset_modes, coset_modes, coset_modes]
    calc
      _ = (sugawaraMode D H m * sugawaraMode D H n -
            sugawaraMode D H n * sugawaraMode D H m) -
          (mode D a s m * mode D a s n - mode D a s n * mode D a s m) := by
        simp only [sub_mul, mul_sub]
        linear_combination (norm := abel) -hmn + hnm
      _ = _ := by
        rw [sugawaraMode_virasoro D H hHG hGH, virasoro_commutator D a ha s hs]
        push_cast
        by_cases h : m + n = 0 <;> simp only [h, ite_true, ite_false, zero_smul]
        · module
        · module

end
end D5.S3.VertexAlgebra.Lattice.NormFourCosetVirasoro
