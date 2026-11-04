/- GID: D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrameEndpoints
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Actual finite Sugawara endpoints and fixed-charge strict-raising remainders. -/

import D5.S3.VertexAlgebra.Lattice.LatticeSugawaraNullFrame
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import Mathlib.Tactic

/-! State-dependent finite capture and endpoints of the original Sugawara operator.
The missing endpoint of the original asymmetric capture vanishes on its actual
input. The two nonzero endpoints give the original momentum current; at zero the
single endpoint gives the integral charge energy. Fixed-charge hypotheses are
explicit. Finite mode sums are not identified with the full BRST operator.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeSugawaraNullFrameEndpoints

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeBRSTModeFiltration LatticeSugawaraNullFrame
open LatticeSugawaraVirasoro LatticeQuartetContraction
open private tensor_sub_left from D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.CountableOccupationFock

open private completeBasis_plus completeBasis_minus completeBasis_transverse repr_plus repr_minus repr_transverse from D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

variable {D : LatticeData}

/-- The actual current supplier's finite interval, including its asymmetric
lower endpoint. It is not replaced by a symmetric or charge-dependent bound. -/
def capture (n : ℤ) (v : Carrier D) : Finset ℤ :=
  Finset.Icc (min 0 (n - vectorFrequencyBound D v))
    (vectorFrequencyBound D v : ℤ)

/-- Both current indices are nonzero here, also when n=0. -/
def interior (n : ℤ) (v : Carrier D) : Finset ℤ :=
  ((capture n v).erase 0).erase n

theorem zero_mem_capture (n : ℤ) (v : Carrier D) : 0 ∈ capture n v := by
  exact Finset.mem_Icc.mpr ⟨min_le_left _ _, Int.natCast_nonneg _⟩

theorem mode_mem_capture_iff (n : ℤ) (v : Carrier D) :
    n ∈ capture n v ↔ n ≤ (vectorFrequencyBound D v : ℤ) := by
  have hR := Int.natCast_nonneg (vectorFrequencyBound D v)
  have hlo : min 0 (n - vectorFrequencyBound D v) ≤ n :=
    le_trans (min_le_right _ _) (by omega)
  simp only [capture, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨hlo, h⟩⟩

theorem mem_interior {n k : ℤ} {v : Carrier D} (hk : k ∈ interior n v) :
    k ∈ capture n v ∧ k ≠ 0 ∧ n-k ≠ 0 := by
  have hh := Finset.mem_erase.mp hk
  have hh' := Finset.mem_erase.mp hh.2
  exact ⟨hh'.2, hh'.1, by omega⟩

/-- The original H-weighted normal summand, before any change of basis. -/
def weightedNormal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (n k : ℤ) : Module.End ℂ (Carrier D) :=
  ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j • normalSummand D i j k (n-k)

/-- An absent k=n endpoint is actually zero: the positive n current is the
rightmost factor of the nonnegative normal-ordering branch. -/
theorem absent_endpoint_zero (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (n : ℤ) (v : Carrier D) (hn : n ∉ capture n v) :
    weightedNormal H n n v = 0 := by
  classical
  have hR : (vectorFrequencyBound D v : ℤ) < n := by
    exact lt_of_not_ge (fun h => hn ((mode_mem_capture_iff n v).mpr h))
  have hnpos : ¬ n < 0 := by
    have := Int.natCast_nonneg (vectorFrequencyBound D v)
    omega
  have hterm (i j : Fin D.rank) : normalSummand D i j n (n-n) v = 0 := by
    simp only [normalSummand, if_neg hnpos, Module.End.mul_apply,
      neutralMode_vanish D i v n hR, map_zero]
  simp only [weightedNormal, LinearMap.sum_apply, LinearMap.smul_apply, hterm,
    smul_zero, Finset.sum_const_zero]

theorem weighted_interval (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (n : ℤ) (v : Carrier D) :
    sugawaraMode D H n v =
      (2 : ℂ)⁻¹ • ∑ k ∈ capture n v, weightedNormal H n k v := by
  classical
  rw [sugawaraMode_interval_sum]
  apply congrArg (fun z : Carrier D => (2 : ℂ)⁻¹ • z)
  simp only [Finset.smul_sum]
  change (∑ i : Fin D.rank, ∑ j : Fin D.rank,
    ∑ k ∈ capture n v, H i j • normalSummand D i j k (n-k) v) = _
  calc
    _ = ∑ i : Fin D.rank, ∑ k ∈ capture n v, ∑ j : Fin D.rank,
        H i j • normalSummand D i j k (n-k) v := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k ∈ capture n v, ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j • normalSummand D i j k (n-k) v := by rw [Finset.sum_comm]
    _ = _ := by simp only [weightedNormal, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem extract_one {V : Type*} [AddCommMonoid V]
    (s : Finset ℤ) (f : ℤ → V) (r : ℤ) (hr : r ∈ s) :
    (∑ k ∈ s, f k) = f r + ∑ k ∈ s.erase r, f k := by
  classical
  calc
    _ = ∑ k ∈ insert r (s.erase r), f k := by rw [Finset.insert_erase hr]
    _ = _ := Finset.sum_insert (Finset.notMem_erase r s)

theorem extract_nonzero_endpoints
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) (hn : n ≠ 0)
    (v : Carrier D) :
    (∑ k ∈ capture n v, weightedNormal H n k v) =
      weightedNormal H n 0 v + weightedNormal H n n v +
        ∑ k ∈ interior n v, weightedNormal H n k v := by
  classical
  rw [extract_one (capture n v) (fun k => weightedNormal H n k v) 0
    (zero_mem_capture n v)]
  by_cases hmem : n ∈ capture n v
  · have he : n ∈ (capture n v).erase 0 := Finset.mem_erase.mpr ⟨hn, hmem⟩
    rw [extract_one ((capture n v).erase 0) (fun k => weightedNormal H n k v) n he]
    simp only [interior]
    abel
  · have he : n ∉ (capture n v).erase 0 := fun hh => hmem (Finset.mem_erase.mp hh).2
    rw [absent_endpoint_zero H n v hmem]
    simp [interior, Finset.erase_eq_of_notMem he]

theorem extract_zero_endpoint (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) :
    (∑ k ∈ capture 0 v, weightedNormal H 0 k v) =
      weightedNormal H 0 0 v + ∑ k ∈ interior 0 v, weightedNormal H 0 k v := by
  classical
  simpa [interior] using
    extract_one (capture 0 v) (fun k => weightedNormal H 0 k v) 0
      (zero_mem_capture 0 v)

/- Endpoint contraction is done in the ORIGINAL standard basis. In particular,
the transverse contribution is retained in the full momentum, not discarded. -/
private theorem zero_current_single (u : LatticeLightConeCoordinates.E D)
    (p : Charge D) (P : Oscillator D) :
    a u 0 (Finsupp.single p P) = g D u (chargeVector p) • Finsupp.single p P := by
  rw [a_single, polynomialCurrent_zero]
  simp only [Finsupp.smul_single]

private theorem zero_after_current (u v : LatticeLightConeCoordinates.E D)
    (p : Charge D) (n : ℤ) (P : Oscillator D) :
    a u 0 (a v n (Finsupp.single p P)) =
      g D u (chargeVector p) • a v n (Finsupp.single p P) := by
  rw [a_single, zero_current_single]

private theorem normal_at_zero (i j : Fin D.rank) (p : Charge D)
    (n : ℤ) (P : Oscillator D) :
    normalSummand D i j 0 n (Finsupp.single p P) =
      g D (standardBasis D i) (chargeVector p) •
        a (standardBasis D j) n (Finsupp.single p P) := by
  rw [← originalNormal_eq_normalSummand]
  simp only [originalNormal, if_neg (show ¬ (0 : ℤ) < 0 by omega), Module.End.mul_apply]
  rw [zero_current_single, map_smul]

/-- Both sign branches, including the reversed nonnegative normal order. -/
private theorem normal_at_mode (i j : Fin D.rank) (p : Charge D)
    (n : ℤ) (P : Oscillator D) :
    normalSummand D i j n 0 (Finsupp.single p P) =
      g D (standardBasis D j) (chargeVector p) •
        a (standardBasis D i) n (Finsupp.single p P) := by
  rw [← originalNormal_eq_normalSummand]
  by_cases hn : n < 0
  · simp only [originalNormal, if_pos hn, Module.End.mul_apply]
    rw [zero_current_single, map_smul]
  · simp only [originalNormal, if_neg hn, Module.End.mul_apply]
    exact zero_after_current _ _ p n P

private theorem contract_second
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (p : Charge D) (n : ℤ) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * g D (standardBasis D j) (chargeVector p)) •
        a (standardBasis D i) n) = a (chargeVector p) n := by
  classical
  have hrow (i : Fin D.rank) :
      (∑ j : Fin D.rank, H i j * g D (standardBasis D j) (chargeVector p)) =
        chargeVector p i := by
    calc
      _ = ∑ j : Fin D.rank, H i j * g D (chargeVector p) (standardBasis D j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [g_symm D (standardBasis D j) (chargeVector p)]
      _ = _ := inverse_covector H hHG (chargeVector p) i
  calc
    _ = ∑ i : Fin D.rank,
        (∑ j : Fin D.rank, H i j * g D (standardBasis D j) (chargeVector p)) •
          a (standardBasis D i) n := by simp only [Finset.sum_smul]
    _ = ∑ i : Fin D.rank, chargeVector p i • a (standardBasis D i) n := by
      simp_rw [hrow]
    _ = _ := (a_basis_expand (standardBasis D) (chargeVector p) n).symm

private theorem contract_first
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * g D (standardBasis D i) (chargeVector p)) •
        a (standardBasis D j) n) = a (chargeVector p) n := by
  classical
  have hs := inverseGram_symmetric (D := D) H hHG hGH
  have hcol (j : Fin D.rank) :
      (∑ i : Fin D.rank, H i j * g D (standardBasis D i) (chargeVector p)) =
        chargeVector p j := by
    calc
      _ = ∑ i : Fin D.rank, H j i * g D (chargeVector p) (standardBasis D i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : H i j = H j i := congrArg (fun M => M i j) hs
        rw [hij, g_symm D (standardBasis D i) (chargeVector p)]
      _ = _ := inverse_covector H hHG (chargeVector p) j
  calc
    _ = ∑ j : Fin D.rank,
        (∑ i : Fin D.rank, H i j * g D (standardBasis D i) (chargeVector p)) •
          a (standardBasis D j) n := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = ∑ j : Fin D.rank, chargeVector p j • a (standardBasis D j) n := by
      simp_rw [hcol]
    _ = _ := (a_basis_expand (standardBasis D) (chargeVector p) n).symm

theorem weighted_endpoint_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (P : Oscillator D) :
    weightedNormal H n 0 (Finsupp.single p P) =
      a (chargeVector p) n (Finsupp.single p P) := by
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single p P))
    (contract_first H hHG hGH p n)
  simpa only [weightedNormal, sub_zero, LinearMap.sum_apply, LinearMap.smul_apply,
    normal_at_zero, smul_smul] using hc

theorem weighted_endpoint_mode
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (p : Charge D) (n : ℤ) (P : Oscillator D) :
    weightedNormal H n n (Finsupp.single p P) =
      a (chargeVector p) n (Finsupp.single p P) := by
  have hc := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single p P))
    (contract_second H hHG p n)
  simpa only [weightedNormal, sub_self, LinearMap.sum_apply, LinearMap.smul_apply,
    normal_at_mode, smul_smul] using hc

private theorem half_double (v : Carrier D) : (2 : ℂ)⁻¹ • (v+v) = v := by
  rw [← two_smul ℂ v, smul_smul]
  norm_num

theorem charge_pairing (p : Charge D) :
    g D (chargeVector p) (chargeVector p) = (bilinear D p p : ℂ) := by
  simp [g, chargeVector, bilinear, Int.cast_sum, Int.cast_mul, mul_assoc]

theorem half_charge_pairing (p : Charge D) :
    (2 : ℂ)⁻¹ * g D (chargeVector p) (chargeVector p) =
      (LatticePositiveEnergy.chargeEnergy D p : ℂ) := by
  have hh : (2 : ℂ) * (LatticePositiveEnergy.chargeEnergy D p : ℂ) =
      g D (chargeVector p) (chargeVector p) := by
    rw [charge_pairing]
    exact_mod_cast LatticePositiveEnergy.two_chargeEnergy D p
  rw [← hh, ← mul_assoc]
  norm_num

/-- A finite operator for THIS input's capture. No infinite sum in End, and
no assertion that this input-dependent formula defines an all-input operator. -/
def interiorOperator (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (n : ℤ) (v : Carrier D) : Module.End ℂ (Carrier D) :=
  (2 : ℂ)⁻¹ • ∑ k ∈ interior n v, weightedNormal H n k

theorem nonzero_mode_split
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (hn : n ≠ 0) (P : Oscillator D) :
    sugawaraMode D H n (Finsupp.single p P) =
      a (chargeVector p) n (Finsupp.single p P) +
        interiorOperator H n (Finsupp.single p P) (Finsupp.single p P) := by
  rw [weighted_interval, extract_nonzero_endpoints H n hn,
    weighted_endpoint_zero H hHG hGH, weighted_endpoint_mode H hHG]
  rw [smul_add, half_double]
  simp only [interiorOperator, LinearMap.smul_apply, LinearMap.sum_apply]

/-- Exactly ONE k=0 endpoint. Its scalar is the original integral charge
energy bilinear(p,p)/2, with no normal-ordering intercept inserted. -/
theorem zero_mode_split
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : Oscillator D) :
    sugawaraMode D H 0 (Finsupp.single p P) =
      (LatticePositiveEnergy.chargeEnergy D p : ℂ) • Finsupp.single p P +
        interiorOperator H 0 (Finsupp.single p P) (Finsupp.single p P) := by
  rw [weighted_interval, extract_zero_endpoint,
    weighted_endpoint_zero H hHG hGH, zero_current_single, smul_add, smul_smul,
    half_charge_pairing]
  simp only [interiorOperator, LinearMap.smul_apply, LinearMap.sum_apply]

/-- Endpoint to subtract on the literal p sector. This is not a chargewise
replacement for the original Sugawara mode on other charges. -/
def endpoint (p : Charge D) (n : ℤ) : Module.End ℂ (Carrier D) :=
  if n = 0 then (LatticePositiveEnergy.chargeEnergy D p : ℂ) • 1
  else a (chargeVector p) n

theorem remainder_eq_interior_on_sector
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (P : Oscillator D) :
    (sugawaraMode D H n - endpoint p n) (Finsupp.single p P) =
      interiorOperator H n (Finsupp.single p P) (Finsupp.single p P) := by
  by_cases hn : n = 0
  · subst n
    simp only [LinearMap.sub_apply, endpoint, if_pos rfl, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [zero_mode_split H hHG hGH p P]
    exact add_sub_cancel_left _ _
  · simp only [LinearMap.sub_apply, endpoint, if_neg hn]
    rw [nonzero_mode_split H hHG hGH p n hn P]
    exact add_sub_cancel_left _ _

private theorem tp_add_left (A C : Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) :
    tp (A+C) G = tp A G + tp C G := by
  simp only [tp, TensorProduct.map_add_left]

private theorem tp_smul_left (z : ℂ) (A : Module.End ℂ (Carrier D))
    (G : Module.End ℂ Fock) : tp (z • A) G = z • tp A G := by
  simp only [tp, TensorProduct.map_smul_left]

private theorem tp_sum_left {ι : Type*} (s : Finset ι)
    (A : ι → Module.End ℂ (Carrier D)) (G : Module.End ℂ Fock) :
    tp (∑ i ∈ s, A i) G = ∑ i ∈ s, tp (A i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tp]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, tp_add_left, ih]

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

private theorem frame_cross_shift (k l q : ℤ) (hk : k ≠ 0) (hl : l ≠ 0) :
    Shift (actualBasis F B) degree
      (tp (frameNormal F B (plus t) (minus t) k l) (c q)) 1 := by
  by_cases hneg : k < 0
  · simpa [frameNormal, originalNormal, hneg, completeBasis_plus,
      completeBasis_minus] using original_cross_c_shift F B k l q hk hl
  · simpa [frameNormal, originalNormal, hneg, completeBasis_plus,
      completeBasis_minus] using original_reverse_cross_c_shift F B l k q hl hk

private theorem frame_reverse_cross_shift (k l q : ℤ) (hk : k ≠ 0) (hl : l ≠ 0) :
    Shift (actualBasis F B) degree
      (tp (frameNormal F B (minus t) (plus t) k l) (c q)) 1 := by
  by_cases hneg : k < 0
  · simpa [frameNormal, originalNormal, hneg, completeBasis_plus,
      completeBasis_minus] using original_reverse_cross_c_shift F B k l q hk hl
  · simpa [frameNormal, originalNormal, hneg, completeBasis_plus,
      completeBasis_minus] using original_cross_c_shift F B l k q hl hk

private theorem frame_transverse_shift (r s : Fin t) (k l q : ℤ) :
    Shift (actualBasis F B) degree
      (tp (frameNormal F B (transverse t r) (transverse t s) k l) (c q)) 1 := by
  by_cases hneg : k < 0
  · simpa [frameNormal, originalNormal, hneg, completeBasis_transverse] using
      original_transverse_pair_c_shift F B (B r) (B s) k l q
  · simpa [frameNormal, originalNormal, hneg, completeBasis_transverse] using
      original_transverse_pair_c_shift F B (B s) (B r) l k q

/-- This statement is about the WHOLE original H-weighted coefficient.
The ++, -- and mixed coefficients have already cancelled by the two-sided
inverse-Gram identities. It asserts nothing about an arbitrary raw aMinus². -/
theorem weighted_interior_c_shift
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (n k q : ℤ) (hk : k ≠ 0) (hl : n-k ≠ 0) :
    Shift (actualBasis F B) degree (tp (weightedNormal H n k) (c q)) 1 := by
  classical
  have he : weightedNormal H n k =
      frameNormal F B (plus t) (minus t) k (n-k) +
      frameNormal F B (minus t) (plus t) k (n-k) +
      ∑ r : Fin t, ∑ s : Fin t,
        frameCoeff F B H (transverse t r) (transverse t s) •
          frameNormal F B (transverse t r) (transverse t s) k (n-k) := by
    exact (weighted_normal_frame F B H k (n-k)).trans
      (weighted_frame_sector F B H hHG hGH k (n-k))
  rw [he]
  simp only [tp_add_left, tp_sum_left, tp_smul_left]
  apply shift_add
  · exact shift_add _ _ (frame_cross_shift F B k (n-k) q hk hl)
      (frame_reverse_cross_shift F B k (n-k) q hk hl)
  · apply shift_sum
    intro r hr
    apply shift_sum
    intro s hs
    exact shift_smul _ _ _ (frame_transverse_shift F B r s k (n-k) q)

theorem finite_interior_c_shift
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (n : ℤ) (v : Carrier D) :
    Shift (actualBasis F B) degree (tp (interiorOperator H n v) (c (-n))) 1 := by
  classical
  simp only [interiorOperator, tp_smul_left, tp_sum_left]
  apply shift_smul
  apply shift_sum
  intro k hk
  have hh := mem_interior hk
  exact weighted_interior_c_shift F B H hHG hGH n k (-n) hh.2.1 hh.2.2

/-- The original tensor action equals the genuine finite interior on a literal
charge-p basis vector. The capture uses its actual original matter polynomial,
not the coordinate polynomial's unproved frequency bound. -/
theorem original_remainder_basis_action
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (m : Exponents t) (S : Finset ℕ) :
    let v : Carrier D :=
      Finsupp.single p ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1))
    tp (sugawaraMode D H n - endpoint p n) (c (-n))
        (actualBasis F B (⟨p,m⟩,S)) =
      tp (interiorOperator H n v) (c (-n)) (actualBasis F B (⟨p,m⟩,S)) := by
  dsimp only
  simp only [actualBasis_apply]
  change tp _ _ (Finsupp.single p
    ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)) ⊗ₜ[ℂ] ket S) =
    tp _ _ (Finsupp.single p
      ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)) ⊗ₜ[ℂ] ket S)
  simp only [tp, TensorProduct.map_tmul]
  rw [remainder_eq_interior_on_sector H hHG hGH]

/-- Degree +1 for the ACTUAL remainder, only on basis inputs of actual charge p.
At n=0 the subtraction is the single genuine charge-energy endpoint. -/
theorem original_remainder_fixed_charge_degree
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      (tp (sugawaraMode D H n - endpoint p n) (c (-n)) (actualBasis F B i)) j ≠ 0) :
    degree j = degree i + 1 := by
  rcases i with ⟨⟨p',m⟩,S⟩
  dsimp only at hi
  subst p'
  rw [original_remainder_basis_action F B H hHG hGH p n m S] at hc
  exact finite_interior_c_shift F B H hHG hGH n
    (Finsupp.single p ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)))
      (⟨p,m⟩,S) j hc

/-- Nonzero-mode specialization: exact full momentum subtraction, with the
literal fixed-charge condition retained in the theorem statement. -/
theorem quadratic_minus_momentum_fixed_charge_degree
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      (tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n))
        (actualBasis F B i)) j ≠ 0) : degree j = degree i + 1 := by
  apply original_remainder_fixed_charge_degree F B H hHG hGH p n i j hi
  simpa only [endpoint, if_neg hn] using hc

theorem quadratic_minus_momentum_fixed_charge_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      (tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n))
        (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j := by
  rw [quadratic_minus_momentum_fixed_charge_degree F B H hHG hGH p n hn i j hi hc]

/-- A complete single nonzero matter-mode remainder after subtracting the
actual d0 summand. Its fixed-charge qualification is essential. This is still
not an identification or finite capture of the full BRST operator. -/
theorem sugawara_minus_leading_fixed_charge_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (n : ℤ) (hn : n ≠ 0) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      ((tp (sugawaraMode D H n) (c (-n)) -
        F.pPlus p • tp (a F.eMinus n) (c (-n))) (actualBasis F B i)) j ≠ 0) :
    degree i + 1 ≤ degree j := by
  have he : tp (sugawaraMode D H n) (c (-n)) -
      F.pPlus p • tp (a F.eMinus n) (c (-n)) =
      tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n)) +
        momentumRemainder F p n := by
    simp only [momentumRemainder, tp, tensor_sub_left]
    abel
  rw [he] at hc
  by_cases hq : (actualBasis F B).repr
      (tp (sugawaraMode D H n - a (chargeVector p) n) (c (-n))
        (actualBasis F B i)) j = 0
  · apply momentumRemainder_strictRaises F B p n hn i j
    intro hm
    exact hc (by simp [hq, hm])
  · exact quadratic_minus_momentum_fixed_charge_raises F B H hHG hGH p n hn i j hi hq

/-- An arbitrary finite set of original matter modes, subtracting the actual
charge-energy endpoint at zero and only the leading momentum summand elsewhere,
together with the original locally finite ghost cubic. This finite expression
has not been identified with the full BRST remainder. -/
def finiteRemainder (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Charge D) (modes : Finset ℤ) : Module.End ℂ (State D) :=
  (∑ n ∈ modes, (tp (sugawaraMode D H n) (c (-n)) -
    (if n = 0 then tp (endpoint p 0) (c 0)
    else F.pPlus p • tp (a F.eMinus n) (c (-n))))) +
    tp (1 : Module.End ℂ (Carrier D)) D5.S3.Quantum.Fermionic.BcGhostBRST.Qg

/-- All finite mode sets, both signs, and the distinct zero endpoint are
handled on every basis vector of the indicated original integral charge. -/
theorem finiteRemainder_fixed_charge_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (modes : Finset ℤ) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      (finiteRemainder F H p modes (actualBasis F B i)) j ≠ 0) :
    degree i + 1 ≤ degree j := by
  classical
  by_contra hw
  have hm (n : ℤ) : (actualBasis F B).repr
      ((tp (sugawaraMode D H n) (c (-n)) -
        if n = 0 then tp (endpoint p 0) (c 0)
        else F.pPlus p • tp (a F.eMinus n) (c (-n)))
          (actualBasis F B i)) j = 0 := by
    by_contra hnz
    apply hw
    by_cases hn : n = 0
    · subst n
      have hz : (actualBasis F B).repr
          (tp (sugawaraMode D H 0 - endpoint p 0) (c 0)
            (actualBasis F B i)) j ≠ 0 := by
        simpa [tp, tensor_sub_left] using hnz
      exact le_of_eq (original_remainder_fixed_charge_degree F B H hHG hGH
        p 0 i j hi hz).symm
    · apply sugawara_minus_leading_fixed_charge_raises F B H hHG hGH p n hn i j hi
      simpa only [if_neg hn] using hnz
  have hg : (actualBasis F B).repr
      (tp (1 : Module.End ℂ (Carrier D))
        D5.S3.Quantum.Fermionic.BcGhostBRST.Qg (actualBasis F B i)) j = 0 := by
    by_contra hgz
    exact hw (le_of_eq (original_ghost_cubic_shift F B i j hgz).symm)
  apply hc
  change (actualBasis F B).coord j
    (finiteRemainder F H p modes (actualBasis F B i)) = 0
  simp only [finiteRemainder, LinearMap.add_apply, LinearMap.sum_apply,
    map_add, map_sum, Module.Basis.coord_apply, hg, add_zero]
  exact Finset.sum_eq_zero (fun n _ => hm n)

/-- The accepted genuine quartet homotopy preserves degree. Thus its product
with this actual finite remainder raises degree on the same fixed-charge inputs;
no all-powers support or nilpotence certificate is a premise. -/
theorem h_finiteRemainder_fixed_charge_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (modes : Finset ℤ) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      ((h F B p * finiteRemainder F H p modes) (actualBasis F B i)) j ≠ 0) :
    degree i + 1 ≤ degree j := by
  classical
  by_contra hw
  apply hc
  change (actualBasis F B).coord j
    (h F B p (finiteRemainder F H p modes (actualBasis F B i))) = 0
  rw [← basis_expand (actualBasis F B)
    (finiteRemainder F H p modes (actualBasis F B i))]
  simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hr : (actualBasis F B).repr
      (finiteRemainder F H p modes (actualBasis F B i)) l = 0
  · simp [hr]
  · by_cases hh : (actualBasis F B).repr (h F B p (actualBasis F B l)) j = 0
    · simp [hh]
    · have hd := h_shift F B p l j hh
      have hu := finiteRemainder_fixed_charge_raises F B H hHG hGH p modes i l hi hr
      exact False.elim (hw (by omega))

/- STILL OPEN: actual full matter
and ghost cubic finite captures and their assembly into Q-d0; zero-mode b0/c0
cancellation with the actual matter-plus-ghost constant; preservation of the
literal physical shell by d0,h,delta; full h(Q-d0) strict raising; shell bounds,
rank-26 Q^2, HPL, cohomology/no-ghost/string/AdS conclusions. Raw same-sign lowering summands require inverse-Gram cancellation; their
counterexample is explained in the owning filtration Scribe, not retained as a
separate theorem branch.
-/

end D5.S3.VertexAlgebra.LatticeSugawaraNullFrameEndpoints
