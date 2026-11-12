/-
Source-only candidate: UNCOMPILED / UNACCEPTED.

Mixed Ward identities and charge selection for the literal arbitrary-target
full rational Hahn fields. Only the r=0 and then p=0 specializations of the
original mixed Jacobi law are used. No ground, energy, exponent-coset or
common-support assumption is made. The scalar-target conclusion is proved
first for the exact integral Gram image and then for the actual quotient
and weightIndex. Positive definiteness is needed only for weightIndex.

The original module/current construction retains the Bakalov--Kac,
Scott Carnahan and Kalle Kytölä attributions of its imported suppliers.
Pending supplier source is not native acceptance of this candidate.
-/
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleSectorCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner

open LatticeGeneratingFieldLocality LatticeActualConformalState
open LatticeDualCosetModule LatticeDiscriminantTheta
open Modules.FullJacobiCurrentTransport (FullJacobiLatticeModule)
open Modules.ActualGroundChargedSelection (shiftWeight)
open Modules.ActualWeakModuleSectorCoordinates (weightIndex weightIndex_spec weightIndex_shift)
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix

noncomputable section
universe u

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {a b : Charge D} {H : Matrix (Fin D.rank) (Fin D.rank) ℂ}
variable {J : FullJacobiLatticeModule D M} {I : Fields D M}

/-- The source family in Ward has precisely the finiteness supplied by the
original mixed law, independently of the two right families. -/
theorem ward_terms_finite (hI : Lawful D a b H J I)
    (h u v : Carrier D) (p : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (fun i : ℕ => integerBinomial p i •
      mode I (((action D a h)[[(i : ℤ)]]) u) ((p : ℚ) + τ - i) v) := by
  have he : (fun i : ℕ => integerBinomial p i •
      mode I (((action D a h)[[(i : ℤ)]]) u) ((p : ℚ) + τ - i) v) =
      leftTerm D a I h u v p 0 τ := by
    funext i
    simp only [leftTerm, zero_add]
  rw [he]
  exact (hI.jacobi h u v p 0 τ).1

/-- Full mixed Ward identity for every original state and rational mode.
Each right family is individually supported at zero; no cancellation is
used to obtain finiteness or to evaluate its finsum. -/
theorem ward (hI : Lawful D a b H J I)
    (h u v : Carrier D) (p : ℤ) (τ : ℚ) :
    ((J.stateField h)[[p]]) (mode I u τ v) -
      mode I u τ (((action D b h)[[p]]) v) =
        ∑ᶠ i : ℕ, integerBinomial p i •
          mode I (((action D a h)[[(i : ℤ)]]) u) ((p : ℚ) + τ - i) v := by
  have hj := hI.jacobi h u v p 0 τ
  have hf : (∑ᶠ i : ℕ, firstTerm D J I h u v p 0 τ i) =
      ((J.stateField h)[[p]]) (mode I u τ v) := by
    rw [finsum_eq_single _ 0]
    · simp [firstTerm, integerBinomial]
    · intro i hi
      simp [firstTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  have hs : (∑ᶠ i : ℕ, secondTerm D b I h u v p 0 τ i) =
      mode I u τ (((action D b h)[[p]]) v) := by
    rw [finsum_eq_single _ 0]
    · simp [secondTerm, integerBinomial, StateFieldResidueReconstruction.epsilon]
    · intro i hi
      simp [secondTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  have he := hj.2.2.2
  rw [hf, hs] at he
  simpa only [leftTerm, zero_add] using he.symm

/-- Zero-mode Leibniz on all states, including both source and input terms. -/
theorem zero_mode_ward (hI : Lawful D a b H J I)
    (h u v : Carrier D) (τ : ℚ) :
    ((J.stateField h)[[0]]) (mode I u τ v) =
      mode I (((action D a h)[[0]]) u) τ v +
        mode I u τ (((action D b h)[[0]]) v) := by
  have hw := ward hI h u v 0 τ
  have hl : (∑ᶠ i : ℕ, integerBinomial (0 : ℤ) i •
      mode I (((action D a h)[[(i : ℤ)]]) u) ((0 : ℚ) + τ - i) v) =
        mode I (((action D a h)[[0]]) u) τ v := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial]
    · intro i hi
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  simp only [Int.cast_zero] at hw
  rw [hl] at hw
  exact sub_eq_iff_eq_add.mp hw

/-- Literal shifted-current zero mode on an arbitrary oscillator polynomial. -/
theorem current_zero_single (d n : Charge D) (P : Oscillator D) (i : Fin D.rank) :
    ((action D d (currentState D i))[[0]]) (Finsupp.single n P) =
      ((d i + (D.G *ᵥ n) i : ℤ) : ℂ) • Finsupp.single n P := by
  have hrow : bilinear D (unitCharge D i) n = (D.G *ᵥ n) i := by
    simp [bilinear, unitCharge, Matrix.mulVec, dotProduct]
  rw [currentState, action_current_coefficients]
  simp [shiftedCurrentPolynomial, Finsupp.smul_single, hrow, add_comm]

/-- The actual target current has weight a+b+G(n+l), for every polynomial
pair and every rational mode, without any positive-current condition. -/
theorem current_zero_weight (hI : Lawful D a b H J I)
    (n l : Charge D) (P R : Oscillator D) (i : Fin D.rank) (τ : ℚ) :
    ((J.stateField (currentState D i))[[0]])
        (mode I (Finsupp.single n P) τ (Finsupp.single l R)) =
      ((a i + b i + (D.G *ᵥ (n + l)) i : ℤ) : ℂ) •
        mode I (Finsupp.single n P) τ (Finsupp.single l R) := by
  have hw := zero_mode_ward hI (currentState D i)
    (Finsupp.single n P) (Finsupp.single l R) τ
  rw [current_zero_single, current_zero_single] at hw
  have hc :
      (((a i + (D.G *ᵥ n) i : ℤ) : ℂ) + ((b i + (D.G *ᵥ l) i : ℤ) : ℂ)) =
        ((a i + b i + (D.G *ᵥ (n + l)) i : ℤ) : ℂ) := by
    simp only [Matrix.mulVec_add, Pi.add_apply, Int.cast_add]
    ring
  calc
    _ = ((a i + (D.G *ᵥ n) i : ℤ) : ℂ) •
          mode I (Finsupp.single n P) τ (Finsupp.single l R) +
        ((b i + (D.G *ᵥ l) i : ℤ) : ℂ) •
          mode I (Finsupp.single n P) τ (Finsupp.single l R) := by
      simpa only [mode, map_smul, Pi.smul_apply, LinearMap.smul_apply,
        RingHom.id_apply] using hw
    _ = _ := by rw [← add_smul, hc]

/-- The all-current residual is an equation in the original arbitrary target. -/
theorem current_zero_residual (hI : Lawful D a b H J I)
    (n l : Charge D) (P R : Oscillator D) (i : Fin D.rank) (τ : ℚ) :
    ((J.stateField (currentState D i))[[0]])
        (mode I (Finsupp.single n P) τ (Finsupp.single l R)) -
      ((a i + b i + (D.G *ᵥ (n + l)) i : ℤ) : ℂ) •
        mode I (Finsupp.single n P) τ (Finsupp.single l R) = 0 :=
  sub_eq_zero.mpr (current_zero_weight hI n l P R i τ)

/-- Apply the actual scalar-module current to every output charge, not just
to a ground coefficient. The coefficient is an arbitrary oscillator. -/
theorem scalar_current_coordinate_residual {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (n l k : Charge D) (P R : Oscillator D) (i : Fin D.rank) (τ : ℚ) :
    ((c i + (D.G *ᵥ k) i - (a i + b i + (D.G *ᵥ (n + l)) i) : ℤ) : ℂ) •
      mode K (Finsupp.single n P) τ (Finsupp.single l R) k = 0 := by
  have hw := congrArg (fun x : Carrier D => x k)
    (current_zero_residual hK n l P R i τ)
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.zero_apply] at hw
  change (((action D c (currentState D i))[[0]])
      (mode K (Finsupp.single n P) τ (Finsupp.single l R))) k -
    ((a i + b i + (D.G *ᵥ (n + l)) i : ℤ) : ℂ) •
      mode K (Finsupp.single n P) τ (Finsupp.single l R) k = 0 at hw
  rw [LatticeDualCosetIntertwiner.current_component] at hw
  have hrow : bilinear D (unitCharge D i) k = (D.G *ᵥ k) i := by
    simp [bilinear, unitCharge, Matrix.mulVec, dotProduct]
  have he : ((c i + (D.G *ᵥ k) i : ℤ) : ℂ) •
        mode K (Finsupp.single n P) τ (Finsupp.single l R) k -
      ((a i + b i + (D.G *ᵥ (n + l)) i : ℤ) : ℂ) •
        mode K (Finsupp.single n P) τ (Finsupp.single l R) k = 0 := by
    simpa [shiftedCurrentPolynomial, hrow, add_comm] using hw
  simpa only [Int.cast_sub, sub_smul] using he

/-- A nonzero output charge polynomial forces equality of all integral
current weights. No inverse matrix or nonzero-rank hypothesis is needed. -/
theorem coefficient_weight_selection {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (n l k : Charge D) (P R : Oscillator D) (τ : ℚ)
    (hne : mode K (Finsupp.single n P) τ (Finsupp.single l R) k ≠ 0) :
    c + D.G *ᵥ k = a + b + D.G *ᵥ (n + l) := by
  ext i
  have hc := scalar_current_coordinate_residual hK n l k P R i τ
  have hz : ((c i + (D.G *ᵥ k) i - (a i + b i + (D.G *ᵥ (n + l)) i) : ℤ) : ℂ) = 0 :=
    (smul_eq_zero.mp hc).resolve_right hne
  have hi : c i + (D.G *ᵥ k) i - (a i + b i + (D.G *ᵥ (n + l)) i) = 0 := by
    exact_mod_cast hz
  change c i + (D.G *ᵥ k) i = a i + b i + (D.G *ᵥ (n + l)) i
  omega

/-- Exact integral Gram-image selection, with the explicit witness k-n-l. -/
theorem coefficient_charge_selection {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (n l k : Charge D) (P R : Oscillator D) (τ : ℚ)
    (hne : mode K (Finsupp.single n P) τ (Finsupp.single l R) k ≠ 0) :
    a + b = c + gramMap D (k - n - l) := by
  have he := coefficient_weight_selection hK n l k P R τ hne
  have hg : gramMap D (k - n - l) = D.G *ᵥ k - D.G *ᵥ (n + l) := by
    simp only [gramMap, Matrix.toLin'_apply, Matrix.mulVec_sub, Matrix.mulVec_add]
    abel
  rw [hg]
  calc
    a + b = c + D.G *ᵥ k - D.G *ᵥ (n + l) := by rw [he]; abel
    _ = c + (D.G *ᵥ k - D.G *ᵥ (n + l)) := by abel

/-- Charge support belongs to the exact integral image, for each individual
field value. This does not assert any uniform support over inputs or modes. -/
theorem mode_charge_support {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (n l : Charge D) (P R : Oscillator D) (τ : ℚ) :
    Function.support (mode K (Finsupp.single n P) τ (Finsupp.single l R)) ⊆
      {k | a + b = c + gramMap D (k - n - l)} := by
  intro k hk
  exact coefficient_charge_selection hK n l k P R τ hk

/-- Arithmetic separation first kills every homogeneous polynomial pair. -/
theorem homogeneous_mode_eq_zero_of_no_gram_shift
    {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (hsep : ¬ ∃ t : Charge D, a + b = c + gramMap D t)
    (n l : Charge D) (P R : Oscillator D) (τ : ℚ) :
    mode K (Finsupp.single n P) τ (Finsupp.single l R) = 0 := by
  classical
  apply Finsupp.ext
  intro k
  change mode K (Finsupp.single n P) τ (Finsupp.single l R) k = 0
  by_contra hk
  exact hsep ⟨k - n - l, coefficient_charge_selection hK n l k P R τ hk⟩

/-- Independent finite linear induction in BOTH arbitrary arguments. -/
theorem mode_eq_zero_of_no_gram_shift {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (hsep : ¬ ∃ t : Charge D, a + b = c + gramMap D t)
    (u v : Carrier D) (τ : ℚ) : mode K u τ v = 0 := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp [mode]
  | add u w hu hw =>
    simpa only [mode, map_add, Pi.add_apply, LinearMap.add_apply, add_zero]
      using congrArg₂ (· + ·) hu hw
  | single n P =>
    induction v using Finsupp.induction_linear with
    | zero => exact map_zero (mode K (Finsupp.single n P) τ)
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
    | single l R => exact homogeneous_mode_eq_zero_of_no_gram_shift hK hsep n l P R τ

/-- All rational coefficients vanish, so the complete Fields carrier is zero. -/
theorem eq_zero_of_no_gram_shift {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (hsep : ¬ ∃ t : Charge D, a + b = c + gramMap D t) : K = 0 := by
  apply fields_ext
  intro u v q
  have he := mode_eq_zero_of_no_gram_shift hK hsep u v (-q - 1)
  have hq : -(-q - 1) - 1 = q := by ring
  simpa [mode, hq] using he

/-- The concrete separation condition follows from the literal cokernel,
without positivity. It is not assumed at the wrong-discriminant endpoint. -/
theorem no_gram_shift_of_class_ne {c : Charge D}
    (hclass : classOf D (a + b) ≠ classOf D c) :
    ¬ ∃ t : Charge D, a + b = c + gramMap D t := by
  rintro ⟨t, ht⟩
  apply hclass
  rw [ht]
  apply (Submodule.Quotient.eq (gramRange D)).mpr
  change c + gramMap D t - c ∈ gramRange D
  rw [show c + gramMap D t - c = gramMap D t by abel]
  exact ⟨t, rfl⟩

/-- Wrong actual discriminant class kills the FULL rational Hahn field. -/
theorem eq_zero_of_wrong_discriminant {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (hclass : classOf D (a + b) ≠ classOf D c) : K = 0 :=
  eq_zero_of_no_gram_shift hK (no_gram_shift_of_class_ne hclass)

/-- Positivity enters only through the supplied integral weightIndex/coset
equivalence. Its literal shift law proves the required arithmetic separation. -/
theorem no_gram_shift_of_weightIndex_ne {c : Charge D}
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hclass : (weightIndex positiveG (a + b)).1 ≠ (weightIndex positiveG c).1) :
    ¬ ∃ t : Charge D, a + b = c + gramMap D t := by
  rintro ⟨t, ht⟩
  have hc : c = representative D (weightIndex positiveG c).1 +
      gramMap D (weightIndex positiveG c).2 := by
    simpa only [shiftWeight, gramMap, Matrix.toLin'_apply] using
      (weightIndex_spec positiveG c).symm
  have hd : a + b = shiftWeight (representative D (weightIndex positiveG c).1)
      ((weightIndex positiveG c).2 + t) := by
    calc
      a + b = c + gramMap D t := ht
      _ = (representative D (weightIndex positiveG c).1 +
          gramMap D (weightIndex positiveG c).2) + gramMap D t :=
        congrArg (fun x : Charge D => x + gramMap D t) hc
      _ = _ := by
        simp only [shiftWeight, gramMap, Matrix.toLin'_apply, Matrix.mulVec_add]
        abel
  apply hclass
  rw [hd, weightIndex_shift]

/-- Wrong weightIndex sector, with the original positiveG hypothesis only. -/
theorem eq_zero_of_wrong_weightIndex {c : Charge D} {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D c) K)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hclass : (weightIndex positiveG (a + b)).1 ≠ (weightIndex positiveG c).1) : K = 0 :=
  eq_zero_of_no_gram_shift hK (no_gram_shift_of_weightIndex_ne positiveG hclass)

/-- The representative target needed by scalar probes: every wrong sector
vanishes on all states and every rational coefficient, including rank zero. -/
theorem eq_zero_of_wrong_representative {d : Discriminant D}
    {K : Fields D (Carrier D)}
    (hK : Lawful D a b H (scalarModule D (representative D d)) K)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hwrong : d ≠ (weightIndex positiveG (a + b)).1) : K = 0 := by
  have hd : weightIndex positiveG (representative D d) = (d, 0) := by
    simpa only [shiftWeight, Matrix.mulVec_zero, add_zero] using
      (weightIndex_shift positiveG d (0 : Charge D))
  apply eq_zero_of_wrong_weightIndex hK positiveG
  rw [hd]
  exact Ne.symm hwrong

end
end D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner
