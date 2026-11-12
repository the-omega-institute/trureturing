/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full mixed Jacobi laws for source-linear rational Hahn dual-lattice fields. -/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetPositiveEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGroundRigidity

/-!
The acting algebra is the complete original lattice algebra. Both arguments
and the target are complete actual dual modules, with the original cocycle
and conformal state. No charge, exponent coset, or leading coefficient
condition is included in the laws. Classical lattice fusion conventions:
Bakalov--Kac, math/0402315v1, section 4.1. Imported residue and Sugawara
suppliers retain their Scott Carnahan and Kalle Kytölä attributions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState
open LatticeDualCosetModule LatticeDualCosetConformal
open LatticePositiveEnergy LatticeDualCosetEnergy MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix
noncomputable section

abbrev Fields (D : LatticeData) :=
  Carrier D →ₗ[ℂ] HVertexOperator ℚ ℂ (Carrier D) (Carrier D)

def mode {D : LatticeData} (I : Fields D) (u : Carrier D) (τ : ℚ) :
    Carrier D →ₗ[ℂ] Carrier D := (I u).coeff (-τ - 1)

@[simp] theorem mode_smul_source {D : LatticeData} (I : Fields D) (c : ℂ)
    (u : Carrier D) (τ : ℚ) (v : Carrier D) :
    mode I (c • u) τ v = c • mode I u τ v := by simp [mode]

@[simp] theorem mode_add_source {D : LatticeData} (I : Fields D)
    (u w : Carrier D) (τ : ℚ) (v : Carrier D) :
    mode I (u+w) τ v = mode I u τ v + mode I w τ v := by simp [mode]

def leftTerm (D : LatticeData) (a : Charge D) (I : Fields D)
    (h u v : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) : Carrier D :=
  integerBinomial p i • mode I (((action D a h)[[r + i]]) u)
    ((p : ℚ) + τ - i) v

def firstTerm (D : LatticeData) (a b : Charge D) (I : Fields D)
    (h u v : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    ((action D (a + b) h)[[p + r - i]]) (mode I u (τ + i) v)

def secondTerm (D : LatticeData) (b : Charge D) (I : Fields D)
    (h u v : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      mode I u (τ + r - i) (((action D b h)[[p + i]]) v))

/-- The actual full lattice laws, with three separate finite supports. -/
structure Lawful (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (I : Fields D) : Prop where
  source : ∀ u τ, mode I (moduleL D a H (-1) u) τ =
    -(τ : ℂ) • mode I u (τ - 1)
  target : ∀ u τ, (moduleL D (a+b) H (-1)).comp (mode I u τ) -
    (mode I u τ).comp (moduleL D b H (-1)) = -(τ : ℂ) • mode I u (τ - 1)
  jacobi : ∀ h u v p r τ,
    Function.HasFiniteSupport (leftTerm D a I h u v p r τ) ∧
    Function.HasFiniteSupport (firstTerm D a b I h u v p r τ) ∧
    Function.HasFiniteSupport (secondTerm D b I h u v p r τ) ∧
      (∑ᶠ i : ℕ, leftTerm D a I h u v p r τ i) =
        (∑ᶠ i : ℕ, firstTerm D a b I h u v p r τ i) -
          (∑ᶠ i : ℕ, secondTerm D b I h u v p r τ i)

private theorem lawful_zero (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Lawful D a b H 0 where
  source u τ := by apply LinearMap.ext; intro v; simp [mode]
  target u τ := by apply LinearMap.ext; intro v; simp [mode]
  jacobi h u v p r τ := by
    simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]

private theorem lawful_add (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (I K : Fields D) (hI : Lawful D a b H I) (hK : Lawful D a b H K) :
    Lawful D a b H (I+K) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hI.source u τ)
    have hk := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hK.source u τ)
    simpa [mode, smul_add] using congrArg₂ (·+·) hi hk
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hI.target u τ)
    have hk := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hK.target u τ)
    simp only [mode, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_add, Pi.add_apply, LinearMap.add_apply, smul_add] at hi hk ⊢
    linear_combination (norm := module) hi + hk
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hk := hK.jacobi h u v p r τ
    have hl : leftTerm D a (I+K) h u v p r τ =
        leftTerm D a I h u v p r τ + leftTerm D a K h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_add]
    have hf : firstTerm D a b (I+K) h u v p r τ =
        firstTerm D a b I h u v p r τ + firstTerm D a b K h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_add]
    have hs : secondTerm D b (I+K) h u v p r τ =
        secondTerm D b I h u v p r τ + secondTerm D b K h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_add]
    rw [hl, hf, hs]
    refine ⟨hi.1.add hk.1, hi.2.1.add hk.2.1, hi.2.2.1.add hk.2.2.1, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hi.1 hk.1, finsum_add_distrib hi.2.1 hk.2.1,
      finsum_add_distrib hi.2.2.1 hk.2.2.1, hi.2.2.2, hk.2.2.2]
    abel

private theorem lawful_smul (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (c : ℂ) (I : Fields D) (hI : Lawful D a b H I) : Lawful D a b H (c • I) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hI.source u τ)
    simpa [mode, smul_comm c] using congrArg (c • ·) hi
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hI.target u τ)
    simpa [mode, ← smul_sub, smul_comm c] using congrArg (c • ·) hi
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hl : leftTerm D a (c • I) h u v p r τ = c • leftTerm D a I h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_comm c]
    have hf : firstTerm D a b (c • I) h u v p r τ = c • firstTerm D a b I h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_comm c]
    have hs : secondTerm D b (c • I) h u v p r τ = c • secondTerm D b I h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_comm c]
    rw [hl, hf, hs]
    refine ⟨hi.1.smul_right (fun _ => c), hi.2.1.smul_right (fun _ => c),
      hi.2.2.1.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply]
    rw [← smul_finsum' c hi.1, ← smul_finsum' c hi.2.1,
      ← smul_finsum' c hi.2.2.1, hi.2.2.2, smul_sub]

/-- The natural complex submodule of fields satisfying the actual full laws. -/
def operatorSpace (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Submodule ℂ (Fields D) where
  carrier := {I | Lawful D a b H I}
  zero_mem' := lawful_zero D a b H
  add_mem' := fun hi hk => lawful_add D a b H _ _ hi hk
  smul_mem' := fun c _ hi => lawful_smul D a b H c _ hi

open private pairing_symm pairing_add from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetPositiveEnergy

variable (D : LatticeData) (a b : Charge D)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (I : Fields D) (hI : Lawful D a b H I)

include hI in
theorem ward (h u v : Carrier D) (p : ℤ) (τ : ℚ) :
    ((action D (a+b) h)[[p]]) (mode I u τ v) -
      mode I u τ (((action D b h)[[p]]) v) =
        ∑ᶠ i : ℕ, leftTerm D a I h u v p 0 τ i := by
  have hJ := (hI.jacobi h u v p 0 τ).2.2.2
  have hf : (∑ᶠ i : ℕ, firstTerm D a b I h u v p 0 τ i) =
      ((action D (a+b) h)[[p]]) (mode I u τ v) := by
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
  rw [hf, hs] at hJ
  exact hJ.symm

abbrev ground (n : Charge D) : Carrier D := Finsupp.single n (1 : Oscillator D)

theorem current_ground (d n : Charge D) (i : Fin D.rank) (j : ℕ) :
    ((action D d (currentState D i))[[j]]) (ground D n) =
      if j = 0 then ((bilinear D (unitCharge D i) n + d i : ℤ) : ℂ) • ground D n
      else 0 := by
  rw [currentState, action_current_coefficients]
  by_cases hj : j = 0
  · simp [hj, shiftedCurrentPolynomial, ground, Finsupp.smul_single]
  · simp [shiftedCurrentPolynomial, show ¬ (j : ℤ) < 0 by omega, hj, LinearMap.smul_apply,
      LinearMap.sum_apply, pderiv_one, ground]

include hI in
theorem ground_current_ward (n : Charge D) (v : Carrier D) (i : Fin D.rank)
    (p : ℤ) (τ : ℚ) :
    ((action D (a+b) (currentState D i))[[p]]) (mode I (ground D n) τ v) -
      mode I (ground D n) τ (((action D b (currentState D i))[[p]]) v) =
        ((bilinear D (unitCharge D i) n + a i : ℤ) : ℂ) •
          mode I (ground D n) ((p : ℚ) + τ) v := by
  rw [ward D a b H I hI]
  rw [finsum_eq_single _ 0]
  · simp only [leftTerm, integerBinomial, Ring.choose_zero_right, Int.cast_one,
      one_smul, Nat.cast_zero, add_zero, sub_zero, zero_add]
    rw [show (0 : ℤ) = (0 : ℕ) by rfl, current_ground]
    simp only [ite_true, mode, map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
  · intro j hj
    simp [leftTerm, current_ground, hj, mode]

include hI in
theorem energy_ward (u v : Carrier D) (τ : ℚ) :
    moduleL D (a+b) H 0 (mode I u τ v) - mode I u τ (moduleL D b H 0 v) =
      mode I (moduleL D a H 0 u) τ v - ((τ : ℂ) + 1) • mode I u τ v := by
  have hw := ward D a b H I hI (LatticeActualConformalState.omega D H) u v 1 τ
  have hl : (∑ᶠ i : ℕ, leftTerm D a I
      (LatticeActualConformalState.omega D H) u v 1 0 τ i) =
      mode I (moduleL D a H (-1) u) (τ+1) v + mode I (moduleL D a H 0 u) τ v := by
    have hs : Function.support (leftTerm D a I
        (LatticeActualConformalState.omega D H) u v 1 0 τ) ⊆ ({0,1} : Finset ℕ) := by
      intro i hi
      by_contra hn
      have hgt : 1 < i := by simp at hn; omega
      have hc : Ring.choose (1 : ℤ) i = 0 := by
        simpa using (Ring.choose_natCast (R := ℤ) 1 i).trans
          (by simp [Nat.choose_eq_zero_of_lt hgt])
      exact hi (by simp [leftTerm, integerBinomial, hc])
    rw [finsum_eq_sum_of_support_subset _ hs]
    simp [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), leftTerm, integerBinomial,
      Ring.choose_one_right, moduleL, add_comm τ 1]
  rw [hl] at hw
  have hd := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v) (hI.source u (τ+1))
  simp only [LinearMap.smul_apply, add_sub_cancel_right, Rat.cast_add, Rat.cast_one] at hd
  rw [hd] at hw
  simpa only [moduleL, zero_add, add_comm, sub_eq_add_neg, neg_smul] using hw

theorem current_component (d : Charge D) (i : Fin D.rank) (m : ℤ)
    (v : Carrier D) (k : Charge D) :
    (((action D d (currentState D i))[[m]]) v) k =
      shiftedCurrentPolynomial D d 1 i k m (v k) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single n f =>
    rw [currentState, action_current_coefficients]
    by_cases hn : n = k
    · simp [hn]
    · simp [Finsupp.single_apply, hn, Ne.symm hn]

include hI in
theorem coefficient_charge (hHG : H * gramComplex D = 1)
    (n l k : Charge D) (u v : Oscillator D) (τ : ℚ)
    (hne : mode I (Finsupp.single n u) τ (Finsupp.single l v) k ≠ 0) :
    k = n + l := by
  have row (i : Fin D.rank) :
      (bilinear D (unitCharge D i) k : ℂ) -
        (bilinear D (unitCharge D i) n : ℂ) -
        (bilinear D (unitCharge D i) l : ℂ) = 0 := by
    have hw := ward D a b H I hI (currentState D i)
      (Finsupp.single n u) (Finsupp.single l v) 0 τ
    have hl : (∑ᶠ j : ℕ, leftTerm D a I (currentState D i)
        (Finsupp.single n u) (Finsupp.single l v) 0 0 τ j) =
        mode I (((action D a (currentState D i))[[0]]) (Finsupp.single n u))
          τ (Finsupp.single l v) := by
      rw [finsum_eq_single _ 0]
      · simp [leftTerm, integerBinomial]
      · intro j hj
        simp [leftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
    have hz (d q : Charge D) (w : Oscillator D) :
        ((action D d (currentState D i))[[0]]) (Finsupp.single q w) =
          ((bilinear D (unitCharge D i) q + d i : ℤ) : ℂ) • Finsupp.single q w := by
      rw [currentState, action_current_coefficients]
      simp [shiftedCurrentPolynomial, Finsupp.smul_single]
    rw [hl, hz, hz, mode_smul_source, map_smul] at hw
    have h := congrArg (fun w : Carrier D => w k) hw
    simp only [Finsupp.sub_apply, Finsupp.smul_apply] at h
    rw [current_component] at h
    simp [shiftedCurrentPolynomial, mode] at h
    have hs : ((bilinear D (unitCharge D i) k : ℂ) -
        (bilinear D (unitCharge D i) n : ℂ) -
        (bilinear D (unitCharge D i) l : ℂ)) •
          mode I (Finsupp.single n u) τ (Finsupp.single l v) k = 0 := by
      dsimp [mode, HVertexOperator.coeff] at h ⊢
      linear_combination (norm := module) h
    exact (smul_eq_zero.mp hs).resolve_right hne
  let d : Fin D.rank → ℂ := fun j => (k j : ℂ) - (n j : ℂ) - (l j : ℂ)
  have hk : gramComplex D *ᵥ d = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, gramComplex,
      d, bilinear, unitCharge, Int.cast_sum, Int.cast_mul, mul_sub,
      Finset.sum_sub_distrib] using row i
  have hinv := congrArg (fun x : Fin D.rank → ℂ => H *ᵥ x) hk
  rw [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec, Matrix.mulVec_zero] at hinv
  ext i
  have hi : k i - n i - l i = 0 := by
    have hc : (k i : ℂ) - (n i : ℂ) - (l i : ℂ) = 0 := by
      simpa only [d, Pi.zero_apply] using congrFun hinv i
    exact_mod_cast hc
  change k i = n i + l i
  omega

include hI in
theorem ground_charge (hHG : H * gramComplex D = 1)
    (n l k : Charge D) (τ : ℚ) (hne : mode I (ground D n) τ (ground D l) k ≠ 0) :
    k = n+l := coefficient_charge D a b H I hI hHG n l k 1 1 τ hne

include hI in
theorem ground_charge_projection
    (hHG : H * gramComplex D = 1)
    (n l : Charge D) (τ : ℚ) :
    mode I (ground D n) τ (ground D l) =
      Finsupp.single (n+l) (mode I (ground D n) τ (ground D l) (n+l)) := by
  classical
  apply Finsupp.ext
  intro k
  by_cases hk : k = n+l
  · simp [hk]
  · rw [Finsupp.single_eq_of_ne hk]
    by_contra hn
    exact hk (ground_charge D a b H I hI hHG n l k τ hn)

def groundPower (μ ν : Fin D.rank → ℚ) (n l : Charge D) : ℚ :=
  pairing D (fun i => (n i : ℚ) + μ i) (fun i => (l i : ℚ) + ν i)

theorem ground_energy_difference (μ ν : Fin D.rank → ℚ) (n l : Charge D) :
    chargeWeight D (μ+ν) (n+l) - chargeWeight D μ n - chargeWeight D ν l =
      groundPower D μ ν n l := by
  have hv : (fun i => ((n+l) i : ℚ) + (μ+ν) i) =
      (fun i => (n i : ℚ) + μ i) + (fun i => (l i : ℚ) + ν i) := by
    ext i
    simp only [Pi.add_apply, Int.cast_add]
    ring
  unfold chargeWeight groundPower
  rw [hv, pairing_add D, pairing_symm D (fun i => (l i : ℚ) + ν i) (fun i => (n i : ℚ) + μ i)]
  ring

theorem ground_L0 (d : Charge D)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (d i : ℚ)) (n : Charge D) :
    moduleL D d H 0 (ground D n) = (chargeWeight D μ n : ℂ) • ground D n := by
  simpa [carrierBasis_apply, weight, oscillatorEnergy] using
    moduleL_basis_zero D d H hHG hGH μ hDual (n, 0)

theorem dual_add (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)) :
    ∀ i, ∑ j, (D.G i j : ℚ) * (μ+ν) j = ((a+b) i : ℚ) := by
  intro i
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, Int.cast_add]

include hI in
theorem ground_eigen
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))
    (n l : Charge D) (s : ℚ) :
    moduleL D (a+b) H 0 ((I (ground D n)).coeff s (ground D l)) =
      ((chargeWeight D μ n + chargeWeight D ν l + s : ℚ) : ℂ) •
        (I (ground D n)).coeff s (ground D l) := by
  have h := energy_ward D a b H I hI (ground D n) (ground D l) (-s-1)
  rw [ground_L0 D H a hHG hGH μ ha, ground_L0 D H b hHG hGH ν hb] at h
  simp only [mode, show -(-s-1)-1 = s by ring, map_smul,
    LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] at h
  have hc : ((-s-1 : ℚ) : ℂ) + 1 = -(s : ℂ) := by push_cast; ring
  rw [hc, neg_smul, sub_neg_eq_add] at h
  push_cast
  rw [add_smul, add_smul]
  linear_combination (norm := module) h

include hI in
theorem ground_spectrum
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))
    (n l k : Charge D) (e : Exponent D) (s : ℚ)
    (hne : (((I (ground D n)).coeff s (ground D l)) k).coeff e ≠ 0) :
    k = n+l ∧ s = groundPower D μ ν n l + (oscillatorEnergy e : ℚ) := by
  have hk : k = n+l := ground_charge D a b H I hI hHG n l k (-s-1) (by
    simpa only [mode, show -(-s-1)-1 = s by ring] using
      (show ((I (ground D n)).coeff s (ground D l)) k ≠ 0 from
        fun hz => hne (by rw [hz]; simp)))
  subst k
  refine ⟨rfl, ?_⟩
  have hc := congrArg (fun v : Carrier D => carrierCoeffEquiv D v (n+l,e))
    (ground_eigen D a b H I hI hHG hGH μ ν ha hb n l s)
  rw [moduleL_coeff D (a+b) H hHG hGH (μ+ν) (dual_add D a b μ ν ha hb)] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  change (weight D (μ+ν) (n+l,e) : ℂ) * ((((I (ground D n)).coeff s (ground D l)) (n+l)).coeff e) =
    ((chargeWeight D μ n + chargeWeight D ν l + s : ℚ) : ℂ) * ((((I (ground D n)).coeff s (ground D l)) (n+l)).coeff e) at hc
  have hq : weight D (μ+ν) (n+l,e) = chargeWeight D μ n + chargeWeight D ν l + s := by
    exact_mod_cast mul_right_cancel₀ hne hc
  have hd := ground_energy_difference D μ ν n l
  simp only [weight] at hq
  linarith

include hI in
theorem ground_below
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))
    (n l : Charge D) (s : ℚ) (hs : s < groundPower D μ ν n l) :
    (I (ground D n)).coeff s (ground D l) = 0 := by
  ext k e
  by_contra hn
  have he := (ground_spectrum D a b H I hI hHG hGH μ ν ha hb n l k e s
    (by simpa using hn)).2
  have hp : (0 : ℚ) ≤ oscillatorEnergy e := Nat.cast_nonneg _
  linarith

def groundScalar (μ ν : Fin D.rank → ℚ) (n l : Charge D) : ℂ :=
  constantCoeff (((I (ground D n)).coeff (groundPower D μ ν n l) (ground D l)) (n+l))

include hI in
theorem ground_leading
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)) (n l : Charge D) :
    (I (ground D n)).coeff (groundPower D μ ν n l) (ground D l) =
      groundScalar D I μ ν n l • ground D (n+l) := by
  have hp := ground_charge_projection D a b H I hI hHG n l (-groundPower D μ ν n l-1)
  simp only [mode, show -(-groundPower D μ ν n l-1)-1 = groundPower D μ ν n l by ring] at hp
  rw [hp, ground, Finsupp.smul_single]
  congr 1
  ext e
  by_cases he : e = 0
  · subst e
    simp [groundScalar, constantCoeff, coeff_smul]
  · have hz : ((((I (ground D n)).coeff (groundPower D μ ν n l)
        (ground D l)) (n+l)).coeff e) = 0 := by
      by_contra hn
      have hh := (ground_spectrum D a b H I hI hHG hGH μ ν ha hb n l (n+l) e _ hn).2
      have hzero : oscillatorEnergy e = 0 := by
        have hq : (oscillatorEnergy e : ℚ) = 0 := by linarith
        exact_mod_cast hq
      exact he ((oscillatorEnergy_eq_zero_iff D e).mp hzero)
    simpa only [coeff_smul, coeff_one, if_neg (Ne.symm he), smul_zero] using hz

def chargedPower (d m n : Charge D) : ℤ :=
  bilinear D m n + ∑ i, m i * d i

theorem charged_ground_leading (d m n : Charge D) :
    ((action D d (ground D m))[[-chargedPower D d m n-1]]) (ground D n) =
      epsilon D m n • ground D (m+n) := by
  classical
  rw [action_ground_coefficients]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [hs, shiftedRawSingle, translatedPolynomial, chargedPower, creationCoeff,
    exponential_constant, ground]

theorem charged_ground_above (d m n : Charge D) (j : ℤ)
    (hj : -chargedPower D d m n-1 < j) :
    ((action D d (ground D m))[[j]]) (ground D n) = 0 := by
  classical
  rw [action_ground_coefficients]
  have ht : -j-1-bilinear D m n-∑ i, m i*d i < 0 := by
    dsimp [chargedPower] at hj
    omega
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [hs, shiftedRawSingle, translatedPolynomial, creationCoeff, ht, ground]

theorem chargedPower_add (m n l : Charge D) :
    chargedPower D (a+b) m (n+l) = chargedPower D a m n + chargedPower D b m l := by
  simp only [chargedPower, LatticeActualGeneratorLocality.bilinear_add_right,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem groundPower_source_shift (μ ν : Fin D.rank → ℚ)
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)) (m n l : Charge D) :
    groundPower D μ ν (m+n) l = groundPower D μ ν n l + (chargedPower D b m l : ℚ) := by
  have hp := physical_pairing_integral D b ν hb m
  have he : groundPower D μ ν (m+n) l = groundPower D μ ν n l +
      (bilinear D m l : ℚ) + physicalPairing D m ν := by
    simp only [groundPower, pairing, physicalPairing, bilinear, Pi.add_apply,
      Int.cast_add, Int.cast_sum, Int.cast_mul, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [he, hp]
  simp only [chargedPower, Int.cast_add]
  ring

theorem groundPower_input_shift (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ)) (m n l : Charge D) :
    groundPower D μ ν n (m+l) = groundPower D μ ν n l + (chargedPower D a m n : ℚ) := by
  have h := groundPower_source_shift D a ν μ ha m l n
  simpa only [groundPower, pairing_symm D] using h

end
end D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner
