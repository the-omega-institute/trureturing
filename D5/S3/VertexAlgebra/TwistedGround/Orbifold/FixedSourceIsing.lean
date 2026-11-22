/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The norm-four Ising modes and vacuum null on the actual odd twisted sector. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

/-! The norm-four axis on the actual negative twisted sector, using the Borcherds
law with two fixed sources. Its vacuum descendants are formed in the fixed lattice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeInvolution (FixedCarrier fixedMode fixedVacuum fixedTranslation)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.NormFourFirstGradeSpectrum (normFourFixedSource)
open Lattice.NormFourVirasoroVector (self_products)
open OriginalOrbifoldField (Carrier Y Y_fixed_ncoeff_apply)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private central_binomial from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private mixed_vacuum from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
open scoped VertexOperator BigOperators

variable {D : LatticeData} {hu : IsUnit D.G.det}

local notation "Odd" => (paritySpace D hu (-1))
local notation "ρ" => fun v n => (fixedParitySlice D hu (-1) v)[[n]]

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) := (paritySpace D hu (-1)).addCommGroup

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    Module ℂ (paritySpace D hu (-1)) := (paritySpace D hu (-1)).module

local instance (D : LatticeData) :
    AddCommGroup (FixedCarrier D) := (LatticeInvolution.fixedSpace D).addCommGroup

local instance (D : LatticeData) :
    Module ℂ (FixedCarrier D) := (LatticeInvolution.fixedSpace D).module

private theorem commutator_at_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : ℕ → V) :
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) •
      (f i - epsilon 0 • g i)) = f 0 - g 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial, epsilon]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- The iterate is a fixed lattice mode. Its coefficients act on the actual odd sector. -/
theorem odd_iterate (u v : FixedCarrier D) (x : Odd) (r q : ℤ) :
    ρ (fixedMode D u r v) q x =
      ∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial r i) •
        (ρ u (r-i) (ρ v (q+i) x) - epsilon r • ρ v (q+r-i) (ρ u i x)) := by
  have h := (OriginalOrbifoldField.fixedParitySlice_borcherds D hu u v x 0 q r).2.2.2
  dsimp only at h
  rw [finsum_eq_single _ 0] at h
  · simpa [integerBinomial] using h
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- The commutator of two fixed sources on the actual odd sector. -/
theorem odd_commutator (u v : FixedCarrier D) (x : Odd) (p q : ℤ) :
    ρ u p (ρ v q x) - ρ v q (ρ u p x) =
      ∑ᶠ i : ℕ, integerBinomial p i • ρ (fixedMode D u i v) (p+q-i) x := by
  have h := (OriginalOrbifoldField.fixedParitySlice_borcherds D hu u v x p q 0).2.2.2
  dsimp only at h
  rw [commutator_at_zero (fun i : ℕ => ρ u (p+0-i) (ρ v (q+i) x))
    (fun i : ℕ => ρ v (q+0-i) (ρ u (p+i) x))] at h
  simpa only [add_zero, zero_add, Nat.cast_zero, sub_zero] using h.symm

variable (D hu) (a : Charge D) (s : ℂ)

local notation "e" => normFourFixedSource D a s
local notation "F" => fun m => fixedMode D e (m+1)

/-- The actual norm-four modes on the negative twisted parity space, in Virasoro indexing. -/
abbrev oddAxisMode (m : ℤ) : Module.End ℂ Odd := ρ e (m+1)

local notation "L" => oddAxisMode D hu a s

private theorem axis_self_products (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) :
    fixedMode D e 0 e = fixedTranslation D e ∧
    fixedMode D e 1 e = (2 : ℂ) • e ∧ fixedMode D e 2 e = 0 ∧
    fixedMode D e 3 e = (1 / 4 : ℂ) • fixedVacuum D ∧
    ∀ n : ℤ, 4 ≤ n → fixedMode D e n e = 0 := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := self_products D a ha s hs
  exact ⟨Subtype.ext h0, Subtype.ext h1, Subtype.ext h2, Subtype.ext h3,
    fun n hn => Subtype.ext (ht n hn)⟩

/-- The actual odd twisted norm-four modes satisfy the central-charge-one-half relation. -/
theorem odd_virasoro (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) (m n : ℤ) :
    (L m * L n - L n * L m : Module.End ℂ Odd) =
      ((m : ℂ) - (n : ℂ)) • L (m+n) +
        (if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ Odd) else 0) := by
  apply LinearMap.ext
  intro x
  obtain ⟨h0, h1, h2, h3, ht⟩ := axis_self_products D a s ha hs
  let term (j : ℕ) := integerBinomial (m+1) j • ρ (fixedMode D e j e) (m+1+(n+1)-j) x
  have h := odd_commutator e e x (m+1) (n+1)
  change L m (L n x) - L n (L m x) = ∑ᶠ j : ℕ, term j at h
  have finite : (∑ᶠ j : ℕ, term j) = ∑ j ∈ Finset.range 4, term j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra outside
    exact hj (by simp [term, ht j (by omega), show ∀ q, ρ 0 q = mixedMode D hu q 0 from fun _ => rfl])
  -- The mode is the existing source-linear mixed coefficient.
  have coeff (v : FixedCarrier D) (q : ℤ) :
      (fixedParitySlice D hu (-1) v)[[q]] = mixedMode D hu q v := rfl
  have t0 : term 0 = -((m+n+2 : ℤ) : ℂ) • L (m+n) x := by
    simp only [term, integerBinomial, Ring.choose_zero_right, Int.cast_one,
      one_smul, Nat.cast_zero, sub_zero]
    rw [h0, show m + 1 + (n + 1) = m + n + 2 by omega,
      OriginalOrbifoldTranslation.vm_translation, show m + n + 2 - 1 = m + n + 1 by omega]
  have t1 : term 1 = (2 * ((m+1 : ℤ) : ℂ)) • L (m+n) x := by
    simp only [term, Nat.cast_one, h1, integerBinomial, Ring.choose_one_right, coeff,
      map_smul, LinearMap.smul_apply, smul_smul,
      show m + 1 + (n + 1) - 1 = m + n + 1 by omega, mul_comm]
    rfl
  have t2 : term 2 = 0 := by simp [term, h2, coeff]
  have t3 : term 3 = if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) • x else 0 := by
    norm_num only [term, Nat.cast_ofNat, h3]
    rw [coeff, map_smul, LinearMap.smul_apply, mixed_vacuum,
      show m + 1 + (n + 1) - 3 = m + n - 1 by omega]
    by_cases hmn : m+n = 0
    · rw [ite_eq_left hmn, ite_eq_left (show m+n-1 = -1 by omega), smul_smul,
        mul_comm (integerBinomial (m+1) 3), central_binomial]
    · simp [hmn, show m+n-1 ≠ -1 by omega]
  rw [finite] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h
  simp only [t0, t1, t2, t3] at h
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rw [h]
  split_ifs <;> simp only [Module.End.one_apply, LinearMap.smul_apply, LinearMap.zero_apply] <;>
    push_cast <;> module

/-- The lattice Virasoro relation restricted to the actual fixed subspace. -/
theorem fixed_virasoro (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) (m n : ℤ) :
    (F m * F n - F n * F m : Module.End ℂ (FixedCarrier D)) =
      ((m : ℂ) - (n : ℂ)) • F (m+n) +
        (if m+n = 0 then
          (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (FixedCarrier D)) else 0) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun
    (Lattice.NormFourVirasoroVector.virasoro_commutator D a ha s hs m n) x.val
  by_cases hmn : m+n = 0 <;>
    simp only [hmn, ite_true, ite_false, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_zero] at h ⊢ <;> exact h

/-- The literal embedded axis field satisfies Virasoro on the original carrier. -/
theorem embedded_virasoro (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) (m n : ℤ) (x : Carrier D hu) :
    let M := fun k : ℤ => (Y D hu hD (e, 0))[[k+1]]
    M m (M n x) - M n (M m x) =
      ((m : ℂ) - (n : ℂ)) • M (m+n) x +
        (if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) • x else 0) := by
  dsimp only
  have hf := LinearMap.congr_fun (fixed_virasoro D a s ha hs m n) x.1
  have ho := LinearMap.congr_fun (odd_virasoro D hu a s ha hs m n) x.2
  apply Prod.ext
  · by_cases hmn : m+n = 0 <;>
      simpa only [hmn, ite_true, ite_false, Y_fixed_ncoeff_apply, Prod.fst_add,
        Prod.fst_sub, Prod.smul_fst, Prod.fst_zero, LinearMap.add_apply,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        Module.End.one_apply, LinearMap.zero_apply] using hf
  · by_cases hmn : m+n = 0 <;>
      simpa only [hmn, ite_true, ite_false, Y_fixed_ncoeff_apply, Prod.snd_add,
        Prod.snd_sub, Prod.smul_snd, Prod.snd_zero, LinearMap.add_apply,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        Module.End.one_apply, LinearMap.zero_apply, oddAxisMode] using ho

/-- The level-six vacuum descendant combination formed with fixed lattice modes. -/
def nullState : FixedCarrier D :=
  (64 : ℂ) • F (-2) (F (-2) (F (-2) (fixedVacuum D))) +
    (93 : ℂ) • F (-3) (F (-3) (fixedVacuum D)) -
    (264 : ℂ) • F (-4) (F (-2) (fixedVacuum D)) -
    (108 : ℂ) • F (-6) (fixedVacuum D)

/-- The level-six vacuum relation transported to the actual fixed subspace. -/
theorem fixed_vacuum_null (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) :
    nullState D a s = 0 := by
  apply Subtype.ext
  exact Lattice.NormFourVacuumNull.level_six_vacuum_null D a ha s hs

/-- Every coefficient of the level-six null field vanishes on the odd twisted space. -/
theorem odd_vacuum_null (ha : bilinear D a a = 4) (hs : s ^ 2 = 1) (q : ℤ) :
    (fixedParitySlice D hu (-1) (nullState D a s))[[q]] = 0 := by
  rw [fixed_vacuum_null D a s ha hs]
  change mixedMode D hu q 0 = 0
  exact map_zero _


end D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing
