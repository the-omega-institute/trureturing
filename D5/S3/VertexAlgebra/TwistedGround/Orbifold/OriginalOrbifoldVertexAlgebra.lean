/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state Borcherds and locality for the original two-sector field. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMJacobi
import D5.S3.VertexAlgebra.BinomialKernelDelta
import Batteries.Tactic.OpenPrivate

/-! The ordered sector identities extend to arbitrary states by additivity.
Lower truncation gives a single locality order for each pair of states. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVertexAlgebra

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution HalfFock.LatticeHalfFockParityField
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open OriginalOrbifoldField OriginalOrbifoldTranslation OriginalOrbifoldJacobi
open OriginalFourMChargeCoset (originalI originalJacobi original_jacobi)
open MixedIntertwiner (originalRightCoefficient)
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon deltaEnd_iterate_apply)
open FieldNormalProductLocality (delta)
open private mode_vv mode_vm mode_mv mode_mm smul_v smul_m sum_v sum_m truncation from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private offset_cutoff from D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
open private jacobiLeftTerm jacobiFirstTerm jacobiSecondTerm from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

variable {D : LatticeData} {hu : IsUnit D.G.det}
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

local notation "A" => Carrier D hu
local notation "V₀" => FixedCarrier D
local notation "M₀" => paritySpace D hu (-1)
local notation "vIn" => (LinearMap.inl ℂ V₀ M₀)
local notation "mIn" => (LinearMap.inr ℂ V₀ M₀)
local notation "μ" => modesOfStateField (Y D hu hD)

/-- The ordered MMV law on the original field for all three integer indices. -/
def MMVBorcherds : Prop :=
  ∀ (u v : M₀) (a : V₀) (p q r : ℤ),
    defect μ (mIn u) (mIn v) (vIn a) p q r = 0

/-- The VVV block is the original fixed lattice Borcherds identity. -/
theorem defect_vvv (a b c : V₀) (p q r : ℤ) :
    defect μ (vIn a) (vIn b) (vIn c) p q r = 0 := by
  let ν := modesOfStateField (fixedY D)
  have law : defect ν a b c p q r = 0 :=
    (defect_eq_zero_iff_borcherds ν (lowerTruncated_modesOfStateField (fixedY D))
      a b c p q r).2 (fixed_borcherds D a b c p q r)
  have fixedCoeff (n : ℤ) (x y : V₀) : ν n x y = fixedMode D x n y :=
    LinearMap.congr_fun (fixedField_ncoeff D x n) y
  unfold defect product iterate at law ⊢
  simp only [fixedCoeff] at law
  simp only [mode_vv, smul_v, ← sum_v, ← map_sub, law, map_zero]

private theorem choose_complex (n : ℤ) (i : ℕ) :
    integerBinomial n i = Ring.choose (n : ℂ) i :=
  Ring.map_choose (Int.castRingHom ℂ) n i

/-- The MMM block is the original negative-twisted Jacobi identity with its native signs. -/
theorem defect_mmm (h24 : D.rank = 24) (u v w : M₀) (p q r : ℤ) :
    defect μ (mIn u) (mIn v) (mIn w) p q r = 0 := by
  have law := original_jacobi D hu hD h24 p q r u v w
  unfold originalJacobi at law
  have reverse :
      (∑ᶠ j, jacobiSecondTerm D hu hD p q r u v w j) =
        epsilon r • ∑ᶠ j : ℕ, (((-1 : ℂ)^j) * integerBinomial r j) •
          originalRightCoefficient D hu (q+r-j) v (originalI D hu hD (p+j) u w) := by
    rw [smul_finsum]
    apply finsum_congr
    intro j
    simp only [jacobiSecondTerm, choose_complex, epsilon,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, smul_smul]
    congr 1
    ring
  rw [reverse] at law
  simp only [jacobiLeftTerm, jacobiFirstTerm, zpow_natCast, ← choose_complex] at law
  have mixedCoeff (n : ℤ) (a : V₀) (x : M₀) :
      mixedMode D hu n a x = ((fixedParitySlice D hu (-1) a)[[n]]) x := rfl
  simp only [mixedCoeff] at law
  unfold defect product iterate
  simp only [mode_mm, mode_vm, mode_mv, smul_m, ← sum_m, ← map_sub]
  rw [← law, sub_self, map_zero]

private theorem product_finite (a b c : A) (p q r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      ((-1 : ℂ)^i * integerBinomial r i) • μ (p+r-i) a (μ (q+i) b c)) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ (truncation hD) b c q
  apply (Finset.range N).finite_toSet.subset
  intro i hi
  refine Finset.mem_range.mpr (lt_of_not_ge fun hn => hi ?_)
  dsimp only
  rw [tail i hn, map_zero, smul_zero]

private theorem iterate_finite (a b c : A) (p q r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      integerBinomial p i • μ (p+q-i) (μ (r+i) a b) c) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ (truncation hD) a b r
  apply (Finset.range N).finite_toSet.subset
  intro i hi
  refine Finset.mem_range.mpr (lt_of_not_ge fun hn => hi ?_)
  dsimp only
  rw [tail i hn, map_zero, LinearMap.zero_apply, smul_zero]

private theorem product_add_first (a a' b c : A) (p q r : ℤ) :
    product μ (a+a') b c p q r = product μ a b c p q r + product μ a' b c p q r := by
  simp only [product, map_add, LinearMap.add_apply, smul_add]
  exact finsum_add_distrib (product_finite hD a b c p q r) (product_finite hD a' b c p q r)

private theorem product_add_second (a b b' c : A) (p q r : ℤ) :
    product μ a (b+b') c p q r = product μ a b c p q r + product μ a b' c p q r := by
  simp only [product, map_add, LinearMap.add_apply, smul_add]
  exact finsum_add_distrib (product_finite hD a b c p q r) (product_finite hD a b' c p q r)

private theorem product_add_third (a b c c' : A) (p q r : ℤ) :
    product μ a b (c+c') p q r = product μ a b c p q r + product μ a b c' p q r := by
  simp only [product, map_add, smul_add]
  exact finsum_add_distrib (product_finite hD a b c p q r) (product_finite hD a b c' p q r)

private theorem iterate_add_first (a a' b c : A) (p q r : ℤ) :
    iterate μ (a+a') b c p q r = iterate μ a b c p q r + iterate μ a' b c p q r := by
  simp only [iterate, map_add, LinearMap.add_apply, smul_add]
  exact finsum_add_distrib (iterate_finite hD a b c p q r) (iterate_finite hD a' b c p q r)

private theorem iterate_add_second (a b b' c : A) (p q r : ℤ) :
    iterate μ a (b+b') c p q r = iterate μ a b c p q r + iterate μ a b' c p q r := by
  simp only [iterate, map_add, LinearMap.add_apply, smul_add]
  exact finsum_add_distrib (iterate_finite hD a b c p q r) (iterate_finite hD a b' c p q r)

private theorem iterate_add_third (a b c c' : A) (p q r : ℤ) :
    iterate μ a b (c+c') p q r = iterate μ a b c p q r + iterate μ a b c' p q r := by
  simp only [iterate, map_add, smul_add]
  exact finsum_add_distrib (iterate_finite hD a b c p q r) (iterate_finite hD a b c' p q r)

private theorem defect_add_first (a a' b c : A) (p q r : ℤ) :
    defect μ (a+a') b c p q r = defect μ a b c p q r + defect μ a' b c p q r := by
  simp only [defect, product_add_first hD, product_add_second hD, iterate_add_first hD, smul_add]
  abel

private theorem defect_add_second (a b b' c : A) (p q r : ℤ) :
    defect μ a (b+b') c p q r = defect μ a b c p q r + defect μ a b' c p q r := by
  simp only [defect, product_add_first hD, product_add_second hD, iterate_add_second hD, smul_add]
  abel

private theorem defect_add_third (a b c c' : A) (p q r : ℤ) :
    defect μ a b (c+c') p q r = defect μ a b c p q r + defect μ a b c' p q r := by
  simp only [defect, product_add_third hD, iterate_add_third hD, smul_add]
  abel

/-- All eight sector laws give the integer defect on arbitrary states in the literal carrier. -/
theorem all_state_defect (h24 : D.rank = 24) (mmv : MMVBorcherds (hu := hu) hD)
    (a b c : A) (p q r : ℤ) : defect μ a b c p q r = 0 := by
  have split (x : A) : x = vIn x.1 + mIn x.2 := by
    change x = (x.1, 0) + (0, x.2)
    exact Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  unfold MMVBorcherds at mmv
  conv_lhs => arg 2; rw [split a]
  conv_lhs => arg 3; rw [split b]
  conv_lhs => arg 4; rw [split c]
  simp only [defect_add_first hD, defect_add_second hD, defect_add_third hD,
    defect_vvv hD, defect_vvm hD, defect_vmv hD h24, defect_vmm hD h24,
    defect_mvv hD h24, defect_mvm hD h24, mmv, defect_mmm hD h24, add_zero]

/-- The native identity, including the three genuine finite supports. -/
theorem all_state_borcherds (h24 : D.rank = 24) (mmv : MMVBorcherds (hu := hu) hD)
    (a b c : A) (p q r : ℤ) :
    let left : ℕ → A := fun i => integerBinomial p i • μ (p+q-i) (μ (r+i) a b) c
    let first : ℕ → A := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) • μ (p+r-i) a (μ (q+i) b c)
    let second : ℕ → A := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) • (epsilon r • μ (q+r-i) b (μ (p+i) a c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
          (μ (p+r-i) a (μ (q+i) b c) - epsilon r • μ (q+r-i) b (μ (p+i) a c)) :=
  (defect_eq_zero_iff_borcherds μ (truncation hD) a b c p q r).1
    (all_state_defect hD h24 mmv a b c p q r)

private theorem product_nat (a b c : A) (p q : ℤ) (N : ℕ) :
    product μ a b c p q N = ∑ i ∈ Finset.range (N+1),
      ((-1 : ℂ)^i * (N.choose i : ℂ)) • μ (p+N-i) a (μ (q+i) b c) := by
  unfold product
  have chooseNat (i : ℕ) : integerBinomial N i = (N.choose i : ℂ) := by
    simp [integerBinomial, Ring.choose_natCast]
  simp_rw [chooseNat]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra outside
  have hz : N.choose i = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
  exact hi (by simp [hz])

private theorem reflected_sign (N i : ℕ) (hi : i ≤ N) :
    epsilon (N : ℤ) * ((-1 : ℂ)^(N-i) * (N.choose i : ℂ)) =
      (-1 : ℂ)^i * (N.choose i : ℂ) := by
  have split : (-1 : ℂ)^N = (-1 : ℂ)^i * (-1 : ℂ)^(N-i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have square : ((-1 : ℂ)^(N-i))^2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [epsilon, zpow_natCast, split]
  calc
    _ = (-1 : ℂ)^i * ((-1 : ℂ)^(N-i))^2 * (N.choose i : ℂ) := by ring
    _ = _ := by rw [square, mul_one]

private theorem reverse_product_nat (a b c : A) (p q : ℤ) (N : ℕ) :
    epsilon (N : ℤ) • product μ b a c q p N = ∑ i ∈ Finset.range (N+1),
      ((-1 : ℂ)^i * (N.choose i : ℂ)) • μ (q+i) b (μ (p+N-i) a c) := by
  rw [product_nat hD, Finset.smul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have within : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, reflected_sign N i within,
    Int.natCast_sub within]
  rw [show q + (N : ℤ) - ((N : ℤ) - i) = q+i by omega,
    show p + ((N : ℤ) - i) = p+N-i by omega]

/-- Take a common locality order from truncation of the iterate before choosing the third state. -/
theorem Y_locality (h24 : D.rank = 24) (mmv : MMVBorcherds (hu := hu) hD) (a b : A) :
    ∃ N : ℕ, delta^[N] (FieldNormalProductLocality.commutator (Y D hu hD a) (Y D hu hD b)) =
      0 := by
  obtain ⟨k, tail⟩ := truncation hD a b
  let N := k.toNat
  refine ⟨N, ?_⟩
  funext p q
  apply LinearMap.ext
  intro c
  change ((delta^[N] (FieldNormalProductLocality.commutator (Y D hu hD a) (Y D hu hD b)))
    p q) c = 0
  have hIterate : iterate μ a b c p q N = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    have hi : k ≤ (N : ℤ) + i := by
      have h := Int.self_le_toNat k
      dsimp only [N]
      omega
    rw [tail _ hi, map_zero, LinearMap.zero_apply, smul_zero]
  have law := all_state_defect hD h24 mmv a b c p q (N : ℤ)
  unfold defect at law
  rw [hIterate, sub_zero, product_nat hD, reverse_product_nat hD] at law
  rw [← deltaEnd_iterate_apply, FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply]
  simp only [FieldNormalProductLocality.commutator, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, smul_sub, Finset.sum_sub_distrib]
  exact law

private theorem Y_vacuum : Y D hu hD (vacuumState D hu) = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro b
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, vacuum_ncoeff,
    FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-k - 1) - 1 = k by omega]
  by_cases hk : k = 0
  · simp [hk]
  · have hn : -k - 1 ≠ -1 := by omega
    simp [hk, hn]

/-- The state-field vertex algebra with the original field, vacuum and translation. -/
def actualVertexAlgebra (h24 : D.rank = 24) (mmv : MMVBorcherds (hu := hu) hD) :
    StateFieldVertexAlgebra A where
  stateField := Y D hu hD
  vacuum := vacuumState D hu
  translation := T D hu
  vacuum_field := Y_vacuum hD
  creation a := by simpa only [ite_true] using creation_ncoeff D hu hD a (-1) le_rfl
  creativity a n hn := by
    have h : n ≠ -1 := by omega
    simpa only [ite_eq_right h] using creation_ncoeff D hu hD a n (by omega)
  translation_vacuum := by
    change (fixedTranslation D (fixedVacuum D), MixedIntertwiner.translation D hu 0) = 0
    exact Prod.ext (fixed_actualVertexAlgebra D).translation_vacuum (map_zero _)
  covariance a n := Y_covariance D hu hD h24 n a
  locality := Y_locality hD h24 mmv
  borcherds := all_state_borcherds hD h24 mmv

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVertexAlgebra
