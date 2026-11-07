/- GID: D5/S3/Arith/CharacterSums/GaussSumSubgroupOrbit
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/GaussSumSubgroupOrbit
   mirror-E: none(waiver:algebraic-character-identity)
   anchors: []
   utility: none
   digest: Weighted subgroup Gauss-sum orbits factor and satisfy character orthogonality. -/

module

public import Mathlib.NumberTheory.GaussSum

/-!
# Weighted subgroup orbits of Gauss sums

The output of the weighted orbit operator belongs to the right-translation
eigenspace of the subgroup with eigencharacter the inverse weight. The proof reindexes the
subgroup by left multiplication and does not use Gauss sums. Comparing this
eigencharacter with that of the Gauss function proves that a nonzero weighted
Gauss orbit forces the weights to match the restricted character. This is the
live route used by the vanishing branch of the final orbit formula.

The orbit factors over every commutative coefficient ring. The orthogonality
dichotomy requires an integral domain: distinct characters need not have zero
inner product over a ring with zero divisors. No primitivity assumption on the
additive character, or invertibility assumption on the initial shift, is used.
-/

@[expose] public section

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums

noncomputable section

variable {A K : Type*} [CommRing A] [Fintype A] [CommRing K]

open Classical in
/-- The weighted sum of a function along the orbit of a unit subgroup. -/
def weightedOrbitSum (H : Subgroup Aˣ) (ρ : H →* Kˣ) (F : A → K) (a : A) : K :=
  ∑ h : H, (ρ h : K) * F (a * (h : Aˣ))

open Classical in
/-- Right translation of a weighted orbit has eigencharacter `ρ⁻¹`.
The change of variable `h ↦ g * h` is a bijection of the subgroup. Thus this
operator takes arbitrary functions to the inverse-weight eigenspace for the
right action of `H`, without any domain or division assumptions on `K`. -/
theorem weightedOrbitSum_mulRight
    (H : Subgroup Aˣ) (ρ : H →* Kˣ) (F : A → K) (a : A) (g : H) :
    weightedOrbitSum H ρ F (a * (g : Aˣ)) =
      ((ρ g)⁻¹ : Kˣ) * weightedOrbitSum H ρ F a := by
  classical
  have hweight (h : H) :
      (((ρ g)⁻¹ : Kˣ) : K) * (ρ (g * h) : K) = (ρ h : K) := by
    rw [map_mul, ← Units.val_mul, inv_mul_cancel_left]
  calc
    _ = ∑ h : H, (((ρ g)⁻¹ : Kˣ) : K) *
        ((ρ (g * h) : K) * F (a * ((g * h : H) : Aˣ))) := by
      unfold weightedOrbitSum
      apply Finset.sum_congr rfl
      intro h _
      rw [← mul_assoc, hweight]
      simp only [Subgroup.coe_mul, Units.val_mul, mul_assoc]
    _ = _ := by
      rw [weightedOrbitSum, Finset.mul_sum]
      exact Fintype.sum_bijective (fun h : H => g * h)
        (Group.mulLeft_bijective g) _ _ (fun _ => rfl)

open Classical in
/-- Factor a weighted unit-subgroup orbit into a character coefficient and the
Gauss sum at the initial shift. This identity allows zero divisors in `K`. -/
theorem weighted_gaussSum_subgroup_factor
    (χ : MulChar A K) (ψ : AddChar A K) (H : Subgroup Aˣ)
    (ρ : H →* Kˣ) (a : A) :
    (∑ h : H, (ρ h : K) * gaussSum χ (ψ.mulShift (a * (h : Aˣ)))) =
      (∑ h : H, (ρ h : K) * χ⁻¹ (h : Aˣ)) * gaussSum χ (ψ.mulShift a) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [← AddChar.mulShift_mulShift, gaussSum_mulShift_eq, mul_assoc]

open Classical in
/-- Orthogonality of two unit-valued characters of any finite group, expressed
without field division. The ratio character is trivial exactly when they agree. -/
theorem weighted_unitHom_orthogonality
    {G : Type*} [Group G] [Fintype G] [IsDomain K]
    (ρ σ : G →* Kˣ) :
    (∑ g : G, (ρ g : K) * ((σ g)⁻¹ : Kˣ)) =
      if ρ = σ then (Fintype.card G : K) else 0 := by
  classical
  let δ : G →* K := (Units.coeHom K).comp (ρ * σ⁻¹)
  have hδ : δ = 1 ↔ ρ = σ := by
    constructor
    · intro h
      have hunit : ρ * σ⁻¹ = 1 := by
        ext g
        exact DFunLike.congr_fun h g
      exact mul_inv_eq_one.mp hunit
    · intro h
      subst ρ
      ext g
      simp [δ]
  simpa only [δ, MonoidHom.comp_apply, MonoidHom.mul_apply,
    MonoidHom.inv_apply, Units.coeHom_apply, Units.val_mul, hδ,
    apply_ite, Nat.cast_zero] using sum_hom_units δ

open Classical in
/-- A nonzero weighted Gauss orbit forces its weight to be the restricted
multiplicative character. The proof compares the right-translation eigenlaw
of the general orbit operator with the inverse-character eigenlaw of Gauss
sums, and cancels the nonzero orbit value in the coefficient domain. -/
theorem weighted_gaussSum_subgroup_nonzero_weights [IsDomain K]
    (χ : MulChar A K) (ψ : AddChar A K) (H : Subgroup Aˣ)
    (ρ : H →* Kˣ) (a : A)
    (hne : weightedOrbitSum H ρ (fun b => gaussSum χ (ψ.mulShift b)) a ≠ 0) :
    ρ = χ.toUnitHom.comp H.subtype := by
  classical
  apply MonoidHom.ext
  intro g
  apply inv_injective
  apply Units.ext
  apply mul_right_cancel₀ hne
  have heigen := weightedOrbitSum_mulRight H ρ
    (fun b => gaussSum χ (ψ.mulShift b)) a g
  have hgauss :
      weightedOrbitSum H ρ (fun b => gaussSum χ (ψ.mulShift b)) (a * (g : Aˣ)) =
        χ⁻¹ (g : Aˣ) *
          weightedOrbitSum H ρ (fun b => gaussSum χ (ψ.mulShift b)) a := by
    unfold weightedOrbitSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    dsimp only
    have harg : (a * (g : Aˣ)) * (h : Aˣ) = (a * (h : Aˣ)) * (g : Aˣ) := by
      ac_rfl
    rw [harg, ← AddChar.mulShift_mulShift, gaussSum_mulShift_eq]
    ac_rfl
  have hinv : χ⁻¹ (g : Aˣ) = (((χ.toUnitHom.comp H.subtype) g)⁻¹ : Kˣ) := by
    rw [MulChar.inv_apply, Ring.inverse_unit]
    change χ ((g : Aˣ)⁻¹ : Aˣ) = ↑((χ.toUnitHom (g : Aˣ))⁻¹)
    rw [← map_inv]
    rfl
  rw [hinv] at hgauss
  exact heigen.symm.trans hgauss

open Classical in
/-- The weighted orbit projects onto the restriction of the multiplicative
character. Its value is the subgroup cardinality times the initial Gauss sum
when the weights match that restriction, and is zero otherwise. -/
theorem weighted_gaussSum_subgroup_orbit [IsDomain K]
    (χ : MulChar A K) (ψ : AddChar A K) (H : Subgroup Aˣ)
    (ρ : H →* Kˣ) (a : A) :
    (∑ h : H, (ρ h : K) * gaussSum χ (ψ.mulShift (a * (h : Aˣ)))) =
      if ρ = χ.toUnitHom.comp H.subtype then
        (Fintype.card H : K) * gaussSum χ (ψ.mulShift a) else 0 := by
  classical
  split_ifs with hmatch
  · rw [weighted_gaussSum_subgroup_factor]
    have hinv (h : H) :
        χ⁻¹ (h : Aˣ) = (((χ.toUnitHom.comp H.subtype) h)⁻¹ : Kˣ) := by
      rw [MulChar.inv_apply, Ring.inverse_unit]
      change χ ((h : Aˣ)⁻¹ : Aˣ) = ↑((χ.toUnitHom (h : Aˣ))⁻¹)
      rw [← map_inv]
      rfl
    simp_rw [hinv]
    rw [weighted_unitHom_orthogonality]
    simp [hmatch]
  · by_contra hne
    exact hmatch (weighted_gaussSum_subgroup_nonzero_weights χ ψ H ρ a hne)

end

end D5.S3.Arith.CharacterSums
