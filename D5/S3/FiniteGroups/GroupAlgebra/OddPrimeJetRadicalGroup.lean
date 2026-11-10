/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Principal units embedded in the actual original-label kernel. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalUnits
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalGroup
open Polynomial Module OddPrimeJetDeformation OddPrimeJetRadical OddPrimeJetGroup
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
variable (q : K →ₗ[F] K)

private theorem kernel_commutes (x : (project (p := p) (K := K) q).ker) :
    OddPrimeJetCommutant.commutesOriginal q x.val.val.1.toLinearMap := by
  have hlabel : x.val.val.2 = 1 := congrArg Subtype.val x.property
  intro g v
  have h := x.val.property g v
  rw [hlabel] at h
  exact h

private def unitToKernel : (commutantAlgebra (p := p) (K := K) q)ˣ →* (project (p := p) (K := K) q).ker where
  toFun x := ⟨⟨(LinearMap.GeneralLinearGroup.toLinearEquiv
      (Units.map (commutantAlgebra (p := p) (K := K) q).val.toMonoidHom x), 1), x.val.property⟩, rfl⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · ext v; rfl
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · ext v; rfl
    · rfl

private def kernelToUnit (x : (project (p := p) (K := K) q).ker) : (commutantAlgebra (p := p) (K := K) q)ˣ where
  val := ⟨x.val.val.1.toLinearMap, kernel_commutes (p := p) (K := K) q x⟩
  inv := ⟨(x⁻¹).val.val.1.toLinearMap, kernel_commutes (p := p) (K := K) q x⁻¹⟩
  val_inv := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact x.val.val.1.apply_symm_apply v
  inv_val := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact x.val.val.1.symm_apply_apply v

/-- A native group equivalence with the actual label-projection kernel. -/
def commutantUnitsEquiv : (commutantAlgebra (p := p) (K := K) q)ˣ ≃* (project (p := p) (K := K) q).ker :=
  MulEquiv.ofBijective (unitToKernel (p := p) (K := K) q) ⟨by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : (project (p := p) (K := K) q).ker => z.val.val.1.toLinearMap) h,
    by
      intro x
      refine ⟨kernelToUnit (p := p) (K := K) q x, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · ext v; rfl
      · exact (congrArg Subtype.val x.property).symm⟩

variable (hq : q 1 = 0)
/-- Principal units as an actual subgroup of the original-pair kernel. -/
def actualPrincipalUnits : Subgroup (project (p := p) (K := K) q).ker :=
  (principalUnits (p := p) (K := K) q hq).map (commutantUnitsEquiv (p := p) (K := K) q).toMonoidHom

private def principalEquiv : principalUnits (p := p) (K := K) q hq ≃* actualPrincipalUnits (p := p) (K := K) q hq :=
  (commutantUnitsEquiv (p := p) (K := K) q).subgroupMap (principalUnits (p := p) (K := K) q hq)

/-- The embedded principal units commute in the actual original group. -/
private theorem actualPrincipalUnits_commute (x y : actualPrincipalUnits (p := p) (K := K) q hq) : x * y = y * x := by
  let e := principalEquiv (p := p) (K := K) q hq
  obtain ⟨a,rfl⟩ := e.surjective x
  obtain ⟨b,rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, principalUnits_commute (p := p) (K := K)]

/-- The actual subgroup, including its original-label component, has exponent p. -/
private theorem actualPrincipalUnits_pow (x : actualPrincipalUnits (p := p) (K := K) q hq) : x ^ p = 1 := by
  let e := principalEquiv (p := p) (K := K) q hq
  obtain ⟨a,rfl⟩ := e.surjective x
  rw [← map_pow, principalUnits_pow (p := p) (K := K), map_one]

/-- The order of the embedded actual principal-unit subgroup. -/
private theorem actualPrincipalUnits_cardinality [Fintype K] {n : ℕ}
    (hK : Fintype.card K = p ^ n) :
    Nat.card (actualPrincipalUnits (p := p) (K := K) q hq) = p^(n*(p-2)+n*n) := by
  rw [← Nat.card_congr (principalEquiv (p := p) (K := K) q hq).toEquiv]
  exact principalUnits_cardinality (p := p) (K := K) q hq hK

/-- The full elementary-abelian assertion on the actual original-label kernel. -/
theorem actual_principal_unit_structure [Fintype K] {n : ℕ}
    (hK : Fintype.card K = p^n) :
    (∀ x y : actualPrincipalUnits (p := p) q hq, x*y = y*x) ∧
    (∀ x : actualPrincipalUnits (p := p) q hq, x^p = 1) ∧
    Nat.card (actualPrincipalUnits (p := p) q hq) = p^(n*(p-2)+n*n) :=
  ⟨actualPrincipalUnits_commute q hq, actualPrincipalUnits_pow q hq,
    actualPrincipalUnits_cardinality q hq hK⟩

#print axioms actual_principal_unit_structure

#print axioms commutantUnitsEquiv
end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalGroup
