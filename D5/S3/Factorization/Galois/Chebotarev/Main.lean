/- GID: D5/S3/Factorization/Galois/Chebotarev/Main
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/Main
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chebotarev density is conjugacy-class size divided by Galois-group order. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.Abelian
public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldDensity

/-!
# Chebotarev's density theorem

For a finite Galois extension `L/K` of number fields and a conjugacy class `C`
of `Gal(L/K)`, the unramified prime ideals whose Frobenius class is `C` have
Dirichlet density `|C| / |Gal(L/K)|`.

The proof uses the abelian theorem over the fixed field of a cyclic subgroup
and transfers its density to the original base field.

Source: Sharifi, *Algebraic Number Theory*, Theorem 7.2.2; Stevenhagen-Lenstra,
*Chebotarev and his density theorem*, Appendix.
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

open scoped ENNReal

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Chebotarev's density theorem for a conjugacy class of a finite Galois extension. -/
theorem chebotarev_density
    [FiniteDimensional K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  let e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  have : IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul e x y, ← map_mul e y x, mul_comm' x y]
  exact density_lift_through_fixedField σ
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    (e ⟨σ, Subgroup.mem_zpowers σ⟩) rfl rfl
    (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))

end Chebotarev
