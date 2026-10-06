/- GID: D5/S3/FiniteGroups/NikolovSegal/FactorOrbits
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/FactorOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual factor orbits and their equivariant product decomposition. -/

import D5.S3.FiniteGroups.NikolovSegal.LargeMinimalNormalStructure
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

set_option autoImplicit false
namespace NikolovSegal
universe u
variable {A : Type u} [Group A]

/-- Automorphisms act on the actual minimal normal subgroups by image. -/
instance minimalFactorAction : MulAction (MulAut A) (MinimalNormalFactor A) where
  smul α M := ⟨M.val.map α.toMonoidHom, minimal_normal_map_equiv M.property α⟩
  one_smul M := by
    apply Subtype.ext
    change M.val.map (MonoidHom.id A) = M.val
    exact Subgroup.map_id M.val
  mul_smul α β M := by
    apply Subtype.ext
    change M.val.map (α * β).toMonoidHom = (M.val.map β.toMonoidHom).map α.toMonoidHom
    rw [Subgroup.map_map]
    rfl

/-- The genuine permutation representation of the factor action. -/
def minimalFactorPermutation : MulAut A →* Equiv.Perm (MinimalNormalFactor A) :=
  MulAction.toPermHom (MulAut A) (MinimalNormalFactor A)

private def factorProductAut (α : MulAut A) :
    MulAut (∀ M : MinimalNormalFactor A, M.val) where
  toFun f M := ⟨α (f (α⁻¹ • M)), by
    have h := Subgroup.mem_map_of_mem α.toMonoidHom (f (α⁻¹ • M)).property
    change α (f (α⁻¹ • M)) ∈ (α • (α⁻¹ • M)).val at h
    simpa using h⟩
  invFun f M := ⟨α⁻¹ (f (α • M)), by
    have h := Subgroup.mem_map_of_mem α⁻¹.toMonoidHom (f (α • M)).property
    change α⁻¹ (f (α • M)) ∈ (α⁻¹ • (α • M)).val at h
    simpa using h⟩
  left_inv f := by
    funext M
    apply Subtype.ext
    change α⁻¹ (α ((fun L => (f L : A)) (α⁻¹ • (α • M)))) = (f M : A)
    rw [MulAut.inv_apply_self, inv_smul_smul]
  right_inv f := by
    funext M
    apply Subtype.ext
    change α (α⁻¹ ((fun L => (f L : A)) (α • (α⁻¹ • M)))) = (f M : A)
    rw [MulAut.apply_inv_self, smul_inv_smul]
  map_mul' f g := by funext M; apply Subtype.ext; exact map_mul α _ _

private theorem factor_image_mem (α : MulAut A) (M : MinimalNormalFactor A) (x : M.val) :
    α x ∈ (α • M).val := Subgroup.mem_map_of_mem α.toMonoidHom x.property

private theorem factorProductAut_single [DecidableEq (MinimalNormalFactor A)] (α : MulAut A) (M : MinimalNormalFactor A)
    (x : M.val) :
    factorProductAut α (Pi.mulSingle M x) =
      Pi.mulSingle (M := fun L : MinimalNormalFactor A => L.val) (α • M) ⟨α x, factor_image_mem α M x⟩ := by
  classical
  funext L
  apply Subtype.ext
  by_cases he : L = α • M
  · subst L
    change α ((fun L => ((Pi.mulSingle (M := fun L : MinimalNormalFactor A => L.val) M x L) : A)) (α⁻¹ • (α • M))) = _
    rw [inv_smul_smul]
    dsimp only
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · have hn : α⁻¹ • L ≠ M := by
      intro h
      apply he
      have := congrArg (α • ·) h
      simpa using this
    simp [factorProductAut, Pi.mulSingle_eq_of_ne hn, Pi.mulSingle_eq_of_ne he]

/-- Naturality of the accepted canonical internal-product isomorphism. -/
private theorem socleProductEquiv_natural [Finite A]
    (hs : minimalNormalSocle A = ⊤) (hz : Subgroup.center A = ⊥)
    (α : MulAut A) (f : ∀ M : MinimalNormalFactor A, M.val) :
    socleProductEquiv hs hz (factorProductAut α f) = α (socleProductEquiv hs hz f) := by
  classical
  let := Fintype.ofFinite (MinimalNormalFactor A)
  suffices he : (socleProductEquiv hs hz).toMonoidHom.comp (factorProductAut α).toMonoidHom =
      α.toMonoidHom.comp (socleProductEquiv hs hz).toMonoidHom from congrArg (fun h => h f) he
  apply MonoidHom.pi_ext
  intro M x
  change socleProductEquiv hs hz (factorProductAut α (Pi.mulSingle M x)) =
    α (socleProductEquiv hs hz (Pi.mulSingle M x))
  rw [factorProductAut_single]
  change Subgroup.noncommPiCoprod (minimal_normal_factors_commute (G := A)) (Pi.mulSingle (α • M) _) =
    α (Subgroup.noncommPiCoprod (minimal_normal_factors_commute (G := A)) (Pi.mulSingle M x))
  simp only [Subgroup.noncommPiCoprod_mulSingle]

abbrev prescribedActionGroup {m : ℕ} (k : Fin m → MulAut A) :=
  Subgroup.closure (Set.range k)

abbrev FactorOrbit {m : ℕ} (k : Fin m → MulAut A) :=
  MulAction.orbitRel.Quotient (prescribedActionGroup k) (MinimalNormalFactor A)

abbrev OrbitFactor {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) := o.orbit

/-- An orbit block is the product of the actual subgroup factors in that orbit. -/
abbrev OrbitBlock {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :=
  ∀ M : OrbitFactor k o, M.val.val

private theorem orbit_factor_map {m : ℕ} (k : Fin m → MulAut A)
    (o : FactorOrbit k) (α : prescribedActionGroup k) (M : OrbitFactor k o) :
    (α • M).val.val = M.val.val.map α.val.toMonoidHom := rfl

/-- Restriction of a generated automorphism to an actual orbit block. -/
def orbitBlockAut {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k)
    (α : prescribedActionGroup k) : MulAut (OrbitBlock k o) where
  toFun f M := ⟨α.val (f (α⁻¹ • M)), by
    have h := Subgroup.mem_map_of_mem α.val.toMonoidHom (f (α⁻¹ • M)).property
    rw [← orbit_factor_map k o α (α⁻¹ • M)] at h
    simpa using h⟩
  invFun f M := ⟨α.val⁻¹ (f (α • M)), by
    have h := Subgroup.mem_map_of_mem α.val⁻¹.toMonoidHom (f (α • M)).property
    change α.val⁻¹ (f (α • M)) ∈ (α⁻¹ • (α • M)).val.val at h
    simpa using h⟩
  left_inv f := by
    funext M
    apply Subtype.ext
    change α.val⁻¹ (α.val ((fun L => (f L : A)) (α⁻¹ • (α • M)))) = (f M : A)
    rw [MulAut.inv_apply_self, inv_smul_smul]
  right_inv f := by
    funext M
    apply Subtype.ext
    change α.val (α.val⁻¹ ((fun L => (f L : A)) (α • (α⁻¹ • M)))) = (f M : A)
    rw [MulAut.apply_inv_self, smul_inv_smul]
  map_mul' f g := by funext M; apply Subtype.ext; exact map_mul α.val _ _

/-- Restriction is a homomorphism, so it retains the generated tuple action. -/
def orbitBlockAutHom {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :
    prescribedActionGroup k →* MulAut (OrbitBlock k o) where
  toFun := orbitBlockAut k o
  map_one' := by
    ext f M
    change (fun L => (f L : A)) ((1 : prescribedActionGroup k)⁻¹ • M) = (f M : A)
    rw [inv_one, one_smul]
  map_mul' α β := by
    ext f M
    change α.val (β.val ((fun L => (f L : A)) ((α * β)⁻¹ • M))) =
      α.val (β.val ((fun L => (f L : A)) (β⁻¹ • (α⁻¹ • M))))
    rw [mul_inv_rev, mul_smul]

def prescribedOrbitAut {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :
    Fin m → MulAut (OrbitBlock k o) :=
  fun i => orbitBlockAutHom k o ⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩

private theorem prescribed_lifts_generate {m : ℕ} (k : Fin m → MulAut A) :
    Subgroup.closure (Set.range (fun i =>
      (⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : prescribedActionGroup k))) = ⊤ := by
  apply Subgroup.map_injective (f := (prescribedActionGroup k).subtype) Subtype.coe_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  change prescribedActionGroup k = (⊤ : Subgroup (prescribedActionGroup k)).map
    (prescribedActionGroup k).subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- Permutations of the actual factors in one orbit. -/
def orbitFactorPermutation {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :
    prescribedActionGroup k →* Equiv.Perm (OrbitFactor k o) :=
  MulAction.toPermHom (prescribedActionGroup k) (OrbitFactor k o)

def prescribedOrbitPermutation {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :
    Fin m → Equiv.Perm (OrbitFactor k o) :=
  fun i => orbitFactorPermutation k o ⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩

/-- The restricted tuple generates exactly the permutation image of K. -/
theorem prescribedOrbitPermutation_generated {m : ℕ} (k : Fin m → MulAut A)
    (o : FactorOrbit k) :
    Subgroup.closure (Set.range (prescribedOrbitPermutation k o)) =
      (orbitFactorPermutation k o).range := by
  have h := congrArg (Subgroup.map (orbitFactorPermutation k o)) (prescribed_lifts_generate k)
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map] at h
  exact h

/-- Thus the prescribed permutations themselves generate a transitive action
on each block's factors; mere transitivity under a larger ambient group is unused. -/
theorem prescribedOrbitPermutation_transitive {m : ℕ} (k : Fin m → MulAut A)
    (o : FactorOrbit k) (M L : OrbitFactor k o) :
    ∃ σ : Subgroup.closure (Set.range (prescribedOrbitPermutation k o)), σ.val M = L := by
  obtain ⟨α, hα⟩ := MulAction.IsPretransitive.exists_smul_eq (M := prescribedActionGroup k) M L
  refine ⟨⟨orbitFactorPermutation k o α, ?_⟩, hα⟩
  rw [prescribedOrbitPermutation_generated]
  exact ⟨α, rfl⟩

/-- Dependent Pi regrouping by the actual orbit quotient. -/
noncomputable def factorOrbitProductEquiv {m : ℕ} (k : Fin m → MulAut A) :
    (∀ M : MinimalNormalFactor A, M.val) ≃* (∀ o : FactorOrbit k, OrbitBlock k o) where
  toFun f _ M := f M.val
  invFun g M := g (Quotient.mk'' M) ⟨M, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩
  left_inv f := rfl
  right_inv g := by
    funext o M
    obtain ⟨M, hM⟩ := M
    have he := MulAction.orbitRel.Quotient.mem_orbit.mp hM
    subst o
    rfl
  map_mul' f g := rfl

instance factorOrbitFinite [Finite A] {m : ℕ} (k : Fin m → MulAut A) :
    Finite (FactorOrbit k) := inferInstanceAs (Finite (Quotient _))

instance orbitFactorNonempty {m : ℕ} (k : Fin m → MulAut A) (o : FactorOrbit k) :
    Nonempty (OrbitFactor k o) := (MulAction.orbitRel.Quotient.nonempty_orbit o).to_subtype

/-- The actual internal direct product, regrouped into the prescribed orbits. -/
noncomputable def orbitProductEquiv [Finite A]
    (hs : minimalNormalSocle A = ⊤) (hz : Subgroup.center A = ⊥)
    {m : ℕ} (k : Fin m → MulAut A) :
    A ≃* (∀ o : FactorOrbit k, OrbitBlock k o) :=
  (socleProductEquiv hs hz).symm.trans (factorOrbitProductEquiv k)

/-- Each generated automorphism acts on its actual block separately. -/
theorem orbitProductEquiv_equivariant [Finite A]
    (hs : minimalNormalSocle A = ⊤) (hz : Subgroup.center A = ⊥)
    {m : ℕ} (k : Fin m → MulAut A) (α : prescribedActionGroup k)
    (x : A) (o : FactorOrbit k) :
    orbitProductEquiv hs hz k (α.val x) o =
      orbitBlockAut k o α (orbitProductEquiv hs hz k x o) := by
  have he := socleProductEquiv_natural hs hz α.val ((socleProductEquiv hs hz).symm x)
  rw [MulEquiv.apply_symm_apply] at he
  have hc := congrArg (socleProductEquiv hs hz).symm he
  rw [MulEquiv.symm_apply_apply] at hc
  change factorOrbitProductEquiv k ((socleProductEquiv hs hz).symm (α.val x)) o = _
  rw [← hc]
  rfl

/-- The exact equivariance for the prescribed tuple, with no action assumption. -/
theorem orbitProductEquiv_prescribed [Finite A]
    (hs : minimalNormalSocle A = ⊤) (hz : Subgroup.center A = ⊥)
    {m : ℕ} (k : Fin m → MulAut A) (i : Fin m) (x : A) (o : FactorOrbit k) :
    orbitProductEquiv hs hz k (k i x) o =
      prescribedOrbitAut k o i (orbitProductEquiv hs hz k x o) :=
  orbitProductEquiv_equivariant hs hz k ⟨k i, Subgroup.subset_closure ⟨i, rfl⟩⟩ x o

end NikolovSegal
