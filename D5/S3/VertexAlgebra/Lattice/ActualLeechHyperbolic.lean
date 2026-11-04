/- GID: D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original ordered integral hyperbolic extension and actual Leech product. -/

import D5.S3.Arith.Lattices.Golay.RealLeech
import D5.S3.VertexAlgebra.Lattice.OrderedHyperbolicExtension

/-! The single choice below is from the actual accepted
Golay-Leech theorem. It is used for ALL charge, determinant, signature and
inverse statements. This is the Leech/fake-Monster lattice dependency;
V-natural and the physical cohomology assertions are separate obligations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechHyperbolic

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeRealNullFrame OrderedHyperbolicExtension
open D5.S3.Arith.Lattices.Golay

/-- The very D supplied by the actual Leech realization theorem. -/
def leechData : LatticeData :=
  Classical.choose RealLeech.exists_positive_even_unimodular_gram

/-- The e paired with that SAME D in the SAME existential witness. -/
def leechCoordinates : Charge leechData ≃ₗ[ℤ] RealLeech.lattice :=
  Classical.choose (Classical.choose_spec RealLeech.exists_positive_even_unimodular_gram)

theorem leech_spec :
    leechData.rank = 24 ∧ IsUnit leechData.G.det ∧
    (leechData.G.map (Int.castRingHom ℝ)).PosDef ∧
    (∀ a b : Charge leechData, (bilinear leechData a b : ℝ) =
      RealLeech.pairing (leechCoordinates a : RealLeech.Space)
        (leechCoordinates b : RealLeech.Space)) :=
  Classical.choose_spec
    (Classical.choose_spec RealLeech.exists_positive_even_unimodular_gram)

/-- The original ordered extension of the same actual Leech witness. -/
abbrev rank26Data : LatticeData := extend leechData

/-- The complete product charge coordinates, on the original charge carrier. -/
def productCoordinates (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) :
    Charge (extend D) ≃ₗ[ℤ] RealLeech.lattice × (ℤ × ℤ) :=
  (splitEquiv D).trans (e.prodCongr (LinearEquiv.refl ℤ (ℤ × ℤ)))

@[simp] theorem productCoordinates_splice (D : LatticeData)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D) (m n : ℤ) :
    productCoordinates D e (splice D a m n) = (e a, (m, n)) := by
  change (e ((splitEquiv D (R := ℤ) (splice D a m n)).1),
    (splitEquiv D (R := ℤ) (splice D a m n)).2) = _
  rw [split_splice]

def coordinates : Charge rank26Data ≃ₗ[ℤ] RealLeech.lattice × (ℤ × ℤ) :=
  productCoordinates leechData leechCoordinates

abbrev ProductSpace := RealLeech.Space × (ℝ × ℝ)

/-- Actual dot/8 on the Leech factor, and the integral U pairing on the axes. -/
def productPairing : LinearMap.BilinForm ℝ ProductSpace where
  toFun x :=
    { toFun := fun y => RealLeech.pairing x.1 y.1 + x.2.1 * y.2.2 + x.2.2 * y.2.1
      map_add' := by
        intro y z
        change RealLeech.pairing x.1 (y.1 + z.1) +
          x.2.1 * (y.2.2 + z.2.2) + x.2.2 * (y.2.1 + z.2.1) = _
        simp only [map_add]
        ring
      map_smul' := by
        intro c y
        change RealLeech.pairing x.1 (c • y.1) +
          x.2.1 * (c * y.2.2) + x.2.2 * (c * y.2.1) = _
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change RealLeech.pairing (x.1 + y.1) z.1 +
      (x.2.1 + y.2.1) * z.2.2 + (x.2.2 + y.2.2) * z.2.1 =
        (RealLeech.pairing x.1 z.1 + x.2.1 * z.2.2 + x.2.2 * z.2.1) +
        (RealLeech.pairing y.1 z.1 + y.2.1 * z.2.2 + y.2.2 * z.2.1)
    simp only [map_add, LinearMap.add_apply]
    ring
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro z
    change RealLeech.pairing (c • x.1) z.1 +
      (c * x.2.1) * z.2.2 + (c * x.2.2) * z.2.1 =
        c * (RealLeech.pairing x.1 z.1 + x.2.1 * z.2.2 + x.2.2 * z.2.1)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem productPairing_apply (x y : ProductSpace) :
    productPairing x y = RealLeech.pairing x.1 y.1 +
      x.2.1 * y.2.2 + x.2.2 * y.2.1 := rfl

/-- This is the actual Leech image times the two integer axes in the real space. -/
def productLattice : Submodule ℤ ProductSpace :=
  RealLeech.lattice.prod ((1 : Submodule ℤ ℝ).prod (1 : Submodule ℤ ℝ))

/-- Discreteness comes from the actual Leech factor and the integer axes. -/
instance : DiscreteTopology productLattice := by
  let J := Submodule.span ℤ (Set.range (Module.Basis.singleton Unit ℝ))
  have hJ : J = (1 : Submodule ℤ ℝ) := by
    simp [J, Submodule.one_eq_span]
  have : DiscreteTopology (1 : Submodule ℤ ℝ) := by
    rw [← hJ]
    infer_instance
  let f : productLattice → RealLeech.lattice ×
      ((1 : Submodule ℤ ℝ) × (1 : Submodule ℤ ℝ)) := fun x =>
    (⟨x.val.1, x.property.1⟩,
      (⟨x.val.2.1, x.property.2.1⟩, ⟨x.val.2.2, x.property.2.2⟩))
  have hf : Continuous f := by
    exact (continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have h1 := congrArg (fun z => (z.1 : RealLeech.Space)) h
    have h2 := congrArg (fun z => ((z.2.1 : ℝ), (z.2.2 : ℝ))) h
    exact Prod.ext h1 h2
  exact DiscreteTopology.of_continuous_injective hf hinj

/-- The actual indefinite product spans its real ambient space. -/
instance : IsZLattice ℝ productLattice where
  span_top := by
    have haxis : Submodule.span ℝ ((1 : Submodule ℤ ℝ) : Set ℝ) = ⊤ := by
      simp [Submodule.one_eq_span]
    change Submodule.span ℝ ((RealLeech.lattice : Set RealLeech.Space) ×ˢ
      (((1 : Submodule ℤ ℝ) : Set ℝ) ×ˢ ((1 : Submodule ℤ ℝ) : Set ℝ))) = ⊤
    rw [Submodule.span_prod_eq ℝ
      (s := (RealLeech.lattice : Set RealLeech.Space))
      (t := (((1 : Submodule ℤ ℝ) : Set ℝ) ×ˢ ((1 : Submodule ℤ ℝ) : Set ℝ)))
      (zero_mem _) ⟨zero_mem _, zero_mem _⟩]
    rw [Submodule.span_prod_eq ℝ
      (s := ((1 : Submodule ℤ ℝ) : Set ℝ))
      (t := ((1 : Submodule ℤ ℝ) : Set ℝ)) (zero_mem _) (zero_mem _), haxis,
      IsZLattice.span_top]
    simp

/-- Actual ambient inclusion of the charge-product coordinates. -/
def productInclusion : (RealLeech.lattice × (ℤ × ℤ)) →ₗ[ℤ] ProductSpace where
  toFun x := ((x.1 : RealLeech.Space), ((x.2.1 : ℝ), (x.2.2 : ℝ)))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

theorem productInclusion_mem (x : RealLeech.lattice × (ℤ × ℤ)) :
    productInclusion x ∈ productLattice := by
  exact ⟨x.1.property, Submodule.mem_one.mpr ⟨x.2.1, rfl⟩,
    Submodule.mem_one.mpr ⟨x.2.2, rfl⟩⟩

theorem productLattice_eq_range : productLattice = productInclusion.range := by
  ext x
  constructor
  · rintro ⟨hx, hm, hn⟩
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp hm
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
    refine ⟨(⟨x.1, hx⟩, (m, n)), ?_⟩
    change (x.1, ((m : ℝ), (n : ℝ))) = x
    have hm' : (m : ℝ) = x.2.1 := hm
    have hn' : (n : ℝ) = x.2.2 := hn
    simp [hm', hn']
  · rintro ⟨x, rfl⟩
    exact productInclusion_mem x

/-- Geometric selfduality, using the actual Leech theorem and both axis tests.
No positive-definite-lattice constructor is applied to this indefinite form. -/
theorem product_self_dual : productPairing.dualSubmodule productLattice = productLattice := by
  ext x
  constructor
  · intro hx
    have hL : x.1 ∈ RealLeech.lattice := by
      rw [← RealLeech.self_dual]
      apply RealLeech.pairing.mem_dualSubmodule.mpr
      intro y hy
      have h := productPairing.mem_dualSubmodule.mp hx (y, (0, 0))
        (show (y, (0, 0)) ∈ productLattice from ⟨hy, zero_mem _, zero_mem _⟩)
      simpa using h
    have hm : x.2.1 ∈ (1 : Submodule ℤ ℝ) := by
      have haxis : ((0, (0, 1)) : ProductSpace) ∈ productLattice :=
        ⟨zero_mem _, zero_mem _, Submodule.mem_one.mpr ⟨1, by simp⟩⟩
      have h := productPairing.mem_dualSubmodule.mp hx (0, (0, 1)) haxis
      simpa using h
    have hn : x.2.2 ∈ (1 : Submodule ℤ ℝ) := by
      have haxis : ((0, (1, 0)) : ProductSpace) ∈ productLattice :=
        ⟨zero_mem _, Submodule.mem_one.mpr ⟨1, by simp⟩, zero_mem _⟩
      have h := productPairing.mem_dualSubmodule.mp hx (0, (1, 0)) haxis
      simpa using h
    exact ⟨hL, hm, hn⟩
  · rintro ⟨hx, hm, hn⟩
    apply productPairing.mem_dualSubmodule.mpr
    rintro y ⟨hy, hr, hs⟩
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp hm
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
    obtain ⟨s, hs⟩ := Submodule.mem_one.mp hs
    obtain ⟨k, hk⟩ := RealLeech.integral_pairing x.1 y.1 hx hy
    apply Submodule.mem_one.mpr
    refine ⟨k + m * s + n * r, ?_⟩
    change ((k + m * s + n * r : ℤ) : ℝ) = productPairing x y
    have hm' : (m : ℝ) = x.2.1 := hm
    have hn' : (n : ℝ) = x.2.2 := hn
    have hr' : (r : ℝ) = y.2.1 := hr
    have hs' : (s : ℝ) = y.2.2 := hs
    rw [productPairing_apply, hk, ← hm', ← hn', ← hr', ← hs']
    push_cast
    ring

theorem product_even (x : ProductSpace) (hx : x ∈ productLattice) :
    ∃ k : ℤ, productPairing x x = 2 * (k : ℝ) := by
  obtain ⟨hx, hm, hn⟩ := hx
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp hm
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
  obtain ⟨k, hk⟩ := RealLeech.even_norm x.1 hx
  refine ⟨k + m * n, ?_⟩
  have hm' : (m : ℝ) = x.2.1 := hm
  have hn' : (n : ℝ) = x.2.2 := hn
  rw [productPairing_apply, hk, ← hm', ← hn']
  push_cast
  ring

/-- Original charge pairing agrees with the ACTUAL ambient product pairing. -/
theorem actual_pairing_splice (a b : Charge leechData) (m n r s : ℤ) :
    (bilinear rank26Data (splice leechData a m n) (splice leechData b r s) : ℝ) =
      productPairing
        ((leechCoordinates a : RealLeech.Space), ((m : ℝ), (n : ℝ)))
        ((leechCoordinates b : RealLeech.Space), ((r : ℝ), (s : ℝ))) := by
  change (bilinear (extend leechData) _ _ : ℝ) = _
  simp only [bilinear_splice, Int.cast_add, Int.cast_mul, leech_spec.2.2.2,
    productPairing_apply]

/-- Every original charge is realized in the actual geometric product. -/
theorem actual_pairing (q q' : Charge rank26Data) :
    (bilinear rank26Data q q' : ℝ) =
      productPairing (productInclusion (coordinates q)) (productInclusion (coordinates q')) := by
  obtain ⟨⟨a, m, n⟩, rfl⟩ := (splitEquiv leechData (R := ℤ)).symm.surjective q
  obtain ⟨⟨b, r, s⟩, rfl⟩ := (splitEquiv leechData (R := ℤ)).symm.surjective q'
  simpa [coordinates, productInclusion] using actual_pairing_splice a b m n r s

end D5.S3.VertexAlgebra.ActualLeechHyperbolic
