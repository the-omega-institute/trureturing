/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream residue-field support for finite-field extensions. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/LocalField/ResidueField.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.UnitFiltration

/-!
# Residue fields of nonarchimedean local fields

This file gives names to Mathlib's residue field and reduction maps for the canonical valuation
ring of a local field.  It records the exact kernels needed for congruence and unit-filtration
arguments, specializes Mathlib's adic Teichmüller map, and exposes the standard trace and norm
maps for finite residue-field extensions.

The Teichmüller lift is multiplicative, reduces to its input, and is fixed by the cardinality
power of the residue field.  No arbitrary representatives are used in its definition.
-/

namespace LanglandsFirstMainLemma

section Basic

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue field of the canonical valuation ring of `F`. -/
noncomputable abbrev ResidueField :=
  IsLocalRing.ResidueField (ringOfIntegers F)

/-- The canonical reduction map `𝒪_F → k_F`. -/
noncomputable abbrev residueMap : ringOfIntegers F →+* ResidueField F :=
  IsLocalRing.residue (ringOfIntegers F)

/-- Every residue class has an integral representative. -/
theorem residueMap_surjective : Function.Surjective (residueMap F) :=
  IsLocalRing.residue_surjective

/-- An integral element reduces to zero exactly when it belongs to the first valuation lattice. -/
@[simp]
theorem residueMap_eq_zero_iff (x : ringOfIntegers F) :
    residueMap F x = 0 ↔ (x : F) ∈ lattice F 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, ← mem_lattice_one_iff_mem_maximalIdeal F]

/-- Equality after reduction is congruence modulo the first valuation lattice. -/
@[simp]
theorem residueMap_eq_residueMap_iff (x y : ringOfIntegers F) :
    residueMap F x = residueMap F y ↔ ((x : F) - (y : F)) ∈ lattice F 1 := by
  rw [← sub_eq_zero, ← map_sub, residueMap_eq_zero_iff]
  rfl

/-- Reduction of an element of `F` supplied with a proof that it is integral. -/
noncomputable def reduce (x : F) (hx : x ∈ lattice F 0) : ResidueField F :=
  residueMap F ⟨x, (mem_lattice_zero_iff F).1 hx⟩

@[simp]
theorem reduce_mk (x : ringOfIntegers F) :
    reduce F x ((mem_lattice_zero_iff F).2 x.property) = residueMap F x := rfl

/-- Two integral field elements have the same reduction exactly when they are congruent at
depth one.  In particular, the statement is independent of the supplied integrality proofs. -/
theorem reduce_eq_reduce_iff {x y : F}
    (hx : x ∈ lattice F 0) (hy : y ∈ lattice F 0) :
    reduce F x hx = reduce F y hy ↔ CongruentAtDepth 1 x y := by
  rw [reduce, reduce, residueMap_eq_residueMap_iff]
  exact (congruentAtDepth_iff_sub_mem_lattice F 1 x y).symm

/-- A chosen finite enumeration of the residue field, obtained from Mathlib's `Finite`
instance for local-field residue fields. -/
@[reducible] noncomputable def residueFieldFintype : Fintype (ResidueField F) :=
  Fintype.ofFinite (ResidueField F)

/-- The manuscript's `q_F = |k_F|`. -/
noncomputable def residueCard : ℕ :=
  @Fintype.card (ResidueField F) (residueFieldFintype F)

theorem one_lt_residueCard : 1 < residueCard F := by
  letI := residueFieldFintype F
  exact Fintype.one_lt_card

/-- Reduction on local units. -/
noncomputable abbrev residueUnits : unitGroup F →* (ResidueField F)ˣ :=
  (ValuativeRel.valuation F).valuationSubring.unitGroupToResidueFieldUnits

/-- Every nonzero residue class has a local-unit representative. -/
theorem residueUnits_surjective : Function.Surjective (residueUnits F) :=
  (ValuativeRel.valuation F).valuationSubring.surjective_unitGroupToResidueFieldUnits

@[simp]
theorem residueUnits_coe (u : unitGroup F) :
    ((residueUnits F u : (ResidueField F)ˣ) : ResidueField F) =
      residueMap F (unitGroupMulEquivRingOfIntegers F u) := rfl

/-- The kernel of unit reduction is exactly the first positive unit layer, viewed inside `U⁰`. -/
theorem residueUnits_ker :
    (residueUnits F).ker =
      unitFiltrationInside F (show 0 ≤ 1 by omega) := by
  let A := (ValuativeRel.valuation F).valuationSubring
  have hden : unitFiltrationInside F (show 0 ≤ 1 by omega) =
      A.principalUnitGroup.comap A.unitGroup.subtype := by
    ext u
    rw [mem_unitFiltrationInside]
    change (u : Fˣ) ∈ unitFiltration F 1 ↔ (u : Fˣ) ∈ A.principalUnitGroup
    rw [unitFiltration_one_eq_principalUnitGroup F]
  exact A.ker_unitGroupToResidueFieldUnits.trans hden.symm

end Basic

section Teichmuller

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's adic Teichmüller map, specialized to the complete valuation ring of `F`.

The auxiliary monoid lift identifies the finite (hence perfect) residue field with its
perfection.  The local-field uniformity supplies adic completeness of the valuation ring. -/
noncomputable def teichmuller : ResidueField F →*₀ ringOfIntegers F := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Field (ResidueField F) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (ringOfIntegers F))
  let p := ringChar (ResidueField F)
  letI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField F) p⟩
  let e : ResidueField F →* Perfection (ResidueField F) p :=
    Perfection.liftMonoidHom p (ResidueField F) (ResidueField F)
      (MonoidHom.id (ResidueField F))
  let t := Perfection.teichmuller₀ p
    (IsLocalRing.maximalIdeal (ringOfIntegers F))
  rcases t with ⟨⟨t, htzero⟩, htone, htmul⟩
  have hezero : e 0 = 0 := by
    apply Perfection.ext
    intro n
    simp [e, Perfection.liftMonoidHom]
  exact
    { toFun := fun x ↦ t (e x)
      map_one' := (congrArg t e.map_one').trans htone
      map_mul' := fun x y ↦ (congrArg t (e.map_mul' x y)).trans (htmul (e x) (e y))
      map_zero' := (congrArg t hezero).trans htzero }

set_option backward.isDefEq.respectTransparency false in
/-- The Teichmüller lift is a section of reduction. -/
@[simp]
theorem residueMap_teichmuller (x : ResidueField F) :
    residueMap F (teichmuller F x) = x := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : Field (ResidueField F) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (ringOfIntegers F))
  let p := ringChar (ResidueField F)
  letI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField F) p⟩
  let e : ResidueField F →* Perfection (ResidueField F) p :=
    Perfection.liftMonoidHom p (ResidueField F) (ResidueField F)
      (MonoidHom.id (ResidueField F))
  let t := Perfection.teichmuller₀ p
    (IsLocalRing.maximalIdeal (ringOfIntegers F))
  change residueMap F (t (e x)) = x
  calc
    residueMap F (t (e x)) = Perfection.coeff (ResidueField F) p 0 (e x) :=
      Perfection.mk_teichmuller₀ (e x)
    _ = x := Perfection.coeffMonoidHom_zero_liftMonoidHom p
      (MonoidHom.id (ResidueField F)) x

theorem teichmuller_injective : Function.Injective (teichmuller F) :=
  Function.LeftInverse.injective (residueMap_teichmuller F)

@[simp]
theorem teichmuller_eq_zero_iff (x : ResidueField F) :
    teichmuller F x = 0 ↔ x = 0 := by
  rw [← map_zero (teichmuller F)]
  exact (teichmuller_injective F).eq_iff

/-- Every Teichmüller representative is a root of `X ^ q_F - X`. -/
@[simp]
theorem teichmuller_pow_residueCard (x : ResidueField F) :
    teichmuller F x ^ residueCard F = teichmuller F x := by
  letI := residueFieldFintype F
  rw [← map_pow]
  congr 1
  exact FiniteField.pow_card x

/-- The nonzero Teichmüller representatives, as units of the valuation ring. -/
noncomputable def teichmullerUnits : (ResidueField F)ˣ →* (ringOfIntegers F)ˣ :=
  Units.map (teichmuller F).toMonoidHom

@[simp]
theorem coe_teichmullerUnits (x : (ResidueField F)ˣ) :
    (teichmullerUnits F x : ringOfIntegers F) = teichmuller F (x : ResidueField F) := rfl

end Teichmuller

section Functoriality

variable {A B C : Type*}
  [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

/-- The residue-field map induced by a local ring homomorphism. -/
noncomputable abbrev residueMapOfLocalHom (f : A →+* B) [IsLocalHom f] :
    IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B :=
  IsLocalRing.ResidueField.map f

@[simp]
theorem residueMapOfLocalHom_residue (f : A →+* B) [IsLocalHom f] (x : A) :
    residueMapOfLocalHom f (IsLocalRing.residue A x) = IsLocalRing.residue B (f x) := rfl

@[simp]
theorem residueMapOfLocalHom_id :
    residueMapOfLocalHom (RingHom.id A) = RingHom.id (IsLocalRing.ResidueField A) :=
  IsLocalRing.ResidueField.map_id

/-- Induced residue maps respect composition of local homomorphisms. -/
theorem residueMapOfLocalHom_comp (f : A →+* B) (g : B →+* C)
    [IsLocalHom f] [IsLocalHom g] :
    residueMapOfLocalHom (g.comp f) =
      (residueMapOfLocalHom g).comp (residueMapOfLocalHom f) :=
  IsLocalRing.ResidueField.map_comp f g

end Functoriality

section TraceNorm

variable (k K : Type*) [Field k] [Field K] [Finite K] [Algebra k K]

/-- The trace map for a finite residue-field extension. -/
noncomputable abbrev residueTrace : K →ₗ[k] k := Algebra.trace k K

/-- The norm map for a finite residue-field extension. -/
noncomputable abbrev residueNorm : K →* k := Algebra.norm k

@[simp]
theorem residueTrace_algebraMap (x : k) :
    residueTrace k K (algebraMap k K x) = Module.finrank k K • x :=
  Algebra.trace_algebraMap x

@[simp]
theorem residueNorm_algebraMap (x : k) :
    residueNorm k K (algebraMap k K x) = x ^ Module.finrank k K :=
  Algebra.norm_algebraMap x

/-- The finite-field trace is the sum of the Frobenius conjugates. -/
theorem algebraMap_residueTrace_eq_sum_frobenius (x : K) :
    algebraMap k K (residueTrace k K x) =
      ∑ i ∈ Finset.range (Module.finrank k K), x ^ (Nat.card k ^ i) :=
  FiniteField.algebraMap_trace_eq_sum_pow k K x

/-- The finite-field norm is the product of the Frobenius conjugates. -/
theorem algebraMap_residueNorm_eq_prod_frobenius (x : K) :
    algebraMap k K (residueNorm k K x) =
      ∏ i ∈ Finset.range (Module.finrank k K), x ^ (Nat.card k ^ i) :=
  FiniteField.algebraMap_norm_eq_prod_pow k K x

end TraceNorm

section TraceNormTower

variable (k K L : Type*) [Field k] [Field K] [Field L]
  [Finite K] [Finite L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

/-- Residue traces compose in a tower of finite fields. -/
theorem residueTrace_trans (x : L) :
    residueTrace k K (residueTrace K L x) = residueTrace k L x :=
  Algebra.trace_trace x

/-- Residue norms compose in a tower of finite fields. -/
theorem residueNorm_trans (x : L) :
    residueNorm k K (residueNorm K L x) = residueNorm k L x :=
  Algebra.norm_norm

end TraceNormTower

end LanglandsFirstMainLemma
