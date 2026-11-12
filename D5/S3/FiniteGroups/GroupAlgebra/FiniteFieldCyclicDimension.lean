/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteFieldCyclicDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.ZMod,
     mathlib/module/Mathlib.LinearAlgebra.Dimension.Free,
     mathlib/module/Mathlib.Algebra.Order.Floor.Div]
   utility: none
   digest: Actual cyclic projectivity over finite fields forces the ceiling dimension bound. -/

import D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldUniformCyclicDimension
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.LinearAlgebra.Dimension.Free

/-!
Restrict the actual representation to the canonical prime field. Invariants
have the same vector predicate, and both norms are the same finite sum. The
public norm criterion therefore transfers actual cyclic projectivity. The
imported public prime-field theorem is used once, without unfolding its proof.
One actual subgroup of order p then gives p-divisibility of the K-dimension
through the public norm criterion, ordinary field-linear lifting, and the
public norm-section equivalence. Cancellation and ceiling division give the
finite-field bound. Rank zero is treated before choosing a nonidentity element.

The prime-field import is used only through its public theorem. The bound is
a classical derived consequence, with no equality construction or novelty claim.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension

open scoped MonoidAlgebra

universe uK uV uP

section Restriction

variable {p : ℕ} [Fact p.Prime]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]
variable {P : Type uP} [Group P]
variable {V : Type uV} [AddCommGroup V] [Module K V]
variable [Module (ZMod p) V] [IsScalarTower (ZMod p) K V]

/-- Forget only the coefficient scalars, retaining the actual vector action. -/
private def primeRestriction (ρ : Representation K P V) :
    Representation (ZMod p) P V where
  toFun g := (ρ g).restrictScalars (ZMod p)
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ρ.map_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (ρ.map_mul g h) v

private theorem primeRestriction_norm [Fintype P]
    (ρ : Representation K P V) (v : V) :
    (primeRestriction (p := p) ρ).norm v = ρ.norm v := by
  change (∑ g : P, (ρ g).restrictScalars (ZMod p)) v = (∑ g : P, ρ g) v
  simp only [LinearMap.sum_apply, LinearMap.restrictScalars_apply]

/-- The norm criterion transfers projectivity on this actual finite p-group.
This does not assume that group-algebra projectivity descends along scalars. -/
private theorem primeRestriction_projective [Finite P] [CharP K p]
    (hP : IsPGroup p P) (ρ : Representation K P V)
    (hproj : Module.Projective K[P] ρ.asModule) :
    Module.Projective (ZMod p)[P] (primeRestriction (p := p) ρ).asModule := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  have hpK : (p : K) ^ 1 = 0 := by
    simpa only [pow_one] using (CharP.cast_eq_zero K p)
  have hp₀ : (p : ZMod p) ^ 1 = 0 := by simp
  have hN :=
    ((PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) hpK hP ρ).mp hproj).2
  apply
    (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) hp₀ hP (primeRestriction (p := p) ρ)).mpr
  refine ⟨inferInstance, ?_⟩
  intro w
  let wK : ρ.invariants := ⟨w.1, fun g => w.2 g⟩
  obtain ⟨v, hv⟩ := hN wK
  refine ⟨v, ?_⟩
  exact (primeRestriction_norm (p := p) ρ v).trans hv

end Restriction

/-- The actual elementary abelian group, including rank zero, is a p-group. -/
private theorem elementary_isPGroup (p r : ℕ) [Fact p.Prime] :
    IsPGroup p (Multiplicative (Fin r → ZMod p)) := by
  apply IsPGroup.of_card (n := r)
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_pi_const, ZMod.card]

/-- A projective representation of an actual finite p-group over a field has
dimension equal to the group order times its invariant dimension. The section
is obtained from the public criterion and ordinary field-module lifting. -/
private theorem finrank_eq_card_mul_invariants
    (p : ℕ) [Fact p.Prime]
    {K : Type uK} [Field K] [CharP K p]
    {P : Type uP} [Group P] [Fintype P]
    {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hP : IsPGroup p P) (ρ : Representation K P V)
    (hproj : Module.Projective K[P] ρ.asModule) :
    Module.finrank K V = Fintype.card P * Module.finrank K ρ.invariants := by
  classical
  have hpK : (p : K) ^ 1 = 0 := by
    simpa only [pow_one] using (CharP.cast_eq_zero K p)
  have hN :=
    ((PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) hpK hP ρ).mp hproj).2
  let N : V →ₗ[K] ρ.invariants :=
    ρ.norm.codRestrict ρ.invariants (fun v g => ρ.self_norm_apply g v)
  have hNsurj : Function.Surjective N := by
    intro w
    obtain ⟨v, hv⟩ := hN w
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨L, hL⟩ := Module.projective_lifting_property N
    (LinearMap.id : ρ.invariants →ₗ[K] ρ.invariants) hNsurj
  have hsection (w : ρ.invariants) : ρ.norm (L w) = (w : V) :=
    congrArg (fun z : ρ.invariants => (z : V)) (LinearMap.congr_fun hL w)
  obtain ⟨e, _he⟩ :=
    PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section
      p 1 (by decide) hpK hP ρ L hsection
  calc
    Module.finrank K V = Module.finrank K (P → ρ.invariants) := e.finrank_eq
    _ = Fintype.card P * Module.finrank K ρ.invariants := by
      rw [Module.finrank_pi_fintype]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/-- For a finite coefficient field of prime-field degree f, actual cyclic
projectivity forces dimension at least p * ceil(r/f). No algebra, scalar tower,
or scalar-restricted projectivity is an additional hypothesis. -/
theorem prime_mul_ceilDiv_finrank_le_finrank_of_cyclic_projective
    (p r : ℕ) [Fact p.Prime]
    {K : Type uK} [Field K] [Finite K] [CharP K p]
    {V : Type uV} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (Multiplicative (Fin r → ZMod p)) V)
    (hproj : ∀ H : Subgroup (Multiplicative (Fin r → ZMod p)), IsCyclic H →
      Module.Projective K[H] (Representation.asModule (ρ.comp H.subtype))) :
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    p * (r ⌈/⌉ Module.finrank (ZMod p) K) ≤ Module.finrank K V := by
  classical
  let : Algebra (ZMod p) K := ZMod.algebra K p
  by_cases hr : r = 0
  · subst r
    simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let : Module (ZMod p) V := Module.compHom V (algebraMap (ZMod p) K)
  let : IsScalarTower (ZMod p) K V := inferInstance
  let : FiniteDimensional (ZMod p) K := inferInstance
  let : FiniteDimensional (ZMod p) V := FiniteDimensional.trans (ZMod p) K V
  have hfpos : 0 < Module.finrank (ZMod p) K := Module.finrank_pos
  have hE := elementary_isPGroup p r
  let ρ₀ : Representation (ZMod p) (Multiplicative (Fin r → ZMod p)) V :=
    primeRestriction (p := p) ρ
  have hproj₀ : ∀ H : Subgroup (Multiplicative (Fin r → ZMod p)), IsCyclic H →
      Module.Projective (ZMod p)[H] (Representation.asModule (ρ₀.comp H.subtype)) := by
    intro H hH
    change Module.Projective (ZMod p)[H]
      (primeRestriction (p := p) (ρ.comp H.subtype)).asModule
    exact primeRestriction_projective (p := p)
      (hE.to_subgroup H) (ρ.comp H.subtype) (hproj H hH)
  have hrank₀ :=
    PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective
      p r ρ₀ hproj₀
  have hrank : r * p ≤ Module.finrank (ZMod p) K * Module.finrank K V := by
    rw [Module.finrank_mul_finrank (ZMod p) K V]
    exact hrank₀
  let g : Multiplicative (Fin r → ZMod p) := Multiplicative.ofAdd (fun _ => 1)
  have hgne : g ≠ 1 := by
    intro hg
    have hi := congrArg
      (fun a : Multiplicative (Fin r → ZMod p) => a.toAdd ⟨0, hrpos⟩) hg
    have hi' : (1 : ZMod p) = 0 := by
      simpa only [g, toAdd_ofAdd, toAdd_one, Pi.zero_apply] using hi
    exact one_ne_zero hi'
  have hgpow : g ^ p = 1 := by
    apply Multiplicative.ext
    rw [toAdd_pow, toAdd_one]
    funext i
    exact ZModModule.char_nsmul_eq_zero p (g.toAdd i)
  have hcard : Fintype.card (Subgroup.zpowers g) = p :=
    Fintype.card_zpowers.trans (orderOf_eq_prime hgpow hgne)
  let n := Module.finrank K (Representation.invariants (ρ.comp (Subgroup.zpowers g).subtype))
  have hd : Module.finrank K V = p * n := by
    simpa only [hcard] using
      (finrank_eq_card_mul_invariants p (hE.to_subgroup (Subgroup.zpowers g))
        (ρ.comp (Subgroup.zpowers g).subtype) (hproj _ inferInstance))
  have hrn : r ≤ Module.finrank (ZMod p) K * n := by
    have hmul : r * p ≤ (Module.finrank (ZMod p) K * n) * p := by
      calc
        r * p ≤ Module.finrank (ZMod p) K * Module.finrank K V := hrank
        _ = (Module.finrank (ZMod p) K * n) * p := by
          rw [hd]
          ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Fact.out : p.Prime).pos
  have hceil : r ⌈/⌉ Module.finrank (ZMod p) K ≤ n :=
    (ceilDiv_le_iff_le_mul hfpos).mpr hrn
  calc
    p * (r ⌈/⌉ Module.finrank (ZMod p) K) ≤ p * n := Nat.mul_le_mul_left p hceil
    _ = Module.finrank K V := hd.symm

end D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension
