/- GID: D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveDimension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Basic, mathlib/module/Mathlib.RepresentationTheory.Intertwining, mathlib/module/Mathlib.Algebra.Module.Projective]
   utility: none
   digest: A modular finite p-group representation is projective exactly at the invariant dimension bound. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupInvariantEmbedding
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Intertwining

/-!
The proof uses the unnormalised Representation.norm. Projectivity splits a
surjective regular-function cover. Its invariant functions are constant, so
evaluation at 1 supplies norm preimages of the invariant basis. These define
a map from a regular free module which is injective on invariants. A nonzero
kernel would contain a nonzero fixed vector, so the whole map is injective.
The existing invariant embedding gives the opposite dimension inequality.
At equality that embedding is an isomorphism onto a regular free module.

All auxiliary declarations are private and consumed below. This is classical
modular representation theory, with no novelty claim or verified exact source
citation for this full criterion. The existing Webb note supports only the
augmentation-nilpotence input to PGroupInvariants. No commutative group-algebra
or local-ring result, averaging, algebraic closure or semisimplicity is used.
The construction is structural, hence utility none.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveDimension

open scoped MonoidAlgebra

universe uK uP uV uW uI

section Functions

variable {k : Type uK} {P : Type uP} {V : Type uV} {W : Type uW}
variable [Field k] [Group P] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

-- T_g(f)(h) = f(h*g). This is a left action even when P is nonabelian.
private def rightTranslate : Representation k P (P → W) where
  toFun g :=
    { toFun := fun f h => f (h * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext h
    exact congrArg f (mul_one h)
  map_mul' g a := by
    apply LinearMap.ext
    intro f
    funext h
    change f (h * (g * a)) = f ((h * g) * a)
    rw [mul_assoc]

private theorem invariant_function_constant (f : P → W)
    (hf : f ∈ (rightTranslate (k := k) (P := P) (W := W)).invariants) (h : P) :
    f h = f 1 := by
  have he := congrFun ((Representation.mem_invariants _ f).mp hf h) (1 : P)
  change f (1 * h) = f 1 at he
  simpa only [one_mul] using he

variable [Fintype P]

-- This is the regular-module map induced by the ordinary linear map L.
private def orbitSum (ρ : Representation k P V) (L : W →ₗ[k] V) :
    Representation.IntertwiningMap (rightTranslate (k := k) (P := P) (W := W)) ρ where
  toLinearMap :=
    { toFun := fun f => ∑ g : P, ρ g (L (f g⁻¹))
      map_add' := by
        intro f a
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    change (∑ a : P, ρ a (L (f (a⁻¹ * g)))) = ρ g (∑ a : P, ρ a (L (f a⁻¹)))
    rw [map_sum]
    symm
    refine Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ ?_
    intro a
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
      map_mul, Module.End.mul_apply]

private theorem orbitSum_apply (ρ : Representation k P V) (L : W →ₗ[k] V)
    (f : P → W) : orbitSum ρ L f = ∑ g : P, ρ g (L (f g⁻¹)) := rfl

private theorem orbitSum_delta [DecidableEq P]
    (ρ : Representation k P V) (L : W →ₗ[k] V) (w : W) :
    orbitSum ρ L (Pi.single (1 : P) w) = L w := by
  classical
  rw [orbitSum_apply]
  simp [Pi.single_apply, apply_ite]

private theorem orbitSum_constant (ρ : Representation k P V) (L : W →ₗ[k] V) (w : W) :
    orbitSum ρ L (fun _ : P => w) = ρ.norm (L w) := by
  simp only [orbitSum_apply, Representation.norm, LinearMap.sum_apply]

-- Reuse the actual free/regular representation, including its module basis.
omit [Fintype P] in
private theorem free_apply_coordinate {ι : Type uI} (g : P) (z : ι →₀ k[P]) (i : ι) :
    Representation.free k P ι g z i = Representation.leftRegular k P g (z i) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single j a =>
      by_cases h : j = i
      · subst j
        simp only [Representation.finsupp_single, Finsupp.single_eq_same]
      · simp [Representation.finsupp_single, h]

omit [Fintype P] in
private theorem rightTranslate_free [Finite P] [FiniteDimensional k W] :
    Module.Free k[P] (rightTranslate (k := k) (P := P) (W := W)).asModule := by
  classical
  let ι := Fin (Module.finrank k W)
  let b : Module.Basis ι k W := Module.finBasis k W
  let C : (P → W) ≃ₗ[k] (ι → P → k) :=
    { toFun := fun f i g => b.equivFun (f g⁻¹) i
      invFun := fun a g => b.equivFun.symm (fun i => a i g⁻¹)
      left_inv := by intro f; funext g; simp
      right_inv := by
        intro a
        funext i g
        change b.equivFun (b.equivFun.symm (fun j => a j (g⁻¹)⁻¹)) i = a i g
        rw [inv_inv, LinearEquiv.apply_symm_apply]
      map_add' := by intro f a; funext i g; simp
      map_smul' := by intro c f; funext i g; simp }
  let D : (P → k) ≃ₗ[k] k[P] :=
    (Finsupp.linearEquivFunOnFinite k k P).symm.trans
      (MonoidAlgebra.coeffLinearEquiv k).symm
  let E : (P → W) ≃ₗ[k] (ι →₀ k[P]) :=
    (C.trans (LinearEquiv.piCongrRight fun _ : ι => D)).trans
      (Finsupp.linearEquivFunOnFinite k k[P] ι).symm
  have hE (f : P → W) (i : ι) (g : P) :
      (E f i).coeff g = b.equivFun (f g⁻¹) i := by
    rfl
  let T : Representation.IntertwiningMap
      (rightTranslate (k := k) (P := P) (W := W)) (Representation.free k P ι) :=
    { toLinearMap := E.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro f
        apply Finsupp.ext
        intro i
        apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro a
        change (E ((rightTranslate (k := k) (P := P) (W := W)) g f) i).coeff a =
          (Representation.free k P ι g (E f) i).coeff a
        rw [free_apply_coordinate, Representation.coeff_ofMulAction, hE, hE]
        change b.equivFun (f (a⁻¹ * g)) i = b.equivFun (f ((g⁻¹ * a)⁻¹)) i
        rw [mul_inv_rev, inv_inv] }
  let TA := Representation.IntertwiningMap.equivLinearMapAsModule _ _ T
  have hTA : Function.Bijective TA := by
    change Function.Bijective E
    exact E.bijective
  let EA := LinearEquiv.ofBijective TA hTA
  exact Module.Free.of_equiv' (Representation.free_asModule_free k P ι) EA.symm

-- Projectivity is used here: split q(f) = sum_g rho(g)(f(g^-1)).
-- For invariant v, its lift is constant, and q of that constant is a norm.
private theorem invariant_norm_preimage (ρ : Representation k P V)
    [Module.Projective k[P] ρ.asModule] (v : ρ.invariants) :
    ∃ x : V, ρ.norm x = (v : V) := by
  classical
  let τ := rightTranslate (k := k) (P := P) (W := V)
  let q := orbitSum ρ (LinearMap.id : V →ₗ[k] V)
  let qA := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ q
  have hq : Function.Surjective qA := by
    intro y
    refine ⟨τ.asModuleEquiv.symm (Pi.single (1 : P) (ρ.asModuleEquiv y)), ?_⟩
    apply ρ.asModuleEquiv.injective
    exact orbitSum_delta ρ (LinearMap.id : V →ₗ[k] V) (ρ.asModuleEquiv y)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qA
    (LinearMap.id : ρ.asModule →ₗ[k[P]] ρ.asModule) hq
  let S : Representation.IntertwiningMap ρ τ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ).symm s
  let u : P → V := S (v : V)
  have hufix : u ∈ τ.invariants := by
    apply (Representation.mem_invariants τ u).mpr
    intro g
    change τ g (S (v : V)) = S (v : V)
    rw [← Representation.IntertwiningMap.isIntertwining ρ τ S g (v : V),
      (Representation.mem_invariants ρ (v : V)).mp v.property g]
  have hconst : u = fun _ : P => u 1 :=
    funext fun h => invariant_function_constant u hufix h
  refine ⟨u 1, ?_⟩
  calc
    ρ.norm (u 1) = q u := by
      symm
      calc
        q u = q (fun _ : P => u 1) := congrArg q hconst
        _ = ρ.norm (u 1) :=
          orbitSum_constant ρ (LinearMap.id : V →ₗ[k] V) (u 1)
    _ = (v : V) := by
      have hv := congrArg ρ.asModuleEquiv
        (LinearMap.congr_fun hs (ρ.asModuleEquiv.symm (v : V)))
      exact hv

end Functions

section Criterion

variable {k : Type uK} {P : Type uP} {V : Type uV} {W : Type uW}
variable [Field k] [Group P] [Finite P] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

private theorem injective_of_invariant_kernel
    (p : ℕ) [Fact p.Prime] [CharP k p] (hP : IsPGroup p P)
    (ρ : Representation k P V) (σ : Representation k P W)
    (f : Representation.IntertwiningMap ρ σ)
    (hf : ∀ v : V, v ∈ ρ.invariants → f v = 0 → v = 0) :
    Function.Injective f := by
  classical
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hxn
    let K : Subrepresentation ρ := f.ker
    let xK : K.toSubmodule := ⟨x, hx⟩
    have hxK : xK ≠ 0 := by
      intro he
      exact hxn (congrArg (fun z : K.toSubmodule => (z : V)) he)
    obtain ⟨y, hy, hyfix⟩ :=
      PGroupInvariants.exists_nonzero_mem_invariants_of_isPGroup
        (R := k) (P := P) (V := K.toSubmodule) p hP K.toRepresentation xK hxK
    have hyV : (y : V) ∈ ρ.invariants := by
      apply (Representation.mem_invariants ρ (y : V)).mpr
      intro g
      exact (Subrepresentation.toRepresentation_apply_coe
        (ρ' := K) (g := g) (v := y) (w := y)).mp
          ((Representation.mem_invariants K.toRepresentation y).mp hyfix g)
    have hy0 : (y : V) = 0 := hf y hyV (LinearMap.mem_ker.mp y.property)
    exact hy (Subtype.ext hy0)
  exact LinearMap.ker_eq_bot.mp hker

/-- For every finite (possibly nonabelian) p-group over any field of
characteristic p, a finite-dimensional representation is projective over the
group algebra exactly when its dimension is the group order times the
dimension of its invariants. The three underlying universes are independent;
the zero vector space and the trivial group are included. -/
theorem projective_iff_finrank_eq_card_mul_finrank_invariants
    [FiniteDimensional k V]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P) (ρ : Representation k P V) :
    Module.Projective k[P] ρ.asModule ↔
      Module.finrank k V = Nat.card P * Module.finrank k ρ.invariants := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let τ := rightTranslate (k := k) (P := P) (W := ρ.invariants)
  have hdim : Module.finrank k (P → ρ.invariants) =
      Nat.card P * Module.finrank k ρ.invariants := by
    rw [Module.finrank_pi_fintype]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨F, hFinj, hFeq⟩ :=
    PGroupInvariantEmbedding.exists_injective_linearMap_invariants_rightTranslate p hP ρ
  constructor
  · intro hproj
    let : Module.Projective k[P] ρ.asModule := hproj
    let ι := Fin (Module.finrank k ρ.invariants)
    let b : Module.Basis ι k ρ.invariants := Module.finBasis k ρ.invariants
    have hb : ∀ i : ι, ∃ x : V, ρ.norm x = (b i : V) :=
      fun i => invariant_norm_preimage ρ (b i)
    choose x hx using hb
    let L : ρ.invariants →ₗ[k] V := b.constr k x
    let N : V →ₗ[k] ρ.invariants := LinearMap.codRestrict ρ.invariants ρ.norm
      (fun v => (Representation.mem_invariants ρ (ρ.norm v)).mpr
        (fun g => ρ.self_norm_apply g v))
    have hNL : N.comp L = LinearMap.id := by
      apply b.ext
      intro i
      apply Subtype.ext
      simpa only [LinearMap.comp_apply, L, Module.Basis.constr_basis,
        LinearMap.id_apply, N, LinearMap.codRestrict_apply]
        using hx i
    have hNL_apply (w : ρ.invariants) : ρ.norm (L w) = (w : V) := by
      exact congrArg (fun z : ρ.invariants => (z : V)) (LinearMap.congr_fun hNL w)
    let Φ : Representation.IntertwiningMap τ ρ := orbitSum ρ L
    have hΦ : Function.Injective Φ := by
      apply injective_of_invariant_kernel p hP τ ρ Φ
      intro f hfix hf0
      have hc : f = fun _ : P => f 1 :=
        funext fun h => invariant_function_constant f hfix h
      have he : Φ f = (f 1 : V) := by
        change orbitSum ρ L f = (f 1 : V)
        rw [hc, orbitSum_constant, hNL_apply]
      have hz : f 1 = 0 := Subtype.ext (he.symm.trans hf0)
      rw [hc, hz]
      rfl
    have hlo : Nat.card P * Module.finrank k ρ.invariants ≤ Module.finrank k V := by
      rw [← hdim]
      exact LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
    have hhi : Module.finrank k V ≤ Nat.card P * Module.finrank k ρ.invariants := by
      rw [← hdim]
      exact LinearMap.finrank_le_finrank_of_injective hFinj
    exact Nat.le_antisymm hhi hlo
  · intro heq
    have hFsurj : Function.Surjective F :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (heq.trans hdim.symm)).mp hFinj
    let T : Representation.IntertwiningMap ρ τ :=
      { toLinearMap := F
        isIntertwining' g := by
          apply LinearMap.ext
          intro v
          funext h
          exact hFeq g h v }
    let TA := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ T
    have hTA : Function.Bijective TA := by
      change Function.Bijective F
      exact ⟨hFinj, hFsurj⟩
    let E := LinearEquiv.ofBijective TA hTA
    let : Module.Free k[P] τ.asModule := rightTranslate_free
    exact Module.Projective.of_equiv' E.symm

end Criterion

end D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveDimension
