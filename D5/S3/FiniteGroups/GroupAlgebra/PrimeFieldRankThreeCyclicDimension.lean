/- GID: D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldRankThreeCyclicDimension
   generality: G
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: [mathlib/module/Mathlib.RingTheory.LocalRing.Module, mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLin]
   utility: none
   digest: Cyclic projectivity for an actual elementary abelian group of rank three forces prime-field dimension at least 3p. -/

import D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

/-!
SOURCE ONLY, UNCOMPILED. Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679.
The rank-two import is the immutable source candidate, not an accepted dependency.
The accompanying visibility-only patch exposes its geometric_norm_polynomial and
chain_independent, consumed below by norm_power and truncated_power_basis.

The algebra used here is the ACTUAL group algebra F[Multiplicative F]. We prove
its locality and construct its (t (p := p))-power basis; no local-ring, free-chain,
constant-reduction, faithfulness, or splitting hypothesis is added to the endpoint.
The first coefficient is an augmentation derivation, not division by (t (p := p)).
The quadratic-centralizer argument is proved in its inverse-free form: every
nonzero element of that centralizer is injective, hence it has no nonzero
nilpotents. This avoids installing an artificial field structure on matrices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldRankThreeCyclicDimension

open scoped MonoidAlgebra
open Module Polynomial Matrix

universe uV uG uH

private abbrev F (p : ℕ) := ZMod p
private abbrev C (p : ℕ) := Multiplicative (F p)
private abbrev E (p : ℕ) := F p × (F p × F p)
private abbrev G (p : ℕ) := Multiplicative (E p)
private abbrev A (p : ℕ) := (F p)[C p]
private abbrev W (p : ℕ) := Fin 2 → F p
private abbrev M₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R

variable {p : ℕ} [Fact p.Prime]

private instance algebra_charP : CharP (A p) p :=
  charP_of_injective_algebraMap (algebraMap (F p) (A p)).injective p

private instance algebra_finite : Module.Finite (F p) (A p) :=
  Module.Finite.of_basis (MonoidAlgebra.basis (C p) (F p))

private def generator : C p := Multiplicative.ofAdd 1

private theorem generator_pow (n : ℕ) :
    ((generator (p := p))) ^ n = Multiplicative.ofAdd (n : F p) := by
  simp [generator, ← ofAdd_nsmul, nsmul_eq_mul]

private theorem c_pow (c : C p) : c ^ p = 1 := by
  apply Multiplicative.ext
  simp [toAdd_pow, nsmul_eq_mul]

private theorem g_pow (g : G p) : g ^ p = 1 := by
  apply Multiplicative.ext
  ext <;> simp [toAdd_pow, nsmul_eq_mul]

private def finiteEnumeration : Fin p ≃ C p :=
  (ZMod.finEquiv p).toEquiv.trans Multiplicative.ofAdd

private theorem finiteEnumeration_apply (i : Fin p) :
    finiteEnumeration i = generator ^ (i : ℕ) := by
  rw [generator_pow]
  change (ZMod.finEquiv p i : F p) = (i : ℕ)
  cases p with
  | zero => exact ((Fact.out : Nat.Prime 0).ne_zero rfl).elim
  | succ n => exact (ZMod.natCast_zmod_val (ZMod.finEquiv (n+1) i)).symm

private noncomputable def augmentation : A p →ₐ[F p] F p :=
  MonoidAlgebra.lift (F p) (F p) (C p) 1

private noncomputable def firstCoefficient : A p →ₗ[F p] F p :=
  (Finsupp.linearCombination (F p) (fun c : C p => c.toAdd)).comp
    (MonoidAlgebra.coeffLinearEquiv (F p)).toLinearMap

private noncomputable def z : A p := MonoidAlgebra.single generator 1
private noncomputable def t : A p := (z (p := p)) - 1
private noncomputable def nu : A p := ∑ c : C p, MonoidAlgebra.single c 1

private theorem augmentation_of (c : C p) :
    augmentation (MonoidAlgebra.of (F p) (C p) c) = 1 := by
  simp [augmentation, MonoidAlgebra.of_apply]

@[simp] private theorem augmentation_single (c : C p) (r : F p) :
    augmentation (MonoidAlgebra.single c r) = r := by
  simp [augmentation]

private theorem firstCoefficient_of (c : C p) :
    firstCoefficient (MonoidAlgebra.of (F p) (C p) c) = c.toAdd := by
  change (Finsupp.linearCombination (F p) (fun c : C p => c.toAdd))
    (Finsupp.single c 1) = c.toAdd
  simp

private theorem augmentation_t : augmentation ((t (p := p)) : A p) = 0 := by
  simp [t, z, augmentation]

private theorem firstCoefficient_one : firstCoefficient (1 : A p) = 0 := by
  change firstCoefficient (MonoidAlgebra.of (F p) (C p) 1) = 0
  simpa using (firstCoefficient_of (p := p)) (1 : C p)

private theorem firstCoefficient_t : firstCoefficient ((t (p := p)) : A p) = 1 := by
  change firstCoefficient ((MonoidAlgebra.of (F p) (C p)) generator - 1) = 1
  rw [map_sub, firstCoefficient_of, firstCoefficient_one]
  simp [generator]

-- This derivation is literally coefficient one after z=1+t. It is defined on
-- the group algebra, so well-definedness modulo t^p does not need cancellation.
private theorem firstCoefficient_mul (a b : A p) :
    firstCoefficient (a * b) =
      augmentation a * firstCoefficient b + firstCoefficient a * augmentation b := by
  induction a using MonoidAlgebra.induction_on with
  | of c =>
    induction b using MonoidAlgebra.induction_on with
    | of d =>
      rw [← map_mul, firstCoefficient_of, firstCoefficient_of, firstCoefficient_of,
        augmentation_of, augmentation_of]
      simp [add_comm]
    | add b₁ b₂ hb₁ hb₂ => simp only [mul_add, map_add, hb₁, hb₂]; ring
    | smul r b hb => simp only [mul_smul_comm, map_smul, hb, smul_eq_mul]; ring
  | add a₁ a₂ ha₁ ha₂ => simp only [add_mul, map_add, ha₁, ha₂]; ring
  | smul r a ha => simp only [smul_mul_assoc, map_smul, ha, smul_eq_mul]; ring

private theorem firstCoefficient_t_mul (a : A p) :
    firstCoefficient ((t (p := p)) * a) = augmentation a := by
  rw [firstCoefficient_mul, augmentation_t, firstCoefficient_t]
  ring

private theorem frobenius_augmentation (a : A p) :
    a ^ p = algebraMap (F p) (A p) (augmentation a) := by
  induction a using MonoidAlgebra.induction_on with
  | of c =>
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, c_pow, augmentation]
  | add a b ha hb =>
      rw [add_pow_char, ha, hb, map_add, map_add]
  | smul r a ha =>
      rw [smul_pow, ZMod.pow_card, ha, map_smul]
      simp [Algebra.smul_def]

private theorem t_nilpotent : ((t (p := p)) : A p) ^ p = 0 := by
  rw [frobenius_augmentation, augmentation_t, map_zero]

private theorem algebra_local : IsLocalRing (A p) := by
  classical
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : augmentation a = 0
  · right
    apply IsNilpotent.isUnit_one_sub
    exact ⟨p, by rw [frobenius_augmentation, ha, map_zero]⟩
  · left
    apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
    rw [frobenius_augmentation]
    exact (isUnit_iff_ne_zero.mpr ha).map (algebraMap (F p) (A p))

private theorem augmentation_kernel_principal (a : A p) :
    augmentation a = 0 ↔ (t (p := p)) ∣ a := by
  have hdiv : ∀ a : A p, (t (p := p)) ∣ a - algebraMap (F p) (A p) (augmentation a) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of c =>
        have hc : c = generator ^ c.toAdd.val := by
          rw [generator_pow, ZMod.natCast_zmod_val, ofAdd_toAdd]
        have hz : MonoidAlgebra.of (F p) (C p) c = (z (p := p)) ^ c.toAdd.val := by
          calc
            _ = MonoidAlgebra.of (F p) (C p) (generator ^ c.toAdd.val) := congrArg _ hc
            _ = (z (p := p)) ^ c.toAdd.val := map_pow _ _ _
        rw [augmentation_of, map_one, hz]
        exact sub_one_dvd_pow_sub_one ((z (p := p)) : A p) c.toAdd.val
    | add a b ha hb =>
        simpa [map_add, add_sub_add_comm] using dvd_add ha hb
    | smul r a ha =>
        simpa [map_smul, Algebra.smul_def, mul_sub] using dvd_mul_of_dvd_right ha
          (algebraMap (F p) (A p) r)
  constructor
  · intro ha
    simpa [ha] using hdiv a
  · rintro ⟨b, rfl⟩
    simp [augmentation_t]

private theorem norm_power : ((nu (p := p)) : A p) = (t (p := p)) ^ (p - 1) := by
  have hgeom := congrArg (Polynomial.aeval ((z (p := p)) : A p))
    (PrimeFieldCyclicProjectivityDimension.geometric_norm_polynomial (p := p))
  have henum : (∑ c : C p, MonoidAlgebra.single c (1 : F p)) =
      ∑ i : Fin p, (z (p := p)) ^ (i : ℕ) := by
    rw [← ((finiteEnumeration (p := p))).sum_comp
      (fun c : C p => MonoidAlgebra.single c (1 : F p))]
    apply Finset.sum_congr rfl
    intro i _
    simp [finiteEnumeration_apply, z, MonoidAlgebra.single_pow]
  rw [nu, henum, ← Finset.sum_range]
  simpa only [map_sum, map_pow, map_sub, map_one, Polynomial.aeval_X, t] using hgeom

private theorem norm_ne_zero : ((nu (p := p)) : A p) ≠ 0 := by
  intro h
  have hc := congrArg (fun a : A p => a.coeff 1) h
  simpa [nu, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single] using hc

private theorem norm_mul (a : A p) : (nu (p := p)) * a = augmentation a • (nu (p := p)) := by
  obtain ⟨b, hb⟩ := (augmentation_kernel_principal
    (a - algebraMap (F p) (A p) (augmentation a))).mp (by simp)
  have hz : (nu (p := p)) * (a - algebraMap (F p) (A p) (augmentation a)) = 0 := by
    rw [hb, norm_power, ← mul_assoc, ← pow_succ,
      Nat.sub_add_cancel (Fact.out : p.Prime).pos, t_nilpotent, zero_mul]
  rw [mul_sub, sub_eq_zero] at hz
  simpa [Algebra.smul_def, mul_comm] using hz

-- Genuine t-chain basis. Together with the later A-basis of size two this is
-- the promised local-free / two-free-chains bridge, not a Jordan assumption.
private noncomputable def truncated_power_basis : Basis (Fin p) (F p) (A p) := by
  let N : Module.End (F p) (A p) :=
    { toFun := fun a => (t (p := p)) * a
      map_add' := mul_add (t (p := p))
      map_smul' := by intro r a; simp [Algebra.smul_def, mul_assoc, mul_left_comm] }
  have hpow (n : ℕ) (a : A p) : (N ^ n) a = (t (p := p)) ^ n * a := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ', Module.End.mul_apply, ih, mul_assoc, N]
  have hN : N ^ p = 0 := by
    apply LinearMap.ext
    intro a
    rw [hpow, t_nilpotent, zero_mul, LinearMap.zero_apply]
  have htop : (N ^ (p - 1)) 1 ≠ 0 := by
    rw [hpow, mul_one, ← norm_power]
    exact (norm_ne_zero (p := p))
  have hli := PrimeFieldCyclicProjectivityDimension.chain_independent N hN 1 htop
  have hd : Module.finrank (F p) (A p) = p := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (C p) (F p))]
    simp [C, F, ZMod.card]
  exact (basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin p => (N ^ (i : ℕ)) 1) hli (by simpa using hd.symm)).map
      (LinearEquiv.refl (F p) (A p))

private theorem algebra_dimension : Module.finrank (F p) (A p) = p := by
  rw [Module.finrank_eq_card_basis ((truncated_power_basis (p := p)))]
  simp

private def direction (a : E p) : C p →* G p where
  toFun c := Multiplicative.ofAdd (c.toAdd • a)
  map_one' := by simp
  map_mul' c d := by simp [add_smul]

private theorem direction_injective {a : E p} (ha : a ≠ 0) :
    Function.Injective (direction a) := by
  intro c d h
  apply Multiplicative.ext
  have he : (c.toAdd - d.toAdd) • a = 0 := by
    simpa [direction, sub_smul, sub_eq_zero] using congrArg Multiplicative.toAdd h
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right ha)

-- Projectivity is transported along an actual group equivalence, including
-- its group-algebra ring equivalence. It is not inferred from the image action.
private theorem projective_reindex
    {H : Type uH} {J : Type uG} [Group H] [Group J]
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    (σ : Representation (F p) J V) (e : H ≃* J)
    (hσ : Module.Projective (F p)[J] σ.asModule) :
    Module.Projective (F p)[H] (Representation.asModule (σ.comp e.toMonoidHom)) := by
  classical
  let τ : Representation (F p) H V := σ.comp e.toMonoidHom
  let r := (MonoidAlgebra.domCongr (F p) (F p) e.symm).toRingEquiv
  letI := RingHomInvPair.of_ringEquiv r
  letI := RingHomInvPair.symm (r : (F p)[J] →+* (F p)[H]) (r.symm : (F p)[H] →+* (F p)[J])
  let eV : LinearEquiv (r : (F p)[J] →+* (F p)[H])
      (σ' := (r.symm : (F p)[H] →+* (F p)[J])) σ.asModule τ.asModule :=
    { toFun := fun v => τ.asModuleEquiv.symm (σ.asModuleEquiv v)
      invFun := fun v => σ.asModuleEquiv.symm (τ.asModuleEquiv v)
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl
      map_add' := by intro v w; rfl
      map_smul' := by
        intro a v
        apply τ.asModuleEquiv.injective
        change σ.asAlgebraHom a (σ.asModuleEquiv v) =
          τ.asAlgebraHom (r a) (σ.asModuleEquiv v)
        induction a using MonoidAlgebra.induction_on with
        | of c => simp [r, τ, MonoidAlgebra.domCongr, MonoidAlgebra.of_apply]
        | add a b ha hb => simp [map_add, LinearMap.add_apply, ha, hb]
        | smul s a ha =>
          have hr : r (s • a) = s • r a :=
            (MonoidAlgebra.domCongr (F p) (F p) e.symm).map_smul s a
          simp only [map_smul, LinearMap.smul_apply, ha, hr] }
  letI := hσ
  exact Module.Projective.of_equiv eV

private theorem pullback_cyclic_projective
    {H : Type uH} {J : Type uG} [Group H] [Group J]
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    (ρ : Representation (F p) J V) (f : H →* J) (hf : Function.Injective f)
    (hcyc : ∀ Q : Subgroup J, IsCyclic Q →
      Module.Projective (F p)[Q] (Representation.asModule (ρ.comp Q.subtype)))
    (Q : Subgroup H) (hQ : IsCyclic Q) :
    Module.Projective (F p)[Q] (Representation.asModule ((ρ.comp f).comp Q.subtype)) := by
  let e := Q.equivMapOfInjective f hf
  letI : IsCyclic Q := hQ
  have hmap : IsCyclic (Q.map f) := isCyclic_of_surjective e e.surjective
  have hp := projective_reindex (ρ.comp (Q.map f).subtype) e (hcyc _ hmap)
  have heq : (ρ.comp (Q.map f).subtype).comp e.toMonoidHom =
      (ρ.comp f).comp Q.subtype := by ext q; rfl
  exact Eq.mp (congrArg (fun σ : Representation (F p) _ V =>
    Module.Projective (F p)[_] σ.asModule) heq) hp

private theorem direction_projective
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    (ρ : Representation (F p) (G p) V)
    (hcyc : ∀ Q : Subgroup (G p), IsCyclic Q →
      Module.Projective (F p)[Q] (Representation.asModule (ρ.comp Q.subtype)))
    {a : E p} (ha : a ≠ 0) :
    Module.Projective (A p) (Representation.asModule (ρ.comp (direction a))) := by
  let f := direction a
  let e : C p ≃* f.range := MonoidHom.ofInjective (direction_injective ha)
  have hcyclic : IsCyclic f.range := isCyclic_of_surjective e e.surjective
  have hp := projective_reindex (ρ.comp f.range.subtype) e (hcyc _ hcyclic)
  have heq : (ρ.comp f.range.subtype).comp e.toMonoidHom = ρ.comp f := by ext c; rfl
  exact Eq.mp (congrArg (fun σ : Representation (F p) _ V =>
    Module.Projective (F p)[_] σ.asModule) heq) hp

private theorem cyclic_free
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule) : Module.Free (A p) σ.asModule := by
  letI : IsLocalRing (A p) := algebra_local
  letI : Module.Projective (A p) σ.asModule := hσ
  letI : Module.Finite (A p) σ.asModule :=
    Module.Finite.of_restrictScalars_finite (F p) (A p) σ.asModule
  exact Module.free_of_flat_of_isLocalRing

private theorem cyclic_dimension
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule) :
    p * Module.finrank (A p) σ.asModule = Module.finrank (F p) V := by
  letI := cyclic_free σ hσ
  have h := Module.finrank_mul_finrank (F p) (A p) σ.asModule
  rw [algebra_dimension, σ.asModuleEquiv.finrank_eq] at h
  exact h

private noncomputable def cyclic_basis_two
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule)
    (hd : Module.finrank (F p) V = 2 * p) : Basis (Fin 2) (A p) σ.asModule := by
  letI := cyclic_free σ hσ
  letI : Module.Finite (A p) σ.asModule :=
    Module.Finite.of_restrictScalars_finite (F p) (A p) σ.asModule
  have hr := cyclic_dimension σ hσ
  have htwo : Module.finrank (A p) σ.asModule = 2 := by
    rw [hd] at hr
    have hp := (Fact.out : p.Prime).pos
    nlinarith
  exact Module.finBasisOfFinrankEq (A p) σ.asModule htwo

private noncomputable def cyclic_coordinates
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule)
    (hd : Module.finrank (F p) V = 2 * p) : V ≃ₗ[F p] (Fin 2 → A p) :=
  σ.asModuleEquiv.symm.trans ((cyclic_basis_two σ hσ hd).equivFun.restrictScalars (F p))

private noncomputable def constantMatrix : M₂ (A p) →ₐ[F p] M₂ (F p) :=
  ((augmentation (p := p))).mapMatrix

private noncomputable def coefficientMatrix : M₂ (A p) →ₗ[F p] M₂ (F p) :=
  ((firstCoefficient (p := p))).mapMatrix

private noncomputable def matrixOperator (B : M₂ (A p)) :
    Module.End (F p) (Fin 2 → A p) := (Matrix.toLin' B).restrictScalars (F p)

private theorem coefficientMatrix_one : (coefficientMatrix (p := p)) (1 : M₂ (A p)) = 0 := by
  ext i j
  by_cases hij : i = j <;> simp [coefficientMatrix, Matrix.one_apply, hij,
    firstCoefficient_one]

private theorem coefficientMatrix_mul (B D : M₂ (A p)) :
    (coefficientMatrix (p := p)) (B * D) =
      (constantMatrix (p := p)) B * (coefficientMatrix (p := p)) D + (coefficientMatrix (p := p)) B * (constantMatrix (p := p)) D := by
  ext i j
  simp only [coefficientMatrix, constantMatrix, LinearMap.mapMatrix_apply,
    AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    firstCoefficient_mul, Finset.sum_add_distrib]

private noncomputable def bottom : (Fin 2 → A p) →ₗ[F p] W p where
  toFun x i := augmentation (x i)
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

private noncomputable def top : W p →ₗ[F p] (Fin 2 → A p) where
  toFun x i := x i • (nu (p := p))
  map_add' x y := by ext i; simp [add_smul]
  map_smul' r x := by ext i; simp [smul_smul]

private theorem bottom_surjective : Function.Surjective ((bottom (p := p))) := by
  intro x
  exact ⟨fun i => algebraMap (F p) (A p) (x i), by ext i; simp [bottom]⟩

private theorem top_injective : Function.Injective ((top (p := p))) := by
  intro x y h
  ext i
  have he : (x i - y i) • ((nu (p := p)) : A p) = 0 := by
    simpa [top, sub_smul] using congrArg (fun z : Fin 2 → A p => z i) (sub_eq_zero.mpr h)
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right (norm_ne_zero (p := p)))

set_option maxHeartbeats 800000 in
-- Normalizing the scalar restrictions and matrix action unfolds both module structures.
private theorem top_factorization (B : M₂ (A p)) :
    (matrixOperator (p := p)) ((nu (p := p)) • B) =
      (top (p := p)).comp ((Matrix.toLin' ((constantMatrix (p := p)) B)).comp (bottom (p := p))) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [matrixOperator, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, LinearMap.comp_apply,
    top, bottom, constantMatrix, AlgHom.mapMatrix_apply, Matrix.map_apply]
  change (∑ j, nu * B i j * x j) =
    (∑ j, augmentation (B i j) * augmentation (x j)) • nu
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  change (nu (p := p)) * B i j * x j = (augmentation (B i j) * augmentation (x j)) • (nu (p := p))
  rw [mul_assoc, norm_mul, map_mul]

private theorem range_rank_injective_comp
    {K X Y Z : Type*} [Field K]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module K X] [Module K Y] [Module K Z]
    (j : Y →ₗ[K] Z) (hj : Function.Injective j) (f : X →ₗ[K] Y) :
    Module.finrank K (LinearMap.range (j.comp f)) =
      Module.finrank K (LinearMap.range f) := by
  let q : LinearMap.range f →ₗ[K] Z := j.comp (LinearMap.range f).subtype
  have hq : Function.Injective q := hj.comp Subtype.val_injective
  have hr : LinearMap.range q = LinearMap.range (j.comp f) := by
    ext z
    constructor
    · rintro ⟨⟨y, x, hx⟩, hy⟩
      exact ⟨x, by simpa [q, LinearMap.comp_apply, hx] using hy⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨f x, ⟨x, rfl⟩⟩, rfl⟩
  rw [← hr, LinearMap.finrank_range_of_inj hq]

private theorem range_rank_equivalent
    {K X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
    [Module K X] [Module K Y] (e : X ≃ₗ[K] Y)
    (f : Module.End K X) (g : Module.End K Y)
    (he : ∀ x, e (f x) = g (e x)) :
    Module.finrank K (LinearMap.range f) = Module.finrank K (LinearMap.range g) := by
  have hr : LinearMap.range g = (LinearMap.range f).map e.toLinearMap := by
    ext y
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨f (e.symm y), ⟨e.symm y, rfl⟩, by exact (he (e.symm y)).trans (congrArg g (e.apply_symm_apply y))⟩
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨e v, (he v).symm⟩
  rw [hr, LinearEquiv.finrank_map_eq]

-- Exact rank identity, not just an upper estimate. The (bottom (p := p)) map is onto
-- and the (top (p := p)) map is one-to-one, including when p=2.
private theorem top_rank_identity (B : M₂ (A p)) :
    Module.finrank (F p) (LinearMap.range ((matrixOperator (p := p)) ((nu (p := p)) • B))) =
      Module.finrank (F p) (LinearMap.range (Matrix.toLin' ((constantMatrix (p := p)) B))) := by
  rw [top_factorization, range_rank_injective_comp (top (p := p)) (top_injective (p := p))]
  have hr : LinearMap.range ((Matrix.toLin' ((constantMatrix (p := p)) B)).comp (bottom (p := p))) =
      LinearMap.range (Matrix.toLin' ((constantMatrix (p := p)) B)) :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (bottom_surjective (p := p)))
  rw [hr]

private theorem canonical_norm
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    (σ : Representation (F p) (C p) V) :
    σ.asAlgebraHom (nu (p := p)) = (σ generator - 1) ^ (p - 1) := by
  rw [norm_power, map_pow, t, map_sub, z, Representation.asAlgebraHom_single_one, map_one]

private theorem cyclic_coordinates_action
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule)
    (hd : Module.finrank (F p) V = 2 * p) (a : A p) (v : V) :
    cyclic_coordinates σ hσ hd (σ.asAlgebraHom a v) =
      a • cyclic_coordinates σ hσ hd v := by
  change (cyclic_basis_two σ hσ hd).equivFun
      (σ.asModuleEquiv.symm (σ.asAlgebraHom a v)) = _
  have he : σ.asModuleEquiv.symm (σ.asAlgebraHom a v) = a • σ.asModuleEquiv.symm v := rfl
  rw [he, map_smul]
  rfl

private theorem norm_rank_two
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V] (σ : Representation (F p) (C p) V)
    (hσ : Module.Projective (A p) σ.asModule)
    (hd : Module.finrank (F p) V = 2 * p) :
    Module.finrank (F p) (LinearMap.range ((σ generator - 1) ^ (p - 1))) = 2 := by
  have hc (v : V) :
      cyclic_coordinates σ hσ hd (((σ generator - 1) ^ (p - 1)) v) =
        (matrixOperator (p := p)) ((nu (p := p)) • (1 : M₂ (A p))) (cyclic_coordinates σ hσ hd v) := by
    rw [← canonical_norm, cyclic_coordinates_action]
    ext i
    simp [matrixOperator, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [range_rank_equivalent (cyclic_coordinates σ hσ hd) _ _ hc,
    (top_rank_identity (p := p)), map_one]
  have hfull : LinearMap.range (Matrix.toLin' (1 : M₂ (F p))) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    exact ⟨x, by simp⟩
  rw [hfull, finrank_top]
  simp

private theorem constant_kernel_factor (B : M₂ (A p))
    (hB : (constantMatrix (p := p)) B = 0) : ∃ Q : M₂ (A p), B = (t (p := p)) • Q := by
  have hex (i j : Fin 2) : ∃ q : A p, B i j = (t (p := p)) * q := by
    have hz : augmentation (B i j) = 0 := congrFun (congrFun hB i) j
    obtain ⟨q, hq⟩ := (augmentation_kernel_principal _).mp hz
    exact ⟨q, hq⟩
  choose Q hQ using hex
  exact ⟨Q, by apply Matrix.ext; intro i j; exact hQ i j⟩

private theorem kernel_norm_leading (B : M₂ (A p))
    (hB : (constantMatrix (p := p)) B = 1) :
    Module.finrank (F p) (LinearMap.range ((matrixOperator (p := p)) ((B - 1) ^ (p - 1)))) =
      Module.finrank (F p)
        (LinearMap.range (Matrix.toLin' (((coefficientMatrix (p := p)) B) ^ (p - 1)))) := by
  obtain ⟨Q, hQ⟩ := (constant_kernel_factor (p := p)) (B - 1) (by rw [map_sub, hB, map_one]; simp)
  have hd : (coefficientMatrix (p := p)) B = (constantMatrix (p := p)) Q := by
    have he := congrArg (coefficientMatrix (p := p)) hQ
    rw [map_sub, coefficientMatrix_one, sub_zero] at he
    exact he.trans (by ext i j; exact firstCoefficient_t_mul (Q i j))
  rw [hQ, smul_pow, ← norm_power, (top_rank_identity (p := p)), map_pow, ← hd]

private noncomputable def commutingAction
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    (ρ : Representation (F p) (G p) V) (s : E p) (g : G p) :
    Module.End (A p) (Representation.asModule (ρ.comp (direction s))) :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    ((ρ g).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro c v
      change (ρ g * ρ (direction s c)) v = (ρ (direction s c) * ρ g) v
      rw [← map_mul, ← map_mul, mul_comm]))

private noncomputable def blockAction
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V]
    (ρ : Representation (F p) (G p) V) (s : E p)
    (hσ : Module.Projective (A p) (Representation.asModule (ρ.comp (direction s))))
    (hd : Module.finrank (F p) V = 2 * p) : G p →* M₂ (A p) where
  toFun g := LinearMap.toMatrixAlgEquiv (cyclic_basis_two (ρ.comp (direction s)) hσ hd)
    (commutingAction ρ s g)
  map_one' := by
    let b := cyclic_basis_two (ρ.comp (direction s)) hσ hd
    change LinearMap.toMatrixAlgEquiv b (commutingAction ρ s 1) = 1
    rw [← map_one (LinearMap.toMatrixAlgEquiv b)]
    congr 1
    apply LinearMap.ext
    intro v
    apply (Representation.asModuleEquiv (ρ.comp (direction s))).injective
    change ρ 1 ((Representation.asModuleEquiv (ρ.comp (direction s))) v) = _
    rw [map_one, Module.End.one_apply]
    rfl
  map_mul' g h := by
    let b := cyclic_basis_two (ρ.comp (direction s)) hσ hd
    change LinearMap.toMatrixAlgEquiv b (commutingAction ρ s (g*h)) =
      LinearMap.toMatrixAlgEquiv b (commutingAction ρ s g) *
        LinearMap.toMatrixAlgEquiv b (commutingAction ρ s h)
    rw [← map_mul (LinearMap.toMatrixAlgEquiv b)]
    congr 1
    apply LinearMap.ext
    intro v
    apply (Representation.asModuleEquiv (ρ.comp (direction s))).injective
    change ρ (g*h) ((Representation.asModuleEquiv (ρ.comp (direction s))) v) =
      ρ g (ρ h ((Representation.asModuleEquiv (ρ.comp (direction s))) v))
    rw [map_mul, Module.End.mul_apply]

private theorem blockAction_intertwines
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V]
    (ρ : Representation (F p) (G p) V) (s : E p)
    (hσ : Module.Projective (A p) (Representation.asModule (ρ.comp (direction s))))
    (hd : Module.finrank (F p) V = 2 * p) (g : G p) (v : V) :
    cyclic_coordinates (ρ.comp (direction s)) hσ hd (ρ g v) =
      (matrixOperator (p := p)) (blockAction ρ s hσ hd g)
        (cyclic_coordinates (ρ.comp (direction s)) hσ hd v) := by
  let b := cyclic_basis_two (ρ.comp (direction s)) hσ hd
  let w := (Representation.asModuleEquiv (ρ.comp (direction s))).symm v
  change b.repr (commutingAction ρ s g w) =
    LinearMap.toMatrixAlgEquiv b (commutingAction ρ s g) *ᵥ b.repr w
  have hm : LinearMap.toMatrixAlgEquiv b (commutingAction ρ s g) =
      LinearMap.toMatrix b b (commutingAction ρ s g) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  rw [hm]
  exact (LinearMap.toMatrix_mulVec_repr b b (commutingAction ρ s g) w).symm

private theorem blockAction_distinguished
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V]
    (ρ : Representation (F p) (G p) V) (s : E p)
    (hσ : Module.Projective (A p) (Representation.asModule (ρ.comp (direction s))))
    (hd : Module.finrank (F p) V = 2 * p) :
    blockAction ρ s hσ hd (Multiplicative.ofAdd s) = (z (p := p)) • (1 : M₂ (A p)) := by
  apply Matrix.ext
  intro i j
  change LinearMap.toMatrixAlgEquiv
    (cyclic_basis_two (ρ.comp (direction s)) hσ hd)
    (commutingAction ρ s (Multiplicative.ofAdd s)) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  have he (v : (Representation.asModule (ρ.comp (direction s)))) :
      commutingAction ρ s (Multiplicative.ofAdd s) v = ((z (p := p)) : A p) • v := by
    apply (Representation.asModuleEquiv (ρ.comp (direction s))).injective
    simp [commutingAction, Representation.asModuleEquiv_map_smul, z, generator, direction]
    rfl
  rw [he, map_smul, Basis.repr_self]
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

private theorem block_norm_rank
    {V : Type uV} [AddCommGroup V] [Module (F p) V]
    [FiniteDimensional (F p) V]
    (ρ : Representation (F p) (G p) V) (s : E p)
    (hσ : Module.Projective (A p) (Representation.asModule (ρ.comp (direction s))))
    (hd : Module.finrank (F p) V = 2 * p) (a : E p)
    (hτ : Module.Projective (A p) (Representation.asModule (ρ.comp (direction a)))) :
    Module.finrank (F p)
      (LinearMap.range ((matrixOperator (p := p))
        ((blockAction ρ s hσ hd (Multiplicative.ofAdd a) - 1) ^ (p - 1)))) = 2 := by
  let e := cyclic_coordinates (ρ.comp (direction s)) hσ hd
  let B := blockAction ρ s hσ hd
  have hbase (v : V) : e ((ρ (Multiplicative.ofAdd a) - 1) v) =
      (matrixOperator (p := p)) (B (Multiplicative.ofAdd a) - 1) (e v) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub,
      blockAction_intertwines, matrixOperator, map_sub, Matrix.toLin'_one,
      LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.id_apply]
    exact congrArg (fun x => x - e v) (blockAction_intertwines ρ s hσ hd _ v)
  have hpow (n : ℕ) (v : V) : e (((ρ (Multiplicative.ofAdd a) - 1) ^ n) v) =
      (matrixOperator (p := p)) ((B (Multiplicative.ofAdd a) - 1) ^ n) (e v) := by
    induction n with
    | zero => simp [matrixOperator, e]
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, hbase, ih, pow_succ']
        simp [matrixOperator, Matrix.toLin'_mul, LinearMap.comp_apply]
  have hr := range_rank_equivalent e _ _ (hpow (p - 1))
  have hn := norm_rank_two (ρ.comp (direction a)) hτ hd
  have hgen : (ρ.comp (direction a)) generator = ρ (Multiplicative.ofAdd a) := by
    simp [direction, generator]
  rw [hgen] at hn
  exact hr.symm.trans hn

private theorem dimension_W : Module.finrank (F p) (W p) = 2 := by
  simp [W, Module.finrank_pi]

private theorem dimension_E : Module.finrank (F p) (E p) = 3 := by
  simp [E, Module.finrank_prod]

private theorem scalar_is_nsmul
    {X : Type*} [AddCommGroup X] [Module (F p) X] (a : F p) (x : X) :
    a • x = a.val • x := by
  rw [← Nat.cast_smul_eq_nsmul (F p), ZMod.natCast_zmod_val]

private noncomputable def primeLinearOfAddHom
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module (F p) X] [Module (F p) Y] (f : X →+ Y) : X →ₗ[F p] Y where
  __ := f
  map_smul' a x := by
    change f (a • x) = a • f x
    rw [scalar_is_nsmul, scalar_is_nsmul, map_nsmul]

private theorem power_injective
    (T : Module.End (F p) (W p)) (hT : Function.Injective T) (n : ℕ) :
    Function.Injective (T ^ n) := by
  induction n with
  | zero => intro v w h; exact h
  | succ n ih =>
      intro v w he
      apply ih
      apply hT
      simpa only [pow_succ', Module.End.mul_apply] using he

private theorem eigen_power
    (T : Module.End (F p) (W p)) (v : W p) (a : F p)
    (h : T v = a • v) (n : ℕ) : (T ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', Module.End.mul_apply, ih, h, smul_smul, mul_comm]

private theorem nilpotent_square
    (D : Module.End (F p) (W p)) (hD : D ^ p = 0) : D ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearMap.ker (D ^ p) := by simp [hD]
  have hz := Module.End.ker_pow_le_ker_pow_finrank D p hv
  simpa only [(dimension_W (p := p)), LinearMap.mem_ker, LinearMap.zero_apply] using hz

-- The single substantial 2x2 centralizer calculation is shared by both the
-- unipotent image bound and the quadratic (no eigenvalue) argument.
private theorem cyclic_pair_centralizer
    (X T : Module.End (F p) (W p)) (v : W p)
    (hli : LinearIndependent (F p) ![X v, v]) (hTX : Commute T X) :
    ∃ a b : F p, T = a • 1 + b • X := by
  classical
  let B : Basis (Fin 2) (F p) (W p) :=
    basisOfLinearIndependentOfCardEqFinrank' ![X v, v] hli (by simp [(dimension_W (p := p))])
  have hB0 : B 0 = X v := by simp [B]
  have hB1 : B 1 = v := by simp [B]
  let a := B.repr (T v) 1
  let b := B.repr (T v) 0
  have hv : T v = a • v + b • X v := by
    have he := B.sum_repr (T v)
    rw [Fin.sum_univ_two, hB0, hB1] at he
    exact he.symm.trans (add_comm _ _)
  refine ⟨a, b, B.ext (fun i => ?_)⟩
  fin_cases i
  · change T (B 0) = (a • 1 + b • X) (B 0)
    rw [hB0]
    change T (X v) = a • X v + b • X (X v)
    have hc := LinearMap.congr_fun hTX.eq v
    change T (X v) = X (T v) at hc
    rw [hc, hv, map_add, map_smul, map_smul]
  · change T (B 1) = (a • 1 + b • X) (B 1)
    rw [hB1]
    exact hv

private theorem nilpotent_cyclic_pair
    (D : Module.End (F p) (W p)) (hD : D ^ 2 = 0) (v : W p) (hv : D v ≠ 0) :
    LinearIndependent (F p) ![D v, v] := by
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ a : F p, a • v ≠ D v
  refine ⟨fun hz => hv (by rw [hz, map_zero]), ?_⟩
  intro a ha
  have he := congrArg D ha
  have hDD : D (D v) = 0 := by
    change (D ^ 2) v = 0
    simpa only [LinearMap.zero_apply] using LinearMap.congr_fun hD v
  have haz : a = 0 := (smul_eq_zero.mp (by simpa [hDD] using he)).resolve_right hv
  exact hv (by simpa [haz] using ha.symm)

private theorem unipotent_centralizer
    (D T : Module.End (F p) (W p)) (hD : D ≠ 0) (hD2 : D ^ 2 = 0)
    (hTD : Commute T D) (hTp : T ^ p = 1) :
    ∃ b : F p, T = 1 + b • D := by
  have hex : ∃ v : W p, D v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hD (LinearMap.ext hn)
  obtain ⟨v, hv⟩ := hex
  obtain ⟨a, b, hT⟩ := cyclic_pair_centralizer D T v (nilpotent_cyclic_pair D hD2 v hv) hTD
  have hDD : D (D v) = 0 := by
    change (D ^ 2) v = 0
    simpa only [LinearMap.zero_apply] using LinearMap.congr_fun hD2 v
  have heigen : T (D v) = a • D v := by simp [hT, hDD]
  have he := eigen_power T (D v) a heigen p
  rw [hTp, Module.End.one_apply, ZMod.pow_card] at he
  have ha : a = 1 := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp ?_).resolve_right hv
    rw [sub_smul, one_smul, ← he, sub_self]
  exact ⟨b, by simpa only [ha, one_smul] using hT⟩

private theorem pencil_injective
    (X : Module.End (F p) (W p))
    (hX : ∀ a : F p, Function.Injective (X - a • (1 : Module.End (F p) (W p))))
    {a b : F p} (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Injective (a • (1 : Module.End (F p) (W p)) + b • X) := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
    intro v w he
    have hz : a • (v - w) = 0 := by
      simpa [hb, smul_sub] using sub_eq_zero.mpr he
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left ha)
  · have hscale : b⁻¹ • (a • (1 : Module.End (F p) (W p)) + b • X) =
        X - (-(b⁻¹ * a)) • 1 := by
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul,
        sub_eq_add_neg, neg_smul, neg_neg, add_comm]
    intro v w he
    apply hX (-(b⁻¹ * a))
    rw [← hscale]
    simpa only [LinearMap.smul_apply] using congrArg (fun y : W p => b⁻¹ • y) he

private theorem no_eigenvalue_pair
    (X : Module.End (F p) (W p))
    (hX : ∀ a : F p, Function.Injective (X - a • (1 : Module.End (F p) (W p)))) (v : W p) (hv : v ≠ 0) :
    LinearIndependent (F p) ![X v, v] := by
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ a : F p, a • v ≠ X v
  refine ⟨hv, ?_⟩
  intro a ha
  have hz : (X - a • 1) v = (X - a • 1) 0 := by simp [ha.symm]
  exact hv (hX a hz)

-- This is precisely the needed field property of the quadratic centralizer.
-- All nonzero aI+bX are injective, so a commuting nilpotent must be zero.
private theorem quadratic_centralizer_no_nilpotents
    (X D : Module.End (F p) (W p))
    (hX : ∀ a : F p, Function.Injective (X - a • (1 : Module.End (F p) (W p))))
    (hDX : Commute D X) (hD : IsNilpotent D) : D = 0 := by
  let v : W p := Pi.single 0 1
  have hv : v ≠ 0 := by intro hz; have := congrFun hz 0; simpa [v] using this
  obtain ⟨a, b, he⟩ := cyclic_pair_centralizer X D v (no_eigenvalue_pair X hX v hv) hDX
  by_cases hab : a = 0 ∧ b = 0
  · simp [he, hab.1, hab.2]
  · have hinj : Function.Injective D := by
      rw [he]
      exact pencil_injective X hX (by tauto)
    obtain ⟨n, hn⟩ := hD
    exact (hv (power_injective D hinj n (by simp [hn]))).elim

private noncomputable def reductionKernel (R : G p →* M₂ (F p)) : Submodule (F p) (E p) where
  carrier := {a | R (Multiplicative.ofAdd a) = 1}
  zero_mem' := by simpa using R.map_one
  add_mem' := by
    intro a b ha hb
    change R (Multiplicative.ofAdd a * Multiplicative.ofAdd b) = 1
    rw [map_mul, ha, hb, one_mul]
  smul_mem' := by
    intro c a ha
    change R (Multiplicative.ofAdd (c • a)) = 1
    rw [scalar_is_nsmul, ofAdd_nsmul, map_pow, ha, one_pow]

private theorem reductionKernel_large (R : G p →* M₂ (F p)) :
    2 ≤ Module.finrank (F p) (reductionKernel R) := by
  classical
  by_cases htriv : ∀ g : G p, R g = 1
  · have htop : reductionKernel R = ⊤ := by
      ext a
      simp [reductionKernel, htriv]
    rw [htop, finrank_top, (dimension_E (p := p))]
    omega
  · obtain ⟨g₀, hg₀⟩ := not_forall.mp htriv
    let D : Module.End (F p) (W p) := Matrix.toLin' (R g₀ - 1)
    have hDp : D ^ p = 0 := by
      have hp : (R g₀ - 1) ^ p = 0 := by
        rw [sub_pow_char_of_commute p (Commute.one_right _), ← map_pow, g_pow,
          map_one, one_pow, sub_self]
      simpa [D] using congrArg (Matrix.toLin' : M₂ (F p) → Module.End (F p) (W p)) hp
    have hD : D ≠ 0 := by
      intro hz
      have he : R g₀ - 1 = 0 := Matrix.toLin'.injective (by simpa [D] using hz)
      exact hg₀ (sub_eq_zero.mp he)
    have hD2 := nilpotent_square D hDp
    have hclass (g : G p) : ∃ b : F p, Matrix.toLin' (R g) = 1 + b • D := by
      apply unipotent_centralizer D (Matrix.toLin' (R g)) hD hD2
      · change Matrix.toLin' (R g) * Matrix.toLin' (R g₀ - 1) =
          Matrix.toLin' (R g₀ - 1) * Matrix.toLin' (R g)
        have he : R g * (R g₀ - 1) = (R g₀ - 1) * R g := by
          rw [mul_sub, sub_mul, mul_one, one_mul, ← map_mul, ← map_mul, mul_comm g g₀]
        simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using congrArg Matrix.toLin' he
      · rw [← Matrix.toLin'_pow, ← map_pow, g_pow, map_one, Matrix.toLin'_one]
        rfl
    choose b hb using hclass
    have huniq {a c : F p} (he : 1 + a • D = 1 + c • D) : a = c := by
      apply sub_eq_zero.mp
      have hz : (a - c) • D = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact add_left_cancel he
      exact (smul_eq_zero.mp hz).resolve_right hD
    have hadd (g h : G p) : b (g * h) = b g + b h := by
      apply huniq
      calc
        1 + b (g * h) • D = Matrix.toLin' (R (g * h)) := (hb _).symm
        _ = Matrix.toLin' (R g) * Matrix.toLin' (R h) := by
          simp only [map_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]
        _ = (1 + b g • D) * (1 + b h • D) := by rw [hb, hb]
        _ = 1 + (b g + b h) • D := by
          have hDD : D * D = 0 := by simpa only [pow_two] using hD2
          simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
            mul_smul_comm, hDD, smul_zero]
          module
    let qadd : E p →+ F p :=
      { toFun a := b (Multiplicative.ofAdd a)
        map_zero' := by
          apply huniq
          simpa only [ofAdd_zero, map_one, Matrix.toLin'_one,
            zero_smul, add_zero, Module.End.one_eq_id] using (hb 1).symm
        map_add' a c := hadd (Multiplicative.ofAdd a) (Multiplicative.ofAdd c) }
    let q : E p →ₗ[F p] F p := primeLinearOfAddHom qadd
    have hker : reductionKernel R = LinearMap.ker q := by
      ext a
      change R (Multiplicative.ofAdd a) = 1 ↔ b (Multiplicative.ofAdd a) = 0
      constructor
      · intro ha
        apply huniq
        simpa only [ha, Matrix.toLin'_one, zero_smul, add_zero, Module.End.one_eq_id] using (hb (Multiplicative.ofAdd a)).symm
      · intro ha
        apply Matrix.toLin'.injective
        simp only [hb, ha, zero_smul, add_zero, Matrix.toLin'_one, Module.End.one_eq_id]
    have hrank := q.finrank_range_add_finrank_ker
    have hle := (LinearMap.range q).finrank_le
    rw [(dimension_E (p := p))] at hrank
    have hF : Module.finrank (F p) (F p) = 1 := Module.finrank_self _
    rw [hF] at hle
    rw [hker]
    omega

private noncomputable def reduced (B : G p →* M₂ (A p)) : G p →* M₂ (F p) :=
  ((constantMatrix (p := p))).toMonoidHom.comp B

private noncomputable def leading (B : G p →* M₂ (A p)) :
    reductionKernel (reduced B) →ₗ[F p] M₂ (F p) :=
  primeLinearOfAddHom
    { toFun a := (coefficientMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p)))
      map_zero' := by
        simp only [Submodule.coe_zero, ofAdd_zero, map_one,
          coefficientMatrix_one]
      map_add' a b := by
        have ha : (constantMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p))) = 1 := a.property
        have hb : (constantMatrix (p := p)) (B (Multiplicative.ofAdd (b : E p))) = 1 := b.property
        change (coefficientMatrix (p := p))
          (B (Multiplicative.ofAdd (a : E p) * Multiplicative.ofAdd (b : E p))) = _
        rw [map_mul, coefficientMatrix_mul, ha, hb, one_mul, mul_one, add_comm] }

private theorem leading_commutes_reduction (B : G p →* M₂ (A p))
    (a : reductionKernel (reduced B)) (g : G p) :
    Commute (reduced B g) (leading B a) := by
  have he : B g * B (Multiplicative.ofAdd (a : E p)) =
      B (Multiplicative.ofAdd (a : E p)) * B g := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hc := congrArg (coefficientMatrix (p := p)) he
  have ha : (constantMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p))) = 1 := a.property
  rw [coefficientMatrix_mul, coefficientMatrix_mul, ha, one_mul, mul_one] at hc
  change (constantMatrix (p := p)) (B g) * (coefficientMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p))) =
    (coefficientMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p))) * (constantMatrix (p := p)) (B g)
  exact add_right_cancel (by simpa only [add_comm] using hc)

private theorem leading_injective (B : G p →* M₂ (A p))
    (hnorm : ∀ a : E p, a ≠ 0 →
      Module.finrank (F p)
        (LinearMap.range ((matrixOperator (p := p)) ((B (Multiplicative.ofAdd a) - 1) ^ (p - 1)))) = 2)
    (a : reductionKernel (reduced B)) (ha : a ≠ 0) :
    Function.Injective (Matrix.toLin' (leading B a)) := by
  have hane : (a : E p) ≠ 0 := by
    intro hz
    exact ha (Subtype.ext hz)
  have hr := hnorm (a : E p) hane
  have hk : (constantMatrix (p := p)) (B (Multiplicative.ofAdd (a : E p))) = 1 := a.property
  rw [(kernel_norm_leading (p := p)) _ hk] at hr
  change Module.finrank (F p)
      (LinearMap.range (Matrix.toLin' ((leading B a) ^ (p - 1)))) = 2 at hr
  have hfull : LinearMap.range (Matrix.toLin' ((leading B a) ^ (p - 1))) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hr.trans (dimension_W (p := p)).symm)
  have hinj : Function.Injective (Matrix.toLin' ((leading B a) ^ (p - 1))) :=
    LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp hfull)
  intro v w he
  have hz : Matrix.toLin' (leading B a) (v - w) = 0 := by simp [map_sub, he]
  have hn : p - 1 = p - 2 + 1 := by have hp := (Fact.out : p.Prime).two_le; omega
  have hpw : Matrix.toLin' ((leading B a) ^ (p - 1)) (v - w) = 0 := by
    rw [Matrix.toLin'_pow, hn, pow_succ, Module.End.mul_apply, hz, map_zero]
  exact sub_eq_zero.mp (hinj (hpw.trans (map_zero _).symm))

private theorem distinguished_leading
    (B : G p →* M₂ (A p)) (s : E p)
    (hs : B (Multiplicative.ofAdd s) = (z (p := p)) • (1 : M₂ (A p))) :
    ∃ sK : reductionKernel (reduced B), (sK : E p) = s ∧ leading B sK = 1 := by
  have hεz : augmentation (z : A p) = 1 := by simp [z, augmentation]
  have hδz : firstCoefficient ((z (p := p)) : A p) = 1 := by
    have hz : (z : A p) = t + 1 := by dsimp [t]; abel
    rw [hz, map_add, firstCoefficient_t, firstCoefficient_one, add_zero]
  have hred : reduced B (Multiplicative.ofAdd s) = 1 := by
    change (constantMatrix (p := p)) (B (Multiplicative.ofAdd s)) = 1
    rw [hs]
    ext i j
    by_cases hij : i = j <;> simp [constantMatrix, Matrix.one_apply, hij, hεz]
  refine ⟨⟨s, hred⟩, rfl, ?_⟩
  change (coefficientMatrix (p := p)) (B (Multiplicative.ofAdd s)) = 1
  rw [hs]
  ext i j
  by_cases hij : i = j <;> simp [coefficientMatrix, Matrix.one_apply, hij, hδz]

-- Rank THREE is used before reduction is made trivial. In particular this
-- theorem says nothing about an arbitrary rank-two elementary group.
private theorem two_block_obstruction
    (B : G p →* M₂ (A p)) (s : E p) (hs : s ≠ 0)
    (hBs : B (Multiplicative.ofAdd s) = (z (p := p)) • (1 : M₂ (A p)))
    (hnorm : ∀ a : E p, a ≠ 0 →
      Module.finrank (F p)
        (LinearMap.range ((matrixOperator (p := p)) ((B (Multiplicative.ofAdd a) - 1) ^ (p - 1)))) = 2) :
    False := by
  classical
  let R := reduced B
  let K := reductionKernel R
  let L := leading B
  obtain ⟨sK, hsK, hLs⟩ := (distinguished_leading (p := p)) B s hBs
  have hsKne : sK ≠ 0 := by
    intro hz
    apply hs
    rw [← hsK, hz]
    rfl
  have hKdim : 2 ≤ Module.finrank (F p) K := reductionKernel_large R
  have hspan : Submodule.span (F p) ({sK} : Set K) ≠ ⊤ := by
    intro he
    have hr : Module.finrank (F p) (Submodule.span (F p) ({sK} : Set K)) = 1 :=
      finrank_span_singleton (K := F p) hsKne
    rw [he, finrank_top] at hr
    omega
  have hex : ∃ h : K, h ∉ Submodule.span (F p) ({sK} : Set K) := by
    by_contra hn
    push_neg at hn
    exact hspan (Submodule.eq_top_iff'.mpr hn)
  obtain ⟨h, hh⟩ := hex
  have hXeigen (a : F p) : Function.Injective (Matrix.toLin' (L h - a • 1)) := by
    have hne : h - a • sK ≠ 0 := by
      intro hz
      have he : h = a • sK := sub_eq_zero.mp hz
      rw [he] at hh
      exact hh (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
    have hi := leading_injective B hnorm (h - a • sK) hne
    simpa only [map_sub, map_smul, hLs] using hi
  let X : Module.End (F p) (W p) := Matrix.toLin' (L h)
  have hX (a : F p) : Function.Injective (X - a • (1 : Module.End (F p) (W p))) := by
    simpa only [X, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id] using hXeigen a
  have htriv (g : G p) : R g = 1 := by
    let D : Module.End (F p) (W p) := Matrix.toLin' (R g - 1)
    have hcomm : Commute D X := by
      have hc := leading_commutes_reduction B h g
      have hm : (R g - 1) * L h = L h * (R g - 1) := by
        rw [sub_mul, mul_sub, one_mul, mul_one, hc.eq]
      change Matrix.toLin' (R g - 1) * Matrix.toLin' (L h) =
        Matrix.toLin' (L h) * Matrix.toLin' (R g - 1)
      simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using congrArg Matrix.toLin' hm
    have hnil : IsNilpotent D := by
      refine ⟨p, ?_⟩
      have hp : (R g - 1) ^ p = 0 := by
        rw [sub_pow_char_of_commute p (Commute.one_right _), ← map_pow, g_pow,
          map_one, one_pow, sub_self]
      simpa only [D, Matrix.toLin'_pow, map_zero] using congrArg Matrix.toLin' hp
    have hz : D = 0 := quadratic_centralizer_no_nilpotents X D hX hcomm hnil
    have hm : R g - 1 = 0 := Matrix.toLin'.injective (by simpa [D] using hz)
    exact sub_eq_zero.mp hm
  have hKtop : K = ⊤ := by
    ext a
    simp [K, reductionKernel, htriv]
  let v : W p := Pi.single 0 1
  have hv : v ≠ 0 := by intro hz; have := congrFun hz 0; simpa [v] using this
  let evaluation : K →ₗ[F p] W p :=
    { toFun a := Matrix.toLin' (L a) v
      map_add' a b := by simp [map_add]
      map_smul' c a := by simp [map_smul] }
  have heval : Function.Injective evaluation := by
    intro a b he
    have hz : evaluation (a - b) = 0 := by rw [map_sub, he, sub_self]
    by_contra hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hi := leading_injective B hnorm (a - b) hne
    have hezero : Matrix.toLin' (L (a - b)) v = Matrix.toLin' (L (a - b)) 0 := by
      change Matrix.toLin' (L (a - b)) v = 0 at hz
      exact hz.trans (map_zero _).symm
    exact hv (hi hezero)
  have hle := LinearMap.finrank_le_finrank_of_injective heval
  change Module.finrank (F p) K ≤ Module.finrank (F p) (W p) at hle
  rw [hKtop, finrank_top, (dimension_E (p := p)), (dimension_W (p := p))] at hle
  omega

private def rankTwoInclusion : Multiplicative (F p × F p) →* G p where
  toFun g := Multiplicative.ofAdd (g.toAdd.1, (g.toAdd.2, 0))
  map_one' := rfl
  map_mul' g h := by apply Multiplicative.ext; simp

private theorem rankTwoInclusion_injective : Function.Injective ((rankTwoInclusion (p := p))) := by
  intro g h he
  apply Multiplicative.ext
  apply Prod.ext
  · simpa [rankTwoInclusion] using congrArg (fun a : G p => a.toAdd.1) he
  · simpa [rankTwoInclusion] using congrArg (fun a : G p => a.toAdd.2.1) he

/-- Every nonzero finite-dimensional F_p representation of the actual group
C_p^3 whose restrictions to all actual cyclic subgroups are projective has
dimension at least 3p. Includes p=2, independent universes, and nonfaithful
representations. This is candidate source, with no compilation claim. -/
theorem three_mul_prime_le_finrank_of_cyclic_projective
    {V : Type uV} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (rho : Representation (ZMod p)
      (Multiplicative (ZMod p × (ZMod p × ZMod p))) V)
    (hcyc : ∀ H : Subgroup (Multiplicative (ZMod p × (ZMod p × ZMod p))),
      IsCyclic H → Module.Projective (ZMod p)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod p) H V))) :
    3 * p ≤ Module.finrank (ZMod p) V := by
  classical
  let rho₂ : Representation (F p) (Multiplicative (F p × F p)) V :=
    rho.comp ((rankTwoInclusion (p := p)))
  have hcyc₂ : ∀ H : Subgroup (Multiplicative (F p × F p)), IsCyclic H →
      Module.Projective (F p)[H] (Representation.asModule (rho₂.comp H.subtype)) :=
    pullback_cyclic_projective rho rankTwoInclusion rankTwoInclusion_injective hcyc
  have htwo : 2 * p ≤ Module.finrank (F p) V :=
    PrimeFieldCyclicProjectivityDimension.two_mul_prime_le_finrank_of_cyclic_projective
      rho₂ hcyc₂
  let s : E p := (1, (0, 0))
  have hs : s ≠ 0 := by
    intro hz
    exact one_ne_zero (congrArg (fun a : E p => a.1) hz)
  have hσ := direction_projective rho hcyc hs
  have hdim := cyclic_dimension (rho.comp (direction s)) hσ
  by_contra hbound
  change ¬ 3 * p ≤ Module.finrank (F p) V at hbound
  have hlt : Module.finrank (F p) V < 3 * p := by omega
  have hfreeRank : Module.finrank (A p) (Representation.asModule (rho.comp (direction s))) = 2 := by
    have hp := (Fact.out : p.Prime).pos
    have hlow : 2 ≤ Module.finrank (A p) (Representation.asModule (rho.comp (direction s))) := by
      nlinarith
    have hupp : Module.finrank (A p) (Representation.asModule (rho.comp (direction s))) < 3 := by
      nlinarith
    omega
  have hd : Module.finrank (F p) V = 2 * p := by
    rw [hfreeRank] at hdim
    nlinarith
  let B := blockAction rho s hσ hd
  have hBs : B (Multiplicative.ofAdd s) = (z (p := p)) • (1 : M₂ (A p)) :=
    blockAction_distinguished rho s hσ hd
  have hnorm (a : E p) (ha : a ≠ 0) :
      Module.finrank (F p)
        (LinearMap.range ((matrixOperator (p := p)) ((B (Multiplicative.ofAdd a) - 1) ^ (p - 1)))) = 2 :=
    block_norm_rank rho s hσ hd a (direction_projective rho hcyc ha)
  exact two_block_obstruction B s hs hBs hnorm

end D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldRankThreeCyclicDimension



