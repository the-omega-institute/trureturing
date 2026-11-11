/- GID: D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Intertwining, mathlib/module/Mathlib.Algebra.Module.Projective, mathlib/module/Mathlib.LinearAlgebra.Finsupp.VectorSpace]
   utility: none
   digest: A split p-nilpotent group norm gives a coinduced equivalence; projectivity is exactly projective invariants and norm-surjectivity. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupInvariants
import D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentationPrimePower
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RepresentationTheory.Intertwining

/-!
Let R be a commutative ring and P a finite, possibly nonabelian p-group.
If (p : R)^a = 0 with 0 < a, the augmentation ideal I of R[P] satisfies
I^(a * (Nat.card P - 1) + 1) = 0. The coefficient-reduction filtration
I^(k * (Nat.card P - 1) + 1) ≤ (pR[P])^k I supplies this bound, including
for a trivial group and the zero ring. The least ideal power annihilating
a supplied nonzero vector then detects a nonzero fixed vector in any module.
The private detector adapts the augmentation argument of PGroupInvariants,
using its arbitrary-semiring theorem exists_nonzero_killed_by_ideal and the
arithmetic bound of PGroupAugmentationPrimePower.

The actual orbit-sum map is injective by detection on its kernel. On its
actual quotient, detection and the explicit cocycle formula b(x) = a_x(1)
prove surjectivity. Right translation is T_g(f)(h) = f(h*g), so the formula
keeps the multiplication order for nonabelian groups. No linear complement
or coefficient-projectivity assumption is needed for the supplied-section
equivalence. For group-algebra projectivity, projectivity of the actual
invariant coefficient module is the additional obstruction over a ring.

R, P and V have independent universes. The coefficient ring may be zero,
and the module may be zero or arbitrarily generated. No field, finiteness
of the module, locality, noetherianity or nontriviality assumption is used.
Basis indices are arbitrary; only P is converted from functions to finite
support. The necessity of projective invariants and a norm section is
independent of p and its nilpotence. These are structural classical
arguments, with utility none and no claim of literature novelty.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing

open scoped MonoidAlgebra

universe uR uP uV uW uI

section Functions

variable {R : Type uR} {P : Type uP} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group P] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

-- T_g(f)(h) = f(h*g), and T_g T_a = T_(g*a), also for nonabelian P.
def rightTranslate : Representation R P (P → W) where
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
    (hf : f ∈ (rightTranslate (R := R) (P := P) (W := W)).invariants) (h : P) :
    f h = f 1 := by
  have he := congrFun ((Representation.mem_invariants _ f).mp hf h) (1 : P)
  change f (1 * h) = f 1 at he
  simpa only [one_mul] using he

private theorem free_apply_coordinate {ι : Type uI} (g : P) (z : ι →₀ R[P]) (i : ι) :
    Representation.free R P ι g z i = Representation.leftRegular R P g (z i) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single j a =>
      by_cases h : j = i
      · subst j
        simp only [Representation.finsupp_single, Finsupp.single_eq_same]
      · simp [Representation.finsupp_single, h]

-- Only P is finite. In particular no finite-support conversion is made on ι.
-- On scalar deltas this sends delta_x to the group-algebra basis element x⁻¹.
private theorem rightTranslate_free [Finite P] [Module.Free R W] :
    Module.Free R[P] (rightTranslate (R := R) (P := P) (W := W)).asModule := by
  classical
  let ι := Module.Free.ChooseBasisIndex R W
  let b : Module.Basis ι R W := Module.Free.chooseBasis R W
  let C : (P → W) ≃ₗ[R] (P → ι →₀ R) :=
    { toFun := fun f g => b.repr (f g⁻¹)
      invFun := fun a g => b.repr.symm (a g⁻¹)
      left_inv := by intro f; funext g; simp
      right_inv := by
        intro a
        funext g
        change b.repr (b.repr.symm (a (g⁻¹)⁻¹)) = a g
        rw [inv_inv, LinearEquiv.apply_symm_apply]
      map_add' := by intro f a; funext g; simp
      map_smul' := by intro c f; funext g; simp }
  let D : (P → ι →₀ R) ≃ₗ[R] (P →₀ ι →₀ R) :=
    (Finsupp.linearEquivFunOnFinite R (ι →₀ R) P).symm
  let S : (P →₀ ι →₀ R) ≃ₗ[R] (ι →₀ P →₀ R) :=
    (((Finsupp.curryLinearEquiv R).symm.trans
      (Finsupp.mapDomain.linearEquiv R R (Equiv.prodComm P ι))).trans
      (Finsupp.curryLinearEquiv R))
  have hS (z : P →₀ ι →₀ R) (i : ι) (g : P) : S z i g = z g i := by
    change (Finsupp.mapDomain (Equiv.prodComm P ι) z.uncurry) (i, g) = z g i
    calc
      _ = z.uncurry ((Equiv.prodComm P ι).symm (i, g)) :=
        Finsupp.mapDomain_equiv_apply (f := Equiv.prodComm P ι) z.uncurry (i, g)
      _ = z g i := rfl
  let E : (P → W) ≃ₗ[R] (ι →₀ R[P]) :=
    ((C.trans D).trans S).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv R).symm)
  have hE (f : P → W) (i : ι) (g : P) :
      (E f i).coeff g = b.repr (f g⁻¹) i := by
    change S (D (C f)) i g = b.repr (f g⁻¹) i
    calc
      _ = D (C f) g i := hS (D (C f)) i g
      _ = C f g i :=
        congrArg (fun a : P → ι →₀ R => a g i)
          ((Finsupp.linearEquivFunOnFinite R (ι →₀ R) P).apply_symm_apply (C f))
      _ = b.repr (f g⁻¹) i := rfl
  let T : Representation.IntertwiningMap
      (rightTranslate (R := R) (P := P) (W := W)) (Representation.free R P ι) :=
    { toLinearMap := E.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro f
        apply Finsupp.ext
        intro i
        apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro a
        change (E ((rightTranslate (R := R) (P := P) (W := W)) g f) i).coeff a =
          (Representation.free R P ι g (E f) i).coeff a
        rw [free_apply_coordinate, Representation.coeff_ofMulAction, hE, hE]
        change b.repr (f (a⁻¹ * g)) i = b.repr (f ((g⁻¹ * a)⁻¹)) i
        rw [mul_inv_rev, inv_inv] }
  let TA := Representation.IntertwiningMap.equivLinearMapAsModule _ _ T
  have hTA : Function.Bijective TA := by
    change Function.Bijective E
    exact E.bijective
  let EA := LinearEquiv.ofBijective TA hTA
  exact Module.Free.of_equiv' (Representation.free_asModule_free R P ι) EA.symm

variable [Fintype P]

def orbitSum (ρ : Representation R P V) (L : W →ₗ[R] V) :
    Representation.IntertwiningMap (rightTranslate (R := R) (P := P) (W := W)) ρ where
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

private theorem orbitSum_apply (ρ : Representation R P V) (L : W →ₗ[R] V)
    (f : P → W) : orbitSum ρ L f = ∑ g : P, ρ g (L (f g⁻¹)) := rfl

private theorem orbitSum_delta [DecidableEq P]
    (ρ : Representation R P V) (L : W →ₗ[R] V) (w : W) :
    orbitSum ρ L (Pi.single (1 : P) w) = L w := by
  classical
  rw [orbitSum_apply]
  simp [Pi.single_apply, apply_ite]

private theorem orbitSum_constant (ρ : Representation R P V) (L : W →ₗ[R] V) (w : W) :
    orbitSum ρ L (fun _ : P => w) = ρ.norm (L w) := by
  simp only [orbitSum_apply, Representation.norm, LinearMap.sum_apply]


end Functions

section Detection

variable {R : Type uR} {P : Type uP} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group P] [Finite P] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Nilpotent augmentation detects a fixed vector in any supplied nonzero
module. The least-power argument and action transport require no module
finiteness or nontriviality instance on the coefficient ring. -/
private theorem exists_nonzero_mem_invariants_of_nilpotent_prime
    (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0)
    (hP : IsPGroup p P) (σ : Representation R P V) (x : V) (hx : x ≠ 0) :
    ∃ y : V, y ≠ 0 ∧ y ∈ σ.invariants := by
  classical
  let I : Ideal (MonoidAlgebra R P) :=
    RingHom.ker (MonoidAlgebra.lift R R P (1 : P →* R)).toRingHom
  have : I.IsTwoSided := by dsimp [I]; infer_instance
  have hnil : ∃ n : ℕ, I ^ n = ⊥ := by
    refine ⟨a * (Nat.card P - 1) + 1, ?_⟩
    exact PGroupAugmentationPrimePower.augmentation_ideal_pow_pred_card
      (R := R) p a ha hp hP
  have hx' : σ.asModuleEquiv.symm x ≠ 0 := by
    intro h
    apply hx
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg σ.asModuleEquiv h
  obtain ⟨y, hy, hIy⟩ :=
    PGroupInvariants.exists_nonzero_killed_by_ideal I hnil (σ.asModuleEquiv.symm x) hx'
  refine ⟨σ.asModuleEquiv y, ?_, ?_⟩
  · intro h
    apply hy
    apply σ.asModuleEquiv.injective
    simpa only [map_zero] using h
  · apply (Representation.mem_invariants σ (σ.asModuleEquiv y)).mpr
    intro g
    have hmem : MonoidAlgebra.of R P g - 1 ∈ I := by
      change MonoidAlgebra.lift R R P (1 : P →* R) (MonoidAlgebra.of R P g - 1) = 0
      simp only [map_sub, map_one, MonoidAlgebra.lift_of, MonoidHom.one_apply, sub_self]
    have haction :
        σ.asModuleEquiv ((MonoidAlgebra.of R P g - 1) • y) =
          σ g (σ.asModuleEquiv y) - σ.asModuleEquiv y := by
      rw [Representation.asModuleEquiv_map_smul, map_sub,
        Representation.asAlgebraHom_of, map_one, LinearMap.sub_apply, Module.End.one_apply]
    have hzero : σ g (σ.asModuleEquiv y) - σ.asModuleEquiv y = 0 := by
      calc
        _ = σ.asModuleEquiv ((MonoidAlgebra.of R P g - 1) • y) := haction.symm
        _ = 0 := by rw [hIy _ hmem, map_zero]
    exact sub_eq_zero.mp hzero

-- Detection is applied to the actual kernel subrepresentation.
private theorem injective_of_invariant_kernel
    (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0)
    (hP : IsPGroup p P)
    (ρ : Representation R P V) (σ : Representation R P W)
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
      exists_nonzero_mem_invariants_of_nilpotent_prime
        (R := R) (P := P) (V := K.toSubmodule) p a ha hp hP K.toRepresentation xK hxK
    have hyV : (y : V) ∈ ρ.invariants := by
      apply (Representation.mem_invariants ρ (y : V)).mpr
      intro g
      exact (Subrepresentation.toRepresentation_apply_coe
        (ρ' := K) (g := g) (v := y) (w := y)).mp
          ((Representation.mem_invariants K.toRepresentation y).mp hyfix g)
    have hy0 : (y : V) = 0 := hf y hyV (LinearMap.mem_ker.mp y.property)
    exact hy (Subtype.ext hy0)
  exact LinearMap.ker_eq_bot.mp hker

end Detection


section SplitNorm

variable {R : Type uR} {P : Type uP} {V : Type uV}
variable [CommRing R] [Group P] [Fintype P] [AddCommGroup V] [Module R V]

/-- When (p : R)^a = 0 with 0 < a, a supplied ordinary R-linear section
of the actual norm gives an actual R-linear equivalence to right-translation
functions valued in the invariants. The invariant coefficient module need
not be projective or free. -/
theorem exists_equivariant_linearEquiv_of_norm_section
    (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0)
    (hP : IsPGroup p P) (ρ : Representation R P V)
    (L : ρ.invariants →ₗ[R] V)
    (hL : ∀ w : ρ.invariants, ρ.norm (L w) = (w : V)) :
    ∃ E : V ≃ₗ[R] (P → ρ.invariants),
      ∀ (g h : P) (v : V), E (ρ g v) h = E v (h * g) := by
  classical
  let τ := rightTranslate (R := R) (P := P) (W := ρ.invariants)
  let Φ : Representation.IntertwiningMap τ ρ := orbitSum ρ L
  have hΦconstant (w : ρ.invariants) : Φ (fun _ : P => w) = (w : V) := by
    exact (orbitSum_constant ρ L w).trans (hL w)
  have hΦinj : Function.Injective Φ := by
    apply injective_of_invariant_kernel p a ha hp hP τ ρ Φ
    intro f hf hf0
    have hc : f = fun _ : P => f 1 :=
      funext fun h => invariant_function_constant f hf h
    have hwV : (f 1 : V) = 0 :=
      (hΦconstant (f 1)).symm.trans ((congrArg Φ hc).symm.trans hf0)
    have hw : f 1 = 0 := Subtype.ext hwV
    funext h
    change f h = 0
    rw [invariant_function_constant f hf h, hw]
  -- U is the actual range subrepresentation, and σ is its actual quotient.
  let U : Subrepresentation ρ := Φ.range
  let Q := V ⧸ U.toSubmodule
  let σ : Representation R P Q := U.quotient
  let π : V →ₗ[R] Q := U.toSubmodule.mkQ
  have hU (v : V) : v ∈ U.toSubmodule ↔ ∃ f, Φ f = v :=
    Representation.IntertwiningMap.mem_range τ ρ Φ v
  have hπ (g : P) (v : V) : σ g (π v) = π (ρ g v) := by
    change U.quotient g (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk (ρ g v) : Q)
    exact Subrepresentation.quotient_apply_mk U g v
  have hπzero (v : V) : π v = 0 ↔ v ∈ U.toSubmodule := by
    change (Submodule.Quotient.mk v : V ⧸ U.toSubmodule) = 0 ↔ v ∈ U.toSubmodule
    exact Submodule.Quotient.mk_eq_zero U.toSubmodule
  have hΦsurj : Function.Surjective Φ := by
    intro v
    by_contra hv
    have hvU : v ∉ U.toSubmodule := by
      intro h
      exact hv ((hU v).mp h)
    have hvQ : π v ≠ 0 := fun h => hvU ((hπzero v).mp h)
    obtain ⟨c, hc0, hcfix⟩ :=
      exists_nonzero_mem_invariants_of_nilpotent_prime
        (R := R) (P := P) (V := Q) p a ha hp hP σ (π v) hvQ
    obtain ⟨m, hm⟩ := U.toSubmodule.mkQ_surjective c
    have hdiff (g : P) : ρ g m - m ∈ U.toSubmodule := by
      apply (hπzero _).mp
      have hm' : π m = c := hm
      have hfixedm : σ g (π m) = π m := by
        simpa only [hm'] using (Representation.mem_invariants σ c).mp hcfix g
      calc
        π (ρ g m - m) = π (ρ g m) - π m := map_sub π _ _
        _ = σ g (π m) - π m :=
          congrArg (fun z : Q => z - π m) (hπ g m).symm
        _ = 0 := sub_eq_zero.mpr hfixedm
    -- Each difference has a unique preimage, by injectivity of Φ.
    have hpre (g : P) : ∃ f : P → ρ.invariants, Φ f = ρ g m - m :=
      (hU _).mp (hdiff g)
    choose a ha using hpre
    have hcross (g h : P) : a (g * h) = a g + τ g (a h) := by
      apply hΦinj
      calc
        Φ (a (g * h)) = ρ (g * h) m - m := ha (g * h)
        _ = ρ g (ρ h m) - m := by rw [map_mul, Module.End.mul_apply]
        _ = (ρ g m - m) + ρ g (ρ h m - m) := by
          rw [map_sub, add_comm (ρ g m - m), sub_add_sub_cancel]
        _ = Φ (a g) + ρ g (Φ (a h)) :=
          congrArg₂ (fun x y : V => x + y) (ha g).symm (congrArg (ρ g) (ha h).symm)
        _ = Φ (a g + τ g (a h)) := by
          rw [map_add, Representation.IntertwiningMap.isIntertwining τ ρ Φ g (a h)]
    -- Explicit H1 elimination: b(x)=a_x(1), so a_g(x)=b(x*g)-b(x).
    let b : P → ρ.invariants := fun x => a x 1
    have hb (g x : P) : a g x = b (x * g) - b x := by
      have hc := congrFun (hcross x g) (1 : P)
      change a (x * g) 1 = a x 1 + a g (1 * x) at hc
      rw [one_mul] at hc
      change a g x = a (x * g) 1 - a x 1
      apply eq_sub_iff_add_eq.mpr
      rw [add_comm]
      exact hc.symm
    have hcoboundary (g : P) : a g = τ g b - b := by
      funext x
      exact hb g x
    have hmfix : m - Φ b ∈ ρ.invariants := by
      apply (Representation.mem_invariants ρ _).mpr
      intro g
      have hd : ρ g m - m = Φ (τ g b) - Φ b := by
        calc
          ρ g m - m = Φ (a g) := (ha g).symm
          _ = Φ (τ g b - b) := congrArg Φ (hcoboundary g)
          _ = Φ (τ g b) - Φ b := map_sub Φ.toLinearMap _ _
      calc
        ρ g (m - Φ b) = ρ g m - Φ (τ g b) := by
          rw [map_sub, ← Representation.IntertwiningMap.isIntertwining τ ρ Φ g b]
        _ = m - Φ b := sub_eq_sub_iff_sub_eq_sub.mp hd
    let w : ρ.invariants := ⟨m - Φ b, hmfix⟩
    have hmU : m ∈ U.toSubmodule := by
      have hwU : m - Φ b ∈ U.toSubmodule := by
        exact (hU _).mpr ⟨fun _ : P => w, hΦconstant w⟩
      have hbU : Φ b ∈ U.toSubmodule := (hU _).mpr ⟨b, rfl⟩
      have hadd := U.toSubmodule.add_mem hwU hbU
      simpa only [sub_add_cancel] using hadd
    have hc : c = 0 := hm.symm.trans ((hπzero m).mpr hmU)
    exact hc0 hc
  let F : (P → ρ.invariants) ≃ₗ[R] V :=
    LinearEquiv.ofBijective Φ.toLinearMap ⟨hΦinj, hΦsurj⟩
  have hF (g : P) (f : P → ρ.invariants) : F (τ g f) = ρ g (F f) :=
    Representation.IntertwiningMap.isIntertwining τ ρ Φ g f
  refine ⟨F.symm, ?_⟩
  intro g h v
  have heq : F.symm (ρ g v) = τ g (F.symm v) := by
    apply F.injective
    calc
      F (F.symm (ρ g v)) = ρ g v := F.apply_symm_apply _
      _ = ρ g (F (F.symm v)) := congrArg (ρ g) (F.apply_symm_apply v).symm
      _ = F (τ g (F.symm v)) := (hF g (F.symm v)).symm
  exact congrFun heq h

end SplitNorm

section ProjectivityTransport

variable {R : Type uR} {P : Type uP} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group P] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

-- An ordinary coefficient map gives an actual equivariant pointwise map.
private def pointwise (f : W →ₗ[R] V) :
    Representation.IntertwiningMap
      (rightTranslate (R := R) (P := P) (W := W))
      (rightTranslate (R := R) (P := P) (W := V)) where
  toLinearMap :=
    { toFun := fun a g => f (a g)
      map_add' := by intro a b; funext g; exact f.map_add _ _
      map_smul' := by intro r a; funext g; exact f.map_smul r (a g) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    funext h
    rfl

-- Projective W is a retract of the free coefficient module W →₀ R.
-- Pointwise transport makes functions into W a retract of a free R[P]-module.
private theorem rightTranslate_projective [Finite P] [Module.Projective R W] :
    Module.Projective R[P] (rightTranslate (R := R) (P := P) (W := W)).asModule := by
  classical
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := R) (P := W)).mp inferInstance
  let r : (W →₀ R) →ₗ[R] W := Finsupp.linearCombination R (fun w : W => w)
  let τ := rightTranslate (R := R) (P := P) (W := W)
  let υ := rightTranslate (R := R) (P := P) (W := W →₀ R)
  let I : Representation.IntertwiningMap τ υ := pointwise i
  let S : Representation.IntertwiningMap υ τ := pointwise r
  let IA := Representation.IntertwiningMap.equivLinearMapAsModule τ υ I
  let SA := Representation.IntertwiningMap.equivLinearMapAsModule υ τ S
  let : Module.Free R (W →₀ R) := inferInstance
  let : Module.Free R[P] υ.asModule := rightTranslate_free
  apply Module.Projective.of_split IA SA
  apply LinearMap.ext
  intro a
  apply τ.asModuleEquiv.injective
  change (fun g : P => r (i (τ.asModuleEquiv a g))) = τ.asModuleEquiv a
  funext g
  exact LinearMap.congr_fun hi (τ.asModuleEquiv a g)

-- Restriction of scalars is justified by an actual free coefficient module
-- and restricted split maps, rather than an assumed preservation instance.
theorem coefficient_projective_of_projective (ρ : Representation R P V)
    [Module.Projective R[P] ρ.asModule] : Module.Projective R V := by
  classical
  obtain ⟨i, hi⟩ :=
    (Module.projective_def' (R := R[P]) (P := ρ.asModule)).mp inferInstance
  let A := ρ.asModule →₀ R[P]
  let r : A →ₗ[R[P]] ρ.asModule :=
    Finsupp.linearCombination R[P] (fun v : ρ.asModule => v)
  let : Module.Free R R[P] := Module.Free.of_basis (MonoidAlgebra.basis P R)
  let : Module.Free R A := inferInstance
  -- Restrict the split maps along R → R[P] with compatible scalar actions.
  letI : IsScalarTower R R[P] ρ.asModule := inferInstance
  letI : IsScalarTower R R[P] A := inferInstance
  letI : LinearMap.CompatibleSMul ρ.asModule A R R[P] :=
    LinearMap.IsScalarTower.compatibleSMul (M := ρ.asModule) (M₂ := A) (R := R) (S := R[P])
  letI : LinearMap.CompatibleSMul A ρ.asModule R R[P] :=
    LinearMap.IsScalarTower.compatibleSMul (M := A) (M₂ := ρ.asModule) (R := R) (S := R[P])
  have hproj : Module.Projective R ρ.asModule := by
    apply Module.Projective.of_split (i.restrictScalars R) (r.restrictScalars R)
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun hi v
  let : Module.Projective R ρ.asModule := hproj
  exact Module.Projective.of_equiv' ρ.asModuleEquiv

variable [Fintype P]

-- The codomain is the actual invariant submodule, and the underlying map is
-- the actual, unnormalised Representation.norm.
private def normToInvariants (ρ : Representation R P V) : V →ₗ[R] ρ.invariants where
  toFun v := ⟨ρ.norm v, (Representation.mem_invariants ρ _).mpr
    (fun g => Representation.self_norm_apply ρ g v)⟩
  map_add' x y := Subtype.ext (ρ.norm.map_add x y)
  map_smul' r x := Subtype.ext (ρ.norm.map_smul r x)

-- The orbit-cover section is shared by the invariant norm argument below
-- and the unrestricted endomorphism conjugation-trace criterion.
-- Only the finite group, not p-nilpotence or module finiteness, is needed.
theorem orbit_section_of_projective (ρ : Representation R P V)
    [Module.Projective R[P] ρ.asModule] :
    ∃ S : Representation.IntertwiningMap ρ
        (rightTranslate (R := R) (P := P) (W := V)),
      ∀ v : V, orbitSum ρ (LinearMap.id : V →ₗ[R] V) (S v) = v := by
  classical
  let τ := rightTranslate (R := R) (P := P) (W := V)
  let q := orbitSum ρ (LinearMap.id : V →ₗ[R] V)
  let qA := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ q
  have hq : Function.Surjective qA := by
    intro y
    refine ⟨τ.asModuleEquiv.symm (Pi.single (1 : P) (ρ.asModuleEquiv y)), ?_⟩
    apply ρ.asModuleEquiv.injective
    exact orbitSum_delta ρ (LinearMap.id : V →ₗ[R] V) (ρ.asModuleEquiv y)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qA
    (LinearMap.id : ρ.asModule →ₗ[R[P]] ρ.asModule) hq
  let S : Representation.IntertwiningMap ρ τ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ).symm s
  have hqS (v : V) : q (S v) = v := by
    have hv := congrArg ρ.asModuleEquiv
      (LinearMap.congr_fun hs (ρ.asModuleEquiv.symm v))
    exact hv
  exact ⟨S, hqS⟩

-- Projectivity over the group algebra splits the actual orbit-cover map.
-- Evaluating the equivariant section at 1 gives an ordinary R-linear norm section.
-- This statement itself needs no p-group or characteristic hypothesis.
private theorem norm_section_of_projective (ρ : Representation R P V)
    [Module.Projective R[P] ρ.asModule] :
    ∃ L : ρ.invariants →ₗ[R] V,
      ∀ w : ρ.invariants, ρ.norm (L w) = (w : V) := by
  classical
  let τ := rightTranslate (R := R) (P := P) (W := V)
  let q := orbitSum ρ (LinearMap.id : V →ₗ[R] V)
  obtain ⟨S, hqS⟩ := orbit_section_of_projective ρ
  let L : ρ.invariants →ₗ[R] V :=
    { toFun := fun w => S (w : V) 1
      map_add' := by
        intro w z
        change S ((w : V) + (z : V)) 1 = S (w : V) 1 + S (z : V) 1
        exact congrFun (map_add S (w : V) (z : V)) (1 : P)
      map_smul' := by
        intro r w
        change S (r • (w : V)) 1 = r • S (w : V) 1
        exact congrFun (map_smul S r (w : V)) (1 : P) }
  refine ⟨L, ?_⟩
  intro w
  let u : P → V := S (w : V)
  have hufix : u ∈ τ.invariants := by
    apply (Representation.mem_invariants τ u).mpr
    intro g
    change τ g (S (w : V)) = S (w : V)
    rw [← Representation.IntertwiningMap.isIntertwining ρ τ S g (w : V),
      (Representation.mem_invariants ρ (w : V)).mp w.property g]
  have hconst : u = fun _ : P => u 1 :=
    funext fun h => invariant_function_constant u hufix h
  change ρ.norm (u 1) = (w : V)
  calc
    ρ.norm (u 1) = q (fun _ : P => u 1) :=
      (orbitSum_constant ρ (LinearMap.id : V →ₗ[R] V) (u 1)).symm
    _ = q u := congrArg q hconst.symm
    _ = (w : V) := hqS (w : V)

end ProjectivityTransport

section Criterion

variable {R : Type uR} {P : Type uP} {V : Type uV}
variable [CommRing R] [Group P] [Fintype P] [AddCommGroup V] [Module R V]

/-- Over any commutative ring with (p : R)^a = 0 and 0 < a, a representation
of any finite possibly nonabelian p-group on any R-module is projective over R[P]
iff its invariant coefficient module is R-projective and the actual norm
surjects onto that submodule. No projectivity hypothesis on V is assumed. -/
theorem projective_iff_projective_invariants_and_norm_surjective
    (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0)
    (hP : IsPGroup p P) (ρ : Representation R P V) :
    Module.Projective R[P] ρ.asModule ↔
      Module.Projective R ρ.invariants ∧
        ∀ w : ρ.invariants, ∃ x : V, ρ.norm x = (w : V) := by
  classical
  constructor
  · intro hproj
    let : Module.Projective R[P] ρ.asModule := hproj
    let : Module.Projective R V := coefficient_projective_of_projective ρ
    obtain ⟨L, hL⟩ := norm_section_of_projective ρ
    have hsplit : (normToInvariants ρ).comp L = LinearMap.id := by
      apply LinearMap.ext
      intro w
      exact Subtype.ext (hL w)
    exact ⟨Module.Projective.of_split L (normToInvariants ρ) hsplit,
      fun w => ⟨L w, hL w⟩⟩
  · rintro ⟨hW, hN⟩
    let : Module.Projective R ρ.invariants := hW
    have hNsurj : Function.Surjective (normToInvariants ρ) := by
      intro w
      obtain ⟨v, hv⟩ := hN w
      exact ⟨v, Subtype.ext hv⟩
    obtain ⟨L, hL⟩ := Module.projective_lifting_property (normToInvariants ρ)
      (LinearMap.id : ρ.invariants →ₗ[R] ρ.invariants) hNsurj
    have hsection (w : ρ.invariants) : ρ.norm (L w) = (w : V) :=
      congrArg (fun z : ρ.invariants => (z : V)) (LinearMap.congr_fun hL w)
    obtain ⟨E, hE⟩ := exists_equivariant_linearEquiv_of_norm_section p a ha hp hP ρ L hsection
    let τ := rightTranslate (R := R) (P := P) (W := ρ.invariants)
    let T : Representation.IntertwiningMap ρ τ :=
      { toLinearMap := E.toLinearMap
        isIntertwining' g := by
          apply LinearMap.ext
          intro v
          funext h
          exact hE g h v }
    let TA := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ T
    have hTA : Function.Bijective TA := by
      change Function.Bijective E
      exact E.bijective
    let EA := LinearEquiv.ofBijective TA hTA
    let : Module.Projective R[P] τ.asModule := rightTranslate_projective
    exact Module.Projective.of_equiv' EA.symm

end Criterion

end D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
