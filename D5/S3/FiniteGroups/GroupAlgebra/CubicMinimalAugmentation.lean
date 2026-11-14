/- GID: D5/S3/FiniteGroups/GroupAlgebra/CubicMinimalAugmentation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/CubicMinimalAugmentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Projective, mathlib/module/Mathlib.RepresentationTheory.Coinvariants, mathlib/module/Mathlib.RingTheory.Nakayama]
   utility: none
   digest: Six-dimensional actual rank-two characteristic-three representations with projective cyclic restrictions have two coinvariants and vanishing ordered cubic augmentation products. -/

import D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension
import D5.S3.FiniteGroups.GroupAlgebra.FiniteIndexProjectivity
import D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation
import D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldUniformCyclicDimension
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic

/-!
The augmentation quotient is forced to have dimension two by a regular-module
surjection and the strict kernel-dimension obstruction 3 < 6. Every nonidentity
augmentation then has the same range, forcing every ordered cubic word to vanish.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.CubicMinimalAugmentation

open scoped BigOperators MonoidAlgebra

private abbrev E := Multiplicative (Fin 2 → ZMod 3)
private abbrev A := (ZMod 3)[E]

private def augmentation : A →ₐ[ZMod 3] ZMod 3 :=
  MonoidAlgebra.lift (ZMod 3) (ZMod 3) E (1 : E →* ZMod 3)

private def augmentationIdeal : Ideal A := RingHom.ker augmentation.toRingHom

universe uV

variable {V : Type uV} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V]

private theorem elementary_card : Fintype.card E = 9 := by
  rw [Fintype.card_multiplicative, Fintype.card_pi_const, ZMod.card,
    ]
  norm_num

private theorem elementary_pow_three (g : E) : g ^ 3 = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  funext i
  exact ZModModule.char_nsmul_eq_zero 3 (g.toAdd i)

private theorem actual_order_three {g : E} (hg : g ≠ 1) : orderOf g = 3 :=
  orderOf_eq_prime (elementary_pow_three g) hg

private theorem augmentation_ideal_pow_nine : augmentationIdeal ^ 9 = ⊥ := by
  have hE : IsPGroup 3 E :=
    D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension.elementary_isPGroup 3 2
  have h :=
    D5.S3.FiniteGroups.GroupAlgebra.PGroupAugmentation.augmentation_ideal_pow_card (R := ZMod 3) 3 hE
  simpa only [Nat.card_eq_fintype_card, elementary_card, augmentationIdeal, augmentation] using h

private theorem augmentation_ideal_le_jacobson :
    augmentationIdeal ≤ (⊥ : Ideal A).jacobson := by
  intro a ha
  apply Ideal.radical_le_jacobson
  refine ⟨9, ?_⟩
  have hp := Ideal.pow_mem_pow ha 9
  simpa only [augmentation_ideal_pow_nine] using hp

/- The actual coinvariant projection kills precisely augmentation action.
   This calculation uses the existing Coinvariants quotient, not a substitute
   quotient or an extra hypothesis about the representation. -/
private theorem coinvariant_mk_asModule_smul
    (rho : Representation (ZMod 3) E V) (a : A) (x : rho.asModule) :
    Representation.Coinvariants.mk rho (rho.asModuleEquiv (a • x)) =
      augmentation a • Representation.Coinvariants.mk rho (rho.asModuleEquiv x) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [zero_smul, map_zero]
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | single g r =>
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single]
    change Representation.Coinvariants.mk rho (r • rho g (rho.asModuleEquiv x)) =
      augmentation (MonoidAlgebra.single g r) •
        Representation.Coinvariants.mk rho (rho.asModuleEquiv x)
    simp only [map_smul, Representation.Coinvariants.mk_self_apply]
    congr 1
    simp [augmentation, MonoidAlgebra.lift_single]

private theorem coinvariant_ideal_action
    (rho : Representation (ZMod 3) E V) :
    ((augmentationIdeal • (⊤ : Submodule A rho.asModule)).restrictScalars
        (ZMod 3)).map rho.asModuleEquiv.toLinearMap =
      Representation.Coinvariants.ker rho := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply (Representation.Coinvariants.mk_eq_zero rho).mp
    change x ∈ augmentationIdeal • (⊤ : Submodule A rho.asModule) at hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      change Representation.Coinvariants.mk rho (rho.asModuleEquiv (a • y)) = 0
      exact (coinvariant_mk_asModule_smul rho a y).trans (by
        rw [show augmentation a = 0 from ha, zero_smul])
    · intro x y hx hy
      simp only [map_add, hx, hy, add_zero]
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    let a : A := MonoidAlgebra.single g 1 - 1
    have ha : a ∈ augmentationIdeal := by
      change augmentation a = 0
      simp [a, augmentation, MonoidAlgebra.lift_single]
    have hact : rho.asModuleEquiv (a • rho.asModuleEquiv.symm v) =
        rho g v - v := by
      change (rho.asAlgebraHom a) v = rho g v - v
      simp only [a, map_sub, Representation.asAlgebraHom_single, one_smul,
        map_one, LinearMap.sub_apply, Module.End.one_apply]
    refine ⟨a • rho.asModuleEquiv.symm v, ?_, hact⟩
    change a • rho.asModuleEquiv.symm v ∈
      augmentationIdeal • (⊤ : Submodule A rho.asModule)
    exact Submodule.smul_mem_smul ha
      (show rho.asModuleEquiv.symm v ∈ (⊤ : Submodule A rho.asModule) from
        Submodule.mem_top)

/- This is only transport of the existing quotient by the equality just
   proved. The quotient required by Nakayama is exactly the actual V/IV. -/
private def augmentationQuotientEquivCoinvariants
    (rho : Representation (ZMod 3) E V) :
    (rho.asModule ⧸ augmentationIdeal • (⊤ : Submodule A rho.asModule)) ≃ₗ[ZMod 3]
      Representation.Coinvariants rho :=
  (Submodule.Quotient.restrictScalarsEquiv (ZMod 3)
      (augmentationIdeal • (⊤ : Submodule A rho.asModule))).symm.trans
    (Submodule.Quotient.equiv
      ((augmentationIdeal • (⊤ : Submodule A rho.asModule)).restrictScalars (ZMod 3))
      (Representation.Coinvariants.ker rho) rho.asModuleEquiv
      (coinvariant_ideal_action rho))

private theorem augmentationQuotientEquivCoinvariants_mk
    (rho : Representation (ZMod 3) E V) (x : rho.asModule) :
    augmentationQuotientEquivCoinvariants rho
        ((augmentationIdeal • (⊤ : Submodule A rho.asModule)).mkQ x) =
      Representation.Coinvariants.mk rho (rho.asModuleEquiv x) := rfl

/- Nilpotent Nakayama is applied to the actual group-algebra linear map.
   Finite generation over A follows from finite dimension over ZMod 3. -/
private theorem regular_surjective_of_coinvariant_surjective
    (rho : Representation (ZMod 3) E V)
    (f : (Representation.leftRegular (ZMod 3) E).IntertwiningMap rho)
    (hcoin : Function.Surjective
      ((Representation.Coinvariants.mk rho).comp f.toLinearMap)) :
    Function.Surjective f := by
  let r := Representation.leftRegular (ZMod 3) E
  let fA : r.asModule →ₗ[A] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule r rho f
  let J : Submodule A rho.asModule := augmentationIdeal • ⊤
  let e := augmentationQuotientEquivCoinvariants rho
  letI : Module.Finite A rho.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 3) A rho.asModule
  have hmod : Function.Surjective (J.mkQ.comp fA) := by
    intro q
    obtain ⟨a, ha⟩ := hcoin (e q)
    refine ⟨r.asModuleEquiv.symm a, e.injective ?_⟩
    change augmentationQuotientEquivCoinvariants rho
      (J.mkQ (fA (r.asModuleEquiv.symm a))) = e q
    rw [augmentationQuotientEquivCoinvariants_mk]
    exact ha
  have hfA : Function.Surjective fA :=
    LinearMap.surjective_of_surjective_comp_mkQ fA augmentationIdeal
      augmentation_ideal_le_jacobson hmod
  intro v
  obtain ⟨a, ha⟩ := hfA (rho.asModuleEquiv.symm v)
  refine ⟨r.asModuleEquiv a, ?_⟩
  exact congrArg rho.asModuleEquiv ha

private theorem operator_cube_zero
    (rho : Representation (ZMod 3) E V) (g : E) :
    (rho g - 1) ^ 3 = 0 := by
  have hpow : (rho g) ^ 3 = 1 := by
    rw [← map_pow, elementary_pow_three, map_one]
  have hpoly : ((Polynomial.X - 1 : Polynomial (ZMod 3)) ^ 3) = Polynomial.X ^ 3 - 1 := by
    simpa only [one_pow] using sub_pow_char (Polynomial.X : Polynomial (ZMod 3)) 1
  have h := congrArg (Polynomial.aeval (rho g)) hpoly
  simpa only [map_pow, map_sub, map_one, Polynomial.aeval_X, hpow, one_pow,
    sub_self] using h

private theorem cyclic_invariants_eq_ker
    (rho : Representation (ZMod 3) E V) (g : E) :
    Representation.invariants (rho.comp (Subgroup.zpowers g).subtype) =
      LinearMap.ker (rho g - 1) := by
  classical
  ext v
  constructor
  · intro hv
    change rho g v - v = 0
    exact sub_eq_zero.mpr (hv ⟨g, Subgroup.mem_zpowers g⟩)
  · intro hv
    have hfix : rho g v = v := by
      exact sub_eq_zero.mp (show rho g v - v = 0 from hv)
    have hp : ∀ n : ℕ, ((rho g) ^ n) v = v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simpa only [pow_succ', Module.End.mul_apply, ih] using hfix
    intro h
    let e := finEquivZPowers (isOfFinOrder_of_finite g)
    obtain ⟨i, rfl⟩ := e.surjective h
    change rho (g ^ (i : ℕ)) v = v
    rw [map_pow]
    exact hp i

private theorem cyclic_ker_finrank_two
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    {g : E} (hg : g ≠ 1) (hV : Module.finrank (ZMod 3) V = 6) :
    Module.finrank (ZMod 3) (LinearMap.ker (rho g - 1)) = 2 := by
  classical
  let H := Subgroup.zpowers g
  have ho : orderOf g = 3 := actual_order_three hg
  have hcard : Fintype.card H = 3 := Fintype.card_zpowers.trans ho
  have hdim :=
    D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension.finrank_eq_card_mul_invariants 3
      (IsPGroup.of_card (n := 1) (by
        rw [Nat.card_eq_fintype_card, hcard, pow_one]))
      (rho.comp H.subtype) (hproj H inferInstance)
  rw [hcard, cyclic_invariants_eq_ker rho g, hV] at hdim
  omega

private theorem coinvariant_range_le
    (rho : Representation (ZMod 3) E V) (g : E) :
    LinearMap.range (rho g - 1) ≤ Representation.Coinvariants.ker rho := by
  rintro x ⟨v, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker g v

private theorem coinvariant_finrank_le_two
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6) :
    Module.finrank (ZMod 3) (Representation.Coinvariants rho) ≤ 2 := by
  classical
  let g : E := Multiplicative.ofAdd (fun _ : Fin 2 => 1)
  have hg : g ≠ 1 := by
    intro h
    have h0 := congrArg (fun x : E => x.toAdd 0) h
    simpa [g] using h0
  have hker := cyclic_ker_finrank_two rho hproj hg hV
  have hdimrange := (rho g - 1).finrank_range_add_finrank_ker
  have hle := Submodule.finrank_mono (coinvariant_range_le rho g)
  have hdimquot := (Representation.Coinvariants.ker rho).finrank_quotient_add_finrank
  change Module.finrank (ZMod 3) (Representation.Coinvariants rho) +
    Module.finrank (ZMod 3) (Representation.Coinvariants.ker rho) =
      Module.finrank (ZMod 3) V at hdimquot
  omega

private theorem regular_surjection_of_coinvariant_rank_one
    (rho : Representation (ZMod 3) E V)
    (hcoin : Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 1) :
    ∃ f : (Representation.leftRegular (ZMod 3) E).IntertwiningMap rho,
      Function.Surjective f := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Representation.Coinvariants rho) hcoin
  obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective rho (b 0)
  let f := (Representation.leftRegularMapEquiv rho).symm v
  refine ⟨f, regular_surjective_of_coinvariant_surjective rho f ?_⟩
  intro w
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hcoin (b.ne_zero 0) w
  refine ⟨c • MonoidAlgebra.single (1 : E) 1, ?_⟩
  change Representation.Coinvariants.mk rho
    (f (c • MonoidAlgebra.single (1 : E) 1)) = w
  calc
    _ = c • Representation.Coinvariants.mk rho v := by
      simp [f, Representation.leftRegularMapEquiv_symm_single]
    _ = w := by rw [hv]; exact hc

private theorem regular_restriction_projective (H : Subgroup E) :
    Module.Projective (ZMod 3)[H]
      (Representation.asModule
        ((Representation.leftRegular (ZMod 3) E).comp H.subtype)) := by
  let r := Representation.leftRegular (ZMod 3) E
  let e : r.asModule ≃ₗ[A] A := Representation.ofMulActionSelfAsModuleEquiv
  letI : Module.Projective A r.asModule := Module.Projective.of_equiv' e.symm
  exact D5.S3.FiniteGroups.GroupAlgebra.FiniteIndexProjectivity.projective_restrict r H inferInstance

private theorem intertwining_kernel_restriction_projective
    (rho : Representation (ZMod 3) E V)
    (f : (Representation.leftRegular (ZMod 3) E).IntertwiningMap rho)
    (hf : Function.Surjective f)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V))) :
    ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          ((Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toRepresentation.comp H.subtype)) := by
  intro H hH
  let r := Representation.leftRegular (ZMod 3) E
  let rH : Representation (ZMod 3) H A := r.comp H.subtype
  let rhoH : Representation (ZMod 3) H V := rho.comp H.subtype
  let K := (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toSubmodule
  let kH : Representation (ZMod 3) H K :=
    (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toRepresentation.comp H.subtype
  let fR : rH.IntertwiningMap rhoH :=
    { toLinearMap := f.toLinearMap, isIntertwining' := fun h => f.isIntertwining' h }
  let fH : rH.asModule →ₗ[(ZMod 3)[H]] rhoH.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rH rhoH fR
  have hfH : Function.Surjective fH := by
    intro v
    obtain ⟨a, ha⟩ := hf (rhoH.asModuleEquiv v)
    refine ⟨rH.asModuleEquiv.symm a, ?_⟩
    apply rhoH.asModuleEquiv.injective
    exact ha
  letI : Module.Projective (ZMod 3)[H] rhoH.asModule := hproj H hH
  letI : Module.Projective (ZMod 3)[H] rH.asModule := regular_restriction_projective H
  obtain ⟨sH, hsH⟩ := Module.projective_lifting_property fH
    (LinearMap.id : rhoH.asModule →ₗ[(ZMod 3)[H]] rhoH.asModule) hfH
  let s : rhoH.IntertwiningMap rH :=
    (Representation.IntertwiningMap.equivLinearMapAsModule rhoH rH).symm sH
  have hsection (v : V) : f (s v) = v := by
    have h := DFunLike.congr_fun hsH (rhoH.asModuleEquiv.symm v)
    change f (s v) = v at h
    exact h
  let i : kH.IntertwiningMap rH :=
    { toLinearMap := K.subtype, isIntertwining' := fun h => by ext x; rfl }
  let p0 : A →ₗ[ZMod 3] K :=
    (LinearMap.id - s.toLinearMap.comp f.toLinearMap).codRestrict K (by
      intro a
      change f (a - s (f a)) = 0
      rw [map_sub, hsection, sub_self])
  let p : rH.IntertwiningMap kH :=
    { toLinearMap := p0
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        change rH h a - s (fR (rH h a)) = rH h (a - s (fR a))
        rw [fR.isIntertwining, s.isIntertwining, map_sub] }
  let iH : kH.asModule →ₗ[(ZMod 3)[H]] rH.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule kH rH i
  let pH : rH.asModule →ₗ[(ZMod 3)[H]] kH.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rH kH p
  apply Module.Projective.of_split iH pH
  apply LinearMap.ext
  intro x
  apply kH.asModuleEquiv.injective
  apply Subtype.ext
  change (kH.asModuleEquiv x).val - s (f (kH.asModuleEquiv x).val) =
    (kH.asModuleEquiv x).val
  rw [show f (kH.asModuleEquiv x).val = 0 from (kH.asModuleEquiv x).property,
    map_zero, sub_zero]

private theorem no_coinvariant_finrank_one
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6) :
    Module.finrank (ZMod 3) (Representation.Coinvariants rho) ≠ 1 := by
  classical
  intro hcoin
  obtain ⟨f, hf⟩ := regular_surjection_of_coinvariant_rank_one rho hcoin
  have hKproj := intertwining_kernel_restriction_projective rho f hf hproj
  let eCoeff : A ≃ₗ[ZMod 3] (E →₀ ZMod 3) :=
    MonoidAlgebra.coeffLinearEquiv (ZMod 3)
  letI : Module.Finite (ZMod 3) A :=
    Module.Finite.equiv eCoeff.symm
  let K : Representation (ZMod 3) E (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toSubmodule :=
    (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toRepresentation
  have hregdim : Module.finrank (ZMod 3) A = 9 := by
    rw [eCoeff.finrank_eq, Module.finrank_finsupp_self, elementary_card]
  have hKdim : Module.finrank (ZMod 3)
      (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toSubmodule = 3 := by
    have hrange : LinearMap.range f.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hf
    have hdim := f.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, hV, hregdim] at hdim
    change Module.finrank (ZMod 3) (LinearMap.ker f.toLinearMap) = 3
    omega
  letI : Nontrivial (Representation.IntertwiningMap.ker (Representation.leftRegular (ZMod 3) E) rho f).toSubmodule :=
    Module.nontrivial_of_finrank_pos (by rw [hKdim]; decide)
  -- The rank-two product-group endpoint has a different group carrier.
  -- This existing uniform endpoint specializes directly to the exact E,
  -- preserving every actual cyclic subgroup and the independent V universe.
  have hbound :=
    PrimeFieldUniformCyclicDimension.rank_mul_prime_le_finrank_of_cyclic_projective
      3 2 K hKproj
  rw [hKdim] at hbound
  omega

private theorem coinvariant_finrank_eq_two
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6) :
    Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 2 := by
  have hle := coinvariant_finrank_le_two rho hproj hV
  have hne := no_coinvariant_finrank_one rho hproj hV
  have hpos : 0 < Module.finrank (ZMod 3) (Representation.Coinvariants rho) := by
    by_contra h
    have hz : Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 0 := by omega
    letI : Subsingleton (Representation.Coinvariants rho) := Module.finrank_zero_iff.mp hz
    let f : (Representation.leftRegular (ZMod 3) E).IntertwiningMap rho := 0
    have hf : Function.Surjective f :=
      regular_surjective_of_coinvariant_surjective rho f (by
        intro q
        exact ⟨0, Subsingleton.elim _ _⟩)
    have hzero (v : V) : v = 0 := by
      obtain ⟨a, ha⟩ := hf v
      exact ha.symm
    letI : Subsingleton V := ⟨fun v w => (hzero v).trans (hzero w).symm⟩
    have hzV : Module.finrank (ZMod 3) V = 0 :=
      Module.finrank_zero_iff.mpr inferInstance
    omega
  omega

private theorem all_anchor_range_eq
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6)
    (hcoin : Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 2)
    {g : E} (hg : g ≠ 1) :
    Representation.Coinvariants.ker rho = LinearMap.range (rho g - 1) := by
  have hle := coinvariant_range_le rho g
  have hker := cyclic_ker_finrank_two rho hproj hg hV
  have hdimrange := (rho g - 1).finrank_range_add_finrank_ker
  have hdimquot := (Representation.Coinvariants.ker rho).finrank_quotient_add_finrank
  change Module.finrank (ZMod 3) (Representation.Coinvariants rho) +
    Module.finrank (ZMod 3) (Representation.Coinvariants.ker rho) =
      Module.finrank (ZMod 3) V at hdimquot
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private theorem ordered_operator_word_zero
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6)
    (hcoin : Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 2)
    (g l m : E) :
    (rho g - 1) * (rho l - 1) * (rho m - 1) = 0 := by
  let h : E := Multiplicative.ofAdd (fun _ : Fin 2 => 1)
  have hh : h ≠ 1 := by
    intro he
    have h0 := congrArg (fun x : E => x.toAdd 0) he
    simpa [h] using h0
  let N : Module.End (ZMod 3) V := rho h - 1
  have hcube : N ^ 3 = 0 := operator_cube_zero rho h
  have hanchor := all_anchor_range_eq rho hproj hV hcoin hh
  have hpre (t : E) (v : V) : ∃ w : V, N w = (rho t - 1) v := by
    have hv : (rho t - 1) v ∈ Representation.Coinvariants.ker rho :=
      coinvariant_range_le rho t ⟨v, rfl⟩
    rw [hanchor] at hv
    exact hv
  have hcomm (t : E) (v : V) : (rho t - 1) (N v) = N ((rho t - 1) v) := by
    have hc : Commute (rho t) (rho h) := by
      change rho t * rho h = rho h * rho t
      rw [← map_mul, ← map_mul, mul_comm]
    have hn : Commute (rho t - 1) N :=
      (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
    exact DFunLike.congr_fun hn.eq v
  ext v
  change (rho g - 1) ((rho l - 1) ((rho m - 1) v)) = 0
  obtain ⟨w, hw⟩ := hpre m v
  obtain ⟨u, hu⟩ := hpre l w
  obtain ⟨z, hz⟩ := hpre g u
  calc
    _ = (rho g - 1) ((rho l - 1) (N w)) := by rw [hw]
    _ = N ((rho g - 1) ((rho l - 1) w)) := by rw [hcomm l, hcomm g]
    _ = N ((rho g - 1) (N u)) := by rw [hu]
    _ = N (N ((rho g - 1) u)) := by rw [hcomm g]
    _ = N (N (N z)) := by rw [hz]
    _ = (N ^ 3) z := by
      simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply]
    _ = 0 := by rw [hcube]; rfl

private theorem ordered_three_list_zero
    (rho : Representation (ZMod 3) E V)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V)))
    (hV : Module.finrank (ZMod 3) V = 6)
    (hcoin : Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 2)
    (xs : List E) (hxs : xs.length = 3) :
    (xs.map (fun g => rho g - 1)).prod = 0 := by
  obtain ⟨g, l, m, rfl⟩ := List.length_eq_three.mp hxs
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc] using ordered_operator_word_zero rho hproj hV hcoin g l m

/-- In characteristic three, the exact six-dimensional actual-representation
case has two coinvariants, every actual nonidentity augmentation has the
coinvariant kernel as its range, and every ordered length-three augmentation
word vanishes. The actual-subgroup and arbitrary-representation quantifiers
are retained. -/
theorem cubic_minimal_augmentation
    {V : Type uV} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (rho : Representation (ZMod 3) E V)
    (hV : Module.finrank (ZMod 3) V = 6)
    (hproj : ∀ H : Subgroup E, IsCyclic H →
      Module.Projective (ZMod 3)[H]
        (Representation.asModule
          (rho.comp H.subtype : Representation (ZMod 3) H V))) :
    Module.finrank (ZMod 3) (Representation.Coinvariants rho) = 2 ∧
      (∀ h : E, h ≠ 1 →
        Representation.Coinvariants.ker rho = LinearMap.range (rho h - 1)) ∧
      (∀ xs : List E, xs.length = 3 →
        (xs.map (fun g => rho g - 1)).prod = 0) := by
  have hcoin := coinvariant_finrank_eq_two rho hproj hV
  refine ⟨hcoin, ?_, ?_⟩
  · intro h hh
    exact all_anchor_range_eq rho hproj hV hcoin hh
  · intro xs hxs
    exact ordered_three_list_zero rho hproj hV hcoin xs hxs

end D5.S3.FiniteGroups.GroupAlgebra.CubicMinimalAugmentation
