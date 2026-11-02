/- GID: D5/S3/FiniteGroups/RelativeFrattiniKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/RelativeFrattiniKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.QuotientGroup.Basic]
   utility: none
   digest: Relative Frattini automorphism and outer-automorphism kernels for a normal p-subgroup. -/

import D5.S3.FiniteGroups.FrattiniAutomorphismKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The displacement construction adapts the characteristic-subgroup argument of
Qiuzhen-CFSG/CFSG, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7,
Theory/GroupTheory/CentralCharacteristicAutomorphisms.lean, to the group of
automorphisms preserving a specified subgroup. Apache-2.0; upstream license:
docs/reports/licenses/cfsg-frattini-kernel-LICENSE.txt.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.RelativeFrattiniKernel
open Subgroup
variable {Q : Type*} [Group Q]

/-- All automorphisms preserving the specified subgroup, without a global
characteristic-subgroup assumption. -/
def preservingAut (P : Subgroup Q) : Subgroup (MulAut Q) where
  carrier := {a | ∀ x, x ∈ P ↔ a x ∈ P}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    exact (hb x).trans (ha (b x))
  inv_mem' := by
    intro a ha x
    simpa using (ha (a.symm x)).symm

/-- Restriction to the preserved subgroup. -/
def restriction (P : Subgroup Q) : preservingAut P →* MulAut P where
  toFun a :=
    { toFun x := ⟨a.val x, (a.property x).mp x.property⟩
      invFun x := ⟨a.val.symm x, (by apply (a.property (a.val.symm x)).mpr; simpa using x.property)⟩
      left_inv x := by apply Subtype.ext; exact a.val.left_inv x
      right_inv x := by apply Subtype.ext; exact a.val.right_inv x
      map_mul' x y := by apply Subtype.ext; exact a.val.map_mul x y }
  map_one' := by apply MulEquiv.ext; intro x; rfl
  map_mul' a b := by apply MulEquiv.ext; intro x; rfl

/-- The Frattini subgroup of P viewed inside Q. -/
def relativeFrattini (P : Subgroup Q) : Subgroup Q := (frattini P).map P.subtype

instance relativeFrattini_normal (P : Subgroup Q) [P.Normal] :
    (relativeFrattini P).Normal := ConjAct.normal_of_characteristic_of_normal

private theorem preserves_frattini (P : Subgroup Q) (a : preservingAut P) :
    (relativeFrattini P).map a.val.toMonoidHom = relativeFrattini P := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨restriction P a z,
      (characteristic_iff_map_le.mp inferInstance (restriction P a))
        (mem_map_of_mem _ hz), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨((restriction P a).symm z : P), ?_, ?_⟩
    · exact ⟨(restriction P a).symm z,
        (characteristic_iff_map_le.mp inferInstance (restriction P a).symm)
          (mem_map_of_mem _ hz), rfl⟩
    · exact congrArg Subtype.val ((restriction P a).apply_symm_apply z)

/-- The actual induced action on Q/Frattini(P). -/
def quotientAction (P : Subgroup Q) [P.Normal] :
    preservingAut P →* MulAut (Q ⧸ relativeFrattini P) where
  toFun a := QuotientGroup.congr _ _ a.val (preserves_frattini P a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl

private theorem displacement_mem (P : Subgroup Q) [P.Normal]
    (a : (quotientAction P).ker) (x : Q) :
    x⁻¹ * a.val.val x ∈ relativeFrattini P := by
  have h := DFunLike.congr_fun a.property (QuotientGroup.mk' (relativeFrattini P) x)
  exact QuotientGroup.eq.mp h.symm

/-- Every P-preserving automorphism acting trivially on Q/Frattini(P)
belongs to a p-group, for an arbitrary normal finite p-subgroup P. -/
theorem isPGroup_automorphism_kernel [Finite Q] (P : Subgroup Q) [P.Normal]
    {p : ℕ} (hP : IsPGroup p P) : IsPGroup p (quotientAction P).ker := by
  let B := (quotientAction P).ker
  let r : B →* MulAut P := (restriction P).comp B.subtype
  have hfix (a : r.ker) (x : P) : a.val.val.val x = x := by
    exact congrArg Subtype.val (DFunLike.congr_fun a.property x)
  have hdisp (a : B) (x : Q) : x⁻¹ * a.val.val x ∈ P := by
    obtain ⟨z, _, hz⟩ := displacement_mem P a x
    exact hz ▸ z.property
  let d : r.ker →* (Q → P) :=
    { toFun a x := ⟨x⁻¹ * a.val.val.val x, hdisp a.val x⟩
      map_one' := by funext x; apply Subtype.ext; simp
      map_mul' a b := by
        funext x
        apply Subtype.ext
        change x⁻¹ * a.val.val.val (b.val.val.val x) =
          (x⁻¹ * a.val.val.val x) * (x⁻¹ * b.val.val.val x)
        have hf := hfix a ⟨x⁻¹ * b.val.val.val x, hdisp b.val x⟩
        change a.val.val.val (x⁻¹ * b.val.val.val x) = x⁻¹ * b.val.val.val x at hf
        rw [map_mul, map_inv] at hf
        calc
          _ = x⁻¹ * (a.val.val.val x * (a.val.val.val x)⁻¹ *
              a.val.val.val (b.val.val.val x)) := by simp
          _ = _ := by rw [mul_assoc (a.val.val.val x), hf, mul_assoc] }
  have hd : Function.Injective d := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact mul_left_cancel (congrArg Subtype.val (congrFun hab x))
  have hfunc : IsPGroup p (Q → P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_dvd_pow
    intro f
    refine ⟨k, ?_⟩
    funext x
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (f x)).trans hk)
  have hk : IsPGroup p r.ker := hfunc.of_injective d hd
  have hr : ∀ a : B, r a ∈
      (FrattiniAutomorphismKernel.quotientAut (frattini P)).ker := by
    intro a
    apply MulEquiv.ext
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      symm
      apply (QuotientGroup.eq).mpr
      obtain ⟨z, hz, he⟩ := displacement_mem P a y
      have he' : z = y⁻¹ * r a y := Subtype.ext he
      exact he' ▸ hz
  have ht := IsPGroup.comap_of_ker_isPGroup
    (FrattiniAutomorphismKernel.isPGroup_quotientAut_frattini_kernel hP) r hk
  have he : (FrattiniAutomorphismKernel.quotientAut (frattini P)).ker.comap r = ⊤ := by
    ext a
    exact iff_of_true (hr a) (mem_top a)
  rw [he] at ht
  exact ht.of_surjective (⊤ : Subgroup B).subtype (fun a => ⟨⟨a, mem_top a⟩, rfl⟩)

/-- The subgroup of actual inner automorphisms. -/
def innerAut (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

instance innerAut_normal (G : Type*) [Group G] : (innerAut G).Normal where
  conj_mem := by
    rintro a ⟨g, rfl⟩ b
    refine ⟨b g, ?_⟩
    apply MulEquiv.ext
    intro x
    simp [MulAut.conj_apply, mul_assoc]

/-- The usual outer automorphism group. -/
abbrev OuterAut (G : Type*) [Group G] := MulAut G ⧸ innerAut G

/-- Inner automorphisms inside the group preserving P. -/
def relativeInner (P : Subgroup Q) : Subgroup (preservingAut P) :=
  (innerAut Q).comap (preservingAut P).subtype

instance relativeInner_normal (P : Subgroup Q) : (relativeInner P).Normal :=
  inferInstanceAs ((innerAut Q).comap (preservingAut P).subtype).Normal

/-- The actual P-preserving outer automorphism group A/Inn(Q).
Normality of P ensures that every inner automorphism is in A. -/
abbrev RelativeOuter (P : Subgroup Q) [P.Normal] := preservingAut P ⧸ relativeInner P

/-- Conjugation by an element of Q, as a P-preserving automorphism. -/
def innerLift (P : Subgroup Q) [P.Normal] : Q →* preservingAut P :=
  (MulAut.conj : Q →* MulAut Q).codRestrict (preservingAut P) (by
    intro q x
    constructor
    · intro hx; exact (inferInstance : P.Normal).conj_mem x hx q
    · intro hx
      have hh := (inferInstance : P.Normal).conj_mem _ hx q⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using hh)

private theorem quotientAction_inner (P : Subgroup Q) [P.Normal] (q : Q) :
    quotientAction P (innerLift P q) =
      MulAut.conj (QuotientGroup.mk' (relativeFrattini P) q) := by
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | h x => rfl

/-- The actual induced homomorphism from P-preserving outer automorphisms
to the outer automorphisms of Q/Frattini(P). -/
def outerAction (P : Subgroup Q) [P.Normal] :
    RelativeOuter P →* OuterAut (Q ⧸ relativeFrattini P) :=
  QuotientGroup.lift (relativeInner P)
    ((QuotientGroup.mk' (innerAut (Q ⧸ relativeFrattini P))).comp (quotientAction P)) (by
      rintro a ⟨q, hq⟩
      have ha : a = innerLift P q := Subtype.ext hq.symm
      rw [ha, MonoidHom.mem_ker, MonoidHom.comp_apply, quotientAction_inner]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨QuotientGroup.mk' (relativeFrattini P) q, rfl⟩)

/-- For every subgroup of the actual P-preserving outer automorphism group,
the kernel of its induced action on Out(Q/Frattini(P)) is a p-group. -/
theorem isPGroup_outer_kernel [Finite Q] (P : Subgroup Q) [P.Normal]
    {p : ℕ} (hP : IsPGroup p P) (H : Subgroup (RelativeOuter P)) :
    IsPGroup p ((outerAction P).comp H.subtype).ker := by
  let pi := QuotientGroup.mk' (relativeInner P)
  have hk : (outerAction P).ker ≤ ((quotientAction P).ker).map pi := by
    intro z
    induction z using Quotient.inductionOn with
    | h a =>
      intro ha
      change QuotientGroup.mk' (innerAut (Q ⧸ relativeFrattini P))
        (quotientAction P a) = 1 at ha
      obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp ha
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (relativeFrattini P) y
      let b := a * (innerLift P q)⁻¹
      have hb : b ∈ (quotientAction P).ker := by
        change quotientAction P (a * (innerLift P q)⁻¹) = 1
        rw [map_mul, map_inv, quotientAction_inner, hy]
        exact mul_inv_cancel _
      refine ⟨b, hb, ?_⟩
      have hi : pi (innerLift P q) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨q, rfl⟩
      change pi (a * (innerLift P q)⁻¹) = pi a
      simp only [map_mul, map_inv, hi, inv_one, mul_one]
  have hpker := ((isPGroup_automorphism_kernel P hP).map pi).to_le hk
  exact hpker.comap_subtype

end D5.S3.FiniteGroups.RelativeFrattiniKernel
