/- GID: D5/S3/FiniteGroups/PowerInvariantRefinement
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/PowerInvariantRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict abelianity refinement of simultaneous power equivalence on all finite groups. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The first disjunct of Problem 6.2 of Fernandes, Qureshi, Reis and Ribas,
On a class of combinatorial group invariants, arXiv:2609.20516v1.
Definition 1.5 and Remark 1.6 require one bijection for all integer powers.
The common refinement and alternating bilinear central extensions are classical
ingredients; no priority claim is made. See the linked Blueprint and literature note.
-/

namespace D5.S3.FiniteGroups.PowerInvariantRefinement.Witness
abbrev F := ZMod 3
@[ext] structure T (u v : F) where
  a : F
  b : F
  c : F
  d : F
  z : F
  deriving DecidableEq, Fintype

instance mulInst (u v : F) : Mul (T u v) where
  mul x y := ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d,
    x.z+y.z+u*(x.a*y.b-x.b*y.a)+v*(x.c*y.d-x.d*y.c)⟩
instance oneInst (u v : F) : One (T u v) := ⟨⟨0,0,0,0,0⟩⟩
instance invInst (u v : F) : Inv (T u v) := ⟨fun x => ⟨-x.a,-x.b,-x.c,-x.d,-x.z⟩⟩

@[simp] private theorem mul_a (u v : F) (x y : T u v) : (x*y).a=x.a+y.a := rfl
@[simp] private theorem mul_b (u v : F) (x y : T u v) : (x*y).b=x.b+y.b := rfl
@[simp] private theorem mul_c (u v : F) (x y : T u v) : (x*y).c=x.c+y.c := rfl
@[simp] private theorem mul_d (u v : F) (x y : T u v) : (x*y).d=x.d+y.d := rfl
@[simp] private theorem mul_z (u v : F) (x y : T u v) :
    (x*y).z=x.z+y.z+u*(x.a*y.b-x.b*y.a)+v*(x.c*y.d-x.d*y.c) := rfl
@[simp] private theorem one_a (u v : F) : (1 : T u v).a=0 := rfl
@[simp] private theorem one_b (u v : F) : (1 : T u v).b=0 := rfl
@[simp] private theorem one_c (u v : F) : (1 : T u v).c=0 := rfl
@[simp] private theorem one_d (u v : F) : (1 : T u v).d=0 := rfl
@[simp] private theorem one_z (u v : F) : (1 : T u v).z=0 := rfl
@[simp] private theorem inv_a (u v : F) (x : T u v) : (x⁻¹).a = -x.a := rfl
@[simp] private theorem inv_b (u v : F) (x : T u v) : (x⁻¹).b = -x.b := rfl
@[simp] private theorem inv_c (u v : F) (x : T u v) : (x⁻¹).c = -x.c := rfl
@[simp] private theorem inv_d (u v : F) (x : T u v) : (x⁻¹).d = -x.d := rfl
@[simp] private theorem inv_z (u v : F) (x : T u v) : (x⁻¹).z = -x.z := rfl

instance groupInst (u v : F) : Group (T u v) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc x y w := by apply T.ext <;> simp only [mul_a,mul_b,mul_c,mul_d,mul_z] <;> ring
  one_mul x := by
    apply T.ext <;>
      simp only [mul_a,mul_b,mul_c,mul_d,mul_z,one_a,one_b,one_c,one_d,one_z] <;> ring
  mul_one x := by
    apply T.ext <;>
      simp only [mul_a,mul_b,mul_c,mul_d,mul_z,one_a,one_b,one_c,one_d,one_z] <;> ring
  inv_mul_cancel x := by
    apply T.ext <;>
      simp only [mul_a,mul_b,mul_c,mul_d,mul_z,one_a,one_b,one_c,one_d,one_z,
        inv_a,inv_b,inv_c,inv_d,inv_z] <;> ring

@[simp] private theorem pow_coords (u v : F) (x : T u v) (n : ℕ) :
    x ^ n = ⟨(n:F)*x.a,(n:F)*x.b,(n:F)*x.c,(n:F)*x.d,(n:F)*x.z⟩ := by
  induction n with
  | zero => apply T.ext <;> simp [pow_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    apply T.ext <;>
      simp only [mul_a,mul_b,mul_c,mul_d,mul_z, Nat.cast_add, Nat.cast_one] <;> ring

def recoord (u v s t : F) : T u v ≃ T s t where
  toFun x := ⟨x.a,x.b,x.c,x.d,x.z⟩
  invFun x := ⟨x.a,x.b,x.c,x.d,x.z⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem recoord_pow (u v s t : F) (x : T u v) (n : ℕ) :
    recoord u v s t (x^n) = (recoord u v s t x)^n := by
  simp only [pow_coords]; rfl

private theorem recoord_inv (u v s t : F) (x : T u v) :
    recoord u v s t x⁻¹ = (recoord u v s t x)⁻¹ := rfl

private theorem recoord_zpow (u v s t : F) (x : T u v) (n : ℤ) :
    recoord u v s t (x^n) = (recoord u v s t x)^n := by
  cases n with
  | ofNat n => simpa only [zpow_natCast, Int.ofNat_eq_natCast] using recoord_pow u v s t x n
  | negSucc n => simp only [zpow_negSucc, recoord_inv, recoord_pow]

def PowerEquivalent (G H : Type) [Group G] [Group H] : Prop :=
  ∃ f : G ≃ H, ∀ (g : G) (n : ℤ), f (g^n) = (f g)^n

def Abelian (G : Type) [Group G] : Prop := ∀ x y : G, x*y=y*x

def Refined (G H : Type) [Group G] [Group H] : Prop :=
  PowerEquivalent G H ∧ (Abelian G ↔ Abelian H)

private theorem all_power_equivalent (u v s t : F) : PowerEquivalent (T u v) (T s t) :=
  ⟨recoord u v s t, recoord_zpow u v s t⟩

private theorem zero_abelian : Abelian (T 0 0) := by
  intro x y; apply T.ext <;> simp only [mul_a,mul_b,mul_c,mul_d,mul_z] <;> ring

private theorem first_nonabelian (v : F) : ¬ Abelian (T 1 v) := by
  intro h
  have hz := congrArg T.z (h ⟨1,0,0,0,0⟩ ⟨0,1,0,0,0⟩)
  norm_num only [mul_z, mul_one, mul_zero, sub_zero, zero_sub, zero_add,
    add_zero, one_mul, zero_mul] at hz
  exact (by decide : (1:F) ≠ -1) hz

-- These exact predicates use the actual group multiplication, with no numeric proxy.
private theorem center_first (x : T 1 0) :
    x ∈ Subgroup.center (T 1 0) ↔ x.a=0 ∧ x.b=0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h₁ := congrArg T.z (h ⟨0,1,0,0,0⟩)
    have h₂ := congrArg T.z (h ⟨1,0,0,0,0⟩)
    simp only [mul_z] at h₁ h₂
    constructor
    · simp only [mul_one, mul_zero, sub_zero, zero_sub, zero_add, add_zero, one_mul, zero_mul] at h₁
      have he : (2:F)*x.a=0 := by linear_combination -h₁
      exact (mul_eq_zero.mp he).resolve_left (by decide)
    · simp only [mul_one, mul_zero, sub_zero, zero_sub, zero_add, add_zero, one_mul, zero_mul] at h₂
      have he : (2:F)*x.b=0 := by linear_combination h₂
      exact (mul_eq_zero.mp he).resolve_left (by decide)
  · rintro ⟨ha,hb⟩ y
    apply T.ext <;> simp only [mul_a,mul_b,mul_c,mul_d,mul_z] <;> (try simp [ha,hb]) <;> ring

private theorem center_second (x : T 1 1) :
    x ∈ Subgroup.center (T 1 1) ↔ x.a=0 ∧ x.b=0 ∧ x.c=0 ∧ x.d=0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h₁ := congrArg T.z (h ⟨0,1,0,0,0⟩)
    have h₂ := congrArg T.z (h ⟨1,0,0,0,0⟩)
    have h₃ := congrArg T.z (h ⟨0,0,0,1,0⟩)
    have h₄ := congrArg T.z (h ⟨0,0,1,0,0⟩)
    simp only [mul_z, mul_one, mul_zero, sub_zero, zero_sub, zero_add,
      add_zero, one_mul, zero_mul] at h₁ h₂ h₃ h₄
    refine ⟨?_,?_,?_,?_⟩
    · have he : (2:F)*x.a=0 := by linear_combination -h₁
      exact (mul_eq_zero.mp he).resolve_left (by decide)
    · have he : (2:F)*x.b=0 := by linear_combination h₂
      exact (mul_eq_zero.mp he).resolve_left (by decide)
    · have he : (2:F)*x.c=0 := by linear_combination -h₃
      exact (mul_eq_zero.mp he).resolve_left (by decide)
    · have he : (2:F)*x.d=0 := by linear_combination h₄
      exact (mul_eq_zero.mp he).resolve_left (by decide)
  · rintro ⟨ha,hb,hc,hd⟩ y
    apply T.ext <;> simp only [mul_a,mul_b,mul_c,mul_d,mul_z] <;> (try simp [ha,hb,hc,hd]) <;> ring

noncomputable def centerFirstEquiv : Subgroup.center (T 1 0) ≃ (F × F × F) where
  toFun x := (x.val.c,x.val.d,x.val.z)
  invFun x := ⟨⟨0,0,x.1,x.2.1,x.2.2⟩,(center_first _).mpr ⟨rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have h := (center_first x.val).mp x.property
    apply T.ext <;> simp_all
  right_inv x := by rcases x with ⟨a,b,c⟩; rfl

noncomputable def centerSecondEquiv : Subgroup.center (T 1 1) ≃ F where
  toFun x := x.val.z
  invFun x := ⟨⟨0,0,0,0,x⟩,(center_second _).mpr ⟨rfl,rfl,rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have h := (center_second x.val).mp x.property
    apply T.ext <;> simp_all
  right_inv _ := rfl

private theorem center_card_first : Nat.card (Subgroup.center (T 1 0)) = 27 := by
  rw [Nat.card_congr centerFirstEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

private theorem center_card_second : Nat.card (Subgroup.center (T 1 1)) = 3 := by
  rw [Nat.card_congr centerSecondEquiv]
  norm_num [Nat.card_eq_fintype_card]

private theorem first_second_not_isomorphic : ¬ Nonempty (T 1 0 ≃* T 1 1) := by
  rintro ⟨e⟩
  have h := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [center_card_first,center_card_second] at h
  norm_num at h

private theorem iso_implies_refined {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Refined G H := by
  refine ⟨⟨e.toEquiv, fun g n => map_zpow e g n⟩, ?_⟩
  constructor
  · intro h x y
    obtain ⟨a,rfl⟩ := e.surjective x
    obtain ⟨b,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (h a b)
  · intro h x y
    apply e.injective
    simpa only [map_mul] using h (e x) (e y)

private theorem refined_refl (G : Type) [Group G] : Refined G G :=
  ⟨⟨Equiv.refl G,fun _ _ => rfl⟩,Iff.rfl⟩

private theorem refined_symm {G H : Type} [Group G] [Group H]
    (h : Refined G H) : Refined H G := by
  rcases h with ⟨⟨f,hf⟩,ha⟩
  refine ⟨⟨f.symm,?_⟩,ha.symm⟩
  intro g n
  apply f.injective
  simp only [Equiv.apply_symm_apply,hf]

private theorem refined_trans {G H K : Type} [Group G] [Group H] [Group K]
    (h : Refined G H) (j : Refined H K) : Refined G K := by
  rcases h with ⟨⟨f,hf⟩,ha⟩
  rcases j with ⟨⟨g,hg⟩,hb⟩
  refine ⟨⟨f.trans g,?_⟩,ha.trans hb⟩
  intro x n
  simp only [Equiv.trans_apply,hf,hg]

/-- Exact source Definition 1.5 and both strictness witnesses for Problem 6.2. -/
private theorem strictness_witnesses :
    (Refined (T 1 0) (T 1 1) ∧ ¬ Nonempty (T 1 0 ≃* T 1 1)) ∧
    (PowerEquivalent (T 0 0) (T 1 0) ∧ ¬ Refined (T 0 0) (T 1 0)) := by
  refine ⟨⟨⟨all_power_equivalent 1 0 1 1,?_⟩,first_second_not_isomorphic⟩,
    all_power_equivalent 0 0 1 0,?_⟩
  · exact iff_of_false (first_nonabelian 0) (first_nonabelian 1)
  · intro h
    exact first_nonabelian 0 (h.2.mp zero_abelian)

end D5.S3.FiniteGroups.PowerInvariantRefinement.Witness

namespace D5.S3.FiniteGroups.PowerInvariantRefinement
structure FG where
  carrier : Type
  group : Group carrier
  finite : Finite carrier
attribute [instance] FG.group FG.finite

def Iso (G H : FG) : Prop := Nonempty (G.carrier ≃* H.carrier)
def Pow (G H : FG) : Prop := Witness.PowerEquivalent G.carrier H.carrier
def R (G H : FG) : Prop := Witness.Refined G.carrier H.carrier
def StrictRefines (r s : FG → FG → Prop) : Prop :=
  (∀ G H, r G H → s G H) ∧ ∃ G H, s G H ∧ ¬ r G H

def A : FG := ⟨Witness.T 0 0, inferInstance, inferInstance⟩
def B : FG := ⟨Witness.T 1 0, inferInstance, inferInstance⟩
def C : FG := ⟨Witness.T 1 1, inferInstance, inferInstance⟩

/-- Relabeling either finite group by a group isomorphism preserves the relation. -/
theorem isomorphism_invariant {G G' H H' : FG}
    (e : G.carrier ≃* G'.carrier) (f : H.carrier ≃* H'.carrier) :
    R G H ↔ R G' H' := by
  constructor
  · intro h
    exact Witness.refined_trans (Witness.refined_trans
      (Witness.iso_implies_refined e.symm) h) (Witness.iso_implies_refined f)
  · intro h
    exact Witness.refined_trans (Witness.refined_trans
      (Witness.iso_implies_refined e) h) (Witness.iso_implies_refined f.symm)


theorem finite_source_endpoint :
    Equivalence R ∧ StrictRefines Iso R ∧ StrictRefines R Pow := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro G
    exact Witness.refined_refl G.carrier
  · intro G H h
    exact Witness.refined_symm h
  · intro G H K h j
    exact Witness.refined_trans h j
  · intro G H h
    rcases h with ⟨e⟩
    exact (isomorphism_invariant (MulEquiv.refl G.carrier) e).mp
      (Witness.refined_refl G.carrier)
  · exact ⟨B, C, Witness.strictness_witnesses.1⟩
  · intro G H h
    exact h.1
  · exact ⟨A, B, Witness.strictness_witnesses.2⟩


end D5.S3.FiniteGroups.PowerInvariantRefinement
