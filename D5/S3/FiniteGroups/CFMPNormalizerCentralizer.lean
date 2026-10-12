/- GID: D5/S3/FiniteGroups/CFMPNormalizerCentralizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CFMPNormalizerCentralizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Right-coset centralizer is the normalizer quotient, with the CFMP marked consumer. -/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace D5.S3.FiniteGroups.CFMPNormalizerCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {G : Type*} [Group G] (H : Subgroup G)

abbrev RightCosets := Quotient (QuotientGroup.rightRel H)

def rightMul (a : G) : RightCosets H ≃ RightCosets H where
  toFun := Quotient.map' (fun g : G => g * a) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  invFun := Quotient.map' (fun g : G => g * a⁻¹) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp
  right_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp

@[simp] theorem rightMul_mk (a g : G) :
    rightMul H a (Quotient.mk'' g) = Quotient.mk'' (g * a) := rfl

def normalizerMul {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    RightCosets H ≃ RightCosets H where
  toFun := Quotient.map' (fun g : G => n * g) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have hc := ((Subgroup.mem_normalizer_iff.mp hn) (y * x⁻¹)).mp h
    simpa [mul_assoc] using hc)
  invFun := Quotient.map' (fun g : G => n⁻¹ * g) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have hni : n⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.inv_mem (Subgroup.normalizer (H : Set G)) hn
    have hc := ((Subgroup.mem_normalizer_iff.mp hni) (y * x⁻¹)).mp h
    simpa [mul_assoc] using hc)
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp
  right_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp

@[simp] theorem normalizerMul_mk {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G)) (g : G) :
    normalizerMul H hn (Quotient.mk'' g) = Quotient.mk'' (n * g) := rfl

theorem rightMul_normalizer_commute {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G)) (a : G) :
    rightMul H a * normalizerMul H hn = normalizerMul H hn * rightMul H a := by
  ext q
  refine Quotient.inductionOn' q ?_
  intro g
  simp only [Equiv.Perm.mul_apply, rightMul_mk, normalizerMul_mk]
  congr 1
  simp [mul_assoc]

def commutingPerms : Subgroup (Equiv.Perm (RightCosets H)) :=
  Subgroup.centralizer (Set.range (rightMul H))

def normalizerMap : Subgroup.normalizer (H : Set G) →*
    commutingPerms H where
  toFun n :=
    ⟨normalizerMul H n.property,
      Subgroup.mem_centralizer_iff.mpr (by
        intro r hr
        rcases hr with ⟨a, rfl⟩
        exact rightMul_normalizer_commute H n.property a)⟩
  map_one' := by
    ext q
    refine Quotient.inductionOn' q ?_
    intro g
    simp [normalizerMul_mk]
  map_mul' := by
    intro n m
    ext q
    refine Quotient.inductionOn' q ?_
    intro g
    simp only [normalizerMul_mk]
    congr 1
    simp [mul_assoc]

private theorem rightMul_stabilizer (g : G) :
    rightMul H g (Quotient.mk'' (1 : G)) = Quotient.mk'' (1 : G) ↔ g ∈ H := by
  constructor
  · intro he
    have hr := Quotient.exact' he
    rw [QuotientGroup.rightRel_apply] at hr
    simpa using hr
  · intro hg
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa using hg

private theorem centralizer_map_surjective :
    Function.Surjective (normalizerMap H) := by
  intro p
  let x0 : RightCosets H := Quotient.mk'' (1 : G)
  let n : G := (p.1 x0).out
  have hpbase : p.1 x0 = Quotient.mk'' n := by
    exact (Quotient.out_eq' (p.1 x0)).symm
  have hpcomm (a : G) :
      rightMul H a * p.1 = p.1 * rightMul H a := by
    apply (Subgroup.mem_centralizer_iff.mp p.2)
    exact ⟨a, rfl⟩
  have hstab (a : G) :
      rightMul H a x0 = x0 ↔ a ∈ H :=
    rightMul_stabilizer H a
  have hn : n ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have he := congrArg (fun e : Equiv.Perm (RightCosets H) => e x0)
        (hpcomm h)
      have hfix0 : rightMul H h x0 = x0 := (hstab h).mpr hh
      have he' : rightMul H h (p.1 x0) = p.1 x0 := by
        simpa [Equiv.Perm.mul_apply, hfix0] using he
      rw [hpbase, rightMul_mk] at he'
      have hr := Quotient.exact' he'
      rw [QuotientGroup.rightRel_apply] at hr
      simpa [mul_assoc] using (H.inv_mem hr)
    · intro hh
      have he := congrArg (fun e : Equiv.Perm (RightCosets H) => e x0)
        (hpcomm h)
      have he' : rightMul H h (p.1 x0) = p.1 x0 := by
        rw [hpbase, rightMul_mk]
        apply Quotient.sound'
        rw [QuotientGroup.rightRel_apply]
        simpa [mul_assoc] using (H.inv_mem hh)
      have he'' : p.1 (rightMul H h x0) = p.1 x0 := by
        calc
          p.1 (rightMul H h x0) = rightMul H h (p.1 x0) := by
            simpa [Equiv.Perm.mul_apply] using he.symm
          _ = p.1 x0 := he'
      have hfix : rightMul H h x0 = x0 := p.1.injective he''
      exact (hstab h).mp hfix
  refine ⟨⟨n, hn⟩, ?_⟩
  apply Subtype.ext
  ext q
  refine Quotient.inductionOn' q ?_
  intro g
  have he := congrArg (fun e : Equiv.Perm (RightCosets H) => e x0)
    (hpcomm g)
  have he' : p.1 (rightMul H g x0) = rightMul H g (p.1 x0) := by
    simpa using he.symm
  have he'' : p.1 (Quotient.mk'' g) = Quotient.mk'' (n * g) := by
    simpa [x0, hpbase, rightMul_mk, Equiv.Perm.mul_apply] using he'
  change normalizerMul H hn (Quotient.mk'' g) = p.1 (Quotient.mk'' g)
  rw [normalizerMul_mk]
  exact he''.symm


theorem normalizerMap_ker :
    H.subgroupOf (Subgroup.normalizer (H : Set G)) = (normalizerMap H).ker := by
  apply le_antisymm
  · intro h hh
    change normalizerMap H h = 1
    ext q
    refine Quotient.inductionOn' q ?_
    intro g
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa [mul_assoc] using H.inv_mem hh
  · intro n hn
    change normalizerMap H n = 1 at hn
    have hbase := congrArg (fun p : commutingPerms H =>
      p.1 (Quotient.mk'' (1 : G))) hn
    have he : Quotient.mk'' (s₁ := QuotientGroup.rightRel H) (n : G) =
        Quotient.mk'' (s₁ := QuotientGroup.rightRel H) (1 : G) := by
      simpa [normalizerMap, normalizerMul_mk] using hbase
    have hr := Quotient.exact' he
    rw [QuotientGroup.rightRel_apply] at hr
    change (n : G) ∈ H
    simpa using H.inv_mem hr

/-- The standard-composition group isomorphism from the normalizer quotient to
the permutations of right cosets commuting with every right translation. -/
noncomputable def normalizerCentralizerIso :
    (Subgroup.normalizer (H : Set G) ⧸
      H.subgroupOf (Subgroup.normalizer (H : Set G))) ≃*
      commutingPerms H :=
  QuotientGroup.liftEquiv (H.subgroupOf (Subgroup.normalizer (H : Set G)))
    (centralizer_map_surjective H) (normalizerMap_ker H)

end D5.S3.FiniteGroups.CFMPNormalizerCentralizer
