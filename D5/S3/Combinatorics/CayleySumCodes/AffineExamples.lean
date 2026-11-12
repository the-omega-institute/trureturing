/- GID: D5/S3/Combinatorics/CayleySumCodes/AffineExamples
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/AffineExamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful affine groups and the actual connected and disconnected corrected total-code examples. -/

import D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic

/-!
Faithful affine actions and the complete retained affine constructions.
The connection sets are sets of actual group elements, with loop deletion
inherited from `sumGraph`. The F3 and F5 applications distinguish connected
and disconnected counterexamples to the old exhaustiveness assertions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.CayleySumCodes.AffineExamples

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

/-- Every invertible affine map of the line, with its actual multiplier and translation. -/
structure Affine1 (F : Type*) [Field F] where
  slope : Fˣ
  offset : F
  deriving DecidableEq

variable {F : Type*} [Field F]

@[ext] private theorem affine_ext {a b : Affine1 F}
    (hs : a.slope = b.slope) (ho : a.offset = b.offset) : a = b := by
  cases a; cases b; cases hs; cases ho; rfl

private def product (a b : Affine1 F) : Affine1 F :=
  ⟨a.slope * b.slope, a.offset + (a.slope : F) * b.offset⟩
private def inverse (a : Affine1 F) : Affine1 F :=
  ⟨a.slope⁻¹, -((a.slope⁻¹ : Fˣ) : F) * a.offset⟩

instance : Group (Affine1 F) where
  mul := product
  one := ⟨1, 0⟩
  inv := inverse
  mul_assoc := by
    intro a b c
    change product (product a b) c = product a (product b c)
    apply affine_ext
    · exact mul_assoc _ _ _
    · dsimp [product]; ring
  one_mul := by
    intro a
    change product ⟨1, 0⟩ a = a
    apply affine_ext <;> simp [product]
  mul_one := by
    intro a
    change product a ⟨1, 0⟩ = a
    apply affine_ext <;> simp [product]
  inv_mul_cancel := by
    intro a
    change product (inverse a) a = ⟨1, 0⟩
    apply affine_ext
    · exact inv_mul_cancel a.slope
    · simp [product, inverse]

@[simp] private theorem slope_mul (a b : Affine1 F) :
    (a * b).slope = a.slope * b.slope := rfl
@[simp] private theorem offset_mul (a b : Affine1 F) :
    (a * b).offset = a.offset + (a.slope : F) * b.offset := rfl
@[simp] private theorem slope_one : (1 : Affine1 F).slope = 1 := rfl
@[simp] private theorem offset_one : (1 : Affine1 F).offset = 0 := rfl
@[simp] private theorem slope_inv (a : Affine1 F) : (a⁻¹).slope = a.slope⁻¹ := rfl

instance [Fintype F] [DecidableEq F] : Fintype (Affine1 F) :=
  Fintype.ofEquiv (Fˣ × F)
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => (a.slope, a.offset)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance [Finite F] : Finite (Affine1 F) := by
  classical
  letI := Fintype.ofFinite F
  exact Finite.of_fintype _

/-- The faithful action on the entire field, rather than a scalar proxy. -/
def action (a : Affine1 F) : Equiv.Perm F where
  toFun x := (a.slope : F) * x + a.offset
  invFun x := ((a.slope⁻¹ : Fˣ) : F) * (x - a.offset)
  left_inv x := by simp [mul_add, mul_sub, ← mul_assoc]
  right_inv x := by simp [mul_add, mul_sub, ← mul_assoc]

/-- Composition is the original affine-group operation. -/
theorem action_mul (a b : Affine1 F) : action (a * b) = action a * action b := by
  ext x
  change ((a.slope * b.slope : Fˣ) : F) * x +
      (a.offset + (a.slope : F) * b.offset) =
    (a.slope : F) * ((b.slope : F) * x + b.offset) + a.offset
  simp only [Units.val_mul]; ring

/-- No distinct group elements are identified by this action. -/
theorem action_injective : Function.Injective (action (F := F)) := by
  intro a b h
  have ho := Equiv.congr_fun h 0
  have hs := Equiv.congr_fun h 1
  change (a.slope : F) * 0 + a.offset = (b.slope : F) * 0 + b.offset at ho
  change (a.slope : F) * 1 + a.offset = (b.slope : F) * 1 + b.offset at hs
  simp only [mul_zero, zero_add] at ho
  simp only [mul_one, ho, add_left_inj] at hs
  exact affine_ext (Units.ext hs) ho

/-- The nontranslation conjugacy classes are exactly the full multiplier
fibers. This identifies the source unions of classes with the actual affine
connection sets used by both retained constructions. -/
theorem conjugate_iff (s : Fˣ) (hs : s ≠ 1) (a : Affine1 F) :
    IsConj (⟨s, 0⟩ : Affine1 F) a ↔ a.slope = s := by
  constructor
  · rintro ⟨u, hu⟩
    have h := congrArg Affine1.slope hu.eq
    change (u : Affine1 F).slope * s = a.slope * (u : Affine1 F).slope at h
    have he : s = a.slope := mul_left_cancel (a := (u : Affine1 F).slope)
      (by simpa [mul_comm] using h)
    exact he.symm
  · intro ha
    have hsF : (s : F) ≠ 1 := fun h => hs (Units.ext h)
    apply isConj_iff.mpr
    refine ⟨⟨1, a.offset / (1 - (s : F))⟩, ?_⟩
    apply affine_ext
    · simpa [product, inverse] using ha.symm
    · change (product (product ⟨1, a.offset / (1 - (s : F))⟩ ⟨s, 0⟩)
        (inverse ⟨1, a.offset / (1 - (s : F))⟩)).offset = a.offset
      dsimp [product, inverse]
      simp only [Units.val_one, one_mul, mul_zero, add_zero, inv_one]
      field_simp [sub_ne_zero.mpr hsF.symm]
      <;> ring

/-- The entire multiplicative complement C, fixing zero. -/
def complement : Subgroup (Affine1 F) where
  carrier := {a | a.offset = 0}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.offset + (a.slope : F) * b.offset = 0; simp_all
  inv_mem' := by intro a ha; change -((a.slope⁻¹ : Fˣ) : F) * a.offset = 0; simp_all

/-- Identity together with the full conjugacy class of affine negations. -/
def connection : Set (Affine1 F) := {a | a = 1 ∨ a.slope = -1}

theorem connection_normal : NormalSubset (connection (F := F)) := by
  intro a x hx
  rcases hx with rfl | hx
  · left; simp
  · right
    change a.slope * x.slope * a.slope⁻¹ = -1
    rw [hx]
    simp [mul_comm, mul_left_comm]

/-- The corrected source construction is valid whenever the complement
squares are only 1 or -1, with 1 distinct from -1. This is a full field/group
theorem; its F3 and F5 instances below are the original two examples. -/
theorem total_code [Finite F] (hchar : (1 : F) ≠ -1)
    (hsq : ∀ a : Fˣ, a * a = 1 ∨ a * a = -1) :
    IsTotalPerfectCode (sumGraph (connection (F := F)) connection_normal)
      (complement (F := F) : Set (Affine1 F)) := by
  classical
  intro g
  let h : Affine1 F := ⟨if g.offset = 0 ∧ g.slope * g.slope ≠ 1
    then g.slope⁻¹ else -g.slope⁻¹, 0⟩
  have hunit : (1 : Fˣ) ≠ -1 := fun he => hchar (congrArg Units.val he)
  have eq_inv (u : Fˣ) (hu : g.slope * u = 1) : u = g.slope⁻¹ := by
    apply mul_left_cancel (a := g.slope)
    simpa using hu
  have eq_neg (u : Fˣ) (hu : g.slope * u = -1) : u = -g.slope⁻¹ := by
    apply mul_left_cancel (a := g.slope)
    simpa using hu
  have hm : h ∈ complement (F := F) := rfl
  have hne : g ≠ h := by
    intro he
    have ho : g.offset = 0 := congrArg Affine1.offset he
    have hs := congrArg Affine1.slope he
    by_cases hp : g.slope * g.slope = 1
    · have hn : g.slope = -g.slope⁻¹ := by simpa [h, ho, hp] using hs
      have hx : g.slope * g.slope = -1 := by calc
        g.slope * g.slope = g.slope * (-g.slope⁻¹) := congrArg (g.slope * ·) hn
        _ = -1 := by simp
      exact hunit (hp.symm.trans hx)
    · have hn : g.slope = g.slope⁻¹ := by simpa [h, ho, hp] using hs
      exact hp (by calc
        g.slope * g.slope = g.slope * g.slope⁻¹ := congrArg (g.slope * ·) hn
        _ = 1 := by simp)
  refine ⟨h, ⟨hm, hne, ?_⟩, ?_⟩
  · by_cases he : g.offset = 0 ∧ g.slope * g.slope ≠ 1
    · left
      apply affine_ext
      · simp [h, he, product]
      · simp [h, product, he.1]
    · right
      simp [h, he, product]
  · intro k hk
    have hk0 : k.offset = 0 := hk.1
    have casesSlope : (g.offset = 0 ∧ k.slope = g.slope⁻¹) ∨
        k.slope = -g.slope⁻¹ := by
      rcases hk.2.2 with he | hs
      · left
        have ho := congrArg Affine1.offset he
        have hu := congrArg Affine1.slope he
        exact ⟨by simpa [product, hk0] using ho, eq_inv k.slope hu⟩
      · exact Or.inr (eq_neg k.slope hs)
    apply affine_ext _ hk0
    rcases casesSlope with ⟨ho, hs⟩ | hs
    · have hp : g.slope * g.slope ≠ 1 := by
        intro hp
        apply hk.2.1
        apply affine_ext
        · exact (eq_inv g.slope hp).trans hs.symm
        · exact ho.trans hk0.symm
      simpa [h, ho, hp] using hs
    · have hbad : ¬(g.offset = 0 ∧ g.slope * g.slope ≠ 1) := by
        rintro ⟨ho, hp⟩
        have hneg : g.slope * g.slope = -1 := (hsq g.slope).resolve_left hp
        apply hk.2.1
        apply affine_ext
        · exact (eq_neg g.slope hneg).trans hs.symm
        · exact ho.trans hk0.symm
      simpa [h, hbad] using hs

/-- Exactly the affine maps whose multiplier is a sign. -/
def signedSlope : Subgroup (Affine1 F) where
  carrier := {a | a.slope = 1 ∨ a.slope = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    change a.slope = 1 ∨ a.slope = -1 at ha
    change b.slope = 1 ∨ b.slope = -1 at hb
    change a.slope * b.slope = 1 ∨ a.slope * b.slope = -1
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · left; simp [ha]
    · right; simp [ha]

/-- The exact connectivity condition for the full affine connection set.
In particular generation alone is not substituted for connectivity. -/
theorem connected_iff (hchar : (1 : F) ≠ -1) :
    (sumGraph (connection (F := F)) connection_normal).Connected ↔
      ∀ u : Fˣ, u = 1 ∨ u = -1 := by
  classical
  let graph := sumGraph (connection (F := F)) connection_normal
  have hn : (1 : Fˣ) ≠ -1 := fun h => hchar (congrArg Units.val h)
  constructor
  · intro hc u
    have hgen := D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers.connected_generates
      (connection (F := F)) connection_normal hc
    have hle : Subgroup.closure (connection (F := F)) ≤ signedSlope := by
      apply (Subgroup.closure_le _).2
      intro a ha
      rcases ha with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr ha
    have hm := hle (show (⟨u, 0⟩ : Affine1 F) ∈
        Subgroup.closure (connection (F := F)) by rw [hgen]; trivial)
    exact hm
  · intro hall
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨1, fun a => ?_⟩
    let r : Affine1 F := ⟨-1, 0⟩
    have hr : graph.Adj 1 r := by
      refine ⟨?_, Or.inr ?_⟩
      · intro he; exact hn (congrArg Affine1.slope he)
      · simp [r]
    rcases hall a.slope with ha | ha
    · have hra : graph.Adj r a := by
        refine ⟨?_, Or.inr ?_⟩
        · intro he
          have hh := congrArg Affine1.slope he
          exact hn (ha.symm.trans hh.symm)
        · simp [r, ha]
      exact hr.reachable.trans hra.reachable
    · exact (show graph.Adj 1 a from ⟨by
        intro he
        exact hn ((congrArg Affine1.slope he).trans ha), by
        right; simpa using ha⟩).reachable

/-- The actual embedded subgroup of the multiplicative complement. -/
def liftedSubgroup (H : Subgroup Fˣ) : Subgroup (Affine1 F) where
  carrier := {a | a.slope ∈ H ∧ a.offset = 0}
  one_mem' := ⟨H.one_mem, rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨H.mul_mem ha.1 hb.1, by simp [product, ha.2, hb.2]⟩
  inv_mem' := by
    intro a ha
    refine ⟨H.inv_mem ha.1, ?_⟩
    change -((a.slope⁻¹ : Fˣ) : F) * a.offset = 0
    rw [ha.2, mul_zero]

/-- Full conjugacy classes of every chosen nonidentity multiplier. -/
def transversalConnection (T : Set Fˣ) : Set (Affine1 F) := {a | a.slope ∈ T}

theorem transversalConnection_normal (T : Set Fˣ) :
    NormalSubset (transversalConnection T) := by
  intro a x hx
  change x.slope ∈ T at hx
  change a.slope * x.slope * a.slope⁻¹ ∈ T
  simpa [mul_comm, mul_left_comm, mul_assoc] using hx

private theorem unique_internal (H : Subgroup Fˣ) (T : Set Fˣ)
    (ht : Subgroup.IsComplement T (H : Set Fˣ)) (a0 : Fˣ)
    (ha0 : a0 ∈ T) (haH : a0 ∈ H) (t : Fˣ) (htT : t ∈ T) (htH : t ∈ H) :
    t = a0 := by
  obtain ⟨u, _, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht 1
  exact congrArg Subtype.val ((hu ⟨t, htT⟩ (by simpa using H.inv_mem htH)).trans
    (hu ⟨a0, ha0⟩ (by simpa using H.inv_mem haH)).symm)

/-- The entire retained affine total-code construction, over every finite
field and every multiplicative subgroup. A source transversal is an actual
coset complement in F-units; no code, graph or neighbor-count premise is used.
The source cyclic H=<c^s> and q-1=s*t restrictions instantiate this theorem. -/
theorem total_construction [Finite F] (H : Subgroup Fˣ) (T : Set Fˣ)
    (ht : Subgroup.IsComplement T (H : Set Fˣ)) (a0 : Fˣ)
    (ha0 : a0 ∈ T) (haH : a0 ∈ H) (hns : a0 ∉ squares H) :
    IsTotalPerfectCode (sumGraph (transversalConnection T)
      (transversalConnection_normal T)) (liftedSubgroup H) := by
  intro g
  obtain ⟨t, htH, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g.slope
  let h : Affine1 F := ⟨g.slope⁻¹ * t, 0⟩
  have hm : h ∈ liftedSubgroup H := by
    refine ⟨?_, rfl⟩
    simpa [mul_inv_rev] using H.inv_mem htH
  have hne : g ≠ h := by
    intro heq
    have hgH : g.slope ∈ H := heq.symm ▸ hm.1
    have hs := congrArg Affine1.slope heq
    have hsq : g.slope * g.slope = t := by
      calc
        g.slope * g.slope = g.slope * (g.slope⁻¹ * t) := congrArg (g.slope * ·) hs
        _ = t := by simp [mul_assoc]
    have hta := unique_internal H T ht a0 ha0 haH t t.2
      (hsq ▸ H.mul_mem hgH hgH)
    exact hns ⟨g.slope, hgH, hsq.trans hta⟩
  refine ⟨h, ⟨hm, hne, ?_⟩, ?_⟩
  · change g.slope * (g.slope⁻¹ * t) ∈ T
    simpa [mul_assoc] using t.2
  · intro k hk
    have hkt : g.slope * k.slope ∈ T := hk.2.2
    have he : g.slope * k.slope = t := by
      exact congrArg Subtype.val (hu ⟨g.slope * k.slope, hkt⟩
        (by simpa [mul_inv_rev, mul_assoc] using H.inv_mem hk.1.1))
    apply affine_ext _ hk.1.2
    change k.slope = g.slope⁻¹ * t
    rw [← he]
    simp [mul_assoc]

/-- Remove the internal multiplier class and insert all nonidentity
translations, as in the retained perfect-code construction. -/
def perfectConnection (H : Subgroup Fˣ) (T : Set Fˣ) : Set (Affine1 F) :=
  {a | (a.slope ∈ T ∧ a.slope ∉ H) ∨ (a.slope = 1 ∧ a ≠ 1)}

theorem perfectConnection_normal (H : Subgroup Fˣ) (T : Set Fˣ) :
    NormalSubset (perfectConnection H T) := by
  intro a x hx
  have hs : (a * x * a⁻¹).slope = x.slope := by
    simp [mul_comm, mul_left_comm]
  rcases hx with hx | hx
  · left; change _ ∈ T ∧ _ ∉ H; rwa [hs]
  · right
    refine ⟨hs.trans hx.1, ?_⟩
    intro he
    apply hx.2
    have hh := congrArg (fun z : Affine1 F => a⁻¹ * z * a) he
    simpa [mul_assoc] using hh

/-- Every source transversal yields the retained affine perfect-code
construction, independently of a nonsquare or a total-code assumption. -/
theorem perfect_construction [Finite F] (H : Subgroup Fˣ) (T : Set Fˣ)
    (ht : Subgroup.IsComplement T (H : Set Fˣ)) :
    PerfectCodeTransversal.IsPerfectCode
      (sumGraph (perfectConnection H T) (perfectConnection_normal H T))
      (liftedSubgroup H) := by
  classical
  intro g
  by_cases hgH : g ∈ liftedSubgroup H
  · refine ⟨g, ⟨hgH, Or.inl rfl⟩, ?_⟩
    intro k hk
    rcases hk.2 with he | he
    · exact he.symm
    · rcases he.2 with he | he
      · exact (he.2 (H.mul_mem hgH.1 hk.1.1)).elim
      · apply False.elim
        apply he.2
        apply affine_ext he.1
        change g.offset + (g.slope : F) * k.offset = 0
        simp [hgH.2, hk.1.2]
  · by_cases hgs : g.slope ∈ H
    · let h : Affine1 F := ⟨g.slope⁻¹, 0⟩
      have hm : h ∈ liftedSubgroup H := ⟨H.inv_mem hgs, rfl⟩
      have hgo : g.offset ≠ 0 := fun ho => hgH ⟨hgs, ho⟩
      have hne : g ≠ h := fun he => hgo (congrArg Affine1.offset he)
      refine ⟨h, ⟨hm, Or.inr ⟨hne, Or.inr ⟨?_, ?_⟩⟩⟩, ?_⟩
      · change g.slope * g.slope⁻¹ = 1; simp
      · intro he
        have ho := congrArg Affine1.offset he
        exact hgo (by simpa [h, product] using ho)
      · intro k hk
        rcases hk.2 with he | he
        · exact (hgH (he.symm ▸ hk.1)).elim
        · rcases he.2 with he | he
          · exact (he.2 (H.mul_mem hgs hk.1.1)).elim
          · apply affine_ext _ hk.1.2
            change k.slope = g.slope⁻¹
            have hs : g.slope * k.slope = 1 := he.1
            exact mul_left_cancel (a := g.slope) (by simpa using hs)
    · obtain ⟨t, htH, hu⟩ :=
        Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g.slope
      let h : Affine1 F := ⟨g.slope⁻¹ * t, 0⟩
      have hm : h ∈ liftedSubgroup H := by
        refine ⟨?_, rfl⟩
        simpa [mul_inv_rev] using H.inv_mem htH
      have htN : (t : Fˣ) ∉ H := by
        intro htN
        apply hgs
        have hp := H.mul_mem htN htH
        simpa [mul_assoc] using hp
      have hne : g ≠ h := fun he => hgH (he.symm ▸ hm)
      refine ⟨h, ⟨hm, Or.inr ⟨hne, Or.inl ?_⟩⟩, ?_⟩
      · change g.slope * (g.slope⁻¹ * t) ∈ T ∧
          g.slope * (g.slope⁻¹ * t) ∉ H
        simpa [mul_assoc] using And.intro t.2 htN
      · intro k hk
        rcases hk.2 with he | he
        · exact (hgH (he.symm ▸ hk.1)).elim
        · rcases he.2 with he | he
          · have heq : g.slope * k.slope = t := by
              exact congrArg Subtype.val (hu ⟨g.slope * k.slope, he.1⟩
                (by simpa [mul_inv_rev, mul_assoc] using H.inv_mem hk.1.1))
            apply affine_ext _ hk.1.2
            change k.slope = g.slope⁻¹ * t
            rw [← heq]; simp [mul_assoc]
          · apply False.elim
            apply hgs
            have hs : g.slope * k.slope = 1 := he.1
            have hp := H.inv_mem hk.1.1
            have hge : g.slope = k.slope⁻¹ :=
              (mul_eq_one_iff_eq_inv).mp hs
            rwa [hge]

end D5.S3.Combinatorics.CayleySumCodes.AffineExamples
