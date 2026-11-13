/- GID: D5/S3/Combinatorics/CayleySumCodes/AffineExamples
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/AffineExamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine groups and the actual connected and disconnected corrected total-code examples. -/

import D5.S3.Combinatorics.CayleySumCodes.CodeCentralizers
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic

/-!
Affine groups and corrected total-code examples.
The connection sets are sets of actual group elements, with loop deletion
inherited from `sumGraph`. The F3 and F5 applications distinguish connected
and disconnected examples; the connected F3 example refutes the old exhaustiveness assertion.
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

/-- Full conjugacy classes of every chosen nonidentity multiplier. -/
def transversalConnection (T : Set Fˣ) : Set (Affine1 F) := {a | a.slope ∈ T}

end D5.S3.Combinatorics.CayleySumCodes.AffineExamples
