/- GID: D5/S3/Quantum/Foundation/NiceConeFaces
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/NiceConeFaces
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Ambient dual completeness exposes every original cone face. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Facial dual completeness and exact support-zero sections in the ambient space. -/

noncomputable section
open Set Pointwise

namespace D5.S3.Quantum.Foundation.NiceConeFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Both dual cones use the original ambient algebraic dual. -/
def ambientDual (s : Set V) : PointedCone ℝ (V →ₗ[ℝ] ℝ) :=
  PointedCone.dual (Module.Dual.eval ℝ V) s

/-- Facial dual completeness, with Minkowski sum in the ambient dual. -/
def Nice (C : PointedCone ℝ V) : Prop :=
  ∀ E : C.Face, (ambientDual (E : Set V) : Set (V →ₗ[ℝ] ℝ)) =
    (ambientDual (C : Set V) : Set (V →ₗ[ℝ] ℝ)) +
      ((Submodule.span ℝ (E : Set V)).dualAnnihilator : Set (V →ₗ[ℝ] ℝ))

private def zeroFace (C : PointedCone ℝ V) (a : V →ₗ[ℝ] ℝ)
    (ha : ∀ x ∈ C, 0 ≤ a x) : C.Face where
  toSubmodule := C ⊓ (a.ker.restrictScalars (Nonneg ℝ))
  isFaceOf := by
    apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
    · exact inf_le_left
    · intro x y hx hy hxy
      refine ⟨hx, ?_⟩
      have hz : a (x + y) = 0 := hxy.2
      change a x = 0
      rw [map_add] at hz
      exact le_antisymm (by linarith [ha y hy]) (ha x hx)

/-- A nice closed finite-dimensional cone has all its original faces exposed.
The zero functional includes the whole face; no salience or spanning assumption is imposed. -/
theorem every_face_exposed {C : PointedCone ℝ V}
    (_hclosed : IsClosed (C : Set V)) (hnice : Nice C) (F : C.Face) :
    ∃ a : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ a x) ∧
      (F : Set V) = {x | x ∈ C ∧ a x = 0} := by
  classical
  let Z (a : V →ₗ[ℝ] ℝ) := {x | x ∈ C ∧ a x = 0}
  let S (a : V →ₗ[ℝ] ℝ) := Submodule.span ℝ (Z a)
  let P (n : ℕ) := ∃ a : V →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ a x) ∧
    (∀ x ∈ F, a x = 0) ∧ Module.finrank ℝ (S a) = n
  have hex : ∃ n, P n := ⟨Module.finrank ℝ (S 0), 0,
    by simp, by simp, rfl⟩
  obtain ⟨a, ha, haF, hdim⟩ := Nat.find_spec hex
  let E : C.Face := zeroFace C a ha
  have hE (x : V) : x ∈ E ↔ x ∈ C ∧ a x = 0 := Iff.rfl
  have hFE : F.toPointedCone ≤ E.toPointedCone :=
    fun x hx => (hE x).mpr ⟨F.isFaceOf.le hx, haF x hx⟩
  have hEq : (F : Set V) = (E : Set V) := by
    by_contra hne
    let W := Submodule.span ℝ (E : Set V)
    let D : PointedCone ℝ W := E.toPointedCone.comap W.subtype
    let H : D.Face := ⟨F.toPointedCone.comap W.subtype,
      ((F.isFaceOf.isFaceOf_iff_le E.isFaceOf).mpr hFE).comap W.subtype⟩
    have hgen : Submodule.span ℝ (D : Set W) = ⊤ := by
      apply (Submodule.span_val_image_eq_iff W (D : Set W)).mp
      have hi : Subtype.val '' (D : Set W) = (E : Set V) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
      rw [hi]
    have hproper : H.toPointedCone ≠ D := by
      intro he
      apply hne
      apply Set.Subset.antisymm hFE
      intro x hx
      have hh : (⟨x, Submodule.subset_span hx⟩ : W) ∈ D := hx
      rw [← he] at hh
      exact hh
    obtain ⟨g, hg, hgpos, hgzero⟩ :=
      ExclusionBallFaces.proper_cone_face_support hgen H hproper
    obtain ⟨q, hq⟩ := g.exists_extend
    have hqpos : q ∈ ambientDual (E : Set V) := by
      intro x hx
      have hh := LinearMap.congr_fun hq (⟨x, Submodule.subset_span hx⟩ : W)
      exact hh ▸ hgpos _ hx
    rw [hnice E] at hqpos
    obtain ⟨b, hb, d, hd, hbd⟩ := hqpos
    have hd0 (x : W) : d x = 0 := hd x.property
    have hbq (x : W) : b x = g x := by
      have hh := LinearMap.congr_fun hbd x
      have hhq := LinearMap.congr_fun hq x
      change b x + d x = q x at hh
      rw [hd0, add_zero] at hh
      exact hh.trans hhq
    have hbpos : ∀ x ∈ C, 0 ≤ b x := fun _ hx => hb hx
    have hbF : ∀ x ∈ F, b x = 0 := by
      intro x hx
      let x' : W := ⟨x, Submodule.subset_span (hFE hx)⟩
      exact (hbq x').trans (hgzero x' hx)
    have hbnz : ∃ x ∈ E, b x ≠ 0 := by
      by_contra! hn
      apply hg
      have hk : Submodule.span ℝ (D : Set W) ≤ g.ker :=
        Submodule.span_le.mpr (fun x hx => by
          change g x = 0
          rw [← hbq x]
          exact hn x hx)
      rw [hgen] at hk
      exact LinearMap.ker_eq_top.mp (top_le_iff.mp hk)
    obtain ⟨x, hx, hbx⟩ := hbnz
    have hsub : S (a + b) ≤ S a := by
      apply Submodule.span_le.mpr
      intro y hy
      have hz : a y + b y = 0 := hy.2
      have hay : a y = 0 := le_antisymm (by linarith [hbpos y hy.1]) (ha y hy.1)
      exact Submodule.subset_span ⟨hy.1, hay⟩
    have hker : S (a + b) ≤ b.ker := by
      apply Submodule.span_le.mpr
      intro y hy
      have hz : a y + b y = 0 := hy.2
      change b y = 0
      exact le_antisymm (by linarith [ha y hy.1]) (hbpos y hy.1)
    have hlt : S (a + b) < S a := lt_of_le_of_ne hsub (by
      intro he
      have hxS : x ∈ S a := Submodule.subset_span ((hE x).mp hx)
      rw [← he] at hxS
      exact hbx (hker hxS))
    have hnew : P (Module.finrank ℝ (S (a + b))) :=
      ⟨a + b, fun y hy => add_nonneg (ha y hy) (hbpos y hy),
        fun y hy => by simp [haF y hy, hbF y hy], rfl⟩
    have hmin := Nat.find_min' hex hnew
    have hdrop := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  exact ⟨a, ha, hEq⟩

end D5.S3.Quantum.Foundation.NiceConeFaces
