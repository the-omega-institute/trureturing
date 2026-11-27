/- GID: D5/S3/VertexAlgebra/BRST/MonsterPresentationBracketScalar
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/MonsterPresentationBracketScalar
   mirror-E: none(waiver:algebraic-positive-presentation)
   anchors: []
   utility: none
   digest: Bracketing the positive Monster presentation tensor map acts by a weight scalar. -/

import D5.S3.VertexAlgebra.BRST.MonsterPositiveStringPresentation
import Mathlib.LinearAlgebra.BilinearMap

/-!
Equations (14)–(16) of the direct-presentation derivation dated 2026-11-24 give the
bracket scalar in Borcherds coordinates. The two linear operators have the same bracket
defect, so their difference is a derivation. It vanishes on the positive Serre generators.
-/

set_option autoImplicit false

noncomputable section

open scoped DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.MonsterPresentationBracketScalar

open MonsterPositiveCocycle MonsterPositiveStringPresentation

attribute [local instance 100] LieRing.ofAssociativeRing

section BracketTensor

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The linear map that brackets the two tensor factors. -/
def bracketTensor : L ⊗[ℝ] L →ₗ[ℝ] L :=
  TensorProduct.lift (LieAlgebra.ad ℝ L).toLinearMap

@[simp] theorem bracketTensor_tmul (x y : L) :
    bracketTensor (x ⊗ₜ[ℝ] y) = ⁅x, y⁆ :=
  TensorProduct.lift.tmul x y

/-- Jacobi makes the bracket map equivariant for the diagonal adjoint action. -/
theorem bracketTensor_lie (x : L) (t : L ⊗[ℝ] L) :
    bracketTensor ⁅x, t⁆ = ⁅x, bracketTensor t⁆ := by
  induction t using TensorProduct.inductionOn with
  | tmul y z =>
      rw [TensorProduct.LieModule.lie_tmul_right, map_add]
      simp only [bracketTensor_tmul]
      exact (leibniz_lie x y z).symm
  | add u v hu hv =>
      rw [lie_add, map_add, hu, hv, map_add, lie_add]

private theorem bracketTensor_eta (p q : Weight) (x y : L) :
    bracketTensor (homogeneousEta weightForm p q x y) = (2 * weightForm p q) • ⁅x, y⁆ := by
  simp only [homogeneousEta, map_smul, altTensor_apply, map_sub, bracketTensor_tmul]
  rw [(lie_skew y x).symm, sub_neg_eq_add, ← two_smul ℝ, smul_smul,
    mul_comm (weightForm p q) (2 : ℝ)]

end BracketTensor

/-- The scalar in equation (16), for paper coordinates `(m,n)`. -/
def bracketScalar (p : Weight) : ℝ :=
  -2 * (p.2 : ℝ) * ((p.1 : ℝ) - 1)

theorem bracketScalar_add (p q : Weight) :
    bracketScalar (p + q) = bracketScalar p + bracketScalar q + 2 * weightForm p q := by
  simp only [bracketScalar, weightForm, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_add,
    Prod.snd_add, Int.cast_add]
  ring

variable {J : Type*} (order : J → ℕ+)

local notation "P" => PositivePresentation order
local notation "grade" => presentationGrade order
local notation "Δ" => gradedPresentationDelta order

/-- The diagonal linear map with eigenvalue `bracketScalar p` on the weight-`p` piece. -/
def scalarDiagonal : P →ₗ[ℝ] P :=
  (DirectSum.toModule ℝ Weight P fun p => bracketScalar p • (grade p).subtype).comp
    (DirectSum.decomposeLinearEquiv grade).toLinearMap

theorem scalarDiagonal_of_mem {p : Weight} {x : P} (hx : x ∈ grade p) :
    scalarDiagonal order x = bracketScalar p • x := by
  let u : grade p := ⟨x, hx⟩
  change scalarDiagonal order (u : P) = _
  rw [scalarDiagonal, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.decomposeLinearEquiv_apply_coe grade p u, DirectSum.toModule_lof]
  rfl

private theorem scalarDiagonal_bracket {p q : Weight} {x y : P}
    (hx : x ∈ grade p) (hy : y ∈ grade q) :
    scalarDiagonal order ⁅x, y⁆ =
      ⁅scalarDiagonal order x, y⁆ + ⁅x, scalarDiagonal order y⁆ +
        (2 * weightForm p q) • ⁅x, y⁆ := by
  rw [scalarDiagonal_of_mem order (presentationGrade_bracket order hx hy),
    scalarDiagonal_of_mem order hx, scalarDiagonal_of_mem order hy, bracketScalar_add]
  simp only [smul_lie, lie_smul, add_smul]

/-- The composition of the presentation tensor map with the bracket. -/
def bracketDelta : P →ₗ[ℝ] P :=
  bracketTensor.comp Δ

private theorem bracketDelta_bracket {p q : Weight} {x y : P}
    (hx : x ∈ grade p) (hy : y ∈ grade q) :
    bracketDelta order ⁅x, y⁆ =
      ⁅bracketDelta order x, y⁆ + ⁅x, bracketDelta order y⁆ +
        (2 * weightForm p q) • ⁅x, y⁆ := by
  simp only [bracketDelta, LinearMap.comp_apply]
  rw [gradedPresentationDelta_bracket order hx hy, map_add, map_sub, bracketTensor_lie,
    bracketTensor_lie, bracketTensor_eta, sub_eq_add_neg, lie_skew (bracketTensor (Δ x)) y,
    add_comm ⁅x, bracketTensor (Δ y)⁆]

private theorem difference_bracket (x y : P) :
    let T := bracketDelta order - scalarDiagonal order
    T ⁅x, y⁆ = ⁅T x, y⁆ + ⁅x, T y⁆ := by
  let T := bracketDelta order - scalarDiagonal order
  let b := (LieAlgebra.ad ℝ P).toLinearMap
  have h : b.compr₂ T = b.comp T + b.compl₂ T := by
    apply DirectSum.decompose_lhom_ext grade
    intro p
    apply LinearMap.ext
    intro u
    apply DirectSum.decompose_lhom_ext grade
    intro q
    apply LinearMap.ext
    intro v
    change T ⁅(u : P), (v : P)⁆ = ⁅T u, (v : P)⁆ + ⁅(u : P), T v⁆
    simp only [T, LinearMap.sub_apply, sub_lie, lie_sub,
      bracketDelta_bracket order u.property v.property,
      scalarDiagonal_bracket order u.property v.property]
    abel
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- The images of the free generators Lie-span the Serre quotient. -/
theorem presentation_lieSpan_eq_top :
    LieSubalgebra.lieSpan ℝ P (Set.range (generator order)) = ⊤ := by
  let S := LieSubalgebra.lieSpan ℝ P (Set.range (generator order))
  let f := FreeLieAlgebra.lift ℝ fun j =>
    (⟨generator order j, LieSubalgebra.subset_lieSpan (Set.mem_range_self j)⟩ : S)
  have h : S.incl.comp f = presentationQuotient order := by
    apply FreeLieAlgebra.hom_ext
    intro j
    change ((f (FreeLieAlgebra.of ℝ j) : S) : P) = generator order j
    rw [FreeLieAlgebra.lift_of_apply]
  apply top_unique
  intro x _
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (serreIdeal order).toSubmodule x
  have hu : (f u : P) = (Submodule.Quotient.mk u : P) := DFunLike.congr_fun h u
  rw [← hu]
  exact (f u).property

private theorem eq_top_of_generators (S : LieSubalgebra ℝ P)
    (hS : ∀ j, generator order j ∈ S) : S = ⊤ := by
  apply top_unique
  rw [← presentation_lieSpan_eq_top order]
  exact LieSubalgebra.lieSpan_le.mpr <| by
    rintro _ ⟨j, rfl⟩
    exact hS j

/-- The two operators agree on the entire presentation. -/
theorem bracketDelta_eq_scalarDiagonal :
    bracketDelta order = scalarDiagonal order := by
  let T := bracketDelta order - scalarDiagonal order
  let S : LieSubalgebra ℝ P :=
    { T.ker with
      lie_mem' := fun {x y} hx hy => by
        change T x = 0 at hx
        change T y = 0 at hy
        change T ⁅x, y⁆ = 0
        rw [difference_bracket order x y, hx, hy, zero_lie, lie_zero, add_zero] }
  have hS : S = ⊤ := eq_top_of_generators order S fun j => by
    change bracketDelta order (generator order j) - scalarDiagonal order (generator order j) = 0
    have hΔ : bracketDelta order (generator order j) = 0 := by
      simp [bracketDelta, gradedPresentationDelta_generator]
    rw [hΔ]
    cases j with
    | none =>
        rw [scalarDiagonal_of_mem order (real_mem_presentationGrade order)]
        simp [bracketScalar, realRoot]
    | some j =>
        rw [scalarDiagonal_of_mem order (imaginary_mem_presentationGrade order j)]
        simp [bracketScalar, imaginaryRoot]
  apply LinearMap.ext
  intro x
  have hx : x ∈ S := hS ▸ LieSubalgebra.mem_top x
  exact sub_eq_zero.mp (show T x = 0 from hx)

/-- On a homogeneous element the bracket of the split tensor is
`-2 * n * (m - 1)` times the element, in Borcherds coordinates. -/
theorem bracket_splitTensor_eq_scalar {p : Weight} {x : P} (hx : x ∈ grade p) :
    bracketTensor (Δ x) = bracketScalar p • x := by
  change bracketDelta order x = _
  rw [bracketDelta_eq_scalarDiagonal, scalarDiagonal_of_mem order hx]

private theorem weight_supported_of_ne_zero {p : Weight} {x : P}
    (hx : x ∈ grade p) (hn : x ≠ 0) : p = realRoot ∨ (0 < p.1 ∧ 0 < p.2) := by
  by_cases hreal : p = realRoot
  · exact Or.inl hreal
  · right
    by_contra hout
    rw [presentationGrade_eq_bot_of_outside order p hreal hout, Submodule.mem_bot] at hx
    exact hn hx

/-- Above first coordinate one, a homogeneous element killed by the split tensor vanishes. -/
theorem eq_zero_of_gradedPresentationDelta_eq_zero {p : Weight} {x : P}
    (hx : x ∈ grade p) (hp : 1 < p.1) (hΔ : Δ x = 0) : x = 0 := by
  by_contra hne
  have hreal : p ≠ realRoot := by
    rintro rfl
    simp [realRoot] at hp
  have hpos := (weight_supported_of_ne_zero order hx hne).resolve_left hreal
  have hscalar : bracketScalar p ≠ 0 := by
    have hm : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp
    have hn : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hpos.2
    exact mul_ne_zero (mul_ne_zero (by norm_num) hn.ne') (sub_pos.mpr hm).ne'
  have h : bracketScalar p • x = 0 := by
    rw [← bracket_splitTensor_eq_scalar order hx, hΔ, map_zero]
  exact hne ((smul_eq_zero.mp h).resolve_left hscalar)

/-- The span of pure tensors whose two weights add to `p` and whose first
coordinates are strictly between zero and `p.1`. -/
def presentationTensorBlock (p : Weight) : Submodule ℝ (P ⊗[ℝ] P) :=
  Submodule.span ℝ {t | ∃ (a b : Weight) (u v : P), a + b = p ∧
    0 < a.1 ∧ a.1 < p.1 ∧ 0 < b.1 ∧ b.1 < p.1 ∧
    u ∈ grade a ∧ v ∈ grade b ∧ t = u ⊗ₜ[ℝ] v}

private theorem first_pos_of_ne_zero {a : Weight} {u : P}
    (hu : u ∈ grade a) (hn : u ≠ 0) : 0 < a.1 := by
  rcases weight_supported_of_ne_zero order hu hn with rfl | h
  · norm_num [realRoot]
  · exact h.1

private theorem tmul_mem_block {a b : Weight} {u v : P}
    (hu : u ∈ grade a) (hv : v ∈ grade b) :
    u ⊗ₜ[ℝ] v ∈ presentationTensorBlock order (a + b) := by
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp [hv0]
  have ha := first_pos_of_ne_zero order hu hu0
  have hb := first_pos_of_ne_zero order hv hv0
  exact Submodule.subset_span
    ⟨a, b, u, v, rfl, ha, by simpa only [Prod.fst_add] using lt_add_of_pos_right a.1 hb,
      hb, by simpa only [Prod.fst_add] using lt_add_of_pos_left b.1 ha, hu, hv, rfl⟩

private theorem lie_mem_tensorBlock {a b : Weight} {x : P} {t : P ⊗[ℝ] P}
    (hx : x ∈ grade a) (ht : t ∈ presentationTensorBlock order b) :
    ⁅x, t⁆ ∈ presentationTensorBlock order (a + b) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨c, d, u, v, rfl, _, _, _, _, hu, hv, rfl⟩ := ht
      rw [TensorProduct.LieModule.lie_tmul_right]
      apply Submodule.add_mem
      · simpa only [add_assoc] using
          tmul_mem_block order (presentationGrade_bracket order hx hu) hv
      · simpa only [add_left_comm c a d] using
          tmul_mem_block order hu (presentationGrade_bracket order hx hv)
  | zero => simp
  | add t u _ _ ht hu => rw [lie_add]; exact Submodule.add_mem _ ht hu
  | smul c t _ ht => rw [lie_smul]; exact Submodule.smul_mem _ c ht

private theorem delta_bracket_mem_tensorBlock {a b : Weight} {x y : P}
    (hx : x ∈ grade a) (hy : y ∈ grade b)
    (hΔx : Δ x ∈ presentationTensorBlock order a)
    (hΔy : Δ y ∈ presentationTensorBlock order b) :
    Δ ⁅x, y⁆ ∈ presentationTensorBlock order (a + b) := by
  rw [gradedPresentationDelta_bracket order hx hy, homogeneousEta, altTensor_apply]
  have hyx : ⁅y, Δ x⁆ ∈ presentationTensorBlock order (a + b) := by
    simpa only [add_comm b a] using lie_mem_tensorBlock order hy hΔx
  have ht : y ⊗ₜ[ℝ] x ∈ presentationTensorBlock order (a + b) := by
    simpa only [add_comm b a] using tmul_mem_block order hy hx
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (lie_mem_tensorBlock order hx hΔy) hyx)
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (tmul_mem_block order hx hy) ht))

/-- The split tensor of a weight-`p` element lies in the span of pure tensors
with weight sum `p` and smaller positive first coordinates. -/
theorem gradedPresentationDelta_mem_tensorBlock {p : Weight} {x : P} (hx : x ∈ grade p) :
    Δ x ∈ presentationTensorBlock order p := by
  -- The pieces satisfying the tensor bound span a Lie subalgebra.
  let G (a : Weight) : Submodule ℝ P := grade a ⊓ (presentationTensorBlock order a).comap Δ
  let M : Submodule ℝ P := ⨆ a, G a
  have hlie {u v : P} (hu : u ∈ M) (hv : v ∈ M) : ⁅u, v⁆ ∈ M := by
    refine Submodule.iSup_induction G (motive := fun z => ⁅z, v⁆ ∈ M) hu ?_ ?_ ?_
    · intro a z ha
      refine Submodule.iSup_induction G (motive := fun w => ⁅z, w⁆ ∈ M) hv ?_ ?_ ?_
      · intro b w hb
        exact (le_iSup G (a + b))
          ⟨presentationGrade_bracket order ha.1 hb.1,
            delta_bracket_mem_tensorBlock order ha.1 hb.1 ha.2 hb.2⟩
      · rw [lie_zero]
        exact M.zero_mem
      · intro w₁ w₂ h₁ h₂
        rw [lie_add]
        exact M.add_mem h₁ h₂
    · rw [zero_lie]
      exact M.zero_mem
    · intro z₁ z₂ h₁ h₂
      rw [add_lie]
      exact M.add_mem h₁ h₂
  let S : LieSubalgebra ℝ P := { M with lie_mem' := hlie }
  have hgen {a : Weight} {j : Option J} (hj : generator order j ∈ grade a) :
      generator order j ∈ S :=
    (le_iSup G a) ⟨hj, by simp [gradedPresentationDelta_generator]⟩
  have htop : M = ⊤ := by
    have hS := eq_top_of_generators order S fun j => by
      cases j with
      | none => exact hgen (real_mem_presentationGrade order)
      | some j => exact hgen (imaginary_mem_presentationGrade order j)
    exact congrArg LieSubalgebra.toSubmodule hS
  -- Independence recovers equality in each weight from equality of the sums.
  have hindep := (DirectSum.Decomposition.isInternal (ℳ := grade)).submodule_iSupIndep
  have hG : G = grade := (hindep.le_iff_eq_of_iSup_eq_top htop).mp (fun _ => inf_le_left)
  have hx' : x ∈ G p := by rwa [hG]
  exact hx'.2

end D5.S3.VertexAlgebra.MonsterPresentationBracketScalar
