/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedPairingComparison
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedPairingComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graded duality and comparison of forms on the negative twisted Leech module. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNegativeTwistedSchur
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Graded comparison of bilinear forms for the actual fixed modes on the negative twisted slice. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedPairingComparison

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open OriginalOrbifoldConformal (conformalVector L L_fixed_apply L_zero_twisted)
open OriginalOrbifoldField (Carrier)
open OriginalOrbifoldLowSpectrum (actual_leech_positive_integral_grading)
open OriginalOrbifoldNegativeTwistedIrreducible (NegativeTwisted negative_twisted_irreducible)
open OriginalOrbifoldNegativeTwistedSchur (negative_twisted_mode_end_eq_smul)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedModeMorphisms (fixedModeHom fixedParity_conformal_mode_val)
open Module.End (mem_eigenspace_iff)
open scoped DirectSum VertexOperator

noncomputable section

local notation "hu" => And.left (And.right leech_spec)
local notation "hD" => And.left (And.right (And.right leech_spec))
local notation "mode[" a "," n "]" => (fixedParityY leechData hu (-1) a)[[n]]
local notation "twistedL0" => mode[Prod.fst (conformalVector leechData hu), 1]
local notation "weight[" n "]" => Module.End.eigenspace twistedL0 (n : ℂ)

set_option maxHeartbeats 1200000 in
-- Transporting the conformal mode compares the nested Leech parity and energy subtypes.
private theorem negativeTwistedGrading :
    DirectSum.IsInternal (fun n : ℕ => weight[n]) ∧
      ∀ n : ℕ, FiniteDimensional ℂ (weight[n]) := by
  classical
  let ambientL0 := L leechData hu hD 0
  have hgrading := actual_leech_positive_integral_grading
  change DirectSum.IsInternal (fun n : ℕ => ambientL0.eigenspace (n : ℂ)) ∧
    _ ∧ (∀ μ : ℂ, FiniteDimensional ℂ (ambientL0.eigenspace μ)) at hgrading
  let proj := LinearMap.snd ℂ (FixedCarrier leechData) NegativeTwisted
  have proj_L0 (v : Carrier leechData hu) : proj (ambientL0 v) = twistedL0 (proj v) := by
    apply Subtype.ext
    exact (L_zero_twisted leechData hu hD v).trans
      (fixedParity_conformal_mode_val (-1) (proj v)).symm
  have proj_weight (n : ℕ) : (ambientL0.eigenspace (n : ℂ)).map proj ≤ weight[n] := by
    rintro _ ⟨v, hv, rfl⟩
    apply mem_eigenspace_iff.mpr
    rw [← proj_L0, mem_eigenspace_iff.mp hv, map_smul]
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_, ?_⟩
  · exact (Module.End.eigenspaces_iSupIndep twistedL0).comp
      (f := fun n : ℕ => (n : ℂ)) Nat.cast_injective
  · apply top_unique
    calc
      ⊤ = (⨆ n : ℕ, ambientL0.eigenspace (n : ℂ)).map proj := by
        rw [hgrading.1.submodule_iSup_eq_top, Submodule.map_top]
        have surj : Function.Surjective proj := fun x => ⟨(0, x), rfl⟩
        exact (LinearMap.range_eq_top.mpr surj).symm
      _ = ⨆ n : ℕ, (ambientL0.eigenspace (n : ℂ)).map proj := Submodule.map_iSup _ _
      _ ≤ ⨆ n : ℕ, weight[n] := iSup_mono proj_weight
  · intro n
    let incl := LinearMap.inr ℂ (FixedCarrier leechData) NegativeTwisted
    let inclWeight : weight[n] →ₗ[ℂ] ambientL0.eigenspace (n : ℂ) :=
      (incl.comp (weight[n]).subtype).codRestrict _ (by
        intro x
        apply mem_eigenspace_iff.mpr
        apply Prod.ext
        · apply Subtype.ext
          change (L leechData hu hD 0 (0, x.val)).1.val = (n : ℂ) • (0 : FixedCarrier leechData).val
          rw [L_fixed_apply]
          simp
        · change proj (ambientL0 (0, x.val)) = (n : ℂ) • x.val
          exact (proj_L0 (0, x.val)).trans
            ((mem_eigenspace_iff (f := twistedL0)).mp x.property))
    let : FiniteDimensional ℂ (ambientL0.eigenspace (n : ℂ)) := hgrading.2.2 (n : ℂ)
    apply FiniteDimensional.of_injective inclWeight
    intro x y h
    exact Subtype.ext (congrArg (fun v : ambientL0.eigenspace (n : ℂ) => proj v.val) h)

private theorem linearMap_ext_of_grades {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (G : ℕ → Submodule ℂ V) (hG : DirectSum.IsInternal G)
    {f g : V →ₗ[ℂ] W} (agree : ∀ i (x : G i), f x = g x) : f = g := by
  apply LinearMap.ext_on
    (s := ⋃ i, (G i : Set V)) (by simpa [Submodule.span_iUnion] using hG.submodule_iSup_eq_top)
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact agree i ⟨x, hi⟩

/-- A left-nondegenerate form identifies each finite grade with its dual.
Taking the inverse on each grade gives an endomorphism that represents the
second form against the first one. -/
private theorem exists_comparison_of_graded {V : Type*} [AddCommGroup V] [Module ℂ V]
    (G : ℕ → Submodule ℂ V) (hG : DirectSum.IsInternal G)
    (hfinite : ∀ i, FiniteDimensional ℂ (G i))
    (B B₀ : LinearMap.BilinForm ℂ V) (hinj : Function.Injective B₀)
    (hB : ∀ i j : ℕ, i ≠ j → ∀ (x : G i) (y : G j), B x y = 0)
    (hB₀ : ∀ i j : ℕ, i ≠ j → ∀ (x : G i) (y : G j), B₀ x y = 0) :
    ∃ A : Module.End ℂ V, LinearMap.comp B₀ A = B := by
  classical
  have restrict_injective (i : ℕ) : Function.Injective (B₀.restrict (G i)) := by
    intro x x' hx
    apply Subtype.ext
    apply hinj
    apply linearMap_ext_of_grades G hG
    intro j y
    by_cases hij : i = j
    · subst j
      exact LinearMap.congr_fun hx y
    · exact (hB₀ i j hij x y).trans (hB₀ i j hij x' y).symm
  let gradeDual (i : ℕ) : G i ≃ₗ[ℂ] Module.Dual ℂ (G i) := by
    letI := hfinite i
    exact LinearEquiv.ofInjectiveOfFinrankEq (B₀.restrict (G i)) (restrict_injective i)
      Subspace.dual_finrank_eq.symm
  let compareGrade (i : ℕ) : Module.End ℂ (G i) :=
    (gradeDual i).symm.toLinearMap.comp (B.restrict (G i))
  let assemble := LinearEquiv.ofBijective (DirectSum.coeLinearMap G) hG
  let A : Module.End ℂ V :=
    (DirectSum.toModule ℂ ℕ V (fun i => (G i).subtype.comp (compareGrade i))).comp
      assemble.symm.toLinearMap
  have onGrade (i : ℕ) (x : G i) : A x = (compareGrade i x).val := by
    have hx : assemble (DirectSum.lof ℂ ℕ (fun i => ↥(G i)) i x) = x :=
      DirectSum.coeLinearMap_lof G i x
    change DirectSum.toModule ℂ ℕ V _ (assemble.symm x) = _
    rw [← hx, assemble.symm_apply_apply, DirectSum.toModule_lof]
    rfl
  refine ⟨A, ?_⟩
  apply linearMap_ext_of_grades G hG
  intro i x
  apply linearMap_ext_of_grades G hG
  intro j y
  change B₀ (A x) y = B x y
  rw [onGrade]
  by_cases hij : i = j
  · subst j
    exact LinearMap.congr_fun ((gradeDual i).apply_symm_apply (B.restrict (G i) x)) y
  · exact (hB₀ i j hij (compareGrade i x) y).trans (hB i j hij x y).symm

set_option maxHeartbeats 1200000 in
-- The commutant and form types elaborate over the concrete Leech parity subtype.
/-- Grade-orthogonal bilinear forms on the actual negative twisted Leech module
with the same adjoints for all fixed modes are related by a unique scalar if
the reference form is nonzero. -/
theorem negative_twisted_pairing_eq_smul
    (B B₀ : LinearMap.BilinForm ℂ NegativeTwisted)
    (opposite : FixedCarrier leechData → ℤ → Module.End ℂ NegativeTwisted)
    (hB₀ne : B₀ ≠ 0)
    (hB : ∀ i j : ℕ, i ≠ j → ∀ (x : weight[i]) (y : weight[j]), B x y = 0)
    (hB₀ : ∀ i j : ℕ, i ≠ j → ∀ (x : weight[i]) (y : weight[j]), B₀ x y = 0)
    (hAdj : ∀ a n (x y : NegativeTwisted), B (mode[a, n] x) y = B x (opposite a n y))
    (hAdj₀ : ∀ a n (x y : NegativeTwisted), B₀ (mode[a, n] x) y = B₀ x (opposite a n y)) :
    ∃! c : ℂ, B = c • B₀ := by
  have stable (a : FixedCarrier leechData) (n : ℤ) (x : NegativeTwisted)
      (hx : x ∈ B₀.ker) : mode[a, n] x ∈ B₀.ker := by
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    simp only [hAdj₀, LinearMap.mem_ker.mp hx, LinearMap.zero_apply]
  have hinj : Function.Injective B₀ := LinearMap.ker_eq_bot.mp
    ((negative_twisted_irreducible B₀.ker stable).resolve_right
      (fun h => hB₀ne (LinearMap.ker_eq_top.mp h)))
  obtain ⟨A, hA⟩ := exists_comparison_of_graded (fun n => weight[n])
    negativeTwistedGrading.1 negativeTwistedGrading.2 B B₀ hinj hB hB₀
  have compare (x y : NegativeTwisted) : B₀ (A x) y = B x y :=
    LinearMap.congr_fun (LinearMap.congr_fun hA x) y
  have commute : A ∈ fixedModeHom (-1) (-1) := by
    intro a n x
    apply hinj
    apply LinearMap.ext
    intro y
    calc
      B₀ (A (mode[a, n] x)) y = B (mode[a, n] x) y := compare _ _
      _ = B x (opposite a n y) := hAdj a n x y
      _ = B₀ (A x) (opposite a n y) := (compare _ _).symm
      _ = B₀ (mode[a, n] (A x)) y := (hAdj₀ a n (A x) y).symm
  obtain ⟨c, hc, _⟩ := negative_twisted_mode_end_eq_smul ⟨A, commute⟩
  have hscalar : B = c • B₀ := by
    apply LinearMap.ext
    intro x
    change B x = c • B₀ x
    have hx : A x = c • x := LinearMap.congr_fun hc x
    calc
      B x = B₀ (A x) := (LinearMap.congr_fun hA x).symm
      _ = B₀ (c • x) := congrArg (fun v : NegativeTwisted => B₀ v) hx
      _ = c • B₀ x := map_smul B₀ c x
  exact ⟨c, hscalar, fun d hd => smul_left_injective ℂ hB₀ne (hd.symm.trans hscalar)⟩

set_option pp.proofs true in
#check @negative_twisted_pairing_eq_smul
#print axioms negative_twisted_pairing_eq_smul

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedPairingComparison
