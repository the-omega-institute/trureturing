/- GID: D5/S3/QuantumStates/GNSCompatibleStateExtension
   generality: G
   mirror-B: D5/B/S3/QuantumStates/GNSCompatibleStateExtension
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal]
   utility: none
   digest: Compatible C-star states extend uniquely and yield normalized cyclic completed GNS expectations. -/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder InnerProductSpace
open UniformSpace.Completion

namespace D5.S3.QuantumStates.GNSCompatibleStateExtension

open PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  UniformSpace.Completion.coe' (f.toPreGNS 1)

private theorem cyclicVector_denseRange (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (cyclicVector f)) := by
  have hcoe : DenseRange (fun x : f.PreGNS =>
      (UniformSpace.Completion.coe' x : f.GNS)) :=
    UniformSpace.Completion.denseRange_coe
  have hpre : Function.Surjective (fun a : A => f.toPreGNS a) :=
    f.toPreGNS.surjective
  rw [show (fun a : A => f.gnsStarAlgHom a (cyclicVector f)) =
      (fun a : A => UniformSpace.Completion.coe' (f.toPreGNS a)) by
        funext a
        change f.gnsStarAlgHom a (UniformSpace.Completion.coe' (f.toPreGNS 1)) = _
        simpa [cyclicVector, PositiveLinearMap.leftMulMapPreGNS] using
          (PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe (f := f) (a := a)
            (b := (f.toPreGNS 1)))]
  exact hcoe.comp hpre.denseRange (UniformSpace.Completion.continuous_coe _)

/-- Positivity and normalization give the contractive bound, before extending any tower. -/
private theorem state_bound (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  have hp := f.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a)
  have hpos : 0 ≤ f (star a * a) := f.map_nonneg (star_mul_self_nonneg a)
  have hr : ‖f (star a * a)‖ = (f (star a * a)).re := by
    have he : ((f (star a * a)).re : ℂ) = f (star a * a) := by
      apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hpos).2]
    rw [← he, Complex.norm_real]
    exact abs_of_nonneg (Complex.nonneg_iff.mp hpos).1
  rw [hr] at hp
  rw [hf, norm_one] at hp
  have hp' : (f (star a * a)).re ≤ ‖a‖ * ‖a‖ := by
    simpa [CStarRing.norm_star_mul_self, pow_two] using hp
  have hcs' : ‖f a‖ * ‖f a‖ ≤ (f (star a * a)).re := by
    convert hcs using 1 <;>
      simp [PositiveLinearMap.preGNS_inner_def,
        PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, mul_one, hf,
        RCLike.one_re, map_star, norm_star, PositiveLinearMap.preGNS_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg (f a)) (norm_nonneg a)).mp
  nlinarith [hcs', hp']

/-- The normalized expectation and cyclic orbit in the actual completed GNS Hilbert space. -/
private theorem normalized_gns (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ‖cyclicVector f‖ = 1 ∧
    (∀ a : A, inner ℂ (cyclicVector f) (f.gnsStarAlgHom a (cyclicVector f)) = f a) ∧
    DenseRange (fun a : A => f.gnsStarAlgHom a (cyclicVector f)) := by
  refine ⟨?_, ?_, cyclicVector_denseRange f⟩
  · change ‖((f.toPreGNS 1) : f.GNS)‖ = 1
    rw [UniformSpace.Completion.norm_coe]
    have hs := f.preGNS_norm_sq (f.toPreGNS 1)
    have hr := congrArg Complex.re hs
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, PositiveLinearMap.ofPreGNS_toPreGNS,
      star_one, one_mul, hf, Complex.one_re] at hr
    nlinarith [norm_nonneg (f.toPreGNS 1)]
  · intro a
    change inner ℂ ((f.toPreGNS 1) : f.GNS)
      (f.gnsNonUnitalStarAlgHom a ((f.toPreGNS 1) : f.GNS)) = _
    rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.inner_coe]
    simp [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.leftMulMapPreGNS]

section Tower
variable (S : ℕ → StarSubalgebra ℂ A) (hS : Monotone S)
variable [∀ n, IsClosed (S n : Set A)] [∀ n, PartialOrder (S n)] [∀ n, StarOrderedRing (S n)]
variable (ω : ∀ n, (S n) →ₚ[ℂ] ℂ) (hω : ∀ n, ω n 1 = 1)
variable (hcompat : ∀ n m (hnm : n ≤ m) (a : S n),
  ω m (StarSubalgebra.inclusion (hS hnm) a) = ω n a)

include hS in
private theorem tower_mem (a : ↥(⨆ n, S n)) : ∃ n, (a : A) ∈ S n := by
  have hd : Directed (· ≤ ·) S := hS.directed_le
  have he := StarSubalgebra.coe_iSup_of_directed hd
  have ha : (a : A) ∈ (↑(⨆ n, S n) : Set A) := a.2
  rw [he] at ha
  exact Set.mem_iUnion.mp ha

include hS hcompat in
private theorem tower_agree {a : A} {n m : ℕ} (hn : a ∈ S n) (hm : a ∈ S m) :
    ω n ⟨a,hn⟩ = ω m ⟨a,hm⟩ := by
  have h₁ := hcompat n (max n m) (le_max_left n m) ⟨a,hn⟩
  have h₂ := hcompat m (max n m) (le_max_right n m) ⟨a,hm⟩
  exact h₁.symm.trans h₂

private noncomputable def unionFunctional : ↥(⨆ n, S n) →ₗ[ℂ] ℂ where
  toFun a := ω (Classical.choose (tower_mem S hS a))
    ⟨a, Classical.choose_spec (tower_mem S hS a)⟩
  map_add' a b := by
    let n := Classical.choose (tower_mem S hS a)
    let m := Classical.choose (tower_mem S hS b)
    have ha : (a : A) ∈ S (max n m) := hS (le_max_left n m) (Classical.choose_spec (tower_mem S hS a))
    have hb : (b : A) ∈ S (max n m) := hS (le_max_right n m) (Classical.choose_spec (tower_mem S hS b))
    rw [tower_agree S hS ω hcompat (Classical.choose_spec (tower_mem S hS (a+b))) ((S _).add_mem ha hb)]
    change ω (max n m) (⟨a,ha⟩ + ⟨b,hb⟩) = _
    rw [map_add, tower_agree S hS ω hcompat ha (Classical.choose_spec (tower_mem S hS a)),
      tower_agree S hS ω hcompat hb (Classical.choose_spec (tower_mem S hS b))]
  map_smul' c a := by
    let n := Classical.choose (tower_mem S hS a)
    have ha := Classical.choose_spec (tower_mem S hS a)
    rw [tower_agree S hS ω hcompat (Classical.choose_spec (tower_mem S hS (c • a))) ((S n).smul_mem ha c)]
    exact (ω n).map_smul c ⟨a,ha⟩

include hS hcompat in
private theorem unionFunctional_eq (n : ℕ) (a : S n) :
    unionFunctional S hS ω hcompat ⟨a, le_iSup S n a.2⟩ = ω n a :=
  tower_agree S hS ω hcompat _ a.2

include hS hω hcompat in
/-- Compatible normalized local C-star states extend uniquely to their norm-closed union.
`A` is that closure: density is precisely the closure hypothesis, not a new state axiom. -/
theorem compatible_state_extension
    (hdense : Dense (⋃ n, (S n : Set A))) :
    ∃! f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      (∀ n (a : S n), f a = ω n a) ∧ (∀ a : A, ‖f a‖ ≤ ‖a‖) ∧
      ‖cyclicVector f‖ = 1 ∧
      (∀ a : A, inner ℂ (cyclicVector f) (f.gnsStarAlgHom a (cyclicVector f)) = f a) ∧
      DenseRange (fun a : A => f.gnsStarAlgHom a (cyclicVector f)) := by
  let F := unionFunctional S hS ω hcompat
  let e : ↥(⨆ n, S n) →ₗ[ℂ] A := (⨆ n, S n).toSubalgebra.val.toLinearMap
  have hd : DenseRange e := by
    have he := StarSubalgebra.coe_iSup_of_directed hS.directed_le
    have hr : Set.range e = (↑(⨆ n, S n) : Set A) := by
      ext a; exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun ha => ⟨⟨a,ha⟩,rfl⟩⟩
    simpa [DenseRange, hr, he] using hdense
  have hb : ∀ a, ‖F a‖ ≤ (1:ℝ) * ‖e a‖ := by
    intro a
    exact (state_bound _ (hω _) _).trans_eq (by simp [e])
  let g := F.extendOfNorm e
  have hg (a) : g (e a) = F a := LinearMap.extendOfNorm_eq hd ⟨1,hb⟩ a
  have atStage (n : ℕ) (a : S n) : g a = ω n a := by
    exact (hg ⟨a, le_iSup S n a.2⟩).trans (unionFunctional_eq S hS ω hcompat n a)
  have square : ∀ a : A, 0 ≤ g (star a * a) := by
    apply isClosed_property hd (isClosed_le continuous_const (g.continuous.comp (by fun_prop)))
    intro a
    obtain ⟨n, hn⟩ := tower_mem S hS a
    change 0 ≤ g (star (e a) * e a)
    rw [show star (e a) * e a = ((star (⟨a,hn⟩ : S n) * ⟨a,hn⟩ : S n) : A) from rfl,
      atStage]
    exact (ω n).map_nonneg (star_mul_self_nonneg _)
  let f : A →ₚ[ℂ] ℂ := {
    toLinearMap := g.toLinearMap
    monotone' := by
      intro a b hab
      obtain ⟨c, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hab)
      have hs := square c
      rw [← hc, map_sub] at hs
      exact sub_nonneg.mp hs }
  have hf : f 1 = 1 := (atStage 0 1).trans (hω 0)
  refine ⟨f, ⟨hf, atStage, ?_, normalized_gns f hf⟩, ?_⟩
  · intro a
    change ‖g a‖ ≤ ‖a‖
    simpa using LinearMap.norm_extendOfNorm_apply_le hd 1 hb a
  · intro k hk
    apply PositiveLinearMap.ext
    have heq : (k : A → ℂ) = g := by
      apply hd.equalizer (map_continuous k) g.continuous
      funext a
      obtain ⟨n, hn⟩ := tower_mem S hS a
      exact (hk.2.1 n ⟨a,hn⟩).trans (atStage n ⟨a,hn⟩).symm
    exact congrFun heq
end Tower

#print axioms compatible_state_extension
end D5.S3.QuantumStates.GNSCompatibleStateExtension
