/- GID: D5/S3/Quantum/Analysis/AsynchronousMassRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/AsynchronousMassRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strictly positive asynchronous invariance forces multilinear mass factorization. -/

import Mathlib
import D5.S3.Geometry.FixedPoint.MarkovKakutani
import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation

/-! # Asynchronous maximum principle for multilinear masses -/

namespace D5.S3.Quantum.AsynchronousMassRigidity

open Function Set
open scoped BigOperators

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]
/-- The original normalized base is nonempty, compact, convex and spans the carrier. -/
theorem entire_base_geometry [Nontrivial A] (C : ProperCone ℝ A) (u : Module.Dual ℝ A)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤)
    (hpos : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u).Nonempty ∧
      IsCompact (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u) ∧
      Convex ℝ (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u) ∧
      Submodule.span ℝ (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u) = ⊤ := by
  have hcompact := Foundation.CircuitBalancedConfirmation.base_compact C.isClosed hpos
  have hpure := Foundation.CircuitBalancedConfirmation.pure_span hcompact hpos hgen
  have hspan : Submodule.span ℝ
      (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u) = ⊤ := by
    apply top_unique
    rw [← hpure]
    exact Submodule.span_mono (fun _ hx => hx.1)
  have hne : (Foundation.CircuitBalancedConfirmation.base C.toPointedCone u).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  exact ⟨hne, hcompact,
    Foundation.CircuitBalancedConfirmation.base_convex C.toPointedCone u, hspan⟩

/-- Markov–Kakutani applied to a singleton family gives a fixed point in each nonempty
compact convex invariant set. -/
theorem exists_fixed_mem (Phi : A →ₗ[ℝ] A) {B : Set A}
    (hB : IsCompact B) (hne : B.Nonempty) (hconv : Convex ℝ B)
    (hinv : MapsTo Phi B B) : ∃ x ∈ B, Phi x = x := by
  let T : A →ᴬ[ℝ] A := Phi.toContinuousLinearMap.toContinuousAffineMap
  obtain ⟨x, hx, hfixed⟩ :=
    D5.S3.Geometry.FixedPoint.MarkovKakutani.exists_common_fixed_point
      hne hB hconv (fun _ : Unit => T) (fun _ => hinv) (fun _ _ _ => rfl)
  exact ⟨x, hx, hfixed ()⟩

/-- The full real fixed-dual hypothesis determines every fixed vector from its original mass.
No interior condition on the normalized fixed vector is used. -/
theorem fixed_eq_mass_smul (Phi : A →ₗ[ℝ] A) (u : Module.Dual ℝ A)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    {sigma : A} (hsigma : Phi sigma = sigma) (hu : u sigma = 1)
    {x : A} (hx : Phi x = x) : x = u x • sigma := by
  classical
  let T := Phi - LinearMap.id
  have hdualDim : Module.finrank ℝ (LinearMap.ker T.dualMap) ≤ 1 := by
    let v : LinearMap.ker T.dualMap := ⟨u, by
      apply LinearMap.ext
      intro a
      change u (Phi a - a) = 0
      simp only [map_sub]
      exact sub_eq_zero.mpr (congrArg (fun f : Module.Dual ℝ A => f a) hmass)⟩
    exact finrank_le_one v (by
      intro f
      have hf : (f : Module.Dual ℝ A).comp Phi = f := by
        ext a
        have hz := congrArg (fun g : Module.Dual ℝ A => g a) f.property
        change (f : Module.Dual ℝ A) (Phi a - a) = 0 at hz
        simpa only [map_sub, sub_eq_zero, LinearMap.comp_apply] using hz
      obtain ⟨c, hc⟩ := hdual f hf
      exact ⟨c, Subtype.ext hc.symm⟩)
  have hdim : Module.finrank ℝ (LinearMap.ker T) ≤ 1 := by
    have h₁ := T.finrank_range_add_finrank_ker
    have h₂ := T.dualMap.finrank_range_add_finrank_ker
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₂
    omega
  have hs0 : sigma ≠ 0 := by
    intro hz
    simpa [hz] using hu
  have hline : Submodule.span ℝ {sigma} ≤ LinearMap.ker T := by
    rw [Submodule.span_singleton_le_iff_mem]
    change Phi sigma - sigma = 0
    exact sub_eq_zero.mpr hsigma
  have heq : Submodule.span ℝ {sigma} = LinearMap.ker T :=
    Submodule.eq_of_le_of_finrank_le hline (by
      simpa only [finrank_span_singleton hs0] using hdim)
  have hxmem : x ∈ Submodule.span ℝ {sigma} := by
    rw [heq]
    change Phi x - x = 0
    exact sub_eq_zero.mpr hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
  have hcMass : u x = c := by rw [← hc, map_smul, hu, smul_eq_mul, mul_one]
  simpa only [hcMass] using hc.symm


/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Source: https://github.com/TauCetiProject/TauCeti/blob/66f3330c1cbabafd0f5b3ea4a646c43e23105ee2/TauCeti/Topology/Algebra/Module/FiniteDimension.lean
Original declaration: MultilinearMap.continuous_of_finiteDimensional.
Full license: docs/reports/licenses/TauCeti-LICENSE.txt.
The declaration has private visibility in this owning namespace; its complete
statement and proof are preserved. Attribution and pin correspondence:
docs/reports/licenses/multilinear-continuity-third-party.md.
Retire this transplant when this repository's own lake-manifest.json mathlib rev
supplies an equivalent declaration, replacing both uses by direct application.
-/
section MultilinearContinuity

variable {𝕜 ι : Type*} {M : ι → Type*} {N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Finite ι] [∀ i, AddCommGroup (M i)] [∀ i, Module 𝕜 (M i)] [∀ i, TopologicalSpace (M i)]
  [∀ i, IsTopologicalAddGroup (M i)] [∀ i, ContinuousSMul 𝕜 (M i)] [∀ i, T2Space (M i)]
  [∀ i, FiniteDimensional 𝕜 (M i)] [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul 𝕜 N]

/-- A multilinear map on finitely many finite-dimensional Hausdorff topological vector spaces
over a complete nontrivially normed field is continuous when its codomain is an additive
commutative monoid with continuous addition and scalar multiplication. No bound is required. -/
private theorem continuous_of_finiteDimensional (f : MultilinearMap 𝕜 M N) : Continuous f := by
  classical
  cases nonempty_fintype ι
  set b : ∀ i, Module.Basis (Fin (Module.finrank 𝕜 (M i))) 𝕜 (M i) :=
    fun i ↦ Module.finBasis 𝕜 (M i) with hb
  have key : ⇑f = fun m : ∀ i, M i ↦ ∑ r : ∀ i, Fin (Module.finrank 𝕜 (M i)),
      (∏ i, (b i).repr (m i) (r i)) • f fun i ↦ b i (r i) := by
    funext m
    have hm : f m = f fun i ↦ ∑ j, (b i).repr (m i) j • b i j := by
      congr 1 with i
      exact ((b i).sum_repr (m i)).symm
    rw [hm, f.map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ f.map_smul_univ _ _
  rw [key]
  refine continuous_finsetSum _ fun r _ ↦ Continuous.smul ?_ continuous_const
  refine continuous_finsetProd _ fun i _ ↦ ?_
  exact (((b i).coord (r i)).continuous_of_finiteDimensional.comp
    (continuous_apply i)).congr fun m ↦ Module.Basis.coord_apply _ _ _


end MultilinearContinuity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem weighted_max_eq (alpha : ι → ℝ) (hpos : ∀ i, 0 < alpha i)
    (hsum : ∑ i, alpha i = 1) (v : ι → ℝ) (M : ℝ)
    (hle : ∀ i, v i ≤ M) (hav : ∑ i, alpha i * v i = M) (i : ι) : v i = M := by
  have hz : ∑ j, alpha j * (M - v j) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, hav,
      sub_self]
  have hterm : alpha i * (M - v i) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hpos j).le (sub_nonneg.mpr (hle j)))).mp hz i
        (Finset.mem_univ i)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (hpos i).ne')).symm

/-- A maximizing tuple can be replaced, one coordinate at a time, by the same normalized
fixed vector. The weights are strictly positive; equality is scalar equality at the global maximum. -/
private theorem maximum_at_fixed_tuple (Phi : A →ₗ[ℝ] A) (u : Module.Dual ℝ A)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    {K : Set A} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinv : MapsTo Phi K K) (hnorm : ∀ x ∈ K, u x = 1)
    {sigma : A} (hsigma : sigma ∈ K) (hfixed : Phi sigma = sigma)
    (alpha : ι → ℝ) (hpos : ∀ i, 0 < alpha i) (hsum : ∑ i, alpha i = 1)
    (F : MultilinearMap ℝ (fun _ : ι => A) ℝ)
    (harmonic : ∀ a ∈ Set.pi Set.univ (fun _ : ι => K),
      F a = ∑ i, alpha i * F (Function.update a i (Phi (a i))))
    {a : ι → A} (ha : a ∈ Set.pi Set.univ (fun _ : ι => K))
    (hmax : ∀ b ∈ Set.pi Set.univ (fun _ : ι => K), F b ≤ F a) :
    F (fun _ => sigma) = F a := by
  classical
  let cube : Set (ι → A) := Set.pi Set.univ (fun _ => K)
  have hreplace : ∀ b ∈ cube, F b = F a → ∀ i,
      F (Function.update b i sigma) = F a := by
    intro b hb hba i
    let f := F.toLinearMap b i
    let B := K ∩ {x | f x = F a}
    have hB : IsCompact B := hK.inter_right
      (isClosed_eq f.continuous_of_finiteDimensional continuous_const)
    have hBconv : Convex ℝ B := hconv.inter (by
      intro x hx y hy c d hc hd hcd
      change f x = F a at hx
      change f y = F a at hy
      change f (c • x + d • y) = F a
      simp only [map_add, map_smul, hx, hy, smul_eq_mul]
      rw [← add_mul, hcd, one_mul])
    have hbB : b i ∈ B := ⟨hb i (Set.mem_univ i), by simpa [f] using hba⟩
    have hup (x : A) (hx : x ∈ K) : Function.update b i x ∈ cube := by
      intro j _
      by_cases hji : j = i
      · subst j; simpa using hx
      · simpa [Function.update_of_ne hji] using hb j (Set.mem_univ j)
    have hBinv : MapsTo Phi B B := by
      intro x hx
      refine ⟨hinv hx.1, ?_⟩
      let c := Function.update b i x
      have hc : c ∈ cube := hup x hx.1
      have hcx : F c = F a := hx.2
      have hv (j : ι) : F (Function.update c j (Phi (c j))) ≤ F a := by
        apply hmax
        intro k _
        by_cases hkj : k = j
        · subst k; simpa using hinv (hc j (Set.mem_univ j))
        · simpa [Function.update_of_ne hkj] using hc k (Set.mem_univ k)
      have heq := weighted_max_eq alpha hpos hsum
        (fun j => F (Function.update c j (Phi (c j)))) (F a) hv
        ((harmonic c hc).symm.trans hcx) i
      simpa [f, c, Function.update_idem] using heq
    obtain ⟨x, hx, hxfixed⟩ :=
      exists_fixed_mem Phi hB ⟨b i, hbB⟩ hBconv hBinv
    have heq : x = sigma := by
      simpa only [hnorm x hx.1, one_smul] using
        fixed_eq_mass_smul Phi u hmass hdual
          hfixed (hnorm sigma hsigma) hxfixed
    simpa [heq, f] using hx.2
  have hfinite : ∀ S : Finset ι,
      F (fun i => if i ∈ S then sigma else a i) = F a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa
    | @insert i S hi ih =>
      let b : ι → A := fun j => if j ∈ S then sigma else a j
      have hb : b ∈ cube := by
        intro j _
        dsimp [b]
        split_ifs
        · exact hsigma
        · exact ha j (Set.mem_univ j)
      have he := hreplace b hb ih i
      convert he using 1
      congr 1
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [b, hji, Function.update_of_ne hji]
  simpa using hfinite Finset.univ

/-- Every asynchronous harmonic multilinear form is constant on the entire normalized cube. -/
private theorem constant_on_normalized_cube (Phi : A →ₗ[ℝ] A) (u : Module.Dual ℝ A)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    {K : Set A} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinv : MapsTo Phi K K) (hnorm : ∀ x ∈ K, u x = 1)
    {sigma : A} (hsigma : sigma ∈ K) (hfixed : Phi sigma = sigma)
    (alpha : ι → ℝ) (hpos : ∀ i, 0 < alpha i) (hsum : ∑ i, alpha i = 1)
    (F : MultilinearMap ℝ (fun _ : ι => A) ℝ)
    (harmonic : ∀ a ∈ Set.pi Set.univ (fun _ : ι => K),
      F a = ∑ i, alpha i * F (Function.update a i (Phi (a i)))) :
    ∀ a ∈ Set.pi Set.univ (fun _ : ι => K), F a = F (fun _ => sigma) := by
  classical
  let cube := Set.pi Set.univ (fun _ : ι => K)
  have hc : IsCompact cube := isCompact_univ_pi (fun _ => hK)
  have hn : cube.Nonempty := ⟨fun _ => sigma, fun _ _ => hsigma⟩
  obtain ⟨b, hb, hmax⟩ := hc.exists_isMaxOn hn (continuous_of_finiteDimensional F).continuousOn
  have hm := maximum_at_fixed_tuple Phi u hmass hdual hK hconv hinv hnorm hsigma hfixed
    alpha hpos hsum F harmonic hb hmax
  have hneg : ∀ a ∈ cube,
      (-F) a = ∑ i, alpha i * (-F) (Function.update a i (Phi (a i))) := by
    intro a ha
    simpa only [MultilinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib] using
      congrArg Neg.neg (harmonic a ha)
  obtain ⟨c, hc', hmin⟩ := hc.exists_isMaxOn hn (continuous_of_finiteDimensional F).neg.continuousOn
  have hnmin := maximum_at_fixed_tuple Phi u hmass hdual hK hconv hinv hnorm hsigma hfixed
    alpha hpos hsum (-F) hneg hc' hmin
  intro a ha
  apply le_antisymm
  · have hz : F a ≤ F b := hmax ha
    exact hz.trans_eq hm.symm
  · have hz : -F a ≤ -F c := hmin ha
    have heq : F (fun _ => sigma) = F c := neg_injective hnmin
    rw [← heq] at hz
    exact neg_le_neg_iff.mp hz

private theorem eq_zero_of_spanning_cube {K : Set A} (hspan : Submodule.span ℝ K = ⊤)
    (G : MultilinearMap ℝ (fun _ : ι => A) ℝ)
    (hzero : ∀ a, (∀ i, a i ∈ K) → G a = 0) : G = 0 := by
  apply MultilinearMap.ext_of_span_eq_top (g := fun {i : ι} (x : K) => (x : A))
    (fun _ => by simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq] using hspan)
  intro a
  exact hzero (fun i => a i) (fun i => (a i).property)

/-- The normalized-cube identity extends to all real inputs, using the span of the entire
state base; no tensor cone, copies, mixing, or interior stationary state is assumed. -/
theorem multilinear_mass_factorization (Phi : A →ₗ[ℝ] A) (u : Module.Dual ℝ A)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    {K : Set A} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hspan : Submodule.span ℝ K = ⊤) (hinv : MapsTo Phi K K)
    (hnorm : ∀ x ∈ K, u x = 1)
    (alpha : ι → ℝ) (hpos : ∀ i, 0 < alpha i) (hsum : ∑ i, alpha i = 1)
    (F : MultilinearMap ℝ (fun _ : ι => A) ℝ)
    (harmonic : ∀ a ∈ Set.pi Set.univ (fun _ : ι => K),
      F a = ∑ i, alpha i * F (Function.update a i (Phi (a i)))) :
    ∃ c : ℝ, ∀ a : ι → A, F a = c * ∏ i, u (a i) := by
  classical
  obtain ⟨sigma, hsigma, hfixed⟩ :=
    exists_fixed_mem Phi hK hne hconv hinv
  let c := F (fun _ => sigma)
  let P : MultilinearMap ℝ (fun _ : ι => A) ℝ :=
    (MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap (fun _ => u)
  have hdiff : F - c • P = 0 := by
    apply eq_zero_of_spanning_cube hspan
    intro a ha
    have hc := constant_on_normalized_cube Phi u hmass hdual hK hconv hinv hnorm
      hsigma hfixed alpha hpos hsum F harmonic a (fun i _ => ha i)
    simpa [P, hnorm, ha, c, MultilinearMap.mkPiAlgebra_apply] using sub_eq_zero.mpr hc
  refine ⟨c, fun a => ?_⟩
  have heq := congrArg (fun G : MultilinearMap ℝ (fun _ : ι => A) ℝ => G a) hdiff
  simpa [P, MultilinearMap.mkPiAlgebra_apply, sub_eq_zero] using heq

end D5.S3.Quantum.AsynchronousMassRigidity
