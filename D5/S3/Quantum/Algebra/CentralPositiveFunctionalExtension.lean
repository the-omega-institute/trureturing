/- GID: D5/S3/Quantum/Algebra/CentralPositiveFunctionalExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/CentralPositiveFunctionalExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.HahnBanach, mathlib/module/Mathlib.Analysis.Normed.Module.RCLike.Extend, mathlib/module/Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional]
   utility: none
   digest: Positive ambient extensions of a real self-adjoint-subspace functional with norm-additive mass; the ambient product algebra supplies both signs with total unit mass equal to the operator norm. -/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open ComplexOrder

namespace D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private noncomputable def pairMap (X : Submodule ℝ A) : (X × ℝ) →ₗ[ℝ] (A × A) where
  toFun z := ((z.1 : A) + z.2 • (1 : A), -(z.1 : A) + z.2 • (1 : A))
  map_add' a b := by
    ext <;> simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' c a := by
    ext <;> simp [smul_add, smul_neg, smul_smul, mul_comm, mul_left_comm, mul_assoc]

private lemma selfadjoint_pair_norm [Nontrivial A] (x : A) (t : ℝ)
    (hx : IsSelfAdjoint x) :
    ‖(x + t • (1 : A), -x + t • (1 : A))‖ = ‖x‖ + |t| := by
  have hupper : ‖(x + t • (1 : A), -x + t • (1 : A))‖ ≤ ‖x‖ + |t| := by
    rw [Prod.norm_def]
    apply max_le
    · calc
        ‖x + t • (1 : A)‖ ≤ ‖x‖ + ‖t • (1 : A)‖ := norm_add_le _ _
        _ = ‖x‖ + |t| := by simp [norm_smul]
    · calc
        ‖-x + t • (1 : A)‖ ≤ ‖-x‖ + ‖t • (1 : A)‖ := norm_add_le _ _
        _ = ‖x‖ + |t| := by simp [norm_smul]
  obtain ⟨s, hs, hsa⟩ : ∃ s : ℝ, s ∈ spectrum ℝ x ∧ |s| = ‖x‖ := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum x hx with hs | hs
    · exact ⟨‖x‖, hs, abs_of_nonneg (norm_nonneg _)⟩
    · exact ⟨-‖x‖, hs, by simp⟩
  have hsneg : -s ∈ spectrum ℝ (-x) := by
    rw [← spectrum.neg_eq]
    exact Set.mem_neg.mpr (by simpa using hs)
  have hplus : |t + s| ≤ ‖x + t • (1 : A)‖ := by
    have h := spectrum.norm_le_norm_of_mem <|
      (spectrum.add_mem_add_iff (a := x) (r := s) (s := t)).2 hs
    simpa [Algebra.algebraMap_eq_smul_one, add_comm, add_left_comm, add_assoc,
      Real.norm_eq_abs] using h
  have hminus : |t - s| ≤ ‖-x + t • (1 : A)‖ := by
    have h := spectrum.norm_le_norm_of_mem <|
      (spectrum.add_mem_add_iff (a := -x) (r := -s) (s := t)).2 hsneg
    simpa [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, Real.norm_eq_abs] using h
  have habs : |t| + |s| ≤ max |t + s| |t - s| := by
    rcases le_total 0 t with ht | ht <;> rcases le_total 0 s with hs0 | hs0
    · rw [abs_of_nonneg ht, abs_of_nonneg hs0]
      linarith [le_abs_self (t + s), le_max_left |t + s| |t - s|]
    · rw [abs_of_nonneg ht, abs_of_nonpos hs0]
      linarith [le_abs_self (t - s), le_max_right |t + s| |t - s|]
    · rw [abs_of_nonpos ht, abs_of_nonneg hs0]
      linarith [neg_le_abs (t - s), le_max_right |t + s| |t - s|]
    · rw [abs_of_nonpos ht, abs_of_nonpos hs0]
      linarith [neg_le_abs (t + s), le_max_left |t + s| |t - s|]
  apply le_antisymm hupper
  calc
    ‖x‖ + |t| = |s| + |t| := by rw [hsa]
    _ ≤ max |t + s| |t - s| := by simpa [add_comm] using habs
    _ ≤ max ‖x + t • (1 : A)‖ ‖-x + t • (1 : A)‖ := max_le_max hplus hminus
    _ = ‖(x + t • (1 : A), -x + t • (1 : A))‖ := by rw [Prod.norm_def]

private lemma pairMap_norm (X : Submodule ℝ A) (hX : ∀ x : X, IsSelfAdjoint (x : A))
    [Nontrivial A] (z : X × ℝ) :
    ‖pairMap X z‖ = ‖z.1‖ + |z.2| := by
  simpa [pairMap, add_comm] using selfadjoint_pair_norm (z.1 : A) z.2 (hX z.1)

/-- Every bounded real functional on an arbitrary normed self-adjoint subspace has two
bounded positive complex-linear ambient extensions whose total mass is the original operator
norm. The pair carrier is the actual C*-algebra
`A × A`; no completion, finite-dimensional substitution, or normalization is used. -/
theorem exists_positive_extensions_norm_additive
    (X : Submodule ℝ A) (hX : ∀ x : X, IsSelfAdjoint (x : A))
    (φ : StrongDual ℝ X) :
    ∃ ψplus ψminus : A →P[ℂ] ℂ,
      (∀ x : X, φ x = (ψplus (x : A)).re - (ψminus (x : A)).re) ∧
      (ψplus (1 : A)).re + (ψminus (1 : A)).re = ‖φ‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    refine ⟨0, 0, ?_, ?_⟩
    · intro x
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    · have hφ : φ = 0 := by
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        simp [hx]
      simp [hφ]
  · letI := hA
    let J := pairMap X
    have hJnorm (z : X × ℝ) : ‖J z‖ = ‖z.1‖ + |z.2| := pairMap_norm X hX z
    have hJinj : Function.Injective J := by
      intro z w h
      have hz : J (z - w) = 0 := by simpa [map_sub, h]
      have hn := hJnorm (z - w)
      rw [hz, norm_zero] at hn
      have hxnorm : ‖(z - w).1‖ = 0 := by linarith [norm_nonneg (z - w).1, abs_nonneg (z - w).2]
      have htnorm : |(z - w).2| = 0 := by linarith [norm_nonneg (z - w).1, abs_nonneg (z - w).2]
      exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hxnorm))
        (sub_eq_zero.mp (abs_eq_zero.mp htnorm))
    let E : (X × ℝ) ≃ₗ[ℝ] J.range := LinearEquiv.ofInjective J hJinj
    let c : ℝ := ‖φ‖
    have hc : 0 ≤ c := norm_nonneg φ
    let L₀ : (X × ℝ) →ₗ[ℝ] ℝ :=
      φ.toLinearMap.comp (LinearMap.fst ℝ X ℝ) + c • LinearMap.snd ℝ X ℝ
    let Llin := L₀.comp E.symm.toLinearMap
    have hb (z : J.range) : ‖Llin z‖ ≤ c * ‖z‖ := by
      let q := E.symm z
      have hz : ‖z‖ = ‖q.1‖ + |q.2| := by
        have h := hJnorm q
        have heq : J q = (z : A × A) := congrArg Subtype.val (E.apply_symm_apply z)
        rw [heq] at h
        exact h
      change ‖φ q.1 + c * q.2‖ ≤ c * ‖z‖
      calc
        ‖φ q.1 + c * q.2‖ ≤ ‖φ q.1‖ + ‖c * q.2‖ := norm_add_le _ _
        _ ≤ c * ‖q.1‖ + c * |q.2| := by
          apply add_le_add
          · exact φ.le_opNorm q.1
          · simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
        _ = c * ‖z‖ := by rw [hz]; ring
    let L : StrongDual ℝ J.range := Llin.mkContinuous c (by exact hb)
    obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq J.range L
    have hGJ (z : X × ℝ) : G (J z) = φ z.1 + c * z.2 := by
      have h := hG (E z)
      change G (J z) = L₀ (E.symm (E z)) at h
      simpa [L₀] using h
    have hGone : G 1 = c := by
      have hJ1 : J (0, 1) = (1 : A × A) := by ext <;> simp [J, pairMap]
      simpa [hJ1] using hGJ (0, 1)
    have hGnorm : ‖G‖ = c := by
      apply le_antisymm
      · rw [hGn]
        exact Llin.mkContinuous_norm_le hc hb
      · have h := G.le_opNorm (1 : A × A)
        simpa [hGone, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hc] using h
    let K : StrongDual ℂ (A × A) := G.extendRCLike
    have hKnorm : ‖K‖ = c := by simpa [K] using hGnorm
    have hKre : (K (1 : A × A)).re = c := by
      change RCLike.re (G.extendRCLike (𝕜 := ℂ) 1) = c
      rw [StrongDual.re_extendRCLike_apply, hGone]
    have hKone_norm : ‖K (1 : A × A)‖ = c := by
      apply le_antisymm
      · calc ‖K (1 : A × A)‖ ≤ ‖K‖ * ‖(1 : A × A)‖ := K.le_opNorm _
          _ = c := by rw [hKnorm]; simp [Prod.norm_def]
      · have h := Complex.abs_re_le_norm (K (1 : A × A))
        rw [hKre, abs_of_nonneg hc] at h
        exact h
    have hKone : K (1 : A × A) = (c : ℂ) := by
      apply Complex.ext hKre
      apply (Complex.abs_re_eq_norm).mp
      rw [hKre, abs_of_nonneg hc, hKone_norm]
    have hKmono : Monotone K :=
      (ContinuousLinearMap.monotone_iff_opNorm_eq_map_one).2 (by simpa [hKone, hKnorm])
    let Ψ : (A × A) →P[ℂ] ℂ := { __ := K, monotone' := hKmono }
    let i₁ : A →P[ℂ] (A × A) :=
      PositiveContinuousLinearMap.mk₀ (ContinuousLinearMap.inl ℂ A A)
        (by intro a ha; exact ⟨ha, le_rfl⟩)
    let i₂ : A →P[ℂ] (A × A) :=
      PositiveContinuousLinearMap.mk₀ (ContinuousLinearMap.inr ℂ A A)
        (by intro a ha; exact ⟨le_rfl, ha⟩)
    let ψplus := Ψ.comp i₁
    let ψminus := Ψ.comp i₂
    refine ⟨ψplus, ψminus, ?_, ?_⟩
    · intro x
      have hdiff : ψplus (x : A) - ψminus (x : A) = K ((x : A), -(x : A)) := by
        change Ψ ((x : A), 0) - Ψ (0, (x : A)) = K ((x : A), -(x : A))
        rw [← map_sub]
        change K ((x : A) - 0, 0 - (x : A)) = K ((x : A), -(x : A))
        simp
      have hpair : (K ((x : A), -(x : A))).re = φ x := by
        have hreal : G (J (x, 0)) = φ x := by simpa using hGJ (x, 0)
        calc
          (K ((x : A), -(x : A))).re = (K (J (x, 0))).re := by
            congr 1
            simp [J, pairMap]
          _ = G (J (x, 0)) := by
            change RCLike.re (G.extendRCLike (𝕜 := ℂ) (J (x, 0))) = G (J (x, 0))
            exact StrongDual.re_extendRCLike_apply G _
          _ = φ x := hreal
      have h := congrArg Complex.re hdiff
      simpa [Complex.sub_re, hpair] using h.symm
    · have hadd : ψplus (1 : A) + ψminus (1 : A) = K (1 : A × A) := by
        change Ψ ((1 : A), 0) + Ψ (0, (1 : A)) = K (1 : A × A)
        rw [← map_add]
        change K ((1 : A) + 0, 0 + (1 : A)) = K (1 : A × A)
        simp only [add_zero, zero_add, Prod.mk_one_one]
      have h := congrArg Complex.re hadd
      simpa only [Complex.add_re, hKre] using h

end D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension
