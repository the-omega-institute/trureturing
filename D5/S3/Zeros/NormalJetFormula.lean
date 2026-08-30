/- GID: D5/S3/Zeros/NormalJetFormula
   generality: I
   mirror-B: D5/B/S3/Zeros/NormalJetFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the completed-xi normal jets from the actual normal intensity. -/

import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Data.Nat.Choose.Cast

noncomputable section

namespace D5.S3.Zeros.NormalJetFormula

open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
open scoped ComplexConjugate

/-- The real completed-xi reading on the critical line. -/
def criticalXi (t : ℝ) : ℝ :=
  (xiReading ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re

/-- The actual completed-xi intensity after a real normal displacement. -/
def normalIntensity (delta t : ℝ) : ℝ :=
  Complex.normSq
    (xiReading ((1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t : ℂ)))

/-- The even Taylor coefficient of the actual normal intensity at displacement zero. -/
def normalJet (t : ℝ) (m : ℕ) : ℝ :=
  iteratedDeriv (2 * m) (fun delta : ℝ => normalIntensity delta t) 0 /
    ((2 * m).factorial : ℝ)

private def criticalXiExtension (z : ℂ) : ℂ :=
  xiReading ((1 / 2 : ℂ) + Complex.I * z)

private def normalIntensityExtension (t delta : ℂ) : ℂ :=
  criticalXiExtension (t - Complex.I * delta) *
    criticalXiExtension (t + Complex.I * delta)

private theorem criticalXiExtension_contDiff :
    ContDiff ℂ ⊤ criticalXiExtension := by
  have hxi : ContDiff ℂ ⊤ xiReading :=
    (xi_reading_differentiable.differentiableOn.analyticOnNhd isOpen_univ).contDiff
  exact hxi.comp (by fun_prop)

private theorem normalIntensityExtension_contDiff (t : ℂ) :
    ContDiff ℂ ⊤ (normalIntensityExtension t) := by
  unfold normalIntensityExtension
  exact (criticalXiExtension_contDiff.comp (by fun_prop)).mul
    (criticalXiExtension_contDiff.comp (by fun_prop))

private theorem criticalXiExtension_ofReal (t : ℝ) :
    criticalXiExtension t = (criticalXi t : ℂ) := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have hs : 1 - conj s = s := by
    apply Complex.ext <;> simp [s] <;> ring
  have hreal : xiReading s = conj (xiReading s) := by
    simpa [hs] using xi_reading_one_sub_conj s
  have hre : ((xiReading s).re : ℂ) = xiReading s :=
    Complex.conj_eq_iff_re.mp hreal.symm
  simpa [criticalXiExtension, criticalXi, s] using hre.symm

private theorem normalIntensityExtension_ofReal (delta t : ℝ) :
    normalIntensityExtension t delta = (normalIntensity delta t : ℂ) := by
  let s : ℂ := (1 / 2 : ℂ) + (delta : ℂ) + Complex.I * (t : ℂ)
  have hleft :
      (1 / 2 : ℂ) + Complex.I * ((t : ℂ) - Complex.I * (delta : ℂ)) = s := by
    rw [mul_sub, ← mul_assoc, Complex.I_mul_I]
    simp [s]
    ring
  have hright :
      (1 / 2 : ℂ) + Complex.I * ((t : ℂ) + Complex.I * (delta : ℂ)) =
        1 - conj s := by
    apply Complex.ext <;> simp [s] <;> ring
  simp only [normalIntensityExtension, criticalXiExtension]
  rw [hleft, hright,
    xi_reading_one_sub_conj, Complex.mul_conj]
  rfl

private theorem iteratedDeriv_restrict_complex {f : ℂ → ℂ}
    (hf : ContDiff ℂ ⊤ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => f x) =
      fun x : ℝ => iteratedDeriv n f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      exact ((hf.differentiable_iteratedDeriv n (by simp)).differentiableAt.hasDerivAt.comp_ofReal).deriv

private theorem iteratedDeriv_ofReal {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x : ℂ)) =
      fun x : ℝ => ((iteratedDeriv (𝕜 := ℝ) n f x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      exact ((hf.differentiable_iteratedDeriv n (by simp)).differentiableAt.hasDerivAt.ofReal_comp).deriv

private theorem criticalXi_contDiff : ContDiff ℝ ⊤ criticalXi := by
  change ContDiff ℝ ⊤ (fun x : ℝ => (criticalXiExtension x).re)
  exact criticalXiExtension_contDiff.real_of_complex

private theorem criticalXi_derivative_bridge (n : ℕ) (t : ℝ) :
    iteratedDeriv n criticalXiExtension t =
      ((iteratedDeriv n criticalXi t : ℝ) : ℂ) := by
  have hrestrict := congrFun
    (iteratedDeriv_restrict_complex criticalXiExtension_contDiff n) t
  have hfunctions :
      (fun x : ℝ => criticalXiExtension x) =
        fun x : ℝ => (criticalXi x : ℂ) := by
    funext x
    exact criticalXiExtension_ofReal x
  rw [hfunctions] at hrestrict
  have hcast := congrFun (iteratedDeriv_ofReal criticalXi_contDiff n) t
  exact hrestrict.symm.trans hcast

private theorem normalIntensity_contDiff (t : ℝ) :
    ContDiff ℝ ⊤ (fun delta : ℝ => normalIntensity delta t) := by
  have heq :
      (fun delta : ℝ => normalIntensity delta t) =
        fun delta : ℝ => (normalIntensityExtension t delta).re := by
    funext delta
    rw [normalIntensityExtension_ofReal]
    simp
  rw [heq]
  exact (normalIntensityExtension_contDiff t).real_of_complex

private theorem normalIntensity_derivative_bridge (n : ℕ) (t : ℝ) :
    iteratedDeriv n (normalIntensityExtension t) 0 =
      ((iteratedDeriv n (fun delta : ℝ => normalIntensity delta t) 0 : ℝ) : ℂ) := by
  have hrestrict := congrFun
    (iteratedDeriv_restrict_complex (normalIntensityExtension_contDiff t) n) 0
  have hfunctions :
      (fun delta : ℝ => normalIntensityExtension t delta) =
        fun delta : ℝ => (normalIntensity delta t : ℂ) := by
    funext delta
    exact normalIntensityExtension_ofReal delta t
  rw [hfunctions] at hrestrict
  have hcast := congrFun (iteratedDeriv_ofReal (normalIntensity_contDiff t) n) 0
  exact hrestrict.symm.trans hcast

private theorem criticalXi_affine_derivative (n : ℕ) (t c : ℂ) :
    iteratedDeriv n (fun z => criticalXiExtension (t + c * z)) 0 =
      c ^ n * iteratedDeriv n criticalXiExtension t := by
  have hshift : ContDiff ℂ ⊤ (fun z => criticalXiExtension (t + z)) :=
    criticalXiExtension_contDiff.comp (by fun_prop)
  have h := congrFun
    (iteratedDeriv_comp_const_mul (n := n) (hshift.of_le (by simp)) c) 0
  have htranslate := congrFun
    (iteratedDeriv_comp_const_add n criticalXiExtension t) 0
  simp only [mul_zero, add_zero] at h htranslate
  rw [htranslate] at h
  exact h

private theorem phase_product (m j : ℕ) (hj : j ≤ 2 * m) :
    (-Complex.I) ^ j * Complex.I ^ (2 * m - j) =
      (-1 : ℂ) ^ (m + j) := by
  calc
    (-Complex.I) ^ j * Complex.I ^ (2 * m - j) =
        ((-1 : ℂ) * Complex.I) ^ j * Complex.I ^ (2 * m - j) := by ring
    _ = (-1 : ℂ) ^ j *
        (Complex.I ^ j * Complex.I ^ (2 * m - j)) := by rw [mul_pow]; ring
    _ = (-1 : ℂ) ^ j * Complex.I ^ (j + (2 * m - j)) := by rw [pow_add]
    _ = (-1 : ℂ) ^ j * Complex.I ^ (2 * m) := by rw [Nat.add_sub_of_le hj]
    _ = (-1 : ℂ) ^ j * (Complex.I ^ 2) ^ m := by rw [pow_mul]
    _ = (-1 : ℂ) ^ j * (-1 : ℂ) ^ m := by rw [Complex.I_sq]
    _ = (-1 : ℂ) ^ (m + j) := by rw [← pow_add, Nat.add_comm]

private theorem complex_normal_jet_formula (m : ℕ) (t : ℝ) :
    iteratedDeriv (2 * m) (normalIntensityExtension t) 0 /
        ((2 * m).factorial : ℂ) =
      ∑ j ∈ Finset.range (2 * m + 1),
        ((((-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j criticalXi t *
              iteratedDeriv (2 * m - j) criticalXi t : ℝ) : ℂ)) := by
  have hleft : ContDiffAt ℂ (2 * m)
      (fun z => criticalXiExtension ((t : ℂ) - Complex.I * z)) 0 :=
    (criticalXiExtension_contDiff.comp (by fun_prop)).contDiffAt.of_le (by simp)
  have hright : ContDiffAt ℂ (2 * m)
      (fun z => criticalXiExtension ((t : ℂ) + Complex.I * z)) 0 :=
    (criticalXiExtension_contDiff.comp (by fun_prop)).contDiffAt.of_le (by simp)
  change iteratedDeriv (2 * m)
      ((fun z => criticalXiExtension ((t : ℂ) - Complex.I * z)) *
        (fun z => criticalXiExtension ((t : ℂ) + Complex.I * z))) 0 /
        ((2 * m).factorial : ℂ) = _
  rw [iteratedDeriv_mul hleft hright, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hminus :
      iteratedDeriv j
          (fun z => criticalXiExtension ((t : ℂ) - Complex.I * z)) 0 =
        (-Complex.I) ^ j * iteratedDeriv j criticalXiExtension t := by
    simpa only [sub_eq_add_neg, neg_mul] using
      criticalXi_affine_derivative j (t : ℂ) (-Complex.I)
  have hplus := criticalXi_affine_derivative (2 * m - j) (t : ℂ) Complex.I
  rw [hminus, hplus, criticalXi_derivative_bridge, criticalXi_derivative_bridge,
    Nat.cast_choose ℂ hjle]
  calc
    _ = ((-Complex.I) ^ j * Complex.I ^ (2 * m - j)) /
          ((j.factorial : ℂ) * ((2 * m - j).factorial : ℂ)) *
            ((iteratedDeriv (𝕜 := ℝ) j criticalXi t : ℝ) : ℂ) *
              ((iteratedDeriv (𝕜 := ℝ) (2 * m - j) criticalXi t : ℝ) : ℂ) := by
        field_simp [Nat.factorial_ne_zero]
    _ = (-1 : ℂ) ^ (m + j) /
          ((j.factorial : ℂ) * ((2 * m - j).factorial : ℂ)) *
            ((iteratedDeriv (𝕜 := ℝ) j criticalXi t : ℝ) : ℂ) *
              ((iteratedDeriv (𝕜 := ℝ) (2 * m - j) criticalXi t : ℝ) : ℂ) := by
        rw [phase_product m j hjle]
    _ = _ := by
      push_cast
      rfl

/-- The Taylor coefficient formula for the actual completed-xi normal intensity, together with
its first three coefficients and the real second-normal-derivative identity. -/
theorem normal_jet_formula (t : ℝ) :
    (∀ m : ℕ,
      normalJet t m =
        ∑ j ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j criticalXi t *
              iteratedDeriv (2 * m - j) criticalXi t) ∧
    normalJet t 0 = criticalXi t ^ 2 ∧
    normalJet t 1 =
      iteratedDeriv 1 criticalXi t ^ 2 -
        criticalXi t * iteratedDeriv 2 criticalXi t ∧
    normalJet t 2 =
      (1 / 4 : ℝ) * iteratedDeriv 2 criticalXi t ^ 2 -
        (1 / 3 : ℝ) * iteratedDeriv 1 criticalXi t * iteratedDeriv 3 criticalXi t +
          (1 / 12 : ℝ) * criticalXi t * iteratedDeriv 4 criticalXi t ∧
    iteratedDeriv 2 (fun delta : ℝ => normalIntensity delta t) 0 / 2 =
      iteratedDeriv 1 criticalXi t ^ 2 -
        criticalXi t * iteratedDeriv 2 criticalXi t := by
  have hformula : ∀ m : ℕ,
      normalJet t m =
        ∑ j ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (m + j) /
              ((j.factorial : ℝ) * ((2 * m - j).factorial : ℝ)) *
            iteratedDeriv j criticalXi t *
              iteratedDeriv (2 * m - j) criticalXi t := by
    intro m
    unfold normalJet
    apply Complex.ofReal_injective
    rw [Complex.ofReal_div, Complex.ofReal_sum,
      ← normalIntensity_derivative_bridge]
    exact complex_normal_jet_formula m t
  refine ⟨hformula, ?_, ?_, ?_, ?_⟩
  · simpa [pow_two] using hformula 0
  · have h := hformula 1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    simp only [iteratedDeriv_one] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := hformula 2
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    simp only [iteratedDeriv_one] at h ⊢
    ring_nf at h ⊢
    exact h
  · change normalJet t 1 = _
    have h := hformula 1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    simp only [iteratedDeriv_one] at h ⊢
    ring_nf at h ⊢
    exact h

end D5.S3.Zeros.NormalJetFormula
