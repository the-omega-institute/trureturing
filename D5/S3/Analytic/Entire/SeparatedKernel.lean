/- GID: D5/S3/Analytic/Entire/SeparatedKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/SeparatedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire finite separation, scalar calculus and finite translate-space reconstruction. -/

import D5.S3.Analytic.Entire.TranslationFinite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Finite separation on the complete complex plane and its scalar calculus. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.Entire

/-- At most k entire separated terms. In particular, an entire factor is not
assumed to be a vector in a particular reproducing-kernel Hilbert space. -/
def SeparatedLE (k : ℕ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∃ g h : Fin k → (ℂ → ℂ), (∀ i, Differentiable ℂ (g i)) ∧
    (∀ i, Differentiable ℂ (h i)) ∧ ∀ z w, F z w = ∑ i, g i z * h i w

def FiniteSeparated (F : ℂ → ℂ → ℂ) : Prop := ∃ k, SeparatedLE k F

theorem separated_of_fintype {ι : Type*} [Fintype ι]
    (g h : ι → (ℂ → ℂ)) (hg : ∀ i, Differentiable ℂ (g i))
    (hh : ∀ i, Differentiable ℂ (h i)) :
    SeparatedLE (Fintype.card ι) (fun z w => ∑ i, g i z * h i w) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨fun i => g (e.symm i), fun i => h (e.symm i),
    fun i => hg _, fun i => hh _, ?_⟩
  intro z w
  exact (Equiv.sum_comp e.symm (fun i => g i z * h i w)).symm

theorem SeparatedLE.add {m n : ℕ} {F G : ℂ → ℂ → ℂ}
    (hF : SeparatedLE m F) (hG : SeparatedLE n G) :
    SeparatedLE (m + n) (F + G) := by
  classical
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  obtain ⟨u, v, hu, hv, hG⟩ := hG
  refine ⟨Fin.addCases g u, Fin.addCases h v, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hg j
    · simpa only [Fin.addCases_right] using hu j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hh j
    · simpa only [Fin.addCases_right] using hv j
  · intro z w
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right, Pi.add_apply, hF, hG]

theorem SeparatedLE.const_mul {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F) (c : ℂ) :
    SeparatedLE k (fun z w => c * F z w) := by
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  refine ⟨fun i z => c * g i z, h, fun i => (hg i).const_mul c, hh, ?_⟩
  intro z w
  simp only [hF, Finset.mul_sum, mul_assoc]

theorem SeparatedLE.mul {m n : ℕ} {F G : ℂ → ℂ → ℂ}
    (hF : SeparatedLE m F) (hG : SeparatedLE n G) :
    SeparatedLE (m * n) (F * G) := by
  classical
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  obtain ⟨u, v, hu, hv, hG⟩ := hG
  have hs := separated_of_fintype
    (fun i : Fin m × Fin n => g i.1 * u i.2)
    (fun i : Fin m × Fin n => h i.1 * v i.2)
    (fun i => (hg i.1).mul (hu i.2)) (fun i => (hh i.1).mul (hv i.2))
  have heq : (fun z w => ∑ i : Fin m × Fin n,
      (g i.1 * u i.2) z * (h i.1 * v i.2) w) = F * G := by
    funext z w
    simp only [Fintype.sum_prod_type, Pi.mul_apply, hF, hG, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [Fintype.card_prod, Fintype.card_fin, heq] using hs

theorem finite_separated_const (c : ℂ) : FiniteSeparated (fun _ _ => c) := by
  refine ⟨1, ?_⟩
  simpa using (separated_of_fintype (fun _ : Fin 1 => fun _ : ℂ => c)
    (fun _ : Fin 1 => fun _ : ℂ => (1 : ℂ))
    (fun _ => differentiable_const _) (fun _ => differentiable_const _))

theorem FiniteSeparated.add {F G : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (hG : FiniteSeparated G) : FiniteSeparated (F + G) := by
  obtain ⟨m, hm⟩ := hF
  obtain ⟨n, hn⟩ := hG
  exact ⟨m + n, hm.add hn⟩

theorem FiniteSeparated.mul {F G : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (hG : FiniteSeparated G) : FiniteSeparated (F * G) := by
  obtain ⟨m, hm⟩ := hF
  obtain ⟨n, hn⟩ := hG
  exact ⟨m * n, hm.mul hn⟩

theorem FiniteSeparated.const_mul {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (c : ℂ) : FiniteSeparated (fun z w => c * F z w) := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, hk.const_mul c⟩

theorem FiniteSeparated.sub {F G : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (hG : FiniteSeparated G) : FiniteSeparated (F - G) := by
  convert hF.add (hG.const_mul (-1)) using 1
  funext z w
  simp [sub_eq_add_neg]

theorem FiniteSeparated.pow {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (n : ℕ) : FiniteSeparated (F ^ n) := by
  induction n with
  | zero => exact finite_separated_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

/-- Differentiating in either variable preserves the number of separated terms. -/
theorem SeparatedLE.deriv_left {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F) :
    SeparatedLE k (fun z w => deriv (fun x => F x w) z) := by
  classical
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  refine ⟨fun i => deriv (g i), h, fun i => (hg i).deriv, hh, ?_⟩
  intro z w
  change deriv (fun x => F x w) z = ∑ i, deriv (g i) z * h i w
  have heq : (fun x => F x w) = fun x => ∑ i, g i x * h i w := funext fun x => hF x w
  rw [heq, deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact ((hg i z).hasDerivAt.mul_const (h i w)).deriv
  · intro i _
    exact (hg i z).mul_const (h i w)

theorem SeparatedLE.deriv_right {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F) :
    SeparatedLE k (fun z w => deriv (F z) w) := by
  classical
  obtain ⟨g, h, hg, hh, hF⟩ := hF
  refine ⟨g, fun i => deriv (h i), hg, fun i => (hh i).deriv, ?_⟩
  intro z w
  change deriv (F z) w = ∑ i, g i z * deriv (h i) w
  have heq : F z = fun x => ∑ i, g i z * h i x := funext fun x => hF z x
  rw [heq, deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact ((hh i w).hasDerivAt.const_mul (g i z)).deriv
  · intro i _
    exact (hh i w).const_mul (g i z)

theorem FiniteSeparated.deriv_left {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) : FiniteSeparated (fun z w => deriv (fun x => F x w) z) := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, hk.deriv_left⟩

theorem FiniteSeparated.deriv_right {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) : FiniteSeparated (fun z w => deriv (F z) w) := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, hk.deriv_right⟩

theorem SeparatedLE.linear_precomp {k : ℕ} {F : ℂ → ℂ → ℂ}
    (hF : SeparatedLE k F) (a b : ℂ) :
    SeparatedLE k (fun z w => F (a * z) (b * w)) := by
  obtain ⟨g, h, hg, hh, hsep⟩ := hF
  refine ⟨fun i z => g i (a * z), fun i w => h i (b * w),
    fun i => (hg i).comp (differentiable_id.const_mul a),
    fun i => (hh i).comp (differentiable_id.const_mul b), ?_⟩
  exact fun z w => hsep _ _

theorem FiniteSeparated.linear_precomp {F : ℂ → ℂ → ℂ}
    (hF : FiniteSeparated F) (a b : ℂ) :
    FiniteSeparated (fun z w => F (a * z) (b * w)) := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, hk.linear_precomp a b⟩

/-- Finite separation of the ordinary Hankel kernel bounds the complete
translation span, not merely finitely many sampled translates. -/
theorem finite_translation_space_of_separated_hankel {f : ℂ → ℂ}
    (hF : FiniteSeparated (fun z w => f (z + w))) :
    FiniteDimensional ℂ (translationSpace f) := by
  classical
  obtain ⟨k, g, h, hg, hh, hsep⟩ := hF
  let G : Submodule ℂ (ℂ → ℂ) := Submodule.span ℂ (Set.range g)
  letI : FiniteDimensional ℂ G :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  have hle : translationSpace f ≤ G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change translate t f ∈ G
    have heq : translate t f = ∑ i, h i t • g i := by
      funext z
      simpa only [translate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm] using hsep z t
    rw [heq]
    exact G.sum_mem (fun i _ => G.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

#print axioms finite_translation_space_of_separated_hankel

end D5.S3.Analytic.Entire
