/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentEffectClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentEffectClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first-event effect spaces of a general instrument stabilize within d squared steps and are invariant under the dual no-click map. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure

open Matrix
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

variable {d : ℕ} {α ι ξ : Type} [Fintype α] [Fintype ι] [DecidableEq ξ]

/-- The click effect `B_x = ∑_{lab i = x} L_iᴴ L_i` of the readable outcome `x`. -/
def clickEffect (L : ι → Matrix (Fin d) (Fin d) ℂ) (lab : ι → ξ) (x : ξ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => lab i = x), (L i)ᴴ * L i

/-- The real effect space `𝒱_N = span_ℝ({I} ∪ {𝒜ⁿ(B_x) : n < N, x})` of the first `N` rounds. -/
noncomputable def effectSpace (Q : α → Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (lab : ι → ξ) (N : ℕ) : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  Submodule.span ℝ ({1} ∪ {X | ∃ n < N, ∃ x, X = (noClickDual Q)^[n] (clickEffect L lab x)})

/-- **Finite closure of the first-event effect spaces.** For no-click Kraus operators `Q_a`, click
Kraus operators `L_i` with readable labels `lab i`, and `∑ₐ Q_aᴴ Q_a + ∑ᵢ L_iᴴ L_i = I` on `ℂᵈ`
with `d ≥ 1`, there is `N* ∈ [1, d²]` such that the real effect spaces satisfy `𝒱_N = 𝒱_{N*}` for
all `N ≥ N*`, and `𝒱_{N*}` is invariant under the dual no-click map `𝒜`. -/
theorem effectSpace_closure (hd : 1 ≤ d) (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (lab : ι → ξ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1) :
    ∃ Nstar : ℕ, 1 ≤ Nstar ∧ Nstar ≤ d ^ 2 ∧
      (∀ N, Nstar ≤ N → effectSpace Q L lab N = effectSpace Q L lab Nstar) ∧
      ∀ X ∈ effectSpace Q L lab Nstar, noClickDual Q X ∈ effectSpace Q L lab Nstar := by
  classical
  -- the dual map as a real-linear map
  let A : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := noClickDual Q
      map_add' := fun X Y => by
        simp only [noClickDual, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        simp only [noClickDual, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ X, A X = noClickDual Q X := fun X => rfl
  let V := effectSpace Q L lab
  have hgen : ∀ N, V N = Submodule.span ℝ
      ({1} ∪ {X | ∃ n < N, ∃ x, X = (noClickDual Q)^[n] (clickEffect L lab x)}) := fun N => rfl
  -- monotonicity
  have hmono : ∀ M N, M ≤ N → V M ≤ V N := by
    intro M N hMN
    rw [hgen, hgen]
    refine Submodule.span_mono (Set.union_subset_union_right _ ?_)
    rintro X ⟨n, hn, x, rfl⟩
    exact ⟨n, lt_of_lt_of_le hn hMN, x, rfl⟩
  have h1mem : ∀ N, (1 : Matrix (Fin d) (Fin d) ℂ) ∈ V N := fun N =>
    Submodule.subset_span (Or.inl rfl)
  have hBmem : ∀ N n, n < N → ∀ x, (noClickDual Q)^[n] (clickEffect L lab x) ∈ V N :=
    fun N n hn x => Submodule.subset_span (Or.inr ⟨n, hn, x, rfl⟩)
  -- `𝒜(I) = I - ∑ₓ B_x` lies in `𝒱₁`
  have hA1 : noClickDual Q 1 ∈ V 1 := by
    have hsum : noClickDual Q 1 = 1 - ∑ x ∈ Finset.univ.image lab, clickEffect L lab x := by
      have hfib : ∑ x ∈ Finset.univ.image lab, clickEffect L lab x = ∑ i, (L i)ᴴ * L i := by
        simp only [clickEffect]
        exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem lab
          (Finset.mem_univ i)) _
      simp only [noClickDual, Matrix.mul_one]
      rw [hfib]
      exact eq_sub_of_add_eq hcomp
    rw [hsum]
    exact Submodule.sub_mem _ (h1mem 1)
      (Submodule.sum_mem _ fun x _ => by simpa using hBmem 1 0 Nat.one_pos x)
  -- the recursion `𝒱_{N+1} = 𝒱₁ ⊔ 𝒜(𝒱_N)`
  have hrec : ∀ N, V (N + 1) = V 1 ⊔ (V N).map A := by
    intro N
    apply le_antisymm
    · rw [hgen]
      refine Submodule.span_le.mpr ?_
      rintro X (rfl | ⟨n, hn, x, rfl⟩)
      · exact Submodule.mem_sup_left (h1mem 1)
      · rcases n with _ | m
        · exact Submodule.mem_sup_left (by simpa using hBmem 1 0 Nat.one_pos x)
        · refine Submodule.mem_sup_right ⟨(noClickDual Q)^[m] (clickEffect L lab x),
            hBmem N m (by omega) x, ?_⟩
          rw [hA, Function.iterate_succ_apply']
    · refine sup_le (hmono 1 (N + 1) (by omega)) ?_
      rw [hgen N, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨X, (rfl | ⟨n, hn, x, rfl⟩), rfl⟩
      · rw [hA]; exact hmono 1 (N + 1) (by omega) hA1
      · rw [hA, ← Function.iterate_succ_apply' (noClickDual Q)]
        exact hBmem (N + 1) (n + 1) (by omega) x
  -- one equality persists
  have hprop : ∀ k, V (k + 1) = V k → ∀ m, V (k + m) = V k := by
    intro k hk m
    induction m with
    | zero => rfl
    | succ m ih => rw [← add_assoc, hrec, ih, ← hrec, hk]
  -- every effect in `𝒱_N` is Hermitian
  have hherm : ∀ N, ∀ X ∈ V N, Xᴴ = X := by
    intro N X hX
    rw [hgen] at hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        rcases hX with rfl | ⟨n, -, x, rfl⟩
        · exact conjTranspose_one
        · induction n with
          | zero =>
              simp only [Function.iterate_zero, id, clickEffect, conjTranspose_sum,
                conjTranspose_mul, conjTranspose_conjTranspose]
          | succ n ih =>
              rw [Function.iterate_succ_apply']
              simp only [noClickDual, conjTranspose_sum, conjTranspose_mul,
                conjTranspose_conjTranspose, ih, Matrix.mul_assoc]
    | zero => exact conjTranspose_zero
    | add X Y _ _ hX hY => rw [conjTranspose_add, hX, hY]
    | smul r X _ hX =>
        rw [conjTranspose_smul, hX]
        congr 1
  -- every effect space lies in the Hermitian matrices, of real dimension `d²`
  have hdim : ∀ N, Module.finrank ℝ (V N) ≤ d ^ 2 := by
    intro N
    have hle : V N ≤ D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d := by
      intro X hX
      change X ∈ selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
      exact hherm N X hX
    calc Module.finrank ℝ (V N)
        ≤ Module.finrank ℝ (D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d) :=
          Submodule.finrank_mono hle
      _ = d ^ 2 := D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank d
  -- stabilization within `d²` steps: the ranks of `𝒱_{n+1}` are monotone and bounded by `d²`
  have hexists : ∃ k, 1 ≤ k ∧ k ≤ d ^ 2 ∧ V (k + 1) = V k := by
    have hV1 : 1 ≤ Module.finrank ℝ (V 1) := by
      refine Nat.one_le_iff_ne_zero.mpr fun h => ?_
      have h1 := h1mem 1
      rw [Submodule.finrank_eq_zero.mp h, Submodule.mem_bot] at h1
      have : (1 : Matrix (Fin d) (Fin d) ℂ) ⟨0, hd⟩ ⟨0, hd⟩ = 0 := by rw [h1]; rfl
      simp at this
    obtain ⟨m, hm, hmeq⟩ :=
      D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate.bounded_monotone_has_equal_step
        (fun n => Module.finrank ℝ (V (n + 1))) (d ^ 2)
        (fun a b hab => Submodule.finrank_mono (hmono (a + 1) (b + 1) (by omega)))
        (fun n => hdim (n + 1))
    have hm' : m ≤ d ^ 2 - Module.finrank ℝ (V 1) := hm
    have hV1d := hdim 1
    refine ⟨m + 1, by omega, by omega, ?_⟩
    exact (Submodule.eq_of_le_of_finrank_eq (hmono (m + 1) (m + 1 + 1) (by omega)) hmeq).symm
  obtain ⟨k, hk1, hkd, hk⟩ := hexists
  refine ⟨k, hk1, hkd, fun N hN => ?_, fun X hX => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact hprop k hk m
  · change noClickDual Q X ∈ V k
    rw [← hk, hrec]
    exact Submodule.mem_sup_right ⟨X, hX, rfl⟩

#print axioms effectSpace_closure

end D5.S3.Quantum.Measurement.GeneralInstrumentEffectClosure
