/- GID: D5/S3/Entropy/TriangleFourSymbolNecessity
   generality: G
   mirror-B: D5/B/S3/Entropy/TriangleFourSymbolNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite incident stochastic laws and support-exact common-record recovery on the original sources. -/

import Mathlib
import D5.S3.Divergence.ClassicalDPI
import D5.S3.Entropy.MaxEntropy

namespace D5.S3.Entropy.TriangleFourSymbolNecessity

open scoped BigOperators

/-- The original finite source law and the three incident stochastic kernels.
No source independence, source-cardinality bound, or strict positivity is imposed. -/
structure IncidentLaw (S₁ S₂ S₃ O : Type*)
    [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype O] where
  nu : S₁ × S₂ × S₃ → ℝ
  nu_nonneg : ∀ s, 0 ≤ nu s
  nu_sum : ∑ s, nu s = 1
  KA : S₂ → S₃ → O → ℝ
  KB : S₃ → S₁ → O → ℝ
  KC : S₁ → S₂ → O → ℝ
  KA_nonneg : ∀ s₂ s₃ x, 0 ≤ KA s₂ s₃ x
  KB_nonneg : ∀ s₃ s₁ x, 0 ≤ KB s₃ s₁ x
  KC_nonneg : ∀ s₁ s₂ x, 0 ≤ KC s₁ s₂ x
  KA_sum : ∀ s₂ s₃, ∑ x, KA s₂ s₃ x = 1
  KB_sum : ∀ s₃ s₁, ∑ x, KB s₃ s₁ x = 1
  KC_sum : ∀ s₁ s₂, ∑ x, KC s₁ s₂ x = 1

variable {S₁ S₂ S₃ O : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype O]

namespace IncidentLaw

/-- The six-variable law, with the original three source slots retained. -/
noncomputable def responseLaw (L : IncidentLaw S₁ S₂ S₃ O)
    (s : S₁ × S₂ × S₃) (a b c : O) : ℝ :=
  L.nu s * L.KA s.2.1 s.2.2 a * L.KB s.2.2 s.1 b * L.KC s.1 s.2.1 c

/-- Finite almost-sure agreement: every off-diagonal cell of the response law is zero. -/
def Agreement (L : IncidentLaw S₁ S₂ S₃ O) : Prop :=
  ∀ s a b c, (a ≠ b ∨ b ≠ c) → L.responseLaw s a b c = 0

/-- The actual joint law of the first output and all original sources. -/
noncomputable def recordLaw (L : IncidentLaw S₁ S₂ S₃ O)
    (x : O) (s : S₁ × S₂ × S₃) : ℝ :=
  L.nu s * L.KA s.2.1 s.2.2 x

noncomputable def outputLaw (L : IncidentLaw S₁ S₂ S₃ O) (x : O) : ℝ :=
  ∑ s, L.recordLaw x s

noncomputable def marginal₁ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) : ℝ :=
  ∑ s₂, ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def marginal₂ (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) : ℝ :=
  ∑ s₁, ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def marginal₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₃ : S₃) : ℝ :=
  ∑ s₁, ∑ s₂, L.nu (s₁, s₂, s₃)
noncomputable def pair₁₂ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₂ : S₂) : ℝ :=
  ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def pair₁₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₃ : S₃) : ℝ :=
  ∑ s₂, L.nu (s₁, s₂, s₃)
noncomputable def pair₂₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) (s₃ : S₃) : ℝ :=
  ∑ s₁, L.nu (s₁, s₂, s₃)

/-- The KL defect uses the product of the marginals of this very source law. -/
noncomputable def sourceCost (L : IncidentLaw S₁ S₂ S₃ O) : ℝ :=
  D5.S3.Divergence.ClassicalDPI.klDivergence L.nu
    (fun s => L.marginal₁ s.1 * L.marginal₂ s.2.1 * L.marginal₃ s.2.2)

/-- Positive output symbols; unused symbols of the original output type remain present in `L`. -/
def PositiveOutput (L : IncidentLaw S₁ S₂ S₃ O) := {x : O // 0 < L.outputLaw x}

/-- A probability vector on an original source alphabet. -/
def IsProbability {S : Type*} [Fintype S] (q : S → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1

/-- The complete necessity conclusion, including exact active response rows.
Its existence is not assumed by `IncidentLaw`. -/
open Classical in
noncomputable def BinaryBlockConclusion (L : IncidentLaw S₁ S₂ S₃ O) : Prop :=
  Nonempty (L.PositiveOutput ≃ Bool × Bool) ∧
  ∃ h : (Bool × Bool) ≃ L.PositiveOutput,
    ∃ q₁ : Bool → S₁ → ℝ, ∃ q₂ : Bool → S₂ → ℝ, ∃ q₃ : Bool → S₃ → ℝ,
      (∀ b, IsProbability (q₁ b) ∧ IsProbability (q₂ b) ∧ IsProbability (q₃ b)) ∧
      (∀ s, q₁ false s * q₁ true s = 0) ∧
      (∀ s, q₂ false s * q₂ true s = 0) ∧
      (∀ s, q₃ false s * q₃ true s = 0) ∧
      (∀ u v s, L.recordLaw (h (u, v)).val s =
        (1 / 4 : ℝ) * q₁ u s.1 * q₂ v s.2.1 * q₃ (u ^^ v) s.2.2) ∧
      (∀ s₂ s₃, 0 < L.pair₂₃ s₂ s₃ →
        ∃ v w, 0 < q₂ v s₂ ∧ 0 < q₃ w s₃ ∧
          ∀ x, L.KA s₂ s₃ x = if x = (h (v ^^ w, v)).val then 1 else 0) ∧
      (∀ s₃ s₁, 0 < L.pair₁₃ s₁ s₃ →
        ∃ u w, 0 < q₁ u s₁ ∧ 0 < q₃ w s₃ ∧
          ∀ x, L.KB s₃ s₁ x = if x = (h (u, u ^^ w)).val then 1 else 0) ∧
      (∀ s₁ s₂, 0 < L.pair₁₂ s₁ s₂ →
        ∃ u v, 0 < q₁ u s₁ ∧ 0 < q₂ v s₂ ∧
          ∀ x, L.KC s₁ s₂ x = if x = (h (u, v)).val then 1 else 0)

private theorem positive_entry {I : Type*} [Fintype I] (p : I → ℝ)
    (hsum : 0 < ∑ i, p i) : ∃ i, 0 < p i := by
  by_contra! h
  exact (not_lt_of_ge (Finset.sum_nonpos fun i _ => h i)) hsum

/-- A positive source cell admits one common output and forces every coordinate
of each of its three original stochastic rows. -/
open Classical in
 theorem rows_at_positive_source (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (s : S₁ × S₂ × S₃) (hs : 0 < L.nu s) :
    ∃ x : O,
      (∀ y, L.KA s.2.1 s.2.2 y = if y = x then 1 else 0) ∧
      (∀ y, L.KB s.2.2 s.1 y = if y = x then 1 else 0) ∧
      (∀ y, L.KC s.1 s.2.1 y = if y = x then 1 else 0) := by
  classical
  obtain ⟨a, ha⟩ := positive_entry (L.KA s.2.1 s.2.2) (by rw [L.KA_sum]; norm_num)
  obtain ⟨b, hb⟩ := positive_entry (L.KB s.2.2 s.1) (by rw [L.KB_sum]; norm_num)
  obtain ⟨c, hc⟩ := positive_entry (L.KC s.1 s.2.1) (by rw [L.KC_sum]; norm_num)
  have common {a' b' c' : O}
      (ha' : 0 < L.KA s.2.1 s.2.2 a')
      (hb' : 0 < L.KB s.2.2 s.1 b')
      (hc' : 0 < L.KC s.1 s.2.1 c') : a' = b' ∧ b' = c' := by
    by_contra hn
    have hoff : a' ≠ b' ∨ b' ≠ c' := by tauto
    have hz := hagree s a' b' c' hoff
    have hp : 0 < L.responseLaw s a' b' c' :=
      mul_pos (mul_pos (mul_pos hs ha') hb') hc'
    linarith
  obtain ⟨hab, hbc⟩ := common ha hb hc
  subst b; subst c
  have hAz (y : O) (hy : y ≠ a) : L.KA s.2.1 s.2.2 y = 0 := by
    apply le_antisymm _ (L.KA_nonneg _ _ _)
    by_contra! hp
    exact hy (common hp hb hc).1
  have hBz (y : O) (hy : y ≠ a) : L.KB s.2.2 s.1 y = 0 := by
    apply le_antisymm _ (L.KB_nonneg _ _ _)
    by_contra! hp
    exact hy (common ha hp hc).1.symm
  have hCz (y : O) (hy : y ≠ a) : L.KC s.1 s.2.1 y = 0 := by
    apply le_antisymm _ (L.KC_nonneg _ _ _)
    by_contra! hp
    exact hy (common ha hb hp).2.symm
  have hAa : L.KA s.2.1 s.2.2 a = 1 := by
    calc
      _ = ∑ y, L.KA s.2.1 s.2.2 y := (Finset.sum_eq_single a (by simpa using hAz)).symm
      _ = 1 := L.KA_sum _ _
  have hBa : L.KB s.2.2 s.1 a = 1 := by
    calc
      _ = ∑ y, L.KB s.2.2 s.1 y := (Finset.sum_eq_single a (by simpa using hBz)).symm
      _ = 1 := L.KB_sum _ _
  have hCa : L.KC s.1 s.2.1 a = 1 := by
    calc
      _ = ∑ y, L.KC s.1 s.2.1 y := (Finset.sum_eq_single a (by simpa using hCz)).symm
      _ = 1 := L.KC_sum _ _
  refine ⟨a, ?_, ?_, ?_⟩
  · intro y; split_ifs with hy
    · subst y; exact hAa
    · exact hAz y hy
  · intro y; split_ifs with hy
    · subst y; exact hBa
    · exact hBz y hy
  · intro y; split_ifs with hy
    · subst y; exact hCa
    · exact hCz y hy

end IncidentLaw
end D5.S3.Entropy.TriangleFourSymbolNecessity
