/- GID: D5/S3/Arith/Congruence/PrefixCapacityRealization
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PrefixCapacityRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct a supported probability law realizing forbidden-prefix capacities. -/

import D5.S3.Arith.Congruence.HomogeneousCombCapacity
import D5.S3.Arith.Congruence.RestrictedSpineConstantPotential

/-!
The new inference constructs leaf mass realizing the actual prefixFlow
recursion. It recursively scales the child measures, including the zero-flow
case, and proves every prefix marginal has its prescribed capacity and every
forbidden prefix has zero mass. The existing comb comparison is applied only
after this construction, to bound the normalization denominator.

Repository tree laws, pinned Mathlib finite-sum and tree declarations, the
public Loogle index, and Schroeder's packed and regular tree laws supplied no
arbitrary-capacity realization theorem. This symbolic construction has no
finite-instance, enumeration, checker or numerical-reduction content.
The scalar field is arbitrary, so the same construction yields exact rational
weights suitable for FiniteLaw as well as the real specialization.
-/

open scoped BigOperators
open D5.S3.Arith.Congruence.HomogeneousCombCapacity
open D5.S3.Arith.Congruence.RestrictedSpineConstantPotential (Word)

namespace D5.S3.Arith.Congruence.PrefixCapacityRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual prefix marginal: fix the requested coordinates, then sum all
remaining leaf weights. Prefixes longer than the tree have zero mass. -/
noncomputable def prefixMass {p : ℕ} :
    (n : ℕ) → (Word (Fin p) n → K) → List (Fin p) → K
  | _, μ, [] => ∑ w, μ w
  | 0, _, _ :: _ => 0
  | n + 1, μ, a :: u => prefixMass n (fun w => μ (a, w)) u

/-- Every actual forbidden-prefix tree with positive comb flow admits a
normalized supported leaf law with all the comb-normalized prefix caps. -/
theorem exists_comb_capped_probability
    (p H : ℕ) (hp : 2 ≤ p) (β : ℕ → K) (hβ : ∀ d, 0 ≤ β d)
    (f : List (Fin p) → Bool) (hroot : f [] = false)
    (hlevels : ∀ d < H, forbiddenCount p f (d + 1) ≤ 1)
    (hcomb : 0 < combFlow p H β) :
    ∃ μ : Word (Fin p) H → K,
      (∀ w, 0 ≤ μ w) ∧ (∑ w, μ w) = 1 ∧
      ∀ u : List (Fin p), u.length ≤ H →
        prefixMass H μ u ≤ β u.length / combFlow p H β ∧
        (f u = true → prefixMass H μ u = 0) := by
  classical
  have zeroMass : ∀ n (u : List (Fin p)),
      prefixMass n (fun _ => (0 : K)) u = 0 := by
    intro n
    induction n with
    | zero => intro u; cases u <;> simp [prefixMass]
    | succ n ih => intro u; cases u <;> simp [prefixMass, ih]
  have scale : ∀ n (μ : Word (Fin p) n → K) (u : List (Fin p)) (r : K),
      prefixMass n (fun w => r * μ w) u = r * prefixMass n μ u := by
    intro n
    induction n with
    | zero => intro μ u r; cases u <;> simp [prefixMass]
    | succ n ih =>
        intro μ u r
        cases u with
        | nil => simp [prefixMass, Finset.mul_sum]
        | cons a u => exact ih (fun w => μ (a, w)) u r
  have realize : ∀ n (b : ℕ → K) (g : List (Fin p) → Bool),
      (∀ d, 0 ≤ b d) →
      ∃ μ : Word (Fin p) n → K,
        (∀ w, 0 ≤ μ w) ∧ (∑ w, μ w) = prefixFlow p n b g ∧
        ∀ u : List (Fin p), u.length ≤ n →
          prefixMass n μ u ≤ b u.length ∧
          (g u = true → prefixMass n μ u = 0) := by
    intro n
    induction n with
    | zero =>
        intro b g hb
        refine ⟨fun _ => if g [] then 0 else b 0, ?_, ?_, ?_⟩
        · intro w; split_ifs <;> simp [hb]
        · simp [prefixFlow, Word]
        · intro u hu
          have he : u = [] := by simpa using hu
          subst u
          cases hg : g [] <;> simp [prefixMass, hb]
    | succ n ih =>
        intro b g hb
        by_cases hg : g [] = true
        · refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
          · simp [prefixFlow, hg]
          · intro u _; simp [zeroMass, hb]
        · have hc : ∀ i : Fin p,
              ∃ μ : Word (Fin p) n → K,
                (∀ w, 0 ≤ μ w) ∧
                (∑ w, μ w) = prefixFlow p n (fun d => b (d + 1))
                  (fun u => g (i :: u)) ∧
                ∀ u : List (Fin p), u.length ≤ n →
                  prefixMass n μ u ≤ b (u.length + 1) ∧
                  (g (i :: u) = true → prefixMass n μ u = 0) := by
            intro i
            exact ih _ _ (fun d => hb (d + 1))
          choose μ hμ hmass hprefix using hc
          let S := ∑ i : Fin p,
            prefixFlow p n (fun d => b (d + 1)) (fun u => g (i :: u))
          have hS : 0 ≤ S := by
            apply Finset.sum_nonneg
            intro i _
            rw [← hmass i]
            exact Finset.sum_nonneg (fun w _ => hμ i w)
          by_cases hs : S = 0
          · refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
            · simp only [prefixFlow, hg, Bool.false_eq_true, ↓reduceIte]
              change (∑ _ : Word (Fin p) (n + 1), (0 : K)) = min (b 0) S
              rw [hs, min_eq_right (hb 0)]
              simp
            · intro u _; simp [zeroMass, hb]
          · have hspos : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
            let r := min (b 0) S / S
            have hr0 : 0 ≤ r := div_nonneg (le_min (hb 0) hS) hS
            have hr1 : r ≤ 1 := (div_le_one hspos).2 (min_le_right _ _)
            let ν : Word (Fin p) (n + 1) → K := fun w => r * μ w.1 w.2
            have htotal : (∑ w, ν w) = prefixFlow p (n + 1) b g := by
              change (∑ w : Fin p × Word (Fin p) n, r * μ w.1 w.2) = _
              rw [Fintype.sum_prod_type]
              simp_rw [← Finset.mul_sum, hmass]
              simp only [prefixFlow, hg]
              exact div_mul_cancel₀ _ hs
            refine ⟨ν, fun w => mul_nonneg hr0 (hμ w.1 w.2), htotal, ?_⟩
            intro u hu
            cases u with
            | nil =>
                refine ⟨?_, ?_⟩
                · change (∑ w, ν w) ≤ b 0
                  rw [htotal]
                  simp only [prefixFlow, hg]
                  exact min_le_left _ _
                · intro hbad; exact (hg hbad).elim
            | cons a u =>
                have hul : u.length ≤ n := by simpa using hu
                obtain ⟨hcap, hkill⟩ := hprefix a u hul
                change prefixMass n (fun w => r * μ a w) u ≤ b (u.length + 1) ∧ _
                rw [scale]
                constructor
                · exact (mul_le_mul_of_nonneg_left hcap hr0).trans
                    (mul_le_of_le_one_left (hb (u.length + 1)) hr1)
                · intro hbad
                  change prefixMass n (fun w => r * μ a w) u = 0
                  rw [scale, hkill hbad, mul_zero]
  obtain ⟨ν, hν, htotal, hprefix⟩ := realize H β f hβ
  have hcomparison := comb_le_actual_prefix_flow p H hp β hβ f hroot hlevels
  have hflow : 0 < prefixFlow p H β f := lt_of_lt_of_le hcomb hcomparison
  let μ : Word (Fin p) H → K := fun w => (prefixFlow p H β f)⁻¹ * ν w
  refine ⟨μ, fun w => mul_nonneg (inv_nonneg.mpr hflow.le) (hν w), ?_, ?_⟩
  · dsimp [μ]
    rw [← Finset.mul_sum, htotal, inv_mul_cancel₀ hflow.ne']
  · intro u hu
    obtain ⟨hcap, hkill⟩ := hprefix u hu
    change prefixMass H (fun w => (prefixFlow p H β f)⁻¹ * ν w) u ≤ _ ∧ _
    rw [scale]
    constructor
    · calc
        _ ≤ (prefixFlow p H β f)⁻¹ * β u.length :=
          mul_le_mul_of_nonneg_left hcap (inv_nonneg.mpr hflow.le)
        _ = β u.length / prefixFlow p H β f := by ring
        _ ≤ β u.length / combFlow p H β :=
          div_le_div_of_nonneg_left (hβ _) hcomb hcomparison
    · intro hbad
      rw [hkill hbad, mul_zero]

#print axioms exists_comb_capped_probability

end D5.S3.Arith.Congruence.PrefixCapacityRealization
