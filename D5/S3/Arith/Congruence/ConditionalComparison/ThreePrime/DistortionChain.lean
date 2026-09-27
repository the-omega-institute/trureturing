/- GID: D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Actual distortion chains and conditional caps. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/ThreePrime/DistortionChain.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.Comparison

namespace Erdos7.ThreePrime

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

/-- The complete finite physical distortion, at arbitrary rational thresholds. -/
inductive PhysicalChain (Ω : Type*) [Fintype Ω] : ℕ → Type _
  | nil : PhysicalChain Ω 0
  | snoc {n : ℕ} (past : PhysicalChain Ω n) (base : FiniteLaw Ω)
      (bad : (Fin n → Ω) → Ω → Bool) (δ : ℚ)
      (nonneg : 0 ≤ δ) (below_one : δ < 1) : PhysicalChain Ω (n+1)

namespace PhysicalChain

noncomputable def kernels : {n : ℕ} → PhysicalChain Ω n → KernelChain Ω n
  | 0, .nil => .nil
  | _+1, .snoc P μ bad δ h0 h1 =>
      P.kernels.snoc (fun x ↦ μ.distort (fun y ↦ bad x y = true) δ h0 h1)

noncomputable def totalCharge : {n : ℕ} → PhysicalChain Ω n → ℚ
  | 0, .nil => 0
  | _+1, .snoc P μ bad δ _ _ => P.totalCharge + P.kernels.law.expect
      (fun x ↦ thresholdMass δ (μ.prob (fun y ↦ bad x y = true)))

def covered : {n : ℕ} → PhysicalChain Ω n → (Fin n → Ω) → Bool
  | 0, .nil, _ => false
  | _+1, .snoc P _ bad _ _ _, x =>
      P.covered (Fin.init x) || bad (Fin.init x) (x (Fin.last _))

theorem covered_snoc {n : ℕ} (P : PhysicalChain Ω n) (μ : FiniteLaw Ω)
    (bad : (Fin n → Ω) → Ω → Bool) (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ < 1)
    (x : Fin n → Ω) (y : Ω) :
    (P.snoc μ bad δ h0 h1).covered (Fin.snoc x y) = (P.covered x || bad x y) := by
  simp only [covered, Fin.init_snoc, Fin.snoc_last]

/-- The union estimate holds under one final normalized law. -/
theorem covered_probability_le {n : ℕ} (P : PhysicalChain Ω n) :
    P.kernels.law.prob (fun x ↦ P.covered x = true) ≤ P.totalCharge := by
  induction P with
  | nil => simp [kernels, totalCharge, covered, FiniteLaw.prob, FiniteLaw.expect]
  | @snoc n P μ bad δ h0 h1 ih =>
    let K := fun x ↦ μ.distort (fun y ↦ bad x y = true) δ h0 h1
    have hpoint : ∀ x : Fin n → Ω,
        (K x).expect (fun y ↦ if P.covered x || bad x y then (1:ℚ) else 0) ≤
          (if P.covered x then 1 else 0) +
            thresholdMass δ (μ.prob (fun y ↦ bad x y = true)) := by
      intro x
      have he : (K x).expect (fun y ↦ if bad x y then (1:ℚ) else 0) =
          thresholdMass δ (μ.prob (fun y ↦ bad x y = true)) :=
        μ.distort_prob _ δ h0 h1
      rw [← he, ← (K x).expect_const (if P.covered x then 1 else 0), ← (K x).expect_add]
      apply (K x).expect_mono
      intro y
      cases hc : P.covered x <;> cases hb : bad x y <;> norm_num
    have h := P.kernels.law.expect_mono hpoint
    rw [FiniteLaw.expect_add] at h
    change P.kernels.law.expect _ ≤
      P.kernels.law.prob (fun x ↦ P.covered x = true) + _ at h
    change (P.kernels.snoc K).law.prob
      (fun z ↦ (P.snoc μ bad δ h0 h1).covered z = true) ≤
        P.totalCharge + P.kernels.law.expect
          (fun x ↦ thresholdMass δ (μ.prob (fun y ↦ bad x y = true)))
    refine le_trans ?_ (add_le_add ih (le_refl (P.kernels.law.expect
      (fun x ↦ thresholdMass δ (μ.prob (fun y ↦ bad x y = true))))))
    change (P.kernels.snoc K).law.expect
      (fun z ↦ if (P.snoc μ bad δ h0 h1).covered z then (1:ℚ) else 0) ≤ _
    rw [KernelChain.expect_snoc]
    simpa only [covered_snoc] using h

theorem one_le_charge_of_cover {n : ℕ} (P : PhysicalChain Ω n)
    (hcover : ∀ x, P.covered x = true) : 1 ≤ P.totalCharge := by
  have h := P.covered_probability_le
  simpa only [FiniteLaw.prob, hcover, if_true, FiniteLaw.expect_const] using h

/-- Base-law caps sufficient to construct the full conditional cap system. -/
def BaseCaps {D : ℕ} : {n : ℕ} → PhysicalChain Ω n → Finset ι →
    (ι → Fin n → Ω → Bool) → (ι → Fin n → ℕ) → (Fin n → RunSpec D) → Prop
  | 0, .nil, _, _, _, _ => True
  | n+1, .snoc P μ _ δ _ _, S, req, depth, R =>
      BaseCaps P S (fun c i ↦ req c i.castSucc) (fun c i ↦ depth c i.castSucc)
        (fun i ↦ R i.castSucc) ∧
      ∀ c ∈ S, depth c (Fin.last n) ≠ 0 →
        μ.prob (fun y ↦ req c (Fin.last n) y = true) ≤
        (1-δ)*(R (Fin.last n)).survival (depth c (Fin.last n))

omit [DecidableEq ι] in
theorem kernels_have_caps {n D : ℕ} (P : PhysicalChain Ω n) (S : Finset ι)
    (req : ι → Fin n → Ω → Bool) (depth : ι → Fin n → ℕ) (R : Fin n → RunSpec D)
    (hbase : P.BaseCaps S req depth R) : P.kernels.HasCaps S req depth R := by
  induction P with
  | nil => trivial
  | @snoc n P μ bad δ h0 h1 ih =>
    obtain ⟨hpast, hlast⟩ := hbase
    refine ⟨ih _ _ _ hpast, ?_⟩
    intro x c hc
    by_cases hd : depth c (Fin.last n) = 0
    · rw [hd, RunSpec.survival_zero]
      exact (μ.distort (fun y ↦ bad x y = true) δ h0 h1).prob_le_one _
    · have h := μ.distort_event_cap (fun y ↦ bad x y = true)
        (fun y ↦ req c (Fin.last n) y = true) δ h0 h1
      have hden : 0 < 1-δ := by linarith
      exact h.trans ((div_le_iff₀ hden).2 (by
        simpa only [mul_comm] using hlast c hc hd))

end PhysicalChain
end Erdos7.ThreePrime
