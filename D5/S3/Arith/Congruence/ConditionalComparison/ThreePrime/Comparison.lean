/- GID: D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Conditional comparison on the entire preceding history. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/ThreePrime/Comparison.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.Probability

/-!
# Conditional comparison on the entire preceding history

`KernelChain` retains the full tuple of previous coordinates in every kernel.
The auxiliary coordinates, and only those coordinates, use product laws.
-/

namespace Erdos7.ThreePrime

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

inductive KernelChain (Ω : Type*) [Fintype Ω] : ℕ → Type _
  | nil : KernelChain Ω 0
  | snoc {n : ℕ} (past : KernelChain Ω n)
      (kernel : (Fin n → Ω) → FiniteLaw Ω) : KernelChain Ω (n+1)

namespace KernelChain

noncomputable def law : {n : ℕ} → KernelChain Ω n → FiniteLaw (Fin n → Ω)
  | 0, .nil => FiniteLaw.uniform (Fin 0 → Ω)
  | _+1, .snoc past K => by
      classical
      exact (past.law.joint K).map (fun z ↦ Fin.snoc z.1 z.2)

theorem expect_snoc {n : ℕ} (P : KernelChain Ω n)
    (K : (Fin n → Ω) → FiniteLaw Ω) (f : (Fin (n+1) → Ω) → ℚ) :
    (P.snoc K).law.expect f = P.law.expect (fun x ↦ (K x).expect (fun y ↦ f (Fin.snoc x y))) := by
  classical
  rw [law, FiniteLaw.map_expect, FiniteLaw.joint_expect]

def active {n : ℕ} (S : Finset ι) (req : ι → Fin n → Ω → Bool)
    (x : Fin n → Ω) : Finset ι := S.filter (fun c ↦ ∀ i, req c i (x i) = true)

def aligned {n D : ℕ} (S : Finset ι) (depth : ι → Fin n → ℕ)
    (x : Fin n → Fin (D+1)) : Finset ι := S.filter (fun c ↦ ∀ i, depth c i ≤ (x i).val)

omit [Fintype Ω] [DecidableEq ι] in
@[simp] theorem active_nil (S : Finset ι) (req : ι → Fin 0 → Ω → Bool)
    (x : Fin 0 → Ω) : active S req x = S := by simp [active]

omit [DecidableEq ι] in
@[simp] theorem aligned_nil {D : ℕ} (S : Finset ι) (depth : ι → Fin 0 → ℕ)
    (x : Fin 0 → Fin (D+1)) : aligned S depth x = S := by simp [aligned]

omit [Fintype Ω] [DecidableEq ι] in
theorem active_snoc {n : ℕ} (S : Finset ι) (req : ι → Fin (n+1) → Ω → Bool)
    (x : Fin n → Ω) (y : Ω) :
    active S req (Fin.snoc x y) =
      (active S (fun c i ↦ req c i.castSucc) x).filter (fun c ↦ req c (Fin.last n) y = true) := by
  ext c
  simp only [active, Finset.mem_filter, Fin.forall_fin_succ', Fin.snoc_last, Fin.snoc_castSucc]
  tauto

omit [DecidableEq ι] in
theorem aligned_snoc {n D : ℕ} (S : Finset ι) (depth : ι → Fin (n+1) → ℕ)
    (x : Fin n → Fin (D+1)) (y : Fin (D+1)) :
    aligned S depth (Fin.snoc x y) =
      CappedGain.depthLe (fun c ↦ depth c (Fin.last n)) y.val
        (aligned S (fun c i ↦ depth c i.castSucc) x) := by
  ext c
  simp only [aligned, CappedGain.depthLe, Finset.mem_filter,
    Fin.forall_fin_succ', Fin.snoc_last, Fin.snoc_castSucc]
  tauto

/-- Pointwise bounds for every kernel, conditional on its entire past. -/
def HasCaps {D : ℕ} : {n : ℕ} → KernelChain Ω n → Finset ι →
    (ι → Fin n → Ω → Bool) → (ι → Fin n → ℕ) → (Fin n → RunSpec D) → Prop
  | 0, .nil, _, _, _, _ => True
  | n+1, .snoc P K, S, req, depth, R =>
      HasCaps P S (fun c i ↦ req c i.castSucc) (fun c i ↦ depth c i.castSucc)
        (fun i ↦ R i.castSucc) ∧
      ∀ x c, c ∈ S → (K x).prob (fun y ↦ req c (Fin.last n) y = true) ≤
        (R (Fin.last n)).survival (depth c (Fin.last n))

omit [DecidableEq ι] in
theorem filter_increasing {F : Finset ι → ℚ} (hF : Increasing F)
    (P : ι → Prop) [DecidablePred P] : Increasing (fun S ↦ F (S.filter P)) := by
  intro A B h
  exact hF (Finset.filter_subset_filter P h)

theorem filter_supermodular {F : Finset ι → ℚ} (hF : Supermodular F)
    (P : ι → Prop) [DecidablePred P] : Supermodular (fun S ↦ F (S.filter P)) := by
  intro A B
  have hi : A.filter P ∩ B.filter P = (A ∩ B).filter P := by ext c; simp; tauto
  have hu : A.filter P ∪ B.filter P = (A ∪ B).filter P := by ext c; simp; tauto
  simpa only [hi, hu] using hF (A.filter P) (B.filter P)

/-- Backward conditional rearrangement, with every individual label retained. -/
theorem comparison {n D : ℕ} (P : KernelChain Ω n) (S : Finset ι)
    (req : ι → Fin n → Ω → Bool) (depth : ι → Fin n → ℕ) (R : Fin n → RunSpec D)
    (hdepth : ∀ c ∈ S, ∀ i, depth c i ≤ D) (hcap : P.HasCaps S req depth R)
    (F : Finset ι → ℚ) (hF : Supermodular F) (hInc : Increasing F) :
    P.law.expect (fun x ↦ F (active S req x)) ≤
      (FiniteLaw.piLaw (fun i ↦ (R i).law)).expect (fun x ↦ F (aligned S depth x)) := by
  induction P generalizing S F with
  | nil => simp [law, FiniteLaw.expect_const]
  | @snoc n P K ih =>
    obtain ⟨hpast, hlast⟩ := hcap
    let req₀ := fun c (i : Fin n) ↦ req c i.castSucc
    let depth₀ := fun c (i : Fin n) ↦ depth c i.castSucc
    let R₀ := fun i : Fin n ↦ R i.castSucc
    let lastDepth := fun c ↦ depth c (Fin.last n)
    let μ := FiniteLaw.piLaw (fun i ↦ (R₀ i).law)
    let ν := (R (Fin.last n)).law
    have hstep : ∀ x : Fin n → Ω,
        (K x).expect (fun y ↦ F (active S req (Fin.snoc x y))) ≤
        ν.expect (fun d ↦ F (CappedGain.depthLe lastDepth d.val (active S req₀ x))) := by
      intro x
      rw [show (fun y ↦ F (active S req (Fin.snoc x y))) =
          (fun y ↦ F ((active S req₀ x).filter (fun c ↦ req c (Fin.last n) y = true))) by
        funext y
        rw [active_snoc]]
      apply CappedGain.finite_run_rearrangement (K x) (active S req₀ x)
        (fun y ↦ (active S req₀ x).filter (fun c ↦ req c (Fin.last n) y = true))
        (fun _ ↦ Finset.filter_subset _ _) lastDepth (R (Fin.last n))
        (fun c hc ↦ hdepth c (Finset.mem_filter.mp hc).1 _) hF hInc
      intro c hc
      exact ((K x).prob_mono _ _ (fun y hy ↦ (Finset.mem_filter.mp hy).2)).trans
        (hlast x c (Finset.mem_filter.mp hc).1)
    have hmiddle : ν.expect (fun d ↦ P.law.expect
        (fun x ↦ F (CappedGain.depthLe lastDepth d.val (active S req₀ x)))) ≤
        ν.expect (fun d ↦ μ.expect
          (fun x ↦ F (CappedGain.depthLe lastDepth d.val (aligned S depth₀ x)))) := by
      apply ν.expect_mono
      intro d
      apply ih S req₀ depth₀ R₀ (fun c hc i ↦ hdepth c hc i.castSucc) hpast
        (fun A ↦ F (CappedGain.depthLe lastDepth d.val A))
      · exact filter_supermodular hF (fun c ↦ lastDepth c ≤ d.val)
      · exact filter_increasing hInc (fun c ↦ lastDepth c ≤ d.val)
    rw [expect_snoc]
    calc
      P.law.expect (fun x ↦ (K x).expect (fun y ↦ F (active S req (Fin.snoc x y)))) ≤
          P.law.expect (fun x ↦ ν.expect
            (fun d ↦ F (CappedGain.depthLe lastDepth d.val (active S req₀ x)))) :=
        P.law.expect_mono hstep
      _ = ν.expect (fun d ↦ P.law.expect
          (fun x ↦ F (CappedGain.depthLe lastDepth d.val (active S req₀ x)))) :=
        P.law.expect_comm ν _
      _ ≤ ν.expect (fun d ↦ μ.expect
          (fun x ↦ F (CappedGain.depthLe lastDepth d.val (aligned S depth₀ x)))) := hmiddle
      _ = μ.expect (fun x ↦ ν.expect
          (fun d ↦ F (CappedGain.depthLe lastDepth d.val (aligned S depth₀ x)))) :=
        ν.expect_comm μ _
      _ = (FiniteLaw.piLaw (fun i ↦ (R i).law)).expect (fun x ↦ F (aligned S depth x)) := by
        rw [FiniteLaw.piLaw_expect_snoc]
        simp only [aligned_snoc]
        rfl

end KernelChain

theorem convex_load_supermodular (h : ℚ → ℚ) (hh : ConvexOn ℚ Set.univ h)
    (w : ι → ℚ) (hw : ∀ c, 0 ≤ w c) :
    Supermodular (fun S ↦ h (CappedGain.modularLoad w S)) := by
  apply Supermodular.of_marginal_mono
  intro A B hAB c hcB
  have hcA : c ∉ A := fun hc ↦ hcB (hAB hc)
  have heA : CappedGain.modularLoad w (insert c A) = CappedGain.modularLoad w A + w c := by
    simp [CappedGain.modularLoad, hcA, add_comm]
  have heB : CappedGain.modularLoad w (insert c B) = CappedGain.modularLoad w B + w c := by
    simp [CappedGain.modularLoad, hcB, add_comm]
  rw [heA, heB]
  exact CappedGain.convex_increment_mono hh (CappedGain.modularLoad_increasing hw hAB) (hw c)

theorem convex_load_comparison {n D : ℕ} (P : KernelChain Ω n) (S : Finset ι)
    (req : ι → Fin n → Ω → Bool) (depth : ι → Fin n → ℕ) (R : Fin n → RunSpec D)
    (hdepth : ∀ c ∈ S, ∀ i, depth c i ≤ D) (hcap : P.HasCaps S req depth R)
    (h : ℚ → ℚ) (hconv : ConvexOn ℚ Set.univ h) (hmono : Monotone h)
    (w : ι → ℚ) (hw : ∀ c, 0 ≤ w c) :
    P.law.expect (fun x ↦ h (∑ c ∈ KernelChain.active S req x, w c)) ≤
      (FiniteLaw.piLaw (fun i ↦ (R i).law)).expect
        (fun x ↦ h (∑ c ∈ KernelChain.aligned S depth x, w c)) := by
  exact P.comparison S req depth R hdepth hcap
    (fun A ↦ h (CappedGain.modularLoad w A)) (convex_load_supermodular h hconv w hw)
    (fun _ _ hAB ↦ hmono (CappedGain.modularLoad_increasing hw hAB))

end Erdos7.ThreePrime
