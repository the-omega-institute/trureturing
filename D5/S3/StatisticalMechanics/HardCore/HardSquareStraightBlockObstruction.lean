/- GID: D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Analytic Yang-Baxter obstruction for all straight hard-square blocks of length at least three. -/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-! The straight horizontal clause of Ortega–Peña-Ancavil, arXiv:2611.06780v1,
Question 5.2. Faces use the top row followed by the bottom row. -/

namespace D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction

open scoped BigOperators

/-- Binary heights with no adjacent occupied sites. -/
abbrev Word (k : ℕ) :=
  {w : Fin k → Bool //
    ∀ i j : Fin k, j.val = i.val + 1 → ¬ (w i = true ∧ w j = true)}

noncomputable instance (k : ℕ) : Fintype (Word k) := Fintype.ofFinite _

/-- Face weights with arguments in top-left, top-right, bottom-left, bottom-right order. -/
abbrev Weight (k : ℕ) := Word k → Word k → Word k → Word k → ℂ

/-- Compatibility across the seam from the last site of the left block to the first
site of the right block. -/
def H {k : ℕ} (s t : Word k) : Prop :=
  ∀ i j : Fin k, i.val + 1 = k → j.val = 0 → ¬ (s.val i = true ∧ t.val j = true)

/-- Vertical compatibility at each corresponding site. -/
def V {k : ℕ} (s t : Word k) : Prop :=
  ∀ i : Fin k, ¬ (s.val i = true ∧ t.val i = true)

/-- The legal configurations of the two-by-`2k` rectangle. -/
def FaceSupport {k : ℕ} (a b c d : Word k) : Prop :=
  H a b ∧ H c d ∧ V a c ∧ V b d

/-- Weights are zero outside the common support. -/
def Supported {k : ℕ} (T : Weight k) : Prop :=
  ∀ a b c d, ¬ FaceSupport a b c d → T a b c d = 0

/-- Number of occupied sites of a height. -/
def occ {k : ℕ} (w : Word k) : ℕ :=
  ∑ i : Fin k, (w.val i).toNat

/-- The blocked hard-square weight of equation (4.1), extended by zero. -/
noncomputable def blocked {k : ℕ} (A B C D : ℂˣ) : Weight k := by
  classical
  exact fun a b c d =>
    if FaceSupport a b c d then
      (A : ℂ) ^ occ a * (B : ℂ) ^ occ b * (C : ℂ) ^ occ c * (D : ℂ) ^ occ d
    else 0

/-- Equation (2.2) at the ordered boundary `(a,b,c,d,e,f)`. -/
def EqAt {k : ℕ} (P Q R : Weight k) (ρ : ℂˣ) (a b c d e f : Word k) : Prop :=
  (∑ g : Word k, P f g a b * Q e d f g * R d c g b) =
    (ρ : ℂ) * (∑ g : Word k, R e g f a * Q g c a b * P e d g c)

/-- A separately holomorphic family satisfying the source identity and containing the
blocked weight at an ordered parameter pair. -/
def HasFamily (k : ℕ) (Ω : Set ℂ) (target : Weight k) : Prop :=
  ∃ W : ℂ → ℂ → Weight k,
    (∀ u ∈ Ω, ∀ v ∈ Ω, Supported (W u v)) ∧
    (∀ u ∈ Ω, ∀ a b c d : Word k,
      DifferentiableOn ℂ (fun v => W u v a b c d) Ω) ∧
    (∀ v ∈ Ω, ∀ a b c d : Word k,
      DifferentiableOn ℂ (fun u => W u v a b c d) Ω) ∧
    (∀ p ∈ Ω, ∀ q ∈ Ω, ∀ r ∈ Ω,
      ∃ ρ : ℂˣ, ∀ a b c d e f : Word k,
        EqAt (W p q) (W p r) (W q r) ρ a b c d e f) ∧
    (∃ p ∈ Ω, ∃ r ∈ Ω, W p r = target)

private def empty (k : ℕ) : Word k :=
  ⟨fun _ => false, by simp⟩

/-- The sites of the given parity in one-based numbering. -/
private def alternating (k parity : ℕ) : Word k :=
  ⟨fun i => decide ((i.val + 1) % 2 = parity), by
    intro i j hj
    simp only [decide_eq_true_eq]
    omega⟩

private abbrev L (k : ℕ) := alternating k 0
private abbrev M (k : ℕ) := alternating k 1

private theorem h_empty_left {k : ℕ} (g : Word k) : H (empty k) g := by
  simp [H, empty]

private theorem h_empty_right {k : ℕ} (g : Word k) : H g (empty k) := by
  simp [H, empty]

private theorem v_empty_left {k : ℕ} (g : Word k) : V (empty k) g := by
  simp [V, empty]

private theorem v_empty_right {k : ℕ} (g : Word k) : V g (empty k) := by
  simp [V, empty]

private theorem h_LL (k : ℕ) : H (L k) (L k) := by
  intro i j _ hj h
  have := of_decide_eq_true h.2
  omega

private theorem not_v_LL {k : ℕ} (hk : 3 ≤ k) : ¬ V (L k) (L k) := by
  intro h
  let i : Fin k := ⟨1, by omega⟩
  have hi : (L k).val i = true := by simp [i, alternating]
  exact h i ⟨hi, hi⟩

private theorem v_LM (k : ℕ) : V (L k) (M k) := by
  intro i h
  have hL := of_decide_eq_true h.1
  have hM := of_decide_eq_true h.2
  omega

private theorem eq_empty_of_vertical {k : ℕ} {g : Word k}
    (hgM : V g (M k)) (hLg : V (L k) g) : g = empty k := by
  apply Subtype.ext
  funext i
  change g.val i = false
  by_contra! hi
  have hg : g.val i = true := Bool.eq_true_of_not_eq_false hi
  by_cases h : (i.val + 1) % 2 = 0
  · exact hLg i ⟨decide_eq_true h, hg⟩
  · have h' : (i.val + 1) % 2 = 1 := by omega
    exact hgM i ⟨hg, decide_eq_true h'⟩

private theorem boundary_product_zero {k : ℕ} (hk : 3 ≤ k)
    (P Q R : Weight k) (ρ : ℂˣ) (hP : Supported P) (hQ : Supported Q)
    (heq : EqAt P Q R ρ (empty k) (M k) (L k) (L k) (empty k) (L k)) :
    P (L k) (empty k) (empty k) (M k) *
      Q (empty k) (L k) (L k) (empty k) *
      R (L k) (L k) (empty k) (M k) = 0 := by
  classical
  have hleft :
      (∑ g : Word k, P (L k) g (empty k) (M k) *
        Q (empty k) (L k) (L k) g * R (L k) (L k) g (M k)) =
      P (L k) (empty k) (empty k) (M k) *
        Q (empty k) (L k) (L k) (empty k) *
        R (L k) (L k) (empty k) (M k) := by
    refine Finset.sum_eq_single_of_mem (empty k) (Finset.mem_univ _) ?_
    intro g _ hg
    by_cases hp : FaceSupport (L k) g (empty k) (M k)
    · have hq : ¬ FaceSupport (empty k) (L k) (L k) g :=
        fun h => hg (eq_empty_of_vertical hp.2.2.2 h.2.2.2)
      simp [hQ _ _ _ _ hq]
    · simp [hP _ _ _ _ hp]
  have hright :
      (∑ g : Word k, R (empty k) g (L k) (empty k) *
        Q g (L k) (empty k) (M k) * P (empty k) (L k) g (L k)) = 0 := by
    refine Finset.sum_eq_zero fun g _ => ?_
    have hp : ¬ FaceSupport (empty k) (L k) g (L k) :=
      fun h => not_v_LL hk h.2.2.2
    simp [hP _ _ _ _ hp]
  unfold EqAt at heq
  simpa only [hleft, hright, mul_zero] using heq

private theorem blocked_ne_zero {k : ℕ} (A B C D : ℂˣ)
    {a b c d : Word k} (h : FaceSupport a b c d) : blocked A B C D a b c d ≠ 0 := by
  unfold blocked
  rw [ite_eq_left h]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ A.ne_zero) (pow_ne_zero _ B.ne_zero))
      (pow_ne_zero _ C.ne_zero))
    (pow_ne_zero _ D.ne_zero)

/-- No separately holomorphic family on a connected open domain realizes the common-support
face equation and passes through the blocked weight, for any straight width at least three. -/
theorem result (k : ℕ) (hk : 3 ≤ k) (A B C D : ℂˣ)
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩconn : IsConnected Ω) :
    ¬ HasFamily k Ω (blocked A B C D) := by
  rintro ⟨W, hsupp, hsecond, hfirst, heq, p, hp, r, hr, hblocked⟩
  let F (q : ℂ) := W p q (L k) (empty k) (empty k) (M k)
  let G (q : ℂ) := W q r (L k) (L k) (empty k) (M k)
  have hpFace : FaceSupport (L k) (empty k) (empty k) (M k) :=
    ⟨h_empty_right _, h_empty_left _, v_empty_right _, v_empty_left _⟩
  have hqFace : FaceSupport (empty k) (L k) (L k) (empty k) :=
    ⟨h_empty_left _, h_empty_right _, v_empty_left _, v_empty_right _⟩
  have hrFace : FaceSupport (L k) (L k) (empty k) (M k) :=
    ⟨h_LL k, h_empty_left _, v_empty_right _, v_LM k⟩
  have hmiddle : W p r (empty k) (L k) (L k) (empty k) ≠ 0 := by
    rw [hblocked]
    exact blocked_ne_zero A B C D hqFace
  have hFr : F r ≠ 0 := by
    dsimp only [F]
    rw [hblocked]
    exact blocked_ne_zero A B C D hpFace
  have hGp : G p ≠ 0 := by
    dsimp only [G]
    rw [hblocked]
    exact blocked_ne_zero A B C D hrFace
  have hprod : ∀ q ∈ Ω, F q * G q = 0 := by
    intro q hq
    obtain ⟨ρ, hρ⟩ := heq p hp q hq r hr
    have h := boundary_product_zero hk (W p q) (W p r) (W q r) ρ
      (hsupp p hp q hq) (hsupp p hp r hr) (hρ _ _ _ _ _ _)
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact mul_eq_zero.mpr (Or.inl h)
      · exact (hmiddle h).elim
    · exact mul_eq_zero.mpr (Or.inr h)
  have hF : AnalyticOnNhd ℂ F Ω :=
    (hsecond p hp _ _ _ _).analyticOnNhd hΩopen
  have hG : AnalyticOnNhd ℂ G Ω :=
    (hfirst r hr _ _ _ _).analyticOnNhd hΩopen
  rcases hF.eq_zero_or_eq_zero_of_mul_eq_zero hG hprod hΩconn.isPreconnected with h | h
  · exact hFr (h r hr)
  · exact hGp (h p hp)

end D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction
