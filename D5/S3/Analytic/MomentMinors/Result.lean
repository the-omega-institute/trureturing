/- GID: D5/S3/Analytic/MomentMinors/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/MomentMinors/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two moment minor inequalities from successive positive semidefinite second minors. -/

import D5.S3.Analytic.MomentMinors.MomentKernel
import D5.S3.Analytic.MomentMinors.PairMinor

/-! Successive second minors imply both moment inequalities. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix MeasureTheory

namespace D5.S3.Analytic.MomentMinors.Result
open D5.S3.Analytic.MomentMinors.Defs
open D5.S3.Analytic.MomentMinors.MomentKernel
open D5.S3.Analytic.MomentMinors.PairMinor

private lemma second_minor_bound {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (a b c d : ι) :
    (A a c * A b d - A a d * A b c) ^ 2 ≤
      (A a a * A b b - A a b ^ 2) * (A c c * A d d - A c d ^ 2) := by
  let p : Fin 2 → ι := ![a, c]
  let q : Fin 2 → ι := ![b, d]
  have h := (pairMinor_posSemidef hA p q).det_nonneg
  have hs (i j : ι) : A j i = A i j := by
    simpa only [star_trivial] using hA.isHermitian.apply i j
  norm_num [Matrix.det_fin_two, p, q] at h
  rw [hs a b, hs c d, hs a c, hs b d, hs b c, hs a d] at h
  nlinarith only [h]

private lemma minor_identity (μ : Measure ℝ) (r s u v : ℝ) :
    lam μ ((r + u) / 2) * lam μ ((s + v) / 2) -
      lam μ ((r + v) / 2) * lam μ ((s + u) / 2) =
    xi μ ((r + u) / 2) ((s + v) / 2) -
      xi μ ((r + v) / 2) ((s + u) / 2) := by
  unfold xi
  rw [show ((r + u) / 2 + (s + v) / 2) / 2 =
    ((r + v) / 2 + (s + u) / 2) / 2 by ring]
  ring

private lemma pair_kernel_posSemidef {κ : Type*} [Fintype κ]
    {I : Set ℝ} (hI : I.OrdConnected) {μ : Measure ℝ} (hμ : Admissible μ I)
    (r s : κ → ℝ) (hr : ∀ i, r i ∈ I) (hs : ∀ i, s i ∈ I) :
    Matrix.PosSemidef (fun i j => xi μ ((r i + r j) / 2) ((s i + s j) / 2) -
      xi μ ((r i + s j) / 2) ((s i + r j) / 2) : Matrix κ κ ℝ) := by
  classical
  let t : κ × Fin 2 → ℝ := fun i => if i.2 = 0 then r i.1 else s i.1
  have ht : ∀ i, t i ∈ I := by
    intro i
    dsimp [t]
    split_ifs <;> first | exact hr i.1 | exact hs i.1
  have h := pairMinor_posSemidef (momentKernel_posSemidef hI hμ t ht)
    (fun i => (i, 0)) (fun i => (i, 1))
  simp_rw [← minor_identity]
  simpa [t] using h

private lemma pair_kernel_diag (μ : Measure ℝ) (r s : ℝ) :
    xi μ ((r + r) / 2) ((s + s) / 2) -
      xi μ ((r + s) / 2) ((s + r) / 2) = xi μ r s := by
  rw [show (r + r) / 2 = r by ring, show (s + s) / 2 = s by ring,
    show (s + r) / 2 = (r + s) / 2 by ring]
  simp [xi, pow_two]

private theorem first_claim : claim1 := by
  intro I hI μ hμ r₁ s₁ u₁ v₁ r₂ s₂ u₂ v₂ hr₁ hs₁ hu₁ hv₁ hr₂ hs₂ hu₂ hv₂
  let r : Fin 4 → ℝ := ![r₁, u₁, r₂, u₂]
  let s : Fin 4 → ℝ := ![s₁, v₁, s₂, v₂]
  have hr : ∀ i, r i ∈ I := by intro i; fin_cases i <;> simp_all [r]
  have hs : ∀ i, s i ∈ I := by intro i; fin_cases i <;> simp_all [s]
  have h := second_minor_bound (pair_kernel_posSemidef hI hμ r s hr hs) 0 1 2 3
  simp only [r, s, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    pair_kernel_diag] at h
  exact h

private lemma displaced_kernel_posSemidef {κ : Type*} [Fintype κ]
    {I : Set ℝ} (hI : I.OrdConnected) {μ : Measure ℝ} (hμ : Admissible μ I)
    (a : ℝ) (x : κ → ℝ) (hx : ∀ i, x i ∈ I) (hxa : ∀ i, x i + a ∈ I) :
    Matrix.PosSemidef (fun i j => sigma μ a ((x i + x j) / 2) : Matrix κ κ ℝ) := by
  have h := pair_kernel_posSemidef hI hμ x (fun i => x i + a) hx hxa
  have he (i j : κ) :
      sigma μ a ((x i + x j) / 2) =
      xi μ ((x i + x j) / 2) ((x i + a + (x j + a)) / 2) -
        xi μ ((x i + (x j + a)) / 2) ((x i + a + x j) / 2) := by
    rw [← minor_identity]
    unfold sigma xi
    rw [show (x i + a + (x j + a)) / 2 = (x i + x j) / 2 + a by ring,
      show (x i + (x j + a)) / 2 = (x i + a + x j) / 2 by ring,
      show ((x i + x j) / 2 + ((x i + x j) / 2 + a)) / 2 =
        (x i + a + x j) / 2 by ring]
    ring
  simpa only [← he] using h

private theorem second_claim : claim2 := by
  intro I hI μ hμ a x y z v hx hxa hy hya hz hza hv hva
  let t : Fin 4 → ℝ := ![x, y, z, v]
  have ht : ∀ i, t i ∈ I := by intro i; fin_cases i <;> simp_all [t]
  have hta : ∀ i, t i + a ∈ I := by intro i; fin_cases i <;> simp_all [t]
  have h := second_minor_bound (displaced_kernel_posSemidef hI hμ a t ht hta) 0 1 2 3
  simp only [t, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  unfold theta
  rw [show (x + x) / 2 = x by ring, show (y + y) / 2 = y by ring,
    show (z + z) / 2 = z by ring, show (v + v) / 2 = v by ring] at h
  have he : theta μ a ((x + z) / 2) ((y + v) / 2) -
      theta μ a ((x + v) / 2) ((y + z) / 2) =
      sigma μ a ((x + z) / 2) * sigma μ a ((y + v) / 2) -
      sigma μ a ((x + v) / 2) * sigma μ a ((y + z) / 2) := by
    unfold theta
    rw [show ((x + z) / 2 + (y + v) / 2) / 2 =
      ((x + v) / 2 + (y + z) / 2) / 2 by ring]
    ring
  change _ ≤ _
  rw [← he] at h
  exact h

/-- Both moment minor inequalities hold for every admissible probability law. -/
theorem result : claim := ⟨first_claim, second_claim⟩

end D5.S3.Analytic.MomentMinors.Result
