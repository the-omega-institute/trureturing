/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/RectangleCover
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Soundness of checked dyadic rectangle covers. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Bounds.Slopes
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Bounds.Near
import D5.S0.Certificates.BoxCover.FiniteSublevelCover

namespace RefinedBMV.FourSpectrumLift

open D5.S0.Certificates.BoxCover.FiniteSublevelCover

/-- A finite dyadic cover with checked analytic leaves. -/
inductive RectangleCover where
  | leaf (box : Fin 7 → ℚ × ℚ)
  | meanValue (center whole : Fin 7 → ℚ × ℚ)
  | twoSlopes (center whole : Fin 7 → ℚ × ℚ) (moment : ℚ × ℚ)
  | near (box : Fin 9 → ℚ × ℚ)
  | splitC (left right : RectangleCover)
  | splitH (left right : RectangleCover)

private def cutC (b : ZeroCenterRectangle) : ℚ := (b.cLo + b.cHi) / 2
private def cutH (b : ZeroCenterRectangle) : ℚ := (b.hLo + b.hHi) / 2

def RectangleCover.Valid : RectangleCover → ZeroCenterRectangle → Prop
  | .leaf box, b => leafValid b box
  | .meanValue center whole, b => meanValueValid b center whole
  | .twoSlopes center whole moment, b => twoSlopeValid b center whole moment
  | .near box, b => nearValid b box
  | .splitC l r, b => l.Valid {b with cHi := cutC b} ∧ r.Valid {b with cLo := cutC b}
  | .splitH l r, b => l.Valid {b with hHi := cutH b} ∧ r.Valid {b with hLo := cutH b}

private def RectangleCover.decideValid :
    (t : RectangleCover) → (b : ZeroCenterRectangle) → Decidable (t.Valid b)
  | .leaf box, b => inferInstanceAs (Decidable (leafValid b box))
  | .meanValue center whole, b => inferInstanceAs (Decidable (meanValueValid b center whole))
  | .twoSlopes center whole moment, b =>
    inferInstanceAs (Decidable (twoSlopeValid b center whole moment))
  | .near box, b => inferInstanceAs (Decidable (nearValid b box))
  | .splitC l r, b =>
    letI := l.decideValid {b with cHi := cutC b}
    letI := r.decideValid {b with cLo := cutC b}
    instDecidableAnd
  | .splitH l r, b =>
    letI := l.decideValid {b with hHi := cutH b}
    letI := r.decideValid {b with hLo := cutH b}
    instDecidableAnd

private instance (t : RectangleCover) (b : ZeroCenterRectangle) : Decidable (t.Valid b) :=
  t.decideValid b

private theorem cover_union (a b root : Set (ℝ × ℝ)) (goal : Set (ℝ × ℝ))
    (ha : a ⊆ goal) (hb : b ⊆ goal) (hsplit : root ⊆ a ∪ b) :
    root ⊆ goal := by
  let region : Fin 3 → Set (ℝ × ℝ) := ![a, b, root]
  have hsteps : ∀ i, LocalStep region goal (fun _ (_ : Unit) ↦ 0) 0 i := by
    intro i
    fin_cases i
    · exact LocalStep.covered ha
    · exact LocalStep.covered hb
    · exact LocalStep.split 0 1 (by decide) (by decide) hsplit
  intro x hx
  exact sublevel_mem_target_of_local_steps region goal _ 0 hsteps 2 x hx (by simp)

private def positiveRegion (p : ℕ) : Set (ℝ × ℝ) :=
  {x | 0 < x.1 → x.2 = (1 : ℝ)/p → 0 < deriv^[2] (zeroProfile p) x.1}

private theorem profile_pos_of_normalized {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c)
    (h : 0 < zeroCenterCurvatureAt (1 / (p : ℝ)) c) :
    0 < deriv^[2] (zeroProfile p) c := by
  rw [zeroProfile_deriv2_eq_curvature hp hc]
  exact mul_pos (Real.exp_pos _) h

private def rectRegion (b : ZeroCenterRectangle) : Set (ℝ × ℝ) :=
  {x | b.Holds x.1 x.2}

private theorem RectangleCover.sound (t : RectangleCover) (b : ZeroCenterRectangle)
    (ht : t.Valid b) {p : ℕ} (hp : 0 < p) : rectRegion b ⊆ positiveRegion p := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < (1 : ℝ)/p := one_div_pos.mpr hp'
  induction t generalizing b with
  | leaf box =>
    rintro ⟨c, h⟩ hx hc he
    change h = (1 : ℝ) / p at he
    subst h
    exact profile_pos_of_normalized hp hc (leaf_positive ht hx hh)
  | meanValue center whole =>
    rintro ⟨c, h⟩ hx hc he
    change h = (1 : ℝ) / p at he
    subst h
    exact profile_pos_of_normalized hp hc (meanValue_positive ht hx hh)
  | twoSlopes center whole moment =>
    rintro ⟨c, h⟩ hx hc he
    change h = (1 : ℝ) / p at he
    subst h
    exact profile_pos_of_normalized hp hc (twoSlope_positive ht hx hh)
  | near box =>
    rintro ⟨c, h⟩ hx hc he
    change h = (1 : ℝ) / p at he
    subst h
    exact near_positive ht hp hc hx
  | splitC l r ihl ihr =>
    exact cover_union _ _ _ _ (ihl _ ht.1) (ihr _ ht.2) (fun x hx ↦
      let ⟨hcl, hcu, hhl, hhu⟩ := hx
      (le_total x.1 (cutC b : ℝ)).imp (fun hh ↦ ⟨hcl, hh, hhl, hhu⟩)
        (fun hh ↦ ⟨hh, hcu, hhl, hhu⟩))
  | splitH l r ihl ihr =>
    exact cover_union _ _ _ _ (ihl _ ht.1) (ihr _ ht.2) (fun x hx ↦
      let ⟨hcl, hcu, hhl, hhu⟩ := hx
      (le_total x.2 (cutH b : ℝ)).imp (fun hh ↦ ⟨hcl, hcu, hhl, hh⟩)
        (fun hh ↦ ⟨hcl, hcu, hh, hhu⟩))

/-- A validated cover proves positivity for the actual profile at every real gap in its root. -/
theorem positive_deriv2_of_cover (t : RectangleCover) (b : ZeroCenterRectangle)
    (ht : t.Valid b) {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c)
    (hb : b.Holds c (1 / (p : ℝ))) : 0 < deriv^[2] (zeroProfile p) c :=
  t.sound b ht hp (a := (c, 1 / (p : ℝ))) hb hc rfl

theorem RectangleCover.valid_splitC {l r : RectangleCover} {b : ZeroCenterRectangle}
    (hl : l.Valid {b with cHi := cutC b}) (hr : r.Valid {b with cLo := cutC b}) :
    (RectangleCover.splitC l r).Valid b :=
  And.intro hl hr

theorem RectangleCover.valid_splitH {l r : RectangleCover} {b : ZeroCenterRectangle}
    (hl : l.Valid {b with hHi := cutH b}) (hr : r.Valid {b with hLo := cutH b}) :
    (RectangleCover.splitH l r).Valid b :=
  And.intro hl hr

theorem RectangleCover.valid_transport {t : RectangleCover} {b b' : ZeroCenterRectangle}
    (ht : t.Valid b) (he : b = b') : t.Valid b' :=
  he ▸ ht

end RefinedBMV.FourSpectrumLift
