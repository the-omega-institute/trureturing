/- GID: D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reciprocal supermodularity gives the Jaccard triangle inequality on every lattice. -/

/-
proof_shape: IsStrictlyPositive: bind-only; consumers: IsLogSubmodular, claim, claimSufficiency
proof_shape: IsSupermodular: bind-only; consumers: claim, claimSufficiency, reciprocal_supermodular
proof_shape: IsSubmodular: bind-only; consumer: IsLogSubmodular
proof_shape: IsLogSubmodular: bind-only; consumers: claim, reciprocal_supermodular
proof_shape: jaccardDist: bind-only; consumers: claim, claimSufficiency, resultSufficiency
proof_shape: claim: bind-only; consumer: result
proof_shape: claimSufficiency: bind-only; consumer: resultSufficiency
proof_shape: reciprocal_sum_le: bind-only; consumer: reciprocal_supermodular
proof_shape: scalar_ordered: bind-only; consumer: scalar_bound
proof_shape: scalar_bound: bind-only; consumer: resultSufficiency
proof_shape: reciprocal_supermodular: bind-only; consumer: result
proof_shape: resultSufficiency: bind-only; consumer: result
proof_shape: result: bind-only; settling result
escape_witness: none
admission_basis: open-problem-resolution (#20617; Proved)
Direct frozen dependencies: none (only pinned Mathlib imports).
The source's IsStrictlyPositive definition and its uses remain literal; the proofs use
the resulting pointwise inequalities.
All theorem proofs combine upstream order and logarithm lemmas with case splits and
algebraic normalization. No independent escape witness is asserted.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21649
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices

universe u

variable {L : Type u} [Lattice L]

/-- Definition 3 (i): `f` is strictly positive. -/
def IsStrictlyPositive (f : L → ℝ) : Prop := ∀ X, 0 < f X

/-- Definition 3 (v), (7): `f` is supermodular. -/
def IsSupermodular (f : L → ℝ) : Prop :=
  ∀ X Y, f X + f Y ≤ f (X ⊔ Y) + f (X ⊓ Y)

/-- Definition 3 (iii), (6): `f` is submodular. -/
def IsSubmodular (f : L → ℝ) : Prop :=
  ∀ X Y, f (X ⊔ Y) + f (X ⊓ Y) ≤ f X + f Y

/-- Definition 3 (iv): `f` is strictly positive and `log ∘ f` is submodular. -/
def IsLogSubmodular (f : L → ℝ) : Prop :=
  IsStrictlyPositive f ∧ IsSubmodular (Real.log ∘ f)

/-- (17): the generalized Jaccard distance `d_{f,J}(A, B) = 1 − f(A ∧ B)/f(A ∨ B)`. -/
noncomputable def jaccardDist (f : L → ℝ) (A B : L) : ℝ :=
  1 - f (A ⊓ B) / f (A ⊔ B)

/-- Section 8, second problem: on an arbitrary lattice, a strictly positive, monotone, supermodular and
log-submodular valuation yields a distance `d_{f,J}` satisfying the triangle inequality. -/
def claim : Prop :=
  ∀ (L : Type u) [Lattice L] (f : L → ℝ), IsStrictlyPositive f → Monotone f → IsSupermodular f →
    IsLogSubmodular f → ∀ A B C : L, jaccardDist f A C ≤ jaccardDist f A B + jaccardDist f B C

/-- Section 8, fourth problem: the necessary conditions of Theorem 4 (with strict positivity) suffice on an arbitrary
lattice: if `f` is strictly positive and monotone and `f` and `1/f` are supermodular, then `d_{f,J}` satisfies the
triangle inequality. -/
def claimSufficiency : Prop :=
  ∀ (L : Type u) [Lattice L] (f : L → ℝ), IsStrictlyPositive f → Monotone f → IsSupermodular f →
    IsSupermodular (fun X => (f X)⁻¹) → ∀ A B C : L, jaccardDist f A C ≤ jaccardDist f A B + jaccardDist f B C

private theorem reciprocal_sum_le {r s m t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hm : 0 < m) (ht : 0 < t)
    (hadd : r + s ≤ m + t) (hmul : m * t ≤ r * s) :
    r⁻¹ + s⁻¹ ≤ m⁻¹ + t⁻¹ := by
  rw [inv_add_inv (ne_of_gt hr) (ne_of_gt hs),
    inv_add_inv (ne_of_gt hm) (ne_of_gt ht)]
  exact (div_le_div_of_nonneg_right hadd (le_of_lt (mul_pos hr hs))).trans
    (div_le_div_of_nonneg_left (le_of_lt (add_pos hm ht)) (mul_pos hm ht) hmul)

private theorem scalar_ordered {x y z b w p q : ℝ}
    (hb : 0 < b) (hw : 0 < w) (hz : 0 ≤ z) (hq : 0 ≤ q)
    (hqp : q ≤ p) (hxb : x ≤ b) (hyb : y ≤ b) (hpb : p ≤ 1 / b)
    (hxy : x + y ≤ b + z) (hpq : p + q ≤ 1 / b + 1 / w) :
    x * p + y * q ≤ 1 + z / w := by
  have hp : 0 ≤ p := hq.trans hqp
  by_cases hbz : b ≤ z
  · calc
      x * p + y * q ≤ b * p + b * q :=
        add_le_add (mul_le_mul_of_nonneg_right hxb hp)
          (mul_le_mul_of_nonneg_right hyb hq)
      _ = b * (p + q) := by ring
      _ ≤ b * (1 / b + 1 / w) := mul_le_mul_of_nonneg_left hpq hb.le
      _ = 1 + b / w := by field_simp
      _ ≤ 1 + z / w := add_le_add le_rfl (div_le_div_of_nonneg_right hbz hw.le)
  · have hzb : z ≤ b := le_of_not_ge hbz
    calc
      x * p + y * q = x * (p - q) + (x + y) * q := by ring
      _ ≤ b * (p - q) + (b + z) * q :=
        add_le_add (mul_le_mul_of_nonneg_right hxb (sub_nonneg.mpr hqp))
          (mul_le_mul_of_nonneg_right hxy hq)
      _ = (b - z) * p + z * (p + q) := by ring
      _ ≤ (b - z) * (1 / b) + z * (1 / b + 1 / w) :=
        add_le_add (mul_le_mul_of_nonneg_left hpb (sub_nonneg.mpr hzb))
          (mul_le_mul_of_nonneg_left hpq hz)
      _ = 1 + z / w := by field_simp; ring

private theorem scalar_bound {x y z b w p q : ℝ}
    (hb : 0 < b) (hw : 0 < w) (hz : 0 ≤ z) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hxb : x ≤ b) (hyb : y ≤ b) (hpb : p ≤ 1 / b) (hqb : q ≤ 1 / b)
    (hxy : x + y ≤ b + z) (hpq : p + q ≤ 1 / b + 1 / w) :
    x * p + y * q ≤ 1 + z / w := by
  rcases le_total q p with hqp | hpq'
  · exact scalar_ordered hb hw hz hq hqp hxb hyb hpb hxy hpq
  · have h := scalar_ordered hb hw hz hp hpq' hyb hxb hqb
      (by simpa only [add_comm] using hxy) (by simpa only [add_comm] using hpq)
    simpa only [add_comm] using h

private theorem reciprocal_supermodular {L : Type*} [Lattice L] {f : L → ℝ}
    (hf : (∀ X, 0 < f X)) (hs : IsSupermodular f) (hl : IsLogSubmodular f) :
    IsSupermodular (fun X => (f X)⁻¹) := by
  intro X Y
  have hlog := hl.2 X Y
  change Real.log (f (X ⊔ Y)) + Real.log (f (X ⊓ Y)) ≤
    Real.log (f X) + Real.log (f Y) at hlog
  rw [← Real.log_mul (ne_of_gt (hf (X ⊔ Y))) (ne_of_gt (hf (X ⊓ Y))),
    ← Real.log_mul (ne_of_gt (hf X)) (ne_of_gt (hf Y))] at hlog
  have hmul := (Real.log_le_log_iff (mul_pos (hf (X ⊔ Y)) (hf (X ⊓ Y)))
    (mul_pos (hf X) (hf Y))).mp hlog
  exact reciprocal_sum_le (hf X) (hf Y) (hf (X ⊔ Y)) (hf (X ⊓ Y)) (hs X Y) hmul

theorem resultSufficiency : D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices.claimSufficiency := by
  intro L _ f hf hmono hs hsi A B C
  have hg : Antitone (fun X => (f X)⁻¹) := by
    intro X Y hXY
    exact inv_le_inv₀ (hf Y) (hf X) |>.2 (hmono hXY)
  have hxy : f (A ⊓ B) + f (B ⊓ C) ≤ f B + f (A ⊓ C) := by
    apply (hs (A ⊓ B) (B ⊓ C)).trans
    apply add_le_add
    · exact hmono (sup_le inf_le_right inf_le_left)
    · exact hmono (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
  have hpq : (f (A ⊔ B))⁻¹ + (f (B ⊔ C))⁻¹ ≤ 1 / f B + 1 / f (A ⊔ C) := by
    have hj : A ⊔ C ≤ (A ⊔ B) ⊔ (B ⊔ C) :=
      sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right)
    have hm : B ≤ (A ⊔ B) ⊓ (B ⊔ C) := le_inf le_sup_right le_sup_left
    have h := (hsi (A ⊔ B) (B ⊔ C)).trans (add_le_add (hg hj) (hg hm))
    simpa only [one_div, add_comm] using h
  have h := scalar_bound (hf B) (hf (A ⊔ C)) (hf (A ⊓ C)).le
    (inv_pos.mpr (hf (A ⊔ B))).le (inv_pos.mpr (hf (B ⊔ C))).le
    (hmono inf_le_right) (hmono inf_le_left)
    (by simpa only [one_div] using hg (show B ≤ A ⊔ B from le_sup_right))
    (by simpa only [one_div] using hg (show B ≤ B ⊔ C from le_sup_left)) hxy hpq
  simp only [jaccardDist, div_eq_mul_inv] at h ⊢
  linarith

theorem result : D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices.claim := by
  intro L _ f hf hmono hs hl
  exact resultSufficiency L f hf hmono hs (reciprocal_supermodular hf hs hl)

end D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices
