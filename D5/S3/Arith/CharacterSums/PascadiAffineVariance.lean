/- GID: D5/S3/Arith/CharacterSums/PascadiAffineVariance
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiAffineVariance
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Direction-restricted affine-line variance and its Pascadi hyperbola instance. -/

module

public import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Weighted affine lines in three dimensions and the normalized Pascadi direction curve. -/

public section

namespace D5.S3.Arith.CharacterSums.PascadiAffineVariance

open scoped BigOperators ComplexConjugate

noncomputable section

variable {p : ℕ} [Fact p.Prime]

abbrev Plane (p : ℕ) := ZMod p × ZMod p

private def transform (f : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  ∑ x : ZMod p, f x * ZMod.stdAddChar (a * x)

private lemma char_sum (a : ZMod p) :
    ∑ x : ZMod p, ZMod.stdAddChar (a * x) = if a = 0 then (p : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h, ZMod.card]
  · simpa only [AddChar.mulShift_apply] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p h))

private lemma char_sum_right (a : ZMod p) :
    ∑ x : ZMod p, ZMod.stdAddChar (x * a) = if a = 0 then (p : ℂ) else 0 := by
  simpa only [mul_comm] using char_sum a

private lemma char_conj (a : ZMod p) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [← AddChar.inv_apply_eq_conj, AddChar.map_neg_eq_inv]

private lemma transform_parseval (f : ZMod p → ℂ) :
    ∑ a : ZMod p, Complex.normSq (transform f a) =
      (p : ℝ) * ∑ x : ZMod p, Complex.normSq (f x) := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self, transform, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, char_conj]
  calc
    _ = ∑ x : ZMod p, ∑ y : ZMod p,
        conj (f x) * f y * ∑ a : ZMod p, ZMod.stdAddChar (a * (y - x)) := by
      rw [Finset.sum_comm]
      congr 1
      ext x
      rw [Finset.sum_comm]
      congr 1
      ext y
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [show a * (y - x) = -(a * x) + a * y by ring,
        AddChar.map_add_eq_mul]
      ring
    _ = (p : ℂ) * ∑ x : ZMod p, conj (f x) * f x := by
      simp_rw [char_sum_right, sub_eq_zero, mul_ite, mul_zero]
      simp [Finset.mul_sum, mul_comm, mul_left_comm]
    _ = _ := by rw [Finset.mul_sum]

private def transform2 (f : Plane p → ℂ) (a : Plane p) : ℂ :=
  ∑ x : Plane p, f x * ZMod.stdAddChar (a.1 * x.1 + a.2 * x.2)

private lemma transform2_parseval (f : Plane p → ℂ) :
    ∑ a : Plane p, Complex.normSq (transform2 f a) =
      (p : ℝ) ^ 2 * ∑ x : Plane p, Complex.normSq (f x) := by
  classical
  have ht (a b : ZMod p) : transform2 f (a,b) =
      transform (fun y => transform (fun x => f (x,y)) a) b := by
    simp only [transform2, transform, Fintype.sum_prod_type,
      AddChar.map_add_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [Fintype.sum_prod_type, ht]
  calc
    _ = ∑ a : ZMod p, (p : ℝ) *
        ∑ y : ZMod p, Complex.normSq (transform (fun x => f (x,y)) a) := by
      simp_rw [transform_parseval]
    _ = (p : ℝ) * ∑ y : ZMod p, ∑ a : ZMod p,
        Complex.normSq (transform (fun x => f (x,y)) a) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (p : ℝ) * ∑ y : ZMod p, (p : ℝ) *
        ∑ x : ZMod p, Complex.normSq (f (x,y)) := by simp_rw [transform_parseval]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      ring

private lemma normSq_sum_le_card_mul {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, z i) ≤ (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (z i) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    _ ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
        Complex.normSq_eq_norm_sq] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖))

private lemma frequency_fiber_bound {ι : Type*} (s : Finset ι)
    (freq : ι → ZMod p) (z : ι → ℂ) (k : ℕ)
    (hk : ∀ a, (s.filter fun i => freq i = a).card ≤ k) :
    ∑ t : ZMod p, Complex.normSq
      (∑ i ∈ s, z i * ZMod.stdAddChar (t * freq i)) ≤
      (p : ℝ) * k * ∑ i ∈ s, Complex.normSq (z i) := by
  classical
  let f : ZMod p → ℂ := fun a => ∑ i ∈ s.filter (fun i => freq i = a), z i
  have he (t : ZMod p) : transform f t =
      ∑ i ∈ s, z i * ZMod.stdAddChar (t * freq i) := by
    simp only [transform, f, Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  simp_rw [← he]
  rw [transform_parseval, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
  calc
    ∑ a : ZMod p, Complex.normSq (f a) ≤
        ∑ a : ZMod p, (k : ℝ) * ∑ i ∈ s.filter (fun i => freq i = a),
          Complex.normSq (z i) := by
      apply Finset.sum_le_sum
      intro a _
      exact (normSq_sum_le_card_mul _ _).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hk a)
          (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp

/-- Coverage by the lines `(b₁,b₂,0) + 𝔽ₚ (u₁,u₂,1)`, with arbitrary complex line weights. -/
def coverage (s : Finset (Plane p)) (c : Plane p → Plane p → ℂ)
    (x : Plane p) (t : ZMod p) : ℂ :=
  ∑ u ∈ s, c u (x.1 - t * u.1, x.2 - t * u.2)

/-- The average coverage: each normalized affine line has `p` points in `p³` space. -/
def coverageMean (s : Finset (Plane p)) (c : Plane p → Plane p → ℂ) : ℂ :=
  (∑ t : ZMod p, ∑ x : Plane p, coverage s c x t) / (p : ℂ) ^ 3

private lemma transform2_coverage (s : Finset (Plane p)) (c : Plane p → Plane p → ℂ)
    (a : Plane p) (t : ZMod p) :
    transform2 (fun x => coverage s c x t) a =
      ∑ u ∈ s, transform2 (c u) a *
        ZMod.stdAddChar (t * (a.1 * u.1 + a.2 * u.2)) := by
  classical
  simp only [transform2, coverage, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Fintype.sum_equiv (Equiv.addRight (-(t * u.1), -(t * u.2)))
  intro x
  change c u (x.1 - t * u.1, x.2 - t * u.2) *
      ZMod.stdAddChar (a.1 * x.1 + a.2 * x.2) =
    c u (x.1 + -(t * u.1), x.2 + -(t * u.2)) *
      ZMod.stdAddChar (a.1 * (x.1 + -(t * u.1)) +
        a.2 * (x.2 + -(t * u.2))) *
      ZMod.stdAddChar (t * (a.1 * u.1 + a.2 * u.2))
  have h : a.1 * x.1 + a.2 * x.2 =
      (a.1 * (x.1 + -(t * u.1)) + a.2 * (x.2 + -(t * u.2))) +
        t * (a.1 * u.1 + a.2 * u.2) := by ring
  rw [h, AddChar.map_add_eq_mul]
  simp only [sub_eq_add_neg]
  ring

private lemma mean_eq_mass (s : Finset (Plane p)) (c : Plane p → Plane p → ℂ) :
    coverageMean s c = (∑ u ∈ s, ∑ b : Plane p, c u b) / (p : ℂ) ^ 2 := by
  classical
  have ht (t : ZMod p) : (∑ x : Plane p, coverage s c x t) =
      ∑ u ∈ s, ∑ b : Plane p, c u b := by
    simpa [transform2] using transform2_coverage s c (0,0) t
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold coverageMean
  simp_rw [ht]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

private lemma transform2_constant (z : ℂ) (a : Plane p) :
    transform2 (fun _ : Plane p => z) a =
      if a = (0,0) then (p : ℂ) ^ 2 * z else 0 := by
  classical
  unfold transform2
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul]
  have hi (x : ZMod p) :
      (∑ y : ZMod p, z * (ZMod.stdAddChar (a.1 * x) * ZMod.stdAddChar (a.2 * y))) =
        (z * ZMod.stdAddChar (a.1 * x)) * ∑ y : ZMod p, ZMod.stdAddChar (a.2 * y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hi]
  rw [← Finset.sum_mul, ← Finset.mul_sum, char_sum, char_sum]
  rcases a with ⟨a,b⟩
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha,hb]
  ring

private lemma transform2_centered (s : Finset (Plane p)) (c : Plane p → Plane p → ℂ)
    (a : Plane p) (t : ZMod p) :
    transform2 (fun x => coverage s c x t - coverageMean s c) a =
      if a = (0,0) then 0 else
        ∑ u ∈ s, transform2 (c u) a *
          ZMod.stdAddChar (t * (a.1 * u.1 + a.2 * u.2)) := by
  classical
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [show transform2 (fun x => coverage s c x t - coverageMean s c) a =
      transform2 (fun x => coverage s c x t) a -
        transform2 (fun _ => coverageMean s c) a by
      simp [transform2, sub_mul, Finset.sum_sub_distrib]]
  rw [transform2_coverage, transform2_constant]
  by_cases ha : a = (0,0)
  · subst a
    simp only [ite_true, zero_mul, mul_zero, zero_add, AddChar.map_zero_eq_one, mul_one]
    rw [mean_eq_mass]
    simp only [transform2, zero_mul, zero_add, AddChar.map_zero_eq_one, mul_one]
    field_simp
    ring
  · simp [ha]

/-- A direction family meeting every nonzero linear annihilator plane at most `k` times
has centered line-coverage variance at most `k * p` times the squared line-weight mass. -/
theorem direction_restricted_variance (s : Finset (Plane p)) (k : ℕ)
    (hk : ∀ a b d : ZMod p, a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0 →
      (s.filter fun u => a * u.1 + b * u.2 + d = 0).card ≤ k)
    (c : Plane p → Plane p → ℂ) :
    (∑ t : ZMod p, ∑ x : Plane p,
      Complex.normSq (coverage s c x t - coverageMean s c)) ≤
        (k : ℝ) * p * ∑ u ∈ s, ∑ b : Plane p, Complex.normSq (c u b) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hp)).mp
  calc
    _ = ∑ a : Plane p, ∑ t : ZMod p, Complex.normSq
        (transform2 (fun x => coverage s c x t - coverageMean s c) a) := by
      conv_rhs => rw [Finset.sum_comm]
      simp_rw [transform2_parseval]
      rw [← Finset.mul_sum]
    _ ≤ ∑ a : Plane p, (p : ℝ) * k * ∑ u ∈ s,
        Complex.normSq (transform2 (c u) a) := by
      apply Finset.sum_le_sum
      intro a _
      simp_rw [transform2_centered]
      by_cases ha : a = (0,0)
      · simp only [ha, ite_true, map_zero, Finset.sum_const_zero]
        exact mul_nonneg (mul_nonneg hp.le (Nat.cast_nonneg k))
          (Finset.sum_nonneg fun u _ => Complex.normSq_nonneg _)
      · simp only [ha, ite_false]
        apply frequency_fiber_bound
        intro v
        have hn : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
          by_contra! h
          exact ha (Prod.ext h.1 h.2)
        have hh := hk a.1 a.2 (-v) (hn.elim Or.inl (fun h => Or.inr (Or.inl h)))
        simpa only [add_neg_eq_zero] using hh
    _ = _ := by
      rw [← Finset.mul_sum]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp_rw [transform2_parseval]
      rw [← Finset.mul_sum]
      ring

private lemma quadratic_card_le_two {F : Type*} [Field F]
    (s : Finset F) (A B C : F) (hcoeff : ¬ (A = 0 ∧ B = 0 ∧ C = 0))
    (hs : ∀ x ∈ s, A * x ^ 2 + B * x + C = 0) : s.card ≤ 2 := by
  classical
  by_cases he : s.Nonempty
  · obtain ⟨r,hr⟩ := he
    have hrr := hs r hr
    by_cases hA : A = 0
    · have hB : B ≠ 0 := by
        intro hB
        exact hcoeff ⟨hA,hB,by simpa [hA,hB] using hrr⟩
      have hsub : s ⊆ {r} := by
        intro x hx
        have hx' : B * x + C = 0 := by simpa [hA] using hs x hx
        have hr' : B * r + C = 0 := by simpa [hA] using hrr
        have hh : B * x = B * r := by linear_combination hx' - hr'
        simpa using mul_left_cancel₀ hB hh
      exact (Finset.card_le_card hsub).trans (by simp)
    · have hsub : s ⊆ {r, -(A * r + B)/A} := by
        intro x hx
        have hh : (x-r) * (A * (x + r) + B) = 0 := by
          linear_combination hs x hx - hrr
        rcases mul_eq_zero.mp hh with h | h
        · simp [sub_eq_zero.mp h]
        · have hax : A * x = -(A * r + B) := by linear_combination h
          have hx' : x = -(A * r + B)/A := (eq_div_iff hA).mpr (by simpa [mul_comm] using hax)
          simp [hx']
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

private lemma word_denominator_ne_zero {F : Type*} [Field F] {D : F}
    (hD : D ≠ -1) (u : F × F) (hu : u.1 + u.2 + 1 = D * u.1 * u.2) :
    D * u.1-1 ≠ 0 := by
  intro h
  have hd : D * u.1 = 1 := sub_eq_zero.mp h
  have hx : u.1 = -1 := by linear_combination hu + u.2 * hd
  rw [hx] at hd
  apply hD
  linear_combination -hd

private lemma word_first_injective {F : Type*} [Field F] {D : F}
    (hD : D ≠ -1) (s : Finset (F × F))
    (hs : ∀ u ∈ s, u.1 + u.2 + 1 = D * u.1 * u.2) :
    Set.InjOn Prod.fst (s : Set (F × F)) := by
  intro u hu v hv he
  apply Prod.ext he
  have hv' := hs v hv
  rw [← he] at hv'
  apply mul_left_cancel₀ (word_denominator_ne_zero hD u (hs u hu))
  linear_combination -(hs u hu) + hv'

private lemma hyperbola_plane_card (D : ZMod p) (hD : D ≠ 0) (hne : D ≠ -1)
    (s : Finset (Plane p)) (hs : ∀ u ∈ s, u.1 + u.2 + 1 = D * u.1 * u.2)
    (a b d : ZMod p) (habd : a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0) :
    (s.filter fun u => a * u.1 + b * u.2 + d = 0).card ≤ 2 := by
  classical
  let t := s.filter fun u => a * u.1 + b * u.2 + d = 0
  have hinj : Set.InjOn Prod.fst (t : Set (Plane p)) :=
    (word_first_injective hne s hs).mono (by intro u hu; exact (Finset.mem_filter.mp hu).1)
  rw [← Finset.card_image_iff.mpr hinj]
  apply quadratic_card_le_two _ (D * a) (D * d + b-a) (b-d)
  · rintro ⟨ha,hb,hd⟩
    have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_left hD
    have hDb : (D + 1) * b = 0 := by linear_combination hb + D * hd + ha0
    have hb0 : b = 0 := (mul_eq_zero.mp hDb).resolve_left (by
      intro h
      exact hne (add_eq_zero_iff_eq_neg.mp h))
    have hd0 : d = 0 := by linear_combination hb0 - hd
    rcases habd with h | h | h
    · exact h ha0
    · exact h hb0
    · exact h hd0
  · intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    have hu' := Finset.mem_filter.mp hu
    linear_combination (D * u.1-1) * hu'.2 + b * (hs u hu'.1)

/-- The normalized admissible Pascadi word directions. -/
def pascadiDirections (D : ZMod p) : Finset (Plane p) :=
  Finset.univ.filter fun u => u.1 ≠ 0 ∧ u.2 ≠ 0 ∧ u.1 + u.2 ≠ 0 ∧
    u.1 + 1 ≠ 0 ∧ u.2 + 1 ≠ 0 ∧ u.1 + u.2 + 1 = D * u.1 * u.2

/-- On the Pascadi hyperbola with `D` a unit and `D ≠ -1`, the actual normalized
affine-line coverage has centered variance at most `2 * p` times its squared weights. -/
theorem pascadi_affine_variance (D : ZMod p) (hD : D ≠ 0) (hne : D ≠ -1)
    (c : Plane p → Plane p → ℂ) :
    (∑ t : ZMod p, ∑ x : Plane p,
      Complex.normSq (coverage (pascadiDirections D) c x t -
        coverageMean (pascadiDirections D) c)) ≤
      2 * (p : ℝ) * ∑ u ∈ pascadiDirections D, ∑ b : Plane p,
        Complex.normSq (c u b) := by
  apply direction_restricted_variance _ 2 _ c
  intro a b d hd
  apply hyperbola_plane_card D hD hne _ _ a b d hd
  intro u hu
  exact (Finset.mem_filter.mp hu).2.2.2.2.2.2

end

end D5.S3.Arith.CharacterSums.PascadiAffineVariance
