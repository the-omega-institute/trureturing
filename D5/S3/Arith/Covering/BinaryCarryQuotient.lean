/- GID: D5/S3/Arith/Covering/BinaryCarryQuotient
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/BinaryCarryQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Binary congruence covers descend with activation and the original phase carries. -/

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Covering.BinaryCarryQuotient

/-- A congruence row with its original, unrestricted phase. -/
structure Row where
  e : ℤ
  a : ℤ
  b : ℤ
  c : ℤ

def Row.covers (r : Row) (k l : ℤ) : Prop := r.e ∣ r.a * k + r.b * l - r.c

def Row.scaled (r : Row) (M k l : ℤ) : ℤ :=
  (2 * M / r.e) * (r.a * k + r.b * l - r.c)

/-- The top cohort is exactly the rows with odd period quotient. -/
def Row.top (r : Row) (M : ℤ) : Prop := (2 * M / r.e) % 2 = 1

def Row.normal (r : Row) : ℤ × ℤ := (r.a % 2, r.b % 2)

def Row.active (r : Row) (M k l : ℤ) : Prop := M ∣ r.scaled M k l

/-- The pair and triple predicates retain activation and the same phases. -/
def Criterion {ι : Type*} (rows : ι → Row) (M k l : ℤ) : Prop :=
  (∃ i, ¬ (rows i).top M ∧ (rows i).covers k l) ∨
  (∃ i j, i ≠ j ∧ (rows i).top M ∧ (rows j).top M ∧
    (rows i).normal = (rows j).normal ∧
    (rows i).active M k l ∧ (rows j).active M k l ∧
    (rows i).scaled M k l + (rows j).scaled M k l ≡ M [ZMOD 2 * M]) ∨
  (∃ i j h, (rows i).top M ∧ (rows j).top M ∧ (rows h).top M ∧
    (rows i).normal ≠ (rows j).normal ∧ (rows i).normal ≠ (rows h).normal ∧
    (rows j).normal ≠ (rows h).normal ∧
    (rows i).active M k l ∧ (rows j).active M k l ∧ (rows h).active M k l ∧
    (rows i).scaled M k l + (rows j).scaled M k l + (rows h).scaled M k l ≡
      0 [ZMOD 2 * M])

/-- Arbitrary families of active nonzero-normal binary lines cover precisely by
complementary parallel pairs or a triple of distinct directions with even carry. -/
theorem plane_cover_iff {ι : Type*} (A : ι → Prop) (a b d : ι → Fin 2)
    (hn : ∀ i, A i → a i ≠ 0 ∨ b i ≠ 0) :
    (∀ u v : Fin 2, ∃ i, A i ∧
      ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (d i : ℤ)) % 2 = 0) ↔
    (∃ i j, A i ∧ A j ∧ a i = a j ∧ b i = b j ∧ d i ≠ d j) ∨
    (∃ i j h, A i ∧ A j ∧ A h ∧
      (a i, b i) ≠ (a j, b j) ∧ (a i, b i) ≠ (a h, b h) ∧
      (a j, b j) ≠ (a h, b h) ∧
      ((d i : ℤ) + (d j : ℤ) + (d h : ℤ)) % 2 = 0) := by
  classical
  let P (x y z : Fin 2) := ∃ i, A i ∧ a i = x ∧ b i = y ∧ d i = z
  have line (u v : Fin 2) :
      (∃ i, A i ∧ ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) +
        (d i : ℤ)) % 2 = 0) ↔ P 1 0 u ∨ P 0 1 v ∨ P 1 1 (u + v) := by
    constructor
    · rintro ⟨i, hi, hc⟩
      have hn' := hn i hi
      rcases (show a i = 0 ∨ a i = 1 by omega) with ha | ha <;>
        rcases (show b i = 0 ∨ b i = 1 by omega) with hb | hb
      · simp [ha, hb] at hn'
      · right; left
        refine ⟨i, hi, ha, hb, ?_⟩
        apply Fin.ext
        simp [ha, hb] at hc
        have := (d i).isLt
        have := v.isLt
        omega
      · left
        refine ⟨i, hi, ha, hb, ?_⟩
        apply Fin.ext
        simp [ha, hb] at hc
        have := (d i).isLt
        have := u.isLt
        omega
      · right; right
        refine ⟨i, hi, ha, hb, ?_⟩
        apply Fin.ext
        simp [ha, hb] at hc
        fin_cases u <;> fin_cases v <;> simp at hc ⊢ <;> have := (d i).isLt <;> omega
    · intro hc
      rcases hc with h | h | h <;>
        obtain ⟨i, hi, ha, hb, hd⟩ := h <;>
        refine ⟨i, hi, ?_⟩ <;> rw [ha, hb, hd] <;>
        fin_cases u <;> fin_cases v <;> norm_num
  have four :
      (∀ u v : Fin 2, P 1 0 u ∨ P 0 1 v ∨ P 1 1 (u + v)) ↔
      (P 1 0 0 ∧ P 1 0 1) ∨ (P 0 1 0 ∧ P 0 1 1) ∨ (P 1 1 0 ∧ P 1 1 1) ∨
      (P 1 0 0 ∧ P 0 1 0 ∧ P 1 1 0) ∨ (P 1 0 0 ∧ P 0 1 1 ∧ P 1 1 1) ∨
      (P 1 0 1 ∧ P 0 1 0 ∧ P 1 1 1) ∨ (P 1 0 1 ∧ P 0 1 1 ∧ P 1 1 0) := by
    have logic (p q r s t w : Prop) :
        ((p ∨ r ∨ t) ∧ (p ∨ s ∨ w)) ∧ ((q ∨ r ∨ w) ∧ (q ∨ s ∨ t)) ↔
        (p ∧ q) ∨ (r ∧ s) ∨ (t ∧ w) ∨ (p ∧ r ∧ t) ∨ (p ∧ s ∧ w) ∨
          (q ∧ r ∧ w) ∨ (q ∧ s ∧ t) := by
      clear line hn P
      tauto
    simpa only [Fin.forall_fin_two, zero_add, add_zero,
      show (1 : Fin 2) + 1 = 0 by decide] using
      logic (P 1 0 0) (P 1 0 1) (P 0 1 0) (P 0 1 1) (P 1 1 0) (P 1 1 1)
  rw [show (∀ u v : Fin 2, ∃ i, A i ∧
      ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (d i : ℤ)) % 2 = 0) ↔
      (∀ u v : Fin 2, P 1 0 u ∨ P 0 1 v ∨ P 1 1 (u + v)) from
      forall_congr' fun u => forall_congr' fun v => line u v, four]
  constructor
  · intro hc
    rcases hc with h | h | h | h | h | h | h
    all_goals
      rcases h with ⟨h₁, h₂⟩
      obtain ⟨i, hi, ai, bi, di⟩ := h₁
    · obtain ⟨j, hj, aj, bj, dj⟩ := h₂
      exact Or.inl ⟨i, j, hi, hj, ai.trans aj.symm, bi.trans bj.symm, by omega⟩
    · obtain ⟨j, hj, aj, bj, dj⟩ := h₂
      exact Or.inl ⟨i, j, hi, hj, ai.trans aj.symm, bi.trans bj.symm, by omega⟩
    · obtain ⟨j, hj, aj, bj, dj⟩ := h₂
      exact Or.inl ⟨i, j, hi, hj, ai.trans aj.symm, bi.trans bj.symm, by omega⟩
    all_goals
      obtain ⟨⟨j, hj, aj, bj, dj⟩, ⟨h, hh, ah, bh, dh⟩⟩ := h₂
      refine Or.inr ⟨i, j, h, hi, hj, hh, ?_, ?_, ?_, ?_⟩ <;>
        simp [ai, bi, di, aj, bj, dj, ah, bh, dh]
  · intro hc
    apply four.mp
    intro u v
    apply (line u v).mp
    rcases hc with ⟨i, j, hi, hj, ha, hb, hd⟩ | ⟨i, j, h, hi, hj, hh, hij, hih, hjh, hd⟩
    · by_cases hc : ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (d i : ℤ)) % 2 = 0
      · exact ⟨i, hi, hc⟩
      · refine ⟨j, hj, ?_⟩
        rw [← ha, ← hb]
        have := (d i).isLt
        have := (d j).isLt
        have : (d i : ℤ) ≠ (d j : ℤ) := by
          intro hc; apply hd; apply Fin.ext; exact_mod_cast hc
        omega
    · have ni := hn i hi
      have nj := hn j hj
      have nh := hn h hh
      simp only [ne_eq, Prod.mk.injEq, not_and_or] at hij hih hjh
      have asum : (a i : ℤ) + (a j : ℤ) + (a h : ℤ) = 2 := by omega
      have bsum : (b i : ℤ) + (b j : ℤ) + (b h : ℤ) = 2 := by omega
      have total :
          ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (d i : ℤ)) +
          ((a j : ℤ) * (u : ℤ) + (b j : ℤ) * (v : ℤ) + (d j : ℤ)) +
          ((a h : ℤ) * (u : ℤ) + (b h : ℤ) * (v : ℤ) + (d h : ℤ)) =
          2 * ((u : ℤ) + (v : ℤ)) + ((d i : ℤ) + (d j : ℤ) + (d h : ℤ)) := by
        calc
          _ = ((a i : ℤ) + (a j : ℤ) + (a h : ℤ)) * (u : ℤ) +
              ((b i : ℤ) + (b j : ℤ) + (b h : ℤ)) * (v : ℤ) +
              ((d i : ℤ) + (d j : ℤ) + (d h : ℤ)) := by ring
          _ = _ := by rw [asum, bsum]; ring
      by_cases ci : ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) + (d i : ℤ)) % 2 = 0
      · exact ⟨i, hi, ci⟩
      by_cases cj : ((a j : ℤ) * (u : ℤ) + (b j : ℤ) * (v : ℤ) + (d j : ℤ)) % 2 = 0
      · exact ⟨j, hj, cj⟩
      exact ⟨h, hh, by omega⟩

/-- Phase-preserving descent for every positive even period. The first clause is
the exact four-lift criterion; the second is representative invariance; the last
two identify full integer and original-period coverage with finite quotient coverage.
Only the nonzero top-normal consequence of primitivity is needed. -/
theorem result {ι : Type*} (rows : ι → Row) (M : ℤ) (hM : 0 < M)
    (he : ∀ i, 0 < (rows i).e ∧ (rows i).e ∣ 2 * M)
    (hn : ∀ i, (rows i).top M → (rows i).normal ≠ (0, 0)) :
    (∀ k l : ℤ, (∀ u v : Fin 2, ∃ i,
      (rows i).covers (k + M * (u : ℤ)) (l + M * (v : ℤ))) ↔ Criterion rows M k l) ∧
    (∀ k l z w : ℤ, Criterion rows M (k + M * z) (l + M * w) ↔
      Criterion rows M k l) ∧
    ((∀ k l : ℤ, ∃ i, (rows i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion rows M k l) ∧
    ((∀ k l : ℤ, 0 ≤ k → k < 2 * M → 0 ≤ l → l < 2 * M →
      ∃ i, (rows i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion rows M k l) := by
  classical
  let q (i : ι) := 2 * M / (rows i).e
  have qe (i : ι) : q i * (rows i).e = 2 * M := Int.ediv_mul_cancel (he i).2
  have qne (i : ι) : q i ≠ 0 := by intro hz; have := qe i; rw [hz] at this; omega
  have scale (i : ι) (k l : ℤ) :
      (rows i).covers k l ↔ 2 * M ∣ (rows i).scaled M k l := by
    change (rows i).e ∣ _ ↔ 2 * M ∣ q i * _
    rw [← qe i, Int.mul_dvd_mul_iff_left (qne i)]
  have shift (i : ι) (k l u v : ℤ) :
      (rows i).scaled M (k + M * u) (l + M * v) =
      (rows i).scaled M k l + M * (q i * ((rows i).a * u + (rows i).b * v)) := by
    dsimp [Row.scaled, q]; ring
  have split (f t : ℤ) :
      (2 * M ∣ f + M * t) ↔ M ∣ f ∧ (f / M + t) % 2 = 0 := by
    constructor
    · intro h
      have hf : M ∣ f := by
        have h' : M ∣ f + M * t := dvd_trans (by exact ⟨2, by ring⟩) h
        exact (Int.dvd_add_left (dvd_mul_right M t)).mp h'
      refine ⟨hf, ?_⟩
      rw [show f + M * t = M * (f / M + t) by
        rw [mul_add, Int.mul_ediv_cancel_of_dvd hf], mul_comm 2 M,
        Int.mul_dvd_mul_iff_left (ne_of_gt hM)] at h
      exact Int.emod_eq_zero_of_dvd h
    · rintro ⟨hf, ht⟩
      rw [show f + M * t = M * (f / M + t) by
        rw [mul_add, Int.mul_ediv_cancel_of_dvd hf], mul_comm 2 M,
        Int.mul_dvd_mul_iff_left (ne_of_gt hM)]
      exact Int.dvd_of_emod_eq_zero ht
  have lift (i : ι) (k l u v : ℤ) :
      (rows i).covers (k + M * u) (l + M * v) ↔
      (¬ (rows i).top M ∧ (rows i).covers k l) ∨
      ((rows i).top M ∧ (rows i).active M k l ∧
        ((rows i).scaled M k l / M + (rows i).a * u + (rows i).b * v) % 2 = 0) := by
    rw [scale, shift]
    by_cases ht : (rows i).top M
    · have hq : q i % 2 = 1 := ht
      simp only [ht, not_true_eq_false, false_and, true_and, false_or, Row.active]
      rw [split]
      simp [Int.add_emod, Int.mul_emod, hq, add_assoc]
    · have hq : q i % 2 = 0 := by unfold Row.top at ht; dsimp [q]; omega
      simp only [ht, not_false_eq_true, true_and, false_and, or_false]
      rw [scale, split]
      have hs := split ((rows i).scaled M k l) 0
      simp only [mul_zero, add_zero] at hs
      rw [hs]
      simp [Int.add_emod, Int.mul_emod, hq]
  let bit (z : ℤ) : Fin 2 := ⟨(z % 2).toNat, by omega⟩
  have bitval (z : ℤ) : ((bit z : Fin 2) : ℤ) = z % 2 := by dsimp [bit]; omega
  have bit_eq (x y : ℤ) : bit x = bit y ↔ x % 2 = y % 2 := by
    constructor
    · intro h; simpa only [bitval] using congrArg (fun t : Fin 2 => (t : ℤ)) h
    · intro h; apply Fin.ext; simp [bit, h]
  have local_equiv (k l : ℤ) :
      (∀ u v : Fin 2, ∃ i,
        (rows i).covers (k + M * (u : ℤ)) (l + M * (v : ℤ))) ↔
      Criterion rows M k l := by
    let A (i : ι) := (rows i).top M ∧ (rows i).active M k l
    let a (i : ι) := bit (rows i).a
    let b (i : ι) := bit (rows i).b
    let d (i : ι) := bit ((rows i).scaled M k l / M)
    have nonzero (i : ι) (hi : A i) : a i ≠ 0 ∨ b i ≠ 0 := by
      have hn' := hn i hi.1
      by_contra h
      push Not at h
      have ha := congrArg (fun t : Fin 2 => (t : ℤ)) h.1
      have hb := congrArg (fun t : Fin 2 => (t : ℤ)) h.2
      simp only [a, b, bitval, Fin.val_zero, Int.natCast_zero] at ha hb
      exact hn' (Prod.ext ha hb)
    have lines (u v : Fin 2) :
        (∃ i, (rows i).covers (k + M * (u : ℤ)) (l + M * (v : ℤ))) ↔
        (∃ i, ¬ (rows i).top M ∧ (rows i).covers k l) ∨
        ∃ i, A i ∧ ((a i : ℤ) * (u : ℤ) + (b i : ℤ) * (v : ℤ) +
          (d i : ℤ)) % 2 = 0 := by
      simp only [lift, exists_or, A, a, b, d, bitval]
      apply or_congr Iff.rfl
      apply exists_congr
      intro i
      simp only [and_assoc]
      apply and_congr_right; intro _
      apply and_congr_right; intro _
      simp only [Int.add_emod, Int.mul_emod, Int.emod_emod]
      omega
    have carry (i : ι) (hi : A i) :
        (rows i).scaled M k l = M * ((rows i).scaled M k l / M) :=
      (Int.mul_ediv_cancel_of_dvd hi.2).symm
    have pair (i j : ι) (hi : A i) (hj : A j) :
        d i ≠ d j ↔ (rows i).scaled M k l + (rows j).scaled M k l ≡
          M [ZMOD 2 * M] := by
      change bit _ ≠ bit _ ↔ _
      rw [ne_eq, bit_eq, Int.modEq_iff_dvd]
      rw [show M - ((rows i).scaled M k l + (rows j).scaled M k l) =
          M * (1 - ((rows i).scaled M k l / M + (rows j).scaled M k l / M)) by
        conv_lhs => rw [carry i hi, carry j hj]
        ring, mul_comm 2 M, Int.mul_dvd_mul_iff_left (ne_of_gt hM),
        Int.dvd_iff_emod_eq_zero]
      omega
    have triple (i j h : ι) (hi : A i) (hj : A j) (hh : A h) :
        ((d i : ℤ) + (d j : ℤ) + (d h : ℤ)) % 2 = 0 ↔
        (rows i).scaled M k l + (rows j).scaled M k l + (rows h).scaled M k l ≡
          0 [ZMOD 2 * M] := by
      rw [carry i hi, carry j hj, carry h hh, ← mul_add, ← mul_add]
      rw [Int.modEq_zero_iff_dvd, mul_comm 2 M,
        Int.mul_dvd_mul_iff_left (ne_of_gt hM), Int.dvd_iff_emod_eq_zero]
      simp [d, bitval, Int.add_emod]
    have normals (i j : ι) : (a i, b i) = (a j, b j) ↔
        (rows i).normal = (rows j).normal := by
      simp only [Prod.mk.injEq, a, b, bit_eq, Row.normal]
    simp_rw [lines, forall_or_left]
    rw [plane_cover_iff A a b d nonzero]
    unfold Criterion
    apply or_congr Iff.rfl
    constructor
    · rintro (⟨i, j, hi, hj, ha, hb, hd⟩ | ⟨i, j, h, hi, hj, hh, hij, hih, hjh, hd⟩)
      · exact Or.inl ⟨i, j, by intro heq; subst j; exact hd rfl,
          hi.1, hj.1, (normals i j).mp (Prod.ext ha hb), hi.2, hj.2,
          (pair i j hi hj).mp hd⟩
      · exact Or.inr ⟨i, j, h, hi.1, hj.1, hh.1,
          fun heq => hij ((normals i j).mpr heq),
          fun heq => hih ((normals i h).mpr heq),
          fun heq => hjh ((normals j h).mpr heq), hi.2, hj.2, hh.2,
          (triple i j h hi hj hh).mp hd⟩
    · rintro (⟨i, j, _, hi, hj, hij, hai, haj, hc⟩ |
        ⟨i, j, h, hi, hj, hh, hij, hih, hjh, hai, haj, hah, hc⟩)
      · have heq := (normals i j).mpr hij
        exact Or.inl ⟨i, j, ⟨hi, hai⟩, ⟨hj, haj⟩, congrArg Prod.fst heq,
          congrArg Prod.snd heq, (pair i j ⟨hi, hai⟩ ⟨hj, haj⟩).mpr hc⟩
      · exact Or.inr ⟨i, j, h, ⟨hi, hai⟩, ⟨hj, haj⟩, ⟨hh, hah⟩,
          fun heq => hij ((normals i j).mp heq),
          fun heq => hih ((normals i h).mp heq),
          fun heq => hjh ((normals j h).mp heq),
          (triple i j h ⟨hi, hai⟩ ⟨hj, haj⟩ ⟨hh, hah⟩).mpr hc⟩
  have all_lifts (k l : ℤ) :
      (∀ u v : Fin 2, ∃ i, (rows i).covers (k + M * (u : ℤ)) (l + M * (v : ℤ))) ↔
      ∀ z w : ℤ, ∃ i, (rows i).covers (k + M * z) (l + M * w) := by
    constructor
    · intro h z w
      obtain ⟨i, hi⟩ := h (bit z) (bit w)
      refine ⟨i, ?_⟩
      rw [lift] at hi ⊢
      simpa only [bitval, Int.add_emod, Int.mul_emod, Int.emod_emod] using hi
    · intro h u v; exact h (u : ℤ) (v : ℤ)
  have shift_criterion (k l z w : ℤ) :
      Criterion rows M (k + M * z) (l + M * w) ↔ Criterion rows M k l := by
    rw [← local_equiv, ← local_equiv, all_lifts, all_lifts]
    constructor
    · intro h s t
      simpa only [show k + M * z + M * (s - z) = k + M * s by ring,
        show l + M * w + M * (t - w) = l + M * t by ring] using h (s - z) (t - w)
    · intro h s t
      simpa only [show k + M * (z + s) = k + M * z + M * s by ring,
        show l + M * (w + t) = l + M * w + M * t by ring] using h (z + s) (w + t)
  have global_equiv : (∀ k l : ℤ, ∃ i, (rows i).covers k l) ↔
      ∀ k l : ℤ, 0 ≤ k → k < M → 0 ≤ l → l < M → Criterion rows M k l := by
    constructor
    · intro h k l _ _ _ _
      exact (local_equiv k l).mp (fun u v => h _ _)
    · intro h k l
      have hbase := h (k % M) (l % M) (Int.emod_nonneg _ (ne_of_gt hM))
        (Int.emod_lt_of_pos _ hM) (Int.emod_nonneg _ (ne_of_gt hM))
        (Int.emod_lt_of_pos _ hM)
      have hfiber := (all_lifts _ _).mp ((local_equiv _ _).mpr hbase)
      simpa only [Int.emod_add_mul_ediv] using hfiber (k / M) (l / M)
  refine ⟨local_equiv, shift_criterion, global_equiv, ?_⟩
  constructor
  · intro h k l hk hkM hl hlM
    apply (local_equiv k l).mp
    intro u v
    have hu : 0 ≤ (u : ℤ) ∧ (u : ℤ) < 2 := ⟨by positivity, by exact_mod_cast u.isLt⟩
    have hv : 0 ≤ (v : ℤ) ∧ (v : ℤ) < 2 := ⟨by positivity, by exact_mod_cast v.isLt⟩
    exact h _ _ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  · intro h k l _ _ _ _
    exact global_equiv.mpr h k l

end D5.S3.Arith.Covering.BinaryCarryQuotient
