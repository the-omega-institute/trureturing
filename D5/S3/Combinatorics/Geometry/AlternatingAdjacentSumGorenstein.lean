/- GID: D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Alternating adjacent sums force the unique Gorenstein pair s = 3, r = 1. -/

/-
result
  proof_shape: content
  escape_witness: index_center; not_gorenstein_large_dimension
  admission_basis: open-problem-resolution (#14591; Proved)
  Direct frozen dependencies: none (pinned Mathlib only).

Private theorem judgement form (consumer -> prerequisite):
  bound_ge: bind-only; consumers full_dimensional, index_center,
    not_gorenstein_large_dimension.
  mem_scaled: bind-only; consumers mem_interior_scaled, mem_scaled_two,
    not_gorenstein_large_dimension.
  strict_open: bind-only; consumer mem_interior_scaled.
  interior_coordinate: bind-only; consumer mem_interior_scaled.
  interior_sum: bind-only; consumer mem_interior_scaled.
  mem_interior_scaled: bind-only; consumers full_dimensional, index_center,
    not_gorenstein_large_dimension, mem_interior_two.
  full_dimensional: bind-only; consumer mem_zero_scaled.
  mem_zero_scaled: bind-only; consumers unique_at_zero, gorenstein_three_two.
  coe_eq_zero: bind-only; consumers unique_at_zero, gorenstein_three_two.
  unique_at_zero: bind-only; consumer index_center.
  index_center: content; consumers not_gorenstein_large_dimension, result.
    New construction: uniqueness of the interior lattice point forces q*s = 3
    and c = 1 by comparing c, 1 and (2,1,...,1).
  not_gorenstein_large_dimension: content; consumer result.
    New construction: w = (1,4,3,1,...) is interior to 2P in every d >= 3,
    while w - 1 violates its second adjacent-sum inequality.
  mem_scaled_two: bind-only; consumer gorenstein_three_two.
  mem_interior_two: bind-only; consumer gorenstein_three_two.
  gorenstein_three_two: bind-only; consumer result.
    The source's dimension-two case is a triangle translation, with index one.

Utility none: all statements are parameterized geometric arguments, not
finite enumerations, checkers, numerical reductions or fixed certificates.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

open Set
open scoped Pointwise
namespace D5.S3.Combinatorics.Geometry.AlternatingAdjacentSumGorenstein

private def bound (s : ℕ) (i : ℕ) : ℝ := (s : ℝ) + if (i + 1) % 2 = 0 then 1 else 0

def P (s d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j : Fin d, j.val = i.val + 1 → x i + x j ≤
    (s : ℝ) + (if (i.val + 1) % 2 = 0 then 1 else 0)}

def IsGorenstein (s d : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ ∃ c : Fin d → ℤ, ∀ n : ℕ, ∀ x : Fin d → ℤ,
    ((fun i => (x i : ℝ)) ∈ interior (((n + q : ℕ) : ℝ) • P s d) ↔
      (fun i => ((x - c) i : ℝ)) ∈ ((n : ℝ) • P s d))

def claim : Prop := ∀ s r : ℕ, 2 ≤ s → 1 ≤ r →
  (IsGorenstein s (2*r) ↔ s = 3 ∧ r = 1)


private theorem bound_ge (s i : ℕ) : (s : ℝ) ≤ bound s i := by
  unfold bound
  split <;> linarith

private theorem mem_scaled {s d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    x ∈ t • P s d ↔
      (∀ i, 0 ≤ x i) ∧ ∀ i j : Fin d, j.val = i.val + 1 → x i + x j ≤ t * bound s i.val := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i => mul_nonneg ht.le (hy.1 i), fun i j hij => ?_⟩
    change t * y i + t * y j ≤ t * bound s i.val
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hy.2 i j hij) ht.le
  · rintro ⟨hx, hsum⟩
    refine ⟨fun i => x i / t, ⟨fun i => div_nonneg (hx i) ht.le, ?_⟩, ?_⟩
    · intro i j hij
      rw [← add_div, div_le_iff₀ ht]
      simpa only [bound, mul_comm] using hsum i j hij
    · ext i
      change t * (x i / t) = x i
      field_simp

private theorem strict_open (s d : ℕ) (t : ℝ) :
    IsOpen {x : Fin d → ℝ | (∀ i, 0 < x i) ∧
      ∀ i j : Fin d, j.val = i.val + 1 → x i + x j < t * bound s i.val} := by
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter ?_
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_iInter_of_finite fun _ =>
    isOpen_lt ((continuous_apply i).add (continuous_apply j)) continuous_const

private theorem interior_coordinate {d : ℕ} (i : Fin d) (x : Fin d → ℝ) :
    x ∈ interior {y : Fin d → ℝ | 0 ≤ y i} ↔ 0 < x i := by
  have he := IsOpenMap.preimage_interior_eq_interior_preimage
    (isOpenMap_eval (X := fun _ : Fin d => ℝ) i) (continuous_apply i) (Set.Ici (0 : ℝ))
  change x ∈ interior (Function.eval i ⁻¹' Set.Ici (0 : ℝ)) ↔ _
  rw [← he, interior_Ici]
  rfl

private theorem interior_sum {d : ℕ} (i j : Fin d) (a : ℝ) (x : Fin d → ℝ) :
    x ∈ interior {y : Fin d → ℝ | y i + y j ≤ a} ↔ x i + x j < a := by
  let f : (Fin d → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) + ContinuousLinearMap.proj j
  have hs : Function.Surjective f := by
    intro z
    refine ⟨fun _ => z/2, ?_⟩
    change z/2 + z/2 = z
    ring
  have he := f.interior_preimage hs (Set.Iic a)
  change x ∈ interior (f ⁻¹' Set.Iic a) ↔ _
  rw [he, interior_Iic]
  rfl

private theorem mem_interior_scaled {s d : ℕ} {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    x ∈ interior (t • P s d) ↔
      (∀ i, 0 < x i) ∧ ∀ i j : Fin d, j.val = i.val + 1 → x i + x j < t * bound s i.val := by
  constructor
  · intro hx
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · apply (interior_coordinate i x).mp
      exact interior_mono (fun y hy => ((mem_scaled ht y).mp hy).1 i) hx
    · apply (interior_sum i j (t * bound s i.val) x).mp
      exact interior_mono (fun y hy => ((mem_scaled ht y).mp hy).2 i j hij) hx
  · intro hx
    apply mem_interior.mpr
    refine ⟨_, ?_, strict_open s d t, hx⟩
    intro y hy
    exact (mem_scaled ht y).mpr ⟨fun i => (hy.1 i).le, fun i j hij => (hy.2 i j hij).le⟩

private theorem full_dimensional {s d : ℕ} (hs : 1 ≤ s) : (interior (P s d)).Nonempty := by
  have hpos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hc : (fun _ : Fin d => (s : ℝ) / 4) ∈ interior ((1 : ℝ) • P s d) := by
    apply (mem_interior_scaled zero_lt_one _).mpr
    refine ⟨fun _ => by positivity, fun i j _ => ?_⟩
    have := bound_ge s i.val
    linarith
  exact ⟨_, by simpa using hc⟩

private theorem mem_zero_scaled {s d : ℕ} (hs : 1 ≤ s) (x : Fin d → ℝ) :
    x ∈ (0 : ℝ) • P s d ↔ x = 0 := by
  obtain ⟨y, hy⟩ := full_dimensional (d := d) hs
  rw [Set.zero_smul_set ⟨y, interior_subset hy⟩]
  rfl


private theorem coe_eq_zero {d : ℕ} (x : Fin d → ℤ) : (fun i => (x i : ℝ)) = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    change (x i : ℝ) = 0 at hi
    exact_mod_cast hi
  · rintro rfl
    ext i
    simp

private theorem unique_at_zero {s d q : ℕ} (hs : 1 ≤ s) (c : Fin d → ℤ)
    (h : ∀ n : ℕ, ∀ x : Fin d → ℤ,
      (fun i => (x i : ℝ)) ∈ interior (((n + q : ℕ) : ℝ) • P s d) ↔
        (fun i => ((x-c) i : ℝ)) ∈ ((n : ℝ) • P s d)) (x : Fin d → ℤ) :
    (fun i => (x i : ℝ)) ∈ interior ((q : ℝ) • P s d) ↔ x = c := by
  simpa only [Nat.zero_add, Nat.cast_zero, mem_zero_scaled hs, coe_eq_zero,
    sub_eq_zero] using h 0 x

private theorem index_center {s d q : ℕ} (hs : 2 ≤ s) (hd : 2 ≤ d) (hq : 1 ≤ q)
    (c : Fin d → ℤ)
    (h : ∀ n : ℕ, ∀ x : Fin d → ℤ,
      (fun i => (x i : ℝ)) ∈ interior (((n + q : ℕ) : ℝ) • P s d) ↔
        (fun i => ((x-c) i : ℝ)) ∈ ((n : ℝ) • P s d)) :
    q = 1 ∧ s = 3 ∧ c = 1 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hc := (mem_interior_scaled hqp (fun i => (c i : ℝ))).mp
    ((unique_at_zero (by omega) c h c).mpr rfl)
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hc0 : (1 : ℝ) ≤ (c i0 : ℝ) := by
    have : (0 : ℤ) < c i0 := by
      have hi : (0 : ℝ) < (c i0 : ℝ) := hc.1 i0
      exact_mod_cast hi
    exact_mod_cast (show 1 ≤ c i0 by omega)
  have hc1 : (1 : ℝ) ≤ (c i1 : ℝ) := by
    have : (0 : ℤ) < c i1 := by
      have hi : (0 : ℝ) < (c i1 : ℝ) := hc.1 i1
      exact_mod_cast hi
    exact_mod_cast (show 1 ≤ c i1 by omega)
  have hpair := hc.2 i0 i1 (by rfl)
  have hqsR : (2 : ℝ) < (q : ℝ) * (s : ℝ) := by
    norm_num [bound, i0] at hpair
    dsimp [i0, i1] at hc0 hc1 hpair
    linarith
  have hqs : 3 ≤ q*s := by
    have : 2 < q*s := by exact_mod_cast hqsR
    omega
  have hone : (fun i => ((1 : Fin d → ℤ) i : ℝ)) ∈ interior ((q : ℝ) • P s d) := by
    apply (mem_interior_scaled hqp _).mpr
    refine ⟨fun _ => by norm_num [], fun i j _ => ?_⟩
    have hb := mul_le_mul_of_nonneg_left (bound_ge s i.val) hqp.le
    norm_num []
    exact hqsR.trans_le hb
  have hcenter : c = 1 := ((unique_at_zero (by omega) c h 1).mp hone).symm
  have hlt : q*s < 4 := by
    by_contra hn
    have hge : 4 ≤ q*s := by omega
    have hgeR : (4 : ℝ) ≤ (q : ℝ)*(s : ℝ) := by exact_mod_cast hge
    let v : Fin d → ℤ := fun i => if i.val = 0 then 2 else 1
    have hv : (fun i => (v i : ℝ)) ∈ interior ((q : ℝ) • P s d) := by
      apply (mem_interior_scaled hqp _).mpr
      constructor
      · intro i
        dsimp [v]
        split <;> norm_num
      · intro i j hij
        have hj : j.val ≠ 0 := by omega
        have hsum : ((fun i => (v i : ℝ)) i + (fun i => (v i : ℝ)) j : ℝ) ≤ 3 := by
          simp only [v, hj, ite_false, Int.cast_one]
          split <;> norm_num
        have hb := mul_le_mul_of_nonneg_left (bound_ge s i.val) hqp.le
        linarith
    have he := (unique_at_zero (by omega) c h v).mp hv
    have hi := congrFun (he.trans hcenter) i0
    norm_num [v, i0] at hi
  have heq : q*s = 3 := by omega
  have hq1 : q = 1 := by
    by_contra hn
    have : 2 ≤ q := by omega
    have : 4 ≤ q*s := le_trans (by norm_num) (Nat.mul_le_mul this hs)
    omega
  have hs3 : s = 3 := by simpa [hq1] using heq
  exact ⟨hq1, hs3, hcenter⟩


private theorem not_gorenstein_large_dimension {d : ℕ} (hd : 3 ≤ d) : ¬ IsGorenstein 3 d := by
  rintro ⟨q, hq, c, h⟩
  obtain ⟨rfl, _, rfl⟩ := index_center (by norm_num : 2 ≤ 3) (by omega) hq c h
  let w : Fin d → ℤ := fun i => if i.val = 1 then 4 else if i.val = 2 then 3 else 1
  have hw : (fun i => (w i : ℝ)) ∈ interior ((2 : ℝ) • P 3 d) := by
    apply (mem_interior_scaled (by norm_num) _).mpr
    constructor
    · intro i
      dsimp [w]
      split <;> (try split) <;> norm_num
    · intro i j hij
      by_cases hi0 : i.val = 0
      · have hj1 : j.val = 1 := by omega
        norm_num [w, hi0, hj1, bound]
      by_cases hi1 : i.val = 1
      · have hj2 : j.val = 2 := by omega
        norm_num [w, hi1, hj2, bound]
      by_cases hi2 : i.val = 2
      · have hj3 : j.val = 3 := by omega
        norm_num [w, hi2, hj3, bound]
      · have hj1 : j.val ≠ 1 := by omega
        have hj2 : j.val ≠ 2 := by omega
        have hb := bound_ge 3 i.val
        simp only [w, hi1, hi2, hj1, hj2, ite_false, Int.cast_one]
        norm_num at hb ⊢
        linarith
  have hbad := (h 1 w).mp (by simpa using hw)
  norm_num only [Nat.cast_one] at hbad
  have hp := ((mem_scaled (by norm_num : (0 : ℝ) < 1) _).mp hbad).2
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  have he := hp i1 i2 (by rfl)
  norm_num [w, i1, i2, bound] at he

private theorem mem_scaled_two {t : ℝ} (ht : 0 < t) (x : Fin 2 → ℝ) :
    x ∈ t • P 3 2 ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 3*t := by
  rw [mem_scaled ht]
  norm_num [Fin.forall_fin_two, bound, mul_comm, and_assoc]

private theorem mem_interior_two {t : ℝ} (ht : 0 < t) (x : Fin 2 → ℝ) :
    x ∈ interior (t • P 3 2) ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 3*t := by
  rw [mem_interior_scaled ht]
  norm_num [Fin.forall_fin_two, bound, mul_comm, and_assoc]

private theorem gorenstein_three_two : IsGorenstein 3 2 := by
  refine ⟨1, le_rfl, 1, ?_⟩
  intro n x
  have hnp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  rw [mem_interior_two hnp]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    rw [mem_zero_scaled (by norm_num : 1 ≤ 3), coe_eq_zero, sub_eq_zero]
    constructor
    · rintro ⟨h0, h1, he⟩
      have h0z : (0 : ℤ) < x 0 := by exact_mod_cast h0
      have h1z : (0 : ℤ) < x 1 := by exact_mod_cast h1
      norm_num at he
      have hez : x 0 + x 1 < 3 := by exact_mod_cast he
      ext i
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with hi | hi
      · have : i = 0 := Fin.ext hi
        subst i
        change x 0 = 1
        omega
      · have : i = 1 := Fin.ext hi
        subst i
        change x 1 = 1
        omega
    · rintro rfl
      norm_num
  · have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [mem_scaled_two hpos]
    simp only [Pi.sub_apply, Pi.one_apply, Int.cast_sub, Int.cast_one]
    norm_cast
    constructor
    · rintro ⟨h0, h1, he⟩
      exact ⟨by omega, by omega, by omega⟩
    · rintro ⟨h0, h1, he⟩
      exact ⟨by omega, by omega, by omega⟩

theorem result : claim := by
  intro s r hs hr
  constructor
  · intro hg
    obtain ⟨q, hq, c, h⟩ := hg
    obtain ⟨hq1, hs3, _⟩ := index_center hs (by omega) hq c h
    refine ⟨hs3, ?_⟩
    by_contra hn
    have hd : 3 ≤ 2*r := by omega
    subst s
    exact not_gorenstein_large_dimension hd ⟨q, hq, c, h⟩
  · rintro ⟨rfl, rfl⟩
    simpa using gorenstein_three_two

end D5.S3.Combinatorics.Geometry.AlternatingAdjacentSumGorenstein
