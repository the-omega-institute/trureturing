/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IndexEqualityPatterns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unrestricted three- and four-index sums split into canonical equality patterns. -/

import Mathlib
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs

/-! Canonical decompositions of finite sums by index-equality pattern. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum over injective representative tuples after applying a pattern map. -/
def patternSum {r : ℕ} (p : Fin 4 → Fin r)
    (F : (Fin 4 → ι) → ℝ) : ℝ :=
  ∑ x : Fin r → ι with Function.Injective x, F (x ∘ p)

/-- The analogous pattern sum for triples. -/
def patternSum3 {r : ℕ} (p : Fin 3 → Fin r)
    (F : (Fin 3 → ι) → ℝ) : ℝ :=
  ∑ x : Fin r → ι with Function.Injective x, F (x ∘ p)

private lemma pattern_filter_sum {n r : ℕ} (p : Fin n → Fin r)
    (hp : Function.Surjective p)
    (P : (Fin n → ι) → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ ∃ y : Fin r → ι, Function.Injective y ∧ x = y ∘ p)
    (F : (Fin n → ι) → ℝ) :
    Finset.sum (Finset.univ.filter P) F =
      ∑ y : Fin r → ι with Function.Injective y, F (y ∘ p) := by
  classical
  symm
  apply Finset.sum_bij (fun y _ => y ∘ p)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hy' : Function.Injective y := by simpa using hy
    exact (hP (y ∘ p)).2 ⟨y, hy', rfl⟩
  · intro y₁ hy₁ y₂ hy₂ h
    funext i
    obtain ⟨j, rfl⟩ := hp i
    exact congrFun h j
  · intro x hx
    have hxP : P x := (Finset.mem_filter.mp hx).2
    obtain ⟨y, hy, hxy⟩ := (hP x).1 hxP
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, hxy.symm⟩
  · intro y hy
    rfl

private def p012 (x : Fin 3 → ι) : Prop :=
  x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2
private def p001 (x : Fin 3 → ι) : Prop := x 0 = x 1 ∧ x 0 ≠ x 2
private def p010 (x : Fin 3 → ι) : Prop := x 0 = x 2 ∧ x 0 ≠ x 1
private def p011 (x : Fin 3 → ι) : Prop := x 1 = x 2 ∧ x 0 ≠ x 1
private def p000 (x : Fin 3 → ι) : Prop := x 0 = x 1 ∧ x 0 = x 2

private lemma p012_image (x : Fin 3 → ι) :
    p012 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,2] := by
  constructor
  · intro hx
    rcases hx with ⟨h01, h02, h12⟩
    have hinj : Function.Injective x := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [h01, h02, h12]
    refine ⟨x, hinj, ?_⟩
    funext i
    fin_cases i <;> rfl
  · rintro ⟨y, hy, rfl⟩
    dsimp [p012]
    constructor
    · exact fun h => Fin.zero_ne_one (hy h)
    constructor
    · intro h
      have hh := hy h
      omega
    · intro h
      have hh := hy h
      omega

private lemma p001_image (x : Fin 3 → ι) :
    p001 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,0,1] := by
  constructor
  · rintro ⟨h01, h02⟩
    refine ⟨![x 0, x 2], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h01]
  · rintro ⟨y, hy, rfl⟩
    dsimp [p001]
    constructor
    · rfl
    · exact fun h => Fin.zero_ne_one (hy h)

private lemma p010_image (x : Fin 3 → ι) :
    p010 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,0] := by
  constructor
  · rintro ⟨h02, h01⟩
    refine ⟨![x 0, x 1], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h02]
  · rintro ⟨y, hy, rfl⟩
    dsimp [p010]
    constructor
    · rfl
    · exact fun h => Fin.zero_ne_one (hy h)

private lemma p011_image (x : Fin 3 → ι) :
    p011 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,1] := by
  constructor
  · rintro ⟨h12, h01⟩
    refine ⟨![x 0, x 1], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h12]
  · rintro ⟨y, hy, rfl⟩
    dsimp [p011]
    constructor
    · rfl
    · exact fun h => Fin.zero_ne_one (hy h)

private lemma p000_image (x : Fin 3 → ι) :
    p000 x ↔ ∃ y : Fin 1 → ι, Function.Injective y ∧ x = y ∘ ![0,0,0] := by
  constructor
  · rintro ⟨h01, h02⟩
    refine ⟨![x 0], ?_, ?_⟩
    · intro i j hij
      exact Subsingleton.elim _ _
    · have h12 : x 1 = x 2 := h01.symm.trans h02
      funext i; fin_cases i <;> simp [h01, h02, h12]
  · rintro ⟨y, hy, rfl⟩
    dsimp [p000]
    exact ⟨rfl, rfl⟩

theorem sum_fin_three_eq_pattern_sums :
    ∀ F : (Fin 3 → ι) → ℝ, (∑ x, F x) =
      patternSum3 (r := 3) ![0,1,2] F +
      patternSum3 (r := 2) ![0,0,1] F +
      patternSum3 (r := 2) ![0,1,0] F +
      patternSum3 (r := 2) ![0,1,1] F +
      patternSum3 (r := 1) ![0,0,0] F := by
  classical
  intro F
  have hpoint : ∀ x : Fin 3 → ι,
      F x = (if p012 x then F x else 0) + (if p001 x then F x else 0) +
        (if p010 x then F x else 0) + (if p011 x then F x else 0) +
        (if p000 x then F x else 0) := by
    intro x
    by_cases h01 : x 0 = x 1
    · by_cases h02 : x 0 = x 2
      · have h12 : x 1 = x 2 := h01.symm.trans h02
        simp [p000, p001, p010, p011, p012, h01, h02, h12]
      · by_cases h12 : x 1 = x 2
        · simp [p000, p001, p010, p011, p012, h01, h02, h12]
        · simp [p000, p001, p010, p011, p012, h01, h02, h12]
    · by_cases h02 : x 0 = x 2
      · by_cases h12 : x 1 = x 2
        · simp [p000, p010, p001, p011, p012, h01, h02, h12]
        · have h21 : ¬ x 2 = x 1 := fun h => h12 h.symm
          simp [p000, p010, p001, p011, p012, h01, h02, h12, h21]
      · by_cases h12 : x 1 = x 2
        · simp [p000, p011, p001, p010, p012, h01, h02, h12]
        · simp [p000, p012, p001, p010, p011, h01, h02, h12]
  rw [show (∑ x, F x) = ∑ x, ((if p012 x then F x else 0) +
      (if p001 x then F x else 0) + (if p010 x then F x else 0) +
      (if p011 x then F x else 0) + (if p000 x then F x else 0)) by
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x]
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  simp only [patternSum3]
  rw [pattern_filter_sum ![0,1,2] (by decide) p012 p012_image F,
    pattern_filter_sum ![0,0,1] (by decide) p001 p001_image F,
    pattern_filter_sum ![0,1,0] (by decide) p010 p010_image F,
    pattern_filter_sum ![0,1,1] (by decide) p011 p011_image F,
    pattern_filter_sum ![0,0,0] (by decide) p000 p000_image F]

private def q0123 (x : Fin 4 → ι) : Prop :=
  x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 0 ≠ x 3 ∧
    x 1 ≠ x 2 ∧ x 1 ≠ x 3 ∧ x 2 ≠ x 3
private def q0012 (x : Fin 4 → ι) : Prop :=
  x 0 = x 1 ∧ x 0 ≠ x 2 ∧ x 0 ≠ x 3 ∧ x 2 ≠ x 3
private def q0102 (x : Fin 4 → ι) : Prop :=
  x 0 = x 2 ∧ x 0 ≠ x 1 ∧ x 0 ≠ x 3 ∧ x 1 ≠ x 3
private def q0120 (x : Fin 4 → ι) : Prop :=
  x 0 = x 3 ∧ x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2
private def q0112 (x : Fin 4 → ι) : Prop :=
  x 1 = x 2 ∧ x 0 ≠ x 1 ∧ x 0 ≠ x 3 ∧ x 1 ≠ x 3
private def q0121 (x : Fin 4 → ι) : Prop :=
  x 1 = x 3 ∧ x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2
private def q0122 (x : Fin 4 → ι) : Prop :=
  x 2 = x 3 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2 ∧ x 0 ≠ x 1
private def q0011 (x : Fin 4 → ι) : Prop :=
  x 0 = x 1 ∧ x 2 = x 3 ∧ x 0 ≠ x 2
private def q0101 (x : Fin 4 → ι) : Prop :=
  x 0 = x 2 ∧ x 1 = x 3 ∧ x 0 ≠ x 1
private def q0110 (x : Fin 4 → ι) : Prop :=
  x 0 = x 3 ∧ x 1 = x 2 ∧ x 0 ≠ x 1
private def q0001 (x : Fin 4 → ι) : Prop :=
  x 0 = x 1 ∧ x 0 = x 2 ∧ x 0 ≠ x 3
private def q0010 (x : Fin 4 → ι) : Prop :=
  x 0 = x 1 ∧ x 0 = x 3 ∧ x 0 ≠ x 2
private def q0100 (x : Fin 4 → ι) : Prop :=
  x 0 = x 2 ∧ x 0 = x 3 ∧ x 0 ≠ x 1
private def q0111 (x : Fin 4 → ι) : Prop :=
  x 1 = x 2 ∧ x 1 = x 3 ∧ x 0 ≠ x 1
private def q0000 (x : Fin 4 → ι) : Prop :=
  x 0 = x 1 ∧ x 0 = x 2 ∧ x 0 = x 3

private lemma q0123_image (x : Fin 4 → ι) :
    q0123 x ↔ ∃ y : Fin 4 → ι, Function.Injective y ∧ x = y ∘ ![0,1,2,3] := by
  constructor
  · intro hx
    rcases hx with ⟨h01,h02,h03,h12,h13,h23⟩
    refine ⟨x, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [h01,h02,h03,h12,h13,h23]
    · funext i; fin_cases i <;> rfl
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0123]
    exact ⟨hy.ne (by decide), hy.ne (by decide), hy.ne (by decide),
      hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0012_image (x : Fin 4 → ι) :
    q0012 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,0,1,2] := by
  constructor
  · rintro ⟨h01,h02,h03,h23⟩
    refine ⟨![x 0,x 2,x 3], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h01]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0012]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0102_image (x : Fin 4 → ι) :
    q0102 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,0,2] := by
  constructor
  · rintro ⟨h02,h01,h03,h13⟩
    refine ⟨![x 0,x 1,x 3], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h02]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0102]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0120_image (x : Fin 4 → ι) :
    q0120 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,2,0] := by
  constructor
  · rintro ⟨h03,h01,h02,h12⟩
    refine ⟨![x 0,x 1,x 2], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h03]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0120]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0112_image (x : Fin 4 → ι) :
    q0112 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,1,2] := by
  constructor
  · rintro ⟨h12,h01,h03,h13⟩
    refine ⟨![x 0,x 1,x 3], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h12]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0112]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0121_image (x : Fin 4 → ι) :
    q0121 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,2,1] := by
  constructor
  · rintro ⟨h13,h01,h02,h12⟩
    refine ⟨![x 0,x 1,x 2], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h13]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0121]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0122_image (x : Fin 4 → ι) :
    q0122 x ↔ ∃ y : Fin 3 → ι, Function.Injective y ∧ x = y ∘ ![0,1,2,2] := by
  constructor
  · rintro ⟨h23,h02,h12,h01⟩
    refine ⟨![x 0,x 1,x 2], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h23]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0122]
    exact ⟨rfl, hy.ne (by decide), hy.ne (by decide), hy.ne (by decide)⟩

private lemma q0011_image (x : Fin 4 → ι) :
    q0011 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,0,1,1] := by
  constructor
  · rintro ⟨h01,h23,h02⟩
    refine ⟨![x 0,x 2], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h01,h23]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0011]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0101_image (x : Fin 4 → ι) :
    q0101 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,0,1] := by
  constructor
  · rintro ⟨h02,h13,h01⟩
    refine ⟨![x 0,x 1], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h02,h13]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0101]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0110_image (x : Fin 4 → ι) :
    q0110 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,1,0] := by
  constructor
  · rintro ⟨h03,h12,h01⟩
    refine ⟨![x 0,x 1], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · funext i; fin_cases i <;> simp [h03,h12]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0110]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0001_image (x : Fin 4 → ι) :
    q0001 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,0,0,1] := by
  constructor
  · rintro ⟨h01,h02,h03⟩
    refine ⟨![x 0,x 3], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · have h12 : x 1 = x 2 := h01.symm.trans h02
      funext i; fin_cases i <;> simp [h01,h02,h03,h12]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0001]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0010_image (x : Fin 4 → ι) :
    q0010 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,0,1,0] := by
  constructor
  · rintro ⟨h01,h03,h02⟩
    refine ⟨![x 0,x 2], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · have h13 : x 1 = x 3 := h01.symm.trans h03
      funext i; fin_cases i <;> simp [h01,h03,h02,h13]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0010]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0100_image (x : Fin 4 → ι) :
    q0100 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,0,0] := by
  constructor
  · rintro ⟨h02,h03,h01⟩
    refine ⟨![x 0,x 1], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · have h23 : x 2 = x 3 := h02.symm.trans h03
      funext i; fin_cases i <;> simp [h02,h03,h01,h23]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0100]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0111_image (x : Fin 4 → ι) :
    q0111 x ↔ ∃ y : Fin 2 → ι, Function.Injective y ∧ x = y ∘ ![0,1,1,1] := by
  constructor
  · rintro ⟨h12,h13,h01⟩
    refine ⟨![x 0,x 1], ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · have h23 : x 2 = x 3 := h12.symm.trans h13
      funext i; fin_cases i <;> simp [h12,h13,h01,h23]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0111]
    exact ⟨rfl, rfl, hy.ne (by decide)⟩

private lemma q0000_image (x : Fin 4 → ι) :
    q0000 x ↔ ∃ y : Fin 1 → ι, Function.Injective y ∧ x = y ∘ ![0,0,0,0] := by
  constructor
  · rintro ⟨h01,h02,h03⟩
    refine ⟨![x 0], ?_, ?_⟩
    · intro i j hij; exact Subsingleton.elim _ _
    · have h12 : x 1 = x 2 := h01.symm.trans h02
      have h13 : x 1 = x 3 := h01.symm.trans h03
      have h23 : x 2 = x 3 := h02.symm.trans h03
      funext i; fin_cases i <;> simp [h01,h02,h03,h12,h13,h23]
  · rintro ⟨y,hy,rfl⟩
    dsimp [q0000]
    exact ⟨rfl, rfl, rfl⟩

theorem sum_fin_four_eq_pattern_sums :
    ∀ F : (Fin 4 → ι) → ℝ,
    (∑ x, F x) =
      patternSum (r := 4) ![0,1,2,3] F +
      patternSum (r := 3) ![0,0,1,2] F + patternSum (r := 3) ![0,1,0,2] F +
      patternSum (r := 3) ![0,1,2,0] F + patternSum (r := 3) ![0,1,1,2] F +
      patternSum (r := 3) ![0,1,2,1] F + patternSum (r := 3) ![0,1,2,2] F +
      patternSum (r := 2) ![0,0,1,1] F + patternSum (r := 2) ![0,1,0,1] F +
      patternSum (r := 2) ![0,1,1,0] F +
      patternSum (r := 2) ![0,0,0,1] F + patternSum (r := 2) ![0,0,1,0] F +
      patternSum (r := 2) ![0,1,0,0] F + patternSum (r := 2) ![0,1,1,1] F +
      patternSum (r := 1) ![0,0,0,0] F := by
  classical
  intro F
  have hpoint : ∀ x : Fin 4 → ι,
      F x =
        (if q0123 x then F x else 0) +
        (if q0012 x then F x else 0) + (if q0102 x then F x else 0) +
        (if q0120 x then F x else 0) + (if q0112 x then F x else 0) +
        (if q0121 x then F x else 0) + (if q0122 x then F x else 0) +
        (if q0011 x then F x else 0) + (if q0101 x then F x else 0) +
        (if q0110 x then F x else 0) + (if q0001 x then F x else 0) +
        (if q0010 x then F x else 0) + (if q0100 x then F x else 0) +
        (if q0111 x then F x else 0) + (if q0000 x then F x else 0) := by
    intro x
    by_cases h01 : x 0 = x 1
    all_goals by_cases h02 : x 0 = x 2
    all_goals by_cases h03 : x 0 = x 3
    all_goals by_cases h12 : x 1 = x 2
    all_goals by_cases h13 : x 1 = x 3
    all_goals by_cases h23 : x 2 = x 3
    all_goals simp_all [q0123, q0012, q0102, q0120, q0112, q0121, q0122,
      q0011, q0101, q0110, q0001, q0010, q0100, q0111, q0000]
  rw [show (∑ x, F x) = ∑ x,
      ((if q0123 x then F x else 0) +
        (if q0012 x then F x else 0) + (if q0102 x then F x else 0) +
        (if q0120 x then F x else 0) + (if q0112 x then F x else 0) +
        (if q0121 x then F x else 0) + (if q0122 x then F x else 0) +
        (if q0011 x then F x else 0) + (if q0101 x then F x else 0) +
        (if q0110 x then F x else 0) + (if q0001 x then F x else 0) +
        (if q0010 x then F x else 0) + (if q0100 x then F x else 0) +
        (if q0111 x then F x else 0) + (if q0000 x then F x else 0)) by
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x]
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  simp only [patternSum]
  rw [pattern_filter_sum ![0,1,2,3] (by decide) q0123 q0123_image F,
    pattern_filter_sum ![0,0,1,2] (by decide) q0012 q0012_image F,
    pattern_filter_sum ![0,1,0,2] (by decide) q0102 q0102_image F,
    pattern_filter_sum ![0,1,2,0] (by decide) q0120 q0120_image F,
    pattern_filter_sum ![0,1,1,2] (by decide) q0112 q0112_image F,
    pattern_filter_sum ![0,1,2,1] (by decide) q0121 q0121_image F,
    pattern_filter_sum ![0,1,2,2] (by decide) q0122 q0122_image F,
    pattern_filter_sum ![0,0,1,1] (by decide) q0011 q0011_image F,
    pattern_filter_sum ![0,1,0,1] (by decide) q0101 q0101_image F,
    pattern_filter_sum ![0,1,1,0] (by decide) q0110 q0110_image F,
    pattern_filter_sum ![0,0,0,1] (by decide) q0001 q0001_image F,
    pattern_filter_sum ![0,0,1,0] (by decide) q0010 q0010_image F,
    pattern_filter_sum ![0,1,0,0] (by decide) q0100 q0100_image F,
    pattern_filter_sum ![0,1,1,1] (by decide) q0111 q0111_image F,
    pattern_filter_sum ![0,0,0,0] (by decide) q0000 q0000_image F]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
