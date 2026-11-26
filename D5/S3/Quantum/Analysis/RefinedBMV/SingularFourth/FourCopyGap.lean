/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/FourCopyGap
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic four-gap expansion and contraction in a spectral basis. -/

import D5.S3.Quantum.Analysis.RefinedBMVUniformWords
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-! Four-copy refined BMV on spectral coupling graphs without triangles or quadrilaterals. -/

/-! The cyclic four-gap expansion and its spectral block contraction. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.FourCopyGap

variable {n s : Type*} [Fintype n] [DecidableEq n]

def cycleTrace (C : s → s → Matrix n n ℂ) (i j k l : s) : ℂ :=
  trace (C i j * C j k * C k l * C l i)

open scoped CStarAlgebra in
private theorem trace_mul_nonneg_of_posSemidef {D E : Matrix n n ℂ}
    (hD : D.PosSemidef) (hE : E.PosSemidef) : 0 ≤ trace (D * E) := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  rw [star_eq_conjTranspose] at hS
  calc
    0 ≤ trace (S * E * Sᴴ) := (hE.mul_mul_conjTranspose_same S).trace_nonneg
    _ = trace (D * E) := by
      rw [trace_mul_comm (S * E) Sᴴ, ← mul_assoc, ← hS]

section Compression

variable [DecidableEq s]

/-- The diagonal projection onto a fiber of a spectral label map. -/
def spectralMask (label : n → s) (i : s) : Matrix n n ℂ :=
  diagonal fun a ↦ if label a = i then 1 else 0

/-- A block in the eigenbasis, extended by zero outside its row and column fibers. -/
def spectralBlock (label : n → s) (B : Matrix n n ℂ) (i j : s) : Matrix n n ℂ :=
  spectralMask label i * B * spectralMask label j

end Compression

/-- The four exponents of a cyclic word with four occurrences of its second factor. -/
abbrev Gap := ℕ × ℕ × ℕ × ℕ

/-- All weak compositions of the first degree into four slots. -/
def gaps (p : ℕ) : Finset Gap :=
  (Finset.range (p + 1) ×ˢ (Finset.range (p + 1) ×ˢ
    (Finset.range (p + 1) ×ˢ Finset.range (p + 1)))).filter
    (fun g ↦ g.1 + g.2.1 + g.2.2.1 + g.2.2.2 = p)

@[simp] theorem mem_gaps {p : ℕ} {g : Gap} :
    g ∈ gaps p ↔ g.1 + g.2.1 + g.2.2.1 + g.2.2.2 = p := by
  simp only [gaps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

private def rotate (g : Gap) : Gap := (g.2.1, g.2.2.1, g.2.2.2, g.1)
private def rotateBack (g : Gap) : Gap := (g.2.2.2, g.1, g.2.1, g.2.2.1)

private theorem sum_rotate {M : Type*} [AddCommMonoid M] (p : ℕ) (f : Gap → M) :
    (∑ g ∈ gaps p, f (rotate g)) = ∑ g ∈ gaps p, f g := by
  apply Finset.sum_nbij' rotate rotateBack
  · intro g hg
    simp only [mem_gaps, rotate] at hg ⊢
    omega
  · intro g hg
    simp only [mem_gaps, rotateBack] at hg ⊢
    omega
  · rintro ⟨a, b, c, d⟩ _
    rfl
  · rintro ⟨a, b, c, d⟩ _
    rfl
  · intro g _
    rfl

private def monomial (a b c d : ℝ) (g : Gap) : ℝ :=
  a ^ g.1 * b ^ g.2.1 * c ^ g.2.2.1 * d ^ g.2.2.2

private def balanced (p : ℕ) (a b c d : ℝ) : ℝ :=
  a ^ ((p : ℝ) / 4) * b ^ ((p : ℝ) / 4) *
    c ^ ((p : ℝ) / 4) * d ^ ((p : ℝ) / 4)

private def cyclicSurplus (p : ℕ) (a b c d : ℝ) (g : Gap) : ℝ :=
  (monomial a b c d g + monomial a b c d (rotate g) +
    monomial a b c d (rotate (rotate g)) + monomial a b c d (rotateBack g)) / 4 -
    balanced p a b c d

private theorem rotate_thrice (g : Gap) :
    rotate (rotate (rotate g)) = rotateBack g := by
  rcases g with ⟨a, b, c, d⟩
  rfl

private theorem cyclicSurplus_nonneg {p : ℕ} {g : Gap} (hg : g ∈ gaps p)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ cyclicSurplus p a b c d g := by
  obtain ⟨i, j, k, l⟩ := g
  have htotal : i + j + k + l = p := mem_gaps.mp hg
  let u := monomial a b c d (i, j, k, l)
  let v := monomial a b c d (rotate (i, j, k, l))
  let w := monomial a b c d (rotate (rotate (i, j, k, l)))
  let z := monomial a b c d (rotateBack (i, j, k, l))
  have hu : 0 ≤ u := by dsimp [u, monomial]; positivity
  have hv : 0 ≤ v := by dsimp [v, monomial, rotate]; positivity
  have hw : 0 ≤ w := by dsimp [w, monomial, rotate]; positivity
  have hz : 0 ≤ z := by dsimp [z, monomial, rotateBack]; positivity
  have hprod : u * v * w * z = a ^ p * b ^ p * c ^ p * d ^ p := by
    dsimp [u, v, w, z, monomial, rotate, rotateBack]
    rw [← htotal]
    simp only [pow_add]
    ring
  have hgm := Real.geom_mean_le_arith_mean4_weighted
    (w₁ := 1 / 4) (w₂ := 1 / 4) (w₃ := 1 / 4) (w₄ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hu hv hw hz (by norm_num)
  rw [← Real.mul_rpow hu hv, ← Real.mul_rpow (mul_nonneg hu hv) hw,
    ← Real.mul_rpow (mul_nonneg (mul_nonneg hu hv) hw) hz, hprod,
    Real.mul_rpow (mul_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))
      (pow_nonneg hc _)) (pow_nonneg hd _),
    Real.mul_rpow (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)) (pow_nonneg hc _),
    Real.mul_rpow (pow_nonneg ha _) (pow_nonneg hb _),
    ← Real.rpow_natCast_mul ha, ← Real.rpow_natCast_mul hb,
    ← Real.rpow_natCast_mul hc, ← Real.rpow_natCast_mul hd] at hgm
  change 0 ≤ (u + v + w + z) / 4 - balanced p a b c d
  unfold balanced
  simp only [div_eq_mul_inv, one_mul] at hgm ⊢
  linarith

/-- The numerator of the scalar comparison kernel, before division by the
number of four-slot weak compositions. -/
def gapDefect (p : ℕ) (a b c d : ℝ) : ℝ :=
  (∑ g ∈ gaps p, monomial a b c d g) -
    (gaps p).card * balanced p a b c d

private theorem gapDefect_eq_sum (p : ℕ) (a b c d : ℝ) :
    gapDefect p a b c d = ∑ g ∈ gaps p, cyclicSurplus p a b c d g := by
  simp only [gapDefect, cyclicSurplus, Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← rotate_thrice]
  rw [sum_rotate p (fun x => monomial a b c d (rotate (rotate x))),
    sum_rotate p (fun x => monomial a b c d (rotate x)), sum_rotate p (monomial a b c d)]
  ring

theorem gapDefect_nonneg (p : ℕ) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ gapDefect p a b c d := by
  rw [gapDefect_eq_sum]
  exact Finset.sum_nonneg fun _ hg ↦ cyclicSurplus_nonneg hg ha hb hc hd

private theorem gapDefect_diagonal (p : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    gapDefect p a a a a = 0 := by
  have hb : balanced p a a a a = a ^ p := by
    unfold balanced
    rw [← show (a ^ ((p : ℝ) / 4)) ^ (4 : ℕ) =
      a ^ ((p : ℝ) / 4) * a ^ ((p : ℝ) / 4) *
        a ^ ((p : ℝ) / 4) * a ^ ((p : ℝ) / 4) by ring,
      ← Real.rpow_mul_natCast ha,
      show (p : ℝ) / 4 * ((4 : ℕ) : ℝ) = p by norm_num <;> ring, Real.rpow_natCast]
  have hm : (∑ g ∈ gaps p, monomial a a a a g) = (gaps p).card * a ^ p := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro g hg
    rw [monomial, ← pow_add, ← pow_add, ← pow_add, mem_gaps.mp hg]
  rw [gapDefect, hb, hm, sub_self]

section Words

open private DimThree.runBeforeB DimThree.sum_balancedWords_firstRun DimThree.balancedWords_zeroB
  from D5.S3.Quantum.Analysis.RefinedBMVUniformWords
open private evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43

private theorem sum_gaps_nested {M : Type*} [AddCommMonoid M] (p : ℕ) (F : Gap → M) :
    (∑ g ∈ gaps p, F g) =
      ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
        ∑ l ∈ Finset.range (p - j - k + 1), F (j, k, l, p - j - k - l) := by
  simp only [Finset.sum_sigma']
  let encode (g : Gap) : Σ _ : ℕ, Σ _ : ℕ, ℕ := ⟨g.1, g.2.1, g.2.2.1⟩
  let decode (g : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Gap :=
    (g.1, g.2.1, g.2.2, p - g.1 - g.2.1 - g.2.2)
  refine Finset.sum_nbij' encode decode ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_gaps] at hg
    simp only [encode, Finset.mem_sigma, Finset.mem_range]
    omega
  · intro g hg
    simp only [Finset.mem_sigma, Finset.mem_range] at hg
    simp only [decode, mem_gaps]
    omega
  · intro g hg
    simp only [mem_gaps] at hg
    dsimp only [encode, decode]
    have h : p - g.1 - g.2.1 - g.2.2.1 = g.2.2.2 := by omega
    rw [h] <;> rfl
  · rintro ⟨j, k, l⟩ _
    rfl
  · intro g hg
    simp only [mem_gaps] at hg
    dsimp only [encode, decode]
    have h : p - g.1 - g.2.1 - g.2.2.1 = g.2.2.2 := by omega
    rw [h]

private theorem sum_words_weighted (p : ℕ) (v : List Bool → ℂ) (F : Gap → ℂ)
    (hcut : ∀ i j k l m, v (DimThree.runBeforeB i (DimThree.runBeforeB j
      (DimThree.runBeforeB k (DimThree.runBeforeB l (List.replicate m true))))) =
        F (j, k, l, m + i)) :
    ((balancedWords p 4).map v).sum =
      ∑ g ∈ gaps p, (g.2.2.2 + 1 : ℂ) * F g := by
  rw [sum_gaps_nested]
  calc
    _ = ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p - i + 1),
          ∑ k ∈ Finset.range (p - i - j + 1), ∑ l ∈ Finset.range (p - i - j - k + 1),
            F (j, k, l, p - j - k - l) := by
      rw [DimThree.sum_balancedWords_firstRun (b := 3)]
      simp_rw [DimThree.sum_balancedWords_firstRun (b := 2),
        DimThree.sum_balancedWords_firstRun (b := 1), DimThree.sum_balancedWords_firstRun (b := 0),
        DimThree.balancedWords_zeroB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Function.comp_apply, hcut]
      refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦
        Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun l hl ↦ ?_
      simp only [Finset.mem_range] at hi hj hk hl
      rw [show p - i - j - k - l + i = p - j - k - l by omega]
    _ = ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (p - j + 1),
          ∑ k ∈ Finset.range (p - i - j + 1), ∑ l ∈ Finset.range (p - i - j - k + 1),
            F (j, k, l, p - j - k - l) := by
      apply Finset.sum_comm'
      intro i j
      simp only [Finset.mem_range]
      omega
    _ = ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
          ∑ i ∈ Finset.range (p - j - k + 1), ∑ l ∈ Finset.range (p - i - j - k + 1),
            F (j, k, l, p - j - k - l) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      apply Finset.sum_comm'
      intro i k
      simp only [Finset.mem_range] at hj ⊢
      omega
    _ = ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
          ∑ l ∈ Finset.range (p - j - k + 1), ∑ _i ∈ Finset.range (p - j - k - l + 1),
            F (j, k, l, p - j - k - l) := by
      refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun k hk ↦ ?_
      apply Finset.sum_comm'
      intro i l
      simp only [Finset.mem_range] at hj hk ⊢
      omega
    _ = _ := by simp [nsmul_eq_mul]

private theorem sum_words_cyclic (p : ℕ) (v : List Bool → ℂ) (F : Gap → ℂ)
    (hcut : ∀ i j k l m, v (DimThree.runBeforeB i (DimThree.runBeforeB j
      (DimThree.runBeforeB k (DimThree.runBeforeB l (List.replicate m true))))) =
        F (j, k, l, m + i)) (hcycle : ∀ g, F (rotate g) = F g) :
    4 * ((balancedWords p 4).map v).sum = (p + 4 : ℂ) * ∑ g ∈ gaps p, F g := by
  let w (g : Gap) : ℂ := (g.2.2.2 + 1 : ℂ) * F g
  rw [sum_words_weighted p v F hcut]
  change 4 * (∑ g ∈ gaps p, w g) = _
  calc
    _ = ∑ g ∈ gaps p, (w (rotate g) + w (rotate (rotate g)) +
        w (rotate (rotate (rotate g))) + w g) := by
      simp only [Finset.sum_add_distrib]
      rw [sum_rotate p (fun x => w (rotate (rotate x))),
        sum_rotate p (fun x => w (rotate x)), sum_rotate p w]
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg ↦ ?_
      have htotal := mem_gaps.mp hg
      have hcast : (g.1 : ℂ) + g.2.1 + g.2.2.1 + g.2.2.2 = (p : ℂ) := by
        exact_mod_cast htotal
      simp only [w, hcycle]
      dsimp only [rotate]
      linear_combination F g * hcast

private theorem word_count (a b : ℕ) : (balancedWords a b).length = (a + b).choose b := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero => norm_num [DimThree.balancedWords_zeroB]
    | succ b ih => simpa only [balancedWords, List.length_map, Nat.zero_add, Nat.choose_self] using ih
  | succ a ih =>
    induction b with
    | zero => simp [DimThree.balancedWords_zeroB]
    | succ b ihb =>
      rw [balancedWords, List.length_append, List.length_map, List.length_map, ih, ihb]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.choose_succ_succ (a + b + 1) b).symm

private theorem count_relation (p : ℕ) :
    4 * ((balancedWords p 4).length : ℂ) = (p + 4 : ℂ) * (gaps p).card := by
  simpa only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one, Finset.sum_const]
    using sum_words_cyclic p (fun _ ↦ 1) (fun _ ↦ 1) (fun _ _ _ _ _ ↦ rfl) (fun _ ↦ rfl)

theorem gaps_card (p : ℕ) : (gaps p).card = (p + 3).choose 3 := by
  have hword : 4 * (p + 4).choose 4 = (p + 4) * (gaps p).card := by
    have h := count_relation p
    rw [word_count] at h
    exact_mod_cast h
  have hchoose : (p + 4) * (p + 3).choose 3 = (p + 4).choose 4 * 4 :=
    Nat.add_one_mul_choose_eq (p + 3) 3
  apply Nat.eq_of_mul_eq_mul_left (show 0 < p + 4 by omega)
  rw [hchoose, Nat.mul_comm ((p + 4).choose 4) 4, hword]

private theorem gaps_card_pos (p : ℕ) : 0 < (gaps p).card :=
  Finset.card_pos.mpr ⟨(p, 0, 0, 0), by simp⟩

/-- The actual normalized mean over ordered words with (p) first factors and
four second factors. -/
def wordMean (p : ℕ) (A B : Matrix n n ℂ) : ℂ :=
  ((balancedWords p 4).map fun w ↦ trace (evalWord A B w)).sum / (balancedWords p 4).length

private def gapTrace (A B : Matrix n n ℂ) (g : Gap) : ℂ :=
  trace ((A ^ g.1 * B) * (A ^ g.2.1 * B) * (A ^ g.2.2.1 * B) * (A ^ g.2.2.2 * B))

theorem wordMean_eq_gaps (p : ℕ) (A B : Matrix n n ℂ) :
    wordMean p A B = (∑ g ∈ gaps p, gapTrace A B g) / (gaps p).card := by
  let v (w : List Bool) := trace (evalWord A B w)
  have hcut (i j k l m : ℕ) : v (DimThree.runBeforeB i (DimThree.runBeforeB j
      (DimThree.runBeforeB k (DimThree.runBeforeB l (List.replicate m true))))) =
        gapTrace A B (j, k, l, m + i) := by
    simp only [v, DimThree.runBeforeB, List.append_assoc, List.cons_append, List.nil_append,
      evalWord_block43, evalWord, gapTrace, pow_add, mul_assoc]
    rw [show evalWord A B (List.replicate m true) = A ^ m by
      simpa only [List.append_nil, evalWord, mul_one] using evalWord_block43 A B m []]
    simpa only [mul_assoc] using trace_mul_comm (A ^ i * B)
      (A ^ j * B * (A ^ k * B) * (A ^ l * B) * A ^ m)
  have hcycle (g : Gap) : gapTrace A B (rotate g) = gapTrace A B g := by
    simpa only [gapTrace, rotate, mul_assoc] using
      trace_mul_comm ((A ^ g.2.1 * B) * (A ^ g.2.2.1 * B) * (A ^ g.2.2.2 * B)) (A ^ g.1 * B)
  have hs := sum_words_cyclic p v (gapTrace A B) hcut hcycle
  have hwNat : (balancedWords p 4).length ≠ 0 := by
    rw [word_count]
    exact (Nat.choose_pos (show 4 ≤ p + 4 by omega)).ne'
  have hw : ((balancedWords p 4).length : ℂ) ≠ 0 := by exact_mod_cast hwNat
  have hg : ((gaps p).card : ℂ) ≠ 0 := by exact_mod_cast (gaps_card_pos p).ne'
  change ((balancedWords p 4).map v).sum / (balancedWords p 4).length = _
  apply (div_eq_div_iff hw hg).mpr
  linear_combination ((gaps p).card : ℂ) / 4 * hs -
    (∑ g ∈ gaps p, gapTrace A B g) / 4 * count_relation p

end Words

section Diagonal

variable [Fintype s] [DecidableEq s]

private theorem spectralMask_mul_self (label : n → s) (i : s) :
    spectralMask label i * spectralMask label i = spectralMask label i := by
  rw [spectralMask, diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : label a = i <;> simp [h]

private theorem spectralMask_contract (label : n → s) (i : s) (M : Matrix n n ℂ) :
    spectralMask label i * (spectralMask label i * M) = spectralMask label i * M := by
  rw [← mul_assoc, spectralMask_mul_self]

private theorem spectralBlock_apply (label : n → s) (B : Matrix n n ℂ)
    (i j : s) (a b : n) :
    spectralBlock label B i j a b = if label a = i ∧ label b = j then B a b else 0 := by
  by_cases ha : label a = i <;> by_cases hb : label b = j <;>
    simp [spectralBlock, spectralMask, mul_diagonal, diagonal_mul, ha, hb]

private theorem diagonal_mul_eq_sum (label : n → s) (x : s → ℂ) (B : Matrix n n ℂ) :
    diagonal (fun a ↦ x (label a)) * B = ∑ i, x i • (spectralMask label i * B) := by
  ext a b
  simp only [diagonal_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, spectralMask]
  simp_rw [show ∀ i : s, x i * ((if label a = i then 1 else 0) * B a b) =
      if label a = i then x i * B a b else 0 by
    intro i
    split <;> simp]
  simp

private theorem trace_mask_product (label : n → s) (B : Matrix n n ℂ) (i j k l : s) :
    trace ((spectralMask label i * B) * (spectralMask label j * B) *
      (spectralMask label k * B) * (spectralMask label l * B)) =
        cycleTrace (spectralBlock label B) i j k l := by
  let P := spectralMask label
  let Z := (P i * B) * (P j * B) * (P k * B) * (P l * B)
  change trace Z = trace ((P i * B * P j) * (P j * B * P k) *
    (P k * B * P l) * (P l * B * P i))
  have hblocks : (P i * B * P j) * (P j * B * P k) *
      (P k * B * P l) * (P l * B * P i) = Z * P i := by
    simp only [Z, P, mul_assoc, spectralMask_contract]
  rw [hblocks, trace_mul_comm Z (P i)]
  congr 1
  simp only [Z, P, mul_assoc, spectralMask_contract]

/-- Linear contraction of a scalar kernel against all the spectral block cycles. -/
private def contract (C : s → s → Matrix n n ℂ) :
    (s → s → s → s → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ i, ∑ j, ∑ k, ∑ l, f i j k l * cycleTrace C i j k l
  map_add' f g := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r f := by simp [smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem trace_four_weighted (label : n → s) (B : Matrix n n ℂ)
    (u v w z : s → ℂ) :
    trace ((diagonal (fun a ↦ u (label a)) * B) * (diagonal (fun a ↦ v (label a)) * B) *
      (diagonal (fun a ↦ w (label a)) * B) * (diagonal (fun a ↦ z (label a)) * B)) =
        contract (spectralBlock label B) (fun i j k l ↦ u i * v j * w k * z l) := by
  have hscale (U V W Z : Matrix n n ℂ) (a b c d : ℂ) :
      (a • U) * (b • V) * (c • W) * (d • Z) =
        (a * b * c * d) • (U * V * W * Z) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
    congr 1
    ring
  simp only [diagonal_mul_eq_sum, contract, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_mul, Matrix.mul_sum, hscale, trace_sum, trace_smul, smul_eq_mul,
    trace_mask_product]
  let f (i j k l : s) := u i * v j * w k * z l * cycleTrace (spectralBlock label B) i j k l
  change (∑ l, ∑ k, ∑ j, ∑ i, f i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l
  calc
    _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j k l := by
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j k l := by
      exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ k, ∑ j, f i j k l := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j k l := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f i j k l := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

private def eigenDiagonal (label : n → s) (x : s → ℝ) : Matrix n n ℂ :=
  diagonal fun a ↦ (x (label a) : ℂ)

private def rootDiagonal (label : n → s) (x : s → ℝ) (p : ℕ) : Matrix n n ℂ :=
  eigenDiagonal label (fun i ↦ x i ^ ((p : ℝ) / 4))

private theorem gapTrace_diagonal (label : n → s) (x : s → ℝ) (B : Matrix n n ℂ) (g : Gap) :
    gapTrace (eigenDiagonal label x) B g =
      contract (spectralBlock label B)
        (fun i j k l ↦ (monomial (x i) (x j) (x k) (x l) g : ℂ)) := by
  have hpow (k : ℕ) : (fun a : n ↦ (x (label a) : ℂ)) ^ k =
      (fun a : n ↦ (x (label a) : ℂ) ^ k) := by
    funext a
    simp only [Pi.pow_apply]
  simpa only [gapTrace, eigenDiagonal, diagonal_pow, hpow, monomial, Complex.ofReal_mul,
    Complex.ofReal_pow] using trace_four_weighted label B
      (fun i ↦ ((x i : ℂ) ^ g.1)) (fun i ↦ ((x i : ℂ) ^ g.2.1))
      (fun i ↦ ((x i : ℂ) ^ g.2.2.1)) (fun i ↦ ((x i : ℂ) ^ g.2.2.2))

private theorem trace_four_root (label : n → s) (x : s → ℝ) (p : ℕ) (B : Matrix n n ℂ) :
    trace ((rootDiagonal label x p * B) ^ 4) =
      contract (spectralBlock label B) (fun i j k l ↦ (balanced p (x i) (x j) (x k) (x l) : ℂ)) := by
  simpa only [rootDiagonal, eigenDiagonal, balanced, Complex.ofReal_mul,
    pow_succ, pow_zero, one_mul] using trace_four_weighted label B
      (fun i ↦ (x i ^ ((p : ℝ) / 4) : ℝ))
      (fun i ↦ (x i ^ ((p : ℝ) / 4) : ℝ))
      (fun i ↦ (x i ^ ((p : ℝ) / 4) : ℝ))
      (fun i ↦ (x i ^ ((p : ℝ) / 4) : ℝ))

private theorem diagonal_gap_scaled (label : n → s) (x : s → ℝ) (p : ℕ) (B : Matrix n n ℂ) :
    ((gaps p).card : ℂ) *
        (wordMean p (eigenDiagonal label x) B - trace ((rootDiagonal label x p * B) ^ 4)) =
      contract (spectralBlock label B)
        (fun i j k l ↦ (gapDefect p (x i) (x j) (x k) (x l) : ℂ)) := by
  have hc : ((gaps p).card : ℂ) ≠ 0 := by exact_mod_cast (gaps_card_pos p).ne'
  rw [mul_sub, wordMean_eq_gaps, mul_div_cancel₀ _ hc, trace_four_root]
  simp_rw [gapTrace_diagonal]
  change (∑ g ∈ gaps p, contract (spectralBlock label B) _) -
    ((gaps p).card : ℂ) • contract (spectralBlock label B) _ = _
  rw [← map_sum, ← map_smul, ← map_sub]
  congr 1
  funext i j k l
  simp only [gapDefect, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_sum, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]

end Diagonal

private theorem wordMean_conjugation (p : ℕ) (U : Matrix.unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    wordMean p (Unitary.conjStarAlgAut ℂ _ U A) (Unitary.conjStarAlgAut ℂ _ U B) = wordMean p A B := by
  let f := Unitary.conjStarAlgAut ℂ _ U
  have h (w : List Bool) : evalWord (f A) (f B) w = f (evalWord A B w) := by
    induction w with
    | nil => simp [evalWord]
    | cons b w ih => cases b <;> simp [evalWord, ih]
  change wordMean p (f A) (f B) = wordMean p A B
  simp only [wordMean, h]
  simp only [f, trace_conjugation]

end RefinedBMV.FourCopyGap
