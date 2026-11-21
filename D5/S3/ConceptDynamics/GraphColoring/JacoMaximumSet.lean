/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMaximumSet
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift]
   utility: none
   digest: The maximum set of a finite linear Jaco graph is the label interval [p, R_(n-p)] of one, two or three vertices. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift

/-! Maximum-degree vertex sets of the finite linear Jaco graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-
proof_shape:
  jaconian: definition
  mem_jaconian: content (consumer: set_eq)
  g_mul, phi_eq, g_quad, g_bounds, g_fine: bind-only (consumers: the floor lemmas, result,
    strict_out_singleton)
  bo, frac_eq, P_eq, P_real, P_le, out_shift, P_succ: bind-only (consumers: right_t, out_p,
    out_p1, set_eq, result, strict_out_singleton)
  not_int, frac_ne: content (consumers: regions, result)
  right_t, out_p, out_p1, set_eq, card_eq, regions: content (consumer: result)
  result: content
  strict_out_singleton: content
escape_witness: the degree formula min(i, n - b_i) and the Beatty threshold turn the
  maximum set into the label interval [p, R_t]; the golden identities
  (t + 1) * phi = F + x_n * phi^2, F / phi = n + 2 - F - x_n * phi and their shifts put every
  endpoint and outdegree at a fixed integer plus a floor of x_n against 1/phi^2 and 1/phi.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

/-- The labels of the vertices of `jaco n` attaining its maximum degree. -/
noncomputable def jaconian (n : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun v : Vertex n => (jaco n).degree v = (jaco n).maxDegree).map
    (Function.Embedding.subtype _)

private theorem mem_jaconian (n i : ℕ) :
    i ∈ jaconian n ↔ 1 ≤ i ∧ i ≤ n ∧ (jaco n).maxDegree ≤ i ∧
      i ≤ jacoRight (n - (jaco n).maxDegree) := by
  set P := (jaco n).maxDegree
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp h
    have hv := (Finset.mem_filter.mp hv).2
    simp only [Function.Embedding.coe_subtype]
    have hmem := Finset.mem_Icc.mp v.2
    rw [JacoMaximumDegree.degree_formula] at hv
    have hb := beatty_bounds v.1 hmem.1
    refine ⟨hmem.1, hmem.2, by omega, ?_⟩
    rw [endpoint_eq_beatty]
    exact (beatty_threshold v.1 (n - P)).mpr (by omega)
  · rintro ⟨h1, h2, h3, h4⟩
    have hmem : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    refine Finset.mem_map.mpr ⟨⟨i, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hle := (jaco n).degree_le_maxDegree ⟨i, hmem⟩
    rw [JacoMaximumDegree.degree_formula] at hle ⊢
    rw [endpoint_eq_beatty] at h4
    have := (beatty_threshold i (n - P)).mp h4
    simp only at hle ⊢
    omega


private theorem g_mul : Real.goldenRatio⁻¹ * Real.goldenRatio = 1 :=
  inv_mul_cancel₀ Real.goldenRatio_pos.ne'

private theorem phi_eq : Real.goldenRatio = 1 + Real.goldenRatio⁻¹ := by
  rw [Real.inv_goldenRatio]; linarith [Real.one_sub_goldenConj]

private theorem bo (k : ℕ) : (beattyOut k : ℤ) = ⌊((k : ℝ) + 1) * Real.goldenRatio⁻¹⌋ := by
  have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) / Real.goldenRatio := by
    have := Real.goldenRatio_pos; positivity
  rw [beattyOut, Int.natCast_floor_eq_floor hpos, div_eq_mul_inv]

private theorem not_int (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : (k : ℝ) * Real.goldenRatio⁻¹ ≠ m :=
  (Real.goldenRatio_irrational.inv.natCast_mul (by omega)).ne_int m

private theorem frac_eq (n : ℕ) :
    frac n = ((n : ℝ) + 2) * Real.goldenRatio⁻¹ - ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ := by
  rw [frac, Int.fract, div_eq_mul_inv]

private theorem P_eq (n : ℕ) :
    ((jaco n).maxDegree : ℤ) = ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ - 1 := by
  have := delta_eq_floor n
  rw [delta, div_eq_mul_inv] at this
  exact this

private theorem P_le (n : ℕ) : (jaco n).maxDegree ≤ n := by
  have h := P_eq n
  have hg1 : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hlt : ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ ≤ (n : ℤ) + 1 := by
    rw [Int.floor_le_iff]; push_cast
    have := mul_lt_of_lt_one_right (by positivity : (0 : ℝ) < (n : ℝ) + 2) hg1
    linarith
  omega


private theorem g_quad : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]; ring

private theorem P_real (n : ℕ) :
    ((jaco n).maxDegree : ℝ) = (⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ : ℝ) - 1 := by
  exact_mod_cast P_eq n

/-- `R_t = p + ⌊x_n φ²⌋` with `t = n - p`. -/
private theorem right_t (n : ℕ) :
    (jacoRight (n - (jaco n).maxDegree) : ℤ) =
      (jaco n).maxDegree + ⌊frac n * Real.goldenRatio ^ 2⌋ := by
  have hP := P_eq n
  have hPr := P_real n
  have hle := P_le n
  rw [endpoint_eq_beatty]
  push_cast [hle]
  rw [bo, frac_eq]
  set g := Real.goldenRatio⁻¹ with hg
  set F := ⌊((n : ℝ) + 2) * g⌋ with hF
  have hφ : Real.goldenRatio = 1 + g := phi_eq
  have hq : g ^ 2 + g = 1 := g_quad
  have hc : (((n - (jaco n).maxDegree : ℕ) : ℝ) + 1) * g =
      (((n : ℝ) + 2) * g - F) * Real.goldenRatio ^ 2 + ((2 * F - n - 2 : ℤ) : ℝ) := by
    push_cast [hle]
    rw [hPr]
    linear_combination
      (F * g + F * Real.goldenRatio + F - g ^ 2 * n - 2 * g ^ 2 - g * n * Real.goldenRatio
        - g * n - 2 * g * Real.goldenRatio - 2 * g) * hφ + (F - g * n - 2 * g - n - 2) * hq
  rw [hc, Int.floor_add_intCast]
  omega

/-- `R_p = n + 1 + ⌊-x_n φ⌋` and `b_p = n + 2 - F + ⌊-x_n φ⌋`. -/
private theorem out_p (n : ℕ) :
    (beattyOut (jaco n).maxDegree : ℤ) =
      (n + 2 - ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋) + ⌊-(frac n * Real.goldenRatio)⌋ := by
  have hPr := P_real n
  rw [bo, frac_eq]
  set g := Real.goldenRatio⁻¹ with hg
  set F := ⌊((n : ℝ) + 2) * g⌋ with hF
  have hφ : Real.goldenRatio = 1 + g := phi_eq
  have hq : g ^ 2 + g = 1 := g_quad
  have hc : (((jaco n).maxDegree : ℝ) + 1) * g =
      -((((n : ℝ) + 2) * g - F) * Real.goldenRatio) + ((n + 2 - F : ℤ) : ℝ) := by
    rw [hPr]; push_cast
    linear_combination (-F + g * n + 2 * g) * hφ + (n + 2) * hq
  rw [hc, Int.floor_add_intCast]
  ring

private theorem out_p1 (n : ℕ) :
    (beattyOut ((jaco n).maxDegree + 1) : ℤ) =
      (n + 2 - ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋) +
        ⌊Real.goldenRatio⁻¹ - frac n * Real.goldenRatio⌋ := by
  have hPr := P_real n
  rw [bo, frac_eq]
  set g := Real.goldenRatio⁻¹ with hg
  set F := ⌊((n : ℝ) + 2) * g⌋ with hF
  have hφ : Real.goldenRatio = 1 + g := phi_eq
  have hq : g ^ 2 + g = 1 := g_quad
  have hc : ((((jaco n).maxDegree + 1 : ℕ) : ℝ) + 1) * g =
      (g - (((n : ℝ) + 2) * g - F) * Real.goldenRatio) + ((n + 2 - F : ℤ) : ℝ) := by
    push_cast; rw [hPr]
    linear_combination (-F + g * n + 2 * g) * hφ + (n + 2) * hq
  rw [hc, Int.floor_add_intCast]
  ring


private theorem out_shift (n k : ℕ) :
    (beattyOut (n + k) : ℤ) =
      ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹ + ((k : ℝ) - 1) * Real.goldenRatio⁻¹⌋ := by
  rw [bo]; congr 1; push_cast; ring

private theorem P_succ (n : ℕ) :
    ((jaco (n + 1)).maxDegree : ℤ) =
      ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹⌋ - 1 := by
  rw [P_eq]; congr 2; push_cast; ring

/-- The fractional part `x_n` avoids the thresholds `0`, `1 / φ²` and `1 / φ`. -/
private theorem frac_ne (n : ℕ) :
    frac n ≠ 0 ∧ frac n ≠ 1 - Real.goldenRatio⁻¹ ∧ frac n ≠ Real.goldenRatio⁻¹ := by
  rw [frac_eq]
  set g := Real.goldenRatio⁻¹
  set F := ⌊((n : ℝ) + 2) * g⌋
  refine ⟨fun h => not_int (n + 2) (by omega) F ?_, fun h => not_int (n + 3) (by omega) (F + 1) ?_,
    fun h => not_int (n + 1) (by omega) F ?_⟩ <;> push_cast <;> linarith


private theorem g_bounds : 1 / 2 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 1 := by
  have hq := g_quad
  have hg0 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  constructor <;> nlinarith

/-- For `n ≥ 2` the maximum set is the label interval `[p, R_(n-p)]`, inside `[1, n]`. -/
private theorem set_eq (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ (jaco n).maxDegree ∧ jacoRight (n - (jaco n).maxDegree) ≤ n ∧
      jaconian n = Finset.Icc (jaco n).maxDegree (jacoRight (n - (jaco n).maxDegree)) := by
  have hP := P_eq n
  have hRt := right_t n
  have hle := P_le n
  have hxe := frac_eq n
  have hx0 : 0 ≤ frac n := Int.fract_nonneg _
  have hx1 : frac n < 1 := Int.fract_lt_one _
  obtain ⟨hg5, hg1⟩ := g_bounds
  set g := Real.goldenRatio⁻¹ with hg
  set F := ⌊((n : ℝ) + 2) * g⌋ with hF
  have hφ : Real.goldenRatio = 1 + g := phi_eq
  have hgφ : g * Real.goldenRatio = 1 := g_mul
  have hF2 : 2 ≤ F := by
    rw [hF, Int.le_floor]; push_cast
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hFr : (2 : ℝ) ≤ F := by exact_mod_cast hF2
  have hyφ : (F + frac n) * Real.goldenRatio = (n : ℝ) + 2 := by
    rw [hxe]; linear_combination ((n : ℝ) + 2) * hgφ
  have hbound : ⌊frac n * Real.goldenRatio ^ 2⌋ ≤ (n : ℤ) + 1 - F := by
    rw [Int.floor_le_iff]; push_cast
    have : frac n < F * g := by nlinarith
    rw [hφ] at hyφ ⊢
    nlinarith
  have hP1 : 1 ≤ (jaco n).maxDegree := by omega
  have hRn : jacoRight (n - (jaco n).maxDegree) ≤ n := by omega
  refine ⟨hP1, hRn, ?_⟩
  ext i
  rw [mem_jaconian, Finset.mem_Icc]
  omega


private theorem card_eq (n : ℕ) (hn : 2 ≤ n) :
    ((jaconian n).card : ℤ) = ⌊frac n * Real.goldenRatio ^ 2⌋ + 1 := by
  obtain ⟨h1, h2, h3⟩ := set_eq n hn
  have hRt := right_t n
  rw [h3, Nat.card_Icc]
  have hge : (jaco n).maxDegree ≤ jacoRight (n - (jaco n).maxDegree) := by
    have : 0 ≤ ⌊frac n * Real.goldenRatio ^ 2⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
    omega
  omega

/-- The floor values that decide every clause, on the two sides of `1 / φ²`. -/
private theorem regions (n : ℕ) :
    let x := frac n
    let g := Real.goldenRatio⁻¹
    (x < 1 - g →
      ⌊x * Real.goldenRatio ^ 2⌋ = 0 ∧ ⌊-(x * Real.goldenRatio)⌋ = -1 ∧
      ⌊g - x * Real.goldenRatio⌋ = 0 ∧ ⌊x - g⌋ = -1 ∧ ⌊x + g⌋ = 0 ∧
      (1 ≤ ⌊(x + g) * Real.goldenRatio ^ 2⌋ ∧ ⌊(x + g) * Real.goldenRatio ^ 2⌋ ≤ 2)) ∧
    (1 - g < x →
      1 ≤ ⌊x * Real.goldenRatio ^ 2⌋ ∧ ⌊g - x * Real.goldenRatio⌋ = -1 ∧ ⌊x + g⌋ = 1) := by
  intro x g
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  have hne := frac_ne n
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne.1)
  obtain ⟨hg5, hg1⟩ := g_bounds
  have hq : g ^ 2 + g = 1 := g_quad
  have hφ : Real.goldenRatio = 1 + g := phi_eq
  have hφ2 : Real.goldenRatio ^ 2 = 2 + g := by rw [hφ]; linear_combination hq
  constructor
  · intro hA
    have hxφ : x * Real.goldenRatio < g := by rw [hφ]; nlinarith
    have hxφ2 : x * Real.goldenRatio ^ 2 < 1 := by rw [hφ2]; nlinarith
    have hxφ0 : 0 < x * Real.goldenRatio := by rw [hφ]; nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · rw [Int.le_floor]; push_cast; rw [hφ2]; nlinarith
    · rw [← Int.lt_add_one_iff, Int.floor_lt]; push_cast; rw [hφ2]; nlinarith
  · intro hB
    refine ⟨?_, ?_, ?_⟩
    · rw [Int.le_floor]; push_cast; rw [hφ2]; nlinarith
    · rw [Int.floor_eq_iff]; push_cast; rw [hφ]; constructor <;> nlinarith
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith


/-- The maximum set of every finite linear Jaco graph of order at least two is the
label interval `[p, R_(n-p)]` with one, two or three members, `1 + ⌊x_n φ²⌋` of
them; it is a singleton exactly when `x_n < 1 / φ²`, equivalently under each of
the three source conditions; and a singleton maximum is followed by a doubleton or
tripleton maximum set starting at the same label. -/
theorem result :
    jaconian 1 = {1} ∧
    (∀ n : ℕ, 2 ≤ n →
      jacoRight (n - (jaco n).maxDegree) ≤ n ∧
      jaconian n = Finset.Icc (jaco n).maxDegree (jacoRight (n - (jaco n).maxDegree)) ∧
      ((jaconian n).card : ℤ) = ⌊frac n * Real.goldenRatio ^ 2⌋ + 1 ∧
      ((jaconian n).card = 1 ∨ (jaconian n).card = 2 ∨ (jaconian n).card = 3)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (jaconian n = {(jaco n).maxDegree} ↔ frac n < 1 - Real.goldenRatio⁻¹) ∧
      (jaconian n = {(jaco n).maxDegree} ↔
        n = jacoRight (jaco n).maxDegree ∧
          beattyOut ((jaco n).maxDegree + 1) = beattyOut (jaco n).maxDegree + 1) ∧
      (jaconian n = {(jaco n).maxDegree} ↔ beattyOut (n + 1) = beattyOut (n + 2)) ∧
      (jaconian n = {(jaco n).maxDegree} ↔
        (jaco (n + 1)).maxDegree = (jaco n).maxDegree)) ∧
    (∀ n : ℕ, 2 ≤ n → jaconian n = {(jaco n).maxDegree} →
      jacoRight ((jaco n).maxDegree + 1) = n + 2 ∧
      beattyOut n = (jaco n).maxDegree ∧
      (∀ hv : n ∈ Finset.Icc 1 n, (jaco n).degree ⟨n, hv⟩ = n - (jaco n).maxDegree) ∧
      (jaconian (n + 1) = Finset.Icc (jaco n).maxDegree ((jaco n).maxDegree + 1) ∨
        jaconian (n + 1) = Finset.Icc (jaco n).maxDegree ((jaco n).maxDegree + 2))) := by
  -- singleton criterion in terms of the fractional part
  have single (n : ℕ) (hn : 2 ≤ n) :
      jaconian n = {(jaco n).maxDegree} ↔ frac n < 1 - Real.goldenRatio⁻¹ := by
    obtain ⟨h1, h2, h3⟩ := set_eq n hn
    have hRt := right_t n
    have hne := frac_ne n
    have hreg := regions n
    rw [h3]
    constructor
    · intro h
      by_contra hA
      have hB : 1 - Real.goldenRatio⁻¹ < frac n := lt_of_le_of_ne (not_lt.mp hA) (Ne.symm hne.2.1)
      have := (hreg.2 hB).1
      have hmem : (jaco n).maxDegree + 1 ∈ Finset.Icc (jaco n).maxDegree
          (jacoRight (n - (jaco n).maxDegree)) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [h, Finset.mem_singleton] at hmem
      omega
    · intro hA
      have := (hreg.1 hA).1
      have hR : jacoRight (n - (jaco n).maxDegree) = (jaco n).maxDegree := by omega
      rw [hR, Finset.Icc_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    rw [mem_jaconian, Finset.mem_singleton]
    have hP : (jaco 1).maxDegree = 0 := by
      have h := P_eq 1
      have hf : ⌊((1 : ℕ) + 2 : ℝ) * Real.goldenRatio⁻¹⌋ = 1 := by
        obtain ⟨hg5, hg1⟩ := g_bounds
        have hq := g_quad
        rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
      omega
    have hR : jacoRight 1 = 2 := by decide +kernel
    rw [hP]
    simp only [Nat.sub_zero, hR]
    omega
  · intro n hn
    obtain ⟨h1, h2, h3⟩ := set_eq n hn
    have hc := card_eq n hn
    have hfl0 : 0 ≤ ⌊frac n * Real.goldenRatio ^ 2⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
    have hfl2 : ⌊frac n * Real.goldenRatio ^ 2⌋ ≤ 2 := by
      rw [← Int.lt_add_one_iff, Int.floor_lt]
      have hx1 : frac n < 1 := Int.fract_lt_one _
      obtain ⟨hg5, hg1⟩ := g_bounds
      have hφ2 : Real.goldenRatio ^ 2 = 2 + Real.goldenRatio⁻¹ := by
        rw [Real.goldenRatio_sq]; linarith [phi_eq]
      rw [hφ2]; push_cast
      nlinarith [Int.fract_nonneg (((n : ℝ) + 2) / Real.goldenRatio)]
    exact ⟨h2, h3, hc, by omega⟩
  · intro n hn
    have hs := single n hn
    have hP := P_eq n
    have hbP := out_p n
    have hbP1 := out_p1 n
    have hb1 := out_shift n 1
    have hb2 := out_shift n 2
    have hPs := P_succ n
    have hxe := frac_eq n
    have hreg := regions n
    have hne := frac_ne n
    set F := ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ with hF
    have hy : ((n : ℝ) + 2) * Real.goldenRatio⁻¹ = frac n + (F : ℝ) := by linarith
    have hplus : ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹⌋ =
        ⌊frac n + Real.goldenRatio⁻¹⌋ + F := by
      rw [hy, show frac n + (F : ℝ) + Real.goldenRatio⁻¹ =
        frac n + Real.goldenRatio⁻¹ + (F : ℝ) by ring, Int.floor_add_intCast]
    rw [show ((2 : ℕ) : ℝ) - 1 = 1 by norm_num, one_mul] at hb2
    rw [show ((1 : ℕ) : ℝ) - 1 = 0 by norm_num, zero_mul, add_zero] at hb1
    have hR := endpoint_eq_beatty (jaco n).maxDegree
    refine ⟨hs, ?_, ?_, ?_⟩
    · rw [hs]
      constructor
      · intro hA
        obtain ⟨_, h2, h3, _, _, _⟩ := hreg.1 hA
        constructor <;> omega
      · rintro ⟨h1, h2⟩
        by_contra hA
        have hB : 1 - Real.goldenRatio⁻¹ < frac n :=
          lt_of_le_of_ne (not_lt.mp hA) (Ne.symm hne.2.1)
        have := (hreg.2 hB).2.1
        omega
    · rw [hs]
      constructor
      · intro hA
        have := (hreg.1 hA).2.2.2.2.1
        omega
      · intro h
        by_contra hA
        have hB : 1 - Real.goldenRatio⁻¹ < frac n :=
          lt_of_le_of_ne (not_lt.mp hA) (Ne.symm hne.2.1)
        have := (hreg.2 hB).2.2
        omega
    · rw [hs]
      constructor
      · intro hA
        have := (hreg.1 hA).2.2.2.2.1
        omega
      · intro h
        by_contra hA
        have hB : 1 - Real.goldenRatio⁻¹ < frac n :=
          lt_of_le_of_ne (not_lt.mp hA) (Ne.symm hne.2.1)
        have := (hreg.2 hB).2.2
        omega
  · intro n hn hsing
    have hA := (single n hn).mp hsing
    obtain ⟨r1, r2, r3, -, r5, r6⟩ := (regions n).1 hA
    have hP := P_eq n
    have hbP1 := out_p1 n
    have hPs := P_succ n
    have hxe := frac_eq n
    set F := ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ with hF
    have hy : ((n : ℝ) + 2) * Real.goldenRatio⁻¹ = frac n + (F : ℝ) := by linarith
    have hplus : ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹⌋ =
        ⌊frac n + Real.goldenRatio⁻¹⌋ + F := by
      rw [hy, show frac n + (F : ℝ) + Real.goldenRatio⁻¹ =
        frac n + Real.goldenRatio⁻¹ + (F : ℝ) by ring, Int.floor_add_intCast]
    have hbn : beattyOut n = (jaco n).maxDegree :=
      ((JacoDegreeShift.result n).2.1.mpr (by linarith [g_bounds.1])).symm
    have hR1 := endpoint_eq_beatty ((jaco n).maxDegree + 1)
    have hPeq : (jaco (n + 1)).maxDegree = (jaco n).maxDegree := by omega
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro hv
      rw [JacoMaximumDegree.degree_formula]
      simp only
      omega
    · -- the next order
      obtain ⟨_, _, h3⟩ := set_eq (n + 1) (by omega)
      have hRt := right_t (n + 1)
      have hx' : frac (n + 1) = frac n + Real.goldenRatio⁻¹ := by
        have := frac_eq (n + 1)
        have hfl : ⌊(((n + 1 : ℕ) : ℝ) + 2) * Real.goldenRatio⁻¹⌋ = F := by
          rw [show (((n + 1 : ℕ) : ℝ) + 2) * Real.goldenRatio⁻¹ =
            ((n : ℝ) + 2) * Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹ by push_cast; ring, hplus]
          omega
        rw [this, hfl]; push_cast; linarith
      rw [hx'] at hRt
      rw [h3, hPeq]
      obtain ⟨s1, s2⟩ := r6
      rcases (show ⌊(frac n + Real.goldenRatio⁻¹) * Real.goldenRatio ^ 2⌋ = 1 ∨
          ⌊(frac n + Real.goldenRatio⁻¹) * Real.goldenRatio ^ 2⌋ = 2 by omega) with h | h
      · left
        have hR' : jacoRight (n + 1 - (jaco n).maxDegree) = (jaco n).maxDegree + 1 := by
          rw [← hPeq]; omega
        rw [hR']
      · right
        have hR' : jacoRight (n + 1 - (jaco n).maxDegree) = (jaco n).maxDegree + 2 := by
          rw [← hPeq]; omega
        rw [hR']

#print axioms result

private theorem g_fine : (61 : ℝ) / 100 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 5 / 8 := by
  have hq := g_quad
  have hg0 : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  constructor <;> nlinarith

/-- Strictly increasing outdegrees around `n` force the singleton maximum set
`{b_n}`. -/
theorem strict_out_singleton (n : ℕ) (h1 : beattyOut (n - 1) < beattyOut n)
    (h2 : beattyOut n < beattyOut (n + 1)) : jaconian n = {beattyOut n} := by
  obtain ⟨-, -, hsing, -⟩ := result
  obtain ⟨hg61, hg58⟩ := g_fine
  by_cases hn : n ≤ 1
  · exfalso
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · simp at h1
    · have b1 : (beattyOut 1 : ℤ) = 1 := by
        rw [bo, Int.floor_eq_iff]; push_cast; constructor <;> linarith
      have b2 : (beattyOut (1 + 1) : ℤ) = 1 := by
        rw [bo, Int.floor_eq_iff]; push_cast; constructor <;> linarith
      omega
  have hn : 2 ≤ n := by omega
  have hP := P_eq n
  have hxe := frac_eq n
  have hx0 : 0 ≤ frac n := Int.fract_nonneg _
  have hb0 := out_shift n 0
  have hb1 := out_shift n 1
  have hbm : (beattyOut (n - 1) : ℤ) = ⌊(n : ℝ) * Real.goldenRatio⁻¹⌋ := by
    rw [bo]; congr 1; push_cast [show 1 ≤ n by omega]; ring
  set F := ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹⌋ with hF
  rw [show ((0 : ℕ) : ℝ) - 1 = -1 by norm_num, Nat.add_zero] at hb0
  rw [show ((1 : ℕ) : ℝ) - 1 = 0 by norm_num, zero_mul, add_zero] at hb1
  have e0 : ⌊((n : ℝ) + 2) * Real.goldenRatio⁻¹ + -1 * Real.goldenRatio⁻¹⌋ =
      ⌊frac n - Real.goldenRatio⁻¹⌋ + F := by
    rw [show ((n : ℝ) + 2) * Real.goldenRatio⁻¹ + -1 * Real.goldenRatio⁻¹ =
      frac n - Real.goldenRatio⁻¹ + (F : ℝ) by linarith, Int.floor_add_intCast]
  have em : ⌊(n : ℝ) * Real.goldenRatio⁻¹⌋ = ⌊frac n - 2 * Real.goldenRatio⁻¹⌋ + F := by
    rw [show (n : ℝ) * Real.goldenRatio⁻¹ =
      frac n - 2 * Real.goldenRatio⁻¹ + (F : ℝ) by linarith, Int.floor_add_intCast]
  -- b_n < b_(n+1) gives x < 1/φ; then b_(n-1) < b_n gives x < 2/φ - 1 < 1/φ²
  have hlt1 : frac n < Real.goldenRatio⁻¹ := by
    by_contra hc
    have : 0 ≤ ⌊frac n - Real.goldenRatio⁻¹⌋ := Int.floor_nonneg.mpr (by linarith)
    omega
  have hm1 : ⌊frac n - Real.goldenRatio⁻¹⌋ = -1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have hlt2 : frac n < 2 * Real.goldenRatio⁻¹ - 1 := by
    by_contra hc
    have : -1 ≤ ⌊frac n - 2 * Real.goldenRatio⁻¹⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  have hA : frac n < 1 - Real.goldenRatio⁻¹ := by linarith
  have hbn : beattyOut n = (jaco n).maxDegree := ((JacoDegreeShift.result n).2.1.mpr hlt1).symm
  rw [hbn]
  exact ((hsing n hn).1).mpr hA

#print axioms strict_out_singleton

end D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet
