/- GID: D5/S3/Combinatorics/Circle/RobustSelectorRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/RobustSelectorRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Circle/RobustSelectorRefutation.claim; result=D5/S3/Combinatorics/Circle/RobustSelectorRefutation.result; claim=D5/S3/Combinatorics/Circle/RobustSelectorRefutation.claim
   digest: The full original modular source refutes the universal robust residue selector. -/
module
public import D5.S3.Combinatorics.Circle.OriginalLowerFullBank

/-! # A robust selector obstruction

The complete original physical source admits a counterexample to the proposed
robust lower-half residue selector. This intermediate obstruction does not settle
original word existence.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

@[expose] public section
namespace D5.S3.Combinatorics.Circle.RobustSelectorRefutation

open SourceWidth M5FullWordConsumer OriginalLowerFullBank
open Fin.NatCast
open scoped BigOperators

/-- Original coordinate, computed from the prescribed physical x. -/
def z {k : ℕ} (t : ℕ) (x : Fin k) : ℤ :=
  modulus k - 2 * actualSource k t x

def E {k : ℕ} (t : ℕ) (x : Fin k) (V : ℤ) : ℤ :=
  (modulus k + z t x - 2 * V) / 2

def F {k : ℕ} (t : ℕ) (x : Fin k) : ℤ :=
  (2 : ℤ) ^ (sourceLength t x 6 + 1)

/-- Actual next-row coordinates; A is always sourceSeed 8, the original a0. -/
def B0 {k : ℕ} (t : ℕ) (x : Fin k) : ℤ :=
  modulus k - 2 * (2 : ℤ) ^ sourceLength t x 8 * sourceSeed t x 8

def T1 {k : ℕ} (t : ℕ) (x : Fin k) : ℤ :=
  modulus k - 2 * (2 : ℤ) ^ sourceLength t x 9 * B0 t x

/-- Precisely the original CORNER and GEOMETRY, with integer floor quotients.
The R1/nonET/u>z telescope itself is imported as OriginalSource below. -/
structure CornerGeometry (m t L : ℕ) (b : ℤ) {k : ℕ} (x : Fin k) : Prop where
  corner_pairs : 5 < m
  empty_v : (2 : ℤ) ^ sourceLength t x 5 = 1
  F_lower : 4 ≤ F t x
  F_upper : F t x ≤ (2 : ℤ) ^ (L + 1) / 4
  y_bounds : b ≤ sourceSeed t x 7 ∧ sourceSeed t x 7 ≤ 2 * b - 3
  original_a0 : 2 * b + 1 ≤ sourceSeed t x 8
  ell_bound : E t x (sourceSeed t x 8) / b ≤ (2 : ℤ) ^ L - 3
  corner_residual : (sourceSeed t x 7 - 1) / 2 <
    E t x (sourceSeed t x 8) - (E t x (sourceSeed t x 8) / b) * b
  geometry_branch :
    (F t x / 2 = 2 ∧ (2 : ℤ) ^ L = 8) ∨
    (F t x / 2 = 4 ∧ (2 : ℤ) ^ L = 16)
  geometry_order : sourceSeed t x 8 < B0 t x ∧ B0 t x < T1 t x
  geometry_steep : B0 t x + 1 < 2 * sourceSeed t x 8

def launchLambda {k : ℕ} (t : ℕ) (x : Fin k) : ℤ :=
  (((sourceSeed t x 12 - z t x) / 2) - 1) / sourceSeed t x 11

/-- The natural binary encoding of the depleted row mask. -/
def launchMask {k : ℕ} (t : ℕ) (x : Fin k) : ℕ :=
  2 ^ sourceLength t x 11 - 1 - (launchLambda t x).toNat

/-- Literal physical submask of the ACTUAL row RS, not a scalar interval. -/
def bitsRS {k : ℕ} (t : ℕ) (x : Fin k) : Finset (Fin k) :=
  sourceMask t x 11
    (Finset.univ.filter (fun j : Fin (sourceLength t x 11) =>
      (launchMask t x).testBit j.val))

def charge {k : ℕ} (t : ℕ) (K : Finset (Fin k)) : ℤ :=
  ∑ i ∈ K, actualSource k t i

/-- The FIRST r actual pairs after P12 are empty on BOTH signs. -/
def EmptyPairs {k : ℕ} (t : ℕ) (x : Fin k) (r : ℕ) : Prop :=
  ∀ j : Fin r,
    sourceLength t x (12 + 2 * j.val) = 0 ∧
    sourceLength t x (13 + 2 * j.val) = 0

def endpointSeed {k : ℕ} (t : ℕ) (x : Fin k) (r : ℕ) : ℤ :=
  sourceSeed t x (12 + 2 * r)

def compressedHeight {k : ℕ} (t : ℕ) (x : Fin k) (r : ℕ)
    (K : Finset (Fin k)) : ℤ :=
  (modulus k - endpointSeed t x r + 2 * z t x) / 4 - charge t K

/-- Exact universal intermediate selector. r<=m-7 INCLUDES the true last
positive frontier P_(2m-2). There is no endpoint-factor or viability premise.
N<=8*charge is the rational threshold charge>=N/8 without floor weakening. -/
def claim : Prop :=
  ∀ (m k t L : ℕ) (a b : ℤ) (p d x : Fin k),
    OriginalSource m k t L a b p d x →
    CornerGeometry m t L b x →
    (2 : ℤ) ^ L = 16 → F t x = 8 → 9 ≤ m →
    z t x < sourceSeed t x 12 →
    3 * sourceSeed t x 12 < modulus k →
    ∀ r : ℕ, 1 ≤ r → r ≤ m - 7 → EmptyPairs t x r →
      ∃ K : Finset (Fin k), K ⊆ bitsRS t x ∧
        modulus k ≤ 8 * charge t K ∧
        compressedHeight t x r K % endpointSeed t x r ≤
          (endpointSeed t x r - 1) / 2

private def t51 : ℕ := 2183577952606008
private def x51 : Fin 51 := 50
private def p51 : Fin 51 := 9
private def d51 : Fin 51 := 4
private def a51 : ℤ := 53391520898079
private def b51 : ℤ := 68700259149599

/-- The actual inclusive-threshold LARGE offsets, with physical multiplicity. -/
private def offsetList51 : List (Fin 51) :=
  [0, 5, 10, 15, 17, 21, 22, 25, 29, 31, 32, 33, 36, 37, 38, 39, 40, 43, 45, 48]

private def offsets51 : Finset (Fin 51) := offsetList51.toFinset

private theorem k51_offsets : largeOffsets t51 x51 = offsets51 := by decide +kernel

/-- Normalize the sorted original occurrence enumeration before computing rows. -/
private theorem k51_offset (i : ℕ) (hi : i < 20) :
    sourceOffset t51 x51 i =
      ([0, 5, 10, 15, 17, 21, 22, 25, 29, 31, 32, 33, 36, 37, 38, 39, 40, 43, 45, 48] :
        List ℕ).getD i 51 := by
  have hc : offsets51.card = 20 := by decide +kernel
  have hs : offsets51.sort (· ≤ ·) = offsetList51 := by
    exact (List.toFinset_sort (r := (· ≤ ·)) (l := offsetList51)
      (by decide +kernel)).mpr (by decide +kernel)
  simp only [sourceOffset, cut, k51_offsets]
  rw [dite_eq_left (show i < offsets51.card by simpa only [hc] using hi)]
  simp only [Finset.orderEmbOfFin_apply]
  simp only [hs]
  interval_cases i <;> rfl

local macro "source_decide" : tactic =>
  `(tactic| (
    try simp (disch := omega) only [F, B0, T1, E, z, endpointSeed, compressedHeight,
      launchMask, launchLambda, sourceSeed, sourceLength, sourceParent, k51_offset]
    all_goals decide +kernel))

/-- All fields are checked on the original modular definition, not supplied
as a ledger or as hypotheses. Finite quantifiers retain ALL 51 labels. -/
private theorem k51_original : OriginalSource 10 51 t51 4 a51 b51 p51 d51 x51 := by
  refine {
    pairs := by source_decide
    nonzero := by source_decide
    a_positive := by source_decide
    minimum_inequalities := by source_decide
    negative_minimum := by source_decide
    positive_minimum := by source_decide
    negative_attained := ⟨(10 : Fin 51), by source_decide⟩
    positive_attained := ⟨(5 : Fin 51), by source_decide⟩
    p_maximum := by source_decide
    d_minimum := by source_decide
    positive_count := by source_decide
    negative_count := by source_decide
    x_positive_large := by source_decide
    incoming_d := by source_decide
    p_row := ?_
    x_row_length := by source_decide
    d_row_length := by source_decide
    beta_row_length := by source_decide
    gamma_row_short := by source_decide
    c0_hard := by source_decide
    beta_alternative := Or.inl (by source_decide)
    delta_positive := by source_decide
    delta_hard := by source_decide
    b1_hard := by source_decide
    w_bounds := by source_decide
    w_hard := by source_decide
    w_row_length := by source_decide
    nonET := ⟨(41 : Fin 51), by source_decide, by source_decide, by source_decide⟩
    u_above_z := by source_decide
    power_branch := Or.inr (by source_decide) }
  refine ⟨by source_decide, by source_decide, ?_, by source_decide⟩
  intro j hj
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> source_decide

private theorem k51_corner : CornerGeometry 10 t51 4 b51 x51 := by
  exact {
    corner_pairs := by source_decide
    empty_v := by source_decide
    F_lower := by source_decide
    F_upper := by source_decide
    y_bounds := by source_decide
    original_a0 := by source_decide
    ell_bound := by source_decide
    corner_residual := by source_decide
    geometry_branch := Or.inr ⟨by source_decide, by source_decide⟩
    geometry_order := by source_decide
    geometry_steep := by source_decide }

private theorem k51_bits : bitsRS t51 x51 = {(34 : Fin 51)} := by
  have hlen : sourceLength t51 x51 11 = 2 := by source_decide
  have hparent : sourceParent t51 x51 11 = (32 : Fin 51) := by source_decide
  have hmask : launchMask t51 x51 = 2 := by source_decide
  ext i
  simp only [bitsRS, sourceMask, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hbit, rfl⟩
    have hj : j.val < 2 := by simpa only [hlen] using j.isLt
    have hval : j.val = 1 := by
      by_contra hne
      have hz : j.val = 0 := by omega
      rw [hmask, hz] at hbit
      exact (by decide +kernel : ¬ (2 : ℕ).testBit 0 = true) hbit
    rw [hparent, hval]
    decide +kernel
  · rintro rfl
    refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · rw [hmask]
      change (2 : ℕ).testBit 1 = true
      decide +kernel
    · rw [hparent]
      change advance (32 : Fin 51) 2 = (34 : Fin 51)
      decide +kernel

/-- Classify only subsets of the actual singleton RS mask. No powerset of
Fin 51, unrelated masks, positive full-word control, or sampling is used. -/
private theorem k51_unique (K : Finset (Fin 51))
    (hK : K ⊆ bitsRS t51 x51) (hrobust : modulus 51 ≤ 8 * charge t51 K) :
    K = {(34 : Fin 51)} := by
  have hsub : K ⊆ {(34 : Fin 51)} := by simpa only [k51_bits] using hK
  have hmem : (34 : Fin 51) ∈ K := by
    by_contra hnot
    have hempty : K = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have he : i = (34 : Fin 51) := Finset.mem_singleton.mp (hsub hi)
      subst i
      exact hnot hi
    rw [hempty] at hrobust
    have hfalse : ¬ modulus 51 ≤ 8 * charge t51 (∅ : Finset (Fin 51)) := by source_decide
    exact hfalse hrobust
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)

/-- The actual modular source contradicts the universal robust selector. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨K, hK, hrobust, hlanding⟩ :=
    h 10 51 t51 4 a51 b51 p51 d51 x51 k51_original k51_corner
      (by source_decide) (by source_decide) (by source_decide) (by source_decide) (by source_decide)
      2 (by source_decide) (by source_decide) (by
        intro j
        fin_cases j <;> source_decide)
  have hsingleton := k51_unique K hK hrobust
  rw [hsingleton] at hlanding
  have hheight : compressedHeight t51 x51 2 {(34 : Fin 51)} = 158743074097132 := by source_decide
  have hT : endpointSeed t51 x51 2 = 218836125383029 := by source_decide
  rw [hheight, hT] at hlanding
  have hfailure : ¬ (158743074097132 : ℤ) % 218836125383029 ≤
      (218836125383029 - 1) / 2 := by source_decide
  exact hfailure hlanding

end D5.S3.Combinatorics.Circle.RobustSelectorRefutation
