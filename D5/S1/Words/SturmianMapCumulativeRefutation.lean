/- GID: D5/S1/Words/SturmianMapCumulativeRefutation
   generality: I
   mirror-B: D5/B/S1/Words/SturmianMapCumulativeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/SturmianMapCumulativeRefutation.claim; result=D5/S1/Words/SturmianMapCumulativeRefutation.result; claim=D5/S1/Words/SturmianMapCumulativeRefutation.claim
   digest: Refute the cumulative Sturmian bound at slope two minus square root three. -/

/-
result:
  proof_shape: bind-only (normalization using the frozen open_rotation_run and Mathlib)
  escape_witness: none
  admission_basis: open-problem-resolution (#17837; Refuted)
Direct frozen dependencies (declaration statement_id):
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWord
    sha256:be5fa4666babf428155ad5feb38b257b05db284008cb9bcc1a940ee830c1098d
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter
    sha256:2f3fffa2e006abb3c4b960a36d958d5450218bc2fd89384af0710e73ea02b7e8
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWord_eq_true_iff
    sha256:60afbb7bc690b4581d9aad2e3f5fadb5cdaae01186c9cfa2a38efd0ba31122e0
  D5/S1/Words/Mechanical/FloorFractShift.floor_add_sub_floor
    sha256:7a4f8559ae3b5ca28625632937d3e0502fb7b528c492ed6eb8a6e0c0706ef317
  D5/S1/Words/FibonacciMapFirstStart.open_rotation_run
    sha256:c687b513d5c0cfa8f4f3a51c7c55deb7e19241fc324864308797935a1fd811dc
  D5/S1/Words/Mechanical/IrrationalFractNonvanishing.irrational_natCast_mul_fract_ne_zero
    sha256:e594cfe7ce9f0e32db43cb2bafb1c43c53d764623fbd50adbdbb00c55a581efd
Generated equation from the same frozen owner (include_in_statement: false):
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter.eq_1
    sha256:a5c0289779aeb09bd84605b9fe9496baee2c723692aae841c1a0ae021c405f07
mapLength and claim retain the expressions in issue #17837; the word is the existing
lowerMechanicalWord, related to the source coding by the private sturmian_letter_iff.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Escape audit unfinished for FibonacciMapFirstStart.open_rotation_run:
https://github.com/the-omega-institute/trureturing/issues/19343.
Private declarations (escape_witness: none for each):
  sturmian_letter_iff: bind-only; consumers five_letters, mapLength_three_le_four.
  sqrt_bounds: bind-only; consumers slope_range, five_letters,
    mapLength_three_le_four.
  slope_range: bind-only; consumers denominator_one, five_letters,
    mapLength_three_le_four, result.
  slope_irrational: bind-only; consumers mapLength_three_le_four, result.
  slope_inverse: bind-only; consumer denominator_one.
  denominator_one: bind-only; consumer result.
  five_letters: bind-only; consumer mapLength_two_ge_five.
  mapLength_two_ge_five: bind-only; consumer result.
  mapLength_three_le_four: bind-only; consumer result.
Literature completeness: ASSUMED-UNVERIFIED; no prior settlement was located in the
partial screen recorded in issue #17837. Exact maxima and interval families are not asserted.
-/

import D5.S1.Words.Mechanical.FloorFractShift
import D5.S1.Words.Mechanical.IrrationalFractNonvanishing
import D5.S1.Words.FibonacciMapFirstStart

set_option autoImplicit false

namespace D5.S1.Words.SturmianMapCumulativeRefutation

open D5.S1.Words.Mechanical
open D5.S1.Words.FibonacciMapFirstStart

/-- The longest length `A(d)` of a monochromatic arithmetic progression of difference `d` in the
Sturmian sequence of slope `α` (Joshi, Definitions 2.2.3, 2.6.1 and 2.6.2): the supremum in `ℕ∞`
of the lengths `ℓ ≥ 1` for which some start `i` and letter `a` satisfy `s (i + k * d) = a` for
every `k < ℓ` (an infinite progression gives `⊤`). The Sturmian sequence of Definition 2.2.3 is
the frozen lower mechanical word with slope and intercept `α`; `true` is the letter `b`. -/
noncomputable def mapLength (α : ℝ) (d : ℕ) : ℕ∞ :=
  ⨆ (i : ℕ) (a : Bool) (ℓ : ℕ) (_ : 0 < ℓ ∧ ∀ k < ℓ, lowerMechanicalWord α α (i + k * d) = a),
    (ℓ : ℕ∞)

/-- Joshi's thesis (Open University 2025), Section 6.1, "Stronger cumulative bound on A(d)": for
every Sturmian slope `0 < α < 1/2` and every `n ≥ 1`, every difference `1 ≤ d ≤ q_n` has
`A(d) ≤ A(q_n)`, where `q_n` is the denominator of the `n`-th convergent of `α`. -/
def claim : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 / 2 →
    ∀ n : ℕ, 1 ≤ n → ∀ q : ℕ, (q : ℝ) = (GenContFract.of α).dens n →
      ∀ d : ℕ, 1 ≤ d → d ≤ q → mapLength α d ≤ mapLength α q

/-- Definition 2.2.3: `s n = b` exactly when `⟨(n+1)α⟩ ∈ [1 - α, 1)`. -/
private theorem sturmian_letter_iff {α : ℝ} (h1 : α < 1) (n : ℕ) :
    lowerMechanicalWord α α n = true ↔ 1 - α ≤ Int.fract (((n : ℝ) + 1) * α) := by
  rw [lowerMechanicalWord_eq_true_iff, lowerMechanicalLetter]
  set x : ℝ := ((n : ℝ) + 1) * α with hx
  have e1 : α + ((n + 1 : ℕ) : ℝ) * α = x + α := by rw [hx]; push_cast; ring
  have e2 : α + (n : ℝ) * α = x := by rw [hx]; ring
  rw [e1, e2]
  have key : ⌊x + α⌋ = ⌊x⌋ + ⌊Int.fract x + α⌋ := by
    exact (sub_eq_iff_eq_add').mp (FloorFractShift.floor_add_sub_floor x α)
  rw [key]
  have f0 := Int.fract_nonneg x
  have f1 := Int.fract_lt_one x
  constructor
  · intro h
    have h' : ⌊Int.fract x + α⌋ = 1 := by omega
    have := (Int.floor_eq_iff.mp h').1
    push_cast at this
    linarith
  · intro h
    have h' : ⌊Int.fract x + α⌋ = 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    omega

private theorem sqrt_bounds : (1732 / 1000 : ℝ) < Real.sqrt 3 ∧
    Real.sqrt 3 < 17321 / 10000 := by
  constructor
  · exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

private theorem slope_range : 0 < (2 - Real.sqrt 3 : ℝ) ∧
    (2 - Real.sqrt 3 : ℝ) < 1 / 2 := by
  constructor <;> linarith [sqrt_bounds.1, sqrt_bounds.2]

private theorem slope_irrational : Irrational (2 - Real.sqrt 3) := by
  have h : Irrational (Real.sqrt (3 : ℕ)) :=
    (show Nat.Prime 3 by norm_num).irrational_sqrt
  exact h.natCast_sub 2

private theorem slope_inverse : (2 - Real.sqrt 3)⁻¹ = 2 + Real.sqrt 3 := by
  have h := Real.add_sqrt_self_sq_sub_one_inv (x := 2) (by norm_num)
  norm_num at h
  rw [← h, inv_inv]

private theorem denominator_one : (GenContFract.of (2 - Real.sqrt 3)).dens 1 = 3 := by
  have hf : Int.fract (2 - Real.sqrt 3) = 2 - Real.sqrt 3 :=
    Int.fract_eq_self.mpr ⟨slope_range.1.le, by linarith [slope_range.2]⟩
  have hn : Int.fract (2 - Real.sqrt 3) ≠ 0 := by rw [hf]; exact ne_of_gt slope_range.1
  have hfloor : ⌊(2 : ℝ) + Real.sqrt 3⌋ = 3 := by
    have h : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by
      convert (Real.floor_real_sqrt_eq_nat_sqrt (a := 3)) using 1 <;> norm_num
    rw [Int.floor_ofNat_add, h]
    norm_num
  rw [GenContFract.first_den_eq (GenContFract.of_s_head hn), hf, slope_inverse, hfloor]
  norm_num

private theorem five_letters : ∀ k < 5,
    lowerMechanicalWord (2 - Real.sqrt 3) (2 - Real.sqrt 3) (1 + k * 2) = false := by
  intro k hk
  apply Bool.eq_false_iff.mpr
  intro hb
  have ht := (sturmian_letter_iff (α := 2 - Real.sqrt 3)
    (by linarith [slope_range.2]) (1 + k * 2)).mp hb
  suffices hs : Int.fract (((1 + k * 2 : ℕ) + 1 : ℝ) * (2 - Real.sqrt 3)) <
      1 - (2 - Real.sqrt 3) by linarith
  have hfrac (x : ℝ) (z : ℤ) (hlo : (z : ℝ) ≤ x) (hhi : x < (z : ℝ) + 1)
      (hsmall : x - (z : ℝ) < 1 - (2 - Real.sqrt 3)) :
      Int.fract x < 1 - (2 - Real.sqrt 3) := by
    rw [Int.fract, Int.floor_eq_iff.mpr ⟨hlo, hhi⟩]
    exact hsmall
  interval_cases k
  · apply hfrac _ 0 <;> norm_num <;> linarith [sqrt_bounds.1, sqrt_bounds.2]
  · apply hfrac _ 1 <;> norm_num <;> linarith [sqrt_bounds.1, sqrt_bounds.2]
  · apply hfrac _ 1 <;> norm_num <;> linarith [sqrt_bounds.1, sqrt_bounds.2]
  · apply hfrac _ 2 <;> norm_num <;> linarith [sqrt_bounds.1, sqrt_bounds.2]
  · apply hfrac _ 2 <;> norm_num <;> linarith [sqrt_bounds.1, sqrt_bounds.2]

private theorem mapLength_two_ge_five : (5 : ℕ∞) ≤ mapLength (2 - Real.sqrt 3) 2 := by
  exact le_iSup_of_le 1 (le_iSup_of_le false
    (le_iSup_of_le 5 (le_iSup_of_le ⟨by norm_num, five_letters⟩ le_rfl)))

private theorem mapLength_three_le_four : mapLength (2 - Real.sqrt 3) 3 ≤ 4 := by
  let α : ℝ := 2 - Real.sqrt 3
  let g : ℝ := 3 * Real.sqrt 3 - 5
  have ha0 : 0 < α := slope_range.1
  have ha1 : α < 1 / 2 := slope_range.2
  have hg0 : 0 < g := by dsimp [g]; linarith [sqrt_bounds.1]
  have hga : g < α := by dsimp [g, α]; linarith [sqrt_bounds.2]
  have hg4 : 1 - α < 4 * g := by dsimp [g, α]; linarith [sqrt_bounds.1]
  have hg2 : α < 2 * g := by dsimp [g, α]; linarith [sqrt_bounds.1]
  unfold mapLength
  refine iSup_le fun i => iSup_le fun a => iSup_le fun ℓ => iSup_le fun h => ?_
  suffices hlen : ℓ ≤ 4 by exact_mod_cast hlen
  by_contra hlen
  have hl : 5 ≤ ℓ := Nat.lt_of_not_ge hlen
  let y : ℕ → ℝ := fun k => Int.fract ((((i + k * 3 : ℕ) : ℝ) + 1) * α)
  have yn (k : ℕ) : 0 ≤ y k := Int.fract_nonneg _
  have yu (k : ℕ) : y k < 1 := Int.fract_lt_one _
  have hstep (k : ℕ) : y (k + 1) = Int.fract (y k - g) := by
    dsimp [y]
    rw [Int.fract_fract_sub]
    have he : ((((i + (k + 1) * 3 : ℕ) : ℝ) + 1) * α) =
        ((((i + k * 3 : ℕ) : ℝ) + 1) * α - g) + 1 := by
      dsimp [α, g]
      push_cast
      ring
    rw [he, Int.fract_add_one]
  have ypos (k : ℕ) : 0 < y k := by
    have hne : y k ≠ 0 := by
      simpa only [y, Nat.cast_add, Nat.cast_one] using
        IrrationalFractNonvanishing.irrational_natCast_mul_fract_ne_zero
          slope_irrational (by omega : i + k * 3 + 1 ≠ 0)
    exact lt_of_le_of_ne (yn k) hne.symm
  have yboundary (k : ℕ) : y k ≠ 1 - α := by
    intro heq
    have hz : (((i + k * 3 + 2 : ℕ) : ℝ) * α) =
        ((⌊(((i + k * 3 : ℕ) : ℝ) + 1) * α⌋ + 1 : ℤ) : ℝ) := by
      dsimp [y] at heq
      rw [Int.fract] at heq
      push_cast at heq ⊢
      nlinarith only [heq]
    exact (slope_irrational.natCast_mul (by omega : i + k * 3 + 2 ≠ 0)).ne_int _ hz
  cases a with
  | false =>
    have hm (k : ℕ) (hk : k < 5) : 0 < y k ∧ y k < 1 - α := by
      refine ⟨ypos k, ?_⟩
      have hf := h.2 k (by omega)
      have hn : ¬ lowerMechanicalWord α α (i + k * 3) = true := Bool.eq_false_iff.mp hf
      exact lt_of_not_ge ((sturmian_letter_iff (by linarith : α < 1) (i + k * 3)).not.mp hn)
    have run := open_rotation_run (lo := 0) (hi := 1 - α) (eps := g)
      (x := y) (length := 5) false hg0 (le_refl 0) (by linarith)
      (by linarith) (by norm_num) hm (fun k _ => by simpa [sub_eq_add_neg] using hstep k)
    norm_num at run
    linarith only [run.2, hg4]
  | true =>
    have hm (k : ℕ) (hk : k < 5) : 1 - α < y k ∧ y k < 1 := by
      refine ⟨?_, yu k⟩
      have hb := (sturmian_letter_iff (by linarith : α < 1) (i + k * 3)).mp (h.2 k (by omega))
      exact lt_of_le_of_ne hb (yboundary k).symm
    have run := open_rotation_run (lo := 1 - α) (hi := 1) (eps := g)
      (x := y) (length := 3) false hg0 (by linarith) (le_refl 1)
      (by linarith) (by norm_num) (fun k hk => hm k (by omega))
      (fun k _ => by simpa [sub_eq_add_neg] using hstep k)
    norm_num at run
    linarith only [run.2, hg2]

theorem result : ¬ claim := by
  intro hc
  have hbound := hc (2 - Real.sqrt 3) slope_irrational slope_range.1 slope_range.2
    1 (by norm_num) 3 (by simpa using denominator_one.symm) 2 (by norm_num) (by norm_num)
  have hbad : (5 : ℕ∞) ≤ 4 := mapLength_two_ge_five.trans (hbound.trans mapLength_three_le_four)
  norm_num at hbad

end D5.S1.Words.SturmianMapCumulativeRefutation
