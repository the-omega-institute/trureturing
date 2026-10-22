/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedPrimeCellBounds
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedPrimeCellBounds
   mirror-E: none(waiver:complex-Ioc-weighted-translation)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80; instance=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80
   digest: Variable row and closed-cell certificate soundness, with the original 141-cell input. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalSignedPrimeFourier

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix
open OriginalSignedCompressedFourier
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition (primeWeight)
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining (primeSymmetric)

namespace Prime80

structure Row where
  q : Nat
  p : Nat
  k : Nat
  a : Nat
  b : Nat
  deriving DecidableEq

structure Cell where
  ln : Nat
  ld : Nat
  rn : Nat
  rd : Nat
  deriving DecidableEq


private def Cell.lower (c : Cell) : ℝ := c.ln / c.ld
private def Cell.upper (c : Cell) : ℝ := c.rn / c.rd

-- Structural sums avoid a separate unproved foldl/«prefix» identification.
private def «prefix» (ts : List Row) (accept : Row → Bool) (select : Row → ℕ) : ℕ :=
  match ts with
  | [] => 0
  | t :: rest => (if accept t then select t else 0) + «prefix» rest accept select

private def plusAccept (c : Cell) (t : Row) : Bool :=
  decide (t.q * c.ln ≤ 71 * c.ld)

private def minusAccept (c : Cell) (t : Row) : Bool :=
  decide (t.q * c.rd ≤ 71 * c.rn)

private def Cell.valid (c : Cell) (ts : List Row) : Prop :=
  let ap := «prefix» ts (plusAccept c) Row.a
  let bp := «prefix» ts (plusAccept c) Row.b
  let am := «prefix» ts (minusAccept c) Row.a
  let bm := «prefix» ts (minusAccept c) Row.b
  0 < c.ln ∧ 0 < c.ld ∧ 0 < c.rn ∧ 0 < c.rd ∧
    c.ln * c.rd ≤ c.rn * c.ld ∧
    (c.rn * bp + c.rd * ap) * (c.ln + c.ld) +
      (c.ln * am + c.ld * bm) * (c.rn + c.rd) <
      80 * 1000000 * (c.rn + c.rd) * (c.ln + c.ld)

private instance validDecidable (ts : List Row) (c : Cell) : Decidable (c.valid ts) := by
  unfold Cell.valid
  infer_instance

-- A nonempty closed chain is essential: an empty chain must not certify
-- the lone last endpoint. This recursion checks the exact endpoints too.
private def chain : ℕ → ℕ → List Cell → Prop
  | _, _, [] => False
  | n, d, c :: rest =>
      c.ln * d = n * c.ld ∧
        match rest with
        | [] => c.rn = 71 * c.rd
        | e :: es => chain c.rn c.rd (e :: es)

private instance chainDecidable (n d : ℕ) (cs : List Cell) : Decidable (chain n d cs) :=
  match cs with
  | [] => inferInstanceAs (Decidable False)
  | c :: [] => inferInstanceAs (Decidable (c.ln * d = n * c.ld ∧ c.rn = 71 * c.rd))
  | c :: e :: es =>
      letI := chainDecidable c.rn c.rd (e :: es)
      inferInstanceAs (Decidable (c.ln * d = n * c.ld ∧ chain c.rn c.rd (e :: es)))

/-- Exact rational premises for a variable row table and a variable closed chain.
The endpoint tests remain weak. The checker never samples a real argument. -/
structure CellCertificate (ts : List Row) (cs : List Cell) : Prop where
  valid : ∀ c ∈ cs, c.valid ts
  connected : chain 1 1 cs

variable {ts : List Row} {cs : List Cell}

private lemma lower_pos {c : Cell} (hc : c.valid ts) : 0 < c.lower := by
  exact div_pos (by exact_mod_cast hc.1) (by exact_mod_cast hc.2.1)

private lemma upper_pos {c : Cell} (hc : c.valid ts) : 0 < c.upper := by
  exact div_pos (by exact_mod_cast hc.2.2.1) (by exact_mod_cast hc.2.2.2.1)

private lemma lower_eq_of_cross {c : Cell} {n d : ℕ}
    (hc : c.valid ts) (hd : 0 < d) (he : c.ln * d = n * c.ld) :
    c.lower = (n : ℝ) / d := by
  apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hc.2.1) : (c.ld : ℝ) ≠ 0)
    (by exact_mod_cast (Nat.ne_of_gt hd) : (d : ℝ) ≠ 0)).mpr
  exact_mod_cast he

private lemma upper_eq_71 {c : Cell} (hc : c.valid ts) (he : c.rn = 71 * c.rd) :
    c.upper = 71 := by
  apply (div_eq_iff (by exact_mod_cast (Nat.ne_of_gt hc.2.2.2.1) : (c.rd : ℝ) ≠ 0)).mpr
  exact_mod_cast he

private theorem chain_covers (cs : List Cell) :
    ∀ n d : ℕ, 0 < d → (∀ c ∈ cs, c.valid ts) → chain n d cs →
      ∀ r : ℝ, (n : ℝ) / d ≤ r → r ≤ 71 →
        ∃ c ∈ cs, c.lower ≤ r ∧ r ≤ c.upper := by
  induction cs with
  | nil => intro n d hd hv hc; exact False.elim hc
  | cons c cs ih =>
      intro n d hd hv hc r hl hr
      have hcv : c.valid ts := hv c (by simp)
      have hstart : c.ln * d = n * c.ld := by
        cases cs with
        | nil => exact hc.1
        | cons e es => exact hc.1
      have he : c.lower = (n : ℝ) / d := lower_eq_of_cross hcv hd hstart
      by_cases hru : r ≤ c.upper
      · exact ⟨c, by simp, by simpa only [he] using hl, hru⟩
      · cases cs with
        | nil =>
            have hu : c.upper = 71 := upper_eq_71 hcv hc.2
            exact False.elim (hru (by simpa only [hu] using hr))
        | cons e es =>
            obtain ⟨t, ht, htl, htr⟩ := ih c.rn c.rd hcv.2.2.2.1
              (fun t ht => hv t (List.mem_cons_of_mem c ht)) hc.2 r
              (le_of_lt (lt_of_not_ge hru)) hr
            exact ⟨t, List.mem_cons_of_mem c ht, htl, htr⟩

private theorem complete_closed_coverage (cert : CellCertificate ts cs)
    {r : ℝ} (hl : 1 ≤ r) (hr : r ≤ 71) :
    ∃ c ∈ cs, c.lower ≤ r ∧ r ≤ c.upper := by
  exact chain_covers cs 1 1 (by decide) cert.valid cert.connected r
    (by simpa using hl) hr

def plus (t : Row) (r : ℝ) : ℝ :=
  (r * t.b + t.a) / (1000000 * (r + 1))

def minus (t : Row) (r : ℝ) : ℝ :=
  (r * t.a + t.b) / (1000000 * (r + 1))

lemma plus_nonneg (t : Row) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ plus t r := by
  unfold plus
  positivity

lemma minus_nonneg (t : Row) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ minus t r := by
  unfold minus
  positivity

private lemma plus_mono (t : Row) (hab : t.a ≤ t.b) {r u : ℝ}
    (hr : 0 ≤ r) (hru : r ≤ u) : plus t r ≤ plus t u := by
  have hu : 0 ≤ u := hr.trans hru
  have hab' : (t.a : ℝ) ≤ t.b := by exact_mod_cast hab
  have hcross : 0 ≤ ((t.b : ℝ) - t.a) * (u - r) :=
    mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hru)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * (r + 1))
    (by positivity : (0 : ℝ) < 1000000 * (u + 1))).mpr
  nlinarith

private lemma minus_anti (t : Row) (hab : t.a ≤ t.b) {l r : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) : minus t r ≤ minus t l := by
  have hr : 0 ≤ r := hl.trans hlr
  have hab' : (t.a : ℝ) ≤ t.b := by exact_mod_cast hab
  have hcross : 0 ≤ ((t.b : ℝ) - t.a) * (r - l) :=
    mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hlr)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * (r + 1))
    (by positivity : (0 : ℝ) < 1000000 * (l + 1))).mpr
  nlinarith

-- Exact casts of the weak integer tests. Equality belongs to BOTH tests.
private lemma plus_accept_iff (c : Cell) (t : Row) (hc : c.valid ts) :
    plusAccept c t = true ↔ (t.q : ℝ) * c.lower ≤ 71 := by
  simp only [plusAccept, decide_eq_true_eq, Cell.lower, ← mul_div_assoc]
  rw [div_le_iff₀ (by exact_mod_cast hc.2.1 : (0 : ℝ) < c.ld)]
  constructor <;> intro h <;> exact_mod_cast h

private lemma minus_accept_iff (c : Cell) (t : Row) (hc : c.valid ts) :
    minusAccept c t = true ↔ (t.q : ℝ) ≤ 71 * c.upper := by
  simp only [minusAccept, decide_eq_true_eq, Cell.upper, ← mul_div_assoc]
  rw [le_div_iff₀ (by exact_mod_cast hc.2.2.2.1 : (0 : ℝ) < c.rd)]
  constructor <;> intro h <;> exact_mod_cast h

def rowTerm (t : Row) (r : ℝ) : ℝ :=
  (if (t.q : ℝ) * r ≤ 71 then plus t r else 0) +
    (if (t.q : ℝ) ≤ 71 * r then minus t r else 0)

private def cellTerm (c : Cell) (t : Row) : ℝ :=
  (if plusAccept c t then plus t c.upper else 0) +
    (if minusAccept c t then minus t c.lower else 0)

private lemma rowTerm_le_cellTerm (c : Cell) (hc : c.valid ts) (t : Row)
    (hab : t.a ≤ t.b) {r : ℝ} (hlr : c.lower ≤ r) (hru : r ≤ c.upper) :
    rowTerm t r ≤ cellTerm c t := by
  have hl := (lower_pos hc).le
  have hr := hl.trans hlr
  have hu := (upper_pos hc).le
  apply add_le_add
  · by_cases hp : (t.q : ℝ) * r ≤ 71
    · have hp' : plusAccept c t = true := (plus_accept_iff c t hc).mpr
        ((mul_le_mul_of_nonneg_left hlr (Nat.cast_nonneg _)).trans hp)
      simpa [hp, hp'] using plus_mono t hab hr hru
    · simp only [if_neg hp]
      split_ifs <;> first | exact plus_nonneg t hu | exact le_rfl
  · by_cases hm : (t.q : ℝ) ≤ 71 * r
    · have hm' : minusAccept c t = true := (minus_accept_iff c t hc).mpr
        (hm.trans (mul_le_mul_of_nonneg_left hru (by norm_num)))
      simpa [hm, hm'] using minus_anti t hab hl hlr
    · simp only [if_neg hm]
      split_ifs <;> first | exact minus_nonneg t hl | exact le_rfl
def roundedRow (ts : List Row) (r : ℝ) : ℝ := (ts.map (fun t => rowTerm t r)).sum
private def cellBound (ts : List Row) (c : Cell) : ℝ := (ts.map (cellTerm c)).sum

private lemma rounded_le_cell (hab : ∀ t ∈ ts, t.a ≤ t.b) (c : Cell) (hc : c.valid ts) {r : ℝ}
    (hlr : c.lower ≤ r) (hru : r ≤ c.upper) : roundedRow ts r ≤ cellBound ts c := by
  unfold roundedRow cellBound
  apply List.sum_le_sum
  intro t ht
  exact rowTerm_le_cellTerm c hc t (hab t ht) hlr hru

private lemma prefix_plus (ts : List Row) (accept : Row → Bool) (u : ℝ) :
    (ts.map (fun t => if accept t then plus t u else 0)).sum =
      (u * («prefix» ts accept Row.b : ℝ) + («prefix» ts accept Row.a : ℝ)) /
        (1000000 * (u + 1)) := by
  induction ts with
  | nil => simp [«prefix»]
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons, ih]
      cases ht : accept t <;> simp [«prefix», ht, plus] <;> ring

private lemma prefix_minus (ts : List Row) (accept : Row → Bool) (l : ℝ) :
    (ts.map (fun t => if accept t then minus t l else 0)).sum =
      (l * («prefix» ts accept Row.a : ℝ) + («prefix» ts accept Row.b : ℝ)) /
        (1000000 * (l + 1)) := by
  induction ts with
  | nil => simp [«prefix»]
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons, ih]
      cases ht : accept t <;> simp [«prefix», ht, minus] <;> ring

private lemma cellBound_formula (ts : List Row) (c : Cell) :
    cellBound ts c =
      (c.upper * («prefix» ts (plusAccept c) Row.b : ℝ) +
        («prefix» ts (plusAccept c) Row.a : ℝ)) / (1000000 * (c.upper + 1)) +
      (c.lower * («prefix» ts (minusAccept c) Row.a : ℝ) +
        («prefix» ts (minusAccept c) Row.b : ℝ)) / (1000000 * (c.lower + 1)) := by
  unfold cellBound cellTerm
  rw [List.sum_map_add, prefix_plus, prefix_minus]

private lemma cellBound_lt (c : Cell) (hc : c.valid ts) : cellBound ts c < 80 := by
  let ap := «prefix» ts (plusAccept c) Row.a
  let bp := «prefix» ts (plusAccept c) Row.b
  let am := «prefix» ts (minusAccept c) Row.a
  let bm := «prefix» ts (minusAccept c) Row.b
  have hld : (0 : ℝ) < c.ld := by exact_mod_cast hc.2.1
  have hrd : (0 : ℝ) < c.rd := by exact_mod_cast hc.2.2.2.1
  have hl : (0 : ℝ) < c.ln + c.ld := by positivity
  have hu : (0 : ℝ) < c.rn + c.rd := by positivity
  have hi : ((c.rn : ℝ) * bp + c.rd * ap) * (c.ln + c.ld) +
      ((c.ln : ℝ) * am + c.ld * bm) * (c.rn + c.rd) <
      80 * 1000000 * (c.rn + c.rd) * (c.ln + c.ld) := by
    exact_mod_cast hc.2.2.2.2.2
  have he : cellBound ts c =
      (((c.rn : ℝ) * bp + c.rd * ap) * (c.ln + c.ld) +
        ((c.ln : ℝ) * am + c.ld * bm) * (c.rn + c.rd)) /
        (1000000 * (c.rn + c.rd) * (c.ln + c.ld)) := by
    rw [cellBound_formula ts]
    dsimp [Cell.lower, Cell.upper, ap, bp, am, bm]
    field_simp [hld.ne', hrd.ne', hl.ne', hu.ne']
    <;> ring
  rw [he]
  apply (div_lt_iff₀ (by positivity :
    (0 : ℝ) < 1000000 * (c.rn + c.rd) * (c.ln + c.ld))).mpr
  nlinarith [hi]

/-- Soundness of the closed-cell checker for arbitrary data, not a theorem
about one finite catalogue. Every r in the closed interval is covered. -/
theorem roundedRow_lt_eighty (hab : ∀ t ∈ ts, t.a ≤ t.b)
    (cert : CellCertificate ts cs) {r : ℝ} (hl : 1 ≤ r) (hr : r ≤ 71) :
    roundedRow ts r < 80 := by
  obtain ⟨c, hc, hcl, hcr⟩ := complete_closed_coverage cert hl hr
  exact (rounded_le_cell hab c (cert.valid c hc) hcl hcr).trans_lt
    (cellBound_lt c (cert.valid c hc))

end Prime80
end OriginalSignedPrimeFourier
