/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   digest: Barker's generating function for the literal normalized six-column strip. -/
/-
admission_basis: open-problem-resolution (#28319; Proved)
escape_witness: none
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Basic
/-! Literal six-column arrays and a four-dimensional symbolic continuation transfer. -/
set_option maxRecDepth 100000
set_option Elab.async false
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
open HardinA233175PairStrip (Seen allowed advance good finish finish_fst finish_snd good_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip
abbrev Row := Fin 6 → Fin 6
abbrev Boundary := Fin 5 → Fin 3
def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 5, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5
private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 5, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5
private def Legal {n : ℕ} (A : Fin n × Fin 6 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), bonds (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    widthNormal (false, false) (fun i j => A (i, j))
private instance instDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → Row) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))
private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 6 → Fin 6) :
    Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
/-- The literal filtered count. The first-cell existential sets `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 6 → Fin 6 => Legal A)).card
def pairs (c : Row) : Boundary := fun j => beta (c j.succ)
def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 5, p j ≠ beta (c j.castSucc)
private instance instDecidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))
private instance instDecidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance
private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, HardinA233251TriangleStrip.colour_bond_iff, compatible, pairs]
private abbrev v := widthV rowLegal pairs compatible
private abbrev total := widthTotal rowLegal pairs
private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n
/-- Adjacent boundary labels differ; absent colour two excludes its whole pair. -/
def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 4, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)
private instance instDecidableValid (s : Seen) (p : Boundary) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))
/-- The eight equality shapes of a proper five-label boundary. -/
def shape (p : Boundary) : Fin 8 :=
  if p 2 = p 0 then
    if p 3 = p 1 then (if p 4 = p 0 then 0 else 1)
    else (if p 4 = p 0 then 2 else 3)
  else if p 3 = p 0 then (if p 4 = p 1 then 4 else 5)
    else (if p 4 = p 0 then 6 else 7)
/-- The constant and first three label-transfer moments. -/
def moment (p : Boundary) : Fin 4 → ℤ :=
  ![1, ![26, 22, 24, 18, 12, 18, 20, 22] (shape p),
    ![564, 456, 516, 354, 222, 366, 426, 462] (shape p),
    ![11832, 9510, 10812, 7320, 4542, 7620, 8922, 9660] (shape p)]
private theorem valid_next (s : Seen) (c : Row) (hs : s.1 = true ∨ ∃ i, c i = 1)
    (hc : rowLegal c ∧ good s c) : Valid (finish s c) (pairs c) := by
  refine ⟨(finish_fst s c).mpr hs, ?_, ?_⟩
  · intro j
    have h := HardinA233251TriangleStrip.colour_bond_iff _ _ |>.mp (hc.1 j.succ)
    exact h
  · intro ht j
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((good_iff s c).mp hc.2 i).2 hi with hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    intro hp
    rcases (hb _).mp hp with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh
/-- Count continuations by the second final flag. -/
def classCount (s : Seen) (p : Boundary) (b : Bool) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = b then 1 else 0
/-- Sum one boundary moment over fully seen continuations. -/
def momentCount (s : Seen) (p : Boundary) (i : Fin 4) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = true then moment (pairs c) i else 0
/-- Count first rows by the second final flag. -/
def firstCount (b : Bool) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = b then 1 else 0
/-- Sum a boundary moment over fully seen first rows. -/
def firstMoment (i : Fin 4) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = true then moment (pairs c) i else 0

private theorem sum_rows {m : ℕ} (f : (Fin 6 → Fin m) → ℤ) : (∑ c, f c) =
    ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, ∑ e : Fin m,
      ∑ g : Fin m, f ![a, b, c, d, e, g] := by
  simp_rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin m)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 5 => Fin m)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin m)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin m)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin m)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin m)).sum_comp,
    Fintype.sum_prod_type]
  simp [Fin.consEquiv, Matrix.empty_eq]

private theorem sum_beta (f : Fin 3 → ℤ) :
    (∑ x : Fin 6, f (beta x)) = 2 * ∑ y : Fin 3, f y := by
  simp [Fin.sum_univ_succ, beta]
  ring

private theorem sum_beta_rows (n : ℕ) (f : (Fin n → Fin 3) → ℤ) :
    (∑ c : Fin n → Fin 6, f (fun j => beta (c j))) =
      2 ^ n * ∑ b : Fin n → Fin 3, f b := by
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, pow_zero, one_mul]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ n ih =>
    have hc (x : Fin 6) (c : Fin n → Fin 6) :
        (fun j => beta ((Fin.cons x c : Fin (n + 1) → Fin 6) j)) =
          Fin.cons (beta x) (fun j => beta (c j)) := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6)).sum_comp,
      Fintype.sum_prod_type,
      ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, hc]
    simp_rw [ih]
    rw [← Finset.mul_sum, sum_beta, pow_succ]
    ring

private def labelCount (p : Boundary) (i : Fin 4) : ℤ :=
  ∑ c : Fin 6 → Fin 3,
    if (∀ j : Fin 5, c j.castSucc ≠ c j.succ) ∧
        (∀ j : Fin 5, p j ≠ c j.castSucc)
    then moment (fun j => c j.succ) i else 0

private theorem full_flags (c : Row) :
    good (true, true) c ∧ (finish (true, true) c).2 = true := by
  constructor
  · rw [good_iff]
    intro i
    exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  · exact (finish_snd _ _).mpr (Or.inl rfl)

private theorem full_moments (p : Boundary) (i : Fin 4) :
    momentCount (true, true) p i = 64 * labelCount p i := by
  simp only [momentCount, (full_flags _).1, (full_flags _).2, and_true]
  simp only [rowLegal, colour_bond_iff, compatible, pairs]
  exact sum_beta_rows 6 (fun c =>
    if (∀ j : Fin 5, c j.castSucc ≠ c j.succ) ∧
        (∀ j : Fin 5, p j ≠ c j.castSucc)
    then moment (fun j => c j.succ) i else 0)

private theorem label_01010 (i : Fin 4) :
    labelCount ![0, 1, 0, 1, 0] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
private theorem label_01012 (i : Fin 4) :
    labelCount ![0, 1, 0, 1, 2] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_01020 (i : Fin 4) :
    labelCount ![0, 1, 0, 2, 0] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_01021 (i : Fin 4) :
    labelCount ![0, 1, 0, 2, 1] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_01201 (i : Fin 4) :
    labelCount ![0, 1, 2, 0, 1] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_01202 (i : Fin 4) :
    labelCount ![0, 1, 2, 0, 2] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_01210 (i : Fin 4) :
    labelCount ![0, 1, 2, 1, 0] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_01212 (i : Fin 4) :
    labelCount ![0, 1, 2, 1, 2] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_02010 (i : Fin 4) :
    labelCount ![0, 2, 0, 1, 0] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_02012 (i : Fin 4) :
    labelCount ![0, 2, 0, 1, 2] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_02020 (i : Fin 4) :
    labelCount ![0, 2, 0, 2, 0] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
private theorem label_02021 (i : Fin 4) :
    labelCount ![0, 2, 0, 2, 1] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_02101 (i : Fin 4) :
    labelCount ![0, 2, 1, 0, 1] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_02102 (i : Fin 4) :
    labelCount ![0, 2, 1, 0, 2] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_02120 (i : Fin 4) :
    labelCount ![0, 2, 1, 2, 0] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_02121 (i : Fin 4) :
    labelCount ![0, 2, 1, 2, 1] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_10101 (i : Fin 4) :
    labelCount ![1, 0, 1, 0, 1] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
private theorem label_10102 (i : Fin 4) :
    labelCount ![1, 0, 1, 0, 2] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_10120 (i : Fin 4) :
    labelCount ![1, 0, 1, 2, 0] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_10121 (i : Fin 4) :
    labelCount ![1, 0, 1, 2, 1] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_10201 (i : Fin 4) :
    labelCount ![1, 0, 2, 0, 1] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_10202 (i : Fin 4) :
    labelCount ![1, 0, 2, 0, 2] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_10210 (i : Fin 4) :
    labelCount ![1, 0, 2, 1, 0] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_10212 (i : Fin 4) :
    labelCount ![1, 0, 2, 1, 2] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_12010 (i : Fin 4) :
    labelCount ![1, 2, 0, 1, 0] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_12012 (i : Fin 4) :
    labelCount ![1, 2, 0, 1, 2] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_12020 (i : Fin 4) :
    labelCount ![1, 2, 0, 2, 0] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_12021 (i : Fin 4) :
    labelCount ![1, 2, 0, 2, 1] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_12101 (i : Fin 4) :
    labelCount ![1, 2, 1, 0, 1] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_12102 (i : Fin 4) :
    labelCount ![1, 2, 1, 0, 2] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_12120 (i : Fin 4) :
    labelCount ![1, 2, 1, 2, 0] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_12121 (i : Fin 4) :
    labelCount ![1, 2, 1, 2, 1] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
private theorem label_20101 (i : Fin 4) :
    labelCount ![2, 0, 1, 0, 1] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_20102 (i : Fin 4) :
    labelCount ![2, 0, 1, 0, 2] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_20120 (i : Fin 4) :
    labelCount ![2, 0, 1, 2, 0] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_20121 (i : Fin 4) :
    labelCount ![2, 0, 1, 2, 1] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_20201 (i : Fin 4) :
    labelCount ![2, 0, 2, 0, 1] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_20202 (i : Fin 4) :
    labelCount ![2, 0, 2, 0, 2] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
private theorem label_20210 (i : Fin 4) :
    labelCount ![2, 0, 2, 1, 0] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_20212 (i : Fin 4) :
    labelCount ![2, 0, 2, 1, 2] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_21010 (i : Fin 4) :
    labelCount ![2, 1, 0, 1, 0] i = ![22, 462, 9660, 201702] i := by
  fin_cases i <;> decide +kernel
private theorem label_21012 (i : Fin 4) :
    labelCount ![2, 1, 0, 1, 2] i = ![20, 426, 8922, 186330] i := by
  fin_cases i <;> decide +kernel
private theorem label_21020 (i : Fin 4) :
    labelCount ![2, 1, 0, 2, 0] i = ![18, 366, 7620, 159018] i := by
  fin_cases i <;> decide +kernel
private theorem label_21021 (i : Fin 4) :
    labelCount ![2, 1, 0, 2, 1] i = ![12, 222, 4542, 94542] i := by
  fin_cases i <;> decide +kernel
private theorem label_21201 (i : Fin 4) :
    labelCount ![2, 1, 2, 0, 1] i = ![18, 354, 7320, 152598] i := by
  fin_cases i <;> decide +kernel
private theorem label_21202 (i : Fin 4) :
    labelCount ![2, 1, 2, 0, 2] i = ![24, 516, 10812, 225804] i := by
  fin_cases i <;> decide +kernel
private theorem label_21210 (i : Fin 4) :
    labelCount ![2, 1, 2, 1, 0] i = ![22, 456, 9510, 198492] i := by
  fin_cases i <;> decide +kernel
private theorem label_21212 (i : Fin 4) :
    labelCount ![2, 1, 2, 1, 2] i = ![26, 564, 11832, 247146] i := by
  fin_cases i <;> decide +kernel
section
attribute [local irreducible] labelCount
set_option maxHeartbeats 2000000 in
private theorem label_counts (p : Boundary)
    (hp : ∀ j : Fin 4, p j.castSucc ≠ p j.succ) (i : Fin 4) :
    labelCount p i = ![moment p 1, moment p 2, moment p 3,
      81 * moment p 1 - 90 * moment p 2 + 25 * moment p 3] i := by
  have he : p = ![p 0, p 1, p 2, p 3, p 4] := by
    funext j
    fin_cases j <;> rfl
  rw [he] at hp ⊢
  generalize p 0 = a at hp ⊢
  generalize p 1 = b at hp ⊢
  generalize p 2 = c at hp ⊢
  generalize p 3 = d at hp ⊢
  generalize p 4 = e at hp ⊢
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> first
  | exact absurd hp (by decide +kernel)
  | exact label_01010 i
  | exact label_01012 i
  | exact label_01020 i
  | exact label_01021 i
  | exact label_01201 i
  | exact label_01202 i
  | exact label_01210 i
  | exact label_01212 i
  | exact label_02010 i
  | exact label_02012 i
  | exact label_02020 i
  | exact label_02021 i
  | exact label_02101 i
  | exact label_02102 i
  | exact label_02120 i
  | exact label_02121 i
  | exact label_10101 i
  | exact label_10102 i
  | exact label_10120 i
  | exact label_10121 i
  | exact label_10201 i
  | exact label_10202 i
  | exact label_10210 i
  | exact label_10212 i
  | exact label_12010 i
  | exact label_12012 i
  | exact label_12020 i
  | exact label_12021 i
  | exact label_12101 i
  | exact label_12102 i
  | exact label_12120 i
  | exact label_12121 i
  | exact label_20101 i
  | exact label_20102 i
  | exact label_20120 i
  | exact label_20121 i
  | exact label_20201 i
  | exact label_20202 i
  | exact label_20210 i
  | exact label_20212 i
  | exact label_21010 i
  | exact label_21012 i
  | exact label_21020 i
  | exact label_21021 i
  | exact label_21201 i
  | exact label_21202 i
  | exact label_21210 i
  | exact label_21212 i
end


private def weight (p : Boundary) : Fin 5 → ℤ :=
  ![1, 1, moment p 1, moment p 2, moment p 3]
private def allCounts (s : Seen) (p : Boundary) (i : Fin 5) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = decide (i ≠ 0) then weight (pairs c) i else 0
private def allFirst (i : Fin 5) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = decide (i ≠ 0) then weight (pairs c) i else 0
private def rowPartial (s : Seen) (p : Boundary) (x y : Fin 6) (i : Fin 5) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6, ∑ v : Fin 6,
    let c : Row := ![x, y, z, t, u, v]
    if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = decide (i ≠ 0)
    then weight (pairs c) i else 0
private def firstPartial (x y : Fin 6) (i : Fin 5) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6, ∑ v : Fin 6,
    let c : Row := ![x, y, z, t, u, v]
    if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
      (finish (false, false) c).2 = decide (i ≠ 0) then weight (pairs c) i else 0
private def unseen01010Data : Fin 5 → Fin 6 → Fin 6 → ℤ :=
  ![
    ![![0, 0, 0, 0, 0, 0],
      ![16, 0, 0, 0, 0, 16],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![16, 0, 0, 0, 0, 16],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0],
      ![72, 0, 96, 0, 0, 72],
      ![160, 0, 0, 0, 0, 160],
      ![0, 0, 0, 0, 0, 0],
      ![72, 0, 96, 0, 0, 72],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0],
      ![1568, 0, 1920, 0, 0, 1568],
      ![3552, 0, 0, 0, 0, 3552],
      ![0, 0, 0, 0, 0, 0],
      ![1568, 0, 1920, 0, 0, 1568],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0],
      ![32832, 0, 39936, 0, 0, 32832],
      ![74688, 0, 0, 0, 0, 74688],
      ![0, 0, 0, 0, 0, 0],
      ![32832, 0, 39936, 0, 0, 32832],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0],
      ![685584, 0, 833376, 0, 0, 685584],
      ![1560480, 0, 0, 0, 0, 1560480],
      ![0, 0, 0, 0, 0, 0],
      ![685584, 0, 833376, 0, 0, 685584],
      ![0, 0, 0, 0, 0, 0]]
  ]
private theorem unseen01010_partial (x y : Fin 6) (i : Fin 5) :
    rowPartial (true, false) ![0, 1, 0, 1, 0] x y i = unseen01010Data i x y := by
  fin_cases x <;> fin_cases y <;> fin_cases i <;> decide +kernel
private theorem unseen01010_counts (i : Fin 5) :
    allCounts (true, false) ![0, 1, 0, 1, 0] i = ![64, 800, 17216, 360576, 7530048] i := by
  simp only [allCounts, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![0, 1, 0, 1, 0] x y i) = _
  simp_rw [unseen01010_partial]
  fin_cases i <;> decide +kernel
private def unseen10101Data : Fin 5 → Fin 6 → Fin 6 → ℤ :=
  ![
    ![![0, 16, 0, 0, 16, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 16, 0, 0, 16, 0]],
    ![![0, 72, 96, 0, 72, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 160, 0, 0, 160, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 72, 96, 0, 72, 0]],
    ![![0, 1568, 1920, 0, 1568, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 3552, 0, 0, 3552, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 1568, 1920, 0, 1568, 0]],
    ![![0, 32832, 39936, 0, 32832, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 74688, 0, 0, 74688, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 32832, 39936, 0, 32832, 0]],
    ![![0, 685584, 833376, 0, 685584, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 1560480, 0, 0, 1560480, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 685584, 833376, 0, 685584, 0]]
  ]
private theorem unseen10101_partial (x y : Fin 6) (i : Fin 5) :
    rowPartial (true, false) ![1, 0, 1, 0, 1] x y i = unseen10101Data i x y := by
  fin_cases x <;> fin_cases y <;> fin_cases i <;> decide +kernel
private theorem unseen10101_counts (i : Fin 5) :
    allCounts (true, false) ![1, 0, 1, 0, 1] i = ![64, 800, 17216, 360576, 7530048] i := by
  simp only [allCounts, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![1, 0, 1, 0, 1] x y i) = _
  simp_rw [unseen10101_partial]
  fin_cases i <;> decide +kernel
private def initialData : Fin 5 → Fin 6 → Fin 6 → ℤ :=
  ![
    ![![0, 16, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 120, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 2384, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 49344, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]],
    ![![0, 1028832, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  ]
private theorem initial_partial (x y : Fin 6) (i : Fin 5) :
    firstPartial x y i = initialData i x y := by
  fin_cases x <;> fin_cases y <;> fin_cases i <;> decide +kernel
private theorem initial_row_counts (i : Fin 5) :
    allFirst i = ![16, 120, 2384, 49344, 1028832] i := by
  simp only [allFirst, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, firstPartial x y i) = _
  simp_rw [initial_partial]
  fin_cases i <;> decide +kernel

section
attribute [local irreducible] allCounts
private theorem unseen_counts (p : Boundary)
    (ha : ∀ j : Fin 4, p j.castSucc ≠ p j.succ) (hb : ∀ j, p j ≠ 2) (i : Fin 5) :
    allCounts (true, false) p i = ![64, 800, 17216, 360576, 7530048] i := by
  have he : p = ![p 0, p 1, p 2, p 3, p 4] := by
    funext j
    fin_cases j <;> rfl
  rw [he] at ha hb ⊢
  generalize p 0 = a at ha hb ⊢
  generalize p 1 = b at ha hb ⊢
  generalize p 2 = c at ha hb ⊢
  generalize p 3 = d at ha hb ⊢
  generalize p 4 = e at ha hb ⊢
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> first
  | exact absurd (And.intro ha hb) (by decide +kernel)
  | exact unseen01010_counts i
  | exact unseen10101_counts i
end

private theorem row_counts (s : Seen) (p : Boundary) (h : Valid s p) :
    classCount s p true = (if s.2 then 64 * moment p 1 else 800) ∧
    classCount s p false = (if s.2 then 0 else 64) ∧
    ∀ i : Fin 3, momentCount s p i.succ =
      (if s.2 then 64 * ![moment p 2, moment p 3,
        81 * moment p 1 - 90 * moment p 2 + 25 * moment p 3] i
      else ![17216, 360576, 7530048] i) := by
  rcases s with ⟨x, y⟩
  have hx : x = true := h.1
  subst x
  cases y with
  | false =>
    have hh := unseen_counts p h.2.1 (h.2.2 rfl)
    refine ⟨hh 1, hh 0, ?_⟩
    intro i
    fin_cases i
    · exact hh 2
    · exact hh 3
    · exact hh 4
  | true =>
    have ht := full_moments p 0
    rw [label_counts p h.2.1 0] at ht
    refine ⟨ht, ?_, ?_⟩
    · simp [classCount, (full_flags _).2]
    · intro i
      rw [full_moments, label_counts p h.2.1]
      fin_cases i <;> rfl

private theorem initial_counts :
    firstCount true = 120 ∧ firstCount false = 16 ∧
      ∀ i : Fin 3, firstMoment i.succ = ![2384, 49344, 1028832] i := by
  refine ⟨initial_row_counts 1, initial_row_counts 0, ?_⟩
  intro i
  fin_cases i
  · exact initial_row_counts 2
  · exact initial_row_counts 3
  · exact initial_row_counts 4

/-- One-row transfer moments and the initial-row counts. -/
theorem finite_certificate :
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 64 * moment p 1 else 800) ∧
      classCount s p false = (if s.2 then 0 else 64) ∧
      ∀ i : Fin 3, momentCount s p i.succ =
        (if s.2 then 64 * ![moment p 2, moment p 3,
          81 * moment p 1 - 90 * moment p 2 + 25 * moment p 3] i
        else ![17216, 360576, 7530048] i)) ∧
    firstCount true = 120 ∧ firstCount false = 16 ∧
      ∀ i : Fin 3, firstMoment i.succ = ![2384, 49344, 1028832] i :=
  ⟨row_counts, initial_counts⟩

private theorem initial_valid (c : Row)
    (hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) :
    Valid (finish (false, false) c) (pairs c) := by
  have ht : ∀ y : Fin 6, ((0 : Fin 6) ≠ y ∧ y.val ≠ 5) →
      allowed (advance (false, false) 0) y → y = 1 := by decide +kernel
  have hb : (0 : Fin 6) ≠ c 1 ∧ (c 1).val ≠ 5 := by
    simpa only [hc.1, Fin.val_zero, zero_add] using hc.2.1 0
  have hg : allowed (advance (false, false) 0) (c 1) := by
    have hh : allowed (advance (false, false) (c 0)) (c 1) := hc.2.2.2.1
    simpa only [hc.1] using hh
  exact valid_next (false, false) c (Or.inr ⟨1, ht _ hb hg⟩) hc.2

private def w : ℕ → Fin 4 → ℤ
  | 0, i => ![864, 64, 0, 0] i
  | n + 1, i => ![64 * w n 0 + 17216 * w n 1 + 360576 * w n 2 + 7530048 * w n 3,
      5184 * w n 3, 64 * w n 1 - 5760 * w n 3, 64 * w n 2 + 1600 * w n 3] i
private def eval (n : ℕ) (s : Seen) (p : Boundary) : ℤ :=
  if s.2 then moment p 1 * w n 1 + moment p 2 * w n 2 + moment p 3 * w n 3
  else w n 0

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v (n + 1) s p = eval n s p := by
  induction n generalizing s p with
  | zero =>
    have he : v 1 s p = classCount s p true + classCount s p false := by
      simp only [v, widthV, widthStep, classCount, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · cases hb : (finish s c).2 <;> simp [hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    rw [he, (finite_certificate.1 s p h).1, (finite_certificate.1 s p h).2.1]
    cases hb : s.2 <;> simp [eval, w, hb]
  | succ n ih =>
    rw [v, widthV, widthStep]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      v (n + 1) (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v (n + 1) (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then moment (pairs c) 1 else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then moment (pairs c) 2 else 0) * w n 2 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then moment (pairs c) 3 else 0) * w n 3 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = false
          then (1 : ℤ) else 0) * w n 0 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s c (Or.inl h.1) ⟨hc.1, hc.2.2⟩)]
        cases hb : (finish s c).2 <;> simp [eval, hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    change momentCount s p 1 * w n 1 + momentCount s p 2 * w n 2 +
      momentCount s p 3 * w n 3 + classCount s p false * w n 0 = eval (n + 1) s p
    rw [(finite_certificate.1 s p h).2.2 0, (finite_certificate.1 s p h).2.2 1,
      (finite_certificate.1 s p h).2.2 2, (finite_certificate.1 s p h).2.1]
    cases hb : s.2 <;> simp [hb, eval, w] <;> ring

private theorem a_eq_w (n : ℕ) :
    (a (n + 2) : ℤ) = 16 * w n 0 + 2384 * w n 1 + 49344 * w n 2 + 1028832 * w n 3 := by
  rw [show n + 2 = (n + 1) + 1 by omega, counting_bridge, total, widthTotal]
  change (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
    v (n + 1) (finish (false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v (n + 1) (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then moment (pairs c) 1 else 0) * w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then moment (pairs c) 2 else 0) * w n 2 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then moment (pairs c) 3 else 0) * w n 3 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) * w n 0 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w _ _ _ (initial_valid c hc)]
      cases hb : (finish (false, false) c).2 <;> simp [eval, hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change firstMoment 1 * w n 1 + firstMoment 2 * w n 2 +
    firstMoment 3 * w n 3 + firstCount false * w n 0 = _
  rw [finite_certificate.2.2.2 0, finite_certificate.2.2.2 1,
    finite_certificate.2.2.2 2, finite_certificate.2.2.1]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 6) : ℤ) = 1664 * a (n + 5) - 471040 * a (n + 4) +
      44826624 * a (n + 3) - 1358954496 * a (n + 2) := by
  rw [show n + 6 = (((n + 1) + 1) + 1) + 1 + 2 by omega,
    show n + 5 = ((n + 1) + 1) + 1 + 2 by omega,
    show n + 4 = (n + 1) + 1 + 2 by omega,
    show n + 3 = (n + 1) + 2 by omega,
    a_eq_w, a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  norm_num
  ring

private theorem zero_count : a 0 = 0 := by simp [a, Legal]
private theorem one_count : (a 1 : ℤ) = 136 := by
  rw [show 1 = 0 + 1 from rfl, counting_bridge]
  have he : total (v 0) = firstCount true + firstCount false := by
    simp only [total, widthTotal, v, widthV, firstCount, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · cases hb : (finish (false, false) c).2 <;> simp [hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  rw [he, finite_certificate.2.1, finite_certificate.2.2.1]

attribute [local irreducible] a
open PowerSeries in
/-- Barker's identity for the literal six-column count, with `a 0 = 0`. -/
theorem result :
    (1 - 64 * X) * (1 - 1600 * X + 368640 * X ^ 2 - 21233664 * X ^ 3) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
        8 * X * (17 - 7488 * X + 974848 * X ^ 2 - 40108032 * X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 64 * X) * (1 - 1600 * X + 368640 * X ^ 2 - 21233664 * X ^ 3) * F =
      F - 1664 * (F * X ^ 1) + 471040 * (F * X ^ 2) -
        44826624 * (F * X ^ 3) + 1358954496 * (F * X ^ 4) := by ring
  have hr : (8 * X * (17 - 7488 * X + 974848 * X ^ 2 - 40108032 * X ^ 3) :
      PowerSeries ℤ) =
      136 * X - 59904 * X ^ 2 + 7798784 * X ^ 3 - 320864256 * X ^ 4 := by ring
  change (1 - 64 * X) * (1 - 1600 * X + 368640 * X ^ 2 - 21233664 * X ^ 3) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 6 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega)]
    have hh := recurrence (n - 6)
    have h6 : n - 6 + 6 = n := by omega
    have h5 : n - 6 + 5 = n - 1 := by omega
    have h4 : n - 6 + 4 = n - 2 := by omega
    have h3 : n - 6 + 3 = n - 3 := by omega
    have h2 : n - 6 + 2 = n - 4 := by omega
    rw [h6, h5, h4, h3, h2] at hh
    linarith
  · have h2 := a_eq_w 0
    have h3 := a_eq_w 1
    have h4 := a_eq_w 2
    have h5 := a_eq_w 3
    norm_num [w] at h2 h3 h4 h5
    interval_cases n <;> norm_num only [zero_count, one_count, h2, h3, h4, h5,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, if_true, if_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero, zero_add] <;> ring

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
