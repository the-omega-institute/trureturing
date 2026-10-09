/- GID: D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore
   mirror-E: none(waiver:unbounded-source-family)
   anchors: []
   utility: none
   digest: Actual repeated-word rows and the prescribed-area square core. -/

import D5.S3.Combinatorics.Partitions.WordPartitionInverse
import D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore

open scoped BigOperators
open D5.S3.Combinatorics.Partitions.PaddedWordPartition
open D5.S3.Combinatorics.Partitions.WordPartitionInverse
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.PositivePairs.Span.LiteralPowerSubstitution
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge

private theorem rows_replicate_true_append (n : ℕ) (w : List Bool) :
    rows (List.replicate n true ++ w) = (rows w).map (fun x => x + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rows] at *
      rw [ih]
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem rows_replicate_false_append (n : ℕ) (w : List Bool) :
    rows (List.replicate n false ++ w) = rows w ++ List.replicate n 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, rows]
      rw [ih]
      simp [List.append_assoc, List.replicate_succ']

private theorem rows_repeat_map_add (n : ℕ) (l : List ℕ) :
    (l.flatMap (fun x => List.replicate n (n * x))).map (fun x => x + n) =
      l.flatMap (fun x => List.replicate n (n * (x + 1))) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.flatMap_cons, List.map_append, ih, List.map_replicate]
      congr 1

theorem rows_literalPowerWord (n : ℕ) (w : List Bool) :
    rows (literalPowerWord n w) =
      (rows w).flatMap (fun x => List.replicate n (n * x)) := by
  induction w with
  | nil => simp [literalPowerWord, rows]
  | cons c w ih =>
      cases c with
      | false =>
          change rows (List.replicate n false ++ literalPowerWord n w) = _
          rw [rows_replicate_false_append, ih]
          simp [rows, List.flatMap_append]
      | true =>
          change rows (List.replicate n true ++ literalPowerWord n w) = _
          rw [rows_replicate_true_append, ih]
          simpa [rows, List.flatMap_map] using rows_repeat_map_add n (rows w)

private theorem rows_concat (w z : List Bool) :
    rows (w++z) = (rows z).map (fun r => r + w.count true) ++ rows w := by
  induction w with
  | nil => simp [rows]
  | cons c w ih =>
      cases c with
      | false => simp [rows, ih, List.append_assoc]
      | true =>
          simp [rows, ih, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem literalPowerWord_count (n : ℕ) (w : List Bool) (c : Bool) :
    (literalPowerWord n w).count c = n * w.count c := by
  induction w with
  | nil => simp [literalPowerWord]
  | cons d w ih =>
      simp only [literalPowerWord, List.flatMap_cons, List.count_append] at *
      rw [ih]
      by_cases h : d = c
      · subst d
        simp [Nat.mul_add, Nat.add_comm]
      · simp [List.count_replicate, h]

private theorem repeatedRows_sum (n : ℕ) (l : List ℕ) :
    (l.flatMap (fun x => List.replicate n (n * x))).sum = n ^ 2 * l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.flatMap_cons, List.sum_append, List.sum_replicate, ih,
        smul_eq_mul, List.sum_cons]
      ring

private theorem repeatedRows_square (n : ℕ) (l : List ℕ) :
    squareRows (l.flatMap (fun x => List.replicate n (n * x))) =
      (n : ℝ) ^ 3 * squareRows l := by
  induction l with
  | nil => simp [squareRows]
  | cons x l ih =>
      simp only [List.flatMap_cons, squareRows, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, nsmul_eq_mul, List.map_cons,
        List.sum_cons] at *
      rw [ih]
      push_cast
      ring

private theorem oddRows_replicate_prefix (n x : ℕ) (l : List ℕ) :
    oddRows (List.replicate n x ++ l) =
      (n : ℝ) ^ 2 * x + oddRows l + 2 * n * (l.sum : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, oddRows, ih]
      simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
      push_cast
      ring

private theorem repeatedRows_odd (n : ℕ) (l : List ℕ) :
    oddRows (l.flatMap (fun x => List.replicate n (n * x))) =
      (n : ℝ) ^ 3 * oddRows l := by
  induction l with
  | nil => simp [oddRows]
  | cons x l ih =>
      rw [List.flatMap_cons, oddRows_replicate_prefix, ih, repeatedRows_sum, oddRows]
      push_cast
      ring

private theorem literalPowerWord_area (n : ℕ) (w : List Bool) :
    scatteredTrueFalseCount (literalPowerWord n w) = n ^ 2 * scatteredTrueFalseCount w := by
  rw [← rows_sum, rows_literalPowerWord, repeatedRows_sum, rows_sum]

/-- Literal repetition scales the actual fan coordinates in their homogeneous degrees. -/
theorem G_literalPowerWord (n : ℕ) (w : List Bool) :
    G (literalPowerWord n w) =
      ⟨n * (G w).u, n * (G w).v, (n : ℝ) ^ 2 * (G w).d,
        (n : ℝ) ^ 3 * (G w).e, (n : ℝ) ^ 3 * (G w).f⟩ := by
  rw [all_word_direct, all_word_direct w]
  simp only [same_diagram_rows, same_diagram_columns, literalPowerWord_count,
    literalPowerWord_area, rows_literalPowerWord, repeatedRows_square, repeatedRows_odd]
  apply Five.ext <;> dsimp <;> push_cast <;> ring

def level3Index (x y z : Bool) : Fin 3 → Bool := ![x,y,z]

def P0 : List Bool := (positivePairWords 3 (level3Index true false true)).2
def P1 : List Bool := (positivePairWords 3 (level3Index true false true)).1
def Q0 : List Bool := (positivePairWords 3 (level3Index true false false)).2
def Q1 : List Bool := (positivePairWords 3 (level3Index true false false)).1

private theorem P0_eq : P0 = [false,true,true,true,false] := by
  decide

private theorem P1_eq : P1 = [true,false,true,false,true] := by
  decide

private theorem Q0_eq : Q0 = [false,true,false,true,false] := by
  decide

private theorem Q1_eq : Q1 = [true,false,false,false,true] := by
  decide

def H (e f : Bool) : List Bool :=
  (if e then P1 else P0) ++ (if f then Q1 else Q0) ++ Q0 ++ P0

private theorem H_counts (e f : Bool) :
    (H e f).count true = 10 ∧ (H e f).count false = 10 := by
  cases e <;> cases f <;>
    simp [H, P0_eq, P1_eq, Q0_eq, Q1_eq]

private theorem H_area (e f : Bool) :
    scatteredTrueFalseCount (H e f) = 50 := by
  cases e <;> cases f <;>
    norm_num [H, P0_eq, P1_eq, Q0_eq, Q1_eq,
      scatteredTrueFalseCount]

set_option maxHeartbeats 3000000 in
-- The four direct fan computations expand both moments of the twenty-letter blocks.
private theorem H_G (e f : Bool) :
    G (H e f) =
      ⟨10, 10, 0,
        -92 - 24 * (if e then 1 else 0) - 12 * (if f then 1 else 0),
        -136 - 12 * (if e then 1 else 0) - 24 * (if f then 1 else 0)⟩ := by
  obtain ⟨ht, hf⟩ := H_counts e f
  rw [all_word_direct, ht, hf, H_area, same_diagram_rows, same_diagram_columns]
  cases e <;> cases f <;>
    norm_num [H, P0_eq, P1_eq, Q0_eq, Q1_eq, rows, squareRows, oddRows]

private def thresholdWord (n d e m : ℕ) : List Bool :=
  (List.range m).flatMap fun l =>
    literalPowerWord n (H (decide (l + 1 ≤ d)) (decide (l + 1 ≤ e)))

private theorem min_succ_threshold (m d : ℕ) :
    min (m + 1) d = min m d + if m + 1 ≤ d then 1 else 0 := by
  split <;> omega

set_option maxHeartbeats 3000000 in
-- All five coordinates of the symbolic threshold concatenation are expanded together.
private theorem G_thresholdWord (n d e m : ℕ) :
    G (thresholdWord n d e m) =
      ⟨10 * m * n, 10 * m * n, 0,
        (n : ℝ) ^ 3 * (-92 * m-24 * (min m d : ℕ)-12 * (min m e : ℕ)),
        (n : ℝ) ^ 3 * (-136 * m-12 * (min m d : ℕ)-24 * (min m e : ℕ))⟩ := by
  induction m with
  | zero => simp [thresholdWord, G_nil, zeroFive]
  | succ m ih =>
      simp only [thresholdWord, List.range_succ, List.flatMap_append,
        List.flatMap_singleton] at *
      rw [G_concat, ih, G_literalPowerWord, H_G]
      rw [min_succ_threshold m d, min_succ_threshold m e]
      by_cases hd : m + 1 ≤ d <;> by_cases he : m + 1 ≤ e <;>
        apply Five.ext <;>
          simp [D5.S3.Combinatorics.Partitions.PaddedWordPartition.star, hd, he] <;> ring

private def levels (n : ℕ) : List ℕ → List ℕ → List Bool
  | d :: ds, e :: es => thresholdWord n d e 7 ++ levels (2 * n) ds es
  | _, _ => []

set_option maxHeartbeats 3000000 in
-- The degree-three coordinate expansions include both radix-eight digit recursions.
private theorem G_levels (n : ℕ) (ds es : List ℕ)
    (hlen : ds.length = es.length)
    (hd : ∀ d ∈ ds, d < 8) (he : ∀ e ∈ es, e < 8) :
    G (levels n ds es) =
      ⟨70 * n * ((2 : ℝ) ^ ds.length-1), 70 * n * ((2 : ℝ) ^ ds.length-1), 0,
        (n : ℝ) ^ 3 * (-92 * ((8 : ℝ) ^ ds.length-1)-
          24 * (Nat.ofDigits 8 ds : ℕ)-12 * (Nat.ofDigits 8 es : ℕ)),
        (n : ℝ) ^ 3 * (-136 * ((8 : ℝ) ^ ds.length-1)-
          12 * (Nat.ofDigits 8 ds : ℕ)-24 * (Nat.ofDigits 8 es : ℕ))⟩ := by
  induction ds generalizing n es with
  | nil =>
      have hes : es = [] := List.length_eq_zero_iff.mp hlen.symm
      subst es
      simp [levels, G_nil, zeroFive, Nat.ofDigits]
  | cons d ds ih =>
      cases es with
      | nil => simp at hlen
      | cons e es =>
          have hd0 : d ≤ 7 := by have := hd d (by simp); omega
          have he0 : e ≤ 7 := by have := he e (by simp); omega
          rw [levels, G_concat, G_thresholdWord,
            ih (2 * n) es (by simpa using hlen)
              (by intro x hx; exact hd x (by simp [hx]))
              (by intro x hx; exact he x (by simp [hx]))]
          simp only [Nat.min_eq_right hd0, Nat.min_eq_right he0,
            List.length_cons, Nat.ofDigits_cons, pow_succ]
          apply Five.ext <;>
            dsimp [D5.S3.Combinatorics.Partitions.PaddedWordPartition.star] <;> push_cast <;> ring

/-- The dyadic radix and the exact square core index domain. -/
def q (J : ℕ) : ℕ := 2 ^ J

def coreSide (J : ℕ) : ℕ := 70 * (q J-1)

abbrev CoreIndex (J : ℕ) := Fin ((q J) ^ 3) × Fin ((q J) ^ 3)

/-- Increasing scale, then thresholds one through seven, with low-to-high base-eight digits. -/
def V (J : ℕ) (x : CoreIndex J) : List Bool :=
  levels 1 (Nat.digitsAppend 8 J x.1.val) (Nat.digitsAppend 8 J x.2.val)

private theorem q_cube (J : ℕ) : (q J) ^ 3 = 8 ^ J := by
  simp only [q, ← pow_mul]
  rw [Nat.mul_comm, pow_mul]
  norm_num

private theorem q_pos (J : ℕ) : 0 < q J := by unfold q; positivity

private theorem coreSide_cast (J : ℕ) :
    (coreSide J : ℝ) = 70 * ((2 : ℝ) ^ J-1) := by
  have hq : 1 ≤ q J := q_pos J
  unfold coreSide
  rw [Nat.cast_mul, Nat.cast_sub hq]
  norm_num [q]

private theorem G_V (J : ℕ) (x : CoreIndex J) :
    G (V J x) =
      ⟨coreSide J, coreSide J, 0,
        -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val,
        -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val⟩ := by
  have hx : x.1.val < 8 ^ J := by simpa only [← q_cube] using x.1.isLt
  have hy : x.2.val < 8 ^ J := by simpa only [← q_cube] using x.2.isLt
  rw [V, G_levels 1 _ _
    (by rw [Nat.length_digitsAppend (by norm_num) J hx,
      Nat.length_digitsAppend (by norm_num) J hy])
    (fun d hd => Nat.lt_of_mem_digitsAppend (by norm_num) J d hd)
    (fun e he => Nat.lt_of_mem_digitsAppend (by norm_num) J e he)]
  rw [Nat.length_digitsAppend (by norm_num) J hx]
  have hdx := (Nat.setInvOn_digitsAppend_ofDigits (by norm_num : 1 < 8) J).2 hx
  have hdy := (Nat.setInvOn_digitsAppend_ofDigits (by norm_num : 1 < 8) J).2 hy
  have hpow : (8 : ℝ) ^ J = (q J : ℝ) ^ 3 := by exact_mod_cast (q_cube J).symm
  rw [hdx, hdy, hpow, coreSide_cast]
  simp

private theorem V_counts_area (J : ℕ) (x : CoreIndex J) :
    (V J x).count true = coreSide J ∧ (V J x).count false = coreSide J ∧
    scatteredTrueFalseCount (V J x) = (coreSide J) ^ 2 / 2 := by
  have hg := G_V J x
  have hu := congrArg Five.u hg
  have hv := congrArg Five.v hg
  rw [all_word_direct] at hu hv
  dsimp only at hu hv
  have hut : (V J x).count true = coreSide J := by exact_mod_cast hu
  have hvf : (V J x).count false = coreSide J := by exact_mod_cast hv
  refine ⟨hut, hvf, ?_⟩
  have harea := congrArg Five.d hg
  rw [all_word_direct, hut, hvf] at harea
  have hareaNat : 2 * scatteredTrueFalseCount (V J x) = (coreSide J) ^ 2 := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    dsimp at harea
    nlinarith
  omega

/-- The exact source quotient / remainder word, with false=b and true=a. -/
def fixedZ (b kappa : ℕ) : List Bool :=
  let j := kappa / b
  let z := kappa%b
  if z = 0 then
    List.replicate (b-j) false ++ List.replicate b true ++ List.replicate j false
  else
    List.replicate (b-j-1) false ++ List.replicate z true ++ [false] ++
      List.replicate (b-z) true ++ List.replicate j false

private theorem fixedZ_guards (b kappa : ℕ) (hb : 0 < b) (hk : kappa ≤ b ^ 2) :
    kappa / b ≤ b ∧ kappa%b < b ∧
    (kappa%b ≠ 0 → kappa / b + 1 ≤ b) := by
  have hdiv := Nat.mod_add_div kappa b
  have hmod := Nat.mod_lt kappa hb
  have hquot : kappa / b ≤ b := by
    calc kappa / b ≤ b ^ 2 / b := Nat.div_le_div_right hk
         _ = b := by rw [pow_two, Nat.mul_div_cancel _ hb]
  refine ⟨hquot, hmod, ?_⟩
  intro hz
  by_contra hc
  have heq : kappa / b = b := by omega
  rw [heq] at hdiv
  have hmodpos : 0 < kappa%b := Nat.pos_of_ne_zero hz
  nlinarith

private theorem fixedZ_rows (b kappa : ℕ) (hb : 0 < b) :
    rows (fixedZ b kappa) =
      if kappa%b = 0 then
        List.replicate (kappa / b) b ++ List.replicate (b-kappa / b) 0
      else
        List.replicate (kappa / b) b ++ [kappa%b] ++
          List.replicate (b-kappa / b-1) 0 := by
  unfold fixedZ
  dsimp only
  have hr (j : ℕ) : rows (List.replicate j false) = List.replicate j 0 := by
    simpa [rows] using rows_replicate_false_append j []
  split <;> rename_i hz
  · simp [List.append_assoc, rows_replicate_false_append,
      rows_replicate_true_append, hr]
  · have hmod : kappa % b ≤ b := Nat.le_of_lt (Nat.mod_lt kappa hb)
    simp [List.append_assoc, rows_replicate_false_append,
      rows_replicate_true_append, hr, rows, Nat.sub_add_cancel hmod]

private theorem fixedZ_spec (b kappa : ℕ) (hb : 0 < b) (hk : kappa ≤ b ^ 2) :
    (fixedZ b kappa).count true = b ∧ (fixedZ b kappa).count false = b ∧
    scatteredTrueFalseCount (fixedZ b kappa) = kappa := by
  obtain ⟨hj, hz, hjz⟩ := fixedZ_guards b kappa hb hk
  refine ⟨?_, ?_, ?_⟩
  · unfold fixedZ
    dsimp only
    split <;> simp [List.count_append, List.count_replicate] <;> omega
  · unfold fixedZ
    dsimp only
    split <;> rename_i hz0
    · simp [List.count_append, List.count_replicate]
      omega
    · have := hjz hz0
      simp [List.count_append, List.count_replicate]
      omega
  · rw [← rows_sum, fixedZ_rows b kappa hb]
    have harea := Nat.mod_add_div kappa b
    split <;> rename_i hz0
    · simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
      simpa [hz0, Nat.mul_comm] using harea
    · simpa [List.sum_append, List.sum_replicate, smul_eq_mul, Nat.mul_comm,
        Nat.add_comm] using harea

def suffixArea (J h t : ℕ) : ℕ :=
  t + (coreSide J) ^ 2 / 2-coreSide J * h

/-- The core and its fixed exact-area completion, with no reversal or area normalization. -/
def W (J h t : ℕ) (x : CoreIndex J) : List Bool :=
  V J x ++ fixedZ (h-coreSide J) (suffixArea J h t)

private theorem completion_guards (J h t : ℕ)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    0 < h-coreSide J ∧ Even (coreSide J) ∧
    coreSide J * h ≤ t + (coreSide J) ^ 2 / 2 ∧
    suffixArea J h t + coreSide J * h = t + (coreSide J) ^ 2 / 2 ∧
    suffixArea J h t ≤ (h-coreSide J) ^ 2 := by
  have heven : Even (coreSide J) := by
    refine ⟨35 * (q J-1), ?_⟩
    unfold coreSide
    ring
  have hhalf : (coreSide J) ^ 2 / 2 * 2 = (coreSide J) ^ 2 :=
    Nat.div_mul_cancel (dvd_pow heven.two_dvd (by norm_num : 2 ≠ 0))
  have hprod := Nat.mul_le_mul_right h ha
  have hnon : coreSide J * h ≤ t + (coreSide J) ^ 2 / 2 := by nlinarith
  have hsub : suffixArea J h t + coreSide J * h = t + (coreSide J) ^ 2 / 2 := by
    unfold suffixArea
    exact Nat.sub_add_cancel hnon
  have hb : h-coreSide J + coreSide J = h := by omega
  refine ⟨by omega, heven, hnon, hsub, ?_⟩
  nlinarith

private theorem W_counts_area (J h t : ℕ) (x : CoreIndex J)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    (W J h t x).count true = h ∧ (W J h t x).count false = h ∧
    scatteredTrueFalseCount (W J h t x) = t := by
  obtain ⟨hb, heven, hnon, hsub, hk⟩ := completion_guards J h t hh ha ht0 ht1
  obtain ⟨hvt, hvf, hva⟩ := V_counts_area J x
  obtain ⟨hzt, hzf, hza⟩ := fixedZ_spec (h-coreSide J) (suffixArea J h t) hb hk
  have hsum : coreSide J + (h-coreSide J) = h := by omega
  have hwt : (W J h t x).count true = h := by simp [W, hvt, hzt, hsum]
  have hwf : (W J h t x).count false = h := by simp [W, hvf, hzf, hsum]
  refine ⟨hwt, hwf, ?_⟩
  have hzG := all_word_direct (fixedZ (h-coreSide J) (suffixArea J h t))
  have hd := congrArg Five.d (G_concat (V J x)
    (fixedZ (h-coreSide J) (suffixArea J h t)))
  rw [all_word_direct (V J x), hzG, hvt, hvf, hva, hzt, hzf, hza] at hd
  change (G (W J h t x)).d = _ at hd
  rw [all_word_direct, hwt, hwf] at hd
  dsimp [D5.S3.Combinatorics.Partitions.PaddedWordPartition.star] at hd
  have hhalf : (coreSide J) ^ 2 / 2 * 2 = (coreSide J) ^ 2 :=
    Nat.div_mul_cancel (dvd_pow heven.two_dvd (by norm_num : 2 ≠ 0))
  apply Nat.cast_injective (R := ℝ)
  have hsubR : (suffixArea J h t : ℝ) + (coreSide J : ℝ) * h =
      t + ((coreSide J) ^ 2 / 2 : ℕ) := by exact_mod_cast hsub
  have hbR : ((h-coreSide J : ℕ) : ℝ) + (coreSide J : ℝ) = h := by
    exact_mod_cast (by omega : h-coreSide J + coreSide J = h)
  have hhalfR : (((coreSide J) ^ 2 / 2 : ℕ) : ℝ) * 2 = (coreSide J : ℝ) ^ 2 := by
    exact_mod_cast hhalf
  nlinarith

private theorem G_W (J h t : ℕ) (x : CoreIndex J)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    G (W J h t x) =
      ⟨h, h, 2 * (t : ℝ)-(h : ℝ) ^ 2,
        -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val+
          (G (fixedZ (h-coreSide J) (suffixArea J h t))).e+
          3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d,
        -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val+
          (G (fixedZ (h-coreSide J) (suffixArea J h t))).f+
          3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d⟩ := by
  obtain ⟨hb, _, _, _, hk⟩ := completion_guards J h t hh ha ht0 ht1
  obtain ⟨hzt, hzf, _⟩ := fixedZ_spec (h-coreSide J) (suffixArea J h t) hb hk
  obtain ⟨hwt, hwf, hwa⟩ := W_counts_area J h t x hh ha ht0 ht1
  have hzu : (G (fixedZ (h-coreSide J) (suffixArea J h t))).u = ((h-coreSide J : ℕ) : ℝ) := by
    rw [all_word_direct, hzt]
  have hzv : (G (fixedZ (h-coreSide J) (suffixArea J h t))).v = ((h-coreSide J : ℕ) : ℝ) := by
    rw [all_word_direct, hzf]
  have hcat : G (W J h t x) =
      PaddedWordPartition.star (G (V J x))
        (G (fixedZ (h-coreSide J) (suffixArea J h t))) := G_concat _ _
  apply Five.ext
  · rw [all_word_direct, hwt]
  · rw [all_word_direct, hwf]
  · rw [all_word_direct, hwt, hwf, hwa]
    dsimp
    ring
  · rw [hcat, G_V]
    dsimp [PaddedWordPartition.star]
    rw [hzu, hzv]
    ring
  · rw [hcat, G_V]
    dsimp [PaddedWordPartition.star]
    rw [hzu, hzv]
    ring

private theorem W_joint_injective (J h t : ℕ)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    Function.Injective (fun x : CoreIndex J => ((G (W J h t x)).e, (G (W J h t x)).f)) := by
  intro x y hxy
  have he := congrArg Prod.fst hxy
  have hf := congrArg Prod.snd hxy
  dsimp only at he hf
  rw [G_W J h t x hh ha ht0 ht1, G_W J h t y hh ha ht0 ht1] at he hf
  dsimp only at he hf
  have hx : (x.1.val : ℝ) = y.1.val := by linarith
  have hy : (x.2.val : ℝ) = y.2.val := by linarith
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast hx
  · exact_mod_cast hy

private theorem W_row_joint_injective (J h t : ℕ)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    Function.Injective (fun x : CoreIndex J =>
      (squareRows (rows (W J h t x)), oddRows (rows (W J h t x)))) := by
  intro x y hxy
  obtain ⟨hxt, hxf, hxa⟩ := W_counts_area J h t x hh ha ht0 ht1
  obtain ⟨hyt, hyf, hya⟩ := W_counts_area J h t y hh ha ht0 ht1
  apply W_joint_injective J h t hh ha ht0 ht1
  apply Prod.ext
  · have he := congrArg Prod.fst hxy
    dsimp only at he ⊢
    rw [all_word_direct, all_word_direct, hxt, hxf, hxa, hyt, hyf, hya,
      same_diagram_rows, same_diagram_rows]
    dsimp only at he ⊢
    rw [he]
  · have hf := congrArg Prod.snd hxy
    dsimp only at hf ⊢
    rw [all_word_direct, all_word_direct, hxt, hxf, hxa, hyt, hyf, hya,
      same_diagram_columns, same_diagram_columns]
    dsimp only at hf ⊢
    rw [hf]

/-- Exact-area actual square words, their common direct rows, and their joint image. -/
theorem square_family (J h t : ℕ)
    (hh : 0 < h) (ha : 8 * coreSide J ≤ h)
    (ht0 : h ^ 2 ≤ 8 * t) (ht1 : 8 * t ≤ 7 * h ^ 2) :
    (∀ x : CoreIndex J,
      G (V J x) =
        ⟨coreSide J, coreSide J, 0,
          -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val,
          -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val⟩ ∧
      (V J x).count true = coreSide J ∧ (V J x).count false = coreSide J ∧
      scatteredTrueFalseCount (V J x) = (coreSide J) ^ 2 / 2) ∧
    (0 < h-coreSide J ∧ Even (coreSide J) ∧
      coreSide J * h ≤ t + (coreSide J) ^ 2 / 2 ∧
      suffixArea J h t + coreSide J * h = t + (coreSide J) ^ 2 / 2 ∧
      suffixArea J h t ≤ (h-coreSide J) ^ 2) ∧
    (∀ x : CoreIndex J,
      W J h t x ∈ wordFiber h h t ∧
      (W J h t x).count true = h ∧ (W J h t x).count false = h ∧
      scatteredTrueFalseCount (W J h t x) = t ∧
      (rows (W J h t x)).length = h ∧ (rows (W J h t x)).SortedGE ∧
      (∀ r ∈ rows (W J h t x), r ≤ h) ∧ (rows (W J h t x)).sum = t ∧
      rows (W J h t x) =
        (rows (fixedZ (h-coreSide J) (suffixArea J h t))).map
          (fun r => r + coreSide J) ++ rows (V J x) ∧
      G (W J h t x) =
        ⟨h, h, 2 * (t : ℝ)-(h : ℝ) ^ 2,
          -92 * ((q J : ℝ) ^ 3-1)-24 * x.1.val-12 * x.2.val+
            (G (fixedZ (h-coreSide J) (suffixArea J h t))).e+
            3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d,
          -136 * ((q J : ℝ) ^ 3-1)-12 * x.1.val-24 * x.2.val+
            (G (fixedZ (h-coreSide J) (suffixArea J h t))).f+
            3 * coreSide J * (G (fixedZ (h-coreSide J) (suffixArea J h t))).d⟩) ∧
    Function.Injective (W J h t) ∧
    Function.Injective (fun x : CoreIndex J => ((G (W J h t x)).e, (G (W J h t x)).f)) ∧
    Function.Injective (fun x : CoreIndex J =>
      (squareRows (rows (W J h t x)), oddRows (rows (W J h t x)))) ∧
    (Set.range (W J h t)).ncard = (q J) ^ 6 ∧
    (Set.range (fun x : CoreIndex J => ((G (W J h t x)).e, (G (W J h t x)).f))).ncard =
      (q J) ^ 6 ∧
    (Set.range (fun x : CoreIndex J =>
      (squareRows (rows (W J h t x)), oddRows (rows (W J h t x))))).ncard = (q J) ^ 6 ∧
    (q J) ^ 6 ≤ capacity h h t := by
  refine ⟨fun x => ⟨G_V J x, V_counts_area J x⟩,
    completion_guards J h t hh ha ht0 ht1, ?_⟩
  have hinj := W_joint_injective J h t hh ha ht0 ht1
  have hrinj := W_row_joint_injective J h t hh ha ht0 ht1
  have hwinj : Function.Injective (W J h t) := by
    intro x y hxy
    exact hinj (congrArg (fun w => ((G w).e, (G w).f)) hxy)
  have hmem (x : CoreIndex J) : W J h t x ∈ wordFiber h h t := by
    obtain ⟨hxt, hxf, hxa⟩ := W_counts_area J h t x hh ha ht0 ht1
    refine ⟨?_, by exact_mod_cast hxt, by exact_mod_cast hxf, by exact_mod_cast hxa⟩
    intro he
    rw [he] at hxt
    simp at hxt
    omega
  have hcard : Nat.card (CoreIndex J) = (q J) ^ 6 := by
    simp [CoreIndex, ← pow_add]
  have hwordcard := (Set.ncard_range_of_injective hwinj).trans hcard
  have hjointcard := (Set.ncard_range_of_injective hinj).trans hcard
  have hrowcard := (Set.ncard_range_of_injective hrinj).trans hcard
  refine ⟨?_, hwinj, hinj, hrinj, hwordcard, hjointcard, hrowcard, ?_⟩
  · intro x
    obtain ⟨hxt, hxf, hxa⟩ := W_counts_area J h t x hh ha ht0 ht1
    refine ⟨hmem x, hxt, hxf, hxa, ?_, rows_sorted _, ?_, ?_, ?_,
      G_W J h t x hh ha ht0 ht1⟩
    · rw [rows_length, hxf]
    · simpa only [hxt] using rows_bound (W J h t x)
    · rw [rows_sum, hxa]
    · rw [W, rows_concat, (V_counts_area J x).1]
  · rw [capacity, ← hjointcard]
    apply Set.ncard_le_ncard _ ((fiber_finite h h t).image _)
    rintro _ ⟨x, rfl⟩
    exact ⟨W J h t x, hmem x, rfl⟩

#check rows_literalPowerWord
#check G_literalPowerWord
#check G_V
#check fixedZ_guards
#check fixedZ_rows
#check fixedZ_spec
#check completion_guards
#check G_W
#check square_family
#print axioms rows_literalPowerWord
#print axioms G_literalPowerWord
#print axioms square_family

end D5.S3.Combinatorics.Partitions.PrescribedAreaSquareWordCore
