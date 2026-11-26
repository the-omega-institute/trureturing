/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence.hardin_a235290; premises=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301,D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.count_transfer,D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_path_eq
   digest: Hardin's eleven-lag recurrence for literal stress-three square arrays. -/

/-
hardin_a235290: proof_shape: content
escape_witness: initialResidual_zero checks the diagonal-shift residual on the
  full ten-by-ten window of literal rectangle counts.
admission_basis: open-problem-resolution (#34377)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence

/-! The signed diagonal recurrence for literal indexed square arrays of stress three. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding (Word)
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
  (index par par_succ Hist State evalHist path count_transfer value)
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
  (initialPath initial_path_eq)
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence (hardin_a235301)
open scoped BigOperators

set_option warningAsError true

/-- Coefficients in increasing offset order within the order-ten rectangular window. -/
private def rectangleCoeffs : Fin 10 → ℤ := ![-576, 864, 360, -972, 76, 372, -86, -57, 17, 3]

private def rectangleNext (f : ℕ → ℤ) (t : ℕ) : ℤ :=
  ∑ i : Fin 10, rectangleCoeffs i * f (t + i.val)

private def AxisRecursAt (f : ℕ → ℤ) (t : ℕ) : Prop :=
  f (t + 10) = rectangleNext f t

private theorem axes_of_count (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    AxisRecursAt (fun i => (C 3 3 i k : ℤ)) t ∧
      AxisRecursAt (fun i => (C 3 3 k i : ℤ)) t := by
  obtain ⟨hh, hw⟩ := hardin_a235301 k (t + 10) hk (by omega)
  have axis (f : ℕ → ℤ) (hf :
      f (t + 10) = 3 * f (t + 10 - 1) + 17 * f (t + 10 - 2) -
        57 * f (t + 10 - 3) - 86 * f (t + 10 - 4) + 372 * f (t + 10 - 5) +
        76 * f (t + 10 - 6) - 972 * f (t + 10 - 7) + 360 * f (t + 10 - 8) +
        864 * f (t + 10 - 9) - 576 * f (t + 10 - 10)) : AxisRecursAt f t := by
    unfold AxisRecursAt rectangleNext
    have lag (i : ℕ) (hi : i ≤ 10) : t + 10 - i = t + (10 - i) := by omega
    simp only [lag 1 (by decide), lag 2 (by decide), lag 3 (by decide), lag 4 (by decide),
      lag 5 (by decide), lag 6 (by decide), lag 7 (by decide), lag 8 (by decide),
      lag 9 (by decide), lag 10 (by decide)] at hf
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, rectangleCoeffs]
    norm_num [Fin.val_succ] at hf ⊢
    linear_combination hf
  exact ⟨axis _ hh, axis _ hw⟩

/-- Including the leading coefficient, in increasing offset order. -/
private def residualCoeffs : Fin 12 → ℤ :=
  ![4608, -1152, -6336, 1584, 3280, -820, -800, 200, 92, -23, -4, 1]

private def diagonalResidual (F : ℕ → ℕ → ℤ) (t u : ℕ) : ℤ :=
  ∑ j : Fin 12, residualCoeffs j * F (t + j.val) (u + j.val)

/-- The exact signed assertion in OEIS A235290 revision 7, stated at its left index. -/
private def RecursAt (a : ℕ → ℤ) (n : ℕ) : Prop :=
  a n = 4 * a (n - 1) + 23 * a (n - 2) - 92 * a (n - 3) - 200 * a (n - 4) +
    800 * a (n - 5) + 820 * a (n - 6) - 3280 * a (n - 7) - 1584 * a (n - 8) +
    6336 * a (n - 9) + 1152 * a (n - 10) - 4608 * a (n - 11)

private theorem diagonalResidual_iff (F : ℕ → ℕ → ℤ) (t : ℕ) :
    diagonalResidual F t t = 0 ↔ RecursAt (fun i => F i i) (t + 11) := by
  unfold diagonalResidual RecursAt
  dsimp only
  have lag (i : ℕ) (hi : i ≤ 11) : t + 11 - i = t + (11 - i) := by omega
  simp only [lag 1 (by decide), lag 2 (by decide), lag 3 (by decide), lag 4 (by decide),
    lag 5 (by decide), lag 6 (by decide), lag 7 (by decide), lag 8 (by decide),
    lag 9 (by decide), lag 10 (by decide), lag 11 (by decide),
    Fin.sum_univ_succ, Fin.sum_univ_zero, residualCoeffs]
  norm_num [Fin.val_succ]
  constructor <;> intro h <;> linear_combination h

/-- Shifting the left coordinate of the residual obeys the same order-ten rule. -/
private theorem residual_height (F : ℕ → ℕ → ℤ)
    (hF : ∀ k t, 1 ≤ k → 1 ≤ t → AxisRecursAt (fun i => F i k) t)
    (t u : ℕ) (ht : 1 ≤ t) (hu : 1 ≤ u) :
    AxisRecursAt (fun i => diagonalResidual F i u) t := by
  unfold AxisRecursAt rectangleNext diagonalResidual
  dsimp only
  calc
    (∑ j : Fin 12, residualCoeffs j * F (t + 10 + j.val) (u + j.val)) =
        ∑ j : Fin 12, ∑ i : Fin 10,
          residualCoeffs j * (rectangleCoeffs i * F (t + i.val + j.val) (u + j.val)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := hF (u + j.val) (t + j.val) (by omega) (by omega)
        unfold AxisRecursAt rectangleNext at hj
        dsimp only at hj
        rw [show t + 10 + j.val = (t + j.val) + 10 by omega, hj, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show t + j.val + i.val = t + i.val + j.val by omega]
    _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Shifting the right coordinate of the residual obeys the order-ten rule. -/
private theorem residual_width (F : ℕ → ℕ → ℤ)
    (hF : ∀ k t, 1 ≤ k → 1 ≤ t → AxisRecursAt (F k) t)
    (t u : ℕ) (ht : 1 ≤ t) (hu : 1 ≤ u) :
    AxisRecursAt (diagonalResidual F t) u := by
  have h := residual_height (fun x y => F y x) hF u t hu ht
  simpa only [AxisRecursAt, rectangleNext, diagonalResidual] using h

/-- The first ten terms determine all terms through any common recurrence cutoff. -/
private theorem axis_unique_through (f g : ℕ → ℤ) (bound : ℕ)
    (hf : ∀ t, 1 ≤ t → t + 10 ≤ bound → AxisRecursAt f t)
    (hg : ∀ t, 1 ≤ t → t + 10 ≤ bound → AxisRecursAt g t)
    (hbase : ∀ t, 1 ≤ t → t ≤ 10 → t ≤ bound → f t = g t)
    (n : ℕ) (hn : 1 ≤ n) (hb : n ≤ bound) : f n = g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 10
    · exact hbase n hn hsmall hb
    have hstart : 1 ≤ n - 10 := by omega
    have hsum : n - 10 + 10 = n := by omega
    have fstep := hf (n - 10) hstart (by omega)
    have gstep := hg (n - 10) hstart (by omega)
    unfold AxisRecursAt rectangleNext at fstep gstep
    rw [hsum] at fstep gstep
    rw [fstep, gstep]
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    rw [ih (n - 10 + i.val) (by omega) (by omega) (by omega)]

private theorem axis_zero (f : ℕ → ℤ) (hf : ∀ t, 1 ≤ t → AxisRecursAt f t)
    (hbase : ∀ t, 1 ≤ t → t ≤ 10 → f t = 0) (n : ℕ) (hn : 1 ≤ n) : f n = 0 :=
  axis_unique_through f (fun _ => 0) n (fun t ht _ => hf t ht)
    (fun t _ _ => by simp [AxisRecursAt, rectangleNext])
    (fun t ht hsmall _ => hbase t ht hsmall) n hn le_rfl

/-- A zero initial residual rectangle propagates in both directions over positive indices. -/
private theorem residual_zero_of_first_window
    (hbase : ∀ t u, 1 ≤ t → t ≤ 10 → 1 ≤ u → u ≤ 10 →
      diagonalResidual (fun h w => (C 3 3 h w : ℤ)) t u = 0)
    (t u : ℕ) (ht : 1 ≤ t) (hu : 1 ≤ u) :
    diagonalResidual (fun h w => (C 3 3 h w : ℤ)) t u = 0 := by
  have hh : ∀ i, 1 ≤ i → ∀ j, 1 ≤ j → j ≤ 10 →
      diagonalResidual (fun h w => (C 3 3 h w : ℤ)) i j = 0 := by
    intro i hi j hj hj'
    exact axis_zero (fun x => diagonalResidual (fun h w => (C 3 3 h w : ℤ)) x j)
      (fun x hx => residual_height (fun h w => (C 3 3 h w : ℤ))
        (fun k a hk ha => (axes_of_count k a hk ha).1) x j hx hj)
      (fun x hx hx' => hbase x j hx hx' hj hj') i hi
  exact axis_zero (diagonalResidual (fun h w => (C 3 3 h w : ℤ)) t)
    (fun x hx => residual_width (fun h w => (C 3 3 h w : ℤ))
        (fun k a hk ha => (axes_of_count k a hk ha).2) t x ht hx)
    (hh t ht) u hu

private def columnParity (p : Bool) (j : ℕ) : Bool := if p then !(par j) else par j

@[simp] private theorem columnParity_zero (p : Bool) : columnParity p 0 = p := by
  cases p <;> rfl

private theorem columnParity_succ (p : Bool) (j : ℕ) :
    columnParity p (j + 1) = columnParity (!p) j := by
  cases p <;> simp [columnParity, par_succ]

private abbrev ColumnWeights := Vector ℤ 6

private def columnStep (m : ℕ) (p : Bool) (next : ColumnWeights) : ColumnWeights :=
  Vector.ofFn fun a => (List.ofFn fun b : Fin 6 =>
    if m.testBit (index p a b) then next[b] else 0).sum

private def columnWeights (m : ℕ) : ℕ → Bool → ColumnWeights
  | 0, _ => Vector.replicate 6 1
  | w + 1, p => columnStep m p (columnWeights m w (!p))

private def fastValue (w m : ℕ) : ℤ :=
  (columnWeights m w false)[0]

private noncomputable def suffixCount (w m : ℕ) (p : Bool) (a : Fin 6) : ℤ := by
  classical
  exact ∑ c : Word w,
    if c 0 = a ∧ (∀ j : Fin w,
      m.testBit (index (columnParity p j.val) (c j.castSucc) (c j.succ)) = true)
    then 1 else 0

private theorem suffixCount_zero (m : ℕ) (p : Bool) (a : Fin 6) :
    suffixCount 0 m p a = 1 := by
  classical
  let e : Fin 6 ≃ Word 0 :=
    ⟨fun b _ => b, fun c => c 0, fun _ => rfl, fun c => by
      funext i
      have he : i = 0 := Fin.ext (by have hi := i.isLt; omega)
      rw [he]⟩
  have h := Fintype.sum_equiv e
    (fun b => if b = a then (1 : ℤ) else 0)
    (fun c : Word 0 => if c 0 = a ∧ (∀ j : Fin 0,
      m.testBit (index (columnParity p j.val) (c j.castSucc) (c j.succ)) = true)
      then 1 else 0)
    (fun _ => by simp [e])
  unfold suffixCount
  rw [← h]
  simp

private theorem suffixCount_succ (w m : ℕ) (p : Bool) (a : Fin 6) :
    suffixCount (w + 1) m p a = ∑ b : Fin 6,
      if m.testBit (index p a b) then suffixCount w m (!p) b else 0 := by
  classical
  let e : Fin 6 × Word w ≃ Word (w + 1) := Fin.consEquiv (fun _ : Fin (w + 2) => Fin 6)
  unfold suffixCount
  rw [← e.sum_comp, Fintype.sum_prod_type]
  trans (∑ c : Word w,
    if m.testBit (index p a (c 0)) = true ∧
      (∀ j : Fin w, m.testBit (index (columnParity (!p) j.val)
        (c j.castSucc) (c j.succ)) = true) then (1 : ℤ) else 0)
  · rw [Finset.sum_eq_single a]
    · apply Finset.sum_congr rfl
      intro c _
      simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, true_and,
        Fin.forall_fin_succ, Fin.cons_succ]
      have hzero : (0 : Fin (w + 1)).castSucc = 0 := Fin.ext rfl
      have hleft (j : Fin w) : j.succ.castSucc = j.castSucc.succ := Fin.ext rfl
      simp only [hzero, Fin.cons_zero, Fin.val_zero, columnParity_zero, hleft,
        Fin.cons_succ, Fin.val_succ, columnParity_succ]
    · intro b _ hb
      simp [e, Fin.consEquiv, hb]
    · simp
  · let term (b : Fin 6) (c : Word w) : ℤ :=
      if c 0 = b ∧ ∀ j : Fin w, m.testBit
        (index (columnParity (!p) j.val) (c j.castSucc) (c j.succ)) = true then 1 else 0
    change _ = ∑ b : Fin 6, if m.testBit (index p a b) then ∑ c, term b c else 0
    have distr (b : Fin 6) :
        (if m.testBit (index p a b) then ∑ c : Word w, term b c else 0) =
          ∑ c : Word w, if m.testBit (index p a b) then term b c else 0 := by
      split <;> simp_all
    simp_rw [distr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_eq_single (c 0)]
    · by_cases h : m.testBit (index p a (c 0)) = true <;> simp [h, term]
    · intro b _ hb
      simp [term, Ne.symm hb]
    · simp

private theorem columnWeights_eq (w m : ℕ) (p : Bool) (a : Fin 6) :
    (columnWeights m w p)[a] = suffixCount w m p a := by
  induction w generalizing p a with
  | zero => simp [columnWeights, suffixCount_zero]
  | succ w ih =>
    rw [columnWeights, columnStep]
    change (Vector.ofFn _)[a.val] = _
    rw [Vector.getElem_ofFn, List.sum_ofFn, suffixCount_succ]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih]

private theorem fastValue_eq (w m : ℕ) : fastValue w m = value w m := by
  change (columnWeights m w false)[(0 : Fin 6)] = value w m
  rw [columnWeights_eq]
  unfold suffixCount value
  simp [columnParity]

private def fastCountFrom (xs : Hist State) (w : ℕ) : ℤ :=
  evalHist xs (fun s => fastValue w s.mask)

private theorem fastCountFrom_path (h w : ℕ) (hh : 1 ≤ h) (hw : 1 ≤ w) :
    fastCountFrom (path h) w = (C 3 3 h w : ℤ) := by
  rw [count_transfer h w hh hw]
  simp only [fastCountFrom, fastValue_eq]

/-- Candidate signed integer rectangle counts, indexed by the side parameters. -/
private def rectangleTable (h w : ℕ) : ℤ := ((#[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 40, 108, 272, 744, 1888, 5232, 13376, 37536, 96640, 274368, 710912, 2039424, 5314048,
    15382272, 40272896, 117459456, 308746240, 906083328, 2389348352, 7047112704, 18631057408],
  #[0, 108, 232, 476, 1132, 2556, 6532, 15692, 42100, 104988, 290932, 741836, 2101012, 5430876,
    15615412, 40720652, 118353940, 310480668, 909550132, 2396120396, 7060652692, 18657656796],
  #[0, 272, 476, 832, 1736, 3536, 8336, 18832, 48128, 115952, 312416, 782032, 2180576, 5582576,
    15917216, 41303632, 119516768, 312747632, 914077856, 2405006032, 7078411616, 18692677616],
  #[0, 744, 1132, 1736, 3184, 5784, 12328, 25592, 60856, 138744, 356632, 864056, 2342104,
    5889144, 16525528, 42475832, 121851736, 317293944, 923151832, 2422801976, 7113966424,
    18762768504],
  #[0, 1888, 2556, 3536, 5784, 9568, 18624, 35936, 79728, 172288, 420816, 983456, 2575824,
    6335488, 17408784, 44189216, 125260368, 323970688, 936469776, 2449052576, 7166397264,
    18866545408],
  #[0, 5232, 6532, 8336, 12328, 18624, 32992, 58688, 120112, 242592, 553552, 1227776, 3051088,
    7238304, 19190032, 47635328, 132106192, 337361952, 963161872, 2501628416, 7271370448,
    19074247584],
  #[0, 13376, 15692, 18832, 25592, 35936, 58688, 97888, 187184, 358016, 768272, 1623712,
    3817232, 8702336, 22073168, 53248288, 143248784, 359277056, 1006831952, 2588024992,
    7443849872, 19416695936],
  #[0, 37536, 42100, 48128, 60856, 79728, 120112, 187184, 333952, 603216, 1215520, 2436848,
    5377696, 11665488, 27888352, 64536944, 165624352, 403225296, 1094345440, 2761046768,
    7789147936, 20102042448],
  #[0, 96640, 104988, 115952, 138744, 172288, 242592, 358016, 603216, 1044640, 2006448, 3872192,
    8117424, 16889248, 38126832, 84508736, 205202736, 481284640, 1249786608, 3069367232,
    8404486704, 21326389408],
  #[0, 274368, 290932, 312416, 356632, 420816, 553552, 768272, 1215520, 2006448, 3677632,
    6842576, 13717312, 27477936, 58786432, 124676432, 284666560, 637793328, 1561224832,
    3686729936, 9636217792, 23776468656],
  #[0, 710912, 741836, 782032, 864056, 983456, 1227776, 1623712, 2436848, 3872192, 6842576,
    12420832, 24153296, 47228096, 97258256, 199695712, 433060688, 930865472, 2144492816,
    4845406432, 11948230736, 28382668736],
  #[0, 2039424, 2101012, 2180576, 2342104, 2575824, 3051088, 3817232, 5377696, 8117424,
    13717312, 24153296, 45663424, 87428784, 175026688, 350683472, 731046976, 1518456624,
    3312973312, 7165201616, 16575694144, 37599501744],
  #[0, 5314048, 5430876, 5582576, 5889144, 6335488, 7238304, 8702336, 11665488, 16889248,
    27477936, 47228096, 87428784, 165186208, 324954864, 641988416, 1305665328, 2653212448,
    5569683696, 11651162816, 25525195824, 55441728928],
  #[0, 15382272, 15615412, 15917216, 16525528, 17408784, 19190032, 22073168, 27888352, 38126832,
    58786432, 97258256, 175026688, 324954864, 629438272, 1229598608, 2460648832, 4929217392,
    10091090752, 20632564496, 43436664448, 91141634544],
  #[0, 40272896, 40720652, 41303632, 42475832, 44189216, 47635328, 53248288, 64536944, 84508736,
    124676432, 199695712, 350683472, 641988416, 1229598608, 2385515488, 4729198544, 9400918976,
    18972455312, 38285668192, 78643324112, 161350154816],
  #[0, 117459456, 118353940, 119516768, 121851736, 125260368, 132106192, 143248784, 165624352,
    205202736, 284666560, 433060688, 731046976, 1305665328, 2460648832, 4729198544, 9300386752,
    18380650416, 36775991680, 73637161808, 149110887616, 301830397488],
  #[0, 308746240, 310480668, 312747632, 317293944, 323970688, 337361952, 359277056, 403225296,
    481284640, 637793328, 930865472, 1518456624, 2653212448, 4929217392, 9400918976,
    18380650416, 36197979040, 72074168688, 143730274112, 288814025904, 580399909408],
  #[0, 906083328, 909550132, 914077856, 923151832, 936469776, 963161872, 1006831952, 1094345440,
    1249786608, 1561224832, 2144492816, 3312973312, 5569683696, 10091090752, 18972455312,
    36775991680, 72074168688, 142925492032, 284184904976, 568515582592, 1137861087216],
  #[0, 2389348352, 2396120396, 2405006032, 2422801976, 2449052576, 2501628416, 2588024992,
    2761046768, 3069367232, 3686729936, 4845406432, 7165201616, 11651162816, 20632564496,
    38285668192, 73637161808, 143730274112, 284184904976, 564035537632, 1125588965456,
    2248108869056],
  #[0, 7047112704, 7060652692, 7078411616, 7113966424, 7166397264, 7271370448, 7443849872,
    7789147936, 8404486704, 9636217792, 11948230736, 16575694144, 25525195824, 43436664448,
    78643324112, 149110887616, 288814025904, 568515582592, 1125588965456, 2241668515264,
    4470617838384],
  #[0, 18631057408, 18657656796, 18692677616, 18762768504, 18866545408, 19074247584,
    19416695936, 20102042448, 21326389408, 23776468656, 28382668736, 37599501744, 55441728928,
    91141634544, 161350154816, 301830397488, 580399909408, 1137861087216, 2248108869056,
    4470617838384, 8907655692448]
] : Array (Array ℤ))[h]!)[w]!


set_option maxHeartbeats 0 in
-- Each finite row is checked by kernel reduction.
set_option maxRecDepth 50000 in
/-- The table satisfies the axial recurrence at every window lying in the table. -/
private theorem checkedTableHeight (i : Fin 21) (j : Fin 11) :
    AxisRecursAt (fun h => rectangleTable h (i.val + 1)) (j.val + 1) := by
  fin_cases i <;> revert j <;> unfold AxisRecursAt <;> decide +kernel

set_option maxHeartbeats 0 in
-- Each finite row is checked by kernel reduction.
set_option maxRecDepth 50000 in
private theorem checkedTableWidth (i : Fin 21) (j : Fin 11) :
    AxisRecursAt (rectangleTable (i.val + 1)) (j.val + 1) := by
  fin_cases i <;> revert j <;> unfold AxisRecursAt <;> decide +kernel

set_option maxHeartbeats 0 in
-- Each finite row is checked by kernel reduction.
set_option maxRecDepth 50000 in
private theorem checkedResidual (i j : Fin 10) :
    diagonalResidual rectangleTable (i.val + 1) (j.val + 1) = 0 := by
  fin_cases i <;> revert j <;> decide +kernel

set_option maxHeartbeats 0 in
-- Each finite row is checked by kernel reduction.
set_option maxRecDepth 50000 in
/-- The sparse transfer computes each of the hundred initial literal counts. -/
private theorem checkedSeed (i j : Fin 10) :
    (C 3 3 (i.val + 1) (j.val + 1) : ℤ) = rectangleTable (i.val + 1) (j.val + 1) := by
  rw [← fastCountFrom_path _ _ (by omega) (by omega), initial_path_eq]
  revert j
  fin_cases i <;> decide +kernel

private theorem checkedBoundedSeed (h w : ℕ)
    (hh : 1 ≤ h) (hh' : h ≤ 10) (hw : 1 ≤ w) (hw' : w ≤ 10) :
    (C 3 3 h w : ℤ) = rectangleTable h w := by
  let i : Fin 10 := ⟨h - 1, by omega⟩
  let j : Fin 10 := ⟨w - 1, by omega⟩
  have hi : i.val + 1 = h := by dsimp [i]; omega
  have hj : j.val + 1 = w := by dsimp [j]; omega
  simpa only [hi, hj] using checkedSeed i j

/-- The candidate table is the literal rectangle count on its entire positive range. -/
private theorem rectangleTable_exact (h w : ℕ) (hh : 1 ≤ h) (hh' : h ≤ 21)
    (hw : 1 ≤ w) (hw' : w ≤ 21) : (C 3 3 h w : ℤ) = rectangleTable h w := by
  have heights (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 10) :
      (C 3 3 h k : ℤ) = rectangleTable h k := by
    refine axis_unique_through (fun a => (C 3 3 a k : ℤ)) (fun a => rectangleTable a k) 21
      (fun t ht _ => (axes_of_count k t hk ht).1) ?_ ?_ h hh hh'
    · intro t ht ht'
      let i : Fin 21 := ⟨k-1, by omega⟩
      let j : Fin 11 := ⟨t-1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      have hj : j.val + 1 = t := by dsimp [j]; omega
      simpa only [hi, hj] using checkedTableHeight i j
    · intro t ht ht' _
      exact checkedBoundedSeed t k ht ht' hk hk'
  refine axis_unique_through (fun j => (C 3 3 h j : ℤ)) (rectangleTable h) 21
    (fun t ht _ => (axes_of_count h t hh ht).2) ?_
    (fun t ht ht' _ => heights t ht ht') w hw hw'
  intro t ht ht'
  let i : Fin 21 := ⟨h - 1, by omega⟩
  let j : Fin 11 := ⟨t-1, by omega⟩
  have hi : i.val + 1 = h := by dsimp [i]; omega
  have hj : j.val + 1 = t := by dsimp [j]; omega
  simpa only [hi, hj] using checkedTableWidth i j

/-- The first residual window vanishes entry by entry. Its left indices are
12 through 21 in each coordinate. -/
private theorem initialResidual_zero (t u : ℕ) (ht : 1 ≤ t) (ht' : t ≤ 10)
    (hu : 1 ≤ u) (hu' : u ≤ 10) : diagonalResidual (fun h w => (C 3 3 h w : ℤ)) t u = 0 := by
  let i : Fin 10 := ⟨t-1, by omega⟩
  let j : Fin 10 := ⟨u-1, by omega⟩
  have hi : i.val + 1 = t := by dsimp [i]; omega
  have hj : j.val + 1 = u := by dsimp [j]; omega
  have zero : diagonalResidual rectangleTable t u = 0 := by
    simpa only [hi, hj] using checkedResidual i j
  rw [← zero]
  unfold diagonalResidual
  dsimp only
  apply Finset.sum_congr rfl
  intro k _
  have hlt := k.isLt
  rw [rectangleTable_exact _ _ (by omega) (by omega) (by omega) (by omega)]

/-- Hardin's eleven-lag recurrence for the literal indexed squares of stress three. -/
theorem hardin_a235290 (n : ℕ) (hn : 12 ≤ n) :
    (C 3 3 n n : ℤ) =
      4 * (C 3 3 (n - 1) (n - 1) : ℤ) + 23 * (C 3 3 (n - 2) (n - 2) : ℤ) -
      92 * (C 3 3 (n - 3) (n - 3) : ℤ) - 200 * (C 3 3 (n - 4) (n - 4) : ℤ) +
      800 * (C 3 3 (n - 5) (n - 5) : ℤ) + 820 * (C 3 3 (n - 6) (n - 6) : ℤ) -
      3280 * (C 3 3 (n - 7) (n - 7) : ℤ) - 1584 * (C 3 3 (n - 8) (n - 8) : ℤ) +
      6336 * (C 3 3 (n - 9) (n - 9) : ℤ) + 1152 * (C 3 3 (n - 10) (n - 10) : ℤ) -
      4608 * (C 3 3 (n - 11) (n - 11) : ℤ) := by
  have h := (diagonalResidual_iff (fun h w => (C 3 3 h w : ℤ)) (n - 11)).1
    (residual_zero_of_first_window initialResidual_zero (n - 11) (n - 11) (by omega) (by omega))
  rw [show n - 11 + 11 = n by omega] at h
  exact h

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235290DiagonalRecurrence
