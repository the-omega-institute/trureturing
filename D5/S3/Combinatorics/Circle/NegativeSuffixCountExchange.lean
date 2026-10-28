/- GID: D5/S3/Combinatorics/Circle/NegativeSuffixCountExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/NegativeSuffixCountExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Actual negative-LARGE count surplus gives a full exchange retaining every SMALL. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
public import D5.S3.Combinatorics.Circle.CountSurplusOrdering

/-! # Count-controlled physical exchange with a negative LARGE suffix

The paired count-surplus order retains every actual SMALL occurrence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.NegativeSuffixCountExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open TwoOppositeLargeExchange
open scoped BigOperators

/-- Maximum of the negative magnitudes, with zero for the empty list. -/
def negativeMax {α : Type*} (f : α → ℤ) : List α → ℤ
  | [] => 0
  | i :: X => max (-f i) (negativeMax f X)

private theorem negativeMax_nonneg {α : Type*} (f : α → ℤ) (X : List α) :
    0 ≤ negativeMax f X := by
  induction X with
  | nil => simp [negativeMax]
  | cons i X ih => exact le_trans ih (le_max_right _ _)

private theorem le_negativeMax {α : Type*} (f : α → ℤ) (X : List α)
    (i : α) (hi : i ∈ X) : -f i ≤ negativeMax f X := by
  revert hi
  induction X with
  | nil => simp
  | cons j X ih =>
    intro hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact le_trans (ih hi) (le_max_right _ _)

private theorem negativeMax_le {α : Type*} (f : α → ℤ) (X : List α) (C : ℤ)
    (hC : 0 ≤ C) (hbound : ∀ i ∈ X, -f i ≤ C) : negativeMax f X ≤ C := by
  revert hbound
  induction X with
  | nil => intro _; exact hC
  | cons i X ih =>
    intro hbound
    exact max_le (hbound i (by simp)) (ih (fun j hj => hbound j (by simp [hj])))

def bad {α : Type*} (f : α → ℤ) (T : List α) (c : ℤ) : List α :=
  T.filter (fun i => decide (c < f i))

def good {α : Type*} (f : α → ℤ) (T : List α) (c : ℤ) : List α :=
  T.filter (fun i => decide (0 < f i ∧ f i ≤ c))

def nonpositive {α : Type*} (f : α → ℤ) (T : List α) : List α :=
  T.filter (fun i => decide (f i ≤ 0))

private theorem count_filter_decide {α : Type*} [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (X : List α) (i : α) :
    (X.filter (fun j => decide (P j))).count i = if P i then X.count i else 0 := by
  by_cases hi : P i
  · simp [hi]
  · rw [ite_eq_right hi]
    exact List.count_eq_zero_of_not_mem (by simp [hi])

/-- Exact physical partition, valid also in the presence of zero weights. -/
private theorem bad_good_nonpositive_partition {α : Type*} (f : α → ℤ)
    (T : List α) (c : ℤ) (hc : 0 ≤ c) :
    (bad f T c ++ good f T c ++ nonpositive f T).Perm T := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  simp only [bad, good, nonpositive, List.count_append, count_filter_decide]
  split_ifs <;> omega

/-- The actual SMALL filter, keeping every physical occurrence. -/
def smallTail (k t : ℕ) (Btail : List (Fin k)) : List (Fin k) :=
  Btail.filter (fun i => decide (|s k t i| < Q k))

/-- The actual negative LARGE filter; it is not a list of numerical values. -/
def negativeLargeTail (k t : ℕ) (Btail : List (Fin k)) : List (Fin k) :=
  Btail.filter (fun i => decide (Q k ≤ -s k t i))

private theorem tail_partition {k t : ℕ} (Btail : List (Fin k))
    (hnegative : ∀ i ∈ Btail, Q k ≤ |s k t i| → s k t i < 0) :
    (smallTail k t Btail ++ negativeLargeTail k t Btail).Perm Btail := by
  have heq : Btail.filter (fun i => !decide (|s k t i| < Q k)) =
      negativeLargeTail k t Btail := by
    apply List.filter_congr
    intro i hi
    by_cases hsmall : |s k t i| < Q k
    · have hn : ¬ Q k ≤ -s k t i := by
        have hh := neg_le_abs (s k t i)
        omega
      simp [hsmall, hn]
    · have hn := hnegative i hi (by omega)
      have hlarge : Q k ≤ -s k t i := by rw [abs_of_neg hn] at hsmall; omega
      simp [hsmall, hlarge]
  simpa only [smallTail, heq] using
    (List.filter_append_perm (fun i => decide (|s k t i| < Q k)) Btail)

set_option maxHeartbeats 1600000 in
/-- The computed strict count of actual Bad SMALL is sufficient for a full
exchange with an arbitrary nonempty all-negative LARGE tail. The constructed
competitor retains every old SMALL and returns exactly the two LARGE labels
`x,j`. No returned subset, new endpoint, ordering resource, minimizer or
availability hypothesis is assumed. -/
theorem actualSource_negativeSuffix_count_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p : Fin k) (A Btail : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (A ++ [hit k 2 p] ++ Btail))
    (hpunused : p ∉ A ++ [hit k 2 p] ++ Btail)
    (hnunused : hit k 1 p ∉ A ++ [hit k 2 p] ++ Btail)
    (hnegative : ∀ i ∈ Btail, Q k ≤ |s k t i| → s k t i < 0)
    (hblocklo : C k - s k t p < mass (s k t) (A ++ [hit k 2 p] ++ Btail))
    (hblockhi : mass (s k t) (A ++ [hit k 2 p] ++ Btail) <
      |s k t (hit k 1 p)|)
    (j : Fin k) (hj : j ∈ negativeLargeTail k t Btail)
    (hbad : (bad (s k t) (smallTail k t Btail)
      (C k - negativeMax (s k t) ((negativeLargeTail k t Btail).erase j))).length <
      (negativeLargeTail k t Btail).length) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := A ++ [x] ++ Btail
    let T := smallTail k t Btail
    let Z := (negativeLargeTail k t Btail).erase j
    let c := C k - negativeMax (s k t) Z
    let Bad := bad (s k t) T c
    let Good := good (s k t) T c
    let Nonpos := nonpositive (s k t) T
    let F := Bad.take 1
    let K := Bad.drop 1 ++ Good ++ Nonpos ++ Z
    let e0 := mass (s k t) W - s k t j - s k t p
    ∃ L : List (Fin k),
      let V := A ++ [p, n] ++ F ++ L
      L.Perm K ∧ (F ++ L ++ [j]).Perm Btail ∧
      F.length ≤ 1 ∧ (∀ i ∈ F, i ∈ Bad) ∧
      (∀ i ∈ Bad, i ∈ F ++ L) ∧
      Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
      (∀ a : ℕ, 0 ≤ mass (s k t) (V.take a) ∧ mass (s k t) (V.take a) ≤ C k) ∧
      Inventory k t W V [p, n] [x, j] ∧
      G k t V = G k t W ∧ U V = U W ∧
      H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t j).natAbs =
        H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs ∧
      H k t V < H k t W ∧ J k t V < J k t W ∧
      0 ≤ c ∧ 0 < e0 ∧ e0 < C k ∧ mass (s k t) V = e0 ∧
      remainingMass (s k t) V = -e0 ∧
      remainingSmall t V = remainingSmall t W := by
  classical
  dsimp only
  let f := s k t
  let n := hit k 1 p
  let x := hit k 2 p
  let W := A ++ [x] ++ Btail
  let P := f p
  let D := |f n|
  let r := |f x|
  let T := smallTail k t Btail
  let Neg := negativeLargeTail k t Btail
  let Z := Neg.erase j
  let Lmax := negativeMax f Z
  let c := C k - Lmax
  let Bad := bad f T c
  let Good := good f T c
  let Nonpos := nonpositive f T
  let a0 := mass f A
  let b := a0 + P - D
  let h := mass f W
  let e0 := h - f j - P
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  have geo := native_geometry hk t p hnlarge hexpand
  have hpabs : |f p| = P := abs_of_pos hpositive
  have hnval : f n = -D := by
    simpa [f, n, D, orient, show ¬ s k t p < 0 by omega] using geo.nValue
  have hxval : f x = r := by
    simpa [f, x, r, orient, show ¬ s k t p < 0 by omega] using geo.xValue
  have hDP : D < P := by
    have hh := geo.strictOrder.1
    change D < |f p| at hh
    simpa only [hpabs] using hh
  have hPr : P < r := by
    have hh := geo.strictOrder.2
    change |f p| < r at hh
    simpa only [hpabs] using hh
  have hD : Q k ≤ D := hnlarge
  have hDP_eq : D = N k - 2 * P := by
    have hh := geo.firstEquation
    change D = N k - 2 * |f p| at hh
    simpa only [hpabs] using hh
  have hr_eq : r = 2 * P - D := by
    have hh := geo.secondEquation
    rw [hpabs] at hh
    change r = 4 * P - N k at hh
    omega
  have hbudget : 2 * P ≤ C k + Q k := by
    have hh := geo.budget
    change 2 * |f p| ≤ C k + Q k at hh
    simpa only [hpabs] using hh
  have hbound (i : Fin k) : |f i| ≤ C k :=
    abs_le.mpr (centered_bounds hN0 hodd _)
  have hrC : r ≤ C k := hbound x
  have hZentry (i : Fin k) (hi : i ∈ Z) : Q k ≤ -f i ∧ -f i ≤ C k := by
    have hm := List.mem_of_mem_erase hi
    have hh : i ∈ Btail ∧ Q k ≤ -f i := by
      simpa only [Neg, negativeLargeTail, List.mem_filter, decide_eq_true_eq, f] using hm
    exact ⟨hh.2, le_trans (neg_le_abs _) (hbound i)⟩
  have hjQ : Q k ≤ -f j := by
    have hh : j ∈ Btail ∧ Q k ≤ -f j := by
      simpa only [negativeLargeTail, List.mem_filter, decide_eq_true_eq, f] using hj
    exact hh.2
  have hjC : -f j ≤ C k := le_trans (neg_le_abs _) (hbound j)
  have hsmall (i : Fin k) (hi : i ∈ T) : |f i| < Q k := by
    have hh : i ∈ Btail ∧ |f i| < Q k := by
      simpa only [T, smallTail, List.mem_filter, decide_eq_true_eq, f] using hi
    exact hh.2
  have hpart := tail_partition Btail hnegative
  change (T ++ Neg).Perm Btail at hpart
  have hZlen : Z.length + 1 = Neg.length := List.length_erase_add_one hj
  have hmax0 : 0 ≤ Lmax := negativeMax_nonneg f Z
  have hmaxC : Lmax ≤ C k := negativeMax_le f Z (C k) (by omega)
    (fun i hi => (hZentry i hi).2)
  have hc0 : 0 ≤ c := by dsimp only [c]; omega
  have hNegpart : (Z ++ [j]).Perm Neg :=
    List.perm_append_comm.trans (List.perm_cons_erase hj).symm
  have hbadpart := bad_good_nonpositive_partition f T c hc0
  change (Bad ++ Good ++ Nonpos).Perm T at hbadpart
  have hBadentry (i : Fin k) (hi : i ∈ Bad) : i ∈ T ∧ c < f i := by
    simpa only [Bad, bad, List.mem_filter, decide_eq_true_eq] using hi
  have hGoodentry (i : Fin k) (hi : i ∈ Good) : i ∈ T ∧ 0 < f i ∧ f i ≤ c := by
    simpa only [Good, good, List.mem_filter, decide_eq_true_eq] using hi
  have hNonposentry (i : Fin k) (hi : i ∈ Nonpos) : i ∈ T ∧ f i ≤ 0 := by
    simpa only [Nonpos, nonpositive, List.mem_filter, decide_eq_true_eq] using hi
  change Bad.length < Neg.length at hbad
  have hsW : InStrip f (C k) 0 W := strip_of_legal hW
  obtain ⟨hsA, hsTail⟩ := strip_split A ([x] ++ Btail)
    (by simpa only [W, List.append_assoc] using hsW)
  have ha0 : 0 ≤ a0 ∧ a0 ≤ C k := by
    simpa [mass, a0] using inStrip_prefix hsTail 0
  have hax : 0 ≤ a0 + r ∧ a0 + r ≤ C k := by
    simpa [mass, a0, hxval] using inStrip_prefix hsTail 1
  have hb : 0 ≤ b ∧ b ≤ C k - P := by dsimp only [b]; omega
  have hbQ : b ≤ Q k - 1 := by omega
  have he0 : 0 < e0 ∧ e0 < C k := by
    change C k - P < h at hblocklo
    change h < D at hblockhi
    dsimp only [e0]
    omega
  have he0mass : b + mass f T + mass f Z = e0 := by
    have ht : mass f T + mass f Neg = mass f Btail := by
      simpa only [mass, List.map_append, List.sum_append] using (hpart.map f).sum_eq
    have hz : mass f Z + f j = mass f Neg := by
      simpa only [mass, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero] using (hNegpart.map f).sum_eq
    have hw : h = a0 + r + mass f Btail := by simp [h, W, a0, mass, hxval, add_assoc]
    dsimp only [b, e0]
    omega
  let F := Bad.take 1
  let K := Bad.drop 1 ++ Good ++ Nonpos ++ Z
  let E : Fin k → Bool := fun i => decide (i ∈ Bad.drop 1)
  have hFbad (i : Fin k) (hi : i ∈ F) : i ∈ Bad := (List.take_sublist 1 Bad).subset hi
  have hFlen : F.length ≤ 1 := by simp only [F, List.length_take]; omega
  have hFmass : 0 ≤ mass f F ∧ mass f F ≤ Q k - 1 := by
    cases hlist : Bad with
    | nil =>
      simpa [F, hlist, mass] using (show 0 ≤ (0 : ℤ) ∧ 0 ≤ Q k - 1 by omega)
    | cons i X =>
      have hi := hBadentry i (by simp [hlist])
      have his := hsmall i hi.1
      have hi0 : 0 < f i := by omega
      rw [abs_of_pos hi0] at his
      simpa [F, hlist, mass] using (show 0 ≤ f i ∧ f i ≤ Q k - 1 by omega)
  have hstart : 0 ≤ b + mass f F ∧ b + mass f F ≤ C k := by omega
  have hsF : InStrip f (C k) b F := by
    cases hlist : Bad with
    | nil => simpa [F, hlist, InStrip] using (show 0 ≤ b ∧ b ≤ C k by omega)
    | cons i X =>
      have hm : mass f F = f i := by simp [F, hlist, mass]
      simpa [F, hlist, InStrip] using
        (show 0 ≤ b ∧ b ≤ C k ∧ 0 ≤ b + f i ∧ b + f i ≤ C k by omega)
  have hFK : (F ++ K).Perm (T ++ Z) := by
    apply List.perm_iff_count.mpr
    intro i
    have hp := hbadpart.count_eq i
    have hb := congrArg (fun X : List (Fin k) => X.count i) (List.take_append_drop 1 Bad)
    simp only [List.count_append] at hp hb
    simp only [F, K, List.count_append]
    omega
  have hTZj : (T ++ Z ++ [j]).Perm Btail := by
    have hp : (T ++ Z ++ [j]).Perm (T ++ Neg) := by
      simpa only [List.append_assoc] using hNegpart.append_left T
    exact hp.trans hpart
  have hKorigin (i : Fin k) (hi : i ∈ K) : i ∈ T ∨ i ∈ Z := by
    simp only [K, List.mem_append] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact Or.inl (hBadentry i ((List.drop_sublist 1 Bad).subset hi)).1
    · exact Or.inl (hGoodentry i hi).1
    · exact Or.inl (hNonposentry i hi).1
    · exact Or.inr hi
  have hKpositive (i : Fin k) (hi : i ∈ K) (hi0 : 0 < f i) :
      i ∈ Bad.drop 1 ∨ i ∈ Good := by
    simp only [K, List.mem_append] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact Or.inl hi
    · exact Or.inr hi
    · have hh := (hNonposentry i hi).2; omega
    · have hh := (hZentry i hi).1; omega
  have hExbound (i : Fin k) (_ : i ∈ K) (hi : E i = true) :
      0 < f i ∧ f i ≤ Q k - 1 := by
    have hi' : i ∈ Bad.drop 1 := of_decide_eq_true hi
    have hh := hBadentry i ((List.drop_sublist 1 Bad).subset hi')
    have hs := hsmall i hh.1
    have hp : 0 < f i := by omega
    rw [abs_of_pos hp] at hs
    exact ⟨hp, by omega⟩
  have hKcompat (i : Fin k) (hi : i ∈ K) (a : Fin k) (ha : a ∈ K)
      (hin : E i = false) (hi0 : 0 < f i) (ha0 : f a < 0) : f i - f a ≤ C k := by
    have hin' : i ∉ Bad.drop 1 := of_decide_eq_false hin
    have hiG := (hKpositive i hi hi0).resolve_left hin'
    have hv := (hGoodentry i hiG).2.2
    rcases hKorigin a ha with haT | haZ
    · have hsi := hsmall i (hGoodentry i hiG).1
      have hsa := hsmall a haT
      rw [abs_of_pos hi0] at hsi
      rw [abs_of_neg ha0] at hsa
      omega
    · have hn := le_negativeMax f Z a haZ
      dsimp only [c] at hv
      omega
  have hEcount : K.countP E = (Bad.drop 1).length := by
    have hBadE : ∀ i ∈ Bad.drop 1, E i = true := by intro i hi; exact decide_eq_true hi
    have hGoodE : ∀ i ∈ Good, E i = false := by
      intro i hi
      have hg := (hGoodentry i hi).2.2
      have hn : i ∉ Bad.drop 1 := by
        intro hh
        have hb := (hBadentry i ((List.drop_sublist 1 Bad).subset hh)).2
        omega
      exact decide_eq_false hn
    have hNonE : ∀ i ∈ Nonpos, E i = false := by
      intro i hi
      have hn := (hNonposentry i hi).2
      have he : i ∉ Bad.drop 1 := by
        intro hh
        have hb := (hBadentry i ((List.drop_sublist 1 Bad).subset hh)).2
        omega
      exact decide_eq_false he
    have hZE : ∀ i ∈ Z, E i = false := by
      intro i hi
      have hn := (hZentry i hi).1
      have he : i ∉ Bad.drop 1 := by
        intro hh
        have hb := (hBadentry i ((List.drop_sublist 1 Bad).subset hh)).2
        omega
      exact decide_eq_false he
    simp only [K, List.countP_append]
    rw [List.countP_eq_length.mpr hBadE, List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hGoodE i hi)),
      List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hNonE i hi)), List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hZE i hi))]
    omega
  have hNcount : K.countP (fun i => decide (f i ≤ -Q k)) = Z.length := by
    have hTnot (i : Fin k) (hi : i ∈ T) : decide (f i ≤ -Q k) = false := by
      have hh := hsmall i hi
      have hn := neg_le_abs (f i)
      simp only [decide_eq_false_iff_not]
      omega
    have hBadN : ∀ i ∈ Bad.drop 1, decide (f i ≤ -Q k) = false := by
      intro i hi; exact hTnot i (hBadentry i ((List.drop_sublist 1 Bad).subset hi)).1
    have hGoodN : ∀ i ∈ Good, decide (f i ≤ -Q k) = false := by
      intro i hi; exact hTnot i (hGoodentry i hi).1
    have hNonN : ∀ i ∈ Nonpos, decide (f i ≤ -Q k) = false := by
      intro i hi; exact hTnot i (hNonposentry i hi).1
    have hZN : ∀ i ∈ Z, decide (f i ≤ -Q k) = true := by
      intro i hi
      have hh := (hZentry i hi).1
      simp only [decide_eq_true_eq]
      omega
    simp only [K, List.countP_append]
    rw [List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hBadN i hi)), List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hGoodN i hi)),
      List.countP_eq_zero.mpr (fun i hi => Bool.eq_false_iff.mp (hNonN i hi)), List.countP_eq_length.mpr hZN]
    omega
  have hsurplus : K.countP E ≠ 0 → K.countP E + 1 ≤
      K.countP (fun i => decide (f i ≤ -Q k)) := by
    rw [hEcount, hNcount, List.length_drop]
    omega
  have hFKmass : mass f F + mass f K = mass f T + mass f Z := by
    simpa only [mass, List.map_append, List.sum_append] using (hFK.map f).sum_eq
  have hsum : b + mass f F + mass f K = e0 := by omega
  obtain ⟨L, hL, hsL, _⟩ := CountSurplusOrdering.exists_order_between f E K (Q k)
    (b + mass f F) e0 hQ (by simpa only [← hC] using hstart)
    (by constructor <;> omega) hsum hExbound
    (by simpa only [← hC] using hKcompat) hsurplus
  rw [← hC] at hsL
  have hmassL : mass f L = mass f K := by simpa only [mass] using (hL.map f).sum_eq
  have hFLj : (F ++ L ++ [j]).Perm Btail := by
    apply List.perm_iff_count.mpr
    intro i
    have hp := hFK.count_eq i
    have hz := hTZj.count_eq i
    have hl := hL.count_eq i
    simp only [List.count_append] at hp hz ⊢
    omega
  have hBadretained (i : Fin k) (hi : i ∈ Bad) : i ∈ F ++ L := by
    have htake : i ∈ Bad.take 1 ∨ i ∈ Bad.drop 1 := by
      rw [← List.mem_append, List.take_append_drop]
      exact hi
    rcases htake with hi | hi
    · exact List.mem_append_left _ hi
    · apply List.mem_append_right
      apply hL.mem_iff.mpr
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi))
  have hsPN : InStrip f (C k) a0 [p, n] := by
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + f p ∧ a0 + f p ≤ C k ∧
      0 ≤ a0 + f p + f n ∧ a0 + f p + f n ≤ C k
    rw [hnval]
    change 0 ≤ a0 ∧ a0 ≤ C k ∧ 0 ≤ a0 + P ∧ a0 + P ≤ C k ∧
      0 ≤ a0 + P + -D ∧ a0 + P + -D ≤ C k
    exact ⟨ha0.1, ha0.2, by omega, by omega, by dsimp only [b] at hb; omega,
      by dsimp only [b] at hb; omega⟩
  have hsAPN : InStrip f (C k) 0 (A ++ [p, n]) :=
    inStrip_append hsA (by simpa only [zero_add, a0, mass] using hsPN)
  have hAPN : mass f (A ++ [p, n]) = b := by
    simp only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, hnval]
    dsimp only [b, a0, P, mass]
    ring
  have hsAPNF : InStrip f (C k) 0 (A ++ [p, n] ++ F) := by
    apply inStrip_append hsAPN
    change InStrip f (C k) (0 + mass f (A ++ [p, n])) F
    rw [zero_add, hAPN]
    exact hsF
  let V := A ++ [p, n] ++ F ++ L
  let Ret := [x, j]
  have hsV : InStrip f (C k) 0 V := by
    apply inStrip_append hsAPNF
    have hpre : mass f (A ++ [p, n] ++ F) = b + mass f F := by
      simp only [mass, List.map_append, List.sum_append] at hAPN ⊢
      omega
    change InStrip f (C k) (0 + mass f (A ++ [p, n] ++ F)) L
    rw [zero_add, hpre]
    exact hsL
  have hEnd : mass f V = e0 := by
    have hm : mass f V = mass f (A ++ [p, n]) + mass f F + mass f L := by
      simp only [V, mass, List.map_append, List.sum_append]
    rw [hm, hAPN, hmassL]
    exact hsum
  have hI : [p, n].Nodup := by
    have hpn : p ≠ n := by intro hh; have hv := congrArg f hh; omega
    simp [hpn]
  have hIW (i : Fin k) (hi : i ∈ [p, n]) : i ∉ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hpunused
    · exact hnunused
  have hIL (i : Fin k) (hi : i ∈ [p, n]) : Large k t i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact geo.pLarge
    · exact geo.nLarge
  have hperm : (V ++ Ret).Perm (W ++ [p, n]) := by
    apply List.perm_iff_count.mpr
    intro i
    have hp := hFLj.count_eq i
    simp only [List.count_append, List.count_cons, List.count_nil] at hp
    simp only [V, Ret, W, List.count_append, List.count_cons, List.count_nil]
    omega
  have hRold (i : Fin k) (hi : i ∈ Ret) : i ∈ W := by
    simp only [Ret, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [W]
    · have hjB := (List.mem_filter.mp hj).1
      simp [W, hjB]
  have inv : Inventory k t W V [p, n] Ret :=
    inventory_of_perm hk t W V [p, n] Ret hW.1 hI hIW hRold hIL hperm
  have hxLarge : Large k t x := geo.xLarge
  have hjLarge : Large k t j := by
    have hh := neg_le_abs (f j)
    unfold Large
    change Q k ≤ |f j|
    omega
  have hRetlarge : largeUsed k t Ret = 2 := by
    simp [Ret, largeUsed, mass, largeWeight, hxLarge, hjLarge]
  have hRetenergy : H k t Ret = 3 ^ (f x).natAbs + 3 ^ (f j).natAbs := by
    simp [Ret, H, mass, energyWeight, hxLarge, hjLarge, f, s]
  have hnLarge : Large k t n := geo.nLarge
  have hIlarge : largeUsed k t [p, n] = 2 := by
    simp [largeUsed, mass, largeWeight, geo.pLarge, hnLarge]
  have hIenergy : H k t [p, n] = 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    simp [H, mass, energyWeight, geo.pLarge, hnLarge, f, s]
  have hG : G k t V = G k t W := by
    have hh := inv.largeBalance
    rw [hRetlarge, hIlarge] at hh
    omega
  have hU : U V = U W := by
    have hh := inv.countBalance
    simp only [Ret, List.length_cons, List.length_nil] at hh
    omega
  have hH : H k t V + 3 ^ (f x).natAbs + 3 ^ (f j).natAbs =
      H k t W + 3 ^ (f p).natAbs + 3 ^ (f n).natAbs := by
    have hh := inv.energyBalance
    rw [hRetenergy, hIenergy] at hh
    omega
  have hHstrict : H k t V < H k t W := by
    have henergy := geo.energy
    change 3 ^ (f p).natAbs + 3 ^ (f n).natAbs < 3 ^ (f x).natAbs at henergy
    have hle : H k t V + 3 ^ (f x).natAbs ≤
        H k t W + (3 ^ (f p).natAbs + 3 ^ (f n).natAbs) := by
      calc
        H k t V + 3 ^ (f x).natAbs ≤
            H k t V + 3 ^ (f x).natAbs + 3 ^ (f j).natAbs := Nat.le_add_right _ _
        _ = H k t W + (3 ^ (f p).natAbs + 3 ^ (f n).natAbs) := by
          simpa only [Nat.add_assoc] using hH
    exact Nat.lt_of_add_lt_add_right
      (lt_of_le_of_lt hle (Nat.add_lt_add_left henergy (H k t W)))
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hHstrict)⟩
  have hRfilter : Ret.toFinset.filter (fun i => ¬ Large k t i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh := (Finset.mem_filter.mp hi)
    have hm : i = x ∨ i = j := by simpa [Ret] using hh.1
    rcases hm with rfl | rfl
    · exact hh.2 hxLarge
    · exact hh.2 hjLarge
  have hsmallPart : remainingSmall t V = remainingSmall t W := by
    simpa only [hRfilter, Finset.union_empty] using inv.smallPartition
  refine ⟨L, hL, hFLj, hFlen, hFbad, hBadretained, legal_of_strip inv.nodup hsV,
    hsV, ?_, inv, hG, hU, hH, hHstrict, hJ, hc0, he0.1, he0.2, hEnd, ?_, hsmallPart⟩
  · intro a
    simpa only [mass, zero_add] using inStrip_prefix hsV a
  · rw [inv.complementSum, hEnd]

end D5.S3.Combinatorics.Circle.NegativeSuffixCountExchange
