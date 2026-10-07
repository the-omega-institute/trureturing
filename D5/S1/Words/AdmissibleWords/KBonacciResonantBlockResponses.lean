/- GID: D5/S1/Words/AdmissibleWords/KBonacciResonantBlockResponses
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciResonantBlockResponses
   mirror-E: none(waiver:symbolic-behavior-classification)
   anchors: []
   utility: none
   digest: Actual resonant block responses have exact signatures and joint reachable fibers. -/

import D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
import D5.S1.Words.AdmissibleWords.KBonacciResonantWindowCounts
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 3000000

namespace D5.S1.Words.AdmissibleWords.KBonacciResonantBlockResponses

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
open D5.S1.Words.AdmissibleWords.KBonacciResonantWindowCounts
open scoped BigOperators

/-- Complete-block controlled responses of the actual original-order Boolean words. -/
theorem kbonacci_resonant_block_responses (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (hg : 2 ≤ Nat.gcd m (k + 1)) :
    letI : ∀ j : ℕ, DecidableEq (Fin j → ZMod 2) :=
      fun _ a b => Fintype.decidablePiFintype a b
    let T := k + 1
    let g := Nat.gcd m T
    let p := T / g
    let z : Fin k := ⟨0, by omega⟩
    let base : PartialDFA Bool (Fin k) :=
      { start := z
        step := fun s x => if x then
          if h : s.val + 1 < k then some ⟨s.val + 1, h⟩ else none
          else some z }
    let run := base.evalFrom
    let c := fun n => (dbonacci k (n + 2) : ZMod 2)
    let P : Finset (ZMod T) := Finset.univ.image (fun θ => (g : ZMod T) * θ)
    let W := fun (j : ℕ) (θ : ZMod T) (i : Fin j) => c (θ.val + i.val)
    let addValue := fun (θ : ZMod T) (w : List Bool) =>
      ∑ i : Fin w.length, if w.get i then c (θ.val + i.val) else 0
    let advance := fun (r : Option (ZMod 2 × ZMod T × Fin k)) (w : List Bool) =>
      r.bind (fun q => (run q.2.2 w).map
        (fun s => (q.1 + addValue q.2.1 w, q.2.1 + (w.length : ZMod T), s)))
    let output := fun r : Option (ZMod 2 × ZMod T × Fin k) => r.map Prod.fst
    let response := fun r w => output (advance r w)
    let source := fun w => advance (some (0, 0, z)) w
    let blocks := fun (locally : Bool) (w : List Bool) =>
      m ∣ w.length ∧ (locally = true → ∀ j : ℕ, j * m < w.length →
        run z ((w.drop (j * m)).take m) ≠ none)
    let records := insert none
      ((Finset.univ.product (P.product Finset.univ)).image
        (fun q : ZMod 2 × ZMod T × Fin k => some q))
    let signature := fun (H : ℕ) (r : Option (ZMod 2 × ZMod T × Fin k)) =>
      r.map (fun q => (q.1,
        if H = 0 then Sum.inl (0, W (m * H) q.2.1)
        else if q.2.2.val = k - 1 then Sum.inr (W (m * H - 1) (q.2.1 + 1))
        else Sum.inl (min (k - q.2.2.val) (m * H + 1), W (m * H) q.2.1)))
    let atMost := fun H locally x y => ∀ w, blocks locally w → w.length ≤ m * H →
      response x w = response y w
    let exactFinal := fun H locally x y => ∀ w, blocks locally w → w.length = m * H →
      response x w = response y w
    let atMostTrajectory := fun H locally x y => ∀ w, blocks locally w →
      w.length ≤ m * H → ∀ j, j * m ≤ w.length →
        response x (w.take (j * m)) = response y (w.take (j * m))
    let exactTrajectory := fun H locally x y => ∀ w, blocks locally w →
      w.length = m * H → ∀ j, j * m ≤ w.length →
        response x (w.take (j * m)) = response y (w.take (j * m))
    (∀ n (w : Fin n → Bool) (s : Fin k),
      (run s (List.ofFn w)).isSome = runAdmissible (k - 1) (k - 1 - s.val) n w) ∧
    (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w ↔
      source (List.ofFn w) ≠ none) ∧
    (∀ n (w : Fin n → Bool), output (source (List.ofFn w)) =
      if DBonacciAdmissible k n w then
        some (∑ i : Fin n, if w i then (dbonacci k (i.val + 2) : ZMod 2) else 0)
      else none) ∧
    (∀ w v θ s, source w = some (v, θ, s) →
      θ = (w.length : ZMod T) ∧ s.val = (w.reverse.takeWhile id).length) ∧
    (∀ θ n, c (θ.val + n) = c ((θ + (n : ZMod T)).val)) ∧
    (∀ v θ s x, advance (some (v, θ, s)) [x] =
      if x then if h : s.val + 1 < k then
        some (v + c θ.val, θ + 1, (⟨s.val + 1, h⟩ : Fin k)) else none
      else some (v, θ + 1, z)) ∧
    (∀ r u v, advance r (u ++ v) = advance (advance r u) v) ∧
    (∀ w, response none w = none) ∧
    (∀ locally r, r ∈ records ↔ ∃ w, blocks locally w ∧ source w = r) ∧
    (∀ locally r, ∃ w, blocks locally w ∧ advance r w = none) ∧
    (∀ H locally x y, atMost H locally x y ↔ signature H x = signature H y) ∧
    (∀ H locally x y,
      (atMost H locally x y ↔ exactFinal H locally x y) ∧
      (atMost H locally x y ↔ atMostTrajectory H locally x y) ∧
      (atMost H locally x y ↔ exactTrajectory H locally x y)) ∧
    (records.image (signature 0)).card = 3 ∧
    (∀ H, 1 ≤ H → (records.image (signature H)).card =
      1 + 2 * (min (m * H) (k - 1) * min p (m * H / g + 2) +
        min p (m * H / g + 1))) := by
  classical
  letI : ∀ j : ℕ, DecidableEq (Fin j → ZMod 2) :=
    fun _ a b => Fintype.decidablePiFintype a b
  intro T g p z base run c P W addValue advance output response source blocks
    records signature atMost exactFinal atMostTrajectory exactTrajectory
  have hsupplier := actual_endpoint_operators (K := ZMod 2) k hk
  have hscan := hsupplier.1
  have hlegal := hsupplier.2.1
  have hnormal := hsupplier.2.2.2.2.1
  have hbad := hsupplier.2.2.2.2.2.1
  clear hsupplier
  have hcounts := kbonacci_resonant_window_counts k m hk hm hg
  have hT : 0 < T := by dsimp [T]; omega
  have hrec : ∀ n, dbonacci k (n + k + 2) =
      ∑ i ∈ Finset.range k, dbonacci k (n + i + 2) := by
    intro n
    rw [dbonacci_add_two_of_le k (n + k) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hslide : ∀ n, dbonacci k (n + k + 1 + 2) + dbonacci k (n + 2) =
      2 * dbonacci k (n + k + 2) := by
    intro n
    have hs := Finset.sum_range_succ' (fun i => dbonacci k (n + i + 2)) k
    rw [Finset.sum_range_succ] at hs
    have hshift : (∑ i ∈ Finset.range k, dbonacci k (n + (i + 1) + 2)) =
        dbonacci k (n + k + 1 + 2) := by
      rw [show n + k + 1 = (n + 1) + k by omega, hrec]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    calc
      _ = (∑ i ∈ Finset.range k, dbonacci k (n + (i + 1) + 2)) +
          dbonacci k (n + 2) := by rw [hshift]
      _ = (∑ i ∈ Finset.range k, dbonacci k (n + i + 2)) +
          dbonacci k (n + k + 2) := hs.symm
      _ = _ := by rw [← hrec]; omega
  have hper : Function.Periodic c T := by
    intro n
    have hs := congrArg (fun a : ℕ => (a : ZMod 2)) (hslide n)
    have hs' : c (n + T) + c n = 0 := by
      simpa [c, T, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, CharTwo.two_eq_zero] using hs
    exact CharTwo.add_eq_zero.mp hs'
  have htransport (θ : ZMod T) (n : ℕ) : c (θ.val + n) = c ((θ + (n : ZMod T)).val) := by
    rw [← hper.map_mod_nat (θ.val + n)]
    congr 1
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  have hnil (s : Fin k) : run s [] = some s := rfl
  have hfalse (s : Fin k) (w : List Bool) : run s (false :: w) = run z w := rfl
  have htrue (s : Fin k) (w : List Bool) : run s (true :: w) =
      if h : s.val + 1 < k then run ⟨s.val + 1, h⟩ w else none := by
    by_cases hs : s.val + 1 < k <;>
      simp [run, PartialDFA.evalFrom, runTransition, base, hs]
  have happ (s : Fin k) (u v : List Bool) : run s (u ++ v) =
      (run s u).bind (fun t => run t v) := base.evalFrom_append s u v
  have hones : ∀ (n : ℕ) (s : Fin k), run s (List.replicate n true) =
      if h : s.val + n < k then some ⟨s.val + n, h⟩ else none := by
    intro n
    induction n with
    | zero => intro s; simp [hnil, s.isLt]
    | succ n ih =>
      intro s
      rw [List.replicate_succ, htrue]
      by_cases hs : s.val + 1 < k
      · rw [dif_pos hs, ih]
        by_cases ht : s.val + (n + 1) < k
        · have hh : s.val + 1 + n < k := by omega
          simp only [Fin.val_mk, dif_pos hh, dif_pos ht, Option.some.injEq, Fin.mk.injEq]
          omega
        · have hh : ¬s.val + 1 + n < k := by omega
          simp only [Fin.val_mk, dif_neg hh, dif_neg ht]
      · have hh : ¬s.val + (n + 1) < k := by omega
        rw [dif_neg hs, dif_neg hh]
  have hzeros : ∀ n (s : Fin k), 0 < n → run s (List.replicate n false) = some z := by
    intro n
    induction n with
    | zero => intro s hn; omega
    | succ n ih =>
      intro s _
      rw [List.replicate_succ, hfalse]
      cases n with
      | zero => rfl
      | succ n => exact ih z (by omega)
  have hshift (θ : ZMod T) (n : ℕ) : c (θ.val + (n + 1)) = c ((θ + 1).val + n) := by
    rw [htransport, htransport]
    congr 2
    push_cast
    ring
  have hvalue_cons (θ : ZMod T) (x : Bool) (w : List Bool) :
      addValue θ (x :: w) = (if x then c θ.val else 0) + addValue (θ + 1) w := by
    simp only [addValue, List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem,
      Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hshift]
  have hvalue_nil (θ : ZMod T) : addValue θ [] = 0 := by simp [addValue]
  have hvalue_zeros (θ : ZMod T) (n : ℕ) : addValue θ (List.replicate n false) = 0 := by
    simp [addValue]
  have hvalue_append (θ : ZMod T) (u v : List Bool) :
      addValue θ (u ++ v) = addValue θ u + addValue (θ + (u.length : ZMod T)) v := by
    induction u generalizing θ with
    | nil => simp [hvalue_nil]
    | cons x u ih =>
      rw [List.cons_append, hvalue_cons, ih, hvalue_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      have he : (θ + 1) + (u.length : ZMod T) = θ + ((u.length : ZMod T) + 1) := by ring
      rw [he]
      exact (add_assoc _ _ _).symm
  have hadvance_append (r : Option (ZMod 2 × ZMod T × Fin k)) (u v : List Bool) :
      advance r (u ++ v) = advance (advance r u) v := by
    cases r with
    | none => rfl
    | some q =>
      rcases q with ⟨a, θ, s⟩
      simp only [advance, Option.bind_some, happ]
      cases hru : run s u with
      | none => simp [hru]
      | some t =>
        simp only [Option.bind_some, Option.map_some]
        cases hrv : run t v with
        | none => simp
        | some t' =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          rw [hvalue_append, List.length_append, Nat.cast_add]
          constructor
          · exact (add_assoc _ _ _).symm
          · exact ⟨(add_assoc _ _ _).symm, trivial⟩
  have hfactor (u v w : List Bool) (hw : run z (u ++ v ++ w) ≠ none) : run z v ≠ none := by
    intro hv
    apply hw
    rw [List.append_assoc, happ]
    cases hru : run z u with
    | none => rfl
    | some s =>
      simp only [Option.bind_some]
      have hh : run s v = none := hbad v hv s
      rw [happ, hh]
      rfl
  have hslice (w : List Bool) (hw : run z w ≠ none) (a n : ℕ) :
      run z ((w.drop a).take n) ≠ none := by
    apply hfactor (w.take a) ((w.drop a).take n) ((w.drop a).drop n)
    simpa only [List.append_assoc, List.take_append_drop] using hw
  have hblocks_legal (locally : Bool) (w : List Bool) (hd : m ∣ w.length)
      (hw : run z w ≠ none) : blocks locally w :=
    ⟨hd, fun _ j _ => hslice w hw (j * m) m⟩
  have hblocks_nil (locally : Bool) : blocks locally [] := by simp [blocks]
  have hresponse_nil (r : Option (ZMod 2 × ZMod T × Fin k)) : response r [] = output r := by
    cases r with
    | none => rfl
    | some q => simp [response, output, advance, hnil, hvalue_nil]
  have hresponse_live (v : ZMod 2) (θ : ZMod T) (s : Fin k) (w : List Bool) :
      response (some (v, θ, s)) w = if run s w = none then none else some (v + addValue θ w) := by
    cases hr : run s w <;> simp [response, output, advance, hr]
  have hresponse_zeros (r : Option (ZMod 2 × ZMod T × Fin k)) (n : ℕ) :
      response r (List.replicate n false) = output r := by
    cases r with
    | none => rfl
    | some q =>
      rcases q with ⟨v, θ, s⟩
      cases n with
      | zero => exact hresponse_nil _
      | succ n =>
        rw [hresponse_live, hzeros (n + 1) s (by omega), hvalue_zeros]
        simp [output]
  have hresponse_pad (r : Option (ZMod 2 × ZMod T × Fin k)) (w : List Bool) (n : ℕ) :
      response r (w ++ List.replicate n false) = response r w := by
    change output (advance r (w ++ List.replicate n false)) = output (advance r w)
    rw [hadvance_append]
    exact hresponse_zeros (advance r w) n
  have hzero_legal (n : ℕ) : run z (List.replicate n false) ≠ none := by
    cases n with
    | zero => simp [hnil]
    | succ n => rw [hzeros (n + 1) z (by omega)]; simp
  have hblocks_pad (locally : Bool) (w : List Bool) (hw : blocks locally w) (n : ℕ)
      (hn : m ∣ n) : blocks locally (w ++ List.replicate n false) := by
    refine ⟨by simpa using Nat.dvd_add hw.1 hn, ?_⟩
    intro hl j hj
    by_cases hbefore : j * m < w.length
    · have hfit : j * m + m ≤ w.length := by
        obtain ⟨q, hq⟩ := hw.1
        have hjq : j < q := by nlinarith
        nlinarith
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
      · exact hw.2 hl j hbefore
      · simp only [List.length_drop]
        omega
    · rw [List.drop_append]
      rw [List.drop_eq_nil_of_le (by omega : w.length ≤ j * m)]
      simp only [List.nil_append]
      simp only [List.drop_replicate, List.take_replicate]
      exact hzero_legal _
  have hblocks_prefix (locally : Bool) (w : List Bool) (hw : blocks locally w)
      (j : ℕ) (hj : j * m ≤ w.length) : blocks locally (w.take (j * m)) := by
    refine ⟨by simp [List.length_take, min_eq_left hj], ?_⟩
    intro hl i hi
    have hi' : i * m < w.length := by
      have := List.length_take_le (j * m) w
      omega
    have hij : i < j := by
      simp only [List.length_take, min_eq_left hj] at hi
      nlinarith
    have hprod : i * m + m ≤ j * m := by nlinarith
    have hfit : m ≤ j * m - i * m := by omega
    rw [List.drop_take, List.take_take, min_eq_left hfit]
    exact hw.2 hl i hi'
  have hvalue_ofFn (n : ℕ) (w : Fin n → Bool) :
      addValue 0 (List.ofFn w) = ∑ i : Fin n, if w i then c i.val else 0 := by
    dsimp only [addValue]
    apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := w))) _ _
    intro i
    simp [List.get_eq_getElem, List.getElem_ofFn]
    rfl
  have hsource_legal (n : ℕ) (w : Fin n → Bool) :
      DBonacciAdmissible k n w ↔ source (List.ofFn w) ≠ none := by
    simpa [source, advance] using hlegal n w
  have hsource_output (n : ℕ) (w : Fin n → Bool) :
      output (source (List.ofFn w)) =
        if DBonacciAdmissible k n w then some (∑ i : Fin n, if w i then c i.val else 0)
        else none := by
    change response (some (0, 0, z)) (List.ofFn w) = _
    rw [hresponse_live, hvalue_ofFn]
    by_cases hr : run z (List.ofFn w) = none
    · have hn : ¬ DBonacciAdmissible k n w := by
        intro ha
        exact ((hlegal n w).mp ha) hr
      simp [hr, hn]
    · have ha : DBonacciAdmissible k n w := (hlegal n w).mpr hr
      simp [hr, ha]
  have hbit (v : ZMod 2) (θ : ZMod T) (s : Fin k) (x : Bool) :
      advance (some (v, θ, s)) [x] =
        if x then if h : s.val + 1 < k then
          some (v + c θ.val, θ + 1, (⟨s.val + 1, h⟩ : Fin k)) else none
        else some (v, θ + 1, z) := by
    cases x <;> by_cases hs : s.val + 1 < k <;>
      simp [advance, htrue, hfalse, hnil, hvalue_cons, hvalue_nil, hs]
  have haccept (b : ℕ) (s t : Fin k) (w : List Bool) (hw : w.length ≤ b)
      (hτ : min (k - s.val) (b + 1) = min (k - t.val) (b + 1)) :
      (run s w = none ↔ run t w = none) := by
    by_cases hb : run z w = none
    · have hs : run s w = none := hbad w hb s
      have ht : run t w = none := hbad w hb t
      simp [hs, ht]
    · by_cases hz : false ∈ w
      · obtain ⟨a, u, _, _, hlen, hr, _⟩ := hnormal w hz hb
        have hr' (r : Fin k) : run r w = if r.val + a.val < k then some u else none := hr r
        have he : (s.val + a.val < k) ↔ (t.val + a.val < k) := by
          have hs := s.isLt
          have ht := t.isLt
          omega
        rw [hr', hr']
        simp only [ite_eq_right_iff, Option.some_ne_none, imp_false]
        exact not_congr he
      · have he : w = List.replicate w.length true := by
          apply List.eq_replicate_length.mpr
          intro x hx
          cases x with
          | false => exact False.elim (hz hx)
          | true => rfl
        rw [he, hones, hones]
        have ha : (s.val + w.length < k) ↔ (t.val + w.length < k) := by
          have hs := s.isLt
          have ht := t.isLt
          omega
        simp only [dite_eq_right_iff, Option.some_ne_none, imp_false]
        exact not_congr ha
  have hvalue_window (b : ℕ) (θ φ : ZMod T) (w : List Bool) (hw : w.length ≤ b)
      (he : W b θ = W b φ) : addValue θ w = addValue φ w := by
    apply Finset.sum_congr rfl
    intro i _
    have hc := congrFun he (⟨i.val, by have := i.isLt; omega⟩ : Fin b)
    change c (θ.val + i.val) = c (φ.val + i.val) at hc
    simp only [hc]
  have hnonterminal_suff (b : ℕ) (v : ZMod 2) (θ φ : ZMod T) (s t : Fin k)
      (hτ : min (k - s.val) (b + 1) = min (k - t.val) (b + 1))
      (hW : W b θ = W b φ) (w : List Bool) (hw : w.length ≤ b) :
      response (some (v, θ, s)) w = response (some (v, φ, t)) w := by
    rw [hresponse_live, hresponse_live, hvalue_window b θ φ w hw hW]
    have he := haccept b s t w hw hτ
    by_cases hs : run s w = none
    · rw [if_pos hs, if_pos (he.mp hs)]
    · rw [if_neg hs, if_neg (fun ht => hs (he.mpr ht))]
  have hterminal_suff (b : ℕ) (v : ZMod 2) (θ φ : ZMod T) (s t : Fin k)
      (hs : s.val = k - 1) (ht : t.val = k - 1)
      (hW : W (b - 1) (θ + 1) = W (b - 1) (φ + 1))
      (w : List Bool) (hw : w.length ≤ b) :
      response (some (v, θ, s)) w = response (some (v, φ, t)) w := by
    cases w with
    | nil => simp [hresponse_nil, output]
    | cons x w =>
      cases x with
      | true =>
        have hs' : ¬ s.val + 1 < k := by omega
        have ht' : ¬ t.val + 1 < k := by omega
        simp [hresponse_live, htrue, hs', ht']
      | false =>
        have hlen : w.length ≤ b - 1 := by simp only [List.length_cons] at hw; omega
        simp only [hresponse_live, hfalse, hvalue_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
        rw [hvalue_window (b - 1) (θ + 1) (φ + 1) w hlen hW]
  let pulse := fun n j => List.replicate j false ++ true :: List.replicate (n - j - 1) false
  have hpulse_length (n j : ℕ) (hj : j < n) : (pulse n j).length = n := by
    simp only [pulse, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hpulse_run (n j : ℕ) (s : Fin k) (hj : j < n)
      (hs : s.val + 1 < k ∨ 0 < j) : run s (pulse n j) ≠ none := by
    dsimp only [pulse]
    rw [happ]
    by_cases hj0 : j = 0
    · subst j
      simp only [List.replicate_zero, hnil, Option.bind_some]
      have hsafe : s.val + 1 < k := by omega
      rw [htrue, dif_pos hsafe]
      cases htail : n - 0 - 1 with
      | zero => simp [hnil]
      | succ q => rw [hzeros (q + 1) _ (by omega)]; simp
    · rw [hzeros j s (by omega)]
      simp only [Option.bind_some]
      rw [htrue, dif_pos (by dsimp [z]; omega)]
      cases htail : n - j - 1 with
      | zero => simp [hnil]
      | succ q => rw [hzeros (q + 1) _ (by omega)]; simp
  have hpulse_value (n j : ℕ) (θ : ZMod T) (hj : j < n) :
      addValue θ (pulse n j) = c (θ.val + j) := by
    dsimp only [pulse]
    rw [hvalue_append, hvalue_zeros, hvalue_cons, hvalue_zeros]
    simp only [List.length_replicate, zero_add, add_zero, ↓reduceIte]
    exact (htransport θ j).symm
  have hpulse_response (n j : ℕ) (v : ZMod 2) (θ : ZMod T) (s : Fin k)
      (hj : j < n) (hs : s.val + 1 < k ∨ 0 < j) :
      response (some (v, θ, s)) (pulse n j) = some (v + c (θ.val + j)) := by
    rw [hresponse_live, if_neg (hpulse_run n j s hj hs), hpulse_value n j θ hj]
  have hpulse_blocks (locally : Bool) (H j : ℕ) (hj : j < m * H) :
      blocks locally (pulse (m * H) j) := by
    apply hblocks_legal
    · rw [hpulse_length _ _ hj]
      exact dvd_mul_right m H
    · exact hpulse_run _ _ z hj (Or.inl (by dsimp [z]; omega))
  have hblocks_append (locally : Bool) (u v : List Bool) (hu : blocks locally u)
      (hv : blocks locally v) : blocks locally (u ++ v) := by
    refine ⟨by simpa using Nat.dvd_add hu.1 hv.1, ?_⟩
    intro hl j hj
    by_cases hbefore : j * m < u.length
    · have hfit : j * m + m ≤ u.length := by
        obtain ⟨q, hq⟩ := hu.1
        have hjq : j < q := by nlinarith
        nlinarith
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
      · exact hu.2 hl j hbefore
      · simp only [List.length_drop]
        omega
    · obtain ⟨q, hq⟩ := hu.1
      have hafter : u.length ≤ j * m := by omega
      have he : j * m - u.length = (j - q) * m := by
        rw [Nat.sub_mul, hq, Nat.mul_comm m q]
      rw [List.drop_append, List.drop_eq_nil_of_le hafter, List.nil_append, he]
      apply hv.2 hl (j - q)
      simp only [List.length_append] at hj
      rw [← he]
      omega
  have hpartitions (H : ℕ) (locally : Bool) (x y : Option (ZMod 2 × ZMod T × Fin k)) :
      (atMost H locally x y ↔ exactFinal H locally x y) ∧
      (atMost H locally x y ↔ atMostTrajectory H locally x y) ∧
      (atMost H locally x y ↔ exactTrajectory H locally x y) := by
    have hex : atMost H locally x y ↔ exactFinal H locally x y := by
      constructor
      · intro he w hw hl
        exact he w hw hl.le
      · intro he w hw hl
        have hn : m ∣ m * H - w.length := Nat.dvd_sub (dvd_mul_right m H) hw.1
        have hp := hblocks_pad locally w hw (m * H - w.length) hn
        have hlen : (w ++ List.replicate (m * H - w.length) false).length = m * H := by
          simp only [List.length_append, List.length_replicate]
          omega
        have hh := he _ hp hlen
        simpa only [hresponse_pad] using hh
    have htraj : atMost H locally x y ↔ atMostTrajectory H locally x y := by
      constructor
      · intro he w hw hl j hj
        exact he (w.take (j * m)) (hblocks_prefix locally w hw j hj)
          (by simp [List.length_take, min_eq_left hj]; omega)
      · intro he w hw hl
        have hlen : (w.length / m) * m = w.length := Nat.div_mul_cancel hw.1
        have hh := he w hw hl (w.length / m) hlen.le
        simpa only [hlen, List.take_length] using hh
    refine ⟨hex, htraj, ?_⟩
    constructor
    · intro he w hw hl j hj
      exact (htraj.mp he) w hw hl.le j hj
    · intro he
      apply hex.mpr
      intro w hw hl
      have hj : H * m = w.length := by rw [Nat.mul_comm]; exact hl.symm
      have hh := he w hw hl H hj.le
      simpa only [hj, List.take_length] using hh
  have hresponse_none (v : ZMod 2) (θ : ZMod T) (s : Fin k) (w : List Bool) :
      response (some (v, θ, s)) w = none ↔ run s w = none := by
    rw [hresponse_live]
    by_cases hr : run s w = none <;> simp [hr]
  have hinitial (n a : ℕ) (s : Fin k) :
      run s (List.replicate a true ++ List.replicate (n - a) false) = none ↔ k ≤ s.val + a := by
    rw [happ, hones]
    by_cases hs : s.val + a < k
    · rw [dif_pos hs]
      simp only [Option.bind_some]
      have hn : ¬ k ≤ s.val + a := by omega
      cases htail : n - a with
      | zero => simp [hnil, hn]
      | succ q => rw [hzeros (q + 1) _ (by omega)]; simp [hn]
    · rw [dif_neg hs]
      simp [Nat.le_of_not_gt hs]
  have hordered_threshold (H : ℕ) (locally : Bool) (v u : ZMod 2) (θ φ : ZMod T)
      (s t : Fin k) (he : atMost H locally (some (v, θ, s)) (some (u, φ, t)))
      (hneq : min (k - s.val) (m * H + 1) ≠ min (k - t.val) (m * H + 1))
      (hlt : s.val < t.val) : False := by
    let a := k - t.val
    have hb : a ≤ m * H := by have := s.isLt; have := t.isLt; dsimp [a]; omega
    have ha : a < k := by have := t.isLt; dsimp [a]; omega
    let w := List.replicate a true ++ List.replicate (m * H - a) false
    have hlen : w.length = m * H := by simp [w]; omega
    have hlegalw : run z w ≠ none := by
      simp only [ne_eq, w, hinitial]
      dsimp [z]
      omega
    have hw : blocks locally w := hblocks_legal locally w (by rw [hlen]; exact dvd_mul_right m H) hlegalw
    have hr := he w hw hlen.le
    have ht : response (some (u, φ, t)) w = none := by
      apply (hresponse_none _ _ _ _).mpr
      rw [hinitial]
      dsimp [a]
      have := t.isLt
      omega
    have hs : response (some (v, θ, s)) w ≠ none := by
      simp only [ne_eq, hresponse_none, w, hinitial]
      dsimp [a]
      have := t.isLt
      omega
    exact hs (hr.trans ht)
  have hthreshold_necessary (H : ℕ) (locally : Bool) (v u : ZMod 2) (θ φ : ZMod T)
      (s t : Fin k) (he : atMost H locally (some (v, θ, s)) (some (u, φ, t))) :
      min (k - s.val) (m * H + 1) = min (k - t.val) (m * H + 1) := by
    by_contra hneq
    rcases lt_trichotomy s.val t.val with hlt | heq | hgt
    · exact hordered_threshold H locally v u θ φ s t he hneq hlt
    · exact hneq (by rw [heq])
    · exact hordered_threshold H locally u v φ θ t s
        (fun w hw hl => (he w hw hl).symm) (Ne.symm hneq) hgt
  have hpulse_terminal (n : ℕ) (s : Fin k) (hs : s.val = k - 1) : run s (pulse n 0) = none := by
    dsimp only [pulse]
    simp only [List.replicate_zero, List.nil_append]
    rw [htrue, dif_neg (by omega)]
  have htag_necessary (H : ℕ) (hH : 1 ≤ H) (locally : Bool) (v u : ZMod 2)
      (θ φ : ZMod T) (s t : Fin k)
      (he : atMost H locally (some (v, θ, s)) (some (u, φ, t))) :
      (s.val = k - 1 ↔ t.val = k - 1) := by
    have hb : 0 < m * H := by positivity
    have hh := he (pulse (m * H) 0) (hpulse_blocks locally H 0 hb)
      (hpulse_length _ _ hb).le
    constructor
    · intro hs
      by_contra ht
      have hsafe : t.val + 1 < k := by have := t.isLt; omega
      have hleft : response (some (v, θ, s)) (pulse (m * H) 0) = none :=
        (hresponse_none _ _ _ _).mpr (hpulse_terminal _ s hs)
      have hright : response (some (u, φ, t)) (pulse (m * H) 0) ≠ none := by
        simp only [ne_eq, hresponse_none]
        exact hpulse_run _ _ t hb (Or.inl hsafe)
      exact hright (hh.symm.trans hleft)
    · intro ht
      by_contra hs
      have hsafe : s.val + 1 < k := by have := s.isLt; omega
      have hright : response (some (u, φ, t)) (pulse (m * H) 0) = none :=
        (hresponse_none _ _ _ _).mpr (hpulse_terminal _ t ht)
      have hleft : response (some (v, θ, s)) (pulse (m * H) 0) ≠ none := by
        simp only [ne_eq, hresponse_none]
        exact hpulse_run _ _ s hb (Or.inl hsafe)
      exact hleft (hh.trans hright)
  have hempty (θ φ : ZMod T) : W 0 θ = W 0 φ := by
    funext i
    exact Fin.elim0 i
  have hzero_signature (x y : Option (ZMod 2 × ZMod T × Fin k)) :
      signature 0 x = signature 0 y ↔ output x = output y := by
    cases x with
    | none => cases y <;> simp [signature, output]
    | some a =>
      rcases a with ⟨v, θ, s⟩
      cases y with
      | none => simp [signature, output]
      | some a =>
        rcases a with ⟨u, φ, t⟩
        simp [signature, output, hempty θ φ]
  have hclassification (H : ℕ) (locally : Bool) (x y : Option (ZMod 2 × ZMod T × Fin k)) :
      atMost H locally x y ↔ signature H x = signature H y := by
    by_cases hH : H = 0
    · subst H
      rw [hzero_signature]
      constructor
      · intro he
        simpa only [hresponse_nil] using he [] (hblocks_nil locally) (by simp)
      · intro he w _ hw
        have hz : w = [] := List.length_eq_zero_iff.mp (by omega)
        simpa only [hz, hresponse_nil] using he
    · have hH' : 1 ≤ H := by omega
      constructor
      · intro he
        have hcur : output x = output y := by
          simpa only [hresponse_nil] using he [] (hblocks_nil locally) (by simp)
        cases x with
        | none =>
          cases y with
          | none => rfl
          | some q => simp [output] at hcur
        | some q =>
          rcases q with ⟨v, θ, s⟩
          cases y with
          | none => simp [output] at hcur
          | some q =>
            rcases q with ⟨u, φ, t⟩
            have hv : v = u := by simpa [output] using hcur
            subst u
            have ht := htag_necessary H hH' locally v v θ φ s t he
            by_cases hs : s.val = k - 1
            · have ht' := ht.mp hs
              have hW : W (m * H - 1) (θ + 1) = W (m * H - 1) (φ + 1) := by
                funext i
                have hj : i.val + 1 < m * H := by have := i.isLt; omega
                have hh := he (pulse (m * H) (i.val + 1)) (hpulse_blocks locally H _ hj)
                  (hpulse_length _ _ hj).le
                rw [hpulse_response _ _ v θ s hj (Or.inr (by omega)),
                  hpulse_response _ _ v φ t hj (Or.inr (by omega))] at hh
                have hc := add_left_cancel (Option.some.inj hh)
                simpa only [W, hshift] using hc
              simp [signature, hH, hs, ht', hW]
            · have ht' : t.val ≠ k - 1 := fun hh => hs (ht.mpr hh)
              have hτ := hthreshold_necessary H locally v v θ φ s t he
              have hW : W (m * H) θ = W (m * H) φ := by
                funext i
                have hsafeS : s.val + 1 < k := by have := s.isLt; omega
                have hsafeT : t.val + 1 < k := by have := t.isLt; omega
                have hh := he (pulse (m * H) i.val) (hpulse_blocks locally H _ i.isLt)
                  (hpulse_length _ _ i.isLt).le
                rw [hpulse_response _ _ v θ s i.isLt (Or.inl hsafeS),
                  hpulse_response _ _ v φ t i.isLt (Or.inl hsafeT)] at hh
                exact add_left_cancel (Option.some.inj hh)
              simp [signature, hH, hs, ht', hτ, hW]
      · intro he
        cases x with
        | none =>
          cases y with
          | none => intro w _ _; rfl
          | some q => simp [signature] at he
        | some q =>
          rcases q with ⟨v, θ, s⟩
          cases y with
          | none => simp [signature] at he
          | some q =>
            rcases q with ⟨u, φ, t⟩
            simp only [signature, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
            have hv := he.1
            subst u
            by_cases hs : s.val = k - 1 <;> by_cases ht : t.val = k - 1
            · have hW : W (m * H - 1) (θ + 1) = W (m * H - 1) (φ + 1) := by
                simpa [hH, hs, ht] using he.2
              intro w _ hw
              exact hterminal_suff (m * H) v θ φ s t hs ht hW w hw
            · simp [hH, hs, ht] at he
            · simp [hH, hs, ht] at he
            · have hh : min (k - s.val) (m * H + 1) = min (k - t.val) (m * H + 1) ∧
                  W (m * H) θ = W (m * H) φ := by simpa [hH, hs, ht] using he.2
              intro w _ hw
              exact hnonterminal_suff (m * H) v θ φ s t hh.1 hh.2 w hw
  have hrejection (locally : Bool) (r : Option (ZMod 2 × ZMod T × Fin k)) :
      ∃ w, blocks locally w ∧ advance r w = none := by
    let top : Fin k := ⟨k - 1, by omega⟩
    let u := List.replicate (m * k - (k - 1)) false ++ List.replicate (k - 1) true
    have hn : 0 < m * k - (k - 1) := by
      have hmk : k ≤ m * k := by simpa using Nat.mul_le_mul_right k hm
      omega
    have hlen : u.length = m * k := by simp [u]; omega
    have hrun (s : Fin k) : run s u = some top := by
      dsimp only [u]
      rw [happ, hzeros _ s hn]
      simp only [Option.bind_some]
      rw [hones]
      simp [z, top, show k - 1 < k by omega]
    have hu : blocks locally u := hblocks_legal locally u
      (by rw [hlen]; exact dvd_mul_right m k) (by rw [hrun]; simp)
    have hv : blocks locally (pulse m 0) := by
      simpa only [Nat.mul_one] using hpulse_blocks locally 1 0 (by omega)
    refine ⟨u ++ pulse m 0, hblocks_append locally u _ hu hv, ?_⟩
    cases r with
    | none => rfl
    | some q =>
      rcases q with ⟨v, θ, s⟩
      simp only [advance, Option.bind_some, happ, hrun, Option.bind_some]
      rw [hpulse_terminal m top rfl]
      rfl
  have hPzero : (0 : ZMod T) ∈ P := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
  have hphase_div (θ : ZMod T) (hθ : θ ∈ P) : g ∣ θ.val := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hθ
    subst θ
    have he : ((g * a.val : ℕ) : ZMod T) = (g : ZMod T) * a := by simp [Nat.cast_mul]
    rw [← he, ZMod.val_natCast]
    exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right m T)).mpr (dvd_mul_right g a.val)
  have hc0 : c 0 = 1 := by
    simp [c, dbonacci_add_two_of_lt k 0 (by omega)]
  have hjoint (locally : Bool) (v : ZMod 2) (θ : ZMod T) (s : Fin k) (hθ : θ ∈ P) :
      ∃ w, blocks locally w ∧ source w = some (v, θ, s) := by
    have hcompat : Nat.ModEq (Nat.gcd m T) 0 θ.val :=
      (Nat.modEq_zero_iff_dvd.mpr (hphase_div θ hθ)).symm
    let crt := Nat.chineseRemainder' hcompat
    let N := crt.val + m * T * (s.val + 2)
    have hMT : 1 ≤ m * T := by
      have hp : 0 < m * T := Nat.mul_pos (by omega) hT
      omega
    have hbig : s.val + 2 ≤ N := by
      have hh := Nat.mul_le_mul_right (s.val + 2) hMT
      simp only [one_mul] at hh
      dsimp [N]
      omega
    have hNm : m ∣ N := by
      exact Nat.dvd_add (Nat.modEq_zero_iff_dvd.mp crt.prop.1)
        ⟨T * (s.val + 2), by ring⟩
    have hNθ : (N : ZMod T) = θ := by
      calc
        _ = (crt.val : ZMod T) := by simp [N, Nat.cast_add, Nat.cast_mul]
        _ = (θ.val : ZMod T) := (ZMod.natCast_eq_natCast_iff' _ _ T).mpr crt.prop.2
        _ = θ := ZMod.natCast_zmod_val θ
    let t := N - s.val
    have ht : 2 ≤ t := by dsimp [t]; omega
    let tailValue := addValue (t : ZMod T) (List.replicate s.val true)
    let a := v - tailValue
    have ha : a = 0 ∨ a = 1 := by
      have hv : a.val < 2 := ZMod.val_lt a
      have hc : a.val = 0 ∨ a.val = 1 := by omega
      rcases hc with hc | hc
      · left
        rw [← ZMod.natCast_zmod_val a, hc]
        rfl
      · right
        rw [← ZMod.natCast_zmod_val a, hc]
        rfl
    let bit := decide (a = 1)
    have hbitvalue : (if bit then (1 : ZMod 2) else 0) = a := by
      rcases ha with ha | ha <;> simp [bit, ha]
    let preword := bit :: List.replicate (t - 1) false
    let w := preword ++ List.replicate s.val true
    have hprefix_length : preword.length = t := by simp [preword]; omega
    have hprefix_run : run z preword = some z := by
      dsimp only [preword]
      cases hb : bit with
      | false => rw [hfalse, hzeros _ z (by omega)]
      | true => rw [htrue, dif_pos (by dsimp [z]; omega), hzeros _ _ (by omega)]
    have hrun : run z w = some s := by
      dsimp only [w]
      rw [happ, hprefix_run]
      simp only [Option.bind_some]
      rw [hones]
      simp [z, s.isLt]
    have hlength : w.length = N := by
      simp only [w, List.length_append, List.length_replicate, hprefix_length]
      dsimp [t]
      omega
    have hprefix_value : addValue 0 preword = if bit then (1 : ZMod 2) else 0 := by
      dsimp only [preword]
      rw [hvalue_cons, hvalue_zeros]
      simp [hc0]
    have hvalue : addValue 0 w = v := by
      dsimp only [w]
      rw [hvalue_append, hprefix_value, hprefix_length, hbitvalue]
      simp only [zero_add]
      change (v - tailValue) + tailValue = v
      ring
    refine ⟨w, hblocks_legal locally w (by rw [hlength]; exact hNm) (by rw [hrun]; simp), ?_⟩
    simp only [source, advance, Option.bind_some, hrun, Option.map_some, zero_add]
    rw [hvalue, hlength, hNθ]
  have hsource_range (locally : Bool) (r : Option (ZMod 2 × ZMod T × Fin k)) :
      r ∈ records ↔ ∃ w, blocks locally w ∧ source w = r := by
    constructor
    · intro hr
      cases r with
      | none => exact hrejection locally (some (0, 0, z))
      | some q =>
        rcases q with ⟨v, θ, s⟩
        have hθ : θ ∈ P := by simpa [records] using hr
        exact hjoint locally v θ s hθ
    · rintro ⟨w, hw, rfl⟩
      cases hr : run z w with
      | none => simp [source, advance, hr, records]
      | some s =>
        have hd : g ∣ w.length := (Nat.gcd_dvd_left m T).trans hw.1
        have hθ : (w.length : ZMod T) ∈ P := by
          apply Finset.mem_image.mpr
          refine ⟨(w.length / g : ZMod T), Finset.mem_univ _, ?_⟩
          rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
        simp [source, advance, hr, records, hθ]
  have hsource_record (w : List Bool) (v : ZMod 2) (θ : ZMod T) (s : Fin k)
      (hw : source w = some (v, θ, s)) :
      θ = (w.length : ZMod T) ∧ s.val = (w.reverse.takeWhile id).length := by
    cases hr : run z w with
    | none => simp [source, advance, hr] at hw
    | some t =>
      have he : (addValue 0 w, (w.length : ZMod T), t) = (v, θ, s) := by
        simpa [source, advance, hr] using hw
      have hθ := congrArg (fun q : ZMod 2 × ZMod T × Fin k => q.2.1) he
      have hts := congrArg (fun q : ZMod 2 × ZMod T × Fin k => q.2.2) he
      dsimp only [Prod.fst, Prod.snd] at hθ hts
      subst t
      refine ⟨hθ.symm, ?_⟩
      by_cases hz : false ∈ w
      · have hnot : run z w ≠ none := by rw [hr]; simp
        obtain ⟨a, u, _, htail, _, hnormalRun, _⟩ := hnormal w hz hnot
        have hu : run z w = some u := by
          exact (hnormalRun z).trans (if_pos (by dsimp [z]; simpa using a.isLt))
        have hus : u = s := Option.some.inj (hu.symm.trans hr)
        subst u
        exact htail.symm
      · have he : w = List.replicate w.length true := by
          apply List.eq_replicate_length.mpr
          intro x hx
          cases x with
          | false => exact False.elim (hz hx)
          | true => rfl
        have hn : w.length < k := by
          by_contra hn
          have hb : run z w = none := by
            rw [he, hones, dif_neg (by dsimp [z]; omega)]
          rw [hr] at hb
          contradiction
        have hv : s.val = w.length := by
          have ht := hr
          rw [he, hones, dif_pos (by dsimp [z]; simpa using hn)] at ht
          have hv := congrArg Fin.val (Option.some.inj ht)
          simpa [z] using hv.symm
        rw [hv]
        conv_rhs => rw [he]
        simp
  let fzero := fun v : ZMod 2 => some (v, (Sum.inl (0, W 0 0) :
    (ℕ × (Fin 0 → ZMod 2)) ⊕ (Fin 0 → ZMod 2)))
  have hzero_image : records.image (signature 0) = insert none (Finset.univ.image fzero) := by
    dsimp only [records]
    rw [Finset.image_insert, Finset.image_image]
    simp only [signature, Option.map_none]
    apply congrArg (fun s : Finset (Option (ZMod 2 ×
      ((ℕ × (Fin 0 → ZMod 2)) ⊕ (Fin 0 → ZMod 2)))) => insert none s)
    apply Finset.ext
    intro a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.1, Finset.mem_univ _, ?_⟩
      simp [signature, fzero, hempty q.2.1 0]
    · rintro ⟨v, _, rfl⟩
      refine ⟨(v, 0, z), by simp [hPzero], ?_⟩
      simp [signature, fzero]
  have hzero_count : (records.image (signature 0)).card = 3 := by
    have hinj : Function.Injective fzero := by
      intro v u h
      simpa [fzero] using congrArg (fun r => r.map Prod.fst) h
    rw [hzero_image, Finset.card_insert_of_notMem (by simp [fzero]),
      Finset.card_image_of_injective _ hinj]
    norm_num
  have hpositive_count (H : ℕ) (hH : 1 ≤ H) :
      (records.image (signature H)).card =
        1 + 2 * (min (m * H) (k - 1) * min p (m * H / g + 2) + min p (m * H / g + 1)) := by
    let b := m * H
    have hHne : H ≠ 0 := by omega
    have hgm : g ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m T)
    have hb : 2 ≤ b := by
      have hmb : m ≤ m * H := by simpa using Nat.mul_le_mul_left m hH
      dsimp [b]
      dsimp [g, T] at hgm
      omega
    let tails := (Finset.univ : Finset (Fin k)).filter (fun s => s.val < k - 1)
    let thresholds := tails.image (fun s => min (k - s.val) (b + 1))
    let A := P.image (W b)
    let D := P.image (fun θ => W (b - 1) (θ + 1))
    let nonterminal := (Finset.univ.product (thresholds.product A)).image
      (fun q : ZMod 2 × ℕ × (Fin b → ZMod 2) =>
        some (q.1, (Sum.inl q.2 : (ℕ × (Fin b → ZMod 2)) ⊕ (Fin (b - 1) → ZMod 2))))
    let terminal := (Finset.univ.product D).image
      (fun q : ZMod 2 × (Fin (b - 1) → ZMod 2) =>
        some (q.1, (Sum.inr q.2 : (ℕ × (Fin b → ZMod 2)) ⊕ (Fin (b - 1) → ZMod 2))))
    let top : Fin k := ⟨k - 1, by omega⟩
    have hthreshold_set : thresholds = Finset.Icc 2 (min k (b + 1)) := by
      ext a
      simp only [thresholds, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hs' : s.val < k - 1 := (Finset.mem_filter.mp hs).2
        omega
      · intro ha
        let s : Fin k := ⟨k - a, by omega⟩
        refine ⟨s, ?_, ?_⟩
        · simp only [tails, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [s]
          omega
        · dsimp [s]
          omega
    have hthreshold_count : thresholds.card = min b (k - 1) := by
      rw [hthreshold_set, Nat.card_Icc]
      omega
    have hA : A.card = min p (b / g + 2) := by
      simpa only [A, W, c, P, T, g, p, Nat.add_comm] using (hcounts.2.2 b (by omega)).1
    have hD : D.card = min p (b / g + 1) := by
      have hh := (hcounts.2.2 (b - 1) (by omega)).2
      simpa only [D, W, c, P, T, g, p, Finset.image_image, Function.comp_apply, Function.comp_def,
        Nat.sub_add_cancel (by omega : 1 ≤ b), Nat.add_comm] using hh
    have hnon_inj : Function.Injective
        (fun q : ZMod 2 × ℕ × (Fin b → ZMod 2) =>
          some (q.1, (Sum.inl q.2 : (ℕ × (Fin b → ZMod 2)) ⊕ (Fin (b - 1) → ZMod 2)))) := by
      rintro ⟨v, q⟩ ⟨u, r⟩ h
      simpa using h
    have hterm_inj : Function.Injective
        (fun q : ZMod 2 × (Fin (b - 1) → ZMod 2) =>
          some (q.1, (Sum.inr q.2 : (ℕ × (Fin b → ZMod 2)) ⊕ (Fin (b - 1) → ZMod 2)))) := by
      rintro ⟨v, q⟩ ⟨u, r⟩ h
      simpa using h
    have hnon_card : nonterminal.card = 2 * (thresholds.card * A.card) := by
      dsimp only [nonterminal]
      rw [Finset.card_image_of_injective _ hnon_inj]
      simp only [Finset.product_eq_sprod, Finset.card_product]
      norm_num
    have hterm_card : terminal.card = 2 * D.card := by
      dsimp only [terminal]
      rw [Finset.card_image_of_injective _ hterm_inj]
      simp only [Finset.product_eq_sprod, Finset.card_product]
      norm_num
    have hdisjoint : Disjoint nonterminal terminal := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q', _, h⟩ := Finset.mem_image.mp hb
      simp at h
    have hnone : none ∉ nonterminal ∪ terminal := by
      simp [nonterminal, terminal]
    have himage : records.image (signature H) = insert none (nonterminal ∪ terminal) := by
      dsimp only [records]
      rw [Finset.image_insert, Finset.image_image]
      simp only [signature, Option.map_none]
      apply congrArg (fun s : Finset (Option (ZMod 2 ×
        ((ℕ × (Fin b → ZMod 2)) ⊕ (Fin (b - 1) → ZMod 2)))) => insert none s)
      apply Finset.ext
      intro a
      simp only [nonterminal, terminal, Finset.mem_image, Finset.mem_union]
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨v, θ, s⟩
        have hθ : θ ∈ P := by simpa using hq
        by_cases hs : s.val = k - 1
        · right
          refine ⟨(v, W (b - 1) (θ + 1)), ?_, ?_⟩
          · simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and, D, Finset.mem_image]
            exact ⟨θ, hθ, rfl⟩
          · simp [hHne, hs, b]
        · left
          refine ⟨(v, min (k - s.val) (b + 1), W b θ), ?_, ?_⟩
          · simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and]
            constructor
            · exact Finset.mem_image.mpr ⟨s, by simp [tails]; have := s.isLt; omega, rfl⟩
            · exact Finset.mem_image.mpr ⟨θ, hθ, rfl⟩
          · simp [hHne, hs, b]
      · intro ha
        rcases ha with ha | ha
        · obtain ⟨q, hq, he⟩ := ha
          rcases q with ⟨v, τ, w⟩
          have hτ : τ ∈ thresholds := (Finset.mem_product.mp (Finset.mem_product.mp hq).2).1
          have hw : w ∈ A := (Finset.mem_product.mp (Finset.mem_product.mp hq).2).2
          obtain ⟨s, hs, hsτ⟩ := Finset.mem_image.mp hτ
          obtain ⟨θ, hθ, hθw⟩ := Finset.mem_image.mp hw
          have hs' : s.val < k - 1 := (Finset.mem_filter.mp hs).2
          refine ⟨(v, θ, s), by simp [hθ], ?_⟩
          rw [← he]
          simp [hHne, show s.val ≠ k - 1 by omega, b, ← hsτ, ← hθw]
        · obtain ⟨q, hq, he⟩ := ha
          rcases q with ⟨v, w⟩
          have hw : w ∈ D := (Finset.mem_product.mp hq).2
          obtain ⟨θ, hθ, hθw⟩ := Finset.mem_image.mp hw
          refine ⟨(v, θ, top), by simp [hθ], ?_⟩
          rw [← he]
          simp [hHne, top, b, ← hθw]
    rw [himage, Finset.card_insert_of_notMem hnone, Finset.card_union_of_disjoint hdisjoint,
      hnon_card, hterm_card, hthreshold_count, hA, hD]
    dsimp only [b]
    ring
  exact ⟨hscan, hsource_legal, hsource_output, hsource_record, htransport, hbit,
    hadvance_append, (fun _ => rfl), hsource_range, hrejection, hclassification,
    hpartitions, hzero_count, hpositive_count⟩

#print axioms kbonacci_resonant_block_responses

end D5.S1.Words.AdmissibleWords.KBonacciResonantBlockResponses
