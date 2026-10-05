/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Complete literal windows acquire monochromatic initial phase labels at exact cost. -/

import D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
import D5.S0.Tower.DBonacciGeneral.UniformBaseGap
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators

/-- The original low-bit-first scalar, including every literal position. -/
def value (k : ℕ) : ℕ → List Bool → ZMod 2
  | _, [] => 0
  | n, b :: w => (if b then (dbonacci k (n + 2) : ZMod 2) else 0) + value k (n + 1) w

/-- The actual scanner of consecutive ones; rejection is represented by `none`. -/
def scanner (k : ℕ) (hk : 0 < k) : PartialDFA Bool (Fin k) where
  start := ⟨0, hk⟩
  step s b := if b then
    if h : s.val + 1 < k then some ⟨s.val + 1, h⟩ else none
    else some ⟨0, hk⟩

/-- Only the endpoint scalar is observed on a successful literal history. -/
def output (k : ℕ) (hk : 0 < k) (w : List Bool) : Option (ZMod 2) :=
  ((scanner k hk).eval w).map (fun _ => value k 0 w)

/-- A chronological archive contains the complete issued words and their endpoint outputs. -/
abbrev Archive (m : ℕ) := List ((Fin m → Bool) × Option (ZMod 2))

/-- A selector receives only the free initial output and its chronological archive. -/
abbrev Selector (m : ℕ) (Y : Type*) := Option (ZMod 2) → Archive m → Y ⊕ (Fin m → Bool)

/-- Execution appends all positions of each selected word and charges every issued action. -/
def execute {Y : Type*} {m : ℕ} (k : ℕ) (hk : 0 < k) (π : Selector m Y) :
    ℕ → List Bool → Option (ZMod 2) → Archive m → Option (Y × ℕ)
  | 0, _, y₀, h => match π y₀ h with
    | .inl y => some (y, 0)
    | .inr _ => none
  | d + 1, w, y₀, h => match π y₀ h with
    | .inl y => some (y, 0)
    | .inr B =>
      let w' := w ++ List.ofFn B
      (execute k hk π d w' y₀ (h ++ [(B, output k hk w')])).map
        (fun r => (r.1, r.2 + 1))

/-- Uniform acquisition on one free-value fiber; initial labels remain fixed during execution.
The initial rejection branch returns its prescribed label at zero cost.
The local alphabet requires every selected word to be internally admissible. -/
def Feasible {Y : Type*} (k m : ℕ) (hk : 0 < k) (localOnly : Bool)
    (labels : Fin ((k + 1) / Nat.gcd m (k + 1)) → Y) (reject : Y) (v : ZMod 2) (d : ℕ) : Prop :=
  ∃ π : Selector m Y,
    (∀ y₀ h B, π y₀ h = .inr B → localOnly = true → DBonacciAdmissible k m B) ∧
    (∀ w : List Bool, m ∣ w.length → output k hk w = none →
      execute k hk π d w none [] = some (reject, 0)) ∧
    ∀ (w : List Bool) (j : Fin ((k + 1) / Nat.gcd m (k + 1))),
      m ∣ w.length → output k hk w = some v →
      k + 1 ∣ w.length + j.val * Nat.gcd m (k + 1) →
      ∃ c ≤ d, execute k hk π d w (some v) [] = some (labels j, c)

/-- The last phase index carrying a label different from the baseline, or zero. -/
def lastIndex {Y : Type*} {p : ℕ} (hp : 0 < p) (labels : Fin p → Y) : ℕ :=
  by
    classical
    exact ((Finset.univ.filter (fun j : Fin p => labels j ≠ labels ⟨0, hp⟩)).image Fin.val).sup id

/-- The complete word for a window, with zero at every unselected position. -/
def pulse {Y : Type*} {p : ℕ} (hp : 0 < p) (labels : Fin p → Y)
    (g m u J t : ℕ) : Fin m → Bool := by
  classical
  exact fun i => decide (∃ j : Fin p, t * u < j.val ∧ j.val ≤ (t + 1) * u ∧ j.val ≤ J ∧
    labels j ≠ labels ⟨0, hp⟩ ∧ t * m + i.val + 1 = j.val * g)

/-- Nonbaseline labels in each first-pass window are monochromatic. -/
def Monochromatic {Y : Type*} {p : ℕ} (hp : 0 < p) (labels : Fin p → Y) (u J : ℕ) : Prop :=
  ∀ t (j j' : Fin p),
    t * u < j.val → j.val ≤ (t + 1) * u → j.val ≤ J → labels j ≠ labels ⟨0, hp⟩ →
    t * u < j'.val → j'.val ≤ (t + 1) * u → j'.val ≤ J → labels j' ≠ labels ⟨0, hp⟩ →
    labels j = labels j'

/-- Exact least uniform budget for both values and both complete-word alphabets. -/
theorem narrow_window_cost {Y : Type*} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (hg : 2 ≤ Nat.gcd m (k + 1)) (_hshort : m < k + 1)
    (labels : Fin ((k + 1) / Nat.gcd m (k + 1)) → Y) :
    let g := Nat.gcd m (k + 1)
    let p := (k + 1) / g
    let u := m / g
    ∃ hp : 0 < p,
      let J := lastIndex hp labels
      Monochromatic hp labels u J →
      ∀ (v : ZMod 2) (reject : Y) (localOnly : Bool),
        IsLeast {d : ℕ | Feasible k m (by omega) localOnly labels reject v d} (J ⌈/⌉ u) := by
  classical
  have hkpos : 0 < k := by omega
  let g := Nat.gcd m (k + 1)
  let p := (k + 1) / g
  let u := m / g
  have hgm : g ∣ m := Nat.gcd_dvd_left m (k + 1)
  have hgT : g ∣ k + 1 := Nat.gcd_dvd_right m (k + 1)
  have hmu : g * u = m := Nat.mul_div_cancel' hgm
  have hTp : g * p = k + 1 := Nat.mul_div_cancel' hgT
  have hp : 0 < p := by dsimp [p]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hgT) (by omega)
  have hu : 0 < u := by dsimp [u]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hgm) (by omega)
  refine ⟨hp, ?_⟩
  dsimp only
  intro hmono v reject localOnly
  let J := lastIndex hp labels
  let c := fun n => (dbonacci k (n + 2) : ZMod 2)
  have hperiod : Function.Periodic c (k + 1) := by
    intro n
    have h₀ := dbonacci_add_two_of_le k (n + k) (by omega)
    have h₁ := dbonacci_add_two_of_le k (n + k + 1) (by omega)
    simp only [show n + k - k = n by omega] at h₀
    simp only [show n + k + 1 - k = n + 1 by omega] at h₁
    rw [Fin.sum_univ_eq_sum_range (fun i => dbonacci k (n + i + 2))] at h₀
    rw [Fin.sum_univ_eq_sum_range (fun i => dbonacci k (n + 1 + i + 2))] at h₁
    have hs := Finset.sum_range_succ' (fun i => dbonacci k (n + i + 2)) k
    have ht := Finset.sum_range_succ (fun i => dbonacci k (n + i + 2)) k
    have he : dbonacci k (n + k + 1 + 2) + dbonacci k (n + 2) =
        2 * dbonacci k (n + k + 2) := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_zero] at h₀ h₁ hs ht ⊢
      omega
    have hz := congrArg (fun a : ℕ => (a : ZMod 2)) he
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul] at hz
    have := CharTwo.add_eq_zero.mp hz
    simpa [c, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hcoeff (n : ℕ) : c n = if n % (k + 1) = 0 ∨ n % (k + 1) = k then 1 else 0 := by
    rw [← hperiod.map_mod_nat n]
    have hn := Nat.mod_lt n (by omega : 0 < k + 1)
    by_cases hz : n % (k + 1) = 0
    · simp [c, hz, dbonacci_add_two_of_lt k 0 (by omega)]
    · by_cases ht : n % (k + 1) = k
      · rw [if_pos (Or.inr ht)]
        dsimp only [c]
        rw [ht, dbonacci_diagonal_cardinality]
        have hb : (2 : ℕ) ^ k - 1 + 1 = 2 ^ k := by
          have : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by omega)
          omega
        have hb' := congrArg (fun a : ℕ => (a : ZMod 2)) hb
        have hpow : (2 : ZMod 2) ^ k = 0 := by simp [CharTwo.two_eq_zero, show k ≠ 0 by omega]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at hb'
        rw [hpow] at hb'
        exact (CharTwo.add_eq_zero.mp hb')
      · rw [if_neg (by tauto)]
        dsimp only [c]
        rw [dbonacci_add_two_of_lt k _ (by omega), Nat.cast_pow]
        simp [CharTwo.two_eq_zero, hz]
  have hvalueFn : ∀ (n q : ℕ) (B : Fin q → Bool),
      value k n (List.ofFn B) = ∑ i : Fin q, if B i then c (n + i.val) else 0 := by
    intro n q
    induction q generalizing n with
    | zero => intro B; simp [value]
    | succ q ih =>
      intro B
      rw [List.ofFn_succ, value, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      simp only [c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hvappend : ∀ (w B : List Bool) (n : ℕ),
      value k n (w ++ B) = value k n w + value k (n + w.length) B := by
    intro w
    induction w with
    | nil => intro B n; simp [value]
    | cons b w ih =>
      intro B n
      simp only [List.cons_append, value, List.length_cons, ih]
      simp only [Nat.add_comm, add_assoc]
  let z : Fin k := ⟨0, by omega⟩
  let base := scanner k hkpos
  let run := base.evalFrom
  have hscanBridge : ∀ (bits : List Bool) (q : Option (LiveRecord k))
      (state : Option (Fin k)), state.map Fin.val = q.map LiveRecord.tail →
      (state.bind (fun t => run t bits)).map Fin.val =
        (runWord (bitUpdate k) bits q).map LiveRecord.tail := by
    intro bits
    induction bits with
    | nil =>
      intro q state htail
      simpa [run, PartialDFA.evalFrom, runTransition, runWord] using htail
    | cons b bits ih =>
      intro q state htail
      cases q with
      | none =>
        cases state with
        | none => simpa [runWord, bitUpdate] using ih none none rfl
        | some t => simp at htail
      | some q =>
        cases state with
        | none => simp at htail
        | some t =>
          have ht : t.val = q.tail := Option.some.inj htail
          cases b with
          | false =>
            have h := ih (some ⟨q.value, q.phase + 1, 0⟩) (some z) rfl
            simpa [run, PartialDFA.evalFrom, runTransition, base, scanner,
              runWord, bitUpdate, z] using h
          | true =>
            by_cases safe : t.val + 1 < k
            · have safe' : q.tail + 1 < k := by omega
              have h := ih (some ⟨q.value + coefficient k q.phase, q.phase + 1,
                q.tail + 1⟩) (some ⟨t.val + 1, safe⟩) (by simpa using ht)
              simpa [run, PartialDFA.evalFrom, runTransition, base, scanner,
                runWord, bitUpdate, safe, safe'] using h
            · have safe' : ¬q.tail + 1 < k := by omega
              have h := ih none none rfl
              simpa [run, PartialDFA.evalFrom, runTransition, base, scanner,
                runWord, bitUpdate, safe, safe'] using h
  have hW (j : Fin p) (s : Fin k) (a : ZMod 2) :
      ∃ w : List Bool, m ∣ w.length ∧ k + 1 ∣ w.length + j.val * g ∧
        run z w = some s ∧ value k 0 w = a := by
    let phase : ZMod (k + 1) := -(j.val * g : ℕ)
    have hjg : j.val * g < k + 1 := by
      calc j.val * g < p * g := Nat.mul_lt_mul_of_pos_right j.isLt (by omega)
           _ = k + 1 := by simpa [Nat.mul_comm] using hTp
    have hphase : Nat.gcd m (k + 1) ∣ phase.val := by
      dsimp only [phase]
      rw [ZMod.neg_val]
      split_ifs with hz
      · exact dvd_zero g
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjg]
        exact Nat.dvd_sub hgT (dvd_mul_left g j.val)
    obtain ⟨N, word, hNm, hlegal, hactual, hscalar, htail, hblocks⟩ :=
      joint_history_realization k m hk hm a phase s.val s.isLt hphase
    let w := List.ofFn word
    have hl : w.length = N := List.length_ofFn
    have model := literal_block_execution k hk N word 0 0 0 (by omega)
    have hadmissible : runAdmissible (k - 1) (k - 1) N word = true := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simpa [hr, DBonacciAdmissible] using hlegal
    have hrecord : (⟨wordIncrement k 0 word, (N : ℕ), tailAfter 0 word⟩ : LiveRecord k) =
        ⟨a, phase, s.val⟩ := by
      have he := model.1
      simp only [Nat.sub_zero, hadmissible, ↓reduceIte, zero_add] at he
      exact Option.some.inj (he.symm.trans hactual)
    have hNj : k + 1 ∣ N + j.val * g := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have hNphase : (N : ZMod (k + 1)) = phase := congrArg LiveRecord.phase hrecord
      rw [Nat.cast_add, hNphase]
      exact neg_add_cancel _
    have hrun : run z w = some s := by
      have he := hscanBridge w (some ⟨0, 0, 0⟩) (some z) rfl
      change (run z w).map Fin.val = (runBits k word (some ⟨0, 0, 0⟩)).map LiveRecord.tail at he
      rw [hactual] at he
      obtain ⟨t, ht, hts⟩ := Option.map_eq_some_iff.mp he
      exact ht.trans (congrArg some (Fin.ext hts))
    have hvalue : value k 0 w = a := by
      rw [hvalueFn]
      simpa only [originalWordValue, originalWeight, c, Nat.zero_add] using hscalar
    exact ⟨w, hl ▸ hNm, by simpa only [hl] using hNj, hrun, hvalue⟩
  have hjbound (j : Fin p) : j.val * g < k + 1 := by
    calc j.val * g < p * g := Nat.mul_lt_mul_of_pos_right j.isLt (by omega)
         _ = k + 1 := by simpa [Nat.mul_comm] using hTp
  have hfirst (t : ℕ) : pulse hp labels g m u J t ⟨0, by omega⟩ = false := by
    simp only [pulse, decide_eq_false_iff_not]
    rintro ⟨j, hj, _, _, _, he⟩
    have hmul := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hj)
    have ht : t * u * g = t * m := by rw [Nat.mul_assoc, Nat.mul_comm u g, hmu]
    rw [Nat.succ_mul, ht] at hmul
    omega
  have hgap (t i : ℕ) (hi : i + 1 < m) :
      pulse hp labels g m u J t ⟨i, by omega⟩ = false ∨
      pulse hp labels g m u J t ⟨i + 1, hi⟩ = false := by
    by_contra h
    have hb : pulse hp labels g m u J t ⟨i, by omega⟩ = true := by cases h' : pulse hp labels g m u J t ⟨i, by omega⟩ <;> simp_all
    have hb' : pulse hp labels g m u J t ⟨i + 1, hi⟩ = true := by cases h' : pulse hp labels g m u J t ⟨i + 1, hi⟩ <;> simp_all
    simp only [pulse, decide_eq_true_eq] at hb hb'
    obtain ⟨j, _, _, _, _, he⟩ := hb
    obtain ⟨j', _, _, _, _, he'⟩ := hb'
    have hd := Nat.dvd_sub (dvd_mul_left g j'.val) (dvd_mul_left g j.val)
    have heq : j'.val * g - j.val * g = 1 := by omega
    rw [heq] at hd
    have hh := Nat.le_of_dvd (by omega : 0 < 1) hd
    omega
  have hchainRun : ∀ (w : List Bool) (b : Bool) (s : Fin k),
      s.val = (if b then 1 else 0) →
      (b :: w).IsChain (fun a b => a = false ∨ b = false) →
      ∃ r : Fin k, r.val ≤ 1 ∧ run s w = some r := by
    intro w
    induction w with
    | nil => intro b s hs _; exact ⟨s, by cases b <;> simp_all, rfl⟩
    | cons a w ih =>
      intro b s hs hc
      obtain ⟨hab, hc⟩ := List.isChain_cons_cons.mp hc
      cases a with
      | false =>
        obtain ⟨r, hr, he⟩ := ih false z rfl hc
        exact ⟨r, hr, he⟩
      | true =>
        have hb : b = false := by simpa using hab
        have hs0 : s.val = 0 := by simpa [hb] using hs
        let one : Fin k := ⟨1, by omega⟩
        obtain ⟨r, hr, he⟩ := ih true one rfl hc
        refine ⟨r, hr, ?_⟩
        change runTransition base.step s (true :: w) = some r
        simp only [runTransition, base, scanner, hs0, zero_add,
          dif_pos (by omega : 1 < k)]
        exact he
  have hsafe (t : ℕ) (s : Fin k) :
      ∃ r : Fin k, r.val ≤ 1 ∧ run s (List.ofFn (pulse hp labels g m u J t)) = some r := by
    let B := pulse hp labels g m u J t
    have hc : (List.ofFn B).IsChain (fun a b => a = false ∨ b = false) :=
      List.isChain_ofFn.mpr (hgap t)
    cases he : List.ofFn B with
    | nil => have hl : (List.ofFn B).length = m := List.length_ofFn; rw [he] at hl; simp at hl; omega
    | cons b w =>
      have hb : b = false := by
        have hh : (List.ofFn B)[0]? = some (B ⟨0, by omega⟩) := by simp [show 0 < m by omega]
        rw [he] at hh
        simpa [B, hfirst] using hh
      subst b
      have hc' : (false :: w).IsChain (fun a b => a = false ∨ b = false) := by rwa [he] at hc
      obtain ⟨r, hr, he'⟩ := hchainRun w false z rfl hc'
      refine ⟨r, hr, ?_⟩
      exact he'
  have hlocal (t : ℕ) : DBonacciAdmissible k m (pulse hp labels g m u J t) := by
    have ha := (D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators (K := ZMod 2) k hk).2.1
    apply (ha m _).mpr
    obtain ⟨r, _, hr⟩ := hsafe t z
    change run z (List.ofFn (pulse hp labels g m u J t)) ≠ none
    rw [hr]
    simp
  have hselected (N t : ℕ) (j₀ : Fin p) (hN : k + 1 ∣ N + j₀.val * g)
      (i : Fin m) (j : Fin p) (he : t * m + i.val + 1 = j.val * g) :
      c (N + t * m + i.val) = if j = j₀ then 1 else 0 := by
    have hd : g ∣ N := by
      have := dvd_trans hgT hN
      have hh := Nat.dvd_sub this (dvd_mul_left g j₀.val)
      simpa only [Nat.add_sub_cancel] using hh
    have hd' : g ∣ N + t * m + i.val + 1 := by
      rw [show N + t * m + i.val + 1 = N + j.val * g by omega]
      exact Nat.dvd_add hd (dvd_mul_left g j.val)
    have hz : ¬ (N + t * m + i.val) % (k + 1) = 0 := by
      intro hz
      have hh := dvd_trans hgT (Nat.dvd_of_mod_eq_zero hz)
      have hh' := Nat.dvd_sub hd' hh
      simp only [Nat.add_sub_cancel_left] at hh'
      have := Nat.le_of_dvd (by omega : 0 < 1) hh'
      omega
    have hlast : (N + t * m + i.val) % (k + 1) = k ↔ k + 1 ∣ N + j.val * g := by
      have hn := Nat.mod_lt (N + t * m + i.val) (by omega : 0 < k + 1)
      have hh : N + j.val * g = (N + t * m + i.val) + 1 := by omega
      rw [hh, Nat.dvd_iff_mod_eq_zero, Nat.add_mod (N + t * m + i.val) 1 (k + 1)]
      simp only [Nat.mod_eq_of_lt (by omega : 1 < k + 1)]
      constructor
      · intro hr; rw [hr]; simp
      · intro hr
        by_contra hc
        have hlt : (N + t * m + i.val) % (k + 1) + 1 < k + 1 := by omega
        rw [Nat.mod_eq_of_lt hlt] at hr
        omega
    have hsame : k + 1 ∣ N + j.val * g ↔ j = j₀ := by
      constructor
      · intro hj
        have hh : Nat.ModEq (k + 1) (N + j.val * g) (N + j₀.val * g) :=
          hj.modEq_zero_nat.trans hN.modEq_zero_nat.symm
        have heq := (hh.add_left_cancel' N).eq_of_lt_of_lt (hjbound j) (hjbound j₀)
        apply Fin.ext
        exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < g) heq
      · rintro rfl; exact hN
    rw [hcoeff]
    simp only [hz, false_or, hlast, hsame]
  let A := labels ⟨0, hp⟩
  let S := fun t (j : Fin p) => t * u < j.val ∧ j.val ≤ (t + 1) * u ∧
    j.val ≤ J ∧ labels j ≠ A
  have hJmax (j : Fin p) (hj : labels j ≠ A) : j.val ≤ J := by
    change j.val ≤ ((Finset.univ.filter (fun j : Fin p => labels j ≠ A)).image Fin.val).sup id
    apply Finset.le_sup (f := id) (b := j.val)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
  have hJlt : J < p := by
    apply (Finset.sup_lt_iff hp).mpr
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.isLt
  have hJlabel (hJ : 0 < J) : labels ⟨J, hJlt⟩ ≠ A := by
    obtain ⟨i, hi, hle⟩ := (Finset.le_sup_iff hJ).mp (le_rfl : J ≤ J)
    have hiJ : i ≤ J := Finset.le_sup (f := id) hi
    have he : i = J := Nat.le_antisymm hiJ hle
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hi
    have hj' : labels j ≠ A := by simpa [A] using hj
    have hej : j = ⟨J, hJlt⟩ := Fin.ext (hjv.trans he)
    rwa [← hej]
  have hscalar (N t : ℕ) (j₀ : Fin p) (hN : k + 1 ∣ N + j₀.val * g) :
      value k (N + t * m) (List.ofFn (pulse hp labels g m u J t)) =
        if S t j₀ then 1 else 0 := by
    rw [hvalueFn]
    by_cases hs : S t j₀
    · rw [if_pos hs]
      have hlo : t * m + g ≤ j₀.val * g := by
        have h := Nat.mul_le_mul_right g (Nat.succ_le_of_lt hs.1)
        change (t * u + 1) * g ≤ j₀.val * g at h
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm u g, hmu] at h
        exact h
      have hhi : j₀.val * g ≤ (t + 1) * m := by
        have h := Nat.mul_le_mul_right g hs.2.1
        rw [Nat.mul_assoc, Nat.mul_comm u g, hmu] at h
        exact h
      let i₀ : Fin m := ⟨j₀.val * g - 1 - t * m, by
        have hhi' : j₀.val * g ≤ t * m + m := by simpa only [Nat.add_mul, Nat.one_mul] using hhi
        omega⟩
      have he : t * m + i₀.val + 1 = j₀.val * g := by dsimp [i₀]; omega
      have hb : pulse hp labels g m u J t i₀ = true := by
        simp only [pulse, decide_eq_true_eq]
        exact ⟨j₀, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, he⟩
      rw [Finset.sum_eq_single i₀]
      · rw [if_pos hb, hselected N t j₀ hN i₀ j₀ he, if_pos rfl]
      · intro i _ hi
        by_cases hb' : pulse hp labels g m u J t i = true
        · obtain ⟨j, _, _, _, _, hj⟩ := of_decide_eq_true hb'
          rw [if_pos hb', hselected N t j₀ hN i j hj]
          apply if_neg
          intro heq
          subst j
          have hii : i = i₀ := Fin.ext (by omega)
          exact hi hii
        · exact if_neg hb'
      · simp
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hb : pulse hp labels g m u J t i = true
      · obtain ⟨j, hj, hj', hjJ, hjA, he⟩ := of_decide_eq_true hb
        rw [if_pos hb, hselected N t j₀ hN i j he]
        apply if_neg
        rintro rfl
        exact hs ⟨hj, hj', hjJ, hjA⟩
      · exact if_neg hb
  let D := J ⌈/⌉ u
  have hJD : J ≤ u * D := (ceilDiv_le_iff_le_mul hu).mp (le_rfl : D ≤ D)
  let L := fun t => if h : ∃ j : Fin p, S t j then labels (Classical.choose h) else A
  have hL (t : ℕ) (j : Fin p) (hs : S t j) : L t = labels j := by
    have hex : ∃ j : Fin p, S t j := ⟨j, hs⟩
    rw [show L t = labels (Classical.choose hex) by simp [L, hex]]
    have hc := Classical.choose_spec hex
    exact hmono t _ _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  let π : Selector m Y := fun y₀ H => match y₀ with
    | none => .inl reject
    | some _ => if (H.getLast?.map Prod.snd).getD y₀ ≠ y₀ then .inl (L (H.length - 1))
        else if D ≤ H.length then .inl A else .inr (pulse hp labels g m u J H.length)
  have hup : ∀ (r t N : ℕ) (w : List Bool) (H : Archive m) (j : Fin p),
      t + r = D → w.length = N + t * m → k + 1 ∣ N + j.val * g →
      output k hkpos w = some v → H.length = t →
      (H.getLast?.map Prod.snd).getD (some v) = some v →
      (labels j ≠ A → t * u < j.val) →
      ∃ q ≤ r, execute k hkpos π r w (some v) H = some (labels j, q) := by
    intro r
    induction r with
    | zero =>
      intro t N w H j htr hw hN ho hH hcur hj
      have hjA : labels j = A := by
        by_contra hn
        have h₁ := hj hn
        have h₂ := hJmax j hn
        have htD : t = D := by omega
        rw [htD] at h₁
        exact (not_lt_of_ge (h₂.trans (by simpa only [Nat.mul_comm] using hJD))) h₁
      refine ⟨0, le_rfl, ?_⟩
      simp [execute, π, hcur, hH, show D ≤ t by omega, hjA]
    | succ r ih =>
      intro t N w H j htr hw hN ho hH hcur hj
      have ht : t < D := by omega
      have hπ : π (some v) H = .inr (pulse hp labels g m u J t) := by
        simp [π, hcur, hH, Nat.not_le.mpr ht]
      obtain ⟨s, hr, hv⟩ := Option.map_eq_some_iff.mp ho
      change run z w = some s at hr
      change value k 0 w = v at hv
      obtain ⟨s', hs', hrun⟩ := hsafe t s
      have hrun' : run z (w ++ List.ofFn (pulse hp labels g m u J t)) = some s' := by
        have ha := base.evalFrom_append z w (List.ofFn (pulse hp labels g m u J t))
        change run z (w ++ List.ofFn (pulse hp labels g m u J t)) = _ at ha
        rw [ha]
        change (run z w).bind (fun a => run a (List.ofFn (pulse hp labels g m u J t))) = _
        rw [hr]; exact hrun
      have ho' : output k hkpos (w ++ List.ofFn (pulse hp labels g m u J t)) =
          some (v + if S t j then 1 else 0) := by
        change (run z (w ++ List.ofFn (pulse hp labels g m u J t))).map _ = _
        rw [hrun', Option.map_some, hvappend, hv, Nat.zero_add, hw, hscalar N t j hN]
      by_cases hs : S t j
      · have hvne : v + 1 ≠ v := by intro he; have := add_left_cancel (he.trans (add_zero v).symm); norm_num at this
        have hstop : π (some v) (H ++ [(pulse hp labels g m u J t,
            output k hkpos (w ++ List.ofFn (pulse hp labels g m u J t)))]) = .inl (labels j) := by
          simp [π, ho', hs, hvne, hH, hL t j hs]
        refine ⟨1, by omega, ?_⟩
        cases r <;> simp [execute, hπ, hstop]
      · have hobs : output k hkpos (w ++ List.ofFn (pulse hp labels g m u J t)) = some v := by simpa [hs] using ho'
        have hj' : labels j ≠ A → (t + 1) * u < j.val := by
          intro hn
          have h₁ := hj hn
          have h₂ := hJmax j hn
          by_contra hh
          apply hs
          exact ⟨h₁, by omega, h₂, hn⟩
        obtain ⟨q, hq, he⟩ := ih (t + 1) N
          (w ++ List.ofFn (pulse hp labels g m u J t))
          (H ++ [(pulse hp labels g m u J t, some v)]) j
          (by omega) (by simp [hw]; ring) hN hobs
          (by simp [hH]) (by simp) hj'
        refine ⟨q + 1, by omega, ?_⟩
        simp only [execute, hπ, hobs, he, Option.map_some]
  change IsLeast {d : ℕ | Feasible k m (by omega) localOnly labels reject v d} D
  constructor
  · refine ⟨π, ?_, ?_, ?_⟩
    · intro y₀ H B he _
      cases y₀ with
      | none => simp only [π, Sum.inl_ne_inr] at he
      | some a =>
        dsimp only [π] at he
        split_ifs at he
        simp only [Sum.inr.injEq] at he
        subst B
        exact hlocal H.length
    · intro w _ _
      cases D <;> simp only [execute, π]
    · intro w j hwm ho hphase
      obtain ⟨q, hq, he⟩ := hup D 0 w.length w [] j (by omega)
        (by simp) hphase ho rfl rfl (by
          intro hn
          by_contra hz
          have hj0 : j = ⟨0, hp⟩ := Fin.ext (by change j.val = 0; omega)
          exact hn (congrArg labels hj0))
      exact ⟨q, hq, he⟩
  · intro d hd
    by_contra hnot
    have hdD : d < D := Nat.lt_of_not_ge hnot
    have hJpos : 0 < J := by
      by_contra hz
      have he : J = 0 := by omega
      have heD : D = 0 := by simp [D, he]
      omega
    let j₀ : Fin p := ⟨0, hp⟩
    let j₁ : Fin p := ⟨J, hJlt⟩
    have hlabels : labels j₁ ≠ labels j₀ := hJlabel hJpos
    have hdu : u * d < J := by
      by_contra hh
      have : D ≤ d := (ceilDiv_le_iff_le_mul hu).mpr (by omega)
      omega
    have hdm : d * m + g ≤ J * g := by
      have hh := Nat.mul_le_mul_right g (show u * d + 1 ≤ J by omega)
      have ht : u * d * g = d * m := by
        rw [Nat.mul_assoc, Nat.mul_comm d g, ← Nat.mul_assoc, Nat.mul_comm u g, hmu, Nat.mul_comm]
      simpa only [Nat.add_mul, Nat.one_mul, ht] using hh
    have hJT : J * g + g ≤ k + 1 := by
      have hh := Nat.mul_le_mul_right g (show J + 1 ≤ p by omega)
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_comm p g, hTp] at hh
      exact hh
    obtain ⟨π', _, _, hcorrect⟩ := hd
    have hhead (B : Fin m → Bool) :
        ∃ tail : List Bool, List.ofFn B = B ⟨0, by omega⟩ :: tail := by
      have hh : ∀ n (hn : 0 < n) (C : Fin n → Bool),
          ∃ tail, List.ofFn C = C ⟨0, hn⟩ :: tail := by
        intro n hn C
        cases n with
        | zero => omega
        | succ n => exact ⟨List.ofFn (Fin.tail C), List.ofFn_succ⟩
      exact hh m (by omega) B
    have habsorb : ∀ (r : ℕ) (w w' : List Bool) (y₀ : Option (ZMod 2)) (H : Archive m),
        run z w = none → run z w' = none →
        execute k hkpos π' r w y₀ H = execute k hkpos π' r w' y₀ H := by
      intro r
      induction r with
      | zero => intros; rfl
      | succ r ih =>
        intro w w' y₀ H hw hw'
        cases hπ : π' y₀ H with
        | inl y => simp [execute, hπ]
        | inr B =>
          have hb : run z (w ++ List.ofFn B) = none := by
            have hh := base.evalFrom_append z w (List.ofFn B)
            change run z (w ++ List.ofFn B) = _ at hh
            change run z (w ++ List.ofFn B) = none
            rw [hh]; change (run z w).bind _ = none; rw [hw]; rfl
          have hb' : run z (w' ++ List.ofFn B) = none := by
            have hh := base.evalFrom_append z w' (List.ofFn B)
            change run z (w' ++ List.ofFn B) = _ at hh
            rw [hh]; change (run z w').bind _ = none; rw [hw']; rfl
          have ho : output k hkpos (w ++ List.ofFn B) = none := by
            change (run z (w ++ List.ofFn B)).map _ = none; rw [hb]; rfl
          have ho' : output k hkpos (w' ++ List.ofFn B) = none := by
            change (run z (w' ++ List.ofFn B)).map _ = none; rw [hb']; rfl
          simp only [execute, hπ, ho, ho']
          rw [ih _ _ y₀ (H ++ [(B, none)]) hb hb']
    have hroot : ∃ B : Fin m → Bool, π' (some v) [] = .inr B ∧ B ⟨0, by omega⟩ = false := by
      let top : Fin k := ⟨k - 1, by omega⟩
      obtain ⟨w₀, hm₀, hp₀, hr₀, hv₀⟩ := hW j₀ top v
      obtain ⟨w₁, hm₁, hp₁, hr₁, hv₁⟩ := hW j₁ top v
      have ho₀ : output k hkpos w₀ = some v := by
        change (run z w₀).map _ = some v; rw [hr₀]; simpa using hv₀
      have ho₁ : output k hkpos w₁ = some v := by
        change (run z w₁).map _ = some v; rw [hr₁]; simpa using hv₁
      obtain ⟨q₀, _, he₀⟩ := hcorrect w₀ j₀ hm₀ ho₀ hp₀
      obtain ⟨q₁, _, he₁⟩ := hcorrect w₁ j₁ hm₁ ho₁ hp₁
      cases hπ : π' (some v) [] with
      | inl y =>
        cases d <;> simp [execute, hπ] at he₀ he₁
        all_goals exact False.elim (hlabels (he₁.1.symm.trans he₀.1))
      | inr B =>
        refine ⟨B, rfl, ?_⟩
        cases hb : B ⟨0, by omega⟩ with
        | false => rfl
        | true =>
          obtain ⟨tail, ht⟩ := hhead B
          have hr : run top (List.ofFn B) = none := by
            rw [ht, hb]
            change runTransition base.step top (true :: tail) = none
            simp [runTransition, base, scanner, top,
              show ¬k - 1 + 1 < k by omega]
          have hbad₀ : run z (w₀ ++ List.ofFn B) = none := by
            have hh := base.evalFrom_append z w₀ (List.ofFn B)
            change run z (w₀ ++ List.ofFn B) = _ at hh
            rw [hh]; change (run z w₀).bind _ = none; rw [hr₀]; exact hr
          have hbad₁ : run z (w₁ ++ List.ofFn B) = none := by
            have hh := base.evalFrom_append z w₁ (List.ofFn B)
            change run z (w₁ ++ List.ofFn B) = _ at hh
            rw [hh]; change (run z w₁).bind _ = none; rw [hr₁]; exact hr
          have hout₀ : output k hkpos (w₀ ++ List.ofFn B) = none := by
            change (run z (w₀ ++ List.ofFn B)).map _ = none; rw [hbad₀]; rfl
          have hout₁ : output k hkpos (w₁ ++ List.ofFn B) = none := by
            change (run z (w₁ ++ List.ofFn B)).map _ = none; rw [hbad₁]; rfl
          have heq : execute k hkpos π' d w₀ (some v) [] =
              execute k hkpos π' d w₁ (some v) [] := by
            cases d with
            | zero => simp [execute, hπ]
            | succ r =>
              simp only [execute, hπ, hout₀, hout₁, List.nil_append]
              rw [habsorb r _ _ (some v) [(B, none)] hbad₀ hbad₁]
          rw [he₀, he₁] at heq
          exact False.elim (hlabels (congrArg Prod.fst (Option.some.inj heq)).symm)
    obtain ⟨rootB, hrootB, hrootZero⟩ := hroot
    obtain ⟨w₀, hm₀, hp₀, hr₀, hv₀⟩ := hW j₀ z v
    obtain ⟨w₁, hm₁, hp₁, hr₁, hv₁⟩ := hW j₁ z v
    have ho₀ : output k hkpos w₀ = some v := by
      change (run z w₀).map _ = some v; rw [hr₀]; simpa using hv₀
    have ho₁ : output k hkpos w₁ = some v := by
      change (run z w₁).map _ = some v; rw [hr₁]; simpa using hv₁
    have hquiet (L : List Bool) (hlen : L.length ≤ d * m) (hfirstL : L.head? ≠ some true) :
        value k w₀.length L = 0 ∧ value k w₁.length L = 0 := by
      have hphase₀ : k + 1 ∣ w₀.length := by simpa [j₀] using hp₀
      have hphase₁ : k + 1 ∣ w₁.length + J * g := hp₁
      have h₀ := hvalueFn w₀.length L.length L.get
      have h₁ := hvalueFn w₁.length L.length L.get
      rw [List.ofFn_get] at h₀ h₁
      rw [h₀, h₁]
      constructor <;> apply Finset.sum_eq_zero <;> intro i _
      all_goals have hi : i.val + 1 ≤ d * m := (Nat.succ_le_of_lt i.isLt).trans hlen
      all_goals have hiT : i.val + 1 < k + 1 := by omega
      · by_cases hb : L.get i = true
        · rw [if_pos hb, hcoeff, Nat.add_mod w₀.length i.val (k + 1),
            Nat.mod_eq_zero_of_dvd hphase₀, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega : i.val < k + 1)]
          have hi0 : i.val ≠ 0 := by
            intro he
            have hh : L.head? = some (L.get i) := by
              rw [List.head?_eq_getElem?]
              simpa [he] using List.getElem?_eq_getElem i.isLt
            exact hfirstL (hh.trans (congrArg some hb))
          simp only [Nat.mod_eq_of_lt (by omega : i.val < k + 1)]
          rw [if_neg (by omega)]
        · exact if_neg hb
      · by_cases hb : L.get i = true
        · rw [if_pos hb, hcoeff]
          have hn : i.val + 1 < J * g := by omega
          have hz : ¬(w₁.length + i.val) % (k + 1) = 0 := by
            intro he
            have hh : Nat.ModEq (k + 1) (w₁.length + i.val) (w₁.length + J * g) :=
              (Nat.dvd_of_mod_eq_zero he).modEq_zero_nat.trans hphase₁.modEq_zero_nat.symm
            have heq := (hh.add_left_cancel' w₁.length).eq_of_lt_of_lt
              (by omega : i.val < k + 1) (by omega : J * g < k + 1)
            omega
          have ht : ¬(w₁.length + i.val) % (k + 1) = k := by
            intro he
            have hh : k + 1 ∣ w₁.length + (i.val + 1) := by
              apply Nat.dvd_of_mod_eq_zero
              rw [show w₁.length + (i.val + 1) = (w₁.length + i.val) + 1 by omega,
                Nat.add_mod (w₁.length + i.val) 1 (k + 1), he]
              simp
            have hh' := hh.modEq_zero_nat.trans hphase₁.modEq_zero_nat.symm
            have heq := (hh'.add_left_cancel' w₁.length).eq_of_lt_of_lt
              hiT (by omega : J * g < k + 1)
            omega
          simp [hz, ht]
        · exact if_neg hb
    have hobs (L : List Bool) (hlen : L.length ≤ d * m) (hfirstL : L.head? ≠ some true) :
        output k hkpos (w₀ ++ L) = output k hkpos (w₁ ++ L) := by
      obtain ⟨hq₀, hq₁⟩ := hquiet L hlen hfirstL
      have hrun₀ := base.evalFrom_append z w₀ L
      have hrun₁ := base.evalFrom_append z w₁ L
      change run z (w₀ ++ L) = _ at hrun₀
      change run z (w₁ ++ L) = _ at hrun₁
      change (run z (w₀ ++ L)).map _ = (run z (w₁ ++ L)).map _
      rw [hrun₀, hrun₁]
      change ((run z w₀).bind (fun s => run s L)).map _ =
        ((run z w₁).bind (fun s => run s L)).map _
      rw [hr₀, hr₁]
      simp only [Option.bind_some, hvappend, Nat.zero_add, hv₀, hv₁, hq₀, hq₁, add_zero]
    have hequal : ∀ (r t : ℕ) (L : List Bool) (H : Archive m),
        t + r = d → L.length = t * m → H.length = t → L.head? ≠ some true →
        execute k hkpos π' r (w₀ ++ L) (some v) H =
        execute k hkpos π' r (w₁ ++ L) (some v) H := by
      intro r
      induction r with
      | zero => intros; rfl
      | succ r ih =>
        intro t L H htr hlen hH hfirstL
        cases hπ : π' (some v) H with
        | inl y => simp [execute, hπ]
        | inr B =>
          have hfirst' : (L ++ List.ofFn B).head? ≠ some true := by
            cases hL : L with
            | nil =>
              have ht : t = 0 := (Nat.mul_eq_zero.mp (by simpa only [hL, List.length_nil] using hlen.symm)).resolve_right (by omega)
              have hH' : H = [] := List.length_eq_zero_iff.mp (by omega)
              rw [hH'] at hπ
              have hB : B = rootB := Sum.inr.inj (hπ.symm.trans hrootB)
              subst B
              obtain ⟨tail, htail⟩ := hhead rootB
              simp [htail, hrootZero]
            | cons b tail => simpa [hL] using hfirstL
          have hlen' : (L ++ List.ofFn B).length = (t + 1) * m := by simp [hlen]; ring
          have ho := hobs (L ++ List.ofFn B) (by rw [hlen']; exact Nat.mul_le_mul_right m (by omega)) hfirst'
          simp only [execute, hπ, List.append_assoc]
          rw [ho]
          exact congrArg (Option.map (fun r : Y × ℕ => (r.1, r.2 + 1)))
            (ih (t + 1) (L ++ List.ofFn B)
              (H ++ [(B, output k hkpos (w₁ ++ (L ++ List.ofFn B)))])
              (by omega) hlen' (by simp [hH]) hfirst')
    obtain ⟨q₀, _, he₀⟩ := hcorrect w₀ j₀ hm₀ ho₀ hp₀
    obtain ⟨q₁, _, he₁⟩ := hcorrect w₁ j₁ hm₁ ho₁ hp₁
    have he := hequal d 0 [] [] (by omega) (by simp) rfl (by simp)
    simp only [List.append_nil] at he
    rw [he₀, he₁] at he
    exact hlabels (congrArg Prod.fst (Option.some.inj he)).symm

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost
