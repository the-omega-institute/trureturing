/- GID: D5/S3/Arith/FibonacciAtomic/BottomSiblingBlockCriterion
   generality: G
   mirror-B: none(waiver:source-contract-under-construction)
   mirror-E: none(waiver:source-contract-under-construction)
   anchors: []
   utility: none
   digest: Actual sources fill every residue at one known-row depth; the full sibling-block target remains open. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import D5.S3.Arith.ZeckendorfFutureKernel
import D5.S1.Digit.Infinite.WindowSuccessorGraph
import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.ZeckendorfFutureKernel (advance value legal value_append)
open D5.S1.Digit.Infinite.WindowSuccessorGraph
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy (primePowerProjection)

/-- A source is an actual finite literal prefix from one of the two unit
initializations. Its terminal seam and End flag are computed by `run`. -/
structure ActualPrefix where
  epsilon : Bool
  past : List Window
  terminal : run (some (epsilon, epsilon)) past = some (true, true)

def sourceNumber (source : ActualPrefix) : Nat :=
  (if source.epsilon then 1 else 0) +
    value 2 3 (flatten source.past)

def nextRow (source : ActualPrefix) : Nat × Nat :=
  advance (flatten source.past).length (2, 3)

/-- The known-row domain contains only sources whose computed next row is the
supplied actual row. It has no independent residue or surjectivity field. -/
def KnownRowFiber (H : Nat) (u v : ZMod H) :=
  {source : ActualPrefix //
    ((nextRow source).1 : ZMod H) = u ∧
    ((nextRow source).2 : ZMod H) = v}

/-- Each query resets to this same prefix, appends one literal suffix, then
requests the original raw gcd End answer. -/
def rawGcd (H : Nat) (source : ActualPrefix) (suffix : List Window) : Option Nat :=
  observe (fun N => Nat.gcd N H) source.epsilon source.epsilon
    (if source.epsilon then 1 else 0) 2 3 (source.past ++ suffix)

def rawIndex (H : Nat) (source : ActualPrefix) (suffix : List Window) : Option Nat :=
  observe (fun N => H / Nat.gcd N H) source.epsilon source.epsilon
    (if source.epsilon then 1 else 0) 2 3 (source.past ++ suffix)

def CompleteFuture (H : Nat) (x y : ActualPrefix) : Prop :=
  ∀ suffix : List Window, rawGcd H x suffix = rawGcd H y suffix

def CompleteFutureIndex (H : Nat) (x y : ActualPrefix) : Prop :=
  ∀ suffix : List Window, rawIndex H x suffix = rawIndex H y suffix

/-- The same selected word supplies every prime-power projection of its one
global center. Distinct words may have the same center. -/
noncomputable def centers (t H : Nat) (u v : ZMod H)
    (available : Finset (SuccessfulWord t)) : Finset (ZMod H) :=
  available.image (fun w => -value u v (flatten w.val))

noncomputable def localCenters (t H : Nat) (u v : ZMod H)
    (available : Finset (SuccessfulWord t)) (p : H.primeFactors) :
    Finset (ZMod (p.val ^ H.factorization p.val)) :=
  (centers t H u v available).image (fun a => ZMod.cast a)

/-- Every bottom sibling block contains at least all but one of its leaves. -/
def BottomBlocks (t H : Nat) (u v : ZMod H)
    (available : Finset (SuccessfulWord t)) : Prop :=
  ∀ p : H.primeFactors,
    let e := H.factorization p.val
    let π := primePowerProjection p.val (Nat.sub_le e 1)
    ∀ b : ZMod (p.val ^ (e - 1)),
      ((localCenters t H u v available p).filter fun a => π a = b).card ≥ p.val - 1

/-- The query type is the finite family of globally available attached words. -/
def FiniteIdentifiable (t H : Nat) (u v : ZMod H)
    (available : Finset (SuccessfulWord t)) : Prop :=
  ∃ protocol : PassiveProtocol (↑available) (fun _ => Option Nat),
    Function.FactorsThrough
      (fun source : KnownRowFiber H u v =>
        (sourceNumber source.val : ZMod H))
      (runPassiveProtocol
        (fun word (source : KnownRowFiber H u v) => rawGcd H source.val word.val.val)
        protocol)

/-- This is the exact theorem 114.3 target, including actual row fullness,
future fidelity, the adaptive criterion, and the necessary count. It is a
proposition definition until every clause has a kernel-checked proof. -/
def Target (H t : Nat) (_hH : 2 ≤ H) (u v : ZMod H)
    (_hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v) : Prop :=
  (∃ j : Nat, ∀ r : ZMod H, ∃ source : KnownRowFiber H u v,
      source.val.past.length = j ∧
      (sourceNumber source.val : ZMod H) = r) ∧
  (∀ source : ActualPrefix, 0 < sourceNumber source) ∧
  (∀ x y : KnownRowFiber H u v,
      CompleteFuture H x.val y.val ↔
      (sourceNumber x.val : ZMod H) = (sourceNumber y.val : ZMod H)) ∧
  (∀ x y : KnownRowFiber H u v,
      CompleteFutureIndex H x.val y.val ↔ CompleteFuture H x.val y.val) ∧
  (∀ available : Finset (SuccessfulWord t),
      FiniteIdentifiable t H u v available ↔
        BottomBlocks t H u v available) ∧
  (BottomBlocks t H u v (Finset.univ : Finset (SuccessfulWord t)) →
    ∀ p : H.primeFactors,
      p.val ^ (H.factorization p.val - 1) * (p.val - 1) ≤
        Nat.fib (3 * t + 1)) ∧
  (∃ _source : KnownRowFiber 4 0 1,
    sourceNumber _source.val = 5 ∧
    ∃ available : Finset (SuccessfulWord 2),
      (centers 2 4 0 1 available).card = 2 ∧
      ¬ BottomBlocks 2 4 0 1 available)

/-- Every residue occurs at one shared positive window depth in the supplied
actual row. The construction uses the full Fibonacci interval, a computed
terminal tag, and a positive return period of the modular row permutation. -/
theorem actual_common_depth_fullness (H : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v) :
    ∃ j : Nat, ∀ r : ZMod H, ∃ source : KnownRowFiber H u v,
      source.val.past.length = j ∧
      (sourceNumber source.val : ZMod H) = r := by
  have pack_legal (t : Nat) (bs : List Bool) (hl : bs.length = 3 * t)
      (s : Bool) (hs : legal s bs) :
      (pack bs).length = t ∧ flatten (pack bs) = bs := by
    induction t generalizing bs s with
    | zero =>
      have hnil : bs = [] := List.length_eq_zero_iff.1 (by omega)
      subst bs
      exact ⟨rfl, rfl⟩
    | succ t ih =>
      rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      · simp at hl
      · simp at hl; omega
      · simp at hl; omega
      · have htail : tail.length = 3 * t := by simp only [List.length_cons] at hl; omega
        have hlegal : legal c tail := hs.2.2.2
        obtain ⟨hlen, hflat⟩ := ih tail htail c hlegal
        cases a <;> cases b <;> cases c <;>
          simp_all [legal, pack, triple, flatten, bits]

  have legal_stream_prefix
      (x : D5.S1.Digit.Infinite.SuccessorContinuity.LegalDigits) :
      ∀ (n i : Nat) (s : Bool), (s = true → x.val i = false) →
        legal s (List.ofFn fun k : Fin n => x.val (i + k.val)) := by
    intro n
    induction n with
    | zero => simp [legal]
    | succ n ih =>
      intro i s hs
      rw [List.ofFn_succ]
      simp only [legal]
      constructor
      · intro h
        exact Bool.noConfusion ((hs h.1).symm.trans h.2)
      · have hx := x.property i
        have hnext : x.val i = true → x.val (i + 1) = false := by
          intro h
          have hn : x.val (i + 1) ≠ true := fun h' => hx ⟨h, h'⟩
          cases hv : x.val (i + 1) <;> simp_all
        simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (i + 1) (x.val i) hnext

  have pack_terminal (t : Nat) (s : Bool) (bs : List Bool)
      (ht : 0 < t) (hl : bs.length = 3 * t)
      (hlegal : legal s bs) (hend : bs.getLast? = some true) :
      run (some (s, s)) (pack bs) = some (true, true) := by
    obtain ⟨hlen, hflat⟩ := pack_legal t bs hl s hlegal
    have hfold : ∀ w : List Window, ∀ z : Bool,
        w.foldl (fun _ b => last b) z =
          (flatten w).foldl (fun _ b => b) z := by
      intro w
      induction w with
      | nil => simp [flatten]
      | cons b w ih =>
        intro z
        simp only [List.foldl_cons, flatten, List.flatMap_cons, List.foldl_append]
        rw [show List.foldl (fun _ c => c) z (bits b) = last b by cases b <;> rfl]
        exact ih (last b)
    have hflag : ∀ w : List Window, w ≠ [] →
        ∀ z E : Bool, w.foldl (fun _ b => last b) z = true →
          w.foldl (fun _ b => nonzero b) E = true := by
      intro w
      induction w with
      | nil => simp
      | cons b w ih =>
        intro _ z E hz
        cases w with
        | nil =>
          cases b <;> simp [last, nonzero] at *
        | cons c rest =>
          exact ih (by simp) (last b) (nonzero b) hz
    have hne : pack bs ≠ [] := by
      intro h
      have := hlen
      rw [h] at this
      simp at this
      omega
    have hlast : (flatten (pack bs)).foldl (fun _ b => b) s = true := by
      rw [hflat]
      have hbs : bs = bs.dropLast ++ [true] :=
        (List.dropLast_append_getLast? true (by simpa using hend)).symm
      rw [hbs, List.foldl_append]
      simp
    have hseam : (pack bs).foldl (fun _ b => last b) s = true := by
      rw [hfold]
      exact hlast
    have hE : (pack bs).foldl (fun _ b => nonzero b) s = true :=
      hflag (pack bs) hne s s hseam
    rw [(execution s s (pack bs)).1.2 (by simpa [hflat] using hlegal)]
    simp [hseam, hE]

  have value_fib (n k : Nat) (f : Fin n → Bool) :
      value (Nat.fib (k + 2)) (Nat.fib (k + 3)) (List.ofFn f) =
        ∑ i : Fin n, if f i then Nat.fib (k + i.val + 2) else 0 := by
    induction n generalizing k with
    | zero => simp [value]
    | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [value]
      have hrec : Nat.fib (k + 2) + Nat.fib (k + 3) = Nat.fib (k + 4) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := k + 2)).symm
      rw [hrec]
      have htail := ih (k + 1) (fun i : Fin n => f i.succ)
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ] at *
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

  have advance_fib (n : Nat) :
      advance n (1, 2) = (Nat.fib (n + 2), Nat.fib (n + 3)) := by
    induction n with
    | zero => norm_num [advance, Nat.fib]
    | succ n ih =>
      change (fun z : Nat × Nat => (z.2, z.1 + z.2))^[n + 1] (1, 2) = _
      rw [Function.iterate_succ_apply']
      change (fun z : Nat × Nat => (z.2, z.1 + z.2))^[n] (1, 2) = _ at ih
      rw [ih]
      have hrec := Nat.fib_add_two (n := n + 2)
      apply Prod.ext
      · rfl
      · simpa [Nat.add_assoc] using hrec.symm

  have legal_append_end (s : Bool) (bs : List Bool) (h : legal s bs) :
      legal s (bs ++ [false, true]) := by
    induction bs generalizing s with
    | nil => simp [legal]
    | cons b tail ih =>
      exact ⟨h.1, ih b h.2⟩

  have actual_interval (j N : Nat) (hj : 1 ≤ j)
      (hlo : Nat.fib (3 * j + 2) ≤ N)
      (hhi : N < Nat.fib (3 * j + 3)) :
      ∃ source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix,
        source.past.length = j ∧
        D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.sourceNumber source = N := by
    let L := 3 * j - 1
    have hL : 1 ≤ L := by dsimp [L]; omega
    have hindex : L + 3 = 3 * j + 2 := by dsimp [L]; omega
    have hlength : L + 1 = 3 * j := by dsimp [L]; omega
    have hbound : N - Nat.fib (3 * j + 2) < G L := by
      have hrec : Nat.fib (3 * j + 3) =
          Nat.fib (3 * j + 1) + Nat.fib (3 * j + 2) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := 3 * j + 1))
      change N - Nat.fib (3 * j + 2) < Nat.fib (L + 2)
      have hidx : L + 2 = 3 * j + 1 := by dsimp [L]; omega
      rw [hidx]
      omega
    have hgraph := (window_successor_graph L hL).1
      (N - Nat.fib (3 * j + 2))
      (if N - Nat.fib (3 * j + 2) < G L - 1 then
        N - Nat.fib (3 * j + 2) + 1 else 0)
    obtain ⟨x, hx, _⟩ := hgraph.mpr (by
      by_cases h : N - Nat.fib (3 * j + 2) < G L - 1
      · exact Or.inl ⟨h, if_pos h⟩
      · exact Or.inr (Or.inl ⟨by omega, if_neg h⟩))
    let q0 : List Bool := List.ofFn fun i : Fin L => x.val i.val
    have hqlen : q0.length = L := by simp [q0]
    have hqlegal : legal false q0 := by
      simpa [q0] using legal_stream_prefix x L 0 false (by simp)
    have hqval : value 1 2 q0 = N - Nat.fib (3 * j + 2) := by
      have hv := value_fib L 0 (fun i : Fin L => x.val i.val)
      have hsum :
          (∑ i : Fin L, if x.val i.val then Nat.fib (i.val + 2) else 0) =
            V (P L x) := by
        change (∑ i : Fin L, if x.val i.val then Nat.fib (i.val + 2) else 0) =
          ∑ i : Fin L, Nat.fib (i.val + 2) * (if x.val i.val then 1 else 0)
        apply Finset.sum_congr rfl
        intro i _
        cases x.val i.val <;> simp
      have hv' : value 1 2 q0 = V (P L x) := by
        have hv0 :
            value (Nat.fib 2) (Nat.fib 3) q0 =
              ∑ i : Fin L, if x.val i.val then Nat.fib (i.val + 2) else 0 := by
          simpa only [zero_add, q0] using hv
        have hf2 : Nat.fib 2 = 1 := by decide
        have hf3 : Nat.fib 3 = 2 := by decide
        simpa only [hf2, hf3] using hv0.trans hsum
      exact hv'.trans hx
    have hqappend : value 1 2 (q0 ++ [false, true]) = N := by
      rw [value_append, hqval, hqlen, advance_fib]
      simpa [value, hindex] using (Nat.sub_add_cancel hlo)
    cases hq : q0 with
    | nil => simp [hq] at hqlen; omega
    | cons eps tail =>
      have htaillegal : legal eps tail := by
        have hqlegal' : legal false (eps :: tail) := by simpa [hq] using hqlegal
        exact hqlegal'.2
      have hbslegal : legal eps (tail ++ [false, true]) :=
        legal_append_end eps tail htaillegal
      have hbslen : (tail ++ [false, true]).length = 3 * j := by
        have hltail : tail.length + 1 = L := by simpa [hq] using hqlen
        simp only [List.length_append, List.length_cons, List.length_nil]
        calc
          tail.length + (0 + 1 + 1) = (tail.length + 1) + 1 := by omega
          _ = L + 1 := by rw [hltail]
          _ = 3 * j := hlength
      have hlast : (tail ++ [false, true]).getLast? = some true := by simp
      let source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix :=
        ⟨eps, pack (tail ++ [false, true]),
          pack_terminal j eps (tail ++ [false, true]) (by omega) hbslen hbslegal hlast⟩
      refine ⟨source, (pack_legal j _ hbslen eps hbslegal).1, ?_⟩
      have hflat := (pack_legal j _ hbslen eps hbslegal).2
      change (if eps then 1 else 0) + value 2 3 (flatten (pack (tail ++ [false, true]))) = N
      rw [hflat]
      simpa [hq, value] using hqappend

  have flat_length (w : List Window) : (flatten w).length = 3 * w.length := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      cases b <;> simp [flatten, bits] at * <;> omega

  have cast_advance (H n : Nat) (z : Nat × Nat) :
      (((advance n z).1 : ZMod H), ((advance n z).2 : ZMod H)) =
        advance n ((z.1 : ZMod H), (z.2 : ZMod H)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change
        ((((fun z : Nat × Nat => (z.2, z.1 + z.2))^[n+1] z).1 : ZMod H),
          (((fun z : Nat × Nat => (z.2, z.1 + z.2))^[n+1] z).2 : ZMod H)) =
        ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n+1]
          ((z.1 : ZMod H), (z.2 : ZMod H)))
      change
        ((((fun z : Nat × Nat => (z.2, z.1 + z.2))^[n] z).1 : ZMod H),
          (((fun z : Nat × Nat => (z.2, z.1 + z.2))^[n] z).2 : ZMod H)) =
        ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n]
          ((z.1 : ZMod H), (z.2 : ZMod H))) at ih
      simp only [Function.iterate_succ_apply', Nat.cast_add]
      exact Prod.ext (congrArg Prod.snd ih)
        (by simpa using congrArg (fun p : ZMod H × ZMod H => p.1 + p.2) ih)

  let rowPerm (H : Nat) : (ZMod H × ZMod H) ≃ (ZMod H × ZMod H) := {

    toFun z := (z.2, z.1 + z.2)
    invFun z := (z.2 - z.1, z.1)
    left_inv := by intro z; ext <;> simp
    right_inv := by intro z; ext <;> simp
  }

  have row_return (H : Nat) (hH : 2 ≤ H) :
      let P := orderOf (rowPerm H)
      0 < P ∧ ∀ z : ZMod H × ZMod H, advance P z = z := by
    classical
    letI : NeZero H := ⟨by omega⟩
    let P := orderOf (rowPerm H)
    have hp : (rowPerm H) ^ P = 1 := pow_orderOf_eq_one _
    refine ⟨orderOf_pos _, ?_⟩
    intro z
    change ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[P]) z = z
    calc
      _ = ((rowPerm H) ^ P) z := by rw [Equiv.Perm.coe_pow]; rfl
      _ = z := by rw [hp]; rfl

  have advance_add_mod (H n k : Nat) (z : ZMod H × ZMod H) :
      advance (n + k) z = advance k (advance n z) := by
    change
      (fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n + k] z =
        (fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[k]
          ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n] z)
    simpa only [Nat.add_comm] using
      Function.iterate_add_apply
        (fun z : ZMod H × ZMod H => (z.2, z.1 + z.2)) k n z

  classical
  letI : NeZero H := ⟨by omega⟩
  obtain ⟨source0, hrow0⟩ := hrow
  let j0 := source0.past.length
  let P := orderOf (rowPerm H)
  have hP : 0 < P := (row_return H hH).1
  have hperiod : ∀ z : ZMod H × ZMod H, advance P z = z :=
    (row_return H hH).2
  have hperiod_mul (k : Nat) (z : ZMod H × ZMod H) :
      advance (k * P) z = z := by
    induction k with
    | zero => simp [advance]
    | succ k ih =>
      rw [Nat.succ_mul, advance_add_mod, ih, hperiod]
  let j := j0 + (H + 1) * P
  have hj : 1 ≤ j := by
    have hmul : H + 1 ≤ (H + 1) * P := by
      calc
        H + 1 = (H + 1) * 1 := by simp
        _ ≤ (H + 1) * P := Nat.mul_le_mul_left _ hP
    dsimp [j]
    omega
  have hfib : H ≤ Nat.fib (3 * j + 1) := by
    have hmul : H + 1 ≤ (H + 1) * P := by
      calc
        H + 1 = (H + 1) * 1 := by simp
        _ ≤ (H + 1) * P := Nat.mul_le_mul_left _ hP
    have hlinear := Nat.le_fib_add_one (3 * j + 1)
    dsimp [j] at *
    omega
  let z : ZMod H × ZMod H := (2, 3)
  have hrow0' : advance (3 * j0) z = (u, v) := by
    have hcast := cast_advance H (flatten source0.past).length (2, 3)
    change
      (((nextRow source0).1 : ZMod H), ((nextRow source0).2 : ZMod H)) =
        advance (flatten source0.past).length z at hcast
    rw [flat_length source0.past] at hcast
    exact hcast.symm.trans (Prod.ext hrow0.1 hrow0.2)
  have hrowj : advance (3 * j) z = (u, v) := by
    have hidx : 3 * j = 3 * j0 + (3 * (H + 1)) * P := by
      dsimp [j]
      ring
    rw [hidx, advance_add_mod, hperiod_mul, hrow0']
  refine ⟨j, ?_⟩
  intro r
  let s : Nat := (r - (Nat.fib (3 * j + 2) : ZMod H)).val
  have hs : s < H := ZMod.val_lt _
  have hN : Nat.fib (3 * j + 2) + s < Nat.fib (3 * j + 3) := by
    have hrec : Nat.fib (3 * j + 3) =
        Nat.fib (3 * j + 1) + Nat.fib (3 * j + 2) := by
      simpa [Nat.add_assoc] using (Nat.fib_add_two (n := 3 * j + 1))
    omega
  obtain ⟨source, hlen, hvalue⟩ :=
    actual_interval j (Nat.fib (3 * j + 2) + s) hj (Nat.le_add_right _ _) hN
  have hrow_source :
      (((nextRow source).1 : ZMod H), ((nextRow source).2 : ZMod H)) =
        (u, v) := by
    have hcast := cast_advance H (flatten source.past).length (2, 3)
    change
      (((nextRow source).1 : ZMod H), ((nextRow source).2 : ZMod H)) =
        advance (flatten source.past).length z at hcast
    rw [flat_length source.past, hlen] at hcast
    exact hcast.trans hrowj
  refine ⟨⟨source, ⟨congrArg Prod.fst hrow_source,
    congrArg Prod.snd hrow_source⟩⟩, hlen, ?_⟩
  rw [hvalue]
  simp only [Nat.cast_add]
  dsimp [s]
  rw [ZMod.natCast_zmod_val]
  abel

#print axioms actual_common_depth_fullness

/-- Two actual successful queries have the necessary cardinality, while their
centers miss an entire bottom sibling block. -/
theorem actual_nonconverse :
    ∃ _source : KnownRowFiber 4 0 1,
      sourceNumber _source.val = 5 ∧
      ∃ available : Finset (SuccessfulWord 2),
        (centers 2 4 0 1 available).card = 2 ∧
        ¬ BottomBlocks 2 4 0 1 available := by
  classical
  let source : ActualPrefix :=
    ⟨false, [.high], by decide⟩
  let emptyWord : SuccessfulWord 2 := ⟨[], by decide, rfl⟩
  let secondWord : SuccessfulWord 2 := ⟨[.middle, .high], by decide, rfl⟩
  let available : Finset (SuccessfulWord 2) := {emptyWord, secondWord}
  have hcenters : centers 2 4 0 1 available = {0, 2} := by
    change Finset.image (fun w : SuccessfulWord 2 =>
      -value (0 : ZMod 4) 1 (flatten w.val)) {emptyWord, secondWord} = {0, 2}
    rw [Finset.image_insert, Finset.image_singleton]
    norm_num [emptyWord, secondWord, flatten, bits, value]
    rw [show (-6 : ZMod 4) = 2 by decide]
  refine ⟨⟨source, by decide⟩, by decide, available, ?_, ?_⟩
  · rw [hcenters]
    decide
  · intro h
    have hp : (2 : Nat) ∈ (4 : Nat).primeFactors := by
      rw [show (4 : Nat) = 2 ^ 2 by norm_num, Nat.primeFactors_pow 2 (by norm_num),
        Nat.Prime.primeFactors (by norm_num)]
      simp
    have hfactor : (4 : Nat).factorization 2 = 2 := by
      rw [show (4 : Nat) = 2 ^ 2 by norm_num,
        Nat.factorization_pow_self Nat.prime_two]
    have := h ⟨2, hp⟩ (1 : ZMod (2 ^ ((4 : Nat).factorization 2 - 1)))
    simp only [Subtype.coe_mk] at this
    norm_num [localCenters, hcenters, primePowerProjection] at this
    rcases this with ⟨a, ha⟩
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha.1 with h0 | h2
    · subst a
      have hfalse := ha.2
      change (ZMod.cast (0 : ZMod (2 ^ (4 : Nat).factorization 2)) :
        ZMod (2 ^ ((4 : Nat).factorization 2 - 1))) = 1 at hfalse
      rw [hfactor] at hfalse
      exact (by decide : (ZMod.cast (0 : ZMod 4) : ZMod 2) ≠ 1) hfalse
    · subst a
      have hfalse := ha.2
      change (ZMod.cast (ZMod.cast (2 : ZMod 4) :
        ZMod (2 ^ (4 : Nat).factorization 2)) :
          ZMod (2 ^ ((4 : Nat).factorization 2 - 1))) = 1 at hfalse
      rw [hfactor] at hfalse
      exact (by decide :
        (ZMod.cast (ZMod.cast (2 : ZMod 4) : ZMod 4) : ZMod 2) ≠ 1) hfalse

#print axioms actual_nonconverse

end D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
