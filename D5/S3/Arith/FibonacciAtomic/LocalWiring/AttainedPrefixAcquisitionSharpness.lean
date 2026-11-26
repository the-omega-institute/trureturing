/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisitionSharpness
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisitionSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One lawful hard source per promise and the sharp worst mature update deadline. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition

/-! A fixed difficult source in each promise and a sharp mature-cut deadline
against arbitrary finite adaptive stopping under one common proper tape law. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness

open AttainedPrefixAcquisition LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock
open PublicRowSeedReadiness OrderedBirthPrefix LawfulSourceReadiness NativePastAcquisitionBarrier
open scoped BigOperators

private def pulse (a l i : Nat) : Bool := decide (a ≤ i ∧ (i - a) % l = 0)

private theorem bitNat_mod (b : Bool) : bitNat b % 2 = bitNat b := by
  cases b <;> decide

private theorem pulse_legal (d l : Nat) (hl : 0 < l) (hld : l ≤ d) :
    BoundedBinaryRecurrence.Legal d (pulse (d - 1) l) := by
  let k : Fin d := ⟨d - l, by omega⟩
  refine ⟨d, le_rfl, fun j => decide (j = k), ?_⟩
  intro i
  have hs : (∑ j : Fin d, bitNat (decide (j = k)) *
      bitNat (pulse (d - 1) l (i + j.val))) = bitNat (pulse (d - 1) l (i + k.val)) := by
    rw [Finset.sum_eq_single k]
    · simp [bitNat]
    · intro j _ hj
      simp [hj, bitNat]
    · simp
  rw [hs, bitNat_mod]
  have h₁ : d - 1 ≤ i + d := by omega
  by_cases h₂ : d - 1 ≤ i + k.val
  · have hidx : i + d - (d - 1) = (i + k.val - (d - 1)) + l := by dsimp [k] at *; omega
    simp [pulse, h₁, h₂, hidx, Nat.add_mod_right]
  · have hi : (i + d - (d - 1)) < l := by dsimp [k] at h₂; omega
    have hip : 0 < i + d - (d - 1) := by omega
    have hz : (i + d - (d - 1)) % l ≠ 0 := by rw [Nat.mod_eq_of_lt hi]; omega
    simp [pulse, h₁, h₂, hz]

private theorem impulse_legal (d v : Nat) (hv : v < d) :
    BoundedBinaryRecurrence.Legal d (fun i => decide (i = v)) := by
  refine ⟨d, le_rfl, fun _ => false, ?_⟩
  intro i
  have h : i + d ≠ v := by omega
  simp [bitNat,h]

private theorem zero_legal (d : Nat) : BoundedBinaryRecurrence.Legal d (fun _ => false) := by
  exact ⟨0, Nat.zero_le _, Fin.elim0, fun _ => by simp [bitNat]⟩

private theorem single_hard_binary (d : Nat) (hd : 1 ≤ d) :
    ∃ s, BoundedBinaryRecurrence.Legal d s ∧ ∀ v < 2 * d, ∃ t, BoundedBinaryRecurrence.Legal d t ∧
      (∀ i < v, s i = t i) ∧ s v ≠ t v := by
  refine ⟨pulse (d - 1) d, pulse_legal d d (by omega) le_rfl, ?_⟩
  intro v hv
  by_cases h : v < d - 1
  · refine ⟨_, impulse_legal d v (by omega), ?_, ?_⟩
    · intro i hi
      have ha : ¬ d - 1 ≤ i := by omega
      simp [pulse, ha, hi.ne]
    · simp [pulse, h.not_ge]
  by_cases he : v = d - 1
  · subst v
    refine ⟨_, zero_legal d, ?_, ?_⟩
    · intro i hi
      simp [pulse, hi.not_ge]
    · simp [pulse]
  by_cases hf : v = 2 * d - 1
  · subst v
    refine ⟨_, impulse_legal d (d - 1) (by omega), ?_, ?_⟩
    · intro i hi
      by_cases hi₀ : d - 1 ≤ i
      · have hi₁ : i - (d - 1) < d := by omega
        have hh : i - (d - 1) = 0 ↔ i = d - 1 := by omega
        simp [pulse, hi₀, Nat.mod_eq_of_lt hi₁, hh]
      · have hh : i ≠ d - 1 := by omega
        simp [pulse, hi₀, hh]
    · have hm : 2 * d - 1 - (d - 1) = d := by omega
      have hne : 2 * d - 1 ≠ d - 1 := by omega
      simp [pulse, hm, hne, show d - 1 ≤ 2 * d - 1 by omega]
  let l := v - (d - 1)
  have hl : 0 < l := by dsimp [l]; omega
  have hld : l < d := by dsimp [l]; omega
  refine ⟨pulse (d - 1) l, pulse_legal d l hl hld.le, ?_, ?_⟩
  · intro i hi
    by_cases hi₀ : d - 1 ≤ i
    · have hi₁ : i - (d - 1) < l := by dsimp [l]; omega
      simp [pulse, hi₀, Nat.mod_eq_of_lt hi₁,
        Nat.mod_eq_of_lt (hi₁.trans hld)]
    · simp [pulse, hi₀]
  · simp [pulse, l, Nat.mod_eq_of_lt (show v - (d - 1)<d by omega),
      show d - 1 ≤ v by omega, show v - (d - 1) ≠ 0 by omega]

open D5.S3.Arith.FibonacciAtomic.LocalWiring.UnaryMooreSeparation

private def chain {K : Nat} (restart : Fin K) (q : Fin K) : Fin K :=
  if h : q.val + 1 < K then ⟨q.val + 1, h⟩ else restart

private def initial (K : Nat) (hK : 1 ≤ K) : Fin K := ⟨0, hK⟩

private def last (K : Nat) (q : Fin K) : Bool := decide (q.val = K - 1)

private def chainMachine (K : Nat) (hK : 1 ≤ K) (restart : Fin K) : Machine (Fin K) :=
  ⟨chain restart, last K, initial K hK⟩

/-- The fixed source is the K-cycle with its sole one at phase K−1. -/
def hardMoore (K : Nat) (hK : 1 ≤ K) : Machine (Fin K) :=
  chainMachine K hK (initial K hK)

private def waitMachine (K : Nat) (hK : 1 ≤ K) (v : Nat) (hv : v < K) :
    Machine (Fin K) :=
  ⟨fun q => ⟨min (q.val + 1) v, by omega⟩, fun q => decide (q.val = v), initial K hK⟩

private def zeroMachine (K : Nat) (hK : 1 ≤ K) : Machine (Fin K) :=
  ⟨id, fun _ => false, initial K hK⟩

/-- At high cuts, the restart drops the K−ℓ transient zero states. -/
def mooreAlternative (K : Nat) (hK : 1 ≤ K) (v : Nat) : Machine (Fin K) :=
  if hv : v < K - 1 then waitMachine K hK v (by omega)
  else if h : K - 1 < v ∧ v < 2 * K - 1 then
    chainMachine K hK ⟨K - (v - (K - 1)), by omega⟩
  else zeroMachine K hK

private theorem emit_iterate {Q : Type} (m : Machine Q) (i : Nat) :
    m.emit i = m.label (m.transition^[i] m.start) := by
  exact (unary_moore_separation_and_synthesis 1 (by decide)).2.2.2.1 Q m i

private theorem chain_before {K : Nat} (hK : 1 ≤ K) (r : Fin K) {i : Nat}
    (hi : i < K) : ((chain r)^[i] (initial K hK)).val = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', chain, dite_eq_left (by rw [ih (by omega)]; exact hi)]
    exact congrArg (· + 1) (ih (by omega))

private theorem chain_reset {K : Nat} (hK : 1 ≤ K) (r : Fin K) :
    (chain r)^[K] (initial K hK) = r := by
  have h : K = (K - 1) + 1 := by omega
  calc
    (chain r)^[K] (initial K hK) = (chain r)^[(K - 1) + 1] (initial K hK) :=
      congrArg (fun n => (chain r)^[n] (initial K hK)) h
    _ = r := by
      rw [Function.iterate_succ_apply', chain,
        dite_eq_right (by rw [chain_before hK r (by omega)]; omega)]

private theorem chain_after {K : Nat} (r : Fin K) {j : Nat} (hj : r.val + j < K) :
    ((chain r)^[j] r).val = r.val + j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', chain, dite_eq_left (by rw [ih (by omega)]; omega)]
    exact congrArg (· + 1) (ih (by omega))

private theorem emit_before (K : Nat) (hK : 1 ≤ K) (r : Fin K) {i : Nat} (hi : i < K) :
    (chainMachine K hK r).emit i = decide (i = K - 1) := by
  rw [emit_iterate]
  change decide (((chain r)^[i] (initial K hK)).val = K - 1) = _
  rw [chain_before hK r hi]

private theorem emit_after (K : Nat) (hK : 1 ≤ K) (r : Fin K) {i : Nat}
    (hi : K ≤ i) (hj : r.val + (i - K) < K) :
    (chainMachine K hK r).emit i = decide (r.val + (i - K) = K - 1) := by
  rw [emit_iterate]
  change decide (((chain r)^[i] (initial K hK)).val = K - 1) = _
  conv_lhs => rw [show i = (i - K) + K by omega, Function.iterate_add_apply,
    chain_reset hK r, chain_after r hj]

private theorem emit_wait (K : Nat) (hK : 1 ≤ K) (v : Nat) (hv : v < K) (i : Nat) :
    (waitMachine K hK v hv).emit i = decide (v ≤ i) := by
  rw [emit_iterate]
  let m := waitMachine K hK v hv
  have hstate (j : Nat) : ((m.transition^[j]) m.start).val = min j v := by
    induction j with
    | zero => simp [m, waitMachine, initial]
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      change min (((m.transition^[j]) m.start).val + 1) v = min (j + 1) v
      rw [ih]
      omega
  change decide (((m.transition^[i]) m.start).val = v) = decide (v ≤ i)
  rw [hstate]
  by_cases he : v ≤ i
  · simp [he]
  · simp [Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge he)), he,
      show i ≠ v by omega]

private theorem emit_zero (K : Nat) (hK : 1 ≤ K) (i : Nat) :
    (zeroMachine K hK).emit i = false := by
  rw [emit_iterate]
  rfl

private theorem hardMoore_separates (K : Nat) (hK : 1 ≤ K) (v : Nat) (hv : v < 2 * K - 1) :
    (∀ i < v, (hardMoore K hK).emit i = (mooreAlternative K hK v).emit i) ∧
    (hardMoore K hK).emit v ≠ (mooreAlternative K hK v).emit v := by
  by_cases hsmall : v < K - 1
  · rw [mooreAlternative, dite_eq_left hsmall]
    constructor
    · intro i hi
      rw [hardMoore, emit_before K hK _ (by omega), emit_wait]
      simp [show i ≠ K - 1 by omega, show ¬ v ≤ i by omega]
    · rw [hardMoore, emit_before K hK _ (by omega), emit_wait]
      simp [show v ≠ K - 1 by omega]
  · by_cases hhigh : K - 1 < v
    · rw [mooreAlternative, dite_eq_right hsmall, dite_eq_left ⟨hhigh, hv⟩]
      let r : Fin K := ⟨K - (v - (K - 1)), by omega⟩
      change (∀ i < v, (hardMoore K hK).emit i = (chainMachine K hK r).emit i) ∧ _
      have hr : r.val = K - (v - (K - 1)) := rfl
      constructor
      · intro i hi
        by_cases hiK : i < K
        · rw [hardMoore, emit_before K hK _ hiK, emit_before K hK _ hiK]
        · rw [hardMoore, emit_after K hK _ (by omega) (by change 0 + (i - K) < K; omega),
            emit_after K hK r (by omega) (by rw [hr]; omega)]
          simp [hr, initial, show i - K ≠ K - 1 by omega,
            show K - (v - (K - 1)) + (i - K) ≠ K - 1 by omega]
      · change (hardMoore K hK).emit v ≠ (chainMachine K hK r).emit v
        rw [hardMoore, emit_after K hK _ (by omega) (by change 0 + (v - K) < K; omega),
          emit_after K hK r (by omega) (by rw [hr]; omega)]
        simp [hr, initial, show v - K ≠ K - 1 by omega,
          show K - (v - (K - 1)) + (v - K) = K - 1 by omega]
    · have he : v = K - 1 := by omega
      subst v
      rw [mooreAlternative, dite_eq_right (Nat.lt_irrefl _), dite_eq_right (by omega)]
      constructor
      · intro i hi
        rw [hardMoore, emit_before K hK _ (by omega), emit_zero]
        simp [show i ≠ K - 1 by omega]
      · rw [hardMoore, emit_before K hK _ (by omega), emit_zero]
        simp

variable {Public Tape Local O : Type}

private theorem stopped_eq (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    (x : OutputStream) (j k : Nat) (hj : (run A u tape x j).stopped = true)
    (hk : (run A u tape x k).stopped = true) : run A u tape x j = run A u tape x k := by
  have later {i l : Nat} (hil : i ≤ l) (hi : (run A u tape x i).stopped = true) :
      run A u tape x l = run A u tape x i := by
    induction l, hil using Nat.le_induction with
    | base => rfl
    | succ l _ ih => simp [run, ih, advance, hi]
  rcases Nat.le_total j k with h | h
  · exact (later h hj).symm
  · exact later h hk

private def succeeds (A : Observer Public Tape Local) (u : Public)
    (out : Public → Tape → Record Local → Option O) (task : Nat → OutputStream → O)
    (x : OutputStream) (tape : Tape) : Prop :=
  ∃ k, let r := run A u tape x k
       2 ≤ r.cut ∧ r.stopped = true ∧ out u tape r = some (task r.cut x)

private theorem eventually_no_early_stop (F : Filter Tape) (A : Observer Public Tape Local)
    (u : Public) (out : Public → Tape → Record Local → Option O)
    (task : Nat → OutputStream → O) (L : OutputStream → Prop) (s : OutputStream)
    (N : Nat) (hs : L s)
    (hpair : ∀ e, 2 ≤ e → e < N → ∃ t, L t ∧ matureWord e s = matureWord e t ∧
      task e s ≠ task e t)
    (hok : ∀ x, L x → ∀ᶠ tape in F, succeeds A u out task x tape) :
    ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true → N ≤ (run A u tape s k).cut := by
  have hall : ∀ m ≤ N, ∀ᶠ tape in F, ∀ e < m, 2 ≤ e →
      ∃ t, matureWord e s = matureWord e t ∧ task e s ≠ task e t ∧
        succeeds A u out task t tape := by
    intro m
    induction m with
    | zero =>
      intro _
      exact Filter.univ_mem' fun tape e he => (Nat.not_lt_zero _ he).elim
    | succ m ih =>
      intro hm
      have hp := ih (by omega)
      by_cases hm2 : 2 ≤ m
      · obtain ⟨t, ht, heq, hne⟩ := hpair m hm2 (by omega)
        have htape := hok t ht
        refine Filter.mem_of_superset (Filter.inter_mem hp htape) ?_
        rintro tape ⟨hprior, hnow⟩ e he he2
        by_cases he' : e < m
        · exact hprior e he' he2
        · have heq' : e = m := by omega
          subst e
          exact ⟨t, heq, hne, hnow⟩
      · refine Filter.mem_of_superset hp ?_
        intro tape hprior e he he2
        exact hprior e (by omega) he2
  refine Filter.mem_of_superset (Filter.inter_mem (hok s hs) (hall N le_rfl)) ?_
  rintro tape ⟨⟨j, hc, hj, hsout⟩, hothers⟩ k hk
  let r := run A u tape s k
  have hrj : run A u tape s j = r := stopped_eq A u tape s j k hj hk
  rw [hrj] at hc hsout
  by_contra! hl
  obtain ⟨t, hw, hne, l, _, hlstop, htout⟩ := hothers r.cut hl hc
  have hrt : r = run A u tape t k :=
    ((native_past_acquisition_barrier r.cut s t A u).2.2.1 hw).1 tape k le_rfl
  have hk' : (run A u tape t k).stopped = true := hrt ▸ hk
  have hrl : run A u tape t l = r := (stopped_eq A u tape t l k hlstop hk').trans hrt.symm
  rw [hrl] at htout
  exact hne (Option.some.inj (hsout.symm.trans htout))

open PhysicalBirthClock KnownSeedCurrentFibers LocalTwoStepRecognizer
open PublicRowSeedReadiness OrderedBirthPrefix LawfulSourceReadiness

private theorem prefix_at (s : OutputStream) {k i : Nat} (hi : i < k) :
    (prefixBits (birthOf s) k)[i]? = some (s i) := by
  simp [prefixBits, consume, birthOf, hi]

private theorem erased_presence (t : Labelled) (p : Address) :
    present (shape t) p = present t p := by
  induction p generalizing t with
  | nil => simp [present, atTree]
  | cons b p ih =>
    cases t with
    | of x => cases b <;> rfl
    | mul l r => cases b
                 · exact ih l
                 · exact ih r

private theorem prefixClock_lt (n : Nat) (hn : 2 ≤ n) : matureSize n < clockSum n := by
  cases n with
  | zero => omega
  | succ n =>
    have h : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
    simpa [matureSize, clockSum, List.range_succ] using h

private theorem first_unseen_distinguishes_actual_tasks (n : Nat) (hn : 2 ≤ n) (s t : OutputStream)
    (hprefix : ∀ i < matureSize n, s i = t i) (hbit : s (matureSize n) ≠ t (matureSize n)) :
    matureWord n s = matureWord n t ∧
    physicalTree n s ≠ physicalTree n t ∧
    (fun p => queryNext n p s) ≠ (fun p => queryNext n p t) ∧
    future n s ≠ future n t := by
  have hborn : bornWord n s ≠ bornWord n t := by
    intro he
    have h := congrArg (fun w : List Bool => w[matureSize n]?) he
    exact hbit (Option.some.inj
      ((prefix_at s (prefixClock_lt n hn)).symm.trans
        (h.trans (prefix_at t (prefixClock_lt n hn)))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [matureWord, matureWord, prefixBits, prefixBits]
    apply List.map_congr_left
    intro i hi
    simpa [consume, birthOf] using hprefix i (List.mem_range.mp hi)
  · intro h
    apply hborn
    have he := exact_ordered_birth_prefix (birthOf s) n hn
    exact ((he.2.2.2.2.2.2.1 (birthOf t)).2.2).mp h
  · intro h
    apply hborn
    have hn' : 2 ≤ n + 1 := by omega
    have a := exact_ordered_birth_prefix (birthOf s) (n + 1) hn'
    have b := exact_ordered_birth_prefix (birthOf t) (n + 1) hn'
    have hI := (a.2.2.2.2.2.2.1 (birthOf t)).1
    exact hI.mp (fun p => by
      rw [(a.2.2.2.2.2.1 p).1, (b.2.2.2.2.2.1 p).1, erased_presence, erased_presence]
      exact Iff.of_eq (congrArg (· = true) (congrFun h p)))
  · intro h
    apply hbit
    have hd := (lawful_source_readiness (.binary 0) trivial n hn).2.2.2.2.1 s t
    have heq := hd.mp (fun as => congrArg (fun f : FutureBehavior => (f.1 as).1) h)
    exact congrFun heq (matureSize n)

private theorem row_fixed_alternative {r : Nat} (c seed : Fin r → Bool) (v : Nat) (hv : v < r) :
    ∃ other : Fin r → Bool, (∀ i < v, rowStream c seed i = rowStream c other i) ∧
      rowStream c seed v ≠ rowStream c other v := by
  let other (i : Fin r) := if i.val = v then !seed i else seed i
  have atInitial (s : Fin r → Bool) :=
    (public_row_seed_readiness r c s 2 (by decide)).2.2.2.2.2.2.1
  refine ⟨other, ?_, ?_⟩
  · intro i hi
    rw [atInitial seed ⟨i, by omega⟩, atInitial other ⟨i, by omega⟩]
    simp [other, Nat.ne_of_lt hi]
  · rw [atInitial seed ⟨v,hv⟩, atInitial other ⟨v,hv⟩]
    simp [other]

private theorem promise_fixed_hard (P : Promise) (hP : P.Valid) (hm : 0 < P.target) :
    ∃ s, P.Legal s ∧ ∀ v < P.target, ∃ t, P.Legal t ∧
      (∀ i < v, s i = t i) ∧ s v ≠ t v := by
  cases P with
  | lawful C =>
    cases C with
    | binary d =>
      change 0 < 2*d at hm
      exact single_hard_binary d (by omega)
    | moore K =>
      change 1 ≤ K at hP
      refine ⟨(hardMoore K hP).emit, ⟨Fin K, inferInstance, hardMoore K hP, by simp, rfl⟩, ?_⟩
      intro v hv
      refine ⟨(mooreAlternative K hP v).emit,
        ⟨Fin K, inferInstance, mooreAlternative K hP v, by simp, rfl⟩, ?_⟩
      exact hardMoore_separates K hP v hv
  | row r c =>
    let seed : Fin r → Bool := fun _ => false
    refine ⟨rowStream c seed, ⟨seed,rfl⟩, ?_⟩
    intro v hv
    obtain ⟨other,hbefore,hat⟩ := row_fixed_alternative c seed v hv
    exact ⟨rowStream c other, ⟨other,rfl⟩, hbefore, hat⟩

/-- One controller must stop at a mature cut and output exactly the requested task
for each lawful source, eventually on the same tape filter. -/
def AllSourcesMatureSuccess {Public Tape Local O : Type} (F : Filter Tape)
    (A : Observer Public Tape Local) (u : Public) (P : Promise)
    (out : Public → Tape → Record Local → Option O) (task : Nat → OutputStream → O) : Prop :=
  ∀ s, P.Legal s → ∀ᶠ tape in F, ∃ k,
    let r := run A u tape s k
    2 ≤ r.cut ∧ r.stopped = true ∧ out u tape r = some (task r.cut s)

/-- An actual next-cut literal presence mismatch at one physical address. -/
def nextDisagreement (n : Nat) (p : Address) (sources : OutputStream × OutputStream) : Bool :=
  queryNext n p sources.1 != queryNext n p sources.2

/-- A single lawful source for the promise prevents every earlier mature stop,
for each of the three task outputs and under any common proper tape law. -/
theorem single_adaptive_hard_source (P : Promise) (hP : P.Valid) (hm : 0 < P.target) :
    ∃ s, P.Legal s ∧
    (∀ n, 2 ≤ n → n < deadline P.target → ∃ t, P.Legal t ∧
      matureWord n s = matureWord n t ∧
      physicalTree n s ≠ physicalTree n t ∧
      (∃ p, nextDisagreement n p (s,t) = true) ∧
      future n s ≠ future n t) ∧
    ∀ {Public Tape Local : Type} (F : Filter Tape) [Filter.NeBot F]
      (A : Observer Public Tape Local) (u : Public)
      (outLabels : Public → Tape → Record Local → Option Labelled)
      (outNext : Public → Tape → Record Local → Option (Address → Bool))
      (outFuture : Public → Tape → Record Local → Option FutureBehavior),
      (AllSourcesMatureSuccess F A u P outLabels physicalTree →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut) ∧
      (AllSourcesMatureSuccess F A u P outNext (fun n w p => queryNext n p w) →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut) ∧
      (AllSourcesMatureSuccess F A u P outFuture future →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut) := by
  obtain ⟨s,hs,hshort⟩ := promise_fixed_hard P hP hm
  have alternatives (e : Nat) (he : 2 ≤ e) (hN : e < deadline P.target) :=
    hshort (matureSize e) (by
      by_contra! hc
      exact (Nat.not_le.mpr hN) ((deadline_minimal P.target).2.2 e he hc))
  have actualPairs (e : Nat) (he : 2 ≤ e) (hN : e < deadline P.target) :
      ∃ t, P.Legal t ∧ matureWord e s = matureWord e t ∧
        physicalTree e s ≠ physicalTree e t ∧
        (fun p => queryNext e p s) ≠ (fun p => queryNext e p t) ∧
        future e s ≠ future e t := by
    obtain ⟨t,ht,hinit,hbit⟩ := alternatives e he hN
    exact ⟨t,ht,first_unseen_distinguishes_actual_tasks e he s t hinit hbit⟩
  refine ⟨s,hs,?_,?_⟩
  · intro e he hN
    obtain ⟨t,ht,hw,hLabels,hNext,hFuture⟩ := actualPairs e he hN
    refine ⟨t,ht,hw,hLabels,?_,hFuture⟩
    have hpoint : ∃ p, queryNext e p s ≠ queryNext e p t := by
      by_contra! heq
      exact hNext (funext heq)
    obtain ⟨p,hp⟩ := hpoint
    exact ⟨p, by simpa [nextDisagreement] using hp⟩
  intro Public Tape Local F _ A u outLabels outNext outFuture
  have lower {O : Type} (task : Nat → OutputStream → O)
      (out : Public → Tape → Record Local → Option O)
      (hd : ∀ e ≥ 2, ∀ t, (∀ i < matureSize e, s i = t i) →
          s (matureSize e) ≠ t (matureSize e) → task e s ≠ task e t)
      (h : AllSourcesMatureSuccess F A u P out task) :
      ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
        deadline P.target ≤ (run A u tape s k).cut := by
    apply eventually_no_early_stop F A u out task P.Legal s (deadline P.target) hs _ h
    intro e he hN
    obtain ⟨t,ht,hinit,hbit⟩ := alternatives e he hN
    exact ⟨t,ht,(first_unseen_distinguishes_actual_tasks e he s t hinit hbit).1,
      hd e he t hinit hbit⟩
  exact ⟨lower _ _ (fun e he t hinit hbit =>
      (first_unseen_distinguishes_actual_tasks e he s t hinit hbit).2.1),
    lower _ _ (fun e he t hinit hbit =>
      (first_unseen_distinguishes_actual_tasks e he s t hinit hbit).2.2.1),
    lower _ _ (fun e he t hinit hbit =>
      (first_unseen_distinguishes_actual_tasks e he s t hinit hbit).2.2.2)⟩

#print axioms single_adaptive_hard_source

end D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness
