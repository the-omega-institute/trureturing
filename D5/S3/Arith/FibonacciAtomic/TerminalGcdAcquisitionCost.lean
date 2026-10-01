/- GID: D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-source positive-word terminal gcd identification has the exact prime-axis budget. -/

import D5.S3.Observer.Budget.ResidueHeightUpperBound
import D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

set_option autoImplicit false
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Observer.Budget.ResidueHeightUpperBound
open D5.S3.Observer.Budget.ResiduePosteriorClosure
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy

namespace D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost

def rootCenter {ι : Type} (X : ι → Type) [∀ i, Zero (X i)] (i : ι) :
    PassiveProtocol (X i) (fun _ => ℕ) → X i
  | .stop => 0
  | .query c _ => c

def descend {ι : Type} (X : ι → Type) (i : ι) :
    PassiveProtocol (X i) (fun _ => ℕ) → ℕ → PassiveProtocol (X i) (fun _ => ℕ)
  | .stop, _ => .stop
  | .query _ next, a => next a

def synchronize {ι : Type} (X : ι → Type) [∀ i, Zero (X i)] :
    ℕ → (∀ i, PassiveProtocol (X i) (fun _ => ℕ)) →
      PassiveProtocol (∀ i, X i) (fun _ => ι → ℕ)
  | 0, _ => .stop
  | B + 1, T => .query (fun i => rootCenter X i (T i))
      (fun a => synchronize X B (fun i => descend X i (T i) (a i)))

def replace (v : ℕ × ℕ) : ℕ × ℕ := (v.2, v.1 + v.2)

def graft (v : ℕ × ℕ) : ℕ × ℕ := (v.1 + 1, v.2)

def step (b : Bool) : (ℕ × ℕ) → ℕ × ℕ := if b then replace else graft

def runWord : List Bool → (ℕ × ℕ) → ℕ × ℕ
  | [], v => v
  | b :: w, v => runWord w (step b v)

def quantity (v : ℕ × ℕ) : ℕ := 2 * v.1 + 3 * v.2

def terminalGcd (H : ℕ) (w : List Bool) (v : ℕ × ℕ) : ℕ :=
  Nat.gcd (quantity (runWord w v)) H

def gcdDepth (p e g : ℕ) : ℕ :=
  ((Finset.range (e + 1)).filter fun j => p ^ j ∣ g).sup id

def localProjection (H : ℕ) (p : H.primeFactors) :
    ZMod H →+* ZMod (p.val ^ H.factorization p.val) :=
  ZMod.castHom (Nat.ordProj_dvd H p.val) _

def residueReplace (H : ℕ) : Equiv.Perm (ZMod H × ZMod H) where
  toFun v := (v.2, v.1 + v.2)
  invFun v := (v.2 - v.1, v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

def residueSource (H : ℕ) (v : ℕ × ℕ) : ZMod H × ZMod H := (v.1, v.2)

def scalar (H k : ℕ) (v : ℕ × ℕ) : ZMod H :=
  let t := (residueReplace H ^ k) (residueSource H v)
  2 * t.1 + 3 * t.2

def scalarWord (H k : ℕ) (c : ZMod H) : List Bool :=
  List.replicate k true ++ List.replicate (-c).val false ++
    List.replicate ((H * H).factorial - 1) true ++
    List.replicate c.val false ++ [true]

def actualize (H k : ℕ)
    (crt : ZMod H ≃+* ∀ p : H.primeFactors, ZMod (p.val ^ H.factorization p.val)) :
    PassiveProtocol (∀ p : H.primeFactors, ZMod (p.val ^ H.factorization p.val))
      (fun _ => H.primeFactors → ℕ) → PassiveProtocol (List Bool) (fun _ => ℕ)
  | .stop => .stop
  | .query c next => .query (scalarWord H k (-crt.symm c))
      (fun g => actualize H k crt
        (next (fun p => gcdDepth p.val (H.factorization p.val) g)))

def concatenate : PassiveProtocol (List Bool) (fun _ => ℕ) →
    PassiveProtocol (List Bool) (fun _ => ℕ) → PassiveProtocol (List Bool) (fun _ => ℕ)
  | .stop, U => U
  | .query w next, U => .query w (fun a => concatenate (next a) U)

def costBound (H : ℕ) : ℕ :=
  H.primeFactors.sup fun p => H.factorization p * (p - 1)

open D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

def boundedTree {Q : Type} {Y : Q → Type} {L : Type}
    (policy : Hist Y → Sum Q L) : ℕ → Hist Y → PassiveProtocol Q Y
  | 0, _ => .stop
  | n + 1, h => match policy h with
      | .inr _ => .stop
      | .inl q => .query q (fun y => boundedTree policy n (h ++ [⟨q, y⟩]))


/-- The finite worst query budgets of exact composition-residue strategies.
Every list, including the empty list, is one charged terminal experiment. -/
def treeAcquisitionBudgets (H : ℕ) : Set ℕ :=
  {K | ∃ T : PassiveProtocol (List Bool) (fun _ => ℕ),
    (∀ v v' : ℕ × ℕ,
      runPassiveProtocol (terminalGcd H) T v =
        runPassiveProtocol (terminalGcd H) T v' → residueSource H v = residueSource H v') ∧
    ∀ v : ℕ × ℕ, (runPassiveProtocol (terminalGcd H) T v).length ≤ K}

/-- Exact terminating history policies with uniformly bounded charged terminal queries. -/
def acquisitionBudgets (H : ℕ) : Set ℕ :=
  {K | ∃ (policy : Hist (fun _ : List Bool => ℕ) →
      Sum (List Bool) (ZMod H × ZMod H))
    (trace : (ℕ × ℕ) → Hist (fun _ : List Bool => ℕ)) (fuel : (ℕ × ℕ) → ℕ),
    (∀ v, execute (terminalGcd H) policy (fuel v) [] v =
      some (trace v, residueSource H v)) ∧
    ∀ v, (trace v).length ≤ K}

/-- The least finite worst cost of exact terminating history policies. -/
noncomputable def acquisitionCost (H : ℕ) : ℕ := sInf (acquisitionBudgets H)

/-- Exact composition acquisition uses twice the largest prime-power scalar
budget. The minimum is attained by a same-source positive-word strategy. -/
theorem terminal_gcd_acquisition_cost (H : ℕ) (hH : 1 ≤ H) :
    IsLeast (acquisitionBudgets H) (if H = 1 then 0 else 2 * costBound H) ∧
    acquisitionCost H = if H = 1 then 0 else 2 * costBound H := by
  classical
  have budget_equivalence {W : Type} {Q : Type} {Y : Q → Type} {L : Type} [Nonempty L]
      (read : (q : Q) → W → Y q) (target : W → L) (K : ℕ) :
      (∃ T : PassiveProtocol Q Y,
        (∀ x y, runPassiveProtocol read T x = runPassiveProtocol read T y → target x = target y) ∧
          ∀ x, (runPassiveProtocol read T x).length ≤ K) ↔
        (∃ (policy : Hist Y → Sum Q L) (trace : W → Hist Y) (fuel : W → ℕ),
          (∀ x, execute read policy (fuel x) [] x = some (trace x, target x)) ∧
            ∀ x, (trace x).length ≤ K) := by
    classical
    have raw_tree (policy : Hist Y → Sum Q L) :
        ∀ n K h x t l, execute read policy n h x = some (t, l) → t.length ≤ K →
          runPassiveProtocol read (boundedTree policy (K + 1) h) x = t ∧
            policy (h ++ t) = .inr l := by
      intro n
      induction n with
      | zero => simp [execute]
      | succ n ih =>
        intro K h x t l he hb
        cases hp : policy h with
        | inr label =>
          have equal : ([], label) = (t, l) := by simpa only [execute, hp, Option.some.injEq] using he
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
          simp [boundedTree, hp, runPassiveProtocol]
        | inl q =>
          simp only [execute, hp] at he
          obtain ⟨tail, etail, et⟩ := Option.map_eq_some_iff.mp he
          have ht : ⟨q, read q x⟩ :: tail.1 = t := congrArg Prod.fst et
          have hl : tail.2 = l := congrArg Prod.snd et
          cases K with
          | zero => simp only [← ht, List.length_cons] at hb; omega
          | succ K =>
            have small : tail.1.length ≤ K := by simp only [← ht, List.length_cons] at hb; omega
            obtain ⟨run, terminal⟩ := ih K (h ++ [⟨q, read q x⟩]) x
              tail.1 tail.2 etail small
            constructor
            · rw [boundedTree, hp, runPassiveProtocol, run]
              exact ht
            · rw [← ht, ← hl]
              simpa only [List.append_assoc, List.singleton_append] using terminal
    have tree_raw (p : PassiveProtocol Q Y) (d : Hist Y → L) (x : W) :
        execute read (treePolicy p d) ((runPassiveProtocol read p x).length + 1) [] x =
          some (runPassiveProtocol read p x, d (runPassiveProtocol read p x)) := by
      have aux : ∀ (t : PassiveProtocol Q Y) h, residual p h = t →
          execute read (treePolicy p d) ((runPassiveProtocol read t x).length + 1) h x =
            some (runPassiveProtocol read t x, d (h ++ runPassiveProtocol read t x)) := by
        intro t
        induction t with
        | stop =>
          intro h he
          simp [runPassiveProtocol, execute, treePolicy, he]
        | query q next ih =>
          intro h he
          have hn : residual p (h ++ [⟨q, read q x⟩]) = next (read q x) := by
            simp only [D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual,
              List.foldl_append, List.foldl_cons, List.foldl_nil]
            change advance (residual p h) ⟨q, read q x⟩ = _
            simp [he, advance]
          have hp : treePolicy p d h = .inl q := by simp [treePolicy, he]
          simp only [runPassiveProtocol, List.length_cons, Nat.add_assoc]
          change execute read (treePolicy p d)
            ((runPassiveProtocol read (next (read q x)) x).length + 1 + 1) h x = _
          rw [execute, hp]
          dsimp only
          rw [ih _ _ hn]
          simp [List.append_assoc]
      simpa [D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual] using aux p [] rfl
    constructor
    · rintro ⟨T, identifies, bound⟩
      let decode (h : Hist Y) : L := if hh : ∃ x, runPassiveProtocol read T x = h then
        target (Classical.choose hh) else Classical.choice (inferInstance : Nonempty L)
      have decoded (x : W) : decode (runPassiveProtocol read T x) = target x := by
        dsimp only [decode]
        have hh : ∃ y : W, runPassiveProtocol read T y = runPassiveProtocol read T x := ⟨x, rfl⟩
        rw [dif_pos hh]
        exact identifies _ x (Classical.choose_spec hh)
      refine ⟨treePolicy T decode, runPassiveProtocol read T,
        fun x => (runPassiveProtocol read T x).length + 1, ?_, bound⟩
      intro x
      simpa only [decoded] using tree_raw T decode x
    · rintro ⟨policy, trace, fuel, correct, bound⟩
      let T := boundedTree policy (K + 1) []
      have execution (x : W) := raw_tree policy (fuel x) K [] x (trace x) (target x)
        (correct x) (bound x)
      refine ⟨T, ?_, ?_⟩
      · intro x y same
        have ht : trace x = trace y := (execution x).1.symm.trans
          (same.trans (execution y).1)
        have hx : policy (trace x) = .inr (target x) := by simpa using (execution x).2
        have hy : policy (trace y) = .inr (target y) := by simpa using (execution y).2
        exact Sum.inr.inj (hx.symm.trans ((congrArg policy ht).trans hy))
      · intro x
        change (runPassiveProtocol read (boundedTree policy (K + 1) []) x).length ≤ K
        rw [(execution x).1]
        exact bound x
  have budgets_equal : acquisitionBudgets H = treeAcquisitionBudgets H := by
    ext K
    exact (budget_equivalence (terminalGcd H) (residueSource H) K).symm
  have upper_bound (H : ℕ) (hH : 1 < H) :
      ∃ T : PassiveProtocol (List Bool) (fun _ => ℕ),
        (∀ v v' : ℕ × ℕ,
          runPassiveProtocol (terminalGcd H) T v =
            runPassiveProtocol (terminalGcd H) T v' →
              residueSource H v = residueSource H v') ∧
        ∀ v : ℕ × ℕ,
          (runPassiveProtocol (terminalGcd H) T v).length ≤ 2 * costBound H := by
    classical
    have synchronize_reflects {ι : Type} (X : ι → Type) [∀ i, Zero (X i)]
        (readout : ∀ i, X i → X i → ℕ)
        (B : ℕ) (T : ∀ i, PassiveProtocol (X i) (fun _ => ℕ))
        (y z : ∀ i, X i)
        (hy : ∀ i, (runPassiveProtocol (readout i) (T i) (y i)).length ≤ B)
        (hz : ∀ i, (runPassiveProtocol (readout i) (T i) (z i)).length ≤ B)
        (same : runPassiveProtocol (fun c x i => readout i (c i) (x i))
            (synchronize X B T) y =
          runPassiveProtocol (fun c x i => readout i (c i) (x i))
            (synchronize X B T) z) :
        ∀ i, runPassiveProtocol (readout i) (T i) (y i) =
          runPassiveProtocol (readout i) (T i) (z i) := by
      induction B generalizing T with
      | zero =>
        intro i
        have ey := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hy i))
        have ez := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hz i))
        exact ey.trans ez.symm
      | succ B ih =>
        simp only [synchronize, runPassiveProtocol, List.cons.injEq] at same
        have answers :
            (fun i => readout i (rootCenter X i (T i)) (y i)) =
              (fun i => readout i (rootCenter X i (T i)) (z i)) :=
          congrArg (fun t : Sigma (fun _ : (∀ i, X i) => ι → ℕ) => t.2) same.1
        have shorter (x : ∀ i, X i)
            (hx : ∀ i, (runPassiveProtocol (readout i) (T i) (x i)).length ≤ B + 1) :
            ∀ i, (runPassiveProtocol (readout i)
              (descend X i (T i) (readout i (rootCenter X i (T i)) (x i)))
              (x i)).length ≤ B := by
          intro i
          have h := hx i
          cases he : T i with
          | stop => simp [descend, runPassiveProtocol]
          | query c next =>
            simp only [he, runPassiveProtocol, List.length_cons] at h
            simpa only [descend, rootCenter] using Nat.le_of_succ_le_succ h
        have ai (i : ι) := congrFun answers i
        have descendants :
            (fun i => descend X i (T i) (readout i (rootCenter X i (T i)) (y i))) =
              (fun i => descend X i (T i) (readout i (rootCenter X i (T i)) (z i))) := by
          funext i
          rw [ai i]
        have tails := ih (fun i => descend X i (T i)
          (readout i (rootCenter X i (T i)) (y i)))
          (shorter y hy) (by intro i; simpa only [← ai i] using shorter z hz i)
          (by simpa only [← descendants] using same.2)
        intro i
        cases he : T i with
        | stop => rfl
        | query c next =>
          have eqAnswer : readout i c (y i) = readout i c (z i) := by
            simpa only [he, rootCenter] using ai i
          simpa only [he, descend, rootCenter, runPassiveProtocol, eqAnswer] using
            congrArg (List.cons ⟨c, readout i c (y i)⟩) (tails i)
    have synchronize_length {ι : Type} (X : ι → Type) [∀ i, Zero (X i)]
        (readout : ∀ i, X i → X i → ℕ)
        (B : ℕ) (T : ∀ i, PassiveProtocol (X i) (fun _ => ℕ))
        (y : ∀ i, X i) :
        (runPassiveProtocol (fun c x i => readout i (c i) (x i))
          (synchronize X B T) y).length = B := by
      induction B generalizing T with
      | zero => rfl
      | succ B ih => simp only [synchronize, runPassiveProtocol, List.length_cons, ih]
    have gcd_depth_response (H : ℕ) (p : H.primeFactors) (c y : ZMod H) :
        gcdDepth p.val (H.factorization p.val) (Nat.gcd (y - c).val H) =
          residueReadout p.val (H.factorization p.val)
            (localProjection H p c) (localProjection H p y) := by
      classical
      let e := H.factorization p.val
      have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
      letI : NeZero H := ⟨(Nat.mem_primeFactors.mp p.property).2.2⟩
      letI : NeZero (p.val ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
      unfold gcdDepth residueReadout
      congr 1
      ext j
      by_cases hj : j ∈ Finset.range (e + 1)
      · have hje : j ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        letI : NeZero (p.val ^ j) := ⟨pow_ne_zero _ hp.ne_zero⟩
        simp only [e] at hj
        have hd : p.val ^ j ∣ H :=
          dvd_trans (pow_dvd_pow p.val hje) (Nat.ordProj_dvd H p.val)
        let π := ZMod.castHom hd (ZMod (p.val ^ j))
        let ρ := primePowerProjection p.val hje
        have composition (a : ZMod H) : ρ (localProjection H p a) = π a := by
          exact DFunLike.congr_fun
            (ZMod.castHom_comp (pow_dvd_pow p.val hje) (Nat.ordProj_dvd H p.val)) a
        have congruence (a b : ZMod (p.val ^ e)) :
            a.val % p.val ^ j = b.val % p.val ^ j ↔ ρ a = ρ b := by
          simp only [ρ, primePowerProjection, ZMod.castHom_apply, ZMod.cast_eq_val,
            ZMod.natCast_eq_natCast_iff']
        simp only [Finset.mem_filter, hj, true_and, Nat.dvd_gcd_iff, hd, and_true]
        rw [congruence, composition, composition]
        change p.val ^ j ∣ (y - c).val ↔ π y = π c
        rw [← ZMod.natCast_eq_zero_iff (y - c).val (p.val ^ j)]
        have hpcast : π (y - c) = ((y - c).val : ZMod (p.val ^ j)) := by
          simp only [π, ZMod.castHom_apply, ZMod.cast_eq_val]
        rw [← hpcast]
        rw [map_sub, sub_eq_zero]
      · simp only [e] at hj
        simp only [Finset.mem_filter, hj, false_and]
    have scalar_word_realization (H : ℕ) (hH : 1 < H) (k : ℕ) (c : ZMod H) :
        (∀ v : ℕ × ℕ,
          (quantity (runWord (scalarWord H k c) v) : ZMod H) = scalar H k v + c) ∧
        (scalarWord H k c).length ≤ (H * H).factorial + k + 2 * (H - 1) := by
      classical
      letI : NeZero H := ⟨by omega⟩
      let r := residueReplace H
      let L := (H * H).factorial
      have hL : 0 < L := Nat.factorial_pos _
      have cycle : r ^ L = 1 := by
        have h := pow_card_eq_one (x := r)
        simpa only [Fintype.card_perm, Fintype.card_prod, ZMod.card] using h
      have append (w u : List Bool) (v : ℕ × ℕ) :
          runWord (w ++ u) v = runWord u (runWord w v) := by
        induction w generalizing v with
        | nil => rfl
        | cons b w ih => exact ih (step b v)
      have reps (b : Bool) (a : ℕ) (v : ℕ × ℕ) :
          runWord (List.replicate a b) v = (step b)^[a] v := by
        induction a generalizing v with
        | zero => rfl
        | succ a ih =>
          simpa only [List.replicate_succ, runWord, Function.iterate_succ_apply] using
            ih (step b v)
      have commute : Function.Semiconj (residueSource H) replace r := by
        intro v
        ext <;> simp [residueSource, replace, r, residueReplace]
      have rreps (a : ℕ) (v : ℕ × ℕ) :
          residueSource H (runWord (List.replicate a true) v) =
            (r ^ a) (residueSource H v) := by
        rw [reps]
        simpa only [step, Bool.true_eq_false, ↓reduceIte, Equiv.Perm.coe_pow] using
          commute.iterate_right a v
      have greps (a : ℕ) (v : ℕ × ℕ) :
          residueSource H (runWord (List.replicate a false) v) =
            ((residueSource H v).1 + a, (residueSource H v).2) := by
        induction a generalizing v with
        | zero => simp [runWord, residueSource]
        | succ a ih =>
          rw [List.replicate_succ, runWord, ih]
          ext <;> simp [step, graft, residueSource, Nat.cast_add] <;> ring
      have addmap (j : ℕ) (u v : ZMod H × ZMod H) :
          (r ^ j) (u + v) = (r ^ j) u + (r ^ j) v := by
        induction j with
        | zero => simp
        | succ j ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, ih]
          ext <;> simp [r, residueReplace] <;> ring
      have negatePeriod (u : ZMod H × ZMod H) :
          r ((r ^ (L - 1)) u) = u := by
        have he := congrArg (fun s : Equiv.Perm (ZMod H × ZMod H) => s u) cycle
        simpa only [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hL,
          Equiv.Perm.one_apply] using he
      have shifted (u : ZMod H × ZMod H) (a : ZMod H) :
          (u.1 + a, u.2) = u + (a, 0) := by ext <;> simp
      constructor
      · intro v
        have finish :
            residueSource H (runWord (scalarWord H k c) v) =
              (r ^ k) (residueSource H v) + ((-c), c) := by
          simp only [scalarWord, append]
          rw [show [true] = List.replicate 1 true from rfl]
          simp only [rreps, greps, ZMod.natCast_zmod_val, pow_one]
          rw [shifted, shifted]
          change r ((r ^ (L - 1)) ((r ^ k) (residueSource H v) + ((-c), 0)) + (c, 0)) = _
          rw [show r (_ + _) = r _ + r _ from addmap 1 _ _, negatePeriod]
          ext <;> simp [r, residueReplace] <;> ring
        have finished := congrArg (fun u : ZMod H × ZMod H => 2 * u.1 + 3 * u.2) finish
        convert finished using 1 <;>
          simp only [quantity, residueSource, scalar, r, Nat.cast_add, Nat.cast_mul,
            Nat.cast_ofNat, Prod.fst_add, Prod.snd_add] <;> ring
      · have hc := c.val_lt
        have hn := (-c).val_lt
        simp only [scalarWord, List.length_append, List.length_replicate,
          List.length_singleton]
        change k + (-c).val + (L - 1) + c.val + 1 ≤ L + k + 2 * (H - 1)
        omega
    letI : NeZero H := ⟨by omega⟩
    let X (p : H.primeFactors) := ZMod (p.val ^ H.factorization p.val)
    let crt : ZMod H ≃+* ∀ p : H.primeFactors, X p := ZMod.equivPi H (by omega)
    let readout (c y : ∀ p : H.primeFactors, X p) (p : H.primeFactors) :=
      residueReadout p.val (H.factorization p.val) (c p) (y p)
    have crt_projection (y : ZMod H) (p : H.primeFactors) :
        crt y p = localProjection H p y := by
      exact RingHom.congr_fun
        (Subsingleton.elim ((Pi.evalRingHom X p).comp crt.toRingHom)
          (localProjection H p)) y
    have local_protocol (p : H.primeFactors) :
        ∃ T : PassiveProtocol (X p) (fun _ => ℕ),
          Function.Injective
            (runPassiveProtocol (residueReadout p.val (H.factorization p.val)) T) ∧
          ∀ y : X p,
            (runPassiveProtocol (residueReadout p.val (H.factorization p.val)) T y).length ≤
              costBound H := by
      letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      obtain ⟨T, identifies, lengths⟩ :=
        residue_height_upper_bound p.val (H.factorization p.val) 0 (Nat.zero_le _) 0
      have member (y : X p) :
          y ∈ node p.val (H.factorization p.val) 0 (Nat.zero_le _) 0 := by
        simp only [node, Finset.mem_filter, Finset.mem_univ, true_and]
        have singleton : Subsingleton (ZMod (p.val ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact singleton.elim _ _
      refine ⟨T, fun y z same => identifies (member y) (member z) same, ?_⟩
      intro y
      have bound := lengths y (member y)
      simp only [Nat.sub_zero] at bound
      exact bound.trans
        (Finset.le_sup (f := fun q => H.factorization q * (q - 1)) p.property)
    choose localTrees localIdentifies localBounds using local_protocol
    let joint := synchronize X (costBound H) localTrees
    have joint_identifies : Function.Injective (runPassiveProtocol readout joint) := by
      intro y z same
      have localSame := synchronize_reflects X
        (fun p => residueReadout p.val (H.factorization p.val))
        (costBound H) localTrees y z (fun p => localBounds p (y p))
        (fun p => localBounds p (z p)) same
      funext p
      exact localIdentifies p (localSame p)
    have joint_length (y : ∀ p : H.primeFactors, X p) :
        (runPassiveProtocol readout joint y).length = costBound H :=
      synchronize_length X (fun p => residueReadout p.val (H.factorization p.val))
        (costBound H) localTrees y
    have word_answers (k : ℕ) (centers : ∀ p : H.primeFactors, X p) (v : ℕ × ℕ) :
        (fun p => gcdDepth p.val (H.factorization p.val)
          (terminalGcd H (scalarWord H k (-crt.symm centers)) v)) =
            readout centers (crt (scalar H k v)) := by
      have realized := (scalar_word_realization H hH k (-crt.symm centers)).1 v
      have modvalue : quantity (runWord (scalarWord H k (-crt.symm centers)) v) % H =
          (scalar H k v - crt.symm centers).val := by
        simpa only [ZMod.val_natCast, sub_eq_add_neg] using congrArg ZMod.val realized
      have gcd_eq : terminalGcd H (scalarWord H k (-crt.symm centers)) v =
          Nat.gcd (scalar H k v - crt.symm centers).val H := by
        unfold terminalGcd
        rw [Nat.gcd_comm, Nat.gcd_rec, modvalue]
      funext p
      rw [gcd_eq, gcd_depth_response]
      dsimp only [readout]
      rw [← crt_projection, ← crt_projection, crt.apply_symm_apply]
    have actual_reflects (k : ℕ)
        (U : PassiveProtocol (∀ p : H.primeFactors, X p)
          (fun _ => H.primeFactors → ℕ)) (v v' : ℕ × ℕ)
        (same : runPassiveProtocol (terminalGcd H) (actualize H k crt U) v =
          runPassiveProtocol (terminalGcd H) (actualize H k crt U) v') :
        runPassiveProtocol readout U (crt (scalar H k v)) =
          runPassiveProtocol readout U (crt (scalar H k v')) := by
      induction U with
      | stop => rfl
      | query centers next ih =>
        simp only [actualize, runPassiveProtocol, List.cons.injEq] at same
        have answers : terminalGcd H (scalarWord H k (-crt.symm centers)) v =
            terminalGcd H (scalarWord H k (-crt.symm centers)) v' := congrArg
          (fun a : Sigma (fun _ : List Bool => ℕ) => a.2) same.1
        have local_answers := congrArg
          (fun g => fun p : H.primeFactors => gcdDepth p.val (H.factorization p.val) g)
          answers
        rw [word_answers, word_answers] at local_answers
        simp only [runPassiveProtocol]
        rw [local_answers]
        congr 1
        apply ih
        simpa only [word_answers, local_answers] using same.2
    have actual_length (k : ℕ)
        (U : PassiveProtocol (∀ p : H.primeFactors, X p)
          (fun _ => H.primeFactors → ℕ)) (v : ℕ × ℕ) :
        (runPassiveProtocol (terminalGcd H) (actualize H k crt U) v).length =
          (runPassiveProtocol readout U (crt (scalar H k v))).length := by
      induction U with
      | stop => rfl
      | query centers next ih =>
        simp only [actualize, runPassiveProtocol, List.length_cons, ih, word_answers]
    let first := actualize H 0 crt joint
    let second := actualize H 1 crt joint
    have concatenate_length (T U : PassiveProtocol (List Bool) (fun _ => ℕ))
        (v : ℕ × ℕ) :
        (runPassiveProtocol (terminalGcd H) (concatenate T U) v).length =
          (runPassiveProtocol (terminalGcd H) T v).length +
            (runPassiveProtocol (terminalGcd H) U v).length := by
      induction T with
      | stop => simp only [concatenate, runPassiveProtocol, List.length_nil, Nat.zero_add]
      | query w next ih =>
        simp only [concatenate, runPassiveProtocol, List.length_cons, ih]
        omega
    have concatenate_reflects (T U : PassiveProtocol (List Bool) (fun _ => ℕ))
        (v v' : ℕ × ℕ)
        (same : runPassiveProtocol (terminalGcd H) (concatenate T U) v =
          runPassiveProtocol (terminalGcd H) (concatenate T U) v') :
        runPassiveProtocol (terminalGcd H) T v = runPassiveProtocol (terminalGcd H) T v' ∧
          runPassiveProtocol (terminalGcd H) U v = runPassiveProtocol (terminalGcd H) U v' := by
      induction T with
      | stop => exact ⟨rfl, same⟩
      | query w next ih =>
        simp only [concatenate, runPassiveProtocol, List.cons.injEq] at same
        have answers : terminalGcd H w v = terminalGcd H w v' := congrArg
          (fun a : Sigma (fun _ : List Bool => ℕ) => a.2) same.1
        obtain ⟨ht, hu⟩ := ih (terminalGcd H w v) (by simpa only [answers] using same.2)
        refine ⟨?_, hu⟩
        simp only [runPassiveProtocol]
        rw [← answers]
        exact congrArg (List.cons ⟨w, terminalGcd H w v⟩) ht
    refine ⟨concatenate first second, ?_, ?_⟩
    · intro v v' same
      obtain ⟨hfirst, hsecond⟩ := concatenate_reflects first second v v' same
      have hn := crt.injective (joint_identifies (actual_reflects 0 joint v v' hfirst))
      have hz := crt.injective (joint_identifies (actual_reflects 1 joint v v' hsecond))
      have hnn : (2 : ZMod H) * v.1 + 3 * v.2 = 2 * v'.1 + 3 * v'.2 := by
        simpa [scalar, residueSource] using hn
      have hzz : (3 : ZMod H) * v.1 + 5 * v.2 = 3 * v'.1 + 5 * v'.2 := by
        have h : (2 : ZMod H) * v.2 + 3 * ((v.1 : ZMod H) + v.2) =
            2 * v'.2 + 3 * ((v'.1 : ZMod H) + v'.2) := by
          simpa [scalar, residueSource, residueReplace] using hz
        linear_combination h
      ext
      · calc
          (v.1 : ZMod H) = 5 * (2 * v.1 + 3 * v.2) -
              3 * (3 * v.1 + 5 * v.2) := by ring
          _ = 5 * (2 * v'.1 + 3 * v'.2) - 3 * (3 * v'.1 + 5 * v'.2) := by rw [hnn, hzz]
          _ = v'.1 := by ring
      · calc
          (v.2 : ZMod H) = -3 * (2 * v.1 + 3 * v.2) +
              2 * (3 * v.1 + 5 * v.2) := by ring
          _ = -3 * (2 * v'.1 + 3 * v'.2) + 2 * (3 * v'.1 + 5 * v'.2) := by rw [hnn, hzz]
          _ = v'.2 := by ring
    · intro v
      rw [concatenate_length, actual_length, actual_length, joint_length, joint_length]
      omega

  have lower_axis (H p e : ℕ) (hH : 1 < H) (hp : p.Prime) (he : 1 ≤ e)
      (hexact : e = H.factorization p)
      (T : PassiveProtocol (List Bool) (fun _ => ℕ))
      (identifies : ∀ v v' : ℕ × ℕ,
        runPassiveProtocol (terminalGcd H) T v =
          runPassiveProtocol (terminalGcd H) T v' →
            residueSource H v = residueSource H v') :
      ∃ v : ℕ × ℕ, 2 * e * (p - 1) ≤
        (runPassiveProtocol (terminalGcd H) T v).length := by
    classical
    have hH0 : H ≠ 0 := by omega
    letI : NeZero H := ⟨hH0⟩
    letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    let X := Point p e 2
    let D := H / p ^ e
    have hP : p ^ e ∣ H := by rw [hexact]; exact Nat.ordProj_dvd H p
    have hsplit : H = D * p ^ e := (Nat.div_mul_cancel hP).symm
    have hD : 0 < D := by
      dsimp [D]
      rw [hexact]
      exact Nat.ordCompl_pos p hH0
    have hcop : Nat.Coprime D (p ^ e) := by
      dsimp [D]
      rw [hexact]
      exact (Nat.coprime_ordCompl hp hH0).symm.pow_right _
    let source (x : X) : ℕ × ℕ := (D * (x 0).val, D * (x 1).val)
    have source_injective : Function.Injective (fun x : X => residueSource H (source x)) := by
      intro x y same
      have coordinate (i : Fin 2)
          (eq : ((D * (x i).val : ℕ) : ZMod H) = ((D * (y i).val : ℕ) : ZMod H)) : x i = y i := by
        have bx : D * (x i).val < H := by
          rw [hsplit]
          exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hD
        have by' : D * (y i).val < H := by
          rw [hsplit]
          exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hD
        have integer := congrArg ZMod.val eq
        simp only [ZMod.val_natCast, Nat.mod_eq_of_lt bx, Nat.mod_eq_of_lt by'] at integer
        apply ZMod.val_injective (p ^ e)
        exact Nat.eq_of_mul_eq_mul_left hD integer
      funext i
      fin_cases i
      · exact coordinate 0 (congrArg Prod.fst same)
      · exact coordinate 1 (congrArg Prod.snd same)
    have word_affine (w : List Bool) :
        ∃ A B C : ℕ, ∀ v : ℕ × ℕ,
          quantity (runWord w v) = A * v.1 + B * v.2 + C := by
      induction w with
      | nil => exact ⟨2, 3, 0, fun v => by simp [runWord, quantity]⟩
      | cons b w ih =>
        obtain ⟨A, B, C, representation⟩ := ih
        cases b
        · refine ⟨A, B, A + C, ?_⟩
          intro v
          rw [runWord, representation]
          simp only [step, Bool.false_eq_true, ↓reduceIte, graft]
          ring
        · refine ⟨B, A + B, C, ?_⟩
          intro v
          rw [runWord, representation]
          simp only [step, ↓reduceIte, replace]
          ring
    have local_gcd (n : ℕ) :
        Nat.gcd n (p ^ e) = p ^ residueReadout p e 0 (n : ZMod (p ^ e)) := by
      obtain ⟨s, hs, hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n (p ^ e))
      have depth_eq : residueReadout p e 0 (n : ZMod (p ^ e)) = s := by
        apply le_antisymm
        · apply Finset.sup_le
          intro j hj
          obtain ⟨hje, hz⟩ := Finset.mem_filter.mp hj
          have hje' : j ≤ e := by have := Finset.mem_range.mp hje; omega
          have hd : p ^ j ∣ p ^ e := pow_dvd_pow p hje'
          have hn : p ^ j ∣ n := by
            apply Nat.dvd_of_mod_eq_zero
            simpa only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_mod,
              Nat.mod_mod_of_dvd n hd] using hz
          have divides := Nat.dvd_gcd hn hd
          rw [hg] at divides
          exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp divides
        · apply Finset.le_sup (f := id)
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
          have hn : p ^ s ∣ n := by rw [← hg]; exact Nat.gcd_dvd_left n _
          simp only [ZMod.val_natCast, ZMod.val_zero, Nat.zero_mod,
            Nat.mod_mod_of_dvd n (pow_dvd_pow p hs)]
          exact Nat.mod_eq_zero_of_dvd hn
      rw [depth_eq]
      exact hg
    have word_response (w : List Bool) :
        ∃ q : AffineQuery p e 2, ∃ dW : ℕ, 0 < dW ∧
          ∀ x : X, terminalGcd H w (source x) = dW * p ^ affineReadout p e 2 q x := by
      obtain ⟨A, B, C, representation⟩ := word_affine w
      let q : AffineQuery p e 2 :=
        ((fun i => if i = 0 then (D * A : ZMod (p ^ e)) else (D * B : ZMod (p ^ e))),
          (C : ZMod (p ^ e)))
      refine ⟨q, Nat.gcd C D, Nat.gcd_pos_of_pos_right C hD, ?_⟩
      intro x
      let n := quantity (runWord w (source x))
      have formula : n = D * (A * (x 0).val + B * (x 1).val) + C := by
        dsimp [n]
        rw [representation]
        dsimp [source]
        ring
      have constant : Nat.gcd n D = Nat.gcd C D := by
        rw [formula, Nat.gcd_comm]
        rw [Nat.gcd_mul_left_add_right, Nat.gcd_comm]
      have query : affineValue q x = (n : ZMod (p ^ e)) := by
        rw [formula]
        have one_ne_zero : (1 : Fin 2) ≠ 0 := by decide
        simp only [affineValue, q, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
          Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, one_ne_zero]
        ring
      unfold terminalGcd
      change Nat.gcd n H = _
      rw [hsplit, Nat.Coprime.gcd_mul n hcop, constant, local_gcd]
      rw [affineReadout, query]
    choose query divisor positive responses using word_response
    have simulation (S : PassiveProtocol (List Bool) (fun _ => ℕ)) :
        ∃ U : PassiveProtocol (AffineQuery p e 2) (fun _ => ℕ),
          (∀ x : X,
            (runPassiveProtocol (affineReadout p e 2) U x).length =
              (runPassiveProtocol (terminalGcd H) S (source x)).length) ∧
          (∀ x y : X,
            runPassiveProtocol (affineReadout p e 2) U x =
              runPassiveProtocol (affineReadout p e 2) U y →
            runPassiveProtocol (terminalGcd H) S (source x) =
              runPassiveProtocol (terminalGcd H) S (source y)) := by
      induction S with
      | stop => exact ⟨.stop, fun _ => rfl, fun _ _ _ => rfl⟩
      | query w next ih =>
        choose children lengths reflects using ih
        let decode (r : ℕ) := divisor w * p ^ r
        refine ⟨.query (query w) (fun r => children (decode r)), ?_, ?_⟩
        · intro x
          simp only [runPassiveProtocol, List.length_cons]
          rw [responses]
          exact congrArg Nat.succ (lengths _ x)
        · intro x y same
          simp only [runPassiveProtocol, List.cons.injEq] at same
          have answers : affineReadout p e 2 (query w) x =
              affineReadout p e 2 (query w) y := congrArg
            (fun a : Sigma (fun _ : AffineQuery p e 2 => ℕ) => a.2) same.1
          have tails := reflects (decode (affineReadout p e 2 (query w) x)) x y
            (by simpa only [answers] using same.2)
          simp only [runPassiveProtocol, responses]
          change (⟨w, decode (affineReadout p e 2 (query w) x)⟩ :
            Sigma (fun _ : List Bool => ℕ)) :: _ =
            (⟨w, decode (affineReadout p e 2 (query w) y)⟩ :
              Sigma (fun _ : List Bool => ℕ)) :: _
          rw [← answers]
          exact congrArg (List.cons ⟨w, decode (affineReadout p e 2 (query w) x)⟩) tails
    obtain ⟨U, lengths, reflects⟩ := simulation T
    have injective : Function.Injective (runPassiveProtocol (affineReadout p e 2) U) := by
      intro x y same
      exact source_injective (identifies _ _ (reflects x y same))
    obtain ⟨x, hard⟩ := (affine_valuation_query_lower_bound p e 2 hp he (by decide)).1 U injective
    exact ⟨source x, by simpa only [lengths] using hard⟩

  by_cases h1 : H = 1
  · subst H
    have least : IsLeast (treeAcquisitionBudgets 1) 0 := by
      constructor
      · refine ⟨.stop, ?_, ?_⟩
        · intro v w _
          exact Subsingleton.elim _ _
        · intro v
          simp only [runPassiveProtocol, List.length_nil, le_refl]
      · intro K _
        exact Nat.zero_le K
    have raw_least : IsLeast (acquisitionBudgets 1) 0 := by rw [budgets_equal]; exact least
    exact ⟨by simpa using raw_least, by simpa [acquisitionCost] using raw_least.csInf_eq⟩
  · have hHgt : 1 < H := by omega
    have least : IsLeast (treeAcquisitionBudgets H) (2 * costBound H) := by
      constructor
      · exact upper_bound H hHgt
      · intro K feasible
        obtain ⟨T, identifies, lengths⟩ := feasible
        obtain ⟨p, hp, maximal⟩ := Finset.sup_mem_of_nonempty
          (f := fun p => H.factorization p * (p - 1))
          (Nat.nonempty_primeFactors.mpr hHgt)
        have prime := (Nat.mem_primeFactors.mp hp).1
        have positive : 1 ≤ H.factorization p := by
          exact prime.factorization_pos_of_dvd (by omega : H ≠ 0)
            (Nat.mem_primeFactors.mp hp).2.1
        obtain ⟨v, hard⟩ := lower_axis H p (H.factorization p) hHgt prime positive rfl T identifies
        rw [costBound, ← maximal]
        have reordered : 2 * (H.factorization p * (p - 1)) ≤
            (runPassiveProtocol (terminalGcd H) T v).length := by
          simpa only [Nat.mul_assoc] using hard
        exact reordered.trans (lengths v)
    have raw_least : IsLeast (acquisitionBudgets H) (2 * costBound H) := by
      rw [budgets_equal]
      exact least
    exact ⟨by simpa only [h1, ↓reduceIte] using raw_least,
      by simpa only [acquisitionCost, h1, ↓reduceIte] using raw_least.csInf_eq⟩

#print axioms terminal_gcd_acquisition_cost

end D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
