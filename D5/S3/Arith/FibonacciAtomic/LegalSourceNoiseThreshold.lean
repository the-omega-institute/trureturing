/- GID: D5/S3/Arith/FibonacciAtomic/LegalSourceNoiseThreshold
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LegalSourceNoiseThreshold
   mirror-E: none(waiver:exact-symbolic-noise-boundary)
   anchors: []
   utility: none
   digest: Legal five-window sources have a sharp current-row update-noise threshold. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Nat.SuccPred
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.LegalSourceNoiseThreshold

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.ZeckendorfFutureKernel (legal)
open D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization (noisyRun)
open scoped BigOperators Matrix

abbrev Row := Fin 3 → ℝ
abbrev State := Option (Bool × Bool)

/-- The coordinates are End, End after 100, and End after 010. -/
def canonical : State → Row
  | none => ![0, 0, 0]
  | some (s, E) => ![if E then 1 else 0, if s then 0 else 1, 1]

/-- A low occupied bit reads the second coordinate; the other letters read the third. -/
def readIndex (a : Window) : Fin 3 := if first a then 1 else 2

def target (a : Window) : Row := canonical (some (last a, nonzero a))

/-- The five original outer products, over the real extension of their rational entries. -/
def matrix (a : Window) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec (Pi.single (readIndex a) 1) (target a)

def actual (lam : ℝ) (p : List (Window × Row)) : Row :=
  noisyRun (fun a y => lam • (y ᵥ* matrix a)) (canonical (some (false, false))) p

def noiseBound (ν : ℝ) (p : List (Window × Row)) : Prop :=
  ∀ e ∈ p, ‖e.2‖ ≤ ν

def geometric (lam : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, lam ^ j

def threshold (lam : ℝ) (M : ℕ) : ℝ := lam ^ M / (geometric lam M + 1)

/-- `fixed=false` ranges over all depths up to M; `fixed=true` selects exactly M. -/
def depthAllowed (fixed : Bool) (M n : ℕ) : Prop := if fixed then n = M else n ≤ M

def Recovery {Y : Type*} (out : State → Y) (lam ν : ℝ) (M : ℕ) (fixed : Bool) : Prop :=
  ∃ decode : Row → Y, ∀ p : List (Window × Row),
    depthAllowed fixed M p.length → legal false (flatten (p.map Prod.fst)) →
    noiseBound ν p → decode (actual lam p) = out (run (some (false, false)) (p.map Prod.fst))

def ClockRecovery {Y : Type*} (out : State → Y) (lam ν : ℝ) (M : ℕ)
    (fixed : Bool) : Prop :=
  ∃ decode : ℕ → Row → Y, ∀ p : List (Window × Row),
    depthAllowed fixed M p.length → legal false (flatten (p.map Prod.fst)) →
    noiseBound ν p → decode p.length (actual lam p) =
      out (run (some (false, false)) (p.map Prod.fst))

/-- Arbitrary legal trajectories retain a one-sided margin on occupied coordinates;
zero coordinates retain only their most recent error. -/
private theorem coordinate_invariant (lam ν : ℝ) (hlam : 0 ≤ lam)
    (p : List (Window × Row)) :
    ∀ (s E : Bool) (y : Row) (k : ℕ),
      legal s (flatten (p.map Prod.fst)) → noiseBound ν p →
      (∀ r, canonical (some (s, E)) r = 0 → |y r| ≤ ν) →
      (∀ r, canonical (some (s, E)) r = 1 → lam ^ k - ν * geometric lam k ≤ y r) →
      ∀ r,
        (canonical (run (some (s, E)) (p.map Prod.fst)) r = 0 →
          |noisyRun (fun a x => lam • (x ᵥ* matrix a)) y p r| ≤ ν) ∧
        (canonical (run (some (s, E)) (p.map Prod.fst)) r = 1 →
          lam ^ (k + p.length) - ν * geometric lam (k + p.length) ≤
            noisyRun (fun a x => lam • (x ᵥ* matrix a)) y p r) := by
  induction p with
  | nil =>
      intro s E y k _ _ hz ho r
      exact ⟨hz r, by simpa [run, noisyRun] using ho r⟩
  | cons e p ih =>
      rcases e with ⟨a, ξ⟩
      intro s E y k hlegal hnoise hz ho
      have dead (w : List Window) : run none w = none := by
        have h := (execution false false (.high :: .low :: w)).2.mpr
          (by simp [flatten, bits, legal])
        simpa [run, step, first, last, nonzero] using h
      have live := (execution s E (a :: p.map Prod.fst)).1.mpr hlegal
      have guard : (s && first a) = false := by
        cases s <;> cases a <;> simp [run, step, first, dead] at live ⊢
      have tailLegal : legal (last a) (flatten (p.map Prod.fst)) := by
        apply (execution (last a) (nonzero a) (p.map Prod.fst)).1.mp
        simpa [run, step, guard, List.foldl_cons] using live
      have readOne : canonical (some (s, E)) (readIndex a) = 1 := by
        cases s <;> cases a <;> simp [canonical, readIndex, first] at guard ⊢
      have sourceLower := ho (readIndex a) readOne
      have errorBound : ∀ r, |ξ r| ≤ ν := by
        intro r
        exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm ξ r).trans
          (hnoise (a, ξ) (by simp))
      have action (x : Row) : x ᵥ* matrix a = x (readIndex a) • target a := by
        simp [matrix, Matrix.vecMul_vecMulVec]
      have newZero : ∀ r, canonical (some (last a, nonzero a)) r = 0 →
          |(lam • (y ᵥ* matrix a) + ξ) r| ≤ ν := by
        intro r hr
        simpa [action, target, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hr] using
          errorBound r
      have newOne : ∀ r, canonical (some (last a, nonzero a)) r = 1 →
          lam ^ (k + 1) - ν * geometric lam (k + 1) ≤
            (lam • (y ᵥ* matrix a) + ξ) r := by
        intro r hr
        have hξ := (abs_le.mp (errorBound r)).1
        have hmul := mul_le_mul_of_nonneg_left sourceLower hlam
        simp only [action, Pi.add_apply, Pi.smul_apply, smul_eq_mul, target, hr, mul_one]
        rw [geometric, geom_sum_succ, ← geometric, pow_succ]
        nlinarith
      have tailNoise : noiseBound ν p := fun e he => hnoise e (by simp [he])
      have h := ih (last a) (nonzero a) (lam • (y ᵥ* matrix a) + ξ)
        (k + 1) tailLegal tailNoise newZero newOne
      simpa [run, step, guard, noisyRun, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h

/-- A single coordinate threshold works at every permitted depth and needs no clock. -/
private theorem sufficient (lam ν : ℝ) (M : ℕ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hν : 0 ≤ ν) (hsmall : ν < threshold lam M)
    (fixed : Bool) :
    Recovery canonical lam ν M fixed ∧ ClockRecovery canonical lam ν M fixed ∧
      Recovery endable lam ν M fixed ∧ ClockRecovery endable lam ν M fixed := by
  classical
  have sumNonneg (n : ℕ) : 0 ≤ geometric lam n :=
    Finset.sum_nonneg fun j _ => pow_nonneg hlam0.le j
  have hden : 0 < geometric lam M + 1 := by linarith [sumNonneg M]
  have margin : ν < lam ^ M - ν * geometric lam M := by
    have h := (lt_div_iff₀ hden).mp hsmall
    nlinarith
  let τ : ℝ := (ν + (lam ^ M - ν * geometric lam M)) / 2
  have hτν : ν < τ := by dsimp [τ]; linarith
  have hτmargin : τ < lam ^ M - ν * geometric lam M := by dsimp [τ]; linarith
  have hτ0 : 0 < τ := lt_of_le_of_lt hν hτν
  have hτ1 : τ < 1 := by
    have hp : lam ^ M ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
    have hm : 0 ≤ ν * geometric lam M := mul_nonneg hν (sumNonneg M)
    linarith
  let decode : Row → Row := fun y r => if τ < y r then 1 else 0
  have valid : ∀ p : List (Window × Row), p.length ≤ M →
      legal false (flatten (p.map Prod.fst)) → noiseBound ν p →
      decode (actual lam p) = canonical (run (some (false, false)) (p.map Prod.fst)) := by
    intro p hp hl hn
    have zeroInitial : ∀ r, canonical (some (false, false)) r = 0 →
        |canonical (some (false, false)) r| ≤ ν := by
      intro r hr
      simpa only [hr, abs_zero] using hν
    have oneInitial : ∀ r, canonical (some (false, false)) r = 1 →
        lam ^ 0 - ν * geometric lam 0 ≤ canonical (some (false, false)) r := by
      intro r hr
      simp [hr, geometric]
    have bounds := coordinate_invariant lam ν hlam0.le p false false
      (canonical (some (false, false))) 0 hl hn zeroInitial oneInitial
    have lower : lam ^ M - ν * geometric lam M ≤
        lam ^ p.length - ν * geometric lam p.length := by
      have hpw := pow_le_pow_of_le_one hlam0.le hlam1.le hp
      have hsum : geometric lam p.length ≤ geometric lam M :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
          (fun j _ _ => pow_nonneg hlam0.le j)
      have hmul := mul_le_mul_of_nonneg_left hsum hν
      linarith
    funext r
    have binary : canonical (run (some (false, false)) (p.map Prod.fst)) r = 0 ∨
        canonical (run (some (false, false)) (p.map Prod.fst)) r = 1 := by
      cases run (some (false, false)) (p.map Prod.fst) with
      | none => fin_cases r <;> simp [canonical]
      | some q =>
          rcases q with ⟨s, E⟩
          cases s <;> cases E <;> fin_cases r <;> simp [canonical]
    rcases binary with hz | ho
    · have hy : actual lam p r ≤ ν :=
        (le_abs_self _).trans (by simpa [actual] using (bounds r).1 hz)
      simp only [decode, hz, if_neg (not_lt.mpr (le_trans hy hτν.le))]
    · have hy : τ < actual lam p r := by
        have hb := (bounds r).2 ho
        simp only [Nat.zero_add] at hb
        exact lt_of_lt_of_le hτmargin (le_trans lower hb)
      simp only [decode, ho, if_pos hy]
  have allowed (p : List (Window × Row)) (hp : depthAllowed fixed M p.length) :
      p.length ≤ M := by
    cases fixed with
    | false => exact hp
    | true => exact hp.le
  have stateRecovery : Recovery canonical lam ν M fixed :=
    ⟨decode, fun p hp hl hn => valid p (allowed p hp) hl hn⟩
  let label : Row → Bool := fun y => decide (y 0 = 1)
  have labelCanonical (q : State) : label (canonical q) = endable q := by
    cases q with
    | none => simp [label, canonical, endable]
    | some q => rcases q with ⟨s, E⟩; cases E <;> simp [label, canonical, endable]
  have labelRecovery : Recovery endable lam ν M fixed := by
    refine ⟨label ∘ decode, ?_⟩
    intro p hp hl hn
    change label (decode (actual lam p)) = _
    rw [valid p (allowed p hp) hl hn, labelCanonical]
  refine ⟨stateRecovery, ?_, labelRecovery, ?_⟩
  · obtain ⟨d, hd⟩ := stateRecovery
    exact ⟨fun _ => d, hd⟩
  · obtain ⟨d, hd⟩ := labelRecovery
    exact ⟨fun _ => d, hd⟩

/-- The sharp boundary holds for arbitrary row decoders, with or without a clock,
at every bounded or fixed depth. -/
theorem result (decay : ℚ) (hdecay0 : 0 < decay) (hdecay1 : decay < 1) :
    (∀ (ν : ℝ), 0 ≤ ν → ∀ (M : ℕ) (fixed : Bool),
      (Recovery canonical (decay : ℝ) ν M fixed ↔ M = 0 ∨ ν < threshold decay M) ∧
      (ClockRecovery canonical (decay : ℝ) ν M fixed ↔ M = 0 ∨ ν < threshold decay M) ∧
      (Recovery endable (decay : ℝ) ν M fixed ↔ M = 0 ∨ ν < threshold decay M) ∧
      (ClockRecovery endable (decay : ℝ) ν M fixed ↔ M = 0 ∨ ν < threshold decay M)) ∧
    (∀ (ν : ℝ), 0 ≤ ν → ∀ fixed : Bool,
      Recovery canonical (decay : ℝ) ν 0 fixed ∧ ClockRecovery canonical (decay : ℝ) ν 0 fixed ∧
      Recovery endable (decay : ℝ) ν 0 fixed ∧ ClockRecovery endable (decay : ℝ) ν 0 fixed) ∧
    (∀ (ν : ℝ), 0 ≤ ν → ∀ fixed : Bool,
      (Recovery canonical (decay : ℝ) ν 1 fixed ↔ ν < (decay : ℝ) / 2) ∧
      (ClockRecovery canonical (decay : ℝ) ν 1 fixed ↔ ν < (decay : ℝ) / 2) ∧
      (Recovery endable (decay : ℝ) ν 1 fixed ↔ ν < (decay : ℝ) / 2) ∧
      (ClockRecovery endable (decay : ℝ) ν 1 fixed ↔ ν < (decay : ℝ) / 2)) ∧
    (∀ M : ℕ, 2 ≤ M →
      (decay : ℝ) ^ M / (2 * geometric decay M) < threshold decay M) ∧
    Filter.Tendsto (threshold (decay : ℝ)) Filter.atTop (nhds 0) := by
  classical
  let lam : ℝ := decay
  have hlam : 0 < lam := by dsimp [lam]; exact_mod_cast hdecay0
  have hlam1 : lam < 1 := by dsimp [lam]; exact_mod_cast hdecay1
  have collision (n : ℕ) :
      let c := threshold lam (n + 1)
      ∃ p q : List (Window × Row),
        p.map Prod.fst = List.replicate (n + 1) .low ∧
        q.map Prod.fst = List.replicate (n + 1) .zero ∧
        p.length = n + 1 ∧ q.length = n + 1 ∧
        noiseBound c p ∧ noiseBound c q ∧
        actual lam p = c • canonical (some (false, true)) ∧
        actual lam q = c • canonical (some (false, true)) := by
    dsimp only
    let c := threshold lam (n + 1)
    let zA := canonical (some (false, false))
    let zB := canonical (some (false, true))
    let p : List (Window × Row) := List.replicate (n + 1) (.low, (-c) • zB)
    let q : List (Window × Row) :=
      List.replicate n (.zero, (-c) • zA) ++ [(.zero, ![c, -c, -c])]
    have hsum : 0 ≤ geometric lam (n + 1) :=
      Finset.sum_nonneg fun j _ => pow_nonneg hlam.le j
    have hden : 0 < geometric lam (n + 1) + 1 := by linarith
    have hc : 0 ≤ c := (div_pos (pow_pos hlam _) hden).le
    have critical : lam ^ (n + 1) - c * geometric lam (n + 1) = c := by
      have h : c * (geometric lam (n + 1) + 1) = lam ^ (n + 1) := by
        exact div_mul_cancel₀ _ hden.ne'
      nlinarith
    have action (a : Window) (x : Row) : x ᵥ* matrix a = x (readIndex a) • target a := by
      simp [matrix, Matrix.vecMul_vecMulVec]
    have initialRead (a : Window) : zA (readIndex a) = 1 := by
      cases a <;> rfl
    have repeated (a : Window) (ha : target a (readIndex a) = 1) (k : ℕ) :
        noisyRun (fun b x => lam • (x ᵥ* matrix b)) zA
          (List.replicate (k + 1) (a, (-c) • target a)) =
          (lam ^ (k + 1) - c * geometric lam (k + 1)) • target a := by
      let update : Row → Row := fun x => lam • (x ᵥ* matrix a) + (-c) • target a
      let f : ℕ → Row := fun j => arithGeom lam (-c) 1 j • target a
      have semiconj : Function.Semiconj f Nat.succ update := by
        intro j
        ext r
        simp [f, update, arithGeom_succ, action, Pi.smul_apply, smul_eq_mul, ha]
        ring
      have firstStep : update zA = f 1 := by
        ext r
        simp [update, f, action, initialRead, arithGeom, Pi.smul_apply, smul_eq_mul]
        ring
      rw [show List.replicate (k + 1) (a, (-c) • target a) =
        (List.replicate (k + 1) ()).map (fun _ => (a, (-c) • target a)) by simp]
      unfold noisyRun
      rw [List.foldl_map]
      change (List.replicate (k + 1) ()).foldl (fun x _ => update x) zA = _
      rw [List.foldl_const, List.length_replicate, Function.iterate_succ_apply, firstStep]
      rw [← (semiconj.iterate_right k) 1, Nat.succ_iterate]
      simp [f, arithGeom_eq_add_sum, geometric, Nat.add_comm, sub_eq_add_neg]
    have lowFormula : actual lam p = c • zB := by
      change noisyRun (fun b x => lam • (x ᵥ* matrix b)) zA
        (List.replicate (n + 1) (.low, (-c) • target .low)) = _
      rw [repeated .low (by rfl) n, critical]
      rfl
    have zeroPrefix : actual lam (List.replicate n (.zero, (-c) • zA)) =
        (lam ^ n - c * geometric lam n) • zA := by
      cases n with
      | zero => simp [actual, noisyRun, geometric, zA]
      | succ k => exact repeated .zero (by rfl) k
    have zeroFormula : actual lam q = c • zB := by
      change noisyRun (fun b x => lam • (x ᵥ* matrix b)) zA
        (List.replicate n (.zero, (-c) • zA) ++ [(.zero, ![c, -c, -c])]) = _
      simp only [noisyRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change lam • (actual lam (List.replicate n (.zero, (-c) • zA)) ᵥ* matrix .zero) +
        ![c, -c, -c] = _
      rw [zeroPrefix, action]
      have hs : geometric lam (n + 1) = lam * geometric lam n + 1 := geom_sum_succ
      rw [hs, pow_succ] at critical
      ext r
      fin_cases r <;> simp [target, readIndex, first, last, nonzero, zA, zB,
        canonical, Pi.smul_apply, smul_eq_mul] <;> nlinarith
    have lowNoise : ‖(-c) • zB‖ ≤ c := by
      apply (pi_norm_le_iff_of_nonneg hc).mpr
      intro r
      fin_cases r <;> simp [zB, canonical, Real.norm_eq_abs, abs_of_nonneg hc]
    have zeroNoise : ‖(-c) • zA‖ ≤ c := by
      apply (pi_norm_le_iff_of_nonneg hc).mpr
      intro r
      fin_cases r <;> simp [zA, canonical, Real.norm_eq_abs, abs_of_nonneg hc, hc]
    have lastNoise : ‖(![c, -c, -c] : Row)‖ ≤ c := by
      apply (pi_norm_le_iff_of_nonneg hc).mpr
      intro r
      fin_cases r <;> simp [Real.norm_eq_abs, abs_of_nonneg hc]
    refine ⟨p, q, by simp [p], by simp [q, List.replicate_succ'],
      by simp [p], by simp [q], ?_, ?_, lowFormula, zeroFormula⟩
    · intro e he
      have heq : e = (.low, (-c) • zB) := (List.mem_replicate.mp he).2
      simpa only [heq] using lowNoise
    · intro e he
      rcases List.mem_append.mp he with he | he
      · have heq : e = (.zero, (-c) • zA) := (List.mem_replicate.mp he).2
        simpa only [heq] using zeroNoise
      · have heq : e = (.zero, ![c, -c, -c]) := List.mem_singleton.mp he
        simpa only [heq] using lastNoise
  -- The matrix actions reproduce the symbolic machine on every word.
  have action (a : Window) (x : Row) : x ᵥ* matrix a = x (readIndex a) • target a := by
    simp [matrix, Matrix.vecMul_vecMulVec]
  have singleState (q : State) (a : Window) :
      canonical q ᵥ* matrix a = canonical (step q a) := by
    rw [action]
    cases q with
    | none =>
        ext r
        cases a <;> fin_cases r <;>
          simp [canonical, target, readIndex, first, last, nonzero, step]
    | some q =>
        rcases q with ⟨s, E⟩
        cases s <;> cases E <;> cases a <;> ext r <;> fin_cases r <;>
          simp [canonical, target, readIndex, first, last, nonzero, step]
  have fidelity : ∀ (w : List Window) (q : State),
      noisyRun (fun a y => y ᵥ* matrix a) (canonical q)
        (w.map (fun a => (a, (0 : Row)))) = canonical (run q w) := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a w ih =>
        intro q
        simp only [List.map_cons, noisyRun, List.foldl_cons, run]
        rw [singleState, add_zero]
        exact ih (step q a)
  have rowInjective : Function.Injective canonical := by
    intro q q' h
    cases q with
    | none =>
        cases q' with
        | none => rfl
        | some v =>
            rcases v with ⟨s, E⟩
            have h2 := congrFun h 2
            change (0 : ℝ) = 1 at h2
            norm_num at h2
    | some v =>
        cases q' with
        | none =>
            rcases v with ⟨s, E⟩
            have h2 := congrFun h 2
            change (1 : ℝ) = 0 at h2
            norm_num at h2
        | some v' =>
            rcases v with ⟨s, E⟩
            rcases v' with ⟨s', E'⟩
            have h0 := congrFun h 0
            have h1 := congrFun h 1
            cases s <;> cases E <;> cases s' <;> cases E' <;>
              simp [canonical] at h0 h1 ⊢
  have repeatFixed (a : Window) (q : State)
      (hfixed : canonical q ᵥ* matrix a = canonical q) (n : ℕ) :
      noisyRun (fun b y => y ᵥ* matrix b) (canonical q)
        (List.replicate n (a, (0 : Row))) = canonical q := by
    unfold noisyRun
    rw [show List.replicate n (a, (0 : Row)) =
      (List.replicate n ()).map (fun _ => (a, (0 : Row))) by simp]
    rw [List.foldl_map]
    simp only [add_zero, List.foldl_const, List.length_replicate]
    exact Function.iterate_fixed hfixed n
  have zeroRun (n : ℕ) : run (some (false, false)) (List.replicate n .zero) =
      some (false, false) := by
    apply rowInjective
    rw [← fidelity, List.map_replicate]
    exact repeatFixed .zero (some (false, false)) (by
      simpa [step, first, last, nonzero] using (singleState (some (false, false)) .zero)) n
  have lowRun (n : ℕ) : run (some (false, false)) (List.replicate (n + 1) .low) =
      some (false, true) := by
    apply rowInjective
    rw [← fidelity, List.map_replicate, List.replicate_succ]
    simp only [noisyRun, List.foldl_cons]
    rw [singleState, add_zero]
    exact repeatFixed .low (some (false, true)) (singleState (some (false, true)) .low) n
  have asClock {Y : Type} (out : State → Y) (ν : ℝ) (M : ℕ) (fixed : Bool) :
      Recovery out lam ν M fixed → ClockRecovery out lam ν M fixed := by
    rintro ⟨d, hd⟩
    exact ⟨fun _ => d, hd⟩
  have clockNecessary {Y : Type} (out : State → Y)
      (distinct : out (some (false, true)) ≠ out (some (false, false)))
      (ν : ℝ) (M : ℕ) (hM : 0 < M) (fixed : Bool) :
      ClockRecovery out lam ν M fixed → ν < threshold lam M := by
    rintro ⟨d, hd⟩
    by_contra hsmall
    have large : threshold lam M ≤ ν := le_of_not_gt hsmall
    have hdepth : M - 1 + 1 = M := by omega
    obtain ⟨p, q, hpw, hqw, hpl, hql, hpn, hqn, hpa, hqa⟩ := collision (M - 1)
    rw [hdepth] at hpw hqw hpl hql hpn hqn hpa hqa
    have hpRun : run (some (false, false)) (p.map Prod.fst) = some (false, true) := by
      rw [hpw]
      simpa [hdepth] using lowRun (M - 1)
    have hqRun : run (some (false, false)) (q.map Prod.fst) = some (false, false) := by
      rw [hqw]
      exact zeroRun M
    have hpLegal : legal false (flatten (p.map Prod.fst)) := by
      by_contra hl
      have bad := (execution false false (p.map Prod.fst)).2.mpr hl
      rw [hpRun] at bad
      contradiction
    have hqLegal : legal false (flatten (q.map Prod.fst)) := by
      by_contra hl
      have bad := (execution false false (q.map Prod.fst)).2.mpr hl
      rw [hqRun] at bad
      contradiction
    have hpDepth : depthAllowed fixed M p.length := by
      rw [hpl]
      cases fixed <;> simp [depthAllowed]
    have hqDepth : depthAllowed fixed M q.length := by
      rw [hql]
      cases fixed <;> simp [depthAllowed]
    have hpCorrect := hd p hpDepth hpLegal (fun e he => (hpn e he).trans large)
    have hqCorrect := hd q hqDepth hqLegal (fun e he => (hqn e he).trans large)
    rw [hpl, hpa, hpRun] at hpCorrect
    rw [hql, hqa, hqRun] at hqCorrect
    exact distinct (hpCorrect.symm.trans hqCorrect)
  have stateDistinct : canonical (some (false, true)) ≠ canonical (some (false, false)) := by
    intro h
    have h0 := congrFun h 0
    norm_num [canonical] at h0
  have labelDistinct : endable (some (false, true)) ≠ endable (some (false, false)) := by
    decide
  have zeroRecovery (ν : ℝ) (fixed : Bool) :
      Recovery canonical lam ν 0 fixed ∧ ClockRecovery canonical lam ν 0 fixed ∧
      Recovery endable lam ν 0 fixed ∧ ClockRecovery endable lam ν 0 fixed := by
    have empty (p : List (Window × Row)) (hp : depthAllowed fixed 0 p.length) : p = [] := by
      apply List.length_eq_zero_iff.mp
      cases fixed with
      | false => exact Nat.eq_zero_of_le_zero hp
      | true => exact hp
    have state : Recovery canonical lam ν 0 fixed := by
      refine ⟨fun _ => canonical (some (false, false)), ?_⟩
      intro p hp _ _
      rw [empty p hp]
      rfl
    have label : Recovery endable lam ν 0 fixed := by
      refine ⟨fun _ => false, ?_⟩
      intro p hp _ _
      rw [empty p hp]
      rfl
    exact ⟨state, asClock canonical ν 0 fixed state, label, asClock endable ν 0 fixed label⟩
  have contracts (ν : ℝ) (hν : 0 ≤ ν) (M : ℕ) (fixed : Bool) :
      (Recovery canonical lam ν M fixed ↔ M = 0 ∨ ν < threshold lam M) ∧
      (ClockRecovery canonical lam ν M fixed ↔ M = 0 ∨ ν < threshold lam M) ∧
      (Recovery endable lam ν M fixed ↔ M = 0 ∨ ν < threshold lam M) ∧
      (ClockRecovery endable lam ν M fixed ↔ M = 0 ∨ ν < threshold lam M) := by
    have backward : M = 0 ∨ ν < threshold lam M →
        Recovery canonical lam ν M fixed ∧ ClockRecovery canonical lam ν M fixed ∧
        Recovery endable lam ν M fixed ∧ ClockRecovery endable lam ν M fixed := by
      rintro (rfl | hs)
      · exact zeroRecovery ν fixed
      · exact sufficient lam ν M hlam hlam1 hν hs fixed
    refine ⟨⟨?_, fun h => (backward h).1⟩,
      ⟨?_, fun h => (backward h).2.1⟩,
      ⟨?_, fun h => (backward h).2.2.1⟩,
      ⟨?_, fun h => (backward h).2.2.2⟩⟩
    · intro h
      by_cases hM : M = 0
      · exact Or.inl hM
      · exact Or.inr (clockNecessary canonical stateDistinct ν M (Nat.pos_of_ne_zero hM)
          fixed (asClock canonical ν M fixed h))
    · intro h
      by_cases hM : M = 0
      · exact Or.inl hM
      · exact Or.inr (clockNecessary canonical stateDistinct ν M (Nat.pos_of_ne_zero hM) fixed h)
    · intro h
      by_cases hM : M = 0
      · exact Or.inl hM
      · exact Or.inr (clockNecessary endable labelDistinct ν M (Nat.pos_of_ne_zero hM)
          fixed (asClock endable ν M fixed h))
    · intro h
      by_cases hM : M = 0
      · exact Or.inl hM
      · exact Or.inr (clockNecessary endable labelDistinct ν M (Nat.pos_of_ne_zero hM) fixed h)
  refine ⟨contracts, fun ν _ fixed => zeroRecovery ν fixed, ?_, ?_, ?_⟩
  · intro ν hν fixed
    have h := contracts ν hν 1 fixed
    norm_num [threshold, geometric, lam] at h
    exact h
  · intro M hM
    have lower : 1 + lam ≤ geometric lam M := by
      calc
        1 + lam = geometric lam 2 := by simp [geometric, Finset.sum_range_succ]
        _ ≤ geometric lam M := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
          (fun j _ _ => pow_nonneg hlam.le j)
    unfold threshold
    exact div_lt_div_of_pos_left (pow_pos hlam M) (by linarith) (by linarith)
  · apply squeeze_zero
      (fun n => div_nonneg (pow_nonneg hlam.le n)
        (by have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range n) => pow_nonneg hlam.le j)
            change 0 ≤ geometric lam n + 1
            dsimp [geometric]
            linarith))
      (fun n => div_le_self (pow_nonneg hlam.le n)
        (by have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range n) => pow_nonneg hlam.le j)
            change 1 ≤ geometric lam n + 1
            dsimp [geometric]
            linarith))
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hlam.le hlam1

end D5.S3.Arith.FibonacciAtomic.LegalSourceNoiseThreshold
