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
import Mathlib.Analysis.SpecificLimits.Basic
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
      have guard : (s && first a) = false := by
        cases s <;> cases a <;> simp [flatten, bits, first, legal] at hlegal ⊢
      have tailLegal : legal (last a) (flatten (p.map Prod.fst)) := by
        cases s <;> cases a <;> simp [flatten, bits, last, legal] at hlegal ⊢ <;> tauto
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

#print axioms coordinate_invariant
#print axioms sufficient

end D5.S3.Arith.FibonacciAtomic.LegalSourceNoiseThreshold
