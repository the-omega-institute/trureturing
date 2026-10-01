/- GID: D5/S3/Arith/FibonacciAtomic/ScalarPrefixAcquisition
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ScalarPrefixAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered scalar digit tests preserve every actual prefix and attain the uniform budget. -/

import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import D5.S3.Observer.Budget.ResidueLeafOptimality
import Mathlib.Tactic

set_option autoImplicit false
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

namespace D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition

inductive PrefixProgram (P : ℕ) where
  | done : ZMod P → PrefixProgram P
  | query : ℕ → ℕ → ZMod P → (ℕ → PrefixProgram P) → PrefixProgram P

def forgetPrefix {P : ℕ} : PrefixProgram P → PassiveProtocol (ZMod P) (fun _ => ℕ)
  | .done _ => .stop
  | .query _ _ c next => .query c (fun depth => forgetPrefix (next depth))

def evaluatePrefix (p e : ℕ) : PrefixProgram (p ^ e) → ZMod (p ^ e) → ZMod (p ^ e)
  | .done r, _ => r
  | .query _ _ c next, y => evaluatePrefix p e (next (residueReadout p e c y)) y

def prefixCenter {P : ℕ} : PrefixProgram P → ZMod P
  | .done r => r
  | .query _ _ c _ => c

def prefixDescend {P : ℕ} : PrefixProgram P → ℕ → PrefixProgram P
  | .done r, _ => .done r
  | .query _ _ _ next, depth => next depth

def legalPrefixRun (p e : ℕ) : PrefixProgram (p ^ e) → ZMod (p ^ e) → Prop
  | .done r, y => residueReadout p e r y = e
  | .query s r c next, y => y.val % p ^ s = r ∧
      s ≤ residueReadout p e c y ∧
      legalPrefixRun p e (next (residueReadout p e c y)) y

def padPrefix {P : ℕ} : ℕ → PrefixProgram P → PassiveProtocol (ZMod P) (fun _ => ℕ)
  | 0, _ => .stop
  | rounds + 1, T => .query (prefixCenter T)
      (fun depth => padPrefix rounds (prefixDescend T depth))

def digitTrials (p e s r : ℕ) (next : ℕ → PrefixProgram (p ^ e)) :
    ℕ → ℕ → PrefixProgram (p ^ e)
  | 0, a => next (r + a * p ^ s)
  | attempts + 1, a => .query s r ((r + a * p ^ s : ℕ) : ZMod (p ^ e))
      (fun depth => if s < depth then next (r + a * p ^ s)
        else digitTrials p e s r next attempts (a + 1))

def prefixProgram (p e : ℕ) : ℕ → ℕ → ℕ → PrefixProgram (p ^ e)
  | 0, _, r => .done r
  | levels + 1, s, r => digitTrials p e s r
      (fun updated => prefixProgram p e levels (s + 1) updated) (p - 1) 0

set_option maxHeartbeats 1000000 in
theorem scalar_prefix_acquisition (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ∀ levels s r : ℕ, s + levels = e →
      ∀ y : ZMod (p ^ e), y.val % p ^ s = r →
        evaluatePrefix p e (prefixProgram p e levels s r) y = y ∧
          (runPassiveProtocol (residueReadout p e)
            (forgetPrefix (prefixProgram p e levels s r)) y).length ≤
              levels * (p - 1) ∧
          legalPrefixRun p e (prefixProgram p e levels s r) y := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have geometry := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result p e he).1
  have same (c y : ZMod (p ^ e)) : residueReadout p e c y =
      D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p e c y := by
    unfold residueReadout D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth
    congr 1
    ext j
    simp only [Finset.mem_filter, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff']
  have threshold (s : ℕ) (hs : s ≤ e) (c y : ZMod (p ^ e)) :
      s ≤ residueReadout p e c y ↔ y.val % p ^ s = c.val % p ^ s := by
    rw [same, (geometry c y).2 s hs]
    simp only [ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff']
  have self_depth (y : ZMod (p ^ e)) : residueReadout p e y y = e := by
    apply le_antisymm
    · rw [same]
      exact (geometry y y).1
    · exact (threshold e le_rfl y y).mpr rfl
  have digit_match (s r a : ℕ) (hs : s < e) (ha : a < p)
      (y : ZMod (p ^ e)) (hprefix : y.val % p ^ s = r) :
      s < residueReadout p e ((r + a * p ^ s : ℕ) : ZMod (p ^ e)) y ↔
        y.val / p ^ s % p = a := by
    have hr : r < p ^ s := hprefix ▸ Nat.mod_lt _ (pow_pos hp.pos _)
    have hnew : r + a * p ^ s < p ^ (s + 1) := by
      rw [pow_succ]
      have h := Nat.mul_lt_mul_of_pos_right ha (pow_pos hp.pos s)
      nlinarith
    have hsmall : r + a * p ^ s < p ^ e :=
      hnew.trans_le (Nat.pow_le_pow_right hp.pos (by omega))
    rw [Nat.lt_iff_add_one_le, threshold (s + 1) (by omega)]
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hnew]
    rw [Nat.mod_pow_succ, hprefix]
    constructor
    · intro eq
      have cancellation : p ^ s * (y.val / p ^ s % p) = p ^ s * a := by
        nlinarith
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) cancellation
    · intro eq
      rw [eq]
      ac_rfl
  have response_lower (s r a : ℕ) (hs : s < e) (ha : a < p)
      (y : ZMod (p ^ e)) (hprefix : y.val % p ^ s = r) :
      s ≤ residueReadout p e ((r + a * p ^ s : ℕ) : ZMod (p ^ e)) y := by
    apply (threshold s (by omega) _ y).mpr
    have small : r + a * p ^ s < p ^ e := by
      have hr : r < p ^ s := hprefix ▸ Nat.mod_lt _ (pow_pos hp.pos _)
      have hm := Nat.mul_lt_mul_of_pos_right ha (pow_pos hp.pos s)
      have upper : r + a * p ^ s < p ^ (s + 1) := by rw [pow_succ]; nlinarith
      exact upper.trans_le (Nat.pow_le_pow_right hp.pos (by omega))
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt small]
    have hr : r < p ^ s := hprefix ▸ Nat.mod_lt _ (pow_pos hp.pos _)
    simpa only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr] using hprefix
  have update_prefix (s r a : ℕ) (y : ZMod (p ^ e))
      (hprefix : y.val % p ^ s = r) (digit : y.val / p ^ s % p = a) :
      y.val % p ^ (s + 1) = r + a * p ^ s := by
    rw [Nat.mod_pow_succ, hprefix, digit]
    ac_rfl
  have trials_correct (s r attempts a : ℕ)
      (hs : s < e) (ha : a + attempts = p - 1)
      (next : ℕ → PrefixProgram (p ^ e))
      (y : ZMod (p ^ e)) (hprefix : y.val % p ^ s = r)
      (not_tried : a ≤ y.val / p ^ s % p)
      (next_correct : ∀ updated, y.val % p ^ (s + 1) = updated →
        evaluatePrefix p e (next updated) y = y ∧ legalPrefixRun p e (next updated) y)
      (next_bound : ∀ updated, y.val % p ^ (s + 1) = updated →
        (runPassiveProtocol (residueReadout p e) (forgetPrefix (next updated)) y).length ≤
          (e - (s + 1)) * (p - 1)) :
      evaluatePrefix p e (digitTrials p e s r next attempts a) y = y ∧
        (runPassiveProtocol (residueReadout p e)
          (forgetPrefix (digitTrials p e s r next attempts a)) y).length ≤
            attempts + (e - (s + 1)) * (p - 1) ∧
        legalPrefixRun p e (digitTrials p e s r next attempts a) y := by
    induction attempts generalizing a with
    | zero =>
      have digit : y.val / p ^ s % p = a := by
        have bound := Nat.mod_lt (y.val / p ^ s) hp.pos
        omega
      have updated := update_prefix s r a y hprefix digit
      exact ⟨(next_correct _ updated).1,
        by simpa [digitTrials] using next_bound _ updated, (next_correct _ updated).2⟩
    | succ attempts ih =>
      have alt : a < p := by omega
      by_cases match_depth : s < residueReadout p e ((r + a * p ^ s : ℕ) : ZMod (p ^ e)) y
      · have updated := update_prefix s r a y hprefix
          ((digit_match s r a hs alt y hprefix).mp match_depth)
        refine ⟨?_, ?_, ?_⟩
        · simpa only [digitTrials, evaluatePrefix, if_pos match_depth] using (next_correct _ updated).1
        · simp only [digitTrials, forgetPrefix, runPassiveProtocol, if_pos match_depth,
            List.length_cons]
          have bound := next_bound _ updated
          omega
        · simp only [digitTrials, legalPrefixRun, if_pos match_depth]
          exact ⟨hprefix, (response_lower s r a hs alt y hprefix), (next_correct _ updated).2⟩
      · have remaining : a + 1 ≤ y.val / p ^ s % p := by
          have distinct := mt (digit_match s r a hs alt y hprefix).mpr match_depth
          omega
        obtain ⟨correct, bound, legal⟩ := ih (a + 1) (by omega) remaining
        refine ⟨?_, ?_, ?_⟩
        · simpa only [digitTrials, evaluatePrefix, if_neg match_depth] using correct
        · simp only [digitTrials, forgetPrefix, runPassiveProtocol, if_neg match_depth,
            List.length_cons]
          omega
        · simp only [digitTrials, legalPrefixRun, if_neg match_depth]
          exact ⟨hprefix, (response_lower s r a hs alt y hprefix), legal⟩
  intro levels
  induction levels with
  | zero =>
    intro s r equality y hprefix
    have hs : s = e := by omega
    have final : r = y.val := by
      simpa only [hs, Nat.mod_eq_of_lt (ZMod.val_lt y)] using hprefix.symm
    refine ⟨?_, ?_, ?_⟩
    · simp only [prefixProgram, evaluatePrefix, final, ZMod.natCast_zmod_val]
    · simp [prefixProgram, forgetPrefix, runPassiveProtocol]
    · simpa only [prefixProgram, legalPrefixRun, final, ZMod.natCast_zmod_val] using self_depth y
  | succ levels ih =>
    intro s r equality y hprefix
    have hs : s < e := by omega
    have next_correct (updated : ℕ) (hu : y.val % p ^ (s + 1) = updated) :=
      ih (s + 1) updated (by omega) y hu
    obtain ⟨correct, bound, legal⟩ := trials_correct s r (p - 1) 0 hs (by omega)
      (fun updated => prefixProgram p e levels (s + 1) updated) y hprefix
      (Nat.zero_le _) (fun updated hu => ⟨(next_correct updated hu).1, (next_correct updated hu).2.2⟩)
      (fun updated hu => by simpa [show e - (s + 1) = levels by omega] using
        (next_correct updated hu).2.1)
    refine ⟨correct, ?_, legal⟩
    simpa only [prefixProgram, show e - (s + 1) = levels by omega,
      Nat.succ_mul, Nat.add_comm] using bound

#print axioms scalar_prefix_acquisition

end D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition
