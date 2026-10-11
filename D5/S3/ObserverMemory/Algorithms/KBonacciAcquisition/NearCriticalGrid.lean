/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Common scheduled profiles factor through acquired charges in the full INITIAL grid. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalCommonTailCompression
import Mathlib.Data.BitVec

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open OwnPathCharges WindowChargeInverse GlobalPresetObstruction DonorCorrection
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
open scoped BigOperators

def gridPhase (r m : ℕ) (p q : Fin (2 ^ r)) : ZMod (2 * m - 2 + 1) :=
  ((2 * r + p.val * 2 ^ r + q.val : ℕ) : _)

/-- The immutable row/column table includes every legal INITIAL tail and
every phase outside the grid. Initial bottom has its own unrestricted label. -/
def GridTarget {Y : Type u} (r m : ℕ) (labels : Fin (2 ^ r) → Y)
    (f : Option (LiveRecord (2 * m - 2)) → Y) : Prop :=
  (∀ (v : ZMod 2) (p q : Fin (2 ^ r)) (s : ℕ), s < 2 * m - 2 →
    f (some ⟨v, -gridPhase r m p q, s⟩) = labels (if v = 0 then p else q)) ∧
  (∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
    (∀ p q, j ≠ gridPhase r m p q) → f (some ⟨v, -j, s⟩) = labels 0)

private theorem grid_val (r m : ℕ)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (p q : Fin (2 ^ r)) :
    (gridPhase r m p q).val = 2 * r + p.val * 2 ^ r + q.val := by
  have hp := p.isLt
  have hq := q.isLt
  have hn : 0 < 2 ^ r := by positivity
  have bound : 2 * r + p.val * 2 ^ r + q.val < m := by
    nlinarith [Nat.mul_le_mul_right (2 ^ r) (show p.val + 1 ≤ 2 ^ r by omega)]
  simp only [gridPhase, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

/-- A fixed stream's offline profile is transported to each source's own
acquired charge array. Stops and common rejection retire both arrays; the
unused scheduled suffix supplies no acquired endpoint. -/
private theorem scheduled_own_transport {Y : Type u} (k m : ℕ)
    (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y)
    (b : ℕ) : ∀ (z : ZMod 2) (p q : ZMod (k + 1)) (s : ℕ)
      (free : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m),
    (∀ t < b,
      wordIncrement k (p + (((archive.length + t) * m : ℕ) : ZMod (k + 1)))
          (stream (archive.length + t)) =
      wordIncrement k (q + (((archive.length + t) * m : ℕ) : ZMod (k + 1)))
          (stream (archive.length + t))) →
    ∀ t < b,
      ownCharge (presetSelector stream stop) b z
          (p + ((archive.length * m : ℕ) : ZMod (k + 1))) s free archive t =
      ownCharge (presetSelector stream stop) b z
          (q + ((archive.length * m : ℕ) : ZMod (k + 1))) s free archive t := by
  induction b with
  | zero => intro z p q s free archive codes t ht; omega
  | succ b ih =>
    intro z p q s free archive codes t ht
    cases chosen : stop free archive with
    | some y => simp only [ownCharge, presetSelector, chosen]
    | none =>
      have first := codes 0 (by omega)
      simp only [Nat.add_zero] at first
      simp only [ownCharge, presetSelector, chosen]
      split_ifs with safe
      · cases t with
        | zero => exact first
        | succ t =>
          rw [← first]
          let next := archive ++ [(stream archive.length,
            some (z + wordIncrement k
              (p + ((archive.length * m : ℕ) : ZMod (k + 1))) (stream archive.length)))]
          have length : next.length = archive.length + 1 := by simp [next]
          have shift (a : ZMod (k + 1)) :
              a + ((archive.length * m : ℕ) : ZMod (k + 1)) + (m : ℕ) =
              a + ((next.length * m : ℕ) : ZMod (k + 1)) := by
            rw [length]; push_cast; ring
          rw [shift p, shift q]
          apply ih _ p q _ free next ?_ t (by omega)
          intro i hi
          have e := codes (i + 1) (by omega)
          simpa only [length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using e
      · rfl

private theorem odd_silent (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (h : ℕ) (hh : h ≤ 2 * r - 2)
    (p q : Fin (2 ^ r)) (B : Fin m → Bool) :
    wordIncrement (2 * m - 2)
      (-gridPhase r m p q + (((2 * h + 1) * m : ℕ) : _)) B = 0 := by
  have hm5 : 5 ≤ m := by
    have positive : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  let j := gridPhase r m p q
  have val := grid_val r m hm p q
  have lower : 2 * r ≤ j.val := by dsimp [j]; rw [val]; omega
  have upper : j.val < m := by
    dsimp [j]; rw [val]
    have hp := p.isLt; have hq := q.isLt
    nlinarith [Nat.mul_le_mul_right (2 ^ r) (show p.val + 1 ≤ 2 ^ r by omega)]
  have hhm : h + m ≤ j.val + (2 * m - 2 + 1) := by omega
  have modEq : j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((j.val + (2 * m - 2 + 1) - (h + m) : ℕ) : _) := by
    rw [show (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((h + m : ℕ) : _) by simpa using calendar m hm5 h 1 0]
    rw [Nat.cast_sub hhm]
    rw [Nat.cast_add j.val (2 * m - 2 + 1), ZMod.natCast_self, add_zero,
      ZMod.natCast_zmod_val]
  have outside : m < (j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1))).val := by
    rw [modEq, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [show -j + (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1)) =
    -(j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1))) by abel,
    increment_derivative (2 * m - 2) (by omega) m (by omega)]
  have ext0 : ¬ (j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1))).val < m := by omega
  have ext1 : ¬ (j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1))).val - 1 < m := by omega
  have nz : ¬ (j - (((2 * h + 1) * m : ℕ) : ZMod (2 * m - 2 + 1))).val = 0 := by omega
  simp only [extendedBit, dif_neg ext0, if_neg nz, dif_neg ext1, add_zero]

private theorem count_even (b : ℕ) : OriginalCommonTailCompression.count 2 0 b = (b + 1) / 2 := by
  induction b with
  | zero => simp [OriginalCommonTailCompression.count]
  | succ b ih =>
    have step : OriginalCommonTailCompression.count 2 0 (b + 1) =
        OriginalCommonTailCompression.count 2 0 b + (if 2 ∣ b then 1 else 0) := by
      simp only [OriginalCommonTailCompression.count, Finset.sum_range_succ, Nat.zero_add]
    rw [step, ih]
    by_cases even : 2 ∣ b
    · rw [if_pos even]; have e := Nat.mod_eq_zero_of_dvd even; omega
    · rw [if_neg even]; have e : b % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using even
      omega

/-- A common stream that decodes both scalar fibres must carry at least
two independent r-bit grid coordinates in its informative even slots. -/
theorem original_grid_preset_lower {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f)
    (d : ℕ) (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d) :
    4 * r - 1 ≤ d := by
  classical
  by_contra small
  have hd : d ≤ 4 * r - 2 := by omega
  have hm5 : 5 ≤ m := by
    have positive : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  let profile (pq : Fin (2 ^ r) × Fin (2 ^ r)) (a : Fin (2 * r - 1)) : ZMod 2 :=
    wordIncrement (2 * m - 2)
      (-gridPhase r m pq.1 pq.2 + (((2 * a.val) * m : ℕ) : _)) (stream (2 * a.val))
  have native (v : ZMod 2) (pq : Fin (2 ^ r) × Fin (2 ^ r)) :
      ∃ c, NativeExecute (presetSelector stream stop) d
        (some ⟨v, -gridPhase r m pq.1 pq.2, 0⟩) (some v) [] =
        some (labels (if v = 0 then pq.1 else pq.2), c) := by
    obtain ⟨c, _, ex⟩ := native_fiber (2 * m - 2) m (by omega) (by omega)
      alphabet f v d (presetSelector stream stop)
      (fun history readout => by simpa only [readout] using correct history)
      (-gridPhase r m pq.1 pq.2) 0 (by omega)
      (by rw [FourLabelPaidFeedback.coprime m hm5]; exact one_dvd _)
    rw [target.1 v pq.1 pq.2 0 (by omega)] at ex
    exact ⟨c, ex⟩
  have injective : Function.Injective profile := by
    intro x y eq
    have codes : ∀ t < d,
        wordIncrement (2 * m - 2) (-gridPhase r m x.1 x.2 + ((t * m : ℕ) : _)) (stream t) =
        wordIncrement (2 * m - 2) (-gridPhase r m y.1 y.2 + ((t * m : ℕ) : _)) (stream t) := by
      intro t ht
      by_cases even : 2 ∣ t
      · have et : t = 2 * (t / 2) := by omega
        have a : t / 2 < 2 * r - 1 := by omega
        simpa only [profile, ← et] using congrFun eq ⟨t / 2, a⟩
      · have et : t = 2 * (t / 2) + 1 := by
          have ne : t % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using even
          omega
        rw [et, odd_silent r m hr hm (t / 2) (by omega) x.1 x.2,
          odd_silent r m hr hm (t / 2) (by omega) y.1 y.2]
    have same (v : ZMod 2) :
        labels (if v = 0 then x.1 else x.2) = labels (if v = 0 then y.1 else y.2) := by
      obtain ⟨cx, ex⟩ := native v x
      obtain ⟨cy, ey⟩ := native v y
      apply charge_separates (2 * m - 2) m (by omega) (presetSelector stream stop)
        d v (-gridPhase r m x.1 x.2) (-gridPhase r m y.1 y.2) 0 (by omega)
        (some v) [] _ _ cx cy ex ey
      simpa only [List.length_nil, Nat.zero_add, Nat.zero_mul, Nat.cast_zero, add_zero]
        using scheduled_own_transport (2 * m - 2) m stream stop d v
          (-gridPhase r m x.1 x.2) (-gridPhase r m y.1 y.2) 0 (some v) []
          (by simpa only [List.length_nil, Nat.zero_add] using codes)
    apply Prod.ext
    · apply distinct; simpa using same 0
    · apply distinct; simpa using same 1
  have count := Fintype.card_le_of_injective profile injective
  have exponent : (2 ^ r) * 2 ^ r = 2 ^ (2 * r) := by rw [← pow_add]; congr 1; omega
  have tooMany : 2 ^ (2 * r - 1) < (2 : ℕ) ^ (2 * r) :=
    pow_lt_pow_right₀ (by omega) (by omega)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    ZMod.card] at count
  rw [exponent] at count
  omega

/-- Arbitrary paid-feedback actions on the full original prior cannot
decode even one scalar grid coordinate before r informative even slots. -/
theorem original_grid_adaptive_lower {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f)
    (d : ℕ) (feasible : OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d) :
    2 * r - 1 ≤ d := by
  classical
  by_contra small
  have hd : d ≤ 2 * r - 2 := by omega
  have hm5 : 5 ≤ m := by
    have positive : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  obtain ⟨pi, legal, bottom, correct⟩ := feasible
  let phase (x : ULift.{u} (Fin (2 ^ r))) := -gridPhase r m x.down 0
  have sources (x : ULift.{u} (Fin (2 ^ r))) :
      ∃ history : List (AllowedBlock (2 * m - 2) m alphabet),
        OriginalRecord (2 * m - 2) (by omega)
          (history.flatMap (fun a => List.ofFn a.val)) = some ⟨0, phase x, 0⟩ := by
    obtain ⟨history, actual⟩ :=
      ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega)
        alphabet (fun _ => ())).1 (some ⟨0, phase x, 0⟩)).mp
        (by
          change 0 < 2 * m - 2 ∧ _
          exact ⟨by omega, by rw [FourLabelPaidFeedback.coprime m hm5]; exact one_dvd _⟩)
    exact ⟨history, (record_history _ m (by omega) alphabet history).trans actual⟩
  let history x := Classical.choose (sources x)
  let ws x := (history x).flatMap (fun a => List.ofFn a.val)
  have record x : OriginalRecord (2 * m - 2) (by omega) (ws x) =
      some ⟨0, phase x, 0⟩ := Classical.choose_spec (sources x)
  obtain ⟨P, separates⟩ := OriginalCommonTailCompression.compress
    (2 * m - 2) m (by omega) pi (some 0) (fun x => labels x.down) phase 2 d
    (by
      intro t ht odd x B
      have form : t = 2 * (t / 2) + 1 := by
        have ne : t % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using odd
        omega
      dsimp only [phase]
      rw [form]
      exact odd_silent r m hr hm (t / 2) (by omega) x.down 0 B)
    d 0 (by omega) Set.univ ws 0 0 (by omega) []
    (by intro x _; simpa using record x)
    (by
      intro x _
      obtain ⟨c, _, success⟩ := correct (history x)
      have readout : NarrowWindowCost.output (2 * m - 2) (by omega) (ws x) = some 0 := by
        rw [OriginalExecutionBridge.output_record]
        change endpointReading (OriginalRecord (2 * m - 2) (by omega) (ws x)) = some 0
        rw [record x]; rfl
      change NarrowWindowCost.execute (2 * m - 2) (by omega) pi d (ws x)
        (NarrowWindowCost.output (2 * m - 2) (by omega) (ws x)) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) (ws x)), c) at success
      rw [readout, record, target.1 0 x.down 0 0 (by omega)] at success
      simpa using Exists.intro c success)
  have bound := exact_identification_card_le_pow
    (id : (ULift.{u} (Fin (2 ^ r)) → Fin 2) → ULift.{u} (Fin (2 ^ r)) → Fin 2)
    (by omega) ⟨P, adaptiveProtocol_uses_identity_readout P, by
      intro x y eq
      apply ULift.ext
      exact distinct (separates x (Set.mem_univ _) y (Set.mem_univ _) eq)⟩
  simp only [Fintype.card_ulift, Fintype.card_fin, count_even] at bound
  have weak : (d + 1) / 2 ≤ r - 1 := by omega
  have strong : (2 : ℕ) ^ ((d + 1) / 2) < 2 ^ r :=
    pow_lt_pow_right₀ (by omega) (by omega)
  omega


/-- The pinned little-endian bit representation of one grid coordinate. -/
def coordinateBit {r : ℕ} (p : Fin (2 ^ r)) (a : Fin r) : ZMod 2 :=
  bitScalar ((BitVec.equivFin.symm p).getLsbD a.val)

/-- The inverse charge row at the even paid index 2h. The unused coordinate
is summed over all n possibilities, so either row family has even parity. -/
def gridRow (r : ℕ) (h : ℕ) (side : Bool) (a : Fin r) (i : ℕ) : ZMod 2 :=
  ∑ p : Fin (2 ^ r), ∑ q : Fin (2 ^ r),
    if h + i = 2 * r + p.val * 2 ^ r + q.val then
      coordinateBit (if side then q else p) a else 0

private theorem index_injective (r : ℕ) (p q p' q' : Fin (2 ^ r))
    (eq : 2 * r + p.val * 2 ^ r + q.val = 2 * r + p'.val * 2 ^ r + q'.val) :
    p = p' ∧ q = q' := by
  have e : p.val * 2 ^ r + q.val = p'.val * 2 ^ r + q'.val := by omega
  have mods := congrArg (fun n => n % 2 ^ r) e
  simp only [Nat.mul_add_mod',
    Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt q'.isLt] at mods
  have qe : q = q' := Fin.ext mods
  subst q'
  have mul : p.val * 2 ^ r = p'.val * 2 ^ r := by omega
  exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ r) mul), rfl⟩

private theorem row_at (r h : ℕ) (side : Bool) (a : Fin r)
    (p q : Fin (2 ^ r)) (i : ℕ)
    (eq : h + i = 2 * r + p.val * 2 ^ r + q.val) :
    gridRow r h side a i = coordinateBit (if side then q else p) a := by
  classical
  unfold gridRow
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp [eq]
    · intro q' _ ne
      apply if_neg
      intro e
      exact ne (index_injective r p q' p q (e.symm.trans eq)).2
    · simp
  · intro p' _ ne
    apply Finset.sum_eq_zero
    intro q' _
    apply if_neg
    intro e
    exact ne (index_injective r p' q' p q (e.symm.trans eq)).1
  · simp

private theorem row_zero (r m h : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hh : h ≤ 2 * r - 1)
    (side : Bool) (a : Fin r) : gridRow r h side a 0 = 0 ∧ gridRow r h side a m = 0 := by
  classical
  have small (p q : Fin (2 ^ r)) : 2 * r + p.val * 2 ^ r + q.val < m := by
    have hp := p.isLt; have hq := q.isLt
    nlinarith [Nat.mul_le_mul_right (2 ^ r) (show p.val + 1 ≤ 2 ^ r by omega)]
  constructor <;> unfold gridRow <;> apply Finset.sum_eq_zero <;>
    intro p _ <;> apply Finset.sum_eq_zero <;> intro q _ <;>
    apply if_neg <;> have bound := small p q <;> omega

private theorem row_even (r m h : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hh : h ≤ 2 * r - 1)
    (side : Bool) (a : Fin r) : ∑ i ∈ Finset.range (m + 1), gridRow r h side a i = 0 := by
  classical
  have pick (p q : Fin (2 ^ r)) :
      ∑ i ∈ Finset.range (m + 1),
        (if h + i = 2 * r + p.val * 2 ^ r + q.val then
          coordinateBit (if side then q else p) a else 0) =
        coordinateBit (if side then q else p) a := by
    let e := 2 * r + p.val * 2 ^ r + q.val
    have lower : h ≤ e := by dsimp [e]; omega
    have upper : e < m := by
      dsimp [e]
      have hp := p.isLt; have hq := q.isLt
      nlinarith [Nat.mul_le_mul_right (2 ^ r) (show p.val + 1 ≤ 2 ^ r by omega)]
    rw [Finset.sum_eq_single (e - h)]
    · rw [if_pos (by omega)]
    · intro i _ ne
      apply if_neg; omega
    · simp only [Finset.mem_range]
      intro bad
      omega
  unfold gridRow
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range (m + 1)), pick]
  have parity : ((2 ^ r : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow]
    have two : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [two]
    exact zero_pow (by omega : r ≠ 0)
  cases side <;> simp [nsmul_eq_mul, parity]

private theorem row_charge_grid (r m h : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hh : h ≤ 2 * r - 1)
    (side : Bool) (a : Fin r) (p q : Fin (2 ^ r)) :
    windowCharge (2 * m - 2) m (gridRow r h side a)
      (gridPhase r m p q - (((2 * h) * m : ℕ) : _)) =
      coordinateBit (if side then q else p) a := by
  have hm5 : 5 ≤ m := by
    have pos : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  have val := grid_val r m hm p q
  let e := 2 * r + p.val * 2 ^ r + q.val
  have lower : h ≤ e := by dsimp [e]; omega
  have upper : e < m := by
    have hp := p.isLt; have hq := q.isLt
    dsimp [e]
    nlinarith [Nat.mul_le_mul_right (2 ^ r) (show p.val + 1 ≤ 2 ^ r by omega)]
  have shift : gridPhase r m p q - (((2 * h) * m : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((e - h : ℕ) : _) := by
    have cal := calendar m hm5 h 0 0
    simp only [Nat.add_zero, Nat.zero_mul, zero_add] at cal
    rw [cal, Nat.cast_sub lower]
    rfl
  have shifted : (gridPhase r m p q - (((2 * h) * m : ℕ) : ZMod (2 * m - 2 + 1))).val = e - h := by
    rw [shift, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [windowCharge, shifted, if_pos (by omega)]
  exact row_at r h side a p q (e - h) (by omega)

private theorem row_charge_outside (r m h : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (side : Bool) (a : Fin r)
    (j : ZMod (2 * m - 2 + 1)) (outside : ∀ p q, j ≠ gridPhase r m p q) :
    windowCharge (2 * m - 2) m (gridRow r h side a)
      (j - (((2 * h) * m : ℕ) : _)) = 0 := by
  classical
  have hm5 : 5 ≤ m := by
    have pos : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  unfold windowCharge
  split_ifs
  · unfold gridRow
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro q _
    apply if_neg
    intro eq
    apply outside p q
    have cast := congrArg (fun n : ℕ => (n : ZMod (2 * m - 2 + 1))) eq
    simp only [Nat.cast_add, ZMod.natCast_zmod_val] at cast
    have cal := calendar m hm5 h 0 0
    simp only [Nat.add_zero, Nat.zero_mul, zero_add] at cal
    rw [cal] at cast
    have lhs : (h : ZMod (2 * m - 2 + 1)) + (j - (h : ℕ)) = j := by abel
    rw [lhs] at cast
    simpa only [gridPhase, Nat.cast_add] using cast
  · rfl


/-- Coding blocks alternate with charged all-zero waits. -/
def gridRows (r R : ℕ) (schedule : Fin R → Bool × Fin r) : List (ℕ → ZMod 2) :=
  List.ofFn (fun t : Fin (2 * R - 1) =>
    if even : 2 ∣ t.val then
      if fit : t.val / 2 < R then
        gridRow r (t.val / 2) (schedule ⟨t.val / 2, fit⟩).1 (schedule ⟨t.val / 2, fit⟩).2
      else fun _ => 0
    else fun _ => 0)

def gridWords (r R m : ℕ) (schedule : Fin R → Bool × Fin r) : List (Fin m → Bool) :=
  (gridRows r R schedule).map (prefixWord m)

private theorem rows_safe (r R m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hR : R ≤ 2 * r)
    (schedule : Fin R → Bool × Fin r) :
    safeRows m (gridRows r R schedule) ∧
    ∀ row ∈ gridRows r R schedule, row 0 = 0 := by
  classical
  have properties : ∀ row ∈ gridRows r R schedule,
      (∑ i ∈ Finset.range (m + 1), row i = 0) ∧ row 0 = 0 ∧ row m = 0 := by
    intro row member
    obtain ⟨t, eq⟩ := List.mem_ofFn.mp member
    subst row
    split_ifs with even fit
    · exact ⟨row_even r m (t.val / 2) hr hm (by omega) _ _,
        row_zero r m (t.val / 2) hr hm (by omega) _ _⟩
    · simp
    · simp
  refine ⟨?_, fun row mem => (properties row mem).2.1⟩
  have build : ∀ rows : List (ℕ → ZMod 2),
      (∀ row ∈ rows, (∑ i ∈ Finset.range (m + 1), row i = 0) ∧ row m = 0) →
      safeRows m rows := by
    intro rows
    induction rows with
    | nil => intro _; trivial
    | cons row rest ih =>
      intro props
      exact ⟨(props row (by simp)).1, fun _ _ => Or.inl (props row (by simp)).2,
        ih (fun q mem => props q (by simp [mem]))⟩
  exact build _ (fun row mem => ⟨(properties row mem).1, (properties row mem).2.2⟩)

private theorem grid_archive (r R m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hR : R ≤ 2 * r)
    (alphabet : Bool) (schedule : Fin R → Bool × Fin r)
    (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    (PhysicalWindowDecoder.scriptArchive (gridWords r R m schedule) (some ⟨v, -j, s⟩)).map Prod.snd =
      chargeArchive (2 * m - 2) m (gridRows r R schedule) v j ∧
    none ∉ (PhysicalWindowDecoder.scriptArchive (gridWords r R m schedule) (some ⟨v, -j, s⟩)).map Prod.snd := by
  have hm5 : 5 ≤ m := by
    have pos : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  have safe := rows_safe r R m hr hm hR schedule
  have actual := actual_shared_charge_suffix (2 * m - 2) (by omega) m (by omega)
    (by omega) alphabet (gridRows r R schedule) safe.1 v j s hs
    (fun row mem => Or.inr (safe.2 row (List.mem_of_mem_head? mem)))
    (by rw [FourLabelPaidFeedback.coprime m hm5]; exact one_dvd _)
  have words : (chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet
      (gridRows r R schedule)).map Subtype.val = gridWords r R m schedule := by
    simp only [chargeBlocks, gridWords, AllowedBlock, List.map_map, Function.comp_def]
  rw [← words, PhysicalWindowDecoder.script_readings]
  exact ⟨actual.2.1, actual.2.2.2.1⟩

/-- Only differences of the saved free value and this source's acquired
endpoints enter the decoder. Its little-endian reconstruction is the pinned
BitVec representation, followed by BitVec.equivFin. -/
def gridDecode {Y : Type u} {r R m : ℕ} (labels : Fin (2 ^ r) → Y)
    (position : Fin r → Fin R) (v : ZMod 2) (archive : NarrowWindowCost.Archive m) : Y :=
  labels (BitVec.equivFin
    ((BitVec.ofBoolListLE (List.ofFn (fun a : Fin r =>
      decide ((((PhysicalWindowDecoder.endpointDifferences (some v) (archive.map Prod.snd))[2 * (position a).val]?).join.getD 0) ≠ 0)))).cast List.length_ofFn))

private theorem decode_of_bits {Y : Type u} {r R m : ℕ}
    (labels : Fin (2 ^ r) → Y) (position : Fin r → Fin R) (v : ZMod 2)
    (archive : NarrowWindowCost.Archive m) (p : Fin (2 ^ r))
    (bits : ∀ a : Fin r,
      (PhysicalWindowDecoder.endpointDifferences (some v) (archive.map Prod.snd))[2 * (position a).val]? = some (some (coordinateBit p a))) :
    gridDecode labels position v archive = labels p := by
  unfold gridDecode
  congr 1
  rw [← BitVec.equivFin.apply_symm_apply p]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi,
    Option.getD_some, bits ⟨i, hi⟩, Option.join_some, Option.getD_some, coordinateBit]
  cases (BitVec.equivFin.symm p).getLsbD i <;> norm_num [bitScalar]

private theorem script_decodes {Y : Type u} (r R m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (hR : R ≤ 2 * r)
    (alphabet : Bool) (schedule : Fin R → Bool × Fin r) (position : Fin r → Fin R)
    (labels : Fin (2 ^ r) → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : GridTarget r m labels f) (v : ZMod 2)
    (scheduled : ∀ a, schedule (position a) = (decide (v ≠ 0), a))
    (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    gridDecode labels position v
      (PhysicalWindowDecoder.scriptArchive (gridWords r R m schedule) (some ⟨v, -j, s⟩)) =
      f (some ⟨v, -j, s⟩) := by
  classical
  have readings := (grid_archive r R m hr hm hR alphabet schedule v j s hs).1
  have index (a : Fin r) :
      (PhysicalWindowDecoder.endpointDifferences (some v)
        ((PhysicalWindowDecoder.scriptArchive (gridWords r R m schedule) (some ⟨v, -j, s⟩)).map Prod.snd))[2 * (position a).val]? =
      some (some (windowCharge (2 * m - 2) m
        (gridRow r (position a).val (decide (v ≠ 0)) a)
        (j - (((2 * (position a).val) * m : ℕ) : _)))) := by
    have fit : 2 * (position a).val < 2 * R - 1 := by have := (position a).isLt; omega
    rw [readings, PhysicalWindowDecoder.charge_differences, row_readings_index]
    simp only [gridRows, List.getElem?_ofFn, dif_pos fit,
      Nat.dvd_mul_right, dif_pos, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      dif_pos (position a).isLt, scheduled, Option.map_some]
  by_cases inside : ∃ p q, j = gridPhase r m p q
  · obtain ⟨p, q, rfl⟩ := inside
    rw [target.1 v p q s hs]
    apply decode_of_bits
    intro a
    rw [index, row_charge_grid r m (position a).val hr hm (by have := (position a).isLt; omega)]
    congr 2
    by_cases zero : v = 0 <;> simp [zero]
  · have outside : ∀ p q, j ≠ gridPhase r m p q := by simpa using inside
    rw [target.2 v j s hs outside]
    apply decode_of_bits
    intro a
    rw [index, row_charge_outside r m (position a).val hr hm _ _ j outside]
    simp [coordinateBit, bitScalar]



def adaptiveSchedule (r : ℕ) (v : ZMod 2) (a : Fin r) : Bool × Fin r :=
  (decide (v ≠ 0), a)

def commonSchedule (r : ℕ) (a : Fin (2 * r)) : Bool × Fin r :=
  if fit : a.val < r then (false, ⟨a.val, fit⟩)
  else (true, ⟨a.val - r, by have := a.isLt; omega⟩)

def commonPosition (r : ℕ) (v : ZMod 2) (a : Fin r) : Fin (2 * r) :=
  ⟨(if v = 0 then 0 else r) + a.val, by split_ifs <;> have := a.isLt <;> omega⟩

def adaptiveWords (r m : ℕ) (v : ZMod 2) := gridWords r r m (adaptiveSchedule r v)
def commonWords (r m : ℕ) := gridWords r (2 * r) m (commonSchedule r)

def scriptStreams {m : ℕ} (words : ZMod 2 → List (Fin m → Bool)) :
    ZMod 2 → ℕ → Fin m → Bool := fun v t => (words v)[t]?.getD (fun _ => false)

def scriptStop {Y : Type u} {m : ℕ} (words : ZMod 2 → List (Fin m → Bool))
    (decode : ZMod 2 → NarrowWindowCost.Archive m → Y) (bottom : Y) :
    Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y
  | none, _ => some bottom
  | some v, ar => match (words v)[ar.length]? with
    | some _ => none
    | none => some (decode v ar)

def adaptiveStop {Y : Type u} {r m : ℕ} (labels : Fin (2 ^ r) → Y) (bottom : Y) :=
  scriptStop (adaptiveWords r m) (gridDecode labels (id : Fin r → Fin r)) bottom

def commonStop {Y : Type u} {r m : ℕ} (labels : Fin (2 ^ r) → Y) (bottom : Y) :=
  scriptStop (fun _ => commonWords r m)
    (fun v => gridDecode labels (commonPosition r v) v) bottom

def adaptiveSelector {Y : Type u} {r m : ℕ} (labels : Fin (2 ^ r) → Y) (bottom : Y) :=
  FourLabelPaidFeedback.selectedSelector (scriptStreams (adaptiveWords r m)) (adaptiveStop labels bottom)

def commonStream (r m : ℕ) := scriptStreams (fun _ => commonWords r m) 0

def fee (D : ℕ) {k : ℕ} (q : Option (LiveRecord k)) := if q.isSome then D else 0

private theorem scripts_match (r : ℕ) (v : ZMod 2) (a : Fin r) :
    commonSchedule r (commonPosition r v a) = (decide (v ≠ 0), a) := by
  by_cases zero : v = 0
  · simp [commonSchedule, commonPosition, zero, a.isLt]
  · simp [commonSchedule, commonPosition, zero, show ¬ r + a.val < r by omega]

private theorem scripts_decode {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : GridTarget r m labels f) :
    (∀ (v : ZMod 2) (phase : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      gridDecode labels (id : Fin r → Fin r) v
        (PhysicalWindowDecoder.scriptArchive (adaptiveWords r m v) (some ⟨v, phase, s⟩)) =
        f (some ⟨v, phase, s⟩)) ∧
    (∀ (v : ZMod 2) (phase : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      gridDecode labels (commonPosition r v) v
        (PhysicalWindowDecoder.scriptArchive (commonWords r m) (some ⟨v, phase, s⟩)) =
        f (some ⟨v, phase, s⟩)) := by
  constructor
  · intro v phase s hs
    simpa only [neg_neg, adaptiveWords] using script_decodes r r m hr hm (by omega) alphabet
      (adaptiveSchedule r v) id labels f target v (fun _ => rfl) (-phase) s hs
  · intro v phase s hs
    simpa only [neg_neg, commonWords] using script_decodes r (2 * r) m hr hm le_rfl alphabet
      (commonSchedule r) (commonPosition r v) labels f target v (scripts_match r v) (-phase) s hs

private theorem script_history_trace {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (f : Option (LiveRecord k) → Y) (D : ℕ)
    (words : ZMod 2 → List (Fin m → Bool))
    (decode : ZMod 2 → NarrowWindowCost.Archive m → Y)
    (length : ∀ v, (words v).length = D)
    (decoded : ∀ v phase s, s < k →
      decode v (PhysicalWindowDecoder.scriptArchive (words v) (some ⟨v, phase, s⟩)) =
      f (some ⟨v, phase, s⟩))
    (safe : ∀ (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ), s < k →
      none ∉ (PhysicalWindowDecoder.scriptArchive (words v) (some ⟨v, phase, s⟩)).map Prod.snd)
    (alphabet : Bool) (history : List (AllowedBlock k m alphabet)) :
    let w := history.flatMap (fun a => List.ofFn a.val)
    let q := OriginalRecord k (by omega) w
    let free := NarrowWindowCost.output k (by omega) w
    ∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace
      (FourLabelPaidFeedback.selectedSelector (scriptStreams words) (scriptStop words decode (f none)))
      free q [] issued (f q) ∧
      issued.length = fee D q ∧
      (OriginalAcquiredTrace.archiveWords issued).length = m * fee D q ∧
      none ∉ issued.map Prod.snd := by
  intro w q free
  have output : free = endpointReading q := OriginalExecutionBridge.output_record k (by omega) w
  cases initial : q with
  | none =>
    refine ⟨[], ?_, rfl, by simp [OriginalAcquiredTrace.archiveWords, fee, initial], by simp⟩
    rw [output, initial]
    rfl
  | some source =>
    have freeEq : free = some source.value := by rw [output, initial]; rfl
    have hs : source.tail < k := by
      change OriginalRecord k (by omega) w = some source at initial
      unfold OriginalRecord at initial
      cases scan : (NarrowWindowCost.scanner k (by omega)).eval w with
      | none => simp [scan] at initial
      | some tail =>
        simp only [scan, Option.map_some, Option.some.injEq] at initial
        have eq := congrArg LiveRecord.tail initial
        simpa only [← eq] using tail.isLt
    have same (ar : NarrowWindowCost.Archive m) :
        FourLabelPaidFeedback.selectedSelector (scriptStreams words) (scriptStop words decode (f none))
          (some source.value) ar =
        PhysicalWindowDecoder.finalSelector 0 (words source.value) (decode source.value)
          (some source.value) ar := by
      simp only [FourLabelPaidFeedback.selectedSelector, Option.getD_some,
        presetSelector, scriptStop]
      cases selected : (words source.value)[ar.length]? <;>
        simp [selected, scriptStreams, PhysicalWindowDecoder.finalSelector]
    have script := PhysicalWindowDecoder.original_final_script k m hk (words source.value)
      (decode source.value) w (some source.value) []
    dsimp only at script
    change OriginalRecord k (by omega) w = some source at initial
    rw [initial] at script
    have label := decoded source.value source.phase source.tail hs
    have record : (⟨source.value, source.phase, source.tail⟩ : LiveRecord k) = source := by cases source; rfl
    rw [record] at label
    have trace := (FullPositiveWindowPrice.trace_congr _ _ (some source.value) same _ _ [] _).mpr script.1
    rw [label] at trace
    refine ⟨PhysicalWindowDecoder.scriptArchive (words source.value) (some source), ?_, ?_, ?_, ?_⟩
    · rw [freeEq]; exact trace
    · simpa only [fee, Option.isSome_some, Bool.true_eq, if_true]
        using script.2.2.1.trans (length source.value)
    · rw [OriginalAcquiredTrace.archive_length, script.2.2.1, length source.value]
      simp [fee, Nat.mul_comm]
    · simpa only [record] using safe source.value source.phase source.tail hs



private theorem history_traces {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : GridTarget r m labels f)
    (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
    let w := history.flatMap (fun a => List.ofFn a.val)
    let q := OriginalRecord (2 * m - 2) (by omega) w
    let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
    (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace (adaptiveSelector (r := r) (m := m) labels (f none))
      free q [] issued (f q) ∧ issued.length = fee (2 * r - 1) q ∧
      (OriginalAcquiredTrace.archiveWords issued).length = m * fee (2 * r - 1) q ∧
      none ∉ issued.map Prod.snd) ∧
    (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace
      (presetSelector (commonStream r m) (commonStop (r := r) (m := m) labels (f none)))
      free q [] issued (f q) ∧ issued.length = fee (4 * r - 1) q ∧
      (OriginalAcquiredTrace.archiveWords issued).length = m * fee (4 * r - 1) q ∧
      none ∉ issued.map Prod.snd) := by
  have decoded := scripts_decode r m hr hm alphabet labels f target
  constructor
  · exact script_history_trace (2 * m - 2) m (by omega) f (2 * r - 1)
      (adaptiveWords r m) (gridDecode labels (id : Fin r → Fin r))
      (by intro v; simp [adaptiveWords, gridWords, gridRows]) decoded.1
      (by intro v phase s hs
          simpa only [neg_neg, adaptiveWords] using
            (grid_archive r r m hr hm (by omega) alphabet (adaptiveSchedule r v) v (-phase) s hs).2)
      alphabet history
  · have trace := script_history_trace (2 * m - 2) m (by omega) f (4 * r - 1)
      (fun _ => commonWords r m) (fun v => gridDecode labels (commonPosition r v) v)
      (by intro v; simp only [commonWords, gridWords, gridRows, List.length_map, List.length_ofFn]; omega) decoded.2
      (by intro v phase s hs
          simpa only [neg_neg, commonWords] using
            (grid_archive r (2 * r) m hr hm le_rfl alphabet (commonSchedule r) v (-phase) s hs).2)
      alphabet history
    exact trace

private theorem attainable {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : GridTarget r m labels f) :
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f (2 * r - 1) ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (4 * r - 1) ∧
    FourLabelPaidFeedback.OriginalSelectedPresetFeasible (2 * m - 2) m (by omega)
      alphabet f (2 * r - 1) := by
  have hm5 : 5 ≤ m := by
    have pos : 0 < (2 ^ r) ^ 2 := by positivity
    omega
  have legal : FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet
      (adaptiveSelector (r := r) (m := m) labels (f none)) := by
    intro free ar B chosen localAlphabet
    exact short_legal (2 * m - 2) m (by omega) (by omega) B
  have success (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ c ≤ 2 * r - 1, NarrowWindowCost.execute (2 * m - 2) (by omega)
        (adaptiveSelector (r := r) (m := m) labels (f none)) (2 * r - 1) w
        (NarrowWindowCost.output (2 * m - 2) (by omega) w) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c) := by
    intro w
    obtain ⟨issued, traced, count, _, _⟩ := (history_traces r m hr hm alphabet labels f target history).1
    have bound : fee (2 * r - 1) (OriginalRecord (2 * m - 2) (by omega) w) ≤ 2 * r - 1 := by
      unfold fee; split_ifs <;> omega
    refine ⟨_, bound, ?_⟩
    rw [OriginalAcquiredTrace.execute_paid_trace (2 * m - 2) m (by omega)]
    exact ⟨issued, traced, count, bound⟩
  refine ⟨⟨adaptiveSelector (r := r) (m := m) labels (f none), legal, rfl, success⟩, ?_, ?_⟩
  · have feasible := script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f
      (commonWords r m) (fun v => gridDecode labels (commonPosition r v) v)
      (scripts_decode r m hr hm alphabet labels f target).2
    have length : (commonWords r m).length = 4 * r - 1 := by
      simp only [commonWords, gridWords, gridRows, List.length_map, List.length_ofFn]
      omega
    rw [length] at feasible
    exact feasible
  · exact ⟨scriptStreams (adaptiveWords r m), adaptiveStop labels (f none), legal, rfl, success⟩

/-- Exact full-original grid prices and actual safe attaining traces.
The adaptive actions select one stream from the free INITIAL scalar only. -/
theorem original_near_critical_grid_law {Y : Type u} (r m : ℕ) (hr : 3 ≤ r)
    (hm : (2 ^ r) ^ 2 + 2 * r ≤ m) (alphabet : Bool)
    (labels : Fin (2 ^ r) → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (target : GridTarget r m labels f) :
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = (2 * r - 1 : ℕ) ∧
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = (4 * r - 1 : ℕ) ∧
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f (2 * r - 1) ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (4 * r - 1) ∧
    FourLabelPaidFeedback.OriginalSelectedPresetFeasible (2 * m - 2) m (by omega)
      alphabet f (2 * r - 1) ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace (adaptiveSelector (r := r) (m := m) labels (f none))
        free q [] issued (f q) ∧ issued.length = fee (2 * r - 1) q ∧
        (OriginalAcquiredTrace.archiveWords issued).length = m * fee (2 * r - 1) q ∧
        none ∉ issued.map Prod.snd) ∧
      (∃ issued : NarrowWindowCost.Archive m, OriginalAcquiredTrace.PaidTrace
        (presetSelector (commonStream r m) (commonStop (r := r) (m := m) labels (f none)))
        free q [] issued (f q) ∧ issued.length = fee (4 * r - 1) q ∧
        (OriginalAcquiredTrace.archiveWords issued).length = m * fee (4 * r - 1) q ∧
        none ∉ issued.map Prod.snd)) ∧
    ∀ v : ZMod 2, ∃ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      q = some ⟨v, -gridPhase r m 0 0, 0⟩ ∧ ∃ ad pre : NarrowWindowCost.Archive m,
        OriginalAcquiredTrace.PaidTrace (adaptiveSelector (r := r) (m := m) labels (f none)) free q [] ad (f q) ∧
        (OriginalAcquiredTrace.archiveWords ad).length = m * (2 * r - 1) ∧
        OriginalAcquiredTrace.PaidTrace
          (presetSelector (commonStream r m) (commonStop (r := r) (m := m) labels (f none))) free q [] pre (f q) ∧
        (OriginalAcquiredTrace.archiveWords pre).length = m * (4 * r - 1) := by
  have upper := attainable r m hr hm alphabet labels f target
  refine ⟨?_, ?_, upper.1, upper.2.1, upper.2.2,
    history_traces r m hr hm alphabet labels f target, ?_⟩
  · exact FullPositiveWindowPrice.price_exact _ _ upper.1
      (original_grid_adaptive_lower r m hr hm alphabet labels distinct f target)
  · exact FullPositiveWindowPrice.price_exact _ _ upper.2.1
      (original_grid_preset_lower r m hr hm alphabet labels distinct f target)
  · intro v
    have hm5 : 5 ≤ m := by
      have pos : 0 < (2 ^ r) ^ 2 := by positivity
      omega
    let initial : Option (LiveRecord (2 * m - 2)) := some ⟨v, -gridPhase r m 0 0, 0⟩
    have source : SourceRecord (2 * m - 2) m initial := by
      change 0 < 2 * m - 2 ∧ _
      exact ⟨by omega, by rw [FourLabelPaidFeedback.coprime m hm5]; exact one_dvd _⟩
    obtain ⟨history, actual⟩ :=
      ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega)
        alphabet (fun _ => ())).1 initial).mp source
    have record : OriginalRecord (2 * m - 2) (by omega)
        (history.flatMap (fun a => List.ofFn a.val)) = initial :=
      (OriginalExecutionBridge.record_history (2 * m - 2) m (by omega) alphabet history).trans actual
    have traces := history_traces r m hr hm alphabet labels f target history
    dsimp only at traces
    rw [record] at traces
    obtain ⟨ad, adTrace, _, adBits, _⟩ := traces.1
    obtain ⟨pre, preTrace, _, preBits, _⟩ := traces.2
    refine ⟨history, record, ?_⟩
    rw [record]
    exact ⟨ad, pre, adTrace, by simpa [fee, initial] using adBits,
      preTrace, by simpa [fee, initial] using preBits⟩

#print axioms original_grid_preset_lower
#print axioms original_grid_adaptive_lower
#print axioms original_near_critical_grid_law
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NearCriticalGrid
