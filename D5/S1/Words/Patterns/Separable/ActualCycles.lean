/- GID: D5/S1/Words/Patterns/Separable/ActualCycles
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/ActualCycles
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.Real]
   utility: none
   digest: Complete minimum-cut cycles have actual finite-tuple probabilities and exhaustion. -/

import D5.S1.Words.Patterns.Separable.ActualCountRatios
import D5.S1.Words.Patterns.Separable.StableEndpointCodes

namespace D5.S1.Words.Patterns.Separable.ActualCycles

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
open D5.S1.Words.Patterns.Separable.StableEndpointCodes
open D5.S1.Words.Patterns.Separable.OccupiedComparison
open Filter Topology
open Classical
open scoped BigOperators

abbrev SmallU (K : ℕ) := Σ size : Fin K, Avoider (size.val + 1)
abbrev SmallJ (K : ℕ) (sign : Bool) :=
  Σ size : Fin K, Indecomposable sign (size.val + 1)

/-- An arbitrary finite cycle has no a priori shape or step bound. -/
inductive UnboundedCycle : Bool → Type where
  | terminal {sign : Bool} (size : ℕ) (shape : Indecomposable sign (size + 1)) :
      UnboundedCycle sign
  | discard {sign : Bool} (size : ℕ) (shape : Avoider (size + 1))
      (tail : UnboundedCycle (!sign)) : UnboundedCycle sign

namespace UnboundedCycle

def cap {sign} : UnboundedCycle sign → ℕ
  | .terminal size _ => size + 1
  | .discard size _ tail => max (size + 1) tail.cap

def size {sign} : UnboundedCycle sign → ℕ
  | .terminal size _ => size + 1
  | .discard size _ tail => size + 1 + tail.size

def steps {sign} : UnboundedCycle sign → ℕ
  | .terminal _ _ => 1
  | .discard _ _ tail => tail.steps + 1

private theorem steps_pos {sign} (c : UnboundedCycle sign) : 0 < c.steps := by
  cases c <;> simp [steps]

end UnboundedCycle

/-- One cycle consists of right removals followed by its first left emission. -/
def Cycle (K : ℕ) : Bool → ℕ → Type
  | _, 0 => Empty
  | sign, H + 1 => SmallJ K sign ⊕ (SmallU K × Cycle K (!sign) H)

noncomputable instance (K H : ℕ) (sign : Bool) : Fintype (Cycle K sign H) := by
  induction H generalizing sign with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ H ih =>
    letI := ih (!sign)
    exact inferInstanceAs (Fintype (SmallJ K sign ⊕ (SmallU K × Cycle K (!sign) H)))

namespace Cycle

def size {K sign} : {H : ℕ} → Cycle K sign H → ℕ
  | _ + 1, .inl terminal => terminal.1.val + 1
  | _ + 1, .inr pair => pair.1.1.val + 1 + size pair.2

def code {K sign} : {H : ℕ} → Cycle K sign H → Code K H
  | H + 1, .inl terminal => .emit sign terminal.1 terminal.2 (.stop .good : Code K H)
  | _ + 1, .inr pair => .discard sign pair.1.1 pair.1.2 (code pair.2)

/-- Forget only the two finite bookkeeping bounds. -/
def erase {K sign} : {H : ℕ} → Cycle K sign H → UnboundedCycle sign
  | _ + 1, .inl terminal => .terminal terminal.1.val terminal.2
  | _ + 1, .inr pair => .discard pair.1.1.val pair.1.2 pair.2.erase

private theorem erase_size {K H sign} (c : Cycle K sign H) : c.erase.size = c.size := by
  induction H generalizing sign with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl terminal => rfl
    | inr pair => simp only [erase, UnboundedCycle.size, size, ih]

private theorem legal {K H sign state} (c : Cycle K sign H)
    (compatible : state = none ∨ state = some (!sign)) : Legal state 1 c.code := by
  induction H generalizing sign state with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl terminal =>
      simp only [code, Legal]
      exact ⟨by omega, compatible, Or.inl ⟨by omega, trivial⟩⟩
    | inr pair =>
      exact ⟨by omega, compatible, ih pair.2 (by simp)⟩

def stable {K H sign state} (c : Cycle K sign H)
    (compatible : state = none ∨ state = some (!sign)) : StableCode state 1 K H :=
  ⟨c.code, c.legal compatible⟩

private theorem good {K H sign} (c : Cycle K sign H) : terminal c.code = .good := by
  induction H generalizing sign with
  | zero => exact nomatch c
  | succ H ih => cases c with
    | inl terminal => rfl
    | inr pair => exact ih pair.2

private theorem size_bound {K H sign} (c : Cycle K sign H) : c.size ≤ H * K := by
  induction H generalizing sign with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl terminal =>
      have bound := terminal.1.isLt
      simp only [size, Nat.succ_mul]
      omega
    | inr pair =>
      have bound := pair.1.1.isLt
      have child := ih pair.2
      simp only [size, Nat.succ_mul]
      omega

private theorem code_injective {K H sign} : Function.Injective
    (code (K := K) (H := H) (sign := sign)) := by
  induction H generalizing sign with
  | zero => intro c; exact nomatch c
  | succ H ih =>
    intro first last eq
    cases first with
    | inl a =>
      cases last with
      | inl b =>
        rcases a with ⟨a, α⟩
        rcases b with ⟨b, β⟩
        simp only [code, Code.emit.injEq, true_and, and_true] at eq
        rcases eq with ⟨rfl, h⟩
        cases eq_of_heq h
        rfl
      | inr b => cases eq
    | inr a =>
      cases last with
      | inl b => cases eq
      | inr b =>
        rcases a with ⟨⟨a, α⟩, ta⟩
        rcases b with ⟨⟨b, β⟩, tb⟩
        simp only [code, Code.discard.injEq, true_and] at eq
        rcases eq with ⟨rfl, h, rest⟩
        cases eq_of_heq h
        have same := ih rest
        cases same
        rfl

private theorem legal_zero {K H state} (code : Code K H) (valid : Legal state 0 code) :
    code = .stop .good := by
  cases code with
  | stop kind =>
    have same : kind = .good := by simpa [Legal] using valid
    subst kind
    rfl
  | emit sign size shape tail => exact (Nat.lt_irrefl 0 valid.1).elim
  | discard sign size shape tail => exact (Nat.lt_irrefl 0 valid.1).elim

private theorem of_good {K H state} (code : Code K H) (valid : Legal state 1 code)
    (good : terminal code = .good) :
    ∃ sign : Bool, ∃ cycle : Cycle K sign H,
      (state = none ∨ state = some (!sign)) ∧ cycle.code = code := by
  induction H generalizing state with
  | zero => cases code with
    | stop kind => simp_all [Legal, terminal]
  | succ H ih =>
    cases code with
    | stop kind => simp_all [Legal, terminal]
    | emit sign size shape tail =>
      have rest : Legal none 0 tail := by
        simpa only [show 1 - (size.val + 1) = 0 by omega] using valid.2.2
      have stopped := legal_zero tail rest
      subst tail
      exact ⟨sign, Sum.inl ⟨size, shape⟩, valid.2.1, rfl⟩
    | discard sign size shape tail =>
      obtain ⟨childSign, child, compatible, reconstructed⟩ := ih tail valid.2.2 good
      have signEq : childSign = !sign := by
        rcases compatible with impossible | same
        · cases impossible
        · have same := Option.some.inj same
          simpa only [Bool.not_not] using (congrArg Bool.not same).symm
      subst childSign
      exact ⟨sign, Sum.inr (⟨size, shape⟩, child), valid.2.1,
        by simp only [Cycle.code, reconstructed]⟩

private theorem remaining_cast {state n m} (eq : n = m) (h : EndpointHistory state n) :
    (eq ▸ h : EndpointHistory state m).remaining = h.remaining := by
  cases eq
  rfl

private theorem state_cast {state n m} (eq : n = m) (h : EndpointHistory state n) :
    (eq ▸ h : EndpointHistory state m).remainingState = h.remainingState := by
  cases eq
  rfl

private theorem remaining {K H sign state} (c : Cycle K sign H)
    (compatible : state = none ∨ state = some (!sign)) (n : ℕ) (large : H * K < n) :
    (history (c.stable compatible) n large).remaining = n - c.size ∧
    (history (c.stable compatible) n large).remainingState = none := by
  induction H generalizing sign state n with
  | zero => exact nomatch c
  | succ H ih =>
    cases c with
    | inl item =>
      simp [history, stable, code, decode, remaining_cast, state_cast,
        EndpointHistory.remaining, EndpointHistory.remainingState, size]
    | inr pair =>
      have hchild : H * K < n - (pair.1.1.val + 1) := by
        have := pair.1.1.isLt
        rw [Nat.succ_mul] at large
        omega
      have child := ih pair.2 (state := some sign) (by simp) _ hchild
      simpa only [history, stable, code, decode, remaining_cast, state_cast,
        EndpointHistory.remaining, EndpointHistory.remainingState, size,
        Nat.sub_sub, Nat.add_assoc] using child

end Cycle

namespace UnboundedCycle

private def fitAt (K : ℕ) : (H : ℕ) → {sign : Bool} → (c : UnboundedCycle sign) →
    c.cap ≤ K → c.steps ≤ H → Cycle K sign H
  | 0, _, c, _, hs => False.elim (by have := c.steps_pos; omega)
  | H + 1, _, .terminal size shape, hc, _ =>
      Sum.inl ⟨⟨size, by change size + 1 ≤ K at hc; omega⟩, shape⟩
  | H + 1, _, .discard size shape tail, hc, hs =>
      Sum.inr (⟨⟨size, by have := le_trans (le_max_left _ _) hc; omega⟩, shape⟩,
        fitAt K H tail (le_trans (le_max_right _ _) hc)
          (by change tail.steps + 1 ≤ H + 1 at hs; omega))

def fit {sign} (c : UnboundedCycle sign) (K H : ℕ)
    (capBound : c.cap ≤ K) (stepBound : c.steps ≤ H) : Cycle K sign H :=
  fitAt K H c capBound stepBound

private theorem erase_fit {sign} (c : UnboundedCycle sign) (K H : ℕ)
    (capBound : c.cap ≤ K) (stepBound : c.steps ≤ H) :
    (c.fit K H capBound stepBound).erase = c := by
  induction c generalizing H with
  | terminal size shape =>
    cases H with
    | zero => simp [steps] at stepBound
    | succ H => rfl
  | discard size shape tail ih =>
    cases H with
    | zero => simp [steps] at stepBound
    | succ H =>
      change UnboundedCycle.discard size shape ((tail.fit K H _ _).erase) = _
      rw [ih]

end UnboundedCycle

abbrev Family (K H : ℕ) := Σ sign : Bool, Cycle K sign H

/-- The success kind of the original actual minimum-cut classifier. -/
def FirstSuccess (K H n : ℕ) (π : Avoider n) : Prop :=
  (CappedExploration.classify 1 0 H K (⟨π, trivial⟩ : Carrier none n)).2 = .good

namespace Family

def size {K H} (c : Family K H) : ℕ := c.2.size

def stable {K H} (c : Family K H) : StableCode none 1 K H := c.2.stable (Or.inl rfl)

private theorem size_bound {K H} (c : Family K H) : c.size ≤ H * K := c.2.size_bound

private def firstSign {K H} : Code K H → Option Bool
  | .stop _ => none
  | .emit sign _ _ _ => some sign
  | .discard sign _ _ _ => some sign

private theorem first_sign {K H sign} (c : Cycle K sign H) :
    firstSign c.code = some sign := by
  cases H with
  | zero => exact nomatch c
  | succ H => cases c <;> rfl

private theorem code_injective {K H} :
    Function.Injective (fun c : Family K H => c.stable.val) := by
  rintro ⟨firstSign, first⟩ ⟨lastSign, last⟩ eq
  have signs := congrArg Family.firstSign eq
  change Family.firstSign first.code = Family.firstSign last.code at signs
  rw [first_sign, first_sign] at signs
  have sameSign := Option.some.inj signs
  subst lastSign
  have same := Cycle.code_injective eq
  cases same
  rfl

def leaf {K H} (c : Family K H) (n : ℕ) (large : H * K < n) :
    (history c.stable n large).Leaf ≃ Avoider (n - c.size) := by
  have rem := c.2.remaining (Or.inl rfl) n large
  change (history c.stable n large).remaining = n - c.size ∧
    (history c.stable n large).remainingState = none at rem
  dsimp only [EndpointHistory.Leaf]
  change Carrier (history c.stable n large).remainingState
    (history c.stable n large).remaining ≃ _
  rw [rem.1, rem.2]
  exact Equiv.subtypeUnivEquiv (fun _ => trivial)

private theorem common_parse {K H n} (large : H * K + max (2 * K) 1 < n)
    (first last : Family K H) (π : Avoider n)
    (hf : (history first.stable n (by omega)).Event π)
    (hl : (history last.stable n (by omega)).Event π) : first = last := by
  have firstFiber := (stable_success_fibers K H none 1 0 n
    (by simpa using large) first.stable first.2.good π).mpr hf
  have lastFiber := (stable_success_fibers K H none 1 0 n
    (by simpa using large) last.stable last.2.good π).mpr hl
  rcases firstFiber with ⟨firstAllowed, firstEq⟩
  rcases lastFiber with ⟨lastAllowed, lastEq⟩
  have histEq : history first.stable n (by omega) = history last.stable n (by omega) :=
    congrArg Prod.fst (firstEq.symm.trans lastEq)
  have codes := congrArg (fun path : EndpointHistory none n =>
    compress path .good K H) histEq
  have firstRoundtrip := ((stable_code_transport K H).1 none 1 n (by omega)
    first.stable).2.2.2.1
  have lastRoundtrip := ((stable_code_transport K H).1 none 1 n (by omega)
    last.stable).2.2.2.1
  change compress (history first.stable n _) (terminal first.2.code) K H =
    some first.stable.val at firstRoundtrip
  change compress (history last.stable n _) (terminal last.2.code) K H =
    some last.stable.val at lastRoundtrip
  rw [first.2.good] at firstRoundtrip
  rw [last.2.good] at lastRoundtrip
  rw [firstRoundtrip, lastRoundtrip] at codes
  exact code_injective (Option.some.inj codes)

private theorem complete_parse {K H n} (large : H * K + max (2 * K) 1 < n)
    (π : Avoider n) :
    (∃ c : Family K H, (history c.stable n (by omega)).Event π) ↔ FirstSuccess K H n π := by
  have bound : H * K + max (2 * K) (max 1 0) < n := by simpa using large
  let chosen := boundedClassify 1 0 K H bound (⟨π, trivial⟩ : Carrier none n)
  have actual := (stable_code_transport K H).2 none 1 0 n bound
    (⟨π, trivial⟩ : Carrier none n)
  constructor
  · rintro ⟨c, belongs⟩
    obtain ⟨allowed, parsed⟩ :=
      (stable_success_fibers K H none 1 0 n bound c.stable c.2.good π).mpr belongs
    exact congrArg Prod.snd parsed
  · intro succeeded
    have kind : terminal chosen.val = .good :=
      (congrArg Prod.snd actual).symm.trans succeeded
    obtain ⟨sign, cycle, _, encoded⟩ := Cycle.of_good chosen.val chosen.property kind
    let c : Family K H := ⟨sign, cycle⟩
    have same : c.stable = chosen := Subtype.ext encoded
    refine ⟨c, (stable_success_fibers K H none 1 0 n bound c.stable c.2.good π).mp ?_⟩
    refine ⟨trivial, ?_⟩
    rw [same]
    change CappedExploration.classify 1 0 H K (⟨π, trivial⟩ : Carrier none n) =
      (history chosen n _, .good)
    rw [← kind]
    exact actual

end Family

/-- A tuple has a prescribed number of complete cycles, including the empty tuple. -/
def Tuple (K H : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Family K H × Tuple K H k

/-- Arbitrary fixed finite tuples, independent of exhaustion bounds. -/
def UnboundedTuple : ℕ → Type
  | 0 => Unit
  | k + 1 => (Σ sign : Bool, UnboundedCycle sign) × UnboundedTuple k

namespace UnboundedTuple

def cap : {k : ℕ} → UnboundedTuple k → ℕ
  | 0, _ => 0
  | _ + 1, pair => max pair.1.2.cap pair.2.cap

def size : {k : ℕ} → UnboundedTuple k → ℕ
  | 0, _ => 0
  | _ + 1, pair => pair.1.2.size + pair.2.size

def steps : {k : ℕ} → UnboundedTuple k → ℕ
  | 0, _ => 0
  | _ + 1, pair => max pair.1.2.steps pair.2.steps

def fit : {k : ℕ} → (tuple : UnboundedTuple k) → (K H : ℕ) →
    tuple.cap ≤ K → tuple.steps ≤ H → Tuple K H k
  | 0, _, _, _, _, _ => ()
  | _ + 1, pair, K, H, hc, hs =>
    (⟨pair.1.1, pair.1.2.fit K H (le_trans (le_max_left _ _) hc)
      (le_trans (le_max_left _ _) hs)⟩,
      pair.2.fit K H (le_trans (le_max_right _ _) hc) (le_trans (le_max_right _ _) hs))

end UnboundedTuple

noncomputable instance (K H k : ℕ) : Fintype (Tuple K H k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Family K H × Tuple K H k))

namespace Tuple

def size {K H} : {k : ℕ} → Tuple K H k → ℕ
  | 0, _ => 0
  | _ + 1, pair => pair.1.size + size pair.2

def erase {K H} : {k : ℕ} → Tuple K H k → UnboundedTuple k
  | 0, _ => ()
  | _ + 1, pair => (⟨pair.1.1, pair.1.2.erase⟩, pair.2.erase)

private theorem erase_size {K H k} (tuple : Tuple K H k) : tuple.erase.size = tuple.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [erase, UnboundedTuple.size, size, Family.size, Cycle.erase_size, ih]

private theorem size_bound {K H k} (tuple : Tuple K H k) : tuple.size ≤ k * (H * K) := by
  induction k with
  | zero => simp [size]
  | succ k ih =>
    have hc := tuple.1.size_bound
    have ht := ih tuple.2
    simp only [size, Nat.succ_mul]
    omega

def threshold (K H k : ℕ) : ℕ := k * (H * K) + max (2 * K) 1

private theorem child_bound {K H k n} (tuple : Tuple K H (k + 1))
    (large : threshold K H (k + 1) < n) :
    threshold K H k < n - tuple.1.size := by
  have := tuple.1.size_bound
  simp only [threshold, Nat.succ_mul] at *
  omega

private theorem first_bound {K H k n} (large : threshold K H (k + 1) < n) :
    H * K + max (2 * K) 1 < n := by
  simp only [threshold, Nat.succ_mul] at large
  omega

/-- Restricted actual terminal fibers are passed unchanged to the next cycle. -/
def Event {K H} : {k : ℕ} → Tuple K H k → (n : ℕ) →
    threshold K H k < n → Avoider n → Prop
  | 0, _, _, _, _ => True
  | k + 1, pair, n, large, π =>
    (history pair.1.stable n (by have := first_bound large; omega)).EventFor
      (fun sample => Event pair.2 (n - pair.1.size) (child_bound pair large)
        (pair.1.leaf n (by have := first_bound large; omega) sample)) π

private theorem event_unique {K H k n} (large : threshold K H k < n)
    (first last : Tuple K H k) (π : Avoider n)
    (hf : first.Event n large π) (hl : last.Event n large π) : first = last := by
  induction k generalizing n with
  | zero => exact @Subsingleton.elim Unit inferInstance first last
  | succ k ih =>
    rcases first with ⟨fc, ft⟩
    rcases last with ⟨lc, lt⟩
    rcases hf with ⟨fs, hft, hfs⟩
    rcases hl with ⟨ls, hlt, hls⟩
    have same := Family.common_parse (first_bound large) fc lc π ⟨fs, hfs⟩ ⟨ls, hls⟩
    subst lc
    have sampleEq : fs = ls :=
      (endpoint_history_count_kernel _).2.1 (hfs.trans hls.symm)
    subst ls
    have tails := ih (child_bound (fc, ft) large) ft lt
      (fc.leaf n (by have := first_bound large; omega) fs) hft hlt
    exact congrArg (Prod.mk fc) tails

private theorem event_count {K H k n} (tuple : Tuple K H k)
    (large : threshold K H k < n) :
    Nat.card {π : Avoider n // tuple.Event n large π} =
      Nat.card (Avoider (n - tuple.size)) := by
  induction k generalizing n with
  | zero =>
    simpa only [Event, size, Nat.sub_zero] using
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ : Avoider n => trivial))
  | succ k ih =>
    let path := history tuple.1.stable n (by have := first_bound large; omega)
    let next (sample : path.Leaf) := tuple.2.Event (n - tuple.1.size)
      (child_bound tuple large) (tuple.1.leaf n (by have := first_bound large; omega) sample)
    have kernel := ((endpoint_history_count_kernel path).2.2.2.2.2.2.2.1 next).1
    change Nat.card {π : Avoider n // path.EventFor next π} = _
    rw [kernel]
    let eqv := Equiv.subtypeEquiv
      (p := next) (q := tuple.2.Event (n - tuple.1.size) (child_bound tuple large))
      (tuple.1.leaf n (by have := first_bound large; omega)) (fun _ => Iff.rfl)
    rw [Nat.card_congr eqv, ih tuple.2 (child_bound tuple large)]
    simp only [size, Nat.sub_sub]

private theorem event_mass {K H k n} (tuple : Tuple K H k)
    (large : threshold K H k < n) :
    actualMass n (tuple.Event n large) =
      (Nat.card (Avoider (n - tuple.size)) : ℝ) / Nat.card (Avoider n) := by
  let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
  change ((uniformPmf (Avoider n)).toOuterMeasure
    {π | tuple.Event n large π}).toReal = _
  rw [uniformPmf_toOuterMeasure_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ← Nat.card_eq_fintype_card]
  change (Nat.card {π : Avoider n // tuple.Event n large π} : ℝ) /
    Nat.card (Avoider n) = _
  rw [event_count tuple large]

noncomputable def probability {K H k} (tuple : Tuple K H k) (n : ℕ) : ℝ :=
  if large : threshold K H k < n then actualMass n (tuple.Event n large) else 0

private theorem probability_limit {K H k} (tuple : Tuple K H k) :
    Tendsto tuple.probability atTop (𝓝 (rho ^ tuple.size)) := by
  apply (ActualCountRatios.actual_fixed_shift_ratio tuple.size).congr'
  filter_upwards [Filter.eventually_gt_atTop (threshold K H k)] with n large
  simp only [probability, dif_pos large, event_mass tuple large]

end Tuple

namespace UnboundedTuple

private theorem erase_fit {k} (tuple : UnboundedTuple k) (K H : ℕ)
    (hc : tuple.cap ≤ K) (hs : tuple.steps ≤ H) :
    (tuple.fit K H hc hs).erase = tuple := by
  induction k with
  | zero => exact @Subsingleton.elim Unit inferInstance _ _
  | succ k ih =>
    rcases tuple with ⟨⟨sign, cycle⟩, tail⟩
    change ((⟨sign, (cycle.fit K H _ _).erase⟩ : Σ sign : Bool, UnboundedCycle sign),
      (tail.fit K H _ _).erase) = _
    rw [UnboundedCycle.erase_fit, ih]

end UnboundedTuple

private noncomputable def uMass (K : ℕ) : ℝ := ∑ n ∈ Finset.range K, shapeWeight n
private noncomputable def jMass (K : ℕ) : ℝ := ∑ n ∈ Finset.range K,
  rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)

private theorem small_u_mass (K : ℕ) :
    (∑ shape : SmallU K, rho ^ (shape.1.val + 1)) = uMass K := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  simpa only [uMass, shapeWeight, mul_comm] using
    (Fin.sum_univ_eq_sum_range (fun n =>
      (Nat.card (Avoider (n + 1)) : ℝ) * rho ^ (n + 1)) K)

private theorem small_j_mass (K : ℕ) (sign : Bool) :
    (∑ shape : SmallJ K sign, rho ^ (shape.1.val + 1)) = jMass K := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have counts := ActualCardinality.actual_schroder_cardinality.2.2.1
  simp_rw [counts sign, ← counts false]
  simpa only [jMass, mul_comm] using
    (Fin.sum_univ_eq_sum_range (fun n =>
      (Nat.card (Indecomposable false (n + 1)) : ℝ) * rho ^ (n + 1)) K)

private theorem cycle_mass (K H : ℕ) (sign : Bool) :
    (∑ c : Cycle K sign H, rho ^ c.size) =
      jMass K * ∑ r ∈ Finset.range H, uMass K ^ r := by
  induction H generalizing sign with
  | zero =>
    let : IsEmpty (Cycle K sign 0) := inferInstanceAs (IsEmpty Empty)
    simp
  | succ H ih =>
    change (∑ c : SmallJ K sign ⊕ (SmallU K × Cycle K (!sign) H),
      rho ^ Cycle.size (K := K) (sign := sign) (H := H + 1) c) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Cycle.size]
    simp_rw [show ∀ a b : ℕ, rho ^ (a + 1 + b) = rho ^ (a + 1) * rho ^ b from
      fun a b => pow_add rho (a + 1) b]
    rw [small_j_mass]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, small_u_mass, ih, Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    ring

private theorem family_mass (K H : ℕ) :
    (∑ c : Family K H, rho ^ c.size) =
      2 * jMass K * ∑ r ∈ Finset.range H, uMass K ^ r := by
  rw [Fintype.sum_sigma]
  simp only [Family.size, cycle_mass, Fintype.sum_bool]
  ring

private theorem tuple_mass (K H k : ℕ) :
    (∑ tuple : Tuple K H k, rho ^ tuple.size) =
      (2 * jMass K * ∑ r ∈ Finset.range H, uMass K ^ r) ^ k := by
  induction k with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    simp
  | succ k ih =>
    change (∑ pair : Family K H × Tuple K H k,
      rho ^ (pair.1.size + Tuple.size pair.2)) = _
    simp only [pow_add, Fintype.sum_prod_type, ← Finset.mul_sum]
    rw [← Finset.sum_mul, family_mass, ih, pow_succ]
    ring


private theorem mass_count (n : ℕ) (event : Avoider n → Prop) :
    actualMass n event =
      (Nat.card {π : Avoider n // event π} : ℝ) / Nat.card (Avoider n) := by
  let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
  change ((uniformPmf (Avoider n)).toOuterMeasure {π | event π}).toReal = _
  rw [uniformPmf_toOuterMeasure_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.card_eq_fintype_card]
  rfl

/-- Success means that the actual permutation has the given number of complete cycles
within both finite bounds. Its complement includes every restricted unsuccessful fiber. -/
def Success (K H k n : ℕ) (large : Tuple.threshold K H k < n) (π : Avoider n) : Prop :=
  ∃ tuple : Tuple K H k, tuple.Event n large π

noncomputable def successProbability (K H k n : ℕ) : ℝ :=
  if large : Tuple.threshold K H k < n then actualMass n (Success K H k n large) else 0

/-- Small source sizes are unsuccessful; no restricted leaf is replaced by a full leaf. -/
def Failed (K H k n : ℕ) (π : Avoider n) : Prop :=
  ¬ ∃ large : Tuple.threshold K H k < n, Success K H k n large π

private theorem success_count {K H k n} (large : Tuple.threshold K H k < n) :
    Nat.card {π : Avoider n // Success K H k n large π} =
      ∑ tuple : Tuple K H k, Nat.card (Avoider (n - tuple.size)) := by
  let total := Σ tuple : Tuple K H k, {π : Avoider n // tuple.Event n large π}
  let mapping : total → {π : Avoider n // Success K H k n large π} :=
    fun item => ⟨item.2.val, item.1, item.2.property⟩
  have injective : Function.Injective mapping := by
    rintro ⟨first, firstπ⟩ ⟨last, lastπ⟩ equality
    have actualEq : firstπ.val = lastπ.val := congrArg Subtype.val equality
    have other := lastπ.property
    rw [← actualEq] at other
    have same := Tuple.event_unique large first last firstπ.val firstπ.property other
    subst last
    have actual : firstπ = lastπ := Subtype.ext actualEq
    cases actual
    rfl
  have onto : Function.Surjective mapping := by
    rintro ⟨π, tuple, belongs⟩
    exact ⟨⟨tuple, ⟨π, belongs⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective mapping ⟨injective, onto⟩)]
  simp only [total, Nat.card_eq_fintype_card, Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun tuple _ => by
    simpa only [Nat.card_eq_fintype_card] using Tuple.event_count tuple large)

private theorem success_sum (K H k n : ℕ) :
    successProbability K H k n = ∑ tuple : Tuple K H k, tuple.probability n := by
  by_cases large : Tuple.threshold K H k < n
  · simp only [successProbability, Tuple.probability, dif_pos large,
      mass_count, success_count large, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun tuple _ => by rw [Tuple.event_count tuple large])
  · simp [successProbability, Tuple.probability, large]

private theorem failure_mass (K H k n : ℕ) :
    actualMass n (Failed K H k n) = 1 - successProbability K H k n := by
  have positive : (Nat.card (Avoider n) : ℝ) ≠ 0 := by
    let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
    exact_mod_cast (Nat.card_pos (α := Avoider n)).ne'
  by_cases large : Tuple.threshold K H k < n
  · have same : Failed K H k n = fun π => ¬ Success K H k n large π := by
      funext π
      simp only [Failed]
      simp [large]
    rw [same, successProbability, dif_pos large, mass_count, mass_count]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [Nat.cast_sub (Fintype.card_subtype_le _)]
    rw [sub_div, div_self (by simpa only [Nat.card_eq_fintype_card] using positive)]
  · have same : Failed K H k n = fun _ => True := by
      funext π
      simp [Failed, large]
    rw [same, successProbability, dif_neg large, mass_count]
    simp only [sub_zero, Nat.card_eq_fintype_card, Fintype.card_subtype_true]
    exact div_self (by simpa only [Nat.card_eq_fintype_card] using positive)

private theorem success_limit (K H k : ℕ) :
    Tendsto (successProbability K H k) atTop
      (𝓝 ((2 * jMass K * ∑ r ∈ Finset.range H, uMass K ^ r) ^ k)) := by
  rw [← tuple_mass]
  simpa only [← success_sum] using
    (tendsto_finsetSum Finset.univ (fun tuple _ => Tuple.probability_limit tuple))

private theorem bound_limits (H k : ℕ) :
    Tendsto (fun K => (2 * jMass K * ∑ r ∈ Finset.range H, uMass K ^ r) ^ k)
      atTop (𝓝 ((2 * ceiling * ∑ r ∈ Finset.range H, b ^ r) ^ k)) := by
  have u : Tendsto uMass atTop (𝓝 b) := by
    change Tendsto (fun K => ∑ n ∈ Finset.range K, shapeWeight n) atTop (𝓝 b)
    simpa only [critical_shape_masses.2.1] using
      critical_shape_masses.1.hasSum.tendsto_sum_nat
  have j : Tendsto jMass atTop (𝓝 ceiling) := by
    change Tendsto (fun K => ∑ n ∈ Finset.range K,
      rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)) atTop (𝓝 ceiling)
    simpa only [critical_shape_masses.2.2.2.2.2.1] using
      critical_shape_masses.2.2.2.2.1.hasSum.tendsto_sum_nat
  exact ((tendsto_const_nhds.mul j).mul
    (tendsto_finsetSum (Finset.range H) (fun r _ => u.pow r))).pow k

private theorem cycle_bound_limit (k : ℕ) :
    Tendsto (fun H => (2 * ceiling * ∑ r ∈ Finset.range H, b ^ r) ^ k)
      atTop (𝓝 1) := by
  have sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have bounds : 0 < b ∧ b < 1 := by
    dsimp [b]
    constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have geometric := (hasSum_geometric_of_abs_lt_one
    (show |b| < 1 by rw [abs_of_pos bounds.1]; exact bounds.2)).tendsto_sum_nat
  have normalization : 2 * ceiling * (1 - b)⁻¹ = 1 := by
    dsimp [ceiling, a]
    have nz : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr bounds.2)
    field_simp
  have limit := ((tendsto_const_nhds (x := 2 * ceiling)).mul geometric).pow k
  simpa only [normalization, one_pow] using limit

private theorem exhaustion (k : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ K H N : ℕ, ∀ n ≥ N, actualMass n (Failed K H k n) < ε := by
  have hH := (cycle_bound_limit k).eventually
    (Ioi_mem_nhds (show (1 - ε / 3 : ℝ) < 1 by linarith))
  obtain ⟨H, hH⟩ := hH.exists
  have hK := (bound_limits H k).eventually
    (Ioi_mem_nhds (show (1 - 2 * ε / 3 : ℝ) <
      (2 * ceiling * ∑ r ∈ Finset.range H, b ^ r) ^ k by
      exact lt_trans (by linarith) hH))
  obtain ⟨K, hK⟩ := hK.exists
  have hn := (success_limit K H k).eventually
    (Ioi_mem_nhds (show (1 - ε : ℝ) <
      (2 * jMass K * ∑ r ∈ Finset.range H, uMass K ^ r) ^ k by
      exact lt_trans (by linarith) hK))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hn
  refine ⟨K, H, N, fun n hn => ?_⟩
  rw [failure_mass]
  have := hN n hn
  linarith

/-- Actual finite tuple events are uniquely parsed, counted exactly and exhausted without
losing probability. All limits are along the full sequence of source sizes. -/
theorem actual_complete_cycles :
    (∀ K H k n (large : Tuple.threshold K H k < n)
      (first last : Tuple K H k) (π : Avoider n),
      first.Event n large π → last.Event n large π → first = last) ∧
    (∀ K H k n (large : Tuple.threshold K H k < n) (tuple : Tuple K H k),
      0 < n - tuple.size ∧
      Nat.card {π : Avoider n // tuple.Event n large π} =
        Nat.card (Avoider (n - tuple.size)) ∧
      actualMass n (tuple.Event n large) =
        (Nat.card (Avoider (n - tuple.size)) : ℝ) / Nat.card (Avoider n)) ∧
    (∀ K H k (tuple : Tuple K H k),
      Tendsto tuple.probability atTop (𝓝 (rho ^ tuple.size))) ∧
    (∀ K H k n (large : Tuple.threshold K H k < n),
      Nat.card {π : Avoider n // Success K H k n large π} =
        ∑ tuple : Tuple K H k, Nat.card (Avoider (n - tuple.size))) ∧
    (∀ K H k n, actualMass n (Failed K H k n) = 1 - successProbability K H k n) ∧
    (∀ K H k, Tendsto (successProbability K H k) atTop
      (𝓝 (∑ tuple : Tuple K H k, rho ^ tuple.size))) ∧
    (∀ k (ε : ℝ), 0 < ε →
      ∃ K H N : ℕ, ∀ n ≥ N, actualMass n (Failed K H k n) < ε) ∧
    (∀ k (tuple : UnboundedTuple k),
      ∃ K H : ℕ, ∃ bounded : Tuple K H k, bounded.erase = tuple ∧
        Tendsto bounded.probability atTop (𝓝 (rho ^ tuple.size))) ∧
    (∀ K H n (large : H * K + max (2 * K) 1 < n) (π : Avoider n),
      (∃ c : Family K H, (history c.stable n (by omega)).Event π) ↔ FirstSuccess K H n π) := by
  refine ⟨fun _ _ _ _ large => Tuple.event_unique large,
    ?_,
    fun _ _ _ => Tuple.probability_limit, fun _ _ _ _ => success_count,
    failure_mass, ?_, exhaustion, ?_, ?_⟩
  · intro K H k n large tuple
    refine ⟨?_, Tuple.event_count tuple large, Tuple.event_mass tuple large⟩
    have bound := Tuple.size_bound tuple
    dsimp [Tuple.threshold] at large
    omega
  · intro K H k
    rw [tuple_mass]
    exact success_limit K H k
  · intro k tuple
    let bounded := tuple.fit tuple.cap tuple.steps le_rfl le_rfl
    have erased : bounded.erase = tuple := UnboundedTuple.erase_fit tuple _ _ le_rfl le_rfl
    refine ⟨tuple.cap, tuple.steps, bounded, erased, ?_⟩
    have lengths : tuple.size = bounded.size :=
      (congrArg UnboundedTuple.size erased).symm.trans (Tuple.erase_size bounded)
    rw [lengths]
    exact Tuple.probability_limit bounded
  · exact fun _ _ _ large => Family.complete_parse large

#print axioms actual_complete_cycles

end D5.S1.Words.Patterns.Separable.ActualCycles
