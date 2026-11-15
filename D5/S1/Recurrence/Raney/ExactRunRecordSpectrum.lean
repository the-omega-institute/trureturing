/- GID: D5/S1/Recurrence/Raney/ExactRunRecordSpectrum
   generality: I
   mirror-B: D5/B/S1/Recurrence/Raney/ExactRunRecordSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-prime maximal zero-run and tied-record spectra of the literal R31 sequence. -/

import D5.S1.Recurrence.Raney.ExactBinaryRuns
import D5.S1.Recurrence.Raney.ExactTernaryRuns
import D5.S1.Recurrence.Raney.ExactPrimeRuns

/-! Complete maximal-run length and tied-record value sets of the literal R31 sequence. -/

namespace TrureTuring.Raney

/-- A record is an actual maximal run, at least as long as every earlier run. -/
def IsWeakZeroRunRecord {p : Nat} (ρ : Nat → ZMod p) (a b : Nat) : Prop :=
  IsMaximalDeltaInterval {0} ρ a b ∧
    ∀ c d, IsMaximalDeltaInterval {0} ρ c d → c < a → d + 1 - c ≤ b + 1 - a

/-- The actual maximal run starts no later than any run of the same length. -/
def IsFirstZeroRunLength {p : Nat} (ρ : Nat → ZMod p) (a b : Nat) : Prop :=
  IsMaximalDeltaInterval {0} ρ a b ∧
    ∀ c d, IsMaximalDeltaInterval {0} ρ c d → d + 1 - c = b + 1 - a → a ≤ c

def positiveZeroRunLengths {p : Nat} (ρ : Nat → ZMod p) : Set Nat :=
  {l | 0 < l ∧ ∃ a b, IsMaximalDeltaInterval {0} ρ a b ∧ l = b + 1 - a}

def positiveZeroRunRecordValues {p : Nat} (ρ : Nat → ZMod p) : Set Nat :=
  {l | 0 < l ∧ ∃ a b, IsWeakZeroRunRecord ρ a b ∧ l = b + 1 - a}

/-- Small primes have one interval per exponent; larger primes have two,
with precisely the empty first intervals at powers five and seven omitted. -/
def runSpectrumRetained (p m j : Nat) : Prop :=
  if p = 2 then 2 ≤ m ∧ j = 1
  else if p = 3 then 1 ≤ m ∧ j = 1
  else 5 ≤ p ∧ 1 ≤ m ∧ (j = 1 ∨ j = 2) ∧ (j = 2 ∨ (p ^ m ≠ 5 ∧ p ^ m ≠ 7))

def runSpectrumStart (p m j : Nat) : Nat :=
  if p = 2 then (2 ^ (m + 1) + 2) / 3
  else if p = 3 then (3 ^ m + 1) / 2
  else (j * p ^ m + 2) / 3

def runSpectrumLast (p m j : Nat) : Nat :=
  if p = 2 then 2 ^ m - 1
  else if p = 3 then (3 ^ (m + 1) - 3) / 2
  else if j = 1 then (p ^ m - 3) / 2 else p ^ m - 1

def runSpectrumLength (p m j : Nat) : Nat :=
  if p = 2 then 2 ^ m / 3
  else if p = 3 then 3 ^ m - 1
  else if j = 1 then
    (if p ^ m % 6 = 1 then (p ^ m - 7) / 6 else (p ^ m - 5) / 6)
  else p ^ m / 3

private theorem spectrum_branches (p : Nat) (hp : p.Prime) :
    (∀ a b, IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) a b →
      ∃ m j, runSpectrumRetained p m j ∧ b + 1 - a = runSpectrumLength p m j) ∧
    (∀ m j, runSpectrumRetained p m j →
      IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p))
        (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      runSpectrumLast p m j + 1 - runSpectrumStart p m j = runSpectrumLength p m j ∧
      ∀ c d, IsMaximalDeltaInterval {0} (fun n => (raneyNumber 3 1 n : ZMod p)) c d →
        c < runSpectrumStart p m j → d + 1 - c < runSpectrumLength p m j) ∧
    (∀ m h j k, runSpectrumRetained p m j → runSpectrumRetained p h k →
      (m < h ∨ (m = h ∧ j < k)) → runSpectrumLength p m j < runSpectrumLength p h k) := by
  by_cases hp2 : p = 2
  · subst p
    have spec := raney_binary_exact_zero_run_spectrum
    simp only [runSpectrumRetained, runSpectrumStart, runSpectrumLast, runSpectrumLength,
      ite_true]
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨m, hm, hlen, _⟩ := spec.1 a b hab
      exact ⟨m, 1, ⟨hm, rfl⟩, hlen⟩
    · intro m j hj
      exact spec.2.1 m hj.1
    · rintro m h j k ⟨hm, rfl⟩ ⟨hh, rfl⟩ horder
      exact spec.2.2 m h hm (by omega)
  · by_cases hp3 : p = 3
    · subst p
      have spec := raney_three_exact_zero_runs
      simp only [runSpectrumRetained, runSpectrumStart, runSpectrumLast, runSpectrumLength,
        ite_eq_right (by decide : ¬ (3 : Nat) = 2), ite_true]
      refine ⟨?_, ?_, ?_⟩
      · intro a b hab
        obtain ⟨m, hm, rfl, rfl⟩ := (spec.2.1 a b).mp hab
        exact ⟨m, 1, ⟨hm, rfl⟩, spec.2.2.1 m hm⟩
      · rintro m j ⟨hm, rfl⟩
        refine ⟨(spec.2.1 _ _).mpr ⟨m, hm, rfl, rfl⟩, spec.2.2.1 m hm, ?_⟩
        intro c d hrun hc
        have hle := spec.2.2.2.2.1 m hm c d hrun hc.le
        have hne : d + 1 - c ≠ 3 ^ m - 1 := by
          intro heq
          have := (spec.2.2.2.2.2 m hm c d hrun heq).1
          omega
        omega
      · rintro m h j k ⟨hm, rfl⟩ ⟨hh, rfl⟩ horder
        exact spec.2.2.2.1 (by omega)
    · have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        have := hp.two_le
        omega
      have spec := ExactPrime.raney_prime_ge_five_spectrum p hp hp5
      simp only [runSpectrumRetained, runSpectrumStart, runSpectrumLast, runSpectrumLength,
        ite_eq_right hp2, ite_eq_right hp3]
      refine ⟨?_, ?_, ?_⟩
      · intro a b hab
        obtain ⟨m, j, hm, hj, hne, hlen⟩ := spec.2.1 a b hab
        have hw := spec.1 m hm j hj
        exact ⟨m, j, ⟨hp5, hm, hj, hw.1.mp hne⟩, hlen.trans hw.2.1⟩
      · rintro m j ⟨_, hm, hj, hret⟩
        have hw := spec.1 m hm j hj
        obtain ⟨hrun, hearlier⟩ := hw.2.2 (hw.1.mpr hret)
        exact ⟨hrun, hw.2.1, fun c d hcd hc => (hearlier c d hcd hc).trans_eq hw.2.1⟩
      · rintro m h j k ⟨_, hm, hj, _⟩ ⟨_, hh, hk, _⟩ horder
        have hlt := spec.2.2 m h j k hm hh hj hk horder
        rw [(spec.1 m hm j hj).2.1, (spec.1 h hh k hk).2.1] at hlt
        exact hlt

/-- Complete positive maximal-run and distinct tied-record value sets for every
prime. Each retained interval is an actual positive run, a first occurrence,
and a weak record. No claim that every occurrence is a record is made. -/
theorem raney_all_prime_exact_run_record_spectrum (p : Nat) (hp : p.Prime) :
    let ρ : Nat → ZMod p := fun n => (raneyNumber 3 1 n : ZMod p)
    let values : Set Nat := {l | ∃ m j, runSpectrumRetained p m j ∧ l = runSpectrumLength p m j}
    positiveZeroRunLengths ρ = values ∧
    positiveZeroRunRecordValues ρ = values ∧
    (∀ m j, runSpectrumRetained p m j →
      IsMaximalDeltaInterval {0} ρ (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      0 < runSpectrumLength p m j ∧
      runSpectrumLast p m j + 1 - runSpectrumStart p m j = runSpectrumLength p m j ∧
      IsFirstZeroRunLength ρ (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      IsWeakZeroRunRecord ρ (runSpectrumStart p m j) (runSpectrumLast p m j)) ∧
    (∀ m h j k, runSpectrumRetained p m j → runSpectrumRetained p h k →
      (m < h ∨ (m = h ∧ j < k)) → runSpectrumLength p m j < runSpectrumLength p h k) ∧
    (∀ m h j k, runSpectrumRetained p m j → runSpectrumRetained p h k →
      runSpectrumLength p m j = runSpectrumLength p h k → m = h ∧ j = k) ∧
    (5 ≤ p → ∀ m j, 1 ≤ m → (j = 1 ∨ j = 2) →
      ((j * p ^ m + 2) / 3 ≤ (if j = 1 then (p ^ m - 3) / 2 else p ^ m - 1) ↔
        j = 2 ∨ (p ^ m ≠ 5 ∧ p ^ m ≠ 7))) := by
  dsimp only
  obtain ⟨complete, witnesses, ordered⟩ := spectrum_branches p hp
  have certified (m j : Nat) (hret : runSpectrumRetained p m j) := witnesses m j hret
  have firstRecord (m j : Nat) (hret : runSpectrumRetained p m j) :
      IsFirstZeroRunLength (fun n => (raneyNumber 3 1 n : ZMod p))
        (runSpectrumStart p m j) (runSpectrumLast p m j) ∧
      IsWeakZeroRunRecord (fun n => (raneyNumber 3 1 n : ZMod p))
        (runSpectrumStart p m j) (runSpectrumLast p m j) := by
    obtain ⟨hrun, hlen, hearlier⟩ := certified m j hret
    refine ⟨⟨hrun, ?_⟩, ⟨hrun, ?_⟩⟩
    · intro c d hcd heq
      by_contra h
      have := hearlier c d hcd (by omega)
      omega
    · intro c d hcd hc
      exact (hearlier c d hcd hc).le.trans_eq hlen.symm
  have positive (m j : Nat) (hret : runSpectrumRetained p m j) :
      0 < runSpectrumLength p m j := by
    obtain ⟨hrun, hlen, _⟩ := certified m j hret
    have := hrun.1
    omega
  refine ⟨?_, ?_, ?_, ordered, ?_, ?_⟩
  · ext l
    constructor
    · rintro ⟨_, a, b, hab, rfl⟩
      exact complete a b hab
    · rintro ⟨m, j, hret, rfl⟩
      exact ⟨positive m j hret, runSpectrumStart p m j, runSpectrumLast p m j,
        (certified m j hret).1, (certified m j hret).2.1.symm⟩
  · ext l
    constructor
    · rintro ⟨_, a, b, hab, rfl⟩
      exact complete a b hab.1
    · rintro ⟨m, j, hret, rfl⟩
      exact ⟨positive m j hret, runSpectrumStart p m j, runSpectrumLast p m j,
        (firstRecord m j hret).2, (certified m j hret).2.1.symm⟩
  · intro m j hret
    exact ⟨(certified m j hret).1, positive m j hret, (certified m j hret).2.1,
      (firstRecord m j hret).1, (firstRecord m j hret).2⟩
  · intro m h j k hm hh heq
    have hmh : m = h := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := ordered m h j k hm hh (Or.inl hlt)
        omega
      · have := ordered h m k j hh hm (Or.inl hgt)
        omega
    subst h
    refine ⟨rfl, ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := ordered m m j k hm hh (Or.inr ⟨rfl, hlt⟩)
      omega
    · have := ordered m m k j hh hm (Or.inr ⟨rfl, hgt⟩)
      omega
  · intro hp5 m j hm hj
    exact (ExactPrime.raney_prime_ge_five_spectrum p hp hp5).1 m hm j hj |>.1

#print axioms raney_all_prime_exact_run_record_spectrum

end TrureTuring.Raney
