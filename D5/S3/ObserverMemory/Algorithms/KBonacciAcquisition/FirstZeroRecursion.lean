/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstZeroRecursion
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Exact first-zero necessity and bounded constructive sufficiency on actual prefix cells. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhaseRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstZeroRecursion

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhaseRecovery

/- This model uses the original KBonacci recurrence, its fixed mod-two scalar,
legal-run language and endpoint alphabet. Its all-order results do not provide
a theorem for an arbitrary recurrence, scalar readout or controlled machine. -/

/-- Initial sources and their current records after a successful all-one
prefix. The common current scalar is independent of the initial tail. -/
def prefixRecords (k m t h : ℕ) (v u : ZMod 2) (S : Set (ZMod (k + 1))) :
    Set (Option (LiveRecord k) × Option (LiveRecord k)) :=
  {pair | ∃ phase ∈ S, ∃ s < h,
    pair = (some ⟨v, phase, s⟩,
      some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩)}

/-- Nonempty actual prefix cells retain initial and current tails separately. -/
def prefixCell (k m t h : ℕ) (v u : ZMod 2) (S : Set (ZMod (k + 1)))
    (positive : 0 < h) (nonempty : S.Nonempty) :
    CandidateState k (Option (LiveRecord k)) :=
  ⟨prefixRecords k m t h v u S, by
    obtain ⟨phase, member⟩ := nonempty
    exact ⟨_, phase, member, 0, positive, rfl⟩⟩

/-- All initially live sources rejected by an action share one ORIGINAL label.
For a zero-length leading run the rejection set is empty. -/
def RejectionConstant {k : ℕ} {Y : Type*} (f : Option (LiveRecord k) → Y)
    (v : ZMod 2) (h a : ℕ) (S : Set (ZMod (k + 1))) : Prop :=
  ∀ phase₁ ∈ S, ∀ phase₂ ∈ S, ∀ s₁ < h, ∀ s₂ < h,
    h - a ≤ s₁ → h - a ≤ s₂ →
      f (some ⟨v, phase₁, s₁⟩) = f (some ⟨v, phase₂, s₂⟩)

/-- Literal first-zero constancy: one common rejection label, and a separate
common initial label for each surviving initial phase fiber. -/
def ClearingCondition {k : ℕ} {Y : Type*} (f : Option (LiveRecord k) → Y)
    (v : ZMod 2) (h a : ℕ) (S : Set (ZMod (k + 1))) : Prop :=
  RejectionConstant f v h a S ∧
    ∀ phase ∈ S, ∀ s₁ < h - a, ∀ s₂ < h - a,
      f (some ⟨v, phase, s₁⟩) = f (some ⟨v, phase, s₂⟩)

/-- The child phase set is selected by the ONE increment actually observed. -/
def incrementChild (k m t : ℕ) (S : Set (ZMod (k + 1))) (b : ZMod 2) :
    Set (ZMod (k + 1)) := {phase | phase ∈ S ∧ allOneIncrement k m t phase = b}

/-- Decreasing remaining-tail recursion. At a source prefix one substitutes
`h=k-t*m`; no tail or target is updated inside the label conditions. -/
def FirstZeroCriterion (k m : ℕ) (hm : 1 ≤ m) {Y : Type*}
    (f : Option (LiveRecord k) → Y) (v : ZMod 2) (t h : ℕ)
    (S : Set (ZMod (k + 1))) : Prop :=
  S = ∅ ∨
    (∃ a, a < m ∧ a < h ∧ ClearingCondition f v h a S) ∨
    (if _recurse : m < h then RejectionConstant f v h m S ∧
      ∀ b, (incrementChild k m t S b).Nonempty →
        FirstZeroCriterion k m hm f v (t + 1) (h - m) (incrementChild k m t S b)
      else False)
termination_by h
decreasing_by omega

/-- Every successful bounded subtree at an actual all-one prefix satisfies
the complete first-zero recursion. The induction decreases the remaining
tail range, and every nonempty increment child is an attained endpoint cell. -/
theorem first_zero_necessity (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (localAlphabet : Bool) {Y : Type*} (f : Option (LiveRecord k) → Y)
    (v : ZMod 2) (h t : ℕ) (balance : h + t * m = k) (positive : 0 < h)
    (u : ZMod 2) (S : Set (ZMod (k + 1))) (nonempty : S.Nonempty)
    (n : ℕ)
    (strategy : D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
      (acquisitionSystem k m localAlphabet (Option (LiveRecord k))) (targetGoal f) n
      (prefixCell k m t h v u S positive nonempty)) :
    FirstZeroCriterion k m hm f v t h S := by
  classical
  induction h using Nat.strong_induction_on generalizing t u S n with
  | h h ih =>
    have present : ∀ phase ∈ S, ∀ s < h,
        (some ⟨v, phase, s⟩,
          some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩) ∈
          (prefixCell k m t h v u S positive nonempty).val := by
      intro phase hp s hs
      exact ⟨phase, hp, s, hs, rfl⟩
    have clearZero :
        (∀ phase₁ ∈ S, ∀ phase₂ ∈ S, ∀ s₁ < h, ∀ s₂ < h,
          f (some ⟨v, phase₁, s₁⟩) = f (some ⟨v, phase₂, s₂⟩)) →
        FirstZeroCriterion k m hm f v t h S := by
      intro constant
      rw [FirstZeroCriterion]
      refine Or.inr (Or.inl ⟨0, by omega, positive, ?_⟩)
      constructor
      · intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂ lower₁ lower₂
        omega
      · simpa only [Nat.sub_zero] using
          (fun phase hp s₁ hs₁ s₂ hs₂ => constant phase hp phase hp s₁ hs₁ s₂ hs₂)
    cases strategy with
    | now atGoal =>
        apply clearZero
        intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
        exact atGoal _ (present phase₁ hp₁ s₁ hs₁) _ (present phase₂ hp₂ s₂ hs₂)
    | @step r _ action continuation =>
        have merged : ∀ phase₁ ∈ S, ∀ phase₂ ∈ S, ∀ s₁ < h, ∀ s₂ < h,
            runBits k action.val
              (some ⟨u, phase₁ + ((t * m : ℕ) : ZMod (k + 1)), s₁ + t * m⟩) =
            runBits k action.val
              (some ⟨u, phase₂ + ((t * m : ℕ) : ZMod (k + 1)), s₂ + t * m⟩) →
            f (some ⟨v, phase₁, s₁⟩) = f (some ⟨v, phase₂, s₂⟩) := by
          intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂ equal
          let current₁ : Option (LiveRecord k) :=
            some ⟨u, phase₁ + ((t * m : ℕ) : ZMod (k + 1)), s₁ + t * m⟩
          let updated := runBits k action.val current₁
          let reply := endpointReading updated
          let parent := prefixCell k m t h v u S positive nonempty
          have member₁ : (some ⟨v, phase₁, s₁⟩, updated) ∈
              replyFiber k m parent action.val reply :=
            ⟨current₁, present phase₁ hp₁ s₁ hs₁, rfl, rfl⟩
          let child : CandidateState k (Option (LiveRecord k)) :=
            ⟨replyFiber k m parent action.val reply, ⟨_, member₁⟩⟩
          exact acquisition_merge_obstruction k m localAlphabet f r child
            (continuation child ⟨reply, rfl⟩) _ _ updated member₁
            ⟨_, present phase₂ hp₂ s₂ hs₂, equal.symm, rfl⟩
        have scannerMono : ∀ (q : ℕ) (word : Fin q → Bool) (maxTrue fuel₁ fuel₂ : ℕ),
            fuel₁ ≤ fuel₂ → fuel₂ ≤ maxTrue →
            runAdmissible maxTrue fuel₁ q word = true →
            runAdmissible maxTrue fuel₂ q word = true := by
          intro q
          induction q with
          | zero => intro word maxTrue fuel₁ fuel₂ lower upper accepted; rfl
          | succ q inductionHypothesis =>
              intro word maxTrue fuel₁ fuel₂ lower upper accepted
              cases head : word 0
              · cases fuel₁ <;> cases fuel₂ <;>
                  simpa only [runAdmissible, head, Bool.false_eq_true, ↓reduceIte]
                  using accepted
              · cases fuel₁ with
                | zero => simp [runAdmissible, head] at accepted
                | succ fuel₁ =>
                    cases fuel₂ with
                    | zero => omega
                    | succ fuel₂ =>
                        simp only [runAdmissible, head, ↓reduceIte] at accepted ⊢
                        exact inductionHypothesis (Fin.tail word) maxTrue fuel₁ fuel₂
                          (by omega) (by omega) accepted
        by_cases legal : DBonacciAdmissible k m action.val
        · have classify : ∀ bits : List Bool,
              bits = List.replicate bits.length true ∨
              ∃ a rest, bits = List.replicate a true ++ false :: rest := by
            intro bits
            induction bits with
            | nil => exact Or.inl rfl
            | cons bit bits inductionHypothesis =>
                cases bit
                · exact Or.inr ⟨0, bits, rfl⟩
                · rcases inductionHypothesis with allOnes | ⟨a, rest, cut⟩
                  · exact Or.inl (by
                      simpa only [List.length_cons, List.replicate_succ] using
                        congrArg (List.cons true) allOnes)
                  · exact Or.inr ⟨a + 1, rest, by simp only [List.replicate_succ,
                      List.cons_append, cut]⟩
          rcases classify (List.ofFn action.val) with allOnes | ⟨a, rest, cut⟩
          · have wordEqual : action.val = allOneBlock m := by
              apply List.ofFn_injective
              change List.ofFn action.val = List.ofFn (fun _ : Fin m => true)
              simpa only [List.length_ofFn, List.ofFn_const] using allOnes
            have execute : ∀ phase s, s < h →
                runBits k action.val
                  (some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩) =
                if s + m < h then
                  some ⟨u + allOneIncrement k m t phase,
                    phase + (((t + 1) * m : ℕ) : ZMod (k + 1)), s + (t + 1) * m⟩
                else none := by
              intro phase s hs
              have literal := (all_one_archive_exact k m hk hm 1 u
                (phase + ((t * m : ℕ) : ZMod (k + 1))) (s + t * m)
                (by omega) (fun _ => 0)).2.2
              have safe : s + t * m + 1 * m < k ↔ s + m < h := by omega
              have shift : phase + ((t * m : ℕ) : ZMod (k + 1)) +
                  ((1 * m : ℕ) : ZMod (k + 1)) =
                  phase + (((t + 1) * m : ℕ) : ZMod (k + 1)) := by push_cast; ring
              have tailShift : s + t * m + 1 * m = s + (t + 1) * m := by ring
              simp only [safe] at literal
              simpa only [wordEqual, allOneOrbit, Function.iterate_one,
                Finset.sum_range_one, allOneIncrement, Nat.zero_mul, Nat.cast_zero,
                add_zero, safe, shift, tailShift] using literal
            by_cases recurse : m < h
            · rw [FirstZeroCriterion]
              apply Or.inr
              apply Or.inr
              rw [dif_pos recurse]
              refine ⟨?_, ?_⟩
              · intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂ lower₁ lower₂
                apply merged phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
                rw [execute _ _ hs₁, execute _ _ hs₂,
                  if_neg (by omega), if_neg (by omega)]
              · intro b childNonempty
                have childPositive : 0 < h - m := by omega
                let child := prefixCell k m (t + 1) (h - m) v (u + b)
                  (incrementChild k m t S b) childPositive childNonempty
                have attained : child ∈
                    (acquisitionSystem k m localAlphabet (Option (LiveRecord k))).successor
                      (state := prefixCell k m t h v u S positive nonempty) action := by
                  refine ⟨some (u + b), ?_⟩
                  ext pair
                  rcases pair with ⟨initial, record⟩
                  constructor
                  · rintro ⟨phase, hp, s, hs, pairEqual⟩
                    have initialEqual := congrArg Prod.fst pairEqual
                    have recordEqual := congrArg Prod.snd pairEqual
                    dsimp at initialEqual recordEqual
                    subst initial record
                    refine ⟨some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)),
                      s + t * m⟩, present phase hp.1 s (by omega), ?_, rfl⟩
                    rw [execute _ _ (by omega), if_pos (by omega), hp.2]
                  · rintro ⟨current, origin, updated, observed⟩
                    obtain ⟨phase, hp, s, hs, equal⟩ := origin
                    have initialEqual := congrArg Prod.fst equal
                    have currentEqual := congrArg Prod.snd equal
                    dsimp at initialEqual currentEqual
                    subst initial current
                    rw [execute _ _ hs] at updated
                    by_cases safe : s + m < h
                    · rw [if_pos safe] at updated
                      cases updated
                      have increment : allOneIncrement k m t phase = b := by
                        simp only [endpointReading, Option.some.injEq] at observed
                        exact add_left_cancel observed
                      exact ⟨phase, ⟨hp, increment⟩, s, by omega, by rw [increment]⟩
                    · rw [if_neg safe] at updated
                      cases updated
                      simp [endpointReading] at observed
                have childBalance : h - m + (t + 1) * m = k := by
                  rw [Nat.add_mul, Nat.one_mul]
                  omega
                exact ih (h - m) (by omega) (t + 1) childBalance childPositive
                  (u + b) (incrementChild k m t S b) childNonempty r
                  (continuation child attained)
            · apply clearZero
              intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
              apply merged phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
              rw [execute _ _ hs₁, execute _ _ hs₂,
                if_neg (by omega), if_neg (by omega)]
          · have lengthCut := congrArg List.length cut
            have am : a < m := by simp only [List.length_ofFn, List.length_append,
              List.length_replicate, List.length_cons] at lengthCut; omega
            have execute : ∀ phase s, s < h →
                runBits k action.val
                  (some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩) =
                if s + a < h then
                  some ⟨u + wordIncrement k (phase + ((t * m : ℕ) : ZMod (k + 1))) action.val,
                    phase + ((t * m : ℕ) : ZMod (k + 1)) + (m : ℕ), tailAfter 0 action.val⟩
                else none := by
              intro phase s hs
              have safe : s + t * m + a < k ↔ s + a < h := by omega
              simpa only [safe] using first_zero_block_exact k hk m a action.val rest cut
                legal u (phase + ((t * m : ℕ) : ZMod (k + 1))) (s + t * m) (by omega)
            by_cases ah : a < h
            · rw [FirstZeroCriterion]
              refine Or.inr (Or.inl ⟨a, am, ah, ?_⟩)
              constructor
              · intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂ lower₁ lower₂
                apply merged phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
                rw [execute _ _ hs₁, execute _ _ hs₂,
                  if_neg (by omega), if_neg (by omega)]
              · intro phase hp s₁ hs₁ s₂ hs₂
                apply merged phase hp phase hp s₁ (by omega) s₂ (by omega)
                rw [execute _ _ (by omega), execute _ _ (by omega),
                  if_pos (by omega), if_pos (by omega)]
            · apply clearZero
              intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
              apply merged phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
              rw [execute _ _ hs₁, execute _ _ hs₂,
                if_neg (by omega), if_neg (by omega)]
        · have rejects : ∀ phase s, s < h →
              runBits k action.val
                (some ⟨u, phase + ((t * m : ℕ) : ZMod (k + 1)), s + t * m⟩) = none := by
            intro phase s hs
            have forbidden : runAdmissible (k - 1) (k - 1) m action.val ≠ true := by
              obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
              simpa [hd, DBonacciAdmissible] using legal
            have noScan : runAdmissible (k - 1) (k - 1 - (s + t * m)) m action.val ≠ true :=
              fun accepted => forbidden (scannerMono m action.val (k - 1)
                (k - 1 - (s + t * m)) (k - 1) (by omega) le_rfl accepted)
            have model := (literal_block_execution k hk m action.val u
              (phase + ((t * m : ℕ) : ZMod (k + 1))) (s + t * m) (by omega)).1
            simpa only [Bool.eq_false_iff.mpr noScan, Bool.false_eq_true, ↓reduceIte] using model
          apply clearZero
          intro phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
          apply merged phase₁ hp₁ phase₂ hp₂ s₁ hs₁ s₂ hs₂
          rw [rejects _ _ hs₁, rejects _ _ hs₂]

#print axioms first_zero_necessity

/-- The source's safe phase cost, including zero-action singleton phases. -/
def phaseCost (k m : ℕ) : ℕ :=
  if (k + 1) / Nat.gcd m (k + 1) = 1 then 0
  else if 2 ≤ m then (k + 1) / Nat.gcd m (k + 1) - 1
  else if Odd (k + 1) then 2 * (k + 1) else 2 * (k + 1) + 1

/-- Literal fixed block protocols give a total archive decoder on every
attained live phase fiber. Initial output is the free baseline; no internal
bit, unknown initial clock, or decidable target equality is supplied. -/
theorem safe_phase_protocol (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (localAlphabet : Bool) :
    ∃ actions : List (AllowedBlock k m localAlphabet),
      actions.length = phaseCost k m ∧
      ∀ (v₁ v₂ : ZMod 2) (phase₁ phase₂ : ZMod (k + 1)) (s₁ s₂ : ℕ),
        s₁ < k → s₂ < k →
        Nat.gcd m (k + 1) ∣ phase₁.val → Nat.gcd m (k + 1) ∣ phase₂.val →
        v₁ = v₂ →
        fixedBlockArchive actions (some ⟨v₁, phase₁, s₁⟩) =
          fixedBlockArchive actions (some ⟨v₂, phase₂, s₂⟩) → phase₁ = phase₂ := by
  classical
  let step := fun (action : AllowedBlock k m localAlphabet) => runBits k action.val
  have prefixReading : ∀ (left right : List (AllowedBlock k m localAlphabet)) q₁ q₂,
      endpointReading q₁ = endpointReading q₂ →
      fixedBlockArchive (left ++ right) q₁ = fixedBlockArchive (left ++ right) q₂ →
      endpointReading (runWord step left q₁) = endpointReading (runWord step left q₂) := by
    intro left
    induction left with
    | nil => intro right q₁ q₂ baseline archive; exact baseline
    | cons action left ih =>
        intro right q₁ q₂ baseline archive
        simp only [List.cons_append, fixedBlockArchive, List.cons.injEq] at archive
        exact ih right _ _ archive.1 archive.2
  by_cases singleton : (k + 1) / Nat.gcd m (k + 1) = 1
  · refine ⟨[], by simp [phaseCost, singleton], ?_⟩
    intro v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ baseline archive
    have gEq : Nat.gcd m (k + 1) = k + 1 := by
      have product := Nat.div_mul_cancel (Nat.gcd_dvd_right m (k + 1))
      rw [singleton, one_mul] at product
      exact product
    have z₁ : phase₁.val = 0 := Nat.eq_zero_of_dvd_of_lt hp₁
      (by rw [gEq]; exact ZMod.val_lt phase₁)
    have z₂ : phase₂.val = 0 := Nat.eq_zero_of_dvd_of_lt hp₂
      (by rw [gEq]; exact ZMod.val_lt phase₂)
    exact ZMod.val_injective (k + 1) (z₁.trans z₂.symm)
  by_cases many : 2 ≤ m
  · let action : AllowedBlock k m localAlphabet :=
      ⟨isolatedProbe m (phaseProbeOffset k m), fun _ =>
        (safe_block_phase_recovery k m hk many 0 0 0 0 0 0 (by omega) (by omega)
          (by simp) (by simp)).1⟩
    let n := (k + 1) / Nat.gcd m (k + 1) - 1
    refine ⟨List.replicate n action, by simp [phaseCost, singleton, many, n], ?_⟩
    intro v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ baseline archive
    apply (safe_block_phase_recovery k m hk many v₁ v₂ phase₁ phase₂ s₁ s₂
      hs₁ hs₂ hp₁ hp₂).2.2
    intro r hr
    have runReplicate : ∀ r q,
        runWord step (List.replicate r action) q = (runBits k action.val)^[r] q := by
      intro r
      induction r with
      | zero => intro q; rfl
      | succ r ih =>
          intro q
          simpa only [List.replicate_succ, runWord, step, Function.iterate_succ_apply]
            using ih (runBits k action.val q)
    have split : List.replicate n action =
        List.replicate r action ++ List.replicate (n - r) action := by
      rw [List.replicate_append_replicate, Nat.add_sub_of_le hr]
    have same := prefixReading (List.replicate r action) (List.replicate (n-r) action)
      (some ⟨v₁, phase₁, s₁⟩) (some ⟨v₂, phase₂, s₂⟩)
      (by simp only [endpointReading, baseline]) (by rw [← split]; exact archive)
    simpa only [runReplicate] using same
  · have width : m = 1 := by omega
    subst m
    have bitLegal : ∀ bit : Bool, DBonacciAdmissible k 1 (fun _ => bit) := by
      intro bit
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [hd]
      exact runAdmissible_eq_true_of_length_le d d 1 (fun _ => bit) (by omega) le_rfl
    let zero : AllowedBlock k 1 localAlphabet := ⟨fun _ => false, fun _ => bitLegal false⟩
    let one : AllowedBlock k 1 localAlphabet := ⟨fun _ => true, fun _ => bitLegal true⟩
    let pairs := fun r => (List.replicate r [zero, one]).flatten
    have pairRun : ∀ r q, runWord step (pairs r) q = alternatingBitOrbit k r q := by
      intro r
      induction r with
      | zero => intro q; rfl
      | succ r ih =>
          intro q
          change runWord step (([zero, one] :: List.replicate r [zero, one]).flatten) q = _
          simp only [List.flatten_cons, List.cons_append, List.nil_append, runWord]
          rw [ih]
          rfl
    have pairSplit : ∀ r n, r ≤ n → pairs n = pairs r ++ pairs (n-r) := by
      intro r n hr
      dsimp [pairs]
      rw [← List.flatten_append, List.replicate_append_replicate, Nat.add_sub_of_le hr]
    have appendRun : ∀ (left right : List (AllowedBlock k 1 localAlphabet)) q,
        runWord step (left ++ right) q = runWord step right (runWord step left q) := by
      intro left
      induction left with
      | nil => intro right q; rfl
      | cons action left ih => intro right q; exact ih right (step action q)
    have pairLength : ∀ r, (pairs r).length = 2*r := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih =>
          change (([zero,one] :: List.replicate r [zero,one]).flatten).length = _
          simp only [List.flatten_cons, List.length_append]
          change 2 + (pairs r).length = _
          rw [ih]; omega
    by_cases oddT : Odd (k + 1)
    · refine ⟨pairs (k+1), by simp [phaseCost, singleton, oddT, pairLength, show k ≠ 0 by omega], ?_⟩
      intro v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ baseline archive
      apply (odd_single_bit_phase_recovery k hk oddT v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂).2
      intro r hr
      have same := prefixReading (pairs r) (pairs (k+1-r))
        (some ⟨v₁,phase₁,s₁⟩) (some ⟨v₂,phase₂,s₂⟩)
        (by simp only [endpointReading, baseline])
        (by rw [← pairSplit r (k+1) hr]; exact archive)
      simpa only [pairRun] using same
    · have evenT : Even (k+1) := Nat.not_odd_iff_even.mp oddT
      let half := (k+1)/2
      have lengthT : 2*half = k+1 := by
        obtain ⟨d, hd⟩ := evenT
        dsimp [half]
        omega
      let actions := pairs half ++ zero :: pairs half
      refine ⟨actions, ?_, ?_⟩
      · dsimp [actions]
        simp only [List.length_append, List.length_cons, pairLength]
        simp only [phaseCost, singleton, ↓reduceIte, show ¬ 2 ≤ 1 by omega, oddT]
        omega
      · intro v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ baseline archive
        apply (even_single_bit_phase_recovery k hk evenT v₁ v₂ phase₁ phase₂ s₁ s₂ hs₁ hs₂).2
        · intro r hr
          have split : actions = pairs r ++ (pairs (half-r) ++ zero :: pairs half) := by
            dsimp [actions]
            rw [pairSplit r half hr, List.append_assoc]
          have same := prefixReading (pairs r) (pairs (half-r) ++ zero :: pairs half)
            (some ⟨v₁,phase₁,s₁⟩) (some ⟨v₂,phase₂,s₂⟩)
            (by simp only [endpointReading, baseline]) (by rw [← split]; exact archive)
          simpa only [pairRun] using same
        · intro r hr
          have split : actions = (pairs half ++ [zero] ++ pairs r) ++ pairs (half-r) := by
            dsimp [actions]
            rw [pairSplit r half hr]
            simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
          have same := prefixReading (pairs half ++ [zero] ++ pairs r) (pairs (half-r))
            (some ⟨v₁,phase₁,s₁⟩) (some ⟨v₂,phase₂,s₂⟩)
            (by simp only [endpointReading, baseline]) (by rw [← split]; exact archive)
          simpa only [appendRun, pairRun, runWord, step, zero, evenSingleBitOrbit, half] using same

#print axioms safe_phase_protocol


/-- Remaining successful all-one steps, one clearing or rejection block, and
then the literal safe phase protocol. -/
def prefixBudget (k m h : ℕ) : ℕ := (h - 1) / m + 1 + phaseCost k m

/-- Complete decreasing-tail sufficiency on the actual prefix cell. Every
continuation is constructed only for an attained reply. A future rejection
returns a common ORIGINAL label, whereas impossible cells need no label choice. -/
theorem first_zero_sufficiency (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (localAlphabet : Bool) {Y : Type*} (f : Option (LiveRecord k) → Y)
    (v : ZMod 2) (h t : ℕ) (balance : h + t * m = k) (positive : 0 < h)
    (u : ZMod 2) (S : Set (ZMod (k + 1))) (nonempty : S.Nonempty)
    (phases : ∀ phase ∈ S, Nat.gcd m (k + 1) ∣ phase.val)
    (criterion : FirstZeroCriterion k m hm f v t h S) :
    D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy
      (acquisitionSystem k m localAlphabet (Option (LiveRecord k))) (targetGoal f)
      (prefixBudget k m h) (prefixCell k m t h v u S positive nonempty) := by
  classical
  let system := acquisitionSystem k m localAlphabet (Option (LiveRecord k))
  let goal := targetGoal (k := k) f
  have enlarge : ∀ (n r : ℕ) (cell : CandidateState k (Option (LiveRecord k))), n ≤ r →
      D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy system goal n cell →
      D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.BoundedReachStrategy system goal r cell := by
    intro n r cell lower strategy
    apply (D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.finite_horizon_reachability
      system goal r cell).mp
    have atN := (D5.S3.ConceptDynamics.Control.FiniteHorizonReachability.finite_horizon_reachability
      system goal n cell).mpr strategy
    induction r, lower using Nat.le_induction with
    | base => exact atN
    | succ r hr ih => exact Or.inl ih
  obtain ⟨protocol, protocolLength, decode⟩ := safe_phase_protocol k m hk hm localAlphabet
  have shiftedPhase : ∀ phase, Nat.gcd m (k+1) ∣ phase.val → ∀ r,
      Nat.gcd m (k+1) ∣ (phase + ((r*m : ℕ) : ZMod (k+1))).val := by
    intro phase hp r
    rw [← ZMod.natCast_zmod_val phase, ← Nat.cast_add, ZMod.val_natCast]
    apply (Nat.dvd_mod_iff (Nat.gcd_dvd_right m (k+1))).mpr
    exact dvd_add hp (dvd_mul_of_dvd_right (Nat.gcd_dvd_left m (k+1)) r)
  induction h using Nat.strong_induction_on generalizing t u S with
  | h h ih =>
    let parent := prefixCell k m t h v u S positive nonempty
    have present : ∀ phase ∈ S, ∀ s < h,
        (some ⟨v,phase,s⟩,some ⟨u,phase+((t*m : ℕ) : ZMod (k+1)),s+t*m⟩) ∈ parent.val := by
      intro phase hp s hs; exact ⟨phase,hp,s,hs,rfl⟩
    rw [FirstZeroCriterion] at criterion
    rcases criterion with empty | ⟨a, am, ah, clear⟩ | recurse
    · exact False.elim (by simpa [empty] using nonempty)
    · let bits := List.replicate a true ++ false :: List.replicate (m-a-1) false
      have length : bits.length = m := by simp [bits]; omega
      let word : Fin m → Bool := fun i => bits[(Fin.cast length.symm i).val]
      have cut : List.ofFn word = List.replicate a true ++ false :: List.replicate (m-a-1) false := by
        exact (List.ofFn_congr length (fun i : Fin bits.length => bits[i.val])).symm.trans List.ofFn_getElem
      have wordFalse : ∀ i : Fin m, a ≤ i.val → word i = false := by
        intro i hi
        dsimp [word, bits]
        rw [List.getElem_append_right (as := List.replicate a true) (by simpa only [List.length_replicate] using hi)]
        simp only [List.length_replicate]
        by_cases equal : i.val-a = 0
        · simp [equal]
        · have more : 0 < i.val-a := by omega
          obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero equal
          simp [hr]
      have legal : DBonacciAdmissible k m word := by
        by_cases enough : k ≤ m
        · apply (D5.S1.Words.ClosedRunStarts.closed_word_run_start_equivalence m k (by omega) enough word).1.mpr
          intro j forbidden
          let i : Fin m := ⟨j+k-1, by have size := forbidden.1; omega⟩
          have yes := forbidden.2 i (by dsimp [i]; omega) (by dsimp [i]; omega)
          rw [wordFalse i (by dsimp [i]; omega)] at yes
          cases yes
        · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [hd]
          exact runAdmissible_eq_true_of_length_le d d m word (by omega) le_rfl
      let action : AllowedBlock k m localAlphabet := ⟨word, fun _ => legal⟩
      have execute : ∀ phase s, s < h → runBits k word
          (some ⟨u,phase+((t*m : ℕ) : ZMod (k+1)),s+t*m⟩) =
          if s+a < h then
            some ⟨u+wordIncrement k (phase+((t*m : ℕ) : ZMod (k+1))) word,
              phase+(((t+1)*m : ℕ) : ZMod (k+1)),tailAfter 0 word⟩ else none := by
        intro phase s hs
        have shift : phase+((t*m : ℕ) : ZMod (k+1))+(m : ℕ) =
            phase+(((t+1)*m : ℕ) : ZMod (k+1)) := by push_cast; ring
        simpa only [show s+t*m+a < k ↔ s+a < h by omega, shift]
          using first_zero_block_exact k hk m a word (List.replicate (m-a-1) false)
            cut legal u (phase+((t*m : ℕ) : ZMod (k+1))) (s+t*m) (by omega)
      have safeTail : tailAfter 0 word < k := by
        have scan : runAdmissible (k-1) (k-1-0) m word = true := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          simpa [hd, DBonacciAdmissible] using legal
        exact (literal_block_execution k hk m word 0 0 0 (by omega)).2 scan
      have budget : prefixBudget k m h = ((h-1)/m + phaseCost k m) + 1 := by
        unfold prefixBudget; omega
      rw [budget]
      refine .step action ?_
      intro child attained
      obtain ⟨reply, fiber⟩ := attained
      have origins : ∀ pair ∈ child.val, ∃ phase ∈ S, ∃ s < h,
          pair.1 = some ⟨v,phase,s⟩ ∧
          pair.2 = (if s+a < h then
            some ⟨u+wordIncrement k (phase+((t*m : ℕ) : ZMod (k+1))) word,
              phase+(((t+1)*m : ℕ) : ZMod (k+1)),tailAfter 0 word⟩ else none) ∧
          endpointReading pair.2 = reply := by
        intro pair hp
        rw [fiber] at hp
        obtain ⟨current,origin,updated,observed⟩ := hp
        obtain ⟨phase,hphase,s,hs,equal⟩ := origin
        have fst := congrArg Prod.fst equal
        have snd := congrArg Prod.snd equal
        dsimp at fst snd
        subst current
        exact ⟨phase,hphase,s,hs,fst,updated.symm.trans (execute phase s hs),observed⟩
      cases reply with
      | none =>
          refine .now ?_
          intro first hf second hs
          obtain ⟨phase₁,hp₁,s₁,ht₁,initial₁,current₁,observed₁⟩ := origins first hf
          obtain ⟨phase₂,hp₂,s₂,ht₂,initial₂,current₂,observed₂⟩ := origins second hs
          have reject₁ : ¬ s₁+a < h := by
            intro safe; rw [current₁,if_pos safe] at observed₁; cases observed₁
          have reject₂ : ¬ s₂+a < h := by
            intro safe; rw [current₂,if_pos safe] at observed₂; cases observed₂
          rw [initial₁,initial₂]
          exact clear.1 phase₁ hp₁ phase₂ hp₂ s₁ ht₁ s₂ ht₂ (by omega) (by omega)
      | some value =>
          apply enlarge (phaseCost k m) ((h-1)/m + phaseCost k m) child (Nat.le_add_left _ _)
          have separates : ∀ first ∈ child.val, ∀ second ∈ child.val,
              fixedBlockArchive protocol first.2 = fixedBlockArchive protocol second.2 →
              f first.1 = f second.1 := by
            intro first hf second hs archive
            obtain ⟨phase₁,hp₁,s₁,ht₁,initial₁,current₁,observed₁⟩ := origins first hf
            obtain ⟨phase₂,hp₂,s₂,ht₂,initial₂,current₂,observed₂⟩ := origins second hs
            have survive₁ : s₁+a < h := by
              by_contra notSafe; rw [current₁,if_neg notSafe] at observed₁; cases observed₁
            have survive₂ : s₂+a < h := by
              by_contra notSafe; rw [current₂,if_neg notSafe] at observed₂; cases observed₂
            rw [if_pos survive₁] at current₁
            rw [if_pos survive₂] at current₂
            have baseline : u+wordIncrement k (phase₁+((t*m : ℕ) : ZMod (k+1))) word =
                u+wordIncrement k (phase₂+((t*m : ℕ) : ZMod (k+1))) word := by
              rw [current₁] at observed₁
              rw [current₂] at observed₂
              exact Option.some.inj (observed₁.trans observed₂.symm)
            rw [current₁,current₂] at archive
            have shifted := decode _ _ _ _ _ _ safeTail safeTail
              (shiftedPhase phase₁ (phases phase₁ hp₁) (t+1))
              (shiftedPhase phase₂ (phases phase₂ hp₂) (t+1)) baseline archive
            have same : phase₁ = phase₂ := add_right_cancel shifted
            rw [initial₁,initial₂,← same]
            exact clear.2 phase₁ hp₁ s₁ (by omega) s₂ (by omega)
          have built := archive_controller_synthesis k m localAlphabet f protocol child separates
          rw [protocolLength] at built
          exact (native_controller_exact k m localAlphabet f (phaseCost k m) child).mp built
    · by_cases smaller : m < h
      · rw [dif_pos smaller] at recurse
        let action : AllowedBlock k m localAlphabet := ⟨allOneBlock m, fun _ => by
          obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [hd]
          exact runAdmissible_eq_true_of_length_le d d m (allOneBlock m) (by omega) le_rfl⟩
        have execute : ∀ phase s, s < h → runBits k action.val
            (some ⟨u,phase+((t*m : ℕ) : ZMod (k+1)),s+t*m⟩) =
            if s+m < h then some ⟨u+allOneIncrement k m t phase,
              phase+(((t+1)*m : ℕ) : ZMod (k+1)),s+(t+1)*m⟩ else none := by
          intro phase s hs
          have literal := (all_one_archive_exact k m hk hm 1 u
            (phase+((t*m : ℕ) : ZMod (k+1))) (s+t*m) (by omega) (fun _ => 0)).2.2
          have shift : phase+((t*m : ℕ) : ZMod (k+1))+((1*m : ℕ) : ZMod (k+1)) =
              phase+(((t+1)*m : ℕ) : ZMod (k+1)) := by push_cast; ring
          have tailShift : s+t*m+1*m = s+(t+1)*m := by ring
          simpa only [action, allOneOrbit, Function.iterate_one, Finset.sum_range_one,
            allOneIncrement, Nat.zero_mul, Nat.cast_zero, add_zero,
            show s+t*m+1*m < k ↔ s+m < h by omega, shift,tailShift,
            show s+(t+1)*m < k ↔ s+m < h by rw [Nat.add_mul,Nat.one_mul]; omega] using literal
        have budget : prefixBudget k m h = prefixBudget k m (h-m) + 1 := by
          have divide := Nat.div_eq_sub_div (by omega : 0 < m) (by omega : m ≤ h-1)
          have sub : h-1-m = h-m-1 := by omega
          unfold prefixBudget
          rw [divide,sub]
          omega
        rw [budget]
        refine .step action ?_
        intro child attained
        obtain ⟨reply,fiber⟩ := attained
        cases reply with
        | none =>
            refine .now ?_
            intro first hf second hs
            rw [fiber] at hf hs
            obtain ⟨cur₁,⟨phase₁,hp₁,s₁,ht₁,eq₁⟩,update₁,read₁⟩ := hf
            obtain ⟨cur₂,⟨phase₂,hp₂,s₂,ht₂,eq₂⟩,update₂,read₂⟩ := hs
            have fst₁ := congrArg Prod.fst eq₁
            have snd₁ := congrArg Prod.snd eq₁
            have fst₂ := congrArg Prod.fst eq₂
            have snd₂ := congrArg Prod.snd eq₂
            dsimp at fst₁ snd₁ fst₂ snd₂
            subst cur₁ cur₂
            have reject₁ : ¬ s₁+m < h := by
              intro safe; rw [execute _ _ ht₁,if_pos safe] at update₁
              rw [← update₁] at read₁; cases read₁
            have reject₂ : ¬ s₂+m < h := by
              intro safe; rw [execute _ _ ht₂,if_pos safe] at update₂
              rw [← update₂] at read₂; cases read₂
            rw [fst₁,fst₂]
            exact recurse.1 phase₁ hp₁ phase₂ hp₂ s₁ ht₁ s₂ ht₂ (by omega) (by omega)
        | some value =>
            let b := value-u
            have childPositive : 0 < h-m := by omega
            have childPhases : (incrementChild k m t S b).Nonempty := by
              obtain ⟨pair,hp⟩ := child.property
              rw [fiber] at hp
              obtain ⟨current,⟨phase,hphase,s,hs,equal⟩,updated,observed⟩ := hp
              have currentEq := congrArg Prod.snd equal
              dsimp at currentEq
              subst current
              rw [execute _ _ hs] at updated
              by_cases safe : s+m < h
              · rw [if_pos safe] at updated
                rw [← updated] at observed
                have inc : allOneIncrement k m t phase = b := by
                  simp only [endpointReading,Option.some.injEq] at observed
                  dsimp [b]; linear_combination observed
                exact ⟨phase,hphase,inc⟩
              · rw [if_neg safe] at updated
                rw [← updated] at observed
                cases observed
            let canonical := prefixCell k m (t+1) (h-m) v value
              (incrementChild k m t S b) childPositive childPhases
            have equalCell : child = canonical := by
              apply Subtype.ext
              rw [fiber]
              ext pair
              constructor
              · rintro ⟨current,⟨phase,hphase,s,hs,equal⟩,updated,observed⟩
                have initialEq := congrArg Prod.fst equal
                have currentEq := congrArg Prod.snd equal
                dsimp at initialEq currentEq
                subst current
                rw [execute _ _ hs] at updated
                by_cases safe : s+m < h
                · rw [if_pos safe] at updated
                  rw [← updated] at observed
                  have inc : allOneIncrement k m t phase = b := by
                    simp only [endpointReading,Option.some.injEq] at observed
                    dsimp [b]; linear_combination observed
                  refine ⟨phase,⟨hphase,inc⟩,s,by omega,?_⟩
                  apply Prod.ext initialEq
                  rw [← updated]
                  congr 2
                  dsimp [b] at inc
                  linear_combination inc
                · rw [if_neg safe] at updated
                  rw [← updated] at observed
                  cases observed
              · rintro ⟨phase,hphase,s,hs,equal⟩
                have initialEq := congrArg Prod.fst equal
                have currentEq := congrArg Prod.snd equal
                dsimp at initialEq currentEq
                refine ⟨some ⟨u,phase+((t*m : ℕ) : ZMod (k+1)),s+t*m⟩,?_,?_,?_⟩
                · rw [initialEq]; exact present phase hphase.1 s (by omega)
                · rw [execute _ _ (by omega),if_pos (by omega),hphase.2]
                  dsimp [b]
                  rw [add_sub_cancel]
                  exact currentEq.symm
                · rw [currentEq]; rfl
            rw [equalCell]
            apply ih (h-m) (by omega) (t+1) (by rw [Nat.add_mul,Nat.one_mul]; omega)
              childPositive value (incrementChild k m t S b) childPhases
              (fun phase hp => phases phase hp.1) (recurse.2 b childPhases)
      · rw [dif_neg smaller] at recurse
        exact False.elim recurse

#print axioms first_zero_sufficiency



end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstZeroRecursion
