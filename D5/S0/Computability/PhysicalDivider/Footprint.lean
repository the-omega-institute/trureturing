/- GID: D5/S0/Computability/PhysicalDivider/Footprint
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Persistent physical footprint includes initial cells and all visited and erased cells. -/

import D5.S0.Computability.PhysicalDivider.CallExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

/-- Inclusion of charged intervals does not depend on the cells still being nonblank. -/
def Retains (earlier later : ActiveTape → Extent) : Prop :=
  ∀ k, (later k).low ≤ (earlier k).low ∧ (earlier k).high ≤ (later k).high

/-- The sign bit and the binary expansion of the biased absolute coordinate. -/
def signedHeadDescription (z : ℤ) : List Bool :=
  decide (z < 0) :: Lax51Proofs.RamToTM.fixedBits (z.natAbs + 1).size (z.natAbs + 1)

/-- The observer follows the very same physical run. At every prefix its head is
the actual head; its interval contains the current support and every earlier
charged interval, even after writes of blank or later head movement. -/
theorem persistent_prefix_footprint (initial : LocatedCfg) (charged : ActiveTape → Extent)
    (hhead : ∀ k, (charged k).head = initial.2 k)
    (hwithin : ∀ k, Within (initial.1.tapes k) (charged k))
    (n : ℕ) (final : LocatedCfg)
    (hrun : ((fun o : Option LocatedCfg => o.bind locatedStep)^[n]) (some initial) = some final) :
    (∀ k, (prefixCharge initial charged n k).head = final.2 k ∧
      Within (final.1.tapes k) (prefixCharge initial charged n k)) ∧
    (∀ j ≤ n, Retains (prefixCharge initial charged j) (prefixCharge initial charged n)) ∧
    (∀ j ≤ n, ∃ c,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[j]) (some initial) = some c ∧
      ∀ k, Within (c.1.tapes k)
        ⟨c.2 k, (prefixCharge initial charged n k).low,
          (prefixCharge initial charged n k).high⟩) ∧
    (∀ k, extentCost (prefixCharge initial charged n k) =
      ((prefixCharge initial charged n k).high -
        (prefixCharge initial charged n k).low + 1).toNat +
        (signedHeadDescription (final.2 k)).length) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  have preserve (c d : LocatedCfg) (hs : locatedStep c = some d)
      (e : ActiveTape → Extent) (he : ∀ k, (e k).head = c.2 k)
      (hw : ∀ k, Within (c.1.tapes k) (e k)) :
      ∀ k, Within (d.1.tapes k)
        ⟨d.2 k, min (e k).low (d.2 k), max (e k).high (d.2 k)⟩ := by
    unfold locatedStep at hs
    cases hi : instruction c.1.control with
    | none => simp [hi] at hs
    | some action =>
      simp only [hi, Option.map_some, Option.some.injEq] at hs
      subst d
      intro k
      rcases hw k with ⟨hl, hh, ht⟩
      rw [he k] at hl hh ht
      cases action with
      | read t next =>
        dsimp only [executeInstruction, advanceHeads, Within]
        refine ⟨by omega, by omega, ?_⟩
        intro i hi
        have := ht i hi
        constructor <;> omega
      | write t bit next =>
        dsimp only [executeInstruction, advanceHeads, Within]
        refine ⟨by omega, by omega, ?_⟩
        intro i hi
        by_cases hk : k = t
        · subst k
          simp only [Function.update_self] at hi
          by_cases hz : i = 0
          · subst i; constructor <;> omega
          · rw [Tape.write_nth, if_neg hz] at hi
            have := ht i hi
            constructor <;> omega
        · rw [Function.update_of_ne hk] at hi
          have := ht i hi
          constructor <;> omega
      | move t dir next =>
        cases dir <;> dsimp only [executeInstruction, advanceHeads, Within]
        all_goals
          by_cases hk : k = t
          · subst k
            simp only [Function.update_self]
            refine ⟨by omega, by omega, ?_⟩
            intro i hi
            first
            | rw [Tape.move_left_nth] at hi
              have := ht (i - 1) hi
              constructor <;> omega
            | rw [Tape.move_right_nth] at hi
              have := ht (i + 1) hi
              constructor <;> omega
          · simp only [Function.update_of_ne hk]
            refine ⟨by omega, by omega, ?_⟩
            intro i hi
            have := ht i hi
            constructor <;> omega
  have inv : ∀ n c, (run^[n]) (some initial) = some c →
      (∀ k, (prefixCharge initial charged n k).head = c.2 k ∧
        Within (c.1.tapes k) (prefixCharge initial charged n k)) ∧
      ∀ j ≤ n, Retains (prefixCharge initial charged j) (prefixCharge initial charged n) := by
    intro n
    induction n with
    | zero =>
      intro c hc
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hc
      subst c
      refine ⟨fun k => ⟨hhead k, hwithin k⟩, ?_⟩
      intro j hj
      have : j = 0 := by omega
      subst j
      intro k; exact ⟨le_rfl, le_rfl⟩
    | succ n ih =>
      intro c hc
      rw [Function.iterate_succ_apply'] at hc
      cases hp : (run^[n]) (some initial) with
      | none => simp [hp, run] at hc
      | some p =>
        rw [hp] at hc
        obtain ⟨hb, hm⟩ := ih p hp
        have hs : locatedStep p = some c := hc
        have hc' : (run^[n+1]) (some initial) = some c := by
          rw [Function.iterate_succ_apply', hp]; exact hc
        have eqcharge : prefixCharge initial charged (n+1) = fun k =>
            ⟨c.2 k, min (prefixCharge initial charged n k).low (c.2 k),
              max (prefixCharge initial charged n k).high (c.2 k)⟩ := by
          simp only [prefixCharge, show
            ((fun o : Option LocatedCfg => o.bind locatedStep)^[n+1]) (some initial) = some c
              from hc', Option.getD_some]
        constructor
        · rw [eqcharge]
          exact fun k => ⟨rfl, preserve p c hs _ (fun k => (hb k).1) (fun k => (hb k).2) k⟩
        · intro j hj k
          by_cases hjn : j ≤ n
          · have h := hm j hjn k
            rw [eqcharge]
            exact ⟨le_trans (min_le_left _ _) h.1, le_trans h.2 (le_max_left _ _)⟩
          · have : j = n + 1 := by omega
            subst j; exact ⟨le_rfl, le_rfl⟩
  obtain ⟨hb, hm⟩ := inv n final hrun
  refine ⟨hb, hm, ?_, ?_⟩
  · intro j hj
    cases hc : (run^[j]) (some initial) with
    | none =>
      rw [show n = (n-j)+j by omega, Function.iterate_add_apply, hc,
        Function.iterate_fixed (show run none = none from rfl)] at hrun
      contradiction
    | some c =>
      refine ⟨c, rfl, ?_⟩
      intro k
      have hk := (inv j c hc).1 k
      have hkeep := hm j hj k
      rcases hk.2 with ⟨hl, hh, ht⟩
      rw [hk.1] at hl hh ht
      refine ⟨by dsimp; omega, by dsimp; omega, ?_⟩
      intro i hi
      have := ht i hi
      constructor <;> dsimp <;> omega
  · intro k
    simp only [extentCost, (hb k).1, signedHeadDescription, List.length_cons,
      Lax51Proofs.RamToTM.fixedBits_length]
    omega

end D5.S0.Computability.PhysicalDivider
