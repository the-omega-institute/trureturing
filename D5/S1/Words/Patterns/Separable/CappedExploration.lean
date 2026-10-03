/- GID: D5/S1/Words/Patterns/Separable/CappedExploration
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/CappedExploration
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual capped exploration gives disjoint restricted history fibers. -/

import D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
import Mathlib.Data.Fintype.BigOperators

/-!
The algorithm acts on actual avoiding permutations and recovers actual factors.
All parameters are arbitrary natural numbers, including zero. A selected history
fiber is restricted by the deterministic classifier; no full-leaf count is
assigned to a restricted fiber. These are unbounded symbolic constructions.
-/

namespace D5.S1.Words.Patterns.Separable.CappedExploration

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.EndpointHistoryKernel

structure Recovered {state n} (π : Carrier state n) where
  sign : Bool
  left : ℕ
  right : ℕ
  left_pos : 0 < left
  right_pos : 0 < right
  sum_eq : left + right = n
  compatible : state = none ∨ state = some (!sign)
  first : Indecomposable sign left
  last : Avoider right
  reconstruct : sum_eq ▸ (⟨blockSum sign first.val.val last.val,
    (avoids_block_sum_iff sign _ _).mpr ⟨first.val.property, last.property⟩⟩ :
      Avoider (left + right)) = π.val
  minimum : MinimumCut sign π.val.val left
  unique : ∀ other cut, 0 < cut → cut < n → MinimumCut other π.val.val cut →
    other = sign ∧ cut = left
  factor_unique : ∀ (α : Indecomposable sign left) (β : Avoider right),
    blockSum sign α.val.val β.val = blockSum sign first.val.val last.val →
      α = first ∧ β = last

noncomputable def recover {state n} (π : Carrier state n) (hn : 2 ≤ n) :
    Recovered π := by
  classical
  apply Classical.choice
  have incompatible (sign : Bool) (available : HasProperCut sign π.val.val) :
      ¬HasProperCut (!sign) π.val.val :=
    ((endpoint_history_count_kernel (.stop none n)).2.2.2.2.2.2.2.2
      sign hn π.val).mpr available
  have existsCut : ∃ sign, HasProperCut sign π.val.val := by
    obtain ⟨cut, hp, hb, hcut⟩ :=
      D5.S1.Words.Patterns.Separable.ProperCut.avoidance_proper_cut hn π.val.val
        π.val.property.1 π.val.property.2
    rcases hcut with direct | skew
    · exact ⟨false, cut, by omega, hb, direct⟩
    · exact ⟨true, cut, by omega, hb, skew⟩
  let sign := Classical.choose existsCut
  have hasCut := Classical.choose_spec existsCut
  let left := Nat.find hasCut
  have cutSpec := Nat.find_spec hasCut
  have hleft : 0 < left := cutSpec.1
  have hproper : left < n := cutSpec.2.1
  have minimal : MinimumCut sign π.val.val left := by
    refine ⟨cutSpec.2.2, ?_⟩
    intro smaller hp hb hc
    exact Nat.find_min hasCut hb ⟨hp, by omega, hc⟩
  have compatible : state = none ∨ state = some (!sign) := by
    cases state with
    | none => exact Or.inl rfl
    | some blocked =>
      right
      have different : blocked ≠ sign := by
        intro equality
        exact π.property ((congrArg (fun other => HasProperCut other π.val.val)
          equality).mpr hasCut)
      exact congrArg some (Bool.eq_not_of_ne different)
  let right := n - left
  have hright : 0 < right := by dsimp [right]; omega
  have equality : left + right = n := by dsimp [right]; omega
  let parent : Avoider (left + right) := equality.symm ▸ π.val
  have parentMinimum : MinimumCut sign parent.val left := by
    have transport : ∀ {size} (eq : size = n),
        MinimumCut sign (eq.symm ▸ π.val).val left := by
      intro size eq
      cases eq
      exact minimal
    exact transport equality
  obtain ⟨equivalence, reconstruction, _⟩ :=
    minimum_cut_cartesian_kernel sign left right hleft hright
  let factors := equivalence.symm ⟨parent, parentMinimum⟩
  have assembled : (⟨blockSum sign factors.1.val.val factors.2.val,
      (avoids_block_sum_iff sign _ _).mpr
        ⟨factors.1.val.property, factors.2.property⟩⟩ : Avoider (left + right)) = parent := by
    apply Subtype.ext
    change blockSum sign factors.1.val.val factors.2.val = parent.val
    have certificate : equivalence factors = ⟨parent, parentMinimum⟩ :=
      equivalence.apply_symm_apply _
    exact (reconstruction factors).symm.trans
      (congrArg (fun sample : MinimumFiber sign left right => sample.val.val) certificate)
  constructor
  refine ⟨sign, left, right, hleft, hright, equality, compatible,
    factors.1, factors.2, ?_, minimal, ?_, ?_⟩
  · rw [assembled]
    have cancel : ∀ {size} (eq : size = n),
        eq ▸ (eq.symm ▸ π.val : Avoider size) = π.val := by
      intro size eq
      cases eq
      rfl
    exact cancel equality
  · intro other cut hp hb hm
    have same : other = sign := by
      by_contra different
      have opposite : other = !sign := Bool.eq_not_of_ne different
      exact incompatible sign hasCut (opposite ▸ ⟨cut, hp, hb, hm.1⟩)
    refine ⟨same, ?_⟩
    subst other
    have notSmaller : ¬cut < left := fun hl => minimal.2 cut hp hl hm.1
    have notLarger : ¬left < cut := fun hl => hm.2 left hleft hl minimal.1
    omega
  · intro α β equality
    have same : equivalence (α, β) = equivalence factors := by
      apply Subtype.ext
      apply Subtype.ext
      rw [reconstruction, reconstruction]
      exact equality
    have factorEq := equivalence.injective same
    exact ⟨congrArg Prod.fst factorEq, congrArg Prod.snd factorEq⟩

inductive StopKind where
  | good | short | small | exhausted | cap
  deriving DecidableEq

def StopLaw {state n} (m B H K : ℕ) (history : EndpointHistory state n)
    (sample : history.Leaf) : StopKind → Prop
  | .good => m ≤ history.emitted ∧ B < history.remaining
  | .short => m ≤ history.emitted ∧ history.remaining ≤ B
  | .small => history.emitted < m ∧ history.remaining < 2
  | .exhausted => history.emitted < m ∧ history.steps = H
  | .cap => history.emitted < m ∧
      ∃ sign left right, 0 < left ∧ 0 < right ∧
        history.remaining = left + right ∧ K < left ∧ K < right ∧
        MinimumCut sign sample.val.val left

structure Run {state n} (π : Carrier state n) (m B H K : ℕ) where
  history : EndpointHistory state n
  sample : history.Leaf
  reconstruct : history.assemble sample = π.val
  kind : StopKind
  steps_bound : history.steps ≤ H
  capped : history.Capped K
  stop_law : StopLaw m B H K history sample kind

noncomputable def explore {state n} (m B K : ℕ) :
    (H : ℕ) → (π : Carrier state n) → Run π m B H K := by
  classical
  intro H
  induction H generalizing state n m with
  | zero =>
    intro π
    let history := EndpointHistory.stop state n
    refine ⟨history, π, rfl, ?_, by simp [history, EndpointHistory.steps], trivial, ?_⟩
    · exact if m = 0 then (if B < n then .good else .short)
      else if n < 2 then .small else .exhausted
    · split_ifs with hm hb hn
      · simp [StopLaw, history, EndpointHistory.emitted, EndpointHistory.remaining, hm, hb]
      · simp [StopLaw, history, EndpointHistory.emitted, EndpointHistory.remaining, hm]
        omega
      · simp [StopLaw, history, EndpointHistory.emitted, EndpointHistory.remaining]
        omega
      · simp [StopLaw, history, EndpointHistory.emitted, EndpointHistory.steps]
        omega
  | succ H induction =>
    intro π
    by_cases hm : m = 0
    · let history := EndpointHistory.stop state n
      refine ⟨history, π, rfl, if B < n then .good else .short,
        by simp [history, EndpointHistory.steps], trivial, ?_⟩
      split_ifs with hb <;> simp [StopLaw, history, EndpointHistory.emitted,
        EndpointHistory.remaining, hm] <;> omega
    by_cases hn : n < 2
    · exact ⟨.stop state n, π, rfl, .small, by simp [EndpointHistory.steps], trivial,
        by simp [StopLaw, EndpointHistory.emitted, EndpointHistory.remaining]; omega⟩
    obtain ⟨sign, left, right, hl, hr, equality, compatible, first, last,
      reconstructed, minimal, unique, factorUnique⟩ := recover π (by omega)
    subst n
    by_cases hleft : left ≤ K
    · let child := induction (state := none) (n := right) (m := m - left) ⟨last, trivial⟩
      let history := EndpointHistory.emit sign hl hr compatible first child.history
      refine ⟨history, child.sample, ?_, child.kind, ?_, ⟨hleft, child.capped⟩, ?_⟩
      · apply Subtype.ext
        change blockSum sign first.val.val (child.history.assemble child.sample).val = π.val.val
        rw [child.reconstruct]
        exact congrArg Subtype.val reconstructed
      · dsimp [history, EndpointHistory.steps]
        have := child.steps_bound
        omega
      · have law := child.stop_law
        cases hk : child.kind <;> simp only [hk, StopLaw] at law ⊢ <;>
          dsimp [history, EndpointHistory.emitted, EndpointHistory.remaining,
            EndpointHistory.steps] at *
        · omega
        · omega
        · omega
        · omega
        · obtain ⟨notEnough, s, a, b, ha, hb, hab, hka, hkb, rest⟩ := law
          exact ⟨by omega, s, a, b, ha, hb, hab, hka, hkb, rest⟩
    by_cases hright : right ≤ K
    · let child := induction (state := some sign) (n := left) (m := m) first
      let history := EndpointHistory.discard sign hl hr compatible last child.history
      refine ⟨history, child.sample, ?_, child.kind, ?_, ⟨hright, child.capped⟩, ?_⟩
      · apply Subtype.ext
        change blockSum sign (child.history.assemble child.sample).val last.val = π.val.val
        rw [child.reconstruct]
        exact congrArg Subtype.val reconstructed
      · dsimp [history, EndpointHistory.steps]
        have := child.steps_bound
        omega
      · have law := child.stop_law
        cases hk : child.kind <;> simp only [hk, StopLaw] at law ⊢ <;>
          dsimp [history, EndpointHistory.emitted, EndpointHistory.remaining,
            EndpointHistory.steps] at *
        · exact law
        · exact law
        · exact law
        · omega
        · exact law
    · exact ⟨.stop state (left + right), π, rfl, .cap,
        by simp [EndpointHistory.steps], trivial,
        ⟨by simp [EndpointHistory.emitted]; omega, sign, left, right, hl, hr,
          rfl, by omega, by omega, minimal⟩⟩

abbrev Outcome (state : Option Bool) (n : ℕ) := EndpointHistory state n × StopKind

noncomputable def classify {state n} (m B H K : ℕ) (π : Carrier state n) : Outcome state n :=
  ((explore m B K H π).history, (explore m B K H π).kind)

noncomputable def catalog {state n} (m B H K : ℕ) : Finset (Outcome state n) := by
  classical
  exact Finset.univ.image (classify (state := state) (n := n) m B H K)

def Fiber {state n} (m B H K : ℕ) (outcome : Outcome state n) (π : Avoider n) : Prop :=
  ∃ allowed : Allowed state π, classify m B H K ⟨π, allowed⟩ = outcome

def SelectedLeaf {state n} (m B H K : ℕ) (outcome : Outcome state n)
    (sample : outcome.1.Leaf) : Prop :=
  Fiber m B H K outcome (outcome.1.assemble sample)

def Exclusive {state n} (K : ℕ) : EndpointHistory state n → Prop
  | .stop _ _ => True
  | .emit (left := left) (right := right) _ _ _ _ _ tail =>
      2 * K < left + right ∧ ¬(left ≤ K ∧ right ≤ K) ∧ Exclusive K tail
  | .discard (left := left) (right := right) _ _ _ _ _ tail =>
      2 * K < left + right ∧ ¬(left ≤ K ∧ right ≤ K) ∧ Exclusive K tail

open Classical in
noncomputable def CylinderMass {state n} (m B H K : ℕ)
    (test : List (Option (Fin B)) → Prop) (outcome : Outcome state n) : ℝ :=
  if outcome.2 = .good then
    if test ((outcome.1.word B 0).take m) then actualMass n (Fiber m B H K outcome) else 0
  else actualMass n (fun π => Fiber m B H K outcome π ∧
    test ((EndpointHistory.literal π B 0).take m))

open Classical in
noncomputable def NoFixedMass {state n} (m H K : ℕ) (outcome : Outcome state n) : ℝ :=
  if outcome.2 = .good then
    if EndpointHistory.NoFixedWord m ((outcome.1.word m 0).take m)
      then actualMass n (Fiber m m H K outcome) else 0
  else actualMass n (fun π => Fiber m m H K outcome π ∧ EndpointHistory.AbsoluteNoFixed m π)

open Classical in
theorem actual_capped_partition (state : Option Bool) (n m B H K : ℕ) :
    (∀ π : Carrier state n,
      (explore m B K H π).history.Trace (explore m B K H π).sample ∧
      (explore m B K H π).history.removed ≤ H * K ∧
      (explore m B K H π).history.removed + (explore m B K H π).history.remaining = n) ∧
    (∀ π : Avoider n, Allowed state π ↔
      ∃! outcome : Outcome state n,
        outcome ∈ catalog m B H K ∧ Fiber m B H K outcome π) ∧
    (∀ outcome : Outcome state n,
      Nat.card {π : Avoider n // Fiber m B H K outcome π} =
        Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} ∧
      actualMass n (Fiber m B H K outcome) =
        (Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} : ℝ) /
          Nat.card (Avoider n) ∧
      Nat.card {π : Avoider n // Fiber m B H K outcome π} ≤ Nat.card outcome.1.Leaf ∧
      actualMass n (Fiber m B H K outcome) / actualMass n (Allowed state) =
        outcome.1.weight *
          (Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} : ℝ) /
            Nat.card outcome.1.Leaf) ∧
    (∀ event : Avoider n → Prop,
      Nat.card {π : Avoider n // Allowed state π ∧ event π} =
        ∑ outcome ∈ catalog (state := state) (n := n) m B H K,
          Nat.card {π : Avoider n // Fiber m B H K outcome π ∧ event π} ∧
      actualMass n (fun π => Allowed state π ∧ event π) =
        ∑ outcome ∈ catalog (state := state) (n := n) m B H K,
          actualMass n (fun π => Fiber m B H K outcome π ∧ event π)) ∧
    (∀ test : List (Option (Fin B)) → Prop,
      actualMass n (fun π => Allowed state π ∧
        test ((EndpointHistory.literal π B 0).take m)) =
        ∑ outcome ∈ catalog (state := state) (n := n) m B H K,
          CylinderMass m B H K test outcome) ∧
    (actualMass n (fun π => Allowed state π ∧ EndpointHistory.AbsoluteNoFixed m π) =
      ∑ outcome ∈ catalog (state := state) (n := n) m m H K,
        NoFixedMass m H K outcome) ∧
    (∀ π : Carrier state n, H * K + max (2 * K) (max m B) < n →
      max (2 * K) (max m B) < (explore m B K H π).history.remaining ∧
      (explore m B K H π).kind ≠ .small ∧ (explore m B K H π).kind ≠ .short ∧
      Exclusive K (explore m B K H π).history) := by
  classical
  have mass (event : Avoider n → Prop) : actualMass n event =
      (Nat.card {π : Avoider n // event π} : ℝ) / Nat.card (Avoider n) := by
    let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
    change ((PMF.uniformOfFintype (Avoider n)).toOuterMeasure {π | event π}).toReal = _
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.card_eq_fintype_card]
    rfl
  have sourcePositive : (Nat.card (Avoider n) : ℝ) ≠ 0 := by
    let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
    exact_mod_cast (Nat.card_pos (α := Avoider n)).ne'
  have inCatalog (a b : ℕ) (π : Carrier state n) :
      classify a b H K π ∈ catalog a b H K := by
    exact Finset.mem_image.mpr ⟨π, Finset.mem_univ _, rfl⟩
  have fiberEvent (a b : ℕ) (outcome : Outcome state n) (π : Avoider n)
      (hf : Fiber a b H K outcome π) : outcome.1.Event π := by
    obtain ⟨allowed, classified⟩ := hf
    have historyEq : (explore a b K H ⟨π, allowed⟩).history = outcome.1 :=
      congrArg Prod.fst classified
    have event : (explore a b K H ⟨π, allowed⟩).history.Event π :=
      ⟨(explore a b K H ⟨π, allowed⟩).sample, (explore a b K H ⟨π, allowed⟩).reconstruct⟩
    rwa [historyEq] at event
  have goodLaw (a b : ℕ) (outcome : Outcome state n)
      (member : outcome ∈ catalog a b H K) (good : outcome.2 = .good) :
      a ≤ outcome.1.emitted ∧ b < outcome.1.remaining := by
    obtain ⟨π, _, equality⟩ := Finset.mem_image.mp member
    have hhistory : (explore a b K H π).history = outcome.1 := congrArg Prod.fst equality
    have hkind : (explore a b K H π).kind = .good := (congrArg Prod.snd equality).trans good
    have law := (explore a b K H π).stop_law
    rw [hkind] at law
    change a ≤ (explore a b K H π).history.emitted ∧
      b < (explore a b K H π).history.remaining at law
    rwa [hhistory] at law
  have partition (a b : ℕ) (π : Avoider n) : Allowed state π ↔
      ∃! outcome : Outcome state n,
        outcome ∈ catalog a b H K ∧ Fiber a b H K outcome π := by
    constructor
    · intro allowed
      refine ⟨classify a b H K ⟨π, allowed⟩,
        ⟨inCatalog a b ⟨π, allowed⟩, allowed, rfl⟩, ?_⟩
      rintro outcome ⟨_, other, equality⟩
      exact equality.symm
    · rintro ⟨_, ⟨_, allowed, _⟩, _⟩
      exact allowed
  have fiberCounts (outcome : Outcome state n) :
      Nat.card {π : Avoider n // Fiber m B H K outcome π} =
        Nat.card {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} := by
    let mapping : {sample : outcome.1.Leaf // SelectedLeaf m B H K outcome sample} →
        {π : Avoider n // Fiber m B H K outcome π} :=
      fun sample => ⟨outcome.1.assemble sample.val, sample.property⟩
    have injective : Function.Injective mapping := by
      intro first last equality
      apply Subtype.ext
      exact (endpoint_history_count_kernel outcome.1).2.1 (congrArg Subtype.val equality)
    have surjective : Function.Surjective mapping := by
      rintro ⟨π, hf⟩
      obtain ⟨sample, equality⟩ := fiberEvent m B outcome π hf
      refine ⟨⟨sample, ?_⟩, Subtype.ext equality⟩
      change Fiber m B H K outcome (outcome.1.assemble sample)
      rw [equality]
      exact hf
    exact (Nat.card_congr (Equiv.ofBijective mapping ⟨injective, surjective⟩)).symm
  have counts (a b : ℕ) (event : Avoider n → Prop) :
      Nat.card {π : Avoider n // Allowed state π ∧ event π} =
        ∑ outcome ∈ catalog (state := state) (n := n) a b H K,
          Nat.card {π : Avoider n // Fiber a b H K outcome π ∧ event π} := by
    let codes := {outcome : Outcome state n // outcome ∈ catalog a b H K}
    let total := Σ outcome : codes,
      {π : Avoider n // Fiber a b H K outcome.val π ∧ event π}
    let mapping : total → {π : Avoider n // Allowed state π ∧ event π} :=
      fun item => ⟨item.2.val, item.2.property.1.choose, item.2.property.2⟩
    have injective : Function.Injective mapping := by
      rintro ⟨first, firstπ⟩ ⟨last, lastπ⟩ equality
      have actualEq : firstπ.val = lastπ.val := congrArg Subtype.val equality
      have codeEq : first = last := by
        apply Subtype.ext
        obtain ⟨allowed, classified⟩ := firstπ.property.1
        obtain ⟨other, otherClassified⟩ := lastπ.property.1
        have same : classify a b H K ⟨firstπ.val, allowed⟩ =
            classify a b H K ⟨lastπ.val, other⟩ :=
          congrArg (classify a b H K) (Subtype.ext actualEq)
        exact classified.symm.trans (same.trans otherClassified)
      cases codeEq
      congr 1
      exact Subtype.ext actualEq
    have surjective : Function.Surjective mapping := by
      rintro ⟨π, allowed, hevent⟩
      exact ⟨⟨⟨classify a b H K ⟨π, allowed⟩, inCatalog a b ⟨π, allowed⟩⟩,
        ⟨π, ⟨allowed, rfl⟩, hevent⟩⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective mapping ⟨injective, surjective⟩), Nat.card_sigma]
    simpa only [codes] using Finset.sum_coe_sort
      (catalog (state := state) (n := n) a b H K)
      (fun outcome => Nat.card {π : Avoider n // Fiber a b H K outcome π ∧ event π})
  have massSum (a b : ℕ) (event : Avoider n → Prop) :
      actualMass n (fun π => Allowed state π ∧ event π) =
        ∑ outcome ∈ catalog (state := state) (n := n) a b H K,
          actualMass n (fun π => Fiber a b H K outcome π ∧ event π) := by
    simp_rw [mass]
    rw [counts a b event, Nat.cast_sum, Finset.sum_div]
  have restrict (whole part test : Avoider n → Prop) (flag : Prop)
      (subset : ∀ π, part π → whole π)
      (wholeMass : actualMass n (fun π => whole π ∧ test π) =
        if flag then actualMass n whole else 0) :
      actualMass n (fun π => part π ∧ test π) =
        if flag then actualMass n part else 0 := by
    by_cases hflag : flag
    · rw [if_pos hflag] at wholeMass ⊢
      rw [mass, mass] at wholeMass
      have cardEq : Nat.card {π : Avoider n // whole π ∧ test π} =
          Nat.card {π : Avoider n // whole π} := by
        exact_mod_cast (div_left_inj' sourcePositive).mp wholeMass
      have nestedEq :
          Fintype.card {π : {π : Avoider n // whole π} // test π.val} =
            Fintype.card {π : Avoider n // whole π} := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter whole test)]
        exact cardEq
      have equalPredicates : (fun π => part π ∧ test π) = part := by
        funext π
        apply propext
        refine ⟨And.left, fun hp => ⟨hp, ?_⟩⟩
        by_contra notTest
        have strict := Fintype.card_subtype_lt
          (p := fun x : {π : Avoider n // whole π} => test x.val)
          (x := ⟨π, subset π hp⟩) notTest
        rw [nestedEq] at strict
        omega
      rw [equalPredicates]
    · rw [if_neg hflag] at wholeMass ⊢
      rw [mass, div_eq_zero_iff] at wholeMass
      have zero : Nat.card {π : Avoider n // whole π ∧ test π} = 0 := by
        rcases wholeMass with zero | impossible
        · exact_mod_cast zero
        · exact False.elim (sourcePositive impossible)
      have empty : IsEmpty {π : Avoider n // whole π ∧ test π} := by
        apply Fintype.card_eq_zero_iff.mp
        rwa [← Nat.card_eq_fintype_card]
      have equalPredicates : (fun π => part π ∧ test π) = fun _ => False := by
        funext π
        apply propext
        refine ⟨?_, False.elim⟩
        rintro ⟨hp, ht⟩
        exact empty.false ⟨π, subset π hp, ht⟩
      rw [equalPredicates, mass]
      simp
  refine ⟨?_, partition m B, ?_, ?_, ?_, ?_, ?_⟩
  · intro π
    have kernel := endpoint_history_count_kernel (explore m B K H π).history
    refine ⟨(kernel.1 _).2, ?_, kernel.2.2.2.2.2.1⟩
    exact (kernel.2.2.2.2.2.2.1 K (explore m B K H π).capped).trans
      (Nat.mul_le_mul_right K (explore m B K H π).steps_bound)
  · intro outcome
    have leafPositive : (Nat.card outcome.1.Leaf : ℝ) ≠ 0 := by
      let : Nonempty outcome.1.Leaf := ⟨carrierWitness _ _⟩
      exact_mod_cast (Nat.card_pos (α := outcome.1.Leaf)).ne'
    have allowedPositive : actualMass n (Allowed state) ≠ 0 := by
      let : Nonempty (Carrier state n) := ⟨carrierWitness _ _⟩
      rw [mass]
      apply div_ne_zero _ sourcePositive
      exact_mod_cast (Nat.card_pos (α := Carrier state n)).ne'
    have kernel := endpoint_history_count_kernel outcome.1
    have eventMass : actualMass n outcome.1.Event =
        (Nat.card outcome.1.Leaf : ℝ) / Nat.card (Avoider n) := by
      rw [mass, kernel.2.2.1]
    refine ⟨fiberCounts outcome, by rw [mass, fiberCounts], ?_, ?_⟩
    · rw [fiberCounts outcome]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    · rw [← kernel.2.2.2.1, eventMass, mass, fiberCounts outcome]
      field_simp
  · intro event
    exact ⟨counts m B event, massSum m B event⟩
  · intro test
    rw [massSum]
    apply Finset.sum_congr rfl
    intro outcome member
    unfold CylinderMass
    by_cases good : outcome.2 = .good
    · rw [if_pos good]
      obtain ⟨emitted, remaining⟩ := goodLaw m B outcome member good
      exact restrict outcome.1.Event (Fiber m B H K outcome)
        (fun π => test ((EndpointHistory.literal π B 0).take m))
        (test ((outcome.1.word B 0).take m)) (fiberEvent m B outcome)
        ((endpoint_history_literal_cylinder outcome.1).2.1 B m remaining emitted test)
    · rw [if_neg good]
  · rw [massSum m m]
    apply Finset.sum_congr rfl
    intro outcome member
    unfold NoFixedMass
    by_cases good : outcome.2 = .good
    · rw [if_pos good]
      obtain ⟨emitted, remaining⟩ := goodLaw m m outcome member good
      exact restrict outcome.1.Event (Fiber m m H K outcome)
        (EndpointHistory.AbsoluteNoFixed m)
        (EndpointHistory.NoFixedWord m ((outcome.1.word m 0).take m))
        (fiberEvent m m outcome)
        ((endpoint_history_literal_cylinder outcome.1).2.2.2 m remaining emitted)
    · rw [if_neg good]
  · intro π threshold
    let run := explore m B K H π
    have kernel := endpoint_history_count_kernel run.history
    have removed := (kernel.2.2.2.2.2.2.1 K run.capped).trans
      (Nat.mul_le_mul_right K run.steps_bound)
    have sizeEq := kernel.2.2.2.2.2.1
    have remaining : max (2 * K) (max m B) < run.history.remaining := by omega
    have exclusive : ∀ {root size} (history : EndpointHistory root size),
        2 * K < history.remaining → Exclusive K history := by
      intro root size history
      induction history with
      | stop => simp [Exclusive]
      | @emit root left right sign hl hr compatible shape tail induction =>
        intro bound
        have tailBound := (endpoint_history_count_kernel tail).2.2.2.2.1
        refine ⟨by dsimp [EndpointHistory.remaining] at bound; omega,
          by dsimp [EndpointHistory.remaining] at bound; omega, induction bound⟩
      | @discard root left right sign hl hr compatible shape tail induction =>
        intro bound
        have tailBound := (endpoint_history_count_kernel tail).2.2.2.2.1
        refine ⟨by dsimp [EndpointHistory.remaining] at bound; omega,
          by dsimp [EndpointHistory.remaining] at bound; omega, induction bound⟩
    refine ⟨remaining, ?_, ?_, exclusive run.history (by omega)⟩
    · intro equality
      have law := run.stop_law
      rw [equality] at law
      change run.history.emitted < m ∧ run.history.remaining < 2 at law
      omega
    · intro equality
      have law := run.stop_law
      rw [equality] at law
      change m ≤ run.history.emitted ∧ run.history.remaining ≤ B at law
      omega

#print axioms recover
#print axioms explore
#print axioms actual_capped_partition

end D5.S1.Words.Patterns.Separable.CappedExploration
