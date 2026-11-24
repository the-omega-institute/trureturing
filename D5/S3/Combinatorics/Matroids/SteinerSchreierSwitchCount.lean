/- GID: D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A labelled Steiner system realizes the switch count prescribed by quotient returns. -/

import D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches
import D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
import Mathlib.Logic.Equiv.Option

/-! # Labelled switch counts in Steiner central extensions -/

namespace D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount

open Set
open scoped Set.Notation
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap (Covered Uncovered pair_completion)
open D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations
  (translate translate_none translate_self
    translate_deleted_match switch_commutes_iff)
open D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch
  (pointDeletedFamily point_deleted_switch)
open D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches (SuccessfulStart)

private theorem loopTriples {L : Type*} [Mul L] {r : ℕ}
    (label : Option (Fin (r + 1)) ≃ L)
    (unit : ∀ a, label none * a = a)
    (comm : ∀ a b : L, a * b = b * a)
    (invol : ∀ a b : L, a * (a * b) = b) :
    ∃ (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (complete : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      ∀ (p : Fin (r + 1)) (a : Option (Fin (r + 1))),
        label (translate valid complete p a) = label (some p) * label a := by
  classical
  let S : Set (Set (Fin (r + 1))) := {s | s.ncard = 3 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
    ∃ c ∈ s, label (some a) * label (some b) = label (some c)}
  have rightUnit (a : L) : a * label none = a := (comm _ _).trans (unit _)
  have square (a : L) : a * a = label none := by
    simpa only [rightUnit] using invol a (label none)
  have injMul (a : L) : Function.Injective (a * ·) :=
    (show Function.Involutive (a * ·) from invol a).injective
  have third {a b : Fin (r + 1)} (hab : a ≠ b) :
      ∃ c : Fin (r + 1), c ≠ a ∧ c ≠ b ∧ label (some a) * label (some b) = label (some c) := by
    have productNe : label (some a) * label (some b) ≠ label none := by
      intro h
      apply hab
      simpa using label.injective (injMul (label (some a)) ((square _).trans h.symm))
    obtain ⟨i, hi⟩ := label.surjective (label (some a) * label (some b))
    cases i with
    | none => exact (productNe hi.symm).elim
    | some c =>
      refine ⟨c, ?_, ?_, hi.symm⟩
      · intro hca
        have ha := hi.symm.trans (congrArg (fun j => label (some j)) hca)
        have h := label.injective (injMul (label (some a)) (ha.trans (rightUnit _).symm))
        exact Option.some_ne_none _ h
      · intro hcb
        rw [comm] at hi
        have hb := hi.symm.trans (congrArg (fun j => label (some j)) hcb)
        have h := label.injective (injMul (label (some b)) (hb.trans (rightUnit _).symm))
        exact Option.some_ne_none _ h
  have tripleCard {a b c : Fin (r + 1)} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
      ({a,b,c} : Set (Fin (r + 1))).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hab, hca.symm]), ncard_pair hcb.symm]
  have valid : IsPartialSteiner S := by
    refine ⟨fun s hs => hs.1, ?_⟩
    intro s hs t ht a b hab ha hb hat hbt
    obtain ⟨c, hc, he⟩ := hs.2 a ha b hb hab
    obtain ⟨d, hd, hf⟩ := ht.2 a hat b hbt hab
    have same : c = d := by simpa using label.injective (he.symm.trans hf)
    subst d
    obtain ⟨z, hza, hzb, hz⟩ := third hab
    have hz' : z = c := by simpa using label.injective (hz.symm.trans he)
    subst z
    have card := tripleCard hab hza hzb
    have one : ({a,b,c} : Set (Fin (r + 1))) = s :=
      eq_of_subset_of_ncard_le (insert_subset ha (insert_subset hb (singleton_subset_iff.mpr hc)))
        (by rw [hs.1, card])
    have two : ({a,b,c} : Set (Fin (r + 1))) = t :=
      eq_of_subset_of_ncard_le (insert_subset hat (insert_subset hbt (singleton_subset_iff.mpr hd)))
        (by rw [ht.1, card])
    exact one.symm.trans two
  have complete : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b := by
    intro a b hab
    obtain ⟨c, hca, hcb, he⟩ := third hab
    refine ⟨{a,b,c}, ⟨tripleCard hab hca hcb, ?_⟩, by simp, by simp⟩
    have hac : label (some a) * label (some c) = label (some b) := by
      rw [← he, invol]
    have hbc : label (some b) * label (some c) = label (some a) := by
      rw [← he, comm (label (some a)) (label (some b)), invol]
    intro x hx y hy hxy
    simp only [mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals
      first
      | exact (hxy rfl).elim
      | exact ⟨c, by simp, he⟩
      | exact ⟨b, by simp, hac⟩
      | exact ⟨a, by simp, hbc⟩
      | exact ⟨c, by simp, (comm _ _).trans he⟩
      | exact ⟨b, by simp, (comm _ _).trans hac⟩
      | exact ⟨a, by simp, (comm _ _).trans hbc⟩
  refine ⟨S, valid, complete, ?_⟩
  intro p a
  cases a with
  | none => rw [translate_none, rightUnit]
  | some x =>
    by_cases hx : x = p
    · subst x
      rw [translate_self, square]
    · have px : p ≠ x := fun he => hx he.symm
      rw [translate, dite_eq_right hx]
      let h := pair_completion valid px (complete p x px)
      let y := h.choose
      change label (some y) = label (some p) * label (some x)
      have block : ({p,x,y} : Set (Fin (r + 1))) ∈ S := h.choose_spec.2.2
      obtain ⟨z, hz, equal⟩ := block.2 p (by simp) x (by simp) px
      have hzP : z ≠ p := by
        intro he
        have hEqual := equal.trans (congrArg (fun j => label (some j)) he)
        have bad := label.injective (injMul (label (some p)) (hEqual.trans (rightUnit _).symm))
        exact Option.some_ne_none _ bad
      have hzX : z ≠ x := by
        intro he
        have hEqual := (comm (label (some x)) (label (some p))).trans
          (equal.trans (congrArg (fun j => label (some j)) he))
        have bad := label.injective (injMul (label (some x)) (hEqual.trans (rightUnit _).symm))
        exact Option.some_ne_none _ bad
      have zy : z = y := by
        simpa [hzP, hzX] using hz
      simpa [zy] using equal.symm

private theorem labelledSwitchCount {L : Type*} [Mul L] {r : ℕ}
    (label : Option (Fin (r + 1)) ≃ L)
    (unit : ∀ a, label none * a = a)
    (comm : ∀ a b : L, a * b = b * a)
    (invol : ∀ a b : L, a * (a * b) = b) :
    ∃ (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      (∀ (p : Fin (r + 1)) (a : Option (Fin (r + 1))),
        label (translate valid cover p a) = label (some p) * label a) ∧
      ∀ q : Fin (r + 1), ∃ m : Fin r → Fin r,
        (∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) ∧
        ∀ v : Fin r,
        let p := label (some q)
        let w := label (some (q.succAbove v))
        (label ∘ Option.some ∘ q.succAbove) ''
          {a | SuccessfulStart (pointDeletedFamily S q) m v a} =
          {x | w * (p * x) ≠ p * (w * x)} ∧
        ({a | SuccessfulStart (pointDeletedFamily S q) m v a} : Set (Fin r)).ncard =
          ({x | w * (p * x) ≠ p * (w * x)} : Set L).ncard := by
  classical
  obtain ⟨S, valid, cover, transport⟩ := loopTriples label unit comm invol
  refine ⟨S, valid, cover, transport, ?_⟩
  intro q
  obtain ⟨_, m, _, _, leave, switch⟩ := point_deleted_switch S valid cover q
  refine ⟨m, leave, ?_⟩
  intro v p w
  let embed : Fin r → L := label ∘ Option.some ∘ q.succAbove
  have inj : Function.Injective embed :=
    label.injective.comp ((Option.some_injective _).comp Fin.succAbove_right_injective)
  have rightUnit (x : L) : x * label none = x := (comm _ _).trans (unit _)
  have square (x : L) : x * x = label none := by
    simpa only [rightUnit] using invol x (label none)
  have atUnit : w * (p * label none) = p * (w * label none) := by
    rw [rightUnit, rightUnit, comm w p]
  have atP : w * (p * p) = p * (w * p) := by
    rw [square, rightUnit, comm w p, invol]
  have atW : w * (p * w) = p * (w * w) := by
    rw [comm p w, invol, square, rightUnit]
  have atThird : w * (p * (p * w)) = p * (w * (p * w)) := by
    rw [invol, square, comm p w, invol, square]
  have onLabels (a : Fin r) :
      SuccessfulStart (pointDeletedFamily S q) m v a ↔
        w * (p * embed a) ≠ p * (w * embed a) := by
    by_cases hv : v = a
    · subst a
      exact ⟨fun h => (h.1 rfl).elim, fun h => (h atW).elim⟩
    by_cases hm : v = m a
    · have mate := transport q (some (q.succAbove a))
      rw [translate_deleted_match valid cover q leave a, ← hm] at mate
      have point : embed a = p * w := by
        change w = p * embed a at mate
        rw [mate, invol]
      exact ⟨fun h => (h.2.1 hm).elim, fun h => (h (by rw [point]; exact atThird)).elim⟩
    have sameEnds {b d : Fin r}
        (hb : ({a,v,b} : Set (Fin r)) ∈ pointDeletedFamily S q)
        (hd : ({m a,v,d} : Set (Fin r)) ∈ pointDeletedFamily S q) :
        w * (p * embed a) = p * (w * embed a) ↔ d = m b := by
      let start := some (q.succAbove a)
      let pivot := q.succAbove v
      have left :
          label (translate valid cover pivot (translate valid cover q start)) =
            w * (p * embed a) :=
        (transport pivot (translate valid cover q start)).trans
          (congrArg (w * ·) (transport q start))
      have right :
          label (translate valid cover q (translate valid cover pivot start)) =
            p * (w * embed a) :=
        (transport q (translate valid cover pivot start)).trans
          (congrArg (p * ·) (transport pivot start))
      rw [← left, ← right]
      exact label.injective.eq_iff.trans (switch_commutes_iff valid cover q leave hv hm hb hd)
    constructor
    · rintro ⟨_, _, b, d, hb, hd, hne⟩ h
      exact hne ((sameEnds hb hd).mp h)
    · intro h
      obtain ⟨b,d,hb,hd,_⟩ := switch a v hv hm
      exact ⟨hv, hm, b, d, hb, hd, fun he => h ((sameEnds hb hd).mpr he)⟩
  have image :
      embed '' {a | SuccessfulStart (pointDeletedFamily S q) m v a} =
        {x | w * (p * x) ≠ p * (w * x)} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (onLabels a).mp ha
    · intro h
      obtain ⟨i, rfl⟩ := label.surjective x
      cases i with
      | none => exact (h atUnit).elim
      | some i =>
        by_cases eq : i = q
        · subst i
          exact (h atP).elim
        · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq eq
          exact ⟨a, (onLabels a).mpr h, rfl⟩
  exact ⟨image, (ncard_image_of_injective _ inj).symm.trans (congrArg Set.ncard image)⟩

open Function
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul realizeSchreierReturns)

private theorem extensionNoncommutingCount {L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] (G : SimpleGraph L) (e p q : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0) (centreless : Set.center L = {e})
    (hpq : p ≠ q) (hp : p ≠ e) (hq : q ≠ e)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (t : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e} → A) :
    ∃ labels : Set L → A,
      let _ := extensionMul e labels
      let g : L → L := fun x => p * (q * x)
      let P : L × A := (p, 0)
      let Q : L × A := (q, 0)
      (∀ x : L × A, (e, 0) * x = x) ∧
      (∀ x y : L × A, x * y = y * x) ∧
      (∀ x y : L × A, x * (x * y) = y) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      let selected : Set L := {x | g (g x) ≠ x ∨
        ∃ h : G.connectedComponentMk x ≠ G.connectedComponentMk e,
          t ⟨G.connectedComponentMk x, h⟩ ≠ 0}
      {y : L × A | Q * (P * y) ≠ P * (Q * y)} = selected ×ˢ Set.univ := by
  classical
  obtain ⟨labels, idExt, commExt, involExt, centreExt, identity, prescribed⟩ :=
    realizeSchreierReturns G e p q unit comm invol twice centreless hpq hp hq edges t
  let _ := extensionMul e labels
  let P : L × A := (p, 0)
  let Q : L × A := (q, 0)
  let g : L → L := fun x => p * (q * x)
  let f : L × A → L × A := fun y => P * (Q * y)
  refine ⟨labels, idExt, commExt, involExt, centreExt, ?_⟩
  have two (y : L × A) : f^[2] y = f (f y) := rfl
  have step_ne (x : L) : g x ≠ x := by
    intro h
    have eq : q * x = p * x := by
      change p * (q * x) = x at h
      simpa only [invol] using congrArg (p * ·) h
    apply hpq
    apply (show Involutive (x * ·) from invol x).injective
    change x * p = x * q
    rw [comm x p, comm x q, eq]
  have period {x : L} (hx : g (g x) = x) : minimalPeriod g x = 2 := by
    have hper : IsPeriodicPt g 2 x := hx
    have div := isPeriodicPt_iff_minimalPeriod_dvd.mp hper
    rcases (Nat.dvd_prime Nat.prime_two).mp div with eq | eq
    · exact (step_ne x (minimalPeriod_eq_one_iff_isFixedPt.mp eq)).elim
    · exact eq
  have commute {y : L × A} :
      Q * (P * y) = P * (Q * y) ↔ f^[2] y = y := by
    rw [two]
    change Q * (P * y) = P * (Q * y) ↔ P * (Q * (P * (Q * y))) = y
    constructor
    · intro h
      rw [← h, involExt, involExt]
    · intro h
      have h' := congrArg (fun z => Q * (P * z)) h
      simpa only [involExt, eq_comm] using h'
  let selected : Set L := {x | g (g x) ≠ x ∨
    ∃ h : G.connectedComponentMk x ≠ G.connectedComponentMk e,
      t ⟨G.connectedComponentMk x, h⟩ ≠ 0}
  change ({y | Q * (P * y) ≠ P * (Q * y)} : Set (L × A)) = selected ×ˢ Set.univ
  ext ⟨x, a⟩
  change (Q * (P * (x, a)) ≠ P * (Q * (x, a))) ↔ x ∈ selected ∧ a ∈ Set.univ
  simp only [Set.mem_univ, and_true, selected, Set.mem_ofPred_eq]
  change (¬Q * (P * (x, a)) = P * (Q * (x, a))) ↔ _
  rw [not_congr (commute (y := (x, a)))]
  by_cases hx : g (g x) = x
  · have k := period hx
    by_cases hc : G.connectedComponentMk x = G.connectedComponentMk e
    · have h := identity x hc a
      change f^[minimalPeriod g x] (x, a) = (x, a) at h
      rw [k] at h
      simp [h, hx, hc]
    · have h := prescribed ⟨G.connectedComponentMk x, hc⟩ x rfl a
      change f^[minimalPeriod g x] (x, a) =
        (x, a + t ⟨G.connectedComponentMk x, hc⟩) at h
      rw [k] at h
      simp [h, hx, hc]
  · refine ⟨fun _ => Or.inl hx, fun _ h => hx ?_⟩
    exact congrArg Prod.fst h

/-- A labelled complete system realizes the count for a fixed prescription of returns. -/
theorem realizeLabelledSwitchCount {L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] (G : SimpleGraph L) (e p q : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0) (centreless : Set.center L = {e})
    (hpq : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (t : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e} → A) :
    ∃ (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (i : Fin (r + 1)) (v : Fin r)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b) (m : Fin r → Fin r),
      letI := extensionMul e labels
      let g : L → L := fun x => p * (q * x)
      let selected : Set L := {x | g (g x) ≠ x ∨
        ∃ h : G.connectedComponentMk x ≠ G.connectedComponentMk e,
          t ⟨G.connectedComponentMk x, h⟩ ≠ 0}
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧ label (some (i.succAbove v)) = (q, 0) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      (∀ (j : Fin (r + 1)) (a : Option (Fin (r + 1))),
        label (translate valid cover j a) = label (some j) * label a) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      (label ∘ Option.some ∘ i.succAbove) ''
        {a | SuccessfulStart (pointDeletedFamily S i) m v a} = selected ×ˢ Set.univ ∧
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
        Nat.card A * selected.ncard := by
  classical
  have hp : p ≠ e := by
    intro eq
    exact G.irrefl ((edges e e).mpr (Or.inl (by simpa [eq] using unit e)))
  have hq : q ≠ e := by
    intro eq
    exact G.irrefl ((edges e e).mpr (Or.inr (by simpa [eq] using unit e)))
  obtain ⟨labels, unitExt, commExt, invExt, centreExt, fibres⟩ :=
    extensionNoncommutingCount G e p q unit comm invol twice centreless hpq hp hq edges t
  let _ := extensionMul e labels
  let W := {y : L × A // y ≠ (e, 0)}
  let _ := Fintype.ofFinite W
  have pNe : (p, (0 : A)) ≠ (e, 0) := fun h => hp (congrArg Prod.fst h)
  have qNe : (q, (0 : A)) ≠ (e, 0) := fun h => hq (congrArg Prod.fst h)
  have : Nonempty W := ⟨⟨(p, 0), pNe⟩⟩
  let r := Fintype.card W - 1
  have card : Fintype.card W = r + 1 := by
    have pos : 0 < Fintype.card W := Fintype.card_pos
    dsimp [r]
    omega
  let label : Option (Fin (r + 1)) ≃ L × A :=
    (Equiv.optionCongr (Fintype.equivFinOfCardEq card).symm).trans
      (Equiv.optionSubtypeNe (e, 0))
  have zero : label none = (e, 0) := rfl
  have label_nonidentity (y : L × A) (hy : y ≠ (e, 0)) :
      ∃ z : Fin (r + 1), label (some z) = y := by
    obtain ⟨j, hj⟩ := label.surjective y
    cases j with
    | none => exact (hy (hj.symm.trans zero)).elim
    | some j => exact ⟨j, hj⟩
  obtain ⟨i, hi⟩ := label_nonidentity (p, 0) pNe
  obtain ⟨j, hj⟩ := label_nonidentity (q, 0) qNe
  have different : j ≠ i := by
    intro he
    rw [he, hi] at hj
    exact hpq (congrArg Prod.fst hj)
  obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq different
  have hv' : label (some (i.succAbove v)) = (q, 0) := by rw [hv, hj]
  obtain ⟨S, valid, cover, transport, byPivot⟩ :=
    labelledSwitchCount label (by simpa only [zero] using unitExt) commExt invExt
  obtain ⟨m, leave, byStart⟩ := byPivot i
  refine ⟨labels, r, label, i, v, S, valid, cover, m, zero, hi, hv', centreExt,
    transport, leave, ?_⟩
  have transported := byStart v
  dsimp only at transported
  rw [hi, hv'] at transported
  refine ⟨transported.1.trans fibres, ?_⟩
  rw [transported.2, fibres, Set.ncard_prod, Set.ncard_univ, Nat.mul_comm]

#print axioms realizeLabelledSwitchCount

end D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
