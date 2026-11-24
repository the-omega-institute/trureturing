/- GID: D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact range of binary Steiner switch counts for a fixed pivot pair. -/

import D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact fixed-pair Steiner switch count ranges from the optional four-point components. -/

namespace D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange

open Finset Function SimpleGraph
open D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches (Matchings SuccessfulStart)
open D5.S3.Combinatorics.Matroids.SteinerReturnDependencies (firstReturn returnRow)
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
  (extensionMul extensionSteinerAndCentre identityReturn pairedLift_eq_mul returnAlongComponent)
open D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (extensionNoncommutingCount labelledSwitchCount pointedNumbering squareFixed)
open D5.S3.Combinatorics.Matroids.SteinerSwitchSupport (selectedByRow)
open D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch (pointDeletedFamily)
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap (Covered Uncovered)
open D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations
  (translate translate_involutive translate_ne_self translate_ne_translate)

private theorem pivotSquareSize {L : Type*} [Finite L] [Mul L]
    (G : SimpleGraph L) (e p q : L)
    (one : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (hp : p ≠ e) (hq : q ≠ e) (different : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v) (x : L) :
    (G.connectedComponentMk x).supp.ncard = 4 ↔ p * (q * (p * (q * x))) = x := by
  have inject (z : L) : Function.Injective (· * z) := by
    intro a b eq
    apply (show Function.Involutive (z * ·) from invol z).injective
    change z * a = z * b
    rwa [comm z a, comm z b]
  let matching : Matchings L := {
    first := (p * ·)
    second := (q * ·)
    first_involutive := invol p
    second_involutive := invol q
    first_ne_self := fun z eq => hp (inject z (eq.trans (one z).symm))
    second_ne_self := fun z eq => hq (inject z (eq.trans (one z).symm))
    partners_ne := fun z eq => different (inject z eq)
  }
  have graphEq : G = matching.graph := by
    ext u v
    exact edges u v
  subst G
  change (matching.graph.connectedComponentMk x).supp.ncard = 4 ↔
    matching.first (matching.second (matching.first (matching.second x))) = x
  have commute :
      matching.first (matching.second x) = matching.second (matching.first x) ↔
        matching.first (matching.second (matching.first (matching.second x))) = x := by
    have f := matching.first_involutive
    have g := matching.second_involutive
    constructor
    · intro equal
      rw [equal, g, f]
    · intro equal
      have back := congrArg (matching.second ∘ matching.first) equal
      change matching.second (matching.first
        (matching.first (matching.second (matching.first (matching.second x))))) =
        matching.second (matching.first x) at back
      rw [f, g] at back
      exact back
  rw [← commute]
  refine ⟨fun card => ?_, fun equal => ?_⟩
  · by_contra! ne
    have six := (matching.noncommute_iff_six_le_component x).mp ne
    omega
  · rw [matching.component_eq_square equal, matching.square_card]

private noncomputable def returnValueOnComponent {L A : Type*} [Mul L] [AddCommGroup A]
    [Module (ZMod 2) A] (G : SimpleGraph L) (e p q : L) (labels : Set L → A)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0) (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (involExt : letI := extensionMul e labels
      ∀ u v : L × A, u * (u * v) = v) : G.ConnectedComponent → A := by
  let _ := extensionMul e labels
  let value (x : L) := Finsupp.linearCombination (ZMod 2) labels (returnRow e p q x)
  refine ConnectedComponent.lift value fun x y walk _ => ?_
  have transport :=
    returnAlongComponent G e p q labels invol twice edges involExt walk.reachable (value x)
      (fun a => firstReturn e labels p q x a) (0 : A)
  have returnY := firstReturn e labels p q y (0 : A)
  change (fun w : L × A => (p, 0) * ((q, 0) * w))^[minimalPeriod
    (fun v => p * (q * v)) y] (y, 0) = (y, 0 + value x) at transport
  have eq := congrArg Prod.snd (transport.symm.trans returnY)
  simpa only [zero_add] using eq

private theorem identityValue {L A : Type*} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e p q : L) (labels : Set L → A)
    (one : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (twice : ∀ a : A, a + a = 0)
    (different : p ≠ q) :
    Finsupp.linearCombination (ZMod 2) labels (returnRow e p q e) = 0 := by
  let _ := extensionMul e labels
  have h := identityReturn e p q labels (0 : A) one comm invol twice different
  rcases h with ⟨period, returns⟩
  have first := firstReturn e labels p q e (0 : A)
  rw [pairedLift_eq_mul e labels p q] at returns
  change (fun y : L × A => (p, 0) * ((q, 0) * y))^[2] (e, 0) = (e, 0) at returns
  dsimp only at first
  rw [period, returns] at first
  simpa only [zero_add] using (congrArg Prod.snd first).symm

open Finset

private theorem fourFiberCount {L C : Type*} [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C]
    (component : L → C) (available : Finset C)
    (square : ∀ c ∈ available, (univ.filter (fun x => component x = c)).card = 4)
    (base : Finset L) (separate : ∀ x ∈ base, component x ∉ available) (keep : Finset C) (sub : keep ⊆ available) :
    (base ∪ univ.filter (fun x => component x ∈ keep)).card = base.card + 4 * keep.card := by
  have disj : Disjoint base (univ.filter (fun x => component x ∈ keep)) :=
    disjoint_left.mpr fun x hx hy => separate x hx (sub (mem_filter.mp hy).2)
  rw [card_union_of_disjoint disj]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := component)
    (s := univ.filter (fun x => component x ∈ keep)) (t := keep)
    (fun x hx => (mem_filter.mp hx).2)]
  calc
    _ = ∑ _c ∈ keep, 4 := by
      refine sum_congr rfl fun c hc => ?_
      have filterEq : (univ.filter (fun x => component x ∈ keep)).filter
          (fun x => component x = c) = univ.filter (fun x => component x = c) := by
        ext x
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨And.right, fun eq => ⟨eq.symm ▸ hc, eq⟩⟩
      rw [filterEq, square c (sub hc)]
    _ = _ := by simp [Nat.mul_comm]

private theorem fixedPivotCountRange {L A : Type*} [Fintype L] [DecidableEq L] [Mul L]
    [Finite A] [AddCommGroup A] [Module (ZMod 2) A]
    (G : SimpleGraph L) [Fintype G.ConnectedComponent] [DecidableEq G.ConnectedComponent]
    (e p q : L)
    (one : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (hp : p ≠ e) (hq : q ≠ e) (different : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (count : ℕ) :
    let b := ({x : L | p * (q * (p * (q * x))) ≠ x} : Set L).ncard
    let s := ({C : G.ConnectedComponent | C ≠ G.connectedComponentMk e ∧ C.supp.ncard = 4} :
      Set G.ConnectedComponent).ncard
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      ({w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} :
        Set (L × A)).ncard = count) ↔
      ∃ k ≤ s, (k = 0 ∨ Nontrivial A) ∧ count = Nat.card A * (b + 4 * k) := by
  classical
  have square := pivotSquareSize G e p q one comm invol hp hq different edges
  let comp := G.connectedComponentMk
  let idComponent := comp e
  let Base : Finset L := univ.filter (fun x => p * (q * (p * (q * x))) ≠ x)
  let Available : Finset G.ConnectedComponent :=
    univ.filter (fun C => C ≠ idComponent ∧ C.supp.ncard = 4)
  have memBase (x : L) : x ∈ Base ↔ p * (q * (p * (q * x))) ≠ x := by simp [Base]
  have memAvailable (C : G.ConnectedComponent) :
      C ∈ Available ↔ C ≠ idComponent ∧ C.supp.ncard = 4 := by simp [Available]
  have baseCount : Base.card = ({x : L | p * (q * (p * (q * x))) ≠ x} : Set L).ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    exact memBase x
  have availableCount : Available.card =
      ({C : G.ConnectedComponent | C ≠ comp e ∧ C.supp.ncard = 4} :
        Set G.ConnectedComponent).ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext C
    exact memAvailable C
  have eachFour (C : G.ConnectedComponent) (hc : C ∈ Available) :
      (univ.filter (fun x => comp x = C)).card = 4 := by
    rw [← Set.ncard_coe_finset]
    have eq : (↑(univ.filter (fun x => comp x = C)) : Set L) = C.supp := by
      ext x
      simp [comp, ConnectedComponent.mem_supp_iff]
    rw [eq, (memAvailable C).mp hc |>.2]
  have disjoint (x : L) (hx : x ∈ Base) : comp x ∉ Available :=
    fun hc => (memBase x).mp hx ((square x).mp ((memAvailable (comp x)).mp hc).2)
  rw [← baseCount, ← availableCount]
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  constructor
  · rintro ⟨labels, hc⟩
    let _ := extensionMul e labels
    let invExt := (extensionSteinerAndCentre e labels one comm invol twice centreless).2.2.1
    let values := returnValueOnComponent G e p q labels invol twice edges invExt
    have atId : values idComponent = 0 := identityValue e p q labels one comm invol twice different
    let keep := Available.filter (fun C => values C ≠ 0)
    have subset : keep ⊆ Available := filter_subset _ _
    let chosen := Base ∪ univ.filter (fun x => comp x ∈ keep)
    have image :
        ({w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} :
          Set (L × A)) = (↑chosen : Set L) ×ˢ Set.univ := by
      ext ⟨x, a⟩
      have point := selectedByRow e p q x labels a comm invol different invExt
      dsimp only at point
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, point,
        mem_coe, chosen, mem_union, mem_filter, mem_univ, true_and, memBase, keep, memAvailable]
      change (_ ∨ values (comp x) ≠ 0) ↔ _
      by_cases closed : p * (q * (p * (q * x))) = x
      · have four := (square x).mpr closed
        simp [closed]
        exact fun nonzero => ⟨fun h => nonzero (h ▸ atId), four⟩
      · simp [closed]
    have measured : count = Nat.card A * chosen.card := by
      rw [← hc, image, Set.ncard_prod, Set.ncard_univ, Set.ncard_coe_finset, Nat.mul_comm]
    have support : keep.card = 0 ∨ Nontrivial A := by
      by_cases empty : keep.card = 0
      · exact Or.inl empty
      · obtain ⟨C, active⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero empty)
        exact Or.inr (nontrivial_of_ne (values C) 0 (mem_filter.mp active).2)
    have exactSize := fourFiberCount comp Available eachFour Base disjoint keep subset
    exact ⟨keep.card, card_le_card subset, support,
      measured.trans (congrArg (Nat.card A * ·) exactSize)⟩
  · rintro ⟨k, bound, support, rfl⟩
    obtain ⟨keep, subset, size⟩ := exists_subset_card_eq bound
    obtain ⟨value, active⟩ : ∃ value : A, k ≠ 0 → value ≠ 0 := by
      rcases support with empty | nontrivial
      · exact ⟨0, fun notEmpty => (notEmpty empty).elim⟩
      · let _ := nontrivial
        obtain ⟨value, nonzero⟩ := exists_ne (0 : A)
        exact ⟨value, fun _ => nonzero⟩
    have nonzero {C : G.ConnectedComponent} (present : C ∈ keep) : value ≠ 0 :=
      active (fun zero => (Nat.ne_of_gt (Finset.card_pos.mpr ⟨C, present⟩)) (size.trans zero))
    let t (C : {C : G.ConnectedComponent // C ≠ comp e}) : A :=
      if C.val ∈ keep then value else 0
    obtain ⟨labels, _, _, _, _, image⟩ :=
      extensionNoncommutingCount G e p q one comm invol twice centreless different hp hq edges t
    refine ⟨labels, ?_⟩
    let _ := extensionMul e labels
    let chosen := Base ∪ univ.filter (fun x => comp x ∈ keep)
    have selected :
        ({x : L | p * (q * (p * (q * x))) ≠ x ∨
          ∃ h : comp x ≠ comp e, t ⟨comp x, h⟩ ≠ 0} : Set L) = (↑chosen : Set L) := by
      ext x
      simp only [Set.mem_ofPred_eq, chosen, mem_coe, mem_union, memBase,
        mem_filter, mem_univ, true_and]
      refine or_congr_right ?_
      constructor
      · rintro ⟨h, active⟩
        by_contra absent
        simp [t, absent] at active
      · intro present
        exact ⟨((memAvailable (comp x)).mp (subset present)).1, by simp [t, present, nonzero present]⟩
    dsimp only at image
    change ({w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} :
      Set (L × A)).ncard = _
    rw [image, selected, Set.ncard_prod, Set.ncard_univ, Set.ncard_coe_finset, Nat.mul_comm]
    rw [fourFiberCount comp Available eachFour Base disjoint keep subset, size]

/-- The attainable labelled switch counts form an arithmetic progression. -/
theorem labelledFixedPivotCountRange {L A : Type*} [Finite L] [Mul L]
    [Finite A] [AddCommGroup A] [Module (ZMod 2) A]
    (G : SimpleGraph L) (e p q : L)
    (one : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (hp : p ≠ e) (hq : q ≠ e) (different : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (count : ℕ) :
    let b := ({x : L | p * (q * (p * (q * x))) ≠ x} : Set L).ncard
    let s := ({C : G.ConnectedComponent | C ≠ G.connectedComponentMk e ∧ C.supp.ncard = 4} :
      Set G.ConnectedComponent).ncard
    (∃ (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b)
      (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
      letI := extensionMul e labels
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧
      label (some (i.succAbove v)) = (q, 0) ∧
      (∀ j a, label (translate valid cover j a) = label (some j) * label a) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard = count) ↔
      ∃ k ≤ s, (k = 0 ∨ Nontrivial A) ∧ count = Nat.card A * (b + 4 * k) := by
  classical
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite G.ConnectedComponent
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  have labelCount (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b)
      (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r)
      (atP : label (some i) = (p, 0))
      (atQ : label (some (i.succAbove v)) = (q, 0))
      (transport : letI := extensionMul e labels
        ∀ j a, label (translate valid cover j a) = label (some j) * label a)
      (leave : ∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) :
      letI := extensionMul e labels
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
        ({w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} :
          Set (L × A)).ncard := by
    let _ := extensionMul e labels
    have pass := SteinerAlternatingSwitches.point_deleted_successful_starts S valid cover i
    obtain ⟨_, matched, relation, states⟩ := pass
    have same : matched = m := funext fun a =>
      (leave a (matched a)).mp ((relation a (matched a)).mpr rfl) |>.symm
    subst matched
    have image := (states v).2.1
    let embed : Fin r → L × A := label ∘ Option.some ∘ i.succAbove
    have inj : Function.Injective embed :=
      label.injective.comp ((Option.some_injective _).comp Fin.succAbove_right_injective)
    have transplant :
        label '' {x | 6 ≤ ((SteinerAlternatingSwitches.pivotGraph valid cover i v).connectedComponentMk
          x).supp.ncard} = {w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} := by
      let matching : Matchings (Option (Fin (r + 1))) := {
        first := translate valid cover i
        second := translate valid cover (i.succAbove v)
        first_involutive := translate_involutive valid cover i
        second_involutive := translate_involutive valid cover (i.succAbove v)
        first_ne_self := translate_ne_self valid cover i
        second_ne_self := translate_ne_self valid cover (i.succAbove v)
        partners_ne := translate_ne_translate valid cover (Fin.succAbove_ne i v).symm
      }
      ext w
      obtain ⟨x, rfl⟩ := label.surjective w
      rw [Equiv.image_eq_preimage_symm]
      simp only [Set.mem_preimage, Equiv.symm_apply_apply, Set.mem_ofPred_eq]
      change 6 ≤ (matching.graph.connectedComponentMk x).supp.ncard ↔ _
      rw [← matching.noncommute_iff_six_le_component x]
      have endpoints :
          label (matching.second (matching.first x)) = (q, 0) * ((p, 0) * label x) ∧
          label (matching.first (matching.second x)) = (p, 0) * ((q, 0) * label x) := by
        change label (translate valid cover (i.succAbove v) (translate valid cover i x)) = _ ∧
          label (translate valid cover i (translate valid cover (i.succAbove v) x)) = _
        simp only [transport, atP, atQ, and_self]
      rw [← endpoints.1, ← endpoints.2, label.injective.ne_iff, ne_comm]
    have exactImage : embed '' {a | SuccessfulStart (pointDeletedFamily S i) m v a} =
        {w : L × A | (q, 0) * ((p, 0) * w) ≠ (p, 0) * ((q, 0) * w)} := by
      change (label ∘ (Option.some ∘ i.succAbove)) '' _ = _
      calc
        _ = label '' ((Option.some ∘ i.succAbove) ''
            {a | SuccessfulStart (pointDeletedFamily S i) m v a}) :=
          (Set.image_image label (Option.some ∘ i.succAbove) _).symm
        _ = _ := (congrArg (Set.image label) image).trans transplant
    rw [← Set.ncard_image_of_injective _ inj, exactImage]
  have range := fixedPivotCountRange (A := A) G e p q one comm invol centreless hp hq
    different edges count
  constructor
  · rintro ⟨labels, r, label, S, valid, cover, i, v, m, _zero, atP, atQ, transport, leave, n⟩
    exact range.mp ⟨labels, (labelCount labels r label S valid cover i v m
      atP atQ transport leave).symm.trans n⟩
  · intro result
    obtain ⟨labels, n⟩ := range.mpr result
    let _ := extensionMul e labels
    obtain ⟨unitExt, commExt, invExt, _⟩ :=
      extensionSteinerAndCentre e labels one comm invol twice centreless
    have differentP : (p, (0 : A)) ≠ (e, 0) := fun h => hp (congrArg Prod.fst h)
    have differentQ : (q, (0 : A)) ≠ (e, 0) := fun h => hq (congrArg Prod.fst h)
    obtain ⟨r, label, zero, locate⟩ := pointedNumbering (e, (0 : A)) ⟨(p, 0), differentP⟩
    obtain ⟨i, v, atP, atQ⟩ := locate (p, 0) (q, 0) differentP differentQ
      (fun h => different (congrArg Prod.fst h))
    obtain ⟨S, valid, cover, transport, byDeleted⟩ :=
      labelledSwitchCount label (by simpa only [zero] using unitExt) commExt invExt
    obtain ⟨m, leave, starts⟩ := byDeleted i
    have measured := (starts v).2
    rw [atP, atQ] at measured
    exact ⟨labels, r, label, S, valid, cover, i, v, m, zero, atP, atQ, transport, leave,
      measured.trans n⟩

end D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
