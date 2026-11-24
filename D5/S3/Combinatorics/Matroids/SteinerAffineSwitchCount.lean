/- GID: D5/S3/Combinatorics/Matroids/SteinerAffineSwitchCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerAffineSwitchCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Label-independent switch counts for binary extensions of affine ternary Steiner loops. -/

import D5.S3.Combinatorics.Matroids.SteinerSwitchSupport

/-! Exact switch counts for normalized binary extensions of affine ternary Steiner loops. -/

open Function
open D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (labelledSwitchCount pointedNumbering steinerSquarePeriod)

namespace D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

/-- Adjoin an identity to the affine Steiner quasigroup. -/
def mul : Option V → Option V → Option V
  | none, b => b
  | a, none => a
  | some a, some b => if a = b then none else some (-a - b)

private def move (p q : V) (x : Option V) : Option V := mul (some p) (mul (some q) x)

private def outside (p q x : V) : Prop := x ≠ p ∧ x ≠ q ∧ x ≠ -p - q

private theorem movesByTranslation (p q x : V) (h : outside p q x) :
    move p q (some x) = some (x + q - p) := by
  rcases h with ⟨_, nq, nthird⟩
  have qp : -q - x ≠ p := by
    intro eq
    apply nthird
    calc
      x = -q - (-q - x) := by abel
      _ = -q - p := by rw [eq]
      _ = -p - q := by abel
  simp only [move, mul, ite_eq_right nq.symm, ite_eq_right qp.symm]
  congr 1
  abel

omit [DecidableEq V] in
private theorem translatesOutside (three : ∀ a : V, a + a = -a) (p q x : V)
    (h : outside p q x) : outside p q (x + q - p) := by
  rcases h with ⟨np, nq, nthird⟩
  refine ⟨?_, ?_, ?_⟩
  · intro equal
    apply nthird
    calc
      x = (x + q - p) + p - q := by abel
      _ = (p + p) - q := by rw [equal]
      _ = -p - q := by rw [three]
  · intro equal
    apply np
    calc
      x = (x + q - p) - q + p := by abel
      _ = p := by rw [equal]; abel
  · intro equal
    apply nq
    calc
      x = (x + q - p) + p - q := by abel
      _ = -(q + q) := by rw [equal]; abel
      _ = q := by rw [three, neg_neg]

private theorem closesAfterThree (three : ∀ a : V, a + a = -a) (p q x : V)
    (h : outside p q x) : (move p q)^[3] (some x) = some x := by
  change move p q (move p q (move p q (some x))) = some x
  rw [movesByTranslation p q x h,
      movesByTranslation p q _ (translatesOutside three p q x h),
      movesByTranslation p q _ (translatesOutside three p q _ (translatesOutside three p q x h))]
  congr 1
  calc
    x + q - p + q - p + q - p = x + ((q + q) + q) - ((p + p) + p) := by abel
    _ = x := by rw [three, three]; abel

private theorem outsidePeriod (three : ∀ a : V, a + a = -a) (p q x : V)
    (different : p ≠ q) (h : outside p q x) : minimalPeriod (move p q) (some x) = 3 := by
  have periodic : IsPeriodicPt (move p q) 3 (some x) := closesAfterThree three p q x h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp periodic.minimalPeriod_dvd with fixed | period
  · exfalso
    have step := minimalPeriod_eq_one_iff_isFixedPt.mp fixed
    change move p q (some x) = some x at step
    rw [movesByTranslation p q x h, Option.some.injEq] at step
    exact different (by
      have same := congrArg (fun a : V => a - x + p) step
      calc
        p = x - x + p := by abel
        _ = (x + q - p) - x + p := same.symm
        _ = q := by abel)
  · exact period

omit [DecidableEq V] in
private theorem thirdNeLeft (three : ∀ a : V, a + a = -a) {a b : V} (h : a ≠ b) :
    -a - b ≠ a := by
  intro equal
  apply h
  symm
  calc
    b = -a - (-a - b) := by abel
    _ = -a - a := by rw [equal]
    _ = -(a + a) := by abel
    _ = a := by rw [three, neg_neg]

omit [DecidableEq V] in
private theorem thirdNeRight (three : ∀ a : V, a + a = -a) {a b : V} (h : a ≠ b) :
    -a - b ≠ b := by
  have swap : -a - b = -b - a := by abel
  rw [swap]
  exact thirdNeLeft three h.symm

private theorem timesComm (x y : Option V) : mul x y = mul y x := by
  cases x <;> cases y
  · rfl
  · rfl
  · rfl
  · rename_i a b
    by_cases h : a = b
    · subst b
      simp [mul]
    · simp only [mul, ite_eq_right h, ite_eq_right (Ne.symm h)]
      congr 1
      abel

private theorem timesInvolutive (three : ∀ a : V, a + a = -a) (x y : Option V) :
    mul x (mul x y) = y := by
  cases x with
  | none => rfl
  | some a =>
    cases y with
    | none => simp [mul]
    | some b =>
      by_cases h : a = b
      · subst b
        simp [mul]
      · simp only [mul, ite_eq_right h, ite_eq_right (thirdNeLeft three h).symm]
        congr 1
        abel

private theorem specialMoves (three : ∀ a : V, a + a = -a) {p q : V} (different : p ≠ q) :
    move p q none = some (-p - q) ∧ move p q (some (-p - q)) = none ∧
    move p q (some p) = some q ∧ move p q (some q) = some p := by
  have qp : -q - p = -p - q := by abel
  have qr : -q - (-p - q) = p := by abel
  have pr : -p - (-p - q) = q := by abel
  have pthird := (thirdNeLeft three different).symm
  have qthird := (thirdNeRight three different).symm
  exact ⟨by simp [move, mul, different],
    by simp [move, mul, qthird, qr],
    by simp [move, mul, different.symm, qp, pthird, pr],
    by simp [move, mul]⟩

private theorem specialPeriods (three : ∀ a : V, a + a = -a) {p q : V}
    (different : p ≠ q) :
    minimalPeriod (move p q) none = 2 ∧ minimalPeriod (move p q) (some (-p - q)) = 2 ∧
      minimalPeriod (move p q) (some p) = 2 ∧ minimalPeriod (move p q) (some q) = 2 := by
  let _ : Mul (Option V) := ⟨mul⟩
  have period (x : Option V) (closed : move p q (move p q x) = x) :
      minimalPeriod (move p q) x = 2 :=
    steinerSquarePeriod timesComm (timesInvolutive three)
      (fun h => different (Option.some.inj h)) closed
  obtain ⟨atUnit, atThird, atP, atQ⟩ := specialMoves three different
  exact ⟨period none (atUnit.symm ▸ atThird), period (some (-p - q)) (atThird.symm ▸ atUnit),
    period (some p) (atP.symm ▸ atQ), period (some q) (atQ.symm ▸ atP)⟩

private theorem failsLeftAssociation (three : ∀ a : V, a + a = -a) {p q x : V}
    (hpq : p ≠ q) (h : outside p q x) :
    mul (some p) (mul (some x) (some q)) ≠
      mul (mul (some p) (some x)) (some q) := by
  obtain ⟨hxp, hxq, hthird⟩ := h
  have houterLeft : p ≠ -x - q := by
    intro hp
    apply hthird
    calc
      x = -(-x - q) - q := by abel
      _ = -p - q := by rw [← hp]
  have houterRight : -p - x ≠ q := by
    intro hq
    apply hthird
    calc
      x = -p - (-p - x) := by abel
      _ = -p - q := by rw [hq]
  simp only [mul, ite_eq_right hxq, ite_eq_right hxp.symm, ite_eq_right houterLeft,
    ite_eq_right houterRight]
  intro equal
  have same := Option.some.inj equal
  apply hpq
  have double : p + p = q + q := by
    calc
      p + p = -(-p - x) - q - x + p + q := by abel
      _ = -p - (-x - q) - x + p + q := by rw [same]
      _ = q + q := by abel
  simpa only [three, neg_inj] using double

private theorem centreless [Fintype V] (three : ∀ a : V, a + a = -a)
    (size : 3 < Fintype.card V) :
    let _ : Mul (Option V) := ⟨mul⟩
    Set.center (Option V) = {none} := by
  let _ : Mul (Option V) := ⟨mul⟩
  ext y
  cases y with
  | none =>
    refine ⟨fun _ => rfl, fun _ => Set.mem_center_iff.mpr ?_⟩
    constructor
    · intro a
      cases a <;> rfl
    · intro a b
      cases a <;> rfl
    · intro a b
      change mul (mul a b) none = mul a (mul b none)
      have right (z : Option V) : mul z none = z := by cases z <;> rfl
      simp only [right]
  | some p =>
    refine ⟨fun central => False.elim ?_, fun h => False.elim (Option.some_ne_none _ h)⟩
    have single : ({p} : Finset V).card < (Finset.univ : Finset V).card := by
      simp only [Finset.card_singleton, Finset.card_univ]
      omega
    obtain ⟨q, _, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card single
    have hqp : q ≠ p := by simpa only [Finset.mem_singleton] using hq
    let line : Finset V := {p, q, -p - q}
    have small : line.card < (Finset.univ : Finset V).card := by
      have bound : line.card ≤ 3 := by
        unfold line
        calc
          _ ≤ ({q, -p - q} : Finset V).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({-p - q} : Finset V).card + 1 + 1 := Nat.add_le_add_right
            (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      simpa only [Finset.card_univ] using lt_of_le_of_lt bound size
    obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card small
    have hx' : outside p q x := by simpa only [outside, line, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hx
    exact failsLeftAssociation three hqp.symm hx'
      ((Set.mem_center_iff.mp central).left_assoc (some x) (some q))


open D5.S3.Combinatorics.Matroids.SteinerReturnDependencies (returnRow)
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (factor)

private theorem squareRowsZero (three : ∀ a : V, a + a = -a) {p q : V}
    (different : p ≠ q) :
    let _ : Mul (Option V) := ⟨mul⟩
    ∀ x : Option V, (move p q)^[2] x = x →
      returnRow none (some p) (some q) x = 0 := by
  let _ : Mul (Option V) := ⟨mul⟩
  classical
  let r := -p - q
  have hp : r ≠ p := thirdNeLeft three different
  have hq : r ≠ q := thirdNeRight three different
  have pq : mul (some p) (some q) = some r := by simp [mul, r, different]
  have qp : mul (some q) (some p) = some r := by rw [timesComm, pq]
  have pr : mul (some p) (some r) = some q := by
    rw [← pq, timesInvolutive three]
  have qr : mul (some q) (some r) = some p := by
    rw [← qp, timesInvolutive three]
  let basis : Set (Option V) → (Set (Option V) →₀ ZMod 2) := fun t => Finsupp.single t 1
  let value := basis ({some p, some q, some r} : Set (Option V))
  let f := factor (none : Option V) basis
  have f0 (a : Option V) : f a none = 0 := by simp [f, factor]
  have fsame (a : Option V) : f a a = 0 := by simp [f, factor]
  have pqf : f (some p) (some q) = value := by
    simp only [f, factor, Option.some_ne_none, Option.some.injEq,
      different, or_self, ite_false]
    change basis {some p, some q, mul (some p) (some q)} = value
    rw [pq]
  have qpf : f (some q) (some p) = value := by
    simp only [f, factor, Option.some_ne_none, Option.some.injEq,
      different.symm, or_self, ite_false]
    change basis {some q, some p, mul (some q) (some p)} = value
    rw [qp, Set.insert_comm]
  have prf : f (some p) (some r) = value := by
    simp only [f, factor, Option.some_ne_none, Option.some.injEq,
      hp.symm, or_self, ite_false]
    change basis {some p, some r, mul (some p) (some r)} = value
    rw [pr, Set.pair_comm]
  have qrf : f (some q) (some r) = value := by
    simp only [f, factor, Option.some_ne_none, Option.some.injEq,
      hq.symm, or_self, ite_false]
    change basis {some q, some r, mul (some q) (some r)} = value
    rw [qr]
    congr 1
    ext point
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have twice : value + value = 0 := by
    simp only [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  have unfoldSquare (x : Option V) (period : minimalPeriod (move p q) x = 2) :
      returnRow none (some p) (some q) x =
        (f (some q) x + f (some p) (mul (some q) x)) +
        (f (some q) (move p q x) + f (some p) (mul (some q) (move p q x))) := by
    unfold returnRow
    change ∑ i ∈ Finset.range (minimalPeriod (move p q) x),
        (f (some q) ((move p q)^[i] x) +
          f (some p) (mul (some q) ((move p q)^[i] x))) = _
    rw [period, Finset.sum_range_succ, Finset.sum_range_one]
    rfl
  obtain ⟨move0, moveR, moveP, moveQ⟩ := specialMoves three different
  obtain ⟨per0, perR, perP, perQ⟩ := specialPeriods three different
  have q0 : mul (some q) none = some q := rfl
  have qq : mul (some q) (some q) = none := by simp [mul]
  change ∀ x : Option V, (move p q)^[2] x = x →
    returnRow none (some p) (some q) x = 0
  intro x returns
  cases x with
  | none => rw [unfoldSquare none per0, move0, q0, qr, f0, pqf, qrf, fsame,
      zero_add, add_zero, twice]
  | some x =>
    by_cases xp : x = p
    · subst x
      rw [unfoldSquare _ perP, moveP, qp, qq, qpf, prf, fsame, f0, twice, add_zero, add_zero]
    by_cases xq : x = q
    · subst x
      rw [unfoldSquare _ perQ, moveQ, qq, qp, fsame, f0, qpf, prf, twice, add_zero, add_zero]
    by_cases xr : x = r
    · subst x
      rw [unfoldSquare _ perR, moveR, qr, q0, qrf, fsame, f0, pqf, add_zero, zero_add, twice]
    have period := outsidePeriod three p q x different ⟨xp, xq, xr⟩
    exact False.elim (by
      have dvd := IsPeriodicPt.minimalPeriod_dvd (show IsPeriodicPt (move p q) 2 (some x) from returns)
      rw [period] at dvd
      exact (by decide : ¬ 3 ∣ 2) dvd)


private theorem twoStepReturnIffOnLine (three : ∀ a : V, a + a = -a) {p q : V}
    (different : p ≠ q) (x : Option V) :
    (move p q)^[2] x = x ↔ x ∈ ({none, some p, some q, some (-p - q)} : Set (Option V)) := by
  let r := -p - q
  let line : Set (Option V) := {none, some p, some q, some r}
  change (move p q)^[2] x = x ↔ x ∈ line
  obtain ⟨move0, moveR, moveP, moveQ⟩ := specialMoves three different
  change move p q (move p q x) = x ↔ x ∈ line
  cases x with
  | none => simp [move0, moveR, line]
  | some x =>
    by_cases xp : x = p
    · subst x
      simp [moveP, moveQ, line]
    by_cases xq : x = q
    · subst x
      simp [moveQ, moveP, line]
    by_cases xr : x = r
    · subst x
      have closed : move p q (move p q (some r)) = some r := by rw [moveR, move0]
      simp [closed, line]
    have notPeriod : move p q (move p q (some x)) ≠ some x := by
      intro eq
      have divides := IsPeriodicPt.minimalPeriod_dvd
        (show IsPeriodicPt (move p q) 2 (some x) from eq)
      rw [outsidePeriod three p q x different ⟨xp, xq, xr⟩] at divides
      exact (by decide : ¬ 3 ∣ 2) divides
    simp [notPeriod, line, xp, xq, xr]

omit [DecidableEq V] in
private theorem complementCount [Fintype V] (three : ∀ a : V, a + a = -a) {p q : V}
    (different : p ≠ q) :
    ({none, some p, some q, some (-p - q)} : Set (Option V))ᶜ.ncard =
      Fintype.card V - 3 := by
  classical
  let r := -p - q
  have nline : ({none, some p, some q, some r} : Set (Option V)).ncard = 4 := by
    have hp := thirdNeLeft three different
    have hq := thirdNeRight three different
    have h0 : (none : Option V) ∉ ({some p, some q, some r} : Set (Option V)) := by simp
    have hp0 : some p ∉ ({some q, some r} : Set (Option V)) := by
      simp [different, show p ≠ r from hp.symm]
    change ({none, some p, some q, some r} : Set (Option V)).ncard = 4
    rw [Set.ncard_insert_of_notMem h0, Set.ncard_insert_of_notMem hp0,
      Set.ncard_pair (show some q ≠ some r from fun h => hq (Option.some.inj h.symm))]
  rw [Set.ncard_compl, nline, Nat.card_eq_fintype_card, Fintype.card_option]
  omega

open D5.S3.Combinatorics.Matroids.SteinerSwitchSupport (selectedByRow)
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
  (extensionMul extensionSteinerAndCentre)
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap (Covered Uncovered)
open D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations (translate)
open D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch (pointDeletedFamily)
open D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches (SuccessfulStart)

/-- Every binary labelling gives the same count for all distinct affine pivot pairs. -/
theorem labelledAffineSwitchCount {A : Type*} [Fintype V] [Finite A]
    [AddCommGroup A] [Module (ZMod 2) A]
    (three : ∀ a : V, a + a = -a) (size : 3 < Fintype.card V)
    (labels : Set (Option V) → A) :
    letI : Mul (Option V) := ⟨mul⟩
    letI := extensionMul (none : Option V) labels
    ∃ (r : ℕ) (label : Option (Fin (r + 1)) ≃ Option V × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      label none = (none, 0) ∧ Set.center (Option V × A) = {x | x.1 = none} ∧
      (∀ i a, label (translate valid cover i a) = label (some i) * label a) ∧
      ∀ p q : V, p ≠ q → ∃ (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
        label (some i) = (some p, 0) ∧ label (some (i.succAbove v)) = (some q, 0) ∧
        (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
        (label ∘ Option.some ∘ i.succAbove) ''
          {a | SuccessfulStart (pointDeletedFamily S i) m v a} =
          ({none, some p, some q, some (-p - q)} : Set (Option V))ᶜ ×ˢ Set.univ ∧
        ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
          Nat.card A * (Fintype.card V - 3) := by
  let _ : Mul (Option V) := ⟨mul⟩
  let _ := extensionMul (none : Option V) labels
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  obtain ⟨identity, comm, invol, centre⟩ :=
    extensionSteinerAndCentre (none : Option V) labels (fun _ => rfl)
      timesComm (timesInvolutive three) twice (centreless three size)
  obtain ⟨r, label, zero, locate⟩ :=
    pointedNumbering (none, (0 : A)) ⟨(some (0 : V), 0), by simp⟩
  obtain ⟨S, valid, cover, transport, byDeleted⟩ :=
    labelledSwitchCount label (by simpa only [zero] using identity) comm invol
  refine ⟨r, label, S, valid, cover, zero, centre, transport, fun p q different => ?_⟩
  obtain ⟨i, v, hi, hv⟩ := locate (some p, 0) (some q, 0) (by simp) (by simp)
    (fun eq => different (Option.some.inj (congrArg Prod.fst eq)))
  obtain ⟨m, leave, byStart⟩ := byDeleted i
  have image := (byStart v).1
  have count := (byStart v).2
  rw [hi, hv] at image count
  have fibres :
      ({y : Option V × A | (some q, 0) * ((some p, 0) * y) ≠
        (some p, 0) * ((some q, 0) * y)} : Set (Option V × A)) =
        ({none, some p, some q, some (-p - q)} : Set (Option V))ᶜ ×ˢ Set.univ := by
    ext ⟨x, a⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, Set.mem_compl_iff]
    have selection := selectedByRow none (some p) (some q) x labels a timesComm
      (timesInvolutive three) (fun h => different (Option.some.inj h)) invol
    dsimp only at selection
    rw [selection]
    change (move p q (move p q x) ≠ x ∨
      Finsupp.linearCombination (ZMod 2) labels (returnRow none (some p) (some q) x) ≠ 0) ↔ _
    have onLine := twoStepReturnIffOnLine three different x
    by_cases returns : move p q (move p q x) = x
    · simp [returns, onLine.mp returns, squareRowsZero three different x returns]
    · exact ⟨fun _ h => returns (onLine.mpr h), fun _ => Or.inl returns⟩
  rw [fibres] at image count
  refine ⟨i, v, m, hi, hv, leave, image, count.trans ?_⟩
  rw [Set.ncard_prod, Set.ncard_univ, complementCount three different, Nat.mul_comm]

end D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount
