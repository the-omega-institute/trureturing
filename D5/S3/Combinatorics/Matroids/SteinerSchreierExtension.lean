/- GID: D5/S3/Combinatorics/Matroids/SteinerSchreierExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSchreierExtension
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Arbitrary component returns are realized by Steiner triple labels. -/

/-
realizeSchreierReturns
  proof_shape: content
  admission_basis: escape-witness
  escape_witness: different edges of the alternating circuits outside the
    identity component use pairwise distinct Steiner triples. This permits
    independent component sums from one assignment of triple labels.
  Direct frozen dependency: InvolutionOrbitSplit.component_split.
-/

import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Mathlib.Algebra.Group.Center
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto

/-! # Central extensions of Steiner loops with prescribed returns -/

namespace D5.S3.Combinatorics.Matroids.SteinerSchreierExtension

open Function Set
open scoped BigOperators

private def triple {L : Type*} [Mul L] (p x : L) : Set L :=
  {p, x, p * x}

/-- Equality of labels of two edges through the same pivot identifies their unordered ends. -/
private theorem samePivotTriple {L : Type*} [Mul L] {p x y : L}
    (hp : ∀ u : L, p * (p * u) = u) (hx : x ≠ p) :
    triple p x = triple p y ↔ x = y ∨ x = p * y := by
  constructor
  · intro h
    have mem : x ∈ triple p y := by
      rw [← h]
      simp [triple]
    simpa [triple, hx] using mem
  · rintro (rfl | rfl)
    · rfl
    · change ({p, p * y, p * (p * y)} : Set L) = {p, y, p * y}
      rw [hp y]
      ext w
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto

/-- Different pivots can use the same triple only on the edges between their special vertices. -/
private theorem distinctPivotTriple {L : Type*} [Mul L] {p q x y : L}
    (hp : ∀ u : L, p * (p * u) = u) (hpq : p ≠ q)
    (hxq : x ≠ q) (hxpq : x ≠ p * q) :
    triple p x ≠ triple q y := by
  intro h
  have mem : q ∈ triple p x := by
    rw [h]
    simp [triple]
  have members : q = p ∨ q = x ∨ q = p * x := by
    simpa [triple] using mem
  rcases members with e | e | e
  · exact hpq e.symm
  · exact hxq e.symm
  · have swapped := congrArg (p * ·) e
    change p * q = p * (p * x) at swapped
    rw [hp x] at swapped
    exact hxpq swapped.symm

noncomputable def factor {L A : Type*} [Mul L] [Zero A]
    (e : L) (labels : Set L → A) (p x : L) : A := by
  classical
  exact if p = e ∨ x = e ∨ p = x then 0 else labels (triple p x)

private noncomputable def pairedLift {L A : Type*} [Mul L] [AddCommMonoid A]
    (e : L) (labels : Set L → A) (p q : L) (x : L × A) : L × A :=
  (p * (q * x.1), x.2 + (factor e labels q x.1 + factor e labels p (q * x.1)))

/-- After any number of rounds, the fibre coordinate is the sum of their two edge labels. -/
theorem pairedLiftIterate {L A : Type*} [Mul L] [AddCommMonoid A]
    (e : L) (labels : Set L → A) (p q x : L) (a : A) (n : ℕ) :
    let step : L → L := fun y => p * (q * y)
    (pairedLift e labels p q)^[n] (x, a) =
      (step^[n] x,
        a + ∑ i ∈ Finset.range n,
          (factor e labels q (step^[i] x) + factor e labels p (q * (step^[i] x)))) := by
  let step : L → L := fun y => p * (q * y)
  change (pairedLift e labels p q)^[n] (x, a) = (step^[n] x, a + _)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply', Finset.sum_range_succ]
    simp only [pairedLift, add_assoc, step]


open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

/-- The two colours along a complete product orbit use pairwise distinct triples. -/
private theorem circuitTripleInjective {L : Type*} [Finite L] [Mul L] (p q x : L)
    (hp : ∀ y : L, p * (p * y) = y) (hq : ∀ y : L, q * (q * y) = y)
    (hpFree : ∀ y : L, p * y ≠ y) (hqFree : ∀ y : L, q * y ≠ y)
    (hpq : p ≠ q)
    (outside : ∀ (n : ℕ) (y : L),
      (y = (fun u => p * (q * u))^[n] x ∨ y = q * (fun u => p * (q * u))^[n] x) →
      y ≠ p ∧ y ≠ q ∧ y ≠ p * q) :
    let step : L → L := fun y => p * (q * y)
    let k := minimalPeriod step x
    Injective (fun (b : Bool × Fin k) =>
      if b.1 then triple p (q * step^[b.2.val] x) else triple q (step^[b.2.val] x)) := by
  let step : L → L := fun y => p * (q * y)
  let k := minimalPeriod step x
  let P : Equiv.Perm L := ⟨(p * ·), (p * ·), hp, hp⟩
  let Q : Equiv.Perm L := ⟨(q * ·), (q * ·), hq, hq⟩
  have comp : (⇑(P * Q) : L → L) = step := by
    funext y
    exact Equiv.Perm.mul_apply P Q y
  let R := RotationOrbit (P * Q) x
  let T := RotationOrbit (P * Q) (P x)
  have split := component_split P Q hp hq hpFree hqFree x
  have inFirst (i : ℕ) : step^[i] x ∈ R := by
    refine ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow, comp]
  have inSecond (i : ℕ) : q * step^[i] x ∈ T := by
    change q * step^[i] x ∈ RotationOrbit (P * Q) (P x)
    rw [← split.2.2.2.2.2]
    exact ⟨_, inFirst i, rfl⟩
  have distinctOrbits : Disjoint R T := split.1
  have indexInj : Injective (fun i : Fin k => step^[i.val] x) := by
    intro i j h
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h)
  have qTripleInj : Injective (fun i : Fin k => triple q (step^[i.val] x)) := by
    intro i j h
    have point := (outside i.val (step^[i.val] x) (Or.inl rfl)).2.1
    rcases (samePivotTriple hq point).mp h with eq | eq
    · exact indexInj eq
    · exact (Set.disjoint_left.mp distinctOrbits (inFirst i) (eq ▸ inSecond j)).elim
  have pTripleInj : Injective (fun i : Fin k => triple p (q * step^[i.val] x)) := by
    intro i j h
    have point := (outside i.val (q * step^[i.val] x) (Or.inr rfl)).1
    rcases (samePivotTriple hp point).mp h with eq | eq
    · exact indexInj ((show Injective (q * ·) from Function.Involutive.injective hq) eq)
    · have later : p * (q * step^[j.val] x) ∈ R := by
        change step (step^[j.val] x) ∈ R
        exact (iterate_succ_apply' step j.val x) ▸ inFirst (j.val + 1)
      exact (Set.disjoint_left.mp distinctOrbits later (eq ▸ inSecond i)).elim
  have cross (i j : Fin k) :
      triple p (q * step^[i.val] x) ≠ triple q (step^[j.val] x) := by
    have hs := outside i.val (q * step^[i.val] x) (Or.inr rfl)
    exact distinctPivotTriple hp hpq hs.2.1 hs.2.2
  change Injective (fun b : Bool × Fin k =>
    if b.1 then triple p (q * step^[b.2.val] x) else triple q (step^[b.2.val] x))
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  cases a <;> cases b
  · exact congrArg (Prod.mk false) (qTripleInj h)
  · exact (cross j i h.symm).elim
  · exact (cross i j h).elim
  · exact congrArg (Prod.mk true) (pTripleInj h)


open SimpleGraph

/-- Triples used by the circuits of distinct components are distinct. -/
private theorem allCircuitTriplesInjective {L I : Type*} [Finite L] [Mul L]
    (G : SimpleGraph L) (e p q : L) (rep : I → L)
    (hp : ∀ y : L, p * (p * y) = y) (hq : ∀ y : L, q * (q * y) = y)
    (hpFree : ∀ y : L, p * y ≠ y) (hqFree : ∀ y : L, q * y ≠ y)
    (hpq : p ≠ q) (hpe : p * e = p) (hqe : q * e = q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (notSpecial : ∀ i : I, ¬G.Reachable e (rep i))
    (distinct : ∀ i j : I, G.Reachable (rep i) (rep j) → i = j) :
    let step : L → L := fun y => p * (q * y)
    let length (i : I) := minimalPeriod step (rep i)
    Injective (fun (b : (i : I) × Bool × Fin (length i)) =>
      if b.2.1 then triple p (q * step^[b.2.2.val] (rep b.1))
      else triple q (step^[b.2.2.val] (rep b.1))) := by
  let step : L → L := fun y => p * (q * y)
  let length (i : I) := minimalPeriod step (rep i)
  have reachedP (u : L) : G.Reachable u (p * u) :=
    ((edges _ _).2 (Or.inl rfl)).reachable
  have reachedQ (u : L) : G.Reachable u (q * u) :=
    ((edges _ _).2 (Or.inr rfl)).reachable
  have reachedEven (i : I) (n : ℕ) : G.Reachable (rep i) (step^[n] (rep i)) := by
    induction n with
    | zero => exact Reachable.rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact ih.trans ((reachedQ _).trans (reachedP _))
  have reachedOdd (i : I) (n : ℕ) : G.Reachable (rep i) (q * step^[n] (rep i)) :=
    (reachedEven i n).trans (reachedQ _)
  have reachedIdentityP : G.Reachable e p := hpe ▸ reachedP e
  have reachedIdentityQ : G.Reachable e q := hqe ▸ reachedQ e
  have reachedIdentityPQ : G.Reachable e (p * q) :=
    reachedIdentityQ.trans (reachedP q)
  have outside (i : I) (n : ℕ) (y : L)
      (path : y = step^[n] (rep i) ∨ y = q * step^[n] (rep i)) :
      y ≠ p ∧ y ≠ q ∧ y ≠ p * q := by
    have walk : G.Reachable (rep i) y := by
      rcases path with rfl | rfl
      · exact reachedEven i n
      · exact reachedOdd i n
    refine ⟨fun eq => ?_, fun eq => ?_, fun eq => ?_⟩
    · exact notSpecial i (reachedIdentityP.trans (eq ▸ walk.symm))
    · exact notSpecial i (reachedIdentityQ.trans (eq ▸ walk.symm))
    · exact notSpecial i (reachedIdentityPQ.trans (eq ▸ walk.symm))
  have joined {a x y : L} (ha : ∀ u : L, a * (a * u) = u)
      (path : ∀ z : L, G.Reachable z (a * z)) (hx : x ≠ a)
      (eq : triple a x = triple a y) : G.Reachable x y := by
    rcases (samePivotTriple ha hx).mp eq with rfl | rfl
    · exact Reachable.rfl
    · exact (path y).symm
  have indices {i j : I} (u : Fin (length i)) (v : Fin (length j)) (a b : Bool)
      (eq : (if a then triple p (q * step^[u.val] (rep i))
                 else triple q (step^[u.val] (rep i))) =
            (if b then triple p (q * step^[v.val] (rep j))
                 else triple q (step^[v.val] (rep j)))) : i = j := by
    have qOut := (outside i u.val (step^[u.val] (rep i)) (Or.inl rfl)).2.1
    have pOut := outside i u.val (q * step^[u.val] (rep i)) (Or.inr rfl)
    have pOut' := outside j v.val (q * step^[v.val] (rep j)) (Or.inr rfl)
    cases a <;> cases b
    · exact distinct i j ((reachedEven i u.val).trans
        ((joined hq reachedQ qOut eq).trans (reachedEven j v.val).symm))
    · exact (distinctPivotTriple hp hpq pOut'.2.1 pOut'.2.2 eq.symm).elim
    · exact (distinctPivotTriple hp hpq pOut.2.1 pOut.2.2 eq).elim
    · exact distinct i j ((reachedOdd i u.val).trans
        ((joined hp reachedP pOut.1 eq).trans (reachedOdd j v.val).symm))
  change Injective (fun (b : (i : I) × Bool × Fin (length i)) =>
    if b.2.1 then triple p (q * step^[b.2.2.val] (rep b.1))
    else triple q (step^[b.2.2.val] (rep b.1)))
  rintro ⟨i, a, u⟩ ⟨j, b, v⟩ h
  have hij := indices u v a b h
  subst j
  have same : (a, u) = (b, v) :=
    circuitTripleInjective p q (rep i) hp hq hpFree hqFree hpq (outside i) h
  exact congrArg (Sigma.mk i) same


/-- Every chosen representative outside the identity component has its prescribed return. -/
private theorem prescribeRepresentativeReturns {L I A : Type*} [Finite L] [Mul L]
    [AddCommMonoid A] (G : SimpleGraph L) (e p q : L) (rep : I → L) (t : I → A)
    (hp : ∀ y : L, p * (p * y) = y) (hq : ∀ y : L, q * (q * y) = y)
    (hpFree : ∀ y : L, p * y ≠ y) (hqFree : ∀ y : L, q * y ≠ y)
    (hpq : p ≠ q) (hpe : p * e = p) (hqe : q * e = q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (notSpecial : ∀ i : I, ¬G.Reachable e (rep i))
    (distinct : ∀ i j : I, G.Reachable (rep i) (rep j) → i = j) :
    let step : L → L := fun y => p * (q * y)
    let length (i : I) := minimalPeriod step (rep i)
    ∃ labels : Set L → A, ∀ (i : I) (u : A),
      (pairedLift e labels p q)^[length i] (rep i, u) = (rep i, u + t i) := by
  classical
  let step : L → L := fun y => p * (q * y)
  let length (i : I) := minimalPeriod step (rep i)
  let tag (b : (i : I) × Bool × Fin (length i)) : Set L :=
    if b.2.1 then triple p (q * step^[b.2.2.val] (rep b.1))
    else triple q (step^[b.2.2.val] (rep b.1))
  let value (b : (i : I) × Bool × Fin (length i)) : A :=
    if b.2.1 = true ∧ b.2.2.val = 0 then t b.1 else 0
  let labels := Function.extend tag value (fun _ => 0)
  have htag : Injective tag :=
    allCircuitTriplesInjective G e p q rep hp hq hpFree hqFree hpq hpe hqe
      edges notSpecial distinct
  have reachedP (u : L) : G.Reachable u (p * u) :=
    ((edges _ _).2 (Or.inl rfl)).reachable
  have reachedQ (u : L) : G.Reachable u (q * u) :=
    ((edges _ _).2 (Or.inr rfl)).reachable
  have reachedEven (i : I) (n : ℕ) : G.Reachable (rep i) (step^[n] (rep i)) := by
    induction n with
    | zero => exact Reachable.rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact ih.trans ((reachedQ _).trans (reachedP _))
  have noE {i : I} {y : L} (h : G.Reachable (rep i) y) : y ≠ e := by
    rintro rfl
    exact notSpecial i h.symm
  have noP {i : I} {y : L} (h : G.Reachable (rep i) y) : p ≠ y := by
    rintro rfl
    exact notSpecial i ((show G.Reachable e p from hpe ▸ reachedP e).trans h.symm)
  have noQ {i : I} {y : L} (h : G.Reachable (rep i) y) : q ≠ y := by
    rintro rfl
    exact notSpecial i ((show G.Reachable e q from hqe ▸ reachedQ e).trans h.symm)
  have pNeE : p ≠ e := (hpe ▸ hpFree e)
  have qNeE : q ≠ e := (hqe ▸ hqFree e)
  have row (i : I) (j : ℕ) (hj : j < length i) :
      factor e labels q (step^[j] (rep i)) +
        factor e labels p (q * step^[j] (rep i)) = if j = 0 then t i else 0 := by
    let index : Fin (length i) := ⟨j, hj⟩
    have hQ := htag.extend_apply value (fun _ => 0) ⟨i, false, index⟩
    have hP : labels (triple p (q * step^[j] (rep i))) = (if j = 0 then t i else 0) := by
      simpa [labels, tag, value, index] using
        htag.extend_apply value (fun _ => 0) ⟨i, true, index⟩
    have hEven := reachedEven i j
    have hOdd := hEven.trans (reachedQ _)
    change labels (triple q (step^[j] (rep i))) = 0 at hQ
    simp only [factor, qNeE, pNeE, noE hEven, noE hOdd, noQ hEven, noP hOdd,
      or_false, ite_false, hQ, hP, zero_add]
  have positive (i : I) : 0 < length i :=
    minimalPeriod_pos_of_mem_periodicPts
      (((show Injective (p * ·) from Function.Involutive.injective hp).comp
        (show Injective (q * ·) from Function.Involutive.injective hq)).mem_periodicPts (rep i))
  use labels
  intro i u
  have result := pairedLiftIterate e labels p q (rep i) u (length i)
  change (pairedLift e labels p q)^[length i] (rep i, u) =
      (step^[length i] (rep i), u + _) at result
  rw [result]
  have total : (∑ j ∈ Finset.range (length i),
      (factor e labels q (step^[j] (rep i)) +
        factor e labels p (q * step^[j] (rep i)))) = t i := by
    trans ∑ j ∈ Finset.range (length i), if j = 0 then t i else 0
    · exact Finset.sum_congr rfl fun j hj => row i j (Finset.mem_range.mp hj)
    · simp [positive i]
  rw [total, isPeriodicPt_minimalPeriod step (rep i)]


/-- The multiplication on the central extension given by labels on triples. -/
@[instance_reducible]
noncomputable def extensionMul {L A : Type*} [Mul L] [AddCommMonoid A]
    (e : L) (labels : Set L → A) : Mul (L × A) where
  mul a b := (a.1 * b.1, a.2 + b.2 + factor e labels a.1 b.1)

private theorem factor_symm {L A : Type*} [Mul L] [Zero A]
    (e : L) (labels : Set L → A) (hcomm : ∀ x y : L, x * y = y * x) (p x : L) :
    factor e labels p x = factor e labels x p := by
  classical
  have branch : (p = e ∨ x = e ∨ p = x) ↔ (x = e ∨ p = e ∨ x = p) := by
    simp only [eq_comm (a := p) (b := x)]
    tauto
  have same : triple p x = triple x p := by
    unfold triple
    rw [hcomm p x]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  simp only [factor, branch, same]

private theorem factor_invariant {L A : Type*} [Mul L] [Zero A]
    (e : L) (labels : Set L → A) (rightUnit : ∀ x : L, x * e = x)
    (invol : ∀ x y : L, x * (x * y) = y) (p x : L) :
    factor e labels p (p * x) = factor e labels p x := by
  classical
  have square : p * p = e := by
    have h := invol p e
    rwa [rightUnit] at h
  have inj : Injective (p * ·) := Function.Involutive.injective (invol p)
  have toIdentity : p * x = e ↔ p = x := by
    rw [← square]
    exact inj.eq_iff.trans eq_comm
  have fixedPivot : p = p * x ↔ x = e := by
    constructor
    · intro h
      exact (inj ((rightUnit p).trans h)).symm
    · rintro rfl
      exact (rightUnit p).symm
  have branch : (p = e ∨ p * x = e ∨ p = p * x) ↔ (p = e ∨ x = e ∨ p = x) := by
    rw [toIdentity, fixedPivot]
    tauto
  have same : triple p (p * x) = triple p x := by
    unfold triple
    rw [invol p x]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  simp only [factor, branch, same]

theorem extensionSteinerAndCentre {L A : Type*} [Mul L] [AddCommGroup A]
    (e : L) (labels : Set L → A) (unit : ∀ x : L, e * x = x)
    (comm : ∀ x y : L, x * y = y * x) (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0) (centreless : Set.center L = {e}) :
    letI := extensionMul e labels
    (∀ x : L × A, (e, 0) * x = x) ∧
    (∀ x y : L × A, x * y = y * x) ∧
    (∀ x y : L × A, x * (x * y) = y) ∧
    Set.center (L × A) = {x | x.1 = e} := by
  classical
  letI := extensionMul e labels
  have rightUnit (v : L) : v * e = v := (comm v e).trans (unit v)
  have leftZero (v : L) : factor e labels e v = 0 := by simp [factor]
  have rightZero (v : L) : factor e labels v e = 0 :=
    (factor_symm e labels comm v e).trans (leftZero v)
  have commExt (x y : L × A) : x * y = y * x := by
    apply Prod.ext
    · exact comm _ _
    · change x.2 + y.2 + factor e labels x.1 y.1 =
        y.2 + x.2 + factor e labels y.1 x.1
      rw [factor_symm e labels comm x.1 y.1, add_comm x.2 y.2]
  refine ⟨?_, commExt, ?_, ?_⟩
  · intro x
    apply Prod.ext
    · exact unit _
    · change 0 + x.2 + factor e labels e x.1 = x.2
      simp [leftZero]
  · intro x y
    apply Prod.ext
    · exact invol _ _
    · change x.2 + (x.2 + y.2 + factor e labels x.1 y.1) +
          factor e labels x.1 (x.1 * y.1) = y.2
      rw [factor_invariant e labels rightUnit invol]
      calc
        _ = y.2 + (x.2 + x.2) + (factor e labels x.1 y.1 + factor e labels x.1 y.1) := by abel
        _ = y.2 := by rw [twice, twice, add_zero, add_zero]
  · ext x
    constructor
    · intro h
      let proj : (L × A) →ₙ* L := ⟨Prod.fst, fun _ _ => rfl⟩
      have hs : Surjective proj := fun y => ⟨(y, 0), rfl⟩
      have z := Set.mem_center_iff.mpr ((Set.mem_center_iff.mp h).map (f := proj) hs)
      rw [centreless] at z
      exact z
    · rcases x with ⟨u,a⟩
      intro hu
      change u = e at hu
      subst u
      refine ⟨commExt (e,a), ?_, ?_⟩
      · intro x y
        apply Prod.ext
        · change e * (x.1 * y.1) = (e * x.1) * y.1
          rw [unit, unit]
        · change a + (x.2 + y.2 + factor e labels x.1 y.1) + factor e labels e (x.1 * y.1) =
            a + x.2 + factor e labels e x.1 + y.2 + factor e labels (e * x.1) y.1
          simp only [leftZero, unit, add_zero, add_assoc]
      · intro x y
        apply Prod.ext
        · change (x.1 * y.1) * e = x.1 * (y.1 * e)
          rw [rightUnit, rightUnit]
        · change x.2 + y.2 + factor e labels x.1 y.1 + a + factor e labels (x.1 * y.1) e =
            x.2 + (y.2 + a + factor e labels y.1 e) + factor e labels x.1 (y.1 * e)
          simp only [rightZero, rightUnit, add_zero]
          abel


/-- The product of the two lifted pivots is the two-step fibre map. -/
theorem pairedLift_eq_mul {L A : Type*} [Mul L] [AddCommMonoid A]
    (e : L) (labels : Set L → A) (p q : L) :
    letI := extensionMul e labels
    pairedLift e labels p q = (fun x : L × A => (p, 0) * ((q, 0) * x)) := by
  letI := extensionMul e labels
  funext x
  apply Prod.ext
  · rfl
  · change x.2 + (factor e labels q x.1 + factor e labels p (q * x.1)) =
      0 + (0 + x.2 + factor e labels q x.1) + factor e labels p (q * x.1)
    simp [add_assoc]

theorem identityReturn {L A : Type*} [Mul L] [AddCommGroup A]
    (e p q : L) (labels : Set L → A) (a : A)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ u : A, u + u = 0) (hpq : p ≠ q) :
    let step : L → L := fun y => p * (q * y)
    minimalPeriod step e = 2 ∧ (pairedLift e labels p q)^[2] (e, a) = (e, a) := by
  let step : L → L := fun y => p * (q * y)
  have rightUnit (x : L) : x * e = x := (comm x e).trans (unit x)
  have square (x : L) : x * x = e := by
    simpa only [rightUnit] using invol x e
  have first : step e = p * q := by
    change p * (q * e) = _
    rw [rightUnit]
  have qpr : q * (p * q) = p := by
    rw [comm p q, invol]
  have second : step (p * q) = e := by
    change p * (q * (p * q)) = e
    rw [qpr, square]
  have two : step^[2] e = e := by
    rw [iterate_succ_apply', iterate_one, first, second]
  have noFixed : step e ≠ e := by
    rw [first, ← square p]
    exact ((show Injective (p * ·) from Function.Involutive.injective (invol p)).ne hpq.symm)
  have notOne : minimalPeriod step e ≠ 1 := by
    intro h
    have periodic := isPeriodicPt_minimalPeriod step e
    rw [h] at periodic
    exact noFixed periodic
  have period : minimalPeriod step e = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp
      ((show IsPeriodicPt step 2 e from two).minimalPeriod_dvd)).resolve_left notOne
  refine ⟨period, ?_⟩
  have factorUnit (x : L) : factor e labels x e = 0 := by simp [factor]
  have factorSquare (x : L) : factor e labels x x = 0 := by simp [factor]
  have matching : factor e labels q (p * q) = factor e labels p q := by
    rw [comm p q, factor_invariant e labels rightUnit invol, factor_symm e labels comm q p]
  have h := pairedLiftIterate e labels p q e a 2
  change (pairedLift e labels p q)^[2] (e, a) =
    (step^[2] e, a + ∑ i ∈ Finset.range 2,
      (factor e labels q (step^[i] e) + factor e labels p (q * step^[i] e))) at h
  rw [h, two]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iterate_zero, id_eq,
    iterate_one, first, qpr, rightUnit, factorUnit, factorSquare, add_zero, matching, twice]


private theorem iterateReflection {X : Type*} (f T : X → X)
    (reflect : ∀ x, f (T (f x)) = T x) (n : ℕ) (x : X) :
    f^[n] (T (f^[n] x)) = T x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply' f n x, reflect, ih]

private theorem periodAtReflection {X : Type*} (f T : X → X)
    (reflect : ∀ x, f (T (f x)) = T x) (hT : Involutive T) (x : X) :
    minimalPeriod f (T x) = minimalPeriod f x := by
  have divides (y : X) : minimalPeriod f (T y) ∣ minimalPeriod f y := by
    have h := iterateReflection f T reflect (minimalPeriod f y) y
    rw [show f^[minimalPeriod f y] y = y from isPeriodicPt_minimalPeriod f y] at h
    exact (show IsPeriodicPt f (minimalPeriod f y) (T y) from h).minimalPeriod_dvd
  refine Nat.dvd_antisymm (divides x) ?_
  simpa only [hT x] using divides (T x)

private theorem returnAlongReflection {L A : Type*} [AddCommGroup A]
    (g T : L → L) (f : L × A → L × A) (offset : L → A)
    (reflectG : ∀ x, g (T (g x)) = T x) (hT : Involutive T)
    (reflectF : ∀ w, f ((T (f w).1, (f w).2 + offset (f w).1)) =
        (T w.1, w.2 + offset w.1))
    (twice : ∀ a : A, a + a = 0) {x : L} {t : A}
    (returns : ∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a + t)) :
    ∀ b : A, f^[minimalPeriod g (T x)] (T x, b) = (T x, b + t) := by
  intro b
  rw [periodAtReflection g T reflectG hT]
  let lift (w : L × A) : L × A := (T w.1, w.2 + offset w.1)
  let a := b - offset x
  have shift : f^[minimalPeriod g x] (x, a + t) = (x, a) := by
    rw [returns, add_assoc, twice, add_zero]
  have h := iterateReflection f lift reflectF (minimalPeriod g x) (x, a + t)
  rw [shift] at h
  have left : lift (x, a) = (T x, b) := by simp [lift, a]
  have right : lift (x, a + t) = (T x, b + t) := by
    apply Prod.ext
    · rfl
    · change b - offset x + t + offset x = b + t
      abel
  rwa [left, right] at h

theorem returnAlongComponent {L A : Type*} [Mul L] [AddCommGroup A]
    (G : SimpleGraph L) (e p q : L) (labels : Set L → A)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (involExt : letI := extensionMul e labels
      ∀ x y : L × A, x * (x * y) = y)
    {x y : L} (path : G.Reachable x y) (t : A) :
    letI := extensionMul e labels
    let g : L → L := fun u => p * (q * u)
    let f : L × A → L × A := fun u => (p, 0) * ((q, 0) * u)
    (∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a + t)) →
      ∀ a : A, f^[minimalPeriod g y] (y, a) = (y, a + t) := by
  letI := extensionMul e labels
  let g : L → L := fun u => p * (q * u)
  let f : L × A → L × A := fun u => (p, 0) * ((q, 0) * u)
  change (∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a + t)) →
    ∀ a : A, f^[minimalPeriod g y] (y, a) = (y, a + t)
  intro ret
  have multiply (z : L) (u : L × A) :
      (z, 0) * u = (z * u.1, u.2 + factor e labels z u.1) := by
    apply Prod.ext
    · rfl
    · exact congrArg (· + factor e labels z u.1) (zero_add _)
  have reflectsP (u : L) : g (p * g u) = p * u := by
    change p * (q * (p * (p * (q * u)))) = p * u
    rw [invol p, invol q]
  have reflectsQ (u : L) : g (q * g u) = q * u := by
    change p * (q * (q * (p * (q * u)))) = q * u
    rw [invol q, invol p]
  have reflectsLiftP (u : L × A) : f ((p, 0) * f u) = (p, 0) * u := by
    change (p, (0 : A)) * ((q, (0 : A)) * ((p, (0 : A)) *
      ((p, (0 : A)) * ((q, (0 : A)) * u)))) = (p, (0 : A)) * u
    rw [involExt (p, 0), involExt (q, 0)]
  have reflectsLiftQ (u : L × A) : f ((q, 0) * f u) = (q, 0) * u := by
    change (p, (0 : A)) * ((q, (0 : A)) * ((q, (0 : A)) *
      ((p, (0 : A)) * ((q, (0 : A)) * u)))) = (q, (0 : A)) * u
    rw [involExt (q, 0), involExt (p, 0)]
  have reflectPair (z : L) (h : ∀ u, f ((z, 0) * f u) = (z, 0) * u) (u : L × A) :
      f ((z * (f u).1, (f u).2 + factor e labels z (f u).1)) =
         (z * u.1, u.2 + factor e labels z u.1) := by
    simpa only [multiply] using h u
  rw [reachable_iff_reflTransGen] at path
  induction path with
  | refl => exact ret
  | @tail u v _ edge ih =>
    rcases (edges u v).1 edge with rfl | rfl
    · exact returnAlongReflection g (p * ·) f (factor e labels p) reflectsP
        (invol p) (reflectPair p reflectsLiftP) twice ih
    · exact returnAlongReflection g (q * ·) f (factor e labels q) reflectsQ
        (invol q) (reflectPair q reflectsLiftQ) twice ih

/-- The extension realizes every prescribed return throughout each component. -/
theorem realizeSchreierReturns {L A : Type*} [Finite L] [Mul L] [AddCommGroup A]
    (G : SimpleGraph L) (e p q : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (twice : ∀ a : A, a + a = 0) (centreless : Set.center L = {e})
    (hpq : p ≠ q) (hp : p ≠ e) (hq : q ≠ e)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (t : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e} → A) :
    ∃ labels : Set L → A,
      letI := extensionMul e labels
      let g : L → L := fun y => p * (q * y)
      let f : L × A → L × A := fun y => (p, 0) * ((q, 0) * y)
      (∀ x : L × A, (e, 0) * x = x) ∧
      (∀ x y : L × A, x * y = y * x) ∧
      (∀ x y : L × A, x * (x * y) = y) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      (∀ x, G.connectedComponentMk x = G.connectedComponentMk e →
        ∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a)) ∧
      ∀ (C : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e}) (x : L),
        G.connectedComponentMk x = C.val →
          ∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a + t C) := by
  classical
  let I := {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e}
  have representative (C : I) : ∃ x : L, G.connectedComponentMk x = C.val :=
    (ConnectedComponent.exists (p := fun C' => C' = C.val)).mp ⟨C.val, rfl⟩
  choose rep hrep using representative
  have separate (C : I) : ¬G.Reachable e (rep C) := by
    intro h
    exact C.prop ((hrep C).symm.trans (ConnectedComponent.sound h).symm)
  have distinct (C C' : I) (h : G.Reachable (rep C) (rep C')) : C = C' :=
    Subtype.ext ((hrep C).symm.trans ((ConnectedComponent.sound h).trans (hrep C')))
  have rightUnit (x : L) : x * e = x := (comm x e).trans (unit x)
  have injectRight (x : L) : Injective (· * x) := by
    intro u v h
    apply (show Involutive (x * ·) from invol x).injective
    simpa only [comm x u, comm x v] using h
  have noFixed {z : L} (hz : z ≠ e) (x : L) : z * x ≠ x := by
    intro h
    exact hz (injectRight x (h.trans (unit x).symm))
  obtain ⟨labels, returns⟩ := prescribeRepresentativeReturns G e p q rep t (invol p) (invol q)
    (noFixed hp) (noFixed hq) hpq (rightUnit p) (rightUnit q) edges separate distinct
  letI := extensionMul e labels
  obtain ⟨idExt, commExt, involExt, centerExt⟩ :=
    extensionSteinerAndCentre e labels unit comm invol twice centreless
  refine ⟨labels, idExt, commExt, involExt, centerExt, ?_, ?_⟩
  · intro x connected
    have atIdentity (a : A) :
        (fun y : L × A => (p, 0) * ((q, 0) * y))^[
          minimalPeriod (fun y => p * (q * y)) e] (e, a) = (e, a + 0) := by
      obtain ⟨period, identity⟩ := identityReturn e p q labels a unit comm invol twice hpq
      rw [period, ← pairedLift_eq_mul e labels p q, add_zero]
      exact identity
    simpa only [add_zero] using returnAlongComponent G e p q labels invol twice edges
      involExt (ConnectedComponent.exact connected.symm) 0 atIdentity
  · intro C x connected
    have fromRep (a : A) :
        (fun y : L × A => (p, 0) * ((q, 0) * y))^[
          minimalPeriod (fun y => p * (q * y)) (rep C)] (rep C, a) = (rep C, a + t C) := by
      rw [← pairedLift_eq_mul e labels p q]
      exact returns C a
    exact returnAlongComponent G e p q labels invol twice edges involExt
      (ConnectedComponent.exact ((hrep C).trans connected.symm)) (t C) fromRep


end D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
