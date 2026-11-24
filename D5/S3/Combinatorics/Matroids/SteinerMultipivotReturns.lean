/- GID: D5/S3/Combinatorics/Matroids/SteinerMultipivotReturns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerMultipivotReturns
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Three Steiner square returns satisfy a sharp parity constraint in a Boolean subloop. -/

import D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Group.Center
import Mathlib.Tactic.FinCases

/-! # Simultaneous returns over a Boolean Steiner subloop -/

namespace D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns

open scoped BigOperators

private theorem parity {A : Type*} [AddCommGroup A] (twice : ∀ x : A, x + x = 0)
    (u v w : A) :
    (∃ a b c : A, a + b = u ∧ a + c = v ∧ b + c = w) ↔ (u + v) + w = 0 := by
  constructor
  · rintro ⟨a, b, c, rfl, rfl, rfl⟩
    calc
      (a + b) + (a + c) + (b + c) = (a + a) + (b + b) + (c + c) := by abel
      _ = 0 := by simp [twice]
  · intro compatible
    refine ⟨0, u, v, zero_add _, zero_add _, ?_⟩
    have eq : u + v = -w := eq_neg_of_add_eq_zero_left compatible
    have opp : -w = w := (eq_neg_of_add_eq_zero_left (twice w)).symm
    exact eq.trans opp


private def cubeTriple (pivot corner : BitVec 3) : Finset (BitVec 3) :=
  {pivot, corner, pivot ^^^ corner}

private def colour (pivot : BitVec 3) : List (Finset (BitVec 3)) :=
  [cubeTriple pivot 4, cubeTriple pivot (if pivot = 1 then 6 else 5)]

private def square (p q x : BitVec 3) : List (Finset (BitVec 3)) :=
  let a := q ^^^ x
  let b := p ^^^ a
  let c := q ^^^ b
  [cubeTriple q x, cubeTriple p a, cubeTriple q b, cubeTriple p c]

private theorem triple_swap (p x : BitVec 3) :
    cubeTriple p (p ^^^ x) = cubeTriple p x := by
  have invol : p ^^^ (p ^^^ x) = x := by
    rw [← BitVec.xor_assoc, BitVec.xor_self]
    simp
  simp only [cubeTriple, invol]
  exact congrArg (insert p) (Finset.pair_comm _ _)

private theorem xor_invol (a x : BitVec 3) : a ^^^ (a ^^^ x) = x := by
  rw [← BitVec.xor_assoc, BitVec.xor_self]
  simp

private theorem xor_cross (a b x : BitVec 3) : a ^^^ (b ^^^ x) = b ^^^ (a ^^^ x) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem square_colours (p q x : BitVec 3) :
    square p q x = [cubeTriple q x, cubeTriple p (q ^^^ x),
      cubeTriple q (p ^^^ x), cubeTriple p x] := by
  have middle : cubeTriple q (p ^^^ (q ^^^ x)) = cubeTriple q (p ^^^ x) := by
    rw [xor_cross p q x, triple_swap]
  have last : q ^^^ (p ^^^ (q ^^^ x)) = p ^^^ x := by
    rw [xor_cross q p (q ^^^ x), xor_invol]
  simp only [square, middle, last, triple_swap]

private theorem square_shift_second (p q x : BitVec 3) :
    (square p q (q ^^^ x)).Perm (square p q x) := by
  rw [square_colours, square_colours, xor_invol, triple_swap, xor_cross p q x, triple_swap]
  apply List.Perm.cons
  exact List.reverse_perm [cubeTriple p (q ^^^ x), cubeTriple q (p ^^^ x), cubeTriple p x]

private theorem square_shift_first (p q x : BitVec 3) :
    (square p q (p ^^^ x)).Perm (square p q x) := by
  rw [square_colours, square_colours, xor_invol, triple_swap, xor_cross q p x, triple_swap]
  exact (List.reverse_perm [cubeTriple q x, cubeTriple p (q ^^^ x),
    cubeTriple q (p ^^^ x)]).append_right [cubeTriple p x]

private theorem returnTable (i : Fin 4) :
    let x := BitVec.ofNat 3 (4 + i.val)
    (square 1 2 x).Perm (colour 1 ++ colour 2) ∧
    (square 1 3 x).Perm (colour 1 ++ colour 3) ∧
    (square 2 3 x).Perm (colour 2 ++ colour 3) := by
  intro x
  have fromAnchor (p q : BitVec 3)
      (cover : x = 4 ∨ x = p ^^^ 4 ∨ x = q ^^^ 4 ∨ x = p ^^^ (q ^^^ 4)) :
      (square p q x).Perm (square p q 4) := by
    rcases cover with hx | hx | hx | hx
    · rw [hx]
    · rw [hx]
      exact square_shift_first p q 4
    · rw [hx]
      exact square_shift_second p q 4
    · rw [hx]
      exact (square_shift_first p q (q ^^^ 4)).trans (square_shift_second p q 4)
  have c12 : x = 4 ∨ x = 1 ^^^ 4 ∨ x = 2 ^^^ 4 ∨ x = 1 ^^^ (2 ^^^ 4) := by
    dsimp [x]
    fin_cases i <;> decide
  have c13 : x = 4 ∨ x = 1 ^^^ 4 ∨ x = 3 ^^^ 4 ∨ x = 1 ^^^ (3 ^^^ 4) := by
    dsimp [x]
    fin_cases i <;> decide
  have c23 : x = 4 ∨ x = 2 ^^^ 4 ∨ x = 3 ^^^ 4 ∨ x = 2 ^^^ (3 ^^^ 4) := by
    dsimp [x]
    fin_cases i <;> decide
  exact ⟨(fromAnchor 1 2 c12).trans (by decide), (fromAnchor 1 3 c13).trans (by decide),
    (fromAnchor 2 3 c23).trans (by decide)⟩

private def assign {A : Type*} [Zero A] (b c : A) (t : Finset (BitVec 3)) : A :=
  if t = cubeTriple 2 4 then b else if t = cubeTriple 3 4 then c else 0

private theorem assign_sum {A : Type*} [AddCommGroup A] (b c : A) :
    ((colour 1).map (assign b c)).sum = 0 ∧
    ((colour 2).map (assign b c)).sum = b ∧
    ((colour 3).map (assign b c)).sum = c := by
  have a12 : cubeTriple 1 4 ≠ cubeTriple 2 4 := by decide
  have a13 : cubeTriple 1 4 ≠ cubeTriple 3 4 := by decide
  have a12' : cubeTriple 1 6 ≠ cubeTriple 2 4 := by decide
  have a13' : cubeTriple 1 6 ≠ cubeTriple 3 4 := by decide
  have a23 : cubeTriple 2 4 ≠ cubeTriple 3 4 := by decide
  have a22' : cubeTriple 2 5 ≠ cubeTriple 2 4 := by decide
  have a23' : cubeTriple 2 5 ≠ cubeTriple 3 4 := by decide
  have a32' : cubeTriple 3 5 ≠ cubeTriple 2 4 := by decide
  have a33' : cubeTriple 3 5 ≠ cubeTriple 3 4 := by decide
  have one : colour 1 = [cubeTriple 1 4, cubeTriple 1 6] := rfl
  have two : colour 2 = [cubeTriple 2 4, cubeTriple 2 5] := rfl
  have three : colour 3 = [cubeTriple 3 4, cubeTriple 3 5] := rfl
  rw [one, two, three]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, assign,
    a12, a13, a12', a13', a23.symm, a22', a23', a32', a33', eq_self, ite_true,
    ite_false, add_zero, and_self]

private theorem prescribeCubeReturns {A : Type*} [AddCommGroup A]
    (twice : ∀ x : A, x + x = 0) (u v w : A) :
    (∃ labels : Finset (BitVec 3) → A, ∀ x : Fin 4,
      let y := BitVec.ofNat 3 (4 + x.val)
      ((square 1 2 y).map labels).sum = u ∧
      ((square 1 3 y).map labels).sum = v ∧
      ((square 2 3 y).map labels).sum = w) ↔ (u + v) + w = 0 := by
  constructor
  · rintro ⟨labels, actual⟩
    obtain ⟨h1, h2, h3⟩ := returnTable 0
    obtain ⟨hu, hv, hw⟩ := actual 0
    apply (parity twice u v w).mp
    exact ⟨_, _, _,
      (by simpa using ((h1.map labels).sum_eq.symm.trans hu)),
      (by simpa using ((h2.map labels).sum_eq.symm.trans hv)),
      (by simpa using ((h3.map labels).sum_eq.symm.trans hw))⟩
  · intro compatible
    refine ⟨assign u v, ?_⟩
    intro x
    obtain ⟨h1, h2, h3⟩ := returnTable x
    obtain ⟨hzero, hu, hv⟩ := assign_sum u v
    have hw : u + v = w := (eq_neg_of_add_eq_zero_left compatible).trans
      (eq_neg_of_add_eq_zero_left (twice w)).symm
    have h12 := (h1.map (assign u v)).sum_eq
    have h13 := (h2.map (assign u v)).sum_eq
    have h23 := (h3.map (assign u v)).sum_eq
    rw [List.map_append, List.sum_append, hzero, hu, zero_add] at h12
    rw [List.map_append, List.sum_append, hzero, hv, zero_add] at h13
    rw [List.map_append, List.sum_append, hu, hv, hw] at h23
    exact ⟨h12, h13, h23⟩

private theorem prescribeEmbeddedCubeReturns {A L : Type*} [AddCommGroup A]
    (b : BitVec 3 ↪ L) (twice : ∀ x : A, x + x = 0) (u v w : A) :
    let key := fun s : Finset (BitVec 3) => b '' (↑s : Set (BitVec 3))
    (∃ labels : Set L → A, ∀ x : Fin 4,
      let y := BitVec.ofNat 3 (4 + x.val)
      ((square 1 2 y).map (labels ∘ key)).sum = u ∧
      ((square 1 3 y).map (labels ∘ key)).sum = v ∧
      ((square 2 3 y).map (labels ∘ key)).sum = w) ↔ (u + v) + w = 0 := by
  classical
  intro key
  constructor
  · rintro ⟨labels, sums⟩
    exact (prescribeCubeReturns twice u v w).mp ⟨labels ∘ key, sums⟩
  · intro h
    obtain ⟨labels, sums⟩ := (prescribeCubeReturns twice u v w).mpr h
    have inj : Function.Injective key := by
      intro s t eq
      exact Finset.coe_injective (Set.image_injective.mpr b.injective eq)
    refine ⟨labels ∘ Function.invFun key, ?_⟩
    have recover : (labels ∘ Function.invFun key) ∘ key = labels :=
      funext fun t => congrArg labels (Function.leftInverse_invFun inj t)
    simpa only [recover] using sums

open Function
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
  (extensionMul factor pairedLift_eq_mul pairedLiftIterate)

private theorem factorColour {A L : Type*} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (labels : Set L → A) (p x : BitVec 3)
    (hp : p ≠ 0) (hx : x ≠ 0) (hpx : p ≠ x) :
    factor (b 0) labels (b p) (b x) =
      labels (b '' (↑(cubeTriple p x) : Set (BitVec 3))) := by
  classical
  have image : b '' (↑(cubeTriple p x) : Set (BitVec 3)) =
      ({b p, b x, b p * b x} : Set L) := by
    rw [← mul p x]
    simp [cubeTriple, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton]
  have hn : ¬ (b p = b 0 ∨ b x = b 0 ∨ b p = b x) := by
    rintro (h | h | h)
    · exact hp (b.injective h)
    · exact hx (b.injective h)
    · exact hpx (b.injective h)
  simp only [factor, ite_eq_right hn, image]
  rfl

private theorem liftSquare {A L : Type*} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (labels : Set L → A) (p q : BitVec 3) (i : Fin 4) (a : A)
    (hp : p ∈ ([1, 2, 3] : List (BitVec 3)))
    (hq : q ∈ ([1, 2, 3] : List (BitVec 3))) :
    letI := extensionMul (b 0) labels
    let x := BitVec.ofNat 3 (4 + i.val)
    let f : L × A → L × A := fun y => (b p, 0) * ((b q, 0) * y)
    f^[2] (b x, a) =
      (b x, a + ((square p q x).map (fun s => labels (b '' (↑s : Set (BitVec 3))))).sum) := by
  classical
  let _ := extensionMul (b 0) labels
  let x := BitVec.ofNat 3 (4 + i.val)
  let f : L × A → L × A := fun y => (b p, 0) * ((b q, 0) * y)
  let step : L → L := fun y => b p * (b q * y)
  let key := fun s : Finset (BitVec 3) => labels (b '' (↑s : Set (BitVec 3)))
  change f^[2] (b x, a) = (b x, a + ((square p q x).map key).sum)
  have checked : ∀ (p q : BitVec 3) (i : Fin 4),
      p ∈ ([1, 2, 3] : List (BitVec 3)) → q ∈ ([1, 2, 3] : List (BitVec 3)) →
      let x := BitVec.ofNat 3 (4 + i.val)
      let y := q ^^^ x
      let z := p ^^^ y
      let w := q ^^^ z
      p ≠ 0 ∧ q ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w ≠ 0 ∧
        q ≠ x ∧ p ≠ y ∧ q ≠ z ∧ p ≠ w ∧ (p ^^^ w) = x := by
    decide
  obtain ⟨p0, q0, x0, y0, z0, w0, qx, py, qz, pw, returns⟩ := checked p q i hp hq
  have qMul (y : BitVec 3) : b q * b y = b (q ^^^ y) := (mul q y).symm
  have stepAt (y : BitVec 3) : step (b y) = b (p ^^^ (q ^^^ y)) := by
    simp only [step, qMul, ← mul p]
  have closes : step^[2] (b x) = b x := by
    change step (step (b x)) = b x
    rw [stepAt, stepAt, returns]
  dsimp only [f]
  rw [← pairedLift_eq_mul (b 0) labels (b p) (b q), pairedLiftIterate]
  change (step^[2] (b x), a + ∑ j ∈ Finset.range 2,
    (factor (b 0) labels (b q) (step^[j] (b x)) +
      factor (b 0) labels (b p) (b q * step^[j] (b x)))) =
    (b x, a + ((square p q x).map key).sum)
  rw [closes]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iterate_zero,
    id_eq, iterate_one, stepAt, qMul, factorColour b mul labels q x q0 x0 qx,
    factorColour b mul labels p (q ^^^ x) p0 y0 py,
    factorColour b mul labels q (p ^^^ (q ^^^ x)) q0 z0 qz,
    factorColour b mul labels p (q ^^^ (p ^^^ (q ^^^ x))) p0 w0 pw,
    square, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, key]
  abel

/-- One round takes the second matching edge and then the first. -/
def pairLift {A L : Type*} [Mul (L × A)] [Zero A] (p q : L)
    (x : L × A) : L × A :=
  (p, 0) * ((q, 0) * x)

/-- The three returns over a Boolean subloop are realizable exactly when their sum is zero. -/
theorem simultaneousReturns {A L : Type*} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (twice : ∀ x : A, x + x = 0) (u v w : A) :
    (∃ labels : Set L → A,
      letI := extensionMul (b 0) labels
      ∀ i : Fin 4, ∀ a : A,
        let x := b (BitVec.ofNat 3 (4 + i.val))
        (pairLift (b 1) (b 2))^[2] (x, a) = (x, a + u) ∧
        (pairLift (b 1) (b 3))^[2] (x, a) = (x, a + v) ∧
        (pairLift (b 2) (b 3))^[2] (x, a) = (x, a + w)) ↔ (u + v) + w = 0 := by
  let key := fun t : Finset (BitVec 3) => b '' (↑t : Set (BitVec 3))
  have matching (labels : Set L → A) (p q : BitVec 3)
      (hp : p ∈ ([1, 2, 3] : List (BitVec 3)))
      (hq : q ∈ ([1, 2, 3] : List (BitVec 3)))
      (i : Fin 4) (a r : A) :
      letI := extensionMul (b 0) labels
      let x := BitVec.ofNat 3 (4 + i.val)
      (pairLift (b p) (b q))^[2] (b x, a) = (b x, a + r) ↔
        ((square p q x).map (labels ∘ key)).sum = r := by
    let _ := extensionMul (b 0) labels
    change (pairLift (b p) (b q))^[2] (b (BitVec.ofNat 3 (4 + i.val)), a) = _ ↔ _
    rw [show pairLift (b p) (b q) =
      (fun y : L × A => (b p, 0) * ((b q, 0) * y)) from rfl,
      liftSquare b mul labels p q i a hp hq]
    constructor
    · intro h
      exact add_left_cancel (congrArg Prod.snd h)
    · intro h
      exact congrArg (fun z => (b (BitVec.ofNat 3 (4 + i.val)), a + z)) h
  constructor
  · rintro ⟨labels, realized⟩
    apply (prescribeEmbeddedCubeReturns b twice u v w).mp
    refine ⟨labels, ?_⟩
    intro i
    obtain ⟨h₁, h₂, h₃⟩ := realized i 0
    exact ⟨(matching labels 1 2 (by decide) (by decide) i 0 u).mp h₁,
      (matching labels 1 3 (by decide) (by decide) i 0 v).mp h₂,
      (matching labels 2 3 (by decide) (by decide) i 0 w).mp h₃⟩
  · intro h
    obtain ⟨labels, sums⟩ := (prescribeEmbeddedCubeReturns b twice u v w).mpr h
    refine ⟨labels, ?_⟩
    intro i a
    obtain ⟨h₁, h₂, h₃⟩ := sums i
    exact ⟨(matching labels 1 2 (by decide) (by decide) i a u).mpr h₁,
      (matching labels 1 3 (by decide) (by decide) i a v).mpr h₂,
      (matching labels 2 3 (by decide) (by decide) i a w).mpr h₃⟩

private def pick {L : Type*} (e p : L) (b : Bool) : L := if b then p else e

/-- Three equal Steiner factors contain a Boolean subloop, with the same identity as the product. -/
theorem existsCentrelessBooleanCube {L : Type*} [Mul L] (e p : L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y)
    (centre : Set.center L = {e}) (hp : p ≠ e) :
    ∃ b : BitVec 3 ↪ L × L × L, b 0 = (e, e, e) ∧
      Set.center (L × L × L) = {b 0} ∧
      ∀ x y : BitVec 3, b (x ^^^ y) = b x * b y := by
  have rightUnit (x : L) : x * e = x := (comm x e).trans (unit x)
  have square : p * p = e := by simpa only [rightUnit] using invol p e
  have pickMul (a b : Bool) : pick e p (a ^^ b) = pick e p a * pick e p b := by
    cases a <;> cases b <;> simp [pick, unit, rightUnit, square]
  have pickInj : Function.Injective (pick e p) := by
    intro a b h
    cases a <;> cases b <;> simp_all [pick, hp, hp.symm]
  let b : BitVec 3 ↪ L × L × L := ⟨fun x =>
    (pick e p (x.getLsbD 0), pick e p (x.getLsbD 1), pick e p (x.getLsbD 2)), by
      intro x y h
      have h₀ := pickInj (congrArg Prod.fst h)
      have h₁ := pickInj (congrArg (fun z => z.2.1) h)
      have h₂ := pickInj (congrArg (fun z => z.2.2) h)
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · exact h₀
      · exact h₁
      · exact h₂⟩
  have id : b 0 = (e, e, e) := rfl
  refine ⟨b, id, ?_, ?_⟩
  · rw [id, Set.center_prod, Set.center_prod, centre]
    ext x
    simp
  · intro x y
    have atBit (i : ℕ) : pick e p ((x ^^^ y).getLsbD i) =
        pick e p (x.getLsbD i) * pick e p (y.getLsbD i) := by
      rw [BitVec.getLsbD_xor]
      exact pickMul _ _
    exact Prod.ext (atBit 0) (Prod.ext (atBit 1) (atBit 2))

#print axioms existsCentrelessBooleanCube
#print axioms simultaneousReturns

end D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
