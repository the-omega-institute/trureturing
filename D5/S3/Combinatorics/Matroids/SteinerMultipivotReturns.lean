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
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Center

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

private theorem returnTable :
    ∀ x : Fin 4, let y := BitVec.ofNat 3 (4 + x.val)
      (square 1 2 y).Perm (colour 1 ++ colour 2) ∧
      (square 1 3 y).Perm (colour 1 ++ colour 3) ∧
      (square 2 3 y).Perm (colour 2 ++ colour 3) := by
  decide

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
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)

private theorem liftColour {A L : Type*} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (labels : Set L → A) (p x : BitVec 3) (a : A)
    (hp : p ≠ 0) (hx : x ≠ 0) (hpx : p ≠ x) :
    letI := extensionMul (b 0) labels
    ((b p, (0 : A)) : L × A) * (b x, a) =
      (b (p ^^^ x), a + labels (b '' (↑(cubeTriple p x) : Set (BitVec 3)))) := by
  classical
  let _ := extensionMul (b 0) labels
  change (b p * b x, 0 + a + (if b p = b 0 ∨ b x = b 0 ∨ b p = b x then 0 else
    labels ({b p, b x, b p * b x} : Set L))) = _
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
  rw [ite_eq_right hn, zero_add, image, mul]

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
  let key := fun s : Finset (BitVec 3) => labels (b '' (↑s : Set (BitVec 3)))
  change f (f (b x, a)) = (b x, a + ((square p q x).map key).sum)
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
  dsimp only [f]
  rw [liftColour b mul labels q x a q0 x0 qx,
    liftColour b mul labels p (q ^^^ x) _ p0 y0 py,
    liftColour b mul labels q (p ^^^ (q ^^^ x)) _ q0 z0 qz,
    liftColour b mul labels p (q ^^^ (p ^^^ (q ^^^ x))) _ p0 w0 pw]
  change (b (p ^^^ (q ^^^ (p ^^^ (q ^^^ x)))), _) = (b x, _)
  apply Prod.ext
  · exact congrArg b returns
  · simp only [square, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
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

private abbrev Plane := Option (ZMod 3 × ZMod 3)

private def planeMul : Plane → Plane → Plane
  | none, y => y
  | x, none => x
  | some x, some y => if x = y then none else some (-x - y)

private instance : Mul Plane := ⟨planeMul⟩

private theorem planeUnit (x : Plane) : (none : Plane) * x = x := rfl

private theorem planeComm : ∀ x y : Plane, x * y = y * x := by
  decide

private theorem planeInvol : ∀ x y : Plane, x * (x * y) = y := by
  decide

private theorem planeCentre : Set.center Plane = {none} := by
  ext x
  change x ∈ Set.center Plane ↔ x = none
  have check : ∀ z : Plane,
      ((∀ a, z * a = a * z) ∧ (∀ a b, z * (a * b) = (z * a) * b) ∧
        (∀ a b, (a * b) * z = a * (b * z))) ↔ z = none := by
    decide
  rw [← check x]
  constructor
  · intro h
    have hZ := Set.mem_center_iff.mp h
    exact ⟨hZ.comm, hZ.left_assoc, hZ.right_assoc⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact Set.mem_center_iff.mpr ⟨h₁, h₂, h₃⟩

private abbrev Model := Plane × Plane × Plane

private def encodeBit (b : Bool) : Plane := if b then some (0, 0) else none

private def embedModel (u : BitVec 3) : Model :=
  (encodeBit (u.getLsbD 0), encodeBit (u.getLsbD 1), encodeBit (u.getLsbD 2))

private theorem embedModel_injective : Function.Injective embedModel := by
  change ∀ x y : BitVec 3, embedModel x = embedModel y → x = y
  decide

private theorem embedModel_mul : ∀ x y : BitVec 3,
    embedModel (x ^^^ y) = embedModel x * embedModel y := by
  decide

private theorem modelCentre : Set.center Model = {embedModel 0} := by
  rw [Set.center_prod, Set.center_prod, planeCentre]
  ext x
  rcases x with ⟨x,y,z⟩
  simp [embedModel, encodeBit]

private def cubeInCentreless : BitVec 3 ↪ Model :=
  ⟨embedModel, embedModel_injective⟩

private theorem centrelessIncompatibleReturns :
    ¬ (∃ labels : Set Model → ZMod 2,
      letI := extensionMul (embedModel 0) labels
      ∀ i : Fin 4, ∀ a : ZMod 2,
        let x := embedModel (BitVec.ofNat 3 (4 + i.val))
        (pairLift (embedModel 1) (embedModel 2))^[2] (x, a) = (x, a + 1) ∧
        (pairLift (embedModel 1) (embedModel 3))^[2] (x, a) = (x, a + 0) ∧
        (pairLift (embedModel 2) (embedModel 3))^[2] (x, a) = (x, a + 0)) := by
  intro h
  have parity := (simultaneousReturns cubeInCentreless embedModel_mul
    (show ∀ a : ZMod 2, a + a = 0 by decide) 1 0 0).mp h
  exact (by decide : ¬ (((1 : ZMod 2) + 0) + 0 = 0)) parity

/-- A centreless finite Steiner loop contains a Boolean cube with incompatible returns. -/
theorem existsCentrelessObstruction :
    ∃ (L : Type) (mul : Mul L) (b : BitVec 3 ↪ L),
      letI := mul
      Nat.card L = 1000 ∧
      (∀ x : L, b 0 * x = x) ∧ (∀ x y : L, x * y = y * x) ∧
      (∀ x y : L, x * (x * y) = y) ∧ Set.center L = {b 0} ∧
      (∀ x y : BitVec 3, b (x ^^^ y) = b x * b y) ∧
      ¬ (∃ labels : Set L → ZMod 2,
        letI := extensionMul (b 0) labels
        ∀ i : Fin 4, ∀ a : ZMod 2,
          let x := b (BitVec.ofNat 3 (4 + i.val))
          (pairLift (b 1) (b 2))^[2] (x, a) = (x, a + 1) ∧
          (pairLift (b 1) (b 3))^[2] (x, a) = (x, a + 0) ∧
          (pairLift (b 2) (b 3))^[2] (x, a) = (x, a + 0)) := by
  refine ⟨Model, inferInstance, cubeInCentreless, ?_, ?_, ?_, ?_, modelCentre,
    embedModel_mul, centrelessIncompatibleReturns⟩
  · simp [Model, Plane, Nat.card_eq_fintype_card]
  · intro x
    rcases x with ⟨a, b, c⟩
    exact Prod.ext (planeUnit a) (Prod.ext (planeUnit b) (planeUnit c))
  · rintro ⟨a, b, c⟩ ⟨x, y, z⟩
    exact Prod.ext (planeComm a x) (Prod.ext (planeComm b y) (planeComm c z))
  · rintro ⟨a, b, c⟩ ⟨x, y, z⟩
    exact Prod.ext (planeInvol a x) (Prod.ext (planeInvol b y) (planeInvol c z))

#print axioms existsCentrelessObstruction
#print axioms simultaneousReturns

end D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
