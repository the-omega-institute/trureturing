/- GID: D5/S3/Topology/FourBraidKhovanovHomology
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovHomology
   mirror-E: none(waiver:algebraically-proved)
   anchors: [lake/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Integral chain contraction certificates for the four-braid cube. -/

import D5.S3.Topology.FourBraidKhovanovCube
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Sparse certificate checks interpreted as linear identities over the integers. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.FourBraidKhovanovCube

/-- A column of coefficients over the integers. Repeated entries are added. -/
abbrev Sparse (m : Nat) := List (Fin m × Int)

abbrev Free (m : Nat) := Fin m →₀ Int
abbrev Columns (n m : Nat) := Fin n → Sparse m

namespace Sparse

variable {l m n : Nat}

private def vector : Sparse m → Free m
  | [] => 0
  | (i, a) :: xs => Finsupp.single i a + vector xs

private theorem vector_append (x y : Sparse m) :
    vector (x ++ y) = vector x + vector y := by
  induction x with
  | nil => simp [vector]
  | cons p x ih => rcases p with ⟨i, a⟩; simp [vector, ih, add_assoc]

private def scale (a : Int) (xs : Sparse m) : Sparse m :=
  xs.map fun (i, b) => (i, a * b)

private theorem vector_scale (a : Int) (xs : Sparse m) :
    vector (scale a xs) = a • vector xs := by
  induction xs with
  | nil => simp [scale, vector]
  | cons p xs ih =>
    rcases p with ⟨i, b⟩
    change Finsupp.single i (a * b) + vector (scale a xs) =
      a • (Finsupp.single i b + vector xs)
    rw [ih, smul_add, Finsupp.smul_single, smul_eq_mul]

private def coefficient (xs : Sparse m) (i : Fin m) : Int :=
  (xs.map fun (j, a) => if i == j then a else 0).sum

private theorem vector_apply (xs : Sparse m) (i : Fin m) :
    vector xs i = coefficient xs i := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨j, a⟩
    change (Finsupp.single j a + vector xs) i =
      (if i == j then a else 0) + coefficient xs i
    simp only [Finsupp.add_apply, ih]
    by_cases h : i = j
    · subst j; simp
    · simp [h]

private def zero (xs : Sparse m) : Bool :=
  xs.all fun p => coefficient xs p.1 == 0

private theorem zero_sound {xs : Sparse m} (h : zero xs = true) : vector xs = 0 := by
  ext i
  rw [vector_apply]
  change coefficient xs i = 0
  by_cases hi : ∃ a, (i, a) ∈ xs
  · obtain ⟨a, ha⟩ := hi
    simpa using (List.all_eq_true.mp h) (i, a) ha
  · clear h
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      rcases p with ⟨j, a⟩
      have hj : i ≠ j := fun e => hi ⟨a, by simp [e]⟩
      have ht : ¬∃ a, (i, a) ∈ xs := fun ⟨a, ha⟩ => hi ⟨a, List.mem_cons_of_mem _ ha⟩
      change (if i == j then a else 0) + coefficient xs i = 0
      simp [hj, ih ht]

def linear (c : Columns n m) : Free n →ₗ[Int] Free m :=
  Finsupp.linearCombination Int (fun i => vector (c i))

private theorem linear_single (c : Columns n m) (i : Fin n) (a : Int) :
    linear c (Finsupp.single i a) = a • vector (c i) := by
  simp [linear]

private def applyColumn (c : Columns n m) (xs : Sparse n) : Sparse m :=
  xs.flatMap fun (i, a) => scale a (c i)

private theorem vector_applyColumn (c : Columns n m) (xs : Sparse n) :
    vector (applyColumn c xs) = linear c (vector xs) := by
  induction xs with
  | nil => simp [applyColumn, vector]
  | cons p xs ih =>
    rcases p with ⟨i, a⟩
    simp only [applyColumn, List.flatMap_cons, vector_append, vector_scale, vector, map_add,
      linear_single]
    rw [← ih]
    rfl

private theorem ext_single {f g : Free n →ₗ[Int] Free m}
    (h : ∀ i, f (Finsupp.single i 1) = g (Finsupp.single i 1)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single i a =>
    rw [show Finsupp.single i a = a • (Finsupp.single i (1 : Int)) by simp, map_smul,
      map_smul, h]

private def allColumns {n : Nat} (test : Fin n → Bool) : Bool :=
  (List.ofFn test).all id

private theorem allColumns_sound {test : Fin n → Bool} (h : allColumns test = true)
    (i : Fin n) : test i = true :=
  List.all_eq_true.mp h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

def checkZeroComp (a : Columns l m) (b : Columns n l) : Bool :=
  allColumns fun i => zero (applyColumn a (b i))

theorem zeroComp (a : Columns l m) (b : Columns n l) (h : checkZeroComp a b = true) :
    (linear a).comp (linear b) = 0 := by
  apply ext_single
  intro i
  simpa [linear_single, vector_applyColumn] using zero_sound (allColumns_sound h i)

def checkRetract (p : Columns n m) (i : Columns m n) : Bool :=
  allColumns fun j => zero (applyColumn p (i j) ++ [(j, -1)])

theorem retract (p : Columns n m) (i : Columns m n) (h : checkRetract p i = true) :
    (linear p).comp (linear i) = LinearMap.id := by
  apply ext_single
  intro j
  have hj := zero_sound (allColumns_sound h j)
  simpa [vector_applyColumn, vector_append, vector, Finsupp.single_neg, ← sub_eq_add_neg,
    sub_eq_zero, linear_single] using hj

def checkHomotopy {a b r : Nat}
    (incoming : Columns a n) (outgoing : Columns n b)
    (previous : Columns n a) (following : Columns b n)
    (i : Columns r n) (p : Columns n r) : Bool :=
  allColumns fun j => zero (applyColumn incoming (previous j) ++
    applyColumn following (outgoing j) ++ applyColumn i (p j) ++ [(j, -1)])

theorem homotopy {a b r : Nat}
    (incoming : Columns a n) (outgoing : Columns n b)
    (previous : Columns n a) (following : Columns b n)
    (i : Columns r n) (p : Columns n r)
    (h : checkHomotopy incoming outgoing previous following i p = true) :
    (linear incoming).comp (linear previous) + (linear following).comp (linear outgoing) +
      (linear i).comp (linear p) = LinearMap.id := by
  apply ext_single
  intro j
  have hj := zero_sound (allColumns_sound h j)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, linear_single,
    one_smul]
  apply sub_eq_zero.mp
  simpa [vector_applyColumn, vector_append, vector, Finsupp.single_neg, sub_eq_add_neg,
    add_assoc] using hj

private def checkBlock {n : Nat} (test : Fin n → Bool) (b : Nat) : Bool :=
  (List.range' (16 * b) 16).all fun x => if h : x < n then test ⟨x, h⟩ else true

private theorem allColumns_of_blocks {n blocks : Nat} {test : Fin n → Bool}
    (bound : n ≤ 16 * blocks)
    (checks : ∀ b < blocks, checkBlock test b = true) : allColumns test = true := by
  apply List.all_eq_true.mpr
  intro value hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  have hi := i.isLt
  have hq : i.val / 16 < blocks := by omega
  have hi' : i.val ∈ List.range' (16 * (i.val / 16)) 16 := by
    rw [List.mem_range'_1]
    omega
  have hx := List.all_eq_true.mp (checks _ hq) _ hi'
  simpa [hi] using hx

def checkZeroCompBlock (a : Columns l m) (b : Columns n l) (block : Nat) : Bool :=
  checkBlock (fun i => zero (applyColumn a (b i))) block

theorem checkZeroComp_of_blocks (a : Columns l m) (b : Columns n l) {blocks : Nat}
    (bound : n ≤ 16 * blocks)
    (checks : ∀ k < blocks, checkZeroCompBlock a b k = true) :
    checkZeroComp a b = true := allColumns_of_blocks bound checks

def checkRetractBlock (p : Columns n m) (i : Columns m n) (block : Nat) : Bool :=
  checkBlock (fun j => zero (applyColumn p (i j) ++ [(j, -1)])) block

theorem checkRetract_of_blocks (p : Columns n m) (i : Columns m n) {blocks : Nat}
    (bound : m ≤ 16 * blocks)
    (checks : ∀ k < blocks, checkRetractBlock p i k = true) :
    checkRetract p i = true := allColumns_of_blocks bound checks

def checkHomotopyBlock {a b r : Nat}
    (incoming : Columns a n) (outgoing : Columns n b)
    (previous : Columns n a) (following : Columns b n)
    (i : Columns r n) (p : Columns n r) (block : Nat) : Bool :=
  checkBlock (fun j => zero (applyColumn incoming (previous j) ++
    applyColumn following (outgoing j) ++ applyColumn i (p j) ++ [(j, -1)])) block

theorem checkHomotopy_of_blocks {a b r blocks : Nat}
    (incoming : Columns a n) (outgoing : Columns n b)
    (previous : Columns n a) (following : Columns b n)
    (i : Columns r n) (p : Columns n r)
    (bound : n ≤ 16 * blocks)
    (checks : ∀ k < blocks, checkHomotopyBlock incoming outgoing previous following i p k = true) :
    checkHomotopy incoming outgoing previous following i p = true :=
  allColumns_of_blocks bound checks

abbrev IntegerColumn := List (Nat × Int)

def eraseIndices (xs : Sparse m) : IntegerColumn :=
  xs.map fun (i, a) => (i.val, a)

private theorem eraseIndices_append (x y : Sparse m) :
    eraseIndices (x ++ y) = eraseIndices x ++ eraseIndices y := by
  unfold eraseIndices
  exact List.map_append

private def rawCoefficient (xs : IntegerColumn) (i : Nat) : Int :=
  (xs.map fun (j, a) => if i == j then a else 0).sum

private theorem rawCoefficient_eq (xs : Sparse m) (i : Fin m) :
    rawCoefficient (eraseIndices xs) i.val = coefficient xs i := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j, a⟩
    change (if i.val == j.val then a else 0) + rawCoefficient (eraseIndices xs) i.val =
      (if i == j then a else 0) + coefficient xs i
    rw [ih]
    by_cases h : i = j
    · simp [h]
    · have hv : i.val ≠ j.val := fun h' => h (Fin.ext h')
      simp [h, hv]

def rawZero (xs : IntegerColumn) : Bool :=
  xs.all fun (i, _) => rawCoefficient xs i == 0

private theorem rawZero_eq (xs : Sparse m) : rawZero (eraseIndices xs) = zero xs := by
  unfold rawZero zero eraseIndices
  rw [List.all_map]
  apply congrArg (fun f => xs.all f)
  funext p
  exact congrArg (· == (0 : Int)) (rawCoefficient_eq xs p.1)

def rawApply (read : Nat → IntegerColumn) (xs : IntegerColumn) : IntegerColumn :=
  xs.flatMap fun (i, a) => (read i).map fun (j, b) => (j, a * b)

private theorem rawApply_eq (c : Columns n m) (read : Nat → IntegerColumn)
    (agrees : ∀ i : Fin n, read i.val = eraseIndices (c i)) (xs : Sparse n) :
    rawApply read (eraseIndices xs) = eraseIndices (applyColumn c xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i, a⟩
    change ((read i.val).map fun (j, b) => (j, a * b)) ++ rawApply read (eraseIndices xs) =
      eraseIndices (scale a (c i) ++ applyColumn c xs)
    rw [ih, agrees i]
    simp [eraseIndices, scale, List.map_map, Function.comp_def]

def rawBlock (n block : Nat) (test : Nat → Bool) : Bool :=
  (List.range' (16 * block) 16).all fun x => if x < n then test x else true

private theorem rawBlock_eq {n : Nat} (block : Nat) (test : Nat → Bool) (typed : Fin n → Bool)
    (agrees : ∀ i : Fin n, test i.val = typed i) :
    rawBlock n block test = checkBlock typed block := by
  unfold rawBlock checkBlock
  apply congrArg (fun f => (List.range' (16 * block) 16).all f)
  funext x
  by_cases h : x < n
  · simpa [h] using agrees ⟨x, h⟩
  · simp [h]

theorem rawZeroComp_eq (a : Columns l m) (b : Columns n l)
    (ra rb : Nat → IntegerColumn)
    (ha : ∀ i : Fin l, ra i.val = eraseIndices (a i))
    (hb : ∀ i : Fin n, rb i.val = eraseIndices (b i)) (block : Nat) :
    rawBlock n block (fun j => rawZero (rawApply ra (rb j))) = checkZeroCompBlock a b block := by
  apply rawBlock_eq
  intro j
  rw [hb, rawApply_eq a ra ha, rawZero_eq]

theorem rawRetract_eq (p : Columns n m) (i : Columns m n)
    (rp ri : Nat → IntegerColumn)
    (hp : ∀ j : Fin n, rp j.val = eraseIndices (p j))
    (hi : ∀ j : Fin m, ri j.val = eraseIndices (i j)) (block : Nat) :
    rawBlock m block (fun j => rawZero (rawApply rp (ri j) ++ [(j, -1)])) =
      checkRetractBlock p i block := by
  apply rawBlock_eq
  intro j
  rw [hi, rawApply_eq p rp hp]
  have hz := rawZero_eq (applyColumn p (i j) ++ [(j, -1)])
  rw [eraseIndices_append] at hz
  exact hz

theorem rawHomotopy_eq {a b r : Nat}
    (e : Columns a n) (d : Columns n b) (h₀ : Columns n a) (h₁ : Columns b n)
    (i : Columns r n) (p : Columns n r)
    (re rd rh₀ rh₁ ri rp : Nat → IntegerColumn)
    (he : ∀ j : Fin a, re j.val = eraseIndices (e j))
    (hd : ∀ j : Fin n, rd j.val = eraseIndices (d j))
    (hh₀ : ∀ j : Fin n, rh₀ j.val = eraseIndices (h₀ j))
    (hh₁ : ∀ j : Fin b, rh₁ j.val = eraseIndices (h₁ j))
    (hi : ∀ j : Fin r, ri j.val = eraseIndices (i j))
    (hp : ∀ j : Fin n, rp j.val = eraseIndices (p j))
    (block : Nat) :
    rawBlock n block (fun j => rawZero (rawApply re (rh₀ j) ++ rawApply rh₁ (rd j) ++
      rawApply ri (rp j) ++ [(j, -1)])) = checkHomotopyBlock e d h₀ h₁ i p block := by
  apply rawBlock_eq
  intro j
  rw [hh₀, hd, hp, rawApply_eq e re he, rawApply_eq h₁ rh₁ hh₁, rawApply_eq i ri hi]
  have hz := rawZero_eq
    (applyColumn e (h₀ j) ++ applyColumn h₁ (d j) ++ applyColumn i (p j) ++ [(j, -1)])
  simp only [eraseIndices_append] at hz
  exact hz

theorem checkZeroComp_empty (a : Columns l m) (b : Columns 0 l) :
    checkZeroComp a b = true := rfl

theorem checkRetract_empty (p : Columns n 0) (i : Columns 0 n) :
    checkRetract p i = true := rfl

theorem checkHomotopy_empty {a b r : Nat}
    (incoming : Columns a 0) (outgoing : Columns 0 b)
    (previous : Columns 0 a) (following : Columns b 0)
    (i : Columns r 0) (p : Columns 0 r) :
    checkHomotopy incoming outgoing previous following i p = true := rfl

end Sparse

section Quotient

variable {a n b r : Nat}
variable (e : Free a →ₗ[Int] Free n) (d : Free n →ₗ[Int] Free b)

private def boundary (sq : d.comp e = 0) : Free a →ₗ[Int] LinearMap.ker d :=
  e.codRestrict _ (fun x => DFunLike.congr_fun sq x)

/-- Cohomology at the middle of an integral three-term complex. -/
abbrev Cohomology (sq : d.comp e = 0) :=
  LinearMap.ker d ⧸ LinearMap.range (boundary e d sq)

/-- Passing a chain contraction to the quotient of actual cycles by actual
boundaries. The inverse sends a residual generator back to a cycle. -/
def cohomologyEquiv (sq : d.comp e = 0)
    (p : Free n →ₗ[Int] Free r) (i : Free r →ₗ[Int] Free n)
    (h₀ : Free n →ₗ[Int] Free a) (h₁ : Free b →ₗ[Int] Free n)
    (pd : p.comp e = 0) (di : d.comp i = 0) (pi : p.comp i = LinearMap.id)
    (homotopy : e.comp h₀ + h₁.comp d + i.comp p = LinearMap.id) :
    Cohomology e d sq ≃ₗ[Int] Free r := by
  let B := LinearMap.range (boundary e d sq)
  let toH := B.liftQ (p.comp (LinearMap.ker d).subtype) (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun pd x)
  let toCycle := i.codRestrict (LinearMap.ker d) (fun x => DFunLike.congr_fun di x)
  let fromH := B.mkQ.comp toCycle
  refine { toH with toFun := toH, invFun := fromH, left_inv := ?_, right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    change Submodule.Quotient.mk (toCycle (p x.val)) = Submodule.Quotient.mk x
    symm
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨h₀ x.val, ?_⟩
    apply Subtype.ext
    have hx := DFunLike.congr_fun homotopy x.val
    change e (h₀ x.val) + h₁ (d x.val) + i (p x.val) = x.val at hx
    rw [show d x.val = 0 from x.property, map_zero, add_zero] at hx
    exact (eq_sub_iff_add_eq).mpr hx
  · intro x
    change p (i x) = x
    exact DFunLike.congr_fun pi x

end Quotient

end D5.S3.Topology.FourBraidKhovanovCube
