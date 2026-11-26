/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWallQ8TraceSign
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWallQ8TraceSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.BilinearForm]
   utility: none
   digest: The rank-128 Barnes–Wall quaternion lift has positive defect-ground Gauss sum. -/

import D5.S3.VertexAlgebra.TwistedGround.BinaryGauss

/-! The finite phase calculation for the Barnes–Wall tensor basis and generator
lifts of Keller, Roberts and Roberts (arXiv:2411.13646v2, §§2.2, 3.3 and
Appendix A.1). The lift convention uses the strict lower triangle of the
half-Gram correction and reads products of generators in row-action order. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWallQ8TraceSign

open LatticeTwistedGroundRealization.SignQuotient
open LatticeTwistedGroundRealization (sign_zero sign_sum symmetric_pairing_split)
open BinaryGauss (residue)
open scoped BigOperators

abbrev Word := Fin 128
abbrev Half := Fin 32
abbrev Index := Fin 64
abbrev Charge := Word → F₂
abbrev Coordinate := Index → F₂

private def weight (n : ℕ) : ℕ :=
  (n &&& 1) + ((n >>> 1) &&& 1) + ((n >>> 2) &&& 1) + ((n >>> 3) &&& 1) +
    ((n >>> 4) &&& 1) + ((n >>> 5) &&& 1) + ((n >>> 6) &&& 1)

private def evenWord (u : Word) : Bool := weight u.val % 2 == 0

private def flip (mask : ℕ) (u : Word) : Word :=
  Fin.ofNat 128 (u.val ^^^ mask)

/-- The row is the subset indicator scaled by 2 ^ (4 - ceil(|u|/2)).
The intersection of two subset rows has size 2 ^ |u AND v|, and the
denominator for their inner product is 16. -/
def gramExponent (u v : Word) : ℕ :=
  (8 - weight u.val) / 2 + (8 - weight v.val) / 2 + weight (u.val &&& v.val) - 4

def gramMod8 (u v : Word) : ZMod 8 := 2 ^ gramExponent u v

private def parityOfPower (n : ℕ) : F₂ := if n = 0 then 1 else 0

private theorem parityOfPower_eq (n : ℕ) : parityOfPower n = residue (2 ^ n) := by
  have hz : residue (2 : ZMod 8) = 0 := by decide
  cases n with
  | zero => simp [parityOfPower]
  | succ n => simp [parityOfPower, pow_succ, map_mul, hz]

/-- Divide the diagonal before reduction. Off the diagonal use the strict
lower triangle of the tensor Gram matrix. -/
def halfGram (u v : Word) : F₂ :=
  if u = v then parityOfPower (gramExponent u v - 1)
  else if v < u then parityOfPower (gramExponent u v) else 0

theorem halfGram_from_mod8 (u v : Word) :
    halfGram u v =
      if u = v then residue (2 ^ (gramExponent u v - 1))
      else if v < u then residue (gramMod8 u v) else 0 := by
  simp [halfGram, gramMod8, parityOfPower_eq]

private def affected (mask : ℕ) (isSign : Bool) (u : Word) : Bool :=
  u.val.testBit (if mask = 64 then 6 else 5) == isSign

/-- The explicit sparse integral row in the subset basis, prior to reduction.
When the selected row interacts with the Pauli generator, the flipped-row
coefficient is 2 on even words and 1 on odd words. -/
def integralRow (mask : ℕ) (isSign : Bool) (u : Word) : List (Word × ℤ) :=
  if affected mask isSign u then
    [(u, -1), (flip mask u, if evenWord u then 2 else 1)]
  else [(u, 1)]

/-- A list represents a sum of basis vectors in characteristic two. -/
def generatorRow (mask : ℕ) (isSign : Bool) (u : Word) : List Word :=
  u :: if affected mask isSign u && !evenWord u then [flip mask u] else []

theorem generatorRow_reduction (mask : ℕ) (isSign : Bool) (u : Word) :
    generatorRow mask isSign u =
      ((integralRow mask isSign u).filter (fun entry => entry.2 % 2 == 1)).map Prod.fst := by
  cases h : affected mask isSign u <;> cases e : evenWord u <;>
    simp [generatorRow, integralRow, h, e]

private abbrev x₁ : Word → List Word := generatorRow 64 false
private abbrev z₁ : Word → List Word := generatorRow 64 true
private abbrev x₂ : Word → List Word := generatorRow 32 false
private abbrev z₂ : Word → List Word := generatorRow 32 true

private def pairRows (M : Word → Word → F₂) (xs ys : List Word) : F₂ :=
  (xs.map fun u => (ys.map (M u)).sum).sum

/-- Strict lower triangle of H - g H gᵗ, in characteristic two. -/
def correction (g : Word → List Word) (u v : Word) : F₂ :=
  if v < u then halfGram u v + pairRows halfGram (g u) (g v) else 0

private def leftLabel (t : Half) : Word :=
  let u := t.val % 16 + 32 * (t.val / 16)
  Fin.ofNat 128 (u + if weight u % 2 = 0 then 0 else 64)

private def rightLabel (t : Half) : Word :=
  flip 127 (flip 32 (leftLabel t))

/-- Even labels, with the third tensor bit separating the two halves.
The right half is indexed by the complement of the slot-two flip
of the corresponding left label. -/
def label (t : Index) : Word :=
  if t.val < 32 then leftLabel (Fin.ofNat 32 t.val) else rightLabel (Fin.ofNat 32 t.val)

def displacementRow (t : Index) : List Word := [label t]
def preimageIRow (t : Index) : List Word := [flip 64 (label t)]
def preimageJRow (t : Index) : List Word :=
  flip 32 (label t) :: if (label t).val.testBit 6 then [] else [flip 64 (label t)]

private def addBasis (xs : List Word) : Charge :=
  (xs.map fun u => Pi.single u (1 : F₂)).sum

private def rowsLinear {n : Type} [Fintype n] (rows : n → List Word) :
    (n → F₂) →ₗ[F₂] Charge where
  toFun a := ∑ u, a u • addBasis (rows u)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

@[simp] private theorem rowsLinear_single {n : Type} [Fintype n] [DecidableEq n]
    (rows : n → List Word) (u : n) :
    rowsLinear rows (Pi.single u 1) = addBasis (rows u) := by
  change (∑ i, (Pi.single u (1 : F₂) : n → F₂) i • addBasis (rows i)) = _
  simp [Pi.single_apply, ite_smul]

private theorem rowsLinear_addBasis (g : Word → List Word) (xs : List Word) :
    rowsLinear g (addBasis xs) = addBasis (xs.flatMap g) := by
  induction xs with
  | nil => simp [addBasis]
  | cons u xs ih =>
    simp only [addBasis, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.map_append, List.sum_append, map_add, rowsLinear_single] at *
    rw [ih]

private theorem addBasis_append (xs ys : List Word) :
    addBasis (xs ++ ys) = addBasis xs + addBasis ys := by
  simp [addBasis, List.sum_append]

private theorem pairRows_apply (M : Word → Word → F₂) (xs ys : List Word) :
    (Matrix.of M).toBilin' (addBasis xs) (addBasis ys) = pairRows M xs ys := by
  have single (u : Word) :
      (Matrix.of M).toBilin' (Pi.single u 1) (addBasis ys) = (ys.map (M u)).sum := by
    induction ys with
    | nil => simp [addBasis]
    | cons v ys ih =>
      simp only [addBasis, List.map_cons, List.sum_cons, map_add,
        Matrix.toBilin'_single, Matrix.of_apply] at *
      rw [ih]
  induction xs with
  | nil => simp [addBasis, pairRows]
  | cons u xs ih =>
    simp only [addBasis, pairRows, List.map_cons, List.sum_cons,
      map_add, LinearMap.add_apply] at *
    rw [← single u, ih]

private abbrev H : LinearMap.BilinForm F₂ Charge :=
  Matrix.toBilin' (Matrix.of halfGram)

/-- The i and j actions on L/2L in row-action order. -/
def actionI : Charge →ₗ[F₂] Charge := (rowsLinear z₁).comp (rowsLinear x₁)
def actionJ : Charge →ₗ[F₂] Charge :=
  (rowsLinear z₂).comp ((rowsLinear x₂).comp (rowsLinear x₁))

private def liftForm (g : Word → List Word) : LinearMap.BilinForm F₂ Charge :=
  Matrix.toBilin' (Matrix.of (correction g))

def phaseI (a : Charge) : F₂ :=
  liftForm x₁ a a + liftForm z₁ (rowsLinear x₁ a) (rowsLinear x₁ a)

def phaseJ (b : Charge) : F₂ :=
  let x := rowsLinear x₁ b
  let y := rowsLinear x₂ x
  liftForm x₁ b b + liftForm x₂ x x + liftForm z₂ y y

def displacement : Coordinate →ₗ[F₂] Charge := rowsLinear displacementRow
def preimageI : Coordinate →ₗ[F₂] Charge := rowsLinear preimageIRow
def preimageJ : Coordinate →ₗ[F₂] Charge := rowsLinear preimageJRow

def traceExponent (x : Coordinate) : F₂ :=
  let w := displacement x
  let a := preimageI x
  let b := preimageJ x
  phaseI a + phaseJ b + H w (a + b + w)

private def cancelPairs : List Word → List Word
  | [] => []
  | u :: us =>
    let tail := cancelPairs us
    if u ∈ tail then tail.erase u else u :: tail

private theorem addBasis_cancelPairs (us : List Word) :
    addBasis (cancelPairs us) = addBasis us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    by_cases h : u ∈ cancelPairs us
    · have hp := (List.perm_cons_erase h).map (fun v => Pi.single v (1 : F₂))
      have hs : addBasis (cancelPairs us) =
          Pi.single u 1 + addBasis ((cancelPairs us).erase u) := hp.sum_eq
      simp only [cancelPairs, ite_eq_left h, addBasis, List.map_cons, List.sum_cons]
      change addBasis ((cancelPairs us).erase u) = Pi.single u 1 + addBasis us
      rw [← ih, hs, ← add_assoc]
      funext v
      simp only [Pi.add_apply, CharTwo.add_self_eq_zero, zero_add]
    · simp only [cancelPairs, ite_eq_right h]
      change Pi.single u 1 + addBasis (cancelPairs us) = Pi.single u 1 + addBasis us
      rw [ih]

private def advanceI (us : List Word) : List Word := (us.flatMap x₁).flatMap z₁
private def advanceJ (us : List Word) : List Word :=
  ((us.flatMap x₁).flatMap x₂).flatMap z₂

private theorem actionI_addBasis (us : List Word) :
    actionI (addBasis us) = addBasis (advanceI us) := by
  simp [actionI, advanceI, rowsLinear_addBasis]

private theorem actionJ_addBasis (us : List Word) :
    actionJ (addBasis us) = addBasis (advanceJ us) := by
  simp [actionJ, advanceJ, rowsLinear_addBasis]

private theorem preimageI_check : ∀ t : Index,
    cancelPairs (advanceI (preimageIRow t) ++ preimageIRow t) = displacementRow t := by
  decide +kernel

private theorem preimageJ_check : ∀ t : Index,
    cancelPairs (advanceJ (preimageJRow t) ++ preimageJRow t) = displacementRow t := by
  decide +kernel

private def deltaI : Charge →ₗ[F₂] Charge := actionI + LinearMap.id
private def deltaJ : Charge →ₗ[F₂] Charge := actionJ + LinearMap.id

private theorem preimageI_linear : deltaI.comp preimageI = displacement := by
  apply (Pi.basisFun F₂ Index).ext
  intro t
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, preimageI, displacement, rowsLinear_single,
    deltaI, LinearMap.add_apply, LinearMap.id_apply, actionI_addBasis, ← addBasis_append]
  rw [← addBasis_cancelPairs, preimageI_check]

private theorem preimageJ_linear : deltaJ.comp preimageJ = displacement := by
  apply (Pi.basisFun F₂ Index).ext
  intro t
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, preimageJ, displacement, rowsLinear_single,
    deltaJ, LinearMap.add_apply, LinearMap.id_apply, actionJ_addBasis, ← addBasis_append]
  rw [← addBasis_cancelPairs, preimageJ_check]

/-- The sections solve the two displacement equations on every charge
in the 64-coordinate parametrization. -/
theorem actual_preimages (x : Coordinate) :
    actionI (preimageI x) + preimageI x = displacement x ∧
    actionJ (preimageJ x) + preimageJ x = displacement x :=
  ⟨LinearMap.congr_fun preimageI_linear x, LinearMap.congr_fun preimageJ_linear x⟩

private def indexOf (u : Word) : Index :=
  let onRight := u.val.testBit 4
  let left := if onRight then flip 32 (flip 127 u) else u
  Fin.ofNat 64 (left.val % 16 + (if left.val.testBit 5 then 16 else 0) +
    if onRight then 32 else 0)

private theorem label_indexOf : ∀ u : Word, evenWord u → label (indexOf u) = u := by
  decide +kernel

private theorem indexOf_label : ∀ t : Index, indexOf (label t) = t := by
  decide +kernel

theorem displacement_injective : Function.Injective displacement := by
  intro x y h
  funext t
  have hl : Function.Injective label := Function.LeftInverse.injective indexOf_label
  have read (x : Coordinate) : displacement x (label t) = x t := by
    change (∑ u, x u • addBasis [label u]) (label t) = _
    rw [Finset.sum_apply]
    simp only [addBasis, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [hl.eq_iff]
  simpa only [read] using congrFun h (label t)

private theorem range_of_even_rows (us : List Word) (h : us.all evenWord) :
    addBasis us ∈ LinearMap.range displacement := by
  induction us with
  | nil => simp [addBasis]
  | cons u us ih =>
    have he : evenWord u ∧ us.all evenWord := by simpa using h
    have hu : Pi.single u (1 : F₂) ∈ LinearMap.range displacement := by
      refine ⟨Pi.single (indexOf u) 1, ?_⟩
      simp [displacement, displacementRow, label_indexOf u he.1, addBasis]
    exact (LinearMap.range displacement).add_mem hu (ih he.2)

private theorem deltaI_even : ∀ u : Word,
    (cancelPairs (advanceI [u] ++ [u])).all evenWord := by decide +kernel

private theorem deltaJ_even : ∀ u : Word,
    (cancelPairs (advanceJ [u] ++ [u])).all evenWord := by decide +kernel

private theorem image_in_even
    (delta : Charge →ₗ[F₂] Charge) (rows : Word → List Word)
    (hrows : ∀ u : Word, delta (Pi.single u 1) = addBasis (rows u))
    (he : ∀ u, (rows u).all evenWord) :
    LinearMap.range delta ≤ LinearMap.range displacement := by
  have h : delta = rowsLinear rows := by
    apply (Pi.basisFun F₂ Word).ext
    intro u
    simpa using hrows u
  rw [h]
  rintro _ ⟨x, rfl⟩
  change (∑ u, x u • addBasis (rows u)) ∈ LinearMap.range displacement
  exact Submodule.sum_mem _ fun u _ =>
    Submodule.smul_mem _ _ (range_of_even_rows _ (he u))

/-- Both displacements have exactly the same image, parametrized
without multiplicity by the even tensor words. -/
theorem displacement_images :
    LinearMap.range (actionI + LinearMap.id) = LinearMap.range displacement ∧
    LinearMap.range (actionJ + LinearMap.id) = LinearMap.range displacement := by
  change LinearMap.range deltaI = _ ∧ LinearMap.range deltaJ = _
  constructor
  · apply le_antisymm
    · apply image_in_even deltaI (fun u => cancelPairs (advanceI [u] ++ [u])) _ deltaI_even
      intro u
      rw [addBasis_cancelPairs, addBasis_append, ← actionI_addBasis]
      simp [deltaI, addBasis]
    · rintro _ ⟨x, rfl⟩
      exact ⟨preimageI x, (actual_preimages x).1⟩
  · apply le_antisymm
    · apply image_in_even deltaJ (fun u => cancelPairs (advanceJ [u] ++ [u])) _ deltaJ_even
      intro u
      rw [addBasis_cancelPairs, addBasis_append, ← actionJ_addBasis]
      simp [deltaJ, addBasis]
    · rintro _ ⟨x, rfl⟩
      exact ⟨preimageJ x, (actual_preimages x).2⟩

private def coefficient : Matrix Index Index F₂ := fun u v =>
  let a := preimageIRow u
  let a' := preimageIRow v
  let b := preimageJRow u
  let b' := preimageJRow v
  let x := b.flatMap x₁
  let x' := b'.flatMap x₁
  pairRows (correction x₁) a a' +
    pairRows (correction z₁) (a.flatMap x₁) (a'.flatMap x₁) +
    (pairRows (correction x₁) b b' +
      pairRows (correction x₂) x x' +
      pairRows (correction z₂) (x.flatMap x₂) (x'.flatMap x₂)) +
    pairRows halfGram (displacementRow u) (a' ++ b' ++ displacementRow v)

private def traceForm : LinearMap.BilinForm F₂ Coordinate :=
  let ai := preimageI
  let ax := (rowsLinear x₁).comp ai
  let bj := preimageJ
  let bx := (rowsLinear x₁).comp bj
  let by' := (rowsLinear x₂).comp bx
  (liftForm x₁).comp ai ai + (liftForm z₁).comp ax ax +
    ((liftForm x₁).comp bj bj + (liftForm x₂).comp bx bx + (liftForm z₂).comp by' by') +
    H.comp displacement (ai + bj + displacement)

private theorem traceForm_eq :
    traceForm = Matrix.toBilin' (coefficient : Matrix Index Index F₂) := by
  classical
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun F₂ Index)
  intro u v
  simp only [Pi.basisFun_apply, Matrix.toBilin'_single, traceForm, LinearMap.add_apply,
    LinearMap.BilinForm.comp_apply, LinearMap.comp_apply, preimageI, preimageJ, displacement,
    rowsLinear_single, rowsLinear_addBasis, liftForm]
  rw [← addBasis_append (preimageIRow v) (preimageJRow v),
    ← addBasis_append (preimageIRow v ++ preimageJRow v) (displacementRow v)]
  simp only [coefficient, pairRows_apply]

private def mate (t : Half) : Half := Fin.ofNat 32 (t.val ^^^ 16)
private def shear (t : Half) : Bool := (leftLabel t).val.testBit 6

private def cross : Matrix Index Index F₂ := fun u v =>
  if u.val < 32 ∧ 32 ≤ v.val then
    let s := Fin.ofNat 32 u.val
    let t := Fin.ofNat 32 v.val
    (if s = t then 1 else 0) + (if shear s && (mate s == t) then 1 else 0)
  else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
-- The kernel evaluates the coefficients for all 64 × 64 basis pairs.
private theorem coefficient_check :
    ∀ u v : Index, coefficient u v + coefficient v u = cross u v + cross v u := by
  intro u
  fin_cases u <;> decide +kernel

set_option maxHeartbeats 0 in
-- The same coefficient expression is evaluated on all 64 diagonal entries.
private theorem diagonal_check : ∀ u : Index, coefficient u u = cross u u := by
  decide +kernel

private theorem same_quadratic {n : Type} [Fintype n] [LinearOrder n]
    (A B : Matrix n n F₂)
    (hdiag : ∀ u, A u u = B u u)
    (hpolar : ∀ u v, A u v + A v u = B u v + B v u)
    (x : n → F₂) : A.toBilin' x x = B.toBilin' x x := by
  have hs : (A - B).IsSymm := by
    ext u v
    simp only [Matrix.transpose_apply, Matrix.sub_apply]
    have hp := hpolar u v
    have hz (a : F₂) : -a = a := neg_eq_of_add_eq_zero_left (CharTwo.add_self_eq_zero a)
    simp only [sub_eq_add_neg, hz]
    calc
      A v u + B v u = (A u v + A v u) + (A u v + B v u) := by
        rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]
      _ = B u v + A u v := by
        rw [hp]
        rw [show B u v + B v u + (A u v + B v u) =
          (B u v + A u v) + (B v u + B v u) by abel,
          CharTwo.add_self_eq_zero, add_zero]
      _ = _ := add_comm _ _
  have h := symmetric_pairing_split (A - B) hs x x
  have hzero (u : n) : (A - B) u u = 0 := by simp [hdiag]
  simp only [hzero, zero_mul, Finset.sum_const_zero, CharTwo.add_self_eq_zero,
    mul_zero] at h
  simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using h

/-- The actual lift exponent reduces to the two cross blocks of the
third-bit split. The computation checks only pairs of basis coordinates. -/
theorem traceExponent_cross (x : Coordinate) :
    traceExponent x = Matrix.toBilin' (cross : Matrix Index Index F₂) x x := by
  change traceForm x x = _
  rw [traceForm_eq]
  exact same_quadratic _ _ diagonal_check coefficient_check x

private def twist (y : Half → F₂) (t : Half) : F₂ :=
  y t + if shear t then y (mate t) else 0

private theorem twist_involutive : Function.Involutive twist := by
  have ht : ∀ t : Half, shear (mate t) = !shear t := by decide
  intro y
  funext t
  cases h : shear t with
  | false => simp [twist, h]
  | true =>
    have ht' : shear (mate t) = false := by simpa [h] using ht t
    simp [twist, h, ht', add_assoc, CharTwo.add_self_eq_zero]

private def twistEquiv : (Half → F₂) ≃ (Half → F₂) :=
  ⟨twist, twist, twist_involutive, twist_involutive⟩

private theorem cross_of_blocks {n : ℕ}
    (A : Matrix (Fin (n + n)) (Fin (n + n)) F₂) (x : Fin (n + n) → F₂)
    (shear' : Fin n → Bool) (mate' : Fin n → Fin n)
    (right_zero : ∀ s j, A (Fin.natAdd n s) j = 0)
    (left_zero : ∀ s t, A (Fin.castAdd n s) (Fin.castAdd n t) = 0)
    (mixed : ∀ s t, A (Fin.castAdd n s) (Fin.natAdd n t) =
      (if s = t then 1 else 0) + (if shear' s ∧ mate' s = t then 1 else 0)) :
    A.toBilin' x x = ∑ t : Fin n,
      x (Fin.castAdd n t) *
        (x (Fin.natAdd n t) + if shear' t then x (Fin.natAdd n (mate' t)) else 0) := by
  rw [Matrix.toBilin'_apply, Fin.sum_univ_add (a := n) (b := n)]
  simp only [right_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Fin.sum_univ_add (a := n) (b := n)]
  simp only [left_zero, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, mixed]
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  cases shear' s <;> simp

private theorem cross_eval (x : Coordinate) :
    cross.toBilin' x x =
      ∑ t : Half, x (Fin.castAdd 32 t) * twist (fun s => x (Fin.natAdd 32 s)) t := by
  apply cross_of_blocks cross x shear mate
  · intro s j
    simp [cross, Fin.natAdd]
  · intro s t
    simp [cross, Fin.castAdd, t.isLt]
  · intro s t
    have l : (Fin.ofNat 32 (Fin.castAdd 32 s).val) = s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
    have r : (Fin.ofNat 32 (Fin.natAdd 32 t).val) = t := by
      apply Fin.ext
      change (32 + t.val) % 32 = t.val
      omega
    unfold cross
    rw [ite_eq_left ⟨s.isLt, by simp [Fin.natAdd]⟩]
    rw [l, r]
    simp

private theorem dot_sign_sum :
    (∑ p : (Half → F₂) × (Half → F₂), complexSign (∑ t, p.1 t * p.2 t)) =
      (2 : ℂ) ^ 32 := by
  classical
  have local_sum : (∑ p : F₂ × F₂, complexSign (p.1 * p.2)) = (2 : ℂ) := by
    have h := BinaryGauss.block_sum 0 1 0 (by decide)
    have hc : ZMod.χ₈ (BinaryGauss.gram 0 1 0).det = 1 := by decide
    simpa [BinaryGauss.quadratic, show residue 0 = 0 by decide,
      show residue 1 = 1 by decide, hc] using h
  rw [← (Equiv.arrowProdEquivProdArrow Half (fun _ => F₂) (fun _ => F₂)).sum_comp]
  change (∑ p : Half → F₂ × F₂, complexSign (∑ t, (p t).1 * (p t).2)) = _
  simp_rw [sign_sum Finset.univ]
  rw [← Fintype.prod_sum (fun (_ : Half) (p : F₂ × F₂) => complexSign (p.1 * p.2))]
  simp [local_sum]

/-- The finite Gauss sum for the actual rank-128 trace-product exponent. -/
theorem trace_gauss_sum :
    (∑ x : Coordinate, complexSign (traceExponent x)) = (2 : ℂ) ^ 32 := by
  classical
  let split : Coordinate ≃ (Half → F₂) × (Half → F₂) :=
    (Equiv.arrowCongr (finSumFinEquiv (m := 32) (n := 32)).symm (Equiv.refl F₂)).trans
      (Equiv.sumArrowEquivProdArrow Half Half F₂)
  have h (p : (Half → F₂) × (Half → F₂)) :
      traceExponent (split.symm p) = ∑ t, p.1 t * twist p.2 t := by
    rw [traceExponent_cross, cross_eval]
    change (∑ t : Half,
      Sum.elim p.1 p.2 (finSumFinEquiv.symm (Fin.castAdd 32 t)) *
        twist (fun s => Sum.elim p.1 p.2 (finSumFinEquiv.symm (Fin.natAdd 32 s))) t) = _
    simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inl, Sum.elim_inr, twist]
  rw [← split.symm.sum_comp (fun x => complexSign (traceExponent x))]
  simp_rw [h]
  have hs := dot_sign_sum
  rw [← (Equiv.prodCongr (Equiv.refl (Half → F₂)) twistEquiv).sum_comp
    (fun p : (Half → F₂) × (Half → F₂) => complexSign (∑ t, p.1 t * p.2 t))] at hs
  exact hs

abbrev CommonImage :=
  ↥(LinearMap.range (actionI + LinearMap.id) ⊓ LinearMap.range (actionJ + LinearMap.id))

private noncomputable def commonImageEquiv : Coordinate ≃ CommonImage :=
  ((LinearEquiv.ofInjective displacement displacement_injective).trans
    (LinearEquiv.ofEq _ _ (by rw [displacement_images.1, displacement_images.2, inf_idem]))).toEquiv

noncomputable instance : Fintype CommonImage := Fintype.ofEquiv Coordinate commonImageEquiv

/-- The exponent on the intersection, evaluated using the explicit sections. -/
noncomputable def defectGroundExponent (w : CommonImage) : F₂ :=
  let x := commonImageEquiv.symm w
  let a := preimageI x
  let b := preimageJ x
  phaseI a + phaseJ b + H w.val (a + b + w.val)

/-- The Gauss sum over the actual common displacement image. -/
theorem defect_ground_gauss_sum :
    (∑ w : CommonImage, complexSign (defectGroundExponent w)) = (2 : ℂ) ^ 32 := by
  rw [← commonImageEquiv.sum_comp (fun w => complexSign (defectGroundExponent w))]
  convert trace_gauss_sum using 1
  apply Finset.sum_congr rfl
  intro x _
  have hw : (commonImageEquiv x).val = displacement x := rfl
  simp only [defectGroundExponent, Equiv.symm_apply_apply, hw, traceExponent]

#print axioms defect_ground_gauss_sum

end D5.S3.VertexAlgebra.TwistedGround.BarnesWallQ8TraceSign
