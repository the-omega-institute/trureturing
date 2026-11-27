/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pBinaryInvariantForms
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pBinaryInvariantForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48p catalogue transvections fix exactly three nonzero binary forms, cycled by z. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameLatticeAction
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# Binary invariant forms of the P48p catalogue action

A column form evaluates the catalogue row vector by pairing with it. The right
action on lattice rows thus pulls back column forms by left multiplication by
the same matrix reduced modulo two. Each nonzero form defines an index-two
sublattice by its kernel.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pBinaryInvariantForms

open scoped Matrix BigOperators
open P48pSyndromeFrame (p48pFrameRows p48pPairingFrame p48pPairingFrame_eq)
open P48pSymmetricCommutantCertificate
  (catalogueFrameMap tCatalogueMap uCatalogueMap zCatalogueMap tFrameMatrix uFrameMatrix Z1)
open private tIndex tSign uIndex uSign from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
open private signedRows signed_mul_frame cubicRows cubic_mul_frame from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameLatticeAction
open private dotOfFn_eq from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate

abbrev BinaryForm := Fin 48 → ZMod 2
private abbrev BinaryMatrix := Matrix (Fin 48) (Fin 48) (ZMod 2)
private abbrev IntMatrix := Matrix (Fin 48) (Fin 48) ℤ

/-- Bit zero is catalogue coordinate zero. -/
def formOfMask (mask : Nat) : BinaryForm :=
  fun i => if mask.testBit i.val then 1 else 0

private abbrev maskA : Nat := 0x7c8000000000
private abbrev maskB : Nat := 0x2dbdb669e03b
private abbrev maskC : Nat := 0x513db669e03b

def formA : BinaryForm := formOfMask maskA
def formB : BinaryForm := formOfMask maskB
def formC : BinaryForm := formOfMask maskC

/-- Entrywise reduction of the integral catalogue matrix in characteristic two. -/
def modTwo (M : Matrix (Fin 48) (Fin 48) ℤ) : Matrix (Fin 48) (Fin 48) (ZMod 2) :=
  M.map (Int.castRingHom (ZMod 2))

private def rowMask (table : Array Nat) (i : Fin 48) : Nat := table.getD i.val 0

private def tRows : Array Nat := #[
  0xf537c1d33c2f, 0xa0d87efc1a4d, 0x939354885728, 0xaca45474a153,
  0xc18649ad3328, 0xa943e395a49a, 0x5aacd30be80c, 0x4711c5adccd7,
  0x8372e2e95ec5, 0x88941ca936c9, 0xcb60707c1e15, 0xfee3b59a8003,
  0x76653bd7b665, 0xcdd0efa21f9a, 0xccbe866e09ce, 0xa3e425d9ff7a,
  0xc7550920fb0, 0x43a86b538ea7, 0x3c5a7ca8f724, 0x28233106d4f2,
  0x5f3310002021, 0xd11c68870b38, 0x50704c2bae7b, 0xf42057e9e4d7,
  0x311712bf5081, 0xc546860ccd43, 0x8e45f06d3ea9, 0xbae1b2d1d14f,
  0x3b99706f6e4e, 0xb8fb231d08db, 0xf955e47373fe, 0x92ff945812b0,
  0xe3cc3818450, 0x196fe5f2b390, 0x8ef0169ccfb, 0x51488a685eed,
  0xfea98a4422b4, 0x42b85263cc25, 0xc40d20ed153c, 0xa124b4b9c67d,
  0x1b673fede82d, 0xaa0375d56df7, 0x1e316fc158b7, 0x405fd17ec85c,
  0xf9d752635ab2, 0x125bb0725c5c, 0x9121483c6919, 0x995fe5f49626
]

private def uRows : Array Nat := #[
  0x569341d5dd42, 0xbda3573653d, 0xa0d1369fc37e, 0xed038fa63878,
  0x23e12b2102dc, 0xf756d5eef1ed, 0xbc261c2d208, 0xdabd3fbc0f9e,
  0xc61904c46df4, 0x6499651540c9, 0x773dc4f6ac26, 0x548ea08452d4,
  0xfdaa6a38698f, 0x783d2f075914, 0x109f945566c, 0x44397b7ae85a,
  0x7b737bb3ab49, 0xde6ca6fdecd6, 0x3a971f76c941, 0xca52de56b3d5,
  0x35a6beaa6764, 0x55f41c3e3725, 0x3f513fcef04d, 0xfdd9f1e22a49,
  0xafd18ecb586b, 0x2ffa1897e6dc, 0x443a9d436284, 0xca7097234cc9,
  0x4a4185fd0b9d, 0x7da0ee2c93a5, 0x37e54612deb2, 0xd8ccc7b5d67a,
  0xef7d02b1c3a7, 0x13c1b05614e, 0x88e0cb208b6b, 0x6c2f1d97b3f,
  0xe9d145de745c, 0xaa41c14db204, 0xfb48f9cac74c, 0x8a162855ebb3,
  0xafc1dc35ecfc, 0xced2401034cb, 0x3650203c0a02, 0x26cdfc916851,
  0x778cb3ec7405, 0x6ed3c5cc1f63, 0x3fd891d834f, 0x7a55b2df8c27
]

private def zRows : Array Nat := #[
  0x4f3f1052f9d6, 0x80c267df387, 0xbee2f1123a3, 0x73f5299b549,
  0x3ce161257133, 0x5ed857e332fb, 0xf2b727ba2770, 0xc747056c7da2,
  0xac94abdb1ec7, 0x1dfa05ec8d49, 0x94ab6362a, 0xec4bcad58228,
  0x6c41573c9f6c, 0xd47853c18cfe, 0xdcbd9e409eea, 0x638543af80da,
  0xad2ebe466109, 0xcd82709d588c, 0x77755c604a51, 0x535f0fc2728,
  0xca7f544df103, 0x5fc9aab909b1, 0xe42bad3590a1, 0xf1eb2febc4c8,
  0x1575fa24466b, 0xb1834a3df483, 0x27951e4f9286, 0xf7501a727bcd,
  0x58613957c1fa, 0x1ae758d2b325, 0xf904f8ecb5af, 0x32ae34ddc880,
  0x4784c03d9bd8, 0x4977a12cfdde, 0x6fafb8e7ba73, 0xd2d1b76a6170,
  0xbdaa54ff9ba0, 0xa03462abe80f, 0xd6a4394ff91b, 0x48a43c49ce66,
  0x49d8704de64e, 0x90b106c74d0b, 0x3eba010ff3d8, 0xaa850f3c53b9,
  0x4b683370b4a6, 0x418d8fc9960, 0x5ae07212ae05, 0x830f6ace1533
]

private theorem catalogueEntry {O B : IntMatrix} {n : ℤ} (hn : 0 < n)
    (h : O * p48pFrameRows = n • B) (i j : Fin 48) :
    catalogueFrameMap O n i j = (p48pPairingFrame * B) i j / 12 := by
  rw [catalogueFrameMap, ← p48pPairingFrame_eq, Matrix.mul_assoc, h, Matrix.mul_smul,
    Matrix.smul_apply, zsmul_eq_mul]
  rw [mul_comm n ((p48pPairingFrame * B) i j), Int.mul_ediv_mul_of_pos_left _ _ hn]

private def rowRemainders (B : IntMatrix) (i : Fin 48) : List ℤ :=
  List.ofFn fun j : Fin 48 =>
    (List.zipWith (· * ·) (List.ofFn (p48pPairingFrame i))
      (List.ofFn fun k : Fin 48 => B k j)).sum / 12 % 2

private def maskRemainders (mask : Nat) : List ℤ :=
  List.ofFn fun j : Fin 48 => if mask.testBit j.val then 1 else 0

private theorem matrixOfMasks (M B : IntMatrix) (table : Array Nat)
    (hM : ∀ i j, M i j = (p48pPairingFrame * B) i j / 12)
    (h : ∀ i, rowRemainders B i = maskRemainders (rowMask table i)) :
    modTwo M = fun i => formOfMask (rowMask table i) := by
  apply Matrix.ext
  intro i j
  have hEntry := congrFun (List.ofFn_injective (h i)) j
  change (List.zipWith (· * ·) (List.ofFn (p48pPairingFrame i))
      (List.ofFn fun k : Fin 48 => B k j)).sum / 12 % 2 =
    (if (rowMask table i).testBit j.val then 1 else 0 : ℤ) at hEntry
  rw [dotOfFn_eq, ← Matrix.mul_apply (M := p48pPairingFrame) (N := B)] at hEntry
  change ((M i j : ℤ) : ZMod 2) = if (rowMask table i).testBit j.val then 1 else 0
  rw [hM]
  by_cases hb : (rowMask table i).testBit j.val = true
  · rw [if_pos hb, ← Int.cast_one]
    exact (ZMod.intCast_eq_intCast_iff' _ _ 2).2
      (by simpa only [if_pos hb, show (1 : ℤ) % 2 = 1 by decide] using hEntry)
  · rw [if_neg hb, ← Int.cast_zero]
    exact (ZMod.intCast_eq_intCast_iff' _ _ 2).2
      (by simpa only [if_neg hb, show (0 : ℤ) % 2 = 0 by decide] using hEntry)

set_option maxHeartbeats 12000000 in
private theorem tRows_correct : modTwo tCatalogueMap = fun i => formOfMask (rowMask tRows i) := by
  refine matrixOfMasks _ (signedRows tIndex tSign) _ ?_ ?_
  · exact catalogueEntry (O := tFrameMatrix) (n := 1) (by decide)
      (by rw [tFrameMatrix, signed_mul_frame, one_smul])
  · intro i
    fin_cases i <;> decide +kernel

set_option maxHeartbeats 12000000 in
private theorem uRows_correct : modTwo uCatalogueMap = fun i => formOfMask (rowMask uRows i) := by
  refine matrixOfMasks _ (signedRows uIndex uSign) _ ?_ ?_
  · exact catalogueEntry (O := uFrameMatrix) (n := 1) (by decide)
      (by rw [uFrameMatrix, signed_mul_frame, one_smul])
  · intro i
    fin_cases i <;> decide +kernel

set_option maxHeartbeats 12000000 in
private theorem zRows_correct : modTwo zCatalogueMap = fun i => formOfMask (rowMask zRows i) := by
  refine matrixOfMasks _ cubicRows _ ?_ ?_
  · exact catalogueEntry (O := Z1) (n := 12) (by decide) cubic_mul_frame
  · intro i
    fin_cases i <;> decide +kernel

private theorem sum_ofFn_eq {n : Nat} (f : Fin n → ZMod 2) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ, ih]

private def maskDot (row column : Nat) : ZMod 2 :=
  (List.ofFn fun j : Fin 48 => formOfMask row j * formOfMask column j).sum

private theorem maskAction {M : BinaryMatrix} {table : Array Nat} {x y : Nat}
    (hM : M = fun i => formOfMask (rowMask table i))
    (h : ∀ i, maskDot (rowMask table i) x = formOfMask y i) :
    M *ᵥ formOfMask x = formOfMask y := by
  funext i
  rw [hM]
  simpa only [maskDot, sum_ofFn_eq, Matrix.mulVec, dotProduct] using h i

private theorem t_fixesA : modTwo tCatalogueMap *ᵥ formA = formA := by
  apply maskAction (x := maskA) (y := maskA) tRows_correct
  intro i
  fin_cases i <;> decide +kernel

private theorem t_fixesB : modTwo tCatalogueMap *ᵥ formB = formB := by
  apply maskAction (x := maskB) (y := maskB) tRows_correct
  intro i
  fin_cases i <;> decide +kernel

private theorem u_fixesA : modTwo uCatalogueMap *ᵥ formA = formA := by
  apply maskAction (x := maskA) (y := maskA) uRows_correct
  intro i
  fin_cases i <;> decide +kernel

private theorem u_fixesB : modTwo uCatalogueMap *ᵥ formB = formB := by
  apply maskAction (x := maskB) (y := maskB) uRows_correct
  intro i
  fin_cases i <;> decide +kernel

/-- The catalogue generator acts by pullback around the three nonzero forms. -/
theorem z_cycles_forms :
    modTwo zCatalogueMap *ᵥ formA = formB ∧
    modTwo zCatalogueMap *ᵥ formB = formC ∧
    modTwo zCatalogueMap *ᵥ formC = formA := by
  refine ⟨maskAction (x := maskA) (y := maskB) zRows_correct ?_,
    maskAction (x := maskB) (y := maskC) zRows_correct ?_,
    maskAction (x := maskC) (y := maskA) zRows_correct ?_⟩ <;>
    intro i <;> fin_cases i <;> decide +kernel

private theorem formOfMask_xor (r s : Nat) :
    formOfMask (r ^^^ s) = formOfMask r + formOfMask s := by
  funext i
  simp only [formOfMask, Nat.testBit_xor, Pi.add_apply]
  cases r.testBit i.val <;> cases s.testBit i.val <;> decide +kernel

private theorem formOfMask_zero : formOfMask 0 = 0 := by
  funext i
  simp [formOfMask]

private theorem formOfMask_unit (i : Fin 48) :
    formOfMask (2 ^ i.val) = Pi.single i (1 : ZMod 2) := by
  funext j
  by_cases h : i = j
  · subst j
    simp [formOfMask]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [formOfMask, Nat.testBit_two_pow, hv, Pi.single_eq_of_ne (Ne.symm h)]

private theorem formOfMask_selectedUnit (b : Bool) (i : Fin 48) :
    formOfMask (if b then 2 ^ i.val else 0) =
      (if b then (1 : ZMod 2) else 0) • Pi.single i (1 : ZMod 2) := by
  cases b <;> simp [formOfMask_zero, formOfMask_unit]

private theorem formA_add_formB : formA + formB = formC := by
  exact (formOfMask_xor maskA maskB).symm

private def differenceRows (table : Array Nat) : List Nat :=
  List.ofFn fun i : Fin 48 => rowMask table i ^^^ 2 ^ i.val

private def stackedRows : List Nat := differenceRows tRows ++ differenceRows uRows

private theorem differenceRows_annihilate {M : BinaryMatrix} {table : Array Nat} {a : BinaryForm}
    (hM : M = fun i => formOfMask (rowMask table i)) (h : M *ᵥ a = a) :
    ∀ row ∈ differenceRows table, formOfMask row ⬝ᵥ a = 0 := by
  intro row hRow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hRow
  rw [hM] at h
  have hEntry : formOfMask (rowMask table i) ⬝ᵥ a = a i := congrFun h i
  rw [formOfMask_xor, add_dotProduct, formOfMask_unit, single_one_dotProduct, hEntry]
  exact CharTwo.add_self_eq_zero _

/-- Select a binary linear combination of the rows, with the first row at bit zero. -/
private def xorSelected : List Nat → Nat → Nat
  | [], _ => 0
  | row :: rows, selected =>
    let rest := xorSelected rows (selected / 2)
    if selected.testBit 0 then row ^^^ rest else rest

private theorem xorSelected_annihilates (a : BinaryForm) (rows : List Nat)
    (h : ∀ row ∈ rows, formOfMask row ⬝ᵥ a = 0) (selected : Nat) :
    formOfMask (xorSelected rows selected) ⬝ᵥ a = 0 := by
  induction rows generalizing selected with
  | nil => simp [xorSelected, formOfMask_zero]
  | cons row rows ih =>
    have hHead := h row (List.mem_cons_self)
    have hRest := ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) (selected / 2)
    simp only [xorSelected]
    split
    · rw [formOfMask_xor, add_dotProduct, hHead, hRest, add_zero]
    · exact hRest

/-
The selectors replay Gaussian elimination on the 48 t-I rows followed by the
48 u-I rows. Coordinates 44 and 0 are left free. Each other output has one
pivot and at most the two free coordinates. The two free outputs are zero.
-/
private def eliminationSelectors : Array Nat := #[
  0x0, 0xca8a2493f1eea, 0x4002e98218280,
  0x886cdfabac82d, 0xc886a71647062, 0xc02482fdf4de5,
  0xc8ec4c09ec734, 0x486eb8a55b31f, 0xac80ba5e48d0,
  0x864153a60c1b, 0x48ee70bfadf62, 0x40408ad5ca0c8,
  0x22e76d74f7bc, 0x4a24331f6376e, 0xca863565a687e,
  0xea6447f3522, 0x8a08a3bde56a9, 0x8844153c08a2d,
  0x8a8e48265a0d1, 0xca8a4e3250855, 0xc2081b23a7c4b,
  0x88ae51e1d8204, 0x48a44c107b1e4, 0x8820b73335fac,
  0x2a4c4e5a4972, 0xc200d6d335baa, 0x88c22ff1a9ed3,
  0xc8e69ebb42ed0, 0xc026b56b2c85e, 0x8882c35e07f15,
  0x40044749bd24e, 0x808c815ab6431, 0x2c026e1e9946,
  0x8284fc67f9463, 0xca0c79ce9e943, 0xc20e3e8fc7741,
  0x22e3dbb944e9, 0x4826a49c14858, 0x88827daa281a5,
  0x82066cf9b73de, 0x4a0856db761aa, 0x826efd61a56da,
  0x20e8ec0af42f, 0x8ac0a46a859b4, 0x0,
  0x2e4d916ce29d, 0x2cadd1a755e1, 0x8e09dea3dd7f
]

private def pivotTarget (i : Fin 48) : Nat :=
  (2 ^ i.val ^^^ (if maskA.testBit i.val then 2 ^ (44 : Fin 48).val else 0)) ^^^
    (if maskB.testBit i.val then 2 ^ (0 : Fin 48).val else 0)

set_option maxHeartbeats 3000000 in
private theorem eliminationCertificate (i : Fin 48) :
    xorSelected stackedRows (rowMask eliminationSelectors i) = pivotTarget i := by
  fin_cases i <;> decide +kernel

private theorem fixed_coordinates {a : BinaryForm}
    (ht : modTwo tCatalogueMap *ᵥ a = a) (hu : modTwo uCatalogueMap *ᵥ a = a) :
    a = a 44 • formA + a 0 • formB := by
  have h : ∀ row ∈ stackedRows, formOfMask row ⬝ᵥ a = 0 := by
    intro row hr
    rcases List.mem_append.mp hr with hr | hr
    · exact differenceRows_annihilate tRows_correct ht row hr
    · exact differenceRows_annihilate uRows_correct hu row hr
  funext i
  have hi := xorSelected_annihilates a stackedRows h (rowMask eliminationSelectors i)
  rw [eliminationCertificate] at hi
  simp only [pivotTarget, formOfMask_xor, formOfMask_unit i,
    formOfMask_selectedUnit (maskA.testBit i.val) 44,
    formOfMask_selectedUnit (maskB.testBit i.val) 0, add_dotProduct, smul_dotProduct,
    single_one_dotProduct, smul_eq_mul] at hi
  have hEq : a i = formA i * a 44 + formB i * a 0 := by
    apply CharTwo.add_eq_zero.mp
    rw [← add_assoc]
    exact hi
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm (a 44), mul_comm (a 0)]
    using hEq

private theorem fixed_combination (s t : ZMod 2) :
    modTwo tCatalogueMap *ᵥ (s • formA + t • formB) = s • formA + t • formB ∧
    modTwo uCatalogueMap *ᵥ (s • formA + t • formB) = s • formA + t • formB := by
  constructor
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, t_fixesA, t_fixesB]
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, u_fixesA, u_fixesB]

private theorem zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h := ZMod.val_lt x
  have hv : x.val = 0 ∨ x.val = 1 := by omega
  rcases hv with h0 | h1
  · exact Or.inl (ZMod.val_injective 2 h0)
  · exact Or.inr (ZMod.val_injective 2 h1)

/-- The full list of binary forms fixed by both catalogue generators. -/
theorem common_fixed_iff (a : BinaryForm) :
    (modTwo tCatalogueMap *ᵥ a = a ∧ modTwo uCatalogueMap *ᵥ a = a) ↔
    a = 0 ∨ a = formA ∨ a = formB ∨ a = formC := by
  constructor
  · rintro ⟨ht, hu⟩
    have ha := fixed_coordinates ht hu
    rcases zero_or_one (a 44) with h44 | h44 <;>
      rcases zero_or_one (a 0) with h0 | h0 <;>
      simp only [h44, h0, zero_smul, one_smul, zero_add, add_zero, formA_add_formB] at ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr ha))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
    · exact ⟨t_fixesA, u_fixesA⟩
    · exact ⟨t_fixesB, u_fixesB⟩
    · simpa only [one_smul, formA_add_formB] using fixed_combination 1 1

private theorem nonzero_of_eval_one {a : BinaryForm} (i : Fin 48) (h : a i = 1) : a ≠ 0 := by
  intro ha
  have hz : a i = 0 := congrFun ha i
  exact one_ne_zero (h.symm.trans hz)

/-- The nonzero common fixed forms that define index-two kernels in catalogue coordinates. -/
theorem nonzero_common_fixed_iff (a : BinaryForm) :
    ((modTwo tCatalogueMap *ᵥ a = a ∧ modTwo uCatalogueMap *ᵥ a = a) ∧ a ≠ 0) ↔
    a = formA ∨ a = formB ∨ a = formC := by
  rw [common_fixed_iff]
  constructor
  · rintro ⟨h, ha⟩
    exact h.resolve_left ha
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rcases h with rfl | rfl | rfl
    · exact nonzero_of_eval_one 44 (by decide +kernel)
    · exact nonzero_of_eval_one 0 (by decide +kernel)
    · exact nonzero_of_eval_one 0 (by decide +kernel)

/-- The stacked differences in the t and u blocks. -/
def stackedDifference : BinaryForm →ₗ[ZMod 2] BinaryForm × BinaryForm :=
  ((modTwo tCatalogueMap).toLin' - LinearMap.id).prod
    ((modTwo uCatalogueMap).toLin' - LinearMap.id)

theorem mem_commonFixedSpace (a : BinaryForm) :
    a ∈ LinearMap.ker stackedDifference ↔
    modTwo tCatalogueMap *ᵥ a = a ∧ modTwo uCatalogueMap *ᵥ a = a := by
  rw [LinearMap.mem_ker]
  change (modTwo tCatalogueMap *ᵥ a - a, modTwo uCatalogueMap *ᵥ a - a) = (0, 0) ↔ _
  simp only [Prod.mk.injEq, sub_eq_zero]

/-- Evaluation at coordinates 44 and 0 gives linear coordinates on the common kernel. -/
def commonFixedCoordinates : LinearMap.ker stackedDifference ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 where
  toFun a := (a.val 44, a.val 0)
  invFun p := ⟨p.1 • formA + p.2 • formB, (mem_commonFixedSpace _).2 (fixed_combination _ _)⟩
  left_inv a := by
    have h := (mem_commonFixedSpace _).1 a.property
    exact Subtype.ext (fixed_coordinates h.1 h.2).symm
  right_inv p := by
    have hA44 : formA 44 = 1 := by decide +kernel
    have hA0 : formA 0 = 0 := by decide +kernel
    have hB44 : formB 44 = 0 := by decide +kernel
    have hB0 : formB 0 = 1 := by decide +kernel
    apply Prod.ext
    · change (p.1 • formA + p.2 • formB) 44 = p.1
      simp only [Pi.add_apply, Pi.smul_apply, hA44, hB44, smul_eq_mul, mul_one, mul_zero, add_zero]
    · change (p.1 • formA + p.2 • formB) 0 = p.2
      simp only [Pi.add_apply, Pi.smul_apply, hA0, hB0, smul_eq_mul, mul_one, mul_zero, zero_add]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem commonFixedSpace_finrank : Module.finrank (ZMod 2) (LinearMap.ker stackedDifference) = 2 := by
  simpa only [Module.finrank_prod, Module.finrank_self] using commonFixedCoordinates.finrank_eq

theorem stackedDifference_rank : Module.finrank (ZMod 2) (LinearMap.range stackedDifference) = 46 := by
  have h := stackedDifference.finrank_range_add_finrank_ker
  rw [commonFixedSpace_finrank, Module.finrank_pi, Fintype.card_fin] at h
  omega

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pBinaryInvariantForms
