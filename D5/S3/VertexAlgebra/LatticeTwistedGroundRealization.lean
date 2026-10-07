/- GID: D5/S3/VertexAlgebra/LatticeTwistedGroundRealization
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeTwistedGroundRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual lattice reflection quotients have irreducible complex ground representations. -/

import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import D5.S3.QuadraticForms.SymplecticBasis
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Sum.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient

open LatticeGeneratingFieldLocality
open scoped BigOperators

abbrev F₂ := ZMod 2

/-- Sign coordinates are exponents: zero is the positive sign. -/
@[ext] structure SignExtension (A : Type*) [AddCommGroup A] (c : A →+ A →+ F₂) where
  sign : F₂
  charge : A

namespace SignExtension

variable {A : Type*} [AddCommGroup A] {c : A →+ A →+ F₂}

instance : One (SignExtension A c) := ⟨⟨0, 0⟩⟩
instance : Mul (SignExtension A c) :=
  ⟨fun x y => ⟨x.sign + y.sign + c x.charge y.charge, x.charge + y.charge⟩⟩
instance : Inv (SignExtension A c) :=
  ⟨fun x => ⟨-x.sign + c x.charge x.charge, -x.charge⟩⟩

instance : Group (SignExtension A c) where
  mul_assoc x y z := by
    ext
    · change (x.sign + y.sign + c x.charge y.charge) + z.sign +
        c (x.charge + y.charge) z.charge =
        x.sign + (y.sign + z.sign + c y.charge z.charge) +
          c x.charge (y.charge + z.charge)
      simp only [map_add, AddMonoidHom.add_apply]
      abel
    · exact add_assoc _ _ _
  one_mul x := by
    ext
    · change 0 + x.sign + c 0 x.charge = x.sign
      simp
    · exact zero_add _
  mul_one x := by
    ext
    · change x.sign + 0 + c x.charge 0 = x.sign
      simp
    · exact add_zero _
  inv_mul_cancel x := by
    ext
    · change (-x.sign + c x.charge x.charge) + x.sign + c (-x.charge) x.charge = 0
      simp only [map_neg, AddMonoidHom.neg_apply]
      abel
    · exact neg_add_cancel _

/-- The genuine lift of charge reflection. -/
def theta : SignExtension A c ≃* SignExtension A c where
  toFun x := ⟨x.sign, -x.charge⟩
  invFun x := ⟨x.sign, -x.charge⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    ext
    · change x.sign + y.sign + c x.charge y.charge =
        x.sign + y.sign + c (-x.charge) (-y.charge)
      simp
    · exact neg_add _ _

theorem reflection_difference (x : SignExtension A c) :
    x⁻¹ * theta x = ⟨0, -(x.charge + x.charge)⟩ := by
  ext
  · change (-x.sign + c x.charge x.charge) + x.sign +
      c (-x.charge) (-x.charge) = 0
    simp only [map_neg, AddMonoidHom.neg_apply, neg_neg]
    simp only [CharTwo.neg_eq]
    have h := CharTwo.add_self_eq_zero (c x.charge x.charge)
    have hs := CharTwo.add_self_eq_zero x.sign
    linear_combination h + hs
  · exact (neg_add _ _).symm

end SignExtension

/-- The same lower-triangular integer cocycle as the actual lattice fields. -/
def integralCocycle (D : LatticeData) : Charge D →+ Charge D →+ F₂ where
  toFun a := {
    toFun := fun b => (lowerCocycleExponent D a b : F₂)
    map_zero' := by simp [lowerCocycleExponent]
    map_add' := by
      intro b d
      simp only [lowerCocycleExponent, Pi.add_apply, mul_add, Finset.sum_add_distrib,
        Int.cast_add]
      ring }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    simp [lowerCocycleExponent]
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro d
    change (lowerCocycleExponent D (a + b) d : F₂) =
      (lowerCocycleExponent D a d : F₂) + (lowerCocycleExponent D b d : F₂)
    simp only [lowerCocycleExponent, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib, Int.cast_add]
    ring

abbrev Extension (D : LatticeData) := SignExtension (Charge D) (integralCocycle D)
abbrev ModTwoCharge (D : LatticeData) := Fin D.rank → F₂

def lowerMatrix (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℤ :=
  fun i j => (if j < i then D.G i j else 0) +
    (if j = i then halfDiagonal D i else 0)

theorem lower_matrix_formula (D : LatticeData) (a b : Charge D) :
    lowerCocycleExponent D a b = ∑ i, ∑ j, a i * lowerMatrix D i j * b j := by
  classical
  unfold lowerCocycleExponent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [lowerMatrix, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  · rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      ring
    · intro j hj hji
      simp [hji]
    · simp

def modTwoCocycle (D : LatticeData) : ModTwoCharge D →+ ModTwoCharge D →+ F₂ where
  toFun a := (Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂)) a).toAddMonoidHom
  map_zero' := by ext b; simp
  map_add' a b := by ext d; simp

abbrev ReducedExtension (D : LatticeData) :=
  SignExtension (ModTwoCharge D) (modTwoCocycle D)

def reduceCharge (D : LatticeData) : Charge D →+ ModTwoCharge D where
  toFun a := fun i => (a i : F₂)
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

theorem cocycle_reduction (D : LatticeData) (a b : Charge D) :
    modTwoCocycle D (reduceCharge D a) (reduceCharge D b) = integralCocycle D a b := by
  change Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂))
    (fun i => (a i : F₂)) (fun i => (b i : F₂)) = (lowerCocycleExponent D a b : F₂)
  rw [lower_matrix_formula, Matrix.toBilin'_apply]
  simp [Matrix.map_apply]

def reduction (D : LatticeData) : Extension D →* ReducedExtension D where
  toFun x := ⟨x.sign, reduceCharge D x.charge⟩
  map_one' := by
    apply SignExtension.ext
    · rfl
    · exact map_zero (reduceCharge D)
  map_mul' x y := by
    apply SignExtension.ext
    · change x.sign + y.sign + integralCocycle D x.charge y.charge =
        x.sign + y.sign + modTwoCocycle D (reduceCharge D x.charge) (reduceCharge D y.charge)
      rw [cocycle_reduction]
    · exact map_add (reduceCharge D) x.charge y.charge

theorem reduction_surjective (D : LatticeData) : Function.Surjective (reduction D) := by
  intro x
  refine ⟨⟨x.sign, fun i => (x.charge i).val⟩, ?_⟩
  ext
  · rfl
  · simp [reduction, reduceCharge]

/-- This definition uses reflection differences, rather than a prescribed kernel. -/
def K (D : LatticeData) : Subgroup (Extension D) :=
  Subgroup.closure (Set.range (fun x : Extension D => x⁻¹ * SignExtension.theta x))

theorem kernel_membership (D : LatticeData) (x : Extension D) :
    x ∈ (reduction D).ker ↔ x.sign = 0 ∧ ∃ a : Charge D, x.charge = a + a := by
  change (reduction D x = 1) ↔ _
  constructor
  · intro h
    have hs := congrArg SignExtension.sign h
    have hc := congrArg SignExtension.charge h
    refine ⟨hs, ?_⟩
    have hdiv : ∀ i, (2 : ℤ) ∣ x.charge i := by
      intro i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (congrFun hc i)
    choose a ha using hdiv
    refine ⟨a, ?_⟩
    ext i
    simpa [two_mul] using ha i
  · rintro ⟨hs, a, ha⟩
    apply SignExtension.ext
    · exact hs
    · change reduceCharge D x.charge = 0
      ext i
      simp [reduceCharge, ha, CharTwo.add_self_eq_zero]

theorem K_eq_kernel (D : LatticeData) : K D = (reduction D).ker := by
  apply le_antisymm
  · apply (Subgroup.closure_le (reduction D).ker).mpr
    rintro _ ⟨x, rfl⟩
    dsimp only
    rw [SignExtension.reflection_difference]
    exact (kernel_membership D _).mpr ⟨rfl, -x.charge, by simp⟩
  · intro x hx
    obtain ⟨hs, a, ha⟩ := (kernel_membership D x).mp hx
    apply Subgroup.subset_closure
    refine ⟨(⟨0, -a⟩ : Extension D), ?_⟩
    dsimp only
    rw [SignExtension.reflection_difference]
    apply SignExtension.ext
    · exact hs.symm
    · simpa using ha.symm

theorem doubled_central (D : LatticeData) (a : Charge D) (x : Extension D) :
    (⟨0, a + a⟩ : Extension D) * x = x * ⟨0, a + a⟩ := by
  apply SignExtension.ext
  · change 0 + x.sign + integralCocycle D (a + a) x.charge =
      x.sign + 0 + integralCocycle D x.charge (a + a)
    simp [CharTwo.add_self_eq_zero]
  · exact add_comm _ _

instance K_normal (D : LatticeData) : (K D).Normal where
  conj_mem x hx g := by
    rw [K_eq_kernel] at hx
    obtain ⟨hs, a, ha⟩ := (kernel_membership D x).mp hx
    have heq : x = (⟨0, a + a⟩ : Extension D) := SignExtension.ext hs ha
    have hcomm := doubled_central D a g
    rw [← heq] at hcomm
    rw [← hcomm, mul_inv_cancel_right]
    rw [K_eq_kernel]
    exact hx

/-- The actual quotient is identified by its surjective cocycle reduction. -/
noncomputable def quotientEquiv (D : LatticeData) :
    Extension D ⧸ K D ≃* ReducedExtension D :=
  (QuotientGroup.quotientMulEquivOfEq (K_eq_kernel D)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (reduction D) (reduction_surjective D))

def complexSign (s : F₂) : ℂ := if s = 0 then 1 else -1

theorem complexSign_add (s t : F₂) : complexSign (s + t) = complexSign s * complexSign t := by
  fin_cases s <;> fin_cases t <;> norm_num [complexSign, F₂, CharTwo.add_self_eq_zero]

theorem complexSign_integral (a : ℤ) : complexSign (a : F₂) = paritySign a := by
  simp only [complexSign, paritySign, ZMod.intCast_eq_zero_iff_even]

/-- An injective complex unit character of the actual two-element sign group. -/
def complexSignEmbedding :
    {f : Multiplicative F₂ →* ℂˣ // Function.Injective f} := by
  let f : Multiplicative F₂ →* ℂˣ := {
    toFun := fun s => {
      val := complexSign s.toAdd
      inv := complexSign s.toAdd
      val_inv := by rw [← complexSign_add, CharTwo.add_self_eq_zero]; simp [complexSign]
      inv_val := by rw [← complexSign_add, CharTwo.add_self_eq_zero]; simp [complexSign] }
    map_one' := by apply Units.ext; simp [complexSign]
    map_mul' s t := by apply Units.ext; exact complexSign_add s.toAdd t.toAdd }
  refine ⟨f, ?_⟩
  intro s t h
  have hh := congrArg (fun u : ℂˣ => (u : ℂ)) h
  change complexSign s.toAdd = complexSign t.toAdd at hh
  change s.toAdd = t.toAdd
  generalize hs : s.toAdd = a at hh ⊢
  generalize ht : t.toAdd = b at hh ⊢
  fin_cases a <;> fin_cases b <;> norm_num [complexSign, F₂] at hh
  all_goals rfl

theorem lower_matrix_symmetrization (D : LatticeData) :
    lowerMatrix D + (lowerMatrix D).transpose = D.G := by
  ext i j
  change lowerMatrix D i j + lowerMatrix D j i = D.G i j
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hk⟩ := D.even_diagonal i
    simp only [lowerMatrix, lt_self_iff_false, if_false, if_true, zero_add, halfDiagonal]
    omega
  · rcases lt_or_gt_of_ne hij with hij | hji
    · simp [lowerMatrix, hij, ne_of_lt hij, (ne_of_lt hij).symm,
        not_lt_of_gt hij, D.symmetric i j]
    · simp [lowerMatrix, hji, ne_of_gt hji, (ne_of_gt hji).symm,
        not_lt_of_gt hji]

theorem integral_cocycle_symmetrization (D : LatticeData) (a b : Charge D) :
    lowerCocycleExponent D a b + lowerCocycleExponent D b a = bilinear D a b := by
  rw [lower_matrix_formula, lower_matrix_formula]
  unfold bilinear
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun (congrFun (lower_matrix_symmetrization D) i) j
  change lowerMatrix D i j + lowerMatrix D j i = D.G i j at h
  rw [← h]
  ring

theorem integral_cocycle_square (D : LatticeData) (a : Charge D) :
    lowerCocycleExponent D a a = bilinear D a a / 2 := by
  have h := integral_cocycle_symmetrization D a a
  omega

def modTwoPairing (D : LatticeData) : LinearMap.BilinForm F₂ (ModTwoCharge D) :=
  Matrix.toBilin' (D.G.map (Int.castRingHom F₂))

theorem mod_two_cocycle_symmetrization (D : LatticeData) (a b : ModTwoCharge D) :
    modTwoCocycle D a b + modTwoCocycle D b a = modTwoPairing D a b := by
  let aa : Charge D := fun i => (a i).val
  let bb : Charge D := fun i => (b i).val
  have ha : reduceCharge D aa = a := by ext i; simp [reduceCharge, aa]
  have hb : reduceCharge D bb = b := by ext i; simp [reduceCharge, bb]
  rw [← ha, ← hb, cocycle_reduction, cocycle_reduction]
  change (lowerCocycleExponent D aa bb : F₂) + (lowerCocycleExponent D bb aa : F₂) = _
  rw [← Int.cast_add, integral_cocycle_symmetrization]
  simp [modTwoPairing, Matrix.toBilin'_apply, bilinear, reduceCharge, Matrix.map_apply]

theorem mod_two_pairing_alternating (D : LatticeData) : (modTwoPairing D).IsAlt := by
  intro a
  rw [← mod_two_cocycle_symmetrization, CharTwo.add_self_eq_zero]

theorem mod_two_pairing_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det) :
    (modTwoPairing D).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  change ((Int.castRingHom F₂).mapMatrix D.G).det ≠ 0
  rw [← (Int.castRingHom F₂).map_det]
  exact (hu.map (Int.castRingHom F₂)).ne_zero

theorem symplectic_coordinates (D : LatticeData) (hu : IsUnit D.G.det) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n ⊕ Fin n) F₂ (ModTwoCharge D)),
      D.rank = n + n ∧
      D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing D) e := by
  obtain ⟨n, e, he⟩ := D5.S3.QuadraticForms.SymplecticBasis.exists_isSymplecticBasis
    (mod_two_pairing_alternating D) (mod_two_pairing_nondegenerate D hu)
  refine ⟨n, e, ?_, he⟩
  have h := Module.finrank_eq_card_basis e
  simpa using h

theorem reduced_square (D : LatticeData) (x : ReducedExtension D) :
    x * x = ⟨modTwoCocycle D x.charge x.charge, 0⟩ := by
  apply SignExtension.ext
  · change x.sign + x.sign + modTwoCocycle D x.charge x.charge = _
    rw [CharTwo.add_self_eq_zero, zero_add]
  · ext i
    exact CharTwo.add_self_eq_zero _

theorem reduced_commutation (D : LatticeData) (x y : ReducedExtension D) :
    x * y = (⟨modTwoPairing D x.charge y.charge, 0⟩ : ReducedExtension D) * (y * x) := by
  apply SignExtension.ext
  · change x.sign + y.sign + modTwoCocycle D x.charge y.charge =
      modTwoPairing D x.charge y.charge +
        (y.sign + x.sign + modTwoCocycle D y.charge x.charge) +
          modTwoCocycle D 0 (y.charge + x.charge)
    simp only [map_zero,
      AddMonoidHom.zero_apply, add_zero, ← mod_two_cocycle_symmetrization]
    abel_nf
    simp [show (2 : F₂) = 0 by decide]
  · change x.charge + y.charge = 0 + (y.charge + x.charge)
    simp [add_comm]

end D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient


namespace D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

open SignQuotient
open LatticeGeneratingFieldLocality
open scoped BigOperators

noncomputable section

theorem sign_zero : complexSign 0 = 1 := by simp [complexSign]
theorem sign_one : complexSign 1 = -1 := by norm_num [complexSign, F₂]

theorem sign_square (s : F₂) : complexSign s * complexSign s = 1 := by
  rw [← complexSign_add, CharTwo.add_self_eq_zero, sign_zero]

theorem sign_nonzero (s : F₂) : complexSign s ≠ 0 := by
  change ((complexSignEmbedding.val (Multiplicative.ofAdd s) : ℂˣ) : ℂ) ≠ 0
  exact Units.ne_zero _

theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → F₂) :
    complexSign (∑ i ∈ s, f i) = ∏ i ∈ s, complexSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      complexSign_add, ih]

def fourthRoot (q : F₂) : ℂ := if q = 0 then 1 else Complex.I

private theorem fourth_root_nonzero (q : F₂) : fourthRoot q ≠ 0 := by
  unfold fourthRoot
  split_ifs <;> simp

private theorem fourth_root_carry (q a b : F₂) :
    fourthRoot q ^ a.val * fourthRoot q ^ b.val =
      complexSign (q * a * b) * fourthRoot q ^ (a + b).val := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;>
    norm_num [fourthRoot, complexSign, F₂, CharTwo.add_self_eq_zero, Complex.I_sq,
      show (1 : F₂).val = 1 by rfl, pow_two]

section SymmetricPhase

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def normalExponent (S : Matrix ι ι F₂) (v : ι → F₂) : F₂ :=
  ∑ i, ∑ j with i < j, S i j * v i * v j

def diagonalPhase (S : Matrix ι ι F₂) (v : ι → F₂) : ℂ :=
  ∏ i, fourthRoot (S i i) ^ (v i).val

/-- The phase of an ordered product of lifts includes their individual squares. -/
def liftPhase (S : Matrix ι ι F₂) (v : ι → F₂) : ℂ :=
  diagonalPhase S v * complexSign (normalExponent S v)

omit [LinearOrder ι] in
private theorem diagonal_phase_nonzero (S : Matrix ι ι F₂) (v : ι → F₂) :
    diagonalPhase S v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (fourth_root_nonzero _)

private theorem lift_phase_nonzero (S : Matrix ι ι F₂) (v : ι → F₂) :
    liftPhase S v ≠ 0 :=
  mul_ne_zero (diagonal_phase_nonzero S v) (sign_nonzero _)

omit [LinearOrder ι] in
private theorem diagonal_phase_carry (S : Matrix ι ι F₂) (v w : ι → F₂) :
    diagonalPhase S v * diagonalPhase S w =
      complexSign (∑ i, S i i * v i * w i) * diagonalPhase S (v + w) := by
  unfold diagonalPhase
  rw [← Finset.prod_mul_distrib]
  simp_rw [fourth_root_carry]
  rw [Finset.prod_mul_distrib, sign_sum]
  rfl

theorem normal_exponent_add (S : Matrix ι ι F₂) (v w : ι → F₂) :
    normalExponent S v + normalExponent S w =
      (∑ i, ∑ j with i < j, S i j * (v i * w j + w i * v j)) +
        normalExponent S (v + w) := by
  unfold normalExponent
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply]
  ring_nf
  simp [show (2 : F₂) = 0 by decide]

theorem symmetric_pairing_split (S : Matrix ι ι F₂) (hS : S.IsSymm)
    (v w : ι → F₂) :
    Matrix.toBilin' S v w = (∑ i, S i i * v i * w i) +
      (∑ i, ∑ j with i < j, S i j * (v i * w j + w i * v j)) := by
  classical
  rw [Matrix.toBilin'_apply]
  have split (i j : ι) : v i * S i j * w j =
      (if i = j then S i i * v i * w i else 0) +
      (if i < j then S i j * v i * w j else 0) +
      (if j < i then S i j * v i * w j else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [if_pos hij, if_neg (ne_of_lt hij), if_neg (not_lt_of_gt hij),
        zero_add, add_zero]
      ring
    · simp only [ite_true, lt_self_iff_false, if_false, add_zero]
      ring
    · simp only [if_pos hji, if_neg (ne_of_gt hji), if_neg (not_lt_of_gt hji),
        zero_add, add_zero]
      ring
  simp_rw [split]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i, ∑ j, if i = j then S i i * v i * w i else 0) =
      ∑ i, S i i * v i * w i := by simp
  rw [hd]
  have hl : (∑ i, ∑ j, if j < i then S i j * v i * w j else 0) =
      ∑ i, ∑ j, if i < j then S i j * w i * v j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hS.apply j i]
    split_ifs <;> ring
  rw [hl, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem lift_phase_cocycle (S : Matrix ι ι F₂) (hS : S.IsSymm)
    (v w : ι → F₂) :
    liftPhase S v * liftPhase S w =
      complexSign (Matrix.toBilin' S v w) * liftPhase S (v + w) := by
  unfold liftPhase
  calc
    diagonalPhase S v * complexSign (normalExponent S v) *
        (diagonalPhase S w * complexSign (normalExponent S w)) =
      (diagonalPhase S v * diagonalPhase S w) *
        complexSign (normalExponent S v + normalExponent S w) := by
          rw [complexSign_add]
          ring
    _ = _ := by
      rw [diagonal_phase_carry, normal_exponent_add, symmetric_pairing_split S hS,
        complexSign_add, complexSign_add]
      ring

end SymmetricPhase

abbrev Half (n : ℕ) := Fin n → F₂
abbrev Coordinates (n : ℕ) := (Fin n ⊕ Fin n) → F₂
abbrev Ground (n : ℕ) := Half n → ℂ

def leftHalf {n : ℕ} (v : Coordinates n) : Half n := fun i => v (Sum.inl i)
def rightHalf {n : ℕ} (v : Coordinates n) : Half n := fun i => v (Sum.inr i)

def dot {n : ℕ} (x y : Half n) : F₂ := ∑ i, x i * y i

def standardCocycle {n : ℕ} (v w : Coordinates n) : F₂ := dot (rightHalf w) (leftHalf v)

def weylOperator {n : ℕ} (v : Coordinates n) : Module.End ℂ (Ground n) where
  toFun f := fun t => complexSign (dot (rightHalf v) t) * f (t + leftHalf v)
  map_add' f g := by ext t; simp [mul_add]
  map_smul' a f := by ext t; simp [mul_left_comm]

private theorem weyl_zero (n : ℕ) : weylOperator (0 : Coordinates n) = 1 := by
  apply LinearMap.ext
  intro f
  funext t
  have hl : leftHalf (0 : Coordinates n) = 0 := rfl
  simp [weylOperator, dot, hl, rightHalf, sign_zero]

private theorem weyl_mul {n : ℕ} (v w : Coordinates n) :
    weylOperator v * weylOperator w = complexSign (standardCocycle v w) •
      weylOperator (v + w) := by
  have h (t : Half n) : dot (rightHalf v) t + dot (rightHalf w) (t + leftHalf v) =
      standardCocycle v w + dot (rightHalf (v + w)) t := by
    simp only [dot, standardCocycle, leftHalf, rightHalf, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
    ring
  apply LinearMap.ext
  intro f
  funext t
  change complexSign (dot (rightHalf v) t) *
      (complexSign (dot (rightHalf w) (t + leftHalf v)) *
        f ((t + leftHalf v) + leftHalf w)) =
    complexSign (standardCocycle v w) *
      (complexSign (dot (rightHalf (v + w)) t) * f (t + leftHalf (v + w)))
  rw [← mul_assoc, ← complexSign_add, h, complexSign_add]
  have ht : (t + leftHalf v) + leftHalf w = t + leftHalf (v + w) := by
    ext i
    exact add_assoc _ _ _
  rw [ht, mul_assoc]

def standardMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₂
  | Sum.inl i, Sum.inr j => if i = j then 1 else 0
  | _, _ => 0

private theorem standard_matrix_formula {n : ℕ} (v w : Coordinates n) :
    Matrix.toBilin' (standardMatrix n) v w = standardCocycle v w := by
  classical
  simp [Matrix.toBilin'_apply, Fintype.sum_sum_type, standardMatrix,
    standardCocycle, dot, rightHalf, leftHalf, mul_comm]

section Coordinates

local instance coordinateOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv.injective

variable (D : LatticeData) {n : ℕ}
variable (e : Module.Basis (Fin n ⊕ Fin n) F₂ (ModTwoCharge D))

def coordinateCocycle : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₂ :=
  LinearMap.BilinForm.toMatrix e
    (Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂)))

def squareCorrection : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₂ :=
  coordinateCocycle D e + standardMatrix n

private theorem coordinate_cocycle_formula (a b : ModTwoCharge D) :
    Matrix.toBilin' (coordinateCocycle D e) (fun i => e.repr a i) (fun i => e.repr b i) =
      modTwoCocycle D a b := by
  change Matrix.toBilin' (coordinateCocycle D e) (fun i => e.repr a i)
    (fun i => e.repr b i) = Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂)) a b
  have h := congrArg (fun B : LinearMap.BilinForm F₂ (ModTwoCharge D) => B a b)
    (Matrix.toBilin_toMatrix e
      (Matrix.toBilin' ((lowerMatrix D).map (Int.castRingHom F₂))))
  rw [Matrix.toBilin_apply] at h
  simpa only [coordinateCocycle, Matrix.toBilin'_apply] using h

private theorem square_correction_symmetric
    (he : D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing D) e) :
    (squareCorrection D e).IsSymm := by
  ext i j
  have hc : coordinateCocycle D e i j + coordinateCocycle D e j i =
      modTwoPairing D (e i) (e j) := by
    simp only [coordinateCocycle, LinearMap.BilinForm.toMatrix_apply]
    change modTwoCocycle D (e i) (e j) + modTwoCocycle D (e j) (e i) = _
    exact mod_two_cocycle_symmetrization D (e i) (e j)
  have hb : modTwoPairing D (e i) (e j) = standardMatrix n i j + standardMatrix n j i := by
    rcases i with i | i <;> rcases j with j | j
    · simpa [standardMatrix] using he.inl_inl i j
    · by_cases hij : i = j
      · subst j
        simpa [standardMatrix] using he.inl_inr_self i
      · simpa [standardMatrix, hij] using he.inl_inr_of_ne i j hij
    · have hsym : modTwoPairing D (e (Sum.inr i)) (e (Sum.inl j)) =
          modTwoPairing D (e (Sum.inl j)) (e (Sum.inr i)) := by
        rw [← (mod_two_pairing_alternating D).neg_eq, CharTwo.neg_eq]
      rw [hsym]
      by_cases hij : j = i
      · subst i
        simpa [standardMatrix] using he.inl_inr_self j
      · simpa [standardMatrix, hij] using he.inl_inr_of_ne j i hij
    · simpa [standardMatrix] using he.inr_inr i j
  change coordinateCocycle D e j i + standardMatrix n j i =
    coordinateCocycle D e i j + standardMatrix n i j
  rw [hb] at hc
  have hneg := CharTwo.neg_eq (coordinateCocycle D e i j)
  have hneg' := CharTwo.neg_eq (standardMatrix n j i)
  linear_combination hc + hneg - hneg'

private theorem lift_phase_zero : liftPhase (squareCorrection D e) 0 = 1 := by
  simp [liftPhase, diagonalPhase, normalExponent, sign_zero]

def actionScalar (x : ReducedExtension D) : ℂ :=
  complexSign x.sign * liftPhase (squareCorrection D e) (e.equivFun x.charge)

private theorem action_scalar_nonzero (x : ReducedExtension D) : actionScalar D e x ≠ 0 :=
  mul_ne_zero (sign_nonzero _) (lift_phase_nonzero _ _)

private theorem action_scalar_mul
    (he : D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing D) e)
    (x y : ReducedExtension D) :
    actionScalar D e (x * y) = actionScalar D e x * actionScalar D e y *
      complexSign (standardCocycle (e.equivFun x.charge) (e.equivFun y.charge)) := by
  let v := e.equivFun x.charge
  let w := e.equivFun y.charge
  let c := modTwoCocycle D x.charge y.charge
  let p := standardCocycle v w
  have hC : Matrix.toBilin' (squareCorrection D e) v w = c + p := by
    simp only [squareCorrection, map_add, LinearMap.add_apply]
    rw [standard_matrix_formula]
    exact congrArg (fun z => z + p) (coordinate_cocycle_formula D e x.charge y.charge)
  have hP := lift_phase_cocycle (squareCorrection D e) (square_correction_symmetric D e he) v w
  simp only [Matrix.toBilin'_apply] at hC hP
  rw [hC, complexSign_add] at hP
  symm
  calc
    actionScalar D e x * actionScalar D e y * complexSign p =
        complexSign x.sign * complexSign y.sign *
          (liftPhase (squareCorrection D e) v * liftPhase (squareCorrection D e) w) *
          complexSign p := by unfold actionScalar; dsimp [v, w]; ring
    _ = complexSign x.sign * complexSign y.sign * complexSign c *
        liftPhase (squareCorrection D e) (v + w) := by
      rw [hP]
      calc
        _ = complexSign x.sign * complexSign y.sign * complexSign c *
          liftPhase (squareCorrection D e) (v + w) * (complexSign p * complexSign p) := by ring
        _ = _ := by rw [sign_square, mul_one]
    _ = actionScalar D e (x * y) := by
      change complexSign x.sign * complexSign y.sign * complexSign c *
        liftPhase (squareCorrection D e) (v + w) =
        complexSign (x.sign + y.sign + c) *
          liftPhase (squareCorrection D e) (e.equivFun (x.charge + y.charge))
      simp only [map_add, complexSign_add]
      dsimp [v, w, c]

/-- The operators represent the original reduced cocycle, including its lift squares. -/
def reducedRepresentation
    (he : D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing D) e) :
    Representation ℂ (ReducedExtension D) (Ground n) where
  toFun x := actionScalar D e x • weylOperator (e.equivFun x.charge)
  map_one' := by
    change actionScalar D e ⟨0, 0⟩ • weylOperator (e.equivFun 0) = 1
    simp only [actionScalar,
      map_zero, sign_zero, lift_phase_zero, one_mul, one_smul, weyl_zero]
  map_mul' x y := by
    change actionScalar D e (x * y) • weylOperator (e.equivFun (x.charge + y.charge)) =
      (actionScalar D e x • weylOperator (e.equivFun x.charge)) *
        (actionScalar D e y • weylOperator (e.equivFun y.charge))
    simp only [map_add, smul_mul_assoc, mul_smul_comm,
      weyl_mul, smul_smul, action_scalar_mul D e he]
    congr 1
    ring

end Coordinates

def shift {n : ℕ} (x : Half n) (f : Ground n) : Ground n := fun t => f (t + x)
def diagonal {n : ℕ} (y : Half n) (f : Ground n) : Ground n :=
  fun t => complexSign (dot y t) * f t

private theorem projector_bit (a b : F₂) :
    (1 + complexSign a * complexSign b) / 2 = if a = b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [complexSign, F₂, CharTwo.add_self_eq_zero]

/-- Coordinate projectors isolate a single matrix coefficient. -/
private theorem coordinate_projector_mem {n : ℕ} (W : Submodule ℂ (Ground n))
    (hdiag : ∀ y f, f ∈ W → diagonal y f ∈ W) (f : Ground n) (hf : f ∈ W)
    (t : Half n) : (fun u => if u = t then f u else 0) ∈ W := by
  classical
  have masks : ∀ s : Finset (Fin n),
      (fun u => if ∀ i ∈ s, u i = t i then f u else 0) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | @insert i s hi ih =>
      let g : Ground n := fun u => if ∀ j ∈ s, u j = t j then f u else 0
      have hg : g ∈ W := ih
      have hd := hdiag (Pi.single i 1) g hg
      have hh := W.smul_mem (1 / 2 : ℂ) (W.add_mem hg (W.smul_mem (complexSign (t i)) hd))
      convert hh using 1
      funext u
      change (if ∀ j ∈ insert i s, u j = t j then f u else 0) =
        (1 / 2 : ℂ) * (g u + complexSign (t i) * diagonal (Pi.single i 1) g u)
      have hdot : dot (Pi.single i (1 : F₂)) u = u i := by simp [dot, Pi.single_apply]
      simp only [diagonal, hdot]
      by_cases hu : ∀ j ∈ s, u j = t j
      · have hp := projector_bit (t i) (u i)
        dsimp [g]
        simp only [if_pos hu]
        by_cases hui : u i = t i
        · have hui' : ∀ j ∈ insert i s, u j = t j := by
            simpa only [Finset.forall_mem_insert] using And.intro hui hu
          rw [if_pos hui']
          rw [if_pos hui.symm] at hp
          linear_combination -f u * hp
        · have hui' : ¬∀ j ∈ insert i s, u j = t j := by
            intro h
            exact hui (h i (Finset.mem_insert_self i s))
          rw [if_neg hui']
          rw [if_neg (Ne.symm hui)] at hp
          linear_combination -f u * hp
      · dsimp [g]
        simp [hu]
  have h := masks Finset.univ
  have heq : ∀ u : Half n, (∀ i ∈ Finset.univ, u i = t i) ↔ u = t := by
    intro u
    simp only [Finset.mem_univ, forall_const]
    exact funext_iff.symm
  simpa only [heq] using h

private theorem shift_diagonal_irreducibility {n : ℕ} (W : Submodule ℂ (Ground n))
    (hshift : ∀ x f, f ∈ W → shift x f ∈ W)
    (hdiag : ∀ y f, f ∈ W → diagonal y f ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨f, hf, hfn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨t, ht⟩ : ∃ t, f t ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hfn (funext hn)
  have hd := coordinate_projector_mem W hdiag f hf t
  have hsingle : Pi.single t (1 : ℂ) ∈ W := by
    convert W.smul_mem (f t)⁻¹ hd using 1
    funext u
    by_cases hut : u = t
    · subst u
      simp [ht]
    · simp [hut]
  have hall (u : Half n) : Pi.single u (1 : ℂ) ∈ W := by
    have h := hshift (t + u) (Pi.single t 1) hsingle
    convert h using 1
    funext v
    have heq : v + (t + u) = t ↔ v = u := by
      have hc : (u : Half n) + (t + u) = t := by
        funext i
        change u i + (t i + u i) = t i
        rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
      constructor
      · intro h
        apply add_right_cancel (b := t + u)
        exact h.trans hc.symm
      · rintro rfl
        exact hc
    simp [shift, Pi.single_apply, heq, eq_comm]
  apply top_unique
  rw [← (Pi.basisFun ℂ (Half n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  have heq : (Pi.basisFun ℂ (Half n)) u = Pi.single u (1 : ℂ) := by
    funext v
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [heq]
  exact hall u

section ActualQuotient

attribute [local instance] coordinateOrder

variable (D : LatticeData) {n : ℕ}
variable (e : Module.Basis (Fin n ⊕ Fin n) F₂ (ModTwoCharge D))
variable (he : D5.S3.QuadraticForms.SymplecticBasis.IsSymplecticBasis (modTwoPairing D) e)

def quotientRepresentation : Representation ℂ (Extension D ⧸ K D) (Ground n) :=
  (reducedRepresentation D e he).comp (quotientEquiv D).toMonoidHom

private theorem quotient_weyl_stability (W : Subrepresentation (quotientRepresentation D e he))
    (v : Coordinates n) (f : Ground n) (hf : f ∈ W) : weylOperator v f ∈ W := by
  let x : ReducedExtension D := ⟨0, e.equivFun.symm v⟩
  let g := (quotientEquiv D).symm x
  have hg := W.apply_mem_toSubmodule g hf
  have hx : actionScalar D e x ≠ 0 := action_scalar_nonzero D e x
  have hmap : quotientRepresentation D e he g = actionScalar D e x • weylOperator v := by
    simp only [quotientRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      g, MulEquiv.apply_symm_apply]
    change actionScalar D e x • weylOperator (e.equivFun (e.equivFun.symm v)) = _
    rw [LinearEquiv.apply_symm_apply]
  have h := W.toSubmodule.smul_mem (actionScalar D e x)⁻¹ hg
  rw [hmap, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hx, one_smul] at h
  exact h

/-
The invariant-subspace argument isolates coefficients by the commuting sign
diagonals, then transports them by shifts. The lattice cocycle enters the
operators through the symmetric correction and its fourth-root carry law.
-/
private theorem quotient_representation_irreducible :
    Representation.IsIrreducible (quotientRepresentation D e he) := by
  classical
  have hbot : (⊥ : Subrepresentation (quotientRepresentation D e he)) ≠ ⊤ := by
    intro h
    have hz : (fun _ : Half n => (1 : ℂ)) ∈
        (⊥ : Subrepresentation (quotientRepresentation D e he)) := by
      rw [h]
      trivial
    change (fun _ : Half n => (1 : ℂ)) ∈ (⊥ : Submodule ℂ (Ground n)) at hz
    have hzero : (fun _ : Half n => (1 : ℂ)) = 0 := by simpa using hz
    exact one_ne_zero (congrFun hzero 0)
  let : Nontrivial (Subrepresentation (quotientRepresentation D e he)) :=
    ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hd : ∀ y f, f ∈ W.toSubmodule → diagonal y f ∈ W.toSubmodule := by
    intro y f hf
    let v : Coordinates n := Sum.elim 0 y
    have h := quotient_weyl_stability D e he W v f hf
    have hv : leftHalf v = 0 := rfl
    have hr : rightHalf v = y := rfl
    change weylOperator v f ∈ W.toSubmodule at h
    convert h using 1
    funext t
    simp [diagonal, weylOperator, hv, hr]
  have hs : ∀ x f, f ∈ W.toSubmodule → shift x f ∈ W.toSubmodule := by
    intro x f hf
    let v : Coordinates n := Sum.elim x 0
    have h := quotient_weyl_stability D e he W v f hf
    have hv : leftHalf v = x := rfl
    have hr : rightHalf v = 0 := rfl
    change weylOperator v f ∈ W.toSubmodule at h
    convert h using 1
    funext t
    simp [weylOperator, shift, hr, dot, sign_zero, hv]
  rcases shift_diagonal_irreducibility W.toSubmodule hs hd with h | h
  · exact False.elim (hW (Subrepresentation.toSubmodule_injective h))
  · exact Subrepresentation.toSubmodule_injective h

private theorem quotient_sign_action (s : F₂) :
    quotientRepresentation D e he (QuotientGroup.mk (⟨s, 0⟩ : Extension D)) =
      complexSign s • (1 : Module.End ℂ (Ground n)) := by
  simp only [quotientRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (show ∀ x : Extension D, quotientEquiv D (QuotientGroup.mk x) = reduction D x
      from fun _ => rfl)]
  change actionScalar D e ⟨s, 0⟩ • weylOperator (e.equivFun 0) = _
  simp only [actionScalar, map_zero, lift_phase_zero, mul_one, weyl_zero]

private theorem quotient_charge_square (a : Charge D) :
    quotientRepresentation D e he (QuotientGroup.mk (⟨0, a⟩ : Extension D)) ^ 2 =
      paritySign (bilinear D a a / 2) • (1 : Module.End ℂ (Ground n)) := by
  rw [← map_pow, ← QuotientGroup.mk_pow]
  simp only [quotientRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (show ∀ x : Extension D, quotientEquiv D (QuotientGroup.mk x) = reduction D x
      from fun _ => rfl), pow_two, map_mul, reduced_square]
  change actionScalar D e ⟨modTwoCocycle D (reduceCharge D a) (reduceCharge D a), 0⟩ •
    weylOperator (e.equivFun 0) = _
  rw [cocycle_reduction]
  simp only [actionScalar, map_zero, lift_phase_zero, mul_one, weyl_zero]
  change complexSign (lowerCocycleExponent D a a : F₂) • _ = _
  rw [complexSign_integral, integral_cocycle_square]

private theorem quotient_charge_commutation (a b : Charge D) :
    quotientRepresentation D e he (QuotientGroup.mk (⟨0, a⟩ : Extension D)) *
      quotientRepresentation D e he (QuotientGroup.mk (⟨0, b⟩ : Extension D)) =
    paritySign (bilinear D a b) •
      (quotientRepresentation D e he (QuotientGroup.mk (⟨0, b⟩ : Extension D)) *
        quotientRepresentation D e he (QuotientGroup.mk (⟨0, a⟩ : Extension D))) := by
  let x := reduction D (⟨0, a⟩ : Extension D)
  let y := reduction D (⟨0, b⟩ : Extension D)
  have hc := congrArg (reducedRepresentation D e he) (reduced_commutation D x y)
  have hsign : reducedRepresentation D e he
      (⟨modTwoPairing D x.charge y.charge, 0⟩ : ReducedExtension D) =
      complexSign (bilinear D a b : F₂) • (1 : Module.End ℂ (Ground n)) := by
    have hb : modTwoPairing D x.charge y.charge = (bilinear D a b : F₂) := by
      simp [x, y, reduction, reduceCharge, modTwoPairing, Matrix.toBilin'_apply,
        Matrix.map_apply, bilinear]
    change actionScalar D e ⟨modTwoPairing D x.charge y.charge, 0⟩ •
      weylOperator (e.equivFun 0) = _
    simp only [actionScalar, map_zero, lift_phase_zero, mul_one, weyl_zero, hb]
  simp only [map_mul, hsign, smul_mul_assoc, one_mul, complexSign_integral] at hc
  simpa only [quotientRepresentation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    (show ∀ x : Extension D, quotientEquiv D (QuotientGroup.mk x) = reduction D x
      from fun _ => rfl)] using hc

end ActualQuotient

/-
The dimension follows from functions on one half of the symplectic coordinates.
No positivity, root condition, lattice classification or VOA extension is used.
-/
theorem actual_twisted_ground_representation (D : LatticeData) (hu : IsUnit D.G.det) :
    ∃ (n : ℕ) (ρ : Representation ℂ (Extension D ⧸ K D) (Ground n)),
      D.rank = n + n ∧ Representation.IsIrreducible ρ ∧
      ρ (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
        -(1 : Module.End ℂ (Ground n)) ∧
      Module.finrank ℂ (Ground n) = 2 ^ (D.rank / 2) ∧
      (D.rank = 24 → Module.finrank ℂ (Ground n) = 2 ^ 12) ∧
      (∀ a : Charge D, ρ (QuotientGroup.mk (⟨0, a⟩ : Extension D)) ^ 2 =
        paritySign (bilinear D a a / 2) • (1 : Module.End ℂ (Ground n))) ∧
      (∀ a b : Charge D, ρ (QuotientGroup.mk (⟨0, a⟩ : Extension D)) *
          ρ (QuotientGroup.mk (⟨0, b⟩ : Extension D)) =
        paritySign (bilinear D a b) • (ρ (QuotientGroup.mk (⟨0, b⟩ : Extension D)) *
          ρ (QuotientGroup.mk (⟨0, a⟩ : Extension D)))) := by
  obtain ⟨n, e, hr, he⟩ := symplectic_coordinates D hu
  refine ⟨n, quotientRepresentation D e he, hr,
    quotient_representation_irreducible D e he, ?_, ?_, ?_, quotient_charge_square D e he,
    quotient_charge_commutation D e he⟩
  · rw [quotient_sign_action, sign_one, neg_one_smul]
  · have hd : Module.finrank ℂ (Ground n) = 2 ^ n := by
      simp [Ground, Half, Module.finrank_fintype_fun_eq_card, F₂]
    rw [hd, hr]
    congr 1
    omega
  · intro h24
    have hn : n = 12 := by omega
    subst n
    simp [Ground, Half, Module.finrank_fintype_fun_eq_card, F₂]

end

end D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
