/- GID: D5/S3/QuadraticForms/OrthogonalLieStructure
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OrthogonalLieStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual standard orthogonal Lie algebras and their classical structure. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: actual classical Lie structure, not a finite certificate or algorithm.
escape_witness: contracted_double_rotation, ad_square_zero_eq_zero
The proof-shape assessment is the author's and awaits independent whole review.
  hasTrivialRadical_of_card_ne_four: proof_shape: content;
    escape_witness: contracted_double_rotation, ad_square_zero_eq_zero;
    consumers: so_four_hasTrivialRadical, hasTrivialRadical
  so_four_hasTrivialRadical: proof_shape: bind-only; escape_witness: none;
    consumers: hasTrivialRadical
  hasTrivialRadical: proof_shape: bind-only; escape_witness: none;
    consumers: KMV full radical-quotient construction (in progress)
Classical orthogonal structure is credited as classical. The evolution-algebra
application retains the supplied Ma-then-Zhang credit and makes no priority claim.
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Lie.Prod
import D5.S3.QuadraticForms.LieRadicalTransfer

/-!
Classical orthogonal Lie-algebra structure used by the KMV radical-quotient
argument. All carriers below are mathlib's actual standard orthogonal matrix
Lie algebras. No dimension-tagged replacement is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.OrthogonalLieStructure

attribute [local instance 100] LieRing.ofAssociativeRing
open LieAlgebra
open D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal

variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

private def rotation (i j : n) : Orthogonal.so n k :=
  ⟨Matrix.single i j 1 - Matrix.single j i 1, by
    rw [Orthogonal.mem_so]
    simp [Matrix.transpose_sub, Matrix.transpose_single, neg_sub]⟩

private def rotationProjector (i j : n) (A : Orthogonal.so n k) : Orthogonal.so n k :=
  -⁅rotation i j, ⁅rotation i j, A⁆⁆

private theorem rotation_square (i j : n) (hij : i ≠ j) :
    (rotation (k := k) i j).val * (rotation i j).val =
      -(Matrix.single i i 1 + Matrix.single j j 1) := by
  simp [rotation, sub_mul, mul_sub, Matrix.single_mul_single_of_ne,
    hij, Ne.symm hij]

private theorem rotationProjector_entry (i j : n) (hij : i ≠ j)
    (A : Orthogonal.so n k) (r s : n) :
    (rotationProjector i j A).val r s =
      if ((r = i ∨ r = j) ∧ ¬(s = i ∨ s = j)) ∨
          (¬(r = i ∨ r = j) ∧ (s = i ∨ s = j)) then A.val r s else 0 := by
  have hexpand (X Y : Matrix n n k) :
      -(X * (X * Y - Y * X) - (X * Y - Y * X) * X) =
      -(X * X * Y) + 2 • (X * Y * X) - Y * (X * X) := by
    noncomm_ring
  change (-( (rotation i j).val * ((rotation i j).val * A.val - A.val * (rotation i j).val) -
    ((rotation i j).val * A.val - A.val * (rotation i j).val) * (rotation i j).val)) r s = _
  rw [hexpand, rotation_square i j hij]
  simp only [rotation, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.smul_apply]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    simp_all [Matrix.single_apply, Matrix.single_mul_apply_same,
      Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_same,
      Matrix.mul_single_apply_of_ne, diagonal_zero, coefficient_skew] <;> ring

private theorem rotationProjector_mem (I : LieIdeal k (Orthogonal.so n k))
    {A : Orthogonal.so n k} (hA : A ∈ I) (i j : n) : rotationProjector i j A ∈ I :=
  I.neg_mem (I.lie_mem (I.lie_mem hA))

/-- Four commuting coordinate projectors isolate one rotation as soon as five
coordinate indices are available. The exceptional dimension four is visible in
this calculation rather than inferred from a dimension label. -/
private theorem isolate_rotation_five (A : Orthogonal.so n k)
    (i j t u v : n) (hij : i ≠ j) (hit : i ≠ t) (hiu : i ≠ u) (hiv : i ≠ v)
    (hjt : j ≠ t) (hju : j ≠ u) (hjv : j ≠ v) (htu : t ≠ u) (htv : t ≠ v)
    (huv : u ≠ v) :
    rotationProjector j v (rotationProjector i u
      (rotationProjector j t (rotationProjector i t A))) =
      A.val i j • rotation i j := by
  apply Subtype.ext
  ext r s
  simp only [rotationProjector_entry j v hjv, rotationProjector_entry i u hiu,
    rotationProjector_entry j t hjt, rotationProjector_entry i t hit]
  have hsupport :
      ((((r = j ∨ r = v) ∧ ¬(s = j ∨ s = v)) ∨
          (¬(r = j ∨ r = v) ∧ (s = j ∨ s = v))) ∧
        (((r = i ∨ r = u) ∧ ¬(s = i ∨ s = u)) ∨
          (¬(r = i ∨ r = u) ∧ (s = i ∨ s = u))) ∧
        (((r = j ∨ r = t) ∧ ¬(s = j ∨ s = t)) ∨
          (¬(r = j ∨ r = t) ∧ (s = j ∨ s = t))) ∧
        (((r = i ∨ r = t) ∧ ¬(s = i ∨ s = t)) ∨
          (¬(r = i ∨ r = t) ∧ (s = i ∨ s = t)))) ↔
        (r = i ∧ s = j) ∨ (r = j ∧ s = i) := by
    aesop
  by_cases h : (r = i ∧ s = j) ∨ (r = j ∧ s = i)
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp_all [rotation, Matrix.single_apply, coefficient_skew]
  · have hn := mt hsupport.mp h
    simp only [not_and_or] at hn
    rcases hn with h₁ | h₂ | h₃ | h₄ <;>
      simp_all [rotation, Matrix.single_apply]

private theorem isolate_rotation_three (A : Orthogonal.so n k)
    (i j t : n) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (hn : Fintype.card n = 3) :
    rotationProjector j t (rotationProjector i t A) = A.val i j • rotation i j := by
  have hset : ({i,j,t} : Finset n) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [hij, hit, hjt, hn])
  have hcover (r : n) : r = i ∨ r = j ∨ r = t := by
    have hr : r ∈ ({i,j,t} : Finset n) := by rw [hset]; exact Finset.mem_univ r
    simpa using hr
  apply Subtype.ext
  ext r s
  rcases hcover r with rfl | rfl | rfl <;>
    rcases hcover s with rfl | rfl | rfl <;>
    simp [rotationProjector_entry, hit, hjt, hij, Ne.symm hit, Ne.symm hjt,
      Ne.symm hij, rotation, Matrix.single_apply, coefficient_skew]

private theorem rotation_neg (i j : n) : rotation (k := k) j i = -rotation i j := by
  apply Subtype.ext
  simp [rotation, neg_sub]

private theorem rotation_adjacent (i j t : n) (hij : i ≠ j) (hjt : j ≠ t)
    (hit : i ≠ t) : ⁅rotation (k := k) i j, rotation j t⁆ = rotation i t := by
  apply Subtype.ext
  simp [rotation, Ring.lie_def, sub_mul, mul_sub,
    Matrix.single_mul_single_of_ne, hij, hjt, hit,
    Ne.symm hij, Ne.symm hjt, Ne.symm hit]

private theorem rotation_self (i : n) : rotation (k := k) i i = 0 := by
  apply Subtype.ext
  simp [rotation]

private theorem sum_rotations (A : Orthogonal.so n k) :
    (∑ i, ∑ j, (A.val i j / 2) • rotation i j) = A := by
  apply Subtype.ext
  ext r s
  simp only [LieSubalgebra.coe_sum, SetLike.val_smul, rotation, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]
  simp [Finset.sum_sub_distrib, mul_ite, coefficient_skew]
  ring

private theorem ideal_eq_top_of_rotation_mem (I : LieIdeal k (Orthogonal.so n k))
    (i j : n) (hij : i ≠ j) (hR : rotation i j ∈ I) : I = ⊤ := by
  have hstar (t : n) : rotation i t ∈ I := by
    by_cases hti : t = i
    · subst t; rw [rotation_self]; exact I.zero_mem
    by_cases htj : t = j
    · subst t; exact hR
    have h := lie_mem_left k (Orthogonal.so n k) I (rotation i j) (rotation j t) hR
    rwa [rotation_adjacent i j t hij (Ne.symm htj) (Ne.symm hti)] at h
  have hall (r s : n) : rotation r s ∈ I := by
    by_cases hrs : r = s
    · subst s; rw [rotation_self]; exact I.zero_mem
    by_cases hri : r = i
    · subst r; exact hstar s
    by_cases hsi : s = i
    · subst s; rw [rotation_neg]; exact I.neg_mem (hstar r)
    have hri' : rotation r i ∈ I := by rw [rotation_neg]; exact I.neg_mem (hstar r)
    have h := lie_mem_left k (Orthogonal.so n k) I (rotation r i) (rotation i s) hri'
    rwa [rotation_adjacent r i s hri (Ne.symm hsi) hrs] at h
  apply top_unique
  intro A hA
  rw [← sum_rotations A]
  exact I.sum_mem (fun r _ => I.sum_mem (fun t _ => I.smul_mem _ (hall r t)))

private theorem exists_outside (s : Finset n) (hs : s.card < Fintype.card n) :
    ∃ i : n, i ∉ s := by
  by_contra! h
  have hsub : (Finset.univ : Finset n) ⊆ s := fun i _ => h i
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_univ] at hc
  omega

/-- The actual standard orthogonal algebra is simple in dimension three and in
every dimension at least five. The proof isolates rotations inside arbitrary
ideals; it does not use a dimension-only replacement for simplicity. -/
theorem isSimple_of_card_ne_four (hn : 3 ≤ Fintype.card n) (hfour : Fintype.card n ≠ 4) :
    IsSimple k (Orthogonal.so n k) := by
  classical
  have hideal (I : LieIdeal k (Orthogonal.so n k)) : I = ⊥ ∨ I = ⊤ := by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    have hex : ∃ A : Orthogonal.so n k, A ∈ I ∧ A ≠ 0 := by
      by_contra! h
      apply hI
      apply le_antisymm ?_ bot_le
      intro A hA
      change A = 0
      exact h A hA
    obtain ⟨A,hAI,hA⟩ := hex
    have hentry : ∃ i j, A.val i j ≠ 0 := by
      by_contra! h
      apply hA
      apply Subtype.ext
      ext i j
      exact h i j
    obtain ⟨i,j,hijA⟩ := hentry
    have hij : i ≠ j := by intro h; subst j; exact hijA (diagonal_zero A i)
    obtain ⟨t,ht⟩ := exists_outside ({i,j} : Finset n) (by simp [hij]; omega)
    have hti : t ≠ i := by simpa using (show t ≠ i ∧ t ≠ j by simpa using ht).1
    have htj : t ≠ j := by simpa using (show t ≠ i ∧ t ≠ j by simpa using ht).2
    have hisolate : A.val i j • rotation i j ∈ I := by
      by_cases hthree : Fintype.card n = 3
      · rw [← isolate_rotation_three A i j t hij (Ne.symm hti) (Ne.symm htj) hthree]
        exact rotationProjector_mem I (rotationProjector_mem I hAI i t) j t
      · have hfive : 5 ≤ Fintype.card n := by omega
        obtain ⟨u,hu⟩ := exists_outside ({i,j,t} : Finset n) (by simp [hij, Ne.symm hti, Ne.symm htj]; omega)
        have hu' : u ≠ i ∧ u ≠ j ∧ u ≠ t := by simpa using hu
        obtain ⟨v,hv⟩ := exists_outside ({i,j,t,u} : Finset n) (by
          simp [hij, Ne.symm hti, Ne.symm htj, hu'.1, hu'.2.1, hu'.2.2,
            Ne.symm hu'.1, Ne.symm hu'.2.1, Ne.symm hu'.2.2]; omega)
        have hv' : v ≠ i ∧ v ≠ j ∧ v ≠ t ∧ v ≠ u := by simpa using hv
        rw [← isolate_rotation_five A i j t u v hij (Ne.symm hti) (Ne.symm hu'.1)
          (Ne.symm hv'.1) (Ne.symm htj) (Ne.symm hu'.2.1) (Ne.symm hv'.2.1)
          (Ne.symm hu'.2.2) (Ne.symm hv'.2.2.1) (Ne.symm hv'.2.2.2)]
        exact rotationProjector_mem I (rotationProjector_mem I
          (rotationProjector_mem I (rotationProjector_mem I hAI i t) j t) i u) j v
    have hR : rotation (k := k) i j ∈ I := by
      have h := I.smul_mem (A.val i j)⁻¹ hisolate
      simpa only [smul_smul, inv_mul_cancel₀ hijA, one_smul] using h
    exact ideal_eq_top_of_rotation_mem I i j hij hR
  refine ⟨hideal, ?_⟩
  intro habelian
  obtain ⟨i,hi⟩ := exists_outside (∅ : Finset n) (by simp; omega)
  obtain ⟨j,hj⟩ := exists_outside ({i} : Finset n) (by simp; omega)
  have hji : j ≠ i := by simpa using hj
  obtain ⟨t,ht⟩ := exists_outside ({i,j} : Finset n) (by simp [Ne.symm hji]; omega)
  have ht' : t ≠ i ∧ t ≠ j := by simpa using ht
  have hz := trivial_lie_zero (Orthogonal.so n k) (Orthogonal.so n k)
    (rotation (k := k) i j) (rotation j t)
  rw [rotation_adjacent i j t (Ne.symm hji) (Ne.symm ht'.2) (Ne.symm ht'.1)] at hz
  have hh := congrArg (fun R : Orthogonal.so n k => R.val i t) hz
  simp [rotation, Matrix.single_apply, Ne.symm ht'.1, ht'.1] at hh

private theorem single_sandwich (A B : Matrix n n k) (i j r s : n) :
    (A * Matrix.single i j 1 * B : Matrix n n k) r s = A r i * B j s := by
  have h (x : n) : (A * Matrix.single i j 1 : Matrix n n k) r x =
      if x = j then A r i else 0 := by
    by_cases hx : x = j
    · subst x
      simp
    · simp [hx]
  rw [Matrix.mul_apply]
  simp_rw [h]
  simp [ite_mul]

private theorem double_rotation_entry (A : Orthogonal.so n k) (i j r s : n) :
    (⁅A, ⁅A, rotation i j⁆⁆).val r s =
      (if s = j then (A.val * A.val) r i else 0) -
      (if s = i then (A.val * A.val) r j else 0) -
      2 * (A.val r i * A.val j s - A.val r j * A.val i s) +
      (if r = i then (A.val * A.val) j s else 0) -
      (if r = j then (A.val * A.val) i s else 0) := by
  change (A.val * (A.val * (rotation i j).val - (rotation i j).val * A.val) -
    (A.val * (rotation i j).val - (rotation i j).val * A.val) * A.val : Matrix n n k) r s = _
  have he (X Y : Matrix n n k) : X * (X * Y - Y * X) - (X * Y - Y * X) * X =
      X * X * Y - (X * Y * X + X * Y * X) + Y * (X * X) := by noncomm_ring
  rw [he]
  simp only [rotation, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.add_apply]
  rw [single_sandwich, single_sandwich]
  by_cases hs : s = j <;> by_cases ht : s = i <;>
    by_cases hr : r = i <;> by_cases hu : r = j <;>
    simp_all [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne,
      Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne] <;> ring

private theorem square_transpose (A : Orthogonal.so n k) :
    (A.val * A.val).transpose = A.val * A.val := by
  rw [Matrix.transpose_mul, (Orthogonal.mem_so n k A.val).mp A.property, neg_mul_neg]

private theorem contracted_double_rotation (A : Orthogonal.so n k) (r i : n) :
    ∑ j, (⁅A, ⁅A, rotation i j⁆⁆).val r j =
      ((Fintype.card n : k) - 4) * (A.val * A.val) r i +
        if r = i then Matrix.trace (A.val * A.val) else 0 := by
  simp_rw [double_rotation_entry, diagonal_zero, mul_zero, zero_sub,
    mul_neg, sub_neg_eq_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.card_univ]
  have hs : (∑ j, A.val r j * A.val i j) = -(A.val * A.val) r i := by
    calc
      (∑ j, A.val r j * A.val i j) = ∑ j, -(A.val r j * A.val j i) :=
        Finset.sum_congr rfl (fun j _ => by rw [coefficient_skew A j i, mul_neg])
      _ = -(A.val * A.val) r i := by rw [Finset.sum_neg_distrib]; rfl
  rw [← Finset.mul_sum, hs]
  have hsym : (A.val * A.val) i r = (A.val * A.val) r i :=
    congrArg (fun X : Matrix n n k => X r i) (square_transpose A)
  by_cases hri : r = i
  · subst r
    simp only [ite_true, Finset.sum_ite_irrel, Matrix.trace, Matrix.diag_apply]
    ring
  · simp only [hri, ite_false, Finset.sum_ite_irrel, Finset.sum_const_zero, hsym]
    ring

private theorem trace_square_zero_of_ad_square_zero (A : Orthogonal.so n k)
    (hA : ∀ B : Orthogonal.so n k, ⁅A, ⁅A, B⁆⁆ = 0)
    (hn : 3 ≤ Fintype.card n) : Matrix.trace (A.val * A.val) = 0 := by
  have hi (i : n) :
      ((Fintype.card n : k) - 4) * (A.val * A.val) i i +
        Matrix.trace (A.val * A.val) = 0 := by
    simpa [hA] using (contracted_double_rotation A i i).symm
  have hs : (∑ i, (((Fintype.card n : k) - 4) * (A.val * A.val) i i +
      Matrix.trace (A.val * A.val))) = 0 := Finset.sum_eq_zero (fun i _ => hi i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ] at hs
  change ((Fintype.card n : k) - 4) * Matrix.trace (A.val * A.val) +
    (Fintype.card n : k) * Matrix.trace (A.val * A.val) = 0 at hs
  have ht : (2 * ((Fintype.card n : k) - 2)) * Matrix.trace (A.val * A.val) = 0 := by
    linear_combination hs
  have h2 : (Fintype.card n : k) ≠ 2 := by
    exact_mod_cast (show Fintype.card n ≠ 2 by omega)
  exact (mul_eq_zero.mp ht).resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h2))

private theorem square_zero_of_ad_square_zero (A : Orthogonal.so n k)
    (hA : ∀ B : Orthogonal.so n k, ⁅A, ⁅A, B⁆⁆ = 0)
    (hn : 3 ≤ Fintype.card n) (hfour : Fintype.card n ≠ 4) : A.val * A.val = 0 := by
  have ht := trace_square_zero_of_ad_square_zero A hA hn
  have h4 : (Fintype.card n : k) ≠ 4 := by exact_mod_cast hfour
  ext r i
  have hh : ((Fintype.card n : k) - 4) * (A.val * A.val) r i = 0 := by
    simpa [hA, ht] using (contracted_double_rotation A r i).symm
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr h4)

private theorem ad_square_zero_eq_zero (A : Orthogonal.so n k)
    (hA : ∀ B : Orthogonal.so n k, ⁅A, ⁅A, B⁆⁆ = 0)
    (hn : 3 ≤ Fintype.card n) (hfour : Fintype.card n ≠ 4) : A = 0 := by
  have hs := square_zero_of_ad_square_zero A hA hn hfour
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun B : Orthogonal.so n k => B.val i j) (hA (rotation i j))
  change (⁅A, ⁅A, rotation i j⁆⁆).val i j = 0 at hh
  rw [double_rotation_entry] at hh
  simp [hs, diagonal_zero] at hh
  exact hh

/-- A standard orthogonal Lie algebra in dimension three or at least five has
trivial actual solvable radical. This proof works over every characteristic-zero
field, without algebraic closedness. The dimension-four split case is separate. -/
theorem hasTrivialRadical_of_card_ne_four
    (hn : 3 ≤ Fintype.card n) (hfour : Fintype.card n ≠ 4) :
    HasTrivialRadical k (Orthogonal.so n k) := by
  apply (hasTrivialRadical_iff_no_abelian_ideals k (Orthogonal.so n k)).mpr
  intro I hI
  letI : IsLieAbelian I := hI
  apply le_antisymm ?_ bot_le
  intro A hA
  change A = 0
  apply ad_square_zero_eq_zero A ?_ hn hfour
  intro B
  have hAB : ⁅A, B⁆ ∈ I := lie_mem_left k (Orthogonal.so n k) I _ _ hA
  exact congrArg Subtype.val
    (trivial_lie_zero I I (⟨A, hA⟩ : I) (⟨⁅A, B⁆, hAB⟩ : I))

private def skewThree (a b c : k) : Orthogonal.so (Fin 3) k :=
  ⟨!![0,a,b; -a,0,c; -b,-c,0], by
    rw [Orthogonal.mem_so]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

private def skewFour (a b c d e f : k) : Orthogonal.so (Fin 4) k :=
  ⟨!![0,a,b,c; -a,0,d,e; -b,-d,0,f; -c,-e,-f,0], by
    rw [Orthogonal.mem_so]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

private theorem normal_three (A : Orthogonal.so (Fin 3) k) :
    A = skewThree (A.val 0 1) (A.val 0 2) (A.val 1 2) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | exact diagonal_zero A _ | rfl | exact coefficient_skew A _ _

private theorem normal_four (A : Orthogonal.so (Fin 4) k) :
    A = skewFour (A.val 0 1) (A.val 0 2) (A.val 0 3)
      (A.val 1 2) (A.val 1 3) (A.val 2 3) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | exact diagonal_zero A _ | rfl | exact coefficient_skew A _ _

private def fourToThree (A : Orthogonal.so (Fin 4) k) :
    Orthogonal.so (Fin 3) k × Orthogonal.so (Fin 3) k :=
  (skewThree (A.val 0 1 + A.val 2 3) (A.val 0 2 - A.val 1 3)
      (A.val 0 3 + A.val 1 2),
   skewThree (A.val 0 1 - A.val 2 3) (A.val 0 2 + A.val 1 3)
      (A.val 1 2 - A.val 0 3))

private def threeToFour (P : Orthogonal.so (Fin 3) k × Orthogonal.so (Fin 3) k) :
    Orthogonal.so (Fin 4) k :=
  skewFour ((P.1.val 0 1 + P.2.val 0 1) / 2)
    ((P.1.val 0 2 + P.2.val 0 2) / 2)
    ((P.1.val 1 2 - P.2.val 1 2) / 2)
    ((P.1.val 1 2 + P.2.val 1 2) / 2)
    ((P.2.val 0 2 - P.1.val 0 2) / 2)
    ((P.1.val 0 1 - P.2.val 0 1) / 2)

-- The finite matrix bracket calculation expands both rotation triples.
set_option maxHeartbeats 1600000 in
/-- The actual classical dimension-four orthogonal Lie algebra splits into two
actual dimension-three orthogonal Lie algebras. The coordinates are the two
self-dual rotation triples; no algebraic-closedness assumption is needed. -/
def soFourEquiv : Orthogonal.so (Fin 4) k ≃ₗ⁅k⁆
    Orthogonal.so (Fin 3) k × Orthogonal.so (Fin 3) k where
  toFun := fourToThree
  invFun := threeToFour
  left_inv A := by
    conv_rhs => rw [normal_four A]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourToThree, threeToFour, skewThree, skewFour] <;> ring
  right_inv P := by
    rcases P with ⟨A,B⟩
    conv_rhs => rw [normal_three A, normal_three B]
    apply Prod.ext <;> apply Subtype.ext <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [fourToThree, threeToFour, skewThree, skewFour] <;> ring
  map_add' A B := by
    apply Prod.ext <;> apply Subtype.ext <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [fourToThree, skewThree] <;> ring
  map_smul' c A := by
    apply Prod.ext <;> apply Subtype.ext <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [fourToThree, skewThree] <;> ring
  map_lie' := by
    intro A B
    have hA := normal_four A
    have hB := normal_four B
    rw [hA, hB]
    apply Prod.ext <;> apply Subtype.ext <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [fourToThree, skewThree, skewFour, Ring.lie_def,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The dimension-four standard orthogonal Lie algebra has trivial actual
solvable radical, by its explicit split into two dimension-three factors. -/
theorem so_four_hasTrivialRadical : HasTrivialRadical k (Orthogonal.so (Fin 4) k) := by
  haveI : HasTrivialRadical k (Orthogonal.so (Fin 3) k) :=
    hasTrivialRadical_of_card_ne_four (by simp) (by simp)
  let f : Bool → (Orthogonal.so (Fin 3) k × Orthogonal.so (Fin 3) k) →ₗ⁅k⁆
      Orthogonal.so (Fin 3) k :=
    fun a => if a then LieHom.fst _ _ _ else LieHom.snd _ _ _
  have hf : ∀ a, Function.Surjective (f a) := by
    intro a
    cases a
    · exact LieHom.snd_surjective
    · exact LieHom.fst_surjective
  haveI : HasTrivialRadical k (Orthogonal.so (Fin 3) k × Orthogonal.so (Fin 3) k) :=
    D5.S3.QuadraticForms.LieRadicalTransfer.hasTrivialRadical_of_separating_surjections
      (fun _ : Bool => Orthogonal.so (Fin 3) k) f hf (by
        intro x hx
        apply Prod.ext
        · exact hx true
        · exact hx false)
  exact D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer.trivialRadical_of_equiv
    (soFourEquiv (k := k)).symm

/-- Every standard orthogonal Lie algebra in dimension at least three has
trivial actual solvable radical. The dimension-four boundary is included. -/
theorem hasTrivialRadical (m : ℕ) (hm : 3 ≤ m) :
    HasTrivialRadical k (Orthogonal.so (Fin m) k) := by
  by_cases h : m = 4
  · subst m
    exact so_four_hasTrivialRadical
  · exact hasTrivialRadical_of_card_ne_four (by simpa using hm) (by simpa using h)

end D5.S3.QuadraticForms.OrthogonalLieStructure
