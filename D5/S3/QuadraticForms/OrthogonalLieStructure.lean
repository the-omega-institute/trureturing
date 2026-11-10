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
escape_witness: isolate_rotation_five, isolate_rotation_three, soFourEquiv
The proof-shape assessment is the author's and awaits independent whole review.
  hasTrivialRadical_of_card_ne_four: proof_shape: bind-only;
    escape_witness: none;
    consumers: so_four_hasTrivialRadical, hasTrivialRadical
  so_four_hasTrivialRadical: proof_shape: bind-only; escape_witness: none;
    consumers: hasTrivialRadical
  hasTrivialRadical: proof_shape: bind-only; escape_witness: none;
    consumers: DerivationRadicalQuotient.quotient_of_nonzero_squares
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
  -⁅rotation (k := k) i j, ⁅rotation (k := k) i j, A⁆⁆

private theorem rotation_square (i j : n) (hij : i ≠ j) :
    (rotation (k := k) i j).val * (rotation i j).val =
      -(Matrix.single i i 1 + Matrix.single j j 1) := by
  simp [rotation, sub_mul, mul_sub, Matrix.single_mul_single_of_ne,
    hij, Ne.symm hij] <;> abel

private theorem rotationProjector_entry (i j : n) (hij : i ≠ j)
    (A : Orthogonal.so n k) (r s : n) :
    (rotationProjector i j A).val r s =
      if ((r = i ∨ r = j) ∧ ¬(s = i ∨ s = j)) ∨
          (¬(r = i ∨ r = j) ∧ (s = i ∨ s = j)) then A.val r s else 0 := by
  have hexpand (X Y : Matrix n n k) :
      -(X * (X * Y - Y * X) - (X * Y - Y * X) * X) =
      -(X * X * Y) + 2 • (X * Y * X) - Y * (X * X) := by
    noncomm_ring
  change ((-((rotation (k := k) i j).val *
    ((rotation (k := k) i j).val * A.val - A.val * (rotation (k := k) i j).val) -
    ((rotation (k := k) i j).val * A.val - A.val * (rotation (k := k) i j).val) *
      (rotation (k := k) i j).val)) : Matrix n n k) r s = _
  rw [hexpand, rotation_square i j hij]
  simp only [rotation, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.smul_apply]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    simp_all [Matrix.single_apply, Matrix.single_mul_apply_same,
      Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_same,
      Matrix.mul_single_apply_of_ne, diagonal_zero, coefficient_skew A i j, eq_comm] <;>
    (try rw [coefficient_skew A r s]) <;> ring

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
  have hmask (p q u v : Prop) [Decidable p] [Decidable q] [Decidable u]
      [Decidable v] (x : k) :
      (if p then (if q then (if u then (if v then x else 0) else 0) else 0) else 0) =
      if p ∧ q ∧ u ∧ v then x else 0 := by
    by_cases hp : p <;> by_cases hq : q <;> by_cases hu : u <;> by_cases hv : v <;>
      simp [hp,hq,hu,hv]
  simp only [hmask, hsupport]
  by_cases h : (r = i ∧ s = j) ∨ (r = j ∧ s = i)
  · rcases h with ⟨hr,hs⟩ | ⟨hr,hs⟩
    · subst r; subst s
      simp [rotation, Matrix.single_apply, hij, Ne.symm hij]
    · subst r; subst s
      simp [rotation, Matrix.single_apply, hij, Ne.symm hij, coefficient_skew A i j]
  · have h₁ : ¬ (i = r ∧ j = s) := by
      rintro ⟨rfl,rfl⟩
      exact h (Or.inl ⟨rfl,rfl⟩)
    have h₂ : ¬ (j = r ∧ i = s) := by
      rintro ⟨rfl,rfl⟩
      exact h (Or.inr ⟨rfl,rfl⟩)
    simp [h,rotation,Matrix.single_apply,h₁,h₂]

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
  rcases hcover r with hr | hr | hr <;>
    rcases hcover s with hs | hs | hs <;>
    simp [hr, hs, rotationProjector_entry, hit, hjt, hij, Ne.symm hit, Ne.symm hjt,
      Ne.symm hij, rotation, Matrix.single_apply, coefficient_skew A i j, diagonal_zero]

private theorem rotation_neg (i j : n) : rotation (k := k) j i = -rotation i j := by
  apply Subtype.ext
  simp [rotation, neg_sub]

private theorem rotation_adjacent (i j t : n) (hij : i ≠ j) (hjt : j ≠ t)
    (hit : i ≠ t) : ⁅rotation (k := k) i j, rotation j t⁆ = rotation (k := k) i t := by
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
  change (Orthogonal.so n k).incl (∑ i, ∑ j, (A.val i j / 2) • rotation i j) = A.val
  simp only [map_sum, map_smul]
  change (∑ i, ∑ j, (A.val i j / 2) •
    (Matrix.single i j 1 - Matrix.single j i 1)) = A.val
  ext r s
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul, mul_sub, mul_ite, Finset.sum_sub_distrib]
  have hdelta (f : n → n → k) (r s : n) :
      (∑ i, ∑ j, if i = r ∧ j = s then f i j else 0) = f r s := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro i hi hir
      exact Finset.sum_eq_zero (fun j hj => by simp [hir])
    · simp
  have hdelta' (f : n → n → k) (r s : n) :
      (∑ i, ∑ j, if j = r ∧ i = s then f i j else 0) = f s r := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro i hi his
      exact Finset.sum_eq_zero (fun j hj => by simp [his])
    · simp
  simp only [hdelta, hdelta']
  rw [coefficient_skew A r s]
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
      change (A.val i j)⁻¹ • (A.val i j • rotation i j) ∈ I at h
      simpa only [smul_smul, inv_mul_cancel₀ hijA, one_smul] using h
    exact ideal_eq_top_of_rotation_mem I i j hij hR
  refine ⟨hideal, ?_⟩
  intro habelian
  letI : IsLieAbelian (Orthogonal.so n k) := habelian
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

/-- A standard orthogonal Lie algebra in dimension three or at least five has
trivial actual solvable radical. This proof works over every characteristic-zero
field, without algebraic closedness. The dimension-four split case is separate. -/
theorem hasTrivialRadical_of_card_ne_four
    (hn : 3 ≤ Fintype.card n) (hfour : Fintype.card n ≠ 4) :
    HasTrivialRadical k (Orthogonal.so n k) := by
  have : IsSimple k (Orthogonal.so n k) := isSimple_of_card_ne_four hn hfour
  infer_instance

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
