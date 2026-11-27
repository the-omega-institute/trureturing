/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct sums of vertex labels give orthogonal symmetric unitaries for a partition of edges into parallel classes. -/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Symmetric unitary bases from parallel classes

A restricted edge-sum labeling turns each class into a family of character
congruences. The edge partition and diagonal characters give a basis of the
complex symmetric subspace.
-/

open scoped BigOperators ComplexConjugate
open Matrix Module

namespace AffineNine

noncomputable section

abbrev Edge (X : Type*) := {e : Sym2 X // ¬e.IsDiag}

def edge {X : Type*} (x y : X) (h : x ≠ y) : Edge X :=
  ⟨s(x, y), fun hd => h (Sym2.mk_isDiag_iff.mp hd)⟩

@[elab_as_elim] theorem Edge.inductionOn {X : Type*} {P : Edge X → Prop}
    (e : Edge X) (h : ∀ x y (hne : x ≠ y), P (edge x y hne)) : P e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ x y => exact h x y (fun hxy => he (Sym2.mk_isDiag_iff.mpr hxy))

/-- A vertex label whose endpoint sums enumerate the unordered edges of the class. -/
structure EdgeLabeling (F B G : Type*) [AddCommGroup G] where
  label : B → F → G
  edgeEquiv : B × Edge F ≃ G
  edgeEquiv_apply : ∀ b x y (h : x ≠ y),
    edgeEquiv (b, edge x y h) = label b x + label b y

/-- The local matrix inserted on every block of a class. -/
structure FlatHollow (F : Type*) [Fintype F] [DecidableEq F] where
  matrix : Matrix F F ℂ
  unitary : matrix ∈ Matrix.unitaryGroup F ℂ
  symm : matrix.IsSymm
  diag : ∀ x, matrix x x = 0
  normSq : ∀ x y, x ≠ y → ‖matrix x y‖ ^ 2 = 1 / 8

/-- Each class decomposes the vertices into blocks. Every distinct pair lies in
exactly one block of exactly one class. -/
structure ParallelClasses (V D F B : Type*) where
  coords : D → V ≃ F × B
  unique_class : ∀ x y : V, x ≠ y →
    ∃! d, (coords d x).2 = (coords d y).2

variable {X V D F B G : Type*}

private def classEdge (P : ParallelClasses V D F B) (d : D)
    (b : B) (e : Edge F) : Edge V :=
  ⟨e.1.map (fun x => (P.coords d).symm (x, b)), by
    induction e using Edge.inductionOn with
    | _ x y hxy =>
      intro hd
      exact hxy (congrArg Prod.fst ((P.coords d).symm.injective
        (Sym2.mk_isDiag_iff.mp hd)))⟩

/-- The class and block of an edge are unique, so the disjoint sum over classes
and blocks enumerates the edges of the complete graph. -/
def ParallelClasses.edges (P : ParallelClasses V D F B) : D × (B × Edge F) ≃ Edge V :=
  Equiv.ofBijective (fun p => classEdge P p.1 p.2.1 p.2.2) (by
    constructor
    · rintro ⟨d, b, e⟩ ⟨d', b', e'⟩
      induction e using Edge.inductionOn with
      | _ x y hxy =>
        induction e' using Edge.inductionOn with
        | _ x' y' hx'y' =>
          intro h
          have hp := Sym2.eq_iff.mp (congrArg Subtype.val h)
          have hn : (P.coords d).symm (x, b) ≠ (P.coords d).symm (y, b) :=
            fun hh => hxy (congrArg Prod.fst ((P.coords d).symm.injective hh))
          obtain ⟨c, _, hc⟩ := P.unique_class _ _ hn
          have hd : d = c := hc d (by simp)
          have hd' : d' = c := hc d' (by
            rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy])
          have he : d' = d := hd'.trans hd.symm
          rw [he] at hp ⊢
          rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · have hx := Prod.mk.inj ((P.coords d).symm.injective hx)
            have hy := Prod.mk.inj ((P.coords d).symm.injective hy)
            exact Prod.ext rfl (Prod.ext hx.2
              (Subtype.ext (Sym2.eq_iff.mpr (Or.inl ⟨hx.1, hy.1⟩))))
          · have hx := Prod.mk.inj ((P.coords d).symm.injective hx)
            have hy := Prod.mk.inj ((P.coords d).symm.injective hy)
            exact Prod.ext rfl (Prod.ext hx.2
              (Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨hx.1, hy.1⟩))))
    · intro e
      induction e using Edge.inductionOn with
      | _ x y hxy =>
        obtain ⟨d, hd, _⟩ := P.unique_class x y hxy
        have hne : (P.coords d x).1 ≠ (P.coords d y).1 :=
          fun hf => hxy ((P.coords d).injective (Prod.ext hf hd))
        refine ⟨(d, (P.coords d x).2, edge _ _ hne), Subtype.ext ?_⟩
        change s((P.coords d).symm ((P.coords d x).1, (P.coords d x).2),
          (P.coords d).symm ((P.coords d y).1, (P.coords d x).2)) = s(x, y)
        rw [hd]
        have hx : (P.coords d).symm ((P.coords d x).1, (P.coords d y).2) = x := by
          rw [← hd]
          exact (P.coords d).symm_apply_apply x
        rw [hx]
        simp)

section Pairing

variable [Fintype X]

/-- Hilbert–Schmidt inner product, conjugate-linear in the first matrix. -/
def hs (A B : Matrix X X ℂ) : ℂ :=
  ∑ i, ∑ j, conj (A i j) * B i j

theorem hs_self_of_unitary [DecidableEq X] {A : Matrix X X ℂ}
    (hA : A ∈ Matrix.unitaryGroup X ℂ) : hs A A = Fintype.card X := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA
  unfold hs
  calc
    _ = ∑ i, (A * star A) i i := by
      simp only [Matrix.mul_apply, Matrix.star_apply, mul_comm]
      rfl
    _ = _ := by simp [h]

private def hsLinear (A : Matrix X X ℂ) : Matrix X X ℂ →ₗ[ℂ] ℂ where
  toFun := hs A
  map_add' M N := by
    simp [hs, mul_add, Finset.sum_add_distrib]
  map_smul' c M := by
    simp [hs, Finset.mul_sum, mul_left_comm]

end Pairing

open scoped Classical in
private theorem sum_characters [AddCommGroup G] [Fintype G] (χ ψ : AddChar G ℂ) :
    ∑ g, conj (χ g) * ψ g = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  simp only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
    Fintype.expect_eq_sum_div_card] at h
  have hg : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_eq_iff hg] at h
  calc
    _ = ∑ g, ψ g * conj (χ g) := Finset.sum_congr rfl fun g _ => mul_comm _ _
    _ = _ := by
      rw [h]
      split_ifs <;> simp

private def orderedEdge {X : Type*} (p : {p : X × X // p.1 ≠ p.2}) : Edge X :=
  edge p.1.1 p.1.2 p.2

private theorem sum_offDiag [DecidableEq X] [Fintype X] (f : Edge X → ℂ) :
    (∑ x, ∑ y, if h : x ≠ y then f (edge x y h) else 0) = 2 * ∑ e, f e := by
  classical
  let O := {p : X × X // p.1 ≠ p.2}
  let q : O → Edge X := orderedEdge
  have hfiber (e : Edge X) : (Finset.univ.filter fun p : O => q p = e).card = 2 := by
    induction e using Edge.inductionOn with
    | _ x y h =>
      let p : O := ⟨(x, y), h⟩
      let p' : O := ⟨(y, x), h.symm⟩
      have hne : p ≠ p' := fun hh => h (congrArg (fun a : O => a.1.1) hh)
      have hset : (Finset.univ.filter fun o : O => q o = edge x y h) = {p, p'} := by
        ext ⟨⟨a, b⟩, hab⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rw [← Subtype.val_inj]
        change s(a, b) = s(x, y) ↔ (⟨(a, b), hab⟩ : O) = p ∨ (⟨(a, b), hab⟩ : O) = p'
        rw [Sym2.eq_iff]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (he | he)
          · exact Or.inl (Prod.mk.inj (congrArg Subtype.val he))
          · exact Or.inr (Prod.mk.inj (congrArg Subtype.val he))
      rw [hset]
      simp [hne]
  calc
    _ = ∑ p : O, f (q p) := by
      rw [← Fintype.sum_prod_type']
      rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight fun p => by simp)
      intro p
      rfl
    _ = ∑ e : Edge X, ∑ p ∈ Finset.univ.filter (fun p : O => q p = e), f e := by
      symm
      exact Finset.sum_fiberwise' Finset.univ q f
    _ = _ := by simp [hfiber, Finset.mul_sum, two_mul]

section Assembly

variable [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Fintype B] [DecidableEq B] [AddCommGroup G] [Fintype G]

private def charDiagonal (l : V → G) (χ : AddChar G ℂ) : Matrix V V ℂ :=
  Matrix.diagonal fun v => χ (l v)

private theorem charDiagonal_unitary (l : V → G) (χ : AddChar G ℂ) :
    charDiagonal l χ ∈ Matrix.unitaryGroup V ℂ := by
  rw [charDiagonal, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro v
  rw [Unitary.mem_iff]
  have h := χ.norm_apply (l v)
  constructor
  · change conj (χ (l v)) * χ (l v) = 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num
  · change χ (l v) * conj (χ (l v)) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num

private def classMatrix (C : FlatHollow F) (e : V ≃ F × B) : Matrix V V ℂ :=
  (Matrix.blockDiagonal fun _ : B => C.matrix).submatrix e e

private theorem classMatrix_unitary (C : FlatHollow F) (e : V ≃ F × B) :
    classMatrix C e ∈ Matrix.unitaryGroup V ℂ := by
  rw [classMatrix, Matrix.submatrix_equiv_mem_unitary, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  simp only [← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff.mp C.unitary]
  exact Matrix.blockDiagonal_one

/-- Character congruence of the reindexed block-diagonal unitary. -/
def hollow (C : FlatHollow F) (L : EdgeLabeling F B G) (e : V ≃ F × B)
    (χ : AddChar G ℂ) : Matrix V V ℂ :=
  let U := charDiagonal (fun v => L.label (e v).2 (e v).1) χ
  U * classMatrix C e * U

theorem hollow_unitary (C : FlatHollow F) (L : EdgeLabeling F B G) (e : V ≃ F × B)
    (χ : AddChar G ℂ) : hollow C L e χ ∈ Matrix.unitaryGroup V ℂ :=
  mul_mem (mul_mem (charDiagonal_unitary _ χ) (classMatrix_unitary C e))
    (charDiagonal_unitary _ χ)

omit [Fintype B] [Fintype G] in
private theorem hollow_apply (C : FlatHollow F) (L : EdgeLabeling F B G)
    (e : V ≃ F × B) (χ : AddChar G ℂ) (v w : V) :
    hollow C L e χ v w =
      if (e v).2 = (e w).2 then
        χ (L.label (e v).2 (e v).1 + L.label (e v).2 (e w).1) * C.matrix (e v).1 (e w).1
      else 0 := by
  simp only [hollow, Matrix.mul_diagonal, Matrix.diagonal_mul, charDiagonal,
    classMatrix, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
  split_ifs with h
  · rw [AddChar.map_add_eq_mul, h]
    ring
  · simp

omit [Fintype B] [Fintype G] in
theorem hollow_symm (C : FlatHollow F) (L : EdgeLabeling F B G) (e : V ≃ F × B)
    (χ : AddChar G ℂ) : (hollow C L e χ).IsSymm := by
  apply Matrix.IsSymm.ext
  intro v w
  rw [hollow_apply, hollow_apply]
  by_cases h : (e v).2 = (e w).2
  · rw [ite_eq_left h, ite_eq_left h.symm, ← h, add_comm, C.symm.apply]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

omit [Fintype B] [Fintype G] in
@[simp] theorem hollow_diag (C : FlatHollow F) (L : EdgeLabeling F B G) (e : V ≃ F × B)
    (χ : AddChar G ℂ) (v : V) : hollow C L e χ v v = 0 := by
  simp [hollow_apply, C.diag]

omit [Fintype B] [Fintype G] in
theorem hollow_zero_of_different_blocks (C : FlatHollow F) (L : EdgeLabeling F B G)
    (e : V ≃ F × B) (χ : AddChar G ℂ) {v w : V} (h : (e v).2 ≠ (e w).2) :
    hollow C L e χ v w = 0 := by
  simp [hollow_apply, h]

private theorem complex_flat (C : FlatHollow F) {x y : F} (h : x ≠ y) :
    conj (C.matrix x y) * C.matrix x y = (1 / 8 : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, C.normSq _ _ h]
  norm_num

open scoped Classical in
theorem hollow_hs (C : FlatHollow F) (L : EdgeLabeling F B G) (e : V ≃ F × B)
    (χ ψ : AddChar G ℂ) :
    hs (hollow C L e χ) (hollow C L e ψ) =
      (1 / 4 : ℂ) * (if χ = ψ then (Fintype.card G : ℂ) else 0) := by
  classical
  let f : G → ℂ := fun g => conj (χ g) * ψ g
  rw [← sum_characters]
  calc
    _ = ∑ b : B, ∑ x : F, ∑ y : F,
          if h : x ≠ y then (1 / 8 : ℂ) * f (L.edgeEquiv (b, edge x y h)) else 0 := by
      let E := e.trans (Equiv.prodComm F B)
      let a : V → V → ℂ := fun v w => conj (hollow C L e χ v w) * hollow C L e ψ v w
      change (∑ v, ∑ w, a v w) = _
      calc
        _ = ∑ p : B × F, ∑ q : B × F, a (E.symm p) (E.symm q) := by
          apply Fintype.sum_equiv E
          intro v
          rw [E.symm_apply_apply]
          exact Fintype.sum_equiv E _ _ (fun w => by rw [E.symm_apply_apply])
        _ = _ := by
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single b]
          · refine Finset.sum_congr rfl fun y _ => ?_
            change a (e.symm (x, b)) (e.symm (y, b)) = _
            by_cases hxy : x = y
            · subst y
              simp [a]
            · simp only [a, hollow_apply, e.apply_symm_apply, dite_eq_left hxy, L.edgeEquiv_apply]
              calc
                _ = (conj (C.matrix x y) * C.matrix x y) * f (L.label b x + L.label b y) := by
                  dsimp [f]
                  simp only [starRingEnd_apply, star_mul]
                  ring
                _ = _ := by rw [complex_flat C hxy]
          · intro b' _ hb'
            change ∑ y, a (e.symm (x, b)) (e.symm (y, b')) = 0
            simp [a, hollow_apply, Ne.symm hb']
          · simp
    _ = ∑ b, 2 * ∑ e : Edge F, (1 / 8 : ℂ) * f (L.edgeEquiv (b, e)) := by
      exact Finset.sum_congr rfl fun b _ =>
        sum_offDiag (fun e => (1 / 8 : ℂ) * f (L.edgeEquiv (b, e)))
    _ = (1 / 4 : ℂ) * ∑ p : B × Edge F, f (L.edgeEquiv p) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.mul_sum, ← mul_assoc]
      norm_num
    _ = _ := by rw [Fintype.sum_equiv L.edgeEquiv _ f (fun _ => rfl)]


variable [AddCommGroup V]

/-- Diagonal characters and one copy of the label-group characters for each class. -/
abbrev Index (V D G : Type*) [AddCommGroup V] [AddCommGroup G] :=
  AddChar V ℂ ⊕ (D × AddChar G ℂ)

/-- The combined diagonal and hollow family. -/
def family (C : FlatHollow F) (L : EdgeLabeling F B G) (P : ParallelClasses V D F B) :
    Index V D G → Matrix V V ℂ
  | .inl χ => charDiagonal id χ
  | .inr (d, χ) => hollow C L (P.coords d) χ

theorem family_unitary (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) (i : Index V D G) :
    family C L P i ∈ Matrix.unitaryGroup V ℂ := by
  rcases i with χ | ⟨d, χ⟩
  · exact charDiagonal_unitary id χ
  · exact hollow_unitary C L (P.coords d) χ

omit [Fintype B] [Fintype G] in
theorem family_symm (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) (i : Index V D G) : (family C L P i).IsSymm := by
  rcases i with χ | ⟨d, χ⟩
  · exact Matrix.diagonal_transpose _
  · exact hollow_symm C L (P.coords d) χ

open scoped Classical in
theorem family_hs (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) (i j : Index V D G) :
    hs (family C L P i) (family C L P j) =
      if i = j then (Fintype.card V : ℂ) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa using hs_self_of_unitary (family_unitary C L P i)
  rcases i with χ | ⟨d, χ⟩ <;> rcases j with ψ | ⟨d', ψ⟩
  · have h : χ ≠ ψ := fun he => hij (congrArg Sum.inl he)
    simpa [family, charDiagonal, hs, Matrix.diagonal_apply, h] using sum_characters χ ψ
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro w _
    by_cases h : v = w
    · subst w
      simp [family]
    · simp [family, charDiagonal, Matrix.diagonal_apply_ne _ h]
  · simp [family, charDiagonal, hs, Matrix.diagonal_apply, mul_ite]
  · change hs (hollow C L (P.coords d) χ) (hollow C L (P.coords d') ψ) = _
    rw [ite_eq_right hij]
    by_cases hd : d = d'
    · subst d'
      have h : χ ≠ ψ := fun he => hij (congrArg (fun c => Sum.inr (d, c)) he)
      simp [hollow_hs, h]
    · unfold hs
      apply Finset.sum_eq_zero
      intro v _
      apply Finset.sum_eq_zero
      intro w _
      by_cases hvw : v = w
      · subst w
        simp
      · by_cases h : (P.coords d v).2 = (P.coords d w).2
        · obtain ⟨c, _, hc⟩ := P.unique_class v w hvw
          have h' : (P.coords d' v).2 ≠ (P.coords d' w).2 :=
            fun hh => hd ((hc d h).trans (hc d' hh).symm)
          simp [hollow_zero_of_different_blocks C L _ ψ h']
        · simp [hollow_zero_of_different_blocks C L _ χ h]

variable [Fintype D]

omit [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B] [AddCommGroup V] in
theorem ParallelClasses.card_hollow (P : ParallelClasses V D F B)
    (L : EdgeLabeling F B G) :
    Fintype.card (D × AddChar G ℂ) = (Fintype.card V).choose 2 := by
  classical
  calc
    _ = Fintype.card (D × G) := by simp
    _ = Fintype.card (Edge V) := Fintype.card_congr
      (((Equiv.refl D).prodCongr L.edgeEquiv.symm).trans P.edges)
    _ = _ := Sym2.card_subtype_not_diag

omit [Fintype F] [DecidableEq F] [Fintype B] [DecidableEq B] in
theorem ParallelClasses.card_index (P : ParallelClasses V D F B)
    (L : EdgeLabeling F B G) :
    Fintype.card (Index V D G) = (Fintype.card V + 1).choose 2 := by
  rw [Fintype.card_sum, AddChar.card_eq, P.card_hollow L, Nat.choose_succ_succ',
    Nat.choose_one_right]

/-- The complex subspace of symmetric matrices. -/
def symmetric (V : Type*) : Submodule ℂ (Matrix V V ℂ) where
  carrier := {A | A.IsSymm}
  zero_mem' := by simp [Matrix.IsSymm]
  add_mem' hA hB := Matrix.IsSymm.ext fun i j => by
    simp only [Matrix.add_apply, hA.apply i j, hB.apply i j]
  smul_mem' c A hA := Matrix.IsSymm.ext fun i j => by
    simp only [Matrix.smul_apply, hA.apply i j]

private def symmetricEquiv (V : Type*) : symmetric V ≃ₗ[ℂ] (Sym2 V → ℂ) where
  toFun A := Sym2.lift ⟨A.1, fun i j => (A.2.apply i j).symm⟩
  invFun f := ⟨fun i j => f s(i, j), Matrix.IsSymm.ext fun i j => congrArg f (Sym2.eq_swap)⟩
  left_inv A := rfl
  right_inv f := by
    funext e
    induction e using Sym2.inductionOn
    rfl
  map_add' A B := by
    funext e
    induction e using Sym2.inductionOn
    rfl
  map_smul' c A := by
    funext e
    induction e using Sym2.inductionOn
    rfl

omit [DecidableEq V] [AddCommGroup V] in
theorem finrank_symmetric : Module.finrank ℂ (symmetric V) = (Fintype.card V + 1).choose 2 := by
  rw [(symmetricEquiv V).finrank_eq, Module.finrank_fintype_fun_eq_card, Sym2.card]

private theorem family_linearIndependent (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) :
    LinearIndependent ℂ (family C L P) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (hsLinear (family C L P i)) hc
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ j, c j * hs (family C L P i) (family C L P j)) = 0 at h
  simp only [family_hs, mul_ite, mul_zero] at h
  rw [Finset.sum_eq_single i] at h
  · have hi : c i * (Fintype.card V : ℂ) = 0 := by simpa using h
    exact (mul_eq_zero.mp hi).resolve_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

private def symmetricFamily (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) (i : Index V D G) : symmetric V :=
  ⟨family C L P i, family_symm C L P i⟩

/-- The assembled family is a basis of the entire complex symmetric subspace. -/
def assemble (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) : Basis (Index V D G) ℂ (symmetric V) :=
  basisOfLinearIndependentOfCardEqFinrank (b := symmetricFamily C L P)
    (LinearIndependent.of_comp (symmetric V).subtype (family_linearIndependent C L P))
    ((P.card_index L).trans finrank_symmetric.symm)

@[simp] theorem assemble_apply (C : FlatHollow F) (L : EdgeLabeling F B G)
    (P : ParallelClasses V D F B) (i : Index V D G) :
    (assemble C L P i : Matrix V V ℂ) = family C L P i := by
  rw [assemble, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

end Assembly

end
end AffineNine
