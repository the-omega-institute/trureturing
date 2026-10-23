/- GID: D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TreeResponseQuartet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: Real tree Schur responses satisfy the full block determinant quartet law. -/
module

public import Mathlib.Logic.Equiv.Option
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Instances.Matrix
public import D5.S3.Arith.AbsoluteValues.Heights.Hadamard

/-! Full block determinants and their repeated-minimum quartet relation. -/

@[expose] public section

open Matrix Unitary

namespace D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet

universe u

/-- The minimum of three real numbers occurs at least twice. -/
def RepeatedMin (x y z : ℝ) : Prop :=
  (x = y ∧ y ≤ z) ∨ (x = z ∧ z ≤ y) ∨ (y = z ∧ z ≤ x)

/-- The full fixed-fibre block, with no coordinate compression. -/
def block {V : Type u} {r : ℕ} (M : Matrix (V × Fin r) (V × Fin r) ℝ)
    (x y : V) : Matrix (Fin r) (Fin r) ℝ :=
  M.submatrix (fun i => (x, i)) (fun i => (y, i))

/-- The absolute determinant of the whole block. -/
noncomputable def weight {V : Type u} {r : ℕ}
    (M : Matrix (V × Fin r) (V × Fin r) ℝ) (x y : V) : ℝ :=
  |(block M x y).det|

/-- Only distinct nonadjacent vertices must have zero blocks. -/
def Supported {V : Type u} {r : ℕ} (G : SimpleGraph V)
    (M : Matrix (V × Fin r) (V × Fin r) ℝ) : Prop :=
  ∀ x y, x ≠ y → ¬G.Adj x y → block M x y = 0

/-- The three perfect matchings of four, possibly repeated, marked vertices. -/
def Quartet {V : Type u} (d : V → V → ℝ) (a b c e : V) : Prop :=
  RepeatedMin (d a b * d c e) (d a c * d b e) (d a e * d b c)

private theorem repeated_min_scale {x y z t : ℝ} (ht : 0 ≤ t)
    (h : RepeatedMin x y z) : RepeatedMin (t * x) (t * y) (t * z) := by
  rcases h with h | h | h
  · exact Or.inl ⟨congrArg (t * ·) h.1, mul_le_mul_of_nonneg_left h.2 ht⟩
  · exact Or.inr (Or.inl ⟨congrArg (t * ·) h.1, mul_le_mul_of_nonneg_left h.2 ht⟩)
  · exact Or.inr (Or.inr ⟨congrArg (t * ·) h.1, mul_le_mul_of_nonneg_left h.2 ht⟩)

private theorem repeated_min_dup {x y : ℝ} (h : RepeatedMin x y y) : y ≤ x := by
  rcases h with h | h | h <;> rcases h with ⟨h, h'⟩ <;> linarith

private theorem quartet_leaf_lift {U : Type u} (d : U → U → ℝ)
    (hpos : ∀ x y, 0 ≤ d x y) (hsym : ∀ x y, d x y = d y x)
    (hq : ∀ a b c e, Quartet d a b c e) (u : U) (t s : ℝ)
    (ht : 0 ≤ t) (hs : t ^ 2 * d u u ≤ s) :
    let D : Option U → Option U → ℝ := fun x y =>
      match x, y with
      | none, none => s
      | none, some y => t * d u y
      | some x, none => t * d u x
      | some x, some y => d x y
    ∀ a b c e, Quartet D a b c e := by
  dsimp only
  have htwo (x y : U) : (t * d u x) * (t * d u y) ≤ s * d x y := by
    have hh : d u x * d u y ≤ d u u * d x y := by
      exact repeated_min_dup (by simpa [Quartet, mul_comm] using hq u u x y)
    calc
      (t * d u x) * (t * d u y) = t ^ 2 * (d u x * d u y) := by ring
      _ ≤ t ^ 2 * (d u u * d x y) := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
      _ = (t ^ 2 * d u u) * d x y := by ring
      _ ≤ s * d x y := mul_le_mul_of_nonneg_right hs (hpos x y)
  intro a b c e
  cases a with
  | none =>
    cases b with
    | none =>
      cases c with
      | none => cases e <;> simp [Quartet, RepeatedMin, mul_comm]
      | some c =>
        cases e with
        | none => simp [Quartet, RepeatedMin, mul_comm]
        | some e => exact Or.inr (Or.inr ⟨by dsimp <;> ring, by simpa [mul_comm] using htwo c e⟩)
    | some b =>
      cases c with
      | none =>
        cases e with
        | none => simp [Quartet, RepeatedMin, mul_comm]
        | some e => exact Or.inr (Or.inl ⟨by dsimp <;> ring, by simpa [mul_comm] using htwo b e⟩)
      | some c =>
        cases e with
        | none =>
          exact Or.inl ⟨by dsimp <;> ring, by simpa [mul_comm, hsym c b] using htwo b c⟩
        | some e =>
          simpa only [Quartet, mul_assoc] using repeated_min_scale ht (hq u b c e)
  | some a =>
    cases b with
    | none =>
      cases c with
      | none =>
        cases e with
        | none => simp [Quartet, RepeatedMin, mul_comm]
        | some e => exact Or.inl ⟨by dsimp <;> ring, by simpa [mul_comm] using htwo a e⟩
      | some c =>
        cases e with
        | none => exact Or.inr (Or.inl ⟨rfl, by simpa [mul_comm, hsym c a] using htwo a c⟩)
        | some e =>
          simpa only [Quartet, hsym a u, mul_assoc, mul_left_comm] using
            repeated_min_scale ht (hq a u c e)
    | some b =>
      cases c with
      | none =>
        cases e with
        | none => exact Or.inr (Or.inr ⟨by dsimp <;> ring, by simpa [mul_comm] using htwo a b⟩)
        | some e =>
          simpa only [Quartet, hsym a u, hsym b u, mul_assoc, mul_left_comm] using
            repeated_min_scale ht (hq a b u e)
      | some c =>
        cases e with
        | none =>
          simpa only [Quartet, hsym a u, hsym b u, hsym c u, mul_assoc, mul_left_comm] using
            repeated_min_scale ht (hq a b c u)
        | some e => exact hq a b c e

private theorem schur_posDef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {D : Matrix n n ℝ} (h : (fromBlocks A B Bᴴ D).PosDef) :
    (D - Bᴴ * A⁻¹ * B).PosDef := by
  have hA : A.PosDef := by exact h.submatrix (e := Sum.inl) Sum.inl_injective
  letI := hA.isUnit.invertible
  letI := h.isUnit.invertible
  have hS := (Matrix.PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  letI := Matrix.invertibleOfFromBlocks₁₁Invertible A B Bᴴ D
  apply hS.posDef_iff_isUnit.mpr
  simpa only [invOf_eq_nonsing_inv] using (isUnit_of_invertible (D - Bᴴ * ⅟A * B))

private theorem det_add_psd {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : A.det ≤ (A + B).det := by
  open scoped MatrixOrder in
  have hs (X : Matrix (Fin r) (Fin r) ℝ) (hX : X.PosSemidef) :
      CFC.sqrt X * (CFC.sqrt X)ᵀ = X := by
    have hsym : (CFC.sqrt X)ᵀ = CFC.sqrt X := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
    rw [hsym, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  simpa only [hs A hA, hs B hB] using
    Matrix.det_mul_transpose_self_le_det_add (CFC.sqrt A) (CFC.sqrt B)

private def leafEquiv {V : Type u} [DecidableEq V] (v : V) (r : ℕ) :
    Fin r ⊕ ({x : V // x ≠ v} × Fin r) ≃ V × Fin r where
  toFun := Sum.elim (fun i => (v, i)) (fun p => (p.1.val, p.2))
  invFun := fun p => if h : p.1 = v then Sum.inl p.2 else Sum.inr (⟨p.1, h⟩, p.2)
  left_inv := by
    intro p
    cases p with
    | inl i => simp
    | inr p => simp [p.1.property]
  right_inv := by
    rintro ⟨x, i⟩
    by_cases h : x = v <;> simp_all

private def coupling {V : Type u} {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (v : V) :
    Matrix (Fin r) ({x : V // x ≠ v} × Fin r) ℝ :=
  Q.submatrix (fun i => (v, i)) (fun p => (p.1.val, p.2))

private def remainder {V : Type u} {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (v : V) :
    Matrix ({x : V // x ≠ v} × Fin r) ({x : V // x ≠ v} × Fin r) ℝ :=
  Q.submatrix (fun p => (p.1.val, p.2)) (fun p => (p.1.val, p.2))

private noncomputable def peel {V : Type u} {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (v : V) :=
  remainder Q v - (coupling Q v)ᴴ * (block Q v v)⁻¹ * coupling Q v

private theorem leaf_reindex {V : Type u} {r : ℕ} [DecidableEq V]
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian) (v : V) :
    Q.submatrix (leafEquiv v r) (leafEquiv v r) =
      fromBlocks (block Q v v) (coupling Q v) (coupling Q v)ᴴ (remainder Q v) := by
  ext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => simpa [leafEquiv, coupling] using (hQ.apply (i.1.val, i.2) (v, j)).symm
    | inr j => rfl

private theorem peel_posDef {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {Q : Matrix (V × Fin r) (V × Fin r) ℝ} (hQ : Q.PosDef) (v : V) :
    (peel Q v).PosDef := by
  apply schur_posDef
  rw [← leaf_reindex Q hQ.isHermitian v]
  exact hQ.submatrix (leafEquiv v r).injective

private theorem peel_inverse {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {Q : Matrix (V × Fin r) (V × Fin r) ℝ} (hQ : Q.PosDef) (v : V) :
    Q⁻¹.submatrix (leafEquiv v r) (leafEquiv v r) =
      fromBlocks
        ((block Q v v)⁻¹ + (block Q v v)⁻¹ * coupling Q v * (peel Q v)⁻¹ *
          (coupling Q v)ᴴ * (block Q v v)⁻¹)
        (-((block Q v v)⁻¹ * coupling Q v * (peel Q v)⁻¹))
        (-((peel Q v)⁻¹ * (coupling Q v)ᴴ * (block Q v v)⁻¹))
        (peel Q v)⁻¹ := by
  have hA : (block Q v v).PosDef := hQ.submatrix (fun _ _ h => congrArg Prod.snd h)
  letI := hA.isUnit.invertible
  letI : Invertible (remainder Q v - (coupling Q v)ᴴ * ⅟(block Q v v) * coupling Q v) := by
    rw [invOf_eq_nonsing_inv]
    exact (peel_posDef hQ v).isUnit.invertible
  letI := (hQ.submatrix (leafEquiv v r).injective).isUnit.invertible
  rw [← inv_submatrix_equiv, leaf_reindex Q hQ.isHermitian v]
  letI := (by
    rw [← leaf_reindex Q hQ.isHermitian v]
    exact (hQ.submatrix (leafEquiv v r).injective).isUnit.invertible :
      Invertible (fromBlocks (block Q v v) (coupling Q v)
        (coupling Q v)ᴴ (remainder Q v)))
  simpa only [invOf_eq_nonsing_inv, peel] using
    (Matrix.invOf_fromBlocks₁₁_eq (block Q v v) (coupling Q v)
      (coupling Q v)ᴴ (remainder Q v))

private theorem peel_blocks {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {Q : Matrix (V × Fin r) (V × Fin r) ℝ} (hQ : Q.PosDef) (v : V)
    (x y : {x : V // x ≠ v}) : block Q⁻¹ x.val y.val = block (peel Q v)⁻¹ x y := by
  have h := congrArg (fun M => M.submatrix (fun i => Sum.inr (x, i))
      (fun j => Sum.inr (y, j))) (peel_inverse hQ v)
  exact h

private theorem coupling_zero {V : Type u} {r : ℕ} {G : SimpleGraph V}
    {Q : Matrix (V × Fin r) (V × Fin r) ℝ} (hs : Supported G Q)
    {v u : V} (hu : ∀ w, G.Adj v w → w = u) (x : {x : V // x ≠ v})
    (hx : x.val ≠ u) : (coupling Q v).submatrix id (fun i => (x, i)) = 0 := by
  exact hs v x.val x.property.symm (fun h => hx (hu _ h))

private theorem peel_supported {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Matrix (V × Fin r) (V × Fin r) ℝ}
    (hs : Supported G Q) {v u : V} (hu : ∀ w, G.Adj v w → w = u) :
    Supported (G.induce {x | x ≠ v}) (peel Q v) := by
  intro x y hxy hn
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hz := hs x.val y.val hxy' hn
  have hxory : x.val ≠ u ∨ y.val ≠ u := by
    by_cases hx : x.val = u
    · exact Or.inr (fun hy => hxy' (hx.trans hy.symm))
    · exact Or.inl hx
  unfold block peel
  change block Q x.val y.val -
    ((coupling Q v)ᴴ * (block Q v v)⁻¹ * coupling Q v).submatrix
      (fun i => (x, i)) (fun i => (y, i)) = 0
  rw [submatrix_mul _ _ _ id _ Function.bijective_id,
    submatrix_mul _ _ _ id _ Function.bijective_id]
  rw [hz]
  rcases hxory with hx | hy
  · have hh := congrArg Matrix.conjTranspose (coupling_zero hs hu x hx)
    simp only [conjTranspose_submatrix, conjTranspose_zero] at hh
    rw [hh, zero_mul, zero_mul, sub_zero]
  · rw [coupling_zero hs hu y hy, mul_zero, sub_zero]

private theorem spike_mul {U : Type u} {r : ℕ} [Fintype U] [DecidableEq U]
    (B : Matrix (Fin r) (U × Fin r) ℝ) (u : U)
    (hz : ∀ x, x ≠ u → B.submatrix id (fun i => (x, i)) = 0)
    {n : Type*} [Fintype n] (R : Matrix (U × Fin r) n ℝ) :
    B * R = B.submatrix id (fun i => (u, i)) * R.submatrix (fun i => (u, i)) id := by
  ext i j
  simp only [mul_apply, Fintype.sum_prod_type, submatrix_apply, id_eq]
  apply Finset.sum_eq_single u
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro k _
    have h := congrFun (congrFun (hz x hx) i) k
    simp only [submatrix_apply, id_eq, Matrix.zero_apply] at h
    rw [h, zero_mul]
  · simp

private theorem leaf_cross {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Matrix (V × Fin r) (V × Fin r) ℝ}
    (hQ : Q.PosDef) (hs : Supported G Q) {v u : V}
    (huv : u ≠ v) (hu : ∀ w, G.Adj v w → w = u) (x : {x : V // x ≠ v}) :
    block Q⁻¹ v x.val = (-(block Q v v)⁻¹ * block Q v u) *
      block (peel Q v)⁻¹ ⟨u, huv⟩ x := by
  have hz (y : {x : V // x ≠ v}) (hy : y ≠ ⟨u, huv⟩) :=
    coupling_zero hs hu y (fun h => hy (Subtype.ext h))
  have hinv := congrArg (fun M => M.submatrix Sum.inl (fun i => Sum.inr (x, i)))
    (peel_inverse hQ v)
  change block Q⁻¹ v x.val =
    (-((block Q v v)⁻¹ * coupling Q v * (peel Q v)⁻¹)).submatrix id (fun i => (x, i)) at hinv
  rw [hinv]
  simp only [Matrix.mul_assoc]
  rw [spike_mul (coupling Q v) ⟨u, huv⟩ hz]
  simp only [Matrix.neg_mul]
  rfl

private theorem weight_symm {V : Type u} {r : ℕ}
    {Q : Matrix (V × Fin r) (V × Fin r) ℝ} (hQ : Q.IsHermitian) (x y : V) :
    weight Q x y = weight Q y x := by
  have hb : block Q x y = (block Q y x)ᵀ := by
    ext i j
    exact hQ.isSymm.apply _ _
  simp only [weight, hb, det_transpose]

private theorem spike_sandwich {U : Type u} {r : ℕ} [Fintype U] [DecidableEq U]
    (B : Matrix (Fin r) (U × Fin r) ℝ) (u : U)
    (hz : ∀ x, x ≠ u → B.submatrix id (fun i => (x, i)) = 0)
    (R : Matrix (U × Fin r) (U × Fin r) ℝ) :
    B * R * Bᴴ = B.submatrix id (fun i => (u, i)) * block R u u *
      (B.submatrix id (fun i => (u, i)))ᴴ := by
  have hr := congrArg Matrix.transpose (spike_mul B u hz Rᵀ)
  simp only [transpose_mul, transpose_transpose, transpose_submatrix] at hr
  simp only [conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.mul_assoc, hr, ← Matrix.mul_assoc, spike_mul B u hz]
  rfl

private theorem leaf_variance {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Matrix (V × Fin r) (V × Fin r) ℝ}
    (hQ : Q.PosDef) (hs : Supported G Q) {v u : V}
    (huv : u ≠ v) (hu : ∀ w, G.Adj v w → w = u) :
    block Q⁻¹ v v = (block Q v v)⁻¹ +
      (-(block Q v v)⁻¹ * block Q v u) * block (peel Q v)⁻¹ ⟨u, huv⟩ ⟨u, huv⟩ *
      (-(block Q v v)⁻¹ * block Q v u)ᴴ := by
  have hz (y : {x : V // x ≠ v}) (hy : y ≠ ⟨u, huv⟩) :=
    coupling_zero hs hu y (fun h => hy (Subtype.ext h))
  have hinv := congrArg (fun M => M.submatrix Sum.inl Sum.inl) (peel_inverse hQ v)
  change block Q⁻¹ v v = (block Q v v)⁻¹ +
    (block Q v v)⁻¹ * coupling Q v * (peel Q v)⁻¹ *
      (coupling Q v)ᴴ * (block Q v v)⁻¹ at hinv
  have hA : (block Q v v).PosDef := hQ.submatrix (fun _ _ h => congrArg Prod.snd h)
  have hAinv := hA.inv.isHermitian.eq
  rw [hinv]
  simp only [conjTranspose_mul, conjTranspose_neg, hAinv, neg_mul, mul_neg, neg_neg]
  congr 1
  calc
    _ = (block Q v v)⁻¹ *
        (coupling Q v * (peel Q v)⁻¹ * (coupling Q v)ᴴ) * (block Q v v)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [spike_sandwich (coupling Q v) ⟨u, huv⟩ hz]
      change (block Q v v)⁻¹ * (block Q v u * _ * (block Q v u)ᴴ) * _ = _
      simp only [Matrix.mul_assoc]

private theorem leaf_diagonal_bound {V : Type u} {r : ℕ} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Matrix (V × Fin r) (V × Fin r) ℝ}
    (hQ : Q.PosDef) (hs : Supported G Q) {v u : V}
    (huv : u ≠ v) (hu : ∀ w, G.Adj v w → w = u) :
    |(-(block Q v v)⁻¹ * block Q v u).det| ^ 2 *
      weight (peel Q v)⁻¹ ⟨u, huv⟩ ⟨u, huv⟩ ≤ weight Q⁻¹ v v := by
  let F := -(block Q v v)⁻¹ * block Q v u
  let C := block (peel Q v)⁻¹ ⟨u, huv⟩ ⟨u, huv⟩
  have hA : (block Q v v).PosDef := hQ.submatrix (fun _ _ h => congrArg Prod.snd h)
  have hC : C.PosDef := (peel_posDef hQ v).inv.submatrix
    (fun _ _ h => congrArg Prod.snd h)
  have hFC : (F * C * Fᴴ).PosSemidef := hC.posSemidef.mul_mul_conjTranspose_same F
  have hh := det_add_psd (F * C * Fᴴ) (block Q v v)⁻¹ hFC hA.inv.posSemidef
  have hv : block Q⁻¹ v v = F * C * Fᴴ + (block Q v v)⁻¹ := by
    rw [leaf_variance hQ hs huv hu, add_comm]
  have hdiag : (block Q⁻¹ v v).PosDef := hQ.inv.submatrix
    (fun _ _ h => congrArg Prod.snd h)
  rw [← hv, det_mul, det_mul, det_conjTranspose] at hh
  change |F.det| ^ 2 * |C.det| ≤ |(block Q⁻¹ v v).det|
  rw [abs_of_pos hC.det_pos, abs_of_pos hdiag.det_pos, sq_abs]
  simpa only [star_trivial, pow_two, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Every finite positive definite tree matrix has the full-determinant inverse quartet law.
The four vertices may coincide, and all edge blocks may be singular or zero. -/
theorem inverse_tree_quartet {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (G : SimpleGraph V) (Q : Matrix (V × Fin r) (V × Fin r) ℝ)
    (hG : G.IsTree) (hQ : Q.PosDef) (hs : Supported G Q) (a b c e : V) :
    Quartet (weight Q⁻¹) a b c e := by
  classical
  suffices main : ∀ n (W : Type u) [Fintype W] [DecidableEq W], Fintype.card W = n →
      ∀ (T : SimpleGraph W) (M : Matrix (W × Fin r) (W × Fin r) ℝ),
        T.IsTree → M.PosDef → Supported T M →
          ∀ a b c e, Quartet (weight M⁻¹) a b c e by
    exact main (Fintype.card V) V rfl G Q hG hQ hs a b c e
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W instW instDW hn T M hT hM hsup a b c e
    by_cases hW : Nontrivial W
    · letI := hW
      obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hvu, hu⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hv
      let U := {x : W // x ≠ v}
      let u' : U := ⟨u, hvu.ne'⟩
      have hsmall : Fintype.card U < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := v) (by simp)
      have htree : (T.induce {x | x ≠ v}).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv, hT.isAcyclic.induce _⟩
      have hrest := ih (Fintype.card U) hsmall U rfl (T.induce {x | x ≠ v})
        (peel M v) htree (peel_posDef hM v) (peel_supported hsup hu)
      let t : ℝ := |(-(block M v v)⁻¹ * block M v u).det|
      let s : ℝ := weight M⁻¹ v v
      let D : Option U → Option U → ℝ := fun x y => match x, y with
        | none, none => s
        | none, some y => t * weight (peel M v)⁻¹ u' y
        | some x, none => t * weight (peel M v)⁻¹ u' x
        | some x, some y => weight (peel M v)⁻¹ x y
      have hD : ∀ a b c e, Quartet D a b c e :=
        quartet_leaf_lift (weight (peel M v)⁻¹) (fun _ _ => abs_nonneg _)
          (weight_symm (peel_posDef hM v).inv.isHermitian) hrest u' t s
          (abs_nonneg _) (leaf_diagonal_bound hM hsup hvu.ne' hu)
      let E := Equiv.optionSubtypeNe v
      have hd (x y : Option U) : weight M⁻¹ (E x) (E y) = D x y := by
        cases x with
        | none =>
          cases y with
          | none => rfl
          | some y =>
            change |(block M⁻¹ v y.val).det| = _
            rw [leaf_cross hM hsup hvu.ne' hu y, det_mul, abs_mul]
            rfl
        | some x =>
          cases y with
          | none =>
            rw [weight_symm hM.inv.isHermitian]
            change |(block M⁻¹ v x.val).det| = _
            rw [leaf_cross hM hsup hvu.ne' hu x, det_mul, abs_mul]
            rfl
          | some y =>
            change |(block M⁻¹ x.val y.val).det| = _
            rw [peel_blocks hM v x y]
            rfl
      have hh := hD (E.symm a) (E.symm b) (E.symm c) (E.symm e)
      simpa only [Quartet, ← hd, Equiv.apply_symm_apply] using hh
    · haveI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
      have hb : b = a := Subsingleton.elim _ _
      have hc : c = a := Subsingleton.elim _ _
      have he : e = a := Subsingleton.elim _ _
      subst b; subst c; subst e
      exact Or.inl ⟨rfl, le_refl _⟩

/-- A rectangular restriction keeps every coordinate and every original diagonal entry. -/
def cut {V : Type u} {r : ℕ} (Q : Matrix (V × Fin r) (V × Fin r) ℝ)
    (B C : Set V) : Matrix (B × Fin r) (C × Fin r) ℝ :=
  Q.submatrix (fun p => (p.1.val, p.2)) (fun p => (p.1.val, p.2))

/-- Eliminate exactly the complement of the retained set. -/
noncomputable def response {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (B : Set V) [DecidablePred (· ∈ B)] :
    Matrix (B × Fin r) (B × Fin r) ℝ :=
  cut Q B B - cut Q B Bᶜ * (cut Q Bᶜ Bᶜ)⁻¹ * cut Q Bᶜ B

private def partitionEquiv {V : Type u} {r : ℕ} (B : Set V) [DecidablePred (· ∈ B)] :
    (↥B × Fin r) ⊕ (↥(Bᶜ) × Fin r) ≃ V × Fin r where
  toFun := Sum.elim (fun p => (p.1.val, p.2)) (fun p => (p.1.val, p.2))
  invFun := fun p => if h : p.1 ∈ B then Sum.inl (⟨p.1, h⟩, p.2)
    else Sum.inr (⟨p.1, h⟩, p.2)
  left_inv := by
    intro p
    cases p with
    | inl p => simp [p.1.property]
    | inr p =>
      have hp : p.1.val ∉ B := p.1.property
      simp [hp]
  right_inv := by rintro ⟨x, i⟩; by_cases h : x ∈ B <;> simp [h]

private theorem cut_adjoint {V : Type u} {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian) (B C : Set V) :
    cut Q C B = (cut Q B C)ᴴ := by
  ext i j
  exact (hQ.apply _ _).symm

private noncomputable def regularized {V : Type u} {r : ℕ} [DecidableEq V]
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (B : Set V) [DecidablePred (· ∈ B)] (m : ℝ) :=
  Q + diagonal (fun p => if p.1 ∈ B then m else 0)

private theorem regularized_reindex {V : Type u} {r : ℕ} [DecidableEq V]
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian)
    (B : Set V) [DecidablePred (· ∈ B)] (m : ℝ) :
    (regularized Q B m).submatrix (partitionEquiv B) (partitionEquiv B) =
      fromBlocks (cut Q B B + m • 1) (cut Q B Bᶜ)
        (cut Q B Bᶜ)ᴴ (cut Q Bᶜ Bᶜ) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [regularized, partitionEquiv, cut, diagonal_apply, one_apply,
        i.1.property, Prod.ext_iff, Subtype.val_inj]
    | inr j =>
      have hn : (i.1.val, i.2) ≠ (j.1.val, j.2) := by
        intro h
        have he : i.1.val = j.1.val := congrArg Prod.fst h
        exact j.1.property (he ▸ i.1.property)
      simp [regularized, partitionEquiv, cut, diagonal_apply, hn]
  | inr i =>
    cases j with
    | inl j =>
      have hh := hQ.apply (i.1.val, i.2) (j.1.val, j.2)
      have hp : i.1.val ∉ B := i.1.property
      simpa [regularized, partitionEquiv, cut, diagonal_apply, hp] using hh.symm
    | inr j =>
      have hp : i.1.val ∉ B := i.1.property
      simp [regularized, partitionEquiv, cut, diagonal_apply, hp]

private theorem shift_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (hS : S.IsHermitian) :
    ∃ c : ℝ, 0 < c ∧ ∀ m, c < m → (S + m • 1).PosDef := by
  let l := hS.eigenvalues
  let U := hS.eigenvectorUnitary
  refine ⟨(∑ i, |l i|) + 1, by positivity, ?_⟩
  intro m hm
  have hd : (diagonal (fun i => l i + m)).PosDef := by
    apply posDef_diagonal_iff.mpr
    intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (l j))
      (Finset.mem_univ i)
    linarith [neg_abs_le (l i)]
  have hdiag : diagonal (fun i => l i + m) = diagonal l + m • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [diagonal_apply, one_apply, hij]
  have he : S + m • 1 = conjStarAlgAut ℝ _ U (diagonal (fun i => l i + m)) := by
    rw [hdiag, map_add, map_smul, map_one]
    congr 1
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hS.spectral_theorem
  rw [he, conjStarAlgAut_apply]
  exact (Unitary.isUnit_coe (U := U)).posDef_star_right_conjugate_iff.mpr hd

private theorem fromBlocks_posDef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (K : Matrix n n ℝ) (hK : K.PosDef) (hS : (A - B * K⁻¹ * Bᴴ).PosDef) :
    (fromBlocks A B Bᴴ K).PosDef := by
  letI := hK.isUnit.invertible
  letI : Invertible (A - B * ⅟K * Bᴴ) := by
    rw [invOf_eq_nonsing_inv]
    exact hS.isUnit.invertible
  letI := Matrix.fromBlocks₂₂Invertible A B Bᴴ K
  have hh := (Matrix.PosDef.fromBlocks₂₂ A B hK).mpr hS.posSemidef
  exact hh.posDef_iff_isUnit.mpr (isUnit_of_invertible _)

private theorem response_hermitian {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian)
    (B : Set V) [DecidablePred (· ∈ B)] : (response Q B).IsHermitian := by
  unfold response
  rw [cut_adjoint Q hQ B Bᶜ]
  exact (hQ.submatrix _).sub (isHermitian_mul_mul_conjTranspose _ (hQ.submatrix _).inv)

private theorem regularized_posDef {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian)
    (B : Set V) [DecidablePred (· ∈ B)] (hK : (cut Q Bᶜ Bᶜ).PosDef)
    (m : ℝ) (hS : (response Q B + m • 1).PosDef) :
    (regularized Q B m).PosDef := by
  have hh : (cut Q B B + m • 1 - cut Q B Bᶜ * (cut Q Bᶜ Bᶜ)⁻¹ *
      (cut Q B Bᶜ)ᴴ).PosDef := by
    convert hS using 1
    unfold response
    rw [cut_adjoint Q hQ B Bᶜ]
    abel
  have hp := fromBlocks_posDef _ _ _ hK hh
  rw [← regularized_reindex Q hQ B m] at hp
  convert hp.submatrix (partitionEquiv B).symm.injective using 1
  ext i j
  simp only [submatrix_apply, Equiv.apply_symm_apply]

private theorem regularized_inverse {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian)
    (B : Set V) [DecidablePred (· ∈ B)] (hK : (cut Q Bᶜ Bᶜ).PosDef)
    (m : ℝ) (hS : (response Q B + m • 1).PosDef) :
    cut (regularized Q B m)⁻¹ B B = (response Q B + m • 1)⁻¹ := by
  have he : cut Q B B + m • 1 - cut Q B Bᶜ * (cut Q Bᶜ Bᶜ)⁻¹ *
      (cut Q B Bᶜ)ᴴ = response Q B + m • 1 := by
    unfold response
    rw [cut_adjoint Q hQ B Bᶜ]
    abel
  letI := hK.isUnit.invertible
  letI : Invertible (cut Q B B + m • 1 - cut Q B Bᶜ * ⅟(cut Q Bᶜ Bᶜ) *
      (cut Q B Bᶜ)ᴴ) := by
    rw [invOf_eq_nonsing_inv, he]
    exact hS.isUnit.invertible
  letI := Matrix.fromBlocks₂₂Invertible (cut Q B B + m • 1) (cut Q B Bᶜ)
    (cut Q B Bᶜ)ᴴ (cut Q Bᶜ Bᶜ)
  have hi := Matrix.invOf_fromBlocks₂₂_eq (cut Q B B + m • 1) (cut Q B Bᶜ)
    (cut Q B Bᶜ)ᴴ (cut Q Bᶜ Bᶜ)
  simp only [invOf_eq_nonsing_inv] at hi
  rw [← regularized_reindex Q hQ B m, inv_submatrix_equiv] at hi
  have hb := congrArg (fun M => M.submatrix Sum.inl Sum.inl) hi
  change cut (regularized Q B m)⁻¹ B B =
    (cut Q B B + m • 1 - cut Q B Bᶜ * (cut Q Bᶜ Bᶜ)⁻¹ * (cut Q B Bᶜ)ᴴ)⁻¹ at hb
  rwa [he] at hb

private theorem regularized_supported {V : Type u} {r : ℕ} [DecidableEq V]
    (G : SimpleGraph V) (Q : Matrix (V × Fin r) (V × Fin r) ℝ)
    (hs : Supported G Q) (B : Set V) [DecidablePred (· ∈ B)] (m : ℝ) :
    Supported G (regularized Q B m) := by
  intro x y hxy hn
  have hz := hs x y hxy hn
  ext i j
  have h : (x, i) ≠ (y, j) := fun h => hxy (congrArg Prod.fst h)
  have h' := congrFun (congrFun hz i) j
  simpa [block, regularized, diagonal_apply, h] using h'

private noncomputable def smooth {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (t : ℝ) := S * (1 + t • S)⁻¹

private theorem resolvent_eq {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (m : ℝ) (hm : m ≠ 0) (hS : (S + m • 1).PosDef) :
    smooth S m⁻¹ = m • 1 - m ^ 2 • (S + m • 1)⁻¹ := by
  have he : 1 + m⁻¹ • S = m⁻¹ • (S + m • 1) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hm, one_smul]
    abel
  letI : Invertible (m⁻¹) := invertibleOfNonzero (inv_ne_zero hm)
  unfold smooth
  rw [he, Matrix.inv_smul (S + m • 1) m⁻¹ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  simp only [invOf_eq_inv, inv_inv, Matrix.mul_smul]
  have hi := Matrix.mul_nonsing_inv (A := S + m • 1)
    ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)
  rw [add_mul, Matrix.smul_mul, one_mul] at hi
  calc
    m • (S * (S + m • 1)⁻¹) = m • (1 - m • (S + m • 1)⁻¹) := by
      congr 1
      exact eq_sub_of_add_eq hi
    _ = _ := by rw [smul_sub, smul_smul, pow_two]

private theorem smooth_continuousAt_zero {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) : ContinuousAt (smooth S) 0 := by
  have hc : ContinuousAt (fun t : ℝ => (1 : Matrix n n ℝ) + t • S) 0 := by fun_prop
  have hi : ContinuousAt (Inv.inv : Matrix n n ℝ → Matrix n n ℝ) 1 := by
    apply continuousAt_matrix_inv
    simp only [det_one]
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ (one_ne_zero : (1 : ℝ) ≠ 0))
  exact continuousAt_const.mul (hi.comp_of_eq hc (by simp))

private theorem repeated_min_limit {f g h : ℝ → ℝ} {x y z : ℝ}
    (hf : Filter.Tendsto f Filter.atTop (nhds x))
    (hg : Filter.Tendsto g Filter.atTop (nhds y))
    (hh : Filter.Tendsto h Filter.atTop (nhds z))
    (hp : ∀ᶠ m in Filter.atTop, RepeatedMin (f m) (g m) (h m)) : RepeatedMin x y z := by
  have hc : IsClosed {p : ℝ × ℝ × ℝ | RepeatedMin p.1 p.2.1 p.2.2} := by
    have c₁ : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := continuous_fst
    have c₂ : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := continuous_fst.comp continuous_snd
    have c₃ : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) := continuous_snd.comp continuous_snd
    exact ((isClosed_eq c₁ c₂).inter (isClosed_le c₂ c₃)).union
      (((isClosed_eq c₁ c₃).inter (isClosed_le c₃ c₂)).union
        ((isClosed_eq c₂ c₃).inter (isClosed_le c₃ c₁)))
  exact hc.mem_of_tendsto (hf.prodMk_nhds (hg.prodMk_nhds hh)) hp

private theorem smooth_block {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (Q : Matrix (V × Fin r) (V × Fin r) ℝ) (hQ : Q.IsHermitian)
    (B : Set V) [DecidablePred (· ∈ B)] (hK : (cut Q Bᶜ Bᶜ).PosDef)
    (m : ℝ) (hm : m ≠ 0) (hS : (response Q B + m • 1).PosDef)
    (x y : B) (hxy : x ≠ y) :
    block (smooth (response Q B) m⁻¹) x y =
      (-m ^ 2) • block (regularized Q B m)⁻¹ x.val y.val := by
  rw [resolvent_eq _ m hm hS]
  have hi := regularized_inverse Q hQ B hK m hS
  rw [← hi]
  ext i j
  have h : (x, i) ≠ (y, j) := fun h => hxy (congrArg Prod.fst h)
  simp [block, cut, h, one_apply]

/-- The determinant quartet for the actual Schur response. The complement of `B` is the only
eliminated set; all other retained coordinates are grounded when the four blocks are read.
There is no positivity assumption on the full matrix or on its response. -/
theorem complete263_2 {V : Type u} [Fintype V] [DecidableEq V] {r : ℕ}
    (T : SimpleGraph V) (H : Matrix (V × Fin r) (V × Fin r) ℝ)
    (hT : T.IsTree) (hH : H.IsSymm) (hs : Supported T H) (z : ℝ)
    (B : Set V) [DecidablePred (· ∈ B)]
    (hK : (cut (H - z • 1) Bᶜ Bᶜ).PosDef) (P : Fin 4 ↪ B) :
    Quartet (weight (response (H - z • 1) B)) (P 0) (P 1) (P 2) (P 3) := by
  classical
  let Q := H - z • 1
  have hQ : Q.IsHermitian := (isHermitian_iff_isSymm.mpr hH).sub
    (isHermitian_one.smul (IsSelfAdjoint.all z))
  have hsup : Supported T Q := by
    intro x y hxy hn
    have hz := hs x y hxy hn
    ext i j
    have h : (x, i) ≠ (y, j) := fun h => hxy (congrArg Prod.fst h)
    simpa [Q, block, one_apply, h] using congrFun (congrFun hz i) j
  let S := response Q B
  obtain ⟨c, hc, hshift⟩ := shift_posDef S (response_hermitian Q hQ B)
  have hweight (x y : B) :
      Filter.Tendsto (fun m : ℝ => weight (smooth S m⁻¹) x y)
        Filter.atTop (nhds (weight S x y)) := by
    have hb : Continuous (fun M : Matrix (B × Fin r) (B × Fin r) ℝ => block M x y) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_apply (y, j)).comp (continuous_apply (x, i))
    have hw := (hb.matrix_det.abs).continuousAt.comp (smooth_continuousAt_zero S)
    have hh := hw.tendsto.comp (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun m : ℝ => m⁻¹) Filter.atTop (nhds 0))
    simpa only [Function.comp_def, weight, smooth, zero_smul, add_zero, inv_one, mul_one] using hh
  have hquart : ∀ᶠ m : ℝ in Filter.atTop,
      Quartet (weight (smooth S m⁻¹)) (P 0) (P 1) (P 2) (P 3) := by
    filter_upwards [Filter.eventually_gt_atTop c] with m hm
    have hmpos : 0 < m := hc.trans hm
    have hSm := hshift m hm
    have hM := regularized_posDef Q hQ B hK m hSm
    have hq := inverse_tree_quartet T (regularized Q B m) hT hM
      (regularized_supported T Q hsup B m) (P 0).val (P 1).val (P 2).val (P 3).val
    let f : ℝ := |(-m ^ 2) ^ r|
    have hd (i j : Fin 4) (hij : i ≠ j) :
        weight (smooth S m⁻¹) (P i) (P j) =
          f * weight (regularized Q B m)⁻¹ (P i).val (P j).val := by
      unfold weight
      rw [smooth_block Q hQ B hK m hmpos.ne' hSm (P i) (P j) (P.injective.ne hij),
        det_smul, Fintype.card_fin, abs_mul]
    have hh := repeated_min_scale (sq_nonneg f) hq
    unfold Quartet
    rw [hd 0 1 (by decide), hd 2 3 (by decide), hd 0 2 (by decide),
      hd 1 3 (by decide), hd 0 3 (by decide), hd 1 2 (by decide)]
    convert hh using 1 <;> ring
  exact repeated_min_limit
    ((hweight (P 0) (P 1)).mul (hweight (P 2) (P 3)))
    ((hweight (P 0) (P 2)).mul (hweight (P 1) (P 3)))
    ((hweight (P 0) (P 3)).mul (hweight (P 1) (P 2))) hquart

end D5.S3.Combinatorics.SpectralGraph.TreeResponseQuartet
