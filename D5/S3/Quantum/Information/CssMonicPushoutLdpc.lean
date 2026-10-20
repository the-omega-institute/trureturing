/- GID: D5/S3/Quantum/Information/CssMonicPushoutLdpc
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CssMonicPushoutLdpc
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Basis-preserving monic CSS pushouts have explicit LDPC row and column bounds. -/

/-
proof_shape: result: content
proof_shape: quotient_out_injective: bind-only; consumers: pushoutD2_row_bound, pushoutD1_row_bound
escape_witness: result: quotient_block_row_bound (row-support injection on the live proof path)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19605
admission_basis: open-problem-resolution (#19488; Proved)
Direct frozen dependencies: none (pinned Mathlib only)

The public claim keeps the preregistered definitions literally; proofs use the corresponding declarations.
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! Binding conventions for A. Cowtan and S. Burton, "CSS code surgery as a universal construction",
arXiv:2301.13738v6 (Quantum 8 (2024) 1344): based length-2 chain complexes `C₂ → C₁ → C₀` over `𝔽₂` (the Z-type
complexes of CSS codes), basis-preserving chain maps (Definition 3.4), monic spans, the basis-preserving pushout
`Qₙ = (C ⊕ D)ₙ / fₙ ∼ gₙ` with `∂Q [x] = [∂ x]` (Definition 5.1, Lemma 5.4), the LDPC property of a family (all row and
column weights of the differentials bounded by a constant, Section 4.1), and Conjecture D.1. -/

namespace D5.S3.Quantum.Information.CssMonicPushoutLdpc

open Matrix

/-- A based length-2 chain complex `C₂ → C₁ → C₀` over `𝔽₂`: the basis of `Cᵢ` is `Fin (dim i)` and the differentials
`∂₂ : C₂ → C₁`, `∂₁ : C₁ → C₀` are matrices with `∂₁ ∂₂ = 0`. -/
structure BasedComplex where
  dim : Fin 3 → ℕ
  d2 : Matrix (Fin (dim 1)) (Fin (dim 2)) (ZMod 2)
  d1 : Matrix (Fin (dim 0)) (Fin (dim 1)) (ZMod 2)
  comp : d1 * d2 = 0

/-- The matrix of the linear map sending the basis vector `a` to the basis vector `φ a`. -/
def basisMatrix {m n : ℕ} (φ : Fin m → Fin n) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun j a => if φ a = j then 1 else 0

/-- A basis-preserving chain map `f : A → C` (Definition 3.4): in each degree its matrix maps basis elements to basis
elements, so it is given by functions `fᵢ` on the bases, and it commutes with the differentials. -/
structure BPChainMap (A C : BasedComplex) where
  f : ∀ i : Fin 3, Fin (A.dim i) → Fin (C.dim i)
  comm2 : C.d2 * basisMatrix (f 2) = basisMatrix (f 1) * A.d2
  comm1 : C.d1 * basisMatrix (f 1) = basisMatrix (f 0) * A.d1

/-- A chain map of complexes of finite-dimensional `𝔽₂`-vector spaces is monic exactly when it is injective in every
degree; for a basis-preserving map this says that each linear map `basisMatrix (f i)` is injective. -/
def BPChainMap.Monic {A C : BasedComplex} (φ : BPChainMap A C) : Prop :=
  ∀ i : Fin 3, Function.Injective (basisMatrix (φ.f i)).mulVec

/-- The identification `fᵢ(a) ∼ gᵢ(a)` on the disjoint union of the bases of `Cᵢ` and `Dᵢ`. -/
def glue {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D) (i : Fin 3) :
    Fin (C.dim i) ⊕ Fin (D.dim i) → Fin (C.dim i) ⊕ Fin (D.dim i) → Prop :=
  fun x y => ∃ a, x = Sum.inl (φ.f i a) ∧ y = Sum.inr (ψ.f i a)

/-- The basis of `Qᵢ = (C ⊕ D)ᵢ / fᵢ ∼ gᵢ` (Lemma 5.4: the basis-preserving choice of pushout). -/
abbrev PBasis {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D) (i : Fin 3) : Type :=
  Quot (glue φ ψ i)

private noncomputable instance pbasisFintype {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D) (i : Fin 3) :
    Fintype (PBasis φ ψ i) := by
  classical
  exact Fintype.ofFinite _

/-- The differentials of `(C ⊕ D)`. -/
def sumD2 (C D : BasedComplex) :
    Matrix (Fin (C.dim 1) ⊕ Fin (D.dim 1)) (Fin (C.dim 2) ⊕ Fin (D.dim 2)) (ZMod 2) :=
  Matrix.fromBlocks C.d2 0 0 D.d2

def sumD1 (C D : BasedComplex) :
    Matrix (Fin (C.dim 0) ⊕ Fin (D.dim 0)) (Fin (C.dim 1) ⊕ Fin (D.dim 1)) (ZMod 2) :=
  Matrix.fromBlocks C.d1 0 0 D.d1

/-- The pushout differential `∂Q [y] = [∂ y]`: the column of the class `Y` is the image in `Q` of the column of a
representative of `Y`, where the image of a vector `v` has coefficient `Σ_{x ∈ X} v_x` at the class `X`. -/
noncomputable def pushoutD2 {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D) :
    Matrix (PBasis φ ψ 1) (PBasis φ ψ 2) (ZMod 2) := by
  classical
  exact fun X Y => ∑ x ∈ Finset.univ.filter (fun x => Quot.mk _ x = X), sumD2 C D x (Quot.out Y)

noncomputable def pushoutD1 {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D) :
    Matrix (PBasis φ ψ 0) (PBasis φ ψ 1) (ZMod 2) := by
  classical
  exact fun X Y => ∑ x ∈ Finset.univ.filter (fun x => Quot.mk _ x = X), sumD1 C D x (Quot.out Y)

/-- The largest Hamming weight of a row of `M` (the maximal check weight). -/
noncomputable def maxRowWeight {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ (ZMod 2)) : ℕ := by
  classical
  exact Finset.univ.sup fun i => (Finset.univ.filter fun j => M i j ≠ 0).card

/-- The largest Hamming weight of a column of `M` (the maximal number of checks on one qubit). -/
noncomputable def maxColWeight {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ (ZMod 2)) : ℕ :=
  maxRowWeight Mᵀ

/-- A family of codes is LDPC (Section 4.1): the Hamming weight of each column and row in each differential is bounded
from above by a constant independent of the family index. -/
def IsLDPC (d2w d1w : ℕ → ℕ × ℕ) : Prop :=
  ∃ w : ℕ, ∀ n, (d2w n).1 ≤ w ∧ (d2w n).2 ≤ w ∧ (d1w n).1 ≤ w ∧ (d1w n).2 ≤ w

/-- The (row, column) weight pairs of the two differentials of a based complex. -/
noncomputable def weights2 (E : BasedComplex) : ℕ × ℕ := (maxRowWeight E.d2, maxColWeight E.d2)
noncomputable def weights1 (E : BasedComplex) : ℕ × ℕ := (maxRowWeight E.d1, maxColWeight E.d1)

/-- Conjecture D.1, for a family of basis-preserving monic spans `C(n) ← A(n) → D(n)` parameterised by `n ∈ ℕ` whose
apex and feet are Z-type complexes of quantum LDPC codes: the family of pushouts `Q(n)` is also LDPC. -/
def claim : Prop :=
  ∀ (A C D : ℕ → BasedComplex) (φ : ∀ n, BPChainMap (A n) (C n)) (ψ : ∀ n, BPChainMap (A n) (D n)),
    (∀ n, (φ n).Monic) → (∀ n, (ψ n).Monic) →
    IsLDPC (fun n => weights2 (A n)) (fun n => weights1 (A n)) →
    IsLDPC (fun n => weights2 (C n)) (fun n => weights1 (C n)) →
    IsLDPC (fun n => weights2 (D n)) (fun n => weights1 (D n)) →
    IsLDPC (fun n => (maxRowWeight (pushoutD2 (φ n) (ψ n)), maxColWeight (pushoutD2 (φ n) (ψ n))))
      (fun n => (maxRowWeight (pushoutD1 (φ n) (ψ n)), maxColWeight (pushoutD1 (φ n) (ψ n))))

end D5.S3.Quantum.Information.CssMonicPushoutLdpc

namespace D5.S3.Quantum.Information.CssMonicPushoutLdpc

open Matrix CategoryTheory CategoryTheory.Limits.Types
open scoped Classical

private lemma monic_basis_injective {A C : BasedComplex} (φ : BPChainMap A C)
    (hφ : φ.Monic) (i : Fin 3) : Function.Injective (φ.f i) := by
    intro a b hab
    have hcol : (basisMatrix (φ.f i)).mulVec (Pi.single a 1) =
        (basisMatrix (φ.f i)).mulVec (Pi.single b 1) := by
      simp only [Matrix.mulVec_single_one]
      ext j
      simp [Matrix.col, basisMatrix, hab]
    have he := congrFun (hφ i hcol) a
    by_contra hn
    simpa [Pi.single_apply, Ne.symm hn] using he

/-- The binding quotient embeds each of its two summands; the general set-pushout
injectivity theorem supplies the matching property. -/
private lemma matching {A C D : BasedComplex} (φ : BPChainMap A C) (ψ : BPChainMap A D)
    (hφ : φ.Monic) (hψ : ψ.Monic) (i : Fin 3) :
    Function.Injective (fun c : Fin (C.dim i) =>
      (Quot.mk (glue φ ψ i) (Sum.inl c) : PBasis φ ψ i)) ∧
    Function.Injective (fun d : Fin (D.dim i) =>
      (Quot.mk (glue φ ψ i) (Sum.inr d) : PBasis φ ψ i)) := by
    let f := TypeCat.ofHom (φ.f i)
    let g := TypeCat.ofHom (ψ.f i)
    haveI : Mono f := (CategoryTheory.mono_iff_injective f).2 (monic_basis_injective φ hφ i)
    haveI : Mono g := (CategoryTheory.mono_iff_injective g).2 (monic_basis_injective ψ hψ i)
    let t : PBasis φ ψ i → Pushout f g := Quot.map id (by
      rintro x y ⟨a, rfl, rfl⟩
      exact Pushout.Rel.inl_inr a)
    constructor
    · intro x y h
      exact (CategoryTheory.mono_iff_injective (Pushout.inl f g)).1 inferInstance (congrArg t h)
    · intro x y h
      exact (CategoryTheory.mono_iff_injective (Pushout.inr f g)).1 inferInstance (congrArg t h)

private lemma row_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod 2)) (i : ι) :
    (Finset.univ.filter fun j => M i j ≠ 0).card ≤ maxRowWeight M := by
  classical
    exact Finset.le_sup (f := fun i => (Finset.univ.filter fun j => M i j ≠ 0).card)
      (Finset.mem_univ i)

private lemma row_weight_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod 2)) (w : ℕ)
    (h : ∀ i, (Finset.univ.filter fun j => M i j ≠ 0).card ≤ w) :
    maxRowWeight M ≤ w := by
  classical
    exact Finset.sup_le (fun i _ => h i)

/-- Selecting distinct source columns and summing rows over any quotient cannot
increase the support of a column. -/
private lemma quotient_column_card_le {ι κ ρ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype σ]
    (M : Matrix ι κ (ZMod 2)) (p : ι → ρ) (s : σ → κ) (Y : σ) :
    (Finset.univ.filter fun X =>
      (∑ x ∈ Finset.univ.filter (fun x => p x = X), M x (s Y)) ≠ 0).card ≤
    (Finset.univ.filter fun x => M x (s Y) ≠ 0).card := by
  classical
    let S := Finset.univ.filter fun x => M x (s Y) ≠ 0
    apply le_trans (Finset.card_le_card (t := S.image p) ?_) Finset.card_image_le
    intro X hX
    have hn : (∑ x ∈ Finset.univ.filter (fun x => p x = X), M x (s Y)) ≠ 0 :=
      (Finset.mem_filter.mp hX).2
    obtain ⟨x, hx, hmx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmx⟩,
      (Finset.mem_filter.mp hx).2⟩

/-- The row support is injected into the union of at most one row from each block. -/
private lemma quotient_block_row_bound {α β γ δ ρ σ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ρ] [Fintype σ]
    (M : Matrix α γ (ZMod 2)) (N : Matrix β δ (ZMod 2))
    (p : α ⊕ β → ρ) (s : σ → γ ⊕ δ)
    (hpL : Function.Injective (fun a => p (Sum.inl a)))
    (hpR : Function.Injective (fun b => p (Sum.inr b)))
    (hs : Function.Injective s) :
    maxRowWeight (fun X Y => ∑ x ∈ Finset.univ.filter (fun x => p x = X),
      Matrix.fromBlocks M 0 0 N x (s Y)) ≤ maxRowWeight M + maxRowWeight N := by
  classical
    apply row_weight_le
    intro X
    let U := Finset.univ.filter fun a => p (Sum.inl a) = X
    let V := Finset.univ.filter fun b => p (Sum.inr b) = X
    let L := U.biUnion fun a => Finset.univ.filter fun j => M a j ≠ 0
    let R := V.biUnion fun b => Finset.univ.filter fun j => N b j ≠ 0
    have hU : U.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      exact hpL (((Finset.mem_filter.mp ha).2).trans (Finset.mem_filter.mp hb).2.symm))
    have hV : V.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      exact hpR (((Finset.mem_filter.mp ha).2).trans (Finset.mem_filter.mp hb).2.symm))
    have hL : L.card ≤ maxRowWeight M := by
      calc
        L.card ≤ U.card * maxRowWeight M :=
          Finset.card_biUnion_le_card_mul U _ _ (fun a _ => row_card_le M a)
        _ ≤ 1 * maxRowWeight M := Nat.mul_le_mul_right _ hU
        _ = _ := one_mul _
    have hR : R.card ≤ maxRowWeight N := by
      calc
        R.card ≤ V.card * maxRowWeight N :=
          Finset.card_biUnion_le_card_mul V _ _ (fun b _ => row_card_le N b)
        _ ≤ 1 * maxRowWeight N := Nat.mul_le_mul_right _ hV
        _ = _ := one_mul _
    have hinj := Finset.card_le_card_of_injOn s
      (s := Finset.univ.filter fun Y =>
        (∑ x ∈ Finset.univ.filter (fun x => p x = X),
          Matrix.fromBlocks M 0 0 N x (s Y)) ≠ 0)
      (t := L.disjSum R) (by
      intro Y hY
      have hn : (∑ x ∈ Finset.univ.filter (fun x => p x = X),
          Matrix.fromBlocks M 0 0 N x (s Y)) ≠ 0 := (Finset.mem_filter.mp hY).2
      obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      have hp : p x = X := (Finset.mem_filter.mp hx).2
      cases x with
      | inl a =>
        cases he : s Y with
        | inl j =>
          simp only [he, Matrix.fromBlocks_apply₁₁] at hxy
          exact Finset.inl_mem_disjSum.mpr (Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩)
        | inr j => simp [he] at hxy
      | inr b =>
        cases he : s Y with
        | inl j => simp [he] at hxy
        | inr j =>
          simp only [he, Matrix.fromBlocks_apply₂₂] at hxy
          exact Finset.inr_mem_disjSum.mpr (Finset.mem_biUnion.mpr
            ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩))
      (fun _ _ _ _ he => hs he)
    exact hinj.trans ((by simpa only [Finset.card_disjSum] using Nat.add_le_add hL hR))

private lemma quotient_block_col_bound {α β γ δ ρ σ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ρ] [Fintype σ]
    (M : Matrix α γ (ZMod 2)) (N : Matrix β δ (ZMod 2))
    (p : α ⊕ β → ρ) (s : σ → γ ⊕ δ) :
    maxColWeight (fun X Y => ∑ x ∈ Finset.univ.filter (fun x => p x = X),
      Matrix.fromBlocks M 0 0 N x (s Y)) ≤ max (maxColWeight M) (maxColWeight N) := by
  classical
    apply row_weight_le
    intro Y
    have hb := quotient_column_card_le (Matrix.fromBlocks M 0 0 N) p s Y
    change (Finset.univ.filter fun X =>
      (∑ x ∈ Finset.univ.filter (fun x => p x = X),
        Matrix.fromBlocks M 0 0 N x (s Y)) ≠ 0).card ≤ _
    apply hb.trans
    cases he : s Y with
    | inl j =>
      have hset : (Finset.univ.filter fun x : α ⊕ β =>
          Matrix.fromBlocks M 0 0 N x (Sum.inl j) ≠ 0) =
          (Finset.univ.filter fun a => M a j ≠ 0).disjSum ∅ := by
        ext x
        cases x <;> simp
      rw [hset, Finset.card_disjSum, Finset.card_empty, Nat.add_zero]
      exact (row_card_le Mᵀ j).trans (le_max_left _ _)
    | inr j =>
      have hset : (Finset.univ.filter fun x : α ⊕ β =>
          Matrix.fromBlocks M 0 0 N x (Sum.inr j) ≠ 0) =
          (∅ : Finset α).disjSum (Finset.univ.filter fun b => N b j ≠ 0) := by
        ext x
        cases x <;> simp
      rw [hset, Finset.card_disjSum, Finset.card_empty, Nat.zero_add]
      exact (row_card_le Nᵀ j).trans (le_max_right _ _)

private lemma quotient_out_injective {α : Type*} {r : α → α → Prop} :
    Function.Injective (@Quot.out α r) := by
    exact (show Function.LeftInverse (Quot.mk r) (@Quot.out α r) from Quot.out_eq).injective

private lemma pushoutD2_row_bound {A C D : BasedComplex}
    (φ : BPChainMap A C) (ψ : BPChainMap A D) (hφ : φ.Monic) (hψ : ψ.Monic) :
    maxRowWeight (pushoutD2 φ ψ) ≤ maxRowWeight C.d2 + maxRowWeight D.d2 := by
    exact quotient_block_row_bound C.d2 D.d2 (Quot.mk (glue φ ψ 1)) (Quot.out (r := glue φ ψ 2))
      (matching φ ψ hφ hψ 1).1 (matching φ ψ hφ hψ 1).2 quotient_out_injective

private lemma pushoutD1_row_bound {A C D : BasedComplex}
    (φ : BPChainMap A C) (ψ : BPChainMap A D) (hφ : φ.Monic) (hψ : ψ.Monic) :
    maxRowWeight (pushoutD1 φ ψ) ≤ maxRowWeight C.d1 + maxRowWeight D.d1 := by
    exact quotient_block_row_bound C.d1 D.d1 (Quot.mk (glue φ ψ 0)) (Quot.out (r := glue φ ψ 1))
      (matching φ ψ hφ hψ 0).1 (matching φ ψ hφ hψ 0).2 quotient_out_injective

private lemma pushoutD2_col_bound {A C D : BasedComplex}
    (φ : BPChainMap A C) (ψ : BPChainMap A D) :
    maxColWeight (pushoutD2 φ ψ) ≤ max (maxColWeight C.d2) (maxColWeight D.d2) := by
    exact quotient_block_col_bound C.d2 D.d2 (Quot.mk (glue φ ψ 1)) (Quot.out (r := glue φ ψ 2))

private lemma pushoutD1_col_bound {A C D : BasedComplex}
    (φ : BPChainMap A C) (ψ : BPChainMap A D) :
    maxColWeight (pushoutD1 φ ψ) ≤ max (maxColWeight C.d1) (maxColWeight D.d1) := by
    exact quotient_block_col_bound C.d1 D.d1 (Quot.mk (glue φ ψ 0)) (Quot.out (r := glue φ ψ 1))

theorem result : D5.S3.Quantum.Information.CssMonicPushoutLdpc.claim := by
    intro A C D φ ψ hφ hψ _ hC hD
    obtain ⟨wC, hwC⟩ := hC
    obtain ⟨wD, hwD⟩ := hD
    refine ⟨wC + wD, ?_⟩
    intro n
    obtain ⟨c2r, c2c, c1r, c1c⟩ := hwC n
    obtain ⟨d2r, d2c, d1r, d1c⟩ := hwD n
    dsimp [weights2, weights1] at c2r c2c c1r c1c d2r d2c d1r d1c
    refine ⟨(pushoutD2_row_bound (φ n) (ψ n) (hφ n) (hψ n)).trans
      (Nat.add_le_add c2r d2r), ?_,
      (pushoutD1_row_bound (φ n) (ψ n) (hφ n) (hψ n)).trans
      (Nat.add_le_add c1r d1r), ?_⟩
    · exact (pushoutD2_col_bound (φ n) (ψ n)).trans
        (max_le (c2c.trans (Nat.le_add_right _ _)) (d2c.trans (Nat.le_add_left _ _)))
    · exact (pushoutD1_col_bound (φ n) (ψ n)).trans
        (max_le (c1c.trans (Nat.le_add_right _ _)) (d1c.trans (Nat.le_add_left _ _)))


end D5.S3.Quantum.Information.CssMonicPushoutLdpc
