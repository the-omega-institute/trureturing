/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric unitary bases extend along resolvable transversal designs with block multiplicity divisible by three, giving conditional Werner–Holevo rank attainment in powers of three. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.TransversalNineLabels
import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineWernerHolevo
import Mathlib.FieldTheory.Finite.GaloisField

/-! The within-fiber and transversal-class construction of symmetric unitary bases.
The three-block congruences come from `AffineNine.hollow`. Character-weighted
direct sums supply both the within-group matrices and the repetitions of each
three-block class. -/

open scoped ComplexConjugate
open Matrix Module

namespace TransversalNine

open AffineNine
open AffineNineFinite (F9 card_f9)

noncomputable section

/-- The first coordinate is the fiber. In class `d`, the second coordinate
is the transversal block. The two coordinates give a bijective chart. -/
structure ResolvableTD (M : Type*) where
  coords : M → F9 × M ≃ F9 × M
  fst_coords : ∀ d v, (coords d v).1 = v.1
  unique_class : ∀ v w : F9 × M, v.1 ≠ w.1 →
    ∃! d, (coords d v).2 = (coords d w).2

/-- An orthogonal basis of the full symmetric subspace with unitary entries. -/
structure UnitaryBasis (I V : Type*) [Fintype V] [DecidableEq V] where
  basis : Basis I ℂ (symmetric V)
  unitary : ∀ i, (basis i : Matrix V V ℂ) ∈ Matrix.unitaryGroup V ℂ
  orthogonal : ∀ i j, i ≠ j → hs (basis i : Matrix V V ℂ) (basis j : Matrix V V ℂ) = 0

private theorem hs_reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : Y ≃ X)
    (A B : Matrix X X ℂ) : hs (A.submatrix e e) (B.submatrix e e) = hs A B := by
  unfold hs
  apply Fintype.sum_equiv e
  intro x
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private def phasedBlocks {X G : Type*} [DecidableEq G] [AddCommGroup G]
    (A : Matrix X X ℂ) (χ : AddChar G ℂ) : Matrix (X × G) (X × G) ℂ :=
  Matrix.blockDiagonal fun g => χ g • A

private theorem phasedBlocks_unitary {X G : Type*} [Fintype X] [DecidableEq X]
    [Fintype G] [DecidableEq G] [AddCommGroup G] {A : Matrix X X ℂ}
    (hA : A ∈ Matrix.unitaryGroup X ℂ) (χ : AddChar G ℂ) :
    phasedBlocks A χ ∈ Matrix.unitaryGroup (X × G) ℂ := by
  rw [phasedBlocks, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hnorm (g : G) : χ g * star (χ g) = 1 := by
    change χ g * conj (χ g) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, χ.norm_apply]
    norm_num
  convert (Matrix.blockDiagonal_one (m := X) (o := G) (α := ℂ)) using 1
  congr 1
  funext g
  simp only [← Matrix.star_eq_conjTranspose, star_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  change (star (χ g) * χ g) • (A * star A) = 1
  rw [mul_comm (star (χ g)), hnorm, one_smul, Matrix.mem_unitaryGroup_iff.mp hA]

private theorem phasedBlocks_symm {X G : Type*} [DecidableEq G] [AddCommGroup G]
    {A : Matrix X X ℂ} (hA : A.IsSymm) (χ : AddChar G ℂ) : (phasedBlocks A χ).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [phasedBlocks, Matrix.blockDiagonal_apply, Matrix.smul_apply]
  by_cases h : i.2 = j.2
  · rw [ite_eq_left h.symm, ite_eq_left h, hA.apply i.1 j.1, h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

open scoped Classical in
private theorem phasedBlocks_hs {X G : Type*} [Fintype X] [Fintype G]
    [DecidableEq G] [AddCommGroup G] (A B : Matrix X X ℂ) (χ ψ : AddChar G ℂ) :
    hs (phasedBlocks A χ) (phasedBlocks B ψ) =
      (if χ = ψ then (Fintype.card G : ℂ) else 0) * hs A B := by
  have hχψ : ∑ g : G, conj (χ g) * ψ g = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
    have h := AddChar.wInner_cWeight_eq_boole χ ψ
    simp only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
      Fintype.expect_eq_sum_div_card] at h
    rw [div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at h
    simp only [mul_comm (a := conj _)] at *
    rw [h]
    split_ifs <;> simp
  rw [← hχψ, Finset.sum_mul]
  conv_lhs =>
    rw [← hs_reindex (Equiv.prodComm G X), hs, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  simp only [hs, Finset.mul_sum, Fintype.sum_prod_type, Matrix.submatrix_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single g]
  · apply Finset.sum_congr rfl
    intro y _
    simp only [phasedBlocks, Matrix.blockDiagonal_apply_eq, Matrix.smul_apply, smul_eq_mul,
      map_mul]
    ring
  · intro g' _ hg'
    simp [phasedBlocks, Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hg')]
  · simp

private def triple (χ : AddChar TripleLabels ℂ) : Matrix (F9 × ZMod 3) (F9 × ZMod 3) ℂ :=
  hollow f9Local tripleLabeling (Equiv.refl _) χ

variable {I M : Type*} [Fintype M] [DecidableEq M] {s : ℕ}

private def classChart (P : ResolvableTD M) (split : M ≃ ZMod 3 × ZMod s) (d : M) :
    F9 × M ≃ (F9 × ZMod 3) × ZMod s :=
  (P.coords d).trans (((Equiv.refl F9).prodCongr split).trans (Equiv.prodAssoc ..).symm)

/-- The two portions of the basis are indexed by the within-fiber characters
and the class, triple character, and repetition character. -/
abbrev Index (I M : Type*) (s : ℕ) :=
  (I × AddChar F9 ℂ) ⊕ (M × (AddChar TripleLabels ℂ × AddChar (ZMod s) ℂ))

/-- The actual matrices in the gluing construction. The supplied equivalence
groups the blocks of each parallel class into triples. -/
def family (U : UnitaryBasis I M) (P : ResolvableTD M) (split : M ≃ ZMod 3 × ZMod s) :
    Index I M s → Matrix (F9 × M) (F9 × M) ℂ
  | .inl (a, χ) => (phasedBlocks (U.basis a : Matrix M M ℂ) χ).submatrix
      (Equiv.prodComm F9 M) (Equiv.prodComm F9 M)
  | .inr (d, χ, ψ) => (phasedBlocks (triple χ) ψ).submatrix
      (classChart P split d) (classChart P split d)

private theorem family_unitary (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) [NeZero s] (i : Index I M s) :
    family U P split i ∈ Matrix.unitaryGroup (F9 × M) ℂ := by
  rcases i with ⟨a, χ⟩ | ⟨d, χ, ψ⟩
  · exact Matrix.submatrix_equiv_mem_unitary.mpr (phasedBlocks_unitary (U.unitary a) χ)
  · exact Matrix.submatrix_equiv_mem_unitary.mpr
      (phasedBlocks_unitary (hollow_unitary f9Local tripleLabeling (Equiv.refl _) χ) ψ)

private theorem family_symm (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) (i : Index I M s) : (family U P split i).IsSymm := by
  rcases i with ⟨a, χ⟩ | ⟨d, χ, ψ⟩
  · exact (phasedBlocks_symm (U.basis a).2 χ).submatrix _
  · exact (phasedBlocks_symm (hollow_symm f9Local tripleLabeling (Equiv.refl _) χ) ψ).submatrix _

private theorem within_zero (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) (a : I) (χ : AddChar F9 ℂ)
    {v w : F9 × M} (h : v.1 ≠ w.1) :
    family U P split (.inl (a, χ)) v w = 0 := by
  exact Matrix.blockDiagonal_apply_ne (fun g => χ g • (U.basis a : Matrix M M ℂ)) v.2 w.2 h

-- A cross-class entry can survive only on a pair in different fibers
-- whose two class coordinates name the same transversal block.
private theorem cross_zero (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) (d : M) (χ : AddChar TripleLabels ℂ)
    (ψ : AddChar (ZMod s) ℂ) {v w : F9 × M}
    (h : v.1 = w.1 ∨ (P.coords d v).2 ≠ (P.coords d w).2) :
    family U P split (.inr (d, χ, ψ)) v w = 0 := by
  let x := P.coords d v
  let y := P.coords d w
  change (if (split x.2).2 = (split y.2).2 then
    ψ (split x.2).2 * triple χ (x.1, (split x.2).1) (y.1, (split y.2).1) else 0) = 0
  split_ifs with h₂ <;> try rfl
  by_cases h₁ : (split x.2).1 = (split y.2).1
  · have hb : x.2 = y.2 := split.injective (Prod.ext h₁ h₂)
    have hf : x.1 = y.1 := by
      rw [P.fst_coords, P.fst_coords]
      exact h.resolve_right (not_not_intro hb)
    have he : (x.1, (split x.2).1) = (y.1, (split y.2).1) := Prod.ext hf h₁
    rw [he, triple, hollow_diag, mul_zero]
  · rw [triple, hollow_zero_of_different_blocks f9Local tripleLabeling (Equiv.refl _) χ
      (v := (x.1, (split x.2).1)) (w := (y.1, (split y.2).1)) h₁, mul_zero]

private theorem hs_eq_zero_of_disjoint {V : Type*} [Fintype V] {A B : Matrix V V ℂ}
    (h : ∀ v w, A v w = 0 ∨ B v w = 0) : hs A B = 0 := by
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  rcases h v w with hA | hB
  · rw [hA, map_zero, zero_mul]
  · rw [hB, mul_zero]

private theorem family_orthogonal (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) [NeZero s]
    {i j : Index I M s} (hij : i ≠ j) : hs (family U P split i) (family U P split j) = 0 := by
  classical
  rcases i with ⟨a, χ⟩ | ⟨d, χ, ψ⟩ <;> rcases j with ⟨b, χ'⟩ | ⟨d', χ', ψ'⟩
  · simp only [family, hs_reindex, phasedBlocks_hs]
    by_cases h : a = b
    · have hc : χ ≠ χ' := fun hc => hij (by rw [h, hc])
      simp [hc]
    · simp [U.orthogonal _ _ h]
  · apply hs_eq_zero_of_disjoint
    intro v w
    by_cases h : v.1 = w.1
    · exact Or.inr (cross_zero U P split _ _ _ (Or.inl h))
    · exact Or.inl (within_zero U P split _ _ h)
  · apply hs_eq_zero_of_disjoint
    intro v w
    by_cases h : v.1 = w.1
    · exact Or.inl (cross_zero U P split _ _ _ (Or.inl h))
    · exact Or.inr (within_zero U P split _ _ h)
  · by_cases hd : d = d'
    · subst d'
      simp only [family, hs_reindex, phasedBlocks_hs, triple, hollow_hs]
      by_cases h : χ = χ'
      · have hp : ψ ≠ ψ' := fun hp => hij (by rw [h, hp])
        simp [hp]
      · simp [h]
    · apply hs_eq_zero_of_disjoint
      intro v w
      by_cases h : v.1 = w.1
      · exact Or.inl (cross_zero U P split _ _ _ (Or.inl h))
      · by_cases hb : (P.coords d v).2 = (P.coords d w).2
        · obtain ⟨c, _, hc⟩ := P.unique_class v w h
          have hb' : (P.coords d' v).2 ≠ (P.coords d' w).2 :=
            fun he => hd ((hc _ hb).trans (hc _ he).symm)
          exact Or.inr (cross_zero U P split _ _ _ (Or.inr hb'))
        · exact Or.inl (cross_zero U P split _ _ _ (Or.inr hb))

variable [Fintype I]

private theorem family_card (U : UnitaryBasis I M)
    (split : M ≃ ZMod 3 × ZMod s) [NeZero s] :
    Fintype.card (Index I M s) = (Fintype.card (F9 × M) + 1).choose 2 := by
  have hi : Fintype.card I = (Fintype.card M + 1).choose 2 :=
    (Module.finrank_eq_card_basis U.basis).symm.trans finrank_symmetric
  have hm : Fintype.card M = 3 * s := by
    simpa using Fintype.card_congr split
  simp only [Index, Fintype.card_sum, Fintype.card_prod]
  simp only [AddChar.card_eq, card_f9, ZMod.card, card_tripleLabels, hi]
  have hchoose (n : ℕ) : n * (n + 1) = 2 * (n + 1).choose 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (n + 1)]
    exact (Nat.mul_div_cancel' ((even_iff_two_dvd).mp (Nat.even_mul_succ_self n))).symm
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * ((Fintype.card M + 1).choose 2 * 9 + Fintype.card M * (108 * s)) =
        9 * (Fintype.card M * (Fintype.card M + 1)) +
          2 * (Fintype.card M * (36 * Fintype.card M)) := by
      rw [show 108 * s = 36 * Fintype.card M by rw [hm]; ring, hchoose]
      ring
    _ = (9 * Fintype.card M) * (9 * Fintype.card M + 1) := by ring
    _ = 2 * (9 * Fintype.card M + 1).choose 2 := hchoose _

private theorem family_linearIndependent [Nonempty M] [NeZero s] (U : UnitaryBasis I M)
    (P : ResolvableTD M) (split : M ≃ ZMod 3 × ZMod s) :
    LinearIndependent ℂ (family U P split) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let pairing : Matrix (F9 × M) (F9 × M) ℂ →ₗ[ℂ] ℂ :=
    { toFun := hs (family U P split i)
      map_add' A B := by simp [hs, mul_add, Finset.sum_add_distrib]
      map_smul' a A := by simp [hs, Finset.mul_sum, mul_left_comm] }
  have h := congrArg pairing hc
  simp only [map_sum, map_smul, map_zero] at h
  change (∑ j, c j * hs (family U P split i) (family U P split j)) = 0 at h
  rw [Finset.sum_eq_single i] at h
  · rw [hs_self_of_unitary (family_unitary U P split i)] at h
    exact (mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · intro j _ hji
    rw [family_orthogonal U P split (Ne.symm hji), mul_zero]
  · simp

/-- With a specified grouping of the blocks into triples, gluing constructs
a basis of the entire symmetric subspace, with the indicated matrix family. -/
def glue [Nonempty M] [NeZero s] (U : UnitaryBasis I M) (P : ResolvableTD M)
    (split : M ≃ ZMod 3 × ZMod s) : UnitaryBasis (Index I M s) (F9 × M) := by
  let b : Index I M s → symmetric (F9 × M) := fun i => ⟨family U P split i, family_symm U P split i⟩
  let B := basisOfLinearIndependentOfCardEqFinrank (b := b)
    (LinearIndependent.of_comp (symmetric (F9 × M)).subtype (family_linearIndependent U P split))
    ((family_card U split).trans finrank_symmetric.symm)
  have hB : ∀ i, (B i : Matrix (F9 × M) (F9 × M) ℂ) = family U P split i := by
    intro i
    dsimp only [B]
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact ⟨B, fun i => hB i ▸ family_unitary U P split i,
    fun i j h => by rw [hB, hB]; exact family_orthogonal U P split h⟩

private def symmetricReindex {X Y : Type*} (e : Y ≃ X) :
    symmetric X ≃ₗ[ℂ] symmetric Y where
  toFun A := ⟨A.1.submatrix e e, A.2.submatrix e⟩
  invFun A := ⟨A.1.submatrix e.symm e.symm, A.2.submatrix e.symm⟩
  left_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  right_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transport an orthogonal unitary basis along equivalences of its index
and matrix vertex types. -/
def UnitaryBasis.reindex {J V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (U : UnitaryBasis I V) (e : I ≃ J) (v : W ≃ V) : UnitaryBasis J W where
  basis := (U.basis.map (symmetricReindex v)).reindex e
  unitary i := by
    rw [Basis.reindex_apply, Basis.map_apply]
    exact Matrix.submatrix_equiv_mem_unitary.mpr (U.unitary (e.symm i))
  orthogonal i j hij := by
    rw [Basis.reindex_apply, Basis.reindex_apply, Basis.map_apply, Basis.map_apply]
    change hs ((U.basis (e.symm i) : Matrix V V ℂ).submatrix v v)
      ((U.basis (e.symm j) : Matrix V V ℂ).submatrix v v) = 0
    rw [hs_reindex]
    exact U.orthogonal _ _ (fun h => hij (e.symm.injective h))

/-- A resolvable transversal TD(9,m) and a full basis of order m give a full
basis of order 9m whenever 3 divides m. -/
def glueTD [Nonempty M] (U : UnitaryBasis I M) (P : ResolvableTD M)
    (hdiv : 3 ∣ Fintype.card M) :
    UnitaryBasis (Fin ((9 * Fintype.card M + 1).choose 2)) (Fin (9 * Fintype.card M)) := by
  let s := Fintype.card M / 3
  have hm : 3 * s = Fintype.card M := Nat.mul_div_cancel' hdiv
  haveI : NeZero s := ⟨by
    intro h
    have := Fintype.card_ne_zero (α := M)
    exact this (by simpa [h] using hm.symm)⟩
  let e : M ≃ ZMod 3 × ZMod s := (Fintype.equivFinOfCardEq (n := 3 * s) hm.symm).trans
    (Fintype.equivFinOfCardEq (by simp)).symm
  let B := glue U P e
  let i := Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_prod, card_f9] using family_card U e)
  let v : Fin (9 * Fintype.card M) ≃ F9 × M := (Fintype.equivFinOfCardEq (by simp [card_f9])).symm
  exact B.reindex i v

/-- For the nine fibers indexed by F₉ and distinct slopes `a j` in the
ambient field, class `s` consists of the transversals `(j, s * a j + t)`.
The class chart recovers the intercept `t` by subtraction. -/
def affineTD {K : Type*} [Field K] (a : F9 ↪ K) : ResolvableTD K where
  coords s :=
    { toFun := fun v => (v.1, v.2 - s * a v.1)
      invFun := fun p => (p.1, s * a p.1 + p.2)
      left_inv := fun v => Prod.ext rfl (by simp)
      right_inv := fun p => Prod.ext rfl (by simp) }
  fst_coords _ _ := rfl
  unique_class v w h := by
    have ha : a w.1 - a v.1 ≠ 0 := sub_ne_zero.mpr (fun h' => h (a.injective h').symm)
    refine ⟨(w.2 - v.2) / (a w.1 - a v.1), ?_, ?_⟩
    · change v.2 - ((w.2 - v.2) / (a w.1 - a v.1)) * a v.1 =
        w.2 - ((w.2 - v.2) / (a w.1 - a v.1)) * a w.1
      field_simp
      ring
    · intro s hs
      change v.2 - s * a v.1 = w.2 - s * a w.1 at hs
      apply (eq_div_iff ha).mpr
      linear_combination hs

/-- Existence of a full orthogonal symmetric unitary basis in dimension n. -/
abbrev HasBasis (n : ℕ) := Nonempty (UnitaryBasis (Fin ((n + 1).choose 2)) (Fin n))

/-- A full basis in order 3^r gives a full basis in order 3^(r+2). Mathlib supplies
the field of order 3^r and the cardinality bound gives the nine distinct slopes. -/
theorem primePowerStep {r : ℕ} (hr : 2 ≤ r) :
    HasBasis (3 ^ r) → HasBasis (3 ^ (r + 2)) := by
  rintro ⟨U⟩
  let K := GaloisField 3 r
  let : Fintype K := Fintype.ofFinite K
  classical
  have hk : Fintype.card K = 3 ^ r :=
    Fintype.card_eq_nat_card.trans (GaloisField.card 3 r (by omega))
  let e : K ≃ Fin (3 ^ r) := Fintype.equivFinOfCardEq hk
  let : Nonempty K := ⟨0⟩
  have h9 : Fintype.card F9 ≤ Fintype.card K := by
    rw [card_f9, hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hr
  let a : F9 ↪ K := Classical.choice (Function.Embedding.nonempty_of_card_le h9)
  have hdiv : 3 ∣ Fintype.card K := by
    rw [hk]
    exact dvd_pow_self 3 (by omega : r ≠ 0)
  have hd : 9 * Fintype.card K = 3 ^ (r + 2) := by rw [hk, pow_add]; simp [mul_comm]
  let B := glueTD (U.reindex (Equiv.refl _) e) (affineTD a) hdiv
  exact ⟨B.reindex (finCongr (congrArg (fun n => (n + 1).choose 2) hd)) (finCongr hd.symm)⟩

open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open AffineNineRank (HasMixedUnitaryDecomposition)

/-- The canonical Werner–Holevo channel attains the Choi-rank lower bound
in any positive dimension with a full orthogonal symmetric unitary basis. -/
theorem rank_exact {n : ℕ} [NeZero n] (h : HasBasis n) :
    ∃ channel : QuantumChannel (Fin n) (Fin n),
      (∀ X : Matrix (Fin n) (Fin n) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin n) X) ∧
      IsLeast {k : ℕ | HasMixedUnitaryDecomposition channel k} (n * (n + 1) / 2) := by
  obtain ⟨U⟩ := h
  let A (i : Fin ((n + 1).choose 2)) : Matrix (Fin n) (Fin n) ℂ := U.basis i
  have ho i j (hij : i ≠ j) : AffineNineRank.hsInner (A i) (A j) = 0 := by
    rw [AffineNineRank.hsInner_eq_sum]
    exact U.orthogonal i j hij
  simpa only [Fintype.card_fin] using
    AffineNineRank.mixedUnitary_rank_exact A U.unitary (fun i => (U.basis i).2) ho (by simp)

/-- A full orthogonal symmetric unitary basis in dimension 27 gives exact
mixed-unitary rank in dimensions 3^r for r ≥ 3. The odd exponents follow by
induction with the field step. The even exponents use the affine theorem. -/
theorem mixedUnitaryRank_power_three (h27 : HasBasis 27) (r : ℕ) (hr : 3 ≤ r) :
    let n := 3 ^ r
    ∃ channel : QuantumChannel (Fin n) (Fin n),
      (∀ X : Matrix (Fin n) (Fin n) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin n) X) ∧
      IsLeast {k : ℕ | HasMixedUnitaryDecomposition channel k} (n * (n + 1) / 2) := by
  dsimp only
  by_cases heven : r % 2 = 0
  · have hexp : r = 2 * (r / 2) := by omega
    have hpow : 3 ^ r = 9 ^ (r / 2) := by
      calc
        3 ^ r = 3 ^ (2 * (r / 2)) := congrArg (fun k : ℕ => 3 ^ k) hexp
        _ = 9 ^ (r / 2) := by rw [pow_mul]; rfl
    rw [hpow]
    exact mixedUnitaryRank_power_nine (r / 2) (by omega)
  · have hodd (k : ℕ) : HasBasis (3 ^ (3 + 2 * k)) := by
      induction k with
      | zero => exact h27
      | succ k ih =>
        rw [show 3 + 2 * (k + 1) = (3 + 2 * k) + 2 by omega]
        exact primePowerStep (by omega) ih
    have hexp : r = 3 + 2 * ((r - 3) / 2) := by omega
    have : NeZero (3 ^ r) := ⟨by positivity⟩
    exact rank_exact (hexp.symm ▸ hodd ((r - 3) / 2))

#print axioms glueTD
#print axioms affineTD
#print axioms primePowerStep
#print axioms rank_exact
#print axioms mixedUnitaryRank_power_three

end
end TransversalNine
