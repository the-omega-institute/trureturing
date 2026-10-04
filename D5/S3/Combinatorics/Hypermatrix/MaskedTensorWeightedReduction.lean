/- GID: D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Actual masked tensor cardinality reduces to the eligible weight sum. -/

import D5.S3.Combinatorics.Hypermatrix.PencilParameterFibers
import D5.S3.Combinatorics.Hypermatrix.SoutheastFactorization
import D5.S3.Combinatorics.Hypermatrix.LiteralMaskedCellCount

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

namespace D5.S3.Combinatorics.Hypermatrix.MaskedTensorWeightedReduction

attribute [local instance] Classical.propDecidable

open D5.S3.Combinatorics.Hypermatrix.LiteralMaskedCellCount

set_option maxHeartbeats 3000000 in
-- The proof combines induction and explicit finite coordinate constructions.
theorem masked_tensor_weighted_reduction (F : Type*) [Field F] [Fintype F]
    (k : ℕ) (hk : 1 ≤ k) (lam mu : Fin k → ℕ)
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hml : ∀ j, mu j ≤ lam j)
    (hlbound : ∀ j, lam j ≤ k - j.val)
    (hmbound : ∀ j, mu j < k - j.val) :

    Nat.card (ActualCarrier F k lam mu) =
    Fintype.card F ^ (k*k) * (Fintype.card F-1)^(2*k) *
      (∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        if D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi
        then Fintype.card F ^
          (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
            (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi).toNat else 0) := by
  classical
  obtain ⟨normalization, factorFullRank, shiftMap, sameFactors, shiftInjective⟩ :=
    PencilParameterFibers.pencil_parameter_fibers F k hk
  obtain ⟨upperPivotStep, leftSEExists, seUnique⟩ :=
    SoutheastFactorization.southeast_factorization F
  let factors := Factors F k
  have leftMask (nu : Fin k → ℕ)
      (M : Matrix (Fin (k + 1)) (Fin k) F)
      (hM : ∀ r j, k + 1 - nu j ≤ r.val → M r j = 0)
      (L : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
      (hL : L.IsUpperTriangular) :
      ∀ r j, k + 1 - nu j ≤ r.val → (L * M) r j = 0 := by
    intro r j hr
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t < r
    · rw [hL ht, zero_mul]
    · have hrt : r.val ≤ t.val := le_of_not_gt ht
      rw [hM t j (by omega), mul_zero]
  have rightMask (nu : Fin k → ℕ) (hnu : Antitone nu)
      (M : Matrix (Fin (k + 1)) (Fin k) F)
      (hM : ∀ r j, k + 1 - nu j ≤ r.val → M r j = 0)
      (R : Matrix (Fin k) (Fin k) F) (hR : R.IsUpperTriangular) :
      ∀ r j, k + 1 - nu j ≤ r.val → (M * R) r j = 0 := by
    intro r j hr
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : j < t
    · rw [hR ht, mul_zero]
    · have htj : t ≤ j := le_of_not_gt ht
      have hn : nu j ≤ nu t := hnu htj
      rw [hM r t (by omega), zero_mul]
  have triangularRespect (T : Faces F k) (hT : Respects lam mu T)
      (L : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
      (R : Matrix (Fin k) (Fin k) F)
      (hL : L.IsUpperTriangular) (hR : R.IsUpperTriangular) :
      Respects lam mu (L * T.1 * R, L * T.2 * R) := by
    exact ⟨rightMask lam hlam (L * T.1) (leftMask lam T.1 hT.1 L hL) R hR,
      rightMask mu hmu (L * T.2) (leftMask mu T.2 hT.2 L hL) R hR⟩
  have triangularRespectIff (T : Faces F k)
      (L : GL (Fin (k + 1)) F) (R : GL (Fin k) F)
      (hL : (L : Matrix (Fin (k + 1)) (Fin (k + 1)) F).IsUpperTriangular)
      (hR : (R : Matrix (Fin k) (Fin k) F).IsUpperTriangular) :
      Respects lam mu ((L : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * T.1 *
          (R : Matrix (Fin k) (Fin k) F),
        (L : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * T.2 *
          (R : Matrix (Fin k) (Fin k) F)) ↔ Respects lam mu T := by
    letI : Invertible (L : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :=
      L.invertible
    letI : Invertible (R : Matrix (Fin k) (Fin k) F) :=
      R.invertible
    have hLi : L.inv.IsUpperTriangular := by
      change (↑(L⁻¹) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).IsUpperTriangular
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hL
    have hRi : R.inv.IsUpperTriangular := by
      change (↑(R⁻¹) : Matrix (Fin k) (Fin k) F).IsUpperTriangular
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hR
    constructor
    · intro hT
      have hh := triangularRespect _ hT L.inv R.inv hLi hRi
      have cancel (M : Matrix (Fin (k + 1)) (Fin k) F) :
          L.inv * ((L : Matrix (Fin (k + 1)) (Fin (k + 1)) F) * M *
            (R : Matrix (Fin k) (Fin k) F)) * R.inv = M := by
        simp only [← Matrix.mul_assoc, L.inv_val, Matrix.one_mul]
        rw [Matrix.mul_assoc, R.val_inv, Matrix.mul_one]
      simpa only [cancel] using hh
    · intro hT
      exact triangularRespect T hT _ _ hL hR

  have factorEntries (g : factors) (r : Fin (k + 1)) (j : Fin k) :
      (factorMap g).1 r j = ∑ i : Fin k, g.1 r i.castSucc * g.2 i j ∧
      (factorMap g).2 r j = ∑ i : Fin k, g.1 r i.succ * g.2 i j := by
    constructor
    · change (∑ i : Fin k, (∑ s : Fin (k + 1), g.1 r s * E0 F k s i) *
          g.2 i j) = _
      simp [E0]
    · change (∑ i : Fin k, (∑ s : Fin (k + 1), g.1 r s * E1 F k s i) *
          g.2 i j) = _
      simp [E1]
  have literalMaskEquations (g : factors) : Respects lam mu (factorMap g) ↔
      (∀ r j, k + 1 - lam j ≤ r.val →
        (∑ i : Fin k, g.1 r i.castSucc * g.2 i j) = 0) ∧
      (∀ r j, k + 1 - mu j ≤ r.val →
        (∑ i : Fin k, g.1 r i.succ * g.2 i j) = 0) := by
    constructor
    · intro h
      exact ⟨fun r j hr => (factorEntries g r j).1.symm.trans (h.1 r j hr),
        fun r j hr => (factorEntries g r j).2.symm.trans (h.2 r j hr)⟩
    · intro h
      exact ⟨fun r j hr => (factorEntries g r j).1.trans (h.1 r j hr),
        fun r j hr => (factorEntries g r j).2.trans (h.2 r j hr)⟩


  have cellRead_write (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) :
      cellRead sigma pi (cellA sigma pi z) (cellB sigma pi z) = z := by
    funext v
    cases v with
    | inl ab =>
      have hn : ab.val.1 ≠ ab.val.2 := ne_of_lt ab.property.1
      simp [cellRead, cellA, hn, ab.property]
    | inr ij =>
      have hn : ij.val.1 ≠ ij.val.2 := ne_of_lt ij.property.1
      simp [cellRead, cellB, hn, ij.property]
  have cellWrite_read (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (A : Matrix (Fin (k+1)) (Fin (k+1)) F)
      (B : Matrix (Fin k) (Fin k) F) (hA : SEShape sigma A) (hB : NWRightShape pi B) :
      cellA sigma pi (cellRead sigma pi A B) = A ∧
      cellB sigma pi (cellRead sigma pi A B) = B := by
    constructor
    · ext r b
      have hh := hA (sigma.symm r) b
      simpa [cellA, cellRead] using hh.symm
    · ext a i
      have hh := hB i (pi.symm a)
      simpa [cellB, cellRead] using hh.symm
  have cellShape (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) :
      SEShape sigma (cellA sigma pi z) ∧ NWRightShape pi (cellB sigma pi z) := by
    constructor
    · intro a b
      simp only [cellA, Equiv.symm_apply_apply]
      split_ifs <;> rfl
    · intro i j
      simp only [cellB, Equiv.symm_apply_apply]
      split_ifs <;> rfl
  have cellA_unit (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) : IsUnit (cellA sigma pi z) := by
    let N := (cellA sigma pi z).submatrix sigma id
    have ht : N.IsUpperTriangular := by
      intro a b hab
      have hn : a ≠ b := ne_of_gt hab
      have hnb : ¬a < b := not_lt_of_ge (le_of_lt hab)
      simp [N, cellA, hn, hnb]
    have hd (a : Fin (k+1)) : N a a = 1 := by simp [N,cellA]
    have hdet : N.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular ht]
      simp [Matrix.diag, hd]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    change ((cellA sigma pi z).submatrix sigma id).det = 1 at hdet
    rw [Matrix.det_permute, hz, mul_zero] at hdet
    exact zero_ne_one hdet
  have cellB_unit (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) : IsUnit (cellB sigma pi z) := by
    let N := (cellB sigma pi z).submatrix id pi.symm
    have ht : N.IsUpperTriangular := by
      intro a b hab
      have hn : pi.symm b ≠ pi.symm a := fun he =>
        (ne_of_gt hab) (pi.symm.injective he).symm
      have hnb : ¬a < b := not_lt_of_ge (le_of_lt hab)
      simp [N, cellB, hn, hnb]
    have hd (a : Fin k) : N a a = 1 := by simp [N,cellB]
    have hdet : N.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular ht]
      simp [Matrix.diag, hd]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    change ((cellB sigma pi z).submatrix id pi.symm).det = 1 at hdet
    rw [Matrix.det_permute', hz, mul_zero] at hdet
    exact zero_ne_one hdet
  let cellGL (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) : factors :=
    ((cellA_unit sigma pi z).unit, (cellB_unit sigma pi z).unit)
  have cellGL_val (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) :
      ((cellGL sigma pi z).1 : Matrix (Fin (k+1)) (Fin (k+1)) F) = cellA sigma pi z ∧
      ((cellGL sigma pi z).2 : Matrix (Fin k) (Fin k) F) = cellB sigma pi z := by
    exact ⟨IsUnit.unit_spec _, IsUnit.unit_spec _⟩
  let NormalizedCell (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :=
    {g : factors // SEShape sigma g.1.val ∧ NWRightShape pi g.2.val ∧
      Respects lam mu (factorMap g)}
  let CoordinateSolutions (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :=
    {z : CellVariables sigma pi → F // Respects lam mu (factorMap (cellGL sigma pi z))}
  have literalCoordinateEquations (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (z : CellVariables sigma pi → F) :
      Respects lam mu (factorMap (cellGL sigma pi z)) ↔
      (∀ r j, k+1-lam j ≤ r.val →
        (∑ b : Fin k, cellA sigma pi z r b.castSucc * cellB sigma pi z b j) = 0) ∧
      (∀ r j, k+1-mu j ≤ r.val →
        (∑ b : Fin k, cellA sigma pi z r b.succ * cellB sigma pi z b j) = 0) := by
    simpa only [(cellGL_val sigma pi z).1, (cellGL_val sigma pi z).2] using
      literalMaskEquations (cellGL sigma pi z)
  let coordinateMaskedEquiv (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      CoordinateSolutions sigma pi ≃ NormalizedCell sigma pi :=
    { toFun := fun z => ⟨cellGL sigma pi z.val, by
        have hs := cellShape sigma pi z.val
        exact ⟨by simpa only [(cellGL_val sigma pi z.val).1] using hs.1,
          by simpa only [(cellGL_val sigma pi z.val).2] using hs.2, z.property⟩⟩
      invFun := fun g => ⟨cellRead sigma pi g.val.1.val g.val.2.val, by
        have hw := cellWrite_read sigma pi g.val.1.val g.val.2.val g.property.1 g.property.2.1
        have hg : cellGL sigma pi (cellRead sigma pi g.val.1.val g.val.2.val) = g.val := by
          apply Prod.ext
          · apply Units.ext
            exact (cellGL_val _ _ _).1.trans hw.1
          · apply Units.ext
            exact (cellGL_val _ _ _).2.trans hw.2
        rw [hg]
        exact g.property.2.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change cellRead sigma pi (cellGL sigma pi z.val).1.val (cellGL sigma pi z.val).2.val = z.val
        rw [(cellGL_val _ _ _).1, (cellGL_val _ _ _).2]
        exact cellRead_write sigma pi z.val
      right_inv := by
        intro g
        apply Subtype.ext
        have hw := cellWrite_read sigma pi g.val.1.val g.val.2.val g.property.1 g.property.2.1
        apply Prod.ext
        · apply Units.ext
          exact (cellGL_val _ _ _).1.trans hw.1
        · apply Units.ext
          exact (cellGL_val _ _ _).2.trans hw.2 }
  have literalIneligibleCount (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
      (h : ¬D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
        (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi) :
      Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) = 0 := by
    simpa only [if_neg h] using
      literal_cell_count_original_masks F k hk lam mu hlam hmu hml hlbound hmbound sigma pi
  let coordinateLiteralEquiv (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      CoordinateSolutions sigma pi ≃ (LiteralSolutions (F := F) lam mu sigma pi) :=
    Equiv.subtypeEquivRight (literalCoordinateEquations sigma pi)
  have normalizedCoordinateReduction (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      Nat.card (NormalizedCell sigma pi) = Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) :=
    (Nat.card_congr ((coordinateMaskedEquiv sigma pi).symm.trans
      (coordinateLiteralEquiv sigma pi)))

  have paramSurj (T : ActualCarrier F k lam mu) :
      ∃ g : factors, factorMap g = T.val := by
    obtain ⟨A, B, h0, h1⟩ := normalization T.val T.property.2
    exact ⟨(A, B), Prod.ext h0.symm h1.symm⟩
  choose selector selector_eq using paramSurj
  let MaskParameters := {g : factors // Respects lam mu (factorMap g)}
  let totalMap : ActualCarrier F k lam mu × Fˣ → MaskParameters := fun z =>
    ⟨shift (selector z.1) z.2, by
      rw [shiftMap, selector_eq]
      exact z.1.property.1⟩
  have totalBijective : Function.Bijective totalMap := by
    constructor
    · rintro ⟨T, u⟩ ⟨T', v⟩ he
      have hfaces : T.val = T'.val := by
        calc
          _ = factorMap (shift (selector T) u) :=
            (shiftMap (selector T) u |>.trans (selector_eq T)).symm
          _ = factorMap (shift (selector T') v) :=
            congrArg factorMap (congrArg Subtype.val he)
          _ = _ := shiftMap (selector T') v |>.trans (selector_eq T')
      have hT : T = T' := Subtype.ext hfaces
      subst T'
      have huv : u = v := shiftInjective (selector T) (congrArg Subtype.val he)
      cases huv
      rfl
    · intro g
      let T : ActualCarrier F k lam mu :=
        ⟨factorMap g.val, g.property, factorFullRank g.val⟩
      have he : factorMap g.val = factorMap (selector T) := (selector_eq T).symm
      obtain ⟨u, hu⟩ := sameFactors (selector T) g.val he
      exact ⟨(T, u), Subtype.ext hu.symm⟩
  have actualParameterCount :
      Nat.card MaskParameters = Nat.card (ActualCarrier F k lam mu) *
        (Fintype.card F - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective totalMap totalBijective),
      Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := F)]
  have qminusPositive : 0 < Fintype.card F - 1 := by
    rw [← Fintype.card_units]
    exact Fintype.card_pos

  let flipMat {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :=
    M.transpose.submatrix Fin.rev Fin.rev
  have flipOne (n : ℕ) : flipMat (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    dsimp [flipMat]
    rw [Matrix.transpose_one]
    exact Matrix.submatrix_one_equiv Fin.revPerm
  have flipMul {n : ℕ} (M N : Matrix (Fin n) (Fin n) F) :
      flipMat (M * N) = flipMat N * flipMat M := by
    dsimp [flipMat]
    rw [Matrix.transpose_mul]
    exact (Matrix.submatrix_mul_equiv N.transpose M.transpose
      Fin.rev Fin.revPerm Fin.rev).symm
  let flipGL {n : ℕ} (M : GL (Fin n) F) : GL (Fin n) F :=
    { val := flipMat M.val
      inv := flipMat M.inv
      val_inv := by rw [← flipMul, M.inv_val, flipOne]
      inv_val := by rw [← flipMul, M.val_inv, flipOne] }
  have flipGLMul {n : ℕ} (M N : GL (Fin n) F) :
      flipGL (M * N) = flipGL N * flipGL M := by
    apply Units.ext
    exact flipMul M.val N.val
  have flipGLInjective {n : ℕ} : Function.Injective (flipGL (n := n)) := by
    intro M N h
    apply Units.ext
    ext r b
    have hh := congrArg (fun V : GL (Fin n) F => V.val b.rev r.rev) h
    simpa [flipGL, flipMat] using hh
  have flipUpper {n : ℕ} (M : GL (Fin n) F) (hM : M.val.IsUpperTriangular) :
      (flipGL M).val.IsUpperTriangular := by
    intro r b hbr
    exact hM (Fin.rev_lt_rev.mpr hbr)
  let flipPerm {n : ℕ} (p : Equiv.Perm (Fin n)) :=
    Fin.revPerm.trans (p.symm.trans Fin.revPerm)
  have flipShape {n : ℕ} (p : Equiv.Perm (Fin n)) (B : GL (Fin n) F)
      (hB : ∀ i j, B.val (p j) i = if i = j then 1 else
        if i < j ∧ p j < p i then B.val (p j) i else 0) :
      ∀ a b, (flipGL B).val (flipPerm p a) b = if a = b then 1 else
        if a < b ∧ flipPerm p b < flipPerm p a then
          (flipGL B).val (flipPerm p a) b else 0 := by
    intro a b
    have hh := hB (p.symm a.rev) (p.symm b.rev)
    simpa [flipGL, flipMat, flipPerm, Fin.rev_lt_rev, and_comm] using hh

  have upperCoordinates (n : ℕ) :
      {L : GL (Fin n) F // L.val.IsUpperTriangular} ≃
        (Fin n → Fˣ) × ((Σ c : Fin n, Fin c.val) → F) := by
    let build (d : (Fin n → Fˣ) × ((Σ c : Fin n, Fin c.val) → F)) :
        Matrix (Fin n) (Fin n) F := fun r c =>
      if he : r = c then (d.1 r : F) else
        if hl : r < c then d.2 ⟨c, ⟨r.val, hl⟩⟩ else 0
    have triangular (d) : (build d).IsUpperTriangular := by
      intro r c hcr
      change c < r at hcr
      simp [build, ne_of_gt hcr, not_lt_of_ge hcr.le]
    have diagonal (d) (r : Fin n) : build d r r = (d.1 r : F) := by
      simp [build]
    have unitBuild (d) : IsUnit (build d) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_of_isUpperTriangular (triangular d)]
      exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
        (fun r _ => by rw [diagonal]; exact Units.ne_zero _))
    have nonzero (L : {L : GL (Fin n) F // L.val.IsUpperTriangular}) (r : Fin n) :
        L.val.val r r ≠ 0 := by
      have hu := isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units L.val)
      rw [Matrix.det_of_isUpperTriangular L.property] at hu
      exact Finset.prod_ne_zero_iff.mp hu r (Finset.mem_univ _)
    let read (L : {L : GL (Fin n) F // L.val.IsUpperTriangular}) :
        (Fin n → Fˣ) × ((Σ c : Fin n, Fin c.val) → F) :=
      (fun r => Units.mk0 (L.val.val r r) (nonzero L r),
        fun rc => L.val.val ⟨rc.2.val, rc.2.isLt.trans rc.1.isLt⟩ rc.1)
    let write (d : (Fin n → Fˣ) × ((Σ c : Fin n, Fin c.val) → F)) :
        {L : GL (Fin n) F // L.val.IsUpperTriangular} :=
      ⟨(unitBuild d).unit, by rw [IsUnit.unit_spec]; exact triangular d⟩
    refine { toFun := read, invFun := write, left_inv := ?_, right_inv := ?_ }
    · intro L
      apply Subtype.ext
      apply Units.ext
      rw [show (write (read L)).val.val = build (read L) from IsUnit.unit_spec _]
      ext r c
      dsimp [build, read]
      split_ifs with he hl
      · subst c; rfl
      · rfl
      · exact (L.property (lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he))).symm
    · intro d
      apply Prod.ext
      · funext r
        apply Units.ext
        change build d r r = (d.1 r : F)
        exact diagonal d r
      · funext rc
        change build d ⟨rc.2.val, rc.2.isLt.trans rc.1.isLt⟩ rc.1 = d.2 rc
        have hl : (⟨rc.2.val, rc.2.isLt.trans rc.1.isLt⟩ : Fin n) < rc.1 := rc.2.isLt
        simp [build, ne_of_lt hl, hl]
  have upperCard (n : ℕ) :
      Nat.card {L : GL (Fin n) F // L.val.IsUpperTriangular} =
        (Fintype.card F-1)^n * Fintype.card F^(∑ c : Fin n, c.val) := by
    rw [Nat.card_congr (upperCoordinates n), Nat.card_prod]
    simp [Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_units]
  have upperExponent : (∑ c : Fin (k+1), c.val) + (∑ c : Fin k, c.val) = k*k := by
    have sumSucc (n : ℕ) : (∑ c : Fin (n+1), c.val) = (∑ c : Fin n, c.val) + n := by
      rw [Fin.sum_univ_castSucc]
      simp
    have arithmetic (n : ℕ) :
        (∑ c : Fin (n+1), c.val) + (∑ c : Fin n, c.val) = n*n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sumSucc (n+1), sumSucc n]
        nlinarith [sumSucc n]
    exact arithmetic k

  let UpperFactors :=
    {L : GL (Fin (k+1)) F // L.val.IsUpperTriangular} ×
    {R : GL (Fin k) F // R.val.IsUpperTriangular}
  have upperFactorCount : Nat.card UpperFactors =
      Fintype.card F^(k*k) * (Fintype.card F-1)^(2*k+1) := by
    rw [Nat.card_prod, upperCard (k+1), upperCard k]
    rw [show 2*k+1 = (k+1)+k by omega, pow_add, ← pow_add]
    rw [← upperExponent]
    ring
  let NormalParameters := UpperFactors ×
    (Σ sigma : Equiv.Perm (Fin (k+1)), Σ pi : Equiv.Perm (Fin k), NormalizedCell sigma pi)
  let normalFormMap : NormalParameters → MaskParameters := fun z =>
    let L := z.1.1.val
    let R := z.1.2.val
    let g := z.2.2.2.val
    ⟨(L * g.1, g.2 * R), by
      have hh := triangularRespect (factorMap g) z.2.2.2.property.2.2
        L.val R.val z.1.1.property z.1.2.property
      simpa only [factorMap, Units.val_mul, Matrix.mul_assoc] using hh⟩
  have normalFormBijective : Function.Bijective normalFormMap := by
    constructor
    · intro z w hzw
      rcases z with ⟨⟨⟨L, hL⟩, ⟨R, hR⟩⟩, sigma, pi, ⟨A, B⟩, hA, hB, hmask⟩
      rcases w with ⟨⟨⟨L', hL'⟩, ⟨R', hR'⟩⟩, tau, rho, ⟨C, D⟩, hC, hD, hmask'⟩
      have hp : (L * A, B * R) = (L' * C, D * R') :=
        congrArg (fun v : MaskParameters => v.val) hzw
      have hl : L * A = L' * C := congrArg Prod.fst hp
      have hr : B * R = D * R' := congrArg Prod.snd hp
      let U := L⁻¹ * L'
      have hUi : L.inv.IsUpperTriangular := by
        letI := L.invertible
        change (↑(L⁻¹) : Matrix (Fin (k+1)) (Fin (k+1)) F).IsUpperTriangular
        rw [Matrix.GeneralLinearGroup.coe_inv]
        exact Matrix.blockTriangular_inv_of_blockTriangular hL
      have hU : U.val.IsUpperTriangular := hUi.mul hL'
      have hAC : A = U * C := by
        dsimp [U]
        rw [mul_assoc, ← hl, inv_mul_cancel_left]
      obtain ⟨hsigma, hAC', hUone⟩ := seUnique (k+1) sigma tau A C U hU hA hC hAC
      have hLL : L = L' := by
        have hh := congrArg (fun V => L * V) hUone
        simpa [U] using hh.symm
      let V := R * R'⁻¹
      have hRi : R'.inv.IsUpperTriangular := by
        letI := R'.invertible
        change (↑(R'⁻¹) : Matrix (Fin k) (Fin k) F).IsUpperTriangular
        rw [Matrix.GeneralLinearGroup.coe_inv]
        exact Matrix.blockTriangular_inv_of_blockTriangular hR'
      have hV : V.val.IsUpperTriangular := hR.mul hRi
      have hDB : D = B * V := by
        dsimp [V]
        rw [← mul_assoc, hr, mul_inv_cancel_right]
      have hflip : flipGL D = flipGL V * flipGL B := by
        rw [hDB, flipGLMul]
      obtain ⟨hperm, hDC, hVone⟩ := seUnique k (flipPerm rho) (flipPerm pi)
        (flipGL D) (flipGL B) (flipGL V) (flipUpper V hV)
        (flipShape rho D hD) (flipShape pi B hB) hflip
      have hBD : B = D := (flipGLInjective hDC).symm
      have hpi : pi = rho := by
        apply Equiv.ext
        intro a
        have hh := congrArg (fun p : Equiv.Perm (Fin k) => (p (rho a).rev).rev) hperm
        have ht := congrArg pi hh
        simpa [flipPerm] using ht
      have hRR : R = R' := by
        have hv : V = 1 := flipGLInjective (hVone.trans (by
          apply Units.ext
          exact (flipOne k).symm))
        have hh := congrArg (fun W => W * R') hv
        simpa [V] using hh
      cases hsigma
      cases hpi
      cases hAC'
      cases hBD
      cases hLL
      cases hRR
      rfl
    · intro g
      obtain ⟨p, L, C, D, hL, hG, hC, hD, hp, hbelow⟩ := upperPivotStep k g.val.1
      have leftCompletion :
          ∃ L' : GL (Fin (k+1)) F, ∃ sigma : Equiv.Perm (Fin (k+1)),
          ∃ A : GL (Fin (k+1)) F,
            L'.val.IsUpperTriangular ∧ sigma 0 = p ∧
              SEShape sigma A.val ∧ C = L' * A := by
        obtain ⟨L', A, sigma, hL', hCA, hA⟩ := leftSEExists (k+1) C
        have ha0 (t : Fin (k+1)) : A.val t 0 = if t = sigma 0 then 1 else 0 := by
          have hh := hA (sigma.symm t) 0
          have he : sigma.symm t = 0 ↔ t = sigma 0 := by
            constructor
            · intro he
              simpa using congrArg sigma he
            · intro he
              subst t
              simp
          simpa only [Equiv.apply_symm_apply, he, not_lt_zero, false_and, if_false] using hh
        have hLC (r : Fin (k+1)) : C.val r 0 = L'.val r (sigma 0) := by
          rw [hCA, Units.val_mul, Matrix.mul_apply]
          simp_rw [ha0]
          simp
        have hdiag : L'.val (sigma 0) (sigma 0) ≠ 0 := by
          have hu := isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units L')
          rw [Matrix.det_of_isUpperTriangular hL'] at hu
          exact Finset.prod_ne_zero_iff.mp hu (sigma 0) (Finset.mem_univ _)
        have hs : sigma 0 = p := by
          by_contra hn
          rw [← hLC, hC, if_neg hn] at hdiag
          exact hdiag rfl
        exact ⟨L', sigma, A, hL', hs, hA, hCA⟩
      have rightCompletion :
          ∃ pi : Equiv.Perm (Fin k), ∃ B R : GL (Fin k) F,
            NWRightShape pi B.val ∧ R.val.IsUpperTriangular ∧ g.val.2 = B * R := by
        let turn (M : Matrix (Fin k) (Fin k) F) :=
          M.transpose.submatrix Fin.revPerm Fin.revPerm
        have turnUnit (X : GL (Fin k) F) : IsUnit (turn X.val) := by
          apply (Matrix.isUnit_submatrix_equiv Fin.revPerm Fin.revPerm).mpr
          exact (Matrix.isUnit_transpose X.val).mpr X.isUnit
        let H : GL (Fin k) F := (turnUnit g.val.2).unit
        have hHv : H.val = turn g.val.2.val := IsUnit.unit_spec _
        obtain ⟨U, A, sigma, hU, hH, hA⟩ := leftSEExists k H
        let B : GL (Fin k) F := (turnUnit A).unit
        let R : GL (Fin k) F := (turnUnit U).unit
        have hBv : B.val = turn A.val := IsUnit.unit_spec _
        have hRv : R.val = turn U.val := IsUnit.unit_spec _
        let pi : Equiv.Perm (Fin k) :=
          Fin.revPerm.trans (sigma.symm.trans Fin.revPerm)
        refine ⟨pi, B, R, ?_, ?_, ?_⟩
        · intro i j
          have hh := hA (sigma.symm i.rev) (sigma.symm j.rev)
          simpa [hBv, turn, pi, Equiv.trans_apply, Fin.revPerm_apply,
            sigma.symm.injective.eq_iff, eq_comm, and_comm] using hh
        · intro r c hcr
          rw [hRv]
          change U.val c.rev r.rev = 0
          exact hU (Fin.rev_lt_rev.mpr hcr)
        · apply Units.ext
          rw [Units.val_mul, hBv, hRv]
          calc
            g.val.2.val = turn H.val := by
              rw [hHv]
              ext i j
              simp [turn]
            _ = turn (U.val * A.val) := by
              rw [← Units.val_mul, ← hH]
            _ = turn A.val * turn U.val := by
              dsimp [turn]
              rw [Matrix.transpose_mul, Matrix.submatrix_mul_equiv]
      obtain ⟨L', sigma, A, hL', hfirst, hA, hCA⟩ := leftCompletion
      obtain ⟨pi, B, R, hB, hR, hBR⟩ := rightCompletion
      have hLL : (L * L').val.IsUpperTriangular := by
        change (L.val * L'.val).IsUpperTriangular
        exact hL.mul hL'
      have hmasked : Respects lam mu (factorMap (A, B)) := by
        apply (triangularRespectIff (factorMap (A, B)) (L * L') R hLL hR).mp
        have hh := g.property
        change Respects lam mu (g.val.1.val * E0 F k * g.val.2.val,
          g.val.1.val * E1 F k * g.val.2.val) at hh
        rw [hG, hCA, hBR] at hh
        simpa only [factorMap, Units.val_mul, Matrix.mul_assoc] using hh
      refine ⟨((⟨L * L', hLL⟩, ⟨R, hR⟩),
        ⟨sigma, pi, ⟨(A, B), hA, hB, hmasked⟩⟩), ?_⟩
      apply Subtype.ext
      change ((L * L') * A, B * R) = g.val
      apply Prod.ext
      · rw [hG, hCA, mul_assoc]
      · exact hBR.symm
  have normalFormCount : Nat.card MaskParameters = Nat.card UpperFactors *
      ∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        Nat.card (NormalizedCell sigma pi) := by
    rw [← Nat.card_congr (Equiv.ofBijective normalFormMap normalFormBijective)]
    simp only [NormalParameters, Nat.card_prod, Nat.card_sigma]
  simp_rw [normalizedCoordinateReduction] at normalFormCount
  have literalEligibleSum :
      (∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        Nat.card ((LiteralSolutions (F := F) lam mu sigma pi))) =
      ∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        if D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi
        then Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) else 0 := by
    apply Finset.sum_congr rfl
    intro sigma _
    apply Finset.sum_congr rfl
    intro pi _
    split_ifs with hel
    · rfl
    · exact literalIneligibleCount sigma pi hel
  have literalCellCount (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k)) :
      Nat.card ((LiteralSolutions (F := F) lam mu sigma pi)) =
        if D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi
        then Fintype.card F ^
          (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
            (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi).toNat
        else 0 :=
    literal_cell_count_original_masks F k hk lam mu hlam hmu hml hlbound hmbound sigma pi
  have literalSolutionCount : Nat.card UpperFactors *
      ∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        Nat.card (LiteralSolutions (F := F) lam mu sigma pi) =
      (Fintype.card F ^ (k*k) * (Fintype.card F-1)^(2*k) *
      (∑ sigma : Equiv.Perm (Fin (k+1)), ∑ pi : Equiv.Perm (Fin k),
        if D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction.Eligible
          (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi
        then Fintype.card F ^
          (D5.S3.Combinatorics.Permutation.CoupledRepairedWeight.E
            (fun j => k+1-lam j) (fun j => k+1-mu j) sigma pi).toNat else 0)) * (Fintype.card F-1) := by
    simp_rw [upperFactorCount, literalCellCount]
    rw [pow_succ]
    ring
  apply Nat.mul_right_cancel qminusPositive
  rw [← actualParameterCount]
  exact normalFormCount.trans literalSolutionCount

end D5.S3.Combinatorics.Hypermatrix.MaskedTensorWeightedReduction
