/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathReturningBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/WeightedPathReturningBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal matrix units in the returning blocks of the Perron path tower. -/

import D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace

namespace D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks

variable {L : Type*} [Fintype L] [DecidableEq L]
attribute [local instance] Classical.propDecidable
local instance (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

/-- One literal path matrix unit, zero in every other endpoint block. -/
def blockUnit (R : L → L → Prop) (n : ℕ) (s t : L)
    (x y : LegalPath R n s t) : C R n s :=
  Pi.single t (Matrix.single x y 1)

private theorem append_ne (R : L → L → Prop) (n : ℕ) (s a b u : L)
    (ha : R a u) (hb : R b u) (hab : a ≠ b)
    (x : LegalPath R n s a) (y : LegalPath R n s b) :
    append R n s a u ha x ≠ append R n s b u hb y := by
  intro h
  have h' := congrArg (fun z : LegalPath R (n + 1) s u =>
    z.val (Fin.last n).castSucc) h
  simp only [append, Fin.snoc_castSucc, x.property.2.1, y.property.2.1] at h'
  exact hab h'

private theorem iota_unit (R : L → L → Prop) (n : ℕ) (s a u : L)
    (ha : R a u) (x y : LegalPath R n s a) :
    iota R n s (blockUnit R n s a x y) u =
      Matrix.single (append R n s a u ha x) (append R n s a u ha y) 1 := by
  classical
  ext p q
  obtain ⟨⟨⟨b, hb⟩, p⟩, rfl⟩ := (splitPath R n s u).symm.surjective p
  obtain ⟨⟨⟨c, hc⟩, q⟩, rfl⟩ := (splitPath R n s u).symm.surjective q
  change iota R n s (blockUnit R n s a x y) u
      (append R n s b u hb p) (append R n s c u hc q) =
    Matrix.single (append R n s a u ha x) (append R n s a u ha y) 1
      (append R n s b u hb p) (append R n s c u hc q)
  by_cases hbc : b = c
  · subst c
    rw [iota_append_entry]
    by_cases hab : a = b
    · subst b
      simp only [blockUnit, Pi.single_eq_same, Matrix.single_apply,
        (append_isInjective R n s a u ha).eq_iff]
    · simp only [blockUnit, Pi.single_eq_of_ne (Ne.symm hab), Matrix.zero_apply]
      exact (Matrix.single_apply_of_row_ne (append_ne R n s a b u ha hb hab x p)
        _ _ _).symm
  · have hidx : (⟨b, hb⟩ : {t : L // R t u}) ≠ ⟨c, hc⟩ := by
      intro h
      exact hbc (congrArg Subtype.val h)
    simp only [iota, Matrix.submatrix_apply, split_append_coordinates,
      Matrix.blockDiagonal'_apply_ne _ _ _ hidx]
    by_cases hab : a = b
    · subst b
      exact (Matrix.single_apply_of_col_ne _ _
        (append_ne R n s a c u ha hc hbc y q) _).symm
    · exact (Matrix.single_apply_of_row_ne (append_ne R n s a b u ha hb hab x p)
        _ _ _).symm

private theorem iota_unit_zero (R : L → L → Prop) (n : ℕ) (s a u : L)
    (ha : ¬ R a u) (x y : LegalPath R n s a) :
    iota R n s (blockUnit R n s a x y) u = 0 := by
  classical
  ext p q
  obtain ⟨⟨⟨b, hb⟩, p⟩, rfl⟩ := (splitPath R n s u).symm.surjective p
  obtain ⟨⟨⟨c, hc⟩, q⟩, rfl⟩ := (splitPath R n s u).symm.surjective q
  change iota R n s (blockUnit R n s a x y) u
      (append R n s b u hb p) (append R n s c u hc q) = 0
  by_cases hbc : b = c
  · subst c
    rw [iota_append_entry]
    have hba : b ≠ a := by rintro rfl; exact ha hb
    simp [blockUnit, Pi.single_eq_of_ne hba]
  · have hidx : (⟨b, hb⟩ : {t : L // R t u}) ≠ ⟨c, hc⟩ := by
      intro h
      exact hbc (congrArg Subtype.val h)
    simp only [iota, Matrix.submatrix_apply, split_append_coordinates,
      Matrix.blockDiagonal'_apply_ne _ _ _ hidx, Matrix.zero_apply]

private theorem return_kernel (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (m : ℕ) (s v a c u : L) (hva : R v a) (hvc : R v c)
    (hau : R a u) (hcu : R c u) (r : LegalPath R m s v) :
    lastProjection R d δ (m + 1) (by omega) s u
      (append R (m + 1) s a u hau (append R m s v a hva r))
      (append R (m + 1) s c u hcu (append R m s v c hvc r)) =
      if v = u then ((Real.sqrt (d a * d c) / (δ * d v) : ℝ) : ℂ) else 0 := by
  let p := append R (m + 1) s a u hau (append R m s v a hva r)
  let q := append R (m + 1) s c u hcu (append R m s v c hvc r)
  have hp : p.val ⟨m + 1, by omega⟩ = a := by
    change p.val (Fin.last (m + 1)).castSucc = a
    simp [p, append]
  have hq : q.val ⟨m + 1, by omega⟩ = c := by
    change q.val (Fin.last (m + 1)).castSucc = c
    simp [q, append]
  have hv : p.val ⟨(m + 1) - 1, by omega⟩ = v := by
    change p.val ((Fin.last m).castSucc).castSucc = v
    simp [p, append, r.property.2.1]
  have hu : p.val ⟨m + 1 + 1, by omega⟩ = u := by
    change p.val (Fin.last (m + 1 + 1)) = u
    simp [p, append]
  have away : ∀ k : Fin (m + 1 + 1 + 1), k.val ≠ m + 1 → p.val k = q.val k := by
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro _
      simp [p, q, append]
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · intro h
        exact (h rfl).elim
      · intro _
        simp [p, q, append]
  change pathProjection R d δ (m + 1 + 1) s u (m + 1) _ p q = _
  simp only [pathProjection, hp, hq, hv, hu]
  by_cases he : v = u
  · rw [if_pos ⟨away, he⟩, if_pos he]
  · rw [if_neg (fun hh => he hh.2), if_neg he]

/-- Two preceding path matrix units isolate exactly one returning endpoint matrix unit. -/
theorem returning_matrix_unit_factorization (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (m : ℕ) (s v a c : L) (hva : R v a) (hvc : R v c)
    (hav : R a v) (hcv : R c v) (r : LegalPath R m s v)
    (x : LegalPath R (m + 1) s a) (y : LegalPath R (m + 1) s c) :
    iota R (m + 1) s (blockUnit R (m + 1) s a x (append R m s v a hva r)) *
        lastProjection R d δ (m + 1) (by omega) s *
        iota R (m + 1) s (blockUnit R (m + 1) s c (append R m s v c hvc r) y) =
      ((Real.sqrt (d a * d c) / (δ * d v) : ℝ) : ℂ) •
        blockUnit R (m + 1 + 1) s v
          (append R (m + 1) s a v hav x) (append R (m + 1) s c v hcv y) := by
  classical
  funext u
  change iota R (m + 1) s _ u * lastProjection R d δ (m + 1) _ s u *
      iota R (m + 1) s _ u = _
  by_cases hau : R a u
  · by_cases hcu : R c u
    · rw [iota_unit R (m + 1) s a u hau, iota_unit R (m + 1) s c u hcu,
        Matrix.single_mul_mul_single, return_kernel]
      by_cases hvu : v = u
      · subst u
        simp [blockUnit, Matrix.smul_single]
      · simp [hvu, blockUnit, Pi.single_eq_of_ne (Ne.symm hvu)]
    · rw [iota_unit_zero R (m + 1) s c u hcu, mul_zero]
      have huv : u ≠ v := by rintro rfl; exact hcu hcv
      simp [blockUnit, Pi.single_eq_of_ne huv]
  · rw [iota_unit_zero R (m + 1) s a u hau, zero_mul, zero_mul]
    have huv : u ≠ v := by rintro rfl; exact hau hav
    simp [blockUnit, Pi.single_eq_of_ne huv]

/-- The linear space generated by sandwiching the last projection with the preceding tower. -/
def returningSpan (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (m : ℕ) (s : L) :
    Submodule ℂ (C R (m + 1 + 1) s) :=
  Submodule.span ℂ {Z | ∃ X Y : C R (m + 1) s,
    Z = iota R (m + 1) s X * lastProjection R d δ (m + 1) (by omega) s *
      iota R (m + 1) s Y}

/-- All returning endpoint blocks, with literal zero on every other block. -/
def returningBlocks (R : L → L → Prop) (m : ℕ) (s : L) :
    Submodule ℂ (C R (m + 1 + 1) s) where
  carrier := {Z | ∀ v, ¬ Nonempty (LegalPath R m s v) → Z v = 0}
  zero_mem' := by intro v _; rfl
  add_mem' := by
    intro X Y hX hY v hv
    change X v + Y v = 0
    rw [hX v hv, hY v hv, add_zero]
  smul_mem' := by
    intro c X hX v hv
    change c • X v = 0
    rw [hX v hv, smul_zero]

private theorem projection_block_zero (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (m : ℕ) (s v : L) (h : ¬ Nonempty (LegalPath R m s v)) :
    lastProjection R d δ (m + 1) (by omega) s v = 0 := by
  classical
  ext x y
  unfold lastProjection pathProjection
  split_ifs with hback
  · have hv : x.val ((Fin.last m).castSucc).castSucc = v := by
      have hi : (⟨(m + 1) - 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
          ((Fin.last m).castSucc).castSucc := by
        apply Fin.ext
        simp only [Fin.val_mk, Fin.val_castSucc, Fin.val_last]
        omega
      have hj : (⟨m + 1 + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
          Fin.last (m + 1 + 1) := by apply Fin.ext; rfl
      have he : x.val ((Fin.last m).castSucc).castSucc =
          x.val (Fin.last (m + 1 + 1)) := by
        simpa only [hi, hj] using hback.2
      exact he.trans x.property.2.1
    apply (h ?_).elim
    refine ⟨⟨fun i => x.val i.castSucc.castSucc, ?_, hv, ?_⟩⟩
    · simpa using x.property.1
    · intro i
      simpa only [← Fin.castSucc_succ] using x.property.2.2 i.castSucc.castSucc
  · rfl

private theorem returning_unit_mem (R : L → L → Prop) (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (s v : L) (r : LegalPath R m s v)
    (p q : LegalPath R (m + 1 + 1) s v) :
    blockUnit R (m + 1 + 1) s v p q ∈ returningSpan R d δ m s := by
  classical
  obtain ⟨⟨⟨a, hav⟩, x⟩, rfl⟩ := (splitPath R (m + 1) s v).symm.surjective p
  obtain ⟨⟨⟨c, hcv⟩, y⟩, rfl⟩ := (splitPath R (m + 1) s v).symm.surjective q
  change blockUnit R (m + 1 + 1) s v
      (append R (m + 1) s a v hav x) (append R (m + 1) s c v hcv y) ∈ _
  let X := blockUnit R (m + 1) s a x (append R m s v a (hR.symm a v hav) r)
  let Y := blockUnit R (m + 1) s c (append R m s v c (hR.symm c v hcv) r) y
  let α : ℂ := ((Real.sqrt (d a * d c) / (δ * d v) : ℝ) : ℂ)
  have hα : α ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (mul_pos (hd a) (hd c))))
      (ne_of_gt (mul_pos hδ (hd v)))
  have hf : iota R (m + 1) s X * lastProjection R d δ (m + 1) (by omega) s *
      iota R (m + 1) s Y = α • blockUnit R (m + 1 + 1) s v
        (append R (m + 1) s a v hav x) (append R (m + 1) s c v hcv y) :=
    returning_matrix_unit_factorization R d δ m s v a c
      (hR.symm a v hav) (hR.symm c v hcv) hav hcv r x y
  have hmem : iota R (m + 1) s X * lastProjection R d δ (m + 1) (by omega) s *
      iota R (m + 1) s Y ∈ returningSpan R d δ m s :=
    Submodule.subset_span ⟨X, Y, rfl⟩
  have hs := (returningSpan R d δ m s).smul_mem α⁻¹ hmem
  rw [hf, smul_smul, inv_mul_cancel₀ hα, one_smul] at hs
  exact hs

/-- The last projection and the preceding full algebra span exactly the returning endpoint blocks. -/
theorem weighted_path_returning_blocks (R : L → L → Prop) (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (s : L) : returningSpan R d δ m s = returningBlocks R m s := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro Z ⟨X, Y, rfl⟩ v hv
    change iota R (m + 1) s X v * lastProjection R d δ (m + 1) _ s v *
      iota R (m + 1) s Y v = 0
    rw [projection_block_zero R d δ m s v hv, mul_zero, zero_mul]
  · intro Z hZ
    rw [← Finset.univ_sum_single Z]
    apply Submodule.sum_mem
    intro v _
    by_cases hr : Nonempty (LegalPath R m s v)
    · obtain ⟨r⟩ := hr
      let S : Matrix (LegalPath R (m + 1 + 1) s v)
          (LegalPath R (m + 1 + 1) s v) ℂ →ₗ[ℂ] C R (m + 1 + 1) s :=
        LinearMap.single ℂ
          (fun t : L => Matrix (LegalPath R (m + 1 + 1) s t)
            (LegalPath R (m + 1 + 1) s t) ℂ) v
      have hmat : Z v = ∑ p, ∑ q, (Z v p q) • Matrix.single p q 1 := by
        simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
          Matrix.matrix_eq_sum_single (Z v)
      change S (Z v) ∈ returningSpan R d δ m s
      rw [hmat, map_sum]
      apply Submodule.sum_mem
      intro p _
      rw [map_sum]
      apply Submodule.sum_mem
      intro q _
      rw [map_smul]
      apply Submodule.smul_mem
      exact returning_unit_mem R hR d hd δ hδ m s v r p q
    · have hz : Z v = 0 := hZ v hr
      simp only [hz, Pi.single_zero]
      exact (returningSpan R d δ m s).zero_mem

#print axioms returning_matrix_unit_factorization
#print axioms weighted_path_returning_blocks

end D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
