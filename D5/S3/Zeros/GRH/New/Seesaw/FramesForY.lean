/- GID: D5/S3/Zeros/GRH/New/Seesaw/FramesForY
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/FramesForY
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.FramesForY. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/FramesForY.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.LatticeAndTorsionDefs
import D5.S3.Zeros.GRH.New.Seesaw.IndexTypes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Glued lattice is unimodular and real frames exist for the spaces Y_j. -/


open Matrix Fintype
variable {R X ι} [Fintype X] [Fintype ι] {s N : ℕ} [CommRing R] (e : (X ⊕ Unit) ⊕ Fin s ≃ ι)
attribute [local simp] gradedGram Matrix.mul_apply diagonal gradedLatticeBasis signMatrix
  single_apply negCount
attribute [local simp ←] ext_iff submatrix_map

lemma isUnimodular_gradedLatticeBasis_gram {S O} [CommRing S] [StarRing R] {f : S →+* R} {a π :
  Rˣ} {u} (hN : f N = π * star ↑π) : IsUnimodular O
  ((gradedLatticeBasis e a π u)ᴴ * (gradedGram e ↑N).map f * gradedLatticeBasis e a π u) := by
  have (c : Fin s) : c = c.rev ↔ if _ : Odd s then c = ⟨s / 2, by grind⟩ else False := by grind
  let v := e (.inl (.inr ()))
  let H (p q : O) := gradedGram e p + ∑ b, ite (b = b.rev)
    (.single v v (q - 1) - .single v (e (.inr b)) 1 - .single (e (.inr b)) v 1) 0
  refine Eq.subst ?_ ⟨?_, _, ⟨.mkOfMulEqOne (H N 0) (H 0 N) ?_, rfl⟩, rfl⟩ <;> by_cases Odd s <;>
    simp [H, v, *, reindex_equiv e, ← e.sum_comp, apply_ite star,
    apply_ite Subtype.val] <;> grind [star_mul, star_one, Units.mul_inv, u.2.1, map_natCast]

/-- Let N > 0 be an integer, φ: R → ℂ a ring homomorphism, ε signs with exactly ⌊(s+1)/2⌋ minus
signs. Some complex matrix y has yᴴφ(J)y = diag(ε), J the Gram matrix `gradedGram` of X ⊕ point
plus string, and yᴴy = 1 if N = 1. -/
lemma exists_frame_gradedGram (φ : R →+* ℂ) (hN : 0 < N) {ε} (h : negCount ε = (s + 1) / 2) :
    ∃ y, yᴴ * (gradedGram e ↑N).map φ * y = signMatrix ε ∧ (N = 1 → yᴴ * y = 1) := by
  let σ (b : Fin s) := ite (b < (s + 1) / 2) (-1) (1 : ℤˣ)
  obtain ⟨f, rfl⟩ := exists_equiv_of_card_neg (b := 1 ⊕ᵥ σ) (card_congr e.symm) (h.trans (by
    simp (disch := lia) [σ, ↓negCount_sumElim, card_fin_lt_of_le]))
  use gradedBlocks e f.symm 1 (of fun a b ↦ ite (a = b) ↑(σ b / √2) 0 + ite (a = b.rev) ↑(√2⁻¹ + ite
    (a = b) √N⁻¹ 0) 0), ?_, (·.symm ▸ ?_) <;> simp [σ, reindex_equiv f.symm, mul_add, apply_ite
    star, apply_ite φ] <;> intros <;> split_ifs <;> (try lia) <;> norm_cast <;> grind [Nat.cast_pos]
