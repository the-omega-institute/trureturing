/- GID: D5/S3/Zeros/GRH/New/Core/ClassCountBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Core/ClassCountBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Core.ClassCountBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Core/ClassCountBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.ClassReps
import D5.S3.Zeros.GRH.New.Filling.BoxPartition
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski
theorems (known result; see Lib.Adelic.Reduction.Defs).

This file: Crude explicit bound for the class number of the standard unimodular hermitian genus. -/

open NumberField Matrix Fintype DoubleCoset Units

/-- If N is a nonzero natural number in the different of E and f is the number of infinite
places, then the standard definite hermitian space of rank n has at most (1 + 2(6N(fn)²)³)^{4fn²}
classes Γ\G_f/K, K = `Kf` the stabiliser of the standard lattice. -/
lemma Space.card_classes_le {E} [Field E] [CMType E] {N}
    [NeZero N] (h : ↑N ∈ differentIdeal ℤ (𝓞 E)) {n} [Fintype n] : .card (StdClasses
    (Kf E n)) ≤ (1 + 2 * shortBasisConst E n N ^ 3) ^ (4 * numInfPlaces E * card n ^ 2) := by
  choose Y l hY using fun g : StdClasses (Kf E n) ↦ exists_short_basis_stdSpace h g.out
  let A g := g.out⁻¹.1 * (Y g).map (algebraMap ..); let G g := star (Y g) * 1 * Y g
  choose r o hr using exists_rat_near_of_mem_differentIdeal NeZero.out h 0
  let X g := (A g).inv.map r
  replace o g g' := mul_sub (A _).1 _ ((X g).map (↑)) ▸ (l g').mul (by tauto)
  refine Set.ncard_univ _ ▸ .trans_eq (ENat.toNat_le_of_le_natCast
    (mod_cast Filling.encard_integral_le (fun g (k, i, j) ↦
    (G g * cond k (X g) 1) i j) (shortBasisConst E n N ^ 3).cast_nonneg (fun g _ (k, i, j)
    ↦ ⟨?_, fun _ ↦ ?_⟩) fun g' _ g _ e ↦ Quotient.out_equiv_out.1 (rel_iff.2 ?_))) (by simp; ring)
  simp [G, mul_assoc]
  have b {B} := (U.gram_invariant g.out⁻¹ _ B ▸ ((l _).isInt_conjTranspose.mul .one).mul · i j)
  obtain ⟨⟨⟩⟩ := k, b (l _), b (by simpa [A, mul_assoc, ↓val_inv] using IsIntMatrix.one.sub (o g
    g)) <;> simp_all [mul_apply, ← algebraMap_mem_Ô]
  obtain ⟨⟨⟩⟩ := k, Inhabited.mk i <;> simp_all [mul_apply, X, G] <;>
  · repeat grw [norm_sum_le] <;> simp
    grw [hY, hY]; try grw [hr]
    simp; ring_nf; gcongr <;> norm_num [NeZero.one_le]
  simp [funext_iff, ext_iff] at e
  exact ⟨_, ⟨⟨_, gram_mul_of_gram_eq rfl (gram_inv_of_gram_eq e.1)⟩, rfl⟩, _, by
    simpa [mem_Kf, A, ↓val_inv, mul_assoc, (G _).mul_right_inj.1 (e.1 ▸ e.2)]
      using! IsIntMatrix.one.add ((o g g').sub (o g' g')), eq_mul_of_inv_mul_eq rfl⟩
