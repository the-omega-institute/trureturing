/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OddModeStraightening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite mixed mode rewrites for difference-one straightening of the actual odd sector. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField

/-! The local straightening identities for Miyamoto's Lemma 2.4
(arXiv:math/0209101), on the actual fixed-source action on negative parity. -/

set_option autoImplicit false

noncomputable section

open scoped VertexOperator BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddModeStraightening

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedMode)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open StateFieldResidueReconstruction (integerBinomial epsilon)

variable {D : LatticeData} {hu : IsUnit D.G.det}

private abbrev act (a : FixedCarrier D) (n : ℤ) :=
  (fixedParitySlice D hu (-1) a)[[n]]

private theorem finsum_mem {ι : Type*} (S : Submodule ℂ (paritySpace D hu (-1)))
    (f : ι → paritySpace D hu (-1)) (hf : Function.HasFiniteSupport f)
    (h : ∀ i, f i ∈ S) : (∑ᶠ i, f i) ∈ S := by
  classical
  rw [finsum_eq_sum _ hf]
  exact S.sum_mem fun i _ => h i

private theorem iterate (a b : FixedCarrier D) (u : paritySpace D hu (-1)) (q r : ℤ) :
    let first := fun i : ℕ => (((-1 : ℂ) ^ i) * integerBinomial r i) •
      act (hu := hu) a (r-i) (act b (q+i) u)
    let second := fun i : ℕ => (((-1 : ℂ) ^ i) * integerBinomial r i) •
      (epsilon r • act (hu := hu) b (q+r-i) (act a i u))
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      act (hu := hu) (fixedMode D a r b) q u = (∑ᶠ i, first i) - (∑ᶠ i, second i) := by
  have h := OriginalOrbifoldField.fixedParitySlice_borcherds D hu a b u 0 q r
  dsimp only at h ⊢
  have collapse :
      (∑ᶠ i : ℕ, integerBinomial 0 i •
        act (hu := hu) (fixedMode D a (r+i) b) (q-i) u) =
        act (hu := hu) (fixedMode D a r b) q u := by
    rw [finsum_eq_sum_of_support_subset (s := {0})]
    · simp [integerBinomial]
    · intro i hi
      by_contra hne
      have hi0 : i ≠ 0 := by simpa using hne
      exact hi (by simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi0)])
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_add] using h.2.1
  · simpa only [zero_add] using h.2.2.1
  · have law := h.2.2.2
    simp only [zero_add, smul_sub] at law
    rw [finsum_sub_distrib (by simpa only [zero_add] using h.2.1)
        (by simpa only [zero_add] using h.2.2.1), collapse] at law
    exact law

/-- A source C₂ letter at any mode is a finite sum of two-letter actions
whose indices sum to the original index minus two. -/
theorem minusTwo_mem_of_pairs (S : Submodule ℂ (paritySpace D hu (-1)))
    (a b : FixedCarrier D) (q : ℤ) (u : paritySpace D hu (-1))
    (h₁ : ∀ k l : ℤ, k + l = q - 2 → act a k (act b l u) ∈ S)
    (h₂ : ∀ k l : ℤ, k + l = q - 2 → act b k (act a l u) ∈ S) :
    act (fixedMode D a (-2) b) q u ∈ S := by
  obtain ⟨hf, hg, h⟩ := iterate a b u q (-2)
  rw [h]
  exact S.sub_mem
    (finsum_mem S _ hf fun i => S.smul_mem _ (h₁ _ _ (by omega)))
    (finsum_mem S _ hg fun i => S.smul_mem _ (S.smul_mem _ (h₂ _ _ (by omega))))

private theorem minus_one_weight (i : ℕ) :
    ((-1 : ℂ) ^ i) * integerBinomial (-1) i = 1 := by
  rw [integerBinomial, Ring.choose_neg (1 : ℤ) i]
  have index : (1 : ℤ) + i - 1 = (i : ℤ) := by omega
  rw [index, Ring.choose_natCast, Nat.choose_self]
  change (-1 : ℂ) ^ i * (((Int.negOnePow (i : ℤ)) • (1 : ℤ) : ℤ) : ℂ) = 1
  rw [Units.smul_def, smul_eq_mul, mul_one, Int.cast_negOnePow_natCast, ← mul_pow]
  norm_num

private theorem normal_product (a b : FixedCarrier D) (u : paritySpace D hu (-1)) (q : ℤ) :
    let first := fun i : ℕ => act (hu := hu) a (-1-i) (act b (q+i) u)
    let second := fun i : ℕ => act (hu := hu) b (q-1-i) (act a i u)
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      act (hu := hu) (fixedMode D a (-1) b) q u = (∑ᶠ i, first i) + (∑ᶠ i, second i) := by
  obtain ⟨hf, hg, he⟩ := iterate a b u q (-1)
  dsimp only
  have sign : epsilon (-1) = -1 := by norm_num [epsilon]
  simp only [minus_one_weight, one_smul, sign, neg_one_smul, ← sub_eq_add_neg] at hf hg he
  refine ⟨hf, hg.subset ?_, ?_⟩
  · intro i hi
    simpa only [Function.mem_support, neg_ne_zero] using hi
  · simpa only [finsum_neg_distrib, sub_neg_eq_add] using he

private theorem commutator (a b : FixedCarrier D) (u : paritySpace D hu (-1)) (p q : ℤ) :
    let correction := fun i : ℕ => integerBinomial p i •
      act (hu := hu) (fixedMode D a i b) (p + q - i) u
    Function.HasFiniteSupport correction ∧
      act a p (act b q u) - act b q (act a p u) = ∑ᶠ i, correction i := by
  have h := OriginalOrbifoldField.fixedParitySlice_borcherds D hu a b u p q 0
  dsimp only at h ⊢
  refine ⟨by simpa only [zero_add] using h.1, ?_⟩
  have law := h.2.2.2.symm
  rw [finsum_eq_single _ 0] at law
  · simpa only [integerBinomial, epsilon, Ring.choose_zero_right, Int.cast_one,
      pow_zero, zpow_zero, one_mul, one_smul, Nat.cast_zero, add_zero, sub_zero, zero_add]
      using law
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- Swapping two adjacent modes preserves membership modulo the nonnegative
source-mode corrections. -/
theorem swap_mem_iff (S : Submodule ℂ (paritySpace D hu (-1)))
    (a b : FixedCarrier D) (p q : ℤ) (u : paritySpace D hu (-1))
    (h : ∀ i : ℕ, act (fixedMode D a i b) (p + q - i) u ∈ S) :
    act a p (act b q u) ∈ S ↔ act b q (act a p u) ∈ S := by
  obtain ⟨hf, he⟩ := commutator a b u p q
  have diff : act a p (act b q u) - act b q (act a p u) ∈ S := by
    rw [he]
    exact finsum_mem S _ hf fun i => S.smul_mem _ (h i)
  constructor
  · intro hab
    simpa only [sub_sub_cancel] using S.sub_mem hab diff
  · intro hba
    simpa only [sub_add_cancel] using S.add_mem diff hba

private theorem pair_square_lt (j k l : ℤ) (hs : k + l = 2*j) (hk : k ≠ j) :
    2*j^2 < k^2 + l^2 := by
  have hl : l = 2*j - k := by omega
  rw [hl]
  have hpos : 0 < (k - j)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hk)
  calc
    2*j^2 < 2*j^2 + 2*(k-j)^2 := by linarith
    _ = k^2 + (2*j-k)^2 := by ring

private theorem remove_summand {ι : Type*} (S : Submodule ℂ (paritySpace D hu (-1)))
    (f : ι → paritySpace D hu (-1)) (hf : Function.HasFiniteSupport f) (t : ι)
    (h : (∑ᶠ i, f i) ∈ S) (hrest : ∀ i ≠ t, f i ∈ S) : f t ∈ S := by
  classical
  let indices := insert t hf.toFinset
  have hsum : (∑ i ∈ indices, f i) ∈ S := by
    rw [← finsum_eq_sum_of_support_subset f]
    · exact h
    · intro i hi
      exact Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hi)
  have ht : t ∈ indices := Finset.mem_insert_self _ _
  rw [← Finset.sum_erase_add _ _ ht] at hsum
  have hr : (∑ i ∈ indices.erase t, f i) ∈ S :=
    S.sum_mem fun i hi => hrest i (Finset.mem_erase.mp hi).1
  simpa using S.sub_mem hsum hr

/-- An adjacent equal-index pair can be isolated against the shorter normal
product and distinct pairs of the same index sum and strictly larger square sum. -/
theorem duplicate_mem_of_shorter_and_larger (S : Submodule ℂ (paritySpace D hu (-1)))
    (a b : FixedCarrier D) (j : ℤ) (u : paritySpace D hu (-1))
    (h₁ : act (fixedMode D (if j < 0 then a else b) (-1) (if j < 0 then b else a))
      (2*j+1) u ∈ S)
    (h₂ : ∀ k l : ℤ, k + l = 2*j → 2*j^2 < k^2 + l^2 →
      act a k (act b l u) ∈ S)
    (h₃ : ∀ k l : ℤ, k + l = 2*j → 2*j^2 < k^2 + l^2 →
      act b k (act a l u) ∈ S) : act a j (act b j u) ∈ S := by
  by_cases hj : j < 0
  · obtain ⟨hf, hg, h⟩ := normal_product a b u (2*j+1)
    simp only [ite_eq_left hj, h] at h₁
    let t := (-1-j).toNat
    have ht : (t : ℤ) = -1-j := Int.toNat_of_nonneg (by omega)
    have hsecond := finsum_mem S _ hg fun i => h₃ _ _ (by omega)
      (pair_square_lt j _ _ (by omega) (by omega))
    have hfirst := remove_summand S _ hf t
      (by simpa using S.sub_mem h₁ hsecond)
      (fun i hi => h₂ _ _ (by omega) (pair_square_lt j _ _ (by omega) (by omega)))
    change act a (-1-(t : ℤ)) (act b (2*j+1+t) u) ∈ S at hfirst
    simpa only [show -1-(t : ℤ) = j by omega, show 2*j+1+(t : ℤ) = j by omega]
      using hfirst
  · obtain ⟨hf, hg, h⟩ := normal_product b a u (2*j+1)
    simp only [ite_eq_right hj, h] at h₁
    let t := j.toNat
    have ht : (t : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hfirst := finsum_mem S _ hf fun i => h₃ _ _ (by omega)
      (pair_square_lt j _ _ (by omega) (by omega))
    have hsecond := remove_summand S _ hg t
      (by simpa [add_comm] using S.sub_mem h₁ hfirst)
      (fun i hi => h₂ _ _ (by omega) (pair_square_lt j _ _ (by omega) (by omega)))
    change act a (2*j+1-1-(t : ℤ)) (act b t u) ∈ S at hsecond
    simpa only [ht, show 2*j+1-1-j = j by omega] using hsecond

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddModeStraightening
