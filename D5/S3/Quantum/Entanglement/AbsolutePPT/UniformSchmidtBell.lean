/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell
   mirror-E: none(waiver:symbolic-arbitrary-dimension-construction)
   anchors: []
   utility: none
   digest: Arbitrary-dimension Bell rotations realize every independently labelled Schmidt matrix from literal APPT. -/

/- Uncompiled source candidate: an arbitrary-r Bell rotation as actual block
   matrices, its principal PT compression, and the literal assigned-K bridge.
   No positive-definiteness, simple-spectrum or nonnegative-vector premise. -/

/-
utility:none, declaration-by-declaration semantic scope (CLAUDE.md §3.3):
pairMatrix, pairMatrix_unitary, pairUnitary, bellEquiv, bellUnitary:
  Uniform block-matrix and equivalence constructions for arbitrary r; unitarity is proved symbolically rather than by enumerating a bounded dimension.
pair_conjugate_diagonal, pack, bell_conjugate, bell_pt_principal:
  Universal symbolic diagonal and partial-transpose identities for arbitrary real or complex inputs; the coefficient 1/2 normalizes all blocks rather than supplying a certified numerical instance.
actual_pack, literal_assignment_psd:
  Identities and APPT implications for every independent pool permutation in arbitrary permitted local dimensions; no checker, supplied numerical threshold or standalone finite certificate is delivered.
All groups avoid bounded-enumeration, checker, numeric-reduction and
certified-instance as their primary delivered content. Utility semantics
remain subject to independent review; the header does not prove acceptance.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtSpectrum

set_option autoImplicit false
open Matrix
open scoped ComplexOrder BigOperators

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell
open UniformSchmidtCorner UniformSchmidtIncidence UniformSchmidtSpectrum
open QutritPerturbationAttainment QutritSpectralReduction
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
noncomputable section

def pairMatrix (r : ℕ) : Matrix (Edge r ⊕ Edge r) (Edge r ⊕ Edge r) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • fromBlocks (1 : Matrix (Edge r) (Edge r) ℂ) 1 1 (-1)

theorem pairMatrix_unitary (r : ℕ) : pairMatrix r ∈ unitaryGroup _ ℂ := by
  rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [pairMatrix, conjTranspose_smul, c_star, fromBlocks_conjTranspose,
    conjTranspose_one, conjTranspose_neg, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, c_square, fromBlocks_multiply, one_mul, mul_one, neg_mul,
    mul_neg, neg_neg]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply]
  all_goals split_ifs <;> norm_num

def pairUnitary (r : ℕ) : unitaryGroup (Edge r ⊕ Edge r) ℂ :=
  ⟨pairMatrix r, pairMatrix_unitary r⟩

def bellEquiv (r : ℕ) : ((Edge r ⊕ Edge r) ⊕ Fin r) ≃ (Fin r × Fin r) :=
  (Equiv.sumComm (Edge r ⊕ Edge r) (Fin r)).trans (slotEquiv r)

/-- Identity on diagonal singletons, a Hadamard block on each edge pair. -/
def bellUnitary (r : ℕ) : unitaryGroup (Fin r × Fin r) ℂ :=
  extendUnitaryAlong (bellEquiv r) (pairUnitary r)

theorem pair_conjugate_diagonal {r : ℕ} (u v : Edge r → ℂ) :
    (pairUnitary r : Matrix _ _ ℂ) * diagonal (Sum.elim u v) *
      (pairUnitary r : Matrix _ _ ℂ)ᴴ =
    fromBlocks (diagonal (fun e => (u e + v e) / 2))
      (diagonal (fun e => (u e - v e) / 2))
      (diagonal (fun e => (u e - v e) / 2))
      (diagonal (fun e => (u e + v e) / 2)) := by
  change pairMatrix r * diagonal (Sum.elim u v) * (pairMatrix r)ᴴ = _
  rw [← fromBlocks_diagonal]
  simp only [pairMatrix, conjTranspose_smul, c_star, fromBlocks_conjTranspose,
    conjTranspose_one, conjTranspose_neg, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, c_square, fromBlocks_multiply, one_mul, mul_one, neg_mul,
    mul_neg, neg_neg, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  all_goals split_ifs <;> ring

def pack {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    Fin r × Fin r → ℂ :=
  fun q => Sum.elim
    (Sum.elim (fun e => (b (.inr e) : ℂ)) (fun e => (t e : ℂ)))
    (fun i => (b (.inl i) : ℂ)) ((bellEquiv r).symm q)

theorem bell_conjugate {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    (bellUnitary r : Matrix _ _ ℂ) * diagonal (pack t b) *
      (bellUnitary r : Matrix _ _ ℂ)ᴴ =
    (fromBlocks
      (fromBlocks
        (diagonal (fun e => ((b (.inr e) + t e : ℝ) : ℂ) / 2))
        (diagonal (fun e => ((b (.inr e) - t e : ℝ) : ℂ) / 2))
        (diagonal (fun e => ((b (.inr e) - t e : ℝ) : ℂ) / 2))
        (diagonal (fun e => ((b (.inr e) + t e : ℝ) : ℂ) / 2)))
      0 0 (diagonal (fun i => (b (.inl i) : ℂ)))).submatrix
        (bellEquiv r).symm (bellEquiv r).symm := by
  unfold bellUnitary pack
  rw [extendUnitaryAlong_diagonal, pair_conjugate_diagonal]
  push_cast <;> rfl

/-- Entrywise principal compression; the proof splits i=j, i<j, j<i,
never enumerates Fin r. This is the central uncompiled elaboration target. -/
theorem bell_pt_principal {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) :
    (partialTranspose ((bellUnitary r : Matrix _ _ ℂ) * diagonal (pack t b) *
      (bellUnitary r : Matrix _ _ ℂ)ᴴ)).submatrix
        (fun i => (i, i)) (fun i => (i, i)) =
      (1 / 2 : ℂ) • (K t b).map Complex.ofReal := by
  rw [bell_conjugate]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTranspose, Matrix.submatrix_apply, bellEquiv, slotEquiv,
      coordSlot, Matrix.smul_apply, Matrix.map_apply, K]
    <;> ring
  · have hji := Ne.symm hij
    by_cases hlt : i < j
    · have hjlt : ¬j < i := not_lt_of_gt hlt
      simp [partialTranspose, Matrix.submatrix_apply, bellEquiv, slotEquiv,
        coordSlot, hij, hji, hlt, hjlt, edge, K, Matrix.smul_apply,
        Matrix.map_apply, Matrix.diagonal_apply]
      <;> ring
    · have hjlt : j < i := by omega
      simp [partialTranspose, Matrix.submatrix_apply, bellEquiv, slotEquiv,
        coordSlot, hij, hji, hlt, hjlt, edge, K, Matrix.smul_apply,
        Matrix.map_apply, Matrix.diagonal_apply]
      <;> ring

theorem actual_pack {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ)
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    (fun q => (l (label hN π σ q) : ℂ)) =
      pack (fun e => l (assignedTopIndex hN π e))
        (fun p => l (assignedBottomIndex hN σ p)) := by
  funext q
  obtain ⟨z, rfl⟩ := (slotEquiv r).surjective q
  rcases z with i | (e | e) <;>
    simp [label, bellSlotsEquiv, pack, bellEquiv, Function.comp_def]

/-- The actual physical bridge: literal APPT of THIS diagonal spectrum forces
EVERY independently permuted Schmidt K to be PSD, in arbitrary local dimensions.
This theorem has no assignment-PSD premise. Uncompiled candidate only. -/
theorem literal_assignment_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) :
    let hN : a r + b r ≤ m * n :=
      (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
    (assignedK hN l π σ).PosSemidef := by
  dsimp only
  let hN : a r + b r ≤ m * n :=
    (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn)
  have hp := actual_corner_psd hm hn e l h π σ (bellUnitary r)
  dsimp only at hp
  rw [actual_pack hN l π σ] at hp
  have hc := hp.submatrix (fun i : Fin r => (i, i))
  rw [bell_pt_principal] at hc
  have hs := hc.smul (show (0 : ℂ) ≤ 2 by norm_num)
  have hcomplex : ((assignedK hN l π σ).map Complex.ofReal).PosSemidef := by
    convert hs using 1 <;> ext i j <;> simp [assignedK]
  exact real_psd_of_complex _ hcomplex

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell
