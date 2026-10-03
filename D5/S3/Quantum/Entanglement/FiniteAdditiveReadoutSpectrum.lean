/- GID: D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite additive readouts give block matrices and flat reduced spectra. -/

import D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

/- The finite-group state, source blocks, projections, eigenspaces and dimensions,
singular-value list, and entropy are computed from the actual readouts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum

open D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

open scoped BigOperators Matrix ComplexOrder MatrixOrder CStarAlgebra
open scoped Classical
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

variable {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
  [Fintype G] [Fintype A] [Fintype B]
  [DecidableEq G] [DecidableEq A] [DecidableEq B]


/-- Both actual reductions have exactly their block-column and kernel eigenspaces. -/
theorem actual_eigenspaces (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    (∀ x : A → ℂ, (actualReducedA alpha beta).mulVec x =
        (blockWeight alpha beta : ℂ) • x ↔
      ∃ y : BlockQuotient alpha beta → ℂ, (leftVectors alpha beta).mulVec y = x) ∧
    (∀ x : A → ℂ, (actualReducedA alpha beta).mulVec x = 0 ↔
      ((leftVectors alpha beta)ᴴ).mulVec x = 0) ∧
    (∀ x : B → ℂ, (actualReducedB alpha beta).mulVec x =
        (blockWeight alpha beta : ℂ) • x ↔
      ∃ y : BlockQuotient alpha beta → ℂ, (rightVectors alpha beta).mulVec y = x) ∧
    (∀ x : B → ℂ, (actualReducedB alpha beta).mulVec x = 0 ↔
      ((rightVectors alpha beta)ᴴ).mulVec x = 0) ∧
    Module.finrank ℂ (Module.End.eigenspace (actualReducedA alpha beta).mulVecLin
      (blockWeight alpha beta : ℂ)) = Fintype.card (BlockQuotient alpha beta) ∧
    Module.finrank ℂ (Module.End.eigenspace (actualReducedA alpha beta).mulVecLin 0) =
      Fintype.card A - Fintype.card (BlockQuotient alpha beta) ∧
    Module.finrank ℂ (Module.End.eigenspace (actualReducedB alpha beta).mulVecLin
      (blockWeight alpha beta : ℂ)) = Fintype.card (BlockQuotient alpha beta) ∧
    Module.finrank ℂ (Module.End.eigenspace (actualReducedB alpha beta).mulVecLin 0) =
      Fintype.card B - Fintype.card (BlockQuotient alpha beta) := by
  classical
  obtain ⟨hU, hV, _, hredA, hredB, _, _, _, _⟩ :=
    actual_block_matrices alpha beta hpair
  let Q := BlockQuotient alpha beta
  let U := leftVectors alpha beta
  have hw : (blockWeight alpha beta : ℂ) ≠ 0 := by
    have hKA : (0 : ℝ) < Fintype.card alpha.ker := by exact_mod_cast Fintype.card_pos
    have hKB : (0 : ℝ) < Fintype.card beta.ker := by exact_mod_cast Fintype.card_pos
    have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hwR : blockWeight alpha beta ≠ 0 :=
      (div_pos (mul_pos hKA hKB) hN).ne'
    exact_mod_cast hwR
  have characterize (X : Matrix A Q ℂ) (hX : Xᴴ * X = 1)
      (D : Matrix A A ℂ) (hD : D = (blockWeight alpha beta : ℂ) • (X * Xᴴ))
      (x : A → ℂ) :
      (D *ᵥ x = (blockWeight alpha beta : ℂ) • x ↔
        ∃ y : Q → ℂ, X *ᵥ y = x) ∧
      (D *ᵥ x = 0 ↔ Xᴴ *ᵥ x = 0) := by
    constructor
    · constructor
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ] at hx
        exact ⟨Xᴴ *ᵥ x, hw.isUnit.smul_left_cancel.mp hx⟩
      · rintro ⟨y, rfl⟩
        rw [hD, Matrix.smul_mulVec,
          ← Matrix.mulVec_mulVec (X *ᵥ y) X Xᴴ,
          Matrix.mulVec_mulVec y Xᴴ X, hX, Matrix.one_mulVec]
    · constructor
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ] at hx
        have hxy : X *ᵥ (Xᴴ *ᵥ x) = 0 := (smul_eq_zero.mp hx).resolve_left hw
        have hy := congrArg (fun z => Xᴴ *ᵥ z) hxy
        simpa only [Matrix.mulVec_mulVec (Xᴴ *ᵥ x) Xᴴ X, hX,
          Matrix.one_mulVec, Matrix.mulVec_zero] using hy
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ, hx,
          Matrix.mulVec_zero, smul_zero]
  have characterizeB (X : Matrix B Q ℂ) (hX : Xᴴ * X = 1)
      (D : Matrix B B ℂ) (hD : D = (blockWeight alpha beta : ℂ) • (X * Xᴴ))
      (x : B → ℂ) :
      (D *ᵥ x = (blockWeight alpha beta : ℂ) • x ↔
        ∃ y : Q → ℂ, X *ᵥ y = x) ∧
      (D *ᵥ x = 0 ↔ Xᴴ *ᵥ x = 0) := by
    constructor
    · constructor
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ] at hx
        exact ⟨Xᴴ *ᵥ x, hw.isUnit.smul_left_cancel.mp hx⟩
      · rintro ⟨y, rfl⟩
        rw [hD, Matrix.smul_mulVec,
          ← Matrix.mulVec_mulVec (X *ᵥ y) X Xᴴ,
          Matrix.mulVec_mulVec y Xᴴ X, hX, Matrix.one_mulVec]
    · constructor
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ] at hx
        have hxy : X *ᵥ (Xᴴ *ᵥ x) = 0 := (smul_eq_zero.mp hx).resolve_left hw
        have hy := congrArg (fun z => Xᴴ *ᵥ z) hxy
        simpa only [Matrix.mulVec_mulVec (Xᴴ *ᵥ x) Xᴴ X, hX,
          Matrix.one_mulVec, Matrix.mulVec_zero] using hy
      · intro hx
        rw [hD, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x X Xᴴ, hx,
          Matrix.mulVec_zero, smul_zero]
  have dimensions (X : Matrix A Q ℂ) (hX : Xᴴ * X = 1)
      (D : Matrix A A ℂ) (hD : D = (blockWeight alpha beta : ℂ) • (X * Xᴴ)) :
      Module.finrank ℂ (Module.End.eigenspace D.mulVecLin (blockWeight alpha beta : ℂ)) =
        Fintype.card Q ∧
      Module.finrank ℂ (Module.End.eigenspace D.mulVecLin 0) = Fintype.card A - Fintype.card Q := by
    have heq : Module.End.eigenspace D.mulVecLin (blockWeight alpha beta : ℂ) =
        LinearMap.range X.mulVecLin := by
      ext x
      simpa only [Module.End.mem_eigenspace_iff, LinearMap.mem_range, Matrix.mulVecLin_apply]
        using (characterize X hX D hD x).1
    have hrankX : X.rank = Fintype.card Q := by
      rw [← Matrix.rank_conjTranspose_mul_self X, hX, Matrix.rank_one]
    have hrankD : D.rank = Fintype.card Q := by
      rw [hD, Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero hw), Matrix.rank_self_mul_conjTranspose, hrankX]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hrankX
    · rw [Module.End.eigenspace_zero]
      have hn := D.mulVecLin.finrank_range_add_finrank_ker
      have hr : Module.finrank ℂ (LinearMap.range D.mulVecLin) = Fintype.card Q := hrankD
      rw [hr, Module.finrank_pi] at hn
      omega
  have dimensionsB (X : Matrix B Q ℂ) (hX : Xᴴ * X = 1)
      (D : Matrix B B ℂ) (hD : D = (blockWeight alpha beta : ℂ) • (X * Xᴴ)) :
      Module.finrank ℂ (Module.End.eigenspace D.mulVecLin (blockWeight alpha beta : ℂ)) =
        Fintype.card Q ∧
      Module.finrank ℂ (Module.End.eigenspace D.mulVecLin 0) = Fintype.card B - Fintype.card Q := by
    have heq : Module.End.eigenspace D.mulVecLin (blockWeight alpha beta : ℂ) =
        LinearMap.range X.mulVecLin := by
      ext x
      simpa only [Module.End.mem_eigenspace_iff, LinearMap.mem_range, Matrix.mulVecLin_apply]
        using (characterizeB X hX D hD x).1
    have hrankX : X.rank = Fintype.card Q := by
      rw [← Matrix.rank_conjTranspose_mul_self X, hX, Matrix.rank_one]
    have hrankD : D.rank = Fintype.card Q := by
      rw [hD, Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero hw), Matrix.rank_self_mul_conjTranspose, hrankX]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hrankX
    · rw [Module.End.eigenspace_zero]
      have hn := D.mulVecLin.finrank_range_add_finrank_ker
      have hr : Module.finrank ℂ (LinearMap.range D.mulVecLin) = Fintype.card Q := hrankD
      rw [hr, Module.finrank_pi] at hn
      omega
  obtain ⟨hdA, hzA⟩ := dimensions U hU _ hredA
  obtain ⟨hdB, hzB⟩ := dimensionsB (rightVectors alpha beta) hV _ hredB
  exact ⟨fun x => (characterize U hU _ hredA x).1,
    fun x => (characterize U hU _ hredA x).2,
    fun x => (characterizeB (rightVectors alpha beta) hV _ hredB x).1,
    fun x => (characterizeB (rightVectors alpha beta) hV _ hredB x).2,
    hdA, hzA, hdB, hzB⟩

/-- Flat spectra are extracted from the actual reductions, including ambient zero directions. -/
theorem actual_flat_reductions (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    (blockWeight alpha beta = (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ ∧
    Matrix.trace (actualReducedA alpha beta) = 1 ∧
    Matrix.trace (actualReducedB alpha beta) = 1 ∧
    (actualCoefficient alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedA alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedB alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (∃ hA : (actualReducedA alpha beta).PosSemidef,
      (∀ i, hA.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hA.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i = 0)).card =
        Fintype.card A - Fintype.card (BlockQuotient alpha beta)) ∧
    (∃ hB : (actualReducedB alpha beta).PosSemidef,
      (∀ i, hB.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hB.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i = 0)).card =
        Fintype.card B - Fintype.card (BlockQuotient alpha beta))) ∧
    (∃ rhoA : DensityState A, ∃ rhoB : DensityState B,
      densityMatrix rhoA = actualReducedA alpha beta ∧
      densityMatrix rhoB = actualReducedB alpha beta ∧
      vonNeumannEntropy rhoA = Real.log (Fintype.card (BlockQuotient alpha beta)) ∧
      vonNeumannEntropy rhoB = Real.log (Fintype.card (BlockQuotient alpha beta)) ∧
      Real.log (Fintype.card (BlockQuotient alpha beta) : ℝ) =
        Real.log (Fintype.card G : ℝ) - Real.log (Fintype.card alpha.ker : ℝ) -
          Real.log (Fintype.card beta.ker : ℝ)) ∧
    (let T := Matrix.toEuclideanLin (actualCoefficient alpha beta)
     (∀ i : ℕ, T.singularValues i =
       if i < Fintype.card (BlockQuotient alpha beta) then
         Real.sqrt (blockWeight alpha beta) else 0) ∧
     T.singularValues.support.card = Fintype.card (BlockQuotient alpha beta)) ∧
    (alpha.ker ⊓ beta.ker = ⊥ ∧
      Nat.card (kernelSum alpha beta) = Nat.card alpha.ker * Nat.card beta.ker ∧
      Nat.card G = Nat.card (BlockQuotient alpha beta) *
        Nat.card alpha.ker * Nat.card beta.ker) := by
  classical
  have hnormal : alpha.ker ⊓ beta.ker = ⊥ ∧
      Nat.card (kernelSum alpha beta) = Nat.card alpha.ker * Nat.card beta.ker ∧
      Nat.card G = Nat.card (BlockQuotient alpha beta) *
        Nat.card alpha.ker * Nat.card beta.ker := by
    classical
    have hdisj : alpha.ker ⊓ beta.ker = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      have ha : alpha z = 0 := hz.1
      have hb : beta z = 0 := hz.2
      have hz0 : z = 0 := hpair (show (alpha z, beta z) = (alpha 0, beta 0) by
        simp [ha, hb])
      simpa [hz0]
    let f : alpha.ker × beta.ker → kernelSum alpha beta :=
      fun st => ⟨st.1.1 + st.2.1, AddSubgroup.mem_sup.mpr
        ⟨st.1.1, st.1.2, st.2.1, st.2.2, rfl⟩⟩
    have hf_inj : Function.Injective f := by
      rintro ⟨s, t⟩ ⟨s', t'⟩ h
      have hh : s.1 + t.1 = s'.1 + t'.1 := congrArg Subtype.val h
      have ha : alpha s.1 = alpha s'.1 := by
        have hs0 : alpha s.1 = 0 := s.2
        have hs0' : alpha s'.1 = 0 := s'.2
        rw [hs0, hs0']
      have hb : beta s.1 = beta s'.1 := by
        have ht0 : beta t.1 = 0 := t.2
        have ht0' : beta t'.1 = 0 := t'.2
        have hm := congrArg beta hh
        simpa [map_add, ht0, ht0'] using hm
      have hs : s = s' := Subtype.ext (hpair (Prod.ext ha hb))
      subst s'
      have ht : t = t' := Subtype.ext (add_left_cancel hh)
      exact Prod.ext rfl ht
    have hf_surj : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp hz
      refine ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
      exact Subtype.ext hst
    have hcard : Nat.card (kernelSum alpha beta) =
        Nat.card alpha.ker * Nat.card beta.ker := by
      calc
        Nat.card (kernelSum alpha beta) = Nat.card (alpha.ker × beta.ker) :=
          (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
        _ = Nat.card alpha.ker * Nat.card beta.ker := Nat.card_prod _ _
    refine ⟨hdisj, hcard, ?_⟩
    calc
      Nat.card G = Nat.card (BlockQuotient alpha beta) *
          Nat.card (kernelSum alpha beta) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (kernelSum alpha beta)
      _ = Nat.card (BlockQuotient alpha beta) *
          Nat.card alpha.ker * Nat.card beta.ker := by rw [hcard, mul_assoc]
  have hflat : blockWeight alpha beta = (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ ∧
    Matrix.trace (actualReducedA alpha beta) = 1 ∧
    Matrix.trace (actualReducedB alpha beta) = 1 ∧
    (actualCoefficient alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedA alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedB alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (∃ hA : (actualReducedA alpha beta).PosSemidef,
      (∀ i, hA.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hA.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i = 0)).card =
        Fintype.card A - Fintype.card (BlockQuotient alpha beta)) ∧
    (∃ hB : (actualReducedB alpha beta).PosSemidef,
      (∀ i, hB.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hB.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i = 0)).card =
        Fintype.card B - Fintype.card (BlockQuotient alpha beta)) := by
    classical
    obtain ⟨hU, hV, hC, hA, hB, _, _, _, _⟩ :=
      actual_block_matrices alpha beta hpair
    let U := leftVectors alpha beta
    let V := rightVectors alpha beta
    let w := blockWeight alpha beta
    have hw : 0 < w := by
      exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
        (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos)
    have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    have hcounts : Fintype.card G = Fintype.card (BlockQuotient alpha beta) *
        Fintype.card alpha.ker * Fintype.card beta.ker := by
      simpa only [Nat.card_eq_fintype_card] using
        hnormal.2.2
    have hwinv : w = (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ := by
      dsimp [w, blockWeight]
      rw [hcounts]
      push_cast
      have ha : (Fintype.card alpha.ker : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos (α := alpha.ker)).ne'
      have hb : (Fintype.card beta.ker : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos (α := beta.ker)).ne'
      field_simp [ha, hb]
    have hwR : (w : ℂ) * Fintype.card (BlockQuotient alpha beta) = 1 := by
      rw [hwinv]
      push_cast
      exact inv_mul_cancel₀ (by exact_mod_cast
        (Fintype.card_pos (α := BlockQuotient alpha beta)).ne')
    have htraceA : Matrix.trace (actualReducedA alpha beta) = 1 := by
      rw [hA, Matrix.trace_smul, Matrix.trace_mul_comm, hU, Matrix.trace_one]
      exact hwR
    have htraceB : Matrix.trace (actualReducedB alpha beta) = 1 := by
      rw [hB, Matrix.trace_smul, Matrix.trace_mul_comm, hV, Matrix.trace_one]
      exact hwR
    have hrankA : (actualReducedA alpha beta).rank =
        Fintype.card (BlockQuotient alpha beta) := by
      rw [hA, Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero hwC), Matrix.rank_self_mul_conjTranspose,
        ← Matrix.rank_conjTranspose_mul_self (leftVectors alpha beta), hU, Matrix.rank_one]
    have hrankB : (actualReducedB alpha beta).rank =
        Fintype.card (BlockQuotient alpha beta) := by
      rw [hB, Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero hwC), Matrix.rank_self_mul_conjTranspose,
        ← Matrix.rank_conjTranspose_mul_self (rightVectors alpha beta), hV, Matrix.rank_one]
    have hAA : actualReducedA alpha beta =
        actualCoefficient alpha beta * (actualCoefficient alpha beta)ᴴ := by ext; rfl
    have hrankC : (actualCoefficient alpha beta).rank =
        Fintype.card (BlockQuotient alpha beta) := by
      rw [← Matrix.rank_self_mul_conjTranspose, ← hAA, hrankA]
    have hposA : (actualReducedA alpha beta).PosSemidef := by
      rw [hAA]
      exact Matrix.posSemidef_self_mul_conjTranspose _
    have hposB : (actualReducedB alpha beta).PosSemidef := by
      rw [hB]
      exact (Matrix.posSemidef_self_mul_conjTranspose V).smul
        (show (0 : ℂ) ≤ (w : ℂ) by exact_mod_cast hw.le)
    have hquadA : actualReducedA alpha beta * actualReducedA alpha beta =
        (w : ℂ) • actualReducedA alpha beta := by
      simp only [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      calc
        (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by simp [Matrix.mul_assoc]
        _ = U * Uᴴ := by rw [hU, Matrix.mul_one]
    have hquadB : actualReducedB alpha beta * actualReducedB alpha beta =
        (w : ℂ) • actualReducedB alpha beta := by
      simp only [hB, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      calc
        (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
        _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
    have heigsA (i : A) : hposA.isHermitian.eigenvalues i = w ∨
        hposA.isHermitian.eigenvalues i = 0 := by
      let e := Unitary.conjStarAlgAut ℂ (Matrix A A ℂ)
        (star hposA.isHermitian.eigenvectorUnitary)
      have hd := congrArg e hquadA
      rw [map_mul, map_smul, hposA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary] at hd
      have hi := congrArg (fun M : Matrix A A ℂ => M i i) hd
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, smul_eq_mul, Function.comp_apply] at hi
      have hr : hposA.isHermitian.eigenvalues i * hposA.isHermitian.eigenvalues i =
          w * hposA.isHermitian.eigenvalues i := by
        simpa using congrArg Complex.re hi
      have hz : hposA.isHermitian.eigenvalues i *
          (hposA.isHermitian.eigenvalues i - w) = 0 := by nlinarith [hr]
      rcases mul_eq_zero.mp hz with hzero | heq
      · exact Or.inr hzero
      · exact Or.inl (sub_eq_zero.mp heq)
    have heigsB (i : B) : hposB.isHermitian.eigenvalues i = w ∨
        hposB.isHermitian.eigenvalues i = 0 := by
      let e := Unitary.conjStarAlgAut ℂ (Matrix B B ℂ)
        (star hposB.isHermitian.eigenvectorUnitary)
      have hd := congrArg e hquadB
      rw [map_mul, map_smul, hposB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary] at hd
      have hi := congrArg (fun M : Matrix B B ℂ => M i i) hd
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, smul_eq_mul, Function.comp_apply] at hi
      have hr : hposB.isHermitian.eigenvalues i * hposB.isHermitian.eigenvalues i =
          w * hposB.isHermitian.eigenvalues i := by
        simpa using congrArg Complex.re hi
      have hz : hposB.isHermitian.eigenvalues i *
          (hposB.isHermitian.eigenvalues i - w) = 0 := by nlinarith [hr]
      rcases mul_eq_zero.mp hz with hzero | heq
      · exact Or.inr hzero
      · exact Or.inl (sub_eq_zero.mp heq)
    have hsuppA : (Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i ≠ 0)).card =
        Fintype.card (BlockQuotient alpha beta) := by
      rw [← Fintype.card_subtype, ← hposA.isHermitian.rank_eq_card_non_zero_eigs, hrankA]
    have hsuppB : (Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i ≠ 0)).card =
        Fintype.card (BlockQuotient alpha beta) := by
      rw [← Fintype.card_subtype, ← hposB.isHermitian.rank_eq_card_non_zero_eigs, hrankB]
    refine ⟨hwinv, htraceA, htraceB, hrankC, hrankA, hrankB,
      ⟨hposA, heigsA, ?_, ?_⟩, ⟨hposB, heigsB, ?_, ?_⟩⟩
    · convert hsuppA using 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change hposA.isHermitian.eigenvalues i = w ↔ hposA.isHermitian.eigenvalues i ≠ 0
      rcases heigsA i with hi | hi <;> simp [hi, hw.ne', hw.ne'.symm]
    · have hz : Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i = 0) =
          Finset.univ \ Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i ≠ 0) := by
        ext i; simp
      rw [hz, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, hsuppA]
    · convert hsuppB using 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change hposB.isHermitian.eigenvalues i = w ↔ hposB.isHermitian.eigenvalues i ≠ 0
      rcases heigsB i with hi | hi <;> simp [hi, hw.ne', hw.ne'.symm]
    · have hz : Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i = 0) =
          Finset.univ \ Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i ≠ 0) := by
        ext i; simp
      rw [hz, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, hsuppB]
  classical
  obtain ⟨hw, htraceA, htraceB, _, _, _, hspecA, hspecB⟩ :=
    id hflat
  obtain ⟨hposA, heigsA, hcountA, _⟩ := hspecA
  obtain ⟨hposB, heigsB, hcountB, _⟩ := hspecB
  let rhoA : DensityState A := by
    refine ⟨CStarMatrix.ofMatrix (actualReducedA alpha beta), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hposA.nonneg
    · exact htraceA
  let rhoB : DensityState B := by
    refine ⟨CStarMatrix.ofMatrix (actualReducedB alpha beta), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hposB.nonneg
    · exact htraceB
  have hspecA' (i : Fin (Fintype.card A)) :
      D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum rhoA i =
        hposA.isHermitian.eigenvalues₀ i := by
    have hmat : densityMatrix rhoA = actualReducedA alpha beta := by
      ext j k
      rfl
    unfold D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum
    simp only [hmat]
  have hspecB' (i : Fin (Fintype.card B)) :
      D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum rhoB i =
        hposB.isHermitian.eigenvalues₀ i := by
    have hmat : densityMatrix rhoB = actualReducedB alpha beta := by
      ext j k
      rfl
    unfold D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum
    simp only [hmat]
  have hcardA : (Fintype.card A : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hcardB : (Fintype.card B : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hR : (Fintype.card (BlockQuotient alpha beta) : ℝ) > 0 :=
    by exact_mod_cast Fintype.card_pos
  have hKA : (Fintype.card alpha.ker : ℝ) > 0 :=
    by exact_mod_cast Fintype.card_pos
  have hKB : (Fintype.card beta.ker : ℝ) > 0 :=
    by exact_mod_cast Fintype.card_pos
  have hflat_entropyA (w : ℝ) (hw' : w =
      (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹)
      (hpos : (actualReducedA alpha beta).PosSemidef)
      (heigs : ∀ i, hpos.isHermitian.eigenvalues i = w ∨
        hpos.isHermitian.eigenvalues i = 0)
      (hcount : (Finset.univ.filter (fun i =>
        hpos.isHermitian.eigenvalues i = w)).card = Fintype.card (BlockQuotient alpha beta))
      (hwpos : 0 < w) :
      ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    have hpoint (i : A) : Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        if hpos.isHermitian.eigenvalues i = w then Real.negMulLog w else 0 := by
      rcases heigs i with hi | hi
      · simp [hi]
      · have hne : (0 : ℝ) ≠ w := ne_of_lt hwpos
        simp [hi, hne]
    have hsum : ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        ((Finset.univ.filter (fun i => hpos.isHermitian.eigenvalues i = w)).card : ℝ) *
          Real.negMulLog w := by
      simp_rw [hpoint]
      rw [Finset.sum_ite]
      simp
    rw [hsum, hcount]
    have hwform : Real.negMulLog w =
        (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ *
          Real.log (Fintype.card (BlockQuotient alpha beta)) := by
      rw [Real.negMulLog, hw', Real.log_inv]
      ring
    rw [hwform]
    field_simp
  have hflat_entropyB (w : ℝ) (hw' : w =
      (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹)
      (hpos : (actualReducedB alpha beta).PosSemidef)
      (heigs : ∀ i, hpos.isHermitian.eigenvalues i = w ∨
        hpos.isHermitian.eigenvalues i = 0)
      (hcount : (Finset.univ.filter (fun i =>
        hpos.isHermitian.eigenvalues i = w)).card = Fintype.card (BlockQuotient alpha beta))
      (hwpos : 0 < w) :
      ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    have hpoint (i : B) : Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        if hpos.isHermitian.eigenvalues i = w then Real.negMulLog w else 0 := by
      rcases heigs i with hi | hi
      · simp [hi]
      · have hne : (0 : ℝ) ≠ w := ne_of_lt hwpos
        simp [hi, hne]
    have hsum : ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        ((Finset.univ.filter (fun i => hpos.isHermitian.eigenvalues i = w)).card : ℝ) *
          Real.negMulLog w := by
      simp_rw [hpoint]
      rw [Finset.sum_ite]
      simp
    rw [hsum, hcount]
    have hwform : Real.negMulLog w =
        (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ *
          Real.log (Fintype.card (BlockQuotient alpha beta)) := by
      rw [Real.negMulLog, hw', Real.log_inv]
      ring
    rw [hwform]
    field_simp
  have hEA : vonNeumannEntropy rhoA =
      Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    rw [D5.S3.Quantum.Sharpness.FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum]
    unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
    simp_rw [hspecA']
    rw [← RHLinalg.sum_eigenvalues_reindex hposA.isHermitian Real.negMulLog]
    exact hflat_entropyA (blockWeight alpha beta) hw hposA
      heigsA hcountA (by
        exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
          (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos))
  have hEB : vonNeumannEntropy rhoB =
      Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    rw [D5.S3.Quantum.Sharpness.FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum]
    unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
    simp_rw [hspecB']
    rw [← RHLinalg.sum_eigenvalues_reindex hposB.isHermitian Real.negMulLog]
    exact hflat_entropyB (blockWeight alpha beta) hw hposB
      heigsB hcountB (by
        exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
          (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos))
  have hcounts : (Fintype.card G : ℝ) =
      (Fintype.card (BlockQuotient alpha beta) : ℝ) *
        (Fintype.card alpha.ker : ℝ) * (Fintype.card beta.ker : ℝ) := by
    exact_mod_cast (show Fintype.card G =
      Fintype.card (BlockQuotient alpha beta) *
        Fintype.card alpha.ker * Fintype.card beta.ker by
      simpa only [Nat.card_eq_fintype_card] using
        hnormal.2.2)
  have hlog : Real.log (Fintype.card (BlockQuotient alpha beta) : ℝ) =
      Real.log (Fintype.card G : ℝ) - Real.log (Fintype.card alpha.ker : ℝ) -
        Real.log (Fintype.card beta.ker : ℝ) := by
    rw [hcounts, Real.log_mul (mul_ne_zero hR.ne' hKA.ne') hKB.ne',
      Real.log_mul hR.ne' hKA.ne']
    ring
  let T := Matrix.toEuclideanLin (actualCoefficient alpha beta)
  have hgramMatrix : (actualCoefficient alpha beta)ᴴ * actualCoefficient alpha beta =
      actualReducedB alpha beta := by
    ext b d
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, actualReducedB,
      partialTraceLeft, actualJoint]
    have hreal (a : A) (b : B) : star (actualCoefficient alpha beta a b) =
        actualCoefficient alpha beta a b := by simp [actualCoefficient]
    simp_rw [hreal]
  have hgram : T.adjoint ∘ₗ T = Matrix.toEuclideanLin (actualReducedB alpha beta) := by
    dsimp [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change Matrix.toLpLin 2 2 (actualCoefficient alpha beta)ᴴ ∘ₗ
      Matrix.toLpLin 2 2 (actualCoefficient alpha beta) = _
    rw [← Matrix.toLpLin_mul_same, hgramMatrix]
  have hrank : Module.finrank ℂ T.range = Fintype.card (BlockQuotient alpha beta) := by
    have hc := hflat.2.2.2.1
    rw [Matrix.rank_eq_finrank_range_toLin (actualCoefficient alpha beta)
      (EuclideanSpace.basisFun A ℂ).toBasis (EuclideanSpace.basisFun B ℂ).toBasis] at hc
    exact hc
  have heig0 (i : Fin (Fintype.card B)) :
      hposB.isHermitian.eigenvalues₀ i = blockWeight alpha beta ∨
        hposB.isHermitian.eigenvalues₀ i = 0 := by
    simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      heigsB ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card B))) i)
  have hsquare (i : ℕ) (hi : i < Fintype.card B) :
      T.singularValues i ^ 2 = hposB.isHermitian.eigenvalues₀ ⟨i, hi⟩ := by
    have hs := T.sq_singularValues_of_lt finrank_euclideanSpace hi
    simp only [hgram] at hs
    exact hs
  have hsingular (i : ℕ) : T.singularValues i =
      if i < Fintype.card (BlockQuotient alpha beta) then
        Real.sqrt (blockWeight alpha beta) else 0 := by
    by_cases hi : i < Fintype.card (BlockQuotient alpha beta)
    · rw [if_pos hi]
      have hpos : 0 < T.singularValues i :=
        T.singularValues_pos_iff_lt_finrank_range.mpr (by simpa [hrank] using hi)
      have hiB : i < Fintype.card B := by
        have hle := T.finrank_range_le
        rw [hrank, finrank_euclideanSpace] at hle
        exact hi.trans_le hle
      rcases heig0 ⟨i, hiB⟩ with heq | heq
      · calc
          T.singularValues i = Real.sqrt (T.singularValues i ^ 2) :=
            (Real.sqrt_sq (T.singularValues_nonneg i)).symm
          _ = Real.sqrt (blockWeight alpha beta) := by rw [hsquare i hiB, heq]
      · have hz := hsquare i hiB
        rw [heq] at hz
        nlinarith
    · rw [if_neg hi]
      exact T.singularValues_eq_zero_iff_le_finrank_range.mpr (by
        simpa [hrank] using Nat.le_of_not_gt hi)
  exact ⟨hflat, ⟨rhoA, rhoB, rfl, rfl, hEA, hEB, hlog⟩,
    ⟨hsingular, T.card_support_singularValues.trans hrank⟩, hnormal⟩
/- The joint matrix is the actual outer product, so its state properties are
   consequences of the coefficient normalization rather than extra axioms. -/
theorem actual_joint_state (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    (actualJoint alpha beta).PosSemidef ∧
      (actualJoint alpha beta).IsHermitian ∧
      Matrix.trace (actualJoint alpha beta) = 1 ∧
      actualJoint alpha beta * actualJoint alpha beta = actualJoint alpha beta ∧
      (actualJoint alpha beta).rank = 1 ∧
      (∑ p : A × B, star (actualCoefficient alpha beta p.1 p.2) *
        actualCoefficient alpha beta p.1 p.2) = 1 ∧
      actualSourceKet alpha beta = (fun p => actualCoefficient alpha beta p.1 p.2) ∧
      actualSourceKet alpha beta = (Real.sqrt (blockWeight alpha beta) : ℂ) •
        ∑ q : BlockQuotient alpha beta,
          (fun p : A × B => leftVectors alpha beta p.1 q * rightVectors alpha beta p.2 q) := by
  classical
  obtain ⟨⟨_, htraceA, _, _, _, _, _, _⟩, _⟩ := actual_flat_reductions alpha beta hpair
  let psi : A × B → ℂ := fun p => actualCoefficient alpha beta p.1 p.2
  have houter : actualJoint alpha beta = Matrix.vecMulVec psi (star psi) := by
    ext p r
    rfl
  have htrace : Matrix.trace (actualJoint alpha beta) = 1 := by
    rw [← trace_partialTraceRight (actualJoint alpha beta)]
    exact htraceA
  have hnorm : star psi ⬝ᵥ psi = 1 := by
    simpa [houter, Matrix.trace_vecMulVec, dotProduct, mul_comm] using htrace
  have hpos : (actualJoint alpha beta).PosSemidef := by
    rw [houter]
    exact Matrix.posSemidef_vecMulVec_self_star psi
  have hherm : (actualJoint alpha beta).IsHermitian := hpos.isHermitian
  have hidem : actualJoint alpha beta * actualJoint alpha beta = actualJoint alpha beta := by
    rw [houter, Matrix.vecMulVec_mul_vecMulVec, hnorm, one_smul]
  have hpsi : ∃ p, psi p ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : psi = 0 := funext h
    have : (0 : ℂ) = 1 := by simpa [hz, dotProduct] using hnorm
    exact zero_ne_one this
  have hrank_pos : 0 < (actualJoint alpha beta).rank := by
    rw [houter, Matrix.rank_eq_finrank_span_cols]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    obtain ⟨p, hp⟩ := hpsi
    let col : Submodule.span ℂ (Set.range (Matrix.vecMulVec psi (star psi)).col) :=
      ⟨(Matrix.vecMulVec psi (star psi)).col p,
        Submodule.subset_span ⟨p, rfl⟩⟩
    refine ⟨col, ?_⟩
    intro hz
    have hentry := congrFun (congrArg Subtype.val hz) p
    have hmul : psi p * star (psi p) = 0 := by
      simpa [col, Matrix.vecMulVec_apply] using hentry
    exact (mul_ne_zero hp (star_ne_zero.mpr hp)) hmul
  have hrank_le : (actualJoint alpha beta).rank ≤ 1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le psi (star psi)
  have hket : actualSourceKet alpha beta = (fun p => actualCoefficient alpha beta p.1 p.2) := by
    ext p
    rcases p with ⟨a, b⟩
    simp [actualSourceKet, actualCoefficient, Pi.single_apply, Prod.ext_iff, eq_comm]
  refine ⟨hpos, hherm, htrace, hidem, ?_, ?_, hket, ?_⟩
  · omega
  · simpa only [dotProduct, Pi.star_apply, psi] using hnorm
  · rw [hket]
    have hC := (actual_block_matrices alpha beta hpair).2.2.1
    ext p
    have hp := congrArg (fun M : Matrix A B ℂ => M p.1 p.2) hC
    have hreal (b : B) (q : BlockQuotient alpha beta) :
        star (rightVectors alpha beta b q) = rightVectors alpha beta b q := by
      unfold rightVectors
      split_ifs <;> simp [Complex.star_def]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hreal] at hp
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using hp


end D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum

#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_eigenspaces
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_flat_reductions
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_joint_state
