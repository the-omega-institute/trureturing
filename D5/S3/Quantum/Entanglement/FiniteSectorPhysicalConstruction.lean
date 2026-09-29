/- GID: D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Choi/Kraus channel construction and encoded sector splitter. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

/-
Choi positivity and spectral Kraus construction adapted from
leanprover-community/physlib at 6a09b2d1761a0d4430083045a247eb121d8da260.
Copyright (c) 2025 Alex Meiburg. Modified for the canonical CStarMatrix channel.
Full Apache-2.0 license and attribution:
docs/reports/licenses/finite-sector-channel-third-party.md.
Retire when this repository's pinned Mathlib contains equivalent declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open SectorSchmidtEncoding
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
  {spectralSize : ℕ}

set_option maxHeartbeats 40000000 in
/-- Finite Choi positivity yields complete Kraus operators and an isometric dilation. -/
theorem channel_kraus_stinespring :
    (∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b),
      ∃ K : (b × a) → Matrix b a ℂ,
        (∑ k, (K k).conjTranspose * K k) = 1 ∧
        ∀ rho : Matrix a a ℂ,
          CStarMatrix.ofMatrix.symm
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
            ∑ k, K k * rho * (K k).conjTranspose) ∧
    (∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b),
      ∃ V : Matrix ((b × a) × b) a ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ rho : Matrix a a ℂ,
          partialTraceLeft (V * rho * V.conjTranspose) =
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho))) := by
  classical
  let choi {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (channel : QuantumChannel a b) :
      Matrix (b × a) (b × a) ℂ :=
    fun p q => CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single p.2 q.2 1))) p.1 q.1

  have choi_posSemidef {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (channel : QuantumChannel a b) :
      (choi channel).PosSemidef := by
    classical
    by_cases ha : Nonempty a
    · let a₀ : a := Classical.choice ha
      let Y : CStarMatrix a a (CStarMatrix a a ℂ) :=
        CStarMatrix.ofMatrix fun r s =>
          if r = a₀ then CStarMatrix.ofMatrix (Matrix.single a₀ s 1) else 0
      let X : CStarMatrix a a (CStarMatrix a a ℂ) :=
        CStarMatrix.ofMatrix fun r s =>
          CStarMatrix.ofMatrix (Matrix.single r s 1)
      have hY_diag (t : a) :
          Y a₀ t = CStarMatrix.ofMatrix (Matrix.single a₀ t (1 : ℂ)) := by
        change (if a₀ = a₀ then
          CStarMatrix.ofMatrix (Matrix.single a₀ t (1 : ℂ)) else 0) = _
        simp
      have hY_off (t r : a) (ht : t ≠ a₀) : Y t r = 0 := by
        change (if t = a₀ then
          CStarMatrix.ofMatrix (Matrix.single a₀ r (1 : ℂ)) else 0) = 0
        simp [ht]
      have hXeq : X = star Y * Y := by
        apply CStarMatrix.ext
        intro r s
        change CStarMatrix.ofMatrix (Matrix.single r s (1 : ℂ)) =
          ∑ t, star (Y t r) * Y t s
        rw [Finset.sum_eq_single a₀]
        · rw [hY_diag r, hY_diag s]
          change CStarMatrix.ofMatrix (Matrix.single r s (1 : ℂ)) =
            CStarMatrix.ofMatrix
              ((Matrix.single a₀ r (1 : ℂ)).conjTranspose *
                Matrix.single a₀ s 1)
          congr 1
          rw [Matrix.conjTranspose_single, star_one,
            Matrix.single_mul_single_same, one_mul]
        · intro t _ ht
          rw [hY_off t r ht, hY_off t s ht]
          simp
        · intro h
          exact (h (Finset.mem_univ a₀)).elim
      have hX : 0 ≤ X := by
        rw [hXeq]
        exact star_mul_self_nonneg Y
      let H : CStarMatrix a a (CStarMatrix b b ℂ) :=
        X.map channel.toCompletelyPositiveMap
      have hH : 0 ≤ H :=
        channel.toCompletelyPositiveMap.map_cstarMatrix_nonneg X hX
      let e : a ≃ Fin (Fintype.card a) := Fintype.equivFin a
      let HFin : CStarMatrix (Fin (Fintype.card a)) (Fin (Fintype.card a))
          (CStarMatrix b b ℂ) := CStarMatrix.reindexₐ ℂ (CStarMatrix b b ℂ) e H
      have hHFin : 0 ≤ HFin :=
        map_nonneg (CStarMatrix.reindexₐ ℂ (CStarMatrix b b ℂ) e) hH
      let inner : Matrix (Fin (Fintype.card a)) (Fin (Fintype.card a))
          (CStarMatrix b b ℂ) ≃⋆ₐ[ℂ]
          Matrix (Fin (Fintype.card a)) (Fin (Fintype.card a))
            (Matrix b b ℂ) :=
        StarAlgEquiv.ofAlgEquiv
          ((CStarMatrix.ofMatrixStarAlgEquiv (n := b)).symm.toAlgEquiv.mapMatrix)
          (by intro M; ext r s p q; rfl)
      let comp : Matrix (Fin (Fintype.card a)) (Fin (Fintype.card a))
          (Matrix b b ℂ) ≃⋆ₐ[ℂ]
          Matrix (Fin (Fintype.card a) × b) (Fin (Fintype.card a) × b) ℂ :=
        StarAlgEquiv.ofAlgEquiv
          (Matrix.compAlgEquiv (Fin (Fintype.card a)) b ℂ ℂ)
          (by intro M; ext ⟨r, p⟩ ⟨s, q⟩; rfl)
      let flat : CStarMatrix (Fin (Fintype.card a)) (Fin (Fintype.card a))
          (CStarMatrix b b ℂ) ≃⋆ₐ[ℂ]
          CStarMatrix (Fin (Fintype.card a) × b)
            (Fin (Fintype.card a) × b) ℂ :=
        (CStarMatrix.ofMatrixStarAlgEquiv).symm.trans
          (inner.trans (comp.trans CStarMatrix.ofMatrixStarAlgEquiv))
      let Flat := flat HFin
      have hFlat : 0 ≤ Flat :=
        map_nonneg flat hHFin
      let ef : Fin (Fintype.card a) × b ≃ b × a :=
        (Equiv.prodComm (Fin (Fintype.card a)) b).trans
          (Equiv.prodCongr (Equiv.refl b) e.symm)
      let Flat' := CStarMatrix.reindexₐ ℂ ℂ ef Flat
      have hFlat' : 0 ≤ Flat' :=
        map_nonneg (CStarMatrix.reindexₐ ℂ ℂ ef) hFlat
      have hFlat_entry (u v : Fin (Fintype.card a) × b) :
          Flat u v = HFin u.1 v.1 u.2 v.2 := rfl
      have hFlat'_entry (u v : b × a) :
          Flat' u v = Flat (ef.symm u) (ef.symm v) := rfl
      have hHFin_entry (r s : Fin (Fintype.card a)) :
          HFin r s = H (e.symm r) (e.symm s) := rfl
      have hchoi : choi channel = CStarMatrix.ofMatrix.symm Flat' := by
        apply Matrix.ext
        intro ⟨p, r⟩ ⟨q, s⟩
        change choi channel (p, r) (q, s) = Flat' (p, r) (q, s)
        rw [hFlat'_entry, hFlat_entry, hHFin_entry]
        simp [choi, H, X, ef]
        rfl
      rw [hchoi]
      exact Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hFlat')
    · have hzero : choi channel = 0 := by
        ext p q
        exact (ha ⟨p.2⟩).elim
      rw [hzero]
      exact Matrix.PosSemidef.zero

  have quantumChannel_exists_complete_kraus {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (channel : QuantumChannel a b) :
      ∃ K : (b × a) → Matrix b a ℂ,
        (∑ k, (K k).conjTranspose * K k) = 1 ∧
        ∀ rho : Matrix a a ℂ,
          CStarMatrix.ofMatrix.symm
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
            ∑ k, K k * rho * (K k).conjTranspose := by
    have hC := choi_posSemidef channel
    let K : (b × a) → Matrix b a ℂ := fun k i j =>
      (hC.1.eigenvectorUnitary.val : Matrix _ _ ℂ) (i, j) k *
        (Real.sqrt (hC.1.eigenvalues k) : ℂ)
    have hchoi : ∀ p q : b × a, choi channel p q =
        ∑ k, K k p.1 p.2 * star (K k q.1 q.2) := by
      intro p q
      have hspectral := Matrix.IsHermitian.spectral_theorem hC.1
      have hentry := congrFun (congrFun hspectral p) q
      convert hentry using 1
      simp [K, Matrix.mul_apply, Matrix.diagonal]
      ring_nf
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsqrt : ((Real.sqrt (hC.1.eigenvalues k) : ℂ) ^ 2) =
          (hC.1.eigenvalues k : ℂ) := by
        exact_mod_cast Real.sq_sqrt (hC.eigenvalues_nonneg k)
      rw [hsqrt]
    have haction (rho : Matrix a a ℂ) :
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
          ∑ k, K k * rho * (K k).conjTranspose := by
      let f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ :=
        CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
          (channel.toCompletelyPositiveMap.toLinearMap.comp
            CStarMatrix.ofMatrixₗ.toLinearMap)
      change f rho = ∑ k, K k * rho * (K k).conjTranspose
      have expand : rho = ∑ i, ∑ j, rho i j • Matrix.single i j 1 := by
        ext i j
        simp [Matrix.single, Matrix.sum_apply, ite_and]
      apply Matrix.ext
      intro p q
      conv_lhs => rw [expand]
      simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      simp_rw [show ∀ i j, f (Matrix.single i j 1) p q =
            choi channel (p, i) (q, j) from fun _ _ => rfl]
      simp_rw [hchoi]
      simp only [Finset.mul_sum]
      calc
        _ = ∑ i : a, ∑ k : b × a, ∑ j : a,
            rho i j * (K k p i * star (K k q j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = ∑ k : b × a, ∑ i : a, ∑ j : a,
            rho i j * (K k p i * star (K k q j)) := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k _
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    have hcomplete : (∑ k, (K k).conjTranspose * K k) = 1 := by
      ext i j
      let E : Matrix a a ℂ := Matrix.single j i 1
      have htrace := channel.trace_preserving
        (CStarMatrix.ofMatrix E)
      have heq := haction E
      change Matrix.trace (CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix E))) = Matrix.trace E at htrace
      rw [heq] at htrace
      have hentry (k : b × a) :
          ((K k).conjTranspose * K k) i j =
            Matrix.trace (K k * E * (K k).conjTranspose) := by
        rw [Matrix.trace_mul_cycle]
        simp [Matrix.trace_mul_single, E]
      calc
        (∑ k, (K k).conjTranspose * K k) i j =
            ∑ k, Matrix.trace (K k * E * (K k).conjTranspose) := by
          simp only [Matrix.sum_apply]
          exact Finset.sum_congr rfl fun k _ => hentry k
        _ = Matrix.trace (∑ k, K k * E * (K k).conjTranspose) := by
          rw [Matrix.trace_sum]
        _ = Matrix.trace E := htrace
        _ = (1 : Matrix a a ℂ) i j := by
          by_cases hij : i = j
          · subst j
            simp [E, Matrix.trace_single_eq_same]
          · have hji : j ≠ i := Ne.symm hij
            simpa [E, Matrix.one_apply, hij] using
              (Matrix.trace_single_eq_of_ne j i (1 : ℂ) hji)
    exact ⟨K, hcomplete, haction⟩


  let dilation {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (K : (b × a) → Matrix b a ℂ) :
      Matrix ((b × a) × b) a ℂ := fun p i => K p.1 p.2 i

  have quantumChannel_exists_finite_stinespring {a b : Type u} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (channel : QuantumChannel a b) :
      ∃ V : Matrix ((b × a) × b) a ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ rho : Matrix a a ℂ,
          partialTraceLeft (V * rho * V.conjTranspose) =
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) := by
    obtain ⟨K, hK, hAction⟩ := quantumChannel_exists_complete_kraus channel
    let V := dilation K
    have hIso : V.conjTranspose * V = 1 := by
      ext i j
      calc
        (V.conjTranspose * V) i j =
            ∑ k : b × a, ∑ x : b, star (K k x i) * K k x j := by
          change (∑ p : (b × a) × b, star (K p.1 p.2 i) * K p.1 p.2 j) = _
          rw [Fintype.sum_prod_type]
        _ = (∑ k, (K k).conjTranspose * K k) i j := by
          simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
        _ = (1 : Matrix a a ℂ) i j :=
          congrArg (fun M : Matrix a a ℂ => M i j) hK
    refine ⟨V, hIso, ?_⟩
    let L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := {
      toFun := fun rho => partialTraceLeft (V * rho * V.conjTranspose)
      map_add' := by
        intro rho sigma
        ext x y
        simp [partialTraceLeft, Matrix.mul_add, Matrix.add_mul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c rho
        ext x y
        simp [partialTraceLeft, Matrix.mul_smul, Matrix.smul_mul,
          Finset.mul_sum] }
    let R : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := {
      toFun := fun rho => ∑ k, K k * rho * (K k).conjTranspose
      map_add' := by
        intro rho sigma
        simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c rho
        simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum] }
    have hUnit (i j : a) : L (Matrix.single i j (1 : ℂ)) =
        R (Matrix.single i j (1 : ℂ)) := by
      ext x y
      change partialTraceLeft
        (V * Matrix.single i j (1 : ℂ) * V.conjTranspose) x y =
          (∑ k, K k * Matrix.single i j (1 : ℂ) * (K k).conjTranspose) x y
      simp only [partialTraceLeft, Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rfl
    intro rho
    rw [hAction rho]
    change L rho = R rho
    have expand : rho = ∑ i, ∑ j, rho i j • Matrix.single i j 1 := by
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and]
    conv_lhs => rw [expand]
    conv_rhs => rw [expand]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hUnit]

  exact ⟨quantumChannel_exists_complete_kraus,
    quantumChannel_exists_finite_stinespring⟩

set_option maxHeartbeats 40000000 in
/-- Actual source, target, product, mixture, and splitting channels with full matrix actions. -/
theorem physical_encoding [Nonempty Sector] (M : Model Sector spectralSize) :
    ∃ encoding : EncodingChannels M,
    ∃ splitting : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ splittingJoint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d),
      (∀ left right : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
        ∃ joint : QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
          (TargetLocal M.d × TargetLocal M.d), TensorRealization left right joint) ∧
      (∀ (m : ℕ) (weight : Fin m → ℝ), weight ∈ stdSimplex ℝ (Fin m) →
        ∀ left right : Fin m → QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
        ∃ joint : QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
          (TargetLocal M.d × TargetLocal M.d), MixtureRealization weight left right joint) ∧
      TensorRealization splitting splitting splittingJoint ∧
      (∀ X : Matrix (SourceLocal (Coord := Fin spectralSize) M.d)
          (SourceLocal (Coord := Fin spectralSize) M.d) ℂ,
        CStarMatrix.ofMatrix.symm
          (splitting.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        fun b c => ∑ j : Fin spectralSize, X ⟨b.1, (b.2, j)⟩ ⟨c.1, (c.2, j)⟩) ∧
      (∀ X : Matrix Sector Sector ℂ,
        CStarMatrix.ofMatrix.symm
          ((splittingJoint.comp encoding.source).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
          (targetEncoding M.d)ᴴ) := by
  classical
  have hTensorExist {ax ay bx oy : Type u}
      [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
      [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
      (left : QuantumChannel ax bx) (right : QuantumChannel ay oy) :
      ∃ joint : QuantumChannel (ax × ay) (bx × oy),
        ∀ X : Matrix (ax × ay) (ax × ay) ℂ,
          CStarMatrix.ofMatrix.symm
            (joint.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          fun p q => ∑ i : ax, ∑ j : ax, ∑ u : ay, ∑ v : ay,
            X (i, u) (j, v) *
              CStarMatrix.ofMatrix.symm
                (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1)))
                  p.1 q.1 *
              CStarMatrix.ofMatrix.symm
                (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single u v 1)))
                  p.2 q.2 := by
    classical
    obtain ⟨K, hK, hLeft⟩ := (channel_kraus_stinespring).1 left
    obtain ⟨L, hL, hRight⟩ := (channel_kraus_stinespring).1 right
    have hsumIn (A : (bx × ax) → Matrix ax ax ℂ)
        (B : (oy × ay) → Matrix ay ay ℂ) :
        (∑ i, A i) ⊗ₖ (∑ j, B j) = ∑ i, ∑ j, A i ⊗ₖ B j := by
      ext p q
      simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    have hsumOut (A : (bx × ax) → Matrix bx bx ℂ)
        (B : (oy × ay) → Matrix oy oy ℂ) :
        (∑ i, A i) ⊗ₖ (∑ j, B j) = ∑ i, ∑ j, A i ⊗ₖ B j := by
      ext p q
      simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    let T : ((bx × ax) × (oy × ay)) → Matrix (bx × oy) (ax × ay) ℂ :=
      fun r => K r.1 ⊗ₖ L r.2
    have hT : (∑ r, (T r)ᴴ * T r) = 1 := by
      simp only [T, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      rw [← hsumIn, hK, hL, Matrix.one_kronecker_one]
    obtain ⟨joint, hJoint⟩ := finite_kraus_quantum_channel T hT
    have hBasis (i j : ax) (u v : ay) :
        CStarMatrix.ofMatrix.symm
            (joint.toCompletelyPositiveMap
              (CStarMatrix.ofMatrix (Matrix.single (i, u) (j, v) 1))) =
        CStarMatrix.ofMatrix.symm
            (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) ⊗ₖ
          CStarMatrix.ofMatrix.symm
            (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single u v 1))) := by
      rw [hJoint, hLeft, hRight, hsumOut]
      have hSingle : Matrix.single (i, u) (j, v) (1 : ℂ) =
          Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single u v (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, one_mul]
      simp only [T, hSingle, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
    refine ⟨joint, ?_⟩
    intro X
    let F : Matrix (ax × ay) (ax × ay) ℂ →ₗ[ℂ] Matrix (bx × oy) (bx × oy) ℂ :=
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearMap.comp
        (joint.toCompletelyPositiveMap.toLinearMap.comp
          CStarMatrix.ofMatrixStarAlgEquiv.toAlgEquiv.toLinearMap)
    have hX : X = ∑ i : ax × ay, ∑ j : ax × ay,
        X i j • Matrix.single i j (1 : ℂ) := by
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
        Matrix.matrix_eq_sum_single X
    change F X = _
    conv_lhs => rw [hX, map_sum]
    simp only [map_sum, map_smul, Fintype.sum_prod_type]
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change (∑ i : ax, ∑ u : ay, ∑ j : ax, ∑ v : ay,
        X (i, u) (j, v) * F (Matrix.single (i, u) (j, v) 1) p q) = _
    simp_rw [show ∀ i j u v, F (Matrix.single (i, u) (j, v) 1) = _ from hBasis]
    simp only [Matrix.kroneckerMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_assoc]

  have hMixtureChannel {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      {m : ℕ} (weight : Fin m → ℝ) (hWeight : ∀ i, 0 ≤ weight i)
      (hSum : ∑ i, weight i = 1) (channel : Fin m → QuantumChannel a b) :
      ∃ joint : QuantumChannel a b, ∀ X : Matrix a a ℂ,
        CStarMatrix.ofMatrix.symm
          (joint.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ i, (weight i : ℂ) • CStarMatrix.ofMatrix.symm
          ((channel i).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := by
    classical
    choose K hK hChannel using fun i => (channel_kraus_stinespring).1 (channel i)
    let T : Fin m × (b × a) → Matrix b a ℂ :=
      fun ik => (Real.sqrt (weight ik.1) : ℂ) • K ik.1 ik.2
    have hSqrt (i : Fin m) :
        star (Real.sqrt (weight i) : ℂ) * (Real.sqrt (weight i) : ℂ) =
          (weight i : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hWeight i)]
    have hSqrt' (i : Fin m) :
        (Real.sqrt (weight i) : ℂ) * star (Real.sqrt (weight i) : ℂ) =
          (weight i : ℂ) := by rw [mul_comm]; exact hSqrt i
    have hT : (∑ r, (T r)ᴴ * T r) = 1 := by
      simp only [T, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
      rw [Fintype.sum_prod_type]
      simp_rw [hSqrt', ← Finset.smul_sum, hK]
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, hSum, Complex.ofReal_one, one_smul]
    obtain ⟨joint, hJoint⟩ := finite_kraus_quantum_channel T hT
    refine ⟨joint, ?_⟩
    intro X
    rw [hJoint]
    simp only [T, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    rw [Fintype.sum_prod_type]
    simp_rw [hSqrt, ← Finset.smul_sum, ← hChannel]

  have hCoherent {A : Type u} [Fintype A] [DecidableEq A]
      (sector : A → Sector) (w : A → ℂ)
      (hweight : ∀ s, (∑ a, if sector a = s then ‖w a‖ ^ 2 else 0) = 1) :
      let V : Matrix (A × A) Sector ℂ :=
        fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
      Vᴴ * V = 1 ∧
        ∃ C : QuantumChannel Sector (A × A),
          ∀ X : Matrix Sector Sector ℂ,
            CStarMatrix.ofMatrix.symm
              (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = V * X * Vᴴ := by
    classical
    dsimp only
    let V : Matrix (A × A) Sector ℂ :=
      fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
    have hV : Vᴴ * V = 1 := by
      ext s t
      change (∑ xy : A × A, star (V xy s) * V xy t) = (if s = t then 1 else 0)
      rw [Fintype.sum_prod_type]
      have hdiag (a : A) :
          (∑ b, star (V (a, b) s) * V (a, b) t) =
          (if sector a = s then star (w a) else 0) *
            (if sector a = t then w a else 0) := by
        rw [Finset.sum_eq_single a]
        · simp only [V, Prod.fst, Prod.snd, eq_self_iff_true, true_and]
          split_ifs <;> simp_all
        · intro b _ hb
          simp [V, Ne.symm hb]
        · intro ha
          exact False.elim (ha (Finset.mem_univ a))
      simp_rw [hdiag]
      by_cases hst : s = t
      · subst t
        have hs : (∑ a, if sector a = s then ((‖w a‖ ^ 2 : ℝ) : ℂ) else 0) = 1 := by
          have hcast (a : A) : ((if sector a = s then ‖w a‖ ^ 2 else 0 : ℝ) : ℂ) =
              if sector a = s then ((‖w a‖ ^ 2 : ℝ) : ℂ) else 0 := by
            split_ifs <;> rfl
          simpa only [Complex.ofReal_sum, hcast, Complex.ofReal_one] using
            congrArg (fun x : ℝ => (x : ℂ)) (hweight s)
        calc
          _ = ∑ a, if sector a = s then ((‖w a‖ ^ 2 : ℝ) : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : sector a = s <;> simp [ha, Complex.star_def, Complex.conj_mul']
          _ = _ := by simpa using hs
      · simp only [if_neg hst]
        apply Finset.sum_eq_zero
        intro a _
        by_cases has : sector a = s
        · have hat : sector a ≠ t := by simpa [has] using hst
          simp [has, hst]
        · simp [has]
    let K : Unit → Matrix (A × A) Sector ℂ := fun _ => V
    have hK : (∑ j, (K j)ᴴ * K j) = 1 := by simpa [K] using hV
    obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
    refine ⟨hV, C, ?_⟩
    intro X
    simpa [K] using hC X

  have hSourceWeight
      (d : Sector → ℕ) (hd : ∀ s, 0 < d s)
      (spectrum : Sector → (Fin spectralSize) → ℝ) (hpositive : ∀ s j, 0 ≤ spectrum s j)
      (hsum : ∀ s, ∑ j, spectrum s j = 1) :
      ∀ s, (∑ x : Sigma (fun t => Fin (d t) × (Fin spectralSize)),
        if x.1 = s then ‖(Real.sqrt (spectrum x.1 x.2.2 / (d x.1 : ℝ)) : ℂ)‖ ^ 2 else 0) = 1 := by
    intro s
    have hnorm (t : Sector) (j : (Fin spectralSize)) :
        ‖(Real.sqrt (spectrum t j / (d t : ℝ)) : ℂ)‖ ^ 2 =
          spectrum t j / (d t : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (div_nonneg (hpositive t j) (Nat.cast_nonneg _))]
    simp_rw [hnorm]
    rw [Fintype.sum_sigma]
    have hblock (t : Sector) :
        (∑ x : Fin (d t) × (Fin spectralSize), if t = s then spectrum t x.2 / (d t : ℝ) else 0) =
          if t = s then 1 else 0 := by
      by_cases ht : t = s
      · subst t
        have hdne : (d s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd s))
        simp only [if_true, Fintype.sum_prod_type]
        simp [← Finset.sum_div, hsum, hdne]
      · simp [ht]
    simp_rw [hblock]
    simp

  have hTargetWeight
      (d : Sector → ℕ) (hd : ∀ s, 0 < d s) :
      ∀ s, (∑ x : Sigma (fun t => Fin (d t)),
        if x.1 = s then ‖(Real.sqrt ((d x.1 : ℝ)⁻¹) : ℂ)‖ ^ 2 else 0) = 1 := by
    intro s
    have hnorm (t : Sector) :
        ‖(Real.sqrt ((d t : ℝ)⁻¹) : ℂ)‖ ^ 2 = (d t : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))]
    simp_rw [hnorm]
    rw [Fintype.sum_sigma]
    have hblock (t : Sector) :
        (∑ _x : Fin (d t), if t = s then (d t : ℝ)⁻¹ else 0) =
          if t = s then 1 else 0 := by
      by_cases ht : t = s
      · subst t
        have hdne : (d s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd s))
        simp [hdne]
      · simp [ht]
    simp_rw [hblock]
    simp

  have hSplitting {A B : Type u} {J : Type} [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
      (e : A ≃ B × J) :
      ∃ C : QuantumChannel A B,
        ∀ X : Matrix A A ℂ,
          CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (fun b c => ∑ j, X (e.symm (b, j)) (e.symm (c, j))) := by
    classical
    let K : J → Matrix B A ℂ := fun j =>
      Matrix.of fun b a => if a = e.symm (b, j) then 1 else 0
    have hstar (j : J) (b : B) (a : A) :
        star (K j b a) = if a = e.symm (b, j) then 1 else 0 := by
      dsimp [K]
      split_ifs <;> simp
    have hK : (∑ j, (K j)ᴴ * K j) = 1 := by
      ext a c
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply]
      simp only [hstar]
      change (∑ j, ∑ b, (if a = e.symm (b, j) then (1 : ℂ) else 0) *
        (if c = e.symm (b, j) then 1 else 0)) = (if a = c then 1 else 0)
      rw [Finset.sum_comm]
      have hsum : (∑ b, ∑ j,
          (if a = e.symm (b, j) then (1 : ℂ) else 0) *
            (if c = e.symm (b, j) then 1 else 0)) =
          ∑ x : A, (if a = x then (1 : ℂ) else 0) * (if c = x then 1 else 0) := by
        let f : A → ℂ := fun x => (if a = x then 1 else 0) * (if c = x then 1 else 0)
        change (∑ b, ∑ j, f (e.symm (b, j))) = ∑ x, f x
        calc
          _ = ∑ z : B × J, f (e.symm z) := (Fintype.sum_prod_type _).symm
          _ = _ := e.symm.sum_comp f
      rw [hsum]
      by_cases hac : a = c
      · subst c
        simp
      · simp [hac]
    obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
    refine ⟨C, ?_⟩
    intro X
    rw [hC]
    ext b c
    simp only [Matrix.sum_apply]
    simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite]

  obtain ⟨hSourceIsometry, source, hSourceAction⟩ := hCoherent
    (A := SourceLocal (Coord := Fin spectralSize) M.d)
    (fun x => x.1)
    (fun x => (Real.sqrt (M.spectrum x.1 x.2.2 / (M.d x.1 : ℝ)) : ℂ))
    (hSourceWeight M.d M.positiveRank M.spectrum M.spectrumNonneg M.spectrumSum)
  obtain ⟨hTargetIsometry, target, hTargetAction⟩ := hCoherent
    (A := TargetLocal M.d) (fun x => x.1)
    (fun x => (Real.sqrt ((M.d x.1 : ℝ)⁻¹) : ℂ))
    (hTargetWeight M.d M.positiveRank)
  let encoding : EncodingChannels M :=
    { source := source
      target := target
      sourceAction := fun X => hSourceAction X
      targetAction := fun X => hTargetAction X }
  let splitEquiv : SourceLocal (Coord := Fin spectralSize) M.d ≃
      TargetLocal M.d × Fin spectralSize :=
    { toFun := fun x => (⟨x.1, x.2.1⟩, x.2.2)
      invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨splitting, hSplittingAction⟩ := hSplitting splitEquiv
  have hProductExists
      (left right : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d)) :
      ∃ joint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d), TensorRealization left right joint := by
    exact hTensorExist left right
  have hMixtureExists (m : ℕ) (weight : Fin m → ℝ)
      (hweight : weight ∈ stdSimplex ℝ (Fin m))
      (left right : Fin m → QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d)) :
      ∃ joint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d), MixtureRealization weight left right joint := by
    choose product hProduct using fun i => hTensorExist (left i) (right i)
    obtain ⟨joint, hJoint⟩ := hMixtureChannel weight hweight.1 hweight.2 product
    refine ⟨joint, ?_⟩
    intro X
    rw [hJoint]
    apply Finset.sum_congr rfl
    intro i _
    rw [hProduct i X]
    rfl
  obtain ⟨splittingJoint, hSplittingJoint⟩ := hProductExists splitting splitting

  have hCoherentSplit (e : (SourceLocal (Coord := Fin spectralSize) M.d) ≃ (TargetLocal M.d) × (Fin spectralSize))
      (sector : (TargetLocal M.d) → Sector) (w : (TargetLocal M.d) → ℂ) (f : Sector → (Fin spectralSize) → ℂ)
      (X : Matrix Sector Sector ℂ) (p q : (TargetLocal M.d) × (TargetLocal M.d)) :
      let V : Matrix ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) Sector ℂ := Matrix.of fun xy s =>
        if xy.1 = xy.2 ∧ sector (e xy.1).1 = s then
          w (e xy.1).1 * f (sector (e xy.1).1) (e xy.1).2 else 0
      let W : Matrix ((TargetLocal M.d) × (TargetLocal M.d)) Sector ℂ := Matrix.of fun xy s =>
        if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
      (∑ j, ∑ k, (V * X * Vᴴ)
        (e.symm (p.1, j), e.symm (p.2, k))
        (e.symm (q.1, j), e.symm (q.2, k))) =
        (W * (Matrix.of fun s t => (∑ j, f s j * star (f t j)) * X s t) * Wᴴ) p q := by
    classical
    dsimp only
    have hSourceEntry (sector : (SourceLocal (Coord := Fin spectralSize) M.d) → Sector) (w : (SourceLocal (Coord := Fin spectralSize) M.d) → ℂ)
        (X : Matrix Sector Sector ℂ) (xy uv : (SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) :
        let V : Matrix ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) Sector ℂ :=
          Matrix.of fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
        (V * X * Vᴴ) xy uv =
          if xy.1 = xy.2 ∧ uv.1 = uv.2 then
            w xy.1 * X (sector xy.1) (sector uv.1) * star (w uv.1) else 0 := by
      classical
      dsimp only
      let V : Matrix ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) Sector ℂ :=
        Matrix.of fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
      by_cases hxy : xy.1 = xy.2 <;> by_cases huv : uv.1 = uv.2
      all_goals
        simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hxy, huv,
          apply_ite, ite_mul, mul_ite]

    have hTargetEntry (sector : (TargetLocal M.d) → Sector) (w : (TargetLocal M.d) → ℂ)
        (X : Matrix Sector Sector ℂ) (xy uv : (TargetLocal M.d) × (TargetLocal M.d)) :
        let V : Matrix ((TargetLocal M.d) × (TargetLocal M.d)) Sector ℂ :=
          Matrix.of fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
        (V * X * Vᴴ) xy uv =
          if xy.1 = xy.2 ∧ uv.1 = uv.2 then
            w xy.1 * X (sector xy.1) (sector uv.1) * star (w uv.1) else 0 := by
      classical
      dsimp only
      let V : Matrix ((TargetLocal M.d) × (TargetLocal M.d)) Sector ℂ :=
        Matrix.of fun xy s => if xy.1 = xy.2 ∧ sector xy.1 = s then w xy.1 else 0
      by_cases hxy : xy.1 = xy.2 <;> by_cases huv : uv.1 = uv.2
      all_goals
        simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply, hxy, huv,
          apply_ite, ite_mul, mul_ite]
    simp_rw [hSourceEntry (fun a => sector (e a).1)
      (fun a => w (e a).1 * f (sector (e a).1) (e a).2) X]
    rw [hTargetEntry sector w]
    simp only [Equiv.apply_symm_apply, e.symm.injective.eq_iff, Prod.mk.injEq]
    by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2
    all_goals simp [hp, hq, ite_and]
    simp only [star_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

  have hSplitTensor (e : (SourceLocal (Coord := Fin spectralSize) M.d) ≃ (TargetLocal M.d) × (Fin spectralSize)) (C : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d))
      (hC : ∀ X : Matrix (SourceLocal (Coord := Fin spectralSize) M.d) (SourceLocal (Coord := Fin spectralSize) M.d) ℂ,
        CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (fun b c => ∑ j, X (e.symm (b, j)) (e.symm (c, j))))
      (X : Matrix ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) ℂ) (p q : (TargetLocal M.d) × (TargetLocal M.d)) :
      (∑ a : (SourceLocal (Coord := Fin spectralSize) M.d), ∑ c : (SourceLocal (Coord := Fin spectralSize) M.d), ∑ u : (SourceLocal (Coord := Fin spectralSize) M.d), ∑ v : (SourceLocal (Coord := Fin spectralSize) M.d),
        X (a, u) (c, v) *
          CStarMatrix.ofMatrix.symm
            (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single a c 1))) p.1 q.1 *
          CStarMatrix.ofMatrix.symm
            (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single u v 1))) p.2 q.2) =
        ∑ j, ∑ k, X (e.symm (p.1, j), e.symm (p.2, k))
          (e.symm (q.1, j), e.symm (q.2, k)) := by
    classical
    have hUnit (a c : (SourceLocal (Coord := Fin spectralSize) M.d)) (b d : (TargetLocal M.d)) :
        CStarMatrix.ofMatrix.symm
            (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single a c 1))) b d =
          ∑ j, if a = e.symm (b, j) ∧ c = e.symm (d, j) then (1 : ℂ) else 0 := by
      rw [hC]
      simp only [Matrix.single_apply]
    simp only [hUnit]
    calc
      _ = ∑ x : ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) × ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)), ∑ y : (Fin spectralSize) × (Fin spectralSize),
          X (x.1.1, x.2.1) (x.1.2, x.2.2) *
            (if x.1.1 = e.symm (p.1, y.1) ∧ x.1.2 = e.symm (q.1, y.1) then 1 else 0) *
            (if x.2.1 = e.symm (p.2, y.2) ∧ x.2.2 = e.symm (q.2, y.2) then 1 else 0) := by
        simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_comm
      _ = ∑ y : (Fin spectralSize) × (Fin spectralSize), ∑ x : ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)) × ((SourceLocal (Coord := Fin spectralSize) M.d) × (SourceLocal (Coord := Fin spectralSize) M.d)),
          X (x.1.1, x.2.1) (x.1.2, x.2.2) *
            (if x.1.1 = e.symm (p.1, y.1) ∧ x.1.2 = e.symm (q.1, y.1) then 1 else 0) *
            (if x.2.1 = e.symm (p.2, y.2) ∧ x.2.2 = e.symm (q.2, y.2) then 1 else 0) :=
        Finset.sum_comm
      _ = _ := by
        simp [Fintype.sum_prod_type, ite_and, mul_ite, ite_mul]

  have hSplittingSchurAction (X : Matrix Sector Sector ℂ) :
      CStarMatrix.ofMatrix.symm
        ((splittingJoint.comp encoding.source).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
            (targetEncoding M.d)ᴴ := by
    have hSourceCs : encoding.source.toCompletelyPositiveMap (CStarMatrix.ofMatrix X) =
        CStarMatrix.ofMatrix (sourceEncoding M.d M.spectrum * X *
          (sourceEncoding M.d M.spectrum)ᴴ) := by
      apply CStarMatrix.ofMatrix.symm.injective
      exact encoding.sourceAction X
    change CStarMatrix.ofMatrix.symm
      (splittingJoint.toCompletelyPositiveMap
        (encoding.source.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = _
    rw [hSourceCs]
    ext p q
    have hJoint := congrArg (fun Y : Matrix (TargetLocal M.d × TargetLocal M.d)
        (TargetLocal M.d × TargetLocal M.d) ℂ => Y p q)
      (hSplittingJoint (sourceEncoding M.d M.spectrum * X *
        (sourceEncoding M.d M.spectrum)ᴴ))
    rw [hJoint]
    change (∑ a, ∑ c, ∑ u, ∑ v,
      (sourceEncoding M.d M.spectrum * X * (sourceEncoding M.d M.spectrum)ᴴ) (a, u) (c, v) *
        CStarMatrix.ofMatrix.symm
          (splitting.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single a c 1))) p.1 q.1 *
        CStarMatrix.ofMatrix.symm
          (splitting.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single u v 1))) p.2 q.2) = _
    rw [hSplitTensor splitEquiv splitting hSplittingAction]
    have hWeight (s : Sector) (j : Fin spectralSize) :
        (Real.sqrt (M.spectrum s j / (M.d s : ℝ)) : ℂ) =
          (Real.sqrt ((M.d s : ℝ)⁻¹) : ℂ) * (Real.sqrt (M.spectrum s j) : ℂ) := by
      rw [div_eq_mul_inv, Real.sqrt_mul (M.spectrumNonneg s j)]
      push_cast
      ring
    have h := hCoherentSplit splitEquiv (fun x => x.1)
      (fun x => (Real.sqrt ((M.d x.1 : ℝ)⁻¹) : ℂ))
      (fun s j => (Real.sqrt (M.spectrum s j) : ℂ)) X p q
    let V : Matrix
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        Sector ℂ := Matrix.of fun xy s =>
      if xy.1 = xy.2 ∧ (splitEquiv xy.1).1.1 = s then
        (Real.sqrt ((M.d (splitEquiv xy.1).1.1 : ℝ)⁻¹) : ℂ) *
          (Real.sqrt (M.spectrum (splitEquiv xy.1).1.1 (splitEquiv xy.1).2) : ℂ)
      else 0
    let W : Matrix (TargetLocal M.d × TargetLocal M.d) Sector ℂ := Matrix.of fun xy s =>
      if xy.1 = xy.2 ∧ xy.1.1 = s then (Real.sqrt ((M.d xy.1.1 : ℝ)⁻¹) : ℂ) else 0
    let F : Matrix Sector Sector ℂ := Matrix.of fun s t =>
      (∑ j, (Real.sqrt (M.spectrum s j) : ℂ) * star (Real.sqrt (M.spectrum t j) : ℂ)) * X s t
    change (∑ j, ∑ k, (V * X * Vᴴ)
      (splitEquiv.symm (p.1, j), splitEquiv.symm (p.2, k))
      (splitEquiv.symm (q.1, j), splitEquiv.symm (q.2, k))) = (W * F * Wᴴ) p q at h
    have hV : V = sourceEncoding M.d M.spectrum := by
      ext xy s
      dsimp [V, sourceEncoding, splitEquiv]
      split_ifs <;> first | exact (hWeight _ _).symm | rfl
    have hW : W = targetEncoding M.d := rfl
    have hF : F = Matrix.of fun s t => (kernel M s t : ℂ) * X s t := by
      ext s t
      simp only [F, Matrix.of_apply, kernel, Complex.star_def, Complex.conj_ofReal,
        ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    rw [hV, hW, hF] at h
    exact h

  refine ⟨encoding, splitting, splittingJoint, hProductExists, hMixtureExists,
    hSplittingJoint, ?_, hSplittingSchurAction⟩
  simpa [splitEquiv] using hSplittingAction


end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
