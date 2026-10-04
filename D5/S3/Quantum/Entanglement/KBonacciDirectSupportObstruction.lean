/- GID: D5/S3/Quantum/Entanglement/KBonacciDirectSupportObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/KBonacciDirectSupportObstruction
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Actual legal concatenation bounds auxiliary rank through total spectral rows. -/

import D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation
import D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker InnerProductSpace
open Matrix
open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

namespace D5.S3.Quantum.Entanglement.KBonacciDirectSupportObstruction

set_option maxHeartbeats 1600000 in
-- The dependent spectral reconstruction and finite span estimates share one telescope.
/-- A given full-matrix two-page encoder has a reconstructed orthonormal spectral
family. Its total computational rows give every nested-neighborhood dimension bound,
including arbitrary spectral bases and cancellation between spectral terms. -/
theorem actual_encoder_spectral_obstruction (N k mX mY : ℕ)
    (hN : 2 ≤ N) (hk : 2 ≤ k) (_hmX : 1 ≤ mX) (_hmY : 1 ≤ mY) :
  let primeNumbers (N : ℕ) (b : Bool) : Finset (Fin (N + 1)) :=
    Finset.univ.filter (fun n => decide (Nat.Prime n.val) = b)

  let PrimePage (N : ℕ) (b : Bool) := ↥(primeNumbers N b)
  let Logical (N : ℕ) := Σ b : Bool, PrimePage N b
  let Word (m : ℕ) := Fin m → Bool

  let initialRun {m : ℕ} (w : Fin m → Bool) : ℕ :=
    (List.ofFn w).findIdx Bool.not

  let terminalRun {m : ℕ} (w : Fin m → Bool) : ℕ :=
    initialRun (fun i => w i.rev)

  let oneNeighborhood (k n s : ℕ) : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w => DBonacciAdmissible k n w ∧
      (List.ofFn w).head? = some true ∧ initialRun w < k - s)

  let logicalDimension (N : ℕ) (b : Bool) : ℕ := (primeNumbers N b).card

  let _orderedNumbers (N : ℕ) (b : Bool) :
      Fin (logicalDimension N b) ≃o PrimePage N b :=
    (primeNumbers N b).orderIsoOfFin rfl

  let wordPages (k m : ℕ) (b : Bool) : Finset (Word m) :=
    Finset.univ.filter (fun w => DBonacciAdmissible k m w ∧
      (List.ofFn w).head? = some b)

  let capacity (k m : ℕ) (b : Bool) : ℕ := (wordPages k m b).card
  let stateRows (k m s : ℕ) : ℕ :=
    ((wordPages k m true).filter (fun x => terminalRun x = s)).card
  let earlierRows (k m s : ℕ) : ℕ := ∑ u ∈ Finset.range s, stateRows k m u
  let neighborCount (k n s : ℕ) : ℕ := (oneNeighborhood k n s).card

  let zeroMaximum (N k mX mY : ℕ) : ℕ :=
    min (capacity k mX false) (capacity k mY false / logicalDimension N false)

  let oneMaximum (N k mX mY : ℕ) : ℕ :=
    ((List.range k).map (fun s =>
      earlierRows k mX s + neighborCount k mY s / logicalDimension N true)).foldl
        min (capacity k mX true)

  let logicalProjection (N : ℕ) (b : Bool) : Matrix (Logical N) (Logical N) ℂ :=
    Matrix.diagonal (fun l => if l.1 = b then 1 else 0)

  let physicalProjection (k m : ℕ) (b : Bool) : Matrix (Word m) (Word m) ℂ :=
    Matrix.diagonal (fun w => if w ∈ wordPages k m b then 1 else 0)

  let Encoder (N mX mY : ℕ) := Matrix (Word mX × Word mY) (Logical N) ℂ
  let PageStates (mX : ℕ) := Bool → DensityState (Word mX)

  let directContract (N k mX mY : ℕ) (J : Encoder N mX mY) (sigma : PageStates mX) : Prop :=
    J.conjTranspose * J = 1 ∧
    (∀ b : Bool,
      (physicalProjection k mX b ⊗ₖ (1 : Matrix (Word mY) (Word mY) ℂ)) * J =
        J * logicalProjection N b ∧
      ((1 : Matrix (Word mX) (Word mX) ℂ) ⊗ₖ physicalProjection k mY b) * J =
        J * logicalProjection N b ∧
      physicalProjection k mX b * CStarMatrix.ofMatrix.symm (sigma b).val *
        physicalProjection k mX b = CStarMatrix.ofMatrix.symm (sigma b).val) ∧
    (∀ A : Matrix (Logical N) (Logical N) ℂ,
      partialTraceRight (J * A * J.conjTranspose) =
        ∑ b : Bool, Matrix.trace (logicalProjection N b * A) •
          CStarMatrix.ofMatrix.symm (sigma b).val) ∧
    (∀ (psi : Logical N → ℂ) (x : Word mX) (y : Word mY),
      ¬ DBonacciAdmissible k (mX + mY) (Fin.append x y) →
        (Matrix.mulVec J psi) (x, y) = 0)
  let pageRank (sigma : PageStates mX) (b : Bool) : ℕ :=
    Matrix.rank (CStarMatrix.ofMatrix.symm (sigma b).val)
  ∀ (J : Encoder N mX mY) (sigma : PageStates mX),
    directContract N k mX mY J sigma → ∀ b : Bool,
    let hPos : (CStarMatrix.ofMatrix.symm (sigma b).val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sigma b).property.1)
    let E := hPos.isHermitian.eigenvectorBasis
    let lam := hPos.isHermitian.eigenvalues
    let D := {j : Word mX // lam j ≠ 0}
    let q : Word mX → (D → ℂ) := fun x j => (Real.sqrt (lam j.val) : ℂ) * E j.val x
    ∃ W : Matrix (Word mY) (PrimePage N b × D) ℂ,
      W.conjTranspose * W = 1 ∧
      (∀ r x y, J (x,y) ⟨b,r⟩ = ∑ j : D, q x j * W y (r,j)) ∧
      (∀ r j y, y ∉ wordPages k mY b → W y (r,j) = 0) ∧
      Submodule.span ℂ (q '' (wordPages k mX b : Set (Word mX))) = ⊤ ∧
      (b = true → ∀ s : ℕ, s < k →
        let rows := (wordPages k mX b).filter (fun x => s ≤ terminalRun x)
        let V := Submodule.span ℂ (q '' (rows : Set (Word mX)))
        pageRank sigma b ≤ earlierRows k mX s + Module.finrank ℂ V ∧
        (∀ (r : PrimePage N b) (u : D → ℂ), u ∈ V → ∀ y : Word mY,
          y ∉ oneNeighborhood k mY s → ∑ j : D, W y (r,j) * u j = 0) ∧
        logicalDimension N b * Module.finrank ℂ V ≤ neighborCount k mY s) ∧
      pageRank sigma b ≤ if b then oneMaximum N k mX mY else zeroMaximum N k mX mY := by
  classical
  extract_lets primeNumbers PrimePage Logical Word initialRun terminalRun oneNeighborhood logicalDimension _orderedNumbers wordPages capacity stateRows earlierRows neighborCount zeroMaximum oneMaximum logicalProjection physicalProjection Encoder PageStates directContract pageRank
  intro J sigma hc b

  have hsupport (r : PrimePage N b) (x : Word mX) (y : Word mY)
      (hy : y ∉ wordPages k mY b) : J (x,y) ⟨b,r⟩ = 0 := by
    have h := congrArg (fun K : Encoder N mX mY => K (x,y) ⟨b,r⟩) (hc.2.1 b).2.1
    simp [Encoder, Word, Logical, PrimePage, physicalProjection, logicalProjection, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, hy] at h
    exact h.symm
  have hunit (r t : PrimePage N b) (x z : Word mX) :
      (∑ y : Word mY, J (x,y) ⟨b,r⟩ * star (J (z,y) ⟨b,t⟩)) =
        (if r = t then 1 else 0) * (CStarMatrix.ofMatrix.symm (sigma b).val) x z := by
    have h := congrArg (fun A : Matrix (Word mX) (Word mX) ℂ => A x z)
      (hc.2.2.1 (Matrix.single ⟨b,r⟩ ⟨b,t⟩ 1))
    simp [Encoder, Word, Logical, PrimePage, partialTraceRight, Matrix.mul_apply, Matrix.single_apply,
      Matrix.trace_mul_single, logicalProjection, Matrix.diagonal_apply, ite_and] at h
    by_cases hrt : r = t
    · simpa [hrt] using h
    · simpa [hrt, Ne.symm hrt] using h
  let T : Matrix (↥(wordPages k mY b) × Word mX) (PrimePage N b) ℂ :=
    fun yx r => J (yx.2,yx.1.val) ⟨b,r⟩
  have hrepl : UniversalReplacement T (sigma b) := by
    intro rho
    let R : Matrix (PrimePage N b) (PrimePage N b) ℂ := CStarMatrix.ofMatrix.symm rho.val
    ext x z
    change (∑ y : ↥(wordPages k mY b),
      ((T * R) * T.conjTranspose) (y,x) (y,z)) =
        (CStarMatrix.ofMatrix.symm (sigma b).val) x z
    change (∑ y : ↥(wordPages k mY b), ∑ t : PrimePage N b,
      (∑ r : PrimePage N b, J (x,y.val) ⟨b,r⟩ * (R) r t) *
        star (J (z,y.val) ⟨b,t⟩)) = (CStarMatrix.ofMatrix.symm (sigma b).val) x z
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hexchange :
        (∑ t : PrimePage N b, ∑ y : ↥(wordPages k mY b), ∑ r : PrimePage N b,
          J (x,y.val) ⟨b,r⟩ * (R) r t * star (J (z,y.val) ⟨b,t⟩)) =
        (∑ t : PrimePage N b, ∑ r : PrimePage N b, ∑ y : ↥(wordPages k mY b),
          J (x,y.val) ⟨b,r⟩ * (R) r t * star (J (z,y.val) ⟨b,t⟩)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    rw [hexchange]
    have hs (r t : PrimePage N b) :
        (∑ y : ↥(wordPages k mY b), J (x,y.val) ⟨b,r⟩ * star (J (z,y.val) ⟨b,t⟩)) =
          (if r = t then 1 else 0) * (CStarMatrix.ofMatrix.symm (sigma b).val) x z := by
      rw [← Finset.sum_subtype (wordPages k mY b) (by simp) (fun y =>
        J (x,y) ⟨b,r⟩ * star (J (z,y) ⟨b,t⟩))]
      rw [Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => by
        simp [hsupport r x y hy])]
      exact hunit r t x z
    simp_rw [show ∀ (r t : PrimePage N b) (y : ↥(wordPages k mY b)),
      J (x,y.val) ⟨b,r⟩ * (R) r t * star (J (z,y.val) ⟨b,t⟩) =
        (R) r t * (J (x,y.val) ⟨b,r⟩ * star (J (z,y.val) ⟨b,t⟩)) by intros; ring]
    simp_rw [← Finset.mul_sum, hs]
    have hreduce (t : PrimePage N b) :
        (∑ r : PrimePage N b, R r t * ((if r = t then 1 else 0) *
          (CStarMatrix.ofMatrix.symm (sigma b).val) x z)) =
        R t t * (CStarMatrix.ofMatrix.symm (sigma b).val) x z := by
      rw [Finset.sum_eq_single t]
      · rw [if_pos rfl, one_mul]
      · intro r _ hrt
        rw [if_neg hrt, zero_mul, mul_zero]
      · intro h
        exact False.elim (h (Finset.mem_univ t))
    simp_rw [hreduce]
    rw [← Finset.sum_mul]
    have ht : (∑ r : PrimePage N b, (R) r r) = 1 := rho.property.2
    rw [ht, one_mul]
  let hPos : (CStarMatrix.ofMatrix.symm (sigma b).val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sigma b).property.1)
  let E := hPos.isHermitian.eigenvectorBasis
  let lam := hPos.isHermitian.eigenvalues
  let D := {j : Word mX // lam j ≠ 0}
  let q : Word mX → (D → ℂ) := fun x j => (Real.sqrt (lam j.val) : ℂ) * E j.val x
  let v : PrimePage N b × D → EuclideanSpace ℂ ↥(wordPages k mY b) := fun rj =>
    (Real.sqrt (lam rj.2.val) : ℂ)⁻¹ • WithLp.toLp 2
      (fun y => ∑ x : Word mX, star (E rj.2.val x) * J (x,y.val) ⟨b,rj.1⟩)
  have hv : Orthonormal ℂ v := (universal_replacement_capacity_growth T (sigma b) hrepl).1
  let W : Matrix (Word mY) (PrimePage N b × D) ℂ :=
    fun y rj => if hy : y ∈ wordPages k mY b then v rj ⟨y,hy⟩ else 0
  have hWsupport (r : PrimePage N b) (j : D) (y : Word mY)
      (hy : y ∉ wordPages k mY b) : W y (r,j) = 0 := by simp [W,hy]
  have hWorth : W.conjTranspose * W = 1 := by
    ext rj ti
    change (∑ y, star (W y rj) * W y ti) = if rj = ti then 1 else 0
    calc
      _ = ∑ y ∈ wordPages k mY b, star (W y rj) * W y ti := by
        symm
        exact Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => by simp [W,hy])
      _ = ∑ y : ↥(wordPages k mY b), star (W y.val rj) * W y.val ti :=
        Finset.sum_subtype _ (by simp) _
      _ = _ := by
        simpa [W, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using
          orthonormal_iff_ite.mp hv rj ti
  have hcolgram (r : PrimePage N b) :
      let Q : Matrix (Word mX) (Word mY) ℂ := fun x y => J (x,y) ⟨b,r⟩
      Q * Q.conjTranspose = CStarMatrix.ofMatrix.symm (sigma b).val := by
    dsimp only
    ext x z
    change (∑ y, J (x,y) ⟨b,r⟩ * star (J (z,y) ⟨b,r⟩)) = _
    simpa using hunit r r x z
  have hzero (r : PrimePage N b) (j : Word mX) (hj : lam j = 0) (y : Word mY) :
      (∑ x : Word mX, star (E j x) * J (x,y) ⟨b,r⟩) = 0 := by
    let Q : Matrix (Word mX) (Word mY) ℂ := fun x y => J (x,y) ⟨b,r⟩
    have heig : (Q * Q.conjTranspose) *ᵥ (fun x => E j x) = 0 := by
      rw [hcolgram r]
      simpa [lam, E, hj] using hPos.isHermitian.mulVec_eigenvectorBasis j
    have hz := (Matrix.self_mul_conjTranspose_mulVec_eq_zero Q (fun x => E j x)).mp heig
    have hy : (∑ x, star (J (x,y) ⟨b,r⟩) * E j x) = 0 := congrFun hz y
    have hy' := congrArg star hy
    simpa [star_sum, star_mul, mul_comm] using hy'
  have hreconstruct (r : PrimePage N b) (x : Word mX) (y : Word mY) :
      J (x,y) ⟨b,r⟩ = ∑ j : D, q x j * W y (r,j) := by
    by_cases hy : y ∈ wordPages k mY b
    · let ev : EuclideanSpace ℂ (Word mX) →ₗ[ℂ] ℂ :=
        (LinearMap.proj x).comp (WithLp.linearEquiv 2 ℂ (Word mX → ℂ)).toLinearMap
      have hexp := congrArg ev (E.sum_repr' (WithLp.toLp 2 (fun z => J (z,y) ⟨b,r⟩)))
      rw [map_sum] at hexp
      simp only [map_smul] at hexp
      change (∑ j : Word mX, ⟪E j, WithLp.toLp 2 (fun z => J (z,y) ⟨b,r⟩)⟫_ℂ * E j x) =
        J (x,y) ⟨b,r⟩ at hexp
      have hexp' : (∑ j : Word mX, (∑ z : Word mX, star (E j z) * J (z,y) ⟨b,r⟩) * E j x) =
        J (x,y) ⟨b,r⟩ := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hexp
      rw [← hexp']
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Word mX => lam j ≠ 0)]
      have hz : (∑ j : {j : Word mX // ¬ lam j ≠ 0},
        (∑ z, star (E j.val z) * J (z,y) ⟨b,r⟩) * E j.val x) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hzero r j.val (not_ne_iff.mp j.property) y, zero_mul]
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have hn : (Real.sqrt (lam j.val) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne
          (hPos.eigenvalues_nonneg j.val) j.property.symm))
      simp only [W, dif_pos hy]
      change (∑ z, star (E j.val z) * J (z,y) ⟨b,r⟩) * E j.val x =
        ((Real.sqrt (lam j.val) : ℂ) * E j.val x) *
          ((Real.sqrt (lam j.val) : ℂ)⁻¹ * (∑ z, star (E j.val z) * J (z,y) ⟨b,r⟩))
      field_simp
    · rw [hsupport r x y hy]
      simp [hWsupport r, hy]
  have hXsupport (j : D) (x : Word mX) (hx : x ∉ wordPages k mX b) : E j.val x = 0 := by
    have hs := congrArg (fun A : Matrix (Word mX) (Word mX) ℂ => A x)
      (hc.2.1 b).2.2
    have hsrow (z : Word mX) : (CStarMatrix.ofMatrix.symm (sigma b).val) x z = 0 := by
      have h := congrFun hs z
      simpa [physicalProjection, Matrix.diagonal_mul, Matrix.mul_diagonal, hx] using h.symm
    have heig := congrFun (hPos.isHermitian.mulVec_eigenvectorBasis j.val) x
    have heig' : (lam j.val : ℂ) * E j.val x = 0 := by
      simpa [Matrix.mulVec, dotProduct, hsrow, E, lam] using heig.symm
    exact (mul_eq_zero.mp heig').resolve_left (by exact_mod_cast j.property)
  have hqzero (x : Word mX) (hx : x ∉ wordPages k mX b) : q x = 0 := by
    funext j
    simp [q, hXsupport j x hx]
  let F : Matrix (Word mX) D ℂ := q
  have heinner (i j : D) :
      (∑ x : Word mX, star (E i.val x) * E j.val x) = if i = j then 1 else 0 := by
    have h := orthonormal_iff_ite.mp E.orthonormal i.val j.val
    have hij : (i.val = j.val) ↔ i = j := Subtype.ext_iff.symm
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm, hij] using h
  have hFgram : F.conjTranspose * F = Matrix.diagonal (fun j : D => (lam j.val : ℂ)) := by
    ext i j
    change (∑ x : Word mX, star (q x i) * q x j) = if i = j then (lam i.val : ℂ) else 0
    calc
      _ = ((Real.sqrt (lam i.val) : ℂ) * (Real.sqrt (lam j.val) : ℂ)) *
          (∑ x : Word mX, star (E i.val x) * E j.val x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        simp only [q, star_mul]
        simp only [show ∀ t : ℝ, star (t : ℂ) = (t : ℂ) from fun t => by simp]
        ring
      _ = _ := by
        rw [heinner]
        by_cases hij : i = j
        · subst j
          simp only [if_true, mul_one]
          exact_mod_cast Real.mul_self_sqrt (hPos.eigenvalues_nonneg i.val)
        · simp [hij]
  have hFrank : F.rank = Fintype.card D := by
    rw [← Matrix.rank_conjTranspose_mul_self F, hFgram, Matrix.rank_diagonal]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    simp [show ∀ j : D, lam j.val ≠ 0 from fun j => j.property]
  have hfull : Submodule.span ℂ (Set.range q) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank ℂ (Submodule.span ℂ (Set.range F.row)) = _
    rw [← Matrix.rank_eq_finrank_span_row F]
    simpa only [Module.finrank_pi] using hFrank
  have hqspan : Submodule.span ℂ (q '' (wordPages k mX b : Set (Word mX))) = ⊤ := by
    apply top_le_iff.mp
    rw [← hfull]
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    by_cases hx : x ∈ wordPages k mX b
    · exact Submodule.subset_span ⟨x,hx,rfl⟩
    · rw [hqzero x hx]
      exact Submodule.zero_mem _
  have hthreshold (hb : b = true) (s : ℕ) (hs : s < k) :
      let rows := (wordPages k mX b).filter (fun x => s ≤ terminalRun x)
      let V := Submodule.span ℂ (q '' (rows : Set (Word mX)))
      pageRank sigma b ≤ earlierRows k mX s + Module.finrank ℂ V ∧
      (∀ (r : PrimePage N b) (u : D → ℂ), u ∈ V → ∀ y : Word mY,
        y ∉ oneNeighborhood k mY s → ∑ j : D, W y (r,j) * u j = 0) ∧
      logicalDimension N b * Module.finrank ℂ V ≤ neighborCount k mY s := by
    subst b
    let rows := (wordPages k mX true).filter (fun x => s ≤ terminalRun x)
    let low := (wordPages k mX true).filter (fun x => terminalRun x < s)
    let V := Submodule.span ℂ (q '' (rows : Set (Word mX)))
    let U := Submodule.span ℂ (q '' (low : Set (Word mX)))
    have hlows : low.card = earlierRows k mX s := by
      symm
      simpa [earlierRows, stateRows, low, Finset.mem_range] using
        Finset.sum_card_fiberwise_eq_card_filter (wordPages k mX true) (Finset.range s)
          (fun x : Word mX => terminalRun x)
    have hsplit : U ⊔ V = ⊤ := by
      apply top_le_iff.mp
      rw [← hqspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,rfl⟩
      by_cases hxs : terminalRun x < s
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨x,Finset.mem_filter.mpr ⟨hx,hxs⟩,rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span
          ⟨x,Finset.mem_filter.mpr ⟨hx,Nat.le_of_not_gt hxs⟩,rfl⟩)
    have hUdim : Module.finrank ℂ U ≤ low.card := by
      have h := finrank_span_finset_le_card (R := ℂ) (low.image q)
      have himage : ((low.image q : Finset (D → ℂ)) : Set (D → ℂ)) =
          q '' (low : Set (Word mX)) := Finset.coe_image
      rw [himage] at h
      exact h.trans (Finset.card_image_le)
    have hRankD : pageRank sigma true = Fintype.card D := hPos.isHermitian.rank_eq_card_non_zero_eigs
    have hdim : pageRank sigma true ≤ earlierRows k mX s + Module.finrank ℂ V := by
      have h := Submodule.finrank_add_le_finrank_add_finrank U V
      rw [hsplit, finrank_top, Module.finrank_pi, ← hRankD] at h
      rw [hlows] at hUdim
      omega
    have hillegal (r : PrimePage N true) (x : Word mX) (y : Word mY)
        (hbad : ¬ DBonacciAdmissible k (mX+mY) (Fin.append x y)) : J (x,y) ⟨true,r⟩ = 0 := by
      have h := hc.2.2.2 (Pi.single ⟨true,r⟩ 1) x y hbad
      simpa [Encoder, Word, Logical, PrimePage, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h
    have hrows (r : PrimePage N true) (x : Word mX) (hx : x ∈ rows)
        (y : Word mY) (hy : y ∉ oneNeighborhood k mY s) :
        ∑ j : D, W y (r,j) * q x j = 0 := by
      by_cases hypage : y ∈ wordPages k mY true
      · have hxdata := Finset.mem_filter.mp hx
        have hxlegal : DBonacciAdmissible k mX x := (Finset.mem_filter.mp hxdata.1).2.1
        have hydata := (Finset.mem_filter.mp hypage).2
        have hj := (actual_direct_concatenation k mX mY hk).1 x y hxlegal hydata.1
        have hbad : ¬ DBonacciAdmissible k (mX+mY) (Fin.append x y) := by
          intro hjoin
          have ht := hj.2.2.mp hjoin
          apply hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hydata.1,hydata.2,by
            change terminalRun x + initialRun y < k at ht
            omega⟩
        have hz := hillegal r x y hbad
        rw [hreconstruct] at hz
        simpa [mul_comm] using hz
      · simp [hWsupport r, hypage]
    have hspanlegal (r : PrimePage N true) (u : D → ℂ) (hu : u ∈ V)
        (y : Word mY) (hy : y ∉ oneNeighborhood k mY s) :
        ∑ j : D, W y (r,j) * u j = 0 := by
      induction hu using Submodule.span_induction with
      | mem u hu =>
          rcases hu with ⟨x,hx,rfl⟩
          exact hrows r x hx y hy
      | zero => simp
      | add u v _ _ hu hv => simp [mul_add, Finset.sum_add_distrib,hu,hv]
      | smul c u _ hu =>
          simpa [mul_left_comm, ← Finset.mul_sum] using congrArg (fun z : ℂ => c*z) hu
    let L : (PrimePage N true → V) →ₗ[ℂ] (↥(oneNeighborhood k mY s) → ℂ) :=
      { toFun := fun f y => ∑ r : PrimePage N true, ∑ j : D, W y.val (r,j) * (f r).val j
        map_add' := by intros f g; ext y; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by intros c f; ext y; simp [mul_left_comm, Finset.mul_sum] }
    have hLinj : Function.Injective L := by
      apply (LinearMap.ker_eq_bot).mp
      apply LinearMap.ker_eq_bot'.mpr
      intro f hf
      let a : PrimePage N true × D → ℂ := fun rj => (f rj.1).val rj.2
      have hWa : Matrix.mulVec W a = 0 := by
        funext y
        by_cases hy : y ∈ oneNeighborhood k mY s
        · have h := congrFun hf ⟨y,hy⟩
          simpa [L, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, a] using h
        · change (∑ rj : PrimePage N true × D, W y rj * a rj) = 0
          rw [Fintype.sum_prod_type]
          apply Finset.sum_eq_zero
          intro r _
          exact hspanlegal r (f r).val (f r).property y hy
      have ha : a = 0 := by
        have h := congrArg (Matrix.mulVec W.conjTranspose) hWa
        rw [Matrix.mulVec_mulVec, hWorth, Matrix.one_mulVec, Matrix.mulVec_zero] at h
        exact h
      funext r
      apply Subtype.ext
      funext j
      exact congrFun ha (r,j)
    have hcapacity := LinearMap.finrank_le_finrank_of_injective hLinj
    have hcap : logicalDimension N true * Module.finrank ℂ V ≤ neighborCount k mY s := by
      simpa [Module.finrank_pi_fintype, Module.finrank_pi, logicalDimension, PrimePage, neighborCount] using hcapacity
    exact ⟨hdim,hspanlegal,hcap⟩
  have hRankD : pageRank sigma b = Fintype.card D := hPos.isHermitian.rank_eq_card_non_zero_eigs
  have hXdim : pageRank sigma b ≤ capacity k mX b := by
    have h := finrank_span_finset_le_card (R := ℂ) ((wordPages k mX b).image q)
    have himage : (((wordPages k mX b).image q : Finset (D → ℂ)) : Set (D → ℂ)) =
        q '' (wordPages k mX b : Set (Word mX)) := Finset.coe_image
    rw [himage] at h
    change Module.finrank ℂ (Submodule.span ℂ (q '' (wordPages k mX b : Set (Word mX)))) ≤ _ at h
    rw [hqspan, finrank_top, Module.finrank_pi, ← hRankD] at h
    exact h.trans (Finset.card_image_le)
  have hYdim : logicalDimension N b * pageRank sigma b ≤ capacity k mY b := by
    simpa [logicalDimension,PrimePage,pageRank,capacity] using
      (universal_replacement_capacity_growth T (sigma b) hrepl).2
  have hMpos : 0 < logicalDimension N b := by
    apply Finset.card_pos.mpr
    cases b
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [primeNumbers, Nat.not_prime_zero]
    · refine ⟨⟨2, by omega⟩, ?_⟩
      simp [primeNumbers, Nat.prime_two]
  have hmaximum : pageRank sigma b ≤ if b then oneMaximum N k mX mY else zeroMaximum N k mX mY := by
    cases b
    · apply le_min hXdim
      exact (Nat.le_div_iff_mul_le hMpos).mpr (by simpa [mul_comm] using hYdim)
    · have hbounds (s : ℕ) (hs : s < k) :
          pageRank sigma true ≤ earlierRows k mX s + neighborCount k mY s / logicalDimension N true := by
        have h := hthreshold rfl s hs
        dsimp only at h
        have hd : Module.finrank ℂ (Submodule.span ℂ (q ''
            ((wordPages k mX true).filter (fun x => s ≤ terminalRun x) : Set (Word mX)))) ≤
              neighborCount k mY s / logicalDimension N true := by
          apply (Nat.le_div_iff_mul_le hMpos).mpr
          simpa [mul_comm] using h.2.2
        exact h.1.trans (Nat.add_le_add_left hd _)
      have hfold : ∀ (l : List ℕ) (c : ℕ), pageRank sigma true ≤ c →
          (∀ n ∈ l, pageRank sigma true ≤ n) → pageRank sigma true ≤ l.foldl min c := by
        intro l
        induction l with
        | nil => intros; assumption
        | cons n l ih =>
          intro c hdc hall
          apply ih (min c n) (le_min hdc (hall n (by simp)))
          intro u hu
          exact hall u (by simp [hu])
      apply hfold _ _ hXdim
      intro n hn
      rcases List.mem_map.mp hn with ⟨s,hs,rfl⟩
      exact hbounds s (List.mem_range.mp hs)
  exact ⟨W,hWorth,hreconstruct,hWsupport,hqspan,hthreshold,hmaximum⟩


#print axioms actual_encoder_spectral_obstruction

end D5.S3.Quantum.Entanglement.KBonacciDirectSupportObstruction
