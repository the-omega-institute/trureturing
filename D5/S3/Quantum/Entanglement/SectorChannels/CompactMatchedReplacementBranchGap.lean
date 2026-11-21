/- GID: D5/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/CompactMatchedReplacementBranchGap
   mirror-E: none(waiver:finite-physical-channel-construction)
   anchors: []
   utility: none
   digest: The shared-classical branch lower bound for correlated replacement on actual compact flat carriers. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Entanglement.SectorChannels.CompactMatchedReplacementBranchGap

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker

/-- The overlap estimate uses only the arithmetic-geometric mean of two
weights. In particular no Hilbert-space or spectral hypothesis is hidden. -/
private theorem min_square_mul_le_half_sum (c a b : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (c ^ 2) (a*b) ≤ c * (a+b) / 2 := by
  by_cases h : 2*c ≤ a+b
  · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hc (sub_nonneg.mpr h)])
  · have h := lt_of_not_ge h
    have hh : 0 ≤ (a+b)*(2*c-(a+b)) :=
      mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr h.le)
    exact (min_le_right _ _).trans (by nlinarith [sq_nonneg (a-b)])

private theorem min_sum_le_sum_min {α : Type*} (s : Finset α) (z : α → ℝ) (d : ℝ)
    (hd : 0 ≤ d) (hz : ∀ i, 0 ≤ z i) :
    min d (∑ i ∈ s, z i) ≤ ∑ i ∈ s, min d (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [min_eq_right hd]
  | @insert a s h ih =>
    rw [Finset.sum_insert h, Finset.sum_insert h]
    refine le_trans ?_ (add_le_add (le_refl _) ih)
    by_cases h₁ : d ≤ z a
    · rw [min_eq_left h₁]
      exact (min_le_left _ _).trans <| le_add_of_nonneg_right <|
        le_min hd (Finset.sum_nonneg fun i _ => hz i)
    by_cases h₂ : d ≤ ∑ i ∈ s, z i
    · rw [min_eq_left h₂]
      exact (min_le_left _ _).trans <| le_add_of_nonneg_left <| le_min hd (hz a)
    rw [min_eq_right (le_of_not_ge h₁), min_eq_right (le_of_not_ge h₂)]
    exact min_le_right _ _

private theorem weighted_branch_overlap {ι : Type*} [Fintype ι]
    (c w : ℝ) (hc : 0 ≤ c) (hw : 0 ≤ w) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (has : ∑ i, a i = 1) (hbs : ∑ i, b i = 1) :
    (∑ i, min (c^2) (w * (a i * b i))) ≤ c * Real.sqrt w := by
  have hnon := Real.sqrt_nonneg w
  calc
    _ ≤ ∑ i, c * (Real.sqrt w * a i + Real.sqrt w * b i) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := min_square_mul_le_half_sum c (Real.sqrt w * a i) (Real.sqrt w * b i)
        hc (mul_nonneg hnon (ha i)) (mul_nonneg hnon (hb i))
      have he : (Real.sqrt w * a i) * (Real.sqrt w * b i) = w * (a i * b i) := by
        calc
          _ = (Real.sqrt w)^2 * (a i * b i) := by ring
          _ = _ := by rw [Real.sq_sqrt hw]
      rwa [he] at h
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, has, hbs]
      ring

private theorem shared_branch_overlap {ι β : Type*} [Fintype ι] [Fintype β]
    (c : ℝ) (hc : 0 ≤ c) (w : β → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hws : ∑ k, w k = 1) (a b : β → ι → ℝ)
    (ha : ∀ k i, 0 ≤ a k i) (hb : ∀ k i, 0 ≤ b k i)
    (has : ∀ k, ∑ i, a k i = 1) (hbs : ∀ k, ∑ i, b k i = 1) :
    (∑ i, min (c^2) (∑ k, w k * (a k i * b k i))) ≤
      c * Real.sqrt (Fintype.card β : ℝ) := by
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset β))
      (f := fun _ => (1 : ℝ)) (g := w) (r := fun k => Real.sqrt (w k))
      (fun _ _ => zero_le_one) (fun k _ => hw k) (by
        intro k _
        rw [Real.sq_sqrt (hw k), one_mul])
  have hs' : (∑ k, Real.sqrt (w k))^2 ≤ (Fintype.card β : ℝ) := by
    simpa [hws] using hs
  have hroot : (∑ k, Real.sqrt (w k)) ≤ Real.sqrt (Fintype.card β : ℝ) := by
    have hleft : 0 ≤ ∑ k, Real.sqrt (w k) := Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
    have hright := Real.sqrt_nonneg (Fintype.card β : ℝ)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (Fintype.card β : ℝ) by positivity)]
  calc
    _ ≤ ∑ i, ∑ k, min (c^2) (w k * (a k i * b k i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact min_sum_le_sum_min _ _ _ (sq_nonneg c)
        (fun k => mul_nonneg (hw k) (mul_nonneg (ha k i) (hb k i)))
    _ = ∑ k, ∑ i, min (c^2) (w k * (a k i * b k i)) := Finset.sum_comm
    _ ≤ ∑ k, c * Real.sqrt (w k) := Finset.sum_le_sum fun k _ =>
      weighted_branch_overlap c (w k) hc (hw k) _ _ (ha k) (hb k) (has k) (hbs k)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hroot hc


private theorem shared_branch_l1_lower {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (c : ℝ) (hc : 0 ≤ c) (hn : (Fintype.card ι : ℝ) * c^2 = 1)
    (w : β → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1) (a b : β → ι → ℝ)
    (ha : ∀ k i, 0 ≤ a k i) (hb : ∀ k i, 0 ≤ b k i)
    (has : ∀ k, ∑ i, a k i = 1) (hbs : ∀ k, ∑ i, b k i = 1) :
    2 * (1-c * Real.sqrt (Fintype.card β : ℝ)) ≤
      ∑ i, ∑ j, |(if i = j then c^2 else 0) - ∑ k, w k * (a k i * b k j)| := by
  let q i j := ∑ k, w k * (a k i * b k j)
  have hq (i j : ι) : 0 ≤ q i j := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hw k) (mul_nonneg (ha k i) (hb k j))
  have hqsum : (∑ i, ∑ j, q i j) = 1 := by
    calc
      _ = ∑ i : ι, ∑ k : β, ∑ j : ι, w k * (a k i * b k j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ i : ι, ∑ k : β, w k * a k i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        simp_rw [← mul_assoc, ← Finset.mul_sum, hbs, mul_one]
      _ = ∑ k : β, ∑ i : ι, w k * a k i := Finset.sum_comm
      _ = 1 := by simp_rw [← Finset.mul_sum, has, mul_one]; exact hws
  have hD (i : ι) : (∑ j : ι, if i = j then c^2 else 0) = c^2 := by
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro j _ hj
      rw [ite_eq_right (Ne.symm hj)]
    · simp
  have hM (i : ι) : (∑ j, min (if i = j then c^2 else 0) (q i j)) = min (c^2) (q i i) := by
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro j _ hj
      rw [ite_eq_right (Ne.symm hj), min_eq_left (hq i j)]
    · simp
  have hO := shared_branch_overlap c hc w hw hws a b ha hb has hbs
  change (∑ i, min (c^2) (q i i)) ≤ _ at hO
  have hAbs (x y : ℝ) : |x-y| = x+y-2*min x y := by
    rcases le_total x y with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]; ring
  change _ ≤ ∑ i, ∑ j, |(if i = j then c^2 else 0) - q i j|
  simp_rw [hAbs, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [hD, hM, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hn, hqsum]
  linarith

private theorem diagonal_l1_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.IsHermitian) : ∑ i, |(X i i).re| ≤ traceNorm X := by
  let P := posPart X
  let N := negPart X
  have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have hN : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  have he : X = P - N := (CFC.posPart_sub_negPart X hX).symm
  rw [trace_norm_jordan_mass X hX]
  change (∑ i, |(X i i).re|) ≤ P.trace.re + N.trace.re
  have hi (i : n) : |(X i i).re| ≤ (P i i).re + (N i i).re := by
    rw [he]
    change |(P i i).re - (N i i).re| ≤ _
    exact abs_sub_le_iff.mpr ⟨by linarith [(Complex.nonneg_iff.mp (hN.diag_nonneg (i := i))).1],
      by linarith [(Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).1]⟩
  simpa [trace, Matrix.diag, Finset.sum_add_distrib] using Finset.sum_le_sum fun i _ => hi i

private theorem referenceError_le_diamond {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t] {n : ℕ}
    (A B : QuantumChannel s t) (rho : DensityState (Fin n × s)) :
    referenceError A B rho ≤ diamondDistance A B := by
  unfold diamondDistance
  apply le_csSup
  · refine ⟨2, ?_⟩
    rintro x (hx | hx)
    · simp [Set.mem_singleton_iff.mp hx]
    · obtain ⟨m, tau, rfl⟩ := hx
      have h := traceDistance_le_one (referenceState A tau) (referenceState B tau)
      change referenceError A B tau / 2 ≤ 1 at h
      linarith
  · exact Or.inr ⟨n, rho, rfl⟩

private def diagBorn {s t : Type*} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
    (C : QuantumChannel s t) (rho : DensityState (Fin 1 × s)) (i : t) : ℝ :=
  (CStarMatrix.ofMatrix.symm (referenceState C rho).val (0,i) (0,i)).re

private theorem shared_branch_native_diamond {s ι β : Type*} [Fintype s] [DecidableEq s]
    [Fintype ι] [DecidableEq ι] [Fintype β]
    (C Q : QuantumChannel s (ι × ι)) (rho : DensityState (Fin 1 × s))
    (c : ℝ) (hc : 0 ≤ c) (hn : (Fintype.card ι : ℝ) * c^2 = 1)
    (w : β → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1) (a b : β → ι → ℝ)
    (ha : ∀ k i, 0 ≤ a k i) (hb : ∀ k i, 0 ≤ b k i)
    (has : ∀ k, ∑ i, a k i = 1) (hbs : ∀ k, ∑ i, b k i = 1)
    (hC : ∀ i j, diagBorn C rho (i,j) = if i = j then c^2 else 0)
    (hQ : ∀ i j, diagBorn Q rho (i,j) = ∑ k, w k * (a k i * b k j)) :
    2 * (1-c * Real.sqrt (Fintype.card β : ℝ)) ≤ diamondDistance C Q := by
  let X := CStarMatrix.ofMatrix.symm (referenceState C rho).val -
    CStarMatrix.ofMatrix.symm (referenceState Q rho).val
  have hp (σ : DensityState (Fin 1 × (ι × ι))) :
      (CStarMatrix.ofMatrix.symm σ.val).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.prop.1).posSemidef
  have hx : X.IsHermitian := (hp _).isHermitian.sub (hp _).isHermitian
  have hs := shared_branch_l1_lower c hc hn w hw hws a b ha hb has hbs
  have he :
      (∑ i : Fin 1 × (ι × ι), |(X i i).re|) =
        ∑ i, ∑ j, |(if i = j then c^2 else 0) - ∑ k, w k * (a k i * b k j)| := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change |diagBorn C rho (i,j) - diagBorn Q rho (i,j)| = _
    rw [hC,hQ]
  calc
    _ ≤ _ := hs
    _ ≤ traceNorm X := by rw [← he]; exact diagonal_l1_le_traceNorm X hx
    _ ≤ _ := referenceError_le_diamond C Q rho

private def rawEntry {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

private theorem single_basis_psd {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    (Matrix.single a a (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : i = a <;> simp [hi]

private theorem raw_basis_psd {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (a : A) :
    (rawEntry C (Matrix.single a a 1)).PosSemidef := by
  have hn := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (single_basis_psd a).nonneg
  have hn' := map_nonneg C.toCompletelyPositiveMap hn
  exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hn').posSemidef

private def basisBorn {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (a : A) (i : B) : ℝ :=
  (rawEntry C (Matrix.single a a 1) i i).re

private theorem basisBorn_nonneg {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (a : A) (i : B) : 0 ≤ basisBorn C a i :=
  (Complex.nonneg_iff.mp ((raw_basis_psd C a).diag_nonneg (i := i))).1

private theorem basisBorn_sum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (a : A) : ∑ i, basisBorn C a i = 1 := by
  have h0 : Matrix.trace (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix
      (Matrix.single a a 1))) = (1 : ℂ) :=
    (C.trace_preserving _).trans (by change (Matrix.single a a (1 : ℂ)).trace = 1; simp)
  have h := congrArg Complex.re h0
  simpa [basisBorn, rawEntry, Matrix.trace, Matrix.diag, Complex.re_sum] using h

private theorem tensor_basis_entry {A B T : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    (L : QuantumChannel A T) (R : QuantumChannel B T) (a : A) (b : B) (i j : T) :
    tensorRawAction L R (Matrix.single (a,b) (a,b) 1) (i,j) (i,j) =
      rawEntry L (Matrix.single a a 1) i i * rawEntry R (Matrix.single b b 1) j j := by
  classical
  rw [tensorRawAction]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single b]
        · simp [rawEntry]
        · intro k _ hk; simp [Prod.mk.injEq, Ne.symm hk]
        · simp
      · intro k _ hk; simp [Prod.mk.injEq, Ne.symm hk]
      · simp
    · intro k _ hk; simp [Prod.mk.injEq, Ne.symm hk]
    · simp
  · intro k _ hk; simp [Prod.mk.injEq, Ne.symm hk]
  · simp

private theorem mixture_basis_born {A B T : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    {r : ℕ} (w : Fin r → ℝ) (left : Fin r → QuantumChannel A T)
    (right : Fin r → QuantumChannel B T) (Q : QuantumChannel (A × B) (T × T))
    (hQ : MixtureRealization w left right Q) (a : A) (b : B) (i j : T) :
    basisBorn Q (a,b) (i,j) = ∑ k, w k * (basisBorn (left k) a i * basisBorn (right k) b j) := by
  have h := congrArg (fun M : Matrix (T × T) (T × T) ℂ => (M (i,j) (i,j)).re)
    (hQ (Matrix.single (a,b) (a,b) 1))
  change basisBorn Q (a,b) (i,j) = _ at h
  rw [h]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [tensor_basis_entry]
  have hr : (rawEntry (right k) (Matrix.single b b 1) j j).im = 0 :=
    (Complex.nonneg_iff.mp ((raw_basis_psd (right k) b).diag_nonneg (i := j))).2.symm
  simp [basisBorn, Complex.mul_re, Complex.mul_im, hr]

private def basisDensity {A : Type*} [Fintype A] [DecidableEq A] (a : A) : DensityState A :=
  ⟨CStarMatrix.ofMatrix (Matrix.single a a 1),
   map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (single_basis_psd a).nonneg,
   by change (Matrix.single a a (1 : ℂ)).trace = 1; simp⟩

private theorem rawEntry_comp {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (D : QuantumChannel B C) (E : QuantumChannel A B) (X : Matrix A A ℂ) :
    rawEntry (D.comp E) X = rawEntry D (rawEntry E X) := by
  change CStarMatrix.ofMatrix.symm
    (D.toCompletelyPositiveMap (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = _
  unfold rawEntry
  rw [Equiv.apply_symm_apply]

private theorem diagBorn_basis {S T : Type*} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T]
    (C : QuantumChannel S T) (s : S) (i : T) :
    diagBorn C (basisDensity ((0 : Fin 1),s)) i = basisBorn C s i := by
  change (rawEntry C
      (fun u v => Matrix.single ((0 : Fin 1),s) ((0 : Fin 1),s) (1 : ℂ) (0,u) (0,v)) i i).re = _
  have h : (fun u v => Matrix.single ((0 : Fin 1),s) ((0 : Fin 1),s) (1 : ℂ)
      (0,u) (0,v)) = Matrix.single s s 1 := by
    ext u v
    simp [Matrix.single_apply, Prod.mk.injEq]
  rw [h]
  rfl

/-- Native unhalved diamond lower bound after any source channel with one
encoded product basis input. The competitors are actual native mixtures;
their probability laws are derived from the local CPTP channels. -/
private theorem physical_shared_branch_gap {S A B T : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype T] [DecidableEq T]
    (source : QuantumChannel S (A × B))
    (s : S) (a : A) (b : B)
    (hsource : rawEntry source (Matrix.single s s 1) = Matrix.single (a,b) (a,b) 1)
    (C Q : QuantumChannel (A × B) (T × T))
    (c : ℝ) (hc : 0 ≤ c) (hn : (Fintype.card T : ℝ) * c^2 = 1)
    (hC : ∀ i j, basisBorn C (a,b) (i,j) = if i = j then c^2 else 0)
    {r : ℕ} (w : Fin r → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1)
    (left : Fin r → QuantumChannel A T) (right : Fin r → QuantumChannel B T)
    (hQ : MixtureRealization w left right Q) :
    2 * (1-c * Real.sqrt (r : ℝ)) ≤ diamondDistance (C.comp source) (Q.comp source) := by
  let rho := basisDensity ((0 : Fin 1),s)
  have hdiag (D : QuantumChannel (A × B) (T × T)) (t : T × T) :
      diagBorn (D.comp source) rho t = basisBorn D (a,b) t := by
    rw [show diagBorn (D.comp source) rho t = basisBorn (D.comp source) s t from
      diagBorn_basis _ _ _]
    unfold basisBorn
    rw [rawEntry_comp, hsource]
  simpa only [Fintype.card_fin] using
    shared_branch_native_diamond (C.comp source) (Q.comp source) rho c hc hn w hw hws
      (fun k => basisBorn (left k) a) (fun k => basisBorn (right k) b)
      (fun k => basisBorn_nonneg (left k) a) (fun k => basisBorn_nonneg (right k) b)
      (fun k => basisBorn_sum (left k) a) (fun k => basisBorn_sum (right k) b)
      (fun i j => (hdiag C (i,j)).trans (hC i j))
      (fun i j => (hdiag Q (i,j)).trans (mixture_basis_born w left right Q hQ a b i j))

private theorem sum_vary_single {A B D : Type*} [Fintype D] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (v : D → ℂ) :
    (∑ i, Matrix.single a b (v i)) = Matrix.single a b (∑ i, v i) := by
  ext i j
  by_cases hi : a = i <;> by_cases hj : b = j <;> simp [Matrix.sum_apply, hi, hj]

/-- Explicit Kraus family |t⟩⟨a| scaled by sqrt(d t), with no formal
assumption about existence of the matched-replacement channel. -/
private theorem diagonal_replacement_exists {A T : Type*} [Fintype A] [DecidableEq A]
    [Fintype T] [DecidableEq T] (d : T → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hs : ∑ t, d t = 1) :
    ∃ C : QuantumChannel A T, ∀ X,
      rawEntry C X = X.trace • Matrix.diagonal (fun t => (d t : ℂ)) := by
  let e (t : T) : ℂ := (Real.sqrt (d t) : ℂ)
  have he₁ (t : T) : star (e t) = e t := by simp [e]
  have he₂ (t : T) : e t * e t = (d t : ℂ) := by
    dsimp [e]
    exact_mod_cast Real.mul_self_sqrt (hd t)
  let K (i : A × T) : Matrix T A ℂ := Matrix.single i.2 i.1 (e i.2)
  have hkc (i : A × T) : (K i)ᴴ = Matrix.single i.1 i.2 (e i.2) := by
    simp [K, Matrix.conjTranspose_single, he₁]
  have hs' : (∑ t, (d t : ℂ)) = 1 := by exact_mod_cast hs
  have hK : (∑ i, (K i)ᴴ * K i) = 1 := by
    simp_rw [hkc, K, Matrix.single_mul_single_same, he₂]
    rw [Fintype.sum_prod_type]
    simp_rw [sum_vary_single, hs']
    exact Matrix.sum_single_one
  obtain ⟨C, hC⟩ := finite_kraus_quantum_channel K hK
  refine ⟨C, fun X => ?_⟩
  change CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
  rw [hC]
  simp_rw [hkc, K, Matrix.single_mul_mul_single]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_vary_single]
  have hq (t : T) : (∑ a, e t * X a a * e t) = X.trace * (d t : ℂ) := by
    simp_rw [show ∀ z : ℂ, e t * z * e t = (e t * e t) * z from fun _ => by ring,
      he₂, ← Finset.mul_sum]
    rw [Matrix.trace, mul_comm]
    rfl
  simp_rw [hq, Matrix.sum_single_eq_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [hij, smul_eq_mul]

private theorem matched_target_exists {A B T : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    (c : ℝ) (hc : (Fintype.card T : ℝ) * c^2 = 1) :
    ∃ C : QuantumChannel (A × B) (T × T),
      (∀ X, rawEntry C X = X.trace •
        Matrix.diagonal (fun t : T × T => if t.1 = t.2 then ((c^2 : ℝ) : ℂ) else 0)) ∧
      ∀ a b i j, basisBorn C (a,b) (i,j) = if i = j then c^2 else 0 := by
  let d (t : T × T) : ℝ := if t.1 = t.2 then c^2 else 0
  have hd (t : T × T) : 0 ≤ d t := by dsimp [d]; split <;> positivity
  have hsum (i : T) : (∑ j : T, if i = j then c^2 else 0) = c^2 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hds : ∑ t, d t = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ i, ∑ j, if i = j then c^2 else 0) = 1
    simp_rw [hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact hc
  obtain ⟨C, hC⟩ := diagonal_replacement_exists (A := A × B) d hd hds
  refine ⟨C, ?_, ?_⟩
  · intro X
    rw [hC]
    congr 2
    funext t
    by_cases h : t.1 = t.2 <;> simp [d,h]
  · intro a b i j
    unfold basisBorn
    rw [hC]
    by_cases h : i = j
    · simp [d,h,smul_eq_mul, -Complex.ofReal_pow]
    · simp [d,h,smul_eq_mul]

private theorem trace_single_ite {Z : Type*} [Fintype Z] [DecidableEq Z] (z w : Z) :
    (Matrix.single z w (1 : ℂ)).trace = if z = w then 1 else 0 := by
  by_cases h : z = w
  · subst w; simp
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h, ite_eq_right h]

private theorem tensor_replacement {A B T : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    (L : QuantumChannel A T) (R : QuantumChannel B T)
    (P Q : Matrix T T ℂ)
    (hL : ∀ X, rawEntry L X = X.trace • P)
    (hR : ∀ X, rawEntry R X = X.trace • Q)
    (X : Matrix (A × B) (A × B) ℂ) (i j : T × T) :
    tensorRawAction L R X i j = X.trace * (P i.1 j.1 * Q i.2 j.2) := by
  have hLa (a b : A) :
      CStarMatrix.ofMatrix.symm (L.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single a b 1))) i.1 j.1 =
          ((if a=b then 1 else 0) : ℂ) * P i.1 j.1 := by
    change rawEntry L (Matrix.single a b 1) i.1 j.1 = _
    rw [hL]; simp [Matrix.smul_apply, smul_eq_mul, trace_single_ite]
  have hRa (a b : B) :
      CStarMatrix.ofMatrix.symm (R.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single a b 1))) i.2 j.2 =
          ((if a=b then 1 else 0) : ℂ) * Q i.2 j.2 := by
    change rawEntry R (Matrix.single a b 1) i.2 j.2 = _
    rw [hR]; simp [Matrix.smul_apply, smul_eq_mul, trace_single_ite]
  simp only [tensorRawAction, hLa, hRa]
  have hS (a a' : A) (b : B) :
      (∑ b' : B, X (a,b) (a',b') * ((if a=a' then 1 else 0) * P i.1 j.1) *
        ((if b=b' then 1 else 0) * Q i.2 j.2)) =
      X (a,b) (a',b) * ((if a=a' then 1 else 0) * P i.1 j.1) * Q i.2 j.2 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  simp_rw [hS]
  have hT (a : A) :
      (∑ a' : A, ∑ b : B, X (a,b) (a',b) *
        ((if a=a' then 1 else 0) * P i.1 j.1) * Q i.2 j.2) =
      ∑ b : B, X (a,b) (a,b) * (P i.1 j.1 * Q i.2 j.2) := by
    rw [Finset.sum_eq_single a]
    · simp [mul_assoc]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  simp_rw [hT, ← Finset.sum_mul]
  rw [Matrix.trace, Fintype.sum_prod_type]
  rfl

/-- Uniform common classical choice over the target labels realizes the
matched diagonal replacement by actual local CPTP channels. -/
private theorem matched_LOSR_exists {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m : ℕ) (_hm : 0 < m) (c : ℝ) (hc : (m : ℝ) * c^2 = 1) :
    ∃ C : QuantumChannel (A × B) (Fin m × Fin m),
    ∃ L : Fin m → QuantumChannel A (Fin m), ∃ R : Fin m → QuantumChannel B (Fin m),
      MixtureRealization (fun _ => c^2) L R C ∧
      ∀ a b i j, basisBorn C (a,b) (i,j) = if i = j then c^2 else 0 := by
  classical
  let d (t i : Fin m) : ℝ := if t=i then 1 else 0
  have hd (t i : Fin m) : 0 ≤ d t i := by dsimp [d]; split <;> norm_num
  have hs (t : Fin m) : ∑ i, d t i = 1 := by simp [d]
  choose L hL using fun t => diagonal_replacement_exists (A := A) (d t) (hd t) (hs t)
  choose R hR using fun t => diagonal_replacement_exists (A := B) (d t) (hd t) (hs t)
  obtain ⟨C, hC, hb⟩ := matched_target_exists (A := A) (B := B) (T := Fin m) c
    (by simpa using hc)
  refine ⟨C,L,R,?_,hb⟩
  intro X
  change rawEntry C X = _
  rw [hC]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [tensor_replacement _ _ _ _ (hL _) (hR _)]
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂
  · subst j₁; subst j₂
    by_cases h : i₁ = i₂
    · subst i₂
      rw [Finset.sum_eq_single i₁]
      · simp [d, mul_comm]
      · intro t _ ht; simp [d, ht]
      · simp
    · simp only [Matrix.diagonal_apply_eq, ite_eq_right h, mul_zero]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro t _
      by_cases e : t=i₁
      · subst t; simp [d, h]
      · simp [d,e]
  · simp [h₁,h₂,Prod.mk.injEq]
  · simp [h₁,h₂,Prod.mk.injEq]
  · simp [h₁,h₂,Prod.mk.injEq]

private abbrev UnitFlat (S : Type*) := TargetLocal (fun _ : S => 1)

private def unitFlatLabel {S : Type*} (s : S) : UnitFlat S := ⟨s,0⟩

private theorem rank_one_flat_column {S : Type*} [Fintype S] [DecidableEq S]
    (s : S) (p : UnitFlat S × UnitFlat S) :
    targetEncoding (fun _ : S => 1) p s =
      if p = (unitFlatLabel s,unitFlatLabel s) then 1 else 0 := by
  rcases p with ⟨⟨a,i⟩,⟨b,j⟩⟩
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  by_cases ha : a = s <;> by_cases hb : b = s
  · subst a; subst b
    simp [targetEncoding, unitFlatLabel]
  · subst a
    simp [targetEncoding, unitFlatLabel, hb, Ne.symm hb]
  · subst b
    simp [targetEncoding, unitFlatLabel, ha]
  · simp [targetEncoding, unitFlatLabel, ha]

private theorem compact_rank_one_product_input {S : Type*} [Fintype S] [DecidableEq S]
    (source : QuantumChannel S (UnitFlat S × UnitFlat S))
    (hsource : ∀ X, rawEntry source X =
      targetEncoding (fun _ : S => 1) * X *
        (targetEncoding (fun _ : S => 1))ᴴ) (s : S) :
    rawEntry source (Matrix.single s s 1) =
      Matrix.single (unitFlatLabel s,unitFlatLabel s)
        (unitFlatLabel s,unitFlatLabel s) 1 := by
  let U := targetEncoding (fun _ : S => 1)
  let v := (unitFlatLabel s, unitFlatLabel s)
  rw [hsource]
  change U * Matrix.single s s 1 * Uᴴ = Matrix.single v v 1
  ext p q
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.single_mul_apply_same, Matrix.conjTranspose_apply]
    dsimp [U, v]
    rw [rank_one_flat_column, rank_one_flat_column]
    by_cases hp : p = (unitFlatLabel s, unitFlatLabel s) <;>
      by_cases hq : q = (unitFlatLabel s, unitFlatLabel s) <;>
      simp [hp, hq, Ne.symm]
  · intro t _ ht
    have h0 : (Matrix.single s s (1 : ℂ) * Uᴴ) t q = 0 :=
      Matrix.single_mul_apply_of_ne (1 : ℂ) s s t q ht Uᴴ
    rw [h0, mul_zero]
  · simp

private theorem compact_unit_flat_source_exists {S : Type*} [Fintype S] [DecidableEq S] :
    ∃ source : QuantumChannel S (UnitFlat S × UnitFlat S), ∀ X,
      rawEntry source X = targetEncoding (fun _ : S => 1) * X *
        (targetEncoding (fun _ : S => 1))ᴴ := by
  let U := targetEncoding (fun _ : S => 1)
  let V (s : S) := (unitFlatLabel s,unitFlatLabel s)
  have hinj : Function.Injective V := by
    intro s t h
    exact congrArg (fun p : UnitFlat S × UnitFlat S => p.1.1) h
  have hU : Uᴴ * U = 1 := by
    ext s t
    rw [Matrix.mul_apply, Finset.sum_eq_single (V s)]
    · rw [Matrix.conjTranspose_apply]
      have hu (v : S) : U (V s) v = if s = v then 1 else 0 := by
        dsimp only [U]
        rw [rank_one_flat_column]
        by_cases he : s=v
        · simp [he,V]
        · simp [V, he, show V s ≠ V v from fun h => he (hinj h)]
      simp [hu, Matrix.one_apply]
    · intro p _ hp
      have hz : U p s = 0 := by
        change targetEncoding (fun _ : S => 1) p s = 0
        rw [rank_one_flat_column]
        exact ite_eq_right hp
      rw [Matrix.conjTranspose_apply, hz]
      simp
    · simp
  obtain ⟨source, hsource⟩ := finite_kraus_quantum_channel (fun _ : Fin 1 => U)
    (by simpa only [Fin.sum_univ_one] using hU)
  exact ⟨source, fun X => by simpa only [rawEntry, Fin.sum_univ_one] using hsource X⟩

/-- Physical compact flat instance: the reference-visible complexity of
shared classical randomness is not removed by using the compact carrier. -/
theorem result
    (m : ℕ) (hm : 0 < m) :
    ∃ source : QuantumChannel (Fin m) (TargetLocal (fun _ : Fin m => 1) × TargetLocal (fun _ : Fin m => 1)),
    ∃ C : QuantumChannel (TargetLocal (fun _ : Fin m => 1) × TargetLocal (fun _ : Fin m => 1)) (Fin m × Fin m),
    ∃ L : Fin m → QuantumChannel (TargetLocal (fun _ : Fin m => 1)) (Fin m),
    ∃ R : Fin m → QuantumChannel (TargetLocal (fun _ : Fin m => 1)) (Fin m),
      MixtureRealization (fun _ => ((Real.sqrt (m : ℝ))⁻¹)^2) L R C ∧
      ∀ {r : ℕ} (w : Fin r → ℝ),
        (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
        ∀ (left right : Fin r → QuantumChannel (TargetLocal (fun _ : Fin m => 1)) (Fin m))
          (Q : QuantumChannel (TargetLocal (fun _ : Fin m => 1) × TargetLocal (fun _ : Fin m => 1)) (Fin m × Fin m)),
          MixtureRealization w left right Q →
          2 * (1-(Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (r : ℝ)) ≤
            diamondDistance (C.comp source) (Q.comp source) := by
  let c := (Real.sqrt (m : ℝ))⁻¹
  have hc : 0 ≤ c := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hs : (m : ℝ) * c^2 = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity), mul_inv_cancel₀ hm0]
  obtain ⟨source,hsource⟩ := compact_unit_flat_source_exists (S := Fin m)
  obtain ⟨C,L,R,hC,hBorn⟩ := matched_LOSR_exists
    (A := UnitFlat (Fin m)) (B := UnitFlat (Fin m)) m hm c hs
  refine ⟨source,C,L,R,hC,?_⟩
  intro r w hw hsum left right Q hQ
  let s : Fin m := ⟨0,hm⟩
  have hp := compact_rank_one_product_input source hsource s
  exact physical_shared_branch_gap source s _ _ hp C Q c hc (by simpa using hs)
    (hBorn _ _) w hw hsum left right hQ

private theorem replacer_reference_error {A T U : Type} [Fintype A] [DecidableEq A]
    [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    (C Q : QuantumChannel A T) (M N : Matrix T T ℂ)
    (hC : ∀ X, rawEntry C X = X.trace • M)
    (hQ : ∀ X, rawEntry Q X = X.trace • N)
    (rho : DensityState (U × A)) :
    referenceError C Q rho = traceNorm (M-N) := by
  let X := CStarMatrix.ofMatrix.symm rho.val
  let R : Matrix U U ℂ := ∑ a : A, X.submatrix (fun u => (u,a)) (fun u => (u,a))
  have hX : X.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.prop.1).posSemidef
  have hR : R.PosSemidef := Matrix.posSemidef_sum (s := Finset.univ)
    (fun a _ => hX.submatrix (fun u => (u,a)))
  have ht : R.trace = 1 := by
    rw [← rho.prop.2]
    · simp only [R, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.submatrix_apply]
      change (∑ u : U, ∑ a : A, X (u,a) (u,a)) = ∑ p : U × A, X p p
      rw [Fintype.sum_prod_type]
  have hNorm : traceNorm R = 1 := by
    have h := congrArg Complex.re (traceNorm_of_posSemidef hR)
    simpa [ht] using h
  have he :
      CStarMatrix.ofMatrix.symm (referenceState C rho).val -
      CStarMatrix.ofMatrix.symm (referenceState Q rho).val =
        R ⊗ₖ (M-N) := by
    ext p q
    rcases p with ⟨u,a⟩
    rcases q with ⟨v,b⟩
    change rawEntry C (Matrix.of (fun x y => X (u,x) (v,y))) a b -
      rawEntry Q (Matrix.of (fun x y => X (u,x) (v,y))) a b = _
    rw [hC,hQ]
    simp [R, Matrix.trace, Matrix.diag, Matrix.sum_apply,
      Matrix.submatrix_apply, smul_eq_mul, mul_sub]
  unfold referenceError
  rw [he, traceNorm_kronecker, hNorm, one_mul]

theorem replacer_diamond_exact {A T : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype T] [DecidableEq T]
    (C Q : QuantumChannel A T) (M N : Matrix T T ℂ)
    (hC : ∀ X, CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X.trace • M)
    (hQ : ∀ X, CStarMatrix.ofMatrix.symm (Q.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = X.trace • N) :
    diamondDistance C Q = traceNorm (M-N) := by
  apply le_antisymm
  · unfold diamondDistance
    apply csSup_le (by exact ⟨0, Or.inl (by simp)⟩)
    rintro y (hy | ⟨n,rho,rfl⟩)
    · rw [Set.mem_singleton_iff.mp hy]
      exact traceNorm_nonneg _
    · exact (replacer_reference_error C Q M N hC hQ rho).le
  · let rho := basisDensity ((0 : Fin 1), Classical.choice (inferInstance : Nonempty A))
    rw [← replacer_reference_error C Q M N hC hQ rho]
    exact referenceError_le_diamond C Q rho

end D5.S3.Quantum.Entanglement.SectorChannels.CompactMatchedReplacementBranchGap
