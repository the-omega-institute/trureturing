/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMJointWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMJointWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint affine Gaussian evaluation of four inverse-lowered oscillator words. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalProduct

/-! The joint Wick calculation keeps the native contractions between different
punctures. Only the extra normalization contractions are confined to a slot. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMJointWick

open MvPolynomial OriginalChargedRowSource NativeAffineExternalCoefficient
open NativeAffineTransport (transportCovariance transportMean transportCovariance_symm)
open FactorialFockMetric (weight)

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The joint matrix on pending marks and native modes. Every original native
edge is retained. The additional Wick correction acts only on pending marks. -/
def jointCovariance (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ) :
    Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks (transportCovariance U A + C) (U * A) (U * A)ᵀ A

private def jointMean (U : Matrix I J ℂ) (mu : J → ℂ) : I ⊕ J → ℂ :=
  Sum.elim (transportMean U mu) mu

private theorem jointCovariance_symm (U : Matrix I J ℂ) (A : Matrix J J ℂ)
    (C : Matrix I I ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i) :
    ∀ i j, jointCovariance U A C i j = jointCovariance U A C j i := by
  rintro (i | i) (j | j)
  · simp only [jointCovariance, Matrix.fromBlocks_apply₁₁, Matrix.add_apply,
      transportCovariance_symm U A hA i j, hC i j]
  · rfl
  · rfl
  · exact hA i j

/-- Evaluate a native polynomial with the indicated pending marked occupation. -/
def jointReadout (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (d : I →₀ ℕ) : MvPolynomial J ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials J ℂ).constr ℂ fun e =>
    affineMoment (jointCovariance U A C) (jointMean U mu) (d.sumElim e)

private theorem jointReadout_monomial (U : Matrix I J ℂ) (A : Matrix J J ℂ)
    (C : Matrix I I ℂ) (mu : J → ℂ) (d : I →₀ ℕ) (e : J →₀ ℕ) (a : ℂ) :
    jointReadout U A C mu d (monomial e a) =
      a * affineMoment (jointCovariance U A C) (jointMean U mu) (d.sumElim e) := by
  have hm : (monomial e a : MvPolynomial J ℂ) = a • monomial e 1 := by
    simp [smul_monomial, smul_eq_mul]
  rw [hm, map_smul]
  change a • (basisMonomials J ℂ).constr ℂ _ ((basisMonomials J ℂ) e) = _
  rw [Module.Basis.constr_basis, smul_eq_mul]

private def creator (U : Matrix I J ℂ) (i : I) : MvPolynomial J ℂ :=
  ∑ j, U i j • X j

private theorem joint_step_left (M : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ)
    (hM : ∀ i j, M i j = M j i) (d : I →₀ ℕ) (e : J →₀ ℕ) (i : I) :
    affineMoment M m ((d + Finsupp.single i 1).sumElim e) =
      m (.inl i) * affineMoment M m (d.sumElim e) +
      (∑ j, (d j : ℂ) * M (.inl i) (.inl j) *
        affineMoment M m ((d - Finsupp.single j 1).sumElim e)) +
      ∑ j, (e j : ℂ) * M (.inl i) (.inr j) *
        affineMoment M m (d.sumElim (e - Finsupp.single j 1)) := by
  have hadd : (d + Finsupp.single i 1).sumElim e =
      d.sumElim e + Finsupp.single (Sum.inl i) 1 := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hsubL (j : I) : d.sumElim e - Finsupp.single (Sum.inl j) 1 =
      (d - Finsupp.single j 1).sumElim e := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hsubR (j : J) : d.sumElim e - Finsupp.single (Sum.inr j) 1 =
      d.sumElim (e - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  rw [hadd, affineMoment_step M m hM, Fintype.sum_sum_type, ← add_assoc]
  simp only [Finsupp.sumElim_inl, Finsupp.sumElim_inr, hsubL, hsubR]

private theorem joint_step_right (M : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ)
    (hM : ∀ i j, M i j = M j i) (d : I →₀ ℕ) (e : J →₀ ℕ) (i : J) :
    affineMoment M m (d.sumElim (e + Finsupp.single i 1)) =
      m (.inr i) * affineMoment M m (d.sumElim e) +
      (∑ j, (d j : ℂ) * M (.inr i) (.inl j) *
        affineMoment M m ((d - Finsupp.single j 1).sumElim e)) +
      ∑ j, (e j : ℂ) * M (.inr i) (.inr j) *
        affineMoment M m (d.sumElim (e - Finsupp.single j 1)) := by
  have hadd : d.sumElim (e + Finsupp.single i 1) =
      d.sumElim e + Finsupp.single (Sum.inr i) 1 := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hsubL (j : I) : d.sumElim e - Finsupp.single (Sum.inl j) 1 =
      (d - Finsupp.single j 1).sumElim e := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hsubR (j : J) : d.sumElim e - Finsupp.single (Sum.inr j) 1 =
      d.sumElim (e - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  rw [hadd, affineMoment_step M m hM, Fintype.sum_sum_type, ← add_assoc]
  simp only [Finsupp.sumElim_inl, Finsupp.sumElim_inr, hsubL, hsubR]

private theorem creator_cross (U : Matrix I J ℂ) (A : Matrix J J ℂ)
    (hA : ∀ i j, A i j = A j i) (i j : I) :
    ∑ k, U i k * (U * A) j k = transportCovariance U A i j := by
  unfold transportCovariance
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [hA l k]
  ring

/-- Moving a pending mark to the native readout cancels all native pair and
mean terms in the two Wick recurrences, leaving the precise correction. -/
private theorem joint_readout_step (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i)
    (d : I →₀ ℕ) (i : I) (p : MvPolynomial J ℂ) :
    jointReadout U A C mu (d + Finsupp.single i 1) p =
      jointReadout U A C mu d (creator U i * p) +
      ∑ j, (d j : ℂ) * C i j * jointReadout U A C mu (d - Finsupp.single j 1) p := by
  classical
  let L := jointReadout U A C mu
  let M := jointCovariance U A C
  let m := jointMean U mu
  let R := L d ∘ₗ LinearMap.mulLeft ℂ (creator U i) +
    ∑ j, ((d j : ℂ) * C i j) • L (d - Finsupp.single j 1)
  suffices h : L (d + Finsupp.single i 1) = R by
    simpa only [R, L, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun f : MvPolynomial J ℂ →ₗ[ℂ] ℂ => f p) h
  apply MvPolynomial.linearMap_ext
  intro e
  apply LinearMap.ext_ring
  change L (d + Finsupp.single i 1) (monomial e 1) = R (monomial e 1)
  have hsym := jointCovariance_symm U A C hA hC
  simp only [R, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, L, jointReadout_monomial, one_mul,
    creator, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]
  simp only [X, monomial_mul, one_mul, add_comm (Finsupp.single _ 1) e,
    jointReadout_monomial, one_mul, smul_eq_mul]
  rw [joint_step_left _ _ hsym]
  simp_rw [joint_step_right _ _ hsym]
  simp only [jointCovariance, jointMean, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.add_apply]
  simp only [mul_add, Finset.sum_add_distrib, transportMean, Finset.sum_mul]
  -- The sums in the expanded matrix product are finite on both indices.
  have hl : (∑ k, ∑ j, U i k * ((d j : ℂ) * (U * A) j k *
      affineMoment M m ((d - Finsupp.single j 1).sumElim e))) =
      ∑ j, (d j : ℂ) * transportCovariance U A i j *
        affineMoment M m ((d - Finsupp.single j 1).sumElim e) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← creator_cross U A hA, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hr : (∑ k, ∑ j, U i k * ((e j : ℂ) * A k j *
      affineMoment M m (d.sumElim (e - Finsupp.single j 1)))) =
      ∑ j, (e j : ℂ) * (U * A) i j *
        affineMoment M m (d.sumElim (e - Finsupp.single j 1)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hm' : (∑ k, U i k * mu k * affineMoment M m (d.sumElim e)) =
      ∑ k, U i k * (mu k * affineMoment M m (d.sumElim e)) :=
    Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  simp only [M, m, jointCovariance, jointMean] at hl hr hm'
  simp_rw [Finset.mul_sum, add_mul, Finset.sum_add_distrib]
  rw [hl, hr, hm']
  ring

private theorem occupation_erase (l : List I) (k : Fin l.length) :
    jetOccupation (l.eraseIdx k) + Finsupp.single (l.get k) 1 = jetOccupation l := by
  induction l with
  | nil => exact Fin.elim0 k
  | cons i l ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [jetOccupation]
    · simpa [jetOccupation, add_assoc, add_left_comm, add_comm] using ih j

private theorem occupation_count_sum (l : List I) (f : I → ℂ) :
    ∑ i, ((jetOccupation l) i : ℂ) * f i = ∑ k : Fin l.length, f (l.get k) := by
  induction l with
  | nil => simp [jetOccupation]
  | cons i l ih =>
    simp only [jetOccupation, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib,
      List.length_cons, Fin.sum_univ_succ, List.get_cons_zero, List.get_cons_succ', ih]
    simp [Finsupp.single_apply, ite_mul, add_comm]

private theorem joint_readout_marks (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i)
    (d : I →₀ ℕ) (l : List I) (i : I) (hd : ∀ j, d j ≠ 0 → C i j = 0)
    (p : MvPolynomial J ℂ) :
    jointReadout U A C mu (d + jetOccupation (i :: l)) p =
      jointReadout U A C mu (d + jetOccupation l) (creator U i * p) +
      ∑ k : Fin l.length, C i (l.get k) *
        jointReadout U A C mu (d + jetOccupation (l.eraseIdx k)) p := by
  rw [jetOccupation, ← add_assoc, joint_readout_step U A C mu hA hC]
  congr 1
  simp only [Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have hz : ∑ j, (d j : ℂ) * C i j *
      jointReadout U A C mu (d + jetOccupation l - Finsupp.single j 1) p = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : d j = 0
    · simp [h]
    · simp [hd j h]
  rw [hz, zero_add]
  simp_rw [mul_assoc]
  rw [occupation_count_sum]
  apply Finset.sum_congr rfl
  intro k _
  conv_lhs =>
    rw [← occupation_erase l k, ← add_assoc, add_tsub_cancel_right]

/-- A word with the stated creator and contraction recurrence can be
moved through the joint coefficient in a single slot. Pending marks in
other slots still participate through the original native mixed blocks. -/
private theorem move_slot (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i)
    (allowed : I → Prop) (d : I →₀ ℕ)
    (hd : ∀ i j, allowed i → d j ≠ 0 → C i j = 0)
    (W : List I → MvPolynomial J ℂ) (hW0 : W [] = 1)
    (hW : ∀ i l, allowed i → (∀ j ∈ l, allowed j) →
      W (i :: l) = creator U i * W l +
        ∑ k : Fin l.length, C i (l.get k) • W (l.eraseIdx k))
    (l : List I) (hl : ∀ j ∈ l, allowed j) (p : MvPolynomial J ℂ) :
    jointReadout U A C mu (d + jetOccupation l) p =
      jointReadout U A C mu d (W l * p) := by
  induction hn : l.length using Nat.strong_induction_on generalizing l p with
  | h n ih =>
    cases l with
    | nil => simp [jetOccupation, hW0]
    | cons i l =>
      have hi : allowed i := hl i (by simp)
      have htail : ∀ j ∈ l, allowed j := fun j hj => hl j (by simp [hj])
      have hsmall : l.length < n := by simp at hn; omega
      rw [joint_readout_marks U A C mu hA hC d l i (fun j hj => hd i j hi hj),
        hW i l hi htail, add_mul, Finset.sum_mul, map_add, map_sum]
      rw [ih _ hsmall l htail (creator U i * p) rfl]
      congr 1
      · rw [mul_left_comm, ← mul_assoc]
      · apply Finset.sum_congr rfl
        intro k _
        rw [ih _ ((List.length_eraseIdx_le ..).trans_lt hsmall) _
          (fun j hj => htail j (List.eraseIdx_subset hj)) p rfl,
          smul_mul_assoc, map_smul, smul_eq_mul]


private def marksOccupation {S : Type*} (ls : List (S × List I)) : I →₀ ℕ :=
  (ls.map (fun entry => jetOccupation entry.2)).sum

private theorem occupation_zero_of_notMem (i : I) (l : List I) (hi : i ∉ l) :
    jetOccupation l i = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa [List.mem_cons, eq_comm] using hi
    simp [jetOccupation, ih h.2, Finsupp.single_apply, Ne.symm h.1, h.1]

private theorem marksOccupation_zero {S : Type*} (slot : I → S)
    (ls : List (S × List I)) (i : I)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1)
    (hn : ∀ entry ∈ ls, slot i ≠ entry.1) : marksOccupation ls i = 0 := by
  induction ls with
  | nil => rfl
  | cons entry ls ih =>
    have hfront : i ∉ entry.2 := fun hi =>
      hn entry (by simp) (hv entry (by simp) i hi)
    have htail := ih (fun e he => hv e (List.mem_cons_of_mem _ he))
      (fun e he => hn e (List.mem_cons_of_mem _ he))
    simp [marksOccupation, occupation_zero_of_notMem i entry.2 hfront,
      show (ls.map (fun entry => jetOccupation entry.2)).sum i = 0 from htail]

/-- Independent slot words can all be moved through the same native Gaussian
readout. The off-slot entries of the correction vanish, while those of the
native covariance and its transported blocks remain unrestricted. -/
private theorem joint_readout_slot_words {S : Type*} (slot : I → S)
    (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i)
    (hoff : ∀ i j, slot i ≠ slot j → C i j = 0)
    (W : S → List I → MvPolynomial J ℂ)
    (hW0 : ∀ s, W s [] = 1)
    (hW : ∀ s i l, slot i = s → (∀ j ∈ l, slot j = s) →
      W s (i :: l) = creator U i * W s l +
        ∑ k : Fin l.length, C i (l.get k) • W s (l.eraseIdx k))
    (ls : List (S × List I)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) (p : MvPolynomial J ℂ) :
    jointReadout U A C mu (marksOccupation ls) p =
      jointReadout U A C mu 0 ((ls.map (fun entry => W entry.1 entry.2)).prod * p) := by
  induction ls generalizing p with
  | nil => simp [marksOccupation]
  | cons entry ls ih =>
    have hn := List.nodup_cons.mp hslots
    have htail (e : S × List I) (he : e ∈ ls) := hv e (List.mem_cons_of_mem _ he)
    have hzero (i j : I) (hi : slot i = entry.1) (hj : marksOccupation ls j ≠ 0) :
        C i j = 0 := by
      apply hoff
      intro hij
      exact hj (marksOccupation_zero slot ls j htail (by
        intro e he heq
        apply hn.1
        rw [← hi, hij, heq]
        exact List.mem_map_of_mem he))
    have he : marksOccupation (entry :: ls) = marksOccupation ls + jetOccupation entry.2 := by
      simp [marksOccupation, add_comm]
    rw [he, move_slot U A C mu hA hC (fun i => slot i = entry.1) _ hzero
      (W entry.1) (hW0 entry.1) (hW entry.1) entry.2
        (hv entry (List.mem_cons_self ..)) p, ih hn.2 htail]
    simp [mul_left_comm, mul_comm, mul_assoc]


open private affineCoefficient_enlarge from
  D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource

private theorem jetOccupation_append (l r : List I) :
    jetOccupation (l ++ r) = jetOccupation l + jetOccupation r := by
  induction l with
  | nil => simp [jetOccupation]
  | cons i l ih => simp [jetOccupation, ih, add_assoc, add_left_comm, add_comm]

private theorem occupation_flatten {S : Type*} (ls : List (S × List I)) :
    jetOccupation (ls.flatMap Prod.snd) = marksOccupation ls := by
  induction ls with
  | nil => rfl
  | cons entry ls ih => simp [marksOccupation, jetOccupation_append, ih]

private theorem native_readout_monomial (U : Matrix I J ℂ) (A : Matrix J J ℂ)
    (C : Matrix I I ℂ) (mu : J → ℂ) (e : J →₀ ℕ) (a : ℂ) :
    jointReadout U A C mu 0 (monomial e a) = a * ((weight e : ℂ) * affineCoefficient A mu e) := by
  have h := affineCoefficient_enlarge (jointCovariance U A C) (jointMean U mu)
    Function.Embedding.inr e
  have he : e.embDomain (Function.Embedding.inr : J ↪ I ⊕ J) = (0 : I →₀ ℕ).sumElim e := by
    ext (i | i) <;> simp [Finsupp.embDomain_apply, Finsupp.sumElim_apply]
  rw [he] at h
  rw [jointReadout_monomial, affineMoment_coefficient, h]
  simp [weight, Finsupp.prod_sumElim, jointCovariance, jointMean]

/-- The finite marked Gaussian coefficient equals the literal native
occupation evaluation after all independent slot words are applied.
An occurrence may have the same colour and mode as another occurrence. -/
theorem marked_gaussian_slot_words {S : Type*} (slot : I → S)
    (U : Matrix I J ℂ) (A : Matrix J J ℂ) (C : Matrix I I ℂ)
    (mu : J → ℂ) (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i)
    (hoff : ∀ i j, slot i ≠ slot j → C i j = 0)
    (W : S → List I → MvPolynomial J ℂ)
    (hW0 : ∀ s, W s [] = 1)
    (hW : ∀ s i l, slot i = s → (∀ j ∈ l, slot j = s) →
      W s (i :: l) = creator U i * W s l +
        ∑ k : Fin l.length, C i (l.get k) • W s (l.eraseIdx k))
    (ls : List (S × List I)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) :
    let l := ls.flatMap Prod.snd
    let B := transportCovariance U A + C
    let P := (ls.map (fun entry => W entry.1 entry.2)).prod
    coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, B i j * v i * v j) +
        ∑ i, transportMean U mu i * v i)) 0 =
      ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) * affineCoefficient A mu e) := by
  classical
  dsimp only
  have hs (i j : I) : (transportCovariance U A + C) i j =
      (transportCovariance U A + C) j i := by
    simp [Matrix.add_apply, transportCovariance_symm U A hA, hC]
  have hj := OriginalFourMPhysicalCovariance.marked_gaussian_jet (id : I → I)
    (ls.flatMap Prod.snd) (transportCovariance U A + C) (transportMean U mu) hs
  simp only [id_eq, List.map_id, occupation_flatten] at hj
  rw [hj]
  let d := marksOccupation ls
  have he : d.embDomain (Function.Embedding.inl : I ↪ I ⊕ J) = d.sumElim 0 := by
    ext (i | i) <;> simp [Finsupp.embDomain_apply, Finsupp.sumElim_apply]
  have h := affineCoefficient_enlarge (jointCovariance U A C) (jointMean U mu)
    Function.Embedding.inl d
  rw [he] at h
  change affineCoefficient (jointCovariance U A C) (jointMean U mu) (d.sumElim 0) =
    affineCoefficient (transportCovariance U A + C) (transportMean U mu) d at h
  rw [← h]
  have h1 : jointReadout U A C mu d 1 =
      (weight d : ℂ) *
        affineCoefficient (jointCovariance U A C) (jointMean U mu) (d.sumElim 0) := by
    rw [show (1 : MvPolynomial J ℂ) = monomial 0 1 from rfl,
      jointReadout_monomial, one_mul, affineMoment_coefficient]
    simp [weight, Finsupp.prod_sumElim]
  rw [← h1, joint_readout_slot_words slot U A C mu hA hC hoff W hW0 hW ls hslots hv,
    mul_one]
  generalize (ls.map (fun entry => W entry.1 entry.2)).prod = P
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, native_readout_monomial]


open LatticeGeneratingFieldLocality OriginalFourMActualChart OriginalFourMOccupationTransport
open OriginalGaussianExternalBlocks (External explicitEffectiveKernel)
open OriginalGaussianSewnAnalytic (coefficient explicitMean)
open OriginalFourMSignedOverlap (taggedMode)
open OriginalFourMCauchyTaylor
open OriginalFourMNativeOccupation
open OriginalFourMPhysicalCovariance (physicalCovariance)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (contractionScalar)
open private creatorEntry incomingScale weighted_pair_symmetry wordScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private explicit_covariance_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation
open private same_flags from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private chartPeriod from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private evalLower from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering
open private vacuumProjection_apply from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

/-- Native external labels restricted to a common bound on creator modes. -/
abbrev BoundedExternal (D : LatticeData) (N : ℕ) :=
  Bool × (Fin D.rank × Fin (N + 1))

private def externalLabel (D : LatticeData) (N : ℕ) (j : BoundedExternal D N) :
    External D := (j.1, j.2.1, j.2.2)

private def nativeLabel (D : LatticeData) (N : ℕ) (c : Chart) (s : Puncture)
    (i : Fin D.rank) (k : Fin (N + 1)) : BoundedExternal D N ⊕ BoundedExternal D N :=
  taggedMode (flags c s).1 ((flags c s).2, i, k)

private def boundedWord (D : LatticeData) (N : ℕ) (c : Chart) (x : ℝ) (s : Puncture)
    (l : List (Index D)) : MvPolynomial (BoundedExternal D N ⊕ BoundedExternal D N) ℂ :=
  aeval (fun i : Index D => if h : i.2 < N + 1 then
    X (nativeLabel D N c s i.1 ⟨i.2, h⟩) else 0)
    (inverseLoweredWord D c x s l)

private def creatorMatrix (D : LatticeData) (N : ℕ) (c : Chart) (x : ℝ)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N) :
    Matrix I (BoundedExternal D N ⊕ BoundedExternal D N) ℂ :=
  fun i j => ∑ k : Fin ((mode i).2 + 1),
    if nativeLabel D N c (slot i) (mode i).1
      ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ (bound i))⟩ = j then
      creatorEntry c x (slot i) (mode i).2 k else 0

private def gramCorrection (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : I → Puncture) (mode : I → Index D) : Matrix I I ℂ := by
  classical
  exact fun i j => if slot i = slot j then
    incomingScale c x (slot i) (mode i).2 * incomingScale c x (slot i) (mode j).2 *
      ((D.G (mode i).1 (mode j).1 : ℂ) *
        ((-loweringParameter c (slot i)) ^ ((mode i).2 + (mode j).2 + 1) *
          contractionScalar (mode i).2 (mode j).2))
    else 0

private theorem gramCorrection_symm (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (x : ℝ) (slot : I → Puncture) (mode : I → Index D) (i j : I) :
    gramCorrection D c x slot mode i j = gramCorrection D c x slot mode j i := by
  classical
  by_cases h : slot i = slot j
  · have hg := weighted_pair_symmetry D hu (mode i) (mode j)
    simp only [gramCorrection, h, ite_true]
    rw [show (mode j).2 + (mode i).2 + 1 = (mode i).2 + (mode j).2 + 1 by omega]
    linear_combination (incomingScale c x (slot j) (mode i).2 *
      incomingScale c x (slot j) (mode j).2 *
      (-loweringParameter c (slot j))^((mode i).2+(mode j).2+1)) * hg
  · simp [gramCorrection, h, Ne.symm h]

private theorem creator_apply (D : LatticeData) (N : ℕ) (c : Chart) (x : ℝ)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N) (i : I) :
    creator (creatorMatrix D N c x slot mode bound) i =
      ∑ k : Fin ((mode i).2 + 1), creatorEntry c x (slot i) (mode i).2 k •
        X (nativeLabel D N c (slot i) (mode i).1
          ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ (bound i))⟩) := by
  classical
  simp only [creator, creatorMatrix, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [ite_smul]

private theorem bounded_word_step (D : LatticeData) (N : ℕ) (c : Chart) (x : ℝ)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (s : Puncture) (i : I) (l : List I) (hi : slot i = s)
    (hl : ∀ j ∈ l, slot j = s) :
    boundedWord D N c x s ((i :: l).map mode) =
      creator (creatorMatrix D N c x slot mode bound) i * boundedWord D N c x s (l.map mode) +
        ∑ k : Fin l.length, gramCorrection D c x slot mode i (l.get k) •
          boundedWord D N c x s ((l.eraseIdx k).map mode) := by
  classical
  unfold boundedWord
  rw [List.map_cons, inverse_lowered_word_step]
  simp only [map_add, map_mul, map_sum, map_smul, aeval_X, ← List.eraseIdx_map]
  congr 1
  · rw [creator_apply, Finset.sum_fin_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hki := Finset.mem_range.mp hk
    have hkN := lt_of_lt_of_le hki (Nat.succ_le_succ (bound i))
    simp [hki, hkN, hi]
  · rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr (by simp)
    intro k hk
    have hj := hl (l[k]'(by simpa using hk)) (List.getElem_mem _)
    simp [gramCorrection, hi, hj, List.get_eq_getElem]


private theorem creator_matrix_sum (D : LatticeData) (N : ℕ) (c : Chart) (x : ℝ)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (i : I) (f : (BoundedExternal D N ⊕ BoundedExternal D N) → ℂ) :
    (∑ j, creatorMatrix D N c x slot mode bound i j * f j) =
      ∑ k : Fin ((mode i).2 + 1), creatorEntry c x (slot i) (mode i).2 k *
        f (nativeLabel D N c (slot i) (mode i).1
          ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ (bound i))⟩) := by
  classical
  simp only [creatorMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem selected_mean_eq (D : LatticeData) (q : Charge D) (N : ℕ)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N) (i : I) :
    coefficient (mode i).2 (fun u =>
      -(bilinear D (unitCharge D (mode i).1) q : ℂ) *
        physicalSource c x (slot i) u / chartPeriod upperA c x) =
      transportMean (creatorMatrix D N c x slot mode bound)
        (explicitMean D q (externalLabel D N) w) i := by
  rw [selected_radial_physical_mean D q hx hx₁ upperA c hc (slot i) (mode i) hw hwc,
    transportMean, creator_matrix_sum, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left (Finset.mem_range.mp hk)]
  congr 1
  unfold nativeLabel
  generalize (flags c (slot i)).1 = leg
  cases leg <;> rfl

private theorem selected_covariance_eq (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N) (i j : I) :
    (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
      (fun v => coefficient (mode i).2 (fun u =>
        physicalCovariance upperA c x (slot i) (slot j) u v)) =
      (transportCovariance (creatorMatrix D N c x slot mode bound)
        (explicitEffectiveKernel D (externalLabel D N) w) + gramCorrection D c x slot mode) i j := by
  classical
  rw [selected_radial_physical_covariance D hu hx hx₁ upperA c hc
    (slot i) (slot j) (mode i) (mode j) hw hwc]
  simp only [Matrix.add_apply]
  congr 1
  · let U := creatorMatrix D N c x slot mode bound
    let A := explicitEffectiveKernel D (externalLabel D N) w
    have ht : transportCovariance U A i j = ∑ a, U i a * (∑ b, U j b * A a b) := by
      unfold transportCovariance
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [ht]
    simp_rw [U, creator_matrix_sum]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Finset.mul_sum, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    rw [dite_eq_left (Finset.mem_range.mp hl)]
    have he :
        A (nativeLabel D N c (slot i) (mode i).1
          ⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ (bound i))⟩)
          (nativeLabel D N c (slot j) (mode j).1
          ⟨l, lt_of_lt_of_le (Finset.mem_range.mp hl) (Nat.succ_le_succ (bound j))⟩) =
        explicitEffectiveKernel D
          (fun b : Bool => if b then ((flags c (slot j)).2, (mode j).1, l)
            else ((flags c (slot i)).2, (mode i).1, k)) w
          (taggedMode (flags c (slot i)).1 false) (taggedMode (flags c (slot j)).1 true) := by
      dsimp only [A, nativeLabel]
      generalize (flags c (slot i)).1 = a
      generalize (flags c (slot j)).1 = b
      cases a <;> cases b <;> rfl
    rw [he]
    ring
  · have he : ((flags c (slot i)).1 = (flags c (slot j)).1 ∧
        (flags c (slot i)).2 = (flags c (slot j)).2) ↔ slot i = slot j :=
      ⟨same_flags c, fun h => by simp [h]⟩
    simp only [he, gramCorrection, incomingScale]

/-- For either radial chart, apply the physical Taylor selectors to the
signed means and every covariance block and then take the simultaneous
marked coefficient. This gives the actual native factorial Gaussian
readout of the product of the four inverse-lowered words. -/
theorem radial_physical_selected_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (slot : I → Puncture) (mode : I → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (ls : List (Puncture × List I)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) :
    let B := fun i j => (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
      (fun v => coefficient (mode i).2 (fun u =>
        physicalCovariance upperA c x (slot i) (slot j) u v))
    let m := fun i => coefficient (mode i).2 (fun u =>
      -(bilinear D (unitCharge D (mode i).1) q : ℂ) *
        physicalSource c x (slot i) u / chartPeriod upperA c x)
    let P := (ls.map (fun entry => boundedWord D N c x entry.1 (entry.2.map mode))).prod
    coordinateJet (ls.flatMap Prod.snd) (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, B i j * v i * v j) + ∑ i, m i * v i)) 0 =
      ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) *
        affineCoefficient (explicitEffectiveKernel D (externalLabel D N) w)
          (explicitMean D q (externalLabel D N) w) e) := by
  classical
  dsimp only
  simp_rw [selected_covariance_eq D hu N hx hx₁ upperA c hc hw hwc slot mode bound,
    selected_mean_eq D q N hx hx₁ upperA c hc hw hwc slot mode bound]
  apply marked_gaussian_slot_words slot (creatorMatrix D N c x slot mode bound)
    (explicitEffectiveKernel D (externalLabel D N) w) (gramCorrection D c x slot mode)
    (explicitMean D q (externalLabel D N) w) (explicit_covariance_symmetric D _ hw)
    (gramCorrection_symm D hu c x slot mode) _
    (fun s l => boundedWord D N c x s (l.map mode)) _
    (bounded_word_step D N c x slot mode bound) ls hslots hv
  · intro i j hij
    simp [gramCorrection, hij]
  · intro s
    simp [boundedWord, inverseLoweredWord, wordScale, evalLower,
      HalfFock.OriginalHalfCurrentFiniteLowering.wordPolynomial, vacuumProjection_apply]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMJointWick
