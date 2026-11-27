/- GID: D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired Choi CMI decay permits maximal diamond separation. -/

import D5.S3.Quantum.ProcessReconstruction.RankTwoHiddenProcess
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity

/-!
A finite-channel obstruction to a uniform diamond-norm upgrade of Liu and
Wild, DOI 10.1103/51mt-ghpn, §V and Appendix D. The channels are those of
`RankTwoHiddenProcess`. The data are all proper paired-region marginals of the
normalized Choi state. The model assumes exponential Choi CMI decay and places
no circuit-depth promise on the source channels.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

namespace UnitaryReconstruction.LiuWildChoiObstruction

open ParityFamily (Bits Kept Discarded split)
open RankTwoHiddenProcess (channel zeroWord oneWord inBlock phase)

abbrev pairMatrix {a : Type*} [Fintype a] [DecidableEq a]
    (ρ : DensityState a) : Matrix a a ℂ := CStarMatrix.ofMatrix.symm ρ.1

abbrev outer {a : Type*} (v : a → ℂ) : Matrix a a ℂ := vecMulVec v (star v)

section Entropy

variable {k : Type*} [Fintype k] [DecidableEq k]

private theorem negMulLog_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x ≤ 2 * Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hy := Real.sqrt_pos.2 hx
  have hs := Real.sq_sqrt hx.le
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
  rw [Real.log_inv] at hlog
  have hlog' := mul_le_mul_of_nonneg_left hlog hy.le
  rw [mul_sub, mul_inv_cancel₀ hy.ne', mul_one] at hlog'
  have hlog'' := mul_le_mul_of_nonneg_left hlog' hy.le
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    linarith [Real.log_sqrt hx.le]
  change -x * Real.log x ≤ _
  rw [hlogx]
  nlinarith [Real.sqrt_nonneg x]

private theorem sum_state_eigenvalues (ρ : DensityState k) :
    ∑ i, (density_posSemidef ρ).isHermitian.eigenvalues i = 1 := by
  have h := ((density_posSemidef ρ).isHermitian.trace_eq_sum_eigenvalues).symm
  have ht : (pairMatrix ρ).trace = 1 := ρ.2.2
  rw [ht] at h
  simpa using congrArg Complex.re h

/-- Rank three and a unit Rayleigh witness give a dimension-free entropy bound. -/
theorem entropy_le_of_rank_three (ρ : DensityState k) (v : k → ℂ)
    (hv : star v ⬝ᵥ v = 1) (hr : (pairMatrix ρ).rank ≤ 3)
    (δ : ℝ)
    (hOverlap : 1 - δ ≤ (star v ⬝ᵥ (pairMatrix ρ *ᵥ v)).re) :
    vonNeumannEntropy ρ ≤ δ + 4 * Real.sqrt δ := by
  classical
  have : Nonempty k := by
    by_contra! h
    simp [dotProduct] at hv
  let A := pairMatrix ρ
  let hp : A.PosSemidef := density_posSemidef ρ
  let eval := hp.isHermitian.eigenvalues
  have hn (i : k) : 0 ≤ eval i := hp.eigenvalues_nonneg i
  have hsum : ∑ i, eval i = 1 := sum_state_eigenvalues ρ
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ eval Finset.univ_nonempty
  let c := Unitary.conjStarAlgAut ℂ (Matrix k k ℂ) hp.isHermitian.eigenvectorUnitary
  have hspec : A = c (diagonal (Complex.ofReal ∘ eval)) := hp.isHermitian.spectral_theorem
  have hdiag : (diagonal (fun j => ((eval i - eval j : ℝ) : ℂ))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun j => by
      exact_mod_cast sub_nonneg.mpr (hi j (Finset.mem_univ j))
  have heq : c (diagonal (fun j => ((eval i - eval j : ℝ) : ℂ))) =
      (eval i : ℂ) • (1 : Matrix k k ℂ) - A := by
    have hD : diagonal (fun j => ((eval i - eval j : ℝ) : ℂ)) =
        (eval i : ℂ) • (1 : Matrix k k ℂ) - diagonal (Complex.ofReal ∘ eval) := by
      ext j l
      by_cases h : j = l <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]
    rw [hD, map_sub, map_smul, map_one, ← hspec]
  have hPSD : ((eval i : ℂ) • (1 : Matrix k k ℂ) - A).PosSemidef := by
    rw [← heq]
    simpa [c, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hdiag.mul_mul_conjTranspose_same (hp.isHermitian.eigenvectorUnitary : Matrix k k ℂ)
  have hRay := hPSD.dotProduct_mulVec_nonneg v
  have hRay' : (star v ⬝ᵥ (A *ᵥ v)).re ≤ eval i := by
    have h' := (Complex.nonneg_iff.mp hRay).1
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hv,
      Complex.sub_re, sub_nonneg] using h'
  have htop : 1 - δ ≤ eval i := hOverlap.trans hRay'
  let t := (Finset.univ : Finset k).filter (fun j => eval j ≠ 0)
  have ht : t.card ≤ 3 := by
    rw [hp.isHermitian.rank_eq_card_non_zero_eigs] at hr
    simpa [t, Fintype.card_subtype, eval] using hr
  have hit : i ∈ t := by
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hz
    have hz' (j : k) : eval j = 0 :=
      le_antisymm ((hi j (Finset.mem_univ _)).trans_eq hz) (hn j)
    simp [hz'] at hsum
  have hcard : (t.erase i).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hit]
    omega
  have htail : ∑ j ∈ Finset.univ.erase i, eval j = 1 - eval i := by
    linarith [Finset.sum_erase_add (Finset.univ : Finset k) eval (Finset.mem_univ i)]
  have hsmall (j : k) (hj : j ∈ t.erase i) : eval j ≤ δ := by
    have hs : eval j ≤ ∑ l ∈ Finset.univ.erase i, eval l :=
      Finset.single_le_sum (fun l _ => hn l)
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩)
    linarith
  have hsumEntropy : ∑ j ∈ t, Real.negMulLog (eval j) = ∑ j, Real.negMulLog (eval j) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : eval j = 0 <;> simp [hz]
  have htailEntropy : ∑ j ∈ t.erase i, Real.negMulLog (eval j) ≤ 4 * Real.sqrt δ := by
    calc
      _ ≤ ∑ _j ∈ t.erase i, 2 * Real.sqrt δ :=
        Finset.sum_le_sum fun j hj =>
          (negMulLog_le_two_sqrt (hn j)).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hsmall j hj)) (by norm_num))
      _ = ((t.erase i).card : ℝ) * (2 * Real.sqrt δ) := by simp
      _ ≤ _ := by
        have hc : ((t.erase i).card : ℝ) ≤ 2 := by exact_mod_cast hcard
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) (Real.sqrt_nonneg δ)]
  rw [← entropy_toMState]
  change (∑ j, Real.negMulLog (eval j)) ≤ _
  rw [← hsumEntropy, ← Finset.sum_erase_add t _ hit]
  linarith [Real.negMulLog_le_one_sub_self (hn i)]

private theorem state_entropy_nonneg (ρ : DensityState k) : 0 ≤ vonNeumannEntropy ρ := by
  rw [← entropy_toMState]
  exact Sᵥₙ_nonneg _

end Entropy

section Choi

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b]

/-- The unnormalized diagonal vector on the reference and input. -/
def diagonalVector (a : Type*) [DecidableEq a] : a × a → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

def bell (a : Type*) [Fintype a] [DecidableEq a] : a × a → ℂ :=
  (↑(Real.sqrt (Fintype.card a)) : ℂ)⁻¹ • diagonalVector a

omit [DecidableEq a] in
private theorem sqrt_card_pos : 0 < Real.sqrt (Fintype.card a) :=
  Real.sqrt_pos.2 (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card a))

theorem bell_norm : star (bell a) ⬝ᵥ bell a = 1 := by
  have hc : ((Real.sqrt (Fintype.card a) : ℝ) : ℂ) ^ 2 = (Fintype.card a : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card a)
  suffices (Fintype.card a : ℂ) *
      ((↑(Real.sqrt (Fintype.card a)) : ℂ)⁻¹ *
        (↑(Real.sqrt (Fintype.card a)) : ℂ)⁻¹) = 1 by
    simpa [dotProduct, bell, diagonalVector, Fintype.sum_prod_type] using this
  rw [← pow_two, inv_pow, hc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

/-- The normalized Choi state, obtained by applying the actual channel to half of a Bell state. -/
def normalizedChoi (C : QuantumChannel a b) : DensityState (a × b) :=
  referenceState C (pureState (bell a) bell_norm)

def basisVector (x : a) : a × a → ℂ :=
  fun p => if p.1 = x ∧ p.2 = x then 1 else 0

def blockVector (u v : a) (flip : Bool) : a × a → ℂ :=
  basisVector u + phase v flip v • basisVector v

def complementVector (u v : a) : a × a → ℂ :=
  diagonalVector a - basisVector u - basisVector v

omit [Nonempty a] in
private theorem bell_outer_entry (p q : a × a) :
    outer (bell a) p q =
      (Fintype.card a : ℂ)⁻¹ * (diagonalVector a p * diagonalVector a q) := by
  have hc : ((Real.sqrt (Fintype.card a) : ℝ) : ℂ) ^ 2 = (Fintype.card a : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card a)
  have hmul : ((Real.sqrt (Fintype.card a) : ℝ) : ℂ)⁻¹ *
      ((Real.sqrt (Fintype.card a) : ℝ) : ℂ)⁻¹ = (Fintype.card a : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, hc]
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  by_cases h₁ : i = x <;> by_cases h₂ : j = y <;>
    simp [bell, diagonalVector, vecMulVec_apply, h₁, h₂, hmul]

/-- The reference-first normalized Choi entry is the channel on a matrix unit divided by d. -/
theorem normalizedChoi_entry (C : QuantumChannel a b) (i j : a) (x y : b) :
    pairMatrix (normalizedChoi C) (i,x) (j,y) =
      (Fintype.card a : ℂ)⁻¹ *
        C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1)) x y := by
  change referenceMatrix C (outer (bell a)) (i,x) (j,y) = _
  rw [referenceMatrix_apply]
  have he : (Matrix.of fun u v : a => outer (bell a) (i,u) (j,v)) =
      (Fintype.card a : ℂ)⁻¹ • Matrix.single i j 1 := by
    ext u v
    rw [Matrix.of_apply, bell_outer_entry, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    by_cases hu : i = u <;> by_cases hv : j = v <;>
      simp [diagonalVector, hu, hv]
  change C.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (Matrix.of fun u v : a => outer (bell a) (i,u) (j,v))) x y = _
  rw [he]
  change (C.toCompletelyPositiveMap
    ((Fintype.card a : ℂ)⁻¹ • CStarMatrix.ofMatrix (Matrix.single i j 1))) x y = _
  rw [map_smul]
  rfl

omit [Fintype a] [Nonempty a] in
private theorem blockVector_apply (u v : a) (huv : u ≠ v) (flip : Bool) (p : a × a) :
    blockVector u v flip p =
      if p.1 = p.2 ∧ inBlock u v p.2 = true then phase v flip p.2 else 0 := by
  rcases p with ⟨i,x⟩
  by_cases hi : i = x
  · subst i
    by_cases hu : x = u
    · subst x
      cases flip <;> simp [blockVector, basisVector, inBlock, phase, huv]
    · by_cases hv : x = v
      · subst x
        simp [blockVector, basisVector, Pi.single_apply, inBlock, huv, Ne.symm huv]
      · simp [blockVector, basisVector, Pi.single_apply, inBlock, hu, hv, eq_comm]
  · simp [blockVector, basisVector, Pi.single_apply, hi,
      show ∀ y : a, ¬ (i = y ∧ x = y) from fun y ⟨h₁,h₂⟩ => hi (h₁.trans h₂.symm)]

omit [Fintype a] [Nonempty a] in
private theorem complementVector_apply (u v : a) (huv : u ≠ v) (p : a × a) :
    complementVector u v p =
      if p.1 = p.2 ∧ inBlock u v p.2 = false then 1 else 0 := by
  rcases p with ⟨i,x⟩
  by_cases hi : i = x
  · subst i
    by_cases hu : x = u
    · subst x
      simp [complementVector, diagonalVector, basisVector, Pi.single_apply, inBlock,
        huv, Ne.symm huv]
    · by_cases hv : x = v
      · subst x
        simp [complementVector, diagonalVector, basisVector, Pi.single_apply, inBlock,
          huv, Ne.symm huv]
      · simp [complementVector, diagonalVector, basisVector, Pi.single_apply, inBlock,
          hu, hv, eq_comm]
  · simp [complementVector, diagonalVector, basisVector, Pi.single_apply, hi,
      show ∀ y : a, ¬ (i = y ∧ x = y) from fun y ⟨h₁,h₂⟩ => hi (h₁.trans h₂.symm)]

omit [Fintype a] [Nonempty a] in
private theorem phase_of_outside (u v x : a) (flip : Bool) (hx : inBlock u v x = false) :
    phase v flip x = 1 := by
  have h : x ≠ v := by
    rintro rfl
    simp [inBlock] at hx
  simp [phase, h]

theorem normalizedChoi_hiddenChannel (u v : a) (huv : u ≠ v) (flip : Bool) :
    pairMatrix (normalizedChoi (RankTwoHiddenProcess.hiddenChannel u v flip)) =
      (Fintype.card a : ℂ)⁻¹ •
        (outer (blockVector u v flip) + outer (complementVector u v)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  change referenceMatrix (RankTwoHiddenProcess.hiddenChannel u v flip) (outer (bell a))
    (i,x) (j,y) = _
  rw [referenceMatrix_apply, RankTwoHiddenProcess.hiddenChannel_entry, bell_outer_entry]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply,
    blockVector_apply _ _ huv, complementVector_apply _ _ huv]
  by_cases hx : i = x <;> by_cases hy : j = y <;>
    cases hbx : inBlock u v x <;> cases hby : inBlock u v y <;>
    simp [diagonalVector, hx, hy, hbx, hby, phase_of_outside u v _ flip,
      show star (phase v flip y) = phase v flip y by
        by_cases h : flip = true ∧ y = v <;> simp [phase, h], mul_left_comm, mul_assoc]

omit [Nonempty a] in
private theorem block_dot (u v : a) (huv : u ≠ v) (c e : ℂ) :
    star (basisVector u + c • basisVector v) ⬝ᵥ
      (basisVector u + e • basisVector v) = 1 + star c * e := by
  have hb (x y : a) : star (basisVector x) ⬝ᵥ basisVector y =
      if x = y then 1 else 0 := by
    rw [show basisVector y = Pi.single (y,y) 1 by
      funext p
      simp [basisVector, Pi.single_apply, Prod.ext_iff]]
    rw [dotProduct_single]
    simp [basisVector, eq_comm]
  rw [star_add, star_smul, add_dotProduct, dotProduct_add, dotProduct_add,
    smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  simp [hb, huv, Ne.symm huv, smul_eq_mul]

/-- Unhalved trace distance, the convention of Liu–Wild. -/
theorem normalizedChoi_traceNorm (u v : a) (huv : u ≠ v) :
    traceNorm (pairMatrix (normalizedChoi (RankTwoHiddenProcess.hiddenChannel u v false)) -
      pairMatrix (normalizedChoi (RankTwoHiddenProcess.hiddenChannel u v true))) =
      4 / (Fintype.card a : ℝ) := by
  let A (f : Bool) : Matrix (a × a) (a × a) ℂ :=
    (Fintype.card a : ℂ)⁻¹ • outer (blockVector u v f)
  have hpos (f : Bool) : (A f).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)
  have ht (f : Bool) : (A f).trace = (Fintype.card a : ℂ)⁻¹ * 2 := by
    simp only [A, Matrix.trace_smul, smul_eq_mul, Matrix.trace_vecMulVec]
    rw [dotProduct_comm]
    rw [blockVector, block_dot u v huv]
    cases f <;> simp [phase] <;> norm_num
  have ho : A false * A true = 0 := by
    simp only [A, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec]
    rw [blockVector, blockVector, block_dot u v huv]
    simp [phase]
  rw [normalizedChoi_hiddenChannel _ _ huv, normalizedChoi_hiddenChannel _ _ huv]
  simp only [smul_add, add_sub_add_right_eq_sub]
  change traceNorm (A false - A true) = _
  rw [traceNorm_sub_orthogonal _ _ (hpos _) (hpos _) ho, ht, ht]
  simp [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_natCast]
  ring

end Choi

section Paired

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Paired (a : Type*) := a × a

def pairedSplit (s : Finset ι) :
    Paired (Bits ι) ≃ Paired (Discarded s) × Paired (Kept s) :=
  ((split s).prodCongr (split s)).trans (Equiv.prodProdProdComm _ _ _ _)

def pairedMarginal (s : Finset ι) (ρ : DensityState (Paired (Bits ι))) :
    DensityState (Paired (Kept s)) :=
  marginalLeft (relabelState (pairedSplit s).symm ρ)

theorem pairedMarginal_proper_eq (s : Finset ι) (hs : s ≠ Finset.univ) :
    pairedMarginal s (normalizedChoi (channel false)) =
      pairedMarginal s (normalizedChoi (channel true)) := by
  let X := outer (bell (Bits ι))
  have h := RankTwoHiddenProcess.proper_output_reference_eq s hs X
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext p q
  change (∑ z : Paired (Discarded s), referenceMatrix (channel false) X
      ((split s).symm (z.1,p.1), (split s).symm (z.2,p.2))
      ((split s).symm (z.1,q.1), (split s).symm (z.2,q.2))) = _
  change _ = ∑ z : Paired (Discarded s), referenceMatrix (channel true) X
      ((split s).symm (z.1,p.1), (split s).symm (z.2,p.2))
      ((split s).symm (z.1,q.1), (split s).symm (z.2,q.2))
  simp only [Fintype.sum_prod_type, ← referenceMatrix_discard,
    ← referenceMatrix_comp, h]

section MarginalBounds

variable [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem words_ne : (zeroWord : Bits ι) ≠ oneWord := by
  intro h
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  cases congrFun h i

omit [Nonempty ι] in
private theorem diag_split (s : Finset ι) (z : Paired (Discarded s)) (r : Paired (Kept s)) :
    diagonalVector (Bits ι) ((pairedSplit s).symm (z,r)) =
      diagonalVector (Discarded s) z * diagonalVector (Kept s) r := by
  have h : (split s).symm (z.1,r.1) = (split s).symm (z.2,r.2) ↔
      z.1 = z.2 ∧ r.1 = r.2 := by rw [(split s).symm.injective.eq_iff, Prod.mk.injEq]
  change (if (split s).symm (z.1,r.1) = (split s).symm (z.2,r.2) then 1 else 0) = _
  by_cases hz : z.1 = z.2 <;> by_cases hr : r.1 = r.2 <;> simp [h, diagonalVector, hz, hr]

omit [Nonempty ι] in
private theorem basisVector_pairedSplit (s : Finset ι) (x : Bits ι)
    (z : Paired (Discarded s)) (r : Paired (Kept s)) :
    basisVector x ((pairedSplit s).symm (z,r)) =
      basisVector ((split s x).1) z * basisVector ((split s x).2) r := by
  have h (c : Discarded s) (k : Kept s) :
      (split s).symm (c,k) = x ↔ c = (split s x).1 ∧ k = (split s x).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  change (if (split s).symm (z.1,r.1) = x ∧ (split s).symm (z.2,r.2) = x
    then 1 else 0) = _
  simp only [h, basisVector]
  split_ifs <;> simp_all

omit [Nonempty ι] in
theorem bell_pairedSplit (s : Finset ι) (z : Paired (Discarded s)) (r : Paired (Kept s)) :
    bell (Bits ι) ((pairedSplit s).symm (z,r)) =
      bell (Discarded s) z * bell (Kept s) r := by
  have hc := Fintype.card_congr (split s)
  rw [Fintype.card_prod] at hc
  simp only [bell, Pi.smul_apply, smul_eq_mul, diag_split, hc, Nat.cast_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Fintype.card (Discarded s)), Complex.ofReal_mul,
    _root_.mul_inv_rev]
  ring

/-- The span of the retained Bell vector and the two retained basis words. -/
private def pairedSupport (s : Finset ι) : Submodule ℂ (Paired (Kept s) → ℂ) :=
  Submodule.span ℂ (Set.range ![bell (Kept s),
    basisVector ((split s (zeroWord : Bits ι)).2),
    basisVector ((split s (oneWord : Bits ι)).2)])

private theorem bell_scale (a : Type*) [Fintype a] [DecidableEq a] [Nonempty a] :
    (↑(Real.sqrt (Fintype.card a)) : ℂ) • bell a = diagonalVector a := by
  rw [bell, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (sqrt_card_pos (a := a)).ne'

omit [Nonempty ι] in
private theorem complementVector_eq_bell (u v : Bits ι) :
    complementVector u v =
      (↑(Real.sqrt (Fintype.card (Bits ι))) : ℂ) • bell (Bits ι) -
        basisVector u - basisVector v := by rw [bell_scale, complementVector]

set_option maxHeartbeats 500000 in
-- Expanding the paired partial trace and its finite column sums takes extra elaboration.
private theorem pairedMarginal_support (s : Finset ι) (flip : Bool) :
    LinearMap.range (pairMatrix (pairedMarginal s (normalizedChoi (channel flip)))).mulVecLin ≤
      pairedSupport s := by
  classical
  let E := (pairedSplit s).symm
  let U := (zeroWord : Bits ι)
  let V := (oneWord : Bits ι)
  let B := blockVector U V flip
  let Q := complementVector U V
  let S := pairedSupport s
  have h₀ : bell (Kept s) ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have h₁ : basisVector ((split s U).2) ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have h₂ : basisVector ((split s V).2) ∈ S := Submodule.subset_span ⟨2, rfl⟩
  have hBasis (x : Bits ι) (hx : basisVector ((split s x).2) ∈ S)
      (z : Paired (Discarded s)) : (fun r => basisVector x (E (z,r))) ∈ S := by
    have heq : (fun r => basisVector x (E (z,r))) =
        basisVector ((split s x).1) z • basisVector ((split s x).2) := by
      funext r
      exact basisVector_pairedSplit s x z r
    rw [heq]
    exact S.smul_mem _ hx
  have hB (z : Paired (Discarded s)) : (fun r => B (E (z,r))) ∈ S :=
    S.add_mem (hBasis _ h₁ z) (S.smul_mem _ (hBasis _ h₂ z))
  have hQ (z : Paired (Discarded s)) : (fun r => Q (E (z,r))) ∈ S := by
    have heq : (fun r => Q (E (z,r))) =
        ((↑(Real.sqrt (Fintype.card (Bits ι))) : ℂ) * bell (Discarded s) z) • bell (Kept s) -
          (fun r => basisVector U (E (z,r))) - (fun r => basisVector V (E (z,r))) := by
      funext r
      simp [Q, complementVector_eq_bell, E, bell_pairedSplit, mul_assoc]
    rw [heq]
    exact S.sub_mem (S.sub_mem (S.smul_mem _ h₀) (hBasis _ h₁ z)) (hBasis _ h₂ z)
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  have hcol : (pairMatrix (pairedMarginal s (normalizedChoi (channel flip)))).col j =
      (Fintype.card (Bits ι) : ℂ)⁻¹ • ∑ z : Paired (Discarded s),
        (star (B (E (z,j))) • (fun r => B (E (z,r))) +
          star (Q (E (z,j))) • (fun r => Q (E (z,r)))) := by
    funext r
    change (∑ z : Paired (Discarded s),
      pairMatrix (normalizedChoi (RankTwoHiddenProcess.hiddenChannel U V flip))
        (E (z,r)) (E (z,j))) = _
    have h := normalizedChoi_hiddenChannel U V (words_ne (ι := ι)) flip
    simp_rw [h]
    simp only [Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, Pi.star_apply,
      Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    change _ = (Fintype.card (Bits ι) : ℂ)⁻¹ *
      (star (B (E (z,j))) * B (E (z,r)) + star (Q (E (z,j))) * Q (E (z,r)))
    ring
  rw [hcol]
  exact S.smul_mem _ (S.sum_mem fun z _ =>
    S.add_mem (S.smul_mem _ (hB z)) (S.smul_mem _ (hQ z)))

theorem pairedMarginal_rank (s : Finset ι) (flip : Bool) :
    (pairMatrix (pairedMarginal s (normalizedChoi (channel flip)))).rank ≤ 3 := by
  let G : Matrix (Paired (Kept s)) (Fin 3) ℂ := Matrix.of fun r j =>
    (![bell (Kept s), basisVector ((split s (zeroWord : Bits ι)).2),
      basisVector ((split s (oneWord : Bits ι)).2)] : Fin 3 → Paired (Kept s) → ℂ) j r
  have hc : Module.finrank ℂ (pairedSupport s) = G.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  rw [Matrix.rank]
  exact (Submodule.finrank_mono (pairedMarginal_support s flip)).trans
    (hc.trans_le (G.rank_le_card_width.trans_eq (Fintype.card_fin 3)))

/-- Evaluating a rank-one marginal on a vector sums the squared slice overlaps. -/
private theorem sliced_expectation {D R : Type*} [Fintype D] [Fintype R]
    (w : D × R → ℂ) (v : R → ℂ) :
    (star v ⬝ᵥ (partialTraceLeft (outer w) *ᵥ v)).re =
      ∑ z : D, ‖star v ⬝ᵥ (fun r => w (z,r))‖ ^ 2 := by
  have h : partialTraceLeft (outer w) = ∑ z : D, outer (fun r => w (z,r)) := by
    ext i j
    simp [partialTraceLeft, vecMulVec_apply, Matrix.sum_apply]
  rw [h, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [vecMulVec_mulVec, dotProduct_smul]
  have he : (star (fun r => w (z,r)) ⬝ᵥ v) =
      star (star v ⬝ᵥ (fun r => w (z,r))) := by
    rw [star_dotProduct]
  rw [he]
  let x := star v ⬝ᵥ (fun r => w (z,r))
  change (x * star x).re = ‖x‖ ^ 2
  rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.sq_norm]

private theorem dot_bell_complement {a : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
    (u v : a) :
    star (bell a) ⬝ᵥ complementVector u v =
      (↑(((Fintype.card a : ℝ) - 2) / Real.sqrt (Fintype.card a)) : ℂ) := by
  have h (x : a) : star (bell a) ⬝ᵥ basisVector x =
      (↑(Real.sqrt (Fintype.card a)) : ℂ)⁻¹ := by
    rw [show basisVector x = Pi.single (x,x) 1 by
      funext p
      simp [basisVector, Pi.single_apply, Prod.ext_iff], dotProduct_single]
    simp [bell, diagonalVector]
  have hd : star (bell a) ⬝ᵥ diagonalVector a =
      (Fintype.card a : ℂ) * (↑(Real.sqrt (Fintype.card a)) : ℂ)⁻¹ := by
    simp [dotProduct, bell, diagonalVector, Fintype.sum_prod_type]
  simp only [complementVector, dotProduct_sub, h, hd, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

private theorem tensor_dot_bound {D R : Type*} [Fintype D] [Fintype R]
    (w : D × R → ℂ) (u : D → ℂ) (v : R → ℂ) (hu : star u ⬝ᵥ u = 1) :
    ‖star (fun p : D × R => u p.1 * v p.2) ⬝ᵥ w‖ ^ 2 ≤
      ∑ z : D, ‖star v ⬝ᵥ (fun r => w (z,r))‖ ^ 2 := by
  let f (z : D) := star v ⬝ᵥ (fun r => w (z,r))
  have he : star (fun p : D × R => u p.1 * v p.2) ⬝ᵥ w =
      ∑ z : D, star (u z) * f z := by
    simp [dotProduct, Fintype.sum_prod_type, f, Finset.mul_sum, mul_assoc, mul_left_comm]
  have hU : ∑ z : D, ‖u z‖ ^ 2 = 1 := by
    simpa only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.one_re, Complex.sq_norm]
      using congrArg Complex.re hu
  have htriangle : ‖∑ z : D, star (u z) * f z‖ ≤ ∑ z : D, ‖u z‖ * ‖f z‖ := by
    simpa [norm_mul] using (norm_sum_le (Finset.univ : Finset D) (fun z => star (u z) * f z))
  rw [he]
  calc
    _ ≤ (∑ z : D, ‖u z‖ * ‖f z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle _
    _ ≤ _ := by simpa [hU] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset D)
        (fun z => ‖u z‖) (fun z => ‖f z‖))

theorem pairedMarginal_overlap (s : Finset ι) (flip : Bool) :
    1 - 4 / (Fintype.card (Bits ι) : ℝ) ≤
      (star (bell (Kept s)) ⬝ᵥ
        (pairMatrix (pairedMarginal s (normalizedChoi (channel flip))) *ᵥ bell (Kept s))).re := by
  classical
  let E := (pairedSplit s).symm
  let U := (zeroWord : Bits ι)
  let V := (oneWord : Bits ι)
  let B (p : Paired (Discarded s) × Paired (Kept s)) := blockVector U V flip (E p)
  let Q (p : Paired (Discarded s) × Paired (Kept s)) := complementVector U V (E p)
  let d : ℝ := Fintype.card (Bits ι)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Bits ι))
  have hm : pairMatrix (pairedMarginal s (normalizedChoi (channel flip))) =
      (d⁻¹ : ℝ) • (partialTraceLeft (outer B) + partialTraceLeft (outer Q)) := by
    ext i j
    change (∑ z : Paired (Discarded s),
      pairMatrix (normalizedChoi (RankTwoHiddenProcess.hiddenChannel U V flip))
        (E (z,i)) (E (z,j))) = _
    have h := normalizedChoi_hiddenChannel U V (words_ne (ι := ι)) flip
    simp_rw [h]
    simp only [partialTraceLeft, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      vecMulVec_apply, Pi.star_apply, Complex.real_smul, Complex.ofReal_inv,
      d, Complex.ofReal_natCast, ← Finset.sum_add_distrib, Finset.mul_sum, B, Q]
  let η := bell (Kept s)
  have hdot : star (fun p : Paired (Discarded s) × Paired (Kept s) =>
      bell (Discarded s) p.1 * η p.2) ⬝ᵥ Q =
      (↑((d - 2) / Real.sqrt d) : ℂ) := by
    have h := Equiv.sum_comp E
      (fun p => star (bell (Bits ι) p) * complementVector U V p)
    change (∑ p, star (bell (Discarded s) p.1 * η p.2) * Q p) = _
    have hb (p : Paired (Discarded s) × Paired (Kept s)) :
        bell (Discarded s) p.1 * η p.2 = bell (Bits ι) (E p) :=
      (bell_pairedSplit s p.1 p.2).symm
    simp_rw [hb]
    rw [show (∑ p, star (bell (Bits ι) (E p)) * Q p) = _ from h]
    exact dot_bell_complement U V
  have htail := tensor_dot_bound Q (bell (Discarded s)) η bell_norm
  rw [hdot, Complex.norm_real, Real.norm_eq_abs, sq_abs] at htail
  change _ ≤ (star η ⬝ᵥ (pairMatrix (pairedMarginal s (normalizedChoi (channel flip))) *ᵥ η)).re
  rw [hm, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.ofReal_re, Complex.add_re, sliced_expectation, sliced_expectation]
  have hb : 0 ≤ ∑ z : Paired (Discarded s), ‖star η ⬝ᵥ (fun r => B (z,r))‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiv : 1 - 4 / d ≤ d⁻¹ * (((d - 2) / Real.sqrt d) ^ 2) := by
    rw [div_pow, Real.sq_sqrt hd.le]
    field_simp
    nlinarith
  exact hdiv.trans (mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hd.le))

theorem pairedMarginal_entropy (s : Finset ι) (flip : Bool) :
    vonNeumannEntropy (pairedMarginal s (normalizedChoi (channel flip))) ≤
      12 / Real.sqrt (Fintype.card (Bits ι)) := by
  let d : ℝ := Fintype.card (Bits ι)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Bits ι))
  have hd₁ : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card (Bits ι)))
  have h := entropy_le_of_rank_three _ (bell (Kept s)) bell_norm
    (pairedMarginal_rank s flip) (4 / d) (pairedMarginal_overlap s flip)
  have hs := Real.sqrt_pos.2 hd
  have hsd : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hs₁ : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hd₁
  have hle : 4 / d ≤ 4 / Real.sqrt d := by
    apply div_le_div_of_nonneg_left (by norm_num) hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) hs.le]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by norm_num] at h
  change _ ≤ 12 / Real.sqrt d
  calc
    _ ≤ 4 / d + 4 * (2 / Real.sqrt d) := h
    _ ≤ 4 / Real.sqrt d + 4 * (2 / Real.sqrt d) := add_le_add_left hle _
    _ = _ := by ring

/-- For disjoint regions, this entropy combination is the paired conditional mutual information. -/
def pairedCMI (ρ : DensityState (Paired (Bits ι))) (L M N : Finset ι) : ℝ :=
  vonNeumannEntropy (pairedMarginal (L ∪ M) ρ) +
    vonNeumannEntropy (pairedMarginal (M ∪ N) ρ) -
    vonNeumannEntropy (pairedMarginal M ρ) -
    vonNeumannEntropy (pairedMarginal (L ∪ M ∪ N) ρ)

omit [Nonempty ι] in
theorem card_bits : Fintype.card (Bits ι) = 2 ^ Fintype.card ι := by
  simp [ParityFamily.Bits, Fintype.card_fun]

private theorem inv_sqrt_two_pow (n : ℕ) :
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ = Real.exp (-Real.log 2 * n / 2) := by
  have he : Real.exp (Real.log 2 * n / 2) = Real.sqrt ((2 : ℝ) ^ n) := by
    apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity), pow_two, ← Real.exp_add]
    rw [show Real.log 2 * (n : ℝ) / 2 + Real.log 2 * n / 2 = (n : ℝ) * Real.log 2 by ring,
      ← Real.log_pow, Real.exp_log (by positivity)]
  rw [show -Real.log 2 * (n : ℝ) / 2 = -(Real.log 2 * n / 2) by ring, Real.exp_neg, he]

/-- The first bound uses the full register size and the second uses the middle region. -/
theorem pairedCMI_decay (flip : Bool) (L M N : Finset ι) :
    pairedCMI (normalizedChoi (channel flip)) L M N ≤
      24 * Real.exp (-Real.log 2 * Fintype.card ι / 2) ∧
    pairedCMI (normalizedChoi (channel flip)) L M N ≤
      24 * Real.exp (-Real.log 2 * M.card / 2) := by
  have h₁ := pairedMarginal_entropy (L ∪ M) flip
  have h₂ := pairedMarginal_entropy (M ∪ N) flip
  have h₃ := state_entropy_nonneg (pairedMarginal M (normalizedChoi (channel flip)))
  have h₄ := state_entropy_nonneg (pairedMarginal (L ∪ M ∪ N) (normalizedChoi (channel flip)))
  have h : pairedCMI (normalizedChoi (channel flip)) L M N ≤
      24 / Real.sqrt (Fintype.card (Bits ι)) := by
    unfold pairedCMI
    calc
      _ ≤ _ := (sub_le_self _ h₄).trans ((sub_le_self _ h₃).trans (add_le_add h₁ h₂))
      _ = _ := by ring
  rw [card_bits, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, inv_sqrt_two_pow] at h
  refine ⟨h, h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))⟩
  have hc : (M.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast M.card_le_univ
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [mul_le_mul_of_nonneg_left hc hl]

end MarginalBounds

section Minimax

variable [Nonempty ι]

/-- The worst-case diamond error for any single reconstructed channel is at least one. -/
private theorem diamond_minimax (C : QuantumChannel (Bits ι) (Bits ι)) :
    1 ≤ max (diamondDistance (channel false) C) (diamondDistance (channel true) C) := by
  let P : QuantumChannel (Bits ι) (Bits ι) := channel false
  let Q : QuantumChannel (Bits ι) (Bits ι) := channel true
  have h : diamondDistance P Q ≤ diamondDistance P C + diamondDistance Q C := by
    apply diamondDistance_le _ _
      (add_nonneg (diamondDistance_nonneg' _ _) (diamondDistance_nonneg' _ _))
    intro n ρ
    let A := pairMatrix (referenceState P ρ)
    let B := pairMatrix (referenceState Q ρ)
    let T := pairMatrix (referenceState C ρ)
    have h₁ := referenceError_le_diamond P C ρ
    have h₂ := referenceError_le_diamond Q C ρ
    change traceNorm (A - T) ≤ _ at h₁
    change traceNorm (B - T) ≤ _ at h₂
    change traceNorm (A - B) ≤ _
    rw [show A - B = (A - T) + -(B - T) by abel]
    exact (traceNorm_add_le _ _).trans (by rw [traceNorm_neg]; exact add_le_add h₁ h₂)
  rw [show diamondDistance P Q = 2 from RankTwoHiddenProcess.maximal_diamond] at h
  change 1 ≤ max (diamondDistance P C) (diamondDistance Q C)
  linarith [le_max_left (diamondDistance P C) (diamondDistance Q C),
    le_max_right (diamondDistance P C) (diamondDistance Q C)]

def properPairedData (C : QuantumChannel (Bits ι) (Bits ι))
    (s : {s : Finset ι // s ≠ Finset.univ}) : DensityState (Paired (Kept s.val)) :=
  pairedMarginal s.val (normalizedChoi C)

theorem paired_data_minimax
    (estimate : ((s : {s : Finset ι // s ≠ Finset.univ}) → DensityState (Paired (Kept s.val))) →
      QuantumChannel (Bits ι) (Bits ι)) :
    1 ≤ max (diamondDistance (channel false) (estimate (properPairedData (channel false))))
      (diamondDistance (channel true) (estimate (properPairedData (channel true)))) := by
  have h : properPairedData (ι := ι) (channel false) = properPairedData (channel true) :=
    funext fun s => pairedMarginal_proper_eq s.val s.property
  rw [← h]
  exact diamond_minimax _

end Minimax

/-- The uniform obstruction for rank-two unital channels on at least two sites. -/
theorem uniform_obstruction [Nontrivial ι] :
    (∀ flip, IsLeast {k | RankTwoHiddenProcess.HasKrausCount (channel (ι := ι) flip) k} 2 ∧
      (channel (ι := ι) flip).toCompletelyPositiveMap 1 = 1) ∧
    properPairedData (ι := ι) (channel false) = properPairedData (channel true) ∧
    traceNorm (pairMatrix (normalizedChoi (channel (ι := ι) false)) -
      pairMatrix (normalizedChoi (channel (ι := ι) true))) = 4 / (2 : ℝ) ^ Fintype.card ι ∧
    diamondDistance (channel (ι := ι) false) (channel true) = 2 ∧
    (∀ flip (L M N : Finset ι), pairedCMI (normalizedChoi (channel flip)) L M N ≤
      24 * Real.exp (-Real.log 2 * M.card / 2)) := by
  refine ⟨(RankTwoHiddenProcess.rank_two_ambiguity (ι := ι)).1,
    funext fun s => pairedMarginal_proper_eq s.val s.property, ?_,
    RankTwoHiddenProcess.maximal_diamond, fun f L M N => (pairedCMI_decay f L M N).2⟩
  simpa only [channel, card_bits, Nat.cast_pow, Nat.cast_ofNat] using
    (normalizedChoi_traceNorm (zeroWord : Bits ι) oneWord words_ne)

end Paired

end UnitaryReconstruction.LiuWildChoiObstruction
