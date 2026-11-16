/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Frequency restriction after complete original inverse colour transport. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm

/-! A mode-diagonal inverse substitution sums over every colour at the
selected frequency. Increasing the frequency box therefore preserves every
retained transported entry and mean. The restriction is performed after the
full inverse transport, without a positivity or nonempty-type assumption. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeInvolution SignedOscillatorWick LatticeAllStateField
open SourceBPZ.OriginalSourceCoevaluation
open OriginalGaussianExternalBlocks OriginalGaussianSourceGerm
open OriginalGaussianSourceMeans OriginalSourceInverseCoefficient NativeAffineTransport
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open OriginalAffineRecompositionSource OriginalFourMChargeCoset
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open MvPolynomial
open FactorialFockMetric (weight)

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Retain a frequency while keeping its colour unchanged. -/
def internalInclusion (D : LatticeData) (N M : ℕ) (h : N ≤ M) : Internal D N ↪ Internal D M where
  toFun i := (i.1, ⟨i.2.val, i.2.isLt.trans_le h⟩)
  inj' := by
    intro i j he
    apply Prod.ext
    · exact congrArg (fun k : Internal D M => k.1) he
    · exact Fin.ext (congrArg (fun k : Internal D M => k.2.val) he)

private def colourInverse (D : LatticeData) (s : ℕ) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (((-((s : ℂ) + 1))⁻¹ • (gramComplex D)⁻¹))ᵀ

private theorem source_sum (D : LatticeData) (N : ℕ)
    (F : Internal D N ⊕ X → ℂ) (i : Internal D N ⊕ X) :
    transportMean (sourceBlock (J := X) (inverseSubstitution D N)) F i =
      match i with
      | .inl i => ∑ c, colourInverse D i.2.val i.1 c * F (.inl (c, i.2))
      | .inr x => F (.inr x) := by
  cases i with
  | inl i =>
    simp [transportMean, sourceBlock, inverseSubstitution, boxMatrix,
      Fintype.sum_prod_type, colourInverse, ite_mul, eq_comm]
  | inr x => simp [transportMean, sourceBlock, Matrix.one_apply]

private theorem covariance_as_means {I : Type*} [Fintype I]
    (U C : Matrix I I ℂ) (i j : I) :
    transportCovariance U C i j = transportMean U (fun a => transportMean U (C a) j) i := by
  simp only [transportCovariance, transportMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem raw_entry_restrict (D : LatticeData) (N M : ℕ) (h : N ≤ M)
    (e : X → External D) (i j : Internal D N ⊕ X) :
    originalRow D M e ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i)
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) j) =
    originalRow D N e i j := by
  cases i <;> cases j <;> rfl

private theorem raw_mean_restrict (D : LatticeData) (a : Charge D)
    (N M : ℕ) (h : N ≤ M) (e : X → External D) (i : Internal D N ⊕ X) :
    originalMean D a M e
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i) =
    originalMean D a N e i := by
  cases i <;> rfl

/-- Every entry of the actual right covariance restricts across frequency
boxes after its complete inverse-colour transport. External coordinates stay
fixed, and both mixed rectangles are included. -/
theorem original_right_covariance_restrict (D : LatticeData) (N M : ℕ) (h : N ≤ M)
    (e : X → External D) (i j : Internal D N ⊕ X) :
    transportCovariance (sourceBlock (J := X) (inverseSubstitution D M))
      (originalRow D M e)
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i)
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) j) =
    transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
      (originalRow D N e) i j := by
  simp only [covariance_as_means]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [Function.Embedding.sumMap, Sum.map_inl, source_sum,
        internalInclusion]
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
    | inr j =>
      simp only [Function.Embedding.sumMap, Sum.map_inl, Sum.map_inr,
        Function.Embedding.refl_apply, source_sum, internalInclusion]
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
  | inr i =>
    cases j with
    | inl j =>
      simp only [Function.Embedding.sumMap, Sum.map_inl, Sum.map_inr,
        Function.Embedding.refl_apply, source_sum, internalInclusion]
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
    | inr j =>
      simp only [Function.Embedding.sumMap, Sum.map_inr,
        Function.Embedding.refl_apply, source_sum]
      exact raw_entry_restrict D N M h e (.inr i) (.inr j)

/-- The actual opposite-charge right mean has the same full-colour
restriction law. No cutoff-dependent replacement source is introduced. -/
theorem original_right_mean_restrict (D : LatticeData) (a : Charge D)
    (N M : ℕ) (h : N ≤ M) (e : X → External D) (i : Internal D N ⊕ X) :
    originalInverseMean D a M e
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i) =
    originalInverseMean D a N e i := by
  unfold originalInverseMean
  cases i with
  | inl i =>
    simp only [Function.Embedding.sumMap, Sum.map_inl, source_sum, internalInclusion]
    apply Finset.sum_congr rfl
    intro c hc
    congr 1
  | inr i =>
    simp only [Function.Embedding.sumMap, Sum.map_inr,
      Function.Embedding.refl_apply, source_sum]
    exact raw_mean_restrict D (-a) N M h e (.inr i)

private theorem affine_enlarge {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (C : Matrix J J ℂ) (m : J → ℂ)
    (f : I ↪ J) (d : I →₀ ℕ) :
    OriginalChargedRowSource.affineCoefficient C m (d.embDomain f) =
      OriginalChargedRowSource.affineCoefficient (fun i j => C (f i) (f j))
        (fun i => m (f i)) d := by
  have he := congrArg (fun p : ℤ →₀ ℂ => p 0)
    (OriginalCorrectedRowRecompositionSource.affineLaurent_enlarge C m (fun _ => 0) f d)
  simpa [OriginalNormalRowSource.affineLaurent, Finsupp.weight_apply] using he

/-- The full actual native row coefficients stabilize under enlargement of
the internal frequency box. Both external occupations remain in the full
row degree; the right equality uses the complete transported covariance and
opposite-charge mean before coefficient restriction. -/
theorem original_row_coefficients_restrict (D : LatticeData) (a : Charge D)
    (N M : ℕ) (hNM : N ≤ M) (e : X → External D) (z : ℂ)
    (d : Internal D N →₀ ℕ) (h : X →₀ ℕ) :
    let f := (internalInclusion D N M hNM).sumMap (Function.Embedding.refl X)
    OriginalChargedRowSource.affineCoefficient (leftRow D M e z) (leftMean D a M e z)
      ((d.sumElim h).embDomain f) =
      OriginalChargedRowSource.affineCoefficient (leftRow D N e z) (leftMean D a N e z)
        (d.sumElim h) ∧
    OriginalChargedRowSource.affineCoefficient (rightRow D M e z) (rightMean D a M e z)
      ((d.sumElim h).embDomain f) =
      OriginalChargedRowSource.affineCoefficient (rightRow D N e z) (rightMean D a N e z)
        (d.sumElim h) := by
  let f := (internalInclusion D N M hNM).sumMap (Function.Embedding.refl X)
  have hdamp (i : Internal D N ⊕ X) : damp D M z (f i) = damp D N z i := by
    cases i <;> rfl
  have hleft : (fun i j => leftRow D M e z (f i) (f j)) = leftRow D N e z := by
    funext i j
    simp only [leftRow, hdamp, f, raw_entry_restrict]
  have hright : (fun i j => rightRow D M e z (f i) (f j)) = rightRow D N e z := by
    funext i j
    simp only [rightRow, hdamp]
    rw [original_right_covariance_restrict]
  have hm : (fun i => leftMean D a M e z (f i)) = leftMean D a N e z := by
    funext i
    cases i <;> rfl
  have hn : (fun i => rightMean D a M e z (f i)) = rightMean D a N e z := by
    funext i
    simp only [rightMean_raw]
    rw [hdamp, original_right_mean_restrict]
  constructor
  · exact (affine_enlarge _ _ f (d.sumElim h)).trans (by rw [hleft, hm])
  · exact (affine_enlarge _ _ f (d.sumElim h)).trans (by rw [hright, hn])


private theorem inclusion_energy (D : LatticeData) (N M : ℕ) (h : N ≤ M)
    (d : Internal D N →₀ ℕ) :
    internalEnergy D M (d.embDomain (internalInclusion D N M h)) = internalEnergy D N d := by
  simp only [internalEnergy, Finsupp.sum_embDomain]
  rfl

private theorem energy_support (D : LatticeData) (M n : ℕ)
    (d : Internal D M →₀ ℕ) (hd : internalEnergy D M d = n)
    (i : Internal D M) (hi : i ∈ d.support) : i.2.val + 1 ≤ n := by
  have hp : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hs : (i.2.val + 1) * d i ≤ internalEnergy D M d := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((j.2.val + 1) * d j)) hi
  nlinarith

private theorem energy_surjective (D : LatticeData) (N M n : ℕ)
    (h : N ≤ M) (hn : n ≤ N) (d : Internal D M →₀ ℕ)
    (hd : internalEnergy D M d = n) :
    ∃ c : Internal D N →₀ ℕ,
      internalEnergy D N c = n ∧ c.embDomain (internalInclusion D N M h) = d := by
  have hr : d ∈ Set.range (Finsupp.embDomain (internalInclusion D N M h)) := by
    rw [Finsupp.mem_range_embDomain_iff]
    intro i hi
    have hs := energy_support D M n d hd i hi
    refine ⟨(i.1, ⟨i.2.val, by omega⟩), ?_⟩
    apply Prod.ext rfl
    exact Fin.ext rfl
  obtain ⟨c, rfl⟩ := hr
  exact ⟨c, (inclusion_energy D N M h c).symm.trans hd, rfl⟩

private theorem inclusion_join (D : LatticeData) (N M : ℕ) (hNM : N ≤ M)
    (d : Internal D N →₀ ℕ) (h : X →₀ ℕ) :
    (d.sumElim h).embDomain
      ((internalInclusion D N M hNM).sumMap (Function.Embedding.refl X)) =
      (d.embDomain (internalInclusion D N M hNM)).sumElim h := by
  ext i
  cases i with
  | inl i =>
    by_cases hi : i ∈ Set.range (internalInclusion D N M hNM)
    · obtain ⟨j, rfl⟩ := hi
      have he := Finsupp.embDomain_apply_self
        ((internalInclusion D N M hNM).sumMap (Function.Embedding.refl X))
        (d.sumElim h) (.inl j)
      simpa using he
    · rw [Finsupp.embDomain_of_notMem_range, Finsupp.sumElim_inl,
        Finsupp.embDomain_of_notMem_range _ _ _ hi]
      rintro ⟨j | j, hj⟩
      · exact hi ⟨j, Sum.inl.inj hj⟩
      · cases hj
  | inr i =>
    have he := Finsupp.embDomain_apply_self
      ((internalInclusion D N M hNM).sumMap (Function.Embedding.refl X))
      (d.sumElim h) (.inr i)
    simpa using he

/-- The full native row energy layer is unchanged once the cutoff contains
all positive frequencies permitted by its energy. The sum retains exactly
one internal factorial and both full external occupations. This includes
zero energy, rank zero and empty external families. -/
theorem original_row_energy_layer_stabilizes (D : LatticeData) (a : Charge D)
    (N M n : ℕ) (hNM : N ≤ M) (hn : n ≤ N) (e : X → External D)
    (z : ℂ) (h k : X →₀ ℕ) :
    (∑ᶠ d : {d : Internal D N →₀ ℕ // internalEnergy D N d = n},
      (FactorialFockMetric.weight d.val : ℂ) *
        OriginalChargedRowSource.affineCoefficient
          (leftRow D N e z) (leftMean D a N e z) (d.val.sumElim h) *
        OriginalChargedRowSource.affineCoefficient
          (rightRow D N e z) (rightMean D a N e z) (d.val.sumElim k)) =
    ∑ᶠ d : {d : Internal D M →₀ ℕ // internalEnergy D M d = n},
      (FactorialFockMetric.weight d.val : ℂ) *
        OriginalChargedRowSource.affineCoefficient
          (leftRow D M e z) (leftMean D a M e z) (d.val.sumElim h) *
        OriginalChargedRowSource.affineCoefficient
          (rightRow D M e z) (rightMean D a M e z) (d.val.sumElim k) := by
  classical
  let f : {d : Internal D N →₀ ℕ // internalEnergy D N d = n} →
      {d : Internal D M →₀ ℕ // internalEnergy D M d = n} :=
    fun d => ⟨d.val.embDomain (internalInclusion D N M hNM),
      (inclusion_energy D N M hNM d.val).trans d.property⟩
  apply finsum_eq_of_bijective f
  · constructor
    · intro c d he
      apply Subtype.ext
      exact Finsupp.embDomain_injective _ (congrArg Subtype.val he)
    · intro d
      obtain ⟨c, hc, he⟩ := energy_surjective D N M n hNM hn d.val d.property
      exact ⟨⟨c, hc⟩, Subtype.ext he⟩
  · intro d
    have hw : FactorialFockMetric.weight
        (d.val.embDomain (internalInclusion D N M hNM)) =
        FactorialFockMetric.weight d.val := by
      simp only [FactorialFockMetric.weight, Finsupp.prod_embDomain]
    have hl := (original_row_coefficients_restrict D a N M hNM e z d.val h).1
    have hr := (original_row_coefficients_restrict D a N M hNM e z d.val k).2
    simp only [inclusion_join] at hl hr
    dsimp only [f]
    rw [hw, hl, hr]


private theorem box_omega (D : LatticeData) (M : ℕ) (p : Exponent D)
    (hp : ∀ b ∈ p.support, b.2 < M) :
    Finsupp.weight (fun i => (omega D (boxLabel D M i) : ℤ)) (boxOccupation D M p) =
      Finsupp.weight (fun b => (omega D b : ℤ)) p := by
  have he := congrArg (Finsupp.weight (fun b : Index D => (omega D b : ℤ)))
    (box_reconstruct D M p hp)
  simpa only [Finsupp.weight_apply, Finsupp.sum_embDomain] using he

private theorem original_two_rows_box (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (alpha betaL gammaL betaR gammaR : Exponent D)
    (eL eR : ℤ) (n M : ℕ) (ha : oscillatorEnergy alpha = n) (hn : n < M)
    (hbL : ∀ b ∈ betaL.support, b.2 < M) (hgL : ∀ b ∈ gammaL.support, b.2 < M)
    (hbR : ∀ b ∈ betaR.support, b.2 < M) (hgR : ∀ b ∈ gammaR.support, b.2 < M) :
    chargeScalar D a * chargeScalar D (-a) *
      wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
        (monomial alpha 1) (monomial betaL 1)) *
      wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
        (dualOscillatorMonomial D alpha) (monomial betaR 1)) =
    let A := correctedMatrix D (boxLabel D M)
    let U := sourceBlock (J := Internal D M ⊕ Internal D M) (inverseSubstitution D M)
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      ((weight alpha : ℂ) *
        OriginalChargedRowSource.affineCoefficient A
          (correctedMean D a (boxLabel D M))
          (threeOccupation (boxOccupation D M alpha)
            (boxOccupation D M betaL) (boxOccupation D M gammaL)) *
        OriginalChargedRowSource.affineCoefficient (transportCovariance U A)
          (transportMean U (correctedMean D (-a) (boxLabel D M)))
          (threeOccupation (boxOccupation D M alpha)
            (boxOccupation D M betaR) (boxOccupation D M gammaR))) := by
  have ham := energy_mode D alpha n M ha.le hn
  have hl := original_corrected_gaussian_row D hu a alpha betaL gammaL eL
  have he := congrArg (fun p : ℤ →₀ ℂ => p (eL + chargeNorm D a))
    (correctedLaurentRow_on_box D a alpha betaL gammaL M ham hbL hgL)
  dsimp only at hl he
  rw [he] at hl
  have hr := source_inverse_affine_row_box D hu (-a) alpha betaR gammaR eR n M
    ha.le hn hbR hgR
  dsimp only at hr ⊢
  rw [hl, hr]
  simp only [affineLaurent_apply, normal_weight_formula, box_energy D M alpha ham,
    box_omega D M betaL hbL, box_omega D M gammaL hgL,
    box_omega D M betaR hbR, box_omega D M gammaR hgR, ha]
  unfold inverseSubstitution
  split_ifs <;> ring

/-- One arbitrary common frequency box expresses the literal original Wick
energy contraction by its finite native affine energy layer. Both charge
scalars, four external factorials and both Laurent selectors are retained;
the complete inverse-colour substitution acts on the right source row. -/
theorem original_fixed_energy_common_box (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n M : ℕ) (hn : n < M)
    (hbL : ∀ b ∈ betaL.support, b.2 < M) (hgL : ∀ b ∈ gammaL.support, b.2 < M)
    (hbR : ∀ b ∈ betaR.support, b.2 < M) (hgR : ∀ b ∈ gammaR.support, b.2 < M) :
    (∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0) =
    let A := correctedMatrix D (boxLabel D M)
    let U := sourceBlock (J := Internal D M ⊕ Internal D M) (inverseSubstitution D M)
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      ∑ᶠ d : {d : Internal D M →₀ ℕ // internalEnergy D M d = n},
        (weight d.val : ℂ) *
          OriginalChargedRowSource.affineCoefficient A
            (correctedMean D a (boxLabel D M))
            (threeOccupation d.val (boxOccupation D M betaL) (boxOccupation D M gammaL)) *
          OriginalChargedRowSource.affineCoefficient (transportCovariance U A)
            (transportMean U (correctedMean D (-a) (boxLabel D M)))
            (threeOccupation d.val (boxOccupation D M betaR) (boxOccupation D M gammaR)) := by
  classical
  let F (alpha : Exponent D) := chargeScalar D a * chargeScalar D (-a) *
    wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
      (monomial alpha 1) (monomial betaL 1)) *
    wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
      (dualOscillatorMonomial D alpha) (monomial betaR 1))
  have hs : (∑ᶠ alpha : {alpha : Exponent D // oscillatorEnergy alpha = n}, F alpha.val) =
      ∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then F alpha else 0 := by
    rw [finsum_subtype_eq_finsum_cond]
    simp only [finsum_eq_if]
  rw [← hs]
  let f : {alpha : Exponent D // oscillatorEnergy alpha = n} →
      {d : Internal D M →₀ ℕ // internalEnergy D M d = n} := fun alpha =>
    ⟨boxOccupation D M alpha.val, by
      have he := box_energy D M alpha.val (energy_mode D alpha.val n M alpha.property.le hn)
      change (boxOccupation D M alpha.val).sum (fun i c => c * (i.2.val + 1)) =
        oscillatorEnergy alpha.val at he
      simpa only [internalEnergy, Nat.mul_comm]
        using he.trans alpha.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro alpha beta he
      apply Subtype.ext
      have hh := congrArg (fun d => d.embDomain (boxLabel D M)) (congrArg Subtype.val he)
      exact (box_reconstruct D M alpha.val
        (energy_mode D alpha.val n M alpha.property.le hn)).symm.trans
          (hh.trans (box_reconstruct D M beta.val
            (energy_mode D beta.val n M beta.property.le hn)))
    · intro d
      let alpha := d.val.embDomain (boxLabel D M)
      have ham : ∀ b ∈ alpha.support, b.2 < M := by
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hb
        exact i.2.isLt
      have hbox : boxOccupation D M alpha = d.val := by
        exact Finsupp.comapDomain_embDomain _ _
      have he : oscillatorEnergy alpha = n := by
        rw [← box_energy D M alpha ham, hbox]
        change d.val.sum (fun i c => c * (i.2.val + 1)) = n
        simpa only [internalEnergy, Nat.mul_comm] using d.property
      exact ⟨⟨alpha, he⟩, Subtype.ext hbox⟩
  dsimp only
  rw [mul_finsum]
  apply finsum_eq_of_bijective f hf
  intro alpha
  have he := original_two_rows_box D hu a alpha.val betaL gammaL betaR gammaR
    eL eR n M alpha.property hn hbL hgL hbR hgR
  have hw : weight alpha.val = weight (boxOccupation D M alpha.val) := by
    have hr := congrArg weight (box_reconstruct D M alpha.val
      (energy_mode D alpha.val n M alpha.property.le hn))
    simpa only [weight, Finsupp.prod_embDomain] using hr.symm
  dsimp only [F, f]
  rw [he, hw]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
